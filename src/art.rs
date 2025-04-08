use std::{
    collections::{BTreeMap, HashMap},
    f32::consts::E,
    mem::size_of,
    sync::atomic::AtomicU64,
};

use derive_more::derive::From;
use serde_json::Value;

const ART_BLOCK_SIZE: usize = 256;

const TAG_NONE: usize = 0b000;
const TAG_VALUE: usize = 0b001;
const TAG_1: usize = 0b010;
const TAG_4: usize = 0b011;
const TAG_16: usize = 0b100;
const TAG_48: usize = 0b101;
const TAG_256: usize = 0b110;
const TAG_MASK: usize = 0b111;
const PTR_MASK: usize = usize::MAX - TAG_MASK;

const HEAP_TAG_DISK: usize = 0b0;
const HEAP_TAG_MEM: usize = 0b1;

const MAX_PATH_COMPRESSION_BYTES: usize = 9;

const NONE_HEADER: NodeHeader = NodeHeader {
    children: 0,
    path_len: 0,
    path: [0; MAX_PATH_COMPRESSION_BYTES],
    version: 0,
};

#[derive(Debug, From)]
pub enum Error {
    ConflictingTwigTypes { origin: TwigKey, added: TwigKey },
    IncompatibleVersion,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::ConflictingTwigTypes { origin, added } => write!(
                f,
                "New entry for TwigNode {:?} conflicts with previous type {:?}",
                origin, added
            ),
            Error::IncompatibleVersion => write!(f, "Attempt to insert incompatible version"),
        }
    }
}

impl std::error::Error for Error {}

pub type Result<T> = core::result::Result<T, Error>;

pub struct Art {
    len: usize,
    root: NodePtr,
    version_counter: u64,
    allocated_blocks: usize,
}

impl Clone for Art {
    fn clone(&self) -> Self {
        Self {
            len: self.len.clone(),
            root: self.root.clone(),
            version_counter: self.version_counter,
            allocated_blocks: self.allocated_blocks,
        }
    }
}

impl Default for Art {
    fn default() -> Art {
        Art {
            len: 0,
            root: NodePtr::none(),
            version_counter: 0,
            allocated_blocks: 1,
        }
    }
}

impl Art {
    pub const fn new() -> Art {
        Art {
            len: 0,
            root: NodePtr::none(),
            version_counter: 0,
            allocated_blocks: 1,
        }
    }

    pub const fn len(&self) -> usize {
        self.len
    }

    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn root_as_ref(&self) -> &NodePtr {
        &self.root
    }

    pub fn insert(&mut self, key: &[u8], mut value: serde_json::Value, ts: u64) -> Result<HeapPtr> {
        let (parent_opt, cursor) = self.slot_for_key(&key, true, ts).unwrap();
        match cursor.deref_mut() {
            NodeMut::Value(ref mut twig) => {
                twig.header.version += 1;
                twig.checked_add(
                    LeafNode::new(twig.header.version, HeapPtr(ts as uszies), ts),
                    value,
                )
            }
            NodeMut::None => {
                *cursor = NodePtr::value(value);
                if let Some(children) = parent_opt {
                    *children = children.checked_add(1).unwrap();
                }
                self.len += 1;
                None
            }
            _ => unreachable!(),
        }
    }

    pub fn remove(&mut self, key: &[u8]) -> Option<TwigNode> {
        let (parent_opt, cursor) = self.slot_for_key(key, false)?;

        match std::mem::take(cursor).take() {
            Some(old) => {
                if let Some(children) = parent_opt {
                    *children = children.checked_sub(1).unwrap();

                    if *children == 48
                        || *children == 16
                        || *children == 4
                        || *children == 1
                        || *children == 0
                    {
                        self.prune(key);
                    }
                }
                self.len -= 1;
                Some(old)
            }
            None => None,
        }
    }

    pub fn get(&self, key: &[u8]) -> Option<&TwigNode> {
        let mut k: &[u8] = &*key;
        let mut cursor: &NodePtr = &self.root;

        while !k.is_empty() {
            let prefix = cursor.prefix();

            if !k.starts_with(prefix) {
                return None;
            }

            cursor = cursor.child(k[prefix.len()])?;
            k = &k[prefix.len() + 1..];
        }

        match cursor.deref() {
            NodeRef::Value(ref v) => return Some(v),
            NodeRef::None => return None,
            _ => unreachable!(),
        }
    }

    // []
    //  don't do anything
    // [1]
    //  shrink without while loop
    // [1][2]
    //
    // [1:2]
    // [1:2][3]
    // [1][2:3]
    // [12:3][4]
    // [1:2][3:4]
    fn prune(&mut self, key: &[u8]) {
        self.root.prune(key);
    }

    // returns the optional parent node for child maintenance, and the value node
    fn slot_for_key(
        &mut self,
        key: &[u8],
        is_add: bool,
        ts: u64,
    ) -> Option<(Option<&mut u16>, &mut NodePtr)> {
        let mut parent: Option<&mut u16> = None;
        let mut path: &[u8] = &key[..];
        let mut cursor: &mut NodePtr = &mut self.root;
        #[cfg(test)]
        println!("root is {:?}", cursor);

        while !path.is_empty() {
            #[cfg(test)]
            println!("path: {:?} cursor {:?}", path, cursor);
            cursor.assert_size();
            if cursor.is_none() {
                if !is_add {
                    return None;
                }
                // we need to create intermediate nodes before
                // populating the value for this insert
                *cursor = NodePtr::node1(Box::default());
                if let Some(children) = parent {
                    *children = children.checked_add(1).unwrap();
                }
                let prefix_len = (path.len() - 1).min(MAX_PATH_COMPRESSION_BYTES);
                let prefix = &path[..prefix_len];
                cursor.header_mut().path[..prefix_len].copy_from_slice(prefix);
                cursor.header_mut().path_len = u8::try_from(prefix_len).unwrap();
                let (p, child) = cursor.child_mut(path[prefix_len], is_add, false).unwrap();
                parent = Some(p);
                cursor = child;
                path = &path[prefix_len + 1..];
                continue;
            }

            let prefix = cursor.prefix();
            let partial_path = &path[..path.len() - 1];
            if !partial_path.starts_with(prefix) {
                if !is_add {
                    return None;
                }
                // path compression needs to be reduced
                // to allow for this key, which does not
                // share the compressed path.
                #[cfg(test)]
                println!("truncating cursor at {:?}", cursor);
                cursor.truncate_prefix(partial_path);
                #[cfg(test)]
                println!("cursor is now after truncation {:?}", cursor);
                continue;
            }

            let next_byte = path[prefix.len()];
            path = &path[prefix.len() + 1..];

            #[cfg(test)]
            println!("cursor is now {:?}", cursor);
            let clear_child_index = !is_add && path.is_empty();
            let (p, next_cursor) =
                if let Some(opt) = cursor.child_mut(next_byte, is_add, clear_child_index) {
                    opt
                } else {
                    assert!(!is_add);
                    return None;
                };
            cursor = next_cursor;
            parent = Some(p);
        }

        Some((parent, cursor))
    }
}

enum NodeRef<'a> {
    None,
    Value(&'a TwigNode),
    Node1(&'a Node1),
    Node4(&'a Node4),
    Node16(&'a Node16),
    Node48(&'a Node48),
    Node256(&'a Node256),
}

enum NodeMut<'a> {
    None,
    Value(&'a mut TwigNode),
    Node1(&'a mut Node1),
    Node4(&'a mut Node4),
    Node16(&'a mut Node16),
    Node48(&'a mut Node48),
    Node256(&'a mut Node256),
}

#[derive(Debug)]
struct NodePtr(usize);

impl NodePtr {
    const fn none() -> NodePtr {
        NodePtr(TAG_NONE)
    }

    fn node1(n1: Box<Node1>) -> NodePtr {
        let ptr: *mut Node1 = Box::into_raw(n1);
        let us = ptr as usize;
        assert_eq!(us & TAG_1, 0);
        NodePtr(us | TAG_1)
    }

    fn node4(n4: Box<Node4>) -> NodePtr {
        let ptr: *mut Node4 = Box::into_raw(n4);
        let us = ptr as usize;
        assert_eq!(us & TAG_4, 0);
        NodePtr(us | TAG_4)
    }

    fn node16(n16: Box<Node16>) -> NodePtr {
        let ptr: *mut Node16 = Box::into_raw(n16);
        let us = ptr as usize;
        assert_eq!(us & TAG_16, 0);
        NodePtr(us | TAG_16)
    }

    fn node48(n48: Box<Node48>) -> NodePtr {
        let ptr: *mut Node48 = Box::into_raw(n48);
        let us = ptr as usize;
        assert_eq!(us & TAG_48, 0);
        NodePtr(us | TAG_48)
    }

    fn node256(n256: Box<Node256>) -> NodePtr {
        let ptr: *mut Node256 = Box::into_raw(n256);
        let us = ptr as usize;
        assert_eq!(us & TAG_256, 0);
        NodePtr(us | TAG_256)
    }

    fn value(twig: TwigNode) -> NodePtr {
        let bx = Box::new(twig);
        let ptr: *mut TwigNode = Box::into_raw(bx);
        let us = ptr as usize;
        if size_of::<TwigNode>() > 0 {
            assert_eq!(us & TAG_VALUE, 0);
        } else {
            assert_eq!(ptr, std::ptr::NonNull::dangling().as_ptr());
        }
        NodePtr(us | TAG_VALUE)
    }

    const fn deref(&self) -> NodeRef {
        match self.0 & TAG_MASK {
            TAG_NONE => NodeRef::None,
            TAG_VALUE => {
                let ptr: *const TwigNode = if size_of::<TwigNode>() > 0 {
                    (self.0 & PTR_MASK) as *const TwigNode
                } else {
                    std::ptr::NonNull::dangling().as_ptr()
                };
                let reference: &TwigNode = unsafe { &(*ptr) };
                NodeRef::Value(reference)
            }
            TAG_1 => {
                let ptr: *const Node1 = (self.0 & PTR_MASK) as *const Node1;
                let reference: &Node1 = unsafe { &*ptr };
                NodeRef::Node1(reference)
            }
            TAG_4 => {
                let ptr: *const Node4 = (self.0 & PTR_MASK) as *const Node4;
                let reference: &Node4 = unsafe { &*ptr };
                NodeRef::Node4(reference)
            }
            TAG_16 => {
                let ptr: *const Node16 = (self.0 & PTR_MASK) as *const Node16;
                let reference: &Node16 = unsafe { &*ptr };
                NodeRef::Node16(reference)
            }
            TAG_48 => {
                let ptr: *const Node48 = (self.0 & PTR_MASK) as *const Node48;
                let reference: &Node48 = unsafe { &*ptr };
                NodeRef::Node48(reference)
            }
            TAG_256 => {
                let ptr: *const Node256 = (self.0 & PTR_MASK) as *const Node256;
                let reference: &Node256 = unsafe { &*ptr };
                NodeRef::Node256(reference)
            }
            _ => unreachable!(),
        }
    }

    fn deref_mut(&mut self) -> NodeMut {
        match self.0 & TAG_MASK {
            TAG_NONE => NodeMut::None,
            TAG_VALUE => {
                let ptr: *mut TwigNode = if size_of::<TwigNode>() > 0 {
                    (self.0 & PTR_MASK) as *mut TwigNode
                } else {
                    std::ptr::NonNull::dangling().as_ptr()
                };
                let reference: &mut TwigNode = unsafe { &mut (*ptr) };
                NodeMut::Value(reference)
            }
            TAG_1 => {
                let ptr: *mut Node1 = (self.0 & PTR_MASK) as *mut Node1;
                let reference: &mut Node1 = unsafe { &mut *ptr };
                NodeMut::Node1(reference)
            }
            TAG_4 => {
                let ptr: *mut Node4 = (self.0 & PTR_MASK) as *mut Node4;
                let reference: &mut Node4 = unsafe { &mut *ptr };
                NodeMut::Node4(reference)
            }
            TAG_16 => {
                let ptr: *mut Node16 = (self.0 & PTR_MASK) as *mut Node16;
                let reference: &mut Node16 = unsafe { &mut *ptr };
                NodeMut::Node16(reference)
            }
            TAG_48 => {
                let ptr: *mut Node48 = (self.0 & PTR_MASK) as *mut Node48;
                let reference: &mut Node48 = unsafe { &mut *ptr };
                NodeMut::Node48(reference)
            }
            TAG_256 => {
                let ptr: *mut Node256 = (self.0 & PTR_MASK) as *mut Node256;
                let reference: &mut Node256 = unsafe { &mut *ptr };
                NodeMut::Node256(reference)
            }
            _ => unreachable!(),
        }
    }

    fn should_shrink(&self) -> bool {
        match (self.deref(), self.len()) {
            (NodeRef::Node1(_), 0)
            | (NodeRef::Node4(_), 1)
            | (NodeRef::Node16(_), 4)
            | (NodeRef::Node48(_), 16)
            | (NodeRef::Node256(_), 48) => true,
            (_, _) => false,
        }
    }

    fn shrink_to_fit(&mut self) -> bool {
        if !self.should_shrink() {
            return false;
        }

        let old_header = *self.header();
        let children = old_header.children;

        let mut dropped = false;
        let mut swapped = std::mem::take(self);

        *self = match (swapped.deref_mut(), children) {
            (NodeMut::Node1(_), 0) => {
                dropped = true;
                NodePtr::none()
            }
            (NodeMut::Node4(n4), 1) => NodePtr::node1(n4.downgrade()),
            (NodeMut::Node16(n16), 4) => NodePtr::node4(n16.downgrade()),
            (NodeMut::Node48(n48), 16) => NodePtr::node16(n48.downgrade()),
            (NodeMut::Node256(n256), 48) => NodePtr::node48(n256.downgrade()),
            (_, _) => unreachable!(),
        };

        if !dropped {
            *self.header_mut() = old_header;
        }

        dropped
    }

    // returns true if this node went from Node4 to None
    fn prune(&mut self, partial_path: &[u8]) -> bool {
        let prefix = self.prefix();

        assert!(partial_path.starts_with(prefix));

        if partial_path.len() > prefix.len() + 1 {
            let byte = partial_path[prefix.len()];
            let subpath = &partial_path[prefix.len() + 1..];

            let (_, child) = self.child_mut(byte, false, false).expect(
                "prune may only be called with \
                freshly removed keys with a full \
                ancestor chain still in-place.",
            );

            let child_shrunk = child.prune(subpath);
            if child_shrunk {
                let children: &mut u16 = &mut self.header_mut().children;
                *children = children.checked_sub(1).unwrap();

                if let NodeMut::Node48(n48) = self.deref_mut() {
                    n48.key_hashes[byte as usize] = None;
                }
            }
        }

        self.shrink_to_fit()
    }

    const fn is_none(&self) -> bool {
        self.0 == TAG_NONE
    }

    fn take(&mut self) -> Option<TwigNode> {
        let us = self.0;
        self.0 = 0;

        match us & TAG_MASK {
            TAG_NONE => None,
            TAG_VALUE => {
                let ptr: *mut TwigNode = if size_of::<TwigNode>() > 0 {
                    (us & PTR_MASK) as *mut TwigNode
                } else {
                    std::ptr::NonNull::dangling().as_ptr()
                };
                let boxed: Box<TwigNode> = unsafe { Box::from_raw(ptr) };
                Some(*boxed)
            }
            _ => unreachable!(),
        }
    }

    fn header_mut(&mut self) -> &mut NodeHeader {
        match self.deref_mut() {
            NodeMut::Node1(n1) => &mut n1.header,
            NodeMut::Node4(n4) => &mut n4.header,
            NodeMut::Node16(n16) => &mut n16.header,
            NodeMut::Node48(n48) => &mut n48.header,
            NodeMut::Node256(n256) => &mut n256.header,
            _ => unreachable!(),
        }
    }

    fn child(&self, byte: u8) -> Option<&NodePtr> {
        match self.deref() {
            NodeRef::Node1(n1) => n1.child(byte),
            NodeRef::Node4(n4) => n4.child(byte),
            NodeRef::Node16(n16) => n16.child(byte),
            NodeRef::Node48(n48) => n48.child(byte),
            NodeRef::Node256(n256) => n256.child(byte),
            NodeRef::None => None,
            NodeRef::Value(_) => unreachable!(),
        }
    }

    const fn header(&self) -> &NodeHeader {
        match self.deref() {
            NodeRef::Node1(n1) => &n1.header,
            NodeRef::Node4(n4) => &n4.header,
            NodeRef::Node16(n16) => &n16.header,
            NodeRef::Node48(n48) => &n48.header,
            NodeRef::Node256(n256) => &n256.header,
            NodeRef::None => &NONE_HEADER,
            NodeRef::Value(twig) => &twig.header,
        }
    }

    fn prefix(&self) -> &[u8] {
        let header = self.header();
        &header.path[..header.path_len as usize]
    }

    fn truncate_prefix(&mut self, partial_path: &[u8]) {
        #[cfg(test)]
        println!("truncating prefix");
        // expand path at shared prefix
        #[cfg(test)]
        println!(
            "chopping off a prefix at node {:?} since our partial path is {:?}",
            self.header(),
            partial_path
        );
        let prefix = self.prefix();

        let shared_bytes = partial_path
            .iter()
            .zip(prefix.iter())
            .take_while(|(a, b)| a == b)
            .count();

        #[cfg(test)]
        println!(
            "truncated node has path of len {} with a reduction of {}",
            shared_bytes,
            prefix.len() - shared_bytes
        );
        let mut new_node4: Box<Node4> = Box::default();
        new_node4.header.path[..shared_bytes].copy_from_slice(&prefix[..shared_bytes]);
        new_node4.header.path_len = u8::try_from(shared_bytes).unwrap();

        let new_node = NodePtr::node4(new_node4);

        assert!(prefix.starts_with(new_node.prefix()));

        let mut old_cursor = std::mem::replace(self, new_node);

        let old_cursor_header = old_cursor.header_mut();
        let old_cursor_new_child_byte = old_cursor_header.path[shared_bytes];

        // we add +1 because we must account for the extra byte
        // reduced from the node's fan-out itself.
        old_cursor_header.path.rotate_left(shared_bytes + 1);
        old_cursor_header.path_len = old_cursor_header
            .path_len
            .checked_sub(u8::try_from(shared_bytes + 1).unwrap())
            .unwrap();

        let (_, child) = self
            .child_mut(old_cursor_new_child_byte, true, false)
            .unwrap();
        *child = old_cursor;
        child.assert_size();

        self.header_mut().children = 1;
    }

    const fn len(&self) -> usize {
        self.header().children as usize
    }

    fn assert_size(&self) {
        debug_assert_eq!(
            {
                let slots: &[NodePtr] = match self.deref() {
                    NodeRef::Node1(_) => {
                        debug_assert_eq!(self.len(), 1);
                        return;
                    }
                    NodeRef::Node4(n4) => &n4.slots,
                    NodeRef::Node16(n16) => &n16.slots,
                    NodeRef::Node48(n48) => &n48.slots,
                    NodeRef::Node256(n256) => &n256.slots,
                    _ => &[],
                };
                slots.iter().filter(|s| !s.is_none()).count()
            },
            self.len(),
        )
    }

    const fn is_full(&self) -> bool {
        match self.deref() {
            NodeRef::Node1(_) => 1 == self.len(),
            NodeRef::Node4(_) => 4 == self.len(),
            NodeRef::Node16(_) => 16 == self.len(),
            NodeRef::Node48(_) => 48 == self.len(),
            NodeRef::Node256(_) => 256 == self.len(),
            _ => unreachable!(),
        }
    }

    fn upgrade(&mut self) {
        let old_header = *self.header();
        let mut swapped = std::mem::take(self);
        *self = match swapped.deref_mut() {
            NodeMut::Node1(n1) => NodePtr::node4(n1.upgrade()),
            NodeMut::Node4(n4) => NodePtr::node16(n4.upgrade()),
            NodeMut::Node16(n16) => NodePtr::node48(n16.upgrade()),
            NodeMut::Node48(n48) => NodePtr::node256(n48.upgrade()),
            NodeMut::Node256(_) => unreachable!(),
            NodeMut::None => unreachable!(),
            NodeMut::Value(_) => unreachable!(),
        };
        *self.header_mut() = old_header;
    }

    fn node_iter<'a>(&'a self) -> NodeIter<'a> {
        let children: Box<dyn 'a + DoubleEndedIterator<Item = (Option<u8>, &'a NodePtr)>> =
            match self.deref() {
                NodeRef::Node1(n1) => Box::new(n1.iter()),
                NodeRef::Node4(n4) => Box::new(n4.iter()),
                NodeRef::Node16(n16) => Box::new(n16.iter()),
                NodeRef::Node48(n48) => Box::new(n48.iter()),
                NodeRef::Node256(n256) => Box::new(n256.iter()),

                // this is only an iterator over nodes, not leaf values
                NodeRef::None => Box::new([].into_iter()),
                NodeRef::Value(_) => Box::new([].into_iter()),
            };

        NodeIter {
            node: self,
            children,
        }
    }

    fn child_mut(
        &mut self,
        byte: u8,
        is_add: bool,
        clear_child_index: bool,
    ) -> Option<(&mut u16, &mut NodePtr)> {
        // TODO this is gross
        if self.child(byte).is_none() {
            if !is_add {
                return None;
            }
            if self.is_full() {
                self.upgrade()
            }
        }

        Some(match self.deref_mut() {
            NodeMut::Node1(n1) => n1.child_mut(byte),
            NodeMut::Node4(n4) => n4.child_mut(byte),
            NodeMut::Node16(n16) => n16.child_mut(byte),
            NodeMut::Node48(n48) => n48.child_mut(byte, clear_child_index),
            NodeMut::Node256(n256) => n256.child_mut(byte),
            NodeMut::None => unreachable!(),
            NodeMut::Value(_) => unreachable!(),
        })
    }
}

impl Drop for NodePtr {
    fn drop(&mut self) {
        match self.0 & TAG_MASK {
            TAG_NONE => {}
            TAG_VALUE => {
                let ptr: *mut TwigNode = if size_of::<TwigNode>() > 0 {
                    (self.0 & PTR_MASK) as *mut TwigNode
                } else {
                    std::ptr::NonNull::dangling().as_ptr()
                };
                drop(unsafe { Box::from_raw(ptr) });
            }
            TAG_1 => {
                let ptr: *mut Node1 = (self.0 & PTR_MASK) as *mut Node1;
                drop(unsafe { Box::from_raw(ptr) });
            }
            TAG_4 => {
                let ptr: *mut Node4 = (self.0 & PTR_MASK) as *mut Node4;
                drop(unsafe { Box::from_raw(ptr) });
            }
            TAG_16 => {
                let ptr: *mut Node16 = (self.0 & PTR_MASK) as *mut Node16;
                drop(unsafe { Box::from_raw(ptr) });
            }
            TAG_48 => {
                let ptr: *mut Node48 = (self.0 & PTR_MASK) as *mut Node48;
                drop(unsafe { Box::from_raw(ptr) });
            }
            TAG_256 => {
                let ptr: *mut Node256 = (self.0 & PTR_MASK) as *mut Node256;
                drop(unsafe { Box::from_raw(ptr) });
            }
            _ => unreachable!(),
        }
    }
}

impl Default for NodePtr {
    fn default() -> NodePtr {
        NodePtr::none()
    }
}

impl Clone for NodePtr {
    fn clone(&self) -> NodePtr {
        match self.deref() {
            NodeRef::Node1(n1) => NodePtr::node1(Box::new(n1.clone())),
            NodeRef::Node4(n4) => NodePtr::node4(Box::new(n4.clone())),
            NodeRef::Node16(n16) => NodePtr::node16(Box::new(n16.clone())),
            NodeRef::Node48(n48) => NodePtr::node48(Box::new(n48.clone())),
            NodeRef::Node256(n256) => NodePtr::node256(Box::new(n256.clone())),
            NodeRef::None => NodePtr::default(),
            NodeRef::Value(v) => NodePtr::value(v.clone()),
        }
    }
}

struct NodeIter<'a> {
    node: &'a NodePtr,
    children: Box<dyn 'a + DoubleEndedIterator<Item = (Option<u8>, &'a NodePtr)>>,
}

#[derive(Clone, Default, Copy, PartialEq, Debug)]
struct NodeHeader {
    path: [u8; MAX_PATH_COMPRESSION_BYTES],
    path_len: u8,
    children: u16,
    version: u64,
}

#[derive(Clone, Default)]
struct Node1 {
    header: NodeHeader,
    key: u8,
    slot: NodePtr,
}

impl Node1 {
    fn iter<'a>(&'a self) -> impl DoubleEndedIterator<Item = (Option<u8>, &NodePtr)> {
        std::iter::once((Some(self.key), &self.slot))
    }

    const fn child(&self, byte: u8) -> Option<&NodePtr> {
        if self.key == byte && !self.slot.is_none() {
            Some(&self.slot)
        } else {
            None
        }
    }

    fn child_mut(&mut self, byte: u8) -> (&mut u16, &mut NodePtr) {
        assert!(byte == self.key || self.slot.is_none());
        self.key = byte;
        (&mut self.header.children, &mut self.slot)
    }

    fn upgrade(&mut self) -> Box<Node4> {
        let mut n4: Box<Node4> = Box::default();
        n4.keys[0] = Some(self.key);
        std::mem::swap(&mut self.slot, &mut n4.slots[0]);
        n4
    }
}

#[derive(Clone)]
struct Node4 {
    header: NodeHeader,
    keys: [Option<u8>; 4],
    slots: [NodePtr; 4],
}

impl Default for Node4 {
    fn default() -> Node4 {
        Node4 {
            header: Default::default(),
            keys: [None; 4],
            slots: [
                NodePtr::none(),
                NodePtr::none(),
                NodePtr::none(),
                NodePtr::none(),
            ],
        }
    }
}

impl Node4 {
    fn iter<'a>(&'a self) -> impl DoubleEndedIterator<Item = (Option<u8>, &NodePtr)> {
        let mut pairs: [(Option<u8>, &NodePtr); 4] = [
            (self.keys[0], &self.slots[0]),
            (self.keys[1], &self.slots[1]),
            (self.keys[2], &self.slots[2]),
            (self.keys[3], &self.slots[3]),
        ];

        pairs.sort_unstable_by_key(|(k, _)| *k);

        pairs.into_iter().filter(|(_, n)| !n.is_none())
    }

    fn free_slot(&self) -> Option<usize> {
        self.slots.iter().position(NodePtr::is_none)
    }

    fn child(&self, byte: u8) -> Option<&NodePtr> {
        for idx in 0..4 {
            match self.keys[idx] {
                Some(key) => {
                    if key == byte && !self.slots[idx].is_none() {
                        return Some(&self.slots[idx]);
                    }
                }
                None => continue,
            }
        }
        None
    }

    fn child_mut(&mut self, byte: u8) -> (&mut u16, &mut NodePtr) {
        let idx_opt = self
            .keys
            .iter()
            .position(|i| *i == Some(byte))
            .and_then(|idx| {
                if !self.slots[idx].is_none() {
                    Some(idx)
                } else {
                    None
                }
            });
        if let Some(idx) = idx_opt {
            (&mut self.header.children, &mut self.slots[idx])
        } else {
            let free_slot = self.free_slot().unwrap();
            self.keys[free_slot] = Some(byte);
            (&mut self.header.children, &mut self.slots[free_slot])
        }
    }

    fn upgrade(&mut self) -> Box<Node16> {
        let mut n16: Box<Node16> = Box::default();
        for (slot, byte) in self.keys.iter().enumerate() {
            std::mem::swap(&mut self.slots[slot], &mut n16.slots[slot]);
            n16.keys[slot] = *byte;
        }
        n16
    }

    fn downgrade(&mut self) -> Box<Node1> {
        let mut n1: Box<Node1> = Box::default();
        let mut dst_idx = 0;

        for (slot, byte) in self.keys.iter().enumerate() {
            if !self.slots[slot].is_none() {
                std::mem::swap(&mut self.slots[slot], &mut n1.slot);
                n1.key = byte.unwrap();
                dst_idx += 1;
            }
        }

        assert_eq!(dst_idx, 1);

        n1
    }
}

#[derive(Clone)]
struct Node16 {
    header: NodeHeader,
    keys: [Option<u8>; 16],
    slots: [NodePtr; 16],
}

impl Default for Node16 {
    fn default() -> Node16 {
        Node16 {
            header: Default::default(),
            keys: [None; 16],
            slots: std::array::from_fn::<NodePtr, 16, _>(|_| NodePtr::none()),
        }
    }
}

impl Node16 {
    fn iter<'a>(&'a self) -> impl DoubleEndedIterator<Item = (Option<u8>, &NodePtr)> {
        let mut pairs: [(Option<u8>, &NodePtr); 16] = [
            (self.keys[0], &self.slots[0]),
            (self.keys[1], &self.slots[1]),
            (self.keys[2], &self.slots[2]),
            (self.keys[3], &self.slots[3]),
            (self.keys[4], &self.slots[4]),
            (self.keys[5], &self.slots[5]),
            (self.keys[6], &self.slots[6]),
            (self.keys[7], &self.slots[7]),
            (self.keys[8], &self.slots[8]),
            (self.keys[9], &self.slots[9]),
            (self.keys[10], &self.slots[10]),
            (self.keys[11], &self.slots[11]),
            (self.keys[12], &self.slots[12]),
            (self.keys[13], &self.slots[13]),
            (self.keys[14], &self.slots[14]),
            (self.keys[15], &self.slots[15]),
        ];

        pairs.sort_unstable_by_key(|(k, _)| *k);

        pairs.into_iter().filter(|(_, n)| !n.is_none())
    }

    fn free_slot(&self) -> Option<usize> {
        self.slots.iter().position(NodePtr::is_none)
    }

    fn child(&self, byte: u8) -> Option<&NodePtr> {
        for idx in 0..16 {
            if self.keys[idx] == Some(byte) && !self.slots[idx].is_none() {
                return Some(&self.slots[idx]);
            }
        }
        None
    }

    fn child_mut(&mut self, byte: u8) -> (&mut u16, &mut NodePtr) {
        let idx_opt = self
            .keys
            .iter()
            .position(|i| *i == Some(byte))
            .and_then(|idx| {
                if !self.slots[idx].is_none() {
                    Some(idx)
                } else {
                    None
                }
            });
        if let Some(idx) = idx_opt {
            (&mut self.header.children, &mut self.slots[idx])
        } else {
            let free_slot = self.free_slot().unwrap();
            self.keys[free_slot] = Some(byte);
            (&mut self.header.children, &mut self.slots[free_slot])
        }
    }

    fn upgrade(&mut self) -> Box<Node48> {
        let mut n48: Box<Node48> = Box::default();
        for (slot, byte) in self.keys.iter().enumerate() {
            if !self.slots[slot].is_none() {
                std::mem::swap(&mut self.slots[slot], &mut n48.slots[slot]);
                assert_eq!(n48.key_hashes[byte.unwrap() as usize], None);
                n48.key_hashes[byte.unwrap() as usize] = u8::try_from(slot).ok();
            }
        }
        n48
    }

    fn downgrade(&mut self) -> Box<Node4> {
        let mut n4: Box<Node4> = Box::default();
        let mut dst_idx = 0;

        for (slot, byte) in self.keys.iter().enumerate() {
            if !self.slots[slot].is_none() {
                std::mem::swap(&mut self.slots[slot], &mut n4.slots[dst_idx]);
                n4.keys[dst_idx] = *byte;
                dst_idx += 1;
            }
        }

        assert_eq!(dst_idx, 4);

        n4
    }
}

#[derive(Clone)]
struct Node48 {
    header: NodeHeader,
    key_hashes: [Option<u8>; 256],
    slots: [NodePtr; 48],
}

impl Default for Node48 {
    fn default() -> Node48 {
        Node48 {
            header: Default::default(),
            key_hashes: [None; 256],
            slots: std::array::from_fn::<NodePtr, 48, _>(|_| NodePtr::none()),
        }
    }
}

impl Node48 {
    fn iter<'a>(&'a self) -> impl DoubleEndedIterator<Item = (Option<u8>, &NodePtr)> {
        self.key_hashes
            .iter()
            .enumerate()
            .filter(|(_, i)| **i != None && !self.slots[i.unwrap() as usize].is_none())
            .map(|(c, i)| (u8::try_from(c).ok(), &self.slots[i.unwrap() as usize]))
    }

    fn free_slot(&self) -> Option<usize> {
        self.slots.iter().position(NodePtr::is_none)
    }

    const fn child(&self, byte: u8) -> Option<&NodePtr> {
        let idx = self.key_hashes[byte as usize];
        match idx {
            Some(i) => {
                if self.slots[i as usize].is_none() {
                    None
                } else {
                    Some(&self.slots[i as usize])
                }
            }
            None => None,
        }
    }

    fn child_mut(&mut self, byte: u8, clear_child_index: bool) -> (&mut u16, &mut NodePtr) {
        let idx = self.key_hashes[byte as usize];

        match idx {
            None => {
                let free_slot = self.free_slot().unwrap();
                if !clear_child_index {
                    self.key_hashes[byte as usize] = u8::try_from(free_slot).ok();
                }
                (&mut self.header.children, &mut self.slots[free_slot])
            }
            Some(i) => {
                if clear_child_index {
                    self.key_hashes[byte as usize] = None;
                }
                (&mut self.header.children, &mut self.slots[i as usize])
            }
        }
    }

    fn upgrade(&mut self) -> Box<Node256> {
        let mut n256: Box<Node256> = Box::default();

        for (byte, idx) in self.key_hashes.iter().enumerate() {
            if let Some(i) = idx {
                assert!(!self.slots[*i as usize].is_none());
                std::mem::swap(&mut n256.slots[byte], &mut self.slots[*i as usize]);
            }
        }

        n256
    }

    fn downgrade(&mut self) -> Box<Node16> {
        let mut n16: Box<Node16> = Box::default();
        let mut dst_idx = 0;

        for (byte, idx) in self.key_hashes.iter().enumerate() {
            if let Some(i) = idx {
                assert!(!self.slots[*i as usize].is_none());
                std::mem::swap(&mut self.slots[*i as usize], &mut n16.slots[dst_idx]);
                n16.keys[dst_idx] = u8::try_from(byte).ok();
                dst_idx += 1;
            }
        }

        assert_eq!(dst_idx, 16);

        n16
    }
}

#[derive(Clone)]
struct Node256 {
    header: NodeHeader,
    /*
    TODO:
    Add aggregates in the inner nodes instead.
    Should yield more predictable behavior.
    Something along the lines:

    Rust:
        ``aggregates: [SegmentArrayPtr, 256]``

    Where `SegmentArrayPtr` is a pointer to a new data structure,
    which should be used as a Segment Tree for the following metrics:
    `avg(), count(), max(), min(), sum(), group_concat()`
    respecting the types that make sense for each metric (of course).

    Segments should be of a deterministic size: 0-255, 256-511, 512-1023, 1024-2047

    */
    slots: [NodePtr; 256],
}

impl Default for Node256 {
    fn default() -> Self {
        Node256 {
            header: Default::default(),
            slots: std::array::from_fn::<NodePtr, 256, _>(|_| NodePtr::none()),
        }
    }
}

impl Node256 {
    fn iter<'a>(&'a self) -> impl DoubleEndedIterator<Item = (Option<u8>, &NodePtr)> {
        self.slots
            .iter()
            .enumerate()
            .filter(move |(_, slot)| !slot.is_none())
            .map(|(c, slot)| (u8::try_from(c).ok(), slot))
    }

    const fn child(&self, byte: u8) -> Option<&NodePtr> {
        if self.slots[byte as usize].is_none() {
            None
        } else {
            Some(&self.slots[byte as usize])
        }
    }

    fn child_mut(&mut self, byte: u8) -> (&mut u16, &mut NodePtr) {
        let slot = &mut self.slots[byte as usize];
        (&mut self.header.children, slot)
    }

    fn downgrade(&mut self) -> Box<Node48> {
        let mut n48: Box<Node48> = Box::default();
        let mut dst_idx = 0;

        for (byte, slot) in self.slots.iter_mut().enumerate() {
            if !slot.is_none() {
                std::mem::swap(slot, &mut n48.slots[dst_idx]);
                n48.key_hashes[byte] = u8::try_from(dst_idx).ok();
                dst_idx += 1;
            }
        }

        assert_eq!(dst_idx, 48);

        n48
    }
}

#[derive(Debug, Clone, PartialEq)]
struct HeapPtr(usize);

impl HeapPtr {
    fn disk_ptr(disk: Box<HeapDiskPtr>) -> HeapPtr {
        let ptr: *mut HeapDiskPtr = Box::into_raw(disk);
        let us = ptr as usize;
        assert_eq!(us & HEAP_TAG_DISK, 0);
        HeapPtr(us | HEAP_TAG_DISK)
    }
}

struct HeapPage {
    page_header: u64,
    payload: [u8; 4000],
    next_payload: Option<HeapPtr>,
}

#[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
struct HeapDiskPtr {
    block_offset: u64,
    byte_offset: u64,
}

impl HeapDiskPtr {}

enum HeapRef<'page> {
    Mem(&'page HeapPage),
    Disk(&'page HeapDiskPtr),
}

enum HeapMut<'page> {
    Mem(&'page mut HeapPage),
    Disk(&'page mut HeapDiskPtr),
}

#[derive(Debug, Clone, PartialEq)]
struct LeafNode {
    version: u64,
    doc: HeapPtr,
    ts: u64,
}

impl LeafNode {
    pub fn new(version: u64, doc: HeapPtr, ts: u64) -> LeafNode {
        LeafNode { version, doc, ts }
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd, Copy)]
enum TwigKey {
    // This should implement all SQL types, since they should be
    // the way you determine a collumns type.
    Null,
    Bool,
    String,
    Integer,
    Float,
}

impl From<&serde_json::Value> for TwigKey {
    fn from(value: &serde_json::Value) -> Self {
        match value {
            Value::Null => TwigKey::Null,
            Value::Bool(_) => TwigKey::Bool,
            Value::String(_) => TwigKey::String,
            Value::Number(n) => {
                if n.is_f64() {
                    TwigKey::Float
                } else {
                    TwigKey::Integer
                }
            }
            _ => unreachable!(),
        }
    }
}

#[repr(align(8))]
#[derive(Clone, PartialEq, Debug)]
pub struct TwigNode {
    header: NodeHeader,
    key_type: TwigKey,
    leafs: [Option<LeafNode>; 256],
    n_leafs: u8,
}

impl TwigNode {
    fn new(header: NodeHeader, leaf: LeafNode, key: Value) -> Self {
        let mut new = TwigNode {
            header,
            key_type: TwigKey::from(&key),
            leafs: std::array::from_fn(|_| Option::None),
            n_leafs: 255u8,
        };
        new.leafs[0] = Some(leaf);
        new
    }

    fn checked_add(&mut self, leaf: LeafNode, key: Value) -> Result<Option<LeafNode>> {
        // Leafs are organized in a way that most recent
        // entries should be accessed first.
        //
        // The idea is: when searching all most recent results
        // should be found first.
        if std::mem::discriminant(&self.key_type) != std::mem::discriminant(&TwigKey::from(&key)) {
            return Err(Error::ConflictingTwigTypes {
                origin: self.key_type,
                added: TwigKey::from(&key),
            });
        }
        self.n_leafs -= 1;
        let mut old: Option<LeafNode> = None;
        if self.n_leafs > 0 {
            old = std::mem::replace(&mut self.leafs[self.n_leafs as usize], Some(leaf));
        }
        Ok(old)
    }

    fn force_add(&mut self, key: Value, leaf: LeafNode) {
        todo!()
    }
}

/*

#[cfg(test)]
mod test {
    use super::{Art, NodeHeader, TwigNode};

    #[test]
    fn basic() {
        let mut art = Art::new();
        art.insert(
            &vec![5, 2, 3, 0b0],
            TwigNode::new(NodeHeader::default(), String::from("T1")),
        );

        art.insert(
            &vec![7, 21, 4, 0b0],
            TwigNode::new(NodeHeader::default(), String::from("T2")),
        );

        art.insert(
            &vec![5, 2, 0b0],
            TwigNode::new(NodeHeader::default(), String::from("T3")),
        );

        art.insert(
            &vec![5, 2, 3, 25, 0b0],
            TwigNode::new(NodeHeader::default(), String::from("T4")),
        );

        assert_eq!(art.len(), 4);

        art.insert(
            &vec![2, 255, 0b0],
            TwigNode::new(NodeHeader::default(), String::from("T5")),
        );

        art.insert(
            &vec![0],
            TwigNode::new(NodeHeader::default(), String::from("T0")),
        );

        assert_eq!(art.len(), 6);

        art.insert(
            &vec![2, 255, 0b0],
            TwigNode::new(NodeHeader::default(), String::from("T5")),
        );

        art.insert(
            &vec![0],
            TwigNode::new(NodeHeader::default(), String::from("T0")),
        );

        assert_eq!(art.len(), 6);
    }

    #[test]
    fn regression_01() {
        let mut art: Art = Art::new();

        assert_eq!(
            art.insert(
                &[0, 0, 0],
                TwigNode::new(NodeHeader::default(), String::from("Test"))
            ),
            None
        );
        assert_eq!(
            art.insert(
                &[0, 11, 0],
                TwigNode::new(NodeHeader::default(), String::from("Test"))
            ),
            None
        );
        assert_eq!(
            art.insert(
                &[0, 0, 0],
                TwigNode::new(NodeHeader::default(), String::from("Test"))
            ),
            Some(TwigNode::new(NodeHeader::default(), String::from("Test")))
        );

        let it = art.root_as_ref().node_iter();
        for n in it.children {
            println!("test: {:?}", n);
        }

        /*         assert_eq!(
            art.iter().collect::<Vec<_>>(),
            vec![([0, 0, 0], &2), ([0, 11, 0], &1),]
        ); */
    }
}
*/

//#[test]
/* fn regression_00() {
    let mut art: Art = Art::new();

    art.insert(&[37], 38);
    art.insert([0], 1);
    assert_eq!(art.len(), 2);

    art.insert([5], 5);
    art.insert([1], 9);
    art.insert([0], 0);
    art.insert([255], 255);
    art.insert([0], 0);
    art.insert([47], 0);
    art.insert([253], 37);
    assert_eq!(art.len(), 7);

    art.insert([10], 0);
    art.insert([38], 28);
    art.insert([24], 28);
    assert_eq!(art.len(), 10);

    art.insert([28], 30);
    art.insert([30], 30);
    art.insert([28], 15);
    art.insert([51], 48);
    art.insert([53], 255);
    art.insert([59], 58);
    art.insert([58], 58);
    assert_eq!(art.len(), 16);
    assert_eq!(art.remove(&[85]), None);
    assert_eq!(art.len(), 16);
    art.insert([30], 30);
    art.insert([30], 0);
    art.insert([30], 0);
    assert_eq!(art.len(), 16);
    art.insert([143], 254);
    assert_eq!(art.len(), 17);
    art.insert([30], 30);
    assert_eq!(art.len(), 17);
    assert_eq!(art.len(), 17);
    assert_eq!(art.remove(&[85]), None);
    assert_eq!(art.len(), 17);
}

#[test]
fn regression_01() {
    let mut art: Art<u8, 3> = Art::new();

    assert_eq!(art.insert([0, 0, 0], 0), None);
    assert_eq!(art.insert([0, 11, 0], 1), None);
    assert_eq!(art.insert([0, 0, 0], 2), Some(0));

    assert_eq!(
        art.iter().collect::<Vec<_>>(),
        vec![([0, 0, 0], &2), ([0, 11, 0], &1),]
    );
}

#[test]
fn regression_02() {
    let mut art = Art::new();
    art.insert([1, 1, 1], 1);
    art.remove(&[2, 2, 2]);
    art.insert([0, 0, 0], 5);
    assert_eq!(
        art.iter().collect::<Vec<_>>(),
        vec![([0, 0, 0], &5), ([1, 1, 1], &1),]
    );
}

#[test]
fn regression_03() {
    fn expand(k: [u8; 4]) -> [u8; 11] {
        let mut ret = [0; 11];

        ret[0] = k[0];
        ret[5] = k[2];
        ret[10] = k[3];

        let mut b = k[1];
        // byte at index 0 is k[0]
        for i in 1..5 {
            if b.leading_zeros() == 0 {
                ret[i] = 255;
            }
            b = b.rotate_left(1);
        }
        // byte at index 5 is k[2]
        for i in 6..10 {
            if b.leading_zeros() == 0 {
                ret[i] = 255;
            }
            b = b.rotate_left(1);
        }
        // byte at index 10 is k[3]

        ret
    }

    let mut art = Art::new();
    art.insert(expand([1, 173, 33, 255]), 255);
    art.insert(expand([255, 20, 255, 223]), 223);

    let start = expand([223, 223, 223, 223]);
    let end = expand([255, 255, 255, 255]);
    let v = art.range(start..end).count();
    assert_eq!(v, 1);
}

#[test]
fn regression_04() {
    let mut art = Art::new();

    art.insert([], 0);

    assert_eq!(art.get(&[]), Some(&0));
    assert_eq!(art.remove(&[]), Some(0));
    assert_eq!(art.get(&[]), None);

    art.insert([], 3);

    assert_eq!(art.iter().count(), 1);
}

#[test]
fn regression_05() {
    let mut art = Art::new();

    let k = [0; 2];
    art.insert(k, 0);
    assert_eq!(art.remove(&k), Some(0));

    assert!(art.root.is_none());
}

#[test]
fn regression_06() {
    let mut art = Art::new();

    let max = u16::MAX as u32 + 1;

    for i in 0..max {
        let k = i.to_be_bytes();
        art.insert(k, 0);
    }

    for i in 0..max {
        let k = i.to_be_bytes();
        art.remove(&k);
    }

    assert!(art.root.is_none());
}

#[test]
fn regression_07() {
    fn run<T: Default>() {
        let _ = [([], Default::default())]
            .into_iter()
            .collect::<Art<(), 0>>();
    }
    run::<()>();
    run::<u8>();
    run::<u16>();
    run::<u32>();
    run::<u64>();
    run::<usize>();
    run::<String>();
    run::<Vec<usize>>();
} */
