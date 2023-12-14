use std::mem::size_of;

use crate::offsets::PageOffset;
 
const TAG_NONE: usize = 0b000;
const TAG_VALUE: usize = 0b001;
const TAG_1: usize = 0b010;
const TAG_4: usize = 0b011;
const TAG_16: usize = 0b100;
const TAG_48: usize = 0b101;
const TAG_256: usize = 0b110;
const TAG_MASK: usize = 0b111;
const PTR_MASK: usize = usize::MAX - TAG_MASK;

#[derive(Clone)]
pub struct Art {
    len: usize,
    root: NodePtr
}

impl Default for Art {
    fn default() -> Art {
        Art {
            len: 0,
            root: NodePtr::none(),
        }
    }
}

impl Art {
    pub const fn new() -> Art {
        Art {
            len: 0,
            root: NodePtr::none(),
        }
    }

    pub const fn len(&self) -> usize {
        self.len
    }

    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }
}


enum NodeRef<'a> {
    None,
    Value(&'a PageOffset),
    Node1(&'a Node1),
    Node4(&'a Node4),
    Node16(&'a Node16),
    Node48(&'a Node48),
    Node256(&'a Node256) 
}

enum NodeMut<'a> {
    None,
    Value(&'a mut PageOffset),
    Node1(&'a mut Node1),
    Node4(&'a mut Node4),
    Node16(&'a mut Node16),
    Node48(&'a mut Node48),
    Node256(&'a mut Node256),
}

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

    fn value(offset: PageOffset) -> NodePtr {
        let bx = Box::new(offset);
        let ptr: *mut PageOffset = Box::into_raw(bx);
        let us = ptr as usize;
        if size_of::<PageOffset>() > 0 {
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
                let ptr: *const PageOffset = if size_of::<PageOffset>() > 0 {
                    (self.0 & PTR_MASK) as *const PageOffset
                } else {
                    std::ptr::NonNull::dangling().as_ptr()
                };
                let reference: &PageOffset = unsafe { &(*ptr) };
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
                let ptr: *mut PageOffset = if size_of::<PageOffset>() > 0 {
                    (self.0 & PTR_MASK) as *mut PageOffset 
                } else {
                    std::ptr::NonNull::dangling().as_ptr()
                };
                let reference: &mut PageOffset = unsafe { &mut (*ptr) };
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
    
    const fn is_none(&self) -> bool {
        self.0 == TAG_NONE
    }

    fn take(&mut self) -> Option<PageOffset> {
        let us = self.0;
        self.0 = 0;

        match us & TAG_MASK {
            TAG_NONE => None,
            TAG_VALUE => {
                let ptr: *mut PageOffset = if size_of::<PageOffset>() > 0 {
                    (us & PTR_MASK) as *mut PageOffset 
                } else {
                    std::ptr::NonNull::dangling().as_ptr()
                };
                let boxed: Box<PageOffset> = unsafe { Box::from_raw(ptr) };
                Some(*boxed)
            }
            _ => unreachable!(),
        }
    }

}


impl Drop for NodePtr {
    fn drop(&mut self) {
        match self.0 & TAG_MASK {
            TAG_NONE => {}
            TAG_VALUE => {
                let ptr: *mut PageOffset = if size_of::<PageOffset>() > 0 {
                        (self.0 & PTR_MASK) as *mut PageOffset 
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

#[derive(Clone)]
struct NodeHeader {
    prefix: Vec<u8>,
    children: u16,
}

#[derive(Clone)]
struct Node1 {
    header: NodeHeader,
    key: Option<u8>,
    slots: NodePtr
}

#[derive(Clone)]
struct Node4 {
    header: NodeHeader,
    keys: [Option<u8>; 4],
    slots: [NodePtr; 4]
}

#[derive(Clone)]
struct Node16 {
    header: NodeHeader,
    key: [Option<u8>; 16],
    slots: [NodePtr; 16]
}

#[derive(Clone)]
struct Node48 {
    header: NodeHeader,
    key_hashes: [Option<u8>; 256],
    slots: [NodePtr; 48]
}

#[derive(Clone)]
struct Node256 {
    header: NodeHeader,
    slots: [NodePtr; 256]
}