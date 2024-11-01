use std::ffi::CStr;

#[repr(align(8))]
#[derive(Clone, Debug, PartialEq)]
pub struct BlockOffset(u32, u16);

pub struct OffsetPtr(usize);


// ToDo: Usar Cstr strings porque elas sao terminadas em um NULL byte o que facilita o uso
// dentro da ART. Nos terminados em NULL em teoria nao precisao ser expandidos
#[cfg(test)]
mod test {
    use storekey::{encode, decode};

    #[test]
    fn test1() {
        use std::ffi::CString;

        let i = CString::new(String::from("Testando")).expect("Failed!");
        let encode = encode::serialize(&String::from("Testando-possivel-chave")).unwrap();
        let decode: &str = decode::deserialize(&encode).unwrap();
        print!("{:?}", decode);
    }
}