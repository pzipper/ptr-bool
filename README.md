# ptr-bool
tl;dr: a pointer and boolean with the same size as a pointer.

A convenience crate used to bitpack a boolean and pointer into the same eight bytes (four on 32-bit systems, two on 16-bit systems).  This is done by storing the boolean in the one-bit of a two-aligned pointer.

Usually a pointer and a boolean would be padded to be 16 bytes together, while this method allows the pointer and boolean to fit inside of 8 bytes.

This project was inspired by the [rust-gc](https://github.com/Manishearth/rust-gc) project, which used this method for garbage collected references.  I saw the method and thought that this was incredibly smart, so I created my own version with some convenience wrapping and made its own crate.

## Caveats
* The pointer must be aligned by two to ensure that the one-bit is unnecessary and can be used to stored the boolean value.

* Possibly a slight overhead when reading the values of the `PtrBool`, as the boolean value must be omitted from the pointer *each time it's read*, and the pointer value must be omitted from the boolean value each time it is read.  That is, unless there is some sort of unknown optimization built into Rust for the case of storing a boolean in one bit.

* The value stored inside of a `PtrBool` must be `Sized`.  This is because the pointer is converted to and from a `usize`; which loses any metadata which would have been in the raw pointer.