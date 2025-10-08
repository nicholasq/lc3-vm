/// Represents a ROM (Read-Only Memory) structure that holds 16-bit data.
///
/// The `Rom` struct is designed to store a vector of 16-bit unsigned integers (`u16`),
/// which can be used to represent the contents of a ROM image in memory.
pub struct Rom {
    /// A vector containing the 16-bit data of the ROM.
    pub data: Vec<u16>,
}

impl Rom {
    /// Constructs a `Rom` instance from a given ROM image represented as a vector of bytes.
    ///
    /// This method takes a vector of 8-bit unsigned integers (`Vec<u8>`) as input, where each
    /// pair of bytes represents a single 16-bit value in big-endian format. The method converts
    /// these byte pairs into 16-bit unsigned integers and stores them in the `data` field of the
    /// `Rom` struct.
    ///
    /// # Arguments
    ///
    /// * `image` - A vector of bytes (`Vec<u8>`) representing the ROM image. The length of the
    ///   vector must be a multiple of 2, as each 16-bit value is constructed from two bytes.
    ///
    /// # Returns
    ///
    /// A new instance of the `Rom` struct containing the 16-bit data extracted from the input
    /// byte vector.
    ///
    /// # Example
    ///
    /// ```
    /// use crate::rom::Rom;
    ///
    /// let image = vec![0x12, 0x34, 0x56, 0x78];
    /// let rom = Rom::from_image(image);
    ///
    /// assert_eq!(rom.data, vec![0x1234, 0x5678]);
    /// ```
    pub fn from_image(image: Vec<u8>) -> Self {
        let mut u16_vec = Vec::new();
        for chunk in image.chunks_exact(2) {
            let arr = [chunk[0], chunk[1]];
            u16_vec.push(u16::from_be_bytes(arr));
        }
        Rom { data: u16_vec }
    }
}
