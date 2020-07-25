# var_byte_str

## Description
Make a gaps represent of `&str` then compress it by using variable bytes encoding approach. The implementation is inspired by [this gap article](https://nlp.stanford.edu/IR-book/html/htmledition/postings-file-compression-1.html) and [this article](https://nlp.stanford.edu/IR-book/html/htmledition/variable-byte-codes-1.html) from stanford. 

## Rationale
The main idea is that represent Thai string with UTF-8 is expensive. It took 3 bytes to represent a character. Since most of the time, the cluster of text usually come from the same language and Thai language can be represent within single byte, it'd be efficient to store text by using gap approach then compress it using variable byte encoding technique.

The challenge is that the gap encoding is usually done on ordered document id but the stream of character is unordered. It cannot be represent by unsigned int. The problem is, with unsigned int, how to efficiently represent it with minimal number of byte ? This is challenging because consider this text `"หก"`. It is `0x0E2B` follow by `0x0E01`. The gap is `-42`. The direct subtract between two code points result in following bit value `0b11111111_11111111_11111111_11010110`. If we treat it the same way as original algorithm, it will end up require 4 bytes to represent this. We can attempt to encode sign bit directly into byte but it will consume one more bit slot. The original algorithm already consume one bit slot for flagging the last byte of gap. If we goes this path, it mean that we only have 6 available bit per bytes. It mean that many english text will end up taking two bytes per character. For example `"incredibly small"`. The gap between `y` and ` ` and `s` will be `-89` and `83`. Since we will only have 6 bits available per byte. 1 byte will capable of represent only up to `63`. We will need two bytes.

The solution I choose, is to store it as absolute value and store sign flag on `bitvec`. Now, -89 can be stored by 1 bytes + 1 bit.

The cost of using one extra `bitvec` instead of single `Vec<u8>` is one more pointer and two more `usize`. In 64 bits system, it will take 24 more bytes. The total bytes to represent literally empty text is 48 bytes.

Thus if text is short, encode it this way will only result in more bytes needed to store it.

## How to use
Put following line into `cargo.toml`
```toml
var_byte_str="*"
```
or if you need to serialize/deserialize the encoded string, put following line into `cargo.toml`
```toml
var_byte_str={version="*", default=false, features=["serialize"]}
```
1. Encode string then print it
```rust
use var_byte_str::VarByteString;
let original = "Some really long text and may contains some different language like \"คำภาษาไทยที่ใช้พื้นที่เยอะกว่าเนื้อความภาษาอังกฤษเสียอีก\".";
let encoded = VarByteString::from(original);
println!("The text is {}", encoded);
println!("Internal structure is {:?}", encoded);
// Remember that the original is a slice to UTF-8 encoded bytes. It have 16 bytes overhead.
// The encoded one have 24 bytes overhead.
println!("UTF-8 took {} bytes while encoded took {} bytes", original.len() + 16, encoded.len() + 48);
```
2. Encode string and sometime later, decode it.
```rust
use var_byte_str::VarByteString;
let original = "Some really long text and may contains some different language like \"คำภาษาไทยที่ใช้พื้นที่เยอะกว่าเนื้อความภาษาอังกฤษเสียอีก\".";
let encoded = VarByteString::from(original);
let decoded: String = encoded.into();
assert_eq!(original, decoded);
```
3. Iterate through encoded string to obtain current byte representation underneath
```rust
use var_byte_str::VarByteString;
let original = "Some really long text and may contains some different language like \"คำภาษาไทยที่ใช้พื้นที่เยอะกว่าเนื้อความภาษาอังกฤษเสียอีก\".";
let encoded = VarByteString::from(original);
encoded.gaps_bytes().take(11).for_each(|(sign, bytes)| {
    // some operation on obtained sign and `SmallVec<[u8;5]>` object.
})
```
4. Iterate through encoded string to obtain `"gap"` of each char
```rust
use var_byte_str::VarByteString;
let original = "Some really long text and may contains some different language like \"คำภาษาไทยที่ใช้พื้นที่เยอะกว่าเนื้อความภาษาอังกฤษเสียอีก\".";
let encoded = VarByteString::from(original);
encoded.gaps().take(11).for_each(|gap| {
    // some operation on gap
})
```
Note: you don't actually need to encode it first. You can actually use `chars` method on `&str` to calculate `"gap"` by yourself like this:
```rust
let chars = original.chars();
let first_chars = chars.next().unwrap();
chars.fold(first_chars as i64, |prev, ch| {
    let ch = ch as i64;
    let gap = ch - prev;
    // Do something with gap
    ch 
}) ;
```
However, if you already use `VarByteString`, it will save you some line of code by simply using method `gaps`

5. Iterate through encoded string to obtain some char
```rust
use var_byte_str::VarByteString;
let original = "Some really long text and may contains some different language like \"คำภาษาไทยที่ใช้พื้นที่เยอะกว่าเนื้อความภาษาอังกฤษเสียอีก\".";
let encoded = VarByteString::from(original);
encoded.chars().take(11).for_each(|gap| {
    // some operation on char
})
```