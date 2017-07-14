//! Provides `bstr` and `BString` byte string types
//!
//! These types have a relationship similar to the standard types
//! [`str`][str] and [`String`][string].
//!
//! [str]: https://doc.rust-lang.org/std/primitive.str.html
//! [string]: https://doc.rust-lang.org/std/string/struct.String.html

use std::borrow::{Borrow, Cow};
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::iter::FromIterator;
use std::mem::{forget, transmute};
use std::ops::{self, Range, RangeFrom, RangeFull, RangeTo};
use std::ptr;
use std::slice;
use std::str::{from_utf8, from_utf8_unchecked, Utf8Error};
use std::string::FromUtf8Error;

use ref_slice::{ref_slice, ref_slice_mut};

use from_bstr::FromBStr;
use pattern::{Pattern, Searcher, ReverseSearcher, DoubleEndedSearcher};

/// A growable byte string of unknown encoding.
///
/// It is analogous to the standard [`String`][string] type.
///
/// Its borrowed slice counterpart is the [`bstr`][bstr] type.
///
/// [bstr]: struct.bstr.html
/// [string]: https://doc.rust-lang.org/std/string/struct.String.html
#[derive(Clone, Default, Hash)]
pub struct BString {
    bytes: Vec<u8>,
}

impl BString {
    /// Creates a new empty `BString`.
    #[inline]
    pub fn new() -> BString {
        BString{bytes: Vec::new()}
    }

    /// Creates a new empty `BString` with the given capacity.
    #[inline]
    pub fn with_capacity(n: usize) -> BString {
        BString{bytes: Vec::with_capacity(n)}
    }

    /// Returns a concatenated `BString` consisting of the given `bstr` values.
    ///
    /// # Examples
    ///
    /// ```
    /// use bstring::BString;
    ///
    /// assert_eq!(BString::concat(&["hello", "world"]), "helloworld");
    /// ```
    #[inline]
    pub fn concat<S: AsRef<bstr>>(strs: &[S]) -> BString {
        let len = strs.iter().map(|s| s.as_ref().len()).sum::<usize>();
        let mut bs = BString::with_capacity(len);

        for s in strs {
            bs.push_str(s);
        }

        bs
    }

    /// Returns a `BString` consisting of the given `bstr` values,
    /// joined together with the given separator.
    ///
    /// # Examples
    ///
    /// ```
    /// use bstring::BString;
    ///
    /// assert_eq!(BString::join(" ", &["hello", "world"]), "hello world");
    /// ```
    #[inline]
    pub fn join<Sep: AsRef<bstr>, S: AsRef<bstr>>(sep: Sep, strs: &[S]) -> BString {
        if strs.is_empty() {
            return BString::new();
        }

        let sep_len = sep.as_ref().len();
        let cat_len = strs.iter()
            .map(|s| s.as_ref().len()).sum::<usize>();
        let total_len = cat_len + sep_len * (strs.len() - 1);

        let mut first = true;
        let mut bs = BString::with_capacity(total_len);

        for s in strs {
            if !first {
                bs.push_str(sep.as_ref());
            }

            bs.push_str(s);
            first = false;
        }

        bs
    }

    /// Creates a new `BString` from a pointer, length, and capacity.
    ///
    /// # Safety
    ///
    /// This is unsafe due to a number of invariants that are not checked:
    ///
    /// * The memory at `ptr` needs to have been previously allocated by the
    ///   same allocator the standard library uses.
    /// * `length` needs to be less than or equal to `capacity`.
    /// * `capacity` needs to be the correct value.
    pub unsafe fn from_raw_parts(ptr: *mut u8, length: usize, capacity: usize) -> BString {
        BString{bytes: Vec::from_raw_parts(ptr, length, capacity)}
    }

    /// Returns a borrowed `&bstr` slice containing the entire string.
    #[inline]
    pub fn as_bstr(&self) -> &bstr {
        self.as_ref()
    }

    /// Returns a mutable `&bstr` slice containing the entire string.
    #[inline]
    pub fn as_mut_bstr(&mut self) -> &mut bstr {
        self.as_mut()
    }

    /// Returns a mutable reference to the internal `Vec<u8>`.
    ///
    /// This method is safe because `BString` does not enforce any invariants
    /// over the content of its buffer. Any otherwise safe modifications may
    /// be made to the returned `Vec`.
    #[inline]
    pub fn as_mut_vec(&mut self) -> &mut Vec<u8> {
        &mut self.bytes
    }

    /// Consumes the `BString` and returns the internal `Vec<u8>`.
    #[inline]
    pub fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }

    /// Attempts to the convert the `BString` into a `String`.
    ///
    /// If the byte string does not contain valid UTF-8 data,
    /// an error is returned.
    #[inline]
    pub fn into_string(self) -> Result<String, FromUtf8Error> {
        String::from_utf8(self.bytes)
    }

    /// Appends bytes from a given byte string to this buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// use bstring::BString;
    ///
    /// let mut bs = BString::from("Rebecca");
    ///
    /// bs.push_str(" Bunch");
    ///
    /// assert_eq!(bs, "Rebecca Bunch");
    /// ```
    #[inline]
    pub fn push_str<S: AsRef<bstr>>(&mut self, s: S) {
        self.bytes.extend(s.as_ref().as_bytes());
    }

    /// Returns the capacity of this `BString`, in bytes.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.bytes.capacity()
    }

    /// Ensures that the `BString` capacity is at least `additional` bytes
    /// greater than its current length.
    ///
    /// # Panics
    ///
    /// If the new capacity overflows `usize`.
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.bytes.reserve(additional);
    }

    /// Ensures that the `BString` capacity is exactly `additional` bytes
    /// greater than its length.
    ///
    /// # Panics
    ///
    /// If the new the capacity overflows `usize`.
    #[inline]
    pub fn reserve_exact(&mut self, additional: usize) {
        self.bytes.reserve_exact(additional);
    }

    /// Shrinks the capacity of the `BString` to match its length.
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.bytes.shrink_to_fit();
    }

    /// Appends the given byte to end of this `BString`.
    #[inline]
    pub fn push(&mut self, b: u8) {
        self.bytes.push(b);
    }

    /// Shortens the `BString` to the given length.
    ///
    /// If `new_len` is greater than its current length, this has no effect.
    ///
    /// This method does not affect the allocated capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use bstring::BString;
    ///
    /// let mut bs = BString::from("Josh Chan");
    ///
    /// bs.truncate(4);
    ///
    /// assert_eq!(bs, "Josh");
    /// ```
    #[inline]
    pub fn truncate(&mut self, new_len: usize) {
        self.bytes.truncate(new_len);
    }

    /// Removes and returns the last byte of the string.
    ///
    /// Returns `None` if the string is empty.
    #[inline]
    pub fn pop(&mut self) -> Option<u8> {
        self.bytes.pop()
    }

    /// Removes and returns the byte at the position `idx`.
    ///
    /// # Panics
    ///
    /// If `idx` is greater than or equal to the current length.
    #[inline]
    pub fn remove(&mut self, idx: usize) -> u8 {
        self.bytes.remove(idx)
    }

    /// Retains only the elements that satisfy the given predicate.
    ///
    /// In other words, removes all elements for which `f(&e)` return `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bstring::BString;
    ///
    /// let mut bs = BString::from("pretzel");
    ///
    /// bs.retain(|&b| b != b'e');
    ///
    /// assert_eq!(bs, "prtzl");
    /// ```
    #[inline]
    pub fn retain<F: FnMut(&u8) -> bool>(&mut self, f: F) {
        self.bytes.retain(f);
    }

    /// Inserts the given byte at position `idx`.
    #[inline]
    pub fn insert(&mut self, idx: usize, b: u8) {
        self.bytes.insert(idx, b);
    }

    /// Inserts a byte string at position `idx`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bstring::BString;
    ///
    /// let mut bs = BString::from("Covina");
    ///
    /// bs.insert_str(0, "West ");
    ///
    /// assert_eq!(bs, "West Covina");
    /// ```
    #[inline]
    pub fn insert_str<S: AsRef<bstr>>(&mut self, idx: usize, s: S) {
        self.insert_bytes(idx, s.as_ref().as_bytes());
    }

    fn insert_bytes(&mut self, idx: usize, bytes: &[u8]) {
        let len = self.len();
        let amt = bytes.len();

        self.bytes.reserve(amt);

        unsafe {
            ptr::copy(self.bytes.as_ptr().offset(idx as isize),
                self.bytes.as_mut_ptr().offset((idx + amt) as isize),
                len - idx);
            ptr::copy(bytes.as_ptr(),
                self.bytes.as_mut_ptr().offset(idx as isize),
                amt);
            self.bytes.set_len(len + amt);
        }
    }

    /// Splits the `BString` into two at the given index.
    ///
    /// Returns a newly allocated `BString`. `self` contains bytes `[0, at)`
    /// and the returned `BString` contains bytes `[at, len)`.
    ///
    /// The capacity of `self` is not affected.
    ///
    /// # Panics
    ///
    /// If `at` is greater than the current length.
    #[inline]
    pub fn split_off(&mut self, at: usize) -> BString {
        self.bytes.split_off(at).into()
    }

    /// Truncates this `BString`, removing all contents.
    ///
    /// The `BString` will have a length of zero, but its capacity will be
    /// unaffected.
    #[inline]
    pub fn clear(&mut self) {
        self.bytes.clear();
    }

    /// Converts this `BString` into a `Box<bstr>`.
    ///
    /// This will drop any excess capacity.
    #[inline]
    pub fn into_boxed_bstr(self) -> Box<bstr> {
        unsafe { transmute(self.bytes.into_boxed_slice()) }
    }
}

impl ops::Deref for BString {
    type Target = bstr;

    fn deref(&self) -> &bstr {
        self.as_ref()
    }
}

impl ops::DerefMut for BString {
    fn deref_mut(&mut self) -> &mut bstr {
        self.as_mut()
    }
}

impl<'a> From<&'a str> for &'a bstr {
    fn from(s: &str) -> &bstr {
        s.as_ref()
    }
}

impl<'a> From<&'a [u8]> for &'a bstr {
    fn from(s: &[u8]) -> &bstr {
        s.as_ref()
    }
}

impl<'a> From<&'a str> for BString {
    fn from(s: &str) -> BString {
        s.to_owned().into()
    }
}

impl<'a> From<&'a [u8]> for BString {
    fn from(s: &[u8]) -> BString {
        s.to_owned().into()
    }
}

impl<'a> From<&'a bstr> for BString {
    fn from(s: &bstr) -> BString {
        s.to_owned()
    }
}

impl From<String> for BString {
    fn from(s: String) -> BString {
        s.into_bytes().into()
    }
}

impl From<Vec<u8>> for BString {
    fn from(v: Vec<u8>) -> BString {
        BString{bytes: v}
    }
}

/// Byte string slice of unknown encoding.
///
/// It is analogous to the standard [`str`][str] type.
///
/// Its owned counterpart is the [`BString`][bstring] type.
///
/// [bstring]: struct.BString.html
/// [str]: https://doc.rust-lang.org/std/primitive.str.html
#[allow(non_camel_case_types)]
pub struct bstr {
    bytes: [u8],
}

impl bstr {
    /// Creates a new `&bstr` slice from a pointer and length.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given
    /// pointer is valid for `length` bytes, nor whether the the lifetime
    /// inferred is a suitable lifetime for the returned slice.
    pub unsafe fn from_raw_parts<'a>(ptr: *const u8, length: usize) -> &'a bstr {
        transmute(slice::from_raw_parts(ptr, length))
    }

    /// Creates a new `&mut bstr` slice from a pointer and length.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given
    /// pointer is valid for `length` bytes, nor whether the the lifetime
    /// inferred is a suitable lifetime for the returned slice.
    pub unsafe fn from_raw_parts_mut<'a>(ptr: *mut u8, len: usize) -> &'a mut bstr {
        transmute(slice::from_raw_parts_mut(ptr, len))
    }

    /// Returns the length of the string, in bytes.
    #[inline]
    pub fn len(&self) -> usize {
        self.bytes.len()
    }

    /// Returns whether the string is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.bytes.is_empty()
    }

    /// Returns a borrowed reference to the internal byte slice.
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Returns a mutable reference to the internal byte slice.
    #[inline]
    pub fn as_mut_bytes(&mut self) -> &mut [u8] {
        &mut self.bytes
    }

    /// Returns a raw pointer to the contained buffer.
    #[inline]
    pub fn as_ptr(&self) -> *const u8 {
        self.bytes.as_ptr()
    }

    /// Returns a raw mutable pointer to the contained buffer.
    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        self.bytes.as_mut_ptr()
    }

    /// Returns a newly allocated `BString` buffer for the 
    #[inline]
    pub fn to_bstring(&self) -> BString {
        self.to_owned()
    }

    /// Attempts to convert the byte string to a `str` slice.
    ///
    /// If the byte string does not contain valid UTF-8, an error is returned.
    #[inline]
    pub fn to_str(&self) -> Result<&str, Utf8Error> {
        from_utf8(self.as_bytes())
    }

    /// Converts the byte string to a `str` slice.
    ///
    /// # Safety
    ///
    /// The byte string is assumed to contain valid UTF-8.
    pub unsafe fn to_str_unchecked(&self) -> &str {
        from_utf8_unchecked(self.as_bytes())
    }

    /// Converts the byte string a `String`.
    ///
    /// During this conversion, any invalid UTF-8 sequences will be replaced
    /// with `U+FFFD REPLACEMENT CHARACTER`, which looks like this �
    #[inline]
    pub fn to_string_lossy(&self) -> Cow<str> {
        String::from_utf8_lossy(self.as_bytes())
    }

    /// Returns an object that implements `Display` for safely printing
    /// byte strings that may contain non-UTF-8 data.
    #[inline]
    pub fn display(&self) -> Display {
        Display{bs: self}
    }

    /// Returns the byte at the given index.
    ///
    /// Returns `None` if `idx` is greater than or equal to the string length.
    #[inline]
    pub fn get(&self, idx: usize) -> Option<&u8> {
        // TODO: Use SliceIndex when it becomes stable
        self.bytes.get(idx)
    }

    /// Returns the byte at the given index, bypassing bounds-checking.
    ///
    /// # Safety
    ///
    /// The caller of this function must guarantee that `idx` is less than
    /// the byte string length.
    pub unsafe fn get_unchecked(&self, idx: usize) -> &u8 {
        // TODO: Use SliceIndex when it becomes stable
        self.bytes.get_unchecked(idx)
    }

    /// Returns a subslice of this byte string, bypassing bounds-checking.
    ///
    /// # Safety
    ///
    /// The caller of this function must guarantee that:
    ///
    /// * `start` is less than or equal to `end`
    /// * `end` is less than or equal to the byte string length
    pub unsafe fn slice_unchecked(&self, start: usize, end: usize) -> &bstr {
        self.bytes.get_unchecked(start..end).as_ref()
    }

    /// Returns a mutable subslice of this byte string, bypassing bounds-checking.
    ///
    /// # Safety
    ///
    /// The caller of this function must guarantee that:
    ///
    /// * `start` is less than or equal to `end`
    /// * `end` is less than or equal to the byte string length
    pub unsafe fn slice_mut_unchecked(&mut self, start: usize, end: usize) -> &mut bstr {
        self.bytes.get_unchecked_mut(start..end).as_mut()
    }

    /// Returns a borrowed reference to the first byte in the string.
    ///
    /// Returns `None` if the byte string is empty.
    #[inline]
    pub fn first(&self) -> Option<&u8> {
        self.bytes.first()
    }

    /// Returns a mutable reference to the first byte in the string.
    ///
    /// Returns `None` if the byte string is empty.
    #[inline]
    pub fn first_mut(&mut self) -> Option<&mut u8> {
        self.bytes.first_mut()
    }

    /// Returns a borrowed reference to the last byte in the string.
    ///
    /// Returns `None` if the byte string is empty.
    #[inline]
    pub fn last(&self) -> Option<&u8> {
        self.bytes.last()
    }

    /// Returns a mutable reference to the last byte in the string.
    ///
    /// Returns `None` if the byte string is empty.
    #[inline]
    pub fn last_mut(&mut self) -> Option<&mut u8> {
        self.bytes.last_mut()
    }

    /// Returns an iterator over the bytes of this string.
    ///
    /// The element type of the returned iterator is `&u8`.
    #[inline]
    pub fn iter(&self) -> Iter {
        Iter{iter: self.bytes.iter()}
    }

    /// Returns a mutable iterator over the bytes of this string.
    ///
    /// The element type of the returned iterator is `&mut u8`.
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut {
        IterMut{iter: self.bytes.iter_mut()}
    }

    /// Returns an iterator over the lines of this byte string.
    ///
    /// Lines may end with either a newline (`\n`)
    /// or a carriage return followed by a line feed (`\r\n`).
    ///
    /// Yielded subslices will not contain the line ending.
    #[inline]
    pub fn lines(&self) -> Lines {
        Lines{bytes: self}
    }

    /// Returns a subslice with leading and trailing whitespace removed.
    #[inline]
    pub fn trim(&self) -> &bstr {
        self.trim_matches(|b| (b as char).is_whitespace())
    }

    /// Returns a subslice with leading whitespace removed.
    #[inline]
    pub fn trim_left(&self) -> &bstr {
        self.trim_left_matches(|b| (b as char).is_whitespace())
    }

    /// Returns a subslice with trailing whitespace removed.
    #[inline]
    pub fn trim_right(&self) -> &bstr {
        self.trim_right_matches(|b| (b as char).is_whitespace())
    }

    /// Returns a subslice with all matching prefixes and suffixes removed.
    #[inline]
    pub fn trim_matches<'a, P: Pattern<'a>>(&'a self, pat: P) -> &bstr
            where P::Searcher: DoubleEndedSearcher<'a> {
        let mut i = 0;
        let mut j = 0;
        let mut matcher = pat.into_searcher(self);

        if let Some((a, b)) = matcher.next_reject() {
            i = a;
            j = b;
        }

        if let Some((_, b)) = matcher.next_reject_back() {
            j = b;
        }

        &self[i..j]
    }

    /// Returns a subslice with all matching prefixes removed.
    #[inline]
    pub fn trim_left_matches<'a, P: Pattern<'a>>(&'a self, pat: P) -> &bstr {
        let mut i = self.len();
        let mut matcher = pat.into_searcher(self);

        if let Some((a, _)) = matcher.next_reject() {
            i = a;
        }

        &self[i..]
    }

    /// Returns a subslice with all matching suffixes removed.
    #[inline]
    pub fn trim_right_matches<'a, P: Pattern<'a>>(&'a self, pat: P) -> &bstr
            where P::Searcher: ReverseSearcher<'a> {
        let mut j = 0;
        let mut matcher = pat.into_searcher(self);

        if let Some((_, b)) = matcher.next_reject_back() {
            j = b;
        }

        &self[..j]
    }

    /// Partitions the string using the given pattern.
    ///
    /// The string is searched for the given pattern. If it is found,
    /// two subslices are returned: The portion of the string before the matching
    /// substring and the portion occurring after it.
    ///
    /// # Examples
    ///
    /// ```
    /// use bstring::bstr;
    ///
    /// let bs = <&bstr>::from("foo=bar=baz");
    ///
    /// let (a, b) = bs.partition(b'=').unwrap();
    ///
    /// assert_eq!(a, "foo");
    /// assert_eq!(b, "bar=baz");
    /// ```
    #[inline]
    pub fn partition<'a, P: Pattern<'a>>(&'a self, pat: P) -> Option<(&'a bstr, &'a bstr)> {
        pat.into_searcher(self).next_match().map(
            |(start, end)| (&self[..start], &self[end..]))
    }

    /// Partitions the string using the given pattern, searching from the end.
    ///
    /// The string is searched for the given pattern, starting from the end.
    /// If it is found, two subslices are returned: The portion of the string
    /// before the matching substring and the portion occurring after it.
    ///
    /// # Examples
    ///
    /// ```
    /// use bstring::bstr;
    ///
    /// let bs = <&bstr>::from("foo=bar=baz");
    ///
    /// let (a, b) = bs.rpartition(b'=').unwrap();
    ///
    /// assert_eq!(a, "foo=bar");
    /// assert_eq!(b, "baz");
    /// ```
    #[inline]
    pub fn rpartition<'a, P: Pattern<'a>>(&'a self, pat: P) -> Option<(&'a bstr, &'a bstr)>
            where P::Searcher: ReverseSearcher<'a> {
        pat.into_searcher(self).next_match_back().map(
            |(start, end)| (&self[..start], &self[end..]))
    }

    /// Returns an iterator of subslices of this string, separated by a pattern.
    #[inline]
    pub fn split<'a, P: Pattern<'a>>(&'a self, pat: P) -> Split<'a, P> {
        Split(SplitInternal{
            start: 0,
            end: self.len(),
            matcher: pat.into_searcher(self),
            allow_trailing_empty: true,
            finished: false,
        })
    }

    /// Returns a reverse iterator of subslices of this string, separated by a pattern.
    #[inline]
    pub fn rsplit<'a, P: Pattern<'a>>(&'a self, pat: P) -> RSplit<'a, P> {
        RSplit(self.split(pat).0)
    }

    /// Returns an iterator of subslices of this string, separated by a pattern,
    /// limited to at most `count` items.
    ///
    /// If `count` items are returned, the last item will contain the remainder
    /// of the string.
    #[inline]
    pub fn splitn<'a, P: Pattern<'a>>(&'a self, count: usize, pat: P) -> SplitN<'a, P> {
        SplitN(SplitNInternal{
            iter: self.split(pat).0,
            count: count,
        })
    }

    /// Returns a reverse iterator of subslices of this string,
    /// separated by a pattern, limited to at most `count` items.
    ///
    /// If `count` items are returned, the last item will contain the remainder
    /// of the string.
    #[inline]
    pub fn rsplitn<'a, P: Pattern<'a>>(&'a self, count: usize, pat: P)
            -> RSplitN<'a, P>
            where P::Searcher: ReverseSearcher<'a> {
        RSplitN(self.splitn(count, pat).0)
    }

    /// Returns an iterator of subslices of this string, separated by a pattern.
    ///
    /// Equivalent to `split`, except that the final subslice is skipped if
    /// it is empty.
    #[inline]
    pub fn split_terminator<'a, P: Pattern<'a>>(&'a self, pat: P) -> SplitTerminator<'a, P> {
        SplitTerminator(SplitInternal{
            allow_trailing_empty: false,
            .. self.split(pat).0
        })
    }

    /// Returns a reverse iterator of subslices of this string,
    /// separated by a pattern.
    ///
    /// Equivalent to `rsplit`, except that the final subslice is skipped if
    /// it is empty.
    #[inline]
    pub fn rsplit_terminator<'a, P: Pattern<'a>>(&'a self, pat: P)
            -> RSplitTerminator<'a, P>
            where P::Searcher: ReverseSearcher<'a> {
        RSplitTerminator(self.split_terminator(pat).0)
    }

    /// Returns an iterator of delimited words.
    ///
    /// This differs from `split` in that multiple occurances of a pattern
    /// will be considered as one.
    ///
    /// # Notes
    ///
    /// Unlike the other split methods, calling `split_words` on an empty
    /// string will result in an iterator yielding zero elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use bstring::bstr;
    ///
    /// let mut words = <&bstr>::from("   foo   bar   ").split_words(b' ');
    ///
    /// assert_eq!(words.next().unwrap(), "foo");
    /// assert_eq!(words.next().unwrap(), "bar");
    /// assert_eq!(words.next(), None);
    /// ```
    #[inline]
    pub fn split_words<'a, P: Pattern<'a>>(&'a self, pat: P) -> SplitWords<'a, P> {
        let mut sp = SplitWords{
            start: 0,
            matcher: pat.into_searcher(self),
            finished: false,
        };

        sp.init();
        sp
    }

    /// Returns an iterator over matches in the byte string.
    #[inline]
    pub fn matches<'a, P: Pattern<'a>>(&'a self, pat: P) -> Matches<'a, P> {
        Matches(MatchesInternal(pat.into_searcher(self)))
    }

    /// Returns a reverse iterator over matches in the byte string.
    #[inline]
    pub fn rmatches<'a, P: Pattern<'a>>(&'a self, pat: P) -> RMatches<'a, P> {
        RMatches(self.matches(pat).0)
    }

    /// Returns an iterator over matches in the byte string,
    /// including the index at which the match begins.
    #[inline]
    pub fn match_indices<'a, P: Pattern<'a>>(&'a self, pat: P) -> MatchIndices<'a, P> {
        MatchIndices(MatchIndicesInternal(pat.into_searcher(self)))
    }

    /// Returns a reverse iterator over matches in the byte string,
    /// including the index at which the match begins.
    #[inline]
    pub fn rmatch_indices<'a, P: Pattern<'a>>(&'a self, pat: P) -> RMatchIndices<'a, P> {
        RMatchIndices(self.match_indices(pat).0)
    }

    /// Returns the byte string divided into two at `mid`.
    ///
    /// # Panics
    ///
    /// If `mid` is beyond the end of the byte string.
    #[inline]
    pub fn split_at(&self, mid: usize) -> (&bstr, &bstr) {
        let (a, b) = self.bytes.split_at(mid);
        (a.as_ref(), b.as_ref())
    }

    /// Returns the byte string divided into two at `mid`.
    ///
    /// # Panics
    ///
    /// If `mid` is beyond the end of the byte string.
    #[inline]
    pub fn split_at_mut(&mut self, mid: usize) -> (&mut bstr, &mut bstr) {
        let (a, b) = self.bytes.split_at_mut(mid);
        (a.as_mut(), b.as_mut())
    }

    /// Returns the first byte and the rest,
    /// or `None` if the byte string is empty.
    #[inline]
    pub fn split_first(&self) -> Option<(&u8, &bstr)> {
        self.bytes.split_first().map(|(b, s)| (b, s.as_ref()))
    }

    /// Returns the first byte and the rest,
    /// or `None` if the byte string is empty.
    #[inline]
    pub fn split_first_mut(&mut self) -> Option<(&mut u8, &mut bstr)> {
        self.bytes.split_first_mut().map(|(b, s)| (b, s.as_mut()))
    }

    /// Returns the last byte and the rest,
    /// or `None` if the byte string is empty.
    #[inline]
    pub fn split_last(&self) -> Option<(&u8, &bstr)> {
        self.bytes.split_last().map(|(b, s)| (b, s.as_ref()))
    }

    /// Returns the last byte and the rest,
    /// or `None` if the byte string is empty.
    #[inline]
    pub fn split_last_mut(&mut self) -> Option<(&mut u8, &mut bstr)> {
        self.bytes.split_last_mut().map(|(b, s)| (b, s.as_mut()))
    }

    /// Returns whether the byte string contains the given pattern.
    #[inline]
    pub fn contains<'a, P: Pattern<'a>>(&'a self, pat: P) -> bool {
        pat.is_contained_in(self)
    }

    /// Returns whether the byte string starts with the given pattern.
    #[inline]
    pub fn starts_with<'a, P: Pattern<'a>>(&'a self, pat: P) -> bool {
        pat.is_prefix_of(self)
    }

    /// Returns whether the byte string ends with the given pattern.
    #[inline]
    pub fn ends_with<'a, P: Pattern<'a>>(&'a self, pat: P) -> bool
            where P::Searcher: ReverseSearcher<'a> {
        pat.is_suffix_of(self)
    }

    /// Returns the index of the first match of the given pattern.
    ///
    /// Returns `None` if there is no match.
    #[inline]
    pub fn find<'a, P: Pattern<'a>>(&'a self, pat: P) -> Option<usize> {
        pat.into_searcher(self).next_match().map(|(i, _)| i)
    }

    /// Returns the index of the first match of the given pattern,
    /// starting from the end.
    ///
    /// Returns `None` if there is no match.
    #[inline]
    pub fn rfind<'a, P: Pattern<'a>>(&'a self, pat: P) -> Option<usize>
            where P::Searcher: ReverseSearcher<'a> {
        pat.into_searcher(self).next_match_back().map(|(i, _)| i)
    }

    /// Returns a value parsed from the byte string,
    /// using the [`FromBStr`][from] trait
    ///
    /// [from]: ../from_bstr/trait.FromBStr.html
    #[inline]
    pub fn parse<F: FromBStr>(&self) -> Result<F, F::Err> {
        F::from_bstr(self)
    }

    /// Converts a `Box<bstr>` into a `BString`.
    #[inline]
    pub fn into_bstring(mut self: Box<bstr>) -> BString {
        let ptr = self.as_mut_ptr();
        let len = self.len();

        forget(self);
        unsafe { BString::from_raw_parts(ptr, len, len) }
    }
}

/// Utility struct that defines `std::fmt::Display` for a `&bstr`,
/// which may contain non-UTF-8 data.
pub struct Display<'a> {
    bs: &'a bstr,
}

impl<'a> fmt::Display for Display<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.bs.to_string_lossy(), f)
    }
}

impl<'a> fmt::Debug for Display<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.bs.to_string_lossy(), f)
    }
}

/// Iterator over bytes in a byte string.
#[derive(Clone, Debug)]
pub struct Iter<'a> {
    iter: slice::Iter<'a, u8>,
}

/// Mutable iterator over bytes in a byte string.
#[derive(Debug)]
pub struct IterMut<'a> {
    iter: slice::IterMut<'a, u8>,
}

impl<'a> Iter<'a> {
    /// Returns the remainder of the byte string.
    #[inline]
    pub fn as_bstr(&self) -> &'a bstr {
        self.iter.as_slice().as_ref()
    }
}

impl<'a> IterMut<'a> {
    /// Returns the remainder of the mutable byte string.
    #[inline]
    pub fn into_bstr(self) -> &'a mut bstr {
        self.iter.into_slice().as_mut()
    }
}

macro_rules! iterator {
    ( $name:ident , $elem:ty ) => {
        impl<'a> Iterator for $name<'a> {
            type Item = $elem;

            fn next(&mut self) -> Option<$elem> {
                self.iter.next()
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                self.iter.size_hint()
            }

            fn count(self) -> usize {
                self.iter.count()
            }

            fn nth(&mut self, n: usize) -> Option<$elem> {
                self.iter.nth(n)
            }

            fn last(self) -> Option<$elem> {
                self.iter.last()
            }

            fn all<F>(&mut self, predicate: F) -> bool
                    where F: FnMut(Self::Item) -> bool {
                self.iter.all(predicate)
            }

            fn any<F>(&mut self, predicate: F) -> bool
                    where F: FnMut(Self::Item) -> bool {
                self.iter.any(predicate)
            }

            fn find<F>(&mut self, predicate: F) -> Option<$elem>
                    where F: FnMut(&Self::Item) -> bool {
                self.iter.find(predicate)
            }

            fn position<P>(&mut self, predicate: P) -> Option<usize>
                    where P: FnMut(Self::Item) -> bool {
                self.iter.position(predicate)
            }

            fn rposition<P>(&mut self, predicate: P) -> Option<usize>
                    where P: FnMut(Self::Item) -> bool {
                self.iter.rposition(predicate)
            }
        }

        impl<'a> DoubleEndedIterator for $name<'a> {
            fn next_back(&mut self) -> Option<$elem> {
                self.iter.next_back()
            }

            /* Waiting for stabilization
            fn rfind<P>(&mut self, predicate: P) -> Option<$elem> {
                self.iter.rfind(predicate)
            }
            */
        }

        impl<'a> ExactSizeIterator for $name<'a> {}
    }
}

iterator!{ Iter, &'a u8 }
iterator!{ IterMut, &'a mut u8 }

/// Iterator over lines of a byte string.
pub struct Lines<'a> {
    bytes: &'a bstr,
}

impl<'a> Iterator for Lines<'a> {
    type Item = &'a bstr;

    fn next(&mut self) -> Option<&'a bstr> {
        if self.bytes.is_empty() {
            return None;
        }

        let end = match self.bytes.iter().position(|&b| b == b'\n') {
            Some(pos) => pos + 1,
            None => self.bytes.len()
        };

        let line = &self.bytes[..end];
        self.bytes = &self.bytes[end..];

        if line.ends_with("\r\n") {
            Some(&line[..end - 2])
        } else if line.ends_with("\n") {
            Some(&line[..end - 1])
        } else {
            Some(line)
        }
    }
}

macro_rules! generate_pattern_iterators {
    {
        forward:
            $(#[$forward_iterator_attribute:meta])*
            struct $forward_iterator:ident;

        reverse:
            $(#[$reverse_iterator_attribute:meta])*
            struct $reverse_iterator:ident;

        internal:
            $internal_iterator:ident yielding ($iterty:ty);

        delegate $($t:tt)*
    } => {
        $(#[$forward_iterator_attribute])*
        pub struct $forward_iterator<'a, P: Pattern<'a>>($internal_iterator<'a, P>);

        impl<'a, P: Pattern<'a>> fmt::Debug for $forward_iterator<'a, P>
                where P::Searcher: fmt::Debug {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                f.debug_tuple(stringify!($forward_iterator))
                    .field(&self.0)
                    .finish()
            }
        }

        impl<'a, P: Pattern<'a>> Iterator for $forward_iterator<'a, P> {
            type Item = $iterty;

            fn next(&mut self) -> Option<$iterty> {
                self.0.next()
            }
        }

        impl<'a, P: Pattern<'a>> Clone for $forward_iterator<'a, P>
                where P::Searcher: Clone {
            fn clone(&self) -> Self {
                $forward_iterator(self.0.clone())
            }
        }

        $(#[$reverse_iterator_attribute])*
        pub struct $reverse_iterator<'a, P: Pattern<'a>>($internal_iterator<'a, P>);

        impl<'a, P: Pattern<'a>> fmt::Debug for $reverse_iterator<'a, P>
                where P::Searcher: fmt::Debug {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                f.debug_tuple(stringify!($reverse_iterator))
                    .field(&self.0)
                    .finish()
            }
        }

        impl<'a, P: Pattern<'a>> Iterator for $reverse_iterator<'a, P>
                where P::Searcher: ReverseSearcher<'a> {
            type Item = $iterty;

            fn next(&mut self) -> Option<$iterty> {
                self.0.next_back()
            }
        }

        impl<'a, P: Pattern<'a>> Clone for $reverse_iterator<'a, P>
                where P::Searcher: Clone {
            fn clone(&self) -> Self {
                $reverse_iterator(self.0.clone())
            }
        }

        generate_pattern_iterators!($($t)*
            with $forward_iterator, $reverse_iterator, $iterty);
    };
    {
        double ended; with
            $forward_iterator:ident , $reverse_iterator:ident , $iterty:ty
    } => {
        impl<'a, P: Pattern<'a>> DoubleEndedIterator for $forward_iterator<'a, P>
                where P::Searcher: DoubleEndedSearcher<'a> {
            fn next_back(&mut self) -> Option<$iterty> {
                self.0.next_back()
            }
        }

        impl<'a, P: Pattern<'a>> DoubleEndedIterator for $reverse_iterator<'a, P>
                where P::Searcher: DoubleEndedSearcher<'a> {
            fn next_back(&mut self) -> Option<$iterty> {
                self.0.next_back()
            }
        }
    };
    {
        single ended; with
            $forward_iterator:ident , $reverse_iterator:ident , $iterty:ty
    } => {}
}

macro_rules! derive_pattern_clone {
    ( clone $name:ident with |$s:ident| $e:expr ) => {
        impl<'a, P: Pattern<'a>> Clone for $name<'a, P>
                where P::Searcher: Clone {
            fn clone(&self) -> Self {
                let $s = self;
                $e
            }
        }
    }
}

struct SplitInternal<'a, P: Pattern<'a>> {
    start: usize,
    end: usize,
    matcher: P::Searcher,
    allow_trailing_empty: bool,
    finished: bool,
}

derive_pattern_clone!{
    clone SplitInternal
    with |s| SplitInternal { matcher: s.matcher.clone(), .. *s }
}

impl<'a, P: Pattern<'a>> fmt::Debug for SplitInternal<'a, P>
        where P::Searcher: fmt::Debug {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("SplitInternal")
            .field("start", &self.start)
            .field("end", &self.end)
            .field("matcher", &self.matcher)
            .field("allow_trailing_empty", &self.allow_trailing_empty)
            .field("finished", &self.finished)
            .finish()
    }
}

impl<'a, P: Pattern<'a>> SplitInternal<'a, P> {
    fn get_end(&mut self) -> Option<&'a bstr> {
        if !self.finished && (self.allow_trailing_empty || self.end - self.start > 0) {
            self.finished = true;
            Some(&self.matcher.haystack()[self.start..self.end])
        } else {
            None
        }
    }

    fn next(&mut self) -> Option<&'a bstr> {
        if self.finished {
            return None;
        }

        let haystack = self.matcher.haystack();

        match self.matcher.next_match() {
            Some((a, b)) => {
                let elt = &haystack[self.start..a];
                self.start = b;
                Some(elt)
            }
            None => self.get_end()
        }
    }

    fn next_back(&mut self) -> Option<&'a bstr>
            where P::Searcher: ReverseSearcher<'a> {
        if self.finished {
            return None;
        }

        if !self.allow_trailing_empty {
            self.allow_trailing_empty = true;

            match self.next_back() {
                Some(elt) if !elt.is_empty() => return Some(elt),
                _ => if self.finished { return None; }
            }
        }

        let haystack = self.matcher.haystack();

        match self.matcher.next_match_back() {
            Some((a, b)) => {
                let elt = &haystack[b..self.end];
                self.end = a;
                Some(elt)
            }
            None => {
                self.finished = true;
                Some(&haystack[self.start..self.end])
            }
        }
    }
}

generate_pattern_iterators!{
    forward:
        /// Created with the method [`split`][split]
        ///
        /// [split]: struct.bstr.html#method.split
        struct Split;
    reverse:
        /// Created with the method [`rsplit`][rsplit]
        ///
        /// [rsplit]: struct.bstr.html#method.rsplit
        struct RSplit;
    internal:
        SplitInternal yielding (&'a bstr);
    delegate double ended;
}

generate_pattern_iterators!{
    forward:
        /// Created with the method [`split_terminator`][split_terminator]
        ///
        /// [split_terminator]: struct.bstr.html#method.split_terminator
        struct SplitTerminator;
    reverse:
        /// Created with the method [`rsplit_terminator`][rsplit_terminator]
        ///
        /// [rsplit_terminator]: struct.bstr.html#method.rsplit_terminator
        struct RSplitTerminator;
    internal:
        SplitInternal yielding (&'a bstr);
    delegate double ended;
}

struct SplitNInternal<'a, P: Pattern<'a>> {
    iter: SplitInternal<'a, P>,
    count: usize,
}

derive_pattern_clone!{
    clone SplitNInternal
    with |s| SplitNInternal { iter: s.iter.clone(), .. *s }
}

impl<'a, P: Pattern<'a>> fmt::Debug for SplitNInternal<'a, P>
        where P::Searcher: fmt::Debug {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("SplitNInternal")
            .field("iter", &self.iter)
            .field("count", &self.count)
            .finish()
    }
}

impl<'a, P: Pattern<'a>> SplitNInternal<'a, P> {
    fn next(&mut self) -> Option<&'a bstr> {
        match self.count {
            0 => None,
            1 => { self.count = 0; self.iter.get_end() }
            _ => { self.count -= 1; self.iter.next() }
        }
    }

    fn next_back(&mut self) -> Option<&'a bstr>
            where P::Searcher: ReverseSearcher<'a> {
        match self.count {
            0 => None,
            1 => { self.count = 0; self.iter.get_end() }
            _ => { self.count -= 1; self.iter.next_back() }
        }
    }
}

generate_pattern_iterators!{
    forward:
        /// Created with the method [`splitn`][splitn]
        ///
        /// [splitn]: struct.bstr.html#method.splitn
        struct SplitN;
    reverse:
        /// Created with the method [`rsplitn`][rsplitn]
        ///
        /// [rsplitn]: struct.bstr.html#method.rsplitn
        struct RSplitN;
    internal:
        SplitNInternal yielding (&'a bstr);
    delegate single ended;
}

struct MatchesInternal<'a, P: Pattern<'a>>(P::Searcher);

derive_pattern_clone!{
    clone MatchesInternal
    with |s| MatchesInternal(s.0.clone())
}

impl<'a, P: Pattern<'a>> fmt::Debug for MatchesInternal<'a, P>
        where P::Searcher: fmt::Debug {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_tuple("MatchesInternal")
            .field(&self.0)
            .finish()
    }
}

impl<'a, P: Pattern<'a>> MatchesInternal<'a, P> {
    fn next(&mut self) -> Option<&'a bstr> {
        self.0.next_match().map(|(a, b)| &self.0.haystack()[a..b])
    }

    fn next_back(&mut self) -> Option<&'a bstr>
            where P::Searcher: ReverseSearcher<'a> {
        self.0.next_match_back().map(|(a, b)| &self.0.haystack()[a..b])
    }
}

generate_pattern_iterators!{
    forward:
        /// Created with the method [`matches`][matches]
        ///
        /// [matches]: struct.bstr.html#method.matches
        struct Matches;
    reverse:
        /// Created with the method [`rmatches`][rmatches]
        ///
        /// [rmatches]: struct.bstr.html#method.rmatches
        struct RMatches;
    internal:
        MatchesInternal yielding (&'a bstr);
    delegate double ended;
}

struct MatchIndicesInternal<'a, P: Pattern<'a>>(P::Searcher);

derive_pattern_clone!{
    clone MatchIndicesInternal
    with |s| MatchIndicesInternal(s.0.clone())
}

impl<'a, P: Pattern<'a>> fmt::Debug for MatchIndicesInternal<'a, P>
        where P::Searcher: fmt::Debug {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_tuple("MatchIndicesInternal")
            .field(&self.0)
            .finish()
    }
}

impl<'a, P: Pattern<'a>> MatchIndicesInternal<'a, P> {
    fn next(&mut self) -> Option<(usize, &'a bstr)> {
        self.0.next_match().map(
            |(start, end)| (start, &self.0.haystack()[start..end]))
    }

    fn next_back(&mut self) -> Option<(usize, &'a bstr)>
            where P::Searcher: ReverseSearcher<'a> {
        self.0.next_match_back().map(
            |(start, end)| (start, &self.0.haystack()[start..end]))
    }
}

generate_pattern_iterators!{
    forward:
        /// Created with the method [`match_indices`][match_indices]
        ///
        /// [match_indices]: struct.bstr.html#method.match_indices
        struct MatchIndices;
    reverse:
        /// Created with the method [`rmatch_indices`][rmatch_indices]
        ///
        /// [rmatch_indices]: struct.bstr.html#method.rmatch_indices
        struct RMatchIndices;
    internal:
        MatchIndicesInternal yielding ((usize, &'a bstr));
    delegate double ended;
}

/// Created with the method [`split_words`][split_words]
///
/// [split_words]: struct.bstr.html#method.split_words
pub struct SplitWords<'a, P: Pattern<'a>> {
    start: usize,
    matcher: P::Searcher,
    finished: bool,
}

derive_pattern_clone!{
    clone SplitWords
    with |s| SplitWords { matcher: s.matcher.clone(), ..*s }
}

impl<'a, P: Pattern<'a>> fmt::Debug for SplitWords<'a, P>
        where P::Searcher: fmt::Debug {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("SplitWords")
            .field("start", &self.start)
            .field("matcher", &self.matcher)
            .field("finished", &self.finished)
            .finish()
    }
}

impl<'a, P: Pattern<'a>> SplitWords<'a, P> {
    /// Returns the remainder of the input string.
    #[inline]
    pub fn as_bstr(&self) -> &'a bstr {
        &self.matcher.haystack()[self.start..]
    }

    fn init(&mut self) {
        if let Some((a, _)) = self.matcher.next_reject() {
            self.start = a;
        } else {
            self.start = self.matcher.haystack().len();
            self.finished = true;
        }
    }
}

impl<'a, P: Pattern<'a>> Iterator for SplitWords<'a, P> {
    type Item = &'a bstr;

    fn next(&mut self) -> Option<&'a bstr> {
        if self.finished {
            return None;
        }

        let start = self.start;

        let end = match self.matcher.next_match() {
            Some((a, _)) => a,
            None => {
                self.finished = true;
                self.matcher.haystack().len()
            }
        };

        match self.matcher.next_reject() {
            Some((a, _)) => {
                self.start = a;
            }
            None => {
                self.start = self.matcher.haystack().len();
                self.finished = true;
            }
        }

        Some(&self.matcher.haystack()[start..end])
    }
}

impl AsRef<bstr> for u8 {
    fn as_ref(&self) -> &bstr {
        ref_slice(self).as_ref()
    }
}

impl AsRef<bstr> for [u8] {
    fn as_ref(&self) -> &bstr {
        unsafe { transmute(self) }
    }
}

impl AsRef<bstr> for str {
    fn as_ref(&self) -> &bstr {
        self.as_bytes().as_ref()
    }
}

impl AsRef<bstr> for String {
    fn as_ref(&self) -> &bstr {
        self.as_bytes().as_ref()
    }
}

impl AsRef<bstr> for Vec<u8> {
    fn as_ref(&self) -> &bstr {
        self[..].as_ref()
    }
}

impl<'a> AsRef<bstr> for Cow<'a, str> {
    fn as_ref(&self) -> &bstr {
        self.as_bytes().as_ref()
    }
}

impl AsRef<bstr> for bstr {
    fn as_ref(&self) -> &bstr {
        self
    }
}

impl AsRef<bstr> for BString {
    fn as_ref(&self) -> &bstr {
        self.bytes.as_ref()
    }
}

impl AsMut<bstr> for u8 {
    fn as_mut(&mut self) -> &mut bstr {
        ref_slice_mut(self).as_mut()
    }
}

impl AsMut<bstr> for [u8] {
    fn as_mut(&mut self) -> &mut bstr {
        unsafe { transmute(self) }
    }
}

impl AsMut<bstr> for bstr {
    fn as_mut(&mut self) -> &mut bstr {
        self
    }
}

impl AsMut<bstr> for BString {
    fn as_mut(&mut self) -> &mut bstr {
        self.bytes.as_mut()
    }
}

impl AsMut<bstr> for Vec<u8> {
    fn as_mut(&mut self) -> &mut bstr {
        self[..].as_mut()
    }
}

impl Borrow<bstr> for BString {
    fn borrow(&self) -> &bstr {
        self.as_ref()
    }
}

impl Borrow<bstr> for String {
    fn borrow(&self) -> &bstr {
        self.as_ref()
    }
}

impl Borrow<bstr> for Vec<u8> {
    fn borrow(&self) -> &bstr {
        self.as_ref()
    }
}

// Display isn't implemented directly for either BString or bstr because
// this method is lossy for non-UTF-8 data. Forcing the use of `.display()`
// prevents any accidents with `format!` and bstrings being used for non-logging
// purposes.

impl fmt::Debug for BString {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self[..], f)
    }
}

impl fmt::Debug for bstr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.to_string_lossy(), f)
    }
}

impl Hash for bstr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.bytes.hash(state);
    }
}

impl<'a> ops::Add<&'a bstr> for BString {
    type Output = Self;

    fn add(mut self, rhs: &bstr) -> Self {
        self.push_str(rhs);
        self
    }
}

impl<'a> ops::Add<&'a str> for BString {
    type Output = Self;

    fn add(mut self, rhs: &str) -> Self {
        self.push_str(rhs);
        self
    }
}

impl<'a> ops::Add<&'a [u8]> for BString {
    type Output = Self;

    fn add(mut self, rhs: &[u8]) -> Self {
        self.push_str(rhs);
        self
    }
}

impl<'a> ops::AddAssign<&'a bstr> for BString {
    fn add_assign(&mut self, rhs: &bstr) {
        self.push_str(rhs);
    }
}

impl<'a> ops::AddAssign<&'a str> for BString {
    fn add_assign(&mut self, rhs: &str) {
        self.push_str(rhs);
    }
}

impl<'a> ops::AddAssign<&'a [u8]> for BString {
    fn add_assign(&mut self, rhs: &[u8]) {
        self.push_str(rhs);
    }
}

impl<'a> Default for &'a bstr {
    fn default() -> &'a bstr {
        "".as_ref()
    }
}

impl Extend<u8> for BString {
    fn extend<I: IntoIterator<Item=u8>>(&mut self, iter: I) {
        self.bytes.extend(iter);
    }
}

impl<'a> Extend<&'a u8> for BString {
    fn extend<I: IntoIterator<Item=&'a u8>>(&mut self, iter: I) {
        self.bytes.extend(iter);
    }
}

impl<'a> Extend<&'a bstr> for BString {
    fn extend<I: IntoIterator<Item=&'a bstr>>(&mut self, iter: I) {
        for s in iter {
            self.push_str(s);
        }
    }
}

impl<'a> Extend<BString> for BString {
    fn extend<I: IntoIterator<Item=BString>>(&mut self, iter: I) {
        for s in iter {
            self.push_str(s);
        }
    }
}

impl<'a> Extend<&'a str> for BString {
    fn extend<I: IntoIterator<Item=&'a str>>(&mut self, iter: I) {
        for s in iter {
            self.push_str(s);
        }
    }
}

impl<'a> Extend<String> for BString {
    fn extend<I: IntoIterator<Item=String>>(&mut self, iter: I) {
        for s in iter {
            self.push_str(s);
        }
    }
}

impl<'a> Extend<&'a [u8]> for BString {
    fn extend<I: IntoIterator<Item=&'a [u8]>>(&mut self, iter: I) {
        for s in iter {
            self.push_str(s);
        }
    }
}

impl<'a> Extend<Vec<u8>> for BString {
    fn extend<I: IntoIterator<Item=Vec<u8>>>(&mut self, iter: I) {
        for s in iter {
            self.push_str(s);
        }
    }
}

/// Represents an error parsing a `BString` from a `&bstr`.
///
/// As such an operation can never fail, this type cannot be instantiated
/// under any safe conditions.
pub enum ParseError {}

impl FromBStr for BString {
    type Err = ParseError;

    fn from_bstr(s: &bstr) -> Result<BString, ParseError> {
        Ok(s.to_bstring())
    }
}

impl FromIterator<u8> for BString {
    fn from_iter<I: IntoIterator<Item=u8>>(iter: I) -> BString {
        BString{bytes: iter.into_iter().collect()}
    }
}

impl ToOwned for bstr {
    type Owned = BString;

    fn to_owned(&self) -> BString {
        self.bytes.to_owned().into()
    }
}

impl ops::Index<usize> for BString {
    type Output = u8;

    fn index(&self, idx: usize) -> &u8 {
        &self.bytes[idx]
    }
}

impl ops::Index<Range<usize>> for BString {
    type Output = bstr;

    fn index(&self, r: Range<usize>) -> &bstr {
        self.bytes[r].as_ref()
    }
}

impl ops::Index<RangeFrom<usize>> for BString {
    type Output = bstr;

    fn index(&self, r: RangeFrom<usize>) -> &bstr {
        self.bytes[r].as_ref()
    }
}

impl ops::Index<RangeTo<usize>> for BString {
    type Output = bstr;

    fn index(&self, r: RangeTo<usize>) -> &bstr {
        self.bytes[r].as_ref()
    }
}

impl ops::Index<RangeFull> for BString {
    type Output = bstr;

    fn index(&self, r: RangeFull) -> &bstr {
        self.bytes[r].as_ref()
    }
}

impl ops::IndexMut<usize> for BString {
    fn index_mut(&mut self, idx: usize) -> &mut u8 {
        &mut self.bytes[idx]
    }
}

impl ops::IndexMut<Range<usize>> for BString {
    fn index_mut(&mut self, r: Range<usize>) -> &mut bstr {
        self.bytes[r].as_mut()
    }
}

impl ops::IndexMut<RangeFrom<usize>> for BString {
    fn index_mut(&mut self, r: RangeFrom<usize>) -> &mut bstr {
        self.bytes[r].as_mut()
    }
}

impl ops::IndexMut<RangeTo<usize>> for BString {
    fn index_mut(&mut self, r: RangeTo<usize>) -> &mut bstr {
        self.bytes[r].as_mut()
    }
}

impl ops::IndexMut<RangeFull> for BString {
    fn index_mut(&mut self, r: RangeFull) -> &mut bstr {
        self.bytes[r].as_mut()
    }
}

impl ops::Index<usize> for bstr {
    type Output = u8;

    fn index(&self, idx: usize) -> &u8 {
        &self.bytes[idx]
    }
}

impl ops::Index<Range<usize>> for bstr {
    type Output = bstr;

    fn index(&self, r: Range<usize>) -> &bstr {
        self.bytes[r].as_ref()
    }
}

impl ops::Index<RangeFrom<usize>> for bstr {
    type Output = bstr;

    fn index(&self, r: RangeFrom<usize>) -> &bstr {
        self.bytes[r].as_ref()
    }
}

impl ops::Index<RangeTo<usize>> for bstr {
    type Output = bstr;

    fn index(&self, r: RangeTo<usize>) -> &bstr {
        self.bytes[r].as_ref()
    }
}

impl ops::Index<RangeFull> for bstr {
    type Output = bstr;

    fn index(&self, r: RangeFull) -> &bstr {
        self.bytes[r].as_ref()
    }
}

impl ops::IndexMut<usize> for bstr {
    fn index_mut(&mut self, idx: usize) -> &mut u8 {
        &mut self.bytes[idx]
    }
}

impl ops::IndexMut<Range<usize>> for bstr {
    fn index_mut(&mut self, r: Range<usize>) -> &mut bstr {
        self.bytes[r].as_mut()
    }
}

impl ops::IndexMut<RangeFrom<usize>> for bstr {
    fn index_mut(&mut self, r: RangeFrom<usize>) -> &mut bstr {
        self.bytes[r].as_mut()
    }
}

impl ops::IndexMut<RangeTo<usize>> for bstr {
    fn index_mut(&mut self, r: RangeTo<usize>) -> &mut bstr {
        self.bytes[r].as_mut()
    }
}

impl ops::IndexMut<RangeFull> for bstr {
    fn index_mut(&mut self, r: RangeFull) -> &mut bstr {
        self.bytes[r].as_mut()
    }
}

impl<'a> IntoIterator for &'a BString {
    type Item = &'a u8;
    type IntoIter = Iter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a> IntoIterator for &'a mut BString {
    type Item = &'a mut u8;
    type IntoIter = IterMut<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<'a> IntoIterator for &'a bstr {
    type Item = &'a u8;
    type IntoIter = Iter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a> IntoIterator for &'a mut bstr {
    type Item = &'a mut u8;
    type IntoIter = IterMut<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

macro_rules! impl_partial_eq {
    ( $lhs:ty , $rhs:ty ) => {
        impl<'a, 'b> PartialEq<$rhs> for $lhs {
            fn eq(&self, rhs: &$rhs) -> bool { self.as_bytes() == rhs.as_bytes() }
            fn ne(&self, rhs: &$rhs) -> bool { self.as_bytes() != rhs.as_bytes() }
        }
    }
}

impl Eq for BString {}

impl_partial_eq!{ BString, BString }
impl_partial_eq!{ BString, bstr }
impl_partial_eq!{ BString, &'a bstr }
impl_partial_eq!{ BString, Cow<'a, bstr> }
impl_partial_eq!{ BString, String }
impl_partial_eq!{ BString, str }
impl_partial_eq!{ BString, &'a str }
impl_partial_eq!{ BString, Cow<'a, str> }

impl PartialEq<Vec<u8>> for BString {
    fn eq(&self, rhs: &Vec<u8>) -> bool { self.as_bytes() == &rhs[..] }
    fn ne(&self, rhs: &Vec<u8>) -> bool { self.as_bytes() != &rhs[..] }
}

impl PartialEq<[u8]> for BString {
    fn eq(&self, rhs: &[u8]) -> bool { self.as_bytes() == rhs }
    fn ne(&self, rhs: &[u8]) -> bool { self.as_bytes() != rhs }
}

impl Eq for bstr {}

impl_partial_eq!{ bstr, bstr }
impl_partial_eq!{ bstr, BString }
impl_partial_eq!{ bstr, Cow<'a, bstr> }
impl_partial_eq!{ bstr, str }
impl_partial_eq!{ bstr, String }
impl_partial_eq!{ bstr, Cow<'a, str> }
impl_partial_eq!{ &'a bstr, bstr }
impl_partial_eq!{ &'a bstr, BString }
impl_partial_eq!{ &'a bstr, Cow<'b, bstr> }
impl_partial_eq!{ &'a bstr, str }
impl_partial_eq!{ &'a bstr, String }
impl_partial_eq!{ &'a bstr, Cow<'b, str> }
impl_partial_eq!{ Cow<'a, bstr>, bstr }
impl_partial_eq!{ Cow<'a, bstr>, &'b bstr }
impl_partial_eq!{ Cow<'a, bstr>, BString }

impl PartialEq<Vec<u8>> for bstr {
    fn eq(&self, rhs: &Vec<u8>) -> bool { self.as_bytes() == &rhs[..] }
    fn ne(&self, rhs: &Vec<u8>) -> bool { self.as_bytes() != &rhs[..] }
}

impl PartialEq<[u8]> for bstr {
    fn eq(&self, rhs: &[u8]) -> bool { self.as_bytes() == rhs }
    fn ne(&self, rhs: &[u8]) -> bool { self.as_bytes() != rhs }
}

macro_rules! array_partial_eq {
    ( $lhs:ty , $( $n:expr ),* ) => {
        $(
            impl<'a> PartialEq<[u8; $n]> for $lhs {
                fn eq(&self, rhs: &[u8; $n]) -> bool { self.as_bytes() == &rhs[..] }
                fn ne(&self, rhs: &[u8; $n]) -> bool { self.as_bytes() != &rhs[..] }
            }

            impl<'a, 'b> PartialEq<&'b [u8; $n]> for $lhs {
                fn eq(&self, rhs: &&[u8; $n]) -> bool { self.as_bytes() == &rhs[..] }
                fn ne(&self, rhs: &&[u8; $n]) -> bool { self.as_bytes() != &rhs[..] }
            }
        )*
    }
}

array_partial_eq!{ BString, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16 }
array_partial_eq!{ &'a bstr, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16 }

impl Ord for BString {
    fn cmp(&self, rhs: &BString) -> Ordering {
        self[..].cmp(&rhs[..])
    }
}

impl PartialOrd for BString {
    fn partial_cmp(&self, rhs: &BString) -> Option<Ordering> {
        self.as_bytes().partial_cmp(rhs.as_bytes())
    }

    fn lt(&self, rhs: &BString) -> bool { self.as_bytes() < rhs.as_bytes() }
    fn gt(&self, rhs: &BString) -> bool { self.as_bytes() > rhs.as_bytes() }
    fn le(&self, rhs: &BString) -> bool { self.as_bytes() <= rhs.as_bytes() }
    fn ge(&self, rhs: &BString) -> bool { self.as_bytes() >= rhs.as_bytes() }
}

impl Ord for bstr {
    fn cmp(&self, rhs: &bstr) -> Ordering {
        self.bytes.cmp(&rhs.bytes)
    }
}

impl PartialOrd for bstr {
    fn partial_cmp(&self, rhs: &bstr) -> Option<Ordering> {
        self.bytes.partial_cmp(&rhs.bytes)
    }

    fn lt(&self, rhs: &bstr) -> bool { &self.bytes < &rhs.bytes }
    fn gt(&self, rhs: &bstr) -> bool { &self.bytes > &rhs.bytes }
    fn le(&self, rhs: &bstr) -> bool { &self.bytes <= &rhs.bytes }
    fn ge(&self, rhs: &bstr) -> bool { &self.bytes >= &rhs.bytes }
}

#[cfg(test)]
mod test {
    use super::{bstr, BString};

    fn bs<S: ?Sized + AsRef<bstr>>(s: &S) -> &bstr {
        s.as_ref()
    }

    #[test]
    fn test_bstring_concat() {
        let empty: &[String] = &[];
        assert_eq!(BString::concat(empty), "");
        assert_eq!(BString::concat(&["foo"]), "foo");
        assert_eq!(BString::concat(&["foo", "bar"]), "foobar");
    }

    #[test]
    fn test_bstring_join() {
        let empty: &[String] = &[];

        assert_eq!(BString::join(" ", empty), "");
        assert_eq!(BString::join(" ", &["foo"]), "foo");
        assert_eq!(BString::join(b' ', &["foo", "bar"]), "foo bar");
    }

    #[test]
    fn test_bstring_insert_str() {
        let mut bs = BString::from("foobaz");

        bs.insert_str(3, "bar");
        assert_eq!(bs, "foobarbaz");
    }

    #[test]
    fn test_bstr_contains() {
        assert_eq!(bs("foo").contains("foo"), true);
        assert_eq!(bs("foobar").contains("bar"), true);
        assert_eq!(bs("foo").contains("baz"), false);
        assert_eq!(bs("foo").contains("fooo"), false);
    }

    #[test]
    fn test_boxed_bstr() {
        let a = BString::from("foo");
        let _b = a.into_boxed_bstr();

        let a = BString::from("foo");
        let b = a.into_boxed_bstr();
        let _c = b.into_bstring();
    }

    #[test]
    fn test_bstr_find() {
        assert_eq!(bs("hello").find(b'l'), Some(2));
        assert_eq!(bs("hello").find(|b: u8| b == b'o'), Some(4));
        assert_eq!(bs("hello").find(b'x'), None);
        assert_eq!(bs("hello").find(|b: u8| b == b'x'), None);
    }

    #[test]
    fn test_bstr_rfind() {
        assert_eq!(bs("hello").rfind(b'l'), Some(3));
        assert_eq!(bs("hello").rfind(|b: u8| b == b'o'), Some(4));
        assert_eq!(bs("hello").rfind(b'x'), None);
        assert_eq!(bs("hello").rfind(|b: u8| b == b'x'), None);
    }

    #[test]
    fn test_bstr_find_bstr() {
        assert_eq!(bs("").find(""), Some(0));
        assert_eq!(bs("banana").find("apple pie"), None);

        let data = bs("abcabc");
        assert_eq!(data[0..6].find("ab"), Some(0));
        assert_eq!(data[2..6].find("ab"), Some(3 - 2));
        assert_eq!(data[2..4].find("ab"), None);
    }

    #[test]
    fn test_bstr_lines() {
        let mut b = bs("abc").lines();

        assert_matches!(b.next(), Some(s) if s == "abc");
        assert_matches!(b.next(), None);

        let mut b = bs("abc\ndef\n").lines();

        assert_matches!(b.next(), Some(s) if s == "abc");
        assert_matches!(b.next(), Some(s) if s == "def");
        assert_matches!(b.next(), None);

        let mut b = bs("abc\r\ndef").lines();

        assert_matches!(b.next(), Some(s) if s == "abc");
        assert_matches!(b.next(), Some(s) if s == "def");
        assert_matches!(b.next(), None);

    }

    #[test]
    fn test_bstr_trim() {
        assert_eq!(bs("  foo  ").trim(), "foo");
        assert_eq!(bs("  foo  ").trim_left(), "foo  ");
        assert_eq!(bs("  foo  ").trim_right(), "  foo");

        assert_eq!(bs("foo").trim(), "foo");
        assert_eq!(bs("foo").trim_left(), "foo");
        assert_eq!(bs("foo").trim_right(), "foo");
    }

    #[test]
    fn test_bstr_partition() {
        assert_matches!(bs("foo bar").partition(b' '),
            Some((a, b)) if a == "foo" && b == "bar");
        assert_matches!(bs("foobar").partition(b' '), None);
    }

    #[test]
    fn test_bstr_split() {
        let mut iter = bs("foo bar baz").split(|b| b == b' ');

        assert_eq!(iter.next(), Some(bs("foo")));
        assert_eq!(iter.next(), Some(bs("bar")));
        assert_eq!(iter.next(), Some(bs("baz")));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_split_empty() {
        let mut iter = bs("").split(b' ');

        assert_eq!(iter.next(), Some("".as_ref()));
        assert_eq!(iter.next(), None);

        let mut iter = bs("").split_words(b' ');

        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_bstr_split_space() {
        let mut iter = bs("   foo bar   baz    ").split_words(b' ');

        assert_eq!(iter.next(), Some(bs("foo")));
        assert_eq!(iter.as_bstr(), "bar   baz    ");
        assert_eq!(iter.next(), Some(bs("bar")));
        assert_eq!(iter.as_bstr(), "baz    ");
        assert_eq!(iter.next(), Some(bs("baz")));
        assert_eq!(iter.as_bstr(), "");
        assert_eq!(iter.next(), None);
        assert_eq!(iter.as_bstr(), "");
    }

    #[test]
    fn test_bstr_to_bstring() {
        assert_eq!(bs("foo").to_bstring(), "foo");
    }
}
