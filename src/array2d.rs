// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

// FIXME: remove when module made public again
#![allow(dead_code)]

use std::{
    borrow::{Borrow, BorrowMut},
    fmt,
    iter::FusedIterator,
    ops::{
        Bound, Index, IndexMut, Range, RangeBounds, RangeFrom, RangeFull, RangeInclusive, RangeTo,
        RangeToInclusive,
    },
    slice, vec,
};

mod private {
    pub(crate) trait SealedData {}

    impl<T> SealedData for Vec<T> {}
    impl<'a, T> SealedData for &'a [T] {}
    impl<'a, T> SealedData for &'a mut [T] {}
}

pub(crate) trait Array2DData:
    Sized + private::SealedData + Borrow<[<Self as Array2DData>::Element]>
{
    type Element: Sized;
    type StrideType: Copy + Default;
    type IntoIter: Iterator;
    fn read_stride(y_size: usize, stride: Self::StrideType) -> usize;
    fn make_stride(y_size: usize) -> Self::StrideType;
    fn into_iter(this: Array2DBase<Self>) -> Self::IntoIter;
}

impl<T: Sized> Array2DData for Vec<T> {
    type Element = T;
    type StrideType = ();
    type IntoIter = IntoIter<T>;
    fn read_stride(y_size: usize, _stride: Self::StrideType) -> usize {
        y_size
    }
    fn make_stride(_y_size: usize) -> Self::StrideType {
        Default::default()
    }
    fn into_iter(this: Array2DBase<Self>) -> Self::IntoIter {
        IntoIter {
            positions: this.positions(),
            data: IterOwnedData {
                stride: this.stride(),
                offset: 0,
                iter: this.data.into_iter(),
            },
        }
    }
}

impl<'a, T: Sized> Array2DData for &'a [T] {
    type Element = T;
    type StrideType = usize;
    type IntoIter = Iter<'a, T>;
    fn read_stride(_y_size: usize, stride: Self::StrideType) -> usize {
        stride
    }
    fn make_stride(y_size: usize) -> Self::StrideType {
        y_size
    }
    fn into_iter(this: Array2DBase<Self>) -> Self::IntoIter {
        Iter {
            positions: this.positions(),
            stride: this.stride(),
            data: this.data.borrow(),
        }
    }
}

impl<'a, T: Sized> Array2DData for &'a mut [T] {
    type Element = T;
    type StrideType = usize;
    type IntoIter = IterMut<'a, T>;
    fn read_stride(_y_size: usize, stride: Self::StrideType) -> usize {
        stride
    }
    fn make_stride(y_size: usize) -> Self::StrideType {
        y_size
    }
    fn into_iter(this: Array2DBase<Self>) -> Self::IntoIter {
        IterMut {
            positions: this.positions(),
            data: IterOwnedData {
                stride: this.stride(),
                offset: 0,
                iter: this.data.borrow_mut().iter_mut(),
            },
        }
    }
}

/// column-major 2D array
///
/// The alternate display format (using `"{:#}"`) is a reStructuredText table
///
/// Examples:
/// ```ignored
/// # use algebraics::array2d::Array2DOwned;
/// // Note: using strings to demonstrate `Display`, numbers are normally used
/// let mut array = Array2DOwned::from_array(
///     3,
///     3,
///     vec!["0", "1", "2", "10", "11", "12", "20", "21", "22"],
/// );
/// assert_eq!(
///     format!("{}", array),
///     "[ 0  10  20 ]\n\
///      [ 1  11  21 ]\n\
///      [ 2  12  22 ]"
/// );
/// assert_eq!(
///     format!("{:#}", array),
///     "+---+----+----+\n\
///      | 0 | 10 | 20 |\n\
///      +---+----+----+\n\
///      | 1 | 11 | 21 |\n\
///      +---+----+----+\n\
///      | 2 | 12 | 22 |\n\
///      +---+----+----+"
/// );
/// // change the value at x=0, y=2 to a multi-line str
/// array[(0, 2)] = "line 1\nline 2";
///
/// assert_eq!(
///     format!("{}", array),
///     "[ 0       10  20 ]\n\
///      [                ]\n\
///      [ 1       11  21 ]\n\
///      [                ]\n\
///      [ line 1  12  22 ]\n\
///      [ line 2         ]"
/// );
/// assert_eq!(
///     format!("{:#}", array),
///     "+--------+----+----+\n\
///      | 0      | 10 | 20 |\n\
///      +--------+----+----+\n\
///      | 1      | 11 | 21 |\n\
///      +--------+----+----+\n\
///      | line 1 | 12 | 22 |\n\
///      | line 2 |    |    |\n\
///      +--------+----+----+"
/// );
/// ```
// FIXME: unignore doctest when pub
#[derive(Copy, Clone, Hash, Eq, PartialEq, Debug)]
pub(crate) struct Array2DBase<Data: Array2DData> {
    x_size: usize,
    y_size: usize,
    stride: Data::StrideType,
    data: Data,
}

struct Array2DSliceData {
    x_size: usize,
    y_size: usize,
    data_offset: usize,
}

fn get_index_unchecked(stride: usize, x: usize, y: usize) -> usize {
    x * stride + y
}

pub(crate) trait Array2DSliceBound {
    fn to_slice_bound(self) -> (Bound<usize>, Bound<usize>);
}

impl Array2DSliceBound for usize {
    fn to_slice_bound(self) -> (Bound<usize>, Bound<usize>) {
        (Bound::Included(self), Bound::Included(self))
    }
}

fn bound_cloned<T: Clone>(bound: Bound<&T>) -> Bound<T> {
    match bound {
        Bound::Unbounded => Bound::Unbounded,
        Bound::Excluded(v) => Bound::Excluded(v.clone()),
        Bound::Included(v) => Bound::Included(v.clone()),
    }
}

macro_rules! impl_array2d_slice_bound {
    ($t:ty) => {
        impl Array2DSliceBound for $t {
            fn to_slice_bound(self) -> (Bound<usize>, Bound<usize>) {
                (
                    bound_cloned(self.start_bound()),
                    bound_cloned(self.end_bound()),
                )
            }
        }
    };
}

impl_array2d_slice_bound!(RangeFull);
impl_array2d_slice_bound!(Range<usize>);
impl_array2d_slice_bound!(RangeFrom<usize>);
impl_array2d_slice_bound!(RangeTo<usize>);
impl_array2d_slice_bound!(RangeInclusive<usize>);
impl_array2d_slice_bound!(RangeToInclusive<usize>);
impl_array2d_slice_bound!((Bound<usize>, Bound<usize>));
impl_array2d_slice_bound!(Range<&usize>);
impl_array2d_slice_bound!(RangeFrom<&usize>);
impl_array2d_slice_bound!(RangeTo<&usize>);
impl_array2d_slice_bound!(RangeInclusive<&usize>);
impl_array2d_slice_bound!(RangeToInclusive<&usize>);
impl_array2d_slice_bound!((Bound<&usize>, Bound<&usize>));

impl<Data: Array2DData> Array2DBase<Data> {
    /// data is a column-major 2D array
    pub(crate) fn from_array(x_size: usize, y_size: usize, data: Data) -> Self {
        assert_eq!(x_size * y_size, data.borrow().len());
        Self {
            x_size,
            y_size,
            stride: Data::make_stride(y_size),
            data,
        }
    }
    pub(crate) fn x_size(&self) -> usize {
        self.x_size
    }
    pub(crate) fn y_size(&self) -> usize {
        self.y_size
    }
    pub(crate) fn size(&self) -> (usize, usize) {
        (self.x_size, self.y_size)
    }
    fn stride(&self) -> usize {
        Data::read_stride(self.y_size, self.stride)
    }
    fn get_index(&self, x: usize, y: usize) -> usize {
        assert!(x < self.x_size);
        assert!(y < self.y_size);
        get_index_unchecked(self.stride(), x, y)
    }
    fn do_slice<XB: Array2DSliceBound, YB: Array2DSliceBound>(
        &self,
        x_bound: XB,
        y_bound: YB,
    ) -> Array2DSliceData {
        fn start_and_end(
            (start_bound, end_bound): (Bound<usize>, Bound<usize>),
            size: usize,
        ) -> (usize, usize) {
            let start = match start_bound {
                Bound::Unbounded => 0,
                Bound::Excluded(v) => v + 1,
                Bound::Included(v) => v,
            };
            let end = match end_bound {
                Bound::Unbounded => size,
                Bound::Excluded(v) => v,
                Bound::Included(v) => v + 1,
            };
            assert!(start <= end);
            assert!(end <= size);
            (start, end)
        }
        let (x_start, x_end) = start_and_end(x_bound.to_slice_bound(), self.x_size);
        let (y_start, y_end) = start_and_end(y_bound.to_slice_bound(), self.y_size);
        Array2DSliceData {
            x_size: x_end - x_start,
            y_size: y_end - y_start,
            data_offset: get_index_unchecked(self.stride(), x_start, y_start),
        }
    }
    pub(crate) fn slice<XB: Array2DSliceBound, YB: Array2DSliceBound>(
        &self,
        x_bound: XB,
        y_bound: YB,
    ) -> Array2DSlice<Data::Element> {
        let Array2DSliceData {
            x_size,
            y_size,
            data_offset,
        } = self.do_slice(x_bound, y_bound);
        Array2DBase {
            x_size,
            y_size,
            stride: self.stride(),
            data: &self.data.borrow()[data_offset..],
        }
    }
    pub(crate) fn slice_mut<XB: Array2DSliceBound, YB: Array2DSliceBound>(
        &mut self,
        x_bound: XB,
        y_bound: YB,
    ) -> Array2DMutSlice<Data::Element>
    where
        Data: BorrowMut<[<Data as Array2DData>::Element]>,
    {
        let Array2DSliceData {
            x_size,
            y_size,
            data_offset,
        } = self.do_slice(x_bound, y_bound);
        Array2DBase {
            x_size,
            y_size,
            stride: self.stride(),
            data: &mut self.data.borrow_mut()[data_offset..],
        }
    }
    pub(crate) fn positions(&self) -> Positions {
        Positions::new(self.x_size, self.y_size)
    }
    pub(crate) fn iter(&self) -> Iter<Data::Element> {
        Iter {
            positions: self.positions(),
            stride: self.stride(),
            data: self.data.borrow(),
        }
    }
    pub(crate) fn iter_mut(&mut self) -> IterMut<Data::Element>
    where
        Data: BorrowMut<[<Data as Array2DData>::Element]>,
    {
        IterMut {
            positions: self.positions(),
            data: IterOwnedData {
                stride: self.stride(),
                offset: 0,
                iter: self.data.borrow_mut().iter_mut(),
            },
        }
    }
    pub(crate) fn to_owned(&self) -> Array2DOwned<Data::Element>
    where
        Data::Element: Clone,
    {
        Array2DBase::from_array(self.x_size, self.y_size, self.iter().cloned().collect())
    }
    pub(crate) fn swap_elements(&mut self, (x1, y1): (usize, usize), (x2, y2): (usize, usize))
    where
        Data: BorrowMut<[<Data as Array2DData>::Element]>,
    {
        let index1 = self.get_index(x1, y1);
        let index2 = self.get_index(x2, y2);
        self.data.borrow_mut().swap(index1, index2);
    }
}

impl<T> Array2DBase<Vec<T>> {
    pub(crate) fn new_with_positions<F: FnMut(usize, usize) -> T>(
        x_size: usize,
        y_size: usize,
        mut f: F,
    ) -> Self {
        Self::from_array(
            x_size,
            y_size,
            Positions::new(x_size, y_size)
                .map(move |(x, y)| f(x, y))
                .collect(),
        )
    }
    pub(crate) fn new_with<F: FnMut() -> T>(x_size: usize, y_size: usize, f: F) -> Self {
        let len = x_size * y_size;
        let mut data = Vec::with_capacity(len);
        data.resize_with(len, f);
        Self::from_array(x_size, y_size, data)
    }
    pub(crate) fn new(x_size: usize, y_size: usize, value: T) -> Self
    where
        T: Clone,
    {
        let len = x_size * y_size;
        let mut data = Vec::with_capacity(len);
        data.resize(len, value);
        Self::from_array(x_size, y_size, data)
    }
    pub(crate) fn into_data(self) -> Vec<T> {
        self.data
    }
    pub(crate) fn data(&self) -> &[T] {
        &*self.data
    }
    pub(crate) fn data_mut(&mut self) -> &mut [T] {
        &mut *self.data
    }
}

impl<Data: Array2DData> Index<(usize, usize)> for Array2DBase<Data> {
    type Output = Data::Element;
    fn index(&self, (x, y): (usize, usize)) -> &Self::Output {
        let index = self.get_index(x, y);
        &self.data.borrow()[index]
    }
}

impl<Data: Array2DData + BorrowMut<[<Data as Array2DData>::Element]>> IndexMut<(usize, usize)>
    for Array2DBase<Data>
{
    fn index_mut(&mut self, (x, y): (usize, usize)) -> &mut Self::Output {
        let index = self.get_index(x, y);
        &mut self.data.borrow_mut()[index]
    }
}

impl<T: fmt::Display + Clone, Data: Array2DData<Element = T>> fmt::Display for Array2DBase<Data> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.x_size() == 0 || self.y_size() == 0 {
            return writeln!(f, "[x_size={}, y_size={}]", self.x_size(), self.y_size());
        }
        let mut cells: Vec<Vec<String>> = Vec::new();
        let mut row_heights = vec![0usize; self.y_size()];
        let mut col_widths = vec![0usize; self.x_size()];
        cells.resize(self.y_size(), Vec::with_capacity(self.x_size()));
        let mut any_multiline_cells = false;
        for y in 0..self.y_size() {
            for x in 0..self.x_size() {
                let cell_str = format!("{}", self[(x, y)]);
                let mut width = 1;
                let mut height = 0;
                for line in cell_str.lines() {
                    height += 1;
                    width = width.max(line.len());
                }
                height = height.max(1);
                if height > 1 {
                    any_multiline_cells = true;
                }
                row_heights[y] = row_heights[y].max(height);
                col_widths[x] = col_widths[x].max(width);
                cells[y].push(cell_str);
            }
        }
        let write_separator_line = |f: &mut fmt::Formatter| {
            for &col_width in &col_widths {
                write!(f, "+-")?;
                for _ in 0..col_width {
                    write!(f, "-")?;
                }
                write!(f, "-")?;
            }
            write!(f, "+")
        };
        if f.alternate() {
            write_separator_line(f)?;
            writeln!(f)?;
        }
        for y in 0..self.y_size() {
            let is_last_row = y == self.y_size() - 1;
            let mut line_iters: Vec<_> = cells[y].iter().map(|cell| cell.lines()).collect();
            let mut height = row_heights[y];
            if !f.alternate() && any_multiline_cells && !is_last_row {
                height += 1;
            }
            for cell_row in 0..height {
                if !f.alternate() {
                    write!(f, "[")?;
                }
                for x in 0..self.x_size() {
                    let cell_line = line_iters[x].next().unwrap_or("");
                    if f.alternate() {
                        write!(f, "|")?;
                    }
                    write!(
                        f,
                        " {cell_line:width$} ",
                        cell_line = cell_line,
                        width = col_widths[x]
                    )?;
                }
                if f.alternate() {
                    write!(f, "|")?;
                } else {
                    write!(f, "]")?;
                }
                if cell_row != height - 1 {
                    writeln!(f)?;
                }
            }
            if f.alternate() {
                writeln!(f)?;
                write_separator_line(f)?;
            }
            if !is_last_row {
                writeln!(f)?;
            }
        }
        Ok(())
    }
}

pub(crate) type Array2DOwned<T> = Array2DBase<Vec<T>>;
pub(crate) type Array2DSlice<'a, T> = Array2DBase<&'a [T]>;
pub(crate) type Array2DMutSlice<'a, T> = Array2DBase<&'a mut [T]>;

/// column-major 2D positions iterator
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub(crate) struct Positions {
    x: usize,
    y: usize,
    y_size: usize,
    rev_x: usize,
    after_rev_y: usize,
}

impl Default for Positions {
    fn default() -> Self {
        Self {
            x: 0,
            y: 0,
            y_size: 0,
            rev_x: 0,
            after_rev_y: 0,
        }
    }
}

impl Positions {
    pub(crate) fn new(x_size: usize, y_size: usize) -> Self {
        if x_size == 0 || y_size == 0 {
            Self::default()
        } else {
            Self {
                x: 0,
                y: 0,
                y_size,
                rev_x: x_size - 1,
                after_rev_y: y_size,
            }
        }
    }
    pub(crate) fn is_finished(&self) -> bool {
        self.x == self.rev_x && self.y == self.after_rev_y
    }
    pub(crate) fn pos(&self) -> Option<(usize, usize)> {
        if self.is_finished() {
            return None;
        }
        Some((self.x, self.y))
    }
    pub(crate) fn rev_pos(&self) -> Option<(usize, usize)> {
        if self.is_finished() {
            return None;
        }
        Some((self.rev_x, self.after_rev_y - 1))
    }
}

impl Iterator for Positions {
    type Item = (usize, usize);
    fn next(&mut self) -> Option<(usize, usize)> {
        let pos = self.pos()?;
        self.y += 1;
        if self.y == self.y_size && self.rev_x != self.x {
            self.y = 0;
            self.x += 1;
        }
        Some(pos)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
    fn count(self) -> usize {
        self.len()
    }
    fn last(mut self) -> Option<(usize, usize)> {
        self.next_back()
    }
}

impl DoubleEndedIterator for Positions {
    fn next_back(&mut self) -> Option<(usize, usize)> {
        let pos = self.rev_pos()?;
        self.after_rev_y -= 1;
        if self.after_rev_y == 0 && self.rev_x != self.x {
            self.after_rev_y = self.y_size;
            self.rev_x -= 1;
        }
        Some(pos)
    }
}

impl ExactSizeIterator for Positions {
    fn len(&self) -> usize {
        self.y_size * (self.rev_x - self.x) + self.after_rev_y - self.y
    }
}

impl FusedIterator for Positions {}

macro_rules! impl_positions_wrapper {
    (($($trait_args:tt),*), $wrapper:ident, $item:ty) => {
        impl<$($trait_args),*> Iterator for $wrapper<$($trait_args),*> {
            type Item = $item;
            fn next(&mut self) -> Option<$item> {
                let (x, y) = self.positions.next()?;
                Some(self.get_unchecked(x, y))
            }
            fn size_hint(&self) -> (usize, Option<usize>) {
                self.positions.size_hint()
            }
            fn count(self) -> usize {
                self.positions.count()
            }
            fn last(mut self) -> Option<$item> {
                self.next_back()
            }
        }

        impl<$($trait_args),*> DoubleEndedIterator for $wrapper<$($trait_args),*> {
            fn next_back(&mut self) -> Option<$item> {
                let (x, y) = self.positions.next_back()?;
                Some(self.get_unchecked_back(x, y))
            }
        }

        impl<$($trait_args),*> ExactSizeIterator for $wrapper<$($trait_args),*> {
            fn len(&self) -> usize {
                self.positions.len()
            }
        }

        impl<$($trait_args),*> FusedIterator for $wrapper<$($trait_args),*> {}
    };
}

#[derive(Copy, Clone, Debug)]
pub(crate) struct IterWithPositions<'a, T> {
    positions: Positions,
    stride: usize,
    data: &'a [T],
}

impl<'a, T> IterWithPositions<'a, T> {
    pub(crate) fn positions(&self) -> Positions {
        self.positions
    }
    pub(crate) fn without_positions(self) -> Iter<'a, T> {
        let IterWithPositions {
            positions,
            stride,
            data,
        } = self;
        Iter {
            positions,
            stride,
            data,
        }
    }
    fn get_unchecked(&self, x: usize, y: usize) -> ((usize, usize), &'a T) {
        ((x, y), &self.data[get_index_unchecked(self.stride, x, y)])
    }
    fn get_unchecked_back(&self, x: usize, y: usize) -> ((usize, usize), &'a T) {
        self.get_unchecked(x, y)
    }
}

impl_positions_wrapper!(('a, T), IterWithPositions, ((usize, usize), &'a T));

#[derive(Debug)]
pub(crate) struct IterMutWithPositions<'a, T: 'a> {
    positions: Positions,
    data: IterOwnedData<slice::IterMut<'a, T>>,
}

impl<'a, T: 'a> IterMutWithPositions<'a, T> {
    pub(crate) fn positions(&self) -> Positions {
        self.positions
    }
    pub(crate) fn without_positions(self) -> IterMut<'a, T> {
        let IterMutWithPositions { positions, data } = self;
        IterMut { positions, data }
    }
    fn get_unchecked(&mut self, x: usize, y: usize) -> ((usize, usize), &'a mut T) {
        ((x, y), self.data.get_unchecked(x, y))
    }
    fn get_unchecked_back(&mut self, x: usize, y: usize) -> ((usize, usize), &'a mut T) {
        ((x, y), self.data.get_unchecked_back(x, y))
    }
}

impl_positions_wrapper!(('a, T), IterMutWithPositions, ((usize, usize), &'a mut T));

#[derive(Copy, Clone, Debug)]
pub(crate) struct Iter<'a, T> {
    positions: Positions,
    stride: usize,
    data: &'a [T],
}

impl<'a, T> Iter<'a, T> {
    pub(crate) fn positions(&self) -> Positions {
        self.positions
    }
    pub(crate) fn with_positions(self) -> IterWithPositions<'a, T> {
        let Iter {
            positions,
            stride,
            data,
        } = self;
        IterWithPositions {
            positions,
            stride,
            data,
        }
    }
    fn get_unchecked(&self, x: usize, y: usize) -> &'a T {
        &self.data[get_index_unchecked(self.stride, x, y)]
    }
    fn get_unchecked_back(&self, x: usize, y: usize) -> &'a T {
        self.get_unchecked(x, y)
    }
}

impl_positions_wrapper!(('a, T), Iter, &'a T);

#[derive(Debug)]
struct IterOwnedData<Iter> {
    stride: usize,
    offset: usize,
    iter: Iter,
}

impl<Iter: Iterator + DoubleEndedIterator + ExactSizeIterator> IterOwnedData<Iter> {
    fn get_unchecked(&mut self, x: usize, y: usize) -> Iter::Item {
        let index = get_index_unchecked(self.stride, x, y) - self.offset;
        self.offset += index + 1;
        self.iter.nth(index).expect("data shouldn't be empty")
    }
    fn get_unchecked_back(&mut self, x: usize, y: usize) -> Iter::Item {
        let index = get_index_unchecked(self.stride, x, y) - self.offset;
        self.iter
            .nth_back(self.iter.len() - dbg!(index) - 1)
            .expect("data shouldn't be empty")
    }
}

#[derive(Debug)]
pub(crate) struct IterMut<'a, T: 'a> {
    positions: Positions,
    data: IterOwnedData<slice::IterMut<'a, T>>,
}

impl<'a, T: 'a> IterMut<'a, T> {
    pub(crate) fn positions(&self) -> Positions {
        self.positions
    }
    pub(crate) fn with_positions(self) -> IterMutWithPositions<'a, T> {
        let IterMut { positions, data } = self;
        IterMutWithPositions { positions, data }
    }
    fn get_unchecked(&mut self, x: usize, y: usize) -> &'a mut T {
        self.data.get_unchecked(x, y)
    }
    fn get_unchecked_back(&mut self, x: usize, y: usize) -> &'a mut T {
        self.data.get_unchecked_back(x, y)
    }
}

impl_positions_wrapper!(('a, T), IterMut, &'a mut T);

#[derive(Debug)]
pub(crate) struct IntoIterWithPositions<T> {
    positions: Positions,
    data: IterOwnedData<vec::IntoIter<T>>,
}

impl<T> IntoIterWithPositions<T> {
    pub(crate) fn positions(&self) -> Positions {
        self.positions
    }
    pub(crate) fn without_positions(self) -> IntoIter<T> {
        let IntoIterWithPositions { positions, data } = self;
        IntoIter { positions, data }
    }
    fn get_unchecked(&mut self, x: usize, y: usize) -> ((usize, usize), T) {
        ((x, y), self.data.get_unchecked(x, y))
    }
    fn get_unchecked_back(&mut self, x: usize, y: usize) -> ((usize, usize), T) {
        ((x, y), self.data.get_unchecked_back(x, y))
    }
}

impl_positions_wrapper!((T), IntoIterWithPositions, ((usize, usize), T));

#[derive(Debug)]
pub(crate) struct IntoIter<T> {
    positions: Positions,
    data: IterOwnedData<vec::IntoIter<T>>,
}

impl<T> IntoIter<T> {
    pub(crate) fn positions(&self) -> Positions {
        self.positions
    }
    pub(crate) fn with_positions(self) -> IntoIterWithPositions<T> {
        let IntoIter { positions, data } = self;
        IntoIterWithPositions { positions, data }
    }
    fn get_unchecked(&mut self, x: usize, y: usize) -> T {
        self.data.get_unchecked(x, y)
    }
    fn get_unchecked_back(&mut self, x: usize, y: usize) -> T {
        self.data.get_unchecked_back(x, y)
    }
}

impl_positions_wrapper!((T), IntoIter, T);

impl<'a, Data: Array2DData> IntoIterator for &'a Array2DBase<Data> {
    type Item = &'a Data::Element;
    type IntoIter = Iter<'a, Data::Element>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T: 'a, Data: Array2DData<Element = T> + BorrowMut<[T]>> IntoIterator
    for &'a mut Array2DBase<Data>
{
    type Item = &'a mut Data::Element;
    type IntoIter = IterMut<'a, Data::Element>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<Data: Array2DData> IntoIterator for Array2DBase<Data> {
    type Item = <Data::IntoIter as Iterator>::Item;
    type IntoIter = Data::IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        Data::into_iter(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_positions() {
        let expected_positions_list = &[(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)];
        for operation_mask in 0..(1 << expected_positions_list.len()) {
            println!();
            let mut positions = Positions::new(2, 3);
            let mut expected_positions = expected_positions_list.iter().copied();
            dbg!(positions);
            assert_eq!(positions.len(), expected_positions.len());
            for operation_index in 0..expected_positions_list.len() {
                if (operation_mask & (1 << operation_index)) != 0 {
                    let position = dbg!(positions.next());
                    let expected_position = expected_positions.next();
                    assert_eq!(position, expected_position);
                } else {
                    let position = dbg!(positions.next_back());
                    let expected_position = expected_positions.next_back();
                    assert_eq!(position, expected_position);
                }
                dbg!(positions);
                assert_eq!(positions.len(), expected_positions.len());
            }
        }
    }

    #[test]
    fn test_iter_mut() {
        let mut array = Array2DOwned::new_with_positions(2, 3, |x, y| x * 10 + y);
        let expected_list: Vec<_> = array.data().iter().copied().collect();
        for operation_mask in 0..(1 << expected_list.len()) {
            println!();
            let mut expected = expected_list.iter().copied();
            let mut iter_mut = array.iter_mut();
            dbg!(&iter_mut);
            assert_eq!(expected.len(), iter_mut.len());
            for operation_index in 0..expected_list.len() {
                if (operation_mask & (1 << operation_index)) != 0 {
                    let value = dbg!(iter_mut.next()).copied();
                    let expected_value = expected.next();
                    assert_eq!(value, expected_value);
                } else {
                    let value = dbg!(iter_mut.next_back()).copied();
                    let expected_value = expected.next_back();
                    assert_eq!(value, expected_value);
                }
                dbg!(&iter_mut);
                assert_eq!(expected.len(), iter_mut.len());
            }
        }
    }
}
