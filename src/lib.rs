#![allow(non_snake_case)] // non-snake case identifiers used in define_tuple_list_traits! for simplicity
#![doc(html_playground_url = "https://play.rust-lang.org/")]

//! Crate for variadic tuple metaprogramming.
//! 
//! # Rationale
//! 
//! As of writing this crate, rust does not support variadic generics
//! and does not allow to reason about tuples in general.
//! 
//! Most importantly, rust does not allow one to generically
//! implement a trait for all tuples whose elements implement it.
//! 
//! This crate attempts to fill the gap by providing a way
//! to recursively define traits for tuples.
//! 
//! # Tuple lists
//! 
//! Tuple `(A, B, C, D)` can be unambiguously mapped into recursive tuple `(A, (B, (C, (D, ()))))`.
//! 
//! On each level it consists of a pair `(Head, Tail)`, where `Head` is tuple element and
//! `Tail` is a remainder of the list. For last element `Tail` is an empty list.
//! 
//! Unlike regular flat tuples, such recursive tuples can be effectively reasoned about in rust.
//! 
//! This crate calls such structures "tuple lists" and provides a set of traits and macros
//! allowing one to conveniently work with them.
//! 
//! # Example 1: `CustomDisplay` recursive trait
//! 
//! Let's create a simple `Display`-like trait implemented for all tuples
//! whose elements implement it.
//! 
//! ```
//! // Define trait and implement it for several standard types.
//! trait CustomDisplay {
//!     fn fmt(&self) -> String;
//! }
//! impl CustomDisplay for i32  { fn fmt(&self) -> String { self.to_string() } }
//! impl CustomDisplay for bool { fn fmt(&self) -> String { self.to_string() } }
//! impl CustomDisplay for &str { fn fmt(&self) -> String { self.to_string() } }
//! 
//! // Now we have to implement trait for empty tuple,
//! // thus defining initial condition.
//! impl CustomDisplay for () {
//!     fn fmt(&self) -> String { String::new() }
//! }
//! 
//! // Now we can implement trait for a non-empty tuple list, 
//! // this defining recursion and supporting tuple lists of arbitrary length.
//! impl<Head, Tail> CustomDisplay for (Head, Tail) where
//!     Head: CustomDisplay,
//!     Tail: CustomDisplay,
//! {
//!     fn fmt(&self) -> String {
//!         let (head, tail) = self;
//!         return format!("{} {}", head.fmt(), tail.fmt());
//!     }
//! }
//! 
//! // `tuple_list!` macro creates tuple lists from list of arguments.
//! use tuple_list::tuple_list;
//!
//! // Ensure `fmt` is called for each element.
//! let tuple_list = tuple_list!(2, false, "abc");
//! assert_eq!(
//!     tuple_list.fmt(),
//!     "2 false abc ",
//! );
//! 
//! // Since tuple lists implement `CustomDisplay`, they can
//! // be elements in other tuple lists implementing `CustomDisplay`.
//! let nested_tuple_list = tuple_list!(2, false, "abc", tuple_list!(3, true, "def"));
//! assert_eq!(
//!     nested_tuple_list.fmt(),
//!     "2 false abc 3 true def  ",
//! );
//! ```
//! 
//! # Example 2: `PlusOne` recursive trait
//! 
//! Let's create a trait which adds one to each element of a tuple,
//! behaving differently depending on element type.
//! 
//! ```
//! // Define trait and implement it for several primitive types.
//! trait PlusOne {
//!     fn plus_one(&mut self);
//! }
//! impl PlusOne for i32    { fn plus_one(&mut self) { *self += 1; } }
//! impl PlusOne for bool   { fn plus_one(&mut self) { *self = !*self; } }
//! impl PlusOne for String { fn plus_one(&mut self) { self.push('1'); } }
//! 
//! // Now we have to implement trait for empty tuple,
//! // thus defining initial condition.
//! impl PlusOne for () {
//!     fn plus_one(&mut self) {}
//! }
//! 
//! // Now we can implement trait for a non-empty tuple list, 
//! // this defining recursion and supporting tuple lists of arbitrary length.
//! impl<Head, Tail> PlusOne for (Head, Tail) where
//!     Head: PlusOne,
//!     Tail: PlusOne,
//! {
//!     fn plus_one(&mut self) {
//!         self.0.plus_one();
//!         self.1.plus_one();
//!     }
//! }
//! 
//! # use tuple_list::tuple_list;
//! // Now we can use our trait on tuple lists.
//! let mut tuple_list = tuple_list!(2, false, String::from("abc"));
//! tuple_list.plus_one();
//! 
//! // tuple_list! macro also allows us to unpack tuple lists
//! let tuple_list!(a, b, c) = tuple_list;
//! assert_eq!(a, 3);
//! assert_eq!(b, true);
//! assert_eq!(&c, "abc1");
//! ```
//! 
//! # Example 3: `SwapStringAndInt` recursive trait
//! 
//! Let's implement a trait which converts `i32` to `String` and vice versa.
//! 
//! This example is way more complex because it maps tuple list into
//! another tuple list.
//! 
//! ```
//! // Let's define and implement trait for i32 and String
//! // so that it converts String to i32 and vice versa.
//! trait SwapStringAndInt {
//!     type Other;
//!     fn swap(self) -> Self::Other;
//! }
//! impl SwapStringAndInt for i32 {
//!     type Other = String;
//!     fn swap(self) -> String { self.to_string() }
//! }
//! impl SwapStringAndInt for String {
//!     type Other = i32;
//!     fn swap(self) -> i32 { self.parse().unwrap() }
//! }
//! 
//! // Now we have to implement trait for empty tuple,
//! // thus defining initial condition.
//! impl SwapStringAndInt for () {
//!     type Other = ();
//!     fn swap(self) {}
//! }
//! 
//! // Now we can implement trait for a non-empty tuple list, 
//! // this defining recursion and supporting tuple lists of arbitrary length.
//! impl<Head, Tail> SwapStringAndInt for (Head, Tail) where Head: SwapStringAndInt, Tail: SwapStringAndInt {
//!     type Other = (Head::Other, Tail::Other);
//!     fn swap(self) -> Self::Other {
//!         (self.0.swap(), self.1.swap())
//!     }
//! }
//! 
//! # use tuple_list::tuple_list;
//! let original = tuple_list!(4, String::from("2"), 7, String::from("13"));
//! 
//! // Tuple lists implement `SwapStringAndInt` by calling `SwapStringAndInt::swap`
//! // on each member and returnign tuple list of resulting values.
//! let swapped = original.swap();
//! 
//! // Not that types of elements have changed.
//! assert_eq!(
//!     swapped,
//!     tuple_list!(String::from("4"), 2, String::from("7"), 13),
//! );
//! 
//! // Since tuple lists now implement SwapStringAndInt,
//! // they can even contain nested tuple lists:
//! let nested = tuple_list!(tuple_list!(1, String::from("2")), 3);
//! let nested_swapped = nested.swap();
//! assert_eq!(
//!     nested_swapped,
//!     tuple_list!(tuple_list!(String::from("1"), 2), String::from("3")),
//! );
//! 
//! // Now, we can't implement `SwapStringAndInt` for regular tuples
//! // because it would conflict with tuple list implementation,
//! // but we can define helper function allowing us to use `swap`
//! // on regular tuples seamlessly.
//! use tuple_list::Tuple;
//! use tuple_list::TupleList;
//! 
//! // Argument of this function is a regular tuple, not a tuple list.
//! fn swap<T, TL, OtherTL>(tuple: T) -> OtherTL::Tuple where
//!     T: Tuple<TupleList=TL>, // argument type
//!     TL: TupleList + SwapStringAndInt<Other=OtherTL>, // tuple list corresponding to argument tuple
//!     OtherTL: TupleList, // another tuple list, result of `SwapStringAndInt::swap` applied to original tuple list
//! {
//!     tuple.to_tuple_list().swap().to_tuple()
//! }
//! 
//! // Now we can indirectly use `SwapStringAndInt` with regular tuples.
//! let original_tuple = (4, String::from("2"), 7, String::from("13"));
//! let swapped_tuple = swap(original_tuple);
//! assert_eq!(
//!     swapped_tuple,
//!     (String::from("4"), 2, String::from("7"), 13),
//! );
//! ```
//! 
//! # Tuple lists and tuples interoperability
//! 
//! This crate defines `Tuple` and `TupleList` traits, which
//! are automatically implemented and allow you to convert
//! tuples into tuple lists and vice versa.
//! 
//! Best way to handle interoperability is to store your data
//! as tuple lists and convert to tuples if necessary.
//! 
//! Anoter reasonable alternative is to use helper function like
//! the one described in `SwapStringAndInt` example.
//! 
//! Please note that tuple/tuple list conversions are
//! destructive and consume the original, which may pose a problem
//! in some cases.
//! 
//! # Implementing recursive traits for regular tuples
//! 
//! Previous examples described how to implement recursive traits
//! for tuple lists. If you really, really need to implement 
//! recursive traits on regular tuples, it's possible,
//! but not recommended. Such implementations are extremely
//! complex and have serious limitations.
//! 
//! There are two major problems:
//! 
//! 1. Trait implementation for regular tuples may conflict with
//!    implementation for tuple lists.
//! 2. Reference to tuple cannot be transformed
//!    into reference to tuple list.
//! 
//! Both problems are solveable, but working around them makes
//! code extremely complex.
//! 
//! Depending on your use case, you may have to do this:
//! 1. In order to avoid implementations conflict,
//!    add separate trait mirroring the main one,
//!    which will be used for typed list only.
//! 2. Handling `self` and `&self` is very different in
//!    recursive traits for regular tuples. As a result
//!    you may have to split your trait into parts that
//!    accept `self` in the same way.
//! 3. You may have to add generic lifetime to your original
//!    trait. It's not mandatory, but without it nesting
//!    won't work properly.
//! 
//! All use cases can be broadly grouped into two types depending
//! on how `self` is passed into function.
//! 
//! ## Implementing traits with functions which accept `self` by value
//!    
//!    The major problem in this case is the fact
//!    that trait implementation for tuple list
//!    will conflict with trait implementation for
//!    regular tuple.
//!
//!    General solution is to create separate trait
//!    mirroring the main one, which will only used for type lists.
//!
//!    Naive solution will break nesting, but there is
//!    a way to solve that with pretty complex birecursion.
//!
//!    For details please see `tuple_lists::tests::swap_string_and_int_dual_traits_recursion`.
//! 
//! ## Implementing traits with functions which accept `self` by reference or mutable reference
//!
//!    General idea is to convert refernce to tuple into
//!    tuple of references, then convert tuple of references into
//!    tuple list, and then use recursive traits as usual.
//!
//!    The main problem is that recursive trait implementation 
//!    must have generic lifetime argument in order to
//!    track lifetimes of references in tuple list.
//!
//!    This makes it impossible to unambiguously implement
//!    recursive trait for regular tuples, unless original trait
//!    has free generic lifetime argument.
//! 
//!    For an example of this approach see `tuple_lists::tests::plus_one_tuple_list_trait_with_lifetime`.
//!
//!    If it is impossible or not practical to add generic lifetime
//!    argument to the original trait, then it's possible to only
//!    implement recursive trait for tuple lists, as a result
//!    breaking nesting.
//! 
//!    For an example of this approach see `tuple_lists::tests::plus_one_tuple_list_trait_without_lifetime`.
//! 
//! # Rust unstable fetaures and future
//! 
//! This crate works at the edge of what's possible with current type system of rust.
//! 
//! Following planned or unstable features will significantly affect this crate when implemented:
//! 
//! 1. Associated generic types will remove extra lifetime argument requirement
//!    in recursive traits implemented for regular tuples.
//! 2. Trait specialization will allow crate users to use
//!    `TupleCons` and `NonEmptyTuple` traits to define
//!    traits directly on regular tuples,
//!    without recursion through tuple lists.
//! 3. Obviously, as soon as rust implements variadic generics, 
//!    this crate will become obsolete and deprecated.

/*
tuple list recursion
tuple interoperation
tuple value recursion
tuple reference recursion: trait with lifetime
tuple reference recursion: trait without lifetime
*/

/// Trait providing conversion from tuple list into tuple.
///
/// Generic trait implemented for all tuple lists (up to 12 elements).
/// 
/// # Examples
/// 
/// ```
/// use crate::tuple_list::tuple_list;
/// use crate::tuple_list::TupleList;
/// 
/// let tuple_list = tuple_list!(1, false, String::from("abc"));
/// 
/// assert_eq!(
///     tuple_list.to_tuple(),
///     (1, false, String::from("abc")),
/// );
/// ```
pub trait TupleList {
    /// Tuple type corresponding to given tuple list.
    type Tuple: Tuple;

    /// Converts TupleList to tuple.
    fn to_tuple(self) -> Self::Tuple;
}

/// Trait providing conversion from tuple into tuple list.
/// 
/// Generic trait implemented for all tuples (up to 12 elements).
/// 
/// # Examples
/// 
/// ```
/// use crate::tuple_list::Tuple;
/// 
/// let tuple = (1, false, String::from("abc"));
/// 
/// assert_eq!(
///     tuple.to_tuple_list(), 
///     (1, (false, (String::from("abc"), ()))),
/// );
/// ```
pub trait Tuple {
    /// Tuple list type corresponding to given tuple.
    type TupleList: TupleList;

    /// Converts tuple into tuple list.
    fn to_tuple_list(self) -> Self::TupleList;
}

/// Trait providing conversion from references to tuples into tuples of references.
/// 
/// Generic trait implemented for all tuples (up to 12 elements).
/// 
/// # Example
/// ```
/// use tuple_list::TupleAsRef;
/// 
/// fn by_val(tuple: (i32, i32)) {}
/// fn by_ref(tuple: (&i32, &i32)) {}
/// fn by_mut(tuple: (&mut i32, &mut i32)) {}
/// 
/// let mut tuple = (1, 2);
/// by_val(tuple);
/// by_ref(tuple.as_ref());
/// by_mut(tuple.as_mut());
/// ```
// TODO: when rust gets generic associated types
//       move this trait content into Tuple
pub trait TupleAsRef<'a>: Tuple {
    type TupleOfRefs: Tuple;
    type TupleOfMutRefs: Tuple;

    /// Convertes reference to tuple into tuple of references.
    fn as_ref(&'a self) -> Self::TupleOfRefs;

    /// Convertes mutable reference to tuple into tuple of mutable references.
    fn as_mut(&'a mut self) -> Self::TupleOfMutRefs;
}

/// Trait providing tuple construction function, allows to prepend a value to a tuple.
/// 
/// 
// TODO: when rust gets generic associated types
//       move this trait content into Tuple
pub trait TupleCons<Head>: Tuple {
    /// Tuple with `Head` prepended to `Self`
    type ResultingTuple: Tuple;

    /// Constructs a tuple from `head` value and `tail` tuple by prepending `head` to `tail`.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use tuple_list::TupleCons;
    /// 
    /// let a = TupleCons::cons("foo", ());
    /// assert_eq!(
    ///     a,
    ///     ("foo",),
    /// );
    /// 
    /// let b = TupleCons::cons(false, a);
    /// assert_eq!(
    ///     b,
    ///     (false, "foo"),
    /// );
    /// 
    /// let c = TupleCons::cons(4, b);
    /// assert_eq!(
    ///     c,
    ///     (4, false, "foo"),
    /// );
    /// ```
    fn cons(head: Head, tail: Self) -> Self::ResultingTuple;
}

/// Trait allowing to recursively deconstruct tuples.
/// 
/// Generic trait implemented for all non-empty tuples (up to 12 elements).
/// 
/// Most interesting part is that this trait allows you to recursively
/// define some simple traits for regular tuples.
/// 
/// Unofrtunately, it's not quite complete and is pretty unusable as of now.
/// 
/// In order ot be usable outside of this crate it needs support
/// for trait specializations in rust.
/// 
/// In order to properly support implementing traits using for non-value `self`,
/// it needs support for generic associate types.
pub trait NonEmptyTuple: Tuple {
    /// First element of `Self` tuple.
    type Head;
    /// Tuple of remaining elements of `Self` tuple.
    type Tail: Tuple;

    /// Reverse of `TupleCons::cons`, splits `Self` tuple into head value and tail tuple.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use tuple_list::NonEmptyTuple;
    /// 
    /// let abcz = (4, false, "foo");
    /// let (a, bcz) = NonEmptyTuple::uncons(abcz);
    /// let (b, cz) = NonEmptyTuple::uncons(bcz);
    /// let (c, z)  = NonEmptyTuple::uncons(cz);
    /// 
    /// assert_eq!(a, 4);
    /// assert_eq!(b, false);
    /// assert_eq!(c, "foo");
    /// assert_eq!(z, ());
    /// ```
    fn uncons(self) -> (Self::Head, Self::Tail);

    /// Returns first element of a tuple.
    ///
    /// Same as `TupleCons::uncons().0`.
    fn head(self) -> Self::Head;

    /// Returns all but the first element of a tuple.
    /// 
    /// Same as `TupleCons::uncons().1`.
    fn tail(self) -> Self::Tail;
}

/// Macro creating tuple list values from list of expressions.
/// 
/// # Examples
/// 
/// Main use of this macro is to create tuple list values:
/// 
/// ```
/// use tuple_list::tuple_list;
/// 
/// let list = tuple_list!(10, false, "foo");
/// 
/// assert_eq!(
///   list,
///   (10, (false, ("foo", ()))),
/// )
/// ```
/// 
/// Aside from that, `tuple_list!` can sometime be used to define trivial types,
/// but using macro `tuple_list_type!` is recommended instead:
/// 
/// ```
/// # use tuple_list::tuple_list;
/// # use std::collections::HashMap;
/// // trivial types work just fine with tuple_list!
/// let list: tuple_list!(i32, bool, String) = Default::default();
/// 
/// // more complex types will fail when using tuple_list!
/// // but will work with tuple_list_type!
/// use tuple_list::tuple_list_type;
/// 
/// let list: tuple_list_type!(
///     &'static str, 
///     HashMap<i32, i32>, 
///     <std::vec::Vec<bool> as IntoIterator>::Item,
/// ) = tuple_list!("foo", HashMap::new(), false);
/// ```
/// 
/// It can also be used to unpack tuples:
/// 
/// ```
/// # use tuple_list::tuple_list;
/// #
/// let tuple_list!(a, b, c) = (10, (false, ("foo", ())));
/// 
/// assert_eq!(a, 10);
/// assert_eq!(b, false);
/// assert_eq!(c, "foo");
/// ```
/// 
/// Unfortunately, due to rust macro limitations only simple, non-nested match patterns are supported.
/// 
/// It is technically possible to create two separate traits for tuples and tuple lists in order
/// to avoid ambiguity, but result still won't be ergonomic and probably isn't worth it.
#[macro_export]
macro_rules! tuple_list {
    () => ( () );

    // handling simple identifiers, for limited types and patterns support
    ($i:ident)  => ( ($i, ()) );
    ($i:ident,) => ( ($i, ()) );
    ($i:ident, $($e:ident),*)  => ( ($i, tuple_list!($($e),*)) );
    ($i:ident, $($e:ident),*,) => ( ($i, tuple_list!($($e),*)) );

    // handling complex expressions
    ($i:expr)  => ( ($i, ()) );
    ($i:expr,) => ( ($i, ()) );
    ($i:expr, $($e:expr),*)  => ( ($i, tuple_list!($($e),*)) );
    ($i:expr, $($e:expr),*,) => ( ($i, tuple_list!($($e),*)) );
}

/// Macro creating tuple list types from list of element types.
/// 
/// See macro `tuple_list!` for details.
#[macro_export]
macro_rules! tuple_list_type {
    () => ( () );
    
    ($i:ty)  => ( ($i, ()) );
    ($i:ty,) => ( ($i, ()) );
    ($i:ty, $($e:ty),*)  => ( ($i, tuple_list_type!($($e),*)) );
    ($i:ty, $($e:ty),*,) => ( ($i, tuple_list_type!($($e),*)) );
}

// helper, returns first argument, ignores the rest
macro_rules! list_head {
    ($i:ident) => ( $i );
    ($i:ident, $($e:ident),+) => ( $i );
}

// helper, returns all arguments but the first one
macro_rules! list_tail {
    ($i:ident) => ( () );
    ($i:ident, $e:ident) => ( ($e,) );
    ($i:ident, $($e:ident),+) => ( ($($e),*,) );
}

// defines Tuple, TupleList, TupleCons, NonEmptyTuple and TupleAsRef
macro_rules! define_tuple_list_traits {
    () => (
        impl TupleList for () {
            type Tuple = ();
            fn to_tuple(self) {}
        }
        impl Tuple for () {
            type TupleList = ();
            fn to_tuple_list(self) {}
        }
        impl<'a> TupleAsRef<'a> for () {
            type TupleOfRefs = ();
            type TupleOfMutRefs = ();
            fn as_ref(&'a self) {}
            fn as_mut(&'a mut self) {}
        }
    );
    ($($x:ident),*) => (
        impl<$($x),*> TupleList for tuple_list_type!($($x),*) {
            type Tuple = ($($x),*,);
            fn to_tuple(self) -> Self::Tuple {
                let tuple_list!($($x),*) = self;
                return ($($x),*,)
            }
        }
        impl<$($x),*> Tuple for ($($x),*,) {
            type TupleList = tuple_list_type!($($x),*);
            fn to_tuple_list(self) -> Self::TupleList {
                let ($($x),*,) = self;
                return tuple_list!($($x),*);
            }
        }
        impl<'a, $($x: 'a),*> TupleAsRef<'a> for ($($x),*,) {
            type TupleOfRefs = ($(&'a $x),*,);
            type TupleOfMutRefs = ($(&'a mut $x),*,);
            fn as_ref(&'a self) -> Self::TupleOfRefs {
                let ($($x),*,) = self;
                return ($($x),*,);
            }
            fn as_mut(&'a mut self) -> Self::TupleOfMutRefs {
                let ($($x),*,) = self;
                return ($($x),*,);
            }
        }
        impl<$($x),*> NonEmptyTuple for ($($x),*,) {
            type Head = list_head!($($x),*);
            type Tail = list_tail!($($x),*);
            fn uncons(self) -> (Self::Head, Self::Tail) {
                let ($($x),*,) = self;
                return (list_head!($($x),*), list_tail!($($x),*));
            }
            fn head(self) -> Self::Head { self.0 }
            fn tail(self) -> Self::Tail { self.uncons().1 }
        }
        impl<$($x),*> TupleCons<list_head!($($x),*)> for list_tail!($($x),*) {
            type ResultingTuple = ($($x),*,);
            fn cons(head: list_head!($($x),*), tail: Self) -> Self::ResultingTuple {
                let list_head!($($x),*) = head;
                let list_tail!($($x),*) = tail;
                return ($($x),*,);
            }
        }
    );
}

// rust only defines common traits for tuples up to 12 elements
// we'll do the same here, increase number if needed
define_tuple_list_traits!();
define_tuple_list_traits!(T1);
define_tuple_list_traits!(T1, T2);
define_tuple_list_traits!(T1, T2, T3);
define_tuple_list_traits!(T1, T2, T3, T4);
define_tuple_list_traits!(T1, T2, T3, T4, T5);
define_tuple_list_traits!(T1, T2, T3, T4, T5, T6);
define_tuple_list_traits!(T1, T2, T3, T4, T5, T6, T7);
define_tuple_list_traits!(T1, T2, T3, T4, T5, T6, T7, T8);
define_tuple_list_traits!(T1, T2, T3, T4, T5, T6, T7, T8, T9);
define_tuple_list_traits!(T1, T2, T3, T4, T5, T6, T7, T8, T9, T10);
define_tuple_list_traits!(T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11);
define_tuple_list_traits!(T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12);

#[cfg(test)]
mod tests;
