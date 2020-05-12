use super::*;

#[test]
fn all_features() {

    trait NumberOrString {
        type OtherType;

        fn into_other(self) -> Self::OtherType;
        fn format(&self) -> String;
        fn plus_one(&mut self);
    }

    impl NumberOrString for i32 {
        type OtherType = String;

        fn into_other(self) -> Self::OtherType { self.to_string() }
        fn format(&self) -> String { self.to_string() }
        fn plus_one(&mut self) { *self += 1; }
    }

    impl NumberOrString for String {
        type OtherType = i32;

        fn into_other(self) -> Self::OtherType { self.parse().unwrap() }
        fn format(&self) -> String { self.clone() }
        fn plus_one(&mut self) { self.push('1'); }
    }

    // split original trait into separate traits
    // for each kind of `self`
    trait NumberOrStringTupleListValue: TupleList {
        type OtherType: TupleList;

        fn into_other(self) -> Self::OtherType;
    }
    trait NumberOrStringRef {
        fn format_ref(self) -> String; // note that self is by value here
    }
    trait NumberOrStringMutRef {
        fn plus_one_ref(self); // note that self is by value here
    }

    // initial condition
    impl NumberOrStringTupleListValue for Empty {
        type OtherType = Empty;

        fn into_other(self) -> Self::OtherType { Empty }
    }
    impl NumberOrStringRef for Empty {
        fn format_ref(self) -> String { String::new() }
    }
    impl NumberOrStringMutRef for Empty {
        fn plus_one_ref(self) {}
    }

    // recursion
    impl<Head, Tail> NumberOrStringTupleListValue for Pair<Head, Tail> where
        Head: NumberOrString,
        Tail: NumberOrStringTupleListValue,
        Self: TupleList,
        Pair<Head::OtherType, Tail::OtherType>: TupleList,
    {
        type OtherType = Pair<Head::OtherType, Tail::OtherType>;

        fn into_other(self) -> Self::OtherType {
            Pair(self.0.into_other(), self.1.into_other())
        }
    }

    impl<Head, Tail> NumberOrStringRef for Pair<&Head, Tail> where
        Head: NumberOrString,
        Tail: NumberOrStringRef + TupleList,
        Self: TupleList,
    {
        fn format_ref(self) -> String {
            format!("{} {}", self.0.format(), self.1.format_ref())
        }
    }

    impl<Head, Tail> NumberOrStringMutRef for Pair<&mut Head, Tail> where
        Head: NumberOrString,
        Tail: NumberOrStringMutRef + TupleList,
        Self: TupleList,
    {
        fn plus_one_ref(self) {
            self.0.plus_one();
            self.1.plus_one_ref();
        }
    }

    // impl for refs
    impl<'a, T, RT, RTL> NumberOrStringRef for &'a T where
        T: AsTupleOfRefs<'a, TupleOfRefs=RT>,
        RT: Tuple<TupleList=RTL> + 'a,
        RTL: NumberOrStringRef + TupleList,
    {
        fn format_ref(self) -> String {
            self.as_tuple_of_refs().into_tuple_list().format_ref()
        }
    }

    impl<'a, T, RT, RTL> NumberOrStringMutRef for &'a mut T where
        T: AsTupleOfRefs<'a, TupleOfMutRefs=RT>,
        RT: Tuple<TupleList=RTL> + 'a,
        RTL: NumberOrStringMutRef + TupleList,
    {
        fn plus_one_ref(self) {
            self.as_tuple_of_mut_refs().into_tuple_list().plus_one_ref()
        }
    }


    // implementation for tuples
    impl<T> NumberOrString for T where
        T: Tuple,
        T::TupleList: NumberOrStringTupleListValue,
        for<'a> &'a T: NumberOrStringRef,
        for<'a> &'a mut T: NumberOrStringMutRef,
    {
        type OtherType = <<<T as Tuple>::TupleList as NumberOrStringTupleListValue>::OtherType as TupleList>::Tuple;

        fn into_other(self) -> Self::OtherType {
            self.into_tuple_list().into_other().into_tuple()
        }
        fn format(&self) -> String {
            self.format_ref()
        }
        fn plus_one(&mut self) {
            self.plus_one_ref()
        }
    }

    let src = (1, String::from("2"), 3, String::from("4"));
    let dst = (String::from("1"), 2, String::from("3"), 4);
    assert_eq!(
        src.into_other(),
        dst,
    );

    let src = (1, String::from("2"), 3, String::from("4"));
    assert_eq!(
        src.format(),
        "1 2 3 4 ",
    );

    let mut src = (1, String::from("2"), 3, String::from("4"));
    src.plus_one();
    assert_eq!(
        src,
        (2, String::from("21"), 4, String::from("41")),
    );
}

#[test]
fn reverse_test() {
    trait Rewind<Done: TupleList> {
        type RewindResult: TupleList;

        fn rewind(self, done: Done) -> Self::RewindResult;
    }

    impl<Done: TupleList> Rewind<Done> for Empty {
        type RewindResult = Done;

        fn rewind(self, done: Done) -> Done { done }
    }

    impl<Done, Next, Tail> Rewind<Done> for Pair<Next, Tail> where 
        Done: TupleList,
        Pair<Next, Done>: TupleList,
        Tail: Rewind<Pair<Next, Done>> + TupleList,
    {
        type RewindResult = Tail::RewindResult;

        fn rewind(self, done: Done) -> Self::RewindResult {
            let Pair(next, tail) = self;
            return tail.rewind(Pair(next, done));
        }
    }

    fn reverse<T>(t: T) -> T::RewindResult where
        T: Rewind<Empty>
    {
        t.rewind(Empty)
    }

    let original = tuple_list!(1, "foo", false);
    let reversed = tuple_list!(false, "foo", 1);
    assert_eq!(reverse(original), reversed);
}

#[test]
fn append_test() {
    trait Append<T>: TupleList {
        type AppendResult: TupleList;

        fn append(self, value: T) -> Self::AppendResult;
    }

    impl<T> Append<T> for Empty {
        type AppendResult = Pair<T, Empty>;

        fn append(self, value: T) -> Self::AppendResult { Pair(value, Empty) }
    }

    impl<Head, Tail, T> Append<T> for Pair<Head, Tail> where
        Self: TupleList,
        Tail: Append<T>,
        Pair<Head, Tail::AppendResult>: TupleList,
    {
        type AppendResult = Pair<Head, Tail::AppendResult>;

        fn append(self, value: T) -> Self::AppendResult { 
            let Pair(head, tail) = self;
            return Pair(head, tail.append(value));
        }
    }

    let original = tuple_list!(1, "foo", false);
    let appended = tuple_list!(1, "foo", false, 5);
    assert_eq!(original.append(5), appended);
}

#[test]
fn swap_string_and_int_dual_traits_recursion() {
    // real trait, implemented for tuples and primitive types
    trait SwapStringAndInt     {
        type Other;
        fn swap(self) -> Self::Other;
    }
    impl SwapStringAndInt for i32 {
        type Other = String;
        fn swap(self) -> String { self.to_string() }
    };
    impl SwapStringAndInt for String {
        type Other = i32;
        fn swap(self) -> i32 { self.parse().unwrap() }
    };

    // helper trait, only used for recursion on tuple lists
    // goes to SwapStringAndInt for action conversion
    // implemented for tuple lists
    trait SwapStringAndIntTupleList {
        type Other;
        fn swap(self) -> Self::Other;
    }
    // initial condition for recursion
    impl SwapStringAndIntTupleList for Empty {
        type Other = Empty;
        fn swap(self) -> Empty { Empty }
    }
    impl<Head, Tail> SwapStringAndIntTupleList for Pair<Head, Tail> where
        Head: SwapStringAndInt,
        Tail: SwapStringAndIntTupleList + TupleList,
        Tail::Other: TupleList,
    {
        type Other = Pair<Head::Other, Tail::Other>;
        fn swap(self) -> Self::Other {
            // note that actual work is done by `SwapStringAndInt` trait
            // head is `SwapStringAndInt`, tail is converted to tuple
            // which is also `SwapStringAndInt` and then converted back to tuple list
            Pair(self.0.swap(), self.1.swap())
        }
    }

    // implementation of `SwapStringAndInt` for tuples
    impl<T, TL, OtherTL> SwapStringAndInt for T where
        T: Tuple<TupleList=TL>,
        TL: TupleList + SwapStringAndIntTupleList<Other=OtherTL>,
        OtherTL: TupleList,
    {
        type Other = OtherTL::Tuple;
        fn swap(self) -> Self::Other {
            // goes to SwapStringAndIntTupleList for recursion
            // converts result back to tuple
            self.into_tuple_list().swap().into_tuple()
        }
    }

    // Create tuple value.
    let original = (4, String::from("2"), 7, String::from("13"));

    // Tuples implement `SwapStringAndInt`
    let swapped = original.swap();
    assert_eq!(
        swapped,
        (String::from("4"), 2, String::from("7"), 13),
    );

    // nesting  works too
    let nested_tuple = ((1, String::from("2"), 3), 4);
    let nested_tuple_swapped = nested_tuple.swap();
    assert_eq!(
        nested_tuple_swapped,
        ((String::from("1"), 2, String::from("3")), String::from("4")),
    );
}

#[test]
fn swap_string_and_int_tuple() {
    trait SwapStringAndInt {
        type Other;
        fn swap(self) -> Self::Other;
    }
    impl SwapStringAndInt for i32 {
        type Other = String;
        fn swap(self) -> String { self.to_string() }
    }
    impl SwapStringAndInt for String {
        type Other = i32;
        fn swap(self) -> i32 { self.parse().unwrap() }
    }

    impl SwapStringAndInt for () {
        type Other = ();
        fn swap(self) {}
    }

    impl<Head, Tail, TailOther, T> SwapStringAndInt for T where 
        T: NonEmptyTuple<Head=Head, Tail=Tail>,
        Head: SwapStringAndInt,
        Tail: Tuple + SwapStringAndInt<Other=TailOther>,
        TailOther: TupleCons<Head::Other>,
    {
        type Other = TailOther::ConstructedTuple; // resulting from TupleCons
        fn swap(self) -> Self::Other {
            let (head, tail) = self.uncons();
            return TupleCons::cons(head.swap(), tail.swap());
        }
    }

    let original = (4, String::from("2"), 7, String::from("13"));

    let swapped = original.swap();
    assert_eq!(
        swapped,
        (String::from("4"), 2, String::from("7"), 13),
    );

    let nested = ((1, String::from("2")), 3);
    let nested_swapped = nested.swap();
    assert_eq!(
        nested_swapped,
        ((String::from("1"), 2), String::from("3")),
    );
}

#[test]
fn custom_display_tuple() {
    // Define trait and implement it for several standard types.
    trait CustomDisplay {
        fn fmt(self) -> String;
    }
    impl CustomDisplay for i32    { fn fmt(self) -> String { self.to_string() } }
    impl CustomDisplay for bool   { fn fmt(self) -> String { self.to_string() } }
    impl CustomDisplay for String { fn fmt(self) -> String { self } }

    impl CustomDisplay for () {
        fn fmt(self) -> String { String::new() }
    }

    impl<Head, Tail, T> CustomDisplay for T where
        T: NonEmptyTuple<Head=Head, Tail=Tail>,
        Head: CustomDisplay,
        Tail: CustomDisplay + Tuple,
    {
        fn fmt(self) -> String {
            let (head, tail) = self.uncons();
            return format!("{} {}", head.fmt(), tail.fmt());
        }
    }

    let tuple = (2, false, String::from("abc"));
    assert_eq!(
        tuple.fmt(),
        "2 false abc ",
    );

    let recursive_tuple = (2, false, String::from("abc"), (3, true, String::from("def")));
    assert_eq!(
        recursive_tuple.fmt(),
        "2 false abc 3 true def  ",
    );
}

#[test]
fn plus_one_tuple() {
    trait PlusOne<'a> {
        fn plus_one(&'a mut self);
    }

    impl<'a> PlusOne<'a> for i32    { fn plus_one(&'a mut self) { *self += 1; } }
    impl<'a> PlusOne<'a> for bool   { fn plus_one(&'a mut self) { *self = !*self; } }
    impl<'a> PlusOne<'a> for String { fn plus_one(&'a mut self) { self.push('1'); } }

    trait PlusOneTuple: Tuple {
        fn plus_one(self);
    }

    impl PlusOneTuple for () {
        fn plus_one(self) {}
    }

    impl<'a, Head, Tail, T> PlusOneTuple for T where 
        Head: PlusOne<'a> + 'a,
        Tail: PlusOneTuple + 'a,
        T: NonEmptyTuple<Head=&'a mut Head, Tail=Tail> + 'a
    {
        fn plus_one(self) {
            let (head, tail) = self.uncons();
            head.plus_one();
            tail.plus_one();
        }
    }

    impl<'a, T, RT> PlusOne<'a> for T where
        T: NonEmptyTuple + AsTupleOfRefs<'a, TupleOfMutRefs=RT>,
        RT: PlusOneTuple + 'a,
    {
        fn plus_one(&'a mut self) {
            self.as_tuple_of_mut_refs().plus_one()
        }
    }

    let mut tuple = (2, false, String::from("abc"));
    tuple.plus_one();
    let (a, b, c) = tuple;
    assert_eq!(a, 3);
    assert_eq!(b, true);
    assert_eq!(&c, "abc1");
}

#[test]
fn plus_one_tuple_list_trait_with_lifetime() {
    // trait needs free generic lifetime argument
    // for implementation to be unambiguous
    trait PlusOne<'a> {
        fn plus_one(&'a mut self);
    }

    // implemented for primitive types
    impl<'a> PlusOne<'a> for i32    { fn plus_one(&'a mut self) { *self += 1; } }
    impl<'a> PlusOne<'a> for bool   { fn plus_one(&'a mut self) { *self = !*self; } }
    impl<'a> PlusOne<'a> for String { fn plus_one(&'a mut self) { self.push('1'); } }

    // separate trait for recursion
    // implemented for tuple lists
    //
    // note that `self` is passed by value
    // in this case `self` is a tuple list
    // of references, which is consumed
    trait PlusOneTupleList: TupleList {
        fn plus_one(self);
    }

    // initial condition
    impl PlusOneTupleList for Empty {
        fn plus_one(self) {}
    }

    // recursion
    impl<'a, Head, Tail> PlusOneTupleList for Pair<&'a mut Head, Tail> where 
        Head: PlusOne<'a> + 'a,
        Tail: PlusOneTupleList + 'a,
        Self: TupleList,
    {
        fn plus_one(self) {
            self.0.plus_one();
            self.1.plus_one();
        }
    }

    // original trait implementation for regular tuples
    impl<'a, T, RT, RTL> PlusOne<'a> for T where
        T: AsTupleOfRefs<'a, TupleOfMutRefs=RT>, // tuple argument which can be converted into tuple of references
        RT: Tuple<TupleList=RTL> + 'a,        // tuple of references which can be converted into tuple list
        RTL: TupleList + PlusOneTupleList,    // tuple list which implements recursive trait
    {
        fn plus_one(&'a mut self) {
            // 1. converts reference to tuple into tuple of references
            // 2. converts tuple of references into tuple list of references
            // 3. calls recursive trait on tuple list
            self.as_tuple_of_mut_refs().into_tuple_list().plus_one();
        }
    }

    // now original trait can be used on regular tuples
    // nesting works
    let mut tuple = (2, false, String::from("abc"));
    tuple.plus_one();
    let (a, b, c) = tuple;
    assert_eq!(a, 3);
    assert_eq!(b, true);
    assert_eq!(&c, "abc1");
}

#[test]
fn plus_one_tuple_list_trait_without_lifetime() {
    // define trait and implement it for primitive types
    trait PlusOne {
        fn plus_one(&mut self);
    }
    impl PlusOne for i32    { fn plus_one(&mut self) { *self += 1; } }
    impl PlusOne for bool   { fn plus_one(&mut self) { *self = !*self; } }
    impl PlusOne for String { fn plus_one(&mut self) { self.push('1'); } }

    // separate trait for recursion
    // implemented for tuple lists
    //
    // note that `self` is passed by value
    // in this case `self` is a tuple list
    // of references, which is consumed
    trait PlusOneTupleList: TupleList {
        fn plus_one(self);
    }

    // initial condition
    impl PlusOneTupleList for Empty {
        fn plus_one(self) {}
    }

    // recursion
    impl<'a, Head, Tail> PlusOneTupleList for Pair<&'a mut Head, Tail> where 
        Head: PlusOne + 'a,
        Tail: PlusOneTupleList + 'a,
        Self: TupleList,
    {
        fn plus_one(self) {
            self.0.plus_one();
            self.1.plus_one();
        }
    }

    // regular tuples do not implement any traits
    // but it's possible to add a helper function which
    // will accept tuple and call function of recursive trait
    fn plus_one<'a, T, RT, Head, Tail>(tuple: &'a mut T) where
        T: AsTupleOfRefs<'a, TupleOfMutRefs=RT>,           // tuple argument which can be converted into tuple of references
        RT: Tuple<TupleList=Pair<Head, Tail>> + 'a,     // tuple of references which can be converted into tuple list
        Pair<Head, Tail>: TupleList + PlusOneTupleList, // tuple list which implements recursive trait
        Tail: TupleList,
    {
        // 1. converts reference to tuple into tuple of references
        // 2. converts tuple of references into tuple list of references
        // 3. calls recursive trait on tuple list
        tuple.as_tuple_of_mut_refs().into_tuple_list().plus_one();
    }

    // helper function can be used to invoke trait function
    // on regular tuples
    // nesting does not work because tuples don't implement the trait
    let mut tuple = (2, false, String::from("abc"));
    plus_one(&mut tuple);
    let (a, b, c) = tuple;
    assert_eq!(a, 3);
    assert_eq!(b, true);
    assert_eq!(&c, "abc1");
}

#[test]
fn empty() {
    assert_eq!(().into_tuple_list(), Empty);
    assert_eq!((),                 Empty.into_tuple());
}

#[test]
fn single() {
    assert_eq!((false,).into_tuple_list(), Pair(false, Empty));
    assert_eq!((false,),                 Pair(false, Empty).into_tuple());
}

#[test]
fn double() {
    assert_eq!((false, 1).into_tuple_list(), Pair(false, Pair(1, Empty)));
    assert_eq!((false, 1),                 Pair(false, Pair(1, Empty)).into_tuple());
}

#[test]
fn triple() {
    assert_eq!((false, 1, String::from("abc")).into_tuple_list(), Pair(false, Pair(1, Pair(String::from("abc"), Empty))));
    assert_eq!((false, 1, String::from("abc")),                 Pair(false, Pair(1, Pair(String::from("abc"), Empty))).into_tuple());
}

#[test]
fn complex_types() {
    use std::collections::HashMap;
    let t : tuple_list_type!(i32, &str, HashMap<i32, i32>) = Pair(1, Pair("abc", Pair(HashMap::new(), Empty)));
    let tuple_list!(a, b, c) = t;
    assert_eq!(a, 1);
    assert_eq!(b, "abc");
    assert_eq!(c, HashMap::new());
}

#[test]
fn complex_values() {
    let s = String::from("abc");
    let t = tuple_list!(s.len(), s, 2 + 3);
    let tuple_list!(a, b, c) = t;
    assert_eq!(a, 3);
    assert_eq!(b, String::from("abc"));
    assert_eq!(c, 5);
}

/*
#[test]
fn complex_unpack() {
    let tuple_list!(a, Some(tuple_list!(b, c, d))) = tuple_list!(1, Some(tuple_list!(2, 3, 4)))
    assert_eq!(a, 1);
    assert_eq!(b, 2);
    assert_eq!(c, 3);
    assert_eq!(d, 4);
}
*/

#[test]
fn trailing_comma() {
    { // values
        let _a = tuple_list!();
        let _b = tuple_list!(0);
        let _c = tuple_list!(0,);
        let _d = tuple_list!(0,false);
        let _e = tuple_list!(0,false,);
    }
    { // types
        let _a : tuple_list_type!() = Default::default();
        let _b : tuple_list_type!(i32) = Default::default();
        let _c : tuple_list_type!(i32,) = Default::default();
        let _d : tuple_list_type!(i32,bool) = Default::default();
        let _e : tuple_list_type!(i32,bool,) = Default::default();
    }
}

#[test]
fn traits() {
    // test clone (and eq)
    let list : tuple_list_type!(bool, i32, String) = tuple_list!(false, 1, String::from("abc"));
    assert_eq!(list.clone(), list); // test clone and eq

    // test copy
    fn consume(_: tuple_list_type!(i32, bool)) {}
    let copy : tuple_list_type!(i32, bool) = tuple_list!(5, false);
    consume(copy);
    consume(copy);

    // test debug
    assert_eq!(format!("{:?}", tuple_list!(1, false, "abc")), "Pair(1, Pair(false, Pair(\"abc\", Empty)))");

    // test default
    let default: tuple_list_type!(i32, bool, String) = Default::default();
    assert_eq!(default, tuple_list!(0, false, String::new()));

    // test hash, ensure compiles
    use std::hash::Hash;
    use std::collections::hash_map::DefaultHasher;
    let mut hasher = DefaultHasher::new();
    ().hash(&mut hasher);
    tuple_list!(false).hash(&mut hasher);
    tuple_list!(false, String::from("abc")).hash(&mut hasher);

    // test ord (and therefore partialrod, eq and partialeq)
    assert!(tuple_list!(false) < tuple_list!(true));
    assert!(tuple_list!(1, 2) < tuple_list!(2, 3));
    assert!(tuple_list!(5, 3) > tuple_list!(2, 3));
    assert_eq!(tuple_list!(String::from("foo"), false), tuple_list!(String::from("foo"), false));
    assert_ne!(tuple_list!(String::from("foo"), false), tuple_list!(String::from("foo"), true));
}
