use super::*;

#[test]
fn swap_string_and_int_simple_tuple() {
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

    // Now we have to implement trait for empty tuple,
    // thus defining initial condition.
    impl SwapStringAndInt for () {
        type Other = ();
        fn swap(self) {}
    }

    // Now we can implement trait for a non-empty tuple list, 
    // this defining recursion and supporting tuple lists of arbitrary length.
    impl<Head, Tail> SwapStringAndInt for (Head, Tail) where Head: SwapStringAndInt, Tail: SwapStringAndInt {
        type Other = (Head::Other, Tail::Other);
        fn swap(self) -> Self::Other {
            (self.0.swap(), self.1.swap())
        }
    }

    // Create tuple list value.
    let original = tuple_list!(4, String::from("2"), 7, String::from("13"));

    // Tuple lists implement `SwapStringAndInt` by calling `SwapStringAndInt::swap`
    // on each member and returnign tuple list of resulting values.
    let swapped = original.swap();
    assert_eq!(
        swapped,
        tuple_list!(String::from("4"), 2, String::from("7"), 13),
    );

    // Since tuple lists now implement SwapStringAndInt,
    // they can even contain nested tuple lists:
    let nested = tuple_list!(tuple_list!(1, String::from("2")), 3);
    let nested_swapped = nested.swap();
    assert_eq!(
        nested_swapped,
        tuple_list!(tuple_list!(String::from("1"), 2), String::from("3")),
    );

    fn swap<T, TL, OtherTL>(tuple: T) -> OtherTL::Tuple where
        T: Tuple<TupleList=TL>,
        TL: TupleList + SwapStringAndInt<Other=OtherTL>,
        OtherTL: TupleList,
    {
        tuple.to_tuple_list().swap().to_tuple()
    }
    let original_tuple = (4, String::from("2"), 7, String::from("13"));
    let swapped_tuple = swap(original_tuple);
    assert_eq!(
        swapped_tuple,
        (String::from("4"), 2, String::from("7"), 13),
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
        type Other = TailOther::ResultingTuple; // resulting from TupleCons
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
        T: NonEmptyTuple + TupleAsRef<'a, TupleOfMutRefs=RT>,
        RT: PlusOneTuple,
    {
        fn plus_one(&'a mut self) {
            self.as_mut().plus_one()
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
fn plus_one_tuple_list() {
    trait PlusOne<'a> {
        fn plus_one(&'a mut self);
    }

    impl<'a> PlusOne<'a> for i32    { fn plus_one(&'a mut self) { *self += 1; } }
    impl<'a> PlusOne<'a> for bool   { fn plus_one(&'a mut self) { *self = !*self; } }
    impl<'a> PlusOne<'a> for String { fn plus_one(&'a mut self) { self.push('1'); } }

    trait PlusOneTupleList {
        fn plus_one(self);
    }

    impl PlusOneTupleList for () {
        fn plus_one(self) {}
    }

    impl<'a, Head, Tail> PlusOneTupleList for (&'a mut Head, Tail) where 
        Head: PlusOne<'a> + 'a,
        Tail: PlusOneTupleList + 'a,
    {
        fn plus_one(self) {
            self.0.plus_one();
            self.1.plus_one();
        }
    }

    impl<'a, T, RT, Head, Tail> PlusOne<'a> for T where
        T: TupleAsRef<'a, TupleOfMutRefs=RT>,
        RT: Tuple<TupleList=(Head, Tail)>,
        (Head, Tail): TupleList + PlusOneTupleList,
    {
        fn plus_one(&'a mut self) {
            self.as_mut().to_tuple_list().plus_one();
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
fn plus_one_adapter() {
    trait PlusOne {
        fn plus_one(&mut self);
    }

    impl PlusOne for i32    { fn plus_one(&mut self) { *self += 1; } }
    impl PlusOne for bool   { fn plus_one(&mut self) { *self = !*self; } }
    impl PlusOne for String { fn plus_one(&mut self) { self.push('1'); } }

    trait PlusOneTupleList {
        fn plus_one(self);
    }

    impl PlusOneTupleList for () {
        fn plus_one(self) {}
    }

    impl<'a, Head, Tail> PlusOneTupleList for (&'a mut Head, Tail) where 
        Head: PlusOne + 'a,
        Tail: PlusOneTupleList + 'a,
    {
        fn plus_one(self) {
            self.0.plus_one();
            self.1.plus_one();
        }
    }

    fn plus_one<'a, T, RT, Head, Tail>(tuple: &'a mut T) where
        T: TupleAsRef<'a, TupleOfMutRefs=RT>,
        RT: Tuple<TupleList=(Head, Tail)>,
        (Head, Tail): TupleList + PlusOneTupleList,
    {
        tuple.as_mut().to_tuple_list().plus_one();
    }

    let mut tuple = (2, false, String::from("abc"));
    plus_one(&mut tuple);
    let (a, b, c) = tuple;
    assert_eq!(a, 3);
    assert_eq!(b, true);
    assert_eq!(&c, "abc1");
}

#[test]
fn empty() {
    assert_eq!(().to_tuple_list(), ());
    assert_eq!((),                 ().to_tuple());
}

#[test]
fn single() {
    assert_eq!((false,).to_tuple_list(), (false, ()));
    assert_eq!((false,),                 (false, ()).to_tuple());
}

#[test]
fn double() {
    assert_eq!((false, 1).to_tuple_list(), (false, (1, ())));
    assert_eq!((false, 1),                 (false, (1, ())).to_tuple());
}

#[test]
fn triple() {
    assert_eq!((false, 1, String::from("abc")).to_tuple_list(), (false, (1, (String::from("abc"), ()))));
    assert_eq!((false, 1, String::from("abc")),                 (false, (1, (String::from("abc"), ()))).to_tuple());
}

#[test]
fn complex_types() {
    use std::collections::HashMap;
    let t : tuple_list_type!(i32, &str, HashMap<i32, i32>) = (1, ("abc", (HashMap::new(), ())));
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
    assert_eq!(format!("{:?}", tuple_list!(1, false, "abc")), "(1, (false, (\"abc\", ())))");

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
