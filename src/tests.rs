use super::*;

#[test]
fn empty() {
    assert_eq!(().to_tuple_list(), EmptyTupleList);
    assert_eq!((),                 EmptyTupleList.to_tuple());
}

#[test]
fn single() {
    assert_eq!((false,).to_tuple_list(), (false, EmptyTupleList));
    assert_eq!((false,),                 (false, EmptyTupleList).to_tuple());
}

#[test]
fn double() {
    assert_eq!((false, 1).to_tuple_list(), (false, (1, EmptyTupleList)));
    assert_eq!((false, 1),                 (false, (1, EmptyTupleList)).to_tuple());
}

#[test]
fn triple() {
    assert_eq!((false, 1, String::from("abc")).to_tuple_list(), (false, (1, (String::from("abc"), EmptyTupleList))));
    assert_eq!((false, 1, String::from("abc")),                 (false, (1, (String::from("abc"), EmptyTupleList))).to_tuple());
}

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
        let _a : tuple_list!() = Default::default();
        let _b : tuple_list!(i32) = Default::default();
        let _c : tuple_list!(i32,) = Default::default();
        let _d : tuple_list!(i32,bool) = Default::default();
        let _e : tuple_list!(i32,bool,) = Default::default();
    }
}

#[test]
fn traits() {
    // test clone (and eq)
    let list : tuple_list!(bool, i32, String) = tuple_list!(false, 1, String::from("abc"));
    assert_eq!(list.clone(), list); // test clone and eq

    // test copy
    fn consume(_: tuple_list!(i32, bool)) {}
    let copy : tuple_list!(i32, bool) = tuple_list!(5, false);
    consume(copy);
    consume(copy);

    // test debug
    assert_eq!(format!("{:?}", tuple_list!(1, false, "abc")), "(1, (false, (\"abc\", EmptyTupleList)))");

    // test default
    let default: tuple_list!(i32, bool, String) = Default::default();
    assert_eq!(default, tuple_list!(0, false, String::new()));

    // test hash, ensure compiles
    use std::hash::Hash;
    use std::collections::hash_map::DefaultHasher;
    let mut hasher = DefaultHasher::new();
    EmptyTupleList.hash(&mut hasher);
    tuple_list!(false).hash(&mut hasher);
    tuple_list!(false, String::from("abc")).hash(&mut hasher);

    // test ord (and therefore partialrod, eq and partialeq)
    assert!(tuple_list!(false) < tuple_list!(true));
    assert!(tuple_list!(1, 2) < tuple_list!(2, 3));
    assert!(tuple_list!(5, 3) > tuple_list!(2, 3));
    assert_eq!(tuple_list!(String::from("foo"), false), tuple_list!(String::from("foo"), false));
    assert_ne!(tuple_list!(String::from("foo"), false), tuple_list!(String::from("foo"), true));
}
