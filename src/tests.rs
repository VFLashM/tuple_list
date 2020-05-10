use super::*;

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
    let t : tuple_list!(i32, &'static str, HashMap<i32, i32>) = (1, ("abc", (HashMap::new(), ())));
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
    assert_eq!(format!("{:?}", tuple_list!(1, false, "abc")), "(1, (false, (\"abc\", ())))");

    // test default
    let default: tuple_list!(i32, bool, String) = Default::default();
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
