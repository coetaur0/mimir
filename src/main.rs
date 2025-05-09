use mim::parsing;

fn main() {
    let src = "fn f<'a>(r: &'a i32, mut x: i32) -> &'a i32 { let t: &(i32, i32); (*t).1 = 3; if true { return g() } else { (1, 3) }; r }";
    match parsing::parse(src) {
        Ok(ir) => println!("{:#?}", ir),
        Err(errors) => {
            for error in errors {
                println!("{:#?}", error)
            }
        }
    }
}
