use std::vec;

use wasm_encoder::Module;
use wasm_metadata::*;

#[test]
fn add_to_empty_module() {
    let module = Module::new().finish();
    let add = AddMetadata {
        name: Some("foo".to_owned()),
        language: vec![("bar".to_owned(), "1.0".to_owned())],
        processed_by: vec![("baz".to_owned(), "1.0".to_owned())],
        sdk: vec![],
        author: Some(Author::new("Chashu Cat")),
        description: Some(Description::new("Chashu likes tuna")),
        licenses: Some(
            Licenses::new("Apache-2.0 WITH LLVM-exception OR Apache-2.0 OR MIT").unwrap(),
        ),
        source: Some(Source::new("https://github.com/bytecodealliance/wasm-tools").unwrap()),
    };
    let module = add.to_wasm(&module).unwrap();

    let metadata = Metadata::from_binary(&module).unwrap();
    match metadata {
        Metadata::Module {
            name,
            producers,
            author,
            description,
            licenses,
            source,
            range,
        } => {
            assert_eq!(name, Some("foo".to_owned()));
            let producers = producers.expect("some producers");
            assert_eq!(
                producers.get("language").unwrap().get("bar").unwrap(),
                "1.0"
            );
            assert_eq!(
                producers.get("processed-by").unwrap().get("baz").unwrap(),
                "1.0"
            );

            assert_eq!(author.unwrap(), Author::new("Chashu Cat"));
            assert_eq!(description.unwrap(), Description::new("Chashu likes tuna"));
            assert_eq!(
                licenses.unwrap(),
                Licenses::new("Apache-2.0 WITH LLVM-exception OR Apache-2.0 OR MIT").unwrap()
            );
            assert_eq!(
                source.unwrap(),
                Source::new("https://github.com/bytecodealliance/wasm-tools").unwrap(),
            );

            assert_eq!(range.start, 0);
            assert_eq!(range.end, 241);
        }
        _ => panic!("metadata should be module"),
    }
}