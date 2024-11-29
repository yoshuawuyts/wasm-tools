use std::vec;

use wasm_encoder::Module;
use wasm_metadata::*;

#[test]
fn add_to_empty_module() {
    let module = Module::new().finish();
    let add = AddMetadata {
        name: Some("foo".to_owned()),
        language: vec!["bar".to_owned()],
        processed_by: vec![("baz".to_owned(), "1.0".to_owned())],
        sdk: vec![],
        registry_metadata: None,
    };
    let module = add.to_wasm(&module).unwrap();

    let metadata = Metadata::from_binary(&module).unwrap();
    match metadata {
        Metadata::Module {
            name,
            producers,
            range,
        } => {
            assert_eq!(name, Some("foo".to_owned()));
            let producers = producers.expect("some producers");
            assert_eq!(producers.get("language").unwrap().get("bar").unwrap(), "");
            assert_eq!(
                producers.get("processed-by").unwrap().get("baz").unwrap(),
                "1.0"
            );

            assert_eq!(range.start, 0);
            assert_eq!(range.end, 422);
        }
        _ => panic!("metadata should be module"),
    }
}
