(component
  (core module (;0;)
    (type (;0;) (func (param i32) (result i32)))
    (func (;0;) (type 0) (param i32) (result i32)
      unreachable
    )
    (export "foo#c" (func 0))
  )
  (core instance (;0;) (instantiate 0))
  (type (;0;) u8)
  (type (;1;) (func (param "a" 0) (result 0)))
  (alias core export 0 "foo#c" (core func (;0;)))
  (func (;0;) (type 1) (canon lift (core func 0)))
  (instance (;0;)
    (export "a" (type 0))
    (export "b" (type 0))
    (export "c" (func 0))
  )
  (export (;1;) "foo" (instance 0))
)