# Description

This repo contains a library for performing polynomial arithmetic in a way that allows for compile-time checking of degree constraints for each arithmetic operation.  What that means is that polynomials are constructed as arrays of fixed lengths depending on the degree, and any attempt to perform an operation on polynomials of incorrect sizes will cause compiler errors.

# How to Build
```
cargo build
```

# How to Test
```
cargo test
```

# Examples
See unit tests in tests module.