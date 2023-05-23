#[macro_export]
// the inner language [weight => value]+
// desugar it into a series of if else statements
macro_rules! gen_inner {
    ($i:ident, [$w:expr => $v:expr]) => {
        $v
    };
    ($i:ident, [$w1:expr => $v1:expr] [$w2:expr => $v2:expr] $([$ws:expr => $vs:expr])*) => {
        if $i < $w1 {
            $v1
        } else {
            crate::gen_inner!($i, [$w1+$w2 => $v2] $([$ws => $vs])*)
        }
    };
}

// accumulate the weight of the inner language
#[macro_export]
macro_rules! accum {
    () => {
        0
    };
    ([$w1:expr => $v1:expr] $([$ws:expr => $vs:expr])*) => {
        $w1 + crate::accum!($([$ws => $vs])*)
    }
}

// the top level language `u, w => v,+` where `u` is a `Unstructured`, `w` is the weight, and `v` is the value to generate
// it desugars into something like
// {
//      let x = u.int_in_range::<u8>(0..(w1+w2+...+wn-1))?;
//      if x < w1 { v1 } else {
//          if x < w1 + w2 { v2 } else {
//              if x < w1 + w2 + w3 { v3 } else {
//                  ... else { vn }
//              }
//          }
//      }
#[macro_export]
macro_rules! gen {
    ($u:ident, $($ws:expr => $vs:expr),+) => {
        {
            let x = $u.int_in_range::<u8>(0..=((crate::accum!($([$ws => $vs])+)-1)))?;
            crate::gen_inner!(x, $([$ws => $vs])+)
        }
    };
}

// a short circuit to uniformly generate values
// it desguars to the language above where all weights are 1
#[macro_export]
macro_rules! uniform {
    ($u:ident, $($es:expr),+) => {
        {
            let x = $u.int_in_range::<u8>(0..=((crate::accum!($([1 => $es])+)-1)))?;
            crate::gen_inner!(x, $([1 => $es])+)
        }
    };
}
