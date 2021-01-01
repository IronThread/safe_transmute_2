#![no_std]

//! This library provide a completely safe transmute.

extern crate alloc;

use core::{
    any::{TypeId, type_name}, 
    char, 
    mem::ManuallyDrop, 
    num::*, 
    ptr::NonNull, 
    str, 
    mem::size_of, 
    slice
};

use alloc::{
    alloc::Layout,
    boxed::Box,
};

/// Reinterprets the bits of one type to another,without checking the size.
///
/// See [`mem::transmute`] for safety concerns and examples.
#[inline]
unsafe fn transmute<T, U>(x: T) -> U {
    // it's already undefined behaviour if the layouts mismatch so packed can be seen as safe
    #[repr(C, packed)]
    union Transmutter<T, U> {
        a: ManuallyDrop<T>,
        b: ManuallyDrop<U>,
    }

    ManuallyDrop::into_inner(
        Transmutter { 
            a: ManuallyDrop::new(x),
        }
        .b,
    )
}

/*
just a drawn for the derive macro please ignore

#[doc(hidden)]
pub trait S: Sized { }

impl<T> S for T { }
#[doc(hidden)]
pub fn a<T: S>(_: T) { }

#[derive(Transmutable)]
pub struct Foo {
    non_zero: NonZeroU8,
    non_zero1: NonZeroU8,
}

#[repr(C)]
pub struct Foo {
    non_zero: NonZeroU8,
    non_zero1: NonZeroU8,
}

mod a {
    const A: fn(Foo) = crate::a<Foo>;
    type Field1 = <NonZeroU8 as Transmutable>::Dummy;
    type Field2 = <NonZeroU8 as Transmutable>::Dummy;

    unsafe impl Transmutable for FooDummy {
        type Dummy = Self;
        type ElementType = Self;

        fn is_valid(x: &Self::Dummy) -> bool {
            true
        }
    }


    unsafe impl Transmutable for Foo {
        type Dummy = FooDummy;
        type ElementType = Self;

        fn is_valid(x: &Self::Dummy) -> bool {
            Field1::is_valid(x.0) && Field2::is_valid(x.1)
        }
    }

    unsafe impl Transmutable for Foo {
        type Dummy = FooDummy;
        type ElementType = Field2::ElementType;

        fn is_valid(x: &Self::Dummy) -> bool {
            Field1::is_valid(x.0) && Field2::is_valid(x.1)
        }
    }

    // another crate artificial
    use external_crate::Foo;

    fn assert_sized::<T>(_: T) {  }
    const _: fn(Foo) = assert_sized::<Foo>;

    // in my macro
    let mut f = OpenOptions::new().write(true).create(true).open("sized_checker.rs");

    write!(f, "{} Foo {}\n{}", keyword_used, body, include_str!("artificial_crate_code.rs"));

    f.sync_all();

    if Command::new("rustc").arg("sized_checker.rs").status().success() {
        // sized case goes here
    } else {
        // not sized case goes here
    };

    fs::remove_file("sized_checked.rs");
}
#[doc(hidden)]
#[repr(C)]
pub struct FooDummy(Field1, Field2);
*/

/// A type that should be implemented in all types that have not all their fields public upholding
/// all their invariants in `Self::is_valid(dummy: &Self::Dummy)` see [`Self::Dummy`].
/// 
/// This type cannot be implemented in types holding non-static references and will cause UB on
/// static ones,see [`Self::transmute_ref`],[`Self::transmute_mut`] and [`Self::transmute_box`].
pub unsafe trait Transmutable: 'static {
    /// A dummy type to convert to before transmuting to check for invalid values,this has to have
    /// the same layout as `Self` but no invalid values reported by `Self`.
    /// 
    /// This means that you can set `Dummy` to a inner type of `Self` that has some invariants but
    /// not those added in `Self` and reported by `is_valid` as types willing to transmute to
    /// `Self` will use the transmutable implementation if they are not `Dummy`,for that,`Dummy`
    /// must implement `Transmutable`,and even further,types with no value invariant have to put
    /// `Dummy = Self` so this it's observed by the implementation preventing an infinite bucle,
    /// many primitives implement it so,note that the compiler believes that a type implement a
    /// trait while you're inside the implementation.
    type Dummy: Transmutable + ?Sized;

    /// Element type on slices,has to be `Self` on others.
    type ElementType;

    /// Indicates whether the dummy value it's safe to transmute to `Self`.
    fn is_valid(x: &Self::Dummy) -> bool;

    /// Transmutes `T` to `Self` returning an `Err` with `T` when the layouts mismatch or the
    /// associated function `is_valid` returns `false`.
    #[inline]
    fn transmute<T: Transmutable + 'static>(self) -> Result<T, Self> where Self: Sized + 'static {
        T::transmute_i(self)
    }

    // okay,Imma explain this useless impl detail in a few words,back in the past I thought `T`
    // may or may not implement `Transmutable` so I put it without trait bounds; when I realized
    // it wrong was too late and I had a lot of code I don't want to refactorize so,as it does not
    // do anything than the shame of hiding it from the docs,I will not work on.
    // 
    // PRs apreciated if you are a bit more strict.
    #[doc(hidden)]
    fn transmute_i<T: Transmutable + 'static>(x: T) -> Result<Self, T>
    where
        Self: Sized + 'static,
    {
        // debug_assert_eq!(Layout::new::<Self::Dummy>(), Layout::new::<T>());

        /*
        extern "C" {
            fn a(x: T, y: T::Dummy, z: Self, a: Self::Dummy);
        }
        */

        if Layout::new::<T>() == Layout::new::<Self>() {
            unsafe {
                // as the docs pointed out,if the type of `Self` it's equal to `Dummy` then it does
                // not have invalid values and can be transmuted from any layout equivalent data
                if TypeId::of::<Self>() == TypeId::of::<Self::Dummy>()
                    || TypeId::of::<Self>() == TypeId::of::<T>()
                {
                    Ok(transmute(x))
                } else {
                    let dummy = match TransmutableRef::transmute(&x) {
                        Ok(x) => x,
                        Err(_) => return Err(x)
                    };

                    if Self::is_valid(dummy) {
                        Ok(transmute(x))
                    } else {
                        Err(transmute(x))
                    }
                }
            }
        } else {
            Err(x)
        }
    }

    /// Same as `Self::transmute` but can operate on references and cast the size away.
    fn transmute_ref<T: TransmutableRef>(&self) -> Result<T, &Self> {
        TransmutableRef::transmute(self)
    }

    /// Same as `Self::transmute` but can operate on mutable references and cast the size away.
    fn transmute_mut<T: TransmutableMut>(&mut self) -> Result<T, &mut Self> {
        TransmutableMut::transmute(self)
    }

    /// Same as `Self::transmute` but can operate on boxed values.
    fn transmute_box<T: TransmutableBox>(self: Box<Self>) -> Result<T, Box<Self>> where Self: Sized {
        TransmutableBox::transmute(self)
    }
}

#[doc(hidden)]
pub trait TransmutableRef: Sized {
    fn transmute<T: TransmutableRef>(self) -> Result<T, Self>;

    unsafe fn transmute_i<T: ?Sized + Transmutable + 'static>(x: &T) -> Result<Self, &T>;
}

impl<'a, U: Transmutable + ?Sized + 'static> TransmutableRef for &'a U {
    fn transmute<T: TransmutableRef>(self) -> Result<T, Self> {
        unsafe { T::transmute_i(self) }
    }

    #[doc(hidden)]
    unsafe fn transmute_i<T: ?Sized + Transmutable + 'static>(x: &T) -> Result<Self, &T> {
        // debug_assert_eq!(Layout::new::<Self::Dummy>(), Layout::new::<T>());

        let input_is_sized = size_of::<*const T>() == size_of::<usize>();
        let output_is_sized = size_of::<*const Self>() == size_of::<usize>();

        if !(input_is_sized || type_name::<U>().starts_with("[")) || !(output_is_sized || type_name::<U>().starts_with("[")) {
            panic!("Custom DST's are not supported ;).")
        }

        if input_is_sized {
            if output_is_sized {
                // T::element_type() && Self::element_type();
                let output = Layout::new::<U::ElementType>();
                let input = Layout::new::<T::ElementType>();

                if output.align() == input.align() && input.size() >= output.size() {
                    if TypeId::of::<U>() == TypeId::of::<U::Dummy>() || TypeId::of::<U>() == TypeId::of::<T>() {
                        Ok(transmute(x))
                    } else {
                        let dummy = TransmutableRef::transmute(x)?;

                        if U::is_valid(dummy) {
                            Ok(transmute(dummy))
                        } else {
                            Err(transmute(dummy))
                        }
                    }
                } else {
                    Err(x)
                }
            } else {
                // slice case,trait objects not supported
                let a = size_of::<T::ElementType>();
                let b = size_of::<U::ElementType>();
                let mut len = 0;

                while let Some(e) = a.checked_sub(b) {
                    len += 1;
                }

                if len > 0 {
                    let x = slice::from_raw_parts(x as *const T as *const T::ElementType, len);

                    if TypeId::of::<[T::ElementType]>() == TypeId::of::<T::Dummy>() || TypeId::of::<U>() == TypeId::of::<T>() {
                        Ok(transmute(x))
                    } else {
                        let dummy = TransmutableRef::transmute(transmute::<_, &T>(x))?;

                        if T::is_valid(dummy) {
                            Ok(transmute(dummy))
                        } else {
                            Err(transmute(dummy))
                        }
                    }
                } else {
                    Err(x)
                }
            }
        } else {
            if output_is_sized {
                let z = Layout::for_value(x);

                let len = z.size() / size_of::<T::ElementType>();
                let y = Layout::new::<U::ElementType>();

                if Layout::new::<T::ElementType>() == y {
                    return if TypeId::of::<U>() == TypeId::of::<U::Dummy>() || TypeId::of::<U>() == TypeId::of::<T>() {
                        Ok(transmute(x))
                    } else {
                        let dummy = TransmutableRef::transmute(x)?;

                        if U::is_valid(dummy) {
                            Ok(transmute(dummy))
                        } else {
                            Err(transmute(dummy))
                        }
                    };
                }

                if z.align() != y.align() {
                    return Err(x);
                }

                // slice case,trait objects not supported
                let a = y.size();
                let b = size_of::<T::ElementType>();
                let mut len = 0;

                while let Some(e) = a.checked_sub(b) {
                    len += 1;
                }

                if len > 0 {
                    let x = slice::from_raw_parts(x as *const T as *const T::ElementType, len);

                    if TypeId::of::<U>() == TypeId::of::<U::Dummy>() || TypeId::of::<U>() == TypeId::of::<T>() {
                        Ok(transmute(x))
                    } else {
                        let dummy = TransmutableRef::transmute(transmute::<_, &T>(x))?;

                        if U::is_valid(dummy) {
                            Ok(transmute(dummy))
                        } else {
                            Err(transmute(dummy))
                        }
                    }

                } else {
                    Err(x)
                }
            } else {
                let a = Layout::new::<T::ElementType>();
                let b = Layout::new::<U::ElementType>();
                let z = Layout::for_value(x);
                let len = z.size() / size_of::<T::ElementType>();

                if a == b {
                    return if TypeId::of::<U>() == TypeId::of::<U::Dummy>() || TypeId::of::<U>() == TypeId::of::<T>() {
                        Ok(transmute(x))
                    } else {
                        let dummy = TransmutableRef::transmute(x)?;

                        if U::is_valid(dummy) {
                            Ok(transmute(dummy))
                        } else {
                            Err(transmute(dummy))
                        }
                    };
                }

                if a.align() == b.align() {
                    let d = if a.size() <= b.size() {
                        b.size() / a.size()
                    } else {
                        a.size() / b.size()
                    };

                    let y = x;
                    let x = slice::from_raw_parts(y as *const T as *const U::ElementType, len / d);

                    if TypeId::of::<U>() == TypeId::of::<U::Dummy>() || TypeId::of::<U>() == TypeId::of::<T>() {
                        Ok(transmute(x))
                    } else {
                        let dummy = match TransmutableRef::transmute(transmute::<_, &<U::Dummy as Transmutable>::Dummy>(x)) {
                            Ok(x) => x,
                            Err(_) => return Err(transmute(y))
                        };

                        if U::is_valid(dummy) {
                            Ok(transmute(x))
                        } else {
                            Err(y)
                        }
                    }
                } else {
                    Err(x)
                }
            }
        }
    }

}

#[doc(hidden)]
pub unsafe trait TransmutableMut: Sized {
    fn transmute<T: TransmutableMut>(self) -> Result<T, Self>;

    #[doc(hidden)]
    unsafe fn transmute_i<T: ?Sized + Transmutable + 'static>(x: &mut T) -> Result<Self, &mut T>;
}

unsafe impl<'a, U: Transmutable + ?Sized + 'static> TransmutableMut for &'a mut U {
    fn transmute<T: TransmutableMut>(self) -> Result<T, Self> {
        unsafe { T::transmute_i(self) }
    }

    #[doc(hidden)]
    unsafe fn transmute_i<T: ?Sized + Transmutable + 'static>(x: &mut T) -> Result<Self, &mut T> {
        // debug_assert_eq!(Layout::new::<Self::Dummy>(), Layout::new::<T>());

        let input_is_sized = size_of::<*const T>() == size_of::<usize>();
        let output_is_sized = size_of::<*const Self>() == size_of::<usize>();

        if !(input_is_sized || type_name::<U>().starts_with("[")) || !(output_is_sized || type_name::<U>().starts_with("[")) {
            panic!("Custom DST's are not supported ;).")
        }

        if input_is_sized {
            if output_is_sized {
                // T::element_type() && Self::element_type();
                let output = Layout::new::<U::ElementType>();
                let input = Layout::new::<T::ElementType>();

                if output.align() == input.align() && input.size() >= output.size() {
                    if TypeId::of::<U>() == TypeId::of::<U::Dummy>() || TypeId::of::<U>() == TypeId::of::<T>() {
                        Ok(transmute(x))
                    } else {
                        let dummy = match TransmutableRef::transmute(&*x) {
                            Ok(x) => x,
                            Err(_) => return Err(x)
                        };

                        if U::is_valid(dummy) {
                            Ok(transmute(dummy))
                        } else {
                            Err(transmute(dummy))
                        }
                    }
                } else {
                    Err(x)
                }
            } else {
                // slice case,trait objects not supported
                let a = size_of::<T::ElementType>();
                let b = size_of::<U::ElementType>();
                let mut len = 0;

                while let Some(e) = a.checked_sub(b) {
                    len += 1;
                }

                if len > 0 {
                    let x = slice::from_raw_parts_mut(x as *mut T as *mut T::ElementType, len);

                    if TypeId::of::<[T::ElementType]>() == TypeId::of::<T::Dummy>() || TypeId::of::<U>() == TypeId::of::<T>() {
                        Ok(transmute(x))
                    } else {
                        let dummy = match TransmutableRef::transmute(transmute::<_, &T>(&*x)) {
                            Ok(x) => x,
                            Err(_) => return Err(transmute(x))
                        };

                        if T::is_valid(dummy) {
                            Ok(transmute(dummy))
                        } else {
                            Err(transmute(dummy))
                        }
                    }
                } else {
                    Err(x)
                }
            }
        } else {
            if output_is_sized {
                let z = Layout::for_value(x);

                let len = z.size() / size_of::<T::ElementType>();
                let y = Layout::new::<U::ElementType>();

                if Layout::new::<T::ElementType>() == y {
                    return if TypeId::of::<U>() == TypeId::of::<U::Dummy>() || TypeId::of::<U>() == TypeId::of::<T>() {
                        Ok(transmute(x))
                    } else {
                        let dummy = match TransmutableRef::transmute(&*x) {
                            Ok(x) => x,
                            Err(_) => return Err(x)
                        };

                        if U::is_valid(dummy) {
                            Ok(transmute(dummy))
                        } else {
                            Err(transmute(dummy))
                        }
                    };
                }

                if z.align() != y.align() {
                    return Err(x);
                }

                // slice case,trait objects not supported
                let a = y.size();
                let b = size_of::<T::ElementType>();
                let mut len = 0;

                while let Some(e) = a.checked_sub(b) {
                    len += 1;
                }

                if len > 0 {
                    let x = slice::from_raw_parts_mut(x as *mut T as *mut T::ElementType, len);

                    if TypeId::of::<U>() == TypeId::of::<U::Dummy>() || TypeId::of::<U>() == TypeId::of::<T>() {
                        Ok(transmute(x))
                    } else {
                        let dummy = match TransmutableRef::transmute(transmute::<_, &T>(&*x)) {
                            Ok(x) => x,
                            Err(_) => return Err(transmute(x))
                        };

                        if U::is_valid(dummy) {
                            Ok(transmute(dummy))
                        } else {
                            Err(transmute(dummy))
                        }
                    }

                } else {
                    Err(x)
                }
            } else {
                let a = Layout::new::<T::ElementType>();
                let b = Layout::new::<U::ElementType>();
                let z = Layout::for_value(x);
                let len = z.size() / size_of::<T::ElementType>();

                if a == b {
                    return if TypeId::of::<U>() == TypeId::of::<U::Dummy>() || TypeId::of::<U>() == TypeId::of::<T>() {
                        Ok(transmute(x))
                    } else {
                        let dummy = match TransmutableRef::transmute(&*x) {
                            Ok(x) => x,
                            Err(_) => return Err(x)
                        };

                        if U::is_valid(dummy) {
                            Ok(transmute(dummy))
                        } else {
                            Err(transmute(dummy))
                        }
                    };
                }

                if a.align() == b.align() {
                    let d = if a.size() <= b.size() {
                        b.size() / a.size()
                    } else {
                        a.size() / b.size()
                    };

                    let y = x;
                    let x = slice::from_raw_parts_mut(y as *mut T as *mut U::ElementType, len / d);

                    if TypeId::of::<U>() == TypeId::of::<U::Dummy>() || TypeId::of::<U>() == TypeId::of::<T>() {
                        Ok(transmute(x))
                    } else {
                        let dummy = match TransmutableRef::transmute(transmute::<_, &<U::Dummy as Transmutable>::Dummy>(&*x)) {
                            Ok(x) => x,
                            Err(_) => return Err(transmute(y))
                        };

                        if U::is_valid(dummy) {
                            Ok(transmute(x))
                        } else {
                            Err(y)
                        }
                    }
                } else {
                    Err(x)
                }
            }
        }
    }
}

#[doc(hidden)]
pub unsafe trait TransmutableBox: Sized {
    fn transmute<T: TransmutableBox>(self) -> Result<T, Self>;

    #[doc(hidden)]
    unsafe fn transmute_i<T: ?Sized + Transmutable + 'static>(x: Box<T>) -> Result<Self, Box<T>>;
}

unsafe impl<U: Transmutable + 'static> TransmutableBox for Box<U> {
    fn transmute<T: TransmutableBox>(self) -> Result<T, Self> {
        unsafe { T::transmute_i(self) }
    }

    #[doc(hidden)]
    unsafe fn transmute_i<T: ?Sized + Transmutable + 'static>(x: Box<T>) -> Result<Self, Box<T>> {
        // debug_assert_eq!(Layout::new::<Self::Dummy>(), Layout::new::<T>());

        /*
        extern "C" {
            fn a(x: T, y: T::Dummy, z: Self, a: Self::Dummy);
        }
        */

        if Layout::for_value(&*x) == Layout::new::<Self>() {
            unsafe {
                // as the docs pointed out,if the type of `Self` it's equal to `Dummy` then it does
                // not have invalid values and can be transmuted from any layout equivalent data
                if TypeId::of::<U>() == TypeId::of::<U::Dummy>()
                    || TypeId::of::<U>() == TypeId::of::<T>()
                {
                    Ok(Box::from_raw(Box::into_raw(x) as *mut U))
                } else {
                    let dummy = match TransmutableRef::transmute(&*x) {
                        Ok(x) => x,
                        Err(_) => return Err(x)
                    };

                    if U::is_valid(dummy) {
                        Ok(Box::from_raw(Box::into_raw(x) as *mut U))
                    } else {
                        Err(x)
                    }
                }
            }
        } else {
            Err(x)
        }
    }
}

unsafe impl Transmutable for str {
    type Dummy = [u8];
    // SAFETY: this impl detail it's more layout concerning so this is safe
    type ElementType = u8;

    fn is_valid(x: &Self::Dummy) -> bool {
        str::from_utf8(x).is_ok()
    }
}

unsafe impl<'a> Transmutable for bool {
    type Dummy = u8;
    type ElementType = Self;

    fn is_valid(x: &Self::Dummy) -> bool {
        *x < 2
    }
}

/*
unsafe impl<'a> Transmutable for ExitCode {
    type Dummy = u8;
    type ElementType = Self;

    fn is_valid(x: &Self::Dummy) -> bool {
        true
    }
}

*/
macro_rules! impl_transmutable {
    ($($p:ty),*) => {
    $(
    unsafe impl Transmutable for $p {
        type Dummy = Self;
        type ElementType = Self;

        fn is_valid(_: &Self::Dummy) -> bool {
            true
        }
    }
    )*
    }
}

impl_transmutable! { u8, i8, u16, i16, u32, i32, u64, i64, usize, isize, u128, i128, () }

macro_rules! impl_transmutable_nonzero {

    ($($p:ty; $a:ty),*) => {
    $(
    unsafe impl Transmutable for $a {
        type Dummy = $p;
        type ElementType = Self;

        fn is_valid(x: &Self::Dummy) -> bool {
            *x > 0
        }
    }
    )*
    }
}

impl_transmutable_nonzero! {
    u8; NonZeroU8, 
    i8; NonZeroI8, 
    u16; NonZeroU16, 
    i16; NonZeroI16, 
    u32; NonZeroU32, 
    i32; NonZeroI32, 
    u64; NonZeroU64, 
    i64; NonZeroI64, 
    usize; NonZeroUsize, 
    isize; NonZeroIsize, 
    u128; NonZeroU128, 
    i128; NonZeroI128 
}

unsafe impl<T: ?Sized + 'static> Transmutable for *const T {
    type Dummy = Self;
    type ElementType = Self;

    fn is_valid(_: &Self::Dummy) -> bool {
        true
    }
}

unsafe impl<T: ?Sized + 'static> Transmutable for *mut T {
    type Dummy = Self;
    type ElementType = Self;

    fn is_valid(_: &Self::Dummy) -> bool {
        true
    }
}

unsafe impl<T: ?Sized + 'static> Transmutable for NonNull<T> {
    type Dummy = *mut T;
    type ElementType = Self;

    fn is_valid(x: &Self::Dummy) -> bool {
        NonNull::new(*x).is_some()
    }
}

unsafe impl Transmutable for char {
    type Dummy = u32;
    type ElementType = Self;

    fn is_valid(x: &Self::Dummy) -> bool {
        char::from_u32(*x).is_some()
    }
}

// I didn't write all this but I was unable to turn it in a macro.
unsafe impl<A: Transmutable<Dummy = B>,
B: Transmutable<Dummy = C>,
C: Transmutable<Dummy = D>,
D: Transmutable<Dummy = E>,
E: Transmutable<Dummy = F>,
F: Transmutable<Dummy = G>,
G: Transmutable<Dummy = H>,
H: Transmutable<Dummy = I>,
I: Transmutable<Dummy = J>,
J: Transmutable<Dummy = K>,
K: Transmutable<Dummy = L>,
L: Transmutable<Dummy = M>,
M: Transmutable<Dummy = N>,
N: Transmutable<Dummy = O>,
O: Transmutable<Dummy = P>,
P: Transmutable<Dummy = Q>,
Q: Transmutable<Dummy = R>,
R: Transmutable<Dummy = S>,
S: Transmutable<Dummy = T>,
T: Transmutable<Dummy = U>,
U: Transmutable<Dummy = V>,
V: Transmutable<Dummy = W>,
W: Transmutable<Dummy = X>,
X: Transmutable<Dummy = Y>,
Y: Transmutable<Dummy = Z>,
Z: Transmutable<Dummy = ZA>,
ZA: Transmutable<Dummy = ZB>,
ZB: Transmutable<Dummy = ZC>,
ZC: Transmutable<Dummy = ZD>,
ZD: Transmutable<Dummy = ZE>,
ZE: Transmutable<Dummy = ZF>,
ZF: Transmutable<Dummy = ZG>,
ZG: Transmutable<Dummy = ZH>,
ZH: Transmutable<Dummy = ZI>,
ZI: Transmutable<Dummy = ZJ>,
ZJ: Transmutable<Dummy = ZK>,
ZK: Transmutable<Dummy = ZL>,
ZL: Transmutable<Dummy = ZM>,
ZM: Transmutable<Dummy = ZN>,
ZN: Transmutable<Dummy = ZO>,
ZO: Transmutable<Dummy = ZP>,
ZP: Transmutable<Dummy = ZQ>,
ZQ: Transmutable<Dummy = ZR>,
ZR: Transmutable<Dummy = ZS>,
ZS: Transmutable<Dummy = ZT>,
ZT: Transmutable<Dummy = ZU>,
ZU: Transmutable<Dummy = ZV>,
ZV: Transmutable<Dummy = ZW>,
ZW: Transmutable<Dummy = ZX>,
ZX: Transmutable<Dummy = ZY>,
ZY: Transmutable<Dummy = ZZ>,
ZZ: Transmutable<Dummy = ZZA>,
ZZA: Transmutable<Dummy = ZZB>,
ZZB: Transmutable<Dummy = ZZC>,
ZZC: Transmutable<Dummy = ZZD>,
ZZD: Transmutable<Dummy = ZZE>,
ZZE: Transmutable<Dummy = ZZF>,
ZZF: Transmutable<Dummy = ZZG>,
ZZG: Transmutable<Dummy = ZZH>,
ZZH: Transmutable<Dummy = ZZI>,
ZZI: Transmutable<Dummy = ZZJ>,
ZZJ: Transmutable<Dummy = ZZK>,
ZZK: Transmutable<Dummy = ZZL>,
ZZL: Transmutable<Dummy = ZZM>,
ZZM: Transmutable<Dummy = ZZN>,
ZZN: Transmutable<Dummy = ZZO>,
ZZO: Transmutable<Dummy = ZZP>,
ZZP: Transmutable<Dummy = ZZQ>,
ZZQ: Transmutable<Dummy = ZZR>,
ZZR: Transmutable<Dummy = ZZS>,
ZZS: Transmutable<Dummy = ZZT>,
ZZT: Transmutable<Dummy = ZZU>,
ZZU: Transmutable<Dummy = ZZV>,
ZZV: Transmutable<Dummy = ZZW>,
ZZW: Transmutable<Dummy = ZZX>,
ZZX: Transmutable<Dummy = ZZY>,
ZZY: Transmutable<Dummy = ZZZ>,
ZZZ: Transmutable<Dummy = ZZZA>,
ZZZA: Transmutable<Dummy = ZZZB>,
ZZZB: Transmutable<Dummy = ZZZC>,
ZZZC: Transmutable<Dummy = ZZZD>,
ZZZD: Transmutable<Dummy = ZZZE>,
ZZZE: Transmutable<Dummy = ZZZF>,
ZZZF: Transmutable<Dummy = ZZZG>,
ZZZG: Transmutable<Dummy = ZZZH>,
ZZZH: Transmutable<Dummy = ZZZI>,
ZZZI: Transmutable<Dummy = ZZZJ>,
ZZZJ: Transmutable<Dummy = ZZZK>,
ZZZK: Transmutable<Dummy = ZZZL>,
ZZZL: Transmutable<Dummy = ZZZM>,
ZZZM: Transmutable<Dummy = ZZZN>,
ZZZN: Transmutable<Dummy = ZZZO>,
ZZZO: Transmutable<Dummy = ZZZP>,
ZZZP: Transmutable<Dummy = ZZZQ>,
ZZZQ: Transmutable<Dummy = ZZZR>,
ZZZR: Transmutable<Dummy = ZZZS>,
ZZZS: Transmutable<Dummy = ZZZT>,
ZZZT: Transmutable<Dummy = ZZZU>,
ZZZU: Transmutable<Dummy = ZZZV>,
ZZZV: Transmutable<Dummy = ZZZW>,
ZZZW: Transmutable<Dummy = ZZZX>,
ZZZX: Transmutable<Dummy = ZZZX>>
 Transmutable for [A] {
        type Dummy = [A::Dummy];
        type ElementType = A;

        fn is_valid(x: &Self::Dummy) -> bool {
            x.iter().all(A::is_valid)
        }
    }

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn a() {
        assert!(1u8.transmute::<bool>().unwrap());
        assert!(!0u8.transmute::<bool>().unwrap());
        assert!(2u8.transmute::<bool>().is_err());

        let a = [1, 2];
 
        let r: Result<&[bool], &[u32]> = a[..].transmute_ref();

        assert_eq!(r, Err(&[1, 2][..]))
    }
}