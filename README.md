A proof of the following theorem in Lean 4:

> Let m be a positive integer such that 3^m = 1 mod m. Then the function given by f(n) = 3^n + n is a bijection on Z/mZ.

The formalised statement:

```lean4
bijection_mod_m {m x y : ℕ} (hmgt : m > 0) (hm : 3 ^ m ≡ 1 [MOD m]) (hf : f x ≡ f y [MOD m]) : x ≡ y [MOD m]
```