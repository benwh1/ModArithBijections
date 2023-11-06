A proof of the following theorem in Lean 4:

> Let a, b, m be positive integers such that b^m = 1 mod m. Then the function given by f(n) = a * b^n + n is a bijection on Z/mZ.

The formalised statement:

```lean
def f (a b x : ℕ) : ℕ := a * b ^ x + x

bijection_mod_m {a b m x y : ℕ} (hmgt : m > 0) (hm : b ^ m ≡ 1 [MOD m])
  (hf : f a b x ≡ f a b y [MOD m]) : x ≡ y [MOD m]
```
