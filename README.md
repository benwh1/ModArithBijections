A proof of the following theorem in Lean 4:

> Let a, b, c, m be positive integers such that b^m = 1 mod m and c is coprime to m. Then the function given by f(n) = a * b^n + c * n is a bijection on Z/mZ.

The formalised statement:

```lean
def f (a b c x : ℕ) : ℕ := a * b ^ x + c * x

bijection_mod_m {a b c m x y : ℕ} (hmgt : m > 0) (hm : b ^ m ≡ 1 [MOD m]) (hcm : Nat.Coprime c m)
  (hf : f a b c x ≡ f a b c y [MOD m]) : x ≡ y [MOD m]
```
