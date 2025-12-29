import Mathlib

open Int

namespace NumberLib

/-- If `d ∣ a` and `d ∣ b`, then `d ∣ (a - k*b)` for any integer `k`. -/
lemma dvd_sub_mul {d a b k : ℤ} (ha : d ∣ a) (hb : d ∣ b) :
    d ∣ a - k * b := by
  have hkb : d ∣ k * b := by
    simpa using (Int.dvd_mul_of_dvd_right (a := d) (b := k) (c := b) hb)
  exact dvd_sub ha hkb

/-- If `d` divides both `a` and `b`,
  then `d` divides any integer linear combination `x*a + y*b`. -/
lemma dvd_linear_comb {d a b x y : ℤ} (ha : d ∣ a) (hb : d ∣ b) :
    d ∣ x * a + y * b := by
  have hxa : d ∣ x * a := by
    simpa using (Int.dvd_mul_of_dvd_right (a := d) (b := x) (c := a) ha)
  have hyb : d ∣ y * b := by
    simpa using (Int.dvd_mul_of_dvd_right (a := d) (b := y) (c := b) hb)
  exact Int.dvd_add hxa hyb

/-- If `d ∣ a` and `d ∣ b` in `ℕ`, then `(d:ℤ)` divides any integer linear combination
`x*(a:ℤ) + y*(b:ℤ)`. -/
lemma cast_dvd_int_linear_comb {d a b : ℕ} {x y : ℤ}
    (ha : d ∣ a) (hb : d ∣ b) :
    (d : ℤ) ∣ x * (a : ℤ) + y * (b : ℤ) := by
  -- cast the divisibility hypotheses to ℤ
  have haZ : (d : ℤ) ∣ (a : ℤ) := by exact_mod_cast ha
  have hbZ : (d : ℤ) ∣ (b : ℤ) := by exact_mod_cast hb
  -- now use your ℤ-lemma
  simpa [mul_assoc, mul_left_comm, mul_comm] using
     (dvd_linear_comb (d := (d : ℤ)) (a := (a : ℤ)) (b := (b : ℤ)) (x := x) (y := y) haZ hbZ)

/-- A natural number, coerced to `ℤ`, cannot be `-1`. -/
lemma ofNat_ne_neg_one (d : ℕ) : (d : ℤ) ≠ (-1 : ℤ) := by
  intro hd
  have hnonneg : (0 : ℤ) ≤ (d : ℤ) := Int.natCast_nonneg d
  have : (0 : ℤ) ≤ (-1 : ℤ) := by simp [hd] at hnonneg
  have : ¬ ((0 : ℤ) ≤ (-1 : ℤ)) := by decide
  exact this ‹(0 : ℤ) ≤ (-1 : ℤ)›

/-- Handy criterion: if every common divisor of `a` and `b` divides `1`,
  then `a` and `b` are coprime. -/
lemma coprime_of_forall_dvd {a b : ℕ}
    (h : ∀ d : ℕ, d ∣ a → d ∣ b → d ∣ 1) : Nat.Coprime a b := by
  have hg1 : Nat.gcd a b ∣ 1 :=
    h (Nat.gcd a b) (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b)
  exact Nat.coprime_iff_gcd_eq_one.2 (Nat.dvd_one.mp hg1)


/-!
## Main lemmas

Let `d = gcd a b` and `e = gcd (a*n+x) (b*n+y)`.

1) `d ∣ a*y - b*x`.
2) `e ∣ (a/d)*y - (b/d)*x`.

All divisibility claims are stated in `ℤ` to avoid `Nat` subtraction side conditions.
-/

/-- If `d = gcd a b`, then `(d:ℤ)` divides `a*y - b*x` (for all `x y`). -/
theorem gcd_dvd_sub_det
    (a b x y : ℕ) :
    ((Nat.gcd a b : ℕ) : ℤ) ∣ (a : ℤ) * (y : ℤ) - (b : ℤ) * (x : ℤ) := by
  let d : ℕ := Nat.gcd a b
  have hda : d ∣ a := Nat.gcd_dvd_left a b
  have hdb : d ∣ b := Nat.gcd_dvd_right a b
  -- d divides a*y and b*x, hence their difference
  have h1 : (d : ℤ) ∣ (a : ℤ) * (y : ℤ) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (Int.dvd_mul_of_dvd_left (a := (d : ℤ)) (b := (a : ℤ)) (c := (y : ℤ))
          (by exact_mod_cast hda : (d : ℤ) ∣ (a : ℤ)))
  have h2 : (d : ℤ) ∣ (b : ℤ) * (x : ℤ) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (Int.dvd_mul_of_dvd_left (a := (d : ℤ)) (b := (b : ℤ)) (c := (x : ℤ))
          (by exact_mod_cast hdb : (d : ℤ) ∣ (b : ℤ)))
  -- rewrite `a*y - b*x` as `a*y + (-1)*(b*x)` and use `dvd_add`
  simpa [d, sub_eq_add_neg, mul_assoc] using (Int.dvd_add h1 (Int.dvd_neg.mpr h2))

/-- If `d = gcd a b` and `e = gcd (a*n+x) (b*n+y)`, then
`(e:ℤ)` divides `(a/d)*y - (b/d)*x`. -/
theorem gcd_shift_dvd_quot_det
    (a b n x y : ℕ) :
    ((Nat.gcd (a * n + x) (b * n + y) : ℕ) : ℤ) ∣
      ((a / Nat.gcd a b : ℕ) : ℤ) * (y : ℤ) - ((b / Nat.gcd a b : ℕ) : ℤ) * (x : ℤ) := by
  let d : ℕ := Nat.gcd a b
  let e : ℕ := Nat.gcd (a * n + x) (b * n + y)
  let a' : ℕ := a / d
  let b' : ℕ := b / d

  have hdA : d ∣ a := Nat.gcd_dvd_left a b
  have hdB : d ∣ b := Nat.gcd_dvd_right a b

  -- exact decompositions a = d*a', b = d*b' (in ℤ form)
  have haZ : (a : ℤ) = (d : ℤ) * (a' : ℤ) := by
    -- `d * (a/d) = a` in ℕ, then cast and flip
    have : d * (a / d) = a := Nat.mul_div_cancel' hdA
    exact (by
      have : (d : ℤ) * (a' : ℤ) = (a : ℤ) := by exact_mod_cast this
      simpa [a'] using this.symm)
  have hbZ : (b : ℤ) = (d : ℤ) * (b' : ℤ) := by
    have : d * (b / d) = b := Nat.mul_div_cancel' hdB
    exact (by
      have : (d : ℤ) * (b' : ℤ) = (b : ℤ) := by exact_mod_cast this
      simpa [b'] using this.symm)

  -- e divides both shifted terms (in ℤ)
  have he1 : (e : ℤ) ∣ ((a * n + x : ℕ) : ℤ) := by
    exact_mod_cast (Nat.gcd_dvd_left (a * n + x) (b * n + y))
  have he2 : (e : ℤ) ∣ ((b * n + y : ℕ) : ℤ) := by
    exact_mod_cast (Nat.gcd_dvd_right (a * n + x) (b * n + y))

  -- take the linear combination with coefficients `-b'` and `a'`
  have hcomb :
      (e : ℤ) ∣ (- (b' : ℤ)) * ((a * n + x : ℕ) : ℤ) + (a' : ℤ) * ((b * n + y : ℕ) : ℤ) :=
    dvd_linear_comb (d := (e : ℤ))
      (a := ((a * n + x : ℕ) : ℤ)) (b := ((b * n + y : ℕ) : ℤ))
      (x := (- (b' : ℤ))) (y := (a' : ℤ)) he1 he2

  -- compute the combination: n-terms cancel because a=d*a', b=d*b'
  have hEq :
      (- (b' : ℤ)) * ((a * n + x : ℕ) : ℤ) + (a' : ℤ) * ((b * n + y : ℕ) : ℤ)
        =
      (a' : ℤ) * (y : ℤ) - (b' : ℤ) * (x : ℤ) := by
    -- make casts explicit, then ring; use `haZ hbZ` to cancel the n-part
    push_cast
    -- rewrite `a` and `b` as `d*a'` and `d*b'` in the n-part
    -- (after `push_cast`, `a` and `b` appear as `(a:ℤ)` and `(b:ℤ)`)
    -- we only need them inside a `ring` proof, so we just rewrite them.
    simp [sub_eq_add_neg, haZ, hbZ]
    ring

  rcases hcomb with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  -- rewrite the target using `hEq`, then close with `hk`
  calc
    (a' : ℤ) * (y : ℤ) - (b' : ℤ) * (x : ℤ)
        = (- (b' : ℤ)) * ((a * n + x : ℕ) : ℤ) + (a' : ℤ) * ((b * n + y : ℕ) : ℤ) := by
            -- `hEq` is the equality between these; we want this direction
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm,
              mul_left_comm, mul_assoc]
              using hEq.symm
    _ = (e : ℤ) * k := hk

end NumberLib --- IGNORE ---
