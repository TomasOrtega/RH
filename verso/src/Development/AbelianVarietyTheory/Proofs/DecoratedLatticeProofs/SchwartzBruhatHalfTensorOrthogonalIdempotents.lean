import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrOfMulEqZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.PutIn

/- English proof (translation)
Introduce `i j`. Rewrite using `[Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hx i j]`.
-/
theorem isHalf_nsmul {D : D7} {m n : ℕ} {e : AE D} {x : Mx D m n} (hx : IsHalf e x) (k : ℕ) : IsHalf e (k • x) := by
  intro i j
  rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hx i j]

/- English proof (translation)
Introduce `i j`. Rewrite using `[Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hbb]`.
-/
theorem isHalf_smul_idem {D : D7} {m n : ℕ} {b : AE D} (hbb : b * b = b) (x : Mx D m n) : IsHalf b (b • x) := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hbb]

/- English proof (translation)
Introduce `i j`. Establish `h` using `hu i j`. Rewrite using `[Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_sub, ← mul_assoc, hab, zero_mul, sub_zero]`. Rewrite `h` using `[add_mul]`. Take the linear combination `h`.
-/
theorem isHalf_sub_smul {D : D7} {m n : ℕ} {a b : AE D} (hab : a * b = 0) {u : Mx D m n} (hu : IsHalf (a + b) u) :
    IsHalf a (u - b • u) := by
  intro i j
  have h := hu i j
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_sub, ← mul_assoc, hab, zero_mul, sub_zero]
  rw [add_mul] at h
  linear_combination h

/- English proof (translation)
Introduce `D S T a b Λ Φ Ψ hab hbb hΛ ⟨hΦs, kΦ, hkΦ, hΦi, hΦb⟩ ⟨hΨs, kΨ, hkΨ, hΨi, hΨb⟩`. Use `⟨?_, kΦ * kΨ, Nat.mul_pos hkΦ hkΨ, ?_, ?_⟩` and prove the remaining obligations. Introduce `t ht`. Rewrite `ht` using `[tens_apply]`. Establish `h1` using `hΦs _ (left_ne_zero_of_mul ht)`.

Establish `h2` using `hΨs _ (right_ne_zero_of_mul ht)`. Introduce `i j`. Establish `e1` using `h1 i j`. Establish `e2` using `h2 i j`. Simplify using `only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at e1 e2`.

Rewrite `e1` using `[mul_sub, ← mul_assoc, hab, zero_mul, sub_zero]`. Rewrite using `[add_mul, e1]`. Expand and normalize the polynomial expressions, which then agree. Introduce `u hu hhu t`. Establish `hu1 : u - b • u ∈ Λ` using `Λ.sub_mem hu (hΛ u hu)`.

Establish `hu2 : b • u ∈ Λ` using `hΛ u hu`. Establish `e1 : (t + (kΦ * kΨ) • u) - b • (t + (kΦ * kΨ) • u) = (t - b • t) + kΦ • (kΨ • (u - b • u))`. Use extensionality with `i j`. Simplify using `only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `e2 : b • (t + (kΦ * kΨ) • u) = b • t + kΨ • (kΦ • (b • u))`. Use extensionality with `i j`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[tens_apply, tens_apply, e1, e2, hΦi _ (Λ.nsmul_mem hu1 kΨ) (isHalf_nsmul (isHalf_sub_smul hab hhu) kΨ), hΨi _ (Λ.nsmul_mem hu2 kΦ) (isHalf_nsmul (isHalf_smul_idem hbb u) kΦ)]`. Introduce `t ht`. Rewrite `ht` using `[tens_apply]`. Establish `h1` using `hΦb _ (left_ne_zero_of_mul ht)`.

Establish `h2` using `hΨb _ (right_ne_zero_of_mul ht)`. Establish `e : (kΦ * kΨ) • t = kΨ • (kΦ • (t - b • t)) + kΦ • (kΨ • (b • t))`. Use extensionality with `i j`. Simplify using `only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Λ.add_mem (Λ.nsmul_mem h1 kΨ) (Λ.nsmul_mem h2 kΦ)`.
-/
theorem isSBHalf_tens : ∀ (D : D7) (S T : HSp D) (a b : AE D) (Λ : AddSubgroup (WO S T)) (Φ Ψ : WO S T → ℂ),
    a * b = 0 → b * b = b → (∀ u ∈ Λ, b • u ∈ Λ) → IsSBHalf a Λ Φ → IsSBHalf b Λ Ψ →
    IsSBHalf (a + b) Λ (GlobalTheory.FinPl.PutIn.tens b Φ Ψ) := by
  intro D S T a b Λ Φ Ψ hab hbb hΛ ⟨hΦs, kΦ, hkΦ, hΦi, hΦb⟩ ⟨hΨs, kΨ, hkΨ, hΨi, hΨb⟩
  refine ⟨?_, kΦ * kΨ, Nat.mul_pos hkΦ hkΨ, ?_, ?_⟩
  · intro t ht
    rw [tens_apply] at ht
    have h1 := hΦs _ (left_ne_zero_of_mul ht)
    have h2 := hΨs _ (right_ne_zero_of_mul ht)
    intro i j
    have e1 := h1 i j
    have e2 := h2 i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at e1 e2
    rw [mul_sub, ← mul_assoc, hab, zero_mul, sub_zero] at e1
    rw [add_mul, e1]
    ring
  · intro u hu hhu t
    have hu1 : u - b • u ∈ Λ := Λ.sub_mem hu (hΛ u hu)
    have hu2 : b • u ∈ Λ := hΛ u hu
    have e1 : (t + (kΦ * kΨ) • u) - b • (t + (kΦ * kΨ) • u) = (t - b • t) + kΦ • (kΨ • (u - b • u)) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
      push_cast; ring
    have e2 : b • (t + (kΦ * kΨ) • u) = b • t + kΨ • (kΦ • (b • u)) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
      push_cast; ring
    rw [tens_apply, tens_apply, e1, e2,
      hΦi _ (Λ.nsmul_mem hu1 kΨ) (isHalf_nsmul (isHalf_sub_smul hab hhu) kΨ),
      hΨi _ (Λ.nsmul_mem hu2 kΦ) (isHalf_nsmul (isHalf_smul_idem hbb u) kΦ)]
  · intro t ht
    rw [tens_apply] at ht
    have h1 := hΦb _ (left_ne_zero_of_mul ht)
    have h2 := hΨb _ (right_ne_zero_of_mul ht)
    have e : (kΦ * kΨ) • t = kΨ • (kΦ • (t - b • t)) + kΦ • (kΨ • (b • t)) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
      push_cast; ring
    rw [e]
    exact Λ.add_mem (Λ.nsmul_mem h1 kΨ) (Λ.nsmul_mem h2 kΦ)

end GlobalTheory.FinPl.PutIn

end
