import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

/- English proof (translation)
Introduce `hsum hadm X M _ _ T z hz V _ _ Φ hΦ g`. Establish `hidx : ((T.K₀.relIndex T.K : ℕ) : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr T.idx`. Take `⟨Ψ, hΨ⟩ : ∃ Ψ : X → V, ∀ x, Ψ x = T.tf z x • Φ (g * x)` from `⟨_, fun _ => rfl⟩`. Establish `hinv : ∀ k ∈ T.K, ∀ x, Ψ (x * k) = Ψ x`. Introduce `k hk x`.

Establish `h1` using `((hadm X M T z hz.2).2 k hk x).2`. Establish `h2` using `hΦ k hk (g * x)`. Rewrite using `[hΨ, hΨ, h1, ← mul_assoc, h2, smul_smul, mul_right_comm, Units.inv_mul, one_mul]`. Establish `hsingle : ∑ᶠ y : X ⧸ T.K, Ψ y.out = Ψ z`. Rewrite using `[finsum_eq_single _ (QuotientGroup.mk z : X ⧸ T.K)]`.

Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul T.K z`. Rewrite using `[hk]`. Conclude with `hinv k k.2 z`. Introduce `y hy`. Establish `h0 : dosetInd ℂ T.K z y.out = 0`.

Apply `Set.indicator_of_notMem` to reduce the goal to its premises. Introduce `hm`. Take `⟨a, ha, b, hb, e⟩` from `DoubleCoset.mem_doubleCoset.mp hm`. Establish `e' : y.out = z * (a * b)`. Rewrite using `[e, ← hz.1 a, mul_assoc]`.

Establish `h2 : ((y.out : X) : X ⧸ T.K) = (z : X ⧸ T.K)`. Rewrite using `[e']`. Conclude with `QuotientGroup.mk_mul_of_mem z (T.K.mul_mem ha hb)`. Conclude with `hy ((QuotientGroup.out_eq' y).symm.trans h2)`. Rewrite using `[hΨ, TyLev.tf, h0, mul_zero, zero_smul]`.

Establish `hty : tyFn T.J T.ψ 1 = 1`. Unfold `tyFn`. Rewrite using `[dif_pos T.J.one_mem]`. Establish `h1 : (⟨1, T.J.one_mem⟩ : T.J) = 1` using `rfl`. Rewrite using `[h1, map_one]`.

Simplify using the standard rewrite rules. Establish `hdz : dosetInd ℂ T.K z z = 1`. Unfold `dosetInd`. Rewrite using `[Set.indicator_of_mem (DoubleCoset.mem_doubleCoset.mpr ⟨1, T.K.one_mem, 1, T.K.one_mem, by simp⟩)]`. Both sides reduce to the same expression.

Establish `hzz : T.tf z z = ((T.K₀.relIndex T.K : ℕ) : ℂ)⁻¹`. Rewrite using `[TyLev.tf, hz.2, hty, hdz, mul_one, mul_one]`. Establish `hs` using `hsum X V T.K T.K₀ T.le T.idx Ψ hinv`. Unfold `hAct`. Simplify using `only [hΨ] at hs hsingle`.

Rewrite using `[hs, hsingle, hzz, smul_smul, mul_inv_cancel₀ hidx, one_smul]`.
-/
theorem UpperTheory.Gal.W2.Seed.pTfCen :
    (∀ (X V : Type) [Group X] [AddCommGroup V] [Module ℂ V] (K K₀ : Subgroup X), K₀ ≤ K → K₀.relIndex K ≠ 0 → ∀ Ψ : X → V, (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∑ᶠ x : X ⧸ K₀, Ψ x.out = ((K₀.relIndex K : ℕ) : ℂ) • ∑ᶠ y : X ⧸ K, Ψ y.out) → TfAdm → TfCen := by
  intro hsum hadm X M _ _ T z hz V _ _ Φ hΦ g
  have hidx : ((T.K₀.relIndex T.K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr T.idx
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : X → V, ∀ x, Ψ x = T.tf z x • Φ (g * x) := ⟨_, fun _ => rfl⟩
  have hinv : ∀ k ∈ T.K, ∀ x, Ψ (x * k) = Ψ x := by
    intro k hk x
    have h1 := ((hadm X M T z hz.2).2 k hk x).2
    have h2 := hΦ k hk (g * x)
    rw [hΨ, hΨ, h1, ← mul_assoc, h2, smul_smul, mul_right_comm, Units.inv_mul, one_mul]
  have hsingle : ∑ᶠ y : X ⧸ T.K, Ψ y.out = Ψ z := by
    rw [finsum_eq_single _ (QuotientGroup.mk z : X ⧸ T.K)]
    · obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul T.K z
      rw [hk]
      exact hinv k k.2 z
    · intro y hy
      have h0 : dosetInd ℂ T.K z y.out = 0 := by
        apply Set.indicator_of_notMem
        intro hm
        obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.mp hm
        have e' : y.out = z * (a * b) := by
          rw [e, ← hz.1 a, mul_assoc]
        have h2 : ((y.out : X) : X ⧸ T.K) = (z : X ⧸ T.K) := by
          rw [e']
          exact QuotientGroup.mk_mul_of_mem z (T.K.mul_mem ha hb)
        exact hy ((QuotientGroup.out_eq' y).symm.trans h2)
      rw [hΨ, TyLev.tf, h0, mul_zero, zero_smul]
  have hty : tyFn T.J T.ψ 1 = 1 := by
    unfold tyFn
    rw [dif_pos T.J.one_mem]
    have h1 : (⟨1, T.J.one_mem⟩ : T.J) = 1 := rfl
    rw [h1, map_one]
    simp
  have hdz : dosetInd ℂ T.K z z = 1 := by
    unfold dosetInd
    rw [Set.indicator_of_mem (DoubleCoset.mem_doubleCoset.mpr ⟨1, T.K.one_mem, 1, T.K.one_mem, by simp⟩)]
    rfl
  have hzz : T.tf z z = ((T.K₀.relIndex T.K : ℕ) : ℂ)⁻¹ := by
    rw [TyLev.tf, hz.2, hty, hdz, mul_one, mul_one]
  have hs := hsum X V T.K T.K₀ T.le T.idx Ψ hinv
  unfold hAct
  simp only [hΨ] at hs hsingle
  rw [hs, hsingle, hzz, smul_smul, mul_inv_cancel₀ hidx, one_smul]
