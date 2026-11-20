import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.EqIdOfFixed
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.HermRep

section Fixed

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[h.2.2.2, h.2.2.2, star_star]`.
-/
theorem sig_sig (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

/- English proof (translation)
The claim follows from `_root_.Bl.EqIdOfFixed.goal1 h hx`.
-/
theorem exists_of_sig_fixed (h : IsCMExt F E σ) {x : E} (hx : σ x = x) :
    ∃ t : F, algebraMap F E t = x :=
  _root_.Bl.EqIdOfFixed.goal1 h hx

end Fixed

section Form

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (T : Matrix (Fin M) (Fin M) E)

/- English proof (translation)
Simplify using `only [hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]`.
-/
theorem hE_add_left (x x' y : Fin M → E) :
    hE σ T (x + x') y = hE σ T x y + hE σ T x' y := by
  simp only [hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]`.
-/
theorem hE_add_right (x y y' : Fin M → E) :
    hE σ T x (y + y') = hE σ T x y + hE σ T x y' := by
  simp only [hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hE, HeckeCharacterZeroLocus.SiegelWeilU.hform]`. Rewrite using `[Finset.sum_eq_single i, Finset.sum_eq_single j]`. Simplify using the standard rewrite rules. Introduce `k _ hk`. Simplify using `[Pi.single_eq_of_ne hk]`.

Simplify using the standard rewrite rules. Introduce `k _ hk`. Simplify using `[Pi.single_eq_of_ne hk]`. Simplify using the standard rewrite rules.
-/
theorem hE_single (i j : Fin M) (a b : E) :
    hE σ T (Pi.single i a) (Pi.single j b) = σ a * T i j * b := by
  simp only [hE, HeckeCharacterZeroLocus.SiegelWeilU.hform]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro k _ hk; simp [Pi.single_eq_of_ne hk]
  · simp
  · intro k _ hk; simp [Pi.single_eq_of_ne hk]
  · simp

end Form

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ n T hT`. Take `⟨hH, hdet⟩` from `hT`. Distinguish the cases in `hd : ∃ i, T i i ≠ 0`. Take `⟨i, hi⟩` from `hd`. Take `⟨t, ht⟩` from `exists_of_sig_fixed hσ (hH i i)`.

Use `⟨t, Pi.single i 1, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `hi (by rw [← ht, map_zero])`. Rewrite using `[hE_single, ht]`. Simplify using the standard rewrite rules.

Use `push_neg at hd`. Choose the witnesses or unpack the hypotheses as in `⟨i, j, hij⟩ : ∃ i j, T i j ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hdet (by rw [show T = 0 from Matrix.ext hc, Matrix.det_zero])`.

Establish `hne : i ≠ j`. Introduce and unpack `rfl`. Conclude with `hij (hd i)`. Use `⟨2, Pi.single i (σ (T i j)⁻¹) + Pi.single j 1, two_ne_zero, ?_⟩` and prove the remaining obligations. Establish `hji : T j i = σ (T i j)` using `(hH j i).symm`.

Establish `hs : σ (σ (T i j)⁻¹) = (T i j)⁻¹` using `sig_sig hσ _`. Rewrite using `[hE_add_left, hE_add_right, hE_add_right, hE_single, hE_single, hE_single, hE_single, hd i, hd j, hs, hji, map_one, map_ofNat, map_inv₀]`. Establish `h1 : σ (T i j) ≠ 0` using `(map_ne_zero _).2 hij`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_repr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (T : Matrix (Fin (n + 1)) (Fin (n + 1)) E), IsHermND σ T → ∃ (t : F) (x : Fin (n + 1) → E), t ≠ 0 ∧ hE σ T x x = algebraMap F E t := by
  intro F E _ _ _ _ _ σ hσ n T hT
  obtain ⟨hH, hdet⟩ := hT
  by_cases hd : ∃ i, T i i ≠ 0
  · obtain ⟨i, hi⟩ := hd
    obtain ⟨t, ht⟩ := exists_of_sig_fixed hσ (hH i i)
    refine ⟨t, Pi.single i 1, ?_, ?_⟩
    · rintro rfl
      exact hi (by rw [← ht, map_zero])
    · rw [hE_single, ht]; simp
  · push_neg at hd
    obtain ⟨i, j, hij⟩ : ∃ i j, T i j ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hdet (by rw [show T = 0 from Matrix.ext hc, Matrix.det_zero])
    have hne : i ≠ j := by
      rintro rfl
      exact hij (hd i)
    refine ⟨2, Pi.single i (σ (T i j)⁻¹) + Pi.single j 1, two_ne_zero, ?_⟩
    have hji : T j i = σ (T i j) := (hH j i).symm
    have hs : σ (σ (T i j)⁻¹) = (T i j)⁻¹ := sig_sig hσ _
    rw [hE_add_left, hE_add_right, hE_add_right, hE_single, hE_single, hE_single, hE_single,
      hd i, hd j, hs, hji, map_one, map_ofNat, map_inv₀]
    have h1 : σ (T i j) ≠ 0 := (map_ne_zero _).2 hij
    field_simp
    ring

end GlobalTheory.CompanionTheory.SW.HermRep
