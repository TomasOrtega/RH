import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoordEquivApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StarStarOfInvol
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

namespace GlobalTheory.TrUnitLat

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm r P`. Establish `hσ : ∀ e, σ (σ e) = e`. Introduce `x`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises.

Rewrite using `[hcm.2.2.2, hcm.2.2.2, star_star]`. Establish `hs` using `star'_star'_of_invol hσ P`. Establish `htr` using `trace_star'_eq F E σ hσ r P`. Use `⟨fun i j => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [gramOne, Matrix.of_apply]`.

Rewrite using `[← htr, map_mul, hs, mul_comm]`. Introduce `hdet`. Take `⟨w, hw0, hw⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 hdet`. Apply `hw0` to reduce the goal to its premises. Use `set b := powB P`.

Use `set z : Fld P := ∑ j, w j • b j with hz`. Establish `h1 : ∀ i, Algebra.trace E (Fld P) (z * star' P (b i)) = 0`. Introduce `i`. Use `congr_fun hw i` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct, gramOne, Matrix.of_apply, Pi.zero_apply] at this`.

Rewrite using `[hz, Finset.sum_mul, map_sum]`. Rewrite using `[← this]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, map_smul, smul_eq_mul, mul_comm]`. Establish `h2 : ∀ u : Fld P, Algebra.trace E (Fld P) (z * u) = 0`.

Introduce `u`. Establish `hu : u = ∑ i, σ (b.repr (star' P u) i) • star' P (b i)` using `by conv_lhs => rw [← hs u, ← b.sum_repr (star' P u)]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul, star'_algebraMap]`.

Rewrite using `[hu, Finset.mul_sum, map_sum]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, map_smul, h1, smul_zero]`. Establish `hz0 : z = 0` using `(traceForm_nondegenerate E (Fld P)).1 z fun u => by`. Rewrite using `[Algebra.traceForm_apply]`.

Conclude with `h2 u`. Use function extensionality and compare the values at `j`. Conclude with `Fintype.linearIndependent_iff.1 b.linearIndependent w (by rw [← hz0]) j`.
-/
theorem gramOne_herm_nd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r), IsHermND σ (GlobalTheory.TrUnitLat.gramOne P) := by
  intro F E _ _ _ _ _ σ hcm r P
  have hσ : ∀ e, σ (σ e) = e := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hcm.2.2.2, hcm.2.2.2, star_star]
  have hs := star'_star'_of_invol hσ P
  have htr := trace_star'_eq F E σ hσ r P
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [gramOne, Matrix.of_apply]
    rw [← htr, map_mul, hs, mul_comm]
  · intro hdet
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    apply hw0
    set b := powB P
    set z : Fld P := ∑ j, w j • b j with hz
    have h1 : ∀ i, Algebra.trace E (Fld P) (z * star' P (b i)) = 0 := by
      intro i
      have := congr_fun hw i
      simp only [Matrix.mulVec, dotProduct, gramOne, Matrix.of_apply, Pi.zero_apply] at this
      rw [hz, Finset.sum_mul, map_sum]
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_mul_assoc, map_smul, smul_eq_mul, mul_comm]
    have h2 : ∀ u : Fld P, Algebra.trace E (Fld P) (z * u) = 0 := by
      intro u
      have hu : u = ∑ i, σ (b.repr (star' P u) i) • star' P (b i) := by
        conv_lhs => rw [← hs u, ← b.sum_repr (star' P u)]
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, star'_algebraMap]
      rw [hu, Finset.mul_sum, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [mul_smul_comm, map_smul, h1, smul_zero]
    have hz0 : z = 0 := (traceForm_nondegenerate E (Fld P)).1 z fun u => by
      rw [Algebra.traceForm_apply]; exact h2 u
    funext j
    exact Fintype.linearIndependent_iff.1 b.linearIndependent w (by rw [← hz0]) j

end GlobalTheory.TrUnitLat
