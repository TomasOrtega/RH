import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8

namespace GlobalTheory.CompanionTheory.NormPoly

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Take `⟨h1, h2⟩` from `hu`. Establish `hθ : thetaE E n u = u⁻¹` using `eq_inv_of_mul_eq_one_right h2`. Rewrite using `[h1, map_mul, map_inv, hθ, inv_inv, nrm]`. Use `group`.
-/
theorem norm_translate {u : GL (Fin n) E} (hu : IsTransl u) (d : GL (Fin n) E) :
    (d * u⁻¹) * thE E n (d * u⁻¹) = nrm d := by
  obtain ⟨h1, h2⟩ := hu
  have hθ : thetaE E n u = u⁻¹ := eq_inv_of_mul_eq_one_right h2
  rw [h1, map_mul, map_inv, hθ, inv_inv, nrm]
  group

/- English proof (translation)
Rewrite using `[polE, norm_translate hu]`.
-/
theorem polE_translate {u : GL (Fin n) E} (hu : IsTransl u) (d : GL (Fin n) E) :
    polE (d * u⁻¹) = (nrm d).val.charpoly := by
  rw [polE, norm_translate hu]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Establish `hv : ∀ g : GL (Fin n) E, ((GeneralLinearGroup.map τ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = g.val.map τ` using `fun _ => rfl`. Rewrite using `[hv, thetaR_val, thetaR_val, ← map_inv, hv]`. Simplify using `only [Matrix.map_apply, Matrix.transpose_apply]`.

Conclude with `IsCMField.complexEmbedding_complexConj E τ _`.
-/
theorem map_thetaE (τ : E →+* ℂ) (d : GL (Fin n) E) :
    GeneralLinearGroup.map τ (thetaE E n d) =
      thetaR (starRingEnd ℂ) n (GeneralLinearGroup.map τ d) := by
  apply Units.ext
  ext i j
  have hv : ∀ g : GL (Fin n) E, ((GeneralLinearGroup.map τ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = g.val.map τ := fun _ => rfl
  rw [hv, thetaR_val, thetaR_val, ← map_inv, hv]
  simp only [Matrix.map_apply, Matrix.transpose_apply]
  exact IsCMField.complexEmbedding_complexConj E τ _

/- English proof (translation)
Rewrite using `[← map_thetaE, ← map_mul, ← Matrix.charpoly_map]`. Both sides reduce to the same expression.
-/
theorem charpoly_map_nrm (τ : E →+* ℂ) (d : GL (Fin n) E) :
    (GeneralLinearGroup.map τ d * thetaR (starRingEnd ℂ) n (GeneralLinearGroup.map τ d)).val.charpoly =
      (nrm d).val.charpoly.map τ := by
  rw [← map_thetaE, ← map_mul, ← Matrix.charpoly_map]
  rfl

/- English proof (translation)
Establish `hm : (nrm d).val.charpoly.Monic` using `Matrix.charpoly_monic _`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨hm, by simp, h.1, fun τ z hz => ?_⟩` and prove the remaining obligations. Conclude with `h.2 τ z (Polynomial.isRoot_of_mem_roots hz)`.

Introduce and unpack `⟨-, -, hs, hr⟩`. Conclude with `⟨hs, fun τ z hz => hr τ z ((Polynomial.mem_roots (hm.map τ).ne_zero).2 hz)⟩`.
-/
theorem isRegEll_iff_mem_Ell (d : GL (Fin n) E) : IsRegEll d ↔ (nrm d).val.charpoly ∈ Ell E n := by
  have hm : (nrm d).val.charpoly.Monic := Matrix.charpoly_monic _
  constructor
  · intro h
    refine ⟨hm, by simp, h.1, fun τ z hz => ?_⟩
    exact h.2 τ z (Polynomial.isRoot_of_mem_roots hz)
  · rintro ⟨-, -, hs, hr⟩
    exact ⟨hs, fun τ z hz => hr τ z ((Polynomial.mem_roots (hm.map τ).ne_zero).2 hz)⟩

/- English proof (translation)
Introduce `E _ _ _ n u hu d`. Rewrite using `[polE_translate hu]`. Use `⟨isRegEll_iff_mem_Ell d, fun v => ⟨charpoly_map_nrm v.embedding d, fun h => ?_⟩⟩` and prove the remaining obligations. Unfold `EllC`. Rewrite using `[charpoly_map_nrm]`.

Conclude with `⟨h.1.map, fun z hz => h.2 v.embedding z hz⟩`.
-/
theorem polEq : PolEq := by
  intro E _ _ _ n u hu d
  rw [polE_translate hu]
  refine ⟨isRegEll_iff_mem_Ell d, fun v => ⟨charpoly_map_nrm v.embedding d, fun h => ?_⟩⟩
  unfold EllC
  rw [charpoly_map_nrm]
  exact ⟨h.1.map, fun z hz => h.2 v.embedding z hz⟩

end GlobalTheory.CompanionTheory.NormPoly
