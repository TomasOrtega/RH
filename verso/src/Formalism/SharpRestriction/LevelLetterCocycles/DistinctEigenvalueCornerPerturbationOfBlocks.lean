import Formalism.SharpRestriction.LevelLetterCocycles.GoodCongruenceDataOf

noncomputable section

open Formalism.BasicNotions

namespace Formalism.MainNotions.N.RepresentationBoundsCohomology

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Matrix Formalism.RepresentationBoundsCohomology.ringDataObjects Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
  (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result. Replace the relevant objects with their definitions.

Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem card_blk (r t : ℕ) (c : Fin (t + 1)) (hc : c ≠ 0) :
    Fintype.card {a : Fin (r + t) // blkG r t a = c} = 1 := by
  rw [Fintype.card_eq_one_iff]
  have hc1 : 1 ≤ (c : ℕ) := by
    rcases Nat.eq_zero_or_pos (c : ℕ) with h | h
    · exact absurd (Fin.ext h) hc
    · exact h
  have hct := c.isLt
  refine ⟨⟨⟨r + ((c : ℕ) - 1), by omega⟩, ?_⟩, ?_⟩
  · unfold blkG
    rw [dif_neg (by simp)]
    exact Fin.ext (by simp; omega)
  · rintro ⟨a, ha⟩
    apply Subtype.ext
    unfold blkG at ha
    split_ifs at ha with h
    · exact absurd ha.symm hc
    · have h2 := congrArg Fin.val ha
      simp at h2
      exact Fin.ext (by simp; omega)

/- English proof (translation)
Replace the relevant objects with their definitions. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem exists_natAdd (r t : ℕ) (a : Fin (r + t)) (ha : blkG r t a ≠ 0) :
    ∃ c : Fin t, a = Fin.natAdd r c := by
  unfold blkG at ha
  split_ifs at ha with h
  · exact absurd rfl ha
  · exact ⟨⟨(a : ℕ) - r, by have := a.2; omega⟩, Fin.ext (by simp; omega)⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem primHyp_of (hN : NormAt N r ρ π)
    (hG1 : ∀ (γ : GE N) (k : ℕ), (fun x : N.X i => ((rO N i r x γ).charpolyRev).coeff k) ∈ N.T i) :
    PrimHyp (N.O i) (N.T i) (repX N r) π (blk R) (chiU N i 1) (epsU N i) := by
  obtain ⟨hbd, hχ, -⟩ := hN
  refine ⟨N.T_local i, N.T_sep i, hG1, hbd, fun c hc => card_blk R.r R.t c hc, fun g a ha => ?_⟩
  obtain ⟨c, rfl⟩ := exists_natAdd R.r R.t a ha
  have h1 : ((blk R (Fin.natAdd R.r c) : Fin (R.t + 1)) : ℕ) - 1 = (c : ℕ) := by
    rw [show blk R (Fin.natAdd R.r c) = c.succ from blkG_natAdd R.r R.t c]
    simp
  rw [h1]
  refine (hχ g c).trans ?_
  have h2 := N.chi_def i ((c : ℕ) + 1) (by omega) (by have := c.2; omega)
  have h3 : chiU N i ((c : ℕ) + 1) g = chiU N i 1 g * ((epsU N i g)⁻¹ ^ (c : ℕ)) := by
    show N.chi i ((c : ℕ) + 1) g = _
    rw [h2, MonoidHom.mul_apply]
    congr 1
    have h4 : (-(((((c : ℕ) + 1 : ℕ) : ℤ)) - 1)) = -((c : ℕ) : ℤ) := by
      push_cast
      ring
    rw [h4, _root_.zpow_neg, zpow_natCast, MonoidHom.inv_apply, MonoidHom.pow_apply, inv_pow]
    rfl
  rw [h3]
  simp

def InertiaElementIdempotentChoice : Prop :=
  ∃ g0 : GE N, (∃ w ∈ placesOver H.E (N.l i), g0 ∈ Ine (F := H.E) (N.plOm.1 w)) ∧
    (∃ u : ℤ_[N.l i]ˣ, ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g0 : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) =
      1 + (N.l i : ℤ_[N.l i]) ^ N.s0 i * (u : ℤ_[N.l i])) ∧
    ∃ eB e₁ s : N.X i → MatN N i, IdemHyp (N.O i) (N.T i) (repX N r) π (blk R) eB e₁ ∧
      DistinctEigenvalueCornerPerturbation (N.O i) (N.T i) (repX N r) π R.t g0 eB s

end Formalism.MainNotions.N.RepresentationBoundsCohomology

namespace Formalism.MainNotions.LargeLevelLemmas

open Formalism.MainNotions.N Formalism.MainNotions.N.RepresentationBoundsCohomology

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* Matrix.GeneralLinearGroup (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* Matrix.GeneralLinearGroup (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

end Formalism.MainNotions.LargeLevelLemmas

end
