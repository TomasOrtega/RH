import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
import GroundTheory.AutomorphicForms.AnisotropicHeight
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.TorusCh

/- English proof (translation)
Unfold `chi`. Use `Continuous.matrix_det ?_` and prove the remaining obligations. Conclude with `continuous_const.add (continuous_const.mul (Units.continuous_val.sub continuous_const))`.
-/
theorem continuous_chi {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (e : Matrix (Fin n) (Fin n) E) : Continuous (chi e : GA E n → Ad E) := by
  unfold chi
  refine Continuous.matrix_det ?_
  exact continuous_const.add (continuous_const.mul (Units.continuous_val.sub continuous_const))

/- English proof (translation)
Rewrite using `[continuousOn_iff_continuous_domRestrict]`. Set `ψ : ↥(H : Set (GA E n)) → (Ad E)ˣ` to `fun t => ⟨chi e t.1, chi e t.1⁻¹, by rw [← chi_mul e he _ _ (hH _ t.2), mul_inv_cancel, chi_one], by rw [← chi_mul e he _ _ (comm_inv (hH _ t.2)), inv_mul_cancel, chi_one]⟩`. Establish `hψ : Continuous ψ`. Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `(continuous_chi e).comp continuous_subtype_val`.

Conclude with `(continuous_chi e).comp (continuous_inv.comp continuous_subtype_val)`. Establish `hm : Continuous fun t => (GroundTheory.Global.IdeleGroup.ideleModule E (ψ t) : ℝ)` using `continuous_subtype_val.comp (GroundTheory.Global.IdeleGroup.continuous_ideleModule.comp hψ)`. Establish `heq : (H : Set (GA E n)).domRestrict (lam e) = fun t : ↥(H : Set (GA E n)) => Real.log (GroundTheory.Global.IdeleGroup.ideleModule E (ψ t) : ℝ)`. Use function extensionality and compare the values at `t`. Conclude with `hlog (ψ t)`.

Rewrite using `[heq]`. Conclude with `hm.log fun t => (GroundTheory.Global.IdeleGroup.ideleModule E (ψ t)).2.ne'`.
-/
theorem continuousOn_lam (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (e : Matrix (Fin n) (Fin n) E) (he : e * e = e)
    (hlog : ∀ s : (Ad E)ˣ, logAbs (s : Ad E) = Real.log (GroundTheory.Global.IdeleGroup.ideleModule E s : ℝ))
    (H : Subgroup (GA E n)) (hH : ∀ t ∈ H, t.val * rm e = rm e * t.val) :
    ContinuousOn (lam e) (H : Set (GA E n)) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let ψ : ↥(H : Set (GA E n)) → (Ad E)ˣ := fun t =>
    ⟨chi e t.1, chi e t.1⁻¹,
      by rw [← chi_mul e he _ _ (hH _ t.2), mul_inv_cancel, chi_one],
      by rw [← chi_mul e he _ _ (comm_inv (hH _ t.2)), inv_mul_cancel, chi_one]⟩
  have hψ : Continuous ψ := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (continuous_chi e).comp continuous_subtype_val
    · exact (continuous_chi e).comp (continuous_inv.comp continuous_subtype_val)
  have hm : Continuous fun t => (GroundTheory.Global.IdeleGroup.ideleModule E (ψ t) : ℝ) :=
    continuous_subtype_val.comp (GroundTheory.Global.IdeleGroup.continuous_ideleModule.comp hψ)
  have heq : (H : Set (GA E n)).domRestrict (lam e) =
      fun t : ↥(H : Set (GA E n)) => Real.log (GroundTheory.Global.IdeleGroup.ideleModule E (ψ t) : ℝ) := by
    funext t
    exact hlog (ψ t)
  rw [heq]
  exact hm.log fun t => (GroundTheory.Global.IdeleGroup.ideleModule E (ψ t)).2.ne'

end GlobalTheory.CompanionTheory.TorusCh

end
