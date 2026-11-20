import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PairCalc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod
open scoped TensorProduct

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules.

Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Treat this case separately.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
private lemma UpperTheory.Gal.crystallineComparison.Mod.tensor_decomp (p : ℕ) [Fact p.Prime] (B : Type) [AddCommGroup B]
    (a : B ⊗[ℤ] ℤ_[p]) :
    ∃ (c : B) (a' : B ⊗[ℤ] ℤ_[p]), a = c ⊗ₜ[ℤ] (1 : ℤ_[p]) + (p : ℤ) • a' := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul c z =>
    obtain ⟨r, z', hz⟩ : ∃ (r : ℤ) (z' : ℤ_[p]), z = r • (1 : ℤ_[p]) + (p : ℤ) • z' := by
      have h : z - (PadicInt.zmodRepr z : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p])} := by
        rw [← PadicInt.maximalIdeal_eq_span_p]
        exact PadicInt.sub_zmodRepr_mem z
      obtain ⟨z', hz'⟩ := Ideal.mem_span_singleton'.mp h
      refine ⟨(PadicInt.zmodRepr z : ℤ), z', ?_⟩
      have : z = (PadicInt.zmodRepr z : ℤ_[p]) + z' * p := by rw [hz']; ring
      simp only [zsmul_eq_mul, mul_one]
      push_cast
      rw [mul_comm (p : ℤ_[p])]
      first | (rw [mul_one]; exact this) | simpa using this
    refine ⟨r • c, c ⊗ₜ[ℤ] z', ?_⟩
    rw [hz, TensorProduct.tmul_add, TensorProduct.tmul_smul (p : ℤ), TensorProduct.tmul_smul r,
      TensorProduct.smul_tmul']
  | add a b ha hb =>
    obtain ⟨c, a', rfl⟩ := ha
    obtain ⟨d, b', rfl⟩ := hb
    exact ⟨c + d, a' + b', by rw [TensorProduct.add_tmul, smul_add]; abel⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Introduce a local definition for the expression. Extract witnesses or component facts from the available result.

Introduce a local definition for the expression. Establish an intermediate fact. By extensionality, compare the relevant components. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Supply the required witnesses or components. Equip the data with the indicated structure. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.crystallineComparison.Mod.oMod_of :
    OMod := by
  intro p _ D hm x
  obtain ⟨e⟩ := D.splitP
  have hsub : Subsingleton (Fin D.m) := by rw [hm]; infer_instance
  let i0 : Fin D.m := ⟨0, D.m_pos⟩
  obtain ⟨c, a', ha⟩ := tensor_decomp p (𝓞 D.F) (e (x ⊗ₜ[ℤ] (1 : ℤ_[p])) i0 i0)
  let M' : Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p]) := Matrix.of fun _ _ => a'
  have hM : e (x ⊗ₜ[ℤ] (1 : ℤ_[p])) = algebraMap (𝓞 D.F) _ c + (p : ℤ) • M' := by
    ext i j
    obtain rfl := Subsingleton.elim i i0
    obtain rfl := Subsingleton.elim j i0
    rw [ha]
    simp [M', Matrix.algebraMap_matrix_apply, Algebra.TensorProduct.algebraMap_apply]
  have hx : x ⊗ₜ[ℤ] (1 : ℤ_[p]) =
      (algebraMap (𝓞 D.F) D.O c) ⊗ₜ[ℤ] (1 : ℤ_[p]) + (p : ℤ) • e.symm M' := by
    have := congrArg e.symm hM
    rw [e.symm_apply_apply, map_add, map_zsmul, AlgEquiv.commutes,
      Algebra.TensorProduct.algebraMap_apply] at this
    exact this
  let P : Submodule ℤ D.O := LinearMap.range (LinearMap.lsmul ℤ D.O (p : ℤ))
  have hP : ∀ q : D.O ⧸ P, p • q = 0 := by
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective P q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨y, by simp⟩
  letI : Module (ZMod p) (D.O ⧸ P) := AddCommGroup.zmodModule hP
  let Φ : D.O ⊗[ℤ] ℤ_[p] →ₗ[ℤ] D.O ⧸ P := TensorProduct.lift <|
    LinearMap.mk₂ ℤ (fun y z => PadicInt.toZMod z • (Submodule.Quotient.mk y : D.O ⧸ P))
      (fun y y' z => by simp [smul_add])
      (fun n y z => by rw [Submodule.Quotient.mk_smul]; exact smul_comm _ _ _)
      (fun y z z' => by simp [add_smul])
      (fun n y z => by rw [map_zsmul, smul_assoc])
  have h1 : ∀ y : D.O, Φ (y ⊗ₜ[ℤ] (1 : ℤ_[p])) = Submodule.Quotient.mk y := by
    intro y
    change PadicInt.toZMod (1 : ℤ_[p]) • (Submodule.Quotient.mk y : D.O ⧸ P) = _
    rw [map_one, one_smul]
  have h2 := congrArg Φ hx
  rw [map_add, map_zsmul, h1, h1] at h2
  have h3 : (p : ℤ) • Φ (e.symm M') = 0 := by
    rw [natCast_zsmul]; exact hP _
  rw [h3, add_zero, Submodule.Quotient.eq] at h2
  obtain ⟨y, hy⟩ := h2
  refine ⟨c, y, ?_⟩
  have hy' : (p : ℤ) • y = x - algebraMap (𝓞 D.F) D.O c := hy
  rw [map_natCast, ← sub_eq_iff_eq_add', ← hy']
  simp
