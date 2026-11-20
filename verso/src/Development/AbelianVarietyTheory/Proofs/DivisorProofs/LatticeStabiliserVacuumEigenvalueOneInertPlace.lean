import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzTensorNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemAdelicSchwartzSpaceNumberFieldOfMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagMemDoubledVacuumLatticeStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOneNegOneConjAntidiagonalStabilizerMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumEigenInertPlaceLatticeStabiliserStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumEigenvalueEqOneInertPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBoxTensorLeftFixedLinearApplyStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.DblVacV

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' hT v w hw hv k hk c hc`. Take `⟨d', hd', -, dd, omd, hdc, hsp, hbox⟩` from `hT.weil.2.1`. Establish `hvac` using `hT.geo.hM.vac v`. Take `⟨r, hr, hr0⟩` from `GlobalTheory.T.exists_complementaryAdelicSchwartz_tensor_ne_zero _ v (G.M.vac v) hvac.1 hvac.2.1`. Use `set V₀ := tens (evFin F v) (G.M.vac v) r with hV₀`.

Use `set S := boxFun V₀ (fun x => star (V₀ x)) with hS`. Establish `hS0 : ∃ x, S x ≠ 0`. Take `⟨x, hx⟩` from `Function.ne_iff.mp hr0`. Use `⟨Sum.elim x x, ?_⟩` and prove the remaining obligations. Simplify using `only [hS, boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.zero_apply] at hx ⊢`.

Conclude with `mul_ne_zero hx (star_ne_zero.mpr hx)`. Set `H : Subgroup (GlobalTheory.DblVac.UD σ G.V)` to `{ carrier := {g | omd g S = S} one_mem' := by simp mul_mem' := fun {x y} hx hy => by`. Simplify using `only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *`. Rewrite using `[hy, hx]`. Use the proof step `inv_mem' := fun {x} hx => by`.

Simplify using `only [Set.mem_setOf_eq] at *`. Use `conv_lhs => rw [← hx]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }`. Establish `hD : ∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PDiag σ G.V → p ∈ H` using `fun p hp hpd => by`. Take `⟨μ, hμ⟩` from `GlobalTheory.T.doubledVacuum_eigen_inertPlace_latticeStabiliser F E σ B a a' G X om om' hT v w hw hv d' hd' dd omd hdc hsp r hr p hp`.

Establish `h1` using `GlobalTheory.T.doubledVacuum_eigenvalue_eq_one_inertPlace F E σ B a a' G X om om' hT v w hw hv d' hd' dd omd hdc hsp r hr hr0 p hp hpd μ hμ`. Use `show omd p S = S`. Rewrite using `[hμ, h1, one_smul]`. Establish `hA : ∀ q ∈ GlobalTheory.DblVac.KD σ G.V v, q ∈ GlobalTheory.DblVac.PAnti σ G.V → q ∈ H` using `fun q hq hqa => by`. Take `⟨w₀, hw₀, hW⟩` from `GlobalTheory.T.exists_diagOneNegOne_conj_antidiagonalStabilizer_mem σ G.V v`.

Take `⟨h1, h2⟩` from `hW q hq hqa`. Establish `hq' : omd (w₀ * q * w₀⁻¹) S = S` using `hD _ h1 h2`. Take `⟨μ, hμ⟩` from `GlobalTheory.T.doubledVacuum_eigen_inertPlace_latticeStabiliser F E σ B a a' G X om om' hT v w hw hv d' hd' dd omd hdc hsp r hr w₀ hw₀`. Establish `hinv : μ • omd w₀⁻¹ S = S`. Rewrite using `[← LinearMap.map_smul, ← hμ, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`.

Establish `e : q = w₀⁻¹ * (w₀ * q * w₀⁻¹) * w₀` using `by group`. Use `show omd q S = S`. Rewrite using `[e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hμ, LinearMap.map_smul, hq', LinearMap.map_smul, hinv]`. Take `⟨gd, hgd, hgdK⟩` from `GlobalTheory.T.exists_diag_mem_doubledVacuumLatticeStabilizer σ G.V v k hk`. Establish `hfix : omd gd S = S` using `GlobalTheory.T.doubledStabilizer_generated_antidiag_splitPlace_V F E σ B a a' G X om om' hT v w hw hv H hD hA gd hgdK`.

Establish `hb` using `hbox k gd hgd V₀ hr.2 (fun x => star (V₀ x)) (GlobalTheory.T.conj_mem_adelicSchwartzSpaceNumberField_of_mem _ V₀ hr.2)`. Establish `hk1 : (om.comp (MonoidHom.inl _ _)) k V₀ = c • V₀`. Rewrite using `[MonoidHom.comp_apply, MonoidHom.inl_apply, hV₀, hc r hr]`. Use function extensionality and compare the values at `x`. Simplify using `[tens, mul_assoc]`.

Rewrite `hb` using `[hk1]`. Establish `hcS : c • S = S`. Combine the equalities or inequalities in the displayed calculation. Use function extensionality and compare the values at `x`. Simplify using `[hS, boxFun, mul_assoc]`.

Use `_ = omd gd S := hb.symm`. Use `_ = S := hfix`. Take `⟨x, hx⟩` from `hS0`. Use `congrFun hcS x` as an intermediate fact. Simplify using `only [Pi.smul_apply, smul_eq_mul] at this`.

Conclude with `mul_right_cancel₀ hx (this.trans (one_mul _).symm)`.
-/
theorem eigen_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v, ∀ c : ℂ, Acts (evFin F v) (om (k, 1)) (G.M.vac v) (c • G.M.vac v) → c = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hw hv k hk c hc
  obtain ⟨d', hd', -, dd, omd, hdc, hsp, hbox⟩ := hT.weil.2.1
  have hvac := hT.geo.hM.vac v
  obtain ⟨r, hr, hr0⟩ := GlobalTheory.T.exists_complementaryAdelicSchwartz_tensor_ne_zero _ v (G.M.vac v) hvac.1 hvac.2.1
  set V₀ := tens (evFin F v) (G.M.vac v) r with hV₀
  set S := boxFun V₀ (fun x => star (V₀ x)) with hS
  have hS0 : ∃ x, S x ≠ 0 := by
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hr0
    refine ⟨Sum.elim x x, ?_⟩
    simp only [hS, boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.zero_apply] at hx ⊢
    exact mul_ne_zero hx (star_ne_zero.mpr hx)
  let H : Subgroup (GlobalTheory.DblVac.UD σ G.V) :=
    { carrier := {g | omd g S = S}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hD : ∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PDiag σ G.V → p ∈ H := fun p hp hpd => by
    obtain ⟨μ, hμ⟩ := GlobalTheory.T.doubledVacuum_eigen_inertPlace_latticeStabiliser F E σ B a a' G X om om' hT v w hw hv d' hd' dd omd hdc hsp r hr p hp
    have h1 := GlobalTheory.T.doubledVacuum_eigenvalue_eq_one_inertPlace F E σ B a a' G X om om' hT v w hw hv d' hd' dd omd hdc hsp r hr hr0 p hp hpd μ hμ
    show omd p S = S
    rw [hμ, h1, one_smul]
  have hA : ∀ q ∈ GlobalTheory.DblVac.KD σ G.V v, q ∈ GlobalTheory.DblVac.PAnti σ G.V → q ∈ H := fun q hq hqa => by
    obtain ⟨w₀, hw₀, hW⟩ := GlobalTheory.T.exists_diagOneNegOne_conj_antidiagonalStabilizer_mem σ G.V v
    obtain ⟨h1, h2⟩ := hW q hq hqa
    have hq' : omd (w₀ * q * w₀⁻¹) S = S := hD _ h1 h2
    obtain ⟨μ, hμ⟩ := GlobalTheory.T.doubledVacuum_eigen_inertPlace_latticeStabiliser F E σ B a a' G X om om' hT v w hw hv d' hd' dd omd hdc hsp r hr w₀ hw₀
    have hinv : μ • omd w₀⁻¹ S = S := by
      rw [← LinearMap.map_smul, ← hμ, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
    have e : q = w₀⁻¹ * (w₀ * q * w₀⁻¹) * w₀ := by group
    show omd q S = S
    rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hμ, LinearMap.map_smul, hq',
      LinearMap.map_smul, hinv]
  obtain ⟨gd, hgd, hgdK⟩ := GlobalTheory.T.exists_diag_mem_doubledVacuumLatticeStabilizer σ G.V v k hk
  have hfix : omd gd S = S := GlobalTheory.T.doubledStabilizer_generated_antidiag_splitPlace_V F E σ B a a' G X om om' hT v w hw hv H hD hA gd hgdK
  have hb := hbox k gd hgd V₀ hr.2 (fun x => star (V₀ x)) (GlobalTheory.T.conj_mem_adelicSchwartzSpaceNumberField_of_mem _ V₀ hr.2)
  have hk1 : (om.comp (MonoidHom.inl _ _)) k V₀ = c • V₀ := by
    rw [MonoidHom.comp_apply, MonoidHom.inl_apply, hV₀, hc r hr]
    funext x
    simp [tens, mul_assoc]
  rw [hk1] at hb
  have hcS : c • S = S := by
    calc c • S = boxFun (c • V₀) (fun x => star (V₀ x)) := by
          funext x
          simp [hS, boxFun, mul_assoc]
      _ = omd gd S := hb.symm
      _ = S := hfix
  obtain ⟨x, hx⟩ := hS0
  have := congrFun hcS x
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hx (this.trans (one_mul _).symm)

end GlobalTheory.DblVacV
