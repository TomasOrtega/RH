import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilRepRationalPointsThetaFunctionsFock
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalUnitaryGroupStructure
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionSpaceHeisenbergLaws
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.RatPt

variable {D : D7} {S T : HSp D}

/- English proof (translation)
Set `e : AE D` to `(pairA D.host.F 1 0) ⊗ₜ[D.host.F] (1 : D.host.E)`. Establish `h1 : infPart D e = 1` using `rfl`. Establish `h0 : finPart D e = 0`. Express the relevant statement in the definitionally equal form `(0 : Af D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0`. Conclude with `TensorProduct.zero_tmul _ _`.

Use `⟨Matrix.of fun i j => (1 - e) * w i j, Matrix.of fun i j => e * w i j, ?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `infPart D ((1 - e) * w i j) = 0`. Rewrite using `[RingHom.map_mul, RingHom.map_sub, h1, RingHom.map_one, sub_self, zero_mul]`. Use extensionality with `i j`.

Express the relevant statement in the definitionally equal form `finPart D (e * w i j) = 0`. Rewrite using `[RingHom.map_mul, h0, zero_mul]`. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `w i j = (1 - e) * w i j + e * w i j`. Rewrite using `[← add_mul, sub_add_cancel, one_mul]`.
-/
theorem exists_fin_add_real (w : WO S T) :
    ∃ u v : WO S T, u.map (infPart D) = 0 ∧ v.map (finPart D) = 0 ∧ w = u + v := by
  let e : AE D := (pairA D.host.F 1 0) ⊗ₜ[D.host.F] (1 : D.host.E)
  have h1 : infPart D e = 1 := rfl
  have h0 : finPart D e = 0 := by
    change (0 : Af D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    exact TensorProduct.zero_tmul _ _
  refine ⟨Matrix.of fun i j => (1 - e) * w i j, Matrix.of fun i j => e * w i j, ?_, ?_, ?_⟩
  · ext i j
    change infPart D ((1 - e) * w i j) = 0
    rw [RingHom.map_mul, RingHom.map_sub, h1, RingHom.map_one, sub_self, zero_mul]
  · ext i j
    change finPart D (e * w i j) = 0
    rw [RingHom.map_mul, h0, zero_mul]
  · ext i j
    change w i j = (1 - e) * w i j + e * w i j
    rw [← add_mul, sub_add_cancel, one_mul]

/- English proof (translation)
Take `⟨u, v, hu, hv, rfl⟩` from `exists_fin_add_real w`. Establish `h` using `GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 hu (GlobalTheory.WeilVacMove.isTheta_heisO_real hψ hv hf)`. Rewrite `h` using `[GlobalTheory.WeilVacMove.heisO_heisO, (GlobalTheory.WeilVacMove.symplOH_fin_real S T u v hu hv).1, AddChar.map_zero_eq_one, one_smul]`. Then use the resulting hypothesis.
-/
theorem isTheta_heisO {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (w : WO S T) : IsThetaFunO ψ S T (heisO ψ S T w f) := by
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_fin_add_real w
  have h := GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 hu (GlobalTheory.WeilVacMove.isTheta_heisO_real hψ hv hf)
  rwa [GlobalTheory.WeilVacMove.heisO_heisO, (GlobalTheory.WeilVacMove.symplOH_fin_real S T u v hu hv).1, AddChar.map_zero_eq_one,
    one_smul] at h

/- English proof (translation)
Unfold `actO`. Rewrite using `[inv_one, GlobalTheory.Ker.OmRat.mt_one', Matrix.mul_one]`.
-/
theorem actO_one (h : GA D T) (w : WO S T) : actO S T 1 h w =
    HMul.hMul (Formalism.L2.Theta.mt T h) (w : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
  unfold actO
  rw [inv_one, GlobalTheory.Ker.OmRat.mt_one', Matrix.mul_one]

/- English proof (translation)
The claim follows from `Matrix.map_mul (f := (θ ρ).comp (infPart D))`.
-/
theorem compAt_mul (θ : InfFam D) (ρ : D.what₂.Tau) {a b c : ℕ} (x : Mx D a b) (y : Mx D b c) :
    compAt θ ρ (x * y : Mx D a c) = compAt θ ρ x * compAt θ ρ y :=
  Matrix.map_mul (f := (θ ρ).comp (infPart D))

/- English proof (translation)
Use extensionality with `i j`. Conclude with `(hθ ρ).1 (m i j)`.
-/
theorem compAt_rat {θ : InfFam D} (hθ : IsInfFam θ) (ρ : D.what₂.Tau) {a b : ℕ}
    (m : Matrix (Fin a) (Fin b) D.host.E) : compAt θ ρ (m.map (incA D)) = m.map (tauE D ρ) := by
  ext i j
  exact (hθ ρ).1 (m i j)

/- English proof (translation)
Introduce `D S T r g hr ψ θ X eT bas idx hS δ hδ`. Substitute `hr` using the available equality. Take `⟨hψ, hθ, -, -, hM, -, he, -⟩` from `hS`. Take `⟨ga, hga, hδ'⟩` from `id hδ`. Establish `hm : Formalism.L2.Theta.mt T δ = (ga : Matrix (Fin T.rank) (Fin T.rank) D.host.E).map (incA D)` using `(congrArg Units.val hδ').symm`.

Establish `hc : ∀ τ : X.Ψ, compAt θ (eT.symm τ) (Formalism.L2.Theta.mt T δ) = (ga : Matrix (Fin T.rank) (Fin T.rank) D.host.E).map τ.1` using `fun τ => by`. Rewrite using `[hm, compAt_rat hθ, ← he, Equiv.apply_symm_apply]`. Use `⟨ga, hm, ?_, fun Z => ?_, fun w => ⟨fun hw => ⟨actO S T 1 δ⁻¹ w, ?_, ?_⟩, fun τ k => ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `x y`. Establish `hG : X.Gm = (-T.gram)ᵀ` using `hM.1`.

Rewrite using `[hG, GlobalTheory.Ker.Grp.herm_eq, GlobalTheory.Ker.Grp.herm_eq]`. Use `GlobalTheory.Ker.Grp.hform_mulVec _ _ _ ?_ _ _` and prove the remaining obligations. Establish `h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) ga.1 * T.gram * ga.1 = T.gram` using `hga`. Rewrite using `[Matrix.mul_neg, Matrix.neg_mul, h]`. Use function extensionality and compare the values at `τ`.

Express the relevant statement in the definitionally equal form `(ga : Matrix (Fin T.rank) (Fin T.rank) D.host.E).map τ.1 * Z (eT.symm τ) = compAt θ (eT.symm τ) (Formalism.L2.Theta.mt T δ) * Z (eT.symm τ)`. Rewrite using `[hc]`. Unfold `GlobalTheory.Ker.IsRealPt at hw ⊢`. Rewrite using `[GlobalTheory.KerReal.map_actO, hw, Matrix.mul_zero, Matrix.zero_mul]`. Use `GlobalTheory.Ker.OmRat.actO_inv_cancel (1 : GA D S) δ w` as an intermediate fact.

Rewrite `this` using `[inv_one]`. Conclude with `this.symm`. Use function extensionality and compare the values at `a`. Express the relevant statement in the definitionally equal form `compAt θ (eT.symm τ) (actO S T 1 δ w) a k = _`. Rewrite using `[actO_one, compAt_mul, hc]`.

Both sides reduce to the same expression. Introduce `χS χT om H f hf w`. Establish `h1` using `H.om_heis 1 δ w f hf`. Establish `h2` using `H.om_aut 1 (one_mem _) δ hδ _ (isTheta_heisO hψ hf w)`. Rewrite using `[← GlobalTheory.Ker.OmRat.heisO_at_zero ψ _ (om (1, δ) f), ← h1]`.

Conclude with `h2.trans (GlobalTheory.Ker.OmRat.heisO_at_zero _ _ _)`.
-/
theorem rational_points : ∀ (D : D7) (S T : HSp D) (r g : ℕ) (hr : T.rank = r) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (X : Data D.host.E r) (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hS : IsSet ψ θ S T hr X eT bas), ∀ δ ∈ GQ T, ∃ ga : GL (Fin r) D.host.E, Formalism.L2.Theta.mt T δ = ((ga : Matrix (Fin r) (Fin r) D.host.E).submatrix (Fin.cast hr) (Fin.cast hr)).map (incA D) ∧ IsUn X ga ∧ (∀ Z : Fam T, lact ga (frOf hr eT Z) = frOf hr eT (mvZ θ δ Z)) ∧ (∀ w : WO S T, (GlobalTheory.Ker.IsRealPt w → ∃ w' : WO S T, GlobalTheory.Ker.IsRealPt w' ∧ w = actO S T 1 δ w') ∧ ∀ τ k, rePt θ hr eT (actO S T 1 δ w) τ k = ((ga : Matrix (Fin r) (Fin r) D.host.E).map τ.1) *ᵥ rePt θ hr eT w τ k) ∧ ∀ (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∀ w, om (1, δ) f (actO S T 1 δ w) = f w := by
  intro D S T r g hr ψ θ X eT bas idx hS δ hδ
  subst hr
  obtain ⟨hψ, hθ, -, -, hM, -, he, -⟩ := hS
  obtain ⟨ga, hga, hδ'⟩ := id hδ
  have hm : Formalism.L2.Theta.mt T δ = (ga : Matrix (Fin T.rank) (Fin T.rank) D.host.E).map (incA D) :=
    (congrArg Units.val hδ').symm
  have hc : ∀ τ : X.Ψ, compAt θ (eT.symm τ) (Formalism.L2.Theta.mt T δ) =
      (ga : Matrix (Fin T.rank) (Fin T.rank) D.host.E).map τ.1 := fun τ => by
    rw [hm, compAt_rat hθ, ← he, Equiv.apply_symm_apply]
  refine ⟨ga, hm, ?_, fun Z => ?_, fun w => ⟨fun hw => ⟨actO S T 1 δ⁻¹ w, ?_, ?_⟩, fun τ k => ?_⟩, ?_⟩
  · intro x y
    have hG : X.Gm = (-T.gram)ᵀ := hM.1
    rw [hG, GlobalTheory.Ker.Grp.herm_eq, GlobalTheory.Ker.Grp.herm_eq]
    refine GlobalTheory.Ker.Grp.hform_mulVec _ _ _ ?_ _ _
    have h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) ga.1 * T.gram * ga.1 = T.gram := hga
    rw [Matrix.mul_neg, Matrix.neg_mul, h]
  · funext τ
    change (ga : Matrix (Fin T.rank) (Fin T.rank) D.host.E).map τ.1 * Z (eT.symm τ) =
      compAt θ (eT.symm τ) (Formalism.L2.Theta.mt T δ) * Z (eT.symm τ)
    rw [hc]
  · unfold GlobalTheory.Ker.IsRealPt at hw ⊢
    rw [GlobalTheory.KerReal.map_actO, hw, Matrix.mul_zero, Matrix.zero_mul]
  · have := GlobalTheory.Ker.OmRat.actO_inv_cancel (1 : GA D S) δ w
    rw [inv_one] at this
    exact this.symm
  · funext a
    change compAt θ (eT.symm τ) (actO S T 1 δ w) a k = _
    rw [actO_one, compAt_mul, hc]
    rfl
  · intro χS χT om H f hf w
    have h1 := H.om_heis 1 δ w f hf
    have h2 := H.om_aut 1 (one_mem _) δ hδ _ (isTheta_heisO hψ hf w)
    rw [← GlobalTheory.Ker.OmRat.heisO_at_zero ψ _ (om (1, δ) f), ← h1]
    exact h2.trans (GlobalTheory.Ker.OmRat.heisO_at_zero _ _ _)

end GlobalTheory.OneMapRef.RatPt
