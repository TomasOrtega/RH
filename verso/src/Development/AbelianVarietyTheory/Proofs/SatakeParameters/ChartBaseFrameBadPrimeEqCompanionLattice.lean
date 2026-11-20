import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedFrameStandardLocalEqLocalizationStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicPointLatticeMulRationalGLStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionLatticeAdelicLatticeLocalizationEqStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionHermitianLatticeFgStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseFrameLat

/- English proof (translation)
Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, z, hz, hzx⟩`. Use `⟨e.symm x, ⟨s, hs, ?_⟩, by simp⟩` and prove the remaining obligations. Establish `: s • e.symm x = z`.

Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_smul, e.apply_symm_apply]`. Conclude with `hzx.symm`. Rewrite using `[this]`. Conclude with `hz`.

Introduce and unpack `⟨y, ⟨s, hs, hy⟩, rfl⟩`. Conclude with `⟨s, hs, s • y, hy, by simp⟩`.
-/
theorem locP_map_equiv' {R W W' : Type*} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
    (e : W ≃ₗ[R] W') (q : Ideal R) [q.IsPrime] (Λ : Submodule R W) :
    Formalism.HermitianLatticesTheory.localization₂ q (Λ.map (e : W →ₗ[R] W')) = (Formalism.HermitianLatticesTheory.localization₂ q Λ).map (e : W →ₗ[R] W') := by
  ext x
  constructor
  · rintro ⟨s, hs, z, hz, hzx⟩
    refine ⟨e.symm x, ⟨s, hs, ?_⟩, by simp⟩
    have : s • e.symm x = z := by
      apply e.injective
      rw [map_smul, e.apply_symm_apply]
      exact hzx.symm
    rw [this]
    exact hz
  · rintro ⟨y, ⟨s, hs, hy⟩, rfl⟩
    exact ⟨s, hs, s • y, hy, by simp⟩

/- English proof (translation)
The claim follows from `locP_map_equiv' ((toLE c).restrictScalars (𝓞 E)) q Λ`.
-/
theorem locP_mvL_comm {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ} (c : GL (Fin N) E) (q : Ideal (𝓞 E)) [q.IsPrime]
    (Λ : Submodule (𝓞 E) (Fin N → E)) : Formalism.HermitianLatticesTheory.localization₂ q (mvL c Λ) = mvL c (Formalism.HermitianLatticesTheory.localization₂ q Λ) :=
  locP_map_equiv' ((toLE c).restrictScalars (𝓞 E)) q Λ

/- English proof (translation)
Unfold `mvL`. Use `Submodule.map_id _` and compare the differences between its conclusion and the goal. Use `LinearMap.ext fun z => ?_` and prove the remaining obligations. Use `show toLE 1 z = z`. Rewrite using `[toLE_apply, Units.val_one, Matrix.one_mulVec]`.
-/
theorem mvL_one' {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ} (Λ : Submodule (𝓞 E) (Fin N → E)) : mvL 1 Λ = Λ := by
  unfold mvL
  convert Submodule.map_id _
  refine LinearMap.ext fun z => ?_
  show toLE 1 z = z
  rw [toLE_apply, Units.val_one, Matrix.one_mulVec]

/- English proof (translation)
Establish `e : ((mvL c Λ : Submodule (𝓞 E) (Fin N → E)) : Set (Fin N → E)) = (toLE c : (Fin N → E) →ₗ[E] (Fin N → E)) '' (Λ : Set (Fin N → E))`. Unfold `mvL`. Rewrite using `[Submodule.map_coe]`. Both sides reduce to the same expression. Rewrite using `[e, ← Submodule.map_span, h, Submodule.map_top, LinearMap.range_eq_top]`.

Conclude with `(toLE c).surjective`.
-/
theorem span_mvL {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ} (c : GL (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E))
    (h : Submodule.span E (Λ : Set (Fin N → E)) = ⊤) : Submodule.span E ((mvL c Λ : Submodule (𝓞 E) (Fin N → E)) : Set (Fin N → E)) = ⊤ := by
  have e : ((mvL c Λ : Submodule (𝓞 E) (Fin N → E)) : Set (Fin N → E)) = (toLE c : (Fin N → E) →ₗ[E] (Fin N → E)) '' (Λ : Set (Fin N → E)) := by
    unfold mvL
    rw [Submodule.map_coe]
    rfl
  rw [e, ← Submodule.map_span, h, Submodule.map_top, LinearMap.range_eq_top]
  exact (toLE c).surjective

end GlobalTheory.BaseFrameLat

open GlobalTheory.BaseFrameLat in

/- English proof (translation)
Introduce `D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hpins htie i hi β x p hp P`. Establish `hd : 1 ≤ (t.cst μ).D P` using `(t.idx_ok μ).cst_ok.D_pos P`. Establish `hR` using `GlobalTheory.T.transportedFrame_standardLocal_eq_localization t.seam P.1 (frsF t.sel (t.tup μ) p P) p.deco.1.N (GlobalTheory.TopStep.frsF_mem p P)`. Rewrite `hR` using `[hp.lat]`. Establish `hJ : IsUnit (gramN D i hi).det`.

Rewrite using `[← hpins.crd_orth i hi, Matrix.det_mul]`. Establish `hc : IsUnit ((A.crd i hi).1).det` using `(Matrix.isUnit_iff_isUnit_det _).mp (A.crd i hi).isUnit`. Use `IsUnit.mul ?_ hc` and prove the remaining obligations. Use `show IsUnit ((((A.crd i hi).1).map (sigD D : D.host.E →+* D.host.E))ᵀ).det`. Rewrite using `[Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`.

Conclude with `hc.map _`. Establish `hfg : (((St i hi).K β).lev.Lb).FG` using `Module.Finite.iff_fg.mp ((St i hi).K β).lev.Lb_fin`. Establish `hsp` using `((St i hi).K β).lev.Lb_span`. Establish `h4` using `GlobalTheory.T.companionLattice_adelicLattice_localization_eq D.sp (sigD D) rfl (gramN D i hi) hJ a x.1 x.2 _ hfg hsp (seamP t.seam P.1)`. Establish `hCfg` using `GlobalTheory.T.companionHermitianLattice_fg D.sp (gramN D i hi) hJ a _ hfg hsp`.

Use `set C := compan (sp := D.sp) (gramN D i hi) a ((St i hi).K β).lev.Lb with hC`. Establish `hCs : Submodule.span D.host.E (C : Set (Fin (D.R.N i) → D.host.E)) = ⊤`. Use `eq_top_iff.2 (hsp ▸ Submodule.span_mono ?_)` and prove the remaining obligations. Introduce `z hz`. Conclude with `(le_sup_left : ((St i hi).K β).lev.Lb ≤ C) hz`.

Unfold `latCo at hR`. Rewrite `hR` using `[locP_mvL_comm, h4, ← locP_mvL_comm]`. Establish `e1 : mvL (A.crd i hi) (latAd x.1 C) = latAd (ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P)) (mvL (A.fb i hi β P)⁻¹ C)`. Rewrite using `[GlobalTheory.T.adelicPointLattice_mul_rationalGL, ← mvL_mul, mul_inv_cancel, mvL_one']`. Conclude with `(latAd_rat _ _ _).symm`.

Rewrite `hR` using `[e1]`. Establish `h3` using `GlobalTheory.T.localisation_eq_stdAt_of_congruentOne_atPrime (seamP t.seam P.1) _ hd _ _ (mvL (A.fb i hi β P)⁻¹ C) (hCfg.map _) (span_mvL _ _ hCs) (hp.frame P) hR.symm`. Rewrite using `[← h3, ← locP_mvL_comm, ← mvL_mul, mul_inv_cancel, mvL_one']`.
-/
theorem GlobalTheory.TwV.baseFrame_std_eq_compan : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x : UA D i hi) p, IsPtAd A a i hi β x p → ∀ P : SB t μ, mvL (A.fb i hi β P) (stdAt D.host.E (D.R.N i) (seamP t.seam P.1)) = Formalism.HermitianLatticesTheory.localization₂ (seamP t.seam P.1).asIdeal (compan (sp := D.sp) (gramN D i hi) a ((St i hi).K β).lev.Lb)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hpins htie i hi β x p hp P
  have hd : 1 ≤ (t.cst μ).D P := (t.idx_ok μ).cst_ok.D_pos P
  have hR := GlobalTheory.T.transportedFrame_standardLocal_eq_localization t.seam P.1 (frsF t.sel (t.tup μ) p P) p.deco.1.N (GlobalTheory.TopStep.frsF_mem p P)
  rw [hp.lat] at hR
  have hJ : IsUnit (gramN D i hi).det := by
    rw [← hpins.crd_orth i hi, Matrix.det_mul]
    have hc : IsUnit ((A.crd i hi).1).det := (Matrix.isUnit_iff_isUnit_det _).mp (A.crd i hi).isUnit
    refine IsUnit.mul ?_ hc
    show IsUnit ((((A.crd i hi).1).map (sigD D : D.host.E →+* D.host.E))ᵀ).det
    rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hc.map _
  have hfg : (((St i hi).K β).lev.Lb).FG := Module.Finite.iff_fg.mp ((St i hi).K β).lev.Lb_fin
  have hsp := ((St i hi).K β).lev.Lb_span
  have h4 := GlobalTheory.T.companionLattice_adelicLattice_localization_eq D.sp (sigD D) rfl (gramN D i hi) hJ a x.1 x.2 _ hfg hsp (seamP t.seam P.1)
  have hCfg := GlobalTheory.T.companionHermitianLattice_fg D.sp (gramN D i hi) hJ a _ hfg hsp
  set C := compan (sp := D.sp) (gramN D i hi) a ((St i hi).K β).lev.Lb with hC
  have hCs : Submodule.span D.host.E (C : Set (Fin (D.R.N i) → D.host.E)) = ⊤ := by
    refine eq_top_iff.2 (hsp ▸ Submodule.span_mono ?_)
    intro z hz
    exact (le_sup_left : ((St i hi).K β).lev.Lb ≤ C) hz
  unfold latCo at hR
  rw [locP_mvL_comm, h4, ← locP_mvL_comm] at hR
  have e1 : mvL (A.crd i hi) (latAd x.1 C) = latAd (ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P)) (mvL (A.fb i hi β P)⁻¹ C) := by
    rw [GlobalTheory.T.adelicPointLattice_mul_rationalGL, ← mvL_mul, mul_inv_cancel, mvL_one']
    exact (latAd_rat _ _ _).symm
  rw [e1] at hR
  have h3 := GlobalTheory.T.localisation_eq_stdAt_of_congruentOne_atPrime (seamP t.seam P.1) _ hd _ _ (mvL (A.fb i hi β P)⁻¹ C) (hCfg.map _) (span_mvL _ _ hCs) (hp.frame P) hR.symm
  rw [← h3, ← locP_mvL_comm, ← mvL_mul, mul_inv_cancel, mvL_one']
