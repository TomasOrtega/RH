import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbWords
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftFubiniNormalizedTower

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PartialBesselProperness

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section left

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def sE (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) (x : PBQ.XP k p ρ) : B.Mat k n := D.castM e (PBQ.sP Bj x)

open Classical in

def gI (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) (Ψ : B.Mat k n → (Wq →L[ℂ] Wp)) (x : PBQ.XP k p ρ)
    (g : B.Mat k n) : Wq →L[ℂ] Wp :=
  if PBQ.GoodP Bj x then (Bj.π (Matrix.of x.1.1)).comp (Ψ (sE Bj e x * g)) else 0

def TI (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) (Ψ : B.Mat k n → (Wq →L[ℂ] Wp)) (g : B.Mat k n) :
    Wq →L[ℂ] Wp :=
  ∫ x, PBQ.cP Bj x • gI Bj e Ψ x g ∂(PBQ.muXP Bj)

/- English proof (translation)
Use function extensionality and compare the values at `g`. Unfold `PBQ.pbF TI`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [PBQ.ae_goodP (p := p) Bj] with x hx`. Simplify using `[PBQ.pbI, gI, hx, sE]`.
-/
theorem pbF_eq_TI (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (H : B.Mat k n → (Wq →L[ℂ] Wp)) : PBQ.pbF Bj B0 e H = TI Bj e (PBG.Kr B0 H) := by
  funext g
  unfold PBQ.pbF TI
  refine integral_congr_ae ?_
  filter_upwards [PBQ.ae_goodP (p := p) Bj] with x hx
  simp [PBQ.pbI, gI, hx, sE]

/- English proof (translation)
Use `⟨fun i => by simp, fun i j hij => ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.transpose_apply, Matrix.one_apply]`. Rewrite using `[if_neg (ne_of_lt hij)]`.
-/
theorem isLowerUni_one {d : ℕ} : G.IsLowerUni (1 : Matrix (Fin d) (Fin d) ℂ) := by
  refine ⟨fun i => by simp, fun i j hij => ?_⟩
  simp only [Matrix.transpose_apply, Matrix.one_apply]
  rw [if_neg (ne_of_lt hij)]

/- English proof (translation)
Distinguish the cases in `hx : PBQ.GoodP Bj x`. Rewrite using `[PBQ.sP, if_pos hx]`. Establish `h` using `Formalism.FourierDecayAlt.P.LeftFubiniLemmas.left_factor_mem k p ρ Bj.z (-x.2) 1 (Matrix.of x.1.1) (Matrix.of x.1.2) Bj.z_mem isLowerUni_one hx.1 hx.2`. Rewrite `h` using `[Matrix.conjTranspose_one, inv_one, Formalism.FourierDecayAlt.P.PBH.muP_one', Matrix.mul_one]`. Then use the resulting hypothesis. Rewrite using `[PBQ.sP, if_neg hx]`.

Conclude with `Formalism.FourierDecayAlt.P.PBG.one_mem_Sset k (p + ρ) _`.
-/
theorem leftFactor_mem (Bj : B.RealPlaceData k ρ Wp Wq) (x : PBQ.XP k p ρ) :
    PBQ.sP Bj x ∈ Sset k (p + ρ) (liftVec k p ρ Bj.z) := by
  by_cases hx : PBQ.GoodP Bj x
  · rw [PBQ.sP, if_pos hx]
    have h := Formalism.FourierDecayAlt.P.LeftFubiniLemmas.left_factor_mem k p ρ Bj.z (-x.2) 1 (Matrix.of x.1.1) (Matrix.of x.1.2) Bj.z_mem
      isLowerUni_one hx.1 hx.2
    rwa [Matrix.conjTranspose_one, inv_one, Formalism.FourierDecayAlt.P.PBH.muP_one', Matrix.mul_one] at h
  · rw [PBQ.sP, if_neg hx]
    exact Formalism.FourierDecayAlt.P.PBG.one_mem_Sset k (p + ρ) _

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.BetaSesquilinearity.Sset_sub (leftFactor_mem Bj x)`.
-/
theorem sP_GV (Bj : B.RealPlaceData k ρ Wp Wq) (x : PBQ.XP k p ρ) : PBQ.sP Bj x ∈ B.GV k (p + ρ) :=
  Formalism.FourierDecayAlt.P.BetaSesquilinearity.Sset_sub (leftFactor_mem Bj x)

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.PBE.castM_GV e (sP_GV Bj x)`.
-/
theorem sE_GV (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) (x : PBQ.XP k p ρ) : sE Bj e x ∈ B.GV k n :=
  Formalism.FourierDecayAlt.P.PBE.castM_GV e (sP_GV Bj x)

/- English proof (translation)
Substitute `e` using the available equality. Simplify using `only [sE, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]`. Conclude with `leftFactor_mem Bj x`.
-/
theorem sE_mem_S (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) (x : PBQ.XP k p ρ) :
    sE Bj e x ∈ Sset k n (D.castV e (liftVec k p ρ Bj.z)) := by
  subst e
  simp only [sE, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  exact leftFactor_mem Bj x

/- English proof (translation)
Establish `h1 : Continuous (fun x : PBQ.XP k p ρ => (Matrix.of x.1.1 : B.Mat k ρ))` using `continuous_fst.fst`. Establish `h2 : Continuous (fun x : PBQ.XP k p ρ => (Matrix.of x.1.2 : B.Mat k ρ))` using `continuous_fst.snd`. Conclude with `((Formalism.FourierDecayAlt.P.B6.isClosed_UWset k ρ Bj.z).preimage h1).inter ((Formalism.FourierDecayAlt.P.B6.isClosed_Nset k ρ).preimage h2)`.
-/
theorem goodP_closed (Bj : B.RealPlaceData k ρ Wp Wq) : IsClosed {x : PBQ.XP k p ρ | PBQ.GoodP Bj x} := by
  have h1 : Continuous (fun x : PBQ.XP k p ρ => (Matrix.of x.1.1 : B.Mat k ρ)) := continuous_fst.fst
  have h2 : Continuous (fun x : PBQ.XP k p ρ => (Matrix.of x.1.2 : B.Mat k ρ)) := continuous_fst.snd
  exact ((Formalism.FourierDecayAlt.P.B6.isClosed_UWset k ρ Bj.z).preimage h1).inter ((Formalism.FourierDecayAlt.P.B6.isClosed_Nset k ρ).preimage h2)

/- English proof (translation)
Establish `h1 : Continuous (fun x : PBQ.XP k p ρ => U.Rn k p ρ (-x.2))` using `(Formalism.FourierDecayAlt.P.Dx2.SplitF.rn_cont (k := k) p ρ).comp continuous_snd.neg`. Establish `hof1 : Continuous (fun x : PBQ.XP k p ρ => (Matrix.of x.1.1 : B.Mat k ρ))` using `continuous_fst.fst`. Establish `hof2 : Continuous (fun x : PBQ.XP k p ρ => (Matrix.of x.1.2 : B.Mat k ρ))` using `continuous_fst.snd`. Establish `hi1 : ContinuousOn (fun x : PBQ.XP k p ρ => (Matrix.of x.1.1 : B.Mat k ρ)⁻¹) {x | PBQ.GoodP Bj x}` using `Formalism.FourierDecayAlt.P.PBG.inv_cont_GV.comp hof1.continuousOn (fun x hx => hx.1.1)`. Establish `hi2 : ContinuousOn (fun x : PBQ.XP k p ρ => (Matrix.of x.1.2 : B.Mat k ρ)⁻¹) {x | PBQ.GoodP Bj x}` using `Formalism.FourierDecayAlt.P.PBG.inv_cont_GV.comp hof2.continuousOn (fun x hx => hx.2.1)`.

Establish `hf : ContinuousOn (fun x : PBQ.XP k p ρ => U.Rn k p ρ (-x.2) * U.embG k p ρ ((Matrix.of x.1.1 : B.Mat k ρ)⁻¹ * (Matrix.of x.1.2 : B.Mat k ρ)⁻¹)) {x | PBQ.GoodP Bj x}` using `h1.continuousOn.mul ((Formalism.FourierDecayAlt.P.Dx2.SplitF.embg_cont (k := k) p ρ).comp_continuousOn (hi1.mul hi2))`. Use `hf.congr (fun x hx => ?_)` and prove the remaining obligations. Simplify using `only [PBQ.sP, if_pos (show PBQ.GoodP Bj x from hx)]`.
-/
theorem leftFactor_continuousOn (Bj : B.RealPlaceData k ρ Wp Wq) :
    ContinuousOn (fun x : PBQ.XP k p ρ => PBQ.sP Bj x) {x | PBQ.GoodP Bj x} := by
  have h1 : Continuous (fun x : PBQ.XP k p ρ => U.Rn k p ρ (-x.2)) :=
    (Formalism.FourierDecayAlt.P.Dx2.SplitF.rn_cont (k := k) p ρ).comp continuous_snd.neg
  have hof1 : Continuous (fun x : PBQ.XP k p ρ => (Matrix.of x.1.1 : B.Mat k ρ)) := continuous_fst.fst
  have hof2 : Continuous (fun x : PBQ.XP k p ρ => (Matrix.of x.1.2 : B.Mat k ρ)) := continuous_fst.snd
  have hi1 : ContinuousOn (fun x : PBQ.XP k p ρ => (Matrix.of x.1.1 : B.Mat k ρ)⁻¹) {x | PBQ.GoodP Bj x} :=
    Formalism.FourierDecayAlt.P.PBG.inv_cont_GV.comp hof1.continuousOn (fun x hx => hx.1.1)
  have hi2 : ContinuousOn (fun x : PBQ.XP k p ρ => (Matrix.of x.1.2 : B.Mat k ρ)⁻¹) {x | PBQ.GoodP Bj x} :=
    Formalism.FourierDecayAlt.P.PBG.inv_cont_GV.comp hof2.continuousOn (fun x hx => hx.2.1)
  have hf : ContinuousOn (fun x : PBQ.XP k p ρ => U.Rn k p ρ (-x.2) *
      U.embG k p ρ ((Matrix.of x.1.1 : B.Mat k ρ)⁻¹ * (Matrix.of x.1.2 : B.Mat k ρ)⁻¹)) {x | PBQ.GoodP Bj x} :=
    h1.continuousOn.mul ((Formalism.FourierDecayAlt.P.Dx2.SplitF.embg_cont (k := k) p ρ).comp_continuousOn (hi1.mul hi2))
  refine hf.congr (fun x hx => ?_)
  simp only [PBQ.sP, if_pos (show PBQ.GoodP Bj x from hx)]

/- English proof (translation)
Substitute `e` using the available equality. Simplify using `only [sE, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]`. Conclude with `leftFactor_continuousOn Bj`.
-/
theorem sE_contOn (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) :
    ContinuousOn (fun x : PBQ.XP k p ρ => sE Bj e x) {x | PBQ.GoodP Bj x} := by
  subst e
  simp only [sE, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  exact leftFactor_continuousOn Bj

/- English proof (translation)
Unfold `PBQ.cP`. Rewrite using `[norm_mul, Formalism.FourierDecayAlt.P.LeftFubiniLemmas.norm_psi, Formalism.FourierDecayAlt.P.LeftFubiniLemmas.norm_psi, one_mul]`.
-/
theorem norm_cP (Bj : B.RealPlaceData k ρ Wp Wq) (x : PBQ.XP k p ρ) : ‖PBQ.cP Bj x‖ ≤ 1 := by
  unfold PBQ.cP
  rw [norm_mul, Formalism.FourierDecayAlt.P.LeftFubiniLemmas.norm_psi, Formalism.FourierDecayAlt.P.LeftFubiniLemmas.norm_psi, one_mul]

/- English proof (translation)
Unfold `PBQ.cP`. Establish `hof2 : Continuous (fun x : PBQ.XP k p ρ => (Matrix.of x.1.2 : B.Mat k ρ))` using `continuous_fst.snd`. Conclude with `((Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra.psi_cont_of Bj.z cStd).comp hof2).mul ((Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra.psi_cont_of (liftVec k p ρ Bj.z) cStd).comp ((Formalism.FourierDecayAlt.P.Dx2.SplitF.rn_cont (k := k) p ρ).comp continuous_snd))`.
-/
theorem continuous_characterProduct (Bj : B.RealPlaceData k ρ Wp Wq) : Continuous (fun x : PBQ.XP k p ρ => PBQ.cP Bj x) := by
  unfold PBQ.cP
  have hof2 : Continuous (fun x : PBQ.XP k p ρ => (Matrix.of x.1.2 : B.Mat k ρ)) := continuous_fst.snd
  exact ((Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra.psi_cont_of Bj.z cStd).comp hof2).mul
    ((Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra.psi_cont_of (liftVec k p ρ Bj.z) cStd).comp
      ((Formalism.FourierDecayAlt.P.Dx2.SplitF.rn_cont (k := k) p ρ).comp continuous_snd))

/- English proof (translation)
Unfold `gI`. Use `split_ifs with hx`. Use `(ContinuousLinearMap.opNorm_comp_le _ _).trans ?_` and prove the remaining obligations. Use `Formalism.FourierDecayAlt.P.LeftFubiniLemmas.opNorm_pi_le Bj hx.1` as an intermediate fact. Conclude with `(mul_le_of_le_one_left (norm_nonneg _) this)`.

Simplify using the standard rewrite rules.
-/
theorem norm_gI_le (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) (Ψ : B.Mat k n → (Wq →L[ℂ] Wp))
    (x : PBQ.XP k p ρ) (g : B.Mat k n) : ‖gI Bj e Ψ x g‖ ≤ ‖Ψ (sE Bj e x * g)‖ := by
  unfold gI
  split_ifs with hx
  · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have := Formalism.FourierDecayAlt.P.LeftFubiniLemmas.opNorm_pi_le Bj hx.1
    exact (mul_le_of_le_one_left (norm_nonneg _) this)
  · simp

/- English proof (translation)
Establish `: BorelSpace (U.RC k p ρ)` using `Prod.borelSpace`. Establish `: BorelSpace (Mt k ρ × Mt k ρ)` using `Prod.borelSpace`. Conclude with `Prod.borelSpace`.
-/
theorem xp_borel : BorelSpace (PBQ.XP k p ρ) := by
  have : BorelSpace (U.RC k p ρ) := Prod.borelSpace
  have : BorelSpace (Mt k ρ × Mt k ρ) := Prod.borelSpace
  exact Prod.borelSpace

/- English proof (translation)
Use `xp_borel (k := k) (p := p) (ρ := ρ)` as an intermediate fact. Use `set S := {x : PBQ.XP k p ρ | PBQ.GoodP Bj x} with hSdef`. Establish `hπ : ContinuousOn (fun x : PBQ.XP k p ρ => Bj.π (Matrix.of x.1.1)) S` using `Bj.π_cont.comp (continuous_fst.fst : Continuous fun x : PBQ.XP k p ρ => (Matrix.of x.1.1 : B.Mat k ρ)).continuousOn (fun x hx => hx.1)`. Establish `hs : ContinuousOn (fun x => sE Bj e x * g) S` using `(sE_contOn Bj e).mul continuousOn_const`. Establish `hΨ' : ContinuousOn (fun x => Ψ (sE Bj e x * g)) S` using `hΨ.comp hs (fun x _ => Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (sE_GV Bj e x) hg)`.

Establish `hcont : ContinuousOn (fun x => (Bj.π (Matrix.of x.1.1)).comp (Ψ (sE Bj e x * g))) S` using `hπ.clm_comp hΨ'`. Establish `hm` using `hcont.aestronglyMeasurable (μ := PBQ.muXP Bj) (goodP_closed Bj).measurableSet`. Rewrite `hm` using `[Measure.restrict_eq_self_of_ae_mem (s := S) (PBQ.ae_goodP (p := p) Bj)]`. Use `hm.congr ?_` and prove the remaining obligations. Use `filter_upwards [PBQ.ae_goodP (p := p) Bj] with x hx`.

Simplify using `[gI, hx]`.
-/
theorem gI_aesm (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) {Ψ : B.Mat k n → (Wq →L[ℂ] Wp)}
    (hΨ : ContinuousOn Ψ (B.GV k n)) {g : B.Mat k n} (hg : g ∈ B.GV k n) :
    AEStronglyMeasurable (fun x => gI Bj e Ψ x g) (PBQ.muXP Bj) := by
  have := xp_borel (k := k) (p := p) (ρ := ρ)
  set S := {x : PBQ.XP k p ρ | PBQ.GoodP Bj x} with hSdef
  have hπ : ContinuousOn (fun x : PBQ.XP k p ρ => Bj.π (Matrix.of x.1.1)) S :=
    Bj.π_cont.comp (continuous_fst.fst : Continuous fun x : PBQ.XP k p ρ => (Matrix.of x.1.1 : B.Mat k ρ)).continuousOn
      (fun x hx => hx.1)
  have hs : ContinuousOn (fun x => sE Bj e x * g) S := (sE_contOn Bj e).mul continuousOn_const
  have hΨ' : ContinuousOn (fun x => Ψ (sE Bj e x * g)) S :=
    hΨ.comp hs (fun x _ => Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (sE_GV Bj e x) hg)
  have hcont : ContinuousOn (fun x => (Bj.π (Matrix.of x.1.1)).comp (Ψ (sE Bj e x * g))) S := hπ.clm_comp hΨ'
  have hm := hcont.aestronglyMeasurable (μ := PBQ.muXP Bj) (goodP_closed Bj).measurableSet
  rw [Measure.restrict_eq_self_of_ae_mem (s := S) (PBQ.ae_goodP (p := p) Bj)] at hm
  refine hm.congr ?_
  filter_upwards [PBQ.ae_goodP (p := p) Bj] with x hx
  simp [gI, hx]

end left

section deriv

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

open Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.ChartIntegralLocal Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet

def VanishL (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) (Ψ : B.Mat k n → (Wq →L[ℂ] Wp)) (U : Set (B.Mat k n)) :
    Prop :=
  ∀ y ∈ U, ∃ V : Set (B.Mat k n), IsOpen V ∧ y ∈ V ∧ ∃ K : Set (PBQ.XP k p ρ), IsCompact K ∧
    ∀ g ∈ V, g ∈ B.GV k n → ∀ x, PBQ.GoodP Bj x → x ∉ K → Ψ (sE Bj e x * g) = 0

/- English proof (translation)
Use `Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW` as an intermediate fact. Use `Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN` as an intermediate fact. Use `Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ` as an intermediate fact. Establish `: IsFiniteMeasureOnCompacts Bj.μW` using `⟨fun K hK => Bj.haarW.finite_compact K hK⟩`. Establish `: IsFiniteMeasureOnCompacts Bj.μN` using `⟨fun K hK => Bj.haarN.finite_compact K hK⟩`.

Use `Formalism.FourierDecayAlt.P.LeftFubiniLemmas.fmoc_RC (k := k) (p := p) (ρ := ρ)` as an intermediate fact. Unfold `PBQ.muXP`. Use `infer_instance`.
-/
theorem fmoc_XP (Bj : B.RealPlaceData k ρ Wp Wq) : IsFiniteMeasureOnCompacts (PBQ.muXP (p := p) Bj) := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ
  have : IsFiniteMeasureOnCompacts Bj.μW := ⟨fun K hK => Bj.haarW.finite_compact K hK⟩
  have : IsFiniteMeasureOnCompacts Bj.μN := ⟨fun K hK => Bj.haarN.finite_compact K hK⟩
  have := Formalism.FourierDecayAlt.P.LeftFubiniLemmas.fmoc_RC (k := k) (p := p) (ρ := ρ)
  unfold PBQ.muXP
  infer_instance

/- English proof (translation)
Use `⟨(fun q : PBQ.XP k p ρ × B.Mat k n => sE Bj e q.1 * q.2) '' ((K ∩ {x | PBQ.GoodP Bj x}) ×ˢ Kc), ?_, ?_, ?_⟩` and prove the remaining obligations. Use `((hK.inter_right (goodP_closed Bj)).prod hKc).image_of_continuousOn ?_` and prove the remaining obligations. Conclude with `((sE_contOn Bj e).comp continuous_fst.continuousOn (fun q hq => hq.1.2)).mul continuous_snd.continuousOn`. Introduce and unpack `_ ⟨q, hq, rfl⟩`. Conclude with `Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (sE_GV Bj e q.1) (hKcG hq.2)`.

Introduce `x hx hg g hgK`. Conclude with `⟨(x, g), ⟨⟨hx, hg⟩, hgK⟩, rfl⟩`.
-/
theorem img_cpt (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) {K : Set (PBQ.XP k p ρ)} (hK : IsCompact K)
    {Kc : Set (B.Mat k n)} (hKc : IsCompact Kc) (hKcG : Kc ⊆ B.GV k n) :
    ∃ S : Set (B.Mat k n), IsCompact S ∧ S ⊆ B.GV k n ∧
      ∀ x ∈ K, PBQ.GoodP Bj x → ∀ g ∈ Kc, sE Bj e x * g ∈ S := by
  refine ⟨(fun q : PBQ.XP k p ρ × B.Mat k n => sE Bj e q.1 * q.2) '' ((K ∩ {x | PBQ.GoodP Bj x}) ×ˢ Kc), ?_, ?_, ?_⟩
  · refine ((hK.inter_right (goodP_closed Bj)).prod hKc).image_of_continuousOn ?_
    exact ((sE_contOn Bj e).comp continuous_fst.continuousOn (fun q hq => hq.1.2)).mul continuous_snd.continuousOn
  · rintro _ ⟨q, hq, rfl⟩
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (sE_GV Bj e q.1) (hKcG hq.2)
  · intro x hx hg g hgK
    exact ⟨(x, g), ⟨⟨hx, hg⟩, hgK⟩, rfl⟩

/- English proof (translation)
Unfold `RdV`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem rdV_transl {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (Ψ : B.Mat k n → E) (s g X : B.Mat k n) :
    RdV X (fun g' => Ψ (s * g')) g = RdV X Ψ (s * g) := by
  unfold RdV
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Rewrite using `[← rdV_transl, Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.rdV_congr (f₂ := fun _ => (0 : E)) hV hg hgG hX (fun x hx hxG => h x hx hxG)]`. Simplify using `[RdV]`.
-/
theorem rdV_zero_of_vanish {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {Ψ : B.Mat k n → E}
    {s : B.Mat k n} {V : Set (B.Mat k n)} (hV : IsOpen V) (h : ∀ g ∈ V, g ∈ B.GV k n → Ψ (s * g) = 0)
    {g : B.Mat k n} (hg : g ∈ V) (hgG : g ∈ B.GV k n) {X : B.Mat k n} (hX : inLie k n X) : RdV X Ψ (s * g) = 0 := by
  rw [← rdV_transl, Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.rdV_congr (f₂ := fun _ => (0 : E)) hV hg hgG hX (fun x hx hxG => h x hx hxG)]
  simp [RdV]

/- English proof (translation)
Distinguish the cases in `hx : PBQ.GoodP Bj x`. Establish `e1 : gI Bj e Ψ x = fun g => (ContinuousLinearMap.compL ℂ Wq Wp Wp (Bj.π (Matrix.of x.1.1))) (Ψ (sE Bj e x * g * 1))`. Use function extensionality and compare the values at `g`. Simplify using `[gI, hx]`. Rewrite using `[e1]`.

Conclude with `Formalism.FourierDecayAlt.P.B5.ckOn_clm (Formalism.FourierDecayAlt.P.B5.ckOn_translate hΨ (sE_GV Bj e x) Formalism.QuantumDeterminants.WeylGroupFacts.uh_one) _`. Establish `e1 : gI Bj e Ψ x = fun _ => 0` using `by funext g; simp [gI, hx]`. Rewrite using `[e1]`. Conclude with `Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.ckOn_zero _`.
-/
theorem ckOn_gI (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) {m : ℕ∞} {Ψ : B.Mat k n → (Wq →L[ℂ] Wp)}
    (hΨ : CkOn m (GV k n) Ψ) (x : PBQ.XP k p ρ) : CkOn m (GV k n) (gI Bj e Ψ x) := by
  by_cases hx : PBQ.GoodP Bj x
  · have e1 : gI Bj e Ψ x = fun g =>
        (ContinuousLinearMap.compL ℂ Wq Wp Wp (Bj.π (Matrix.of x.1.1))) (Ψ (sE Bj e x * g * 1)) := by
      funext g; simp [gI, hx]
    rw [e1]
    exact Formalism.FourierDecayAlt.P.B5.ckOn_clm (Formalism.FourierDecayAlt.P.B5.ckOn_translate hΨ (sE_GV Bj e x) Formalism.QuantumDeterminants.WeylGroupFacts.uh_one) _
  · have e1 : gI Bj e Ψ x = fun _ => 0 := by funext g; simp [gI, hx]
    rw [e1]; exact Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.ckOn_zero _

/- English proof (translation)
Distinguish the cases in `hx : PBQ.GoodP Bj x`. Use `set L := ContinuousLinearMap.compL ℂ Wq Wp Wp (Bj.π (Matrix.of x.1.1)) with hL`. Establish `e1 : gI Bj e Ψ x = fun g' => L (Ψ (sE Bj e x * g'))`. Use function extensionality and compare the values at `g'`. Simplify using `[gI, hx, hL]`.

Rewrite using `[e1]`. Establish `e2 : gI Bj e (RdV X Ψ) x g = L (RdV X Ψ (sE Bj e x * g))` using `by simp [gI, hx, hL]`. Rewrite using `[e2]`. Establish `hc` using `Formalism.FourierDecayAlt.P.B5.ckOn_curve hΨ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (sE_GV Bj e x) hg) hX`. Establish `hd` using `(hc.differentiable one_ne_zero 0).hasDerivAt`.

Establish `e3 : (fun t : ℝ => L (Ψ (sE Bj e x * cv false X t g))) = fun t : ℝ => L (Ψ (sE Bj e x * g * NormedSpace.exp ((t : ℂ) • X)))`. Use function extensionality and compare the values at `t`. Simplify using `only [cv, Matrix.mul_assoc]`. Use `show deriv (fun t : ℝ => L (Ψ (sE Bj e x * cv false X t g))) 0 = _`. Rewrite using `[e3]`.

Establish `h5` using `(L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd`. Conclude with `h5.deriv`. Establish `e1 : gI Bj e Ψ x = fun _ => 0` using `by funext g; simp [gI, hx]`. Rewrite using `[e1]`. Simplify using `[op, gI, hx]`.
-/
theorem op_gI (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) {Ψ : B.Mat k n → (Wq →L[ℂ] Wp)}
    (hΨ : CkOn 1 (GV k n) Ψ) {X : B.Mat k n} (hX : inLie k n X) (x : PBQ.XP k p ρ) {g : B.Mat k n}
    (hg : g ∈ GV k n) : op false X (gI Bj e Ψ x) g = gI Bj e (RdV X Ψ) x g := by
  by_cases hx : PBQ.GoodP Bj x
  · set L := ContinuousLinearMap.compL ℂ Wq Wp Wp (Bj.π (Matrix.of x.1.1)) with hL
    have e1 : gI Bj e Ψ x = fun g' => L (Ψ (sE Bj e x * g')) := by
      funext g'; simp [gI, hx, hL]
    rw [e1]
    have e2 : gI Bj e (RdV X Ψ) x g = L (RdV X Ψ (sE Bj e x * g)) := by simp [gI, hx, hL]
    rw [e2]
    have hc := Formalism.FourierDecayAlt.P.B5.ckOn_curve hΨ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (sE_GV Bj e x) hg) hX
    have hd := (hc.differentiable one_ne_zero 0).hasDerivAt
    have e3 : (fun t : ℝ => L (Ψ (sE Bj e x * cv false X t g))) =
        fun t : ℝ => L (Ψ (sE Bj e x * g * NormedSpace.exp ((t : ℂ) • X))) := by
      funext t; simp only [cv, Matrix.mul_assoc]
    show deriv (fun t : ℝ => L (Ψ (sE Bj e x * cv false X t g))) 0 = _
    rw [e3]
    have h5 := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    exact h5.deriv
  · have e1 : gI Bj e Ψ x = fun _ => 0 := by funext g; simp [gI, hx]
    rw [e1]
    simp [op, gI, hx]

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Use `fmoc_XP (p := p) Bj` as an intermediate fact. Use `xp_borel (k := k) (p := p) (ρ := ρ)` as an intermediate fact. Establish `: CompleteSpace Wp` using `FiniteDimensional.complete ℂ Wp`. Take `⟨V, hVo, hyV, K, hK, hvan⟩` from `hv y hyU`. Establish `hΨ1 : CkOn 1 (GV k n) Ψ` using `Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hΨ`.

Establish `hΨc : ContinuousOn Ψ (GV k n)` using `Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn hΨ`. Establish `hRΨ : CkOn ⊤ (GV k n) (RdV X Ψ)` using `Formalism.FourierDecayAlt.P.B5.ckOn_RdV hX (by simpa using hΨ)`. Establish `hRc : ContinuousOn (RdV X Ψ) (GV k n)` using `Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn hRΨ`. Choose the witnesses or unpack the hypotheses as in `⟨ε, hε, hball⟩ : ∃ ε > 0, ∀ t ∈ Metric.ball (0 : ℝ) ε, cv false X t y ∈ V := by`. Establish `ho : IsOpen ((fun t : ℝ => cv false X t y) ⁻¹' V)` using `hVo.preimage (cv_continuous false X y)`.

Establish `h0 : (0 : ℝ) ∈ (fun t : ℝ => cv false X t y) ⁻¹' V` using `by show cv false X 0 y ∈ V; rw [cv_zero]; exact hyV`. Take `⟨ε, hε, hb⟩` from `Metric.isOpen_iff.1 ho 0 h0`. Conclude with `⟨ε, hε, fun t ht => hb ht⟩`. Use `set Kc := (fun t : ℝ => cv false X t y) '' Metric.closedBall (0 : ℝ) (ε / 2) with hKcdef`. Establish `hKc : IsCompact Kc` using `(isCompact_closedBall _ _).image (cv_continuous false X y)`.

Establish `hKcG : Kc ⊆ GV k n` using `by rintro _ ⟨t, _, rfl⟩; exact cv_mem hX hy t`. Take `⟨S, hS, hSG, hSmem⟩` from `img_cpt Bj e hK hKc hKcG`. Take `⟨M1, hM1⟩` from `hS.exists_bound_of_continuousOn (hΨc.mono hSG)`. Take `⟨M2, hM2⟩` from `hS.exists_bound_of_continuousOn (hRc.mono hSG)`. Use `set M := max (max M1 M2) 0 with hMdef`.

Use `set β : PBQ.XP k p ρ → ℝ := K.indicator (fun _ => M) with hβdef`. Establish `hβI : Integrable β (PBQ.muXP Bj)` using `(integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne)`. Establish `hε2 : (0 : ℝ) < ε / 2` using `by positivity`. Establish `hmemKc : ∀ t ∈ Metric.ball (0 : ℝ) (ε / 2), cv false X t y ∈ Kc` using `fun t ht => ⟨t, Metric.ball_subset_closedBall ht, rfl⟩`. Establish `hinV : ∀ t ∈ Metric.ball (0 : ℝ) (ε / 2), cv false X t y ∈ V` using `fun t ht => hball t (Metric.ball_subset_ball (by linarith) ht)`.

Establish `hb1 : ∀ t ∈ Metric.ball (0 : ℝ) (ε / 2), ∀ x, ‖op false X (gI Bj e Ψ x) (cv false X t y)‖ ≤ β x`. Introduce `t ht x`. Rewrite using `[op_gI Bj e hΨ1 hX x (cv_mem hX hy t)]`. Distinguish the cases in `hxK : x ∈ K`. Rewrite using `[hβdef, Set.indicator_of_mem hxK]`.

Distinguish the cases in `hx : PBQ.GoodP Bj x`. Conclude with `(norm_gI_le Bj e _ x _).trans ((hM2 _ (hSmem x hxK hx _ (hmemKc t ht))).trans (le_trans (le_max_right _ _) (le_max_left _ _)))`. Simplify using `only [gI, if_neg hx, norm_zero]`. Conclude with `le_max_right _ _`. Rewrite using `[hβdef, Set.indicator_of_notMem hxK]`.

Distinguish the cases in `hx : PBQ.GoodP Bj x`. Establish `hz : RdV X Ψ (sE Bj e x * cv false X t y) = 0` using `rdV_zero_of_vanish hVo (fun g hg hgG => hvan g hg hgG x hx hxK) (hinV t ht) (cv_mem hX hy t) hX`. Simplify using `[gI, hx, hz]`. Simplify using `[gI, hx]`. Establish `hb0 : ∀ x, ‖gI Bj e Ψ x (cv false X 0 y)‖ ≤ β x`.

Introduce `x`. Rewrite using `[cv_zero]`. Distinguish the cases in `hxK : x ∈ K`. Rewrite using `[hβdef, Set.indicator_of_mem hxK]`. Distinguish the cases in `hx : PBQ.GoodP Bj x`.

Establish `hyKc : y ∈ Kc`. Use `hmemKc 0 (Metric.mem_ball_self hε2)` as an intermediate fact. Rewrite `this` using `[cv_zero]`. Then use the resulting hypothesis. Conclude with `(norm_gI_le Bj e Ψ x y).trans ((hM1 _ (hSmem x hxK hx y hyKc)).trans (le_trans (le_max_left _ _) (le_max_left _ _)))`. Simplify using `only [gI, if_neg hx, norm_zero]`.

Conclude with `le_max_right _ _`. Rewrite using `[hβdef, Set.indicator_of_notMem hxK]`. Distinguish the cases in `hx : PBQ.GoodP Bj x`. Simplify using `[gI, hx, hvan y hyV hy x hx hxK]`. Simplify using `[gI, hx]`.

Establish `key` using `step_loc (μ := PBQ.muXP Bj) (b := false) hX (fun x => PBQ.cP Bj x) (norm_cP Bj) (continuous_characterProduct Bj).aestronglyMeasurable (gI Bj e Ψ) (fun x => ckOn_gI Bj e hΨ1 x) hy hε2 (fun t _ => gI_aesm Bj e hΨc (cv_mem hX hy t)) ((gI_aesm Bj e hRc hy).congr (Eventually.of_forall …`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `hβI.mono' ((continuous_characterProduct Bj).aestronglyMeasurable.smul (gI_aesm Bj e hRc hy)) (Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Rewrite using `[norm_smul]`. Use `(mul_le_of_le_one_left (norm_nonneg _) (norm_cP Bj x)).trans ?_` and prove the remaining obligations.

Use `hb1 0 (Metric.mem_ball_self hε2) x` as an intermediate fact. Rewrite `this` using `[cv_zero, op_gI Bj e hΨ1 hX x hy]`. Then use the resulting hypothesis. Use `show op false X (TI Bj e Ψ) y = _`. Rewrite using `[key]`. Unfold `TI`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Rewrite using `[op_gI Bj e hΨ1 hX x hy]`.
-/
theorem rdV_TI (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) {Ψ : B.Mat k n → (Wq →L[ℂ] Wp)}
    (hΨ : CkOn ⊤ (GV k n) Ψ) {U : Set (B.Mat k n)} (hv : VanishL Bj e Ψ U) {X : B.Mat k n} (hX : inLie k n X)
    {y : B.Mat k n} (hyU : y ∈ U) (hy : y ∈ GV k n) :
    Integrable (fun x => PBQ.cP Bj x • gI Bj e (RdV X Ψ) x y) (PBQ.muXP Bj) ∧
      RdV X (TI Bj e Ψ) y = TI Bj e (RdV X Ψ) y := by
  have := fmoc_XP (p := p) Bj
  have := xp_borel (k := k) (p := p) (ρ := ρ)
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  obtain ⟨V, hVo, hyV, K, hK, hvan⟩ := hv y hyU
  have hΨ1 : CkOn 1 (GV k n) Ψ := Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hΨ
  have hΨc : ContinuousOn Ψ (GV k n) := Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn hΨ
  have hRΨ : CkOn ⊤ (GV k n) (RdV X Ψ) := Formalism.FourierDecayAlt.P.B5.ckOn_RdV hX (by simpa using hΨ)
  have hRc : ContinuousOn (RdV X Ψ) (GV k n) := Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn hRΨ
  obtain ⟨ε, hε, hball⟩ : ∃ ε > 0, ∀ t ∈ Metric.ball (0 : ℝ) ε, cv false X t y ∈ V := by
    have ho : IsOpen ((fun t : ℝ => cv false X t y) ⁻¹' V) := hVo.preimage (cv_continuous false X y)
    have h0 : (0 : ℝ) ∈ (fun t : ℝ => cv false X t y) ⁻¹' V := by
      show cv false X 0 y ∈ V; rw [cv_zero]; exact hyV
    obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.1 ho 0 h0
    exact ⟨ε, hε, fun t ht => hb ht⟩
  set Kc := (fun t : ℝ => cv false X t y) '' Metric.closedBall (0 : ℝ) (ε / 2) with hKcdef
  have hKc : IsCompact Kc := (isCompact_closedBall _ _).image (cv_continuous false X y)
  have hKcG : Kc ⊆ GV k n := by rintro _ ⟨t, _, rfl⟩; exact cv_mem hX hy t
  obtain ⟨S, hS, hSG, hSmem⟩ := img_cpt Bj e hK hKc hKcG
  obtain ⟨M1, hM1⟩ := hS.exists_bound_of_continuousOn (hΨc.mono hSG)
  obtain ⟨M2, hM2⟩ := hS.exists_bound_of_continuousOn (hRc.mono hSG)
  set M := max (max M1 M2) 0 with hMdef
  set β : PBQ.XP k p ρ → ℝ := K.indicator (fun _ => M) with hβdef
  have hβI : Integrable β (PBQ.muXP Bj) :=
    (integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne)
  have hε2 : (0 : ℝ) < ε / 2 := by positivity
  have hmemKc : ∀ t ∈ Metric.ball (0 : ℝ) (ε / 2), cv false X t y ∈ Kc :=
    fun t ht => ⟨t, Metric.ball_subset_closedBall ht, rfl⟩
  have hinV : ∀ t ∈ Metric.ball (0 : ℝ) (ε / 2), cv false X t y ∈ V :=
    fun t ht => hball t (Metric.ball_subset_ball (by linarith) ht)
  have hb1 : ∀ t ∈ Metric.ball (0 : ℝ) (ε / 2), ∀ x,
      ‖op false X (gI Bj e Ψ x) (cv false X t y)‖ ≤ β x := by
    intro t ht x
    rw [op_gI Bj e hΨ1 hX x (cv_mem hX hy t)]
    by_cases hxK : x ∈ K
    · rw [hβdef, Set.indicator_of_mem hxK]
      by_cases hx : PBQ.GoodP Bj x
      · exact (norm_gI_le Bj e _ x _).trans ((hM2 _ (hSmem x hxK hx _ (hmemKc t ht))).trans
          (le_trans (le_max_right _ _) (le_max_left _ _)))
      · simp only [gI, if_neg hx, norm_zero]; exact le_max_right _ _
    · rw [hβdef, Set.indicator_of_notMem hxK]
      by_cases hx : PBQ.GoodP Bj x
      · have hz : RdV X Ψ (sE Bj e x * cv false X t y) = 0 :=
          rdV_zero_of_vanish hVo (fun g hg hgG => hvan g hg hgG x hx hxK) (hinV t ht) (cv_mem hX hy t) hX
        simp [gI, hx, hz]
      · simp [gI, hx]
  have hb0 : ∀ x, ‖gI Bj e Ψ x (cv false X 0 y)‖ ≤ β x := by
    intro x
    rw [cv_zero]
    by_cases hxK : x ∈ K
    · rw [hβdef, Set.indicator_of_mem hxK]
      by_cases hx : PBQ.GoodP Bj x
      · have hyKc : y ∈ Kc := by
          have := hmemKc 0 (Metric.mem_ball_self hε2); rwa [cv_zero] at this
        exact (norm_gI_le Bj e Ψ x y).trans ((hM1 _ (hSmem x hxK hx y hyKc)).trans
          (le_trans (le_max_left _ _) (le_max_left _ _)))
      · simp only [gI, if_neg hx, norm_zero]; exact le_max_right _ _
    · rw [hβdef, Set.indicator_of_notMem hxK]
      by_cases hx : PBQ.GoodP Bj x
      · simp [gI, hx, hvan y hyV hy x hx hxK]
      · simp [gI, hx]
  have key := step_loc (μ := PBQ.muXP Bj) (b := false) hX (fun x => PBQ.cP Bj x) (norm_cP Bj)
    (continuous_characterProduct Bj).aestronglyMeasurable (gI Bj e Ψ) (fun x => ckOn_gI Bj e hΨ1 x) hy hε2
    (fun t _ => gI_aesm Bj e hΨc (cv_mem hX hy t))
    ((gI_aesm Bj e hRc hy).congr (Eventually.of_forall fun x => (op_gI Bj e hΨ1 hX x hy).symm))
    β hβI (fun x => by have := hb0 x; rwa [cv_zero] at this) hb1 (TI Bj e Ψ) (fun t _ => rfl)
  refine ⟨?_, ?_⟩
  · refine hβI.mono' ((continuous_characterProduct Bj).aestronglyMeasurable.smul (gI_aesm Bj e hRc hy))
      (Eventually.of_forall fun x => ?_)
    rw [norm_smul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (norm_cP Bj x)).trans ?_
    have := hb1 0 (Metric.mem_ball_self hε2) x
    rwa [cv_zero, op_gI Bj e hΨ1 hX x hy] at this
  · show op false X (TI Bj e Ψ) y = _
    rw [key]
    unfold TI
    congr 1
    funext x
    rw [op_gI Bj e hΨ1 hX x hy]

end deriv

section fold

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

open Formalism.FourierDecayAlt.P.CapelliWordSumExpansion

/- English proof (translation)
Distinguish the cases in `hx : PBQ.GoodP Bj x`. Apply the tactic sequence `simp only [gI, if_pos hx, top_apply', EH_apply] split_ifs <;> simp [ContinuousLinearMap.comp_add]`. Simplify using `[gI, hx]`.
-/
theorem gI_top (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) (Ψ : B.Mat k n → (Wq →L[ℂ] Wp)) (u : ℂ)
    (a b : Fin (2 * n + k + 1)) (x : PBQ.XP k p ρ) (g : B.Mat k n) :
    gI Bj e (Top (Q.EH k n) u a b Ψ) x g =
      (if a = b then u • gI Bj e Ψ x g else 0) +
        (gI Bj e (RdV (Xa k n a b) Ψ) x g + Complex.I • gI Bj e (RdV (Xb k n a b) Ψ) x g) := by
  by_cases hx : PBQ.GoodP Bj x
  · simp only [gI, if_pos hx, top_apply', EH_apply]
    split_ifs <;> simp [ContinuousLinearMap.comp_add]
  · simp [gI, hx]

/- English proof (translation)
Introduce `y hy`. Take `⟨V, hV, hyV, K, hK, h⟩` from `hv y hy`. Use `⟨V, hV, hyV, K, hK, fun g hg hgG x hx hxK => ?_⟩` and prove the remaining obligations. Establish `h0 : ∀ g' ∈ V, g' ∈ GV k n → Ψ (sE Bj e x * g') = 0` using `fun g' a b => h g' a b x hx hxK`. Rewrite using `[top_apply', EH_apply, h g hg hgG x hx hxK, rdV_zero_of_vanish hV h0 hg hgG (Xa_unit a b).1, rdV_zero_of_vanish hV h0 hg hgG (Xb_unit a b).1]`.

Simplify using the standard rewrite rules.
-/
theorem vanish_top (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) {Ψ : B.Mat k n → (Wq →L[ℂ] Wp)}
    {U : Set (B.Mat k n)} (hv : VanishL Bj e Ψ U) (u : ℂ) (a b : Fin (2 * n + k + 1)) :
    VanishL Bj e (Top (Q.EH k n) u a b Ψ) U := by
  intro y hy
  obtain ⟨V, hV, hyV, K, hK, h⟩ := hv y hy
  refine ⟨V, hV, hyV, K, hK, fun g hg hgG x hx hxK => ?_⟩
  have h0 : ∀ g' ∈ V, g' ∈ GV k n → Ψ (sE Bj e x * g') = 0 := fun g' a b => h g' a b x hx hxK
  rw [top_apply', EH_apply, h g hg hgG x hx hxK, rdV_zero_of_vanish hV h0 hg hgG (Xa_unit a b).1,
    rdV_zero_of_vanish hV h0 hg hgG (Xb_unit a b).1]
  simp

/- English proof (translation)
Establish `hA : CkOn ⊤ (GV k n) (RdV (Xa k n a b) Ψ)` using `Formalism.FourierDecayAlt.P.B5.ckOn_RdV (Xa_unit a b).1 (by simpa using hΨ)`. Establish `hB : CkOn ⊤ (GV k n) (RdV (Xb k n a b) Ψ)` using `Formalism.FourierDecayAlt.P.B5.ckOn_RdV (Xb_unit a b).1 (by simpa using hΨ)`. Distinguish the cases in `hab : a = b`. Establish `e1 : Top (Q.EH k n) u a b Ψ = u • Ψ + (RdV (Xa k n a b) Ψ + Complex.I • RdV (Xb k n a b) Ψ)`. Use function extensionality and compare the values at `g`.

Rewrite using `[top_apply', EH_apply, if_pos hab]`. Both sides reduce to the same expression. Rewrite using `[e1]`. Conclude with `Formalism.FourierDecayAlt.P.JCx2.ckOn_add' (Formalism.FourierDecayAlt.P.JCx2.ckOn_smul' _ hΨ) (Formalism.FourierDecayAlt.P.JCx2.ckOn_add' hA (Formalism.FourierDecayAlt.P.JCx2.ckOn_smul' _ hB))`. Establish `e1 : Top (Q.EH k n) u a b Ψ = RdV (Xa k n a b) Ψ + Complex.I • RdV (Xb k n a b) Ψ`.

Use function extensionality and compare the values at `g`. Rewrite using `[top_apply', EH_apply, if_neg hab, zero_add]`. Both sides reduce to the same expression. Rewrite using `[e1]`. Conclude with `Formalism.FourierDecayAlt.P.JCx2.ckOn_add' hA (Formalism.FourierDecayAlt.P.JCx2.ckOn_smul' _ hB)`.
-/
theorem ckOn_top {Ψ : B.Mat k n → (Wq →L[ℂ] Wp)} (hΨ : CkOn ⊤ (GV k n) Ψ) (u : ℂ) (a b : Fin (2 * n + k + 1)) :
    CkOn ⊤ (GV k n) (Top (Q.EH k n) u a b Ψ) := by
  have hA : CkOn ⊤ (GV k n) (RdV (Xa k n a b) Ψ) := Formalism.FourierDecayAlt.P.B5.ckOn_RdV (Xa_unit a b).1 (by simpa using hΨ)
  have hB : CkOn ⊤ (GV k n) (RdV (Xb k n a b) Ψ) := Formalism.FourierDecayAlt.P.B5.ckOn_RdV (Xb_unit a b).1 (by simpa using hΨ)
  by_cases hab : a = b
  · have e1 : Top (Q.EH k n) u a b Ψ = u • Ψ + (RdV (Xa k n a b) Ψ + Complex.I • RdV (Xb k n a b) Ψ) := by
      funext g; rw [top_apply', EH_apply, if_pos hab]; rfl
    rw [e1]
    exact Formalism.FourierDecayAlt.P.JCx2.ckOn_add' (Formalism.FourierDecayAlt.P.JCx2.ckOn_smul' _ hΨ)
      (Formalism.FourierDecayAlt.P.JCx2.ckOn_add' hA (Formalism.FourierDecayAlt.P.JCx2.ckOn_smul' _ hB))
  · have e1 : Top (Q.EH k n) u a b Ψ = RdV (Xa k n a b) Ψ + Complex.I • RdV (Xb k n a b) Ψ := by
      funext g; rw [top_apply', EH_apply, if_neg hab, zero_add]; rfl
    rw [e1]
    exact Formalism.FourierDecayAlt.P.JCx2.ckOn_add' hA (Formalism.FourierDecayAlt.P.JCx2.ckOn_smul' _ hB)

/- English proof (translation)
Establish `hB' : Integrable (fun x => Complex.I • fB x) μ` using `hB.smul Complex.I`. Establish `hAB : Integrable (fun x => fA x + Complex.I • fB x) μ` using `hA.add hB'`. Use `split_ifs`. Establish `h0' : Integrable (fun x => u • f0 x) μ` using `h0.smul u`. Rewrite using `[integral_add h0' hAB, integral_add hA hB', integral_smul, integral_smul]`.

Simplify using `only [zero_add]`. Rewrite using `[integral_add hA hB', integral_smul]`.
-/
theorem int_lin {α : Type*} [MeasurableSpace α] {μ : Measure α} {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [CompleteSpace V] (P : Prop) [Decidable P] (u : ℂ) {f0 fA fB : α → V}
    (h0 : Integrable f0 μ) (hA : Integrable fA μ) (hB : Integrable fB μ) :
    ∫ x, ((if P then u • f0 x else 0) + (fA x + Complex.I • fB x)) ∂μ =
      (if P then u • ∫ x, f0 x ∂μ else 0) + (∫ x, fA x ∂μ + Complex.I • ∫ x, fB x ∂μ) := by
  have hB' : Integrable (fun x => Complex.I • fB x) μ := hB.smul Complex.I
  have hAB : Integrable (fun x => fA x + Complex.I • fB x) μ := hA.add hB'
  split_ifs
  · have h0' : Integrable (fun x => u • f0 x) μ := h0.smul u
    rw [integral_add h0' hAB, integral_add hA hB', integral_smul, integral_smul]
  · simp only [zero_add]
    rw [integral_add hA hB', integral_smul]

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Use `fmoc_XP (p := p) Bj` as an intermediate fact. Use `xp_borel (k := k) (p := p) (ρ := ρ)` as an intermediate fact. Take `⟨V, hVo, hyV, K, hK, hvan⟩` from `hv y hyU`. Take `⟨S, hS, hSG, hSmem⟩` from `img_cpt Bj e hK (isCompact_singleton (x := y)) (Set.singleton_subset_iff.2 hy)`. Take `⟨M1, hM1⟩` from `hS.exists_bound_of_continuousOn (hΨc.mono hSG)`.

Establish `hβI : Integrable (K.indicator (fun _ => max M1 0)) (PBQ.muXP Bj)` using `(integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne)`. Use `hβI.mono' ((continuous_characterProduct Bj).aestronglyMeasurable.smul (gI_aesm Bj e hΨc hy)) (Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Rewrite using `[norm_smul]`. Use `(mul_le_of_le_one_left (norm_nonneg _) (norm_cP Bj x)).trans ?_` and prove the remaining obligations. Distinguish the cases in `hxK : x ∈ K`.

Rewrite using `[Set.indicator_of_mem hxK]`. Distinguish the cases in `hx : PBQ.GoodP Bj x`. Conclude with `(norm_gI_le Bj e Ψ x y).trans ((hM1 _ (hSmem x hxK hx y (Set.mem_singleton y))).trans (le_max_left _ _))`. Simplify using `only [gI, if_neg hx, norm_zero]`. Conclude with `le_max_right _ _`.

Rewrite using `[Set.indicator_of_notMem hxK]`. Distinguish the cases in `hx : PBQ.GoodP Bj x`. Simplify using `[gI, hx, hvan y hyV hy x hx hxK]`. Simplify using `[gI, hx]`.
-/
theorem int_gI (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) {Ψ : B.Mat k n → (Wq →L[ℂ] Wp)}
    (hΨc : ContinuousOn Ψ (GV k n)) {U : Set (B.Mat k n)} (hv : VanishL Bj e Ψ U) {y : B.Mat k n}
    (hyU : y ∈ U) (hy : y ∈ GV k n) : Integrable (fun x => PBQ.cP Bj x • gI Bj e Ψ x y) (PBQ.muXP Bj) := by
  have := fmoc_XP (p := p) Bj
  have := xp_borel (k := k) (p := p) (ρ := ρ)
  obtain ⟨V, hVo, hyV, K, hK, hvan⟩ := hv y hyU
  obtain ⟨S, hS, hSG, hSmem⟩ := img_cpt Bj e hK (isCompact_singleton (x := y)) (Set.singleton_subset_iff.2 hy)
  obtain ⟨M1, hM1⟩ := hS.exists_bound_of_continuousOn (hΨc.mono hSG)
  have hβI : Integrable (K.indicator (fun _ => max M1 0)) (PBQ.muXP Bj) :=
    (integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne)
  refine hβI.mono' ((continuous_characterProduct Bj).aestronglyMeasurable.smul (gI_aesm Bj e hΨc hy)) (Eventually.of_forall fun x => ?_)
  rw [norm_smul]
  refine (mul_le_of_le_one_left (norm_nonneg _) (norm_cP Bj x)).trans ?_
  by_cases hxK : x ∈ K
  · rw [Set.indicator_of_mem hxK]
    by_cases hx : PBQ.GoodP Bj x
    · exact (norm_gI_le Bj e Ψ x y).trans ((hM1 _ (hSmem x hxK hx y (Set.mem_singleton y))).trans (le_max_left _ _))
    · simp only [gI, if_neg hx, norm_zero]; exact le_max_right _ _
  · rw [Set.indicator_of_notMem hxK]
    by_cases hx : PBQ.GoodP Bj x
    · simp [gI, hx, hvan y hyV hy x hx hxK]
    · simp [gI, hx]

/- English proof (translation)
The claim follows from `| [] => ⟨hΨ, hv, fun _ _ _ => rfl⟩ | t :: ts => by have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp obtain ⟨hc, hvv, ih⟩ := foldT_TI Bj e hΨ hU hv ts have e0 : ∀ f : B.Mat k n → (Wq →L[ℂ] Wp), foldT (t :: ts) f = Top (Q.EH k n) t.1 t.2.1 t.2.2 (foldT ts f) := fun f => r …`.
-/
theorem foldT_TI (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) {Ψ : B.Mat k n → (Wq →L[ℂ] Wp)}
    (hΨ : CkOn ⊤ (GV k n) Ψ) {U : Set (B.Mat k n)} (hU : IsOpen U) (hv : VanishL Bj e Ψ U) :
    ∀ ts : List (ℂ × Fin (2 * n + k + 1) × Fin (2 * n + k + 1)),
      CkOn ⊤ (GV k n) (foldT ts Ψ) ∧ VanishL Bj e (foldT ts Ψ) U ∧
        ∀ y ∈ U, y ∈ GV k n → foldT ts (TI Bj e Ψ) y = TI Bj e (foldT ts Ψ) y
  | [] => ⟨hΨ, hv, fun _ _ _ => rfl⟩
  | t :: ts => by
    have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
    obtain ⟨hc, hvv, ih⟩ := foldT_TI Bj e hΨ hU hv ts
    have e0 : ∀ f : B.Mat k n → (Wq →L[ℂ] Wp), foldT (t :: ts) f = Top (Q.EH k n) t.1 t.2.1 t.2.2 (foldT ts f) :=
      fun f => rfl
    refine ⟨by rw [e0]; exact ckOn_top hc _ _ _, by rw [e0]; exact vanish_top Bj e hvv _ _ _, fun y hyU hy => ?_⟩
    have hA := rdV_TI Bj e hc hvv (Xa_unit t.2.1 t.2.2).1 hyU hy
    have hB := rdV_TI Bj e hc hvv (Xb_unit t.2.1 t.2.2).1 hyU hy
    have hI0 := int_gI Bj e (Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn hc) hvv hyU hy
    have hL : foldT (t :: ts) (TI Bj e Ψ) y = (if t.2.1 = t.2.2 then t.1 • TI Bj e (foldT ts Ψ) y else 0) +
        (TI Bj e (RdV (Xa k n t.2.1 t.2.2) (foldT ts Ψ)) y +
          Complex.I • TI Bj e (RdV (Xb k n t.2.1 t.2.2) (foldT ts Ψ)) y) := by
      rw [e0, top_apply', EH_apply,
        rdV_congr hU hyU hy (Xa_unit _ _).1 (fun x hx hxG => ih x hx hxG),
        rdV_congr hU hyU hy (Xb_unit _ _).1 (fun x hx hxG => ih x hx hxG), ih y hyU hy, hA.2, hB.2]
    have hR : TI Bj e (foldT (t :: ts) Ψ) y = (if t.2.1 = t.2.2 then t.1 • TI Bj e (foldT ts Ψ) y else 0) +
        (TI Bj e (RdV (Xa k n t.2.1 t.2.2) (foldT ts Ψ)) y +
          Complex.I • TI Bj e (RdV (Xb k n t.2.1 t.2.2) (foldT ts Ψ)) y) := by
      have hf : (fun x => PBQ.cP Bj x • gI Bj e (foldT (t :: ts) Ψ) x y) = fun x =>
          (if t.2.1 = t.2.2 then t.1 • (PBQ.cP Bj x • gI Bj e (foldT ts Ψ) x y) else 0) +
            (PBQ.cP Bj x • gI Bj e (RdV (Xa k n t.2.1 t.2.2) (foldT ts Ψ)) x y +
              Complex.I • (PBQ.cP Bj x • gI Bj e (RdV (Xb k n t.2.1 t.2.2) (foldT ts Ψ)) x y)) := by
        funext x
        rw [e0, gI_top]
        split_ifs
        · rw [smul_add, smul_add, smul_comm (PBQ.cP Bj x) t.1, smul_comm (PBQ.cP Bj x) Complex.I]
        · rw [smul_add, smul_zero, smul_add, smul_comm (PBQ.cP Bj x) Complex.I]
      unfold TI
      rw [hf, int_lin _ _ hI0 hA.1 hB.1]
    rw [hL, hR]

end fold

section aa

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

open Formalism.FourierDecayAlt.P.CapelliWordSumExpansion

/- English proof (translation)
The claim follows from `| [], _ => rfl | t :: ts, Ψ => by have e0 : ∀ f : B.Mat k n → E, foldT (t :: ts) f = Top (Q.EH k n) t.1 t.2.1 t.2.2 (foldT ts f) := fun f => rfl funext g rw [e0, e0, top_apply', top_apply', EH_apply, EH_apply, foldT_transl s ts Ψ, rdV_transl, rdV_transl]`.
-/
theorem foldT_transl {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : B.Mat k n) :
    ∀ (ts : List (ℂ × Fin (2 * n + k + 1) × Fin (2 * n + k + 1))) (Ψ : B.Mat k n → E),
      foldT ts (fun g => Ψ (s * g)) = fun g => foldT ts Ψ (s * g)
  | [], _ => rfl
  | t :: ts, Ψ => by
    have e0 : ∀ f : B.Mat k n → E, foldT (t :: ts) f = Top (Q.EH k n) t.1 t.2.1 t.2.2 (foldT ts f) := fun f => rfl
    funext g
    rw [e0, e0, top_apply', top_apply', EH_apply, EH_apply, foldT_transl s ts Ψ, rdV_transl, rdV_transl]

/- English proof (translation)
Rewrite using `[Formalism.FourierDecayAlt.P.PBG.qminor_foldT, Formalism.FourierDecayAlt.P.PBG.qminor_foldT]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[foldT_transl]`.
-/
theorem qminor_transl {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : B.Mat k n) {t : ℕ}
    (a b : Fin t → Fin (2 * n + k + 1)) (u : ℂ) (Ψ : B.Mat k n → E) (g : B.Mat k n) :
    qminorOp (EabH (Hpk k n)) a b u (fun g' => Ψ (s * g')) g = qminorOp (EabH (Hpk k n)) a b u Ψ (s * g) := by
  rw [Formalism.FourierDecayAlt.P.PBG.qminor_foldT, Formalism.FourierDecayAlt.P.PBG.qminor_foldT]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [foldT_transl]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `@insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul, ih]`.
-/
theorem comp_fsum {ι : Type*} (A : Wp →L[ℂ] Wp) (s : Finset ι) (c : ι → ℂ) (v : ι → (Wq →L[ℂ] Wp)) :
    A.comp (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i • A.comp (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul, ih]

/- English proof (translation)
Distinguish the cases in `hx : PBQ.GoodP Bj x`. Simplify using `only [gI, if_pos hx]`. Conclude with `comp_fsum _ s c _`. Simplify using `[gI, hx]`.
-/
theorem gI_sum (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (F : ι → B.Mat k n → (Wq →L[ℂ] Wp)) (x : PBQ.XP k p ρ) (g : B.Mat k n) :
    gI Bj e (fun g' => ∑ i ∈ s, c i • F i g') x g = ∑ i ∈ s, c i • gI Bj e (F i) x g := by
  by_cases hx : PBQ.GoodP Bj x
  · simp only [gI, if_pos hx]; exact comp_fsum _ s c _
  · simp [gI, hx]

/- English proof (translation)
Rewrite using `[integral_smul, integral_finsetSum s (f := fun i x => b i • f i x) (fun i hi => (hf i hi).smul (b i))]`. Repeatedly rewrite using `[integral_smul]`.
-/
theorem int_comb {α : Type*} [MeasurableSpace α] {μ : Measure α} {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [CompleteSpace V] {ι : Type*} (s : Finset ι) (a : ℂ) (b : ι → ℂ) (f : ι → α → V)
    (hf : ∀ i ∈ s, Integrable (f i) μ) :
    ∫ x, a • ∑ i ∈ s, b i • f i x ∂μ = a • ∑ i ∈ s, b i • ∫ x, f i x ∂μ := by
  rw [integral_smul, integral_finsetSum s (f := fun i x => b i • f i x) (fun i hi => (hf i hi).smul (b i))]
  simp_rw [integral_smul]

open Classical in

def cfA (m : ℕ) (hm : m ≤ n) (g : B.Mat k n) (c : Fin m → Fin (2 * n + k + 1)) : ℂ :=
  if StrictMono c then
    (Matrix.of fun a l : Fin m => herm (Hpk k n) (g *ᵥ bvec (c l)) (bvec (eI k n (Fin.castLE hm a)))).det
  else 0

open Classical in

def cfV (m : ℕ) (hm : m ≤ n) (g : B.Mat k n) (c : Fin m → Fin (2 * n + k + 1)) : ℂ :=
  if StrictMono (fun l => C3.keyS k n (c l)) then
    (Matrix.of fun a l : Fin m => (g⁻¹ *ᵥ bvec (eI k n (Fin.castLE hm a))) (c l)).det
  else 0

/- English proof (translation)
Unfold `C3.AAop cfA`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem AAop_sum {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (m : ℕ) (hm : m ≤ n) (u : ℂ)
    (f : B.Mat k n → E) (g : B.Mat k n) :
    C3.AAop k n m hm u f g = ∑ c : Fin m → Fin (2 * n + k + 1),
      cfA m hm g c • qminorOp (EabH (Hpk k n)) (C3.xR k n m hm) c u f g := by
  unfold C3.AAop cfA
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

/- English proof (translation)
Unfold `C3.AAvop cfV`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem AAvop_sum {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (m : ℕ) (hm : m ≤ n) (ell : ℂ)
    (f : B.Mat k n → E) (g : B.Mat k n) :
    C3.AAvop k n m hm ell f g = ∑ c : Fin m → Fin (2 * n + k + 1),
      cfV m hm g c • qminorOp (EabH (Hpk k n)) c (C3.sR k n m hm) (ell + (m : ℂ) - 1) f g := by
  unfold C3.AAvop cfV
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Establish `: CompleteSpace Wp` using `FiniteDimensional.complete ℂ Wp`. Use `set ts : Equiv.Perm (Fin t) → List (ℂ × Fin (2 * n + k + 1) × Fin (2 * n + k + 1)) := fun σ => List.ofFn fun j : Fin t => (u - ((j : ℕ) : ℂ), a (σ j), b j) with hts`. Establish `hq : ∀ f : B.Mat k n → (Wq →L[ℂ] Wp), qminorOp (EabH (Hpk k n)) a b u f = fun g => ∑ σ, ((Equiv.Perm.sign σ : ℤ) : ℂ) • foldT (ts σ) f g` using `fun f => funext fun g => Formalism.FourierDecayAlt.P.PBG.qminor_foldT a b u f g`. Establish `hF` using `fun σ => foldT_TI Bj e hΨ hU hv (ts σ)`. Establish `hI : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin t))), Integrable (fun x => PBQ.cP Bj x • gI Bj e (foldT (ts σ) Ψ) x y) (PBQ.muXP Bj)` using `fun σ _ => int_gI Bj e (Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (hF σ).1) (hF σ).2.1 hyU hy`.

Establish `hfun : (fun x => PBQ.cP Bj x • gI Bj e (qminorOp (EabH (Hpk k n)) a b u Ψ) x y) = fun x => (1 : ℂ) • ∑ σ, ((Equiv.Perm.sign σ : ℤ) : ℂ) • (PBQ.cP Bj x • gI Bj e (foldT (ts σ) Ψ) x y)`. Use function extensionality and compare the values at `x`. Rewrite using `[hq, one_smul, gI_sum, Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun σ _ => smul_comm _ _ _`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hfun]`. Conclude with `(integrable_finsetSum _ fun σ hσ => (hI σ hσ).smul ((Equiv.Perm.sign σ : ℤ) : ℂ)).smul (1 : ℂ)`. Establish `lhs : qminorOp (EabH (Hpk k n)) a b u (TI Bj e Ψ) y = ∑ σ, ((Equiv.Perm.sign σ : ℤ) : ℂ) • TI Bj e (foldT (ts σ) Ψ) y`. Rewrite using `[Formalism.FourierDecayAlt.P.PBG.qminor_foldT]`. Conclude with `Finset.sum_congr rfl fun σ _ => by rw [(hF σ).2.2 y hyU hy]`.

Rewrite using `[lhs]`. Unfold `TI`. Rewrite using `[hfun, int_comb _ 1 _ _ hI, one_smul]`.
-/
theorem qminor_TI (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) {Ψ : B.Mat k n → (Wq →L[ℂ] Wp)}
    (hΨ : CkOn ⊤ (GV k n) Ψ) {U : Set (B.Mat k n)} (hU : IsOpen U) (hv : VanishL Bj e Ψ U) {t : ℕ}
    (a b : Fin t → Fin (2 * n + k + 1)) (u : ℂ) {y : B.Mat k n} (hyU : y ∈ U) (hy : y ∈ GV k n) :
    Integrable (fun x => PBQ.cP Bj x • gI Bj e (qminorOp (EabH (Hpk k n)) a b u Ψ) x y) (PBQ.muXP Bj) ∧
      qminorOp (EabH (Hpk k n)) a b u (TI Bj e Ψ) y = TI Bj e (qminorOp (EabH (Hpk k n)) a b u Ψ) y := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  set ts : Equiv.Perm (Fin t) → List (ℂ × Fin (2 * n + k + 1) × Fin (2 * n + k + 1)) :=
    fun σ => List.ofFn fun j : Fin t => (u - ((j : ℕ) : ℂ), a (σ j), b j) with hts
  have hq : ∀ f : B.Mat k n → (Wq →L[ℂ] Wp), qminorOp (EabH (Hpk k n)) a b u f =
      fun g => ∑ σ, ((Equiv.Perm.sign σ : ℤ) : ℂ) • foldT (ts σ) f g :=
    fun f => funext fun g => Formalism.FourierDecayAlt.P.PBG.qminor_foldT a b u f g
  have hF := fun σ => foldT_TI Bj e hΨ hU hv (ts σ)
  have hI : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin t))),
      Integrable (fun x => PBQ.cP Bj x • gI Bj e (foldT (ts σ) Ψ) x y) (PBQ.muXP Bj) :=
    fun σ _ => int_gI Bj e (Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (hF σ).1) (hF σ).2.1 hyU hy
  have hfun : (fun x => PBQ.cP Bj x • gI Bj e (qminorOp (EabH (Hpk k n)) a b u Ψ) x y) = fun x =>
      (1 : ℂ) • ∑ σ, ((Equiv.Perm.sign σ : ℤ) : ℂ) • (PBQ.cP Bj x • gI Bj e (foldT (ts σ) Ψ) x y) := by
    funext x
    rw [hq, one_smul, gI_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun σ _ => smul_comm _ _ _
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact (integrable_finsetSum _ fun σ hσ => (hI σ hσ).smul ((Equiv.Perm.sign σ : ℤ) : ℂ)).smul (1 : ℂ)
  · have lhs : qminorOp (EabH (Hpk k n)) a b u (TI Bj e Ψ) y =
        ∑ σ, ((Equiv.Perm.sign σ : ℤ) : ℂ) • TI Bj e (foldT (ts σ) Ψ) y := by
      rw [Formalism.FourierDecayAlt.P.PBG.qminor_foldT]
      exact Finset.sum_congr rfl fun σ _ => by rw [(hF σ).2.2 y hyU hy]
    rw [lhs]
    unfold TI
    rw [hfun, int_comb _ 1 _ _ hI, one_smul]

open Classical in

/- English proof (translation)
Establish `: CompleteSpace Wp` using `FiniteDimensional.complete ℂ Wp`. Establish `hI` using `fun c => qminor_TI Bj e hΨ hU hv (C3.xR k n m hm) c u hyU hy`. Establish `hpt : ∀ x, PBQ.cP Bj x • (if PBQ.GoodP Bj x then (Bj.π (Matrix.of x.1.1)).comp (C3.AAop k n m hm u (fun g => Ψ (sE Bj e x * g)) y) else 0) = (1 : ℂ) • ∑ c : Fin m → Fin (2 * n + k + 1), cfA m hm y c • (PBQ.cP Bj x • gI Bj e (qminorOp (EabH (Hpk k n)) (C3.xR k n m hm) c u Ψ) x y)`. Introduce `x`. Distinguish the cases in `hx : PBQ.GoodP Bj x`.

Rewrite using `[if_pos hx, AAop_sum, comp_fsum, one_smul, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[qminor_transl, smul_comm]`. Simplify using `[gI, hx]`. Simplify using `[gI, hx]`.

Rewrite using `[AAop_sum, integral_congr_ae (Eventually.of_forall hpt), int_comb _ 1 _ _ (fun c _ => (hI c).1), one_smul]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[(hI c).2]`. Both sides reduce to the same expression.
-/
theorem AA_TI (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) {Ψ : B.Mat k n → (Wq →L[ℂ] Wp)}
    (hΨ : CkOn ⊤ (GV k n) Ψ) {U : Set (B.Mat k n)} (hU : IsOpen U) (hv : VanishL Bj e Ψ U) (m : ℕ) (hm : m ≤ n)
    (u : ℂ) {y : B.Mat k n} (hyU : y ∈ U) (hy : y ∈ GV k n) :
    C3.AAop k n m hm u (TI Bj e Ψ) y = ∫ x, PBQ.cP Bj x • (if PBQ.GoodP Bj x then
      (Bj.π (Matrix.of x.1.1)).comp (C3.AAop k n m hm u (fun g => Ψ (sE Bj e x * g)) y) else 0) ∂(PBQ.muXP Bj) := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have hI := fun c => qminor_TI Bj e hΨ hU hv (C3.xR k n m hm) c u hyU hy
  have hpt : ∀ x, PBQ.cP Bj x • (if PBQ.GoodP Bj x then
      (Bj.π (Matrix.of x.1.1)).comp (C3.AAop k n m hm u (fun g => Ψ (sE Bj e x * g)) y) else 0) =
      (1 : ℂ) • ∑ c : Fin m → Fin (2 * n + k + 1), cfA m hm y c •
        (PBQ.cP Bj x • gI Bj e (qminorOp (EabH (Hpk k n)) (C3.xR k n m hm) c u Ψ) x y) := by
    intro x
    by_cases hx : PBQ.GoodP Bj x
    · rw [if_pos hx, AAop_sum, comp_fsum, one_smul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [qminor_transl, smul_comm]
      simp [gI, hx]
    · simp [gI, hx]
  rw [AAop_sum, integral_congr_ae (Eventually.of_forall hpt), int_comb _ 1 _ _ (fun c _ => (hI c).1), one_smul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [(hI c).2]; rfl

open Classical in

/- English proof (translation)
Establish `: CompleteSpace Wp` using `FiniteDimensional.complete ℂ Wp`. Establish `hI` using `fun c => qminor_TI Bj e hΨ hU hv c (C3.sR k n m hm) (ell + (m : ℂ) - 1) hyU hy`. Establish `hpt : ∀ x, PBQ.cP Bj x • (if PBQ.GoodP Bj x then (Bj.π (Matrix.of x.1.1)).comp (C3.AAvop k n m hm ell (fun g => Ψ (sE Bj e x * g)) y) else 0) = (1 : ℂ) • ∑ c : Fin m → Fin (2 * n + k + 1), cfV m hm y c • (PBQ.cP Bj x • gI Bj e (qminorOp (EabH (Hpk k n)) c (C3.sR k n m hm) (ell + …`. Introduce `x`. Distinguish the cases in `hx : PBQ.GoodP Bj x`.

Rewrite using `[if_pos hx, AAvop_sum, comp_fsum, one_smul, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[qminor_transl, smul_comm]`. Simplify using `[gI, hx]`. Simplify using `[gI, hx]`.

Rewrite using `[AAvop_sum, integral_congr_ae (Eventually.of_forall hpt), int_comb _ 1 _ _ (fun c _ => (hI c).1), one_smul]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[(hI c).2]`. Both sides reduce to the same expression.
-/
theorem AAv_TI (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) {Ψ : B.Mat k n → (Wq →L[ℂ] Wp)}
    (hΨ : CkOn ⊤ (GV k n) Ψ) {U : Set (B.Mat k n)} (hU : IsOpen U) (hv : VanishL Bj e Ψ U) (m : ℕ) (hm : m ≤ n)
    (ell : ℂ) {y : B.Mat k n} (hyU : y ∈ U) (hy : y ∈ GV k n) :
    C3.AAvop k n m hm ell (TI Bj e Ψ) y = ∫ x, PBQ.cP Bj x • (if PBQ.GoodP Bj x then
      (Bj.π (Matrix.of x.1.1)).comp (C3.AAvop k n m hm ell (fun g => Ψ (sE Bj e x * g)) y) else 0)
        ∂(PBQ.muXP Bj) := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have hI := fun c => qminor_TI Bj e hΨ hU hv c (C3.sR k n m hm) (ell + (m : ℂ) - 1) hyU hy
  have hpt : ∀ x, PBQ.cP Bj x • (if PBQ.GoodP Bj x then
      (Bj.π (Matrix.of x.1.1)).comp (C3.AAvop k n m hm ell (fun g => Ψ (sE Bj e x * g)) y) else 0) =
      (1 : ℂ) • ∑ c : Fin m → Fin (2 * n + k + 1), cfV m hm y c •
        (PBQ.cP Bj x • gI Bj e (qminorOp (EabH (Hpk k n)) c (C3.sR k n m hm) (ell + (m : ℂ) - 1) Ψ) x y) := by
    intro x
    by_cases hx : PBQ.GoodP Bj x
    · rw [if_pos hx, AAvop_sum, comp_fsum, one_smul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [qminor_transl, smul_comm]
      simp [gI, hx]
    · simp [gI, hx]
  rw [AAvop_sum, integral_congr_ae (Eventually.of_forall hpt), int_comb _ 1 _ _ (fun c _ => (hI c).1), one_smul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [(hI c).2]; rfl

end aa

section vlet

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

open Classical in

/- English proof (translation)
Establish `: CompleteSpace Wp` using `FiniteDimensional.complete ℂ Wp`. Distinguish the cases in `h0 : ε = 1 ∧ i = 0`. Simplify using `[D.vLet, h0]`. Distinguish the cases in `hl : l.1 = true`. Simplify using `only [D.vLet, h0, hl, if_false, if_true]`.

Rewrite using `[AA_TI Bj e hΨ hU hv _ _ _ hyU hy, ← integral_smul]`. Use `integral_congr_ae (Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Distinguish the cases in `hx : PBQ.GoodP Bj x`. Simplify using `only [if_pos hx]`. Rewrite using `[ContinuousLinearMap.comp_smul, smul_comm]`.

Simplify using `[hx]`. Simplify using `only [D.vLet, h0, hl, if_false]`. Rewrite using `[AAv_TI Bj e hΨ hU hv _ _ _ hyU hy, ← integral_smul]`. Use `integral_congr_ae (Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Distinguish the cases in `hx : PBQ.GoodP Bj x`.

Simplify using `only [if_pos hx, Bool.false_eq_true, if_false]`. Rewrite using `[ContinuousLinearMap.comp_smul, smul_comm]`. Simplify using `[hx]`.
-/
theorem vLet_TI (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) {Ψ : B.Mat k n → (Wq →L[ℂ] Wp)}
    (hΨ : CkOn ⊤ (GV k n) Ψ) {U : Set (B.Mat k n)} (hU : IsOpen U) (hv : VanishL Bj e Ψ U)
    (z z' : Fin (2 * n + k + 1) → ℂ) (i : ℕ) (hi : i ≤ n) (l : C.Letter) (ε : Fin 2) {y : B.Mat k n}
    (hyU : y ∈ U) (hy : y ∈ GV k n) :
    D.vLet k n z z' i hi l ε (TI Bj e Ψ) y = ∫ x, PBQ.cP Bj x • (if PBQ.GoodP Bj x then
      (Bj.π (Matrix.of x.1.1)).comp (D.vLet k n z z' i hi l ε (fun g => Ψ (sE Bj e x * g)) y) else 0)
        ∂(PBQ.muXP Bj) := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  by_cases h0 : ε = 1 ∧ i = 0
  · simp [D.vLet, h0]
  · by_cases hl : l.1 = true
    · simp only [D.vLet, h0, hl, if_false, if_true]
      rw [AA_TI Bj e hΨ hU hv _ _ _ hyU hy, ← integral_smul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      by_cases hx : PBQ.GoodP Bj x
      · simp only [if_pos hx]
        rw [ContinuousLinearMap.comp_smul, smul_comm]
      · simp [hx]
    · simp only [D.vLet, h0, hl, if_false]
      rw [AAv_TI Bj e hΨ hU hv _ _ _ hyU hy, ← integral_smul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      by_cases hx : PBQ.GoodP Bj x
      · simp only [if_pos hx, Bool.false_eq_true, if_false]
        rw [ContinuousLinearMap.comp_smul, smul_comm]
      · simp [hx]

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, f', hU, hgU, hc, he⟩` from `hf g₀ hg₀`. Conclude with `⟨U, f', hU, hgU, hc, fun x hx hxG => he x hx hxG⟩`.
-/
theorem smoothOnH_of_ckOn {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : B.Mat k n → E}
    (hf : CkOn ⊤ (GV k n) f) : SmoothOnH (Hpk k n) f := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, he⟩ := hf g₀ hg₀
  exact ⟨U, f', hU, hgU, hc, fun x hx hxG => he x hx hxG⟩

/- English proof (translation)
Establish `: CompleteSpace Wp` using `FiniteDimensional.complete ℂ Wp`. Establish `hK : CkOn ⊤ (GV k n) (PBG.Kr B0 Ht)` using `fun g hg => Formalism.FourierDecayAlt.P.PBG.kr_loc_cpt B0 hHt hCs hS g hg`. Establish `hKs : SmoothOnH (Hpk k n) (PBG.Kr B0 Ht)` using `smoothOnH_of_ckOn hK`. Take `⟨R, hR⟩` from `hCs.exists_bound_of_continuousOn (Formalism.FourierDecayAlt.P.B6.gN_continuous.continuousOn (s := Cs))`. Establish `hRb : ∃ R : ℝ, ∀ g ∈ B.GV k n, Ht g ≠ 0 → B.gN g ≤ R`.

Use `⟨R, fun g hg hne => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hgt`. Establish `hgC : g ∈ Cs`. Assume the negation of the conclusion as `hgC`. Conclude with `hne (hS g hg hgC)`.

Use `hR g hgC` as an intermediate fact. Rewrite `this` using `[Real.norm_eq_abs]`. Conclude with `hgt ((le_abs_self _).trans this)`. Establish `hL : ∀ g ∈ B.GV k n, Dmin k n B0.z B0.z' g ⟨i, by omega⟩ ≠ 0 → CapelliWordSumExpansion.Loc ⊤ Ht g` using `fun g hg _ => hHt g hg`. Rewrite using `[pbF_eq_TI, pbF_eq_TI, vLet_TI Bj e hK hU hv _ _ i hi l ε hyU hy]`.

Unfold `TI`. Use `integral_congr_ae (Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Distinguish the cases in `hx : PBQ.GoodP Bj x`. Simplify using `only [gI, if_pos hx]`. Establish `hs : sE Bj e x ∈ Sset k n B0.z` using `hzS ▸ sE_mem_S Bj e x`.

Establish `hs1 : (1 : B.Mat k n) ∈ Sset k n B0.z'` using `Formalism.FourierDecayAlt.P.PBG.one_mem_Sset k n B0.z'`. Establish `hmem : sE Bj e x * y ∈ B.GV k n` using `Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (sE_GV Bj e x) hy`. Establish `hD' : Dmin k n B0.z B0.z' (sE Bj e x * y) ⟨i, by omega⟩ ≠ 0`. Use `Formalism.QuantumDeterminants.diagonal_inverse_holds k n B0.z B0.z' B0.z_mem B0.z'_mem _ hs 1 hs1 y ⟨i, by omega⟩` as an intermediate fact. Rewrite `this` using `[Matrix.mul_one]`.

Rewrite using `[this]`. Conclude with `hD`. Establish `htr` using `Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts.vLet_transl B0.z B0.z' B0.z_mem B0.z'_mem i hi l ε hKs hs hs1 hy`. Simplify using `only [Matrix.mul_one] at htr`. Rewrite using `[← htr, ((Formalism.FourierDecayAlt.P.PBG.right_average_smooth_comm k n Wp Wq B0 i hi Ht hL hRb _ hmem hD').2 l ε)]`.

Simplify using `[gI, hx]`.
-/
theorem vLet_pb (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (hzS : B0.z = D.castV e (liftVec k p ρ Bj.z)) {Ht : B.Mat k n → (Wq →L[ℂ] Wp)} (hHt : CkOn ⊤ (GV k n) Ht)
    {Cs : Set (B.Mat k n)} (hCs : IsCompact Cs) (hS : ∀ g ∈ B.GV k n, g ∉ Cs → Ht g = 0) {U : Set (B.Mat k n)}
    (hU : IsOpen U) (hv : VanishL Bj e (PBG.Kr B0 Ht) U) (i : ℕ) (hi : i ≤ n) (l : C.Letter) (ε : Fin 2)
    {y : B.Mat k n} (hyU : y ∈ U) (hy : y ∈ GV k n) (hD : Dmin k n B0.z B0.z' y ⟨i, by omega⟩ ≠ 0) :
    D.vLet k n B0.z B0.z' i hi l ε (PBQ.pbF Bj B0 e Ht) y =
      PBQ.pbF Bj B0 e (D.vLet k n B0.z B0.z' i hi l ε Ht) y := by
  classical
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have hK : CkOn ⊤ (GV k n) (PBG.Kr B0 Ht) := fun g hg => Formalism.FourierDecayAlt.P.PBG.kr_loc_cpt B0 hHt hCs hS g hg
  have hKs : SmoothOnH (Hpk k n) (PBG.Kr B0 Ht) := smoothOnH_of_ckOn hK
  obtain ⟨R, hR⟩ := hCs.exists_bound_of_continuousOn (Formalism.FourierDecayAlt.P.B6.gN_continuous.continuousOn (s := Cs))
  have hRb : ∃ R : ℝ, ∀ g ∈ B.GV k n, Ht g ≠ 0 → B.gN g ≤ R := by
    refine ⟨R, fun g hg hne => ?_⟩
    by_contra hgt
    have hgC : g ∈ Cs := by
      by_contra hgC; exact hne (hS g hg hgC)
    have := hR g hgC
    rw [Real.norm_eq_abs] at this
    exact hgt ((le_abs_self _).trans this)
  have hL : ∀ g ∈ B.GV k n, Dmin k n B0.z B0.z' g ⟨i, by omega⟩ ≠ 0 → CapelliWordSumExpansion.Loc ⊤ Ht g :=
    fun g hg _ => hHt g hg
  rw [pbF_eq_TI, pbF_eq_TI, vLet_TI Bj e hK hU hv _ _ i hi l ε hyU hy]
  unfold TI
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  by_cases hx : PBQ.GoodP Bj x
  · simp only [gI, if_pos hx]
    have hs : sE Bj e x ∈ Sset k n B0.z := hzS ▸ sE_mem_S Bj e x
    have hs1 : (1 : B.Mat k n) ∈ Sset k n B0.z' := Formalism.FourierDecayAlt.P.PBG.one_mem_Sset k n B0.z'
    have hmem : sE Bj e x * y ∈ B.GV k n := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (sE_GV Bj e x) hy
    have hD' : Dmin k n B0.z B0.z' (sE Bj e x * y) ⟨i, by omega⟩ ≠ 0 := by
      have := Formalism.QuantumDeterminants.diagonal_inverse_holds k n B0.z B0.z' B0.z_mem B0.z'_mem _ hs 1 hs1 y ⟨i, by omega⟩
      rw [Matrix.mul_one] at this
      rw [this]; exact hD
    have htr := Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts.vLet_transl B0.z B0.z' B0.z_mem B0.z'_mem i hi l ε hKs hs hs1 hy
    simp only [Matrix.mul_one] at htr
    rw [← htr, ((Formalism.FourierDecayAlt.P.PBG.right_average_smooth_comm k n Wp Wq B0 i hi Ht hL hRb _ hmem hD').2 l ε)]
  · simp [gI, hx]

end vlet

end Formalism.FourierDecayAlt.P.PartialBesselProperness
