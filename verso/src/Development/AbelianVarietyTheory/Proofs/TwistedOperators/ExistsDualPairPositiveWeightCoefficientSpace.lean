import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefDualPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.Divisors.GridTestLatticeLargestSlopeBound
import Formalism.LocalToGlobal.Columns.CoefModB
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorMapDescent

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TopCoefPair

open GlobalTheory.CoefSpace Matrix
open scoped TensorProduct

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

/- English proof (translation)
Substitute `hnm` using the available equality. Both sides reduce to the same expression.
-/
theorem descEnum_cast {n m : ℕ} (E : Finset ℚ) (h1 : E.card = n) (h2 : E.card = m) (hnm : n = m) (a : Fin n) :
    GlobalTheory.SignedHC.descEnum E h1 a = GlobalTheory.SignedHC.descEnum E h2 (Fin.cast hnm a) := by
  subst hnm
  rfl

/- English proof (translation)
The claim follows from `(num D sc.cGap τ).parPi_m`.
-/
theorem par_core_top (G : GridData L sc) (τ : D.what₂.Tau) :
    Node.par D sc.cGap (.core D.R.m) τ = GlobalTheory.SignedHC.plus ((num D sc.cGap τ).weightX 0) :=
  (num D sc.cGap τ).parPi_m

/- English proof (translation)
The claim follows from `funext fun a => by obtain ⟨-, q, -, hS⟩ := M.enum τ have hx : (q a, M.ε τ a) ∈ Node.par D sc.cGap (.core D.R.m) τ := hS ▸ Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩ rw [par_core_top G τ] at hx obtain ⟨y, -, hy⟩ := Finset.mem_image.1 hx exact (congrArg Prod.snd hy).symm`.
-/
theorem sign_top (G : GridData L sc) (M : DSModel (G.V (.core D.R.m)) (Node.par D sc.cGap (.core D.R.m)))
    (τ : D.what₂.Tau) : M.ε τ = fun _ => true := funext fun a => by
  obtain ⟨-, q, -, hS⟩ := M.enum τ
  have hx : (q a, M.ε τ a) ∈ Node.par D sc.cGap (.core D.R.m) τ :=
    hS ▸ Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩
  rw [par_core_top G τ] at hx
  obtain ⟨y, -, hy⟩ := Finset.mem_image.1 hx
  exact (congrArg Prod.snd hy).symm

/- English proof (translation)
Take `⟨hanti, q, hq, hS⟩` from `M.enum τ`. Establish `hn : (G.V (.core D.R.m)).rank = rankP D D.R.m` using `rank_Xp G`. Establish `hE` using `card_weight D sc.cGap τ`. Establish `hmem : ∀ i, q i ∈ (num D sc.cGap τ).weightX 0` using `fun i => by`. Establish `hx : (q i, M.ε τ i) ∈ Node.par D sc.cGap (.core D.R.m) τ` using `hS ▸ Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩`.

Rewrite `hx` using `[par_core_top G τ]`. Take `⟨y, hy, e⟩` from `Finset.mem_image.1 hx`. Rewrite using `[← (Prod.mk.inj e).1]`. Conclude with `hy`. Establish `hqa : StrictAnti q` using `fun i j hij => by`.

Use `hanti hij` as an intermediate fact. Rewrite `this` using `[hq, hq]`. Conclude with `this` after adjusting the coercions. Establish `hd` using `GlobalTheory.SignedHC.descEnum_unique (hE.trans hn.symm) hqa hmem`. Establish `hw` using `La_cast D sc.cGap τ (Fin.cast hn a)`.

Establish `e1 : q a = ((LaP G τ).w a : ℚ) + rhoVec (G.V (.core D.R.m)).rank a`. Rewrite using `[← hd, descEnum_cast _ _ hE hn a]`. Use `show _ = ((La D sc.cGap τ).w (Fin.cast hn a) : ℚ) + _`. Establish `hc : ((G.V (.core D.R.m)).rank : ℚ) = (rankP D D.R.m : ℚ)` using `by exact_mod_cast hn`. Rewrite using `[hw, GlobalTheory.SignedHC.highestWeight, rhoVec, Fin.coe_cast, hc]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hq, e1]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lam_top (G : GridData L sc) (M : DSModel (G.V (.core D.R.m)) (Node.par D sc.cGap (.core D.R.m)))
    (τ : D.what₂.Tau) (a : Fin (G.V (.core D.R.m)).rank) :
    M.lam τ a = ((LaP G τ).w a : ℝ) + ((rhoVec (G.V (.core D.R.m)).rank a : ℚ) : ℝ) := by
  obtain ⟨hanti, q, hq, hS⟩ := M.enum τ
  have hn : (G.V (.core D.R.m)).rank = rankP D D.R.m := rank_Xp G
  have hE := card_weight D sc.cGap τ
  have hmem : ∀ i, q i ∈ (num D sc.cGap τ).weightX 0 := fun i => by
    have hx : (q i, M.ε τ i) ∈ Node.par D sc.cGap (.core D.R.m) τ :=
      hS ▸ Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩
    rw [par_core_top G τ] at hx
    obtain ⟨y, hy, e⟩ := Finset.mem_image.1 hx
    rw [← (Prod.mk.inj e).1]
    exact hy
  have hqa : StrictAnti q := fun i j hij => by
    have := hanti hij
    rw [hq, hq] at this
    exact_mod_cast this
  have hd := GlobalTheory.SignedHC.descEnum_unique (hE.trans hn.symm) hqa hmem
  have hw := La_cast D sc.cGap τ (Fin.cast hn a)
  have e1 : q a = ((LaP G τ).w a : ℚ) + rhoVec (G.V (.core D.R.m)).rank a := by
    rw [← hd, descEnum_cast _ _ hE hn a]
    show _ = ((La D sc.cGap τ).w (Fin.cast hn a) : ℚ) + _
    have hc : ((G.V (.core D.R.m)).rank : ℚ) = (rankP D D.R.m : ℚ) := by exact_mod_cast hn
    rw [hw, GlobalTheory.SignedHC.highestWeight, rhoVec, Fin.coe_cast, hc]
    ring
  rw [hq, e1]
  push_cast
  ring

/- English proof (translation)
Rewrite using `[← polyAction_mul, ← polyAction_mul, show B⁻¹ * (B * g * B⁻¹) = g * B⁻¹ by simp only [mul_assoc, inv_mul_cancel_left]]`.
-/
theorem polyAction_conj {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (B g : ι → GL (Fin n) ℂ)
    (F : Pol ℂ ι n) : actP lam B⁻¹ (actP lam (B * g * B⁻¹) F) = actP lam g (actP lam B⁻¹ F) := by
  rw [← polyAction_mul, ← polyAction_mul, show B⁻¹ * (B * g * B⁻¹) = g * B⁻¹ by simp only [mul_assoc, inv_mul_cancel_left]]

/- English proof (translation)
Rewrite using `[← polyAction_mul, mul_inv_cancel, polyAction_one₂]`.
-/
theorem polyAction_inv_cancel {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (B : ι → GL (Fin n) ℂ)
    (F : Pol ℂ ι n) : actP lam B (actP lam B⁻¹ F) = F := by
  rw [← polyAction_mul, mul_inv_cancel, polyAction_one₂]

/- English proof (translation)
Take `⟨H', _, _, π', e, h1, h2, h3, h4⟩` from `GlobalTheory.NablaType.exists_isHCTypeU_nablaSq _ (LaP G τ)`. Establish `hds : Formalism.MainNotions.S.IsHCTypeU _ (M.lam τ) (M.σ τ)` using `(GlobalTheory.RealPar.isDS_const_iff true _ _).1 (sign_top G M τ ▸ M.ds τ)`. Rewrite `hds` using `[show M.lam τ = _ from funext (lam_top G M τ)]`. Take `⟨A, hA⟩` from `GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU _ _ _ _ _ _ hds h1`. Use `⟨e ∘ₗ A.toLinearMap, h2.comp A.injective, fun x => h3 _, fun k hk x => ?_⟩` and prove the remaining obligations.

Use `show e (A (M.σ τ k x)) = _`. Rewrite using `[hA _ hk, h4 _ hk]`. Both sides reduce to the same expression.
-/
theorem exists_model (G : GridData L sc) (M : DSModel (G.V (.core D.R.m)) (Node.par D sc.cGap (.core D.R.m)))
    (τ : D.what₂.Tau) :
    ∃ A : M.H τ →ₗ[ℂ] MvPolynomial (Fin (G.V (.core D.R.m)).rank × Fin (G.V (.core D.R.m)).rank) ℂ,
      Function.Injective A ∧ (∀ x, A x ∈ nablaSq ℂ _ (LaP G τ)) ∧
      ∀ k : GL (Fin (G.V (.core D.R.m)).rank) ℂ,
        (k : Matrix (Fin (G.V (.core D.R.m)).rank) (Fin (G.V (.core D.R.m)).rank) ℂ) ∈ Matrix.unitaryGroup _ ℂ →
        ∀ x, A (M.σ τ (k : Matrix (Fin (G.V (.core D.R.m)).rank) (Fin (G.V (.core D.R.m)).rank) ℂ) x) =
          sqAct ℂ _ (LaP G τ) k (A x) := by
  obtain ⟨H', _, _, π', e, h1, h2, h3, h4⟩ := GlobalTheory.NablaType.exists_isHCTypeU_nablaSq _ (LaP G τ)
  have hds : Formalism.MainNotions.S.IsHCTypeU _ (M.lam τ) (M.σ τ) :=
    (GlobalTheory.RealPar.isDS_const_iff true _ _).1 (sign_top G M τ ▸ M.ds τ)
  rw [show M.lam τ = _ from funext (lam_top G M τ)] at hds
  obtain ⟨A, hA⟩ := GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU _ _ _ _ _ _ hds h1
  refine ⟨e ∘ₗ A.toLinearMap, h2.comp A.injective, fun x => h3 _, fun k hk x => ?_⟩
  show e (A (M.σ τ k x)) = _
  rw [hA _ hk, h4 _ hk]
  rfl

/- English proof (translation)
Introduce `D T L sc G θ hθ M`. Establish `hε` using `sign_top G M`. Set `hP` to `GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.posDef_dual G`. Set `B : D.what₂.Tau → GL (Fin (G.V (.core D.R.m)).rank) ℂ` to `fun τ => (M.fr_unit τ).unit`. Establish `hG : ∀ τ, gramOf B τ = gramAt D (G.V (.core D.R.m)) τ` using `fun τ => by`.

Rewrite using `[← M.fr_gram τ, hε]`. Simplify using `[gramOf, B, Formalism.REAL.Jm]`. Use `choose A h1 h2 h3 using exists_model G M`. Set `T0 : SmT M →ₗ[ℂ] Pol ℂ D.what₂.Tau (G.V (.core D.R.m)).rank` to `PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ D.what₂.Tau _).compLinearMap fun τ => (Formalism.GradedWeylDivisibility.blockEmb ℂ τ).toLinearMap ∘ₗ A τ ∘ₗ (M.sm τ).subtype)`. Establish `hT0 : ∀ v : M.Vec, T0 (PiTensorProduct.tprod ℂ v) = ten fun τ => A τ (v τ)` using `fun v => by`.

Simplify using `[T0, ten]`. Set `T1 : SmT M →ₗ[ℂ] Pol ℂ D.what₂.Tau (G.V (.core D.R.m)).rank` to `actP (LaP G) B⁻¹ ∘ₗ T0`. Establish `hT1 : ∀ t, T1 t = actP (LaP G) B⁻¹ (T0 t)` using `fun _ => rfl`. Set `pr : (coefPlus G θ).W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ` to `(pairB (LaP G)).compl₁₂ ((VV ℂ (LaP G)).subtype ∘ₗ (GlobalTheory.CoefModel.toHilb (LaP G) hP).symm.toLinearMap) T1`. Establish `hpr : ∀ w t, pr w t = pairB (LaP G) ((GlobalTheory.CoefModel.toHilb (LaP G) hP).symm w).1 (T1 t)` using `fun _ _ => rfl`.

Use `⟨pr, fun h0 => ?_, fun τ g hg w v u hu => ?_⟩` and prove the remaining obligations. Establish `hv : ∀ τ, ∃ v : M.sm τ, (v : M.H τ) ≠ 0` using `fun τ => by`. Use `(M.ds τ).1` as an intermediate fact. Use `(M.ds τ).2.1` as an intermediate fact. Take `⟨v, hv, hs⟩` from `GlobalTheory.GardingVec.exists_smoothVec (M.ds τ).2.2.1 (M.fr_unit τ) (M.fr_gram τ)`.

Conclude with `⟨⟨v, Submodule.subset_span hs⟩, hv⟩`. Use `choose v hv using hv`. Establish `hten : ten (fun τ => A τ (v τ)) ≠ 0` using `GlobalTheory.Proof.TensorMapDescent.ten_ne_zero (fun τ => A τ (v τ)) (fun τ h => hv τ (h1 τ (h.trans (map_zero _).symm)))`. Establish `hmem : T1 (PiTensorProduct.tprod ℂ v) ∈ VV ℂ (LaP G)`. Rewrite using `[hT1, hT0]`.

Conclude with `polyAction_mem_VV _ _ (GlobalTheory.Proof.TensorMapDescent.ten_mem (LaP G) _ fun τ => h2 τ (v τ))`. Establish `hz : T1 (PiTensorProduct.tprod ℂ v) = 0` using `congrArg Subtype.val ((pairingBNondegenerate_holds ℂ _ _ (LaP G)).2 ⟨_, hmem⟩ fun y => by`. Establish `h4 : pr (GlobalTheory.CoefModel.toHilb (LaP G) hP y) (PiTensorProduct.tprod ℂ v) = 0`. Rewrite using `[show pr = 0 from h0]`. Both sides reduce to the same expression.

Rewrite using `[pairBK_apply]`. Conclude with `h4)`. Rewrite `hz` using `[hT1, hT0]`. Use `congrArg (actP (LaP G) B) hz` as an intermediate fact. Conclude with `hten ((polyAction_inv_cancel (LaP G) B _).symm.trans (this.trans (map_zero _)))`.

Establish `ha : IsAtTau θ (G.V (.core D.R.m)) τ g (atTau θ (G.V (.core D.R.m)) τ g)`. Establish `hex` using `(GlobalTheory.PointAtPlace.existsUnique_isAtTau (G.V (.core D.R.m)) τ θ hθ g hg).exists`. Rewrite using `[atTau, dif_pos hex]`. Conclude with `hex.choose_spec`. Use `set Gh := infGL θ (G.V (.core D.R.m)) (atTau θ (G.V (.core D.R.m)) τ g) with hGd`.

Set `k` to `B * Gh * B⁻¹`. Establish `hk : ∀ ρ, (k ρ : Matrix (Fin (G.V (.core D.R.m)).rank) (Fin (G.V (.core D.R.m)).rank) ℂ) ∈ Matrix.unitaryGroup _ ℂ` using `fun ρ => GlobalTheory.CoefSpace.conj_unitary (by`. Use `GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ (G.V (.core D.R.m)) (atTau θ (G.V (.core D.R.m)) τ g) ρ` as an intermediate fact. Rewrite using `[← hG] at this)` and apply the resulting hypothesis. Establish `hup : ∀ ρ, (Function.update v τ u ρ : M.H ρ) = M.σ ρ (k ρ : Matrix (Fin (G.V (.core D.R.m)).rank) (Fin (G.V (.core D.R.m)).rank) ℂ) (v ρ)`.

Introduce `ρ`. Distinguish the cases in `hρ : ρ = τ`. Substitute `hρ` using the available equality. Establish `e : (k ρ : Matrix (Fin (G.V (.core D.R.m)).rank) (Fin (G.V (.core D.R.m)).rank) ℂ) = M.fr ρ * g * (M.fr ρ)⁻¹` using `by show ((B ρ * Gh ρ * (B ρ)⁻¹ : GL (Fin (G.V (.core D.R.m)).rank) ℂ) : Matrix (Fin (G.V (.core D.R.m)).rank) (Fin (G.V (.core D.R.m)).rank) ℂ) = _`. Rewrite using `[Units.val_mul, Units.val_mul, Matrix.coe_units_inv, hGd, infGL_coe, ha.2.1]`.

Both sides reduce to the same expression. Rewrite using `[Function.update_self, hu, e]`. Both sides reduce to the same expression. Establish `e : k ρ = 1`. Establish `: Gh ρ = 1` using `Units.ext (ha.2.2 ρ hρ)`.

Use `show B ρ * Gh ρ * (B ρ)⁻¹ = 1`. Rewrite using `[this, mul_one, mul_inv_cancel]`. Rewrite using `[Function.update_of_ne hρ, e, Units.val_one, (M.ds ρ).2.2.1.1.1]`. Both sides reduce to the same expression. Establish `e0 : T0 (PiTensorProduct.tprod ℂ (Function.update v τ u)) = actP (LaP G) k (T0 (PiTensorProduct.tprod ℂ v))`.

Rewrite using `[hT0, hT0]`. Use `Eq.trans ?_ (actTen ℂ _ _ (LaP G) k _).symm` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `ρ`. Rewrite using `[hup, h3 ρ _ (hk ρ)]`.

Establish `e1 : T1 (PiTensorProduct.tprod ℂ (Function.update v τ u)) = actP (LaP G) Gh (T1 (PiTensorProduct.tprod ℂ v))`. Rewrite using `[hT1, hT1, e0]`. Conclude with `polyAction_conj (LaP G) B Gh _`. Take `⟨x, rfl⟩` from `(GlobalTheory.CoefModel.toHilb (LaP G) hP).surjective w`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← e1]`. Both sides reduce to the same expression. Use `_ = pairB (LaP G) x.1 (T1 (PiTensorProduct.tprod ℂ v)) := pairingBInvariantK_holds ℂ _ _ (LaP G) Gh _ _`. Use `_ = _ := rfl`.
-/
theorem exists_dualPair : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (θ : InfFam D),
    IsInfFam θ → ∀ (M : DSModel (G.V (.core D.R.m)) (Node.par D sc.cGap (.core D.R.m))),
    ∃ pr : (coefPlus G θ).W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ, IsDualPair θ M (coefPlus G θ) pr := by
  intro D T L sc G θ hθ M
  classical
  have hε := sign_top G M
  let hP := GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.posDef_dual G
  let B : D.what₂.Tau → GL (Fin (G.V (.core D.R.m)).rank) ℂ := fun τ => (M.fr_unit τ).unit
  have hG : ∀ τ, gramOf B τ = gramAt D (G.V (.core D.R.m)) τ := fun τ => by
    rw [← M.fr_gram τ, hε]
    simp [gramOf, B, Formalism.REAL.Jm]
  choose A h1 h2 h3 using exists_model G M
  let T0 : SmT M →ₗ[ℂ] Pol ℂ D.what₂.Tau (G.V (.core D.R.m)).rank :=
    PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ D.what₂.Tau _).compLinearMap fun τ =>
      (Formalism.GradedWeylDivisibility.blockEmb ℂ τ).toLinearMap ∘ₗ A τ ∘ₗ (M.sm τ).subtype)
  have hT0 : ∀ v : M.Vec, T0 (PiTensorProduct.tprod ℂ v) = ten fun τ => A τ (v τ) := fun v => by
    simp [T0, ten]
  let T1 : SmT M →ₗ[ℂ] Pol ℂ D.what₂.Tau (G.V (.core D.R.m)).rank := actP (LaP G) B⁻¹ ∘ₗ T0
  have hT1 : ∀ t, T1 t = actP (LaP G) B⁻¹ (T0 t) := fun _ => rfl
  let pr : (coefPlus G θ).W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ :=
    (pairB (LaP G)).compl₁₂ ((VV ℂ (LaP G)).subtype ∘ₗ (GlobalTheory.CoefModel.toHilb (LaP G) hP).symm.toLinearMap) T1
  have hpr : ∀ w t, pr w t = pairB (LaP G) ((GlobalTheory.CoefModel.toHilb (LaP G) hP).symm w).1 (T1 t) := fun _ _ => rfl
  refine ⟨pr, fun h0 => ?_, fun τ g hg w v u hu => ?_⟩
  · have hv : ∀ τ, ∃ v : M.sm τ, (v : M.H τ) ≠ 0 := fun τ => by
      have := (M.ds τ).1
      have := (M.ds τ).2.1
      obtain ⟨v, hv, hs⟩ := GlobalTheory.GardingVec.exists_smoothVec (M.ds τ).2.2.1 (M.fr_unit τ) (M.fr_gram τ)
      exact ⟨⟨v, Submodule.subset_span hs⟩, hv⟩
    choose v hv using hv
    have hten : ten (fun τ => A τ (v τ)) ≠ 0 :=
      GlobalTheory.Proof.TensorMapDescent.ten_ne_zero (fun τ => A τ (v τ)) (fun τ h => hv τ (h1 τ (h.trans (map_zero _).symm)))
    have hmem : T1 (PiTensorProduct.tprod ℂ v) ∈ VV ℂ (LaP G) := by
      rw [hT1, hT0]
      exact polyAction_mem_VV _ _ (GlobalTheory.Proof.TensorMapDescent.ten_mem (LaP G) _ fun τ => h2 τ (v τ))
    have hz : T1 (PiTensorProduct.tprod ℂ v) = 0 := congrArg Subtype.val ((pairingBNondegenerate_holds ℂ _ _ (LaP G)).2
      ⟨_, hmem⟩ fun y => by
        have h4 : pr (GlobalTheory.CoefModel.toHilb (LaP G) hP y) (PiTensorProduct.tprod ℂ v) = 0 := by
          rw [show pr = 0 from h0]
          rfl
        rw [pairBK_apply]
        exact h4)
    rw [hT1, hT0] at hz
    have := congrArg (actP (LaP G) B) hz
    exact hten ((polyAction_inv_cancel (LaP G) B _).symm.trans (this.trans (map_zero _)))
  · have ha : IsAtTau θ (G.V (.core D.R.m)) τ g (atTau θ (G.V (.core D.R.m)) τ g) := by
      have hex := (GlobalTheory.PointAtPlace.existsUnique_isAtTau (G.V (.core D.R.m)) τ θ hθ g hg).exists
      rw [atTau, dif_pos hex]
      exact hex.choose_spec
    set Gh := infGL θ (G.V (.core D.R.m)) (atTau θ (G.V (.core D.R.m)) τ g) with hGd
    let k := B * Gh * B⁻¹
    have hk : ∀ ρ, (k ρ : Matrix (Fin (G.V (.core D.R.m)).rank) (Fin (G.V (.core D.R.m)).rank) ℂ) ∈
        Matrix.unitaryGroup _ ℂ := fun ρ =>
      GlobalTheory.CoefSpace.conj_unitary (by
        have := GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ (G.V (.core D.R.m)) (atTau θ (G.V (.core D.R.m)) τ g) ρ
        rwa [← hG] at this)
    have hup : ∀ ρ, (Function.update v τ u ρ : M.H ρ) =
        M.σ ρ (k ρ : Matrix (Fin (G.V (.core D.R.m)).rank) (Fin (G.V (.core D.R.m)).rank) ℂ) (v ρ) := by
      intro ρ
      by_cases hρ : ρ = τ
      · subst hρ
        have e : (k ρ : Matrix (Fin (G.V (.core D.R.m)).rank) (Fin (G.V (.core D.R.m)).rank) ℂ) =
            M.fr ρ * g * (M.fr ρ)⁻¹ := by
          show ((B ρ * Gh ρ * (B ρ)⁻¹ : GL (Fin (G.V (.core D.R.m)).rank) ℂ) :
            Matrix (Fin (G.V (.core D.R.m)).rank) (Fin (G.V (.core D.R.m)).rank) ℂ) = _
          rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, hGd, infGL_coe, ha.2.1]
          rfl
        rw [Function.update_self, hu, e]
        rfl
      · have e : k ρ = 1 := by
          have : Gh ρ = 1 := Units.ext (ha.2.2 ρ hρ)
          show B ρ * Gh ρ * (B ρ)⁻¹ = 1
          rw [this, mul_one, mul_inv_cancel]
        rw [Function.update_of_ne hρ, e, Units.val_one, (M.ds ρ).2.2.1.1.1]
        rfl
    have e0 : T0 (PiTensorProduct.tprod ℂ (Function.update v τ u)) =
        actP (LaP G) k (T0 (PiTensorProduct.tprod ℂ v)) := by
      rw [hT0, hT0]
      refine Eq.trans ?_ (actTen ℂ _ _ (LaP G) k _).symm
      congr 1
      funext ρ
      rw [hup, h3 ρ _ (hk ρ)]
    have e1 : T1 (PiTensorProduct.tprod ℂ (Function.update v τ u)) =
        actP (LaP G) Gh (T1 (PiTensorProduct.tprod ℂ v)) := by
      rw [hT1, hT1, e0]
      exact polyAction_conj (LaP G) B Gh _
    obtain ⟨x, rfl⟩ := (GlobalTheory.CoefModel.toHilb (LaP G) hP).surjective w
    calc _ = pairB (LaP G) (actP (LaP G) (invTrK Gh) x.1) (actP (LaP G) Gh (T1 (PiTensorProduct.tprod ℂ v))) := by
          rw [← e1]
          rfl
      _ = pairB (LaP G) x.1 (T1 (PiTensorProduct.tprod ℂ v)) := pairingBInvariantK_holds ℂ _ _ (LaP G) Gh _ _
      _ = _ := rfl

end GlobalTheory.TopCoefPair
