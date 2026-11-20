import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridCoreIffFirstRowExtByZero

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

noncomputable section

namespace GlobalTheory.ConjSchr

variable {D : D7}

/- English proof (translation)
Simplify using `only [symplO, hO, GlobalTheory.ChiGrid.negSp_gram, GlobalTheory.CjNeg.inv_neg_mat, Matrix.neg_apply, map_neg, neg_mul, mul_neg, Finset.sum_neg_distrib]`.
-/
theorem symplO_negS (S T : HSp D) (x y : WO S T) :
    symplO (GlobalTheory.ChiGrid.negSp S) T x y = -symplO S T x y := by
  simp only [symplO, hO, GlobalTheory.ChiGrid.negSp_gram, GlobalTheory.CjNeg.inv_neg_mat, Matrix.neg_apply, map_neg, neg_mul, mul_neg,
    Finset.sum_neg_distrib]

def cjF {X : Type} (g : X → ℂ) : X → ℂ := fun w => starRingEnd ℂ (g w)

/- English proof (translation)
Use function extensionality and compare the values at `w`. Simplify using `only [cjF, heisO, map_mul, GlobalTheory.CjNeg.conj_psi hψ, GlobalTheory.CjNeg.symplOH_negS, neg_neg]`.
-/
theorem heisO_conj {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (x : WO S T)
    (g : WO S T → ℂ) :
    heisO ψ S T x (cjF g) = cjF (heisO ψ (GlobalTheory.ChiGrid.negSp S) T x g) := by
  funext w
  simp only [cjF, heisO, map_mul, GlobalTheory.CjNeg.conj_psi hψ, GlobalTheory.CjNeg.symplOH_negS, neg_neg]

/- English proof (translation)
Use function extensionality and compare the values at `w`. Simplify using `[cjF]`.
-/
theorem cjF_cjF {X : Type} (g : X → ℂ) : cjF (cjF g) = g := by
  funext w; simp [cjF]

def conjLin {X : Type} (T : (X → ℂ) →ₗ[ℂ] (X → ℂ)) : (X → ℂ) →ₗ[ℂ] (X → ℂ) where
  toFun g := cjF (T (cjF g))
  map_add' g h := by
    have : cjF (g + h) = cjF g + cjF h := by funext w; simp [cjF]
    funext w; simp [this, cjF]
  map_smul' c g := by
    have : cjF (c • g) = starRingEnd ℂ c • cjF g := by funext w; simp [cjF]
    funext w; simp [this, cjF]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conjLin_apply {X : Type} (T : (X → ℂ) →ₗ[ℂ] (X → ℂ)) (g : X → ℂ) :
    conjLin T g = cjF (T (cjF g)) := rfl

/- English proof (translation)
Take `⟨hs, k, hk, hinv, hsupp⟩` from `h`. Use `⟨fun t ht => hs t ?_, k, hk, fun u hu hue t => ?_, fun t ht => hsupp t ?_⟩` and prove the remaining obligations. Introduce `h0`. Apply `ht` to reduce the goal to its premises. Simplify using `[cjF, h0]`.

Simplify using `only [cjF, hinv u hu hue t]`. Introduce `h0`. Apply `ht` to reduce the goal to its premises. Simplify using `[cjF, h0]`.
-/
theorem isSBHalf_cjF {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {Φ : Mx D m n → ℂ}
    (h : IsSBHalf e Λ Φ) : IsSBHalf e Λ (cjF Φ) := by
  obtain ⟨hs, k, hk, hinv, hsupp⟩ := h
  refine ⟨fun t ht => hs t ?_, k, hk, fun u hu hue t => ?_, fun t ht => hsupp t ?_⟩
  · intro h0; apply ht; simp [cjF, h0]
  · simp only [cjF, hinv u hu hue t]
  · intro h0; apply ht; simp [cjF, h0]

/- English proof (translation)
Establish `e1` using `h.trans _ (isSBHalf_cjF hΦ) x hx`. Rewrite using `[conjLin_apply, conjLin_apply, heisO_conj hψ]`. Establish `e2 : cjF (fun t => Φ (t + x)) = fun t => cjF Φ (t + x)` using `rfl`. Rewrite using `[e2, e1]`. Use `modul Φ hΦ y hy := by`.

Establish `e1` using `h.modul _ (isSBHalf_cjF hΦ) y hy`. Rewrite using `[conjLin_apply, conjLin_apply, heisO_conj hψ]`. Establish `e2 : cjF (fun t => ψ (symplO S T t y) * Φ t) = fun t => ψ (symplO (GlobalTheory.ChiGrid.negSp S) T t y) * cjF Φ t`. Use function extensionality and compare the values at `t`. Simplify using `only [cjF, map_mul, GlobalTheory.CjNeg.conj_psi hψ, symplO_negS]`.

Rewrite using `[e2, e1]`. Use `vac := by`. Establish `e2 : cjF ((1 : ℂ) • halfInd e Λ) = (1 : ℂ) • halfInd e Λ`. Apply the tactic sequence `funext t; simp only [cjF, one_smul, halfInd]; split_ifs <;> simp`. Rewrite using `[conjLin_apply, e2, h.vac]`.
-/
theorem isPlaceModel_conjLin {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {e : AE D}
    {Λ : AddSubgroup (WO S T)} {f₀ : WO S T → ℂ} {T₀ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (h : IsPlaceModel ψ (symplO (GlobalTheory.ChiGrid.negSp S) T) (heisO ψ (GlobalTheory.ChiGrid.negSp S) T) e Λ 1 f₀ T₀) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 (cjF f₀) (conjLin T₀) where
  trans Φ hΦ x hx := by
    have e1 := h.trans _ (isSBHalf_cjF hΦ) x hx
    rw [conjLin_apply, conjLin_apply, heisO_conj hψ]
    have e2 : cjF (fun t => Φ (t + x)) = fun t => cjF Φ (t + x) := rfl
    rw [e2, e1]
  modul Φ hΦ y hy := by
    have e1 := h.modul _ (isSBHalf_cjF hΦ) y hy
    rw [conjLin_apply, conjLin_apply, heisO_conj hψ]
    have e2 : cjF (fun t => ψ (symplO S T t y) * Φ t) =
        fun t => ψ (symplO (GlobalTheory.ChiGrid.negSp S) T t y) * cjF Φ t := by
      funext t; simp only [cjF, map_mul, GlobalTheory.CjNeg.conj_psi hψ, symplO_negS]
    rw [e2, e1]
  vac := by
    have e2 : cjF ((1 : ℂ) • halfInd e Λ) = (1 : ℂ) • halfInd e Λ := by
      funext t; simp only [cjF, one_smul, halfInd]; split_ifs <;> simp
    rw [conjLin_apply, e2, h.vac]

end GlobalTheory.ConjSchr

open GlobalTheory.ConjSchr in
/- English proof (translation)
Introduce `D ψ hψ A WW e ΛA ΛW vac Φ f hT`. Establish `hL : latO (GlobalTheory.Grid.neg A) WW ΛA ΛW (fun _ => True) = latO A WW ΛA ΛW (fun _ => True)` using `GlobalTheory.CoreRowLat.latO_negSp A WW ΛA ΛW _`. Take `⟨⟨T₀, h0⟩, hall⟩` from `hT`. Establish `hf : f = T₀ Φ` using `hall T₀ h0`. Rewrite `h0` using `[hL]`.

Use `⟨conjLin T₀, isPlaceModel_conjLin hψ h0, ?_⟩` and prove the remaining obligations. Use `show cjF f = conjLin T₀ (cjF Φ)`. Rewrite using `[conjLin_apply, cjF_cjF, hf]`.
-/
theorem GlobalTheory.ConjSchr.conj_schroedinger_neg : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A WW : HSp D) (e : AE D) (ΛA : Set (Fin A.rank → D.host.E))
  (ΛW : Set (Fin WW.rank → D.host.E)) (vac Φ f : WO A WW → ℂ),
  IsThetaAt ψ (symplO (GlobalTheory.Grid.neg A) WW) (heisO ψ (GlobalTheory.Grid.neg A) WW) e (latO (GlobalTheory.Grid.neg A) WW ΛA ΛW fun _ => True) 1 vac Φ f →
  ∃ Tm : (WO A WW → ℂ) →ₗ[ℂ] (WO A WW → ℂ),
    IsPlaceModel ψ (symplO A WW) (heisO ψ A WW) e (latO A WW ΛA ΛW fun _ => True) 1 (fun w => starRingEnd ℂ (vac w)) Tm ∧
      (fun w => starRingEnd ℂ (f w)) = Tm (fun w => starRingEnd ℂ (Φ w)) := by
  intro D ψ hψ A WW e ΛA ΛW vac Φ f hT
  have hL : latO (GlobalTheory.Grid.neg A) WW ΛA ΛW (fun _ => True) = latO A WW ΛA ΛW (fun _ => True) :=
    GlobalTheory.CoreRowLat.latO_negSp A WW ΛA ΛW _
  obtain ⟨⟨T₀, h0⟩, hall⟩ := hT
  have hf : f = T₀ Φ := hall T₀ h0
  rw [hL] at h0
  refine ⟨conjLin T₀, isPlaceModel_conjLin hψ h0, ?_⟩
  show cjF f = conjLin T₀ (cjF Φ)
  rw [conjLin_apply, cjF_cjF, hf]
