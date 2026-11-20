import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingPiCurry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialColumnFourierMemSchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialColumnFourierInversionSchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialColumnFourierEqFiniteFourierSumDepthStatement

namespace GlobalTheory.ColFourier
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
variable {A C : Type} [Fintype A] [DecidableEq C]

/- English proof (translation)
Use `haveI := hm.1`. Use `haveI := secondCountable k`. Use `haveI := isAddHaarMeasure_volM m (A := A) P`. Use `haveI : BorelSpace (Matrix A P k) := inferInstanceAs (BorelSpace (A → P → k))`. Establish `hi : ∀ Ξ ∈ SB (Matrix A C k), ∀ Y : Matrix A C k, Integrable (fun U => Ξ (setCols P Y U) * (ψ (pairCols P Y U) : ℂ)) (volM m A P)`.

Introduce `Ξ hΞ Y`. Establish `hg` using `comp_setCols_mem_SB hΞ P Y`. Establish `hc : Continuous fun U : Matrix A P k => pairCols P Y U` using `by unfold pairCols; fun_prop`. Conclude with `(hg.1.continuous.integrable_of_hasCompactSupport hg.2).mul_bdd (c := 1) ((continuous_subtype_val.comp (hψ.continuous.comp hc)).aestronglyMeasurable) (Filter.Eventually.of_forall fun U => (Circle.norm_coe _).le)`. Use function extensionality and compare the values at `Y`.

Simplify using `only [fourierInt, Pi.add_apply, add_mul]`. Conclude with `integral_add (hi _ h₁ Y) (hi _ h₂ Y)`.
-/
theorem fourierInt_add (ψ : AddChar k Circle) (m : Measure k) (hψ : HasConductor ψ 1) (hm : IsUnitVol m)
    (P : Finset C) {Ξ₁ Ξ₂ : Matrix A C k → ℂ} (h₁ : Ξ₁ ∈ SB (Matrix A C k)) (h₂ : Ξ₂ ∈ SB (Matrix A C k)) :
    fourierInt ψ m P (Ξ₁ + Ξ₂) = fourierInt ψ m P Ξ₁ + fourierInt ψ m P Ξ₂ := by
  haveI := hm.1
  haveI := secondCountable k
  haveI := isAddHaarMeasure_volM m (A := A) P
  haveI : BorelSpace (Matrix A P k) := inferInstanceAs (BorelSpace (A → P → k))
  have hi : ∀ Ξ ∈ SB (Matrix A C k), ∀ Y : Matrix A C k,
      Integrable (fun U => Ξ (setCols P Y U) * (ψ (pairCols P Y U) : ℂ)) (volM m A P) := by
    intro Ξ hΞ Y
    have hg := comp_setCols_mem_SB hΞ P Y
    have hc : Continuous fun U : Matrix A P k => pairCols P Y U := by unfold pairCols; fun_prop
    exact (hg.1.continuous.integrable_of_hasCompactSupport hg.2).mul_bdd (c := 1)
      ((continuous_subtype_val.comp (hψ.continuous.comp hc)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun U => (Circle.norm_coe _).le)
  funext Y
  simp only [fourierInt, Pi.add_apply, add_mul]
  exact integral_add (hi _ h₁ Y) (hi _ h₂ Y)

/- English proof (translation)
Use `haveI := hm.1`. Use `haveI := isAddHaarMeasure_volM m (A := A) P`. Use `haveI : MeasurableAdd (Matrix A P k) := inferInstanceAs (MeasurableAdd (A → P → k))`. Use function extensionality and compare the values at `Z`. Unfold `fourierInt`.

Use `set Tp := restrictCols P T`. Rewrite using `[← integral_add_right_eq_self (μ := volM m A P) (fun U => Ξ (setCols P Z U) * (ψ (pairCols P Z U) : ℂ)) Tp, ← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `U`. Establish `ea : GlobalTheory.FlipMatch.pairM (setCols P Z U) R = GlobalTheory.FlipMatch.pairM Z R`.

Simplify using `only [GlobalTheory.FlipMatch.pairM]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : j ∈ P`. Simplify using `[setCols, h, hR i j h]`. Simplify using `[setCols, h]`.

Establish `eb : setCols P Z U + T = setCols P Z (U + Tp)`. Use extensionality with `i j`. Distinguish the cases in `h : j ∈ P`. Simplify using `[setCols, h, Tp, restrictCols]`. Simplify using `[setCols, h, hT i j h]`.

Establish `ec : pairCols P Z (U + Tp) = pairCols P Z U + GlobalTheory.FlipMatch.pairM Z T`. Simplify using `only [pairCols, GlobalTheory.FlipMatch.pairM, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_subset (Finset.subset_univ P) (fun j _ hj => by simp [hT i j hj]), ← Finset.sum_coe_sort P, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `[Tp, restrictCols]`. Expand and normalize the polynomial expressions, which then agree. Establish `key : (ψ (GlobalTheory.FlipMatch.pairM Z R - GlobalTheory.FlipMatch.pairM Z T) : ℂ) * ψ (pairCols P Z U + GlobalTheory.FlipMatch.pairM Z T) = ψ (GlobalTheory.FlipMatch.pairM Z R) * ψ (pairCols P Z U)`. Rewrite using `[← Circle.coe_mul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only`. Rewrite using `[ea, eb, ec]`. Take the linear combination `(Ξ (setCols P Z (U + Tp))) * key.symm`.
-/
theorem fourierInt_shift [Fintype C] (ψ : AddChar k Circle) (m : Measure k) (hm : IsUnitVol m) (P : Finset C)
    (Ξ : Matrix A C k → ℂ) (T R : Matrix A C k) (hT : ∀ r, ∀ s ∉ P, T r s = 0) (hR : ∀ r, ∀ s ∈ P, R r s = 0) :
    fourierInt ψ m P (fun S => (ψ (GlobalTheory.FlipMatch.pairM S R) : ℂ) * Ξ (S + T)) =
      fun Z => (ψ (GlobalTheory.FlipMatch.pairM Z R - GlobalTheory.FlipMatch.pairM Z T) : ℂ) * fourierInt ψ m P Ξ Z := by
  haveI := hm.1
  haveI := isAddHaarMeasure_volM m (A := A) P
  haveI : MeasurableAdd (Matrix A P k) := inferInstanceAs (MeasurableAdd (A → P → k))
  funext Z
  unfold fourierInt
  set Tp := restrictCols P T
  rw [← integral_add_right_eq_self (μ := volM m A P)
    (fun U => Ξ (setCols P Z U) * (ψ (pairCols P Z U) : ℂ)) Tp, ← integral_const_mul]
  congr 1
  funext U
  have ea : GlobalTheory.FlipMatch.pairM (setCols P Z U) R = GlobalTheory.FlipMatch.pairM Z R := by
    simp only [GlobalTheory.FlipMatch.pairM]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : j ∈ P
    · simp [setCols, h, hR i j h]
    · simp [setCols, h]
  have eb : setCols P Z U + T = setCols P Z (U + Tp) := by
    ext i j
    by_cases h : j ∈ P
    · simp [setCols, h, Tp, restrictCols]
    · simp [setCols, h, hT i j h]
  have ec : pairCols P Z (U + Tp) = pairCols P Z U + GlobalTheory.FlipMatch.pairM Z T := by
    simp only [pairCols, GlobalTheory.FlipMatch.pairM, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_subset (Finset.subset_univ P) (fun j _ hj => by simp [hT i j hj]),
      ← Finset.sum_coe_sort P, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Tp, restrictCols]
    ring
  have key : (ψ (GlobalTheory.FlipMatch.pairM Z R - GlobalTheory.FlipMatch.pairM Z T) : ℂ) *
      ψ (pairCols P Z U + GlobalTheory.FlipMatch.pairM Z T) = ψ (GlobalTheory.FlipMatch.pairM Z R) * ψ (pairCols P Z U) := by
    rw [← Circle.coe_mul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 2; ring
  dsimp only
  rw [ea, eb, ec]
  linear_combination (Ξ (setCols P Z (U + Tp))) * key.symm

end GlobalTheory.ColFourier

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

/- English proof (translation)
Introduce `k _ _ _ _ A _ _ C _ _ ψ ϖ P hϖ hψ`. Use `borelize k`. Take `⟨m, hm⟩` from `exists_isUnitVol k`. Use `haveI := hm.1`. Establish `hψ' : HasConductor ψ⁻¹ 1` using `GlobalTheory.ColFourier.hasConductor_inv hψ`.

Establish `hSB` using `fun (χ : AddChar k Circle) (hχ : HasConductor χ 1) (Ξ : Matrix A C k → ℂ) (h : Ξ ∈ SB (Matrix A C k)) => GlobalTheory.T.partialColumnFourier_mem_schwartzBruhat k A C χ m hχ hm P Ξ h`. Establish `hInv` using `fun (χ : AddChar k Circle) (hχ : HasConductor χ 1) (Ξ : Matrix A C k → ℂ) (h : Ξ ∈ SB (Matrix A C k)) => GlobalTheory.T.partialColumnFourier_inversion_schwartzBruhat k A C χ m hχ hm P Ξ h`. Set `L : SB (Matrix A C k) →ₗ[ℂ] (Matrix A C k → ℂ)` to `{ toFun := fun Ξ => fourierInt ψ m P Ξ map_add' := fun a b => GlobalTheory.ColFourier.fourierInt_add ψ m hψ hm P a.2 b.2 map_smul' := fun c a => by`. Use function extensionality and compare the values at `Y`. Simplify using `only [SetLike.val_smul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul, fourierInt]`.

Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `U`. Use `ring }`. Take `⟨F, hF⟩` from `LinearMap.exists_extend L`.

Establish `hFe : ∀ Ξ ∈ SB (Matrix A C k), F Ξ = fourierInt ψ m P Ξ` using `fun Ξ h => LinearMap.congr_fun hF ⟨Ξ, h⟩`. Establish `hmod : ∀ Ξ ∈ SB (Matrix A C k), ∀ T R : Matrix A C k, (fun S => (ψ (pairM S R) : ℂ) * Ξ (S + T)) ∈ SB (Matrix A C k)`. Introduce `Ξ hΞ T R`. Establish `hc : Continuous fun S : Matrix A C k => pairM S R` using `by unfold pairM; fun_prop`. Use `⟨((hψ.isLocallyConstant.comp_continuous hc).comp (fun z : Circle => (z : ℂ))).mul (hΞ.1.comp_continuous (continuous_add_right T)), ?_⟩` and prove the remaining obligations.

Conclude with `(hΞ.2.comp_homeomorph (Homeomorph.addRight T)).mul_left`. Use `⟨F, ⟨fun Ξ h => ?_, fun Ξ₁ h₁ Ξ₂ h₂ he => ?_, fun Ψ hΨ => ?_⟩, fun Ξ hΞ T R hT hR => ?_, fun Ξ hΞ T R hT hR => ?_, fun Ξ hΞ n hn => ?_⟩` and prove the remaining obligations. Use `show F Ξ ∈ SB (Matrix A C k)`. Rewrite using `[hFe Ξ h]`. Conclude with `hSB ψ hψ Ξ h`.

Rewrite `he` using `[hFe _ h₁, hFe _ h₂]`. Rewrite using `[← hInv ψ hψ Ξ₁ h₁, ← hInv ψ hψ Ξ₂ h₂, he]`. Establish `h1` using `hSB ψ⁻¹ hψ' Ψ hΨ`. Use `⟨_, h1, ?_⟩` and prove the remaining obligations. Rewrite using `[hFe _ h1]`.

Simplify `hInv ψ⁻¹ hψ' Ψ hΨ` using `only [inv_inv]`. Rewrite using `[hFe _ (hmod Ξ hΞ T R), hFe _ hΞ]`. Use function extensionality and compare the values at `Z`. Unfold `fourierInt`. Use `congr 1`.

Use function extensionality and compare the values at `U`. Establish `e1 : setCols P Z U + T = setCols P (Z + (T + R)) U`. Use extensionality with `i j`. Distinguish the cases in `h : j ∈ P`. Simplify using `[setCols, h, hT i j h]`.

Simplify using `[setCols, h, hR i j h]`. Establish `e2 : pairM (setCols P Z U) R + pairCols P Z U = pairCols P (Z + (T + R)) U`. Simplify using `only [pairM, pairCols, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_subset (Finset.subset_univ P) (fun j _ hj => by simp [setCols, hj, hR i j hj]), ← Finset.sum_coe_sort P, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `[setCols, j.2, hT i j j.2]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only`. Rewrite using `[e1, ← e2, AddChar.map_add_eq_mul, Circle.coe_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hFe _ (hmod Ξ hΞ T R), hFe _ hΞ]`. Conclude with `GlobalTheory.ColFourier.fourierInt_shift ψ m hm P Ξ T R hT hR`. Rewrite `hn`, the goal using `[hFe _ hΞ]`. Rewrite using `[← GlobalTheory.T.partialColumnFourier_eq_finiteFourierSum_depth k A C ψ⁻¹ m ϖ hϖ hψ' hm P n _ hn]`.

Conclude with `hInv ψ hψ Ξ hΞ`.
-/
theorem GlobalTheory.ColFourier.exists_blockFourier : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A : Type) [Fintype A] [DecidableEq A] (C : Type) [Fintype C] [DecidableEq C] (ψ : AddChar k Circle) (ϖ : kˣ) (P : Finset C), IsUnif ϖ → HasConductor ψ 1 →
    ∃ 𝓕 : (Matrix A C k → ℂ) →ₗ[ℂ] (Matrix A C k → ℂ), Set.BijOn 𝓕 (GlobalTheory.WeilM.SB (Matrix A C k) : Set _) (GlobalTheory.WeilM.SB (Matrix A C k) : Set _) ∧
      (∀ Ξ ∈ GlobalTheory.WeilM.SB (Matrix A C k), ∀ T R : Matrix A C k, (∀ r, ∀ s ∈ P, T r s = 0) → (∀ r, ∀ s ∉ P, R r s = 0) →
        𝓕 (fun S => (ψ (pairM S R) : ℂ) * Ξ (S + T)) = fun Z => 𝓕 Ξ (Z + (T + R))) ∧
      (∀ Ξ ∈ GlobalTheory.WeilM.SB (Matrix A C k), ∀ T R : Matrix A C k, (∀ r, ∀ s ∉ P, T r s = 0) → (∀ r, ∀ s ∈ P, R r s = 0) →
        𝓕 (fun S => (ψ (pairM S R) : ℂ) * Ξ (S + T)) = fun Z => (ψ (pairM Z R - pairM Z T) : ℂ) * 𝓕 Ξ Z) ∧
      ∀ Ξ ∈ GlobalTheory.WeilM.SB (Matrix A C k), ∀ n, IsNatDatum ϖ n (𝓕 Ξ) → fourierSum ψ⁻¹ ϖ n P (𝓕 Ξ) = Ξ := by
  intro k _ _ _ _ A _ _ C _ _ ψ ϖ P hϖ hψ
  borelize k
  obtain ⟨m, hm⟩ := exists_isUnitVol k
  haveI := hm.1
  have hψ' : HasConductor ψ⁻¹ 1 := GlobalTheory.ColFourier.hasConductor_inv hψ
  have hSB := fun (χ : AddChar k Circle) (hχ : HasConductor χ 1) (Ξ : Matrix A C k → ℂ)
    (h : Ξ ∈ SB (Matrix A C k)) => GlobalTheory.T.partialColumnFourier_mem_schwartzBruhat k A C χ m hχ hm P Ξ h
  have hInv := fun (χ : AddChar k Circle) (hχ : HasConductor χ 1) (Ξ : Matrix A C k → ℂ)
    (h : Ξ ∈ SB (Matrix A C k)) => GlobalTheory.T.partialColumnFourier_inversion_schwartzBruhat k A C χ m hχ hm P Ξ h
  let L : SB (Matrix A C k) →ₗ[ℂ] (Matrix A C k → ℂ) :=
    { toFun := fun Ξ => fourierInt ψ m P Ξ
      map_add' := fun a b => GlobalTheory.ColFourier.fourierInt_add ψ m hψ hm P a.2 b.2
      map_smul' := fun c a => by
        funext Y
        simp only [SetLike.val_smul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul, fourierInt]
        rw [← integral_const_mul]
        congr 1; funext U; ring }
  obtain ⟨F, hF⟩ := LinearMap.exists_extend L
  have hFe : ∀ Ξ ∈ SB (Matrix A C k), F Ξ = fourierInt ψ m P Ξ := fun Ξ h => LinearMap.congr_fun hF ⟨Ξ, h⟩
  have hmod : ∀ Ξ ∈ SB (Matrix A C k), ∀ T R : Matrix A C k,
      (fun S => (ψ (pairM S R) : ℂ) * Ξ (S + T)) ∈ SB (Matrix A C k) := by
    intro Ξ hΞ T R
    have hc : Continuous fun S : Matrix A C k => pairM S R := by unfold pairM; fun_prop
    refine ⟨((hψ.isLocallyConstant.comp_continuous hc).comp (fun z : Circle => (z : ℂ))).mul
      (hΞ.1.comp_continuous (continuous_add_right T)), ?_⟩
    exact (hΞ.2.comp_homeomorph (Homeomorph.addRight T)).mul_left
  refine ⟨F, ⟨fun Ξ h => ?_, fun Ξ₁ h₁ Ξ₂ h₂ he => ?_, fun Ψ hΨ => ?_⟩, fun Ξ hΞ T R hT hR => ?_,
    fun Ξ hΞ T R hT hR => ?_, fun Ξ hΞ n hn => ?_⟩
  · show F Ξ ∈ SB (Matrix A C k)
    rw [hFe Ξ h]; exact hSB ψ hψ Ξ h
  · rw [hFe _ h₁, hFe _ h₂] at he
    rw [← hInv ψ hψ Ξ₁ h₁, ← hInv ψ hψ Ξ₂ h₂, he]
  · have h1 := hSB ψ⁻¹ hψ' Ψ hΨ
    refine ⟨_, h1, ?_⟩
    rw [hFe _ h1]
    simpa only [inv_inv] using hInv ψ⁻¹ hψ' Ψ hΨ
  · rw [hFe _ (hmod Ξ hΞ T R), hFe _ hΞ]
    funext Z
    unfold fourierInt
    congr 1
    funext U
    have e1 : setCols P Z U + T = setCols P (Z + (T + R)) U := by
      ext i j
      by_cases h : j ∈ P
      · simp [setCols, h, hT i j h]
      · simp [setCols, h, hR i j h]
    have e2 : pairM (setCols P Z U) R + pairCols P Z U = pairCols P (Z + (T + R)) U := by
      simp only [pairM, pairCols, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_subset (Finset.subset_univ P) (fun j _ hj => by simp [setCols, hj, hR i j hj]),
        ← Finset.sum_coe_sort P, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [setCols, j.2, hT i j j.2]
      ring
    dsimp only
    rw [e1, ← e2, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  · rw [hFe _ (hmod Ξ hΞ T R), hFe _ hΞ]
    exact GlobalTheory.ColFourier.fourierInt_shift ψ m hm P Ξ T R hT hR
  · rw [hFe _ hΞ] at hn ⊢
    rw [← GlobalTheory.T.partialColumnFourier_eq_finiteFourierSum_depth k A C ψ⁻¹ m ϖ hϖ hψ' hm P n _ hn]
    exact hInv ψ hψ Ξ hΞ
