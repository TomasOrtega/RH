import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAdaptedProjectionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfAdelicFourierSeparatingCharsVanishStatement
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Mfac
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DCdE
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.IntegralMul
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.LagrangianProjectionFormula

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation PositivityTheory.ThKW.PhaseFourierInjectivity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def pr (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (ξ₀ : E) (y : WOF F E nS nT) :
    (Fin (nT * nS) → AF F ⊗[F] E) →ₗ[AF F] AF F where
  toFun u := Algebra.trace (AF F) (AF F ⊗[F] E)
    (incAF F E ξ₀ * (JS⁻¹.map (incAF F E) * ((y.map (cAF σ))ᵀ * (vecE F E nS nT).symm u)).trace)
  map_add' u u' := by
    rw [map_add, Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, mul_add, map_add]
  map_smul' r u := by
    have e : (vecE F E nS nT).symm (r • u) = r • (vecE F E nS nT).symm u := rfl
    rw [e, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul, mul_smul_comm, map_smul, RingHom.id_apply]

/- English proof (translation)
Use `LinearMap.ext fun u => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Algebra.trace (AF F) (AF F ⊗[F] E) (incAF F E ξ₀ * (JS⁻¹.map (incAF F E) * (((y + y').map (cAF σ))ᵀ * (vecE F E nS nT).symm u)).trace) = Algebra.trace (AF F) (AF F ⊗[F] E) (incAF F E ξ₀ * (JS⁻¹.map (incAF F E) * ((y.map (cAF σ))ᵀ * (vecE F E nS nT).symm u)).trace) + Algebra.trace …`. Rewrite using `[Matrix.map_add _ (map_add _), Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add, mul_add, map_add]`.
-/
theorem pr_add (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (ξ₀ : E) (y y' : WOF F E nS nT) :
    pr σ JS ξ₀ (y + y') = pr σ JS ξ₀ y + pr σ JS ξ₀ y' := by
  refine LinearMap.ext fun u => ?_
  change Algebra.trace (AF F) (AF F ⊗[F] E) (incAF F E ξ₀ * (JS⁻¹.map (incAF F E) *
      (((y + y').map (cAF σ))ᵀ * (vecE F E nS nT).symm u)).trace) =
    Algebra.trace (AF F) (AF F ⊗[F] E) (incAF F E ξ₀ * (JS⁻¹.map (incAF F E) *
      ((y.map (cAF σ))ᵀ * (vecE F E nS nT).symm u)).trace) +
    Algebra.trace (AF F) (AF F ⊗[F] E) (incAF F E ξ₀ * (JS⁻¹.map (incAF F E) *
      ((y'.map (cAF σ))ᵀ * (vecE F E nS nT).symm u)).trace)
  rw [Matrix.map_add _ (map_add _), Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add, mul_add,
    map_add]

/- English proof (translation)
Unfold `phase symplOF`. Rewrite using `[hOF_dual JS JT hT]`. Simplify using `only [pr, LinearMap.coe_mk, AddHom.coe_mk, AddEquiv.symm_apply_apply]`.
-/
theorem phase_eq (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (hT : JT.det ≠ 0) (ξ₀ : E) (ψ : AddChar (AF F) ℂ) (y v : WOF F E nS nT) :
    phase σ JS JT ξ₀ ψ y v = ψ (pr σ JS ξ₀ y (vecE F E nS nT v)) := by
  unfold phase symplOF
  rw [hOF_dual JS JT hT]
  simp only [pr, LinearMap.coe_mk, AddHom.coe_mk, AddEquiv.symm_apply_apply]

/- English proof (translation)
Simplify using `only [pr, LinearMap.coe_mk, AddHom.coe_mk, AddEquiv.symm_apply_apply]`. Use `congr 1`. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, apply_ite (cAF σ), map_zero, hcc, ite_mul, zero_mul, ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]`. Simplify using `only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pr_single (σ : E →ₐ[F] E) (hcc : ∀ z : AF F ⊗[F] E, cAF σ (cAF σ z) = z) {nS nT : ℕ}
    (JS : Matrix (Fin nS) (Fin nS) E) (ξ₀ : E) (v : WOF F E nS nT) (k : Fin nT) (b : Fin nS) (z : AF F ⊗[F] E) :
    pr σ JS ξ₀ (Matrix.of fun i j => if i = k ∧ j = b then cAF σ z else 0) (vecE F E nS nT v) =
      Algebra.trace (AF F) (AF F ⊗[F] E) (incAF F E ξ₀ * (v * JS⁻¹.map (incAF F E)) k b * z) := by
  simp only [pr, LinearMap.coe_mk, AddHom.coe_mk, AddEquiv.symm_apply_apply]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply,
    apply_ite (cAF σ), map_zero, hcc, ite_mul, zero_mul, ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.mul_sum]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/- English proof (translation)
Use `set v := (vecE F E nS nT).symm u with hv`. Establish `hu : u = vecE F E nS nT v` using `by rw [hv, AddEquiv.apply_symm_apply]`. Establish `hw : ∀ k b, (v * JS⁻¹.map (incAF F E)) k b = 0`. Introduce `k b`. Establish `h0 : incAF F E ξ₀ * (v * JS⁻¹.map (incAF F E)) k b = 0`.

Apply `GlobalTheory.DblSiegelChar.eq_zero_of_psi_trace hψ` to reduce the goal to its premises. Introduce `t`. Use `h (Matrix.of fun i j => if i = k ∧ j = b then cAF σ t else 0)` as an intermediate fact. Rewrite `this` using `[hu, pr_single σ hcc]`. Then use the resulting hypothesis. Establish `hunit : IsUnit (incAF F E ξ₀)` using `(IsUnit.mk0 ξ₀ hξ₀).map (incAF F E)`.

Conclude with `hunit.mul_right_eq_zero.1 h0`. Establish `e1 : v * JS⁻¹.map (incAF F E) = 0`. Use extensionality with `k b`. Conclude with `hw k b`. Establish `e2 : JS⁻¹.map (incAF F E) * JS.map (incAF F E) = 1`.

Rewrite using `[← Matrix.map_mul, Matrix.nonsing_inv_mul JS (Ne.isUnit hS), Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hv0 : v = 0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hu, hv0, map_zero]`.
-/
theorem pr_sep (σ : E →ₐ[F] E) (hcc : ∀ z : AF F ⊗[F] E, cAF σ (cAF σ z) = z) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (hS : JS.det ≠ 0) (ξ₀ : E) (hξ₀ : ξ₀ ≠ 0)
    (u : Fin (nT * nS) → AF F ⊗[F] E) (h : ∀ y : WOF F E nS nT, ψ (pr σ JS ξ₀ y u) = 1) : u = 0 := by
  set v := (vecE F E nS nT).symm u with hv
  have hu : u = vecE F E nS nT v := by rw [hv, AddEquiv.apply_symm_apply]
  have hw : ∀ k b, (v * JS⁻¹.map (incAF F E)) k b = 0 := by
    intro k b
    have h0 : incAF F E ξ₀ * (v * JS⁻¹.map (incAF F E)) k b = 0 := by
      apply GlobalTheory.DblSiegelChar.eq_zero_of_psi_trace hψ
      intro t
      have := h (Matrix.of fun i j => if i = k ∧ j = b then cAF σ t else 0)
      rwa [hu, pr_single σ hcc] at this
    have hunit : IsUnit (incAF F E ξ₀) := (IsUnit.mk0 ξ₀ hξ₀).map (incAF F E)
    exact hunit.mul_right_eq_zero.1 h0
  have e1 : v * JS⁻¹.map (incAF F E) = 0 := by
    ext k b
    exact hw k b
  have e2 : JS⁻¹.map (incAF F E) * JS.map (incAF F E) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul JS (Ne.isUnit hS), Matrix.map_one _ (map_zero _) (map_one _)]
  have hv0 : v = 0 := by
    calc v = v * JS⁻¹.map (incAF F E) * JS.map (incAF F E) := by rw [Matrix.mul_assoc, e2, Matrix.mul_one]
      _ = 0 := by rw [e1, Matrix.zero_mul]
  rw [hu, hv0, map_zero]

end PositivityTheory.ThKW.LagrangianProjectionFormula

end

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation PositivityTheory.ThKW.PhaseFourierInjectivity PositivityTheory.ThKW.LagrangianProjectionFormula in
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 N₁ N₂ c₁ c₂ i₁ i₂ hN`. Establish `hψ : IsStd B.ψ` using `hB.std`. Establish `hψn : ∀ a, ‖B.ψ a‖ = 1` using `GlobalTheory.StdCharWeilDatum.norm_psi hB.std`. Establish `hcc : ∀ z : AF F ⊗[F] E, cAF σ (cAF σ z) = z`. Introduce `z`.

Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x => simp [cAF, sigR, GlobalTheory.DblSiegelChar.invol hB.cm]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`. Establish `he : Continuous (vecE F E nS nT)` using `by show Continuous fun (w : WOF F E nS nT) (k : Fin (nT * nS)) => w (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2`.

Conclude with `continuous_pi fun k => continuous_id.matrix_elem _ _`. Establish `he' : Continuous (vecE F E nS nT).symm` using `by show Continuous fun (u : Fin (nT * nS) → AF F ⊗[F] E) => ((fun i j => u (finProdFinEquiv (i, j))) : WOF F E nS nT) first`. Consider the case `exact continuous_pi fun i => continuous_pi fun j => continuous_apply _`. Consider the case `fun_prop`. Use `haveI : IsTopologicalAddGroup (AF F ⊗[F] E) := IsModuleTopology.topologicalAddGroup (AF F) (AF F ⊗[F] E)`.

Set `E' : WOF F E nS nT ≃ₜ+ (Fin (nT * nS) → AF F ⊗[F] E)` to `{ toAddEquiv := vecE F E nS nT, continuous_toFun := he, continuous_invFun := he' }`. Use `letI : MeasurableSpace (Fin (nT * nS) → AF F ⊗[F] E) := borel _`. Use `haveI : BorelSpace (Fin (nT * nS) → AF F ⊗[F] E) := ⟨rfl⟩`. Use `haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩`. Set `em : WOF F E nS nT ≃ᵐ (Fin (nT * nS) → AF F ⊗[F] E)` to `E'.toHomeomorph.toMeasurableEquiv`.

Use `haveI := hν`. Establish `hμ : (ν.map em).IsAddHaarMeasure` using `ContinuousAddEquiv.isAddHaarMeasure_map ν E'`. Establish `hpc : ∀ a : WOF F E nS nT, Continuous (pr σ JS ξ₀ a)` using `fun a => IsModuleTopology.continuous_of_linearMap _`. Establish `hph : ∀ a, Continuous (phase σ JS JT ξ₀ B.ψ a)`. Introduce `a`.

Establish `e : phase σ JS JT ξ₀ B.ψ a = fun v => B.ψ (pr σ JS ξ₀ a (vecE F E nS nT v))`. Use function extensionality and compare the values at `fun v => phase_eq σ JS JT hT.2 ξ₀ B.ψ a v`. Rewrite using `[e]`. Conclude with `hψ.1.comp ((hpc a).comp he)`. Establish `hint : ∀ a (N : WOF F E nS nT → ℂ), Integrable N ν → Integrable (fun v => phase σ JS JT ξ₀ B.ψ a v * N v) ν`.

Introduce `a N hNi`. Use `hNi.bdd_mul (c := 1) (hph a).aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)` and prove the remaining obligations. Rewrite using `[phase_eq σ JS JT hT.2, hψn]`. Use `set N : (Fin (nT * nS) → AF F ⊗[F] E) → ℂ := fun u => N₁ ((vecE F E nS nT).symm u) - N₂ ((vecE F E nS nT).symm u) with hNdef`. Establish `hNc : Continuous N` using `(c₁.comp he').sub (c₂.comp he')`.

Establish `hNi : Integrable N (ν.map em)`. Rewrite using `[integrable_map_equiv em N]`. Establish `: N ∘ em = fun v => N₁ v - N₂ v`. Use function extensionality and compare the values at `v`. Simplify using `only [hNdef, Function.comp_apply]`.

Rewrite using `[show (vecE F E nS nT).symm (em v) = v from (vecE F E nS nT).symm_apply_apply v]`. Rewrite using `[this]`. Conclude with `i₁.sub i₂`. Establish `key : ∀ a, ∫ u, B.ψ (pr σ JS ξ₀ a u) * N u ∂(ν.map em) = 0`. Introduce `a`.

Rewrite using `[integral_map_equiv em]`. Establish `hx : ∀ v, B.ψ (pr σ JS ξ₀ a (em v)) * N (em v) = phase σ JS JT ξ₀ B.ψ a v * N₁ v - phase σ JS JT ξ₀ B.ψ a v * N₂ v`. Introduce `v`. Establish `h1 : (vecE F E nS nT).symm (em v) = v` using `(vecE F E nS nT).symm_apply_apply v`. Establish `h2 : em v = vecE F E nS nT v` using `rfl`.

Simplify using `only [hNdef, h2, AddEquiv.symm_apply_apply]`. Rewrite using `[phase_eq σ JS JT hT.2]`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[hx]`. Rewrite using `[integral_sub (hint a N₁ i₁) (hint a N₂ i₂), hN a, sub_self]`.

Establish `h0` using `GlobalTheory.T.eq_zero_of_adelicFourier_separatingChars_vanish F E B.ψ hψ (nT * nS) (WOF F E nS nT) (pr σ JS ξ₀) (pr_add σ JS ξ₀) (fun u hu => pr_sep σ hcc hψ JS hS.2 ξ₀ hξ₀ u hu) (ν.map em) hμ N hNc hNi key`. Use function extensionality and compare the values at `v`. Use `congrFun h0 (vecE F E nS nT v)` as an intermediate fact. Simplify using `only [hNdef, AddEquiv.symm_apply_apply, Pi.zero_apply] at this`. Conclude with `sub_eq_zero.1 this`.
-/
theorem PositivityTheory.ThKW.PhaseFourierInjectivity.finj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
    ∀ N₁ N₂ : WOF F E nS nT → ℂ, Continuous N₁ → Continuous N₂ → Integrable N₁ ν → Integrable N₂ ν →
      (∀ y, ∫ v, phase σ JS JT ξ₀ B.ψ y v * N₁ v ∂ν = ∫ v, phase σ JS JT ξ₀ B.ψ y v * N₂ v ∂ν) → N₁ = N₂ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 N₁ N₂ c₁ c₂ i₁ i₂ hN
  have hψ : IsStd B.ψ := hB.std
  have hψn : ∀ a, ‖B.ψ a‖ = 1 := GlobalTheory.StdCharWeilDatum.norm_psi hB.std
  have hcc : ∀ z : AF F ⊗[F] E, cAF σ (cAF σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [cAF, sigR, GlobalTheory.DblSiegelChar.invol hB.cm]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have he : Continuous (vecE F E nS nT) := by
    show Continuous fun (w : WOF F E nS nT) (k : Fin (nT * nS)) => w (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
    exact continuous_pi fun k => continuous_id.matrix_elem _ _
  have he' : Continuous (vecE F E nS nT).symm := by
    show Continuous fun (u : Fin (nT * nS) → AF F ⊗[F] E) =>
      ((fun i j => u (finProdFinEquiv (i, j))) : WOF F E nS nT)
    first
      | exact continuous_pi fun i => continuous_pi fun j => continuous_apply _
      | fun_prop
  haveI : IsTopologicalAddGroup (AF F ⊗[F] E) := IsModuleTopology.topologicalAddGroup (AF F) (AF F ⊗[F] E)
  let E' : WOF F E nS nT ≃ₜ+ (Fin (nT * nS) → AF F ⊗[F] E) :=
    { toAddEquiv := vecE F E nS nT, continuous_toFun := he, continuous_invFun := he' }
  letI : MeasurableSpace (Fin (nT * nS) → AF F ⊗[F] E) := borel _
  haveI : BorelSpace (Fin (nT * nS) → AF F ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  let em : WOF F E nS nT ≃ᵐ (Fin (nT * nS) → AF F ⊗[F] E) := E'.toHomeomorph.toMeasurableEquiv
  haveI := hν
  have hμ : (ν.map em).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν E'
  have hpc : ∀ a : WOF F E nS nT, Continuous (pr σ JS ξ₀ a) := fun a => IsModuleTopology.continuous_of_linearMap _
  have hph : ∀ a, Continuous (phase σ JS JT ξ₀ B.ψ a) := by
    intro a
    have e : phase σ JS JT ξ₀ B.ψ a = fun v => B.ψ (pr σ JS ξ₀ a (vecE F E nS nT v)) :=
      funext fun v => phase_eq σ JS JT hT.2 ξ₀ B.ψ a v
    rw [e]
    exact hψ.1.comp ((hpc a).comp he)
  have hint : ∀ a (N : WOF F E nS nT → ℂ), Integrable N ν →
      Integrable (fun v => phase σ JS JT ξ₀ B.ψ a v * N v) ν := by
    intro a N hNi
    refine hNi.bdd_mul (c := 1) (hph a).aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)
    rw [phase_eq σ JS JT hT.2, hψn]
  set N : (Fin (nT * nS) → AF F ⊗[F] E) → ℂ := fun u => N₁ ((vecE F E nS nT).symm u) - N₂ ((vecE F E nS nT).symm u)
    with hNdef
  have hNc : Continuous N := (c₁.comp he').sub (c₂.comp he')
  have hNi : Integrable N (ν.map em) := by
    rw [integrable_map_equiv em N]
    have : N ∘ em = fun v => N₁ v - N₂ v := by
      funext v
      simp only [hNdef, Function.comp_apply]
      rw [show (vecE F E nS nT).symm (em v) = v from (vecE F E nS nT).symm_apply_apply v]
    rw [this]
    exact i₁.sub i₂
  have key : ∀ a, ∫ u, B.ψ (pr σ JS ξ₀ a u) * N u ∂(ν.map em) = 0 := by
    intro a
    rw [integral_map_equiv em]
    have hx : ∀ v, B.ψ (pr σ JS ξ₀ a (em v)) * N (em v) =
        phase σ JS JT ξ₀ B.ψ a v * N₁ v - phase σ JS JT ξ₀ B.ψ a v * N₂ v := by
      intro v
      have h1 : (vecE F E nS nT).symm (em v) = v := (vecE F E nS nT).symm_apply_apply v
      have h2 : em v = vecE F E nS nT v := rfl
      simp only [hNdef, h2, AddEquiv.symm_apply_apply]
      rw [phase_eq σ JS JT hT.2]
      ring
    simp_rw [hx]
    rw [integral_sub (hint a N₁ i₁) (hint a N₂ i₂), hN a, sub_self]
  have h0 := GlobalTheory.T.eq_zero_of_adelicFourier_separatingChars_vanish F E B.ψ hψ (nT * nS) (WOF F E nS nT) (pr σ JS ξ₀) (pr_add σ JS ξ₀)
    (fun u hu => pr_sep σ hcc hψ JS hS.2 ξ₀ hξ₀ u hu) (ν.map em) hμ N hNc hNi key
  funext v
  have := congrFun h0 (vecE F E nS nT v)
  simp only [hNdef, AddEquiv.symm_apply_apply, Pi.zero_apply] at this
  exact sub_eq_zero.1 this
