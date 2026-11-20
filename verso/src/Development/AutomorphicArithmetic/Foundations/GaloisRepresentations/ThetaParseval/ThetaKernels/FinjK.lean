import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.PrSingle
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.LagrangianProjectionFormula
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation PositivityTheory.ThKW.PhaseFourierInjectivity
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
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
theorem PositivityTheory.ThKW.PhaseFourierInjectivity.finj_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
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
end
