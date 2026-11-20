import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

/- English proof (translation)
Proceed by induction on `hp using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨i, w, rfl⟩` from `hx`. Use `Algebra.subset_adjoin ?_` and prove the remaining obligations. Use `fin_cases i`.

Conclude with `⟨0, w, rfl⟩`. Conclude with `⟨1, w, rfl⟩`. Consider the case `algebraMap r => exact Subalgebra.algebraMap_mem _ r`. Consider the case `add x y _ _ hx hy => exact add_mem hx hy`. Consider the case `mul x y _ _ hx hy => exact mul_mem hx hy`.
-/
private theorem poly_pull {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    {p : (Fin 2 → A F) → ℂ} (hp : p ∈ polyOn F (Fin 2)) :
    (fun v : V4 F => p ![v 0, v 1]) ∈ polyFn (F := F) := by
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, w, rfl⟩ := hx
    refine Algebra.subset_adjoin ?_
    fin_cases i
    · exact ⟨0, w, rfl⟩
    · exact ⟨1, w, rfl⟩
  | algebraMap r => exact Subalgebra.algebraMap_mem _ r
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

/- English proof (translation)
Take `⟨h1, h2⟩` from `(mem_finiteSchwartzBruhatPi F).1 hg`. Establish `hcl : IsClopen T` using `⟨hc.isClosed, ho⟩`. Establish `hi : IsLocallyConstant (T.indicator (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ))`. Conclude with `((LocallyConstant.const (Fin 2 → FiniteAdeleRing (𝓞 F) F) (1 : ℂ)).indicator hcl).isLocallyConstant`. Establish `hcont : Continuous fun y : Fin 4 → FiniteAdeleRing (𝓞 F) F => (![y 0, y 1] : Fin 2 → _)`.

Use `continuous_pi fun i => ?_` and prove the remaining obligations. Use `fin_cases i`. Conclude with `continuous_apply 0`. Conclude with `continuous_apply 1`. Conclude with `(mem_finiteSchwartzBruhatPi F).2 ⟨(hi.comp_continuous hcont).mul h1, h2.mul_left⟩`.
-/
private theorem ind_mul_mem {F : Type} [Field F] [NumberField F]
    {T : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F)} (hc : IsCompact T) (ho : IsOpen T)
    {g : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ finiteSchwartzBruhatPi F (ι := Fin 4)) :
    (fun y : Fin 4 → FiniteAdeleRing (𝓞 F) F =>
      (T.indicator (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) ![y 0, y 1]) * g y) ∈
        finiteSchwartzBruhatPi F (ι := Fin 4) := by
  obtain ⟨h1, h2⟩ := (mem_finiteSchwartzBruhatPi F).1 hg
  have hcl : IsClopen T := ⟨hc.isClosed, ho⟩
  have hi : IsLocallyConstant (T.indicator (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ)) := by
    exact ((LocallyConstant.const (Fin 2 → FiniteAdeleRing (𝓞 F) F) (1 : ℂ)).indicator hcl).isLocallyConstant
  have hcont : Continuous fun y : Fin 4 → FiniteAdeleRing (𝓞 F) F => (![y 0, y 1] : Fin 2 → _) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_apply 0
    · exact continuous_apply 1
  exact (mem_finiteSchwartzBruhatPi F).2 ⟨(hi.comp_continuous hcont).mul h1, h2.mul_left⟩

/- English proof (translation)
Introduce `F _ _ _ δ`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `χ hχ p hp T hc ho`. Proceed by induction on `hχ using Submodule.span_induction with`. Consider the case `mem φ hφ`.

Take `⟨q, hq, g, hg, rfl⟩` from `hφ`. Use `Submodule.subset_span ⟨_, mul_mem (poly_pull hp) hq, _, ind_mul_mem hc ho hg, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `v`. Establish `hfin : finPartPi ![v 0, v 1] = ![finPartPi v 0, finPartPi v 1]`. Use function extensionality and compare the values at `i`.

Apply the tactic sequence `fin_cases i <;> rfl`. Simplify using `only [hfin, Pi.mul_apply]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero`. Establish `: (fun v : V4 F => p ![v 0, v 1] * T.indicator 1 (finPartPi ![v 0, v 1]) * (0 : V4 F → ℂ) v) = 0`.

Use function extensionality and compare the values at `v`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy`.

Use `add_mem hx hy` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `v`. Simplify using `only [Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `smul a x _ hx`. Use `Submodule.smul_mem _ a hx` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `v`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `v₀`. Use `⟨_, Submodule.subset_span ⟨1, one_mem _, finiteTensor fun i => cosetIndicator (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (v₀ i).2, finiteTensor_mem fun i => cosetIndicator_mem_finiteSchwartzBruhat _ _, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `hone : finiteTensor (fun i => cosetIndicator (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (v₀ i).2) (finPartPi v₀) = 1`. Establish `hself : ∀ a : FiniteAdeleRing (𝓞 F) F, cosetIndicator (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) a a = 1` using `fun a => by`.

Rewrite using `[cosetIndicator_apply, if_pos]`. Rewrite using `[sub_self]`. Conclude with `zero_mem _`. Conclude with `Finset.prod_eq_one fun i _ => hself _`. Simplify using `only [hone, Pi.one_apply, one_mul, mul_one]`.

Conclude with `Complex.exp_ne_zero _`.
-/
theorem UpperTheory.ConvolutionTheory.R2.G.fockMul :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F), (∀ χ ∈ FockFn δ, ∀ p ∈ polyOn F (Fin 2), ∀ T : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F), IsCompact T → IsOpen T →
    (fun v : V4 F => p ![v 0, v 1] * T.indicator 1 (finPartPi ![v 0, v 1]) * χ v) ∈ FockFn δ) ∧ ∀ v₀ : V4 F, ∃ χ ∈ FockFn δ, χ v₀ ≠ 0 := by
  intro F _ _ _ δ
  refine ⟨?_, ?_⟩
  · intro χ hχ p hp T hc ho
    induction hχ using Submodule.span_induction with
    | mem φ hφ =>
      obtain ⟨q, hq, g, hg, rfl⟩ := hφ
      refine Submodule.subset_span ⟨_, mul_mem (poly_pull hp) hq, _, ind_mul_mem hc ho hg, ?_⟩
      funext v
      have hfin : finPartPi ![v 0, v 1] = ![finPartPi v 0, finPartPi v 1] := by
        funext i
        fin_cases i <;> rfl
      simp only [hfin, Pi.mul_apply]
      ring
    | zero =>
      have : (fun v : V4 F => p ![v 0, v 1] * T.indicator 1 (finPartPi ![v 0, v 1]) * (0 : V4 F → ℂ) v) = 0 := by
        funext v
        simp
      rw [this]
      exact zero_mem _
    | add x y _ _ hx hy =>
      have := add_mem hx hy
      convert this using 1
      funext v
      simp only [Pi.add_apply]
      ring
    | smul a x _ hx =>
      have := Submodule.smul_mem _ a hx
      convert this using 1
      funext v
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  · intro v₀
    refine ⟨_, Submodule.subset_span ⟨1, one_mem _,
      finiteTensor fun i => cosetIndicator (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (v₀ i).2,
      finiteTensor_mem fun i => cosetIndicator_mem_finiteSchwartzBruhat _ _, rfl⟩, ?_⟩
    have hone : finiteTensor (fun i => cosetIndicator (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (v₀ i).2)
        (finPartPi v₀) = 1 := by
      have hself : ∀ a : FiniteAdeleRing (𝓞 F) F,
          cosetIndicator (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) a a = 1 := fun a => by
        rw [cosetIndicator_apply, if_pos]
        rw [sub_self]
        exact zero_mem _
      exact Finset.prod_eq_one fun i _ => hself _
    simp only [hone, Pi.one_apply, one_mul, mul_one]
    exact Complex.exp_ne_zero _
