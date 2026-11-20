import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

/- English proof (translation)
Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨p, g, hg, rfl⟩` from `hx`. Establish `e : (fun y : Fin 4 → FiniteAdeleRing (𝓞 F) F => schwartzBruhatTensorPi p g fun i => ((0, y i) : A F)) = p (infPartPi fun _ : Fin 4 => (0 : A F)) • g`. Use function extensionality and compare the values at `y`.

Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ hg`. Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => exact Submodule.add_mem _ hx hy`.

Consider the case `smul c x _ hx => exact Submodule.smul_mem _ c hx`.
-/
private theorem slice_mem {F : Type} [Field F] [NumberField F] {f : V4 F → ℂ}
    (hf : f ∈ schwartzBruhatPi F (Fin 4)) :
    (fun y : Fin 4 → FiniteAdeleRing (𝓞 F) F => f fun i => ((0, y i) : A F)) ∈
      finiteSchwartzBruhatPi F (ι := Fin 4) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, g, hg, rfl⟩ := hx
    have e : (fun y : Fin 4 → FiniteAdeleRing (𝓞 F) F =>
        schwartzBruhatTensorPi p g fun i => ((0, y i) : A F)) =
        p (infPartPi fun _ : Fin 4 => (0 : A F)) • g := by
      funext y
      rfl
    rw [e]
    exact Submodule.smul_mem _ _ hg
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

/- English proof (translation)
Establish `key : ∀ a : V4 F, (∀ i, TR.pInf F (a i) = 0) → gauss δ a = 1` using `fun a h => by`. Simplify using `only [gauss, map_add, map_sub, map_mul, map_pow, h]`. Simplify using the standard rewrite rules. Conclude with `key _ fun i => map_zero (TR.infEq F).symm`.
-/
private theorem gauss_fin {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (δ : F)
    (y : Fin 4 → FiniteAdeleRing (𝓞 F) F) : gauss δ (fun i => ((0, y i) : A F)) = 1 := by
  have key : ∀ a : V4 F, (∀ i, TR.pInf F (a i) = 0) → gauss δ a = 1 := fun a h => by
    simp only [gauss, map_add, map_sub, map_mul, map_pow, h]
    simp
  exact key _ fun i => map_zero (TR.infEq F).symm

/- English proof (translation)
Introduce `F _ _ _ δ φ hφ`. Use `⟨_, slice_mem φ.2, funext fun v => ?_⟩` and prove the remaining obligations. Establish `h` using `hφ v (fun i => ((0, (v i).2) : A F)) rfl`. Rewrite `h` using `[gauss_fin, mul_one]`. Rewrite using `[h, mul_comm]`.

Both sides reduce to the same expression.
-/
theorem UpperTheory.ConvolutionTheory.R2.Fo.vacForm :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F), ∀ φ ∈ Vac δ, ∃ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4), φ.1 = fun v => gauss δ v * g (finPartPi v) := by
  intro F _ _ _ δ φ hφ
  refine ⟨_, slice_mem φ.2, funext fun v => ?_⟩
  have h := hφ v (fun i => ((0, (v i).2) : A F)) rfl
  rw [gauss_fin, mul_one] at h
  rw [h, mul_comm]
  rfl
