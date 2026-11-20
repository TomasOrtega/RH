import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.FtBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsTer

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

/- English proof (translation)
Unfold `ψ UpperTheory.ConvolutionTheory.R2.rt`. Rewrite using `[adelicChar_algebraMap]`. Simplify using the standard rewrite rules.
-/
private lemma psi_rt {F : Type} [Field F] [NumberField F] (c : F) : ψ (UpperTheory.ConvolutionTheory.R2.rt c) = 1 := by
  unfold ψ UpperTheory.ConvolutionTheory.R2.rt
  rw [adelicChar_algebraMap]
  simp

/- English proof (translation)
Simplify using `[q4, UpperTheory.ConvolutionTheory.R2.rt, map_sub, map_mul, map_pow]`.
-/
private lemma quadraticForm_rational_embed {F : Type} [Field F] [NumberField F] (δ : F) (ξ : Fin 4 → F) :
    q4 δ (fun i => UpperTheory.ConvolutionTheory.R2.rt (ξ i)) = UpperTheory.ConvolutionTheory.R2.rt (ξ 2 ^ 2 - δ * ξ 3 ^ 2 - ξ 1 * ξ 0) := by
  simp [q4, UpperTheory.ConvolutionTheory.R2.rt, map_sub, map_mul, map_pow]

/- English proof (translation)
Introduce `F _ _ δ η Om hδ hO γ`. Establish `hγ : ratS F γ ∈ Subgroup.closure (Set.range (fun b : F => nU (UpperTheory.ConvolutionTheory.R2.rt b)) ∪ {wW F})`. Rewrite using `[(UpperTheory.ConvolutionTheory.R2.gen F).2]`. Conclude with `⟨γ, rfl⟩`. Establish `key : ∀ g ∈ Subgroup.closure (Set.range (fun b : F => nU (UpperTheory.ConvolutionTheory.R2.rt b)) ∪ {wW F}), ∀ φ : S4 F, Th (Om g φ).1 = Th φ.1`.

Introduce `g hg`. Proceed by induction on `hg using Subgroup.closure_induction with`. Consider the case `mem g hg`. Introduce `φ`. Break down `hg with ⟨b, rfl⟩ | hg` into its components or cases.

Unfold `Th`. Use `tsum_congr fun ξ => ?_` and prove the remaining obligations. Rewrite using `[hO.n, quadraticForm_rational_embed, ← map_mul, psi_rt, one_mul]`. Rewrite `hg` using `[Set.mem_singleton_iff]`. Substitute `hg` using the available equality.

Establish `h : (Om (wW F) φ).1 = ft4 δ φ.1` using `funext (hO.w φ)`. Rewrite using `[h]`. Conclude with `(UpperTheory.ConvolutionTheory.R2.C.ftBasic F δ hδ φ.1 φ.2).2.2`. Consider the case `one => intro φ`. Simplify using the standard rewrite rules.

Consider the case `mul x y _ _ hx hy`. Introduce `φ`. Rewrite using `[map_mul, Module.End.mul_apply, hx, hy]`. Consider the case `inv x _ hx`. Introduce `φ`.

Establish `h` using `hx (Om x⁻¹ φ)`. Rewrite `h` using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`. Conclude with `h.symm`. Conclude with `key _ hγ`.
-/
theorem UpperTheory.ConvolutionTheory.R2.C.thOm :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (η : (A F)ˣ →* ℂˣ) (Om : G1 F →* Module.End ℂ (S4 F)), δ ≠ 0 → IsOm δ η Om → ∀ γ φ, Th (Om (ratS F γ) φ).1 = Th φ.1 := by
  intro F _ _ δ η Om hδ hO γ
  have hγ : ratS F γ ∈ Subgroup.closure (Set.range (fun b : F => nU (UpperTheory.ConvolutionTheory.R2.rt b)) ∪ {wW F}) := by
    rw [(UpperTheory.ConvolutionTheory.R2.gen F).2]
    exact ⟨γ, rfl⟩
  have key : ∀ g ∈ Subgroup.closure (Set.range (fun b : F => nU (UpperTheory.ConvolutionTheory.R2.rt b)) ∪ {wW F}),
      ∀ φ : S4 F, Th (Om g φ).1 = Th φ.1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      intro φ
      rcases hg with ⟨b, rfl⟩ | hg
      · unfold Th
        refine tsum_congr fun ξ => ?_
        rw [hO.n, quadraticForm_rational_embed, ← map_mul, psi_rt, one_mul]
      · rw [Set.mem_singleton_iff] at hg
        subst hg
        have h : (Om (wW F) φ).1 = ft4 δ φ.1 := funext (hO.w φ)
        rw [h]
        exact (UpperTheory.ConvolutionTheory.R2.C.ftBasic F δ hδ φ.1 φ.2).2.2
    | one => intro φ; simp
    | mul x y _ _ hx hy =>
      intro φ
      rw [map_mul, Module.End.mul_apply, hx, hy]
    | inv x _ hx =>
      intro φ
      have h := hx (Om x⁻¹ φ)
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
      exact h.symm
  exact key _ hγ
