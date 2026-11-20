import Mathlib
import Formalism.LocalToGlobal.Columns.BrzColLatOneLattice

open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLattices.TraceIntegrality Formalism.HermitianLatticesTheory

section SlopeTestRemainingChoices

variable {ι : Type} [Fintype ι] [DecidableEq ι]

end SlopeTestRemainingChoices

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ} (lam : DomWeight n)

def stdPairB : StdV K lam →ₗ[K] StdV K lam →ₗ[K] K := pairBK (oneW lam)

instance bzd_finite : Module.Finite K (StdV K lam) := Module.Finite.of_basis (bVV K (oneW lam))

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Conclude with `(pairingBNondegenerate_holds K Unit n (oneW lam)).1 x fun y => by`. Use `congrArg (fun f : Module.Dual K (StdV K lam) => f y) hx` as an intermediate fact. Conclude with `this`.
-/
theorem stdPairB_injective : Function.Injective (stdPairB K lam) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  exact (pairingBNondegenerate_holds K Unit n (oneW lam)).1 x fun y => by
    have := congrArg (fun f : Module.Dual K (StdV K lam) => f y) hx
    exact this

def stdDualEquiv : StdV K lam ≃ₗ[K] Module.Dual K (StdV K lam) :=
  LinearMap.linearEquivOfInjective (stdPairB K lam) (stdPairB_injective K lam) (Subspace.dual_finrank_eq).symm

def stdGramAt (v : InfinitePlace K) : Matrix (VVIdx (oneW lam)) (VVIdx (oneW lam)) ℂ :=
  Matrix.of fun i j => v.embedding (stdPairB K lam (bVV K (oneW lam) i) (bVV K (oneW lam) j))

end Std

/- English proof (translation)
Establish `hX'' : ∀ v, IsUnit (A.dualX v).det` using `fun v => by show IsUnit (((A.X v).transpose)⁻¹).det`. Rewrite using `[Matrix.det_nonsing_inv, Matrix.det_transpose]`. Conclude with `(hG.1 v).ringInverse`. Take `⟨-, -, h3, -, -, -, -⟩` from `Formalism.HN.rerealize K A.V A.ι (Module.Dual K A.V) A.ι A.b A.X A.dualB A.dualX ψ hG.1 hX'' hψ hnorm L' hL'`. Rewrite `h3` using `[hmap]`.

Establish `hd` using `(dual_numbers K A hG hr).1`. Rewrite using `[← hd]`. Use `show Formalism.HN.muDef A.b A.X L' = Formalism.HN.muDef A.dualB A.dualX A.dualL`. Unfold `Formalism.HN.muDef`. Rewrite using `[h3]`.
-/
theorem hlat_mu_of_dual {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (A : HLat K) (hG : A.Good)
    (hr : 0 < A.rank) (L' : Submodule (𝓞 K) A.V) (hL' : L'.FG) (ψ : A.V →ₗ[K] Module.Dual K A.V) (hψ : Function.Injective ψ)
    (hmap : L'.map (ψ.restrictScalars (𝓞 K)) = A.dualL)
    (hnorm : ∀ v x, Formalism.HermitianLatticesTheory.normAt A.dualB A.dualX v (ψ x) = Formalism.HermitianLatticesTheory.normAt A.b A.X v x) :
    (withL A L').mu = -A.mu := by
  have hX'' : ∀ v, IsUnit (A.dualX v).det := fun v => by
    show IsUnit (((A.X v).transpose)⁻¹).det
    rw [Matrix.det_nonsing_inv, Matrix.det_transpose]
    exact (hG.1 v).ringInverse
  obtain ⟨-, -, h3, -, -, -, -⟩ := Formalism.HN.rerealize K A.V A.ι (Module.Dual K A.V) A.ι A.b A.X A.dualB A.dualX ψ hG.1 hX''
    hψ hnorm L' hL'
  rw [hmap] at h3
  have hd := (dual_numbers K A hG hr).1
  rw [← hd]
  show Formalism.HN.muDef A.b A.X L' = Formalism.HN.muDef A.dualB A.dualX A.dualL
  unfold Formalism.HN.muDef
  rw [h3]

end Formalism.L2.Col
