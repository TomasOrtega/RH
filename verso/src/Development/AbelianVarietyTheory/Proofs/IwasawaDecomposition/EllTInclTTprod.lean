import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.Mem.SchurTensor

/- English proof (translation)
Simplify using `[ellT, inclT]`.
-/
theorem ellT_inclT_tprod {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (w : ∀ τ, M.H τ) (v : M.Vec) :
    ellT M w (inclT M (PiTensorProduct.tprod ℂ v)) = ∏ τ, ⟪w τ, (v τ : M.H τ)⟫_ℂ := by
  simp [ellT, inclT]

/- English proof (translation)
Introduce `D θ V S M J χ μ 𝓕 hS hθ hq x hx y hy v w`. Establish `hx'` using `(mem_multT θ M J χ x).1 hx`. Establish `hy'` using `(mem_multT θ M J χ y).1 hy`. Establish `hm` using `(GlobalTheory.MultMem.mem_mult_iff D θ V S M J χ _).1 hy'`. Establish `hI` using `ipM_spec M μ 𝓕 _ _ (hS hθ hq.1 hq.2 _ hx' _ hy')`.

Use `⟨⟨hm.aut w, hm.cusp w⟩, ?_⟩` and prove the remaining obligations. Proceed by induction on `v using PiTensorProduct.induction_on with`. Consider the case `smul_tprod c u`. Take `⟨h1, h2⟩` from `hI u w`. Establish `e : (fun g => star (x (c • PiTensorProduct.tprod ℂ u) g) * y (PiTensorProduct.tprod ℂ w) g) = fun g => star c * (star (x (PiTensorProduct.tprod ℂ u) g) * y (PiTensorProduct.tprod ℂ w) g)`.

Use function extensionality and compare the values at `g`. Rewrite using `[map_smul, Pi.smul_apply, smul_eq_mul, star_mul', mul_assoc]`. Rewrite using `[e]`. Use `⟨h1.const_mul _, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_const_mul, map_smul, map_smul, ellT_inclT_tprod, smul_eq_mul, star_mul', star_prod]`.

Use `(congrArg (star c * ·) h2).trans ?_` and prove the remaining obligations. Establish `e2 : ∏ τ, star ⟪(w τ : M.H τ), (u τ : M.H τ)⟫_ℂ = ∏ τ, ⟪(u τ : M.H τ), (w τ : M.H τ)⟫_ℂ` using `Finset.prod_congr rfl fun τ _ => inner_conj_symm _ _`. Rewrite using `[e2, ipT]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `add a b ha hb`.

Establish `e : (fun g => star (x (a + b) g) * y (PiTensorProduct.tprod ℂ w) g) = fun g => star (x a g) * y (PiTensorProduct.tprod ℂ w) g + star (x b g) * y (PiTensorProduct.tprod ℂ w) g`. Use function extensionality and compare the values at `g`. Rewrite using `[map_add, Pi.add_apply, star_add, add_mul]`. Rewrite using `[e]`. Use `⟨ha.1.add hb.1, ?_⟩` and prove the remaining obligations.

Rewrite using `[integral_add ha.1 hb.1, ha.2, hb.2, map_add, map_add, star_add, mul_add]`.
-/
theorem schur_tensor : ∀ (D : D7) (θ : InfF D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), SchurMult θ M J χ μ 𝓕 → IsInfFam θ → IsQuot V μ 𝓕 → ∀ x ∈ MultT θ M J χ, ∀ y ∈ MultT θ M J χ, ∀ (v : SmT M) (w : M.Vec), IsCuspForm θ V (y (PiTensorProduct.tprod ℂ w)) ∧ IntegrableOn (fun g => star (x v g) * y (PiTensorProduct.tprod ℂ w) g) 𝓕 μ ∧ ∫ g in 𝓕, star (x v g) * y (PiTensorProduct.tprod ℂ w) g ∂μ = ipT M μ 𝓕 y x * star (ellT M (fun τ => (w τ : M.H τ)) (inclT M v)) := by
  intro D θ V S M J χ μ 𝓕 hS hθ hq x hx y hy v w
  have hx' := (mem_multT θ M J χ x).1 hx
  have hy' := (mem_multT θ M J χ y).1 hy
  have hm := (GlobalTheory.MultMem.mem_mult_iff D θ V S M J χ _).1 hy'
  have hI := ipM_spec M μ 𝓕 _ _ (hS hθ hq.1 hq.2 _ hx' _ hy')
  refine ⟨⟨hm.aut w, hm.cusp w⟩, ?_⟩
  induction v using PiTensorProduct.induction_on with
  | smul_tprod c u =>
    obtain ⟨h1, h2⟩ := hI u w
    have e : (fun g => star (x (c • PiTensorProduct.tprod ℂ u) g) * y (PiTensorProduct.tprod ℂ w) g) =
        fun g => star c * (star (x (PiTensorProduct.tprod ℂ u) g) * y (PiTensorProduct.tprod ℂ w) g) := by
      funext g
      rw [map_smul, Pi.smul_apply, smul_eq_mul, star_mul', mul_assoc]
    rw [e]
    refine ⟨h1.const_mul _, ?_⟩
    rw [integral_const_mul, map_smul, map_smul, ellT_inclT_tprod, smul_eq_mul, star_mul', star_prod]
    refine (congrArg (star c * ·) h2).trans ?_
    have e2 : ∏ τ, star ⟪(w τ : M.H τ), (u τ : M.H τ)⟫_ℂ = ∏ τ, ⟪(u τ : M.H τ), (w τ : M.H τ)⟫_ℂ :=
      Finset.prod_congr rfl fun τ _ => inner_conj_symm _ _
    rw [e2, ipT]
    ring
  | add a b ha hb =>
    have e : (fun g => star (x (a + b) g) * y (PiTensorProduct.tprod ℂ w) g) =
        fun g => star (x a g) * y (PiTensorProduct.tprod ℂ w) g + star (x b g) * y (PiTensorProduct.tprod ℂ w) g := by
      funext g
      rw [map_add, Pi.add_apply, star_add, add_mul]
    rw [e]
    refine ⟨ha.1.add hb.1, ?_⟩
    rw [integral_add ha.1 hb.1, ha.2, hb.2, map_add, map_add, star_add, mul_add]

end GlobalTheory.Mem.SchurTensor
