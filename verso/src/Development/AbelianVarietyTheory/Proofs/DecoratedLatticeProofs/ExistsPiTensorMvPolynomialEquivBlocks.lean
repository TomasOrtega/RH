import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.BlockPoly

variable (ι σ : Type) [Fintype ι] [DecidableEq ι]

noncomputable def blockMul :
    MultilinearMap ℂ (fun _ : ι => MvPolynomial σ ℂ) (MvPolynomial (ι × σ) ℂ) :=
  (MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial (ι × σ) ℂ)).compLinearMap
    (fun τ => (rename (Prod.mk τ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial (ι × σ) ℂ).toLinearMap)

/- English proof (translation)
Simplify using `[blockMul]`.
-/
theorem blockMul_apply (f : ι → MvPolynomial σ ℂ) :
    blockMul ι σ f = ∏ τ, rename (Prod.mk τ) (f τ) := by
  simp [blockMul]

noncomputable def expEquiv : (ι → σ →₀ ℕ) ≃ (ι × σ →₀ ℕ) :=
  Finsupp.equivFunOnFinite.symm.trans Finsupp.curryEquiv.symm

/- English proof (translation)
Simplify using `[expEquiv]`.
-/
theorem expEquiv_apply (d : ι → σ →₀ ℕ) (a : ι) (b : σ) : expEquiv ι σ d (a, b) = d a b := by
  simp [expEquiv]

/- English proof (translation)
Use extensionality with `⟨a, b⟩`. Rewrite using `[expEquiv_apply, Finsupp.coe_finset_sum, Finset.sum_apply, Finset.sum_eq_single a]`. Conclude with `Finsupp.mapDomain_apply (fun x y h => by simpa using h) _ _`. Introduce `τ _ hτ`. Apply `Finsupp.mapDomain_notin_range` to reduce the goal to its premises.

Introduce and unpack `⟨c, hc⟩`. Conclude with `hτ (congrArg Prod.fst hc)`. Introduce `h`. Conclude with `absurd (Finset.mem_univ a) h`.
-/
theorem sum_mapDomain_eq (d : ι → σ →₀ ℕ) :
    ∑ τ, (d τ).mapDomain (Prod.mk τ) = expEquiv ι σ d := by
  ext ⟨a, b⟩
  rw [expEquiv_apply, Finsupp.coe_finset_sum, Finset.sum_apply, Finset.sum_eq_single a]
  · exact Finsupp.mapDomain_apply (fun x y h => by simpa using h) _ _
  · intro τ _ hτ
    apply Finsupp.mapDomain_notin_range
    rintro ⟨c, hc⟩
    exact hτ (congrArg Prod.fst hc)
  · intro h; exact absurd (Finset.mem_univ a) h

/- English proof (translation)
Simplify using `only [rename_monomial]`. Rewrite using `[← monomial_sum_one, sum_mapDomain_eq]`.
-/
theorem prod_rename_monomial (d : ι → σ →₀ ℕ) :
    ∏ τ, rename (Prod.mk τ) (monomial (d τ) (1 : ℂ)) = monomial (expEquiv ι σ d) 1 := by
  simp only [rename_monomial]
  rw [← monomial_sum_one, sum_mapDomain_eq]

noncomputable def blockEquiv :
    PiTensorProduct ℂ (fun _ : ι => MvPolynomial σ ℂ) ≃ₗ[ℂ] MvPolynomial (ι × σ) ℂ :=
  (Basis.piTensorProduct (fun _ : ι => basisMonomials σ ℂ)).equiv
    (basisMonomials (ι × σ) ℂ) (expEquiv ι σ)

/- English proof (translation)
Use `(Basis.piTensorProduct (fun _ : ι => basisMonomials σ ℂ)).ext (fun p => ?_)` and prove the remaining obligations. Rewrite using `[LinearEquiv.coe_coe, blockEquiv, Module.Basis.equiv_apply, Basis.piTensorProduct_apply, PiTensorProduct.lift.tprod, blockMul_apply]`. Simplify using `only [coe_basisMonomials]`. Rewrite using `[prod_rename_monomial]`.
-/
theorem blockEquiv_toLinearMap :
    (blockEquiv ι σ).toLinearMap = PiTensorProduct.lift (blockMul ι σ) := by
  refine (Basis.piTensorProduct (fun _ : ι => basisMonomials σ ℂ)).ext (fun p => ?_)
  rw [LinearEquiv.coe_coe, blockEquiv, Module.Basis.equiv_apply, Basis.piTensorProduct_apply,
    PiTensorProduct.lift.tprod, blockMul_apply]
  simp only [coe_basisMonomials]
  rw [prod_rename_monomial]

/- English proof (translation)
Rewrite using `[← LinearEquiv.coe_coe, blockEquiv_toLinearMap, PiTensorProduct.lift.tprod, blockMul_apply]`.
-/
theorem blockEquiv_tprod (f : ι → MvPolynomial σ ℂ) :
    blockEquiv ι σ (PiTensorProduct.tprod ℂ f) = ∏ τ, rename (Prod.mk τ) (f τ) := by
  rw [← LinearEquiv.coe_coe, blockEquiv_toLinearMap, PiTensorProduct.lift.tprod, blockMul_apply]

/- English proof (translation)
Use `choose g hg using fun τ => LinearMap.exists_leftInverse_of_injective (U τ).subtype (U τ).ker_subtype`. Establish `h : (PiTensorProduct.map g) ∘ₗ (PiTensorProduct.map fun τ => (U τ).subtype) = LinearMap.id`. Rewrite using `[← PiTensorProduct.map_comp]`. Simplify using `only [hg]`. Conclude with `PiTensorProduct.map_id`.

Conclude with `Function.LeftInverse.injective (g := PiTensorProduct.map g) (fun x => by simpa using LinearMap.congr_fun h x)`.
-/
theorem map_subtype_injective (U : ι → Submodule ℂ (MvPolynomial σ ℂ)) :
    Function.Injective (PiTensorProduct.map fun τ => (U τ).subtype) := by
  choose g hg using fun τ => LinearMap.exists_leftInverse_of_injective (U τ).subtype (U τ).ker_subtype
  have h : (PiTensorProduct.map g) ∘ₗ (PiTensorProduct.map fun τ => (U τ).subtype) =
      LinearMap.id := by
    rw [← PiTensorProduct.map_comp]
    simp only [hg]
    exact PiTensorProduct.map_id
  exact Function.LeftInverse.injective (g := PiTensorProduct.map g)
    (fun x => by simpa using LinearMap.congr_fun h x)

/- English proof (translation)
Introduce `ι σ _ _`. Use `⟨blockEquiv ι σ, blockEquiv_tprod ι σ, fun U => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `(blockEquiv ι σ).injective.comp (map_subtype_injective ι σ U)`. Rewrite using `[LinearMap.range_eq_map, ← PiTensorProduct.span_tprod_eq_top, Submodule.map_span]`. Use `congr 1`.

Use extensionality with `p`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨g, rfl⟩, rfl⟩`. Use `⟨fun τ => (g τ : MvPolynomial σ ℂ), fun τ => (g τ).2, ?_⟩` and prove the remaining obligations. Simplify using `[PiTensorProduct.map_tprod, blockEquiv_tprod]`.

Introduce and unpack `⟨f, hf, rfl⟩`. Use `⟨PiTensorProduct.tprod ℂ (fun τ => (⟨f τ, hf τ⟩ : U τ)), ⟨_, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `[PiTensorProduct.map_tprod, blockEquiv_tprod]`.
-/
theorem exists_blockEquiv :
    ∀ (ι σ : Type) [Fintype ι] [DecidableEq ι], ∃ e : PiTensorProduct ℂ (fun _ : ι => MvPolynomial σ ℂ) ≃ₗ[ℂ] MvPolynomial (ι × σ) ℂ, (∀ f : ι → MvPolynomial σ ℂ, e (PiTensorProduct.tprod ℂ f) = ∏ τ, rename (Prod.mk τ) (f τ)) ∧ ∀ U : ι → Submodule ℂ (MvPolynomial σ ℂ), Function.Injective (e.toLinearMap ∘ₗ PiTensorProduct.map fun τ => (U τ).subtype) ∧ LinearMap.range (e.toLinearMap ∘ₗ PiTensorProduct.map fun τ => (U τ).subtype) = Submodule.span ℂ {p | ∃ f : ι → MvPolynomial σ ℂ, (∀ τ, f τ ∈ U τ) ∧ p = ∏ τ, rename (Prod.mk τ) (f τ)} := by
  intro ι σ _ _
  refine ⟨blockEquiv ι σ, blockEquiv_tprod ι σ, fun U => ⟨?_, ?_⟩⟩
  · exact (blockEquiv ι σ).injective.comp (map_subtype_injective ι σ U)
  · rw [LinearMap.range_eq_map, ← PiTensorProduct.span_tprod_eq_top, Submodule.map_span]
    congr 1
    ext p
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      refine ⟨fun τ => (g τ : MvPolynomial σ ℂ), fun τ => (g τ).2, ?_⟩
      simp [PiTensorProduct.map_tprod, blockEquiv_tprod]
    · rintro ⟨f, hf, rfl⟩
      refine ⟨PiTensorProduct.tprod ℂ (fun τ => (⟨f τ, hf τ⟩ : U τ)), ⟨_, rfl⟩, ?_⟩
      simp [PiTensorProduct.map_tprod, blockEquiv_tprod]

end GlobalTheory.BlockPoly
