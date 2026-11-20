import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.StatementsPointHeight
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FieldChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Module Matrix
open scoped ComplexOrder

noncomputable section

section Embedding

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

omit [DecidableEq ι] in

/- English proof (translation)
Use `set τ' : K' →ₐ[ℚ] AlgebraicClosure ℚ := τ.toRatAlgHom`. Use `set L : IntermediateField ℚ (AlgebraicClosure ℚ) := τ'.fieldRange`. Set `e : K' ≃ₐ[ℚ] L` to `AlgEquiv.ofInjectiveField τ'`. Establish `: FiniteDimensional ℚ L` using `e.toLinearEquiv.finiteDimensional`. Establish `: NumberField L` using `{}`.

Establish `hx : ∀ k i, τ (y k i) ∈ L` using `fun k i ↦ ⟨y k i, rfl⟩`. Establish `hx0 : BlockNonzero (fun k i ↦ τ (y k i))` using `fun k h ↦ hy k (funext fun i ↦ by`. Use `congrFun h i` as an intermediate fact. Conclude with `τ.injective (by simpa using this))`. Rewrite using `[height_eq_of_le A hx0 L hx]`.

Set `_ : Algebra L K'` to `e.symm.toRingHom.toAlgebra`. Establish `: IsScalarTower ℚ L K'` using `IsScalarTower.of_algebraMap_eq fun q ↦ by`. Express the relevant statement in the definitionally equal form `algebraMap ℚ K' q = e.symm (algebraMap ℚ L q)`. Rewrite using `[AlgEquiv.commutes]`. Establish `he : ∀ k i, algebraMap L K' (coordIn L (fun k i ↦ τ (y k i)) hx k i) = y k i`.

Introduce `k i`. Express the relevant statement in the definitionally equal form `e.symm _ = _`. Rewrite using `[AlgEquiv.symm_apply_eq]`. Apply `Subtype.ext` to reduce the goal to its premises. Both sides reduce to the same expression.

Establish `hblock : BlockNonzero (coordIn L (fun k i ↦ τ (y k i)) hx)` using `fun k h ↦ hx0 k (funext fun i ↦ by`. Use `congrFun h i` as an intermediate fact. Conclude with `congrArg Subtype.val this)`. Establish `hfin` using `finsum_finiteTerm_algebraMap (K := L) (L := K') A hblock`. Establish `harch` using `sum_embeddings_restrict (K := L) (L := K') (fun σ ↦ Real.log (A.metric fun k i ↦ σ (coordIn L (fun k i ↦ τ (y k i)) hx k i)))`.

Simplify using `only [RingHom.comp_apply, he] at hfin harch`. Establish `hdeg` using `Module.finrank_mul_finrank ℚ L K'`. Rewrite using `[hfin, harch, ← hdeg]`. Establish `h1 : (0 : ℝ) < finrank ℚ L` using `by exact_mod_cast Module.finrank_pos`. Establish `h2 : (0 : ℝ) < finrank L K'` using `by exact_mod_cast Module.finrank_pos`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem height_eq_of_ringHom (A : HermLine n) {K' : Type*} [Field K'] [NumberField K']
    (τ : K' →+* AlgebraicClosure ℚ) (y : Cone n K') (hy : BlockNonzero y) :
    height A (fun k i ↦ τ (y k i)) = ((finrank ℚ K' : ℝ))⁻¹ *
      (∑ᶠ w : FinitePlace K', finiteTerm A w y +
        ∑ σ : K' →+* ℂ, Real.log (A.metric fun k i ↦ σ (y k i))) := by
  set τ' : K' →ₐ[ℚ] AlgebraicClosure ℚ := τ.toRatAlgHom
  set L : IntermediateField ℚ (AlgebraicClosure ℚ) := τ'.fieldRange
  let e : K' ≃ₐ[ℚ] L := AlgEquiv.ofInjectiveField τ'
  have : FiniteDimensional ℚ L := e.toLinearEquiv.finiteDimensional
  have : NumberField L := {}
  have hx : ∀ k i, τ (y k i) ∈ L := fun k i ↦ ⟨y k i, rfl⟩
  have hx0 : BlockNonzero (fun k i ↦ τ (y k i)) := fun k h ↦ hy k (funext fun i ↦ by
    have := congrFun h i
    exact τ.injective (by simpa using this))
  rw [height_eq_of_le A hx0 L hx]
  let _ : Algebra L K' := e.symm.toRingHom.toAlgebra
  have : IsScalarTower ℚ L K' := IsScalarTower.of_algebraMap_eq fun q ↦ by
    change algebraMap ℚ K' q = e.symm (algebraMap ℚ L q)
    rw [AlgEquiv.commutes]
  have he : ∀ k i, algebraMap L K' (coordIn L (fun k i ↦ τ (y k i)) hx k i) = y k i := by
    intro k i
    change e.symm _ = _
    rw [AlgEquiv.symm_apply_eq]
    apply Subtype.ext
    rfl
  have hblock : BlockNonzero (coordIn L (fun k i ↦ τ (y k i)) hx) := fun k h ↦ hx0 k (funext fun i ↦ by
    have := congrFun h i
    exact congrArg Subtype.val this)
  have hfin := finsum_finiteTerm_algebraMap (K := L) (L := K') A hblock
  have harch := sum_embeddings_restrict (K := L) (L := K')
    (fun σ ↦ Real.log (A.metric fun k i ↦ σ (coordIn L (fun k i ↦ τ (y k i)) hx k i)))
  simp only [RingHom.comp_apply, he] at hfin harch
  have hdeg := Module.finrank_mul_finrank ℚ L K'
  rw [hfin, harch, ← hdeg]
  have h1 : (0 : ℝ) < finrank ℚ L := by exact_mod_cast Module.finrank_pos
  have h2 : (0 : ℝ) < finrank L K' := by exact_mod_cast Module.finrank_pos
  push_cast
  field_simp

end Embedding

/- English proof (translation)
Introduce `K _ _ r N F φ hφ`. Use `⟨hLine K r N F φ hφ, ?_⟩` and prove the remaining obligations. Introduce `A hA hagree K' _ _ _ v hv τ`. Use `set y : Fin (N + 1) → K' := latticeValue φ v with hy_def`. Establish `hx : latticePoint φ (τ.comp (algebraMap K K')) (fun j ↦ τ (v j)) = fun _ b ↦ τ (y b)`.

Use function extensionality and compare the values at `u b`. Simplify using `[latticePoint, hy_def, latticeValue, map_sum, map_mul]`. Establish `hσ : ∀ σ' : K' →+* ℂ, (fun (_ : Unit) b ↦ σ' (y b)) = latticePoint φ (σ'.comp (algebraMap K K')) (fun j ↦ σ' (v j))`. Introduce `σ'`. Use function extensionality and compare the values at `u b`.

Simplify using `[latticePoint, hy_def, latticeValue, map_sum, map_mul]`. Establish `hy0 : y ≠ 0`. Introduce `h0`. Apply `hv` to reduce the goal to its premises. Establish `hne : Nonempty (K' →+* ℂ)`.

Rewrite using `[← Fintype.card_pos_iff, NumberField.Embeddings.card]`. Conclude with `Module.finrank_pos`. Take `⟨σ'⟩` from `hne`. Use function extensionality and compare the values at `j0`. Take `⟨R, hR⟩` from `(hPts K r N F φ hφ).2.2 (σ'.comp (algebraMap K K')) j0`.

Establish `key : ∑ b, R b * σ' (y b) = σ' (v j0)`. Establish `h1` using `congrFun (hσ σ') ()`. Establish `h2 : ∀ b, σ' (y b) = ∑ j, (σ'.comp (algebraMap K K')) (φ b j) * σ' (v j)` using `fun b ↦ congrFun h1 b`. Simplify using `only [h2, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Establish `h3 : ∀ j, ∑ b, R b * ((σ'.comp (algebraMap K K')) (φ b j) * σ' (v j)) = (∑ b, R b * (σ'.comp (algebraMap K K')) (φ b j)) * σ' (v j)`. Introduce `j`. Rewrite using `[Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun b _ ↦ by ring`. Simplify using `only [h3, hR]`.

Simplify using the standard rewrite rules. Establish `: σ' (v j0) = 0`. Rewrite using `[← key]`. Simplify using `[h0]`. Conclude with `(map_eq_zero_iff σ' σ'.injective).mp this`.

Establish `hblock : BlockNonzero (fun (_ : Unit) b ↦ y b)` using `fun _ h ↦ hy0 (funext fun b ↦ congrFun h b)`. Rewrite using `[hx, height_eq_of_ringHom A τ (fun _ b ↦ y b) hblock]`. Establish `hpos : ∀ w : FinitePlace K', 0 < ⨆ b, w (y b)` using `iSup_place_pos hy0`. Establish `hfin : ∑ᶠ w : FinitePlace K', finiteTerm A w (fun _ b ↦ y b) = -Real.log (genIndex (multiplierIdeal y).toAddSubgroup (1 : Submodule (𝓞 K') K').toAddSubgroup)`. Establish `hterm : ∀ w : FinitePlace K', finiteTerm A w (fun _ b ↦ y b) = Real.log (⨆ b, w (y b))`.

Introduce `w`. Simplify using `[finiteTerm, hA]`. Simplify using `only [hterm]`. Rewrite using `[finsum_log_eq_log_finprod hpos (hasFiniteMulSupport_iSup_place hy0)]`. Establish `hI` using `hIdx K' (Fin (N + 1)) y hy0`.

Rewrite using `[eq_inv_of_mul_eq_one_right hI, Real.log_inv]`. Establish `harch : ∀ σ' : K' →+* ℂ, Real.log (A.metric fun _ b ↦ σ' (y b)) = 1 / 2 * Real.log (gramAt (F.metric (σ'.comp (algebraMap K K'))) σ' (fun _ : Fin 1 ↦ v)).det.re`. Introduce `σ'`. Establish `hw : (fun j ↦ σ' (v j)) ≠ 0`. Introduce `h`.

Apply `hv` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Conclude with `(map_eq_zero_iff σ' σ'.injective).mp (congrFun h j)`. Rewrite using `[show (fun (_ : Unit) b ↦ σ' (y b)) = _ from hσ σ', hagree _ _ hw, Matrix.det_unique]`. Establish `hq : 0 ≤ (star (fun j ↦ σ' (v j)) ⬝ᵥ (F.metric (σ'.comp (algebraMap K K')) *ᵥ fun j ↦ σ' (v j))).re` using `le_of_lt (Complex.lt_def.mp ((F.posDef _).dotProduct_mulVec_pos hw)).1`.

Rewrite using `[Real.log_sqrt hq]`. Simplify using `only [gramAt]`. Unfold `embVec`. Expand and normalize the polynomial expressions, which then agree. Establish `hline : genIndex ((latticeExtend K' F.lattice ⊓ (Submodule.span K' (Set.range fun _ : Fin 1 ↦ v)).restrictScalars (𝓞 K')).toAddSubgroup) (Submodule.span (𝓞 K') (Set.range fun _ : Fin 1 ↦ v)).toAddSubgroup = genIndex (multiplierIdeal y).toAddSubgroup (1 : Submodule (𝓞 K') K').toAd …`.

Set `f : K' →+ (Fin (r + 1) → K')` to `{ toFun := fun a ↦ a • v, map_zero' := zero_smul _ _, map_add' := fun a a' ↦ add_smul a a' v }`. Establish `hf : Function.Injective f` using `smul_left_injective K' hv`. Establish `e1 : (latticeExtend K' F.lattice ⊓ (Submodule.span K' (Set.range fun _ : Fin 1 ↦ v)).restrictScalars (𝓞 K')).toAddSubgroup = (multiplierIdeal y).toAddSubgroup.map f`. Use extensionality with `x`. Simplify using `only [Submodule.mem_toAddSubgroup, Submodule.mem_inf, Submodule.restrictScalars_mem, Set.range_const, Submodule.mem_span_singleton, AddSubgroup.mem_map]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hxL, a, rfl⟩`. Conclude with `⟨a, (hDual K r N F φ hφ K' v a).mp hxL, rfl⟩`. Introduce and unpack `⟨a, ha, rfl⟩`. Conclude with `⟨(hDual K r N F φ hφ K' v a).mpr ha, a, rfl⟩`.

Establish `e2 : (Submodule.span (𝓞 K') (Set.range fun _ : Fin 1 ↦ v)).toAddSubgroup = (1 : Submodule (𝓞 K') K').toAddSubgroup.map f`. Use extensionality with `x`. Simplify using `only [Submodule.mem_toAddSubgroup, Set.range_const, Submodule.mem_span_singleton, AddSubgroup.mem_map, Submodule.mem_one]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, rfl⟩`.

Conclude with `⟨algebraMap (𝓞 K') K' c, ⟨c, rfl⟩, (algebraMap_smul K' c v)⟩`. Introduce and unpack `⟨a, ⟨c, rfl⟩, rfl⟩`. Conclude with `⟨c, (algebraMap_smul K' c v).symm⟩`. Rewrite using `[e1, e2, genIndex, genIndex, AddSubgroup.relIndex_map_map_of_injective _ _ hf, AddSubgroup.relIndex_map_map_of_injective _ _ hf]`. Establish `hdeg : F.lineDegree K' v = normalise K' (-(-Real.log (genIndex (multiplierIdeal y).toAddSubgroup (1 : Submodule (𝓞 K') K').toAddSubgroup)) - ∑ σ' : K' →+* ℂ, Real.log (A.metric fun _ b ↦ σ' (y b)))`.

Unfold `HermLattice.lineDegree subDegree`. Express the relevant statement in the definitionally equal form `normalise K' (Real.log (genIndex ((latticeExtend K' F.lattice ⊓ _).toAddSubgroup) _) - _) = _`. Rewrite using `[hline, Finset.sum_congr rfl fun σ' _ ↦ harch σ', ← Finset.mul_sum, neg_neg]`. Rewrite using `[hdeg, hfin, normalise]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem PointHeightDegree.proof (hPts : OneBlockPoints.Statement) (hLine : LatticeLineExists.Statement)
    (hDual : LineIdealDual.Statement) (hIdx : IdealIndexPlaces.Statement) :
    PointHeightDegree.Statement := by
  intro K _ _ r N F φ hφ
  refine ⟨hLine K r N F φ hφ, ?_⟩
  intro A hA hagree K' _ _ _ v hv τ
  set y : Fin (N + 1) → K' := latticeValue φ v with hy_def

  have hx : latticePoint φ (τ.comp (algebraMap K K')) (fun j ↦ τ (v j)) = fun _ b ↦ τ (y b) := by
    funext u b
    simp [latticePoint, hy_def, latticeValue, map_sum, map_mul]

  have hσ : ∀ σ' : K' →+* ℂ, (fun (_ : Unit) b ↦ σ' (y b)) =
      latticePoint φ (σ'.comp (algebraMap K K')) (fun j ↦ σ' (v j)) := by
    intro σ'
    funext u b
    simp [latticePoint, hy_def, latticeValue, map_sum, map_mul]

  have hy0 : y ≠ 0 := by
    intro h0
    apply hv
    have hne : Nonempty (K' →+* ℂ) := by
      rw [← Fintype.card_pos_iff, NumberField.Embeddings.card]
      exact Module.finrank_pos
    obtain ⟨σ'⟩ := hne
    funext j0
    obtain ⟨R, hR⟩ := (hPts K r N F φ hφ).2.2 (σ'.comp (algebraMap K K')) j0
    have key : ∑ b, R b * σ' (y b) = σ' (v j0) := by
      have h1 := congrFun (hσ σ') ()
      have h2 : ∀ b, σ' (y b) = ∑ j, (σ'.comp (algebraMap K K')) (φ b j) * σ' (v j) := fun b ↦
        congrFun h1 b
      simp only [h2, Finset.mul_sum]
      rw [Finset.sum_comm]
      have h3 : ∀ j, ∑ b, R b * ((σ'.comp (algebraMap K K')) (φ b j) * σ' (v j)) =
          (∑ b, R b * (σ'.comp (algebraMap K K')) (φ b j)) * σ' (v j) := by
        intro j
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun b _ ↦ by ring
      simp only [h3, hR]
      simp
    have : σ' (v j0) = 0 := by
      rw [← key]
      simp [h0]
    exact (map_eq_zero_iff σ' σ'.injective).mp this
  have hblock : BlockNonzero (fun (_ : Unit) b ↦ y b) := fun _ h ↦ hy0 (funext fun b ↦ congrFun h b)
  rw [hx, height_eq_of_ringHom A τ (fun _ b ↦ y b) hblock]

  have hpos : ∀ w : FinitePlace K', 0 < ⨆ b, w (y b) := iSup_place_pos hy0
  have hfin : ∑ᶠ w : FinitePlace K', finiteTerm A w (fun _ b ↦ y b) =
      -Real.log (genIndex (multiplierIdeal y).toAddSubgroup (1 : Submodule (𝓞 K') K').toAddSubgroup) := by
    have hterm : ∀ w : FinitePlace K', finiteTerm A w (fun _ b ↦ y b) = Real.log (⨆ b, w (y b)) := by
      intro w
      simp [finiteTerm, hA]
    simp only [hterm]
    rw [finsum_log_eq_log_finprod hpos (hasFiniteMulSupport_iSup_place hy0)]
    have hI := hIdx K' (Fin (N + 1)) y hy0
    rw [eq_inv_of_mul_eq_one_right hI, Real.log_inv]

  have harch : ∀ σ' : K' →+* ℂ, Real.log (A.metric fun _ b ↦ σ' (y b)) =
      1 / 2 * Real.log (gramAt (F.metric (σ'.comp (algebraMap K K'))) σ' (fun _ : Fin 1 ↦ v)).det.re := by
    intro σ'
    have hw : (fun j ↦ σ' (v j)) ≠ 0 := by
      intro h
      apply hv
      funext j
      exact (map_eq_zero_iff σ' σ'.injective).mp (congrFun h j)
    rw [show (fun (_ : Unit) b ↦ σ' (y b)) = _ from hσ σ', hagree _ _ hw, Matrix.det_unique]
    have hq : 0 ≤ (star (fun j ↦ σ' (v j)) ⬝ᵥ
        (F.metric (σ'.comp (algebraMap K K')) *ᵥ fun j ↦ σ' (v j))).re :=
      le_of_lt (Complex.lt_def.mp ((F.posDef _).dotProduct_mulVec_pos hw)).1
    rw [Real.log_sqrt hq]
    simp only [gramAt]
    unfold embVec
    ring

  have hline : genIndex ((latticeExtend K' F.lattice ⊓
        (Submodule.span K' (Set.range fun _ : Fin 1 ↦ v)).restrictScalars (𝓞 K')).toAddSubgroup)
        (Submodule.span (𝓞 K') (Set.range fun _ : Fin 1 ↦ v)).toAddSubgroup =
      genIndex (multiplierIdeal y).toAddSubgroup (1 : Submodule (𝓞 K') K').toAddSubgroup := by
    let f : K' →+ (Fin (r + 1) → K') :=
      { toFun := fun a ↦ a • v, map_zero' := zero_smul _ _, map_add' := fun a a' ↦ add_smul a a' v }
    have hf : Function.Injective f := smul_left_injective K' hv
    have e1 : (latticeExtend K' F.lattice ⊓
        (Submodule.span K' (Set.range fun _ : Fin 1 ↦ v)).restrictScalars (𝓞 K')).toAddSubgroup =
        (multiplierIdeal y).toAddSubgroup.map f := by
      ext x
      simp only [Submodule.mem_toAddSubgroup, Submodule.mem_inf, Submodule.restrictScalars_mem,
        Set.range_const, Submodule.mem_span_singleton, AddSubgroup.mem_map]
      constructor
      · rintro ⟨hxL, a, rfl⟩
        exact ⟨a, (hDual K r N F φ hφ K' v a).mp hxL, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨(hDual K r N F φ hφ K' v a).mpr ha, a, rfl⟩
    have e2 : (Submodule.span (𝓞 K') (Set.range fun _ : Fin 1 ↦ v)).toAddSubgroup =
        (1 : Submodule (𝓞 K') K').toAddSubgroup.map f := by
      ext x
      simp only [Submodule.mem_toAddSubgroup, Set.range_const, Submodule.mem_span_singleton,
        AddSubgroup.mem_map, Submodule.mem_one]
      constructor
      · rintro ⟨c, rfl⟩
        exact ⟨algebraMap (𝓞 K') K' c, ⟨c, rfl⟩, (algebraMap_smul K' c v)⟩
      · rintro ⟨a, ⟨c, rfl⟩, rfl⟩
        exact ⟨c, (algebraMap_smul K' c v).symm⟩
    rw [e1, e2, genIndex, genIndex, AddSubgroup.relIndex_map_map_of_injective _ _ hf,
      AddSubgroup.relIndex_map_map_of_injective _ _ hf]

  have hdeg : F.lineDegree K' v = normalise K' (-(-Real.log
      (genIndex (multiplierIdeal y).toAddSubgroup (1 : Submodule (𝓞 K') K').toAddSubgroup)) -
      ∑ σ' : K' →+* ℂ, Real.log (A.metric fun _ b ↦ σ' (y b))) := by
    unfold HermLattice.lineDegree subDegree
    change normalise K' (Real.log (genIndex ((latticeExtend K' F.lattice ⊓ _).toAddSubgroup) _) - _) = _
    rw [hline, Finset.sum_congr rfl fun σ' _ ↦ harch σ', ← Finset.mul_sum, neg_neg]
  rw [hdeg, hfin, normalise]
  ring

end

end GroundTheory.Heights₂.Heights
