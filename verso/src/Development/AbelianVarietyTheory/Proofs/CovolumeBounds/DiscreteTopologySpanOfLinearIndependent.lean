import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsOrthonormalOfLinearIndependent
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.LinearIndependentRealOfIntOfDiscrete

open scoped InnerProductSpace
open Module Submodule Matrix

namespace GlobalTheory

section Gram

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/- English proof (translation)
Simplify using `using Hadamard.re_det_gram_sum_smul (𝕜 := ℝ) e m`.
-/
theorem det_gram_real_sum_smul (e : ι → E) (m : Matrix ι ι ℝ) :
    (gram ℝ (fun j => ∑ i, m i j • e i)).det = m.det ^ 2 * (gram ℝ e).det := by
  simpa using Hadamard.re_det_gram_sum_smul (𝕜 := ℝ) e m

end Gram

section Def

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Establish `: Module.Finite ℤ L` using `.of_fg h`. Establish `: IsAddTorsionFree V` using `.of_isTorsionFree ℝ V`. Use `infer_instance`.
-/
theorem free_of_fg {V : Type*} [AddCommGroup V] [Module ℝ V] {L : Submodule ℤ V} (h : L.FG) :
    Module.Free ℤ L := by
  have : Module.Finite ℤ L := .of_fg h
  have : IsAddTorsionFree V := .of_isTorsionFree ℝ V
  infer_instance

open Classical in

noncomputable def spanCovol (L : Submodule ℤ E) : ℝ :=
  if h : L.FG then
    haveI : Module.Finite ℤ L := .of_fg h
    haveI : Module.Free ℤ L := free_of_fg h
    √(gram ℝ fun i => (finBasis ℤ L i : E)).det
  else 0

/- English proof (translation)
Set `w : ι → L` to `fun j => ⟨b' j, h (b' j).2⟩`. Establish `h1 : L'.toAddSubgroup.relIndex L.toAddSubgroup = (b.det w).natAbs` using `AddSubgroup.relIndex_eq_natAbs_det L'.toAddSubgroup L.toAddSubgroup h b' b`. Establish `h2 : (fun j => (b' j : E)) = fun j => ∑ i, ((b.toMatrix w).map (Int.cast : ℤ → ℝ)) i j • (b i : E)`. Use function extensionality and compare the values at `j`. Use `congrArg (fun x : L => (x : E)) (b.sum_repr (w j))` as an intermediate fact.

Simplify using `only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at this`. Simplify using `only [map_apply, Basis.toMatrix_apply, Int.cast_smul_eq_zsmul]`. Conclude with `this.symm`. Rewrite using `[h2, det_gram_real_sum_smul, h1, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, ← Int.cast_det, Nat.cast_natAbs, Int.cast_abs, Basis.det_apply]`.
-/
theorem sqrt_det_gram_eq_relIndex_mul {L' L : Submodule ℤ E} (h : L' ≤ L) (b' : Basis ι ℤ L')
    (b : Basis ι ℤ L) :
    √(gram ℝ fun i => (b' i : E)).det =
      (L'.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) * √(gram ℝ fun i => (b i : E)).det := by
  let w : ι → L := fun j => ⟨b' j, h (b' j).2⟩
  have h1 : L'.toAddSubgroup.relIndex L.toAddSubgroup = (b.det w).natAbs :=
    AddSubgroup.relIndex_eq_natAbs_det L'.toAddSubgroup L.toAddSubgroup h b' b
  have h2 : (fun j => (b' j : E)) =
      fun j => ∑ i, ((b.toMatrix w).map (Int.cast : ℤ → ℝ)) i j • (b i : E) := by
    funext j
    have := congrArg (fun x : L => (x : E)) (b.sum_repr (w j))
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at this
    simp only [map_apply, Basis.toMatrix_apply, Int.cast_smul_eq_zsmul]
    exact this.symm
  rw [h2, det_gram_real_sum_smul, h1, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
    ← Int.cast_det, Nat.cast_natAbs, Int.cast_abs, Basis.det_apply]

/- English proof (translation)
Establish `hf : Module.Finite ℤ L` using `.of_basis b`. Establish `hfg : L.FG` using `Module.Finite.iff_fg.1 hf`. Establish `: Module.Free ℤ L` using `.of_basis b`. Set `e` to `(finBasis ℤ L).indexEquiv b`. Rewrite using `[spanCovol, dif_pos hfg, sqrt_det_gram_eq_relIndex_mul le_rfl b ((finBasis ℤ L).reindex e), AddSubgroup.relIndex_self, Nat.cast_one, one_mul, ← Hadamard.det_gram_comp_equiv _ e]`.

Use `congr 3`. Use extensionality with `i`. Simplify using the standard rewrite rules.
-/
theorem spanCovol_eq_sqrt_det_gram {L : Submodule ℤ E} (b : Basis ι ℤ L) :
    spanCovol L = √(gram ℝ fun i => (b i : E)).det := by
  have hf : Module.Finite ℤ L := .of_basis b
  have hfg : L.FG := Module.Finite.iff_fg.1 hf
  have : Module.Free ℤ L := .of_basis b
  let e := (finBasis ℤ L).indexEquiv b
  rw [spanCovol, dif_pos hfg, sqrt_det_gram_eq_relIndex_mul le_rfl b ((finBasis ℤ L).reindex e),
    AddSubgroup.relIndex_self, Nat.cast_one, one_mul, ← Hadamard.det_gram_comp_equiv _ e]
  congr 3
  ext i
  simp

/- English proof (translation)
Rewrite using `[spanCovol_eq_sqrt_det_gram (Basis.span hv)]`. Simplify using the standard rewrite rules. Use the proof step `@[simp]`.
-/
theorem spanCovol_span {v : ι → E} (hv : LinearIndependent ℤ v) :
    spanCovol (span ℤ (Set.range v)) = √(gram ℝ v).det := by
  rw [spanCovol_eq_sqrt_det_gram (Basis.span hv)]
  simp

@[simp]
/- English proof (translation)
Use `spanCovol_span (E := E) (ι := Empty) (v := Empty.elim) linearIndependent_empty_type` as an intermediate fact. Rewrite `this` using `[Set.range_eq_empty, span_empty]`. Simplify using `using this`.
-/
theorem spanCovol_bot : spanCovol (⊥ : Submodule ℤ E) = 1 := by
  have := spanCovol_span (E := E) (ι := Empty) (v := Empty.elim) linearIndependent_empty_type
  rw [Set.range_eq_empty, span_empty] at this
  simpa using this

/- English proof (translation)
Establish `: Module.Finite ℤ L` using `.of_fg hL`. Establish `: Module.Free ℤ L` using `free_of_fg hL`. Set `b` to `finBasis ℤ L`. Rewrite using `[spanCovol_eq_sqrt_det_gram (b.map (L.equivMapOfInjective (T.toLinearMap.restrictScalars ℤ) T.injective)), spanCovol_eq_sqrt_det_gram b]`. Use `congr 2`.

Use extensionality with `i j`. Conclude with `T.inner_map_map _ _`.
-/
theorem spanCovol_map_linearIsometry {L : Submodule ℤ E} (hL : L.FG) (T : E →ₗᵢ[ℝ] F) :
    spanCovol (L.map (T.toLinearMap.restrictScalars ℤ)) = spanCovol L := by
  have : Module.Finite ℤ L := .of_fg hL
  have : Module.Free ℤ L := free_of_fg hL
  let b := finBasis ℤ L
  rw [spanCovol_eq_sqrt_det_gram
    (b.map (L.equivMapOfInjective (T.toLinearMap.restrictScalars ℤ) T.injective)),
    spanCovol_eq_sqrt_det_gram b]
  congr 2
  ext i j
  exact T.inner_map_map _ _

end Def

section Discrete

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/- English proof (translation)
The claim follows from `DiscreteTopology.of_continuous_injective (β := L) (f := Set.inclusion h) (continuous_inclusion h) (Set.inclusion_injective h)`.
-/
theorem discreteTopology_of_le {N L : Submodule ℤ V} [DiscreteTopology L] (h : N ≤ L) :
    DiscreteTopology N :=
  DiscreteTopology.of_continuous_injective (β := L) (f := Set.inclusion h)
    (continuous_inclusion h) (Set.inclusion_injective h)

variable [FiniteDimensional ℝ V]

/- English proof (translation)
The claim follows from `Module.Finite.iff_fg.1 inferInstance`.
-/
theorem fg_of_discrete (L : Submodule ℤ V) [DiscreteTopology L] : L.FG :=
  Module.Finite.iff_fg.1 inferInstance

/- English proof (translation)
Set `β` to `Basis.extend hv.linearIndepOn_id`. Use `⟨β.reindex (β.indexEquiv (finBasis ℝ V)), ?_⟩` and prove the remaining obligations. Rewrite using `[Basis.range_reindex, Basis.range_extend]`. Conclude with `Basis.subset_extend _`.
-/
theorem exists_basis_range_subset {ι : Type*} {v : ι → V} (hv : LinearIndependent ℝ v) :
    ∃ β : Basis (Fin (finrank ℝ V)) ℝ V, Set.range v ⊆ Set.range β := by
  let β := Basis.extend hv.linearIndepOn_id
  refine ⟨β.reindex (β.indexEquiv (finBasis ℝ V)), ?_⟩
  rw [Basis.range_reindex, Basis.range_extend]
  exact Basis.subset_extend _

/- English proof (translation)
Take `⟨β, hβ⟩` from `exists_basis_range_subset hv`. Conclude with `discreteTopology_of_le (span_mono hβ)`.
-/
theorem discreteTopology_span_of_linearIndependent {ι : Type*} {v : ι → V}
    (hv : LinearIndependent ℝ v) : DiscreteTopology (span ℤ (Set.range v)) := by
  obtain ⟨β, hβ⟩ := exists_basis_range_subset hv
  exact discreteTopology_of_le (span_mono hβ)

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/- English proof (translation)
Use `congrArg (Submodule.map L.subtype) b.span_eq` as an intermediate fact. Rewrite `this` using `[Submodule.map_span, ← Set.range_comp, map_subtype_top]`. Then use the resulting hypothesis.
-/
theorem span_range_coe_basis {ι : Type*} {L : Submodule ℤ V} (b : Basis ι ℤ L) :
    span ℤ (Set.range fun i => (b i : V)) = L := by
  have := congrArg (Submodule.map L.subtype) b.span_eq
  rwa [Submodule.map_span, ← Set.range_comp, map_subtype_top] at this

/- English proof (translation)
The claim follows from `linearIndependent_real_of_int_of_discrete L (fun i => (b i).2) (b.linearIndependent.map' L.subtype (ker_subtype L))`.
-/
theorem linearIndependent_real_coe_basis {ι : Type*} [Fintype ι] {L : Submodule ℤ V}
    [DiscreteTopology L] (b : Basis ι ℤ L) : LinearIndependent ℝ fun i => (b i : V) :=
  linearIndependent_real_of_int_of_discrete L (fun i => (b i).2)
    (b.linearIndependent.map' L.subtype (ker_subtype L))

end Discrete

section Main

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/- English proof (translation)
Rewrite using `[spanCovol_eq_sqrt_det_gram (finBasis ℤ L), covolume_eq_sqrt_det_gram L (finBasis ℤ L)]`.
-/
theorem spanCovol_eq_covolume [MeasurableSpace E] [BorelSpace E] (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] : spanCovol L = ZLattice.covolume L := by
  rw [spanCovol_eq_sqrt_det_gram (finBasis ℤ L), covolume_eq_sqrt_det_gram L (finBasis ℤ L)]

instance discreteTopology_comap_subtype (L : Submodule ℤ E) [DiscreteTopology L]
    (S : Submodule ℝ E) : DiscreteTopology (ZLattice.comap ℝ L S.subtype) :=
  ZLattice.comap_discreteTopology ℝ L continuous_subtype_val S.injective_subtype

instance isZLattice_comap_subtype_span (L : Submodule ℤ E) [DiscreteTopology L] :
    IsZLattice ℝ (ZLattice.comap ℝ L (span ℝ (L : Set E)).subtype) :=
  ⟨span_span_coe_preimage⟩

/- English proof (translation)
Apply the tactic sequence `rw [← spanCovol_map_linearIsometry (fg_of_discrete _) S.subtypeₗᵢ]`. Use `congr 1`. Conclude with `map_comap_eq_self fun x hx => ⟨⟨x, h hx⟩, rfl⟩`.
-/
theorem spanCovol_comap_subtype (L : Submodule ℤ E) [DiscreteTopology L] (S : Submodule ℝ E)
    (h : (L : Set E) ⊆ S) : spanCovol (ZLattice.comap ℝ L S.subtype) = spanCovol L := by
  rw [← spanCovol_map_linearIsometry (fg_of_discrete _) S.subtypeₗᵢ]
  congr 1
  exact map_comap_eq_self fun x hx => ⟨⟨x, h hx⟩, rfl⟩

/- English proof (translation)
Rewrite using `[← spanCovol_eq_covolume, spanCovol_comap_subtype L _ subset_span]`.
-/
theorem spanCovol_eq_covolume_comap_span [MeasurableSpace E] [BorelSpace E] (L : Submodule ℤ E)
    [DiscreteTopology L] :
    spanCovol L = ZLattice.covolume (ZLattice.comap ℝ L (span ℝ (L : Set E)).subtype) := by
  rw [← spanCovol_eq_covolume, spanCovol_comap_subtype L _ subset_span]

noncomputable def projAlong (L N : Submodule ℤ E) : Submodule ℤ E :=
  L.map ((span ℝ (N : Set E))ᗮ.starProjection.toLinearMap.restrictScalars ℤ)

end Main

end GlobalTheory
