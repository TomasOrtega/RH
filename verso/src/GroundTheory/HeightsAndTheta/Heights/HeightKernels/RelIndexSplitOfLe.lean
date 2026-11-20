import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StdCoordMapInjective
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesQuotIndex
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors

noncomputable section

namespace QuotientDegreeSplitAlt

/- English proof (translation)
Establish `h1 : (C.map π).relIndex (A.map π) = (C ⊔ π.ker).relIndex A`. Rewrite using `[← AddSubgroup.relIndex_comap, AddSubgroup.comap_map_eq]`. Establish `hmod : (A ⊓ π.ker) ⊔ C = (C ⊔ π.ker) ⊓ A`. Use extensionality with `x`. Simplify using `only [AddSubgroup.mem_sup, AddSubgroup.mem_inf]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, ⟨hyA, hyW⟩, z, hz, rfl⟩`. Conclude with `⟨⟨z, hz, y, hyW, add_comm z y⟩, add_mem hyA (hCA hz)⟩`. Introduce and unpack `⟨⟨y, hy, z, hz, rfl⟩, hA⟩`. Use `⟨z, ⟨?_, hz⟩, y, hy, add_comm z y⟩` and prove the remaining obligations.

Establish `hz' : z = (y + z) - y` using `by abel`. Rewrite using `[hz']`. Conclude with `sub_mem hA (hCA hy)`. Establish `h2 : C.relIndex ((C ⊔ π.ker) ⊓ A) = C.relIndex (A ⊓ π.ker)`. Rewrite using `[← hmod, AddSubgroup.relIndex_sup_right]`.

Rewrite using `[h1, ← h2, AddSubgroup.relIndex_inf_mul_relIndex, inf_of_le_left le_sup_left]`.
-/
theorem relIndex_split_of_le {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (π : G →+ G')
    {A C : AddSubgroup G} (hCA : C ≤ A) :
    C.relIndex A = C.relIndex (A ⊓ π.ker) * (C.map π).relIndex (A.map π) := by
  have h1 : (C.map π).relIndex (A.map π) = (C ⊔ π.ker).relIndex A := by
    rw [← AddSubgroup.relIndex_comap, AddSubgroup.comap_map_eq]
  have hmod : (A ⊓ π.ker) ⊔ C = (C ⊔ π.ker) ⊓ A := by
    ext x
    simp only [AddSubgroup.mem_sup, AddSubgroup.mem_inf]
    constructor
    · rintro ⟨y, ⟨hyA, hyW⟩, z, hz, rfl⟩
      exact ⟨⟨z, hz, y, hyW, add_comm z y⟩, add_mem hyA (hCA hz)⟩
    · rintro ⟨⟨y, hy, z, hz, rfl⟩, hA⟩
      refine ⟨z, ⟨?_, hz⟩, y, hy, add_comm z y⟩
      have hz' : z = (y + z) - y := by abel
      rw [hz']
      exact sub_mem hA (hCA hy)
  have h2 : C.relIndex ((C ⊔ π.ker) ⊓ A) = C.relIndex (A ⊓ π.ker) := by
    rw [← hmod, AddSubgroup.relIndex_sup_right]
  rw [h1, ← h2, AddSubgroup.relIndex_inf_mul_relIndex, inf_of_le_left le_sup_left]

/- English proof (translation)
Establish `hDA : (A ⊓ C).map π ≤ A.map π` using `AddSubgroup.map_mono inf_le_left`. Establish `hDC : (A ⊓ C).map π ≤ C.map π` using `AddSubgroup.map_mono inf_le_right`. Establish `hA : C.relIndex A = (A ⊓ C).relIndex (A ⊓ π.ker) * (((A ⊓ C).map π).relIndex (A.map π ⊓ C.map π) * (C.map π).relIndex (A.map π))`. Rewrite using `[← AddSubgroup.inf_relIndex_left A C, relIndex_split_of_le π (inf_le_left : A ⊓ C ≤ A), inf_comm (A.map π), AddSubgroup.relIndex_inf_mul_relIndex, inf_of_le_left hDC]`. Establish `hC : A.relIndex C = (A ⊓ C).relIndex (C ⊓ π.ker) * (((A ⊓ C).map π).relIndex (A.map π ⊓ C.map π) * (A.map π).relIndex (C.map π))`.

Rewrite using `[← AddSubgroup.inf_relIndex_right A C, relIndex_split_of_le π (inf_le_right : A ⊓ C ≤ C), AddSubgroup.relIndex_inf_mul_relIndex, inf_of_le_left hDA]`. Establish `hW1 : (C ⊓ π.ker).relIndex (A ⊓ π.ker) = (A ⊓ C).relIndex (A ⊓ π.ker)`. Rewrite using `[← AddSubgroup.inf_relIndex_right (C ⊓ π.ker), ← AddSubgroup.inf_relIndex_right (A ⊓ C)]`. Use `congr 1`. Use extensionality with `x`.

Simplify using `only [AddSubgroup.mem_inf]`. The claim follows by propositional logic. Establish `hW2 : (A ⊓ π.ker).relIndex (C ⊓ π.ker) = (A ⊓ C).relIndex (C ⊓ π.ker)`. Rewrite using `[← AddSubgroup.inf_relIndex_right (A ⊓ π.ker), ← AddSubgroup.inf_relIndex_right (A ⊓ C)]`. Use `congr 1`.

Use extensionality with `x`. Simplify using `only [AddSubgroup.mem_inf]`. The claim follows by propositional logic. Establish `he : ((((A ⊓ C).map π).relIndex (A.map π ⊓ C.map π) : ℕ) : ℝ) ≠ 0`. Introduce `h0`.

Establish `hz : genIndex A C = 0`. Unfold `genIndex`. Rewrite using `[hA]`. Use `push_cast`. Rewrite using `[h0]`.

Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Unfold `genIndex`. Rewrite using `[hA, hC, hW1, hW2]`. Use `push_cast`.

Rewrite using `[div_mul_div_comm, mul_left_comm (((A ⊓ C).relIndex (A ⊓ π.ker) : ℕ) : ℝ), mul_left_comm (((A ⊓ C).relIndex (C ⊓ π.ker) : ℕ) : ℝ), mul_div_mul_left _ _ he]`.
-/
theorem genIndex_split {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (π : G →+ G')
    (A C : AddSubgroup G) (hpos : 0 < genIndex A C) :
    genIndex A C = genIndex (A ⊓ π.ker) (C ⊓ π.ker) * genIndex (A.map π) (C.map π) := by
  have hDA : (A ⊓ C).map π ≤ A.map π := AddSubgroup.map_mono inf_le_left
  have hDC : (A ⊓ C).map π ≤ C.map π := AddSubgroup.map_mono inf_le_right
  have hA : C.relIndex A = (A ⊓ C).relIndex (A ⊓ π.ker) * (((A ⊓ C).map π).relIndex
      (A.map π ⊓ C.map π) * (C.map π).relIndex (A.map π)) := by
    rw [← AddSubgroup.inf_relIndex_left A C, relIndex_split_of_le π (inf_le_left : A ⊓ C ≤ A),
      inf_comm (A.map π), AddSubgroup.relIndex_inf_mul_relIndex, inf_of_le_left hDC]
  have hC : A.relIndex C = (A ⊓ C).relIndex (C ⊓ π.ker) * (((A ⊓ C).map π).relIndex
      (A.map π ⊓ C.map π) * (A.map π).relIndex (C.map π)) := by
    rw [← AddSubgroup.inf_relIndex_right A C, relIndex_split_of_le π (inf_le_right : A ⊓ C ≤ C),
      AddSubgroup.relIndex_inf_mul_relIndex, inf_of_le_left hDA]
  have hW1 : (C ⊓ π.ker).relIndex (A ⊓ π.ker) = (A ⊓ C).relIndex (A ⊓ π.ker) := by
    rw [← AddSubgroup.inf_relIndex_right (C ⊓ π.ker), ← AddSubgroup.inf_relIndex_right (A ⊓ C)]
    congr 1
    ext x
    simp only [AddSubgroup.mem_inf]
    tauto
  have hW2 : (A ⊓ π.ker).relIndex (C ⊓ π.ker) = (A ⊓ C).relIndex (C ⊓ π.ker) := by
    rw [← AddSubgroup.inf_relIndex_right (A ⊓ π.ker), ← AddSubgroup.inf_relIndex_right (A ⊓ C)]
    congr 1
    ext x
    simp only [AddSubgroup.mem_inf]
    tauto
  have he : ((((A ⊓ C).map π).relIndex (A.map π ⊓ C.map π) : ℕ) : ℝ) ≠ 0 := by
    intro h0
    have hz : genIndex A C = 0 := by
      unfold genIndex
      rw [hA]
      push_cast
      rw [h0]
      simp
    linarith
  unfold genIndex
  rw [hA, hC, hW1, hW2]
  push_cast
  rw [div_mul_div_comm, mul_left_comm (((A ⊓ C).relIndex (A ⊓ π.ker) : ℕ) : ℝ),
    mul_left_comm (((A ⊓ C).relIndex (C ⊓ π.ker) : ℕ) : ℝ), mul_div_mul_left _ _ he]

end QuotientDegreeSplitAlt

open QuotientDegreeSplitAlt in

/- English proof (translation)
Introduce `K _ _ n Λ H hFG hspan m k b c hli hmk`. Establish `hcard : Fintype.card (Fin m ⊕ Fin k) = Module.finrank K (Fin n → K)`. Simplify using `[hmk]`. Use `set B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K) := basisOfLinearIndependentOfCardEqFinrank' (Sum.elim b c) hli hcard with hBdef`. Establish `hB : ⇑B = Sum.elim b c` using `coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _`.

Establish `hBl : (fun i => B (Sum.inl i)) = b`. Use function extensionality and compare the values at `i`. Simplify using `[hB]`. Use `set W : Submodule (𝓞 K) (Fin n → K) := (Submodule.span K (Set.range b)).restrictScalars (𝓞 K) with hWdef`. Use `set π' : (Fin n → K) →ₗ[𝓞 K] (Fin k → K) := (coordProj B).restrictScalars (𝓞 K) with hπ'`.

Establish `hkerK : ∀ v, coordProj B v = 0 ↔ v ∈ Submodule.span K (Set.range b)`. Introduce `v`. Rewrite using `[← LinearMap.mem_ker, KLinesQuotIndex.ker_coordProj, hBl]`. Establish `hb0 : ∀ i, coordProj B (b i) = 0` using `fun i => (hkerK _).mpr (Submodule.subset_span ⟨i, rfl⟩)`. Establish `hc1 : ∀ j, coordProj B (c j) = Pi.single j 1`.

Introduce `j`. Establish `hcj : c j = B (Sum.inr j)` using `by simp [hB]`. Rewrite using `[hcj]`. Use function extensionality and compare the values at `j'`. Simplify using `[coordProj, Pi.single_apply, Finsupp.single_apply]`.

Distinguish the cases in `h : j = j'`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`. Use `set O : Submodule (𝓞 K) (Fin n → K) := Submodule.span (𝓞 K) (Set.range (Sum.elim b c)) with hOdef`.

Establish `htop : Submodule.span K (Set.range (Sum.elim b c)) = ⊤` using `hli.span_eq_top_of_card_eq_finrank' hcard`. Establish `hOspan : Submodule.span K (O : Set (Fin n → K)) = ⊤`. Rewrite using `[hOdef, Submodule.span_span_of_tower, htop]`. Establish `hΛlat : Submodule.IsLattice ℚ (Λ.restrictScalars ℤ)` using `LinesIsLattice.full K (Fin n) Λ hFG.restrictScalars hspan`. Establish `hOlat : Submodule.IsLattice ℚ (O.restrictScalars ℤ)` using `LinesIsLattice.full K (Fin n) O (Submodule.fg_span (Set.finite_range _)).restrictScalars hOspan`.

Establish `hpos : 0 < genIndex Λ.toAddSubgroup O.toAddSubgroup` using `(LinesGenIndexTrans.full (Fin n → K) (Λ.restrictScalars ℤ) (O.restrictScalars ℤ) (O.restrictScalars ℤ) hΛlat hOlat hOlat).1`. Establish `hker : (π' : (Fin n → K) →+ (Fin k → K)).ker = W.toAddSubgroup`. Use extensionality with `v`. Rewrite using `[AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, hWdef, Submodule.restrictScalars_mem, ← hkerK]`. Both sides reduce to the same expression.

Establish `hOW : O ⊓ W = Submodule.span (𝓞 K) (Set.range b)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `x ⟨hxO, hxW⟩`. Take `⟨r, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hxO`. Establish `h0 : π' (∑ i, r i • Sum.elim b c i) = 0` using `(hkerK _).mpr hxW`.

Rewrite `h0`, the goal using `[Fintype.sum_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr] at h0 ⊢`. Establish `hs : ∀ j, r (Sum.inr j) = 0`. Introduce `j`. Establish `h1` using `congrFun h0 j`.

Simplify using `only [map_add, map_sum, map_smul, hπ', LinearMap.restrictScalars_apply, hb0, hc1, smul_zero, Finset.sum_const_zero, zero_add, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.zero_apply] at h1`. Conclude with `(smul_eq_zero.mp h1).resolve_right one_ne_zero`. Simplify using `only [hs, zero_smul, Finset.sum_const_zero, add_zero]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Use `le_inf (Submodule.span_mono ?_) (Submodule.span_le_restrictScalars (𝓞 K) K _)` and prove the remaining obligations.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨Sum.inl i, rfl⟩`. Establish `hOmap : O.map π' = Submodule.span (𝓞 K) (Set.range (coordProj B ∘ c))`. Establish `hcomp : ⇑π' ∘ Sum.elim b c = Sum.elim (fun _ => 0) (coordProj B ∘ c)`. Use function extensionality and compare the values at `x`.

Break down `x with i | j` into its components or cases. Conclude with `hb0 i`. Both sides reduce to the same expression. Rewrite using `[hOdef, Submodule.map_span, ← Set.range_comp, hcomp, Set.Sum.elim_range, Submodule.span_union]`. Establish `hbot : Submodule.span (𝓞 K) (Set.range (fun _ : Fin m => (0 : Fin k → K))) = ⊥` using `Submodule.span_eq_bot.mpr (by rintro _ ⟨i, rfl⟩; rfl)`.

Rewrite using `[hbot, bot_sup_eq]`. Establish `hsplit` using `genIndex_split (π' : (Fin n → K) →+ (Fin k → K)) Λ.toAddSubgroup O.toAddSubgroup hpos`. Rewrite `hsplit` using `[hker, ← Submodule.map_toAddSubgroup, ← Submodule.map_toAddSubgroup, hOmap]`. Establish `hinf1 : Λ.toAddSubgroup ⊓ W.toAddSubgroup = (Λ ⊓ W).toAddSubgroup` using `rfl`. Establish `hinf2 : O.toAddSubgroup ⊓ W.toAddSubgroup = (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup`.

Rewrite using `[← hOW]`. Both sides reduce to the same expression. Rewrite `hsplit` using `[hinf1, hinf2]`. Establish `hq` using `LinesQuotIndex.full K n m k B Λ c`. Rewrite `hq` using `[hBl]`.

Use `set x := genIndex (Λ ⊓ W).toAddSubgroup (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup with hx`. Use `set y := genIndex (Λ.map π').toAddSubgroup (Submodule.span (𝓞 K) (Set.range (coordProj B ∘ c))).toAddSubgroup with hy`. Establish `hx0 : 0 ≤ x` using `div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)`. Establish `hy0 : 0 ≤ y` using `div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)`. Establish `hxy : 0 < x * y` using `hsplit ▸ hpos`.

Establish `hxne : x ≠ 0` using `by rintro h; rw [h, zero_mul] at hxy; exact lt_irrefl _ hxy`. Establish `hyne : y ≠ 0` using `by rintro h; rw [h, mul_zero] at hxy; exact lt_irrefl _ hxy`. Unfold `quotDegree subDegree`. Rewrite using `[htop, Submodule.restrictScalars_top, inf_top_eq, hq, hsplit, Real.log_mul hxne hyne, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem S6.QuotientDegreeSplit.proof : S6.QuotientDegreeSplit.Statement := by
  intro K _ _ n Λ H hFG hspan m k b c hli hmk
  have hcard : Fintype.card (Fin m ⊕ Fin k) = Module.finrank K (Fin n → K) := by
    simp [hmk]
  set B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K) :=
    basisOfLinearIndependentOfCardEqFinrank' (Sum.elim b c) hli hcard with hBdef
  have hB : ⇑B = Sum.elim b c := coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  have hBl : (fun i => B (Sum.inl i)) = b := by
    funext i; simp [hB]
  set W : Submodule (𝓞 K) (Fin n → K) :=
    (Submodule.span K (Set.range b)).restrictScalars (𝓞 K) with hWdef
  set π' : (Fin n → K) →ₗ[𝓞 K] (Fin k → K) := (coordProj B).restrictScalars (𝓞 K) with hπ'
  have hkerK : ∀ v, coordProj B v = 0 ↔ v ∈ Submodule.span K (Set.range b) := by
    intro v
    rw [← LinearMap.mem_ker, KLinesQuotIndex.ker_coordProj, hBl]
  have hb0 : ∀ i, coordProj B (b i) = 0 := fun i =>
    (hkerK _).mpr (Submodule.subset_span ⟨i, rfl⟩)
  have hc1 : ∀ j, coordProj B (c j) = Pi.single j 1 := by
    intro j
    have hcj : c j = B (Sum.inr j) := by simp [hB]
    rw [hcj]
    funext j'
    simp [coordProj, Pi.single_apply, Finsupp.single_apply]
    by_cases h : j = j'
    · subst h; simp
    · simp [h, Ne.symm h]

  set O : Submodule (𝓞 K) (Fin n → K) := Submodule.span (𝓞 K) (Set.range (Sum.elim b c)) with hOdef
  have htop : Submodule.span K (Set.range (Sum.elim b c)) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' hcard
  have hOspan : Submodule.span K (O : Set (Fin n → K)) = ⊤ := by
    rw [hOdef, Submodule.span_span_of_tower, htop]
  have hΛlat : Submodule.IsLattice ℚ (Λ.restrictScalars ℤ) :=
    LinesIsLattice.full K (Fin n) Λ hFG.restrictScalars hspan
  have hOlat : Submodule.IsLattice ℚ (O.restrictScalars ℤ) :=
    LinesIsLattice.full K (Fin n) O (Submodule.fg_span (Set.finite_range _)).restrictScalars hOspan
  have hpos : 0 < genIndex Λ.toAddSubgroup O.toAddSubgroup :=
    (LinesGenIndexTrans.full (Fin n → K) (Λ.restrictScalars ℤ) (O.restrictScalars ℤ)
      (O.restrictScalars ℤ) hΛlat hOlat hOlat).1

  have hker : (π' : (Fin n → K) →+ (Fin k → K)).ker = W.toAddSubgroup := by
    ext v
    rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, hWdef, Submodule.restrictScalars_mem,
      ← hkerK]
    rfl

  have hOW : O ⊓ W = Submodule.span (𝓞 K) (Set.range b) := by
    apply le_antisymm
    · rintro x ⟨hxO, hxW⟩
      obtain ⟨r, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hxO
      have h0 : π' (∑ i, r i • Sum.elim b c i) = 0 := (hkerK _).mpr hxW
      rw [Fintype.sum_sum_type] at h0 ⊢
      simp only [Sum.elim_inl, Sum.elim_inr] at h0 ⊢
      have hs : ∀ j, r (Sum.inr j) = 0 := by
        intro j
        have h1 := congrFun h0 j
        simp only [map_add, map_sum, map_smul, hπ', LinearMap.restrictScalars_apply, hb0, hc1,
          smul_zero, Finset.sum_const_zero, zero_add, Finset.sum_apply, Pi.smul_apply,
          Pi.single_apply, smul_ite, Finset.sum_ite_eq, Finset.mem_univ, if_true,
          Pi.zero_apply] at h1
        exact (smul_eq_zero.mp h1).resolve_right one_ne_zero
      simp only [hs, zero_smul, Finset.sum_const_zero, add_zero]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · refine le_inf (Submodule.span_mono ?_) (Submodule.span_le_restrictScalars (𝓞 K) K _)
      rintro _ ⟨i, rfl⟩
      exact ⟨Sum.inl i, rfl⟩

  have hOmap : O.map π' = Submodule.span (𝓞 K) (Set.range (coordProj B ∘ c)) := by
    have hcomp : ⇑π' ∘ Sum.elim b c = Sum.elim (fun _ => 0) (coordProj B ∘ c) := by
      funext x
      rcases x with i | j
      · exact hb0 i
      · rfl
    rw [hOdef, Submodule.map_span, ← Set.range_comp, hcomp, Set.Sum.elim_range,
      Submodule.span_union]
    have hbot : Submodule.span (𝓞 K) (Set.range (fun _ : Fin m => (0 : Fin k → K))) = ⊥ :=
      Submodule.span_eq_bot.mpr (by rintro _ ⟨i, rfl⟩; rfl)
    rw [hbot, bot_sup_eq]

  have hsplit := genIndex_split (π' : (Fin n → K) →+ (Fin k → K)) Λ.toAddSubgroup O.toAddSubgroup hpos
  rw [hker, ← Submodule.map_toAddSubgroup, ← Submodule.map_toAddSubgroup, hOmap] at hsplit
  have hinf1 : Λ.toAddSubgroup ⊓ W.toAddSubgroup = (Λ ⊓ W).toAddSubgroup := rfl
  have hinf2 : O.toAddSubgroup ⊓ W.toAddSubgroup = (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup := by
    rw [← hOW]; rfl
  rw [hinf1, hinf2] at hsplit
  have hq := LinesQuotIndex.full K n m k B Λ c
  rw [hBl] at hq

  set x := genIndex (Λ ⊓ W).toAddSubgroup (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup with hx
  set y := genIndex (Λ.map π').toAddSubgroup
    (Submodule.span (𝓞 K) (Set.range (coordProj B ∘ c))).toAddSubgroup with hy
  have hx0 : 0 ≤ x := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hy0 : 0 ≤ y := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hxy : 0 < x * y := hsplit ▸ hpos
  have hxne : x ≠ 0 := by rintro h; rw [h, zero_mul] at hxy; exact lt_irrefl _ hxy
  have hyne : y ≠ 0 := by rintro h; rw [h, mul_zero] at hxy; exact lt_irrefl _ hxy
  unfold quotDegree subDegree
  rw [htop, Submodule.restrictScalars_top, inf_top_eq, hq, hsplit, Real.log_mul hxne hyne,
    Finset.sum_sub_distrib]
  ring

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
