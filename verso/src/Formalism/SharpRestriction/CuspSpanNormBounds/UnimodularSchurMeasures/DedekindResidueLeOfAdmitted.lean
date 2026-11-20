import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Formalism.FlagUnipotentLattices.HalfDifferenceL1Bound
import Formalism.FlagUnipotentLattices.CoveringRadius2

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData

/- English proof (translation)
Use `h.1` as an intermediate fact. Establish `h1` using `NumberField.IsTotallyComplex.finrank E`. Establish `h2` using `NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces E`. Establish `h3` using `NumberField.InfinitePlace.card_add_two_mul_card_eq_rank E`. Unfold `Formalism.HermitianLatticesTheory.fDeg`.

Use linear arithmetic over natural numbers and integers.
-/
theorem qt_finrank (E : Type) [Field E] [NumberField E] [StarRing E] (h : Formalism.HermitianLatticesTheory.IsCMUnram E) :
    Module.finrank ℚ E = 2 * Formalism.HermitianLatticesTheory.fDeg E := by
  have := h.1
  have h1 := NumberField.IsTotallyComplex.finrank E
  have h2 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces E
  have h3 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank E
  unfold Formalism.HermitianLatticesTheory.fDeg
  omega

/- English proof (translation)
Rewrite using `[qt_finrank E h]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem qt_bound_eq (E : Type) [Field E] [NumberField E] [StarRing E] (h : Formalism.HermitianLatticesTheory.IsCMUnram E) (C : ℝ) :
    (C * Real.log (((|discr E| : ℤ) : ℝ) ^ ((1 : ℝ) / Module.finrank ℚ E))) ^ Module.finrank ℚ E =
      (C * Real.log (|(discr E : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HermitianLatticesTheory.fDeg E : ℝ))))) ^ (2 * Formalism.HermitianLatticesTheory.fDeg E) := by
  rw [qt_finrank E h]
  push_cast
  rfl

/- English proof (translation)
Take `⟨C, hC, h⟩` from `hQ`. Use `⟨C, hC, fun D E _ _ _ hE => ⟨dedekindZeta_residue E, tendsto_sub_one_mul_dedekindZeta_nhdsGT E, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[abs_of_pos (dedekindZeta_residue_pos E), ← qt_bound_eq E hE C]`. Use `h E ?_` and prove the remaining obligations. Rewrite using `[qt_finrank E hE]`.

Establish `: 0 < Formalism.HermitianLatticesTheory.fDeg E` using `Fintype.card_pos`. Use linear arithmetic over natural numbers and integers.
-/
theorem residue_admitted_of_known (hQ : Formalism.HermitianLatticeCounting.S7.DedekindZetaResidueBound) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ D : Formalism.BasicNotions.D7, adm7 D C := by
  obtain ⟨C, hC, h⟩ := hQ
  refine ⟨C, hC, fun D E _ _ _ hE => ⟨dedekindZeta_residue E, tendsto_sub_one_mul_dedekindZeta_nhdsGT E, ?_⟩⟩
  rw [abs_of_pos (dedekindZeta_residue_pos E), ← qt_bound_eq E hE C]
  refine h E ?_
  rw [qt_finrank E hE]
  have : 0 < Formalism.HermitianLatticesTheory.fDeg E := Fintype.card_pos
  omega

/- English proof (translation)
Take `⟨r, hr, hb⟩` from `h E hE`. Establish `h1` using `tendsto_nhds_unique hr (tendsto_sub_one_mul_dedekindZeta_nhdsGT E)`. Establish `h2 : r = dedekindZeta_residue E` using `by exact_mod_cast h1`. Rewrite using `[← h2]`. Conclude with `le_trans (le_abs_self r) hb`.
-/
theorem dedekind_residue_le_of_admitted (D : Formalism.BasicNotions.D7) (C : ℝ) (h : adm7 D C) (E : Type) [Field E] [NumberField E] [StarRing E]
    (hE : Formalism.HermitianLatticesTheory.IsCMUnram E) :
    dedekindZeta_residue E ≤
      (C * Real.log (|(discr E : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HermitianLatticesTheory.fDeg E : ℝ))))) ^ (2 * Formalism.HermitianLatticesTheory.fDeg E) := by
  obtain ⟨r, hr, hb⟩ := h E hE
  have h1 := tendsto_nhds_unique hr (tendsto_sub_one_mul_dedekindZeta_nhdsGT E)
  have h2 : r = dedekindZeta_residue E := by exact_mod_cast h1
  rw [← h2]
  exact le_trans (le_abs_self r) hb

section Cover

variable {N : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin N))) [DiscreteTopology L] [IsZLattice ℝ L]

def qt_basis : Module.Basis (Module.Free.ChooseBasisIndex ℤ L) ℝ (EuclideanSpace ℝ (Fin N)) :=
  (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L

/- English proof (translation)
The claim follows from `(Module.Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ L`.
-/
theorem qt_basis_span : Submodule.span ℤ (Set.range (qt_basis L)) = L :=
  (Module.Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ L

/- English proof (translation)
Use `⟨∑ i, ‖qt_basis L i‖, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Establish `hmem : ((ZSpan.floor (qt_basis L) x : Submodule.span ℤ (Set.range (qt_basis L))) : EuclideanSpace ℝ (Fin N)) ∈ (L : Set _)`. Conclude with `(qt_basis_span L).le (ZSpan.floor (qt_basis L) x).2`. Use `le_trans (Metric.infDist_le_dist_of_mem hmem) ?_` and prove the remaining obligations.

Rewrite using `[dist_eq_norm]`. Conclude with `ZSpan.norm_fract_le (qt_basis L) x`.
-/
theorem qt_bdd : BddAbove (Set.range fun x : EuclideanSpace ℝ (Fin N) => Metric.infDist x (L : Set _)) := by
  refine ⟨∑ i, ‖qt_basis L i‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hmem : ((ZSpan.floor (qt_basis L) x : Submodule.span ℤ (Set.range (qt_basis L))) : EuclideanSpace ℝ (Fin N)) ∈
      (L : Set _) := by
    exact (qt_basis_span L).le (ZSpan.floor (qt_basis L) x).2
  refine le_trans (Metric.infDist_le_dist_of_mem hmem) ?_
  rw [dist_eq_norm]
  exact ZSpan.norm_fract_le (qt_basis L) x

/- English proof (translation)
Establish `hne : Nonempty (Module.Free.ChooseBasisIndex ℤ L)`. Assume the negation of the conclusion as `hE`. Rewrite `hE` using `[not_nonempty_iff]`. Establish `h0` using `Module.finrank_eq_card_basis (qt_basis L)`. Simplify using `at h0`.

Use linear arithmetic over natural numbers and integers. Take `⟨i⟩` from `hne`. Use `set ℓ : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap ((qt_basis L).coord i) with hℓ`. Use `set y := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin N))).symm ℓ with hy`. Establish `hin : ∀ v, inner ℝ y v = (qt_basis L).coord i v` using `fun v => by`.

Rewrite using `[hy, InnerProductSpace.toDual_symm_apply]`. Both sides reduce to the same expression. Use `⟨y, fun x hx => ?_, fun h0 => ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[← qt_basis_span L]`. Use `((qt_basis L).mem_span_iff_repr_mem ℤ x).1 hx i` as an intermediate fact.

Take `⟨z, hz⟩` from `this`. Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[real_inner_comm, hin]`. Simplify using `using hz.symm`. Use `hin (qt_basis L i)` as an intermediate fact.

Rewrite `this` using `[h0, inner_zero_left]`. Simplify using `at this`.
-/
theorem qt_dual_ne (hN : 0 < N) : ∃ y ∈ dualLat L, y ≠ 0 := by
  have hne : Nonempty (Module.Free.ChooseBasisIndex ℤ L) := by
    by_contra hE
    rw [not_nonempty_iff] at hE
    have h0 := Module.finrank_eq_card_basis (qt_basis L)
    simp at h0
    omega
  obtain ⟨i⟩ := hne
  set ℓ : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap ((qt_basis L).coord i) with hℓ
  set y := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin N))).symm ℓ with hy
  have hin : ∀ v, inner ℝ y v = (qt_basis L).coord i v := fun v => by
    rw [hy, InnerProductSpace.toDual_symm_apply]; rfl
  refine ⟨y, fun x hx => ?_, fun h0 => ?_⟩
  · rw [← qt_basis_span L] at hx
    have := ((qt_basis L).mem_span_iff_repr_mem ℤ x).1 hx i
    obtain ⟨z, hz⟩ := this
    refine ⟨z, ?_⟩
    rw [real_inner_comm, hin]
    simpa using hz.symm
  · have := hin (qt_basis L i)
    rw [h0, inner_zero_left] at this
    simp at this

/- English proof (translation)
Break down `Nat.eq_zero_or_pos N with rfl | hN` into its components or cases. Use `⟨0, zero_mem _, ?_⟩` and prove the remaining obligations. Establish `: x = 0` using `Subsingleton.elim _ _`. Simplify using `[this]`. Establish `hcl : IsClosed (L : Set (EuclideanSpace ℝ (Fin N)))`.

Establish `: DiscreteTopology L.toAddSubgroup` using `(inferInstance : DiscreteTopology L)`. Conclude with `AddSubgroup.isClosed_of_discrete (H := L.toAddSubgroup)`. Take `⟨y, hy, hxy⟩` from `hcl.exists_infDist_eq_dist ⟨0, zero_mem L⟩ x`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations. Rewrite using `[← dist_eq_norm, ← hxy]`.

Establish `h1 : Metric.infDist x (L : Set _) ≤ covRad (L : Set (EuclideanSpace ℝ (Fin N)))` using `le_ciSup (qt_bdd L) x`. Establish `h0 : 0 ≤ covRad (L : Set (EuclideanSpace ℝ (Fin N)))` using `le_trans Metric.infDist_nonneg h1`. Establish `h2 : κ ≤ firstMin (dualLat L)`. Take `⟨y0, hy0, hy0'⟩` from `qt_dual_ne L hN`. Use `le_csInf ⟨‖y0‖, y0, hy0, hy0', rfl⟩ ?_` and prove the remaining obligations.

Introduce and unpack `r ⟨z, hz, hz', rfl⟩`. Conclude with `hd z hz hz'`. Establish `h3 : covRad (L : Set (EuclideanSpace ℝ (Fin N))) * κ ≤ (N : ℝ) / 2` using `le_trans (mul_le_mul_of_nonneg_left h2 h0) h5`. Use `le_trans h1 ?_` and prove the remaining obligations. Rewrite using `[le_div_iff₀ (by positivity)]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem qt_cover (h5 : covRad (L : Set (EuclideanSpace ℝ (Fin N))) * firstMin (dualLat L) ≤ (N : ℝ) / 2)
    (κ : ℝ) (hκ : 0 < κ) (hd : ∀ y ∈ dualLat L, y ≠ 0 → κ ≤ ‖y‖) (x : EuclideanSpace ℝ (Fin N)) :
    ∃ y ∈ L, ‖x - y‖ ≤ (N : ℝ) / (2 * κ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨0, zero_mem _, ?_⟩
    have : x = 0 := Subsingleton.elim _ _
    simp [this]
  have hcl : IsClosed (L : Set (EuclideanSpace ℝ (Fin N))) := by
    have : DiscreteTopology L.toAddSubgroup := (inferInstance : DiscreteTopology L)
    exact AddSubgroup.isClosed_of_discrete (H := L.toAddSubgroup)
  obtain ⟨y, hy, hxy⟩ := hcl.exists_infDist_eq_dist ⟨0, zero_mem L⟩ x
  refine ⟨y, hy, ?_⟩
  rw [← dist_eq_norm, ← hxy]
  have h1 : Metric.infDist x (L : Set _) ≤ covRad (L : Set (EuclideanSpace ℝ (Fin N))) :=
    le_ciSup (qt_bdd L) x
  have h0 : 0 ≤ covRad (L : Set (EuclideanSpace ℝ (Fin N))) := le_trans Metric.infDist_nonneg h1
  have h2 : κ ≤ firstMin (dualLat L) := by
    obtain ⟨y0, hy0, hy0'⟩ := qt_dual_ne L hN
    refine le_csInf ⟨‖y0‖, y0, hy0, hy0', rfl⟩ ?_
    rintro r ⟨z, hz, hz', rfl⟩
    exact hd z hz hz'
  have h3 : covRad (L : Set (EuclideanSpace ℝ (Fin N))) * κ ≤ (N : ℝ) / 2 :=
    le_trans (mul_le_mul_of_nonneg_left h2 h0) h5
  refine le_trans h1 ?_
  rw [le_div_iff₀ (by positivity)]
  nlinarith

end Cover

/- English proof (translation)
Introduce `V _ _ _ M hM hspan κ hκ hd x`. Use `set N := Module.finrank ℝ V with hN`. Set `e : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)` to `(stdOrthonormalBasis ℝ V).repr`. Set `eZ : V →ₗ[ℤ] EuclideanSpace ℝ (Fin N)` to `(e.toLinearEquiv.toLinearMap).restrictScalars ℤ`. Establish `heZ : ∀ v, eZ v = e v` using `fun v => rfl`.

Set `L : Submodule ℤ (EuclideanSpace ℝ (Fin N))` to `M.map eZ`. Establish `hback : ∀ y : L, e.symm (y : EuclideanSpace ℝ (Fin N)) ∈ M`. Introduce and unpack `⟨y, v, hv, rfl⟩`. Simplify `hv` using `[heZ]`. Establish `hdisc : DiscreteTopology L`.

Use `hM` as an intermediate fact. Use `DiscreteTopology.of_continuous_injective (f := fun y : L => (⟨e.symm y, hback y⟩ : M)) ?_ ?_` and prove the remaining obligations. Conclude with `Continuous.subtype_mk (e.symm.continuous.comp continuous_subtype_val) _`. Introduce `a b hab`. Use `congrArg Subtype.val hab` as an intermediate fact.

Conclude with `Subtype.ext (e.symm.injective this)`. Establish `hlat : IsZLattice ℝ L`. Use `⟨?_⟩` and prove the remaining obligations. Establish `h1 : ((L : Submodule ℤ _) : Set (EuclideanSpace ℝ (Fin N))) = e.toLinearEquiv.toLinearMap '' (M : Set V)` using `rfl`. Rewrite using `[h1, Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]`.

Establish `h5` using `h N L hlat`. Establish `hd' : ∀ y ∈ dualLat L, y ≠ 0 → κ ≤ ‖y‖`. Introduce `y hy hy0`. Establish `h1 : e.symm y ∈ Formalism.HadamardInequality.zdual M`. Introduce `v hv`.

Take `⟨z, hz⟩` from `hy (e v) ⟨v, hv, rfl⟩`. Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[← hz, ← e.inner_map_map, e.apply_symm_apply]`. Establish `h2 : e.symm y ≠ 0` using `fun h0 => hy0 (by simpa using congrArg e h0)`. Use `hd _ h1 h2` as an intermediate fact.

Rewrite `this` using `[e.symm.norm_map]`. Then use the resulting hypothesis. Take `⟨y, ⟨v, hv, rfl⟩, hy⟩` from `qt_cover L h5 κ hκ hd' (e x)`. Use `⟨v, hv, ?_⟩` and prove the remaining obligations. Rewrite `hy` using `[heZ, ← map_sub, e.norm_map]`. Conclude with `hy`.
-/
theorem cover_radius_of_admitted (D : Formalism.BasicNotions.D7) (h : adm5 D) : Formalism.HermitianLatticeCounting.S7.CoveringRadius2 := by
  intro V _ _ _ M hM hspan κ hκ hd x
  set N := Module.finrank ℝ V with hN
  let e : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N) := (stdOrthonormalBasis ℝ V).repr
  let eZ : V →ₗ[ℤ] EuclideanSpace ℝ (Fin N) := (e.toLinearEquiv.toLinearMap).restrictScalars ℤ
  have heZ : ∀ v, eZ v = e v := fun v => rfl
  let L : Submodule ℤ (EuclideanSpace ℝ (Fin N)) := M.map eZ
  have hback : ∀ y : L, e.symm (y : EuclideanSpace ℝ (Fin N)) ∈ M := by
    rintro ⟨y, v, hv, rfl⟩
    simpa [heZ] using hv
  have hdisc : DiscreteTopology L := by
    have := hM
    refine DiscreteTopology.of_continuous_injective (f := fun y : L => (⟨e.symm y, hback y⟩ : M)) ?_ ?_
    · exact Continuous.subtype_mk (e.symm.continuous.comp continuous_subtype_val) _
    · intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext (e.symm.injective this)
  have hlat : IsZLattice ℝ L := by
    refine ⟨?_⟩
    have h1 : ((L : Submodule ℤ _) : Set (EuclideanSpace ℝ (Fin N))) = e.toLinearEquiv.toLinearMap '' (M : Set V) := rfl
    rw [h1, Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  have h5 := h N L hlat
  have hd' : ∀ y ∈ dualLat L, y ≠ 0 → κ ≤ ‖y‖ := by
    intro y hy hy0
    have h1 : e.symm y ∈ Formalism.HadamardInequality.zdual M := by
      intro v hv
      obtain ⟨z, hz⟩ := hy (e v) ⟨v, hv, rfl⟩
      refine ⟨z, ?_⟩
      rw [← hz, ← e.inner_map_map, e.apply_symm_apply]
    have h2 : e.symm y ≠ 0 := fun h0 => hy0 (by simpa using congrArg e h0)
    have := hd _ h1 h2
    rwa [e.symm.norm_map] at this
  obtain ⟨y, ⟨v, hv, rfl⟩, hy⟩ := qt_cover L h5 κ hκ hd' (e x)
  refine ⟨v, hv, ?_⟩
  rw [heZ, ← map_sub, e.norm_map] at hy
  exact hy

/- English proof (translation)
Introduce `N L hdisc hlat`. Establish `hnn : 0 ≤ firstMin (dualLat L)`. Use `Real.sInf_nonneg ?_` and prove the remaining obligations. Introduce and unpack `r ⟨y, -, -, rfl⟩`. Conclude with `norm_nonneg _`.

Break down `hnn.eq_or_lt with h0 | hpos` into its components or cases. Rewrite using `[← h0, mul_zero]`. Check the signs of the components of the expression. Establish `hd : ∀ y ∈ Formalism.HadamardInequality.zdual L, y ≠ 0 → firstMin (dualLat L) ≤ ‖y‖`. Introduce `y hy hy0`.

Use `csInf_le ⟨0, ?_⟩ ⟨y, hy, hy0, rfl⟩` and prove the remaining obligations. Introduce and unpack `r ⟨z, -, -, rfl⟩`. Conclude with `norm_nonneg _`. Establish `hc : covRad (L : Set (EuclideanSpace ℝ (Fin N))) ≤ (N : ℝ) / (2 * firstMin (dualLat L))`. Use `ciSup_le fun x => ?_` and prove the remaining obligations.

Take `⟨y, hy, hxy⟩` from `h (EuclideanSpace ℝ (Fin N)) L hdisc hlat.span_top _ hpos hd x`. Use `le_trans (Metric.infDist_le_dist_of_mem hy) ?_` and prove the remaining obligations. Rewrite using `[dist_eq_norm]`. Simplify using `using hxy`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem admitted_of_cover_radius (D : Formalism.BasicNotions.D7) (h : Formalism.HermitianLatticeCounting.S7.CoveringRadius2) : adm5 D := by
  intro N L hdisc hlat
  have hnn : 0 ≤ firstMin (dualLat L) := by
    refine Real.sInf_nonneg ?_
    rintro r ⟨y, -, -, rfl⟩
    exact norm_nonneg _
  rcases hnn.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; positivity
  have hd : ∀ y ∈ Formalism.HadamardInequality.zdual L, y ≠ 0 → firstMin (dualLat L) ≤ ‖y‖ := by
    intro y hy hy0
    refine csInf_le ⟨0, ?_⟩ ⟨y, hy, hy0, rfl⟩
    rintro r ⟨z, -, -, rfl⟩
    exact norm_nonneg _
  have hc : covRad (L : Set (EuclideanSpace ℝ (Fin N))) ≤ (N : ℝ) / (2 * firstMin (dualLat L)) := by
    refine ciSup_le fun x => ?_
    obtain ⟨y, hy, hxy⟩ := h (EuclideanSpace ℝ (Fin N)) L hdisc hlat.span_top _ hpos hd x
    refine le_trans (Metric.infDist_le_dist_of_mem hy) ?_
    rw [dist_eq_norm]
    simpa using hxy
  calc covRad (L : Set (EuclideanSpace ℝ (Fin N))) * firstMin (dualLat L)
      ≤ (N : ℝ) / (2 * firstMin (dualLat L)) * firstMin (dualLat L) := mul_le_mul_of_nonneg_right hc hnn
    _ = (N : ℝ) / 2 := by field_simp

/- English proof (translation)
Assemble the required witnesses or components as `⟨cover_radius_of_admitted D, admitted_of_cover_radius D⟩`.
-/
theorem admitted_iff_cover_radius (D : Formalism.BasicNotions.D7) : adm5 D ↔ Formalism.HermitianLatticeCounting.S7.CoveringRadius2 :=
  ⟨cover_radius_of_admitted D, admitted_of_cover_radius D⟩

end Formalism.MainNotions.LeviCoordinates
