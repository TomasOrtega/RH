import Mathlib
import GroundTheory.LocalFields.UnramifiedDefs
import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
import GroundTheory.LocalFields.FilteredSurj
import GroundTheory.GlobalFields.KummerTheory.LocalIndex

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing Filter Polynomial
open GroundTheory.Global (filtrationComplete_unitFiltration filtrationSeparated_unitFiltration
  div_mem_unitFiltration_iff)

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [FiniteDimensional K L] in

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_normIntegerUnits_eq (u : 𝒪[L]ˣ) :
    ((normIntegerUnits K L u : 𝒪[K]ˣ) : 𝒪[K]) = Algebra.norm 𝒪[K] (u : 𝒪[L]) :=
  rfl

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis 𝒪[K] 𝒪[L]`. Use `⟨(Matrix.det (1 + (X : 𝒪[K][X]) • (Algebra.leftMulMatrix b a).map C)).divX.divX.eval r, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.norm_eq_matrix_det b, map_add, map_one, map_smul, Matrix.det_one_add_smul, Algebra.trace_eq_matrix_trace b]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_norm_one_add_smul (r : 𝒪[K]) (a : 𝒪[L]) :
    ∃ c : 𝒪[K], Algebra.norm 𝒪[K] (1 + r • a) =
      1 + r * Algebra.trace 𝒪[K] 𝒪[L] a + r ^ 2 * c := by
  classical
  let b := Module.Free.chooseBasis 𝒪[K] 𝒪[L]
  refine ⟨(Matrix.det (1 + (X : 𝒪[K][X]) • (Algebra.leftMulMatrix b a).map C)).divX.divX.eval r,
    ?_⟩
  rw [Algebra.norm_eq_matrix_det b, map_add, map_one, map_smul, Matrix.det_one_add_smul,
    Algebra.trace_eq_matrix_trace b]
  ring

/- English proof (translation)
Use `conv_lhs => rw [← (Module.Free.chooseBasis 𝒪[K] 𝒪[L]).sum_repr y]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ ↦ ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_mul, Algebra.smul_def]`. Both sides reduce to the same expression.
-/
theorem residue_eq_sum_repr (y : 𝒪[L]) :
    residue 𝒪[L] y = ∑ i, residue 𝒪[K] ((Module.Free.chooseBasis 𝒪[K] 𝒪[L]).repr y i) •
      residue 𝒪[L] (Module.Free.chooseBasis 𝒪[K] 𝒪[L] i) := by
  conv_lhs => rw [← (Module.Free.chooseBasis 𝒪[K] 𝒪[L]).sum_repr y]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Algebra.smul_def, map_mul, Algebra.smul_def]
  rfl

section Residue

variable [IsUnramified K L]

variable (K L) in

def residueBasis : Module.Basis (Module.Free.ChooseBasisIndex 𝒪[K] 𝒪[L]) 𝓀[K] 𝓀[L] :=
  basisOfTopLeSpanOfCardEqFinrank (fun i ↦ residue 𝒪[L] (Module.Free.chooseBasis 𝒪[K] 𝒪[L] i))
    (by
      rintro z -
      obtain ⟨y, rfl⟩ := residue_surjective z
      rw [residue_eq_sum_repr (K := K)]
      exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    (by
      rw [← Module.finrank_eq_card_chooseBasisIndex, finrank_integer K L,
        IsUnramified.finrank_residueField K L])

/- English proof (translation)
Simplify using `[residueBasis]`.
-/
theorem residueBasis_apply (i : Module.Free.ChooseBasisIndex 𝒪[K] 𝒪[L]) :
    residueBasis K L i = residue 𝒪[L] (Module.Free.chooseBasis 𝒪[K] 𝒪[L] i) := by
  simp [residueBasis]

/- English proof (translation)
Establish `h : residue 𝒪[L] y = ∑ j, residue 𝒪[K] ((Module.Free.chooseBasis 𝒪[K] 𝒪[L]).repr y j) • residueBasis K L j`. Simplify using `only [residueBasis_apply]`. Conclude with `residue_eq_sum_repr y`. Rewrite using `[h, (residueBasis K L).repr_sum_self]`.
-/
theorem residueBasis_repr (y : 𝒪[L]) (i : Module.Free.ChooseBasisIndex 𝒪[K] 𝒪[L]) :
    (residueBasis K L).repr (residue 𝒪[L] y) i =
      residue 𝒪[K] ((Module.Free.chooseBasis 𝒪[K] 𝒪[L]).repr y i) := by
  have h : residue 𝒪[L] y = ∑ j, residue 𝒪[K] ((Module.Free.chooseBasis 𝒪[K] 𝒪[L]).repr y j) •
      residueBasis K L j := by
    simp only [residueBasis_apply]
    exact residue_eq_sum_repr y
  rw [h, (residueBasis K L).repr_sum_self]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Algebra.leftMulMatrix_eq_repr_mul, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, residueBasis_apply, ← map_mul, residueBasis_repr]`.
-/
theorem leftMulMatrix_residueBasis (y : 𝒪[L]) :
    Algebra.leftMulMatrix (residueBasis K L) (residue 𝒪[L] y) =
      (Algebra.leftMulMatrix (Module.Free.chooseBasis 𝒪[K] 𝒪[L]) y).map (residue 𝒪[K]) := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    residueBasis_apply, ← map_mul, residueBasis_repr]

/- English proof (translation)
Rewrite using `[Algebra.norm_eq_matrix_det (Module.Free.chooseBasis 𝒪[K] 𝒪[L]), Algebra.norm_eq_matrix_det (residueBasis K L), leftMulMatrix_residueBasis, RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem residue_norm (y : 𝒪[L]) :
    residue 𝒪[K] (Algebra.norm 𝒪[K] y) = Algebra.norm 𝓀[K] (residue 𝒪[L] y) := by
  classical
  rw [Algebra.norm_eq_matrix_det (Module.Free.chooseBasis 𝒪[K] 𝒪[L]),
    Algebra.norm_eq_matrix_det (residueBasis K L), leftMulMatrix_residueBasis, RingHom.map_det]
  rfl

/- English proof (translation)
Rewrite using `[Algebra.trace_eq_matrix_trace (Module.Free.chooseBasis 𝒪[K] 𝒪[L]), Algebra.trace_eq_matrix_trace (residueBasis K L), leftMulMatrix_residueBasis]`. Conclude with `AddMonoidHom.map_trace (residue 𝒪[K]).toAddMonoidHom _`.
-/
theorem residue_trace (y : 𝒪[L]) :
    residue 𝒪[K] (Algebra.trace 𝒪[K] 𝒪[L] y) = Algebra.trace 𝓀[K] 𝓀[L] (residue 𝒪[L] y) := by
  rw [Algebra.trace_eq_matrix_trace (Module.Free.chooseBasis 𝒪[K] 𝒪[L]),
    Algebra.trace_eq_matrix_trace (residueBasis K L), leftMulMatrix_residueBasis]
  exact AddMonoidHom.map_trace (residue 𝒪[K]).toAddMonoidHom _

/- English proof (translation)
Rewrite using `[IsDiscreteValuationRing.irreducible_iff_uniformizer]`. Establish `h` using `map_maximalIdeal K L`. Rewrite `h` using `[IsUnramified.ramificationIndex_eq_one, pow_one, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]`. Conclude with `h.symm`.
-/
theorem irreducible_algebraMap_of_isUnramified {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    Irreducible (algebraMap 𝒪[K] 𝒪[L] ϖ) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  have h := map_maximalIdeal K L
  rw [IsUnramified.ramificationIndex_eq_one, pow_one, hϖ.maximalIdeal_eq, Ideal.map_span,
    Set.image_singleton] at h
  exact h.symm

/- English proof (translation)
Take `⟨t, ht⟩` from `Algebra.trace_surjective 𝓀[K] 𝓀[L] 1`. Take `⟨a, rfl⟩` from `residue_surjective t`. Establish `hu : IsUnit (Algebra.trace 𝒪[K] 𝒪[L] a)`. Rewrite using `[← residue_ne_zero_iff_isUnit, residue_trace, ht]`. Conclude with `one_ne_zero`.

Introduce `c`. Use `⟨(((hu.unit⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * c) • a, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul]`. Take the linear combination `c * Units.inv_mul hu.unit - (((hu.unit⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * c) * hu.unit_spec`.
-/
theorem trace_integer_surjective : Function.Surjective (Algebra.trace 𝒪[K] 𝒪[L]) := by
  obtain ⟨t, ht⟩ := Algebra.trace_surjective 𝓀[K] 𝓀[L] 1
  obtain ⟨a, rfl⟩ := residue_surjective t
  have hu : IsUnit (Algebra.trace 𝒪[K] 𝒪[L] a) := by
    rw [← residue_ne_zero_iff_isUnit, residue_trace, ht]
    exact one_ne_zero
  intro c
  refine ⟨(((hu.unit⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * c) • a, ?_⟩
  rw [map_smul, smul_eq_mul]
  linear_combination c * Units.inv_mul hu.unit - (((hu.unit⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * c) * hu.unit_spec

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using the standard rewrite rules. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[K]`. Establish `hϖL` using `irreducible_algebraMap_of_isUnramified (L := L) hϖ`. Take `⟨a, ha⟩` from `(mem_maximalIdeal_pow_iff hϖL).mp (mem_unitFiltration.mp hu)`.

Establish `hu' : (u : 𝒪[L]) = 1 + ϖ ^ n • a`. Rewrite using `[Algebra.smul_def, map_pow, ← ha]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨c, hc⟩` from `exists_norm_one_add_smul (ϖ ^ n) a`. Rewrite using `[mem_unitFiltration, mem_maximalIdeal_pow_iff hϖ]`.

Use `⟨Algebra.trace 𝒪[K] 𝒪[L] a + ϖ ^ n * c, ?_⟩` and prove the remaining obligations. Rewrite using `[coe_normIntegerUnits_eq, hu', hc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem normIntegerUnits_mem_unitFiltration {n : ℕ} {u : 𝒪[L]ˣ} (hu : u ∈ unitFiltration L n) :
    normIntegerUnits K L u ∈ unitFiltration K n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖL := irreducible_algebraMap_of_isUnramified (L := L) hϖ
  obtain ⟨a, ha⟩ := (mem_maximalIdeal_pow_iff hϖL).mp (mem_unitFiltration.mp hu)
  have hu' : (u : 𝒪[L]) = 1 + ϖ ^ n • a := by
    rw [Algebra.smul_def, map_pow, ← ha]
    ring
  obtain ⟨c, hc⟩ := exists_norm_one_add_smul (ϖ ^ n) a
  rw [mem_unitFiltration, mem_maximalIdeal_pow_iff hϖ]
  refine ⟨Algebra.trace 𝒪[K] 𝒪[L] a + ϖ ^ n * c, ?_⟩
  rw [coe_normIntegerUnits_eq, hu', hc]
  ring

/- English proof (translation)
Take `⟨ζ, hζ⟩` from `FiniteField.unitsMap_norm_surjective 𝓀[K] 𝓀[L] (unitsToResidue K h)`. Take `⟨g, rfl⟩` from `unitsToResidue_surjective L ζ`. Use `⟨g, ?_⟩` and prove the remaining obligations. Rewrite using `[← ker_unitsToResidue, MonoidHom.mem_ker, _root_.map_div, div_eq_one, ← hζ]`. Use `ext`.

Simplify using `[coe_normIntegerUnits_eq, residue_norm]`.
-/
theorem exists_normIntegerUnits_div_mem_one (h : 𝒪[K]ˣ) :
    ∃ g : 𝒪[L]ˣ, h / normIntegerUnits K L g ∈ unitFiltration K 1 := by
  obtain ⟨ζ, hζ⟩ := FiniteField.unitsMap_norm_surjective 𝓀[K] 𝓀[L] (unitsToResidue K h)
  obtain ⟨g, rfl⟩ := unitsToResidue_surjective L ζ
  refine ⟨g, ?_⟩
  rw [← ker_unitsToResidue, MonoidHom.mem_ker, _root_.map_div, div_eq_one, ← hζ]
  ext
  simp [coe_normIntegerUnits_eq, residue_norm]

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[K]`. Establish `hϖL` using `irreducible_algebraMap_of_isUnramified (L := L) hϖ`. Take `⟨c, hc⟩` from `(mem_maximalIdeal_pow_iff hϖ).mp (mem_unitFiltration.mp hh)`. Take `⟨t, ht⟩` from `Algebra.trace_surjective 𝓀[K] 𝓀[L] (residue 𝒪[K] c)`. Take `⟨a, rfl⟩` from `residue_surjective t`.

Establish `hu` using `isUnit_one_add_mul hϖL hn a`. Use `⟨hu.unit, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_unitFiltration, IsUnit.unit_spec, add_sub_cancel_left, mem_maximalIdeal_pow_iff hϖL]`. Conclude with `dvd_mul_right _ _`. Rewrite using `[div_mem_unitFiltration_iff]`.

Take `⟨d, hd⟩` from `exists_norm_one_add_smul (ϖ ^ n) a`. Establish `e1 : ((normIntegerUnits K L hu.unit : 𝒪[K]ˣ) : 𝒪[K]) = 1 + ϖ ^ n * Algebra.trace 𝒪[K] 𝒪[L] a + (ϖ ^ n) ^ 2 * d`. Rewrite using `[coe_normIntegerUnits_eq, IsUnit.unit_spec, ← hd, Algebra.smul_def, map_pow]`. Establish `e2 : c - Algebra.trace 𝒪[K] 𝒪[L] a ∈ 𝓂[K]`. Rewrite using `[← residue_eq_zero_iff, map_sub, residue_trace, ht, sub_self]`.

Take `⟨e, he⟩` from `(mem_maximalIdeal_iff_dvd hϖ).mp e2`. Establish `hh' : (h : 𝒪[K]) = 1 + ϖ ^ n * c`. Rewrite using `[← hc]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[mem_maximalIdeal_pow_iff hϖ]`.

Use `⟨e - ϖ ^ (n - 1) * d, ?_⟩` and prove the remaining obligations. Rewrite using `[e1, hh']`. Take `⟨m, rfl⟩ : ∃ m, n = m + 1` from `⟨n - 1, by omega⟩`. Simplify using `only [Nat.add_sub_cancel]`. Take the linear combination `(ϖ ^ (m + 1)) * he`.
-/
theorem exists_normIntegerUnits_div_mem_succ {n : ℕ} (hn : 1 ≤ n) {h : 𝒪[K]ˣ}
    (hh : h ∈ unitFiltration K n) :
    ∃ g ∈ unitFiltration L n, h / normIntegerUnits K L g ∈ unitFiltration K (n + 1) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖL := irreducible_algebraMap_of_isUnramified (L := L) hϖ
  obtain ⟨c, hc⟩ := (mem_maximalIdeal_pow_iff hϖ).mp (mem_unitFiltration.mp hh)
  obtain ⟨t, ht⟩ := Algebra.trace_surjective 𝓀[K] 𝓀[L] (residue 𝒪[K] c)
  obtain ⟨a, rfl⟩ := residue_surjective t
  have hu := isUnit_one_add_mul hϖL hn a
  refine ⟨hu.unit, ?_, ?_⟩
  · rw [mem_unitFiltration, IsUnit.unit_spec, add_sub_cancel_left, mem_maximalIdeal_pow_iff hϖL]
    exact dvd_mul_right _ _
  · rw [div_mem_unitFiltration_iff]
    obtain ⟨d, hd⟩ := exists_norm_one_add_smul (ϖ ^ n) a
    have e1 : ((normIntegerUnits K L hu.unit : 𝒪[K]ˣ) : 𝒪[K]) =
        1 + ϖ ^ n * Algebra.trace 𝒪[K] 𝒪[L] a + (ϖ ^ n) ^ 2 * d := by
      rw [coe_normIntegerUnits_eq, IsUnit.unit_spec, ← hd, Algebra.smul_def, map_pow]
    have e2 : c - Algebra.trace 𝒪[K] 𝒪[L] a ∈ 𝓂[K] := by
      rw [← residue_eq_zero_iff, map_sub, residue_trace, ht, sub_self]
    obtain ⟨e, he⟩ := (mem_maximalIdeal_iff_dvd hϖ).mp e2
    have hh' : (h : 𝒪[K]) = 1 + ϖ ^ n * c := by
      rw [← hc]
      ring
    rw [mem_maximalIdeal_pow_iff hϖ]
    refine ⟨e - ϖ ^ (n - 1) * d, ?_⟩
    rw [e1, hh']
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    linear_combination (ϖ ^ (m + 1)) * he

/- English proof (translation)
The claim follows from `map_eq_of_graded_surjective (unitFiltration_antitone L) (unitFiltration_antitone K) filtrationComplete_unitFiltration filtrationSeparated_unitFiltration (normIntegerUnits K L) (φ := id) tendsto_id n (fun _ _ _ hg ↦ normIntegerUnits_mem_unitFiltration hg) (fun m _ h hh ↦ by rcases …`.
-/
theorem map_normIntegerUnits_unitFiltration (n : ℕ) :
    (unitFiltration L n).map (normIntegerUnits K L) = unitFiltration K n :=
  map_eq_of_graded_surjective (unitFiltration_antitone L) (unitFiltration_antitone K)
    filtrationComplete_unitFiltration filtrationSeparated_unitFiltration
    (normIntegerUnits K L) (φ := id) tendsto_id n
    (fun _ _ _ hg ↦ normIntegerUnits_mem_unitFiltration hg)
    (fun m _ h hh ↦ by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · obtain ⟨g, hg⟩ := exists_normIntegerUnits_div_mem_one (L := L) h
        exact ⟨g, by simp, hg⟩
      · exact exists_normIntegerUnits_div_mem_succ hm hh)

/- English proof (translation)
Introduce `h`. Establish `e` using `map_normIntegerUnits_unitFiltration (K := K) (L := L) 0`. Rewrite `e` using `[unitFiltration_zero, unitFiltration_zero]`. Establish `hh : h ∈ (⊤ : Subgroup 𝒪[L]ˣ).map (normIntegerUnits K L)`. Rewrite using `[e]`.

Conclude with `Subgroup.mem_top h`. Take `⟨g, -, rfl⟩` from `hh`. Conclude with `⟨g, rfl⟩`.
-/
theorem normIntegerUnits_surjective : Function.Surjective (normIntegerUnits K L) := by
  intro h
  have e := map_normIntegerUnits_unitFiltration (K := K) (L := L) 0
  rw [unitFiltration_zero, unitFiltration_zero] at e
  have hh : h ∈ (⊤ : Subgroup 𝒪[L]ˣ).map (normIntegerUnits K L) := by
    rw [e]
    exact Subgroup.mem_top h
  obtain ⟨g, -, rfl⟩ := hh
  exact ⟨g, rfl⟩

/- English proof (translation)
Establish `h : (normUnits K L).comp (unitsIncl L) = (unitsIncl K).comp (normIntegerUnits K L)`. Use extensionality with `u`. Simplify using `[normUnits_unitsIncl]`. Rewrite using `[unitFiltrationUnits, unitFiltrationUnits, Subgroup.map_map, h, ← Subgroup.map_map, map_normIntegerUnits_unitFiltration]`.
-/
theorem map_normUnits_unitFiltrationUnits (n : ℕ) :
    (unitFiltrationUnits L n).map (normUnits K L) = unitFiltrationUnits K n := by
  have h : (normUnits K L).comp (unitsIncl L) = (unitsIncl K).comp (normIntegerUnits K L) := by
    ext u
    simp [normUnits_unitsIncl]
  rw [unitFiltrationUnits, unitFiltrationUnits, Subgroup.map_map, h, ← Subgroup.map_map,
    map_normIntegerUnits_unitFiltration]

/- English proof (translation)
Rewrite using `[← map_normUnits_unitFiltrationUnits (L := L) 0]`. Conclude with `Subgroup.map_le_range _ _`.
-/
theorem unitFiltrationUnits_zero_le_range_normUnits :
    unitFiltrationUnits K 0 ≤ (normUnits K L).range := by
  rw [← map_normUnits_unitFiltrationUnits (L := L) 0]
  exact Subgroup.map_le_range _ _

end Residue

section NormGroup

variable (K L) in

def ordModFinrank : Kˣ →* Multiplicative (ZMod (Module.finrank K L)) where
  toFun x := Multiplicative.ofAdd ((ord (x : K) : ℤ) : ZMod (Module.finrank K L))
  map_one' := by simp [ord]
  map_mul' x y := by
    rw [Units.val_mul, ord_mul x.ne_zero y.ne_zero, Int.cast_add, ofAdd_add]

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
  [FiniteDimensional K L] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ordModFinrank_apply (x : Kˣ) :
    ordModFinrank K L x = Multiplicative.ofAdd ((ord (x : K) : ℤ) : ZMod (Module.finrank K L)) :=
  rfl

/- English proof (translation)
Introduce `z`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[K]`. Take `⟨k, hk⟩` from `ZMod.intCast_surjective (Multiplicative.toAdd z)`. Use `⟨uniformizerUnit hϖ ^ k, ?_⟩` and prove the remaining obligations. Establish `hϖ0 : (ϖ : K) ≠ 0` using `by exact_mod_cast hϖ.ne_zero`.

Rewrite using `[ordModFinrank_apply, Units.val_zpow_eq_zpow_val, coe_uniformizerUnit, ord_zpow hϖ0, ord_uniformizer hϖ, mul_one, hk]`. Both sides reduce to the same expression.
-/
theorem ordModFinrank_surjective : Function.Surjective (ordModFinrank K L) := by
  intro z
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective (Multiplicative.toAdd z)
  refine ⟨uniformizerUnit hϖ ^ k, ?_⟩
  have hϖ0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  rw [ordModFinrank_apply, Units.val_zpow_eq_zpow_val, coe_uniformizerUnit, ord_zpow hϖ0,
    ord_uniformizer hϖ, mul_one, hk]
  rfl

variable [IsUnramified K L]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Rewrite using `[coe_normUnits, ord_norm, IsUnramified.residueDegree_eq_finrank K L]`. Conclude with `dvd_mul_right _ _`. Introduce and unpack `⟨k, hk⟩`.

Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[K]`. Take `⟨⟨m, u⟩, hx⟩` from `(unitsOfIntProd_bijective hϖ).2 x`. Establish `hm : m.toAdd = Module.finrank K L * k`. Rewrite using `[← hk, ← hx, ord_unitsOfIntProd]`. Take `⟨v, hv⟩` from `normIntegerUnits_surjective (K := K) (L := L) u`.

Use `⟨Units.map (algebraMap K L : K →* L) (uniformizerUnit hϖ) ^ k * unitsIncl L v, ?_⟩` and prove the remaining obligations. Rewrite using `[← hx, unitsOfIntProd_eq, map_mul, map_zpow, normUnits_unitsIncl, hv, hm, zpow_mul]`. Use `congr 2`. Use `ext`. Simplify using `[Algebra.norm_algebraMap]`.
-/
theorem mem_range_normUnits_iff (x : Kˣ) :
    x ∈ (normUnits K L).range ↔ (Module.finrank K L : ℤ) ∣ ord (x : K) := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [coe_normUnits, ord_norm, IsUnramified.residueDegree_eq_finrank K L]
    exact dvd_mul_right _ _
  · rintro ⟨k, hk⟩
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
    obtain ⟨⟨m, u⟩, hx⟩ := (unitsOfIntProd_bijective hϖ).2 x
    have hm : m.toAdd = Module.finrank K L * k := by
      rw [← hk, ← hx, ord_unitsOfIntProd]
    obtain ⟨v, hv⟩ := normIntegerUnits_surjective (K := K) (L := L) u
    refine ⟨Units.map (algebraMap K L : K →* L) (uniformizerUnit hϖ) ^ k * unitsIncl L v, ?_⟩
    rw [← hx, unitsOfIntProd_eq, map_mul, map_zpow, normUnits_unitsIncl, hv, hm, zpow_mul]
    congr 2
    ext
    simp [Algebra.norm_algebraMap]

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[MonoidHom.mem_ker, mem_range_normUnits_iff, ordModFinrank_apply, ofAdd_eq_one, ZMod.intCast_zmod_eq_zero_iff_dvd]`.
-/
theorem ker_ordModFinrank : (ordModFinrank K L).ker = (normUnits K L).range := by
  ext x
  rw [MonoidHom.mem_ker, mem_range_normUnits_iff, ordModFinrank_apply, ofAdd_eq_one,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

variable (K L) in

def quotientRangeNormUnitsEquiv :
    Kˣ ⧸ (normUnits K L).range ≃* Multiplicative (ZMod (Module.finrank K L)) :=
  (QuotientGroup.quotientMulEquivOfEq ker_ordModFinrank.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ ordModFinrank_surjective)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem quotientRangeNormUnitsEquiv_mk (x : Kˣ) :
    quotientRangeNormUnitsEquiv K L (QuotientGroup.mk x) = ordModFinrank K L x :=
  rfl

/- English proof (translation)
Rewrite using `[Subgroup.index, Nat.card_congr (quotientRangeNormUnitsEquiv K L).toEquiv]`. Conclude with `Nat.card_zmod _`.
-/
theorem index_range_normUnits : (normUnits K L).range.index = Module.finrank K L := by
  rw [Subgroup.index, Nat.card_congr (quotientRangeNormUnitsEquiv K L).toEquiv]
  exact Nat.card_zmod _

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce and unpack `q -`. Proceed by induction on `q using QuotientGroup.induction_on with`. Consider the case `H x`. Use `⟨ord (x : K), ?_⟩` and prove the remaining obligations.

Establish `hϖ0 : (ϖ : K) ≠ 0` using `by exact_mod_cast hϖ.ne_zero`. Simplify using `only`. Rewrite using `[← QuotientGroup.mk_zpow, QuotientGroup.eq, mem_range_normUnits_iff, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, coe_uniformizerUnit, ord_mul (inv_ne_zero (zpow_ne_zero _ hϖ0)) x.ne_zero, ← zpow_neg, ord_zpow hϖ0, ord_uniformizer hϖ]`. Simplify using the standard rewrite rules.
-/
theorem zpowers_mk_uniformizerUnit {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    Subgroup.zpowers (QuotientGroup.mk (uniformizerUnit hϖ) : Kˣ ⧸ (normUnits K L).range) = ⊤ := by
  rw [eq_top_iff]
  rintro q -
  induction q using QuotientGroup.induction_on with
  | H x =>
    refine ⟨ord (x : K), ?_⟩
    have hϖ0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
    simp only
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, mem_range_normUnits_iff, Units.val_mul,
      Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, coe_uniformizerUnit,
      ord_mul (inv_ne_zero (zpow_ne_zero _ hϖ0)) x.ne_zero, ← zpow_neg, ord_zpow hϖ0,
      ord_uniformizer hϖ]
    simp

/- English proof (translation)
Rewrite using `[orderOf_eq_card_of_forall_mem_zpowers (fun q ↦ by`. Rewrite using `[zpowers_mk_uniformizerUnit hϖ]`. Conclude with `Subgroup.mem_top q)]`. Conclude with `index_range_normUnits`.
-/
theorem orderOf_mk_uniformizerUnit {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    orderOf (QuotientGroup.mk (uniformizerUnit hϖ) : Kˣ ⧸ (normUnits K L).range) =
      Module.finrank K L := by
  rw [orderOf_eq_card_of_forall_mem_zpowers (fun q ↦ by
    rw [zpowers_mk_uniformizerUnit hϖ]; exact Subgroup.mem_top q)]
  exact index_range_normUnits

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[K]`. Conclude with `isCyclic_iff_exists_zpowers_eq_top.2 ⟨_, zpowers_mk_uniformizerUnit hϖ⟩`.
-/
theorem isCyclic_quotient_range_normUnits : IsCyclic (Kˣ ⧸ (normUnits K L).range) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  exact isCyclic_iff_exists_zpowers_eq_top.2 ⟨_, zpowers_mk_uniformizerUnit hϖ⟩

end NormGroup

end GroundTheory.LocalField
