import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.CrystallineAtPlaces
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

/- English proof (translation)
Take `⟨k, hk⟩` from `R.t_odd`. Rewrite using `[hk]`. Use `push_cast`. Establish `: ((2 * (k : ℤ) + 1 - 1) / 2) = k` using `by omega`. Rewrite using `[this]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem half_int_eq (R : Ranks) : ((((R.t : ℤ) - 1) / 2 : ℤ) : ℚ) = ((R.t : ℚ) - 1) / 2 := by
  obtain ⟨k, hk⟩ := R.t_odd
  rw [hk]
  push_cast
  have : ((2 * (k : ℤ) + 1 - 1) / 2) = k := by omega
  rw [this]; push_cast; ring

/- English proof (translation)
Take `⟨ze, hze⟩` from `P.e_int j`. Unfold `cloud`. Simplify using `only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha⟩`.

Take `⟨zv, hzv⟩` from `P.v_int a`. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[← ha, hze, hzv, Int.floor_intCast, Int.floor_intCast]`. Use `push_cast`. Rewrite using `[half_int_eq]`.

Introduce and unpack `⟨a, ha⟩`. Take `⟨zv, hzv⟩` from `P.v_int a`. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[hze, hzv, Int.floor_intCast, Int.floor_intCast]`. Rewrite `ha` using `[hze, hzv, ← half_int_eq]`.

Conclude with `ha.symm` after adjusting the coercions.
-/
theorem mem_cloud_iff {R : Ranks} (P : HCParam R) (j : Fin R.m) (X : ℤ) :
    X ∈ cloud P j ↔ ∃ a, (X : ℚ) = P.e j + P.v a + ((R.t : ℚ) - 1) / 2 := by
  obtain ⟨ze, hze⟩ := P.e_int j
  unfold cloud
  simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨zv, hzv⟩ := P.v_int a
    refine ⟨a, ?_⟩
    rw [← ha, hze, hzv, Int.floor_intCast, Int.floor_intCast]
    push_cast
    rw [half_int_eq]
  · rintro ⟨a, ha⟩
    obtain ⟨zv, hzv⟩ := P.v_int a
    refine ⟨a, ?_⟩
    rw [hze, hzv, Int.floor_intCast, Int.floor_intCast]
    rw [hze, hzv, ← half_int_eq] at ha
    exact_mod_cast ha.symm

/- English proof (translation)
Take `⟨ze, hze⟩` from `P.e_int j`. Unfold `lows`. Simplify using `only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha⟩`.

Take `⟨zv, hzv⟩` from `P.b_int a`. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[← ha, hze, hzv, Int.floor_intCast, Int.floor_intCast]`. Use `push_cast`. Rewrite using `[half_int_eq]`.

Introduce and unpack `⟨a, ha⟩`. Take `⟨zv, hzv⟩` from `P.b_int a`. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[hze, hzv, Int.floor_intCast, Int.floor_intCast]`. Rewrite `ha` using `[hze, hzv, ← half_int_eq]`.

Conclude with `ha.symm` after adjusting the coercions.
-/
theorem mem_lows_iff {R : Ranks} (P : HCParam R) (j : Fin R.m) (X : ℤ) :
    X ∈ lows P j ↔ ∃ a, (X : ℚ) = P.e j - P.b a + ((R.t : ℚ) - 1) / 2 := by
  obtain ⟨ze, hze⟩ := P.e_int j
  unfold lows
  simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨zv, hzv⟩ := P.b_int a
    refine ⟨a, ?_⟩
    rw [← ha, hze, hzv, Int.floor_intCast, Int.floor_intCast]
    push_cast
    rw [half_int_eq]
  · rintro ⟨a, ha⟩
    obtain ⟨zv, hzv⟩ := P.b_int a
    refine ⟨a, ?_⟩
    rw [hze, hzv, Int.floor_intCast, Int.floor_intCast]
    rw [hze, hzv, ← half_int_eq] at ha
    exact_mod_cast ha.symm

/- English proof (translation)
Unfold `jT2 jW`. Consider the cases of `s`. Simplify using `only [Bool.false_eq_true, if_false, Multiset.map_map, Function.comp_def, Multiset.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`.

Use `hx using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Introduce `h`. Conclude with `⟨_, h, by ring⟩`. Simplify using `only [if_true, Multiset.mem_map]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Use `hx using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Introduce `h`.

Conclude with `⟨_, h, by ring⟩`.
-/
theorem mem_twistedDualJumpsWithoutBlock_iff {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) (u : ℤ) :
    u ∈ jT2 P j s ↔ (if s then -u - 1 else (R.t : ℤ) - 1 - (-u - 1)) ∈ cloud P j + lows P j := by
  unfold jT2 jW
  cases s
  · simp only [Bool.false_eq_true, if_false, Multiset.map_map, Function.comp_def, Multiset.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      convert hx using 1; ring
    · intro h
      exact ⟨_, h, by ring⟩
  · simp only [if_true, Multiset.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      convert hx using 1; ring
    · intro h
      exact ⟨_, h, by ring⟩

/- English proof (translation)
Apply the tactic sequence `have hcast : (if s then (-(u : ℚ) - 1) else (R.t : ℚ) - 1 - (-(u : ℚ) - 1)) = (((if s then -u - 1 else (R.t : ℤ) - 1 - (-u - 1)) : ℤ) : ℚ) := by split_ifs <;> push_cast <;> ring`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_twistedDualJumpsWithoutBlock_iff, Multiset.mem_add, hcast, mem_cloud_iff, mem_lows_iff]`. Unfold `jT1 jR`. Rewrite using `[Multiset.map_add, Multiset.mem_add]`.

Use `show u ∈ jT2 P j s ∨ _ ↔ _`. Apply `or_congr Iff.rfl` to reduce the goal to its premises. Unfold `block`. Simplify using `only [Multiset.map_map, Function.comp_def, Multiset.mem_map, Multiset.mem_range]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨c, hc, rfl⟩; exact ⟨c, hc, by ring⟩`. Introduce and unpack `⟨c, hc, h⟩; exact ⟨c, hc, by omega⟩`.
-/
theorem jumps_rat {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) (u : ℤ) :
    (u ∈ jT2 P j s ↔ ((∃ a, (if s then (-(u : ℚ) - 1) else (R.t : ℚ) - 1 - (-(u : ℚ) - 1)) = P.e j + P.v a + ((R.t : ℚ) - 1) / 2) ∨ ∃ a, (if s then (-(u : ℚ) - 1) else (R.t : ℚ) - 1 - (-(u : ℚ) - 1)) = P.e j - P.b a + ((R.t : ℚ) - 1) / 2)) ∧ (u ∈ jT1 P j s ↔ u ∈ jT2 P j s ∨ ∃ c : ℕ, c < R.t ∧ -u - 1 = c) := by
  have hcast : (if s then (-(u : ℚ) - 1) else (R.t : ℚ) - 1 - (-(u : ℚ) - 1)) =
      (((if s then -u - 1 else (R.t : ℤ) - 1 - (-u - 1)) : ℤ) : ℚ) := by
    split_ifs <;> push_cast <;> ring
  refine ⟨?_, ?_⟩
  · rw [mem_twistedDualJumpsWithoutBlock_iff, Multiset.mem_add, hcast, mem_cloud_iff, mem_lows_iff]
  · unfold jT1 jR
    rw [Multiset.map_add, Multiset.mem_add]
    show u ∈ jT2 P j s ∨ _ ↔ _
    apply or_congr Iff.rfl
    unfold block
    simp only [Multiset.map_map, Function.comp_def, Multiset.mem_map, Multiset.mem_range]
    constructor
    · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, by ring⟩
    · rintro ⟨c, hc, h⟩; exact ⟨c, hc, by omega⟩

end GlobalTheory.HTW.Rec
