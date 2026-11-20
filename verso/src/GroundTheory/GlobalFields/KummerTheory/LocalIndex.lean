import Mathlib
import GroundTheory.LocalFields.UnitsBasic
import GroundTheory.LocalFields.FilteredSurj

namespace GroundTheory.Global

open ValuativeRel IsLocalRing GroundTheory.LocalField
open scoped WithZero

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `succ n ih`. Take `⟨c, hc⟩` from `ih`. Use `⟨n + c + x * c, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_succ, hc]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_one_add_pow_eq {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    ∃ c : R, (1 + x) ^ n = 1 + n * x + x ^ 2 * c := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨n + c + x * c, ?_⟩
    rw [pow_succ, hc]
    push_cast
    ring

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Filtration

/- English proof (translation)
Rewrite using `[mem_unitFiltration]`. Establish `h1 : ((x / y : 𝒪[K]ˣ) : 𝒪[K]) - 1 = ((x : 𝒪[K]) - y) * ((y⁻¹ : 𝒪[K]ˣ) : 𝒪[K])`. Rewrite using `[div_eq_mul_inv, Units.val_mul]`. Take the linear combination `(Units.mul_inv y)`. Establish `h2 : (x : 𝒪[K]) - y = (y : 𝒪[K]) * (((x / y : 𝒪[K]ˣ) : 𝒪[K]) - 1)`.

Rewrite using `[div_eq_mul_inv, Units.val_mul]`. Take the linear combination `(-(x : 𝒪[K])) * (Units.mul_inv y)`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[h2]`.

Conclude with `Ideal.mul_mem_left _ _ h`. Introduce `h`. Rewrite using `[h1]`. Conclude with `Ideal.mul_mem_right _ _ h`.
-/
theorem div_mem_unitFiltration_iff {k : ℕ} {x y : 𝒪[K]ˣ} :
    x / y ∈ unitFiltration K k ↔ (x : 𝒪[K]) - y ∈ 𝓂[K] ^ k := by
  rw [mem_unitFiltration]
  have h1 : ((x / y : 𝒪[K]ˣ) : 𝒪[K]) - 1 = ((x : 𝒪[K]) - y) * ((y⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) := by
    rw [div_eq_mul_inv, Units.val_mul]
    linear_combination (Units.mul_inv y)
  have h2 : (x : 𝒪[K]) - y = (y : 𝒪[K]) * (((x / y : 𝒪[K]ˣ) : 𝒪[K]) - 1) := by
    rw [div_eq_mul_inv, Units.val_mul]
    linear_combination (-(x : 𝒪[K])) * (Units.mul_inv y)
  constructor
  · intro h; rw [h2]; exact Ideal.mul_mem_left _ _ h
  · intro h; rw [h1]; exact Ideal.mul_mem_right _ _ h

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[K]`. Assume the negation of the conclusion as `h0`. Take `⟨m, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ`. Establish `h` using `(mem_maximalIdeal_pow_iff hϖ).mp (hx (m + 1))`. Rewrite `h` using `[pow_succ, mul_comm (u : 𝒪[K]), mul_dvd_mul_iff_left (pow_ne_zero m hϖ.ne_zero)]`.

Conclude with `hϖ.not_isUnit (isUnit_of_dvd_unit h u.isUnit)`.
-/
theorem eq_zero_of_forall_mem_maximalIdeal_pow {x : 𝒪[K]} (hx : ∀ k, x ∈ 𝓂[K] ^ k) : x = 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  by_contra h0
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
  have h := (mem_maximalIdeal_pow_iff hϖ).mp (hx (m + 1))
  rw [pow_succ, mul_comm (u : 𝒪[K]), mul_dvd_mul_iff_left (pow_ne_zero m hϖ.ne_zero)] at h
  exact hϖ.not_isUnit (isUnit_of_dvd_unit h u.isUnit)

/- English proof (translation)
Introduce `u hu`. Establish `: (u : 𝒪[K]) - 1 = 0` using `eq_zero_of_forall_mem_maximalIdeal_pow fun k ↦ hu k`. Use `ext`. Simplify `this` using `[sub_eq_zero]`.
-/
theorem filtrationSeparated_unitFiltration : FiltrationSeparated (unitFiltration K) := by
  intro u hu
  have : (u : 𝒪[K]) - 1 = 0 := eq_zero_of_forall_mem_maximalIdeal_pow fun k ↦ hu k
  ext
  simpa [sub_eq_zero] using this

/- English proof (translation)
Set `_ : UniformSpace K` to `IsTopologicalAddGroup.rightUniformSpace K`. Establish `: IsUniformAddGroup K` using `isUniformAddGroup_of_addCommGroup`. Use `infer_instance`.
-/
theorem isAdicComplete_integer : IsAdicComplete 𝓂[K] 𝒪[K] := by
  let _ : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  infer_instance

/- English proof (translation)
Establish `hc` using `(isAdicComplete_integer (K := K)).toIsPrecomplete`. Introduce `x hx`. Use `choose M hM using hx`. Set `M' : ℕ → ℕ` to `fun N ↦ (Finset.range (N + 1)).sup M`. Establish `hM'ge : ∀ N, M N ≤ M' N` using `fun N ↦ Finset.le_sup (Finset.self_mem_range_succ N)`.

Establish `hM'mono : Monotone M'` using `fun a b hab ↦ Finset.sup_mono (Finset.range_subset_range.2 (by omega))`. Establish `hy : ∀ {a b : ℕ}, a ≤ b → ((x (M' a) : 𝒪[K]) ≡ x (M' b) [SMOD (𝓂[K] ^ a • ⊤ : Submodule 𝒪[K] 𝒪[K])])`. Introduce `a b hab`. Rewrite using `[smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]`. Conclude with `div_mem_unitFiltration_iff.mp (hM a (M' b) ((hM'ge a).trans (hM'mono hab)) (M' a) (hM'ge a))`.

Take `⟨L, hL⟩` from `hc.prec' (fun N ↦ (x (M' N) : 𝒪[K])) hy`. Establish `hL' : ∀ N, (x (M' N) : 𝒪[K]) - L ∈ 𝓂[K] ^ N` using `fun N ↦ by`. Use `hL N` as an intermediate fact. Rewrite `this` using `[smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]`. Then use the resulting hypothesis. Establish `hLu : IsUnit L`.

Assume the negation of the conclusion as `hL0`. Establish `h1 : L ∈ 𝓂[K]` using `(IsLocalRing.mem_maximalIdeal L).mpr hL0`. Establish `h2` using `hL' 1`. Rewrite `h2` using `[pow_one]`. Establish `: (x (M' 1) : 𝒪[K]) ∈ 𝓂[K]`.

Simplify using `using Ideal.add_mem _ h2 h1`. Conclude with `(IsLocalRing.mem_maximalIdeal _).mp this (x (M' 1)).isUnit`. Use `⟨hLu.unit, fun N ↦ ⟨M' N, fun n hn ↦ ?_⟩⟩` and prove the remaining obligations. Rewrite using `[div_mem_unitFiltration_iff, IsUnit.unit_spec]`. Establish `h1 : (x n : 𝒪[K]) - x (M' N) ∈ 𝓂[K] ^ N` using `div_mem_unitFiltration_iff.mp (hM N (M' N) (hM'ge N) n ((hM'ge N).trans hn))`.

Use `Ideal.add_mem _ h1 (hL' N)` as an intermediate fact. Rewrite `this` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem filtrationComplete_unitFiltration : FiltrationComplete (unitFiltration K) := by
  have hc := (isAdicComplete_integer (K := K)).toIsPrecomplete
  intro x hx
  choose M hM using hx

  let M' : ℕ → ℕ := fun N ↦ (Finset.range (N + 1)).sup M
  have hM'ge : ∀ N, M N ≤ M' N := fun N ↦ Finset.le_sup (Finset.self_mem_range_succ N)
  have hM'mono : Monotone M' := fun a b hab ↦
    Finset.sup_mono (Finset.range_subset_range.2 (by omega))
  have hy : ∀ {a b : ℕ}, a ≤ b →
      ((x (M' a) : 𝒪[K]) ≡ x (M' b) [SMOD (𝓂[K] ^ a • ⊤ : Submodule 𝒪[K] 𝒪[K])]) := by
    intro a b hab
    rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
    exact div_mem_unitFiltration_iff.mp
      (hM a (M' b) ((hM'ge a).trans (hM'mono hab)) (M' a) (hM'ge a))
  obtain ⟨L, hL⟩ := hc.prec' (fun N ↦ (x (M' N) : 𝒪[K])) hy
  have hL' : ∀ N, (x (M' N) : 𝒪[K]) - L ∈ 𝓂[K] ^ N := fun N ↦ by
    have := hL N
    rwa [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem] at this
  have hLu : IsUnit L := by
    by_contra hL0
    have h1 : L ∈ 𝓂[K] := (IsLocalRing.mem_maximalIdeal L).mpr hL0
    have h2 := hL' 1
    rw [pow_one] at h2
    have : (x (M' 1) : 𝒪[K]) ∈ 𝓂[K] := by
      simpa using Ideal.add_mem _ h2 h1
    exact (IsLocalRing.mem_maximalIdeal _).mp this (x (M' 1)).isUnit
  refine ⟨hLu.unit, fun N ↦ ⟨M' N, fun n hn ↦ ?_⟩⟩
  rw [div_mem_unitFiltration_iff, IsUnit.unit_spec]
  have h1 : (x n : 𝒪[K]) - x (M' N) ∈ 𝓂[K] ^ N :=
    div_mem_unitFiltration_iff.mp (hM N (M' N) (hM'ge N) n ((hM'ge N).trans hn))
  have := Ideal.add_mem _ h1 (hL' N)
  rwa [sub_add_sub_cancel] at this

end Filtration

section PowerMap

variable {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {n d : ℕ} {ε : 𝒪[K]ˣ}
  (hnd : (n : 𝒪[K]) = ε * ϖ ^ d)
include hϖ hnd

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] hϖ in

/- English proof (translation)
Take `⟨c₀, hc₀⟩` from `exists_one_add_pow_eq (ϖ ^ j * a) n`. Take `⟨t, rfl⟩ : ∃ t, j = d + 1 + t` from `⟨j - (d + 1), by omega⟩`. Use `⟨ϖ ^ t * a ^ 2 * c₀, ?_⟩` and prove the remaining obligations. Rewrite using `[hc₀, hnd]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_one_add_uniformizer_pow_mul_pow_eq {j : ℕ} (hj : d + 1 ≤ j) (a : 𝒪[K]) :
    ∃ c : 𝒪[K], (1 + ϖ ^ j * a) ^ n = 1 + ϖ ^ (j + d) * (ε * a + ϖ * c) := by
  obtain ⟨c₀, hc₀⟩ := exists_one_add_pow_eq (ϖ ^ j * a) n
  obtain ⟨t, rfl⟩ : ∃ t, j = d + 1 + t := ⟨j - (d + 1), by omega⟩
  refine ⟨ϖ ^ t * a ^ 2 * c₀, ?_⟩
  rw [hc₀, hnd]
  ring

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] hϖ in

/- English proof (translation)
Take `⟨c, hc⟩` from `exists_one_add_uniformizer_pow_mul_pow_eq hnd hj a`. Use `⟨c, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_pow_eq_pow_val, ← hc, ← hu, add_sub_cancel]`.
-/
theorem exists_units_pow_eq {j : ℕ} (hj : d + 1 ≤ j) {u : 𝒪[K]ˣ} {a : 𝒪[K]}
    (hu : (u : 𝒪[K]) - 1 = ϖ ^ j * a) :
    ∃ c : 𝒪[K], ((u ^ n : 𝒪[K]ˣ) : 𝒪[K]) = 1 + ϖ ^ (j + d) * (ε * a + ϖ * c) := by
  obtain ⟨c, hc⟩ := exists_one_add_uniformizer_pow_mul_pow_eq hnd hj a
  refine ⟨c, ?_⟩
  rw [Units.val_pow_eq_pow_val, ← hc, ← hu, add_sub_cancel]

/- English proof (translation)
Take `⟨a, ha⟩` from `(mem_maximalIdeal_pow_iff hϖ).mp hu`. Take `⟨c, hc⟩` from `exists_units_pow_eq hnd hj ha`. Rewrite using `[mem_unitFiltration, hc, add_sub_cancel_left, mem_maximalIdeal_pow_iff hϖ]`. Conclude with `dvd_mul_right _ _`.
-/
theorem pow_mem_unitFiltration {j : ℕ} (hj : d + 1 ≤ j) {u : 𝒪[K]ˣ}
    (hu : u ∈ unitFiltration K j) : u ^ n ∈ unitFiltration K (j + d) := by
  obtain ⟨a, ha⟩ := (mem_maximalIdeal_pow_iff hϖ).mp hu
  obtain ⟨c, hc⟩ := exists_units_pow_eq hnd hj ha
  rw [mem_unitFiltration, hc, add_sub_cancel_left, mem_maximalIdeal_pow_iff hϖ]
  exact dvd_mul_right _ _

/- English proof (translation)
Take `⟨b, hb⟩` from `(mem_maximalIdeal_pow_iff hϖ).mp hh`. Establish `hg` using `isUnit_one_add_mul hϖ (n := j) (by omega) ((ε⁻¹ : 𝒪[K]ˣ) * b)`. Establish `hg1 : ((hg.unit : 𝒪[K]ˣ) : 𝒪[K]) - 1 = ϖ ^ j * ((ε⁻¹ : 𝒪[K]ˣ) * b)`. Rewrite using `[IsUnit.unit_spec, add_sub_cancel_left]`. Use `⟨hg.unit, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[mem_unitFiltration, hg1, mem_maximalIdeal_pow_iff hϖ]`. Conclude with `dvd_mul_right _ _`. Take `⟨c, hc⟩` from `exists_units_pow_eq hnd hj hg1`. Rewrite using `[div_mem_unitFiltration_iff, mem_maximalIdeal_pow_iff hϖ]`. Conclude with `⟨-c, by linear_combination hb - hc - ϖ ^ (j + d) * b * (Units.mul_inv ε)⟩`.
-/
theorem exists_pow_div_mem_unitFiltration {j : ℕ} (hj : d + 1 ≤ j) {h : 𝒪[K]ˣ}
    (hh : h ∈ unitFiltration K (j + d)) :
    ∃ g ∈ unitFiltration K j, h / g ^ n ∈ unitFiltration K (j + 1 + d) := by
  obtain ⟨b, hb⟩ := (mem_maximalIdeal_pow_iff hϖ).mp hh
  have hg := isUnit_one_add_mul hϖ (n := j) (by omega) ((ε⁻¹ : 𝒪[K]ˣ) * b)
  have hg1 : ((hg.unit : 𝒪[K]ˣ) : 𝒪[K]) - 1 = ϖ ^ j * ((ε⁻¹ : 𝒪[K]ˣ) * b) := by
    rw [IsUnit.unit_spec, add_sub_cancel_left]
  refine ⟨hg.unit, ?_, ?_⟩
  · rw [mem_unitFiltration, hg1, mem_maximalIdeal_pow_iff hϖ]
    exact dvd_mul_right _ _
  · obtain ⟨c, hc⟩ := exists_units_pow_eq hnd hj hg1
    rw [div_mem_unitFiltration_iff, mem_maximalIdeal_pow_iff hϖ]
    exact ⟨-c, by linear_combination hb - hc - ϖ ^ (j + d) * b * (Units.mul_inv ε)⟩

/- English proof (translation)
Assume the negation of the conclusion as `hu1`. Establish `hex : ∃ k, u ∉ unitFiltration K k`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hu1 (filtrationSeparated_unitFiltration u h)`.

Establish `hJ` using `Nat.find_spec hex`. Establish `hJmin : ∀ k < Nat.find hex, u ∈ unitFiltration K k` using `fun k hk ↦ by`. Use `Nat.find_min hex hk` as an intermediate fact. Simplify using `using this`. Establish `hJd : d + 1 < Nat.find hex`.

Assume the negation of the conclusion as `hle`. Conclude with `hJ (unitFiltration_antitone K (not_lt.mp hle) hu)`. Take `⟨j, hjJ⟩ : ∃ j, Nat.find hex = j + 1` from `⟨Nat.find hex - 1, by omega⟩`. Establish `huj : u ∈ unitFiltration K j` using `hJmin j (by omega)`. Take `⟨a, ha⟩` from `(mem_maximalIdeal_pow_iff hϖ).mp huj`.

Establish `hnot : ¬ ϖ ∣ a`. Introduce and unpack `⟨b, rfl⟩`. Apply `hJ` to reduce the goal to its premises. Rewrite using `[hjJ, mem_unitFiltration, mem_maximalIdeal_pow_iff hϖ, ha, pow_succ]`. Conclude with `mul_dvd_mul_left _ (dvd_mul_right _ _)`.

Take `⟨c, hc⟩` from `exists_units_pow_eq hnd (j := j) (by omega) ha`. Rewrite `hc` using `[hun, Units.val_one, left_eq_add, mul_eq_zero]`. Break down `hc with hc | hc` into its components or cases. Conclude with `pow_ne_zero _ hϖ.ne_zero hc`. Apply `hnot` to reduce the goal to its premises.

Use `⟨-((ε⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * c, ?_⟩` and prove the remaining obligations. Take the linear combination `((ε⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * hc - a * (Units.inv_mul ε)`.
-/
theorem eq_one_of_pow_eq_one {u : 𝒪[K]ˣ} (hu : u ∈ unitFiltration K (d + 1)) (hun : u ^ n = 1) :
    u = 1 := by
  classical
  by_contra hu1
  have hex : ∃ k, u ∉ unitFiltration K k := by
    by_contra h
    push Not at h
    exact hu1 (filtrationSeparated_unitFiltration u h)
  have hJ := Nat.find_spec hex
  have hJmin : ∀ k < Nat.find hex, u ∈ unitFiltration K k := fun k hk ↦ by
    have := Nat.find_min hex hk
    simpa using this
  have hJd : d + 1 < Nat.find hex := by
    by_contra hle
    exact hJ (unitFiltration_antitone K (not_lt.mp hle) hu)
  obtain ⟨j, hjJ⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
  have huj : u ∈ unitFiltration K j := hJmin j (by omega)
  obtain ⟨a, ha⟩ := (mem_maximalIdeal_pow_iff hϖ).mp huj
  have hnot : ¬ ϖ ∣ a := by
    rintro ⟨b, rfl⟩
    apply hJ
    rw [hjJ, mem_unitFiltration, mem_maximalIdeal_pow_iff hϖ, ha, pow_succ]
    exact mul_dvd_mul_left _ (dvd_mul_right _ _)
  obtain ⟨c, hc⟩ := exists_units_pow_eq hnd (j := j) (by omega) ha
  rw [hun, Units.val_one, left_eq_add, mul_eq_zero] at hc
  rcases hc with hc | hc
  · exact pow_ne_zero _ hϖ.ne_zero hc
  · apply hnot
    refine ⟨-((ε⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * c, ?_⟩
    linear_combination ((ε⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * hc - a * (Units.inv_mul ε)

/- English proof (translation)
The claim follows from `map_eq_of_graded_surjective (unitFiltration_antitone K) (unitFiltration_antitone K) filtrationComplete_unitFiltration filtrationSeparated_unitFiltration (powMonoidHom n) (φ := fun j ↦ j + d) (Filter.tendsto_add_atTop_nat d) (d + 1) (fun _ hj _ hg ↦ pow_mem_unitFiltration hϖ hnd h …`.
-/
theorem map_powMonoidHom_unitFiltration :
    (unitFiltration K (d + 1)).map (powMonoidHom n) = unitFiltration K (d + 1 + d) :=
  map_eq_of_graded_surjective (unitFiltration_antitone K) (unitFiltration_antitone K)
    filtrationComplete_unitFiltration filtrationSeparated_unitFiltration (powMonoidHom n)
    (φ := fun j ↦ j + d) (Filter.tendsto_add_atTop_nat d) (d + 1)
    (fun _ hj _ hg ↦ pow_mem_unitFiltration hϖ hnd hj hg)
    (fun _ hj _ hh ↦ exists_pow_div_mem_unitFiltration hϖ hnd hj hh)

/- English proof (translation)
Use `set f : 𝒪[K]ˣ →* 𝒪[K]ˣ := powMonoidHom n`. Use `set V := unitFiltration K (d + 1)`. Establish `hdisj : Disjoint V f.ker`. Rewrite using `[Subgroup.disjoint_def]`. Introduce `u hu hk`.

Conclude with `eq_one_of_pow_eq_one hϖ hnd hu hk`. Establish `h1 : V.relIndex f.ker = Nat.card f.ker`. Rewrite using `[Subgroup.relIndex, Subgroup.subgroupOf_eq_bot.2 hdisj, Subgroup.index_bot]`. Establish `h2 : V.relIndex (V ⊔ f.ker) * (V ⊔ f.ker).index = V.index` using `Subgroup.relIndex_mul_index le_sup_left`. Establish `h3 : V.relIndex (V ⊔ f.ker) = V.relIndex f.ker` using `Subgroup.relIndex_sup_left f.ker V`.

Establish `h4 : (V.map f).index = (V ⊔ f.ker).index * f.range.index` using `V.index_map f`. Rewrite `h4` using `[map_powMonoidHom_unitFiltration hϖ hnd, index_unitFiltration K (by omega)]`. Rewrite `h2` using `[h3, h1, index_unitFiltration K (by omega)]`. Establish `hq : 1 < Nat.card 𝓀[K]` using `Finite.one_lt_card`. Establish `hc : 0 < (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ d` using `Nat.mul_pos (by omega) (pow_pos (by omega) d)`.

Use `Nat.eq_of_mul_eq_mul_left hc ?_` and prove the remaining obligations. Establish `e1 : d + 1 - 1 = d` using `by omega`. Establish `e2 : d + 1 + d - 1 = d + d` using `by omega`. Rewrite `h2` using `[e1]`. Rewrite `h4` using `[e2, pow_add]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem index_range_powMonoidHom_integerUnits_of_eq :
    (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).range.index =
      Nat.card (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).ker * Nat.card 𝓀[K] ^ d := by
  set f : 𝒪[K]ˣ →* 𝒪[K]ˣ := powMonoidHom n
  set V := unitFiltration K (d + 1)
  have hdisj : Disjoint V f.ker := by
    rw [Subgroup.disjoint_def]
    intro u hu hk
    exact eq_one_of_pow_eq_one hϖ hnd hu hk
  have h1 : V.relIndex f.ker = Nat.card f.ker := by
    rw [Subgroup.relIndex, Subgroup.subgroupOf_eq_bot.2 hdisj, Subgroup.index_bot]
  have h2 : V.relIndex (V ⊔ f.ker) * (V ⊔ f.ker).index = V.index :=
    Subgroup.relIndex_mul_index le_sup_left
  have h3 : V.relIndex (V ⊔ f.ker) = V.relIndex f.ker := Subgroup.relIndex_sup_left f.ker V
  have h4 : (V.map f).index = (V ⊔ f.ker).index * f.range.index := V.index_map f
  rw [map_powMonoidHom_unitFiltration hϖ hnd, index_unitFiltration K (by omega)] at h4
  rw [h3, h1, index_unitFiltration K (by omega)] at h2
  have hq : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  have hc : 0 < (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ d :=
    Nat.mul_pos (by omega) (pow_pos (by omega) d)
  refine Nat.eq_of_mul_eq_mul_left hc ?_
  have e1 : d + 1 - 1 = d := by omega
  have e2 : d + 1 + d - 1 = d + d := by omega
  rw [e1] at h2
  rw [e2, pow_add] at h4
  calc (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ d * f.range.index
      = Nat.card f.ker * ((V ⊔ f.ker).index * f.range.index) := by rw [← h2]; ring
    _ = _ := by rw [← h4]; ring

end PowerMap

section Units

variable {n : ℕ}

/- English proof (translation)
Establish `h0 : (ϖ : K) ≠ 0` using `by exact_mod_cast hϖ.ne_zero`. Proceed by induction on `d with`. Consider the case `zero => simp [ord]`. Consider the case `succ d ih`. Rewrite using `[pow_succ, ord_mul (pow_ne_zero _ h0) h0, ih, ord_uniformizer hϖ]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ord_uniformizer_pow {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) (d : ℕ) : ord ((ϖ : K) ^ d) = d := by
  have h0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  induction d with
  | zero => simp [ord]
  | succ d ih =>
    rw [pow_succ, ord_mul (pow_ne_zero _ h0) h0, ih, ord_uniformizer hϖ]
    push_cast
    ring

/- English proof (translation)
Establish `h0 : (n : 𝒪[K]) ≠ 0`. Introduce `h`. Apply `hn` to reduce the goal to its premises. Simplify using `using congrArg (fun x : 𝒪[K] ↦ (x : K)) h`. Take `⟨d, ε, h⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ`.

Use `⟨d, ε, h, ?_⟩` and prove the remaining obligations. Establish `hK : (n : K) = ((ε : 𝒪[K]) : K) * (ϖ : K) ^ d`. Simplify using `using congrArg (fun x : 𝒪[K] ↦ (x : K)) h`. Establish `hε : ((ε : 𝒪[K]) : K) ≠ 0` using `by exact_mod_cast ε.ne_zero`. Establish `hϖd : (ϖ : K) ^ d ≠ 0` using `pow_ne_zero _ (by exact_mod_cast hϖ.ne_zero)`.

Rewrite using `[hK, ord_mul hε hϖd, ord_unit, ord_uniformizer_pow hϖ, zero_add]`.
-/
theorem exists_natCast_eq_unit_mul_pow (hn : (n : K) ≠ 0) {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    ∃ (d : ℕ) (ε : 𝒪[K]ˣ), (n : 𝒪[K]) = ε * ϖ ^ d ∧ ord (n : K) = d := by
  have h0 : (n : 𝒪[K]) ≠ 0 := by
    intro h
    apply hn
    simpa using congrArg (fun x : 𝒪[K] ↦ (x : K)) h
  obtain ⟨d, ε, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
  refine ⟨d, ε, h, ?_⟩
  have hK : (n : K) = ((ε : 𝒪[K]) : K) * (ϖ : K) ^ d := by
    simpa using congrArg (fun x : 𝒪[K] ↦ (x : K)) h
  have hε : ((ε : 𝒪[K]) : K) ≠ 0 := by exact_mod_cast ε.ne_zero
  have hϖd : (ϖ : K) ^ d ≠ 0 := pow_ne_zero _ (by exact_mod_cast hϖ.ne_zero)
  rw [hK, ord_mul hε hϖd, ord_unit, ord_uniformizer_pow hϖ, zero_add]

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[Subgroup.mem_map, mem_rootsOfUnity]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩`. Rewrite `hu` using `[MonoidHom.mem_ker, powMonoidHom_apply]`.

Rewrite using `[← map_pow, hu, map_one]`. Introduce `hx`. Establish `hv : normalizedValuation K (x : K) ^ n = 1`. Rewrite using `[← map_pow, ← Units.val_pow_eq_pow_val, hx, Units.val_one, map_one]`. Establish `hv1 : normalizedValuation K (x : K) = 1`.

Establish `hne : normalizedValuation K (x : K) ≠ 0` using `by simp`. Establish `hlog` using `congrArg WithZero.log hv`. Rewrite `hlog` using `[WithZero.log_pow, WithZero.log_one, smul_eq_zero]`. Break down `hlog with h | h` into its components or cases. Conclude with `absurd h hn`.

Rewrite using `[← WithZero.exp_log hne, h, WithZero.exp_zero]`. Take `⟨u, rfl⟩` from `mem_range_unitsIncl_iff.mpr hv1`. Use `⟨u, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[MonoidHom.mem_ker, powMonoidHom_apply]`. Apply `unitsIncl_injective` to reduce the goal to its premises.

Rewrite using `[map_pow, hx, map_one]`.
-/
theorem map_unitsIncl_ker_powMonoidHom (hn : n ≠ 0) :
    (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).ker.map (unitsIncl K) = rootsOfUnity n K := by
  ext x
  rw [Subgroup.mem_map, mem_rootsOfUnity]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply] at hu
    rw [← map_pow, hu, map_one]
  · intro hx
    have hv : normalizedValuation K (x : K) ^ n = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hx, Units.val_one, map_one]
    have hv1 : normalizedValuation K (x : K) = 1 := by
      have hne : normalizedValuation K (x : K) ≠ 0 := by simp
      have hlog := congrArg WithZero.log hv
      rw [WithZero.log_pow, WithZero.log_one, smul_eq_zero] at hlog
      rcases hlog with h | h
      · exact absurd h hn
      · rw [← WithZero.exp_log hne, h, WithZero.exp_zero]
    obtain ⟨u, rfl⟩ := mem_range_unitsIncl_iff.mpr hv1
    refine ⟨u, ?_, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    apply unitsIncl_injective
    rw [map_pow, hx, map_one]

/- English proof (translation)
Rewrite using `[← map_unitsIncl_ker_powMonoidHom hn, Subgroup.card_map_of_injective unitsIncl_injective]`.
-/
theorem natCard_rootsOfUnity_eq (hn : n ≠ 0) :
    Nat.card (rootsOfUnity n K) = Nat.card (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).ker := by
  rw [← map_unitsIncl_ker_powMonoidHom hn, Subgroup.card_map_of_injective unitsIncl_injective]

omit [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

/- English proof (translation)
Establish `h : (powMonoidHom n : Multiplicative ℤ →* Multiplicative ℤ).range = (AddSubgroup.zmultiples (n : ℤ)).toSubgroup`. Use extensionality with `x`. Rewrite using `[MonoidHom.mem_range, Multiplicative.mem_toSubgroup, Int.mem_zmultiples_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`.

Conclude with `⟨Multiplicative.toAdd y, by simp⟩`. Introduce and unpack `⟨k, hk⟩`. Use `⟨Multiplicative.ofAdd k, ?_⟩` and prove the remaining obligations. Apply `Multiplicative.toAdd.injective` to reduce the goal to its premises. Simplify using `[hk]`.

Rewrite using `[h, AddSubgroup.index_toSubgroup, Int.index_zmultiples]`. Simplify using the standard rewrite rules.
-/
theorem index_range_powMonoidHom_multiplicativeInt (n : ℕ) :
    (powMonoidHom n : Multiplicative ℤ →* Multiplicative ℤ).range.index = n := by
  have h : (powMonoidHom n : Multiplicative ℤ →* Multiplicative ℤ).range =
      (AddSubgroup.zmultiples (n : ℤ)).toSubgroup := by
    ext x
    rw [MonoidHom.mem_range, Multiplicative.mem_toSubgroup, Int.mem_zmultiples_iff]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Multiplicative.toAdd y, by simp⟩
    · rintro ⟨k, hk⟩
      refine ⟨Multiplicative.ofAdd k, ?_⟩
      apply Multiplicative.toAdd.injective
      simp [hk]
  rw [h, AddSubgroup.index_toSubgroup, Int.index_zmultiples]
  simp

omit [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

/- English proof (translation)
Use extensionality with `⟨a, b⟩`. Rewrite using `[Subgroup.mem_prod, MonoidHom.mem_range, MonoidHom.mem_range, MonoidHom.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨x, y⟩, h⟩`. Rewrite `h` using `[powMonoidHom_apply, Prod.pow_mk, Prod.mk.injEq]`.

Conclude with `⟨⟨x, h.1⟩, ⟨y, h.2⟩⟩`. Introduce and unpack `⟨⟨x, hx⟩, ⟨y, hy⟩⟩`. Use `⟨(x, y), ?_⟩` and prove the remaining obligations. Rewrite `hx`, `hy`, the goal using `[powMonoidHom_apply]`. Rewrite using `[Prod.pow_mk, hx, hy]`.
-/
theorem range_powMonoidHom_prod {G H : Type*} [CommGroup G] [CommGroup H] (n : ℕ) :
    (powMonoidHom n : G × H →* G × H).range =
      (powMonoidHom n : G →* G).range.prod (powMonoidHom n : H →* H).range := by
  ext ⟨a, b⟩
  rw [Subgroup.mem_prod, MonoidHom.mem_range, MonoidHom.mem_range, MonoidHom.mem_range]
  constructor
  · rintro ⟨⟨x, y⟩, h⟩
    rw [powMonoidHom_apply, Prod.pow_mk, Prod.mk.injEq] at h
    exact ⟨⟨x, h.1⟩, ⟨y, h.2⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    refine ⟨(x, y), ?_⟩
    rw [powMonoidHom_apply] at hx hy ⊢
    rw [Prod.pow_mk, hx, hy]

/- English proof (translation)
Use `set e := unitsEquivIntProd hϖ`. Establish `hmap : (powMonoidHom n : Kˣ →* Kˣ).range.map (e : Kˣ →* Multiplicative ℤ × 𝒪[K]ˣ) = (powMonoidHom n : Multiplicative ℤ × 𝒪[K]ˣ →* _).range`. Use extensionality with `p`. Rewrite using `[Subgroup.mem_map, MonoidHom.mem_range]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨_, ⟨x, rfl⟩, rfl⟩`. Conclude with `⟨e x, by simp⟩`. Introduce and unpack `⟨q, rfl⟩`. Conclude with `⟨e.symm q ^ n, ⟨e.symm q, rfl⟩, by simp⟩`. Rewrite using `[← Subgroup.index_map_equiv _ e, hmap, range_powMonoidHom_prod, Subgroup.index_prod, index_range_powMonoidHom_multiplicativeInt]`.
-/
theorem index_range_powMonoidHom_units_eq {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) (n : ℕ) :
    (powMonoidHom n : Kˣ →* Kˣ).range.index =
      n * (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).range.index := by
  set e := unitsEquivIntProd hϖ
  have hmap : (powMonoidHom n : Kˣ →* Kˣ).range.map (e : Kˣ →* Multiplicative ℤ × 𝒪[K]ˣ) =
      (powMonoidHom n : Multiplicative ℤ × 𝒪[K]ˣ →* _).range := by
    ext p
    rw [Subgroup.mem_map, MonoidHom.mem_range]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨e x, by simp⟩
    · rintro ⟨q, rfl⟩
      exact ⟨e.symm q ^ n, ⟨e.symm q, rfl⟩, by simp⟩
  rw [← Subgroup.index_map_equiv _ e, hmap, range_powMonoidHom_prod, Subgroup.index_prod,
    index_range_powMonoidHom_multiplicativeInt]

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[K]`. Take `⟨d, ε, hnd, hord⟩` from `exists_natCast_eq_unit_mul_pow hn hϖ`. Establish `hn0 : n ≠ 0` using `by rintro rfl; simp at hn`. Use `⟨d, hord, ?_⟩` and prove the remaining obligations. Rewrite using `[index_range_powMonoidHom_units_eq hϖ, index_range_powMonoidHom_integerUnits_of_eq hϖ hnd, natCard_rootsOfUnity_eq hn0, mul_assoc]`.
-/
theorem index_range_powMonoidHom_eq_mul (hn : (n : K) ≠ 0) :
    ∃ d : ℕ, ord (n : K) = d ∧ (powMonoidHom n : Kˣ →* Kˣ).range.index =
      n * Nat.card (rootsOfUnity n K) * Nat.card 𝓀[K] ^ d := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨d, ε, hnd, hord⟩ := exists_natCast_eq_unit_mul_pow hn hϖ
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  refine ⟨d, hord, ?_⟩
  rw [index_range_powMonoidHom_units_eq hϖ, index_range_powMonoidHom_integerUnits_of_eq hϖ hnd,
    natCard_rootsOfUnity_eq hn0, mul_assoc]

/- English proof (translation)
Take `⟨d, hd, h⟩` from `index_range_powMonoidHom_eq_mul hn`. Rewrite using `[h, hd, zpow_natCast]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem index_range_powMonoidHom (hn : (n : K) ≠ 0) :
    ((powMonoidHom n : Kˣ →* Kˣ).range.index : ℝ) =
      n * Nat.card (rootsOfUnity n K) * (Nat.card 𝓀[K] : ℝ) ^ ord (n : K) := by
  obtain ⟨d, hd, h⟩ := index_range_powMonoidHom_eq_mul hn
  rw [h, hd, zpow_natCast]
  push_cast
  ring

end Units

section Open

/- English proof (translation)
Break down `eq_or_ne z 0 with rfl | hz` into its components or cases. Conclude with `dvd_zero _`. Take `⟨m, w, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz hϖ`. Establish `hzK : (((w : 𝒪[K]) * ϖ ^ m : 𝒪[K]) : K) ≠ 0` using `by exact_mod_cast hz`. Establish `hϖk : (ϖ : K) ^ k ≠ 0` using `pow_ne_zero _ (by exact_mod_cast hϖ.ne_zero)`.

Rewrite `h` using `[← normalizedValuation_lt_iff, normalizedValuation_eq_exp_ord hzK, normalizedValuation_eq_exp_ord hϖk, WithZero.exp_lt_exp, neg_lt_neg_iff, ord_uniformizer_pow hϖ]`. Establish `hord : ord ((((w : 𝒪[K]) * ϖ ^ m : 𝒪[K])) : K) = m`. Establish `hw : ((w : 𝒪[K]) : K) ≠ 0` using `by exact_mod_cast w.ne_zero`. Establish `hϖm : (ϖ : K) ^ m ≠ 0` using `pow_ne_zero _ (by exact_mod_cast hϖ.ne_zero)`. Use `push_cast`.

Rewrite using `[ord_mul hw hϖm, ord_unit, ord_uniformizer_pow hϖ, zero_add]`. Rewrite `h` using `[hord]`. Conclude with `Dvd.dvd.mul_left (pow_dvd_pow ϖ (by omega)) _`.
-/
theorem uniformizer_pow_succ_dvd_of_valuation_lt {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {k : ℕ}
    {z : 𝒪[K]} (h : valuation K (z : K) < valuation K ((ϖ : K) ^ k)) : ϖ ^ (k + 1) ∣ z := by
  rcases eq_or_ne z 0 with rfl | hz
  · exact dvd_zero _
  obtain ⟨m, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz hϖ
  have hzK : (((w : 𝒪[K]) * ϖ ^ m : 𝒪[K]) : K) ≠ 0 := by exact_mod_cast hz
  have hϖk : (ϖ : K) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hϖ.ne_zero)
  rw [← normalizedValuation_lt_iff, normalizedValuation_eq_exp_ord hzK,
    normalizedValuation_eq_exp_ord hϖk, WithZero.exp_lt_exp, neg_lt_neg_iff,
    ord_uniformizer_pow hϖ] at h
  have hord : ord ((((w : 𝒪[K]) * ϖ ^ m : 𝒪[K])) : K) = m := by
    have hw : ((w : 𝒪[K]) : K) ≠ 0 := by exact_mod_cast w.ne_zero
    have hϖm : (ϖ : K) ^ m ≠ 0 := pow_ne_zero _ (by exact_mod_cast hϖ.ne_zero)
    push_cast
    rw [ord_mul hw hϖm, ord_unit, ord_uniformizer_pow hϖ, zero_add]
  rw [hord] at h
  exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (by omega)) _

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[K]`. Take `⟨d, ε, hnd, -⟩` from `exists_natCast_eq_unit_mul_pow hn hϖ`. Apply `Subgroup.isOpen_of_mem_nhds _ (g := 1)` to reduce the goal to its premises. Use `set B : Set K := {y | valuation K (y - 1) < valuation K ((ϖ : K) ^ (d + d))}`. Establish `hB : B ∈ nhds (1 : K)`.

Use `(IsValuativeTopology.hasBasis_nhds' (1 : K)).mem_of_mem ?_` and prove the remaining obligations. Rewrite using `[Ne, Valuation.zero_iff]`. Conclude with `pow_ne_zero _ (by exact_mod_cast hϖ.ne_zero)`. Establish `hB' : Units.val ⁻¹' B ∈ nhds (1 : Kˣ)` using `Units.continuous_val.continuousAt.preimage_mem_nhds (by simpa using hB)`. Use `Filter.mem_of_superset hB' fun x hx ↦ ?_` and prove the remaining obligations.

Simplify using `only [Set.mem_preimage, Set.mem_ofPred_eq, B] at hx`. Establish `hlt1 : valuation K ((x : K) - 1) < 1`. Use `hx.trans_le ?_` and prove the remaining obligations. Rewrite using `[map_pow]`. Conclude with `pow_le_one' ϖ.2 _`.

Establish `hy : (x : K) - 1 ∈ 𝒪[K]` using `hlt1.le`. Establish `hv1 : valuation K (x : K) = 1`. Use `Valuation.map_add_eq_of_lt_right (valuation K) (x := (x : K) - 1) (y := 1) (by rwa [map_one])` as an intermediate fact. Rewrite `this` using `[sub_add_cancel, map_one]`. Then use the resulting hypothesis. Establish `hnv : normalizedValuation K (x : K) = 1`.

Rewrite using `[← map_one (normalizedValuation K), normalizedValuation_eq_iff, map_one, hv1]`. Take `⟨u, rfl⟩` from `mem_range_unitsIncl_iff.mpr hnv`. Establish `hu : u ∈ unitFiltration K (d + 1 + d)`. Rewrite using `[mem_unitFiltration, mem_maximalIdeal_pow_iff hϖ]`. Establish `e1 : d + 1 + d = d + d + 1` using `by omega`.

Rewrite using `[e1]`. Apply `uniformizer_pow_succ_dvd_of_valuation_lt hϖ` to reduce the goal to its premises. Simplify using `using hx`. Rewrite `hu` using `[← map_powMonoidHom_unitFiltration hϖ hnd]`. Take `⟨w, -, rfl⟩` from `hu`.

Conclude with `⟨unitsIncl K w, by simp⟩`.
-/
theorem isOpen_range_powMonoidHom {n : ℕ} (hn : (n : K) ≠ 0) :
    IsOpen ((powMonoidHom n : Kˣ →* Kˣ).range : Set Kˣ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨d, ε, hnd, -⟩ := exists_natCast_eq_unit_mul_pow hn hϖ
  apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
  set B : Set K := {y | valuation K (y - 1) < valuation K ((ϖ : K) ^ (d + d))}
  have hB : B ∈ nhds (1 : K) := by
    refine (IsValuativeTopology.hasBasis_nhds' (1 : K)).mem_of_mem ?_
    rw [Ne, Valuation.zero_iff]
    exact pow_ne_zero _ (by exact_mod_cast hϖ.ne_zero)
  have hB' : Units.val ⁻¹' B ∈ nhds (1 : Kˣ) :=
    Units.continuous_val.continuousAt.preimage_mem_nhds (by simpa using hB)
  refine Filter.mem_of_superset hB' fun x hx ↦ ?_
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, B] at hx
  have hlt1 : valuation K ((x : K) - 1) < 1 := by
    refine hx.trans_le ?_
    rw [map_pow]
    exact pow_le_one' ϖ.2 _
  have hy : (x : K) - 1 ∈ 𝒪[K] := hlt1.le
  have hv1 : valuation K (x : K) = 1 := by
    have := Valuation.map_add_eq_of_lt_right (valuation K) (x := (x : K) - 1) (y := 1)
      (by rwa [map_one])
    rwa [sub_add_cancel, map_one] at this
  have hnv : normalizedValuation K (x : K) = 1 := by
    rw [← map_one (normalizedValuation K), normalizedValuation_eq_iff, map_one, hv1]
  obtain ⟨u, rfl⟩ := mem_range_unitsIncl_iff.mpr hnv
  have hu : u ∈ unitFiltration K (d + 1 + d) := by
    rw [mem_unitFiltration, mem_maximalIdeal_pow_iff hϖ]
    have e1 : d + 1 + d = d + d + 1 := by omega
    rw [e1]
    apply uniformizer_pow_succ_dvd_of_valuation_lt hϖ
    simpa using hx
  rw [← map_powMonoidHom_unitFiltration hϖ hnd] at hu
  obtain ⟨w, -, rfl⟩ := hu
  exact ⟨unitsIncl K w, by simp⟩

end Open

end GroundTheory.Global
