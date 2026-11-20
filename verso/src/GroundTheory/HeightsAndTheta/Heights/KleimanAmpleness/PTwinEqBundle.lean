import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisAltAlt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwinEqBundleLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq

open MvPolynomial

noncomputable section

variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}

/- English proof (translation)
Assemble the required witnesses or components as `⟨X j, X i, 1, Kleiman.X_mem_monos hi, isHomogeneous_X S j, isHomogeneous_X S i, by simp⟩`.
-/
theorem div_mem_chartRing_of_mem (I : Kleiman.Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1)
    (j : Fin (N + 1)) : x j / x i ∈ Kleiman.chartRing S x I :=
  ⟨X j, X i, 1, Kleiman.X_mem_monos hi, isHomogeneous_X S j, isHomogeneous_X S i, by simp⟩

def pairChart {i j : Fin (N + 1)} (hi : x i ≠ 0) (hj : x j ≠ 0) : Kleiman.Chart x :=
  ⟨{i, j}, Finset.insert_nonempty i {j}, by
    intro l hl
    rcases Finset.mem_insert.1 hl with h | h
    · rw [h]; exact (Kleiman.mem_support x).2 hi
    · rw [Finset.mem_singleton.1 h]; exact (Kleiman.mem_support x).2 hj⟩

/- English proof (translation)
Rewrite `hv` using `[← chartRingI.equiv]`. Establish `hij : x i / x j ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x j` using `ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing x j i`. Proceed by induction on `hv using Algebra.adjoin_induction with`. Consider the case `mem y hy`. Take `⟨l, hl, k, rfl⟩` from `hy`.

Express the relevant statement in the definitionally equal form `l ∈ ({i, j} : Finset (Fin (N + 1))) at hl`. Break down `Finset.mem_insert.1 hl with h | h` into its components or cases. Substitute `h` using the available equality. Use `⟨1, ?_⟩` and prove the remaining obligations. Establish `: x l / x j * (x k / x l) = x k / x j` using `by field_simp`.

Rewrite using `[pow_one, this]`. Conclude with `ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing x j k`. Rewrite using `[Finset.mem_singleton.1 h]`. Conclude with `⟨0, by rw [pow_zero, one_mul]; exact ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing x j k⟩`. Consider the case `algebraMap r`.

Conclude with `⟨0, by rw [pow_zero, one_mul]; exact Subalgebra.algebraMap_mem _ r⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨m, hm⟩` from `hy`. Take `⟨n, hn⟩` from `hz`. Use `⟨m + n, ?_⟩` and prove the remaining obligations.

Establish `: (x i / x j) ^ (m + n) * (y + z) = (x i / x j) ^ n * ((x i / x j) ^ m * y) + (x i / x j) ^ m * ((x i / x j) ^ n * z)`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `add_mem (mul_mem (pow_mem hij _) hm) (mul_mem (pow_mem hij _) hn)`. Consider the case `mul y z _ _ hy hz`.

Take `⟨m, hm⟩` from `hy`. Take `⟨n, hn⟩` from `hz`. Use `⟨m + n, ?_⟩` and prove the remaining obligations. Establish `: (x i / x j) ^ (m + n) * (y * z) = ((x i / x j) ^ m * y) * ((x i / x j) ^ n * z)`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Conclude with `mul_mem hm hn`.
-/
theorem exists_pow_mul_mem_of_pair {i j : Fin (N + 1)} (hi : x i ≠ 0) (hj : x j ≠ 0) {v : Ω}
    (hv : v ∈ Kleiman.chartRing S x (pairChart hi hj)) :
    ∃ m : ℕ, (x i / x j) ^ m * v ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x j := by
  rw [← chartRingI.equiv] at hv
  have hij : x i / x j ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x j := ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing x j i
  induction hv using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨l, hl, k, rfl⟩ := hy
    change l ∈ ({i, j} : Finset (Fin (N + 1))) at hl
    rcases Finset.mem_insert.1 hl with h | h
    · subst h
      refine ⟨1, ?_⟩
      have : x l / x j * (x k / x l) = x k / x j := by field_simp
      rw [pow_one, this]
      exact ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing x j k
    · rw [Finset.mem_singleton.1 h]
      exact ⟨0, by rw [pow_zero, one_mul]; exact ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing x j k⟩
  | algebraMap r =>
    exact ⟨0, by rw [pow_zero, one_mul]; exact Subalgebra.algebraMap_mem _ r⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    have : (x i / x j) ^ (m + n) * (y + z) =
        (x i / x j) ^ n * ((x i / x j) ^ m * y) + (x i / x j) ^ m * ((x i / x j) ^ n * z) := by
      ring
    rw [this]
    exact add_mem (mul_mem (pow_mem hij _) hm) (mul_mem (pow_mem hij _) hn)
  | mul y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    have : (x i / x j) ^ (m + n) * (y * z) = ((x i / x j) ^ m * y) * ((x i / x j) ^ n * z) := by
      ring
    rw [this]
    exact mul_mem hm hn

/- English proof (translation)
Use `Submodule.mul_induction_on hz (fun p hp p' hp' => ⟨1, fun _ => p, fun _ => p', fun _ => hp, fun _ => hp', by simp⟩) ?_` and prove the remaining obligations. Introduce `u v hu hv`. Take `⟨k, q, q', hq, hq', rfl⟩` from `hu`. Take `⟨k', r, r', hr, hr', rfl⟩` from `hv`. Use `⟨k + k', Fin.append q r, Fin.append q' r', fun l => ?_, fun l => ?_, ?_⟩` and prove the remaining obligations.

Proceed by induction on `l using Fin.addCases with`. Consider the case `left l => simpa using hq l`. Consider the case `right l => simpa using hr l`. Proceed by induction on `l using Fin.addCases with`. Consider the case `left l => simpa using hq' l`.

Consider the case `right l => simpa using hr' l`. Rewrite using `[Fin.sum_univ_add]`. Simplify using the standard rewrite rules.
-/
theorem exists_sum_mul_eq {A : Subalgebra S Ω} {P P' : Submodule A Ω} {z : Ω} (hz : z ∈ P * P') :
    ∃ (k : ℕ) (q q' : Fin k → Ω), (∀ l, q l ∈ P) ∧ (∀ l, q' l ∈ P') ∧ ∑ l, q l * q' l = z := by
  refine Submodule.mul_induction_on hz
    (fun p hp p' hp' => ⟨1, fun _ => p, fun _ => p', fun _ => hp, fun _ => hp', by simp⟩) ?_
  intro u v hu hv
  obtain ⟨k, q, q', hq, hq', rfl⟩ := hu
  obtain ⟨k', r, r', hr, hr', rfl⟩ := hv
  refine ⟨k + k', Fin.append q r, Fin.append q' r', fun l => ?_, fun l => ?_, ?_⟩
  · induction l using Fin.addCases with
    | left l => simpa using hq l
    | right l => simpa using hr l
  · induction l using Fin.addCases with
    | left l => simpa using hq' l
    | right l => simpa using hr' l
  · rw [Fin.sum_univ_add]
    simp

section First

variable (Q : Kleiman.LineBundle S x)

/- English proof (translation)
Distinguish the cases in `h : x i ≠ 0`. Rewrite `he`, the goal using `[chartModule_of_ne_zero _ h, Submodule.restrictScalars_mem]`. Rewrite `ha` using `[chartRing.equiv S x h]`. Conclude with `(Q.sub _).smul_mem (⟨a, ha⟩ : Kleiman.chartRing S x _) he`. Establish `h0 : toIndefiniteRowSideFullHecke Q.toSubSystem i = ⊥` using `dif_neg h`.

Rewrite `he`, the goal using `[h0, Submodule.mem_bot]`. Rewrite using `[he, smul_zero]`.
-/
theorem ofFirst_stable (i : Fin (N + 1)) (a : Ω) (ha : a ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x i) (e : Ω)
    (he : e ∈ toIndefiniteRowSideFullHecke Q.toSubSystem i) : a • e ∈ toIndefiniteRowSideFullHecke Q.toSubSystem i := by
  by_cases h : x i ≠ 0
  · rw [chartModule_of_ne_zero _ h, Submodule.restrictScalars_mem] at he ⊢
    rw [chartRing.equiv S x h] at ha
    exact (Q.sub _).smul_mem (⟨a, ha⟩ : Kleiman.chartRing S x _) he
  · have h0 : toIndefiniteRowSideFullHecke Q.toSubSystem i = ⊥ := dif_neg h
    rw [h0, Submodule.mem_bot] at he ⊢
    rw [he, smul_zero]

/- English proof (translation)
Rewrite `he` using `[chartModule_of_ne_zero _ hi, Submodule.restrictScalars_mem]`. Establish `hiI : (Kleiman.singleChart hi).1 ⊆ (pairChart hi hj).1`. Express the relevant statement in the definitionally equal form `({i} : Finset (Fin (N + 1))) ⊆ {i, j}`. Simplify using the standard rewrite rules. Establish `hjI : (Kleiman.singleChart hj).1 ⊆ (pairChart hi hj).1`.

Express the relevant statement in the definitionally equal form `({j} : Finset (Fin (N + 1))) ⊆ {i, j}`. Simplify using the standard rewrite rules. Take `⟨a, ⟨u, hu⟩, hae⟩` from `(Q.mem_iff _ _ hjI e).1 (Q.mono _ _ hiI e he)`. Take `⟨m, hm⟩` from `exists_pow_mul_mem_of_pair hi hj (↑u⁻¹ : Kleiman.chartRing S x (pairChart hi hj)).2`. Rewrite `hm` using `[chartRing.equiv S x hj]`.

Use `⟨m, ?_⟩` and prove the remaining obligations. Establish `hinv : ((↑u⁻¹ : Kleiman.chartRing S x (pairChart hi hj)) : Ω) * (a : Ω) = 1`. Use `congrArg Subtype.val (Units.inv_mul u)` as an intermediate fact. Rewrite `this` using `[hu]`. Conclude with `this`.

Establish `key : (x i / x j) ^ m • e = (⟨_, hm⟩ : Kleiman.chartRing S x (Kleiman.singleChart hj)) • ((a : Ω) • e)`. Rewrite using `[Subalgebra.smul_def, smul_eq_mul, smul_eq_mul, smul_eq_mul]`. Express the relevant statement in the definitionally equal form `(x i / x j) ^ m * e = (x i / x j) ^ m * ((↑u⁻¹ : Kleiman.chartRing S x (pairChart hi hj)) : Ω) * ((a : Ω) * e)`. Rewrite using `[show ∀ w : Ω, (x i / x j) ^ m * w * ((a : Ω) * e) = (x i / x j) ^ m * (w * a) * e from fun w => by ring, hinv, mul_one]`. Rewrite using `[chartModule_of_ne_zero _ hj, Submodule.restrictScalars_mem, key]`.

Conclude with `Submodule.smul_mem _ _ hae`.
-/
theorem ofFirst_overlap (i j : Fin (N + 1)) (hi : x i ≠ 0) (hj : x j ≠ 0) (e : Ω)
    (he : e ∈ toIndefiniteRowSideFullHecke Q.toSubSystem i) : ∃ m : ℕ, (x i / x j) ^ m • e ∈ toIndefiniteRowSideFullHecke Q.toSubSystem j := by
  rw [chartModule_of_ne_zero _ hi, Submodule.restrictScalars_mem] at he
  have hiI : (Kleiman.singleChart hi).1 ⊆ (pairChart hi hj).1 := by
    change ({i} : Finset (Fin (N + 1))) ⊆ {i, j}
    simp
  have hjI : (Kleiman.singleChart hj).1 ⊆ (pairChart hi hj).1 := by
    change ({j} : Finset (Fin (N + 1))) ⊆ {i, j}
    simp
  obtain ⟨a, ⟨u, hu⟩, hae⟩ := (Q.mem_iff _ _ hjI e).1 (Q.mono _ _ hiI e he)
  obtain ⟨m, hm⟩ := exists_pow_mul_mem_of_pair hi hj (↑u⁻¹ : Kleiman.chartRing S x (pairChart hi hj)).2
  rw [chartRing.equiv S x hj] at hm
  refine ⟨m, ?_⟩
  have hinv : ((↑u⁻¹ : Kleiman.chartRing S x (pairChart hi hj)) : Ω) * (a : Ω) = 1 := by
    have := congrArg Subtype.val (Units.inv_mul u)
    rw [hu] at this
    exact this
  have key : (x i / x j) ^ m • e =
      (⟨_, hm⟩ : Kleiman.chartRing S x (Kleiman.singleChart hj)) • ((a : Ω) • e) := by
    rw [Subalgebra.smul_def, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    change (x i / x j) ^ m * e =
      (x i / x j) ^ m * ((↑u⁻¹ : Kleiman.chartRing S x (pairChart hi hj)) : Ω) * ((a : Ω) * e)
    rw [show ∀ w : Ω, (x i / x j) ^ m * w * ((a : Ω) * e) = (x i / x j) ^ m * (w * a) * e from
      fun w => by ring, hinv, mul_one]
  rw [chartModule_of_ne_zero _ hj, Submodule.restrictScalars_mem, key]
  exact Submodule.smul_mem _ _ hae

/- English proof (translation)
Take `⟨Q'', hQ⟩` from `Q.invertible (Kleiman.singleChart h)`. Establish `h1 : (1 : Ω) ∈ Q.sub (Kleiman.singleChart h) * Q''` using `hQ ▸ Submodule.mem_one.2 ⟨1, map_one _⟩`. Take `⟨k, q, q', hq, hq', hsum⟩` from `exists_sum_mul_eq h1`. Establish `hprod : ∀ {p p' : Ω}, p ∈ Q.sub (Kleiman.singleChart h) → p' ∈ Q'' → p * p' ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x i`. Introduce `p p' hp hp'`.

Use `Submodule.mul_mem_mul hp hp'` as an intermediate fact. Rewrite `this` using `[hQ, Submodule.mem_one]`. Take `⟨a, ha⟩` from `this`. Rewrite using `[chartRing.equiv S x h, ← ha]`. Conclude with `a.2`.

Establish `hmem : ∀ e, e ∈ (toIndefiniteRowSideFullHecke Q.toSubSystem i).toAddSubgroup ↔ e ∈ Q.sub (Kleiman.singleChart h)`. Introduce `e`. Rewrite using `[Submodule.mem_toAddSubgroup, chartModule_of_ne_zero _ h, Submodule.restrictScalars_mem]`. Use `⟨k, fun l => q l * q' l, fun _ => 1, fun l => hprod (hq l) (hq' l), fun _ => one_mem _, by simpa using hsum, fun l => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hq0 : q l = 0`.

Use `⟨fun _ => 1, ?_, ?_, fun e => ⟨fun _ => ⟨fun _ => e, fun _ => ⟨1, by simp [hq0]⟩, by simp⟩, fun _ => ⟨1, by simp [hq0]⟩⟩⟩` and prove the remaining obligations. Rewrite using `[linearIndependent_unique_iff]`. Conclude with `one_ne_zero`. Rewrite using `[Set.range_const]`. Conclude with `Ideal.span_singleton_eq_top.2 isUnit_one`.

Use `⟨fun _ => q l, ?_, ?_, fun e => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[linearIndependent_unique_iff]`. Conclude with `hq0`. Rewrite using `[Set.range_const]`. Conclude with `Ideal.span_singleton_eq_top.2 (isUnit_iff_ne_zero.2 hq0)`.

Introduce and unpack `⟨n, hn⟩`. Rewrite `hn` using `[hmem]`. Use `⟨fun _ => e / q l, fun _ => ⟨n + 1, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `: (q l * q' l) ^ (n + 1) * (e / q l) = ((q l * q' l) ^ n • e) * q' l`. Rewrite using `[smul_eq_mul]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `hprod hn (hq' l)`. Rewrite using `[Fin.sum_univ_one, smul_eq_mul]`.

Clear the denominators using the available nonvanishing facts. Introduce and unpack `⟨a, ha, rfl⟩`. Take `⟨n, hn⟩` from `ha 0`. Rewrite `hn` using `[chartRing.equiv S x h]`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Rewrite using `[hmem, Fin.sum_univ_one]`. Establish `: (q l * q' l) ^ n • (a 0 • q l) = (⟨_, hn⟩ : Kleiman.chartRing S x (Kleiman.singleChart h)) • q l`. Rewrite using `[Subalgebra.smul_def, smul_eq_mul, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ _ (hq l)`.
-/
theorem ofFirst_frame (i : Fin (N + 1)) (h : x i ≠ 0) :
    ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x i) ∧
      (∀ l, c l ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x i) ∧ ∑ l, c l * f l = 1 ∧
      ∀ l, ∃ b : Fin 1 → Ω, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
        ∀ e, (∃ n : ℕ, f l ^ n • e ∈ (toIndefiniteRowSideFullHecke Q.toSubSystem i).toAddSubgroup) ↔
          ∃ a : Fin 1 → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x i) ∧
            e = ∑ q, a q • b q := by
  obtain ⟨Q'', hQ⟩ := Q.invertible (Kleiman.singleChart h)
  have h1 : (1 : Ω) ∈ Q.sub (Kleiman.singleChart h) * Q'' := hQ ▸ Submodule.mem_one.2 ⟨1, map_one _⟩
  obtain ⟨k, q, q', hq, hq', hsum⟩ := exists_sum_mul_eq h1
  have hprod : ∀ {p p' : Ω}, p ∈ Q.sub (Kleiman.singleChart h) → p' ∈ Q'' →
      p * p' ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x i := by
    intro p p' hp hp'
    have := Submodule.mul_mem_mul hp hp'
    rw [hQ, Submodule.mem_one] at this
    obtain ⟨a, ha⟩ := this
    rw [chartRing.equiv S x h, ← ha]
    exact a.2
  have hmem : ∀ e, e ∈ (toIndefiniteRowSideFullHecke Q.toSubSystem i).toAddSubgroup ↔ e ∈ Q.sub (Kleiman.singleChart h) := by
    intro e
    rw [Submodule.mem_toAddSubgroup, chartModule_of_ne_zero _ h, Submodule.restrictScalars_mem]
  refine ⟨k, fun l => q l * q' l, fun _ => 1, fun l => hprod (hq l) (hq' l), fun _ => one_mem _,
    by simpa using hsum, fun l => ?_⟩
  by_cases hq0 : q l = 0
  · refine ⟨fun _ => 1, ?_, ?_, fun e => ⟨fun _ => ⟨fun _ => e, fun _ => ⟨1, by simp [hq0]⟩, by simp⟩,
      fun _ => ⟨1, by simp [hq0]⟩⟩⟩
    · rw [linearIndependent_unique_iff]
      exact one_ne_zero
    · rw [Set.range_const]
      exact Ideal.span_singleton_eq_top.2 isUnit_one
  · refine ⟨fun _ => q l, ?_, ?_, fun e => ⟨?_, ?_⟩⟩
    · rw [linearIndependent_unique_iff]
      exact hq0
    · rw [Set.range_const]
      exact Ideal.span_singleton_eq_top.2 (isUnit_iff_ne_zero.2 hq0)
    · rintro ⟨n, hn⟩
      rw [hmem] at hn
      refine ⟨fun _ => e / q l, fun _ => ⟨n + 1, ?_⟩, ?_⟩
      · have : (q l * q' l) ^ (n + 1) * (e / q l) = ((q l * q' l) ^ n • e) * q' l := by
          rw [smul_eq_mul]
          field_simp
          ring
        rw [this]
        exact hprod hn (hq' l)
      · rw [Fin.sum_univ_one, smul_eq_mul]
        field_simp
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨n, hn⟩ := ha 0
      rw [chartRing.equiv S x h] at hn
      refine ⟨n, ?_⟩
      rw [hmem, Fin.sum_univ_one]
      have : (q l * q' l) ^ n • (a 0 • q l) =
          (⟨_, hn⟩ : Kleiman.chartRing S x (Kleiman.singleChart h)) • q l := by
        rw [Subalgebra.smul_def, smul_eq_mul, smul_eq_mul, smul_eq_mul]
        ring
      rw [this]
      exact Submodule.smul_mem _ _ (hq l)

def ofFirst : IndefiniteRowSideFullHecke.Kleiman.LineBundle (S := S) x where
  lat i := (toIndefiniteRowSideFullHecke Q.toSubSystem i).toAddSubgroup
  stable i a ha e he := ofFirst_stable Q i a ha e he
  frame i h := ofFirst_frame Q i h
  overlap i j hi hj e he := ofFirst_overlap Q i j hi hj e he

/- English proof (translation)
The claim follows from `Submodule.span_eq _`.
-/
theorem ofFirst_mods (i : Fin (N + 1)) : (ofFirst Q).mods i = toIndefiniteRowSideFullHecke Q.toSubSystem i :=
  Submodule.span_eq _

end First

section Second

variable (Q' : IndefiniteRowSideFullHecke.Kleiman.LineBundle (S := S) x)

def latSub {i : Fin (N + 1)} (h : x i ≠ 0) :
    Submodule (Kleiman.chartRing S x (Kleiman.singleChart h)) Ω where
  carrier := Q'.lat i
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' a e he := Q'.stable i a (by rw [chartRing.equiv S x h]; exact a.2) e he

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_latSub {i : Fin (N + 1)} (h : x i ≠ 0) : (latSub Q' h : Set Ω) = (Q'.lat i : Set Ω) := rfl

def subOf (I : Kleiman.Chart x) : Submodule (Kleiman.chartRing S x I) Ω :=
  Submodule.span _ (⋃ i ∈ I.1, (Q'.lat i : Set Ω))

/- English proof (translation)
Establish `hxi : x i ≠ 0` using `(Kleiman.mem_support x).1 (I.2.2 hi)`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[subOf, Submodule.span_le]`. Introduce `e he`. Take `⟨j, hj, he⟩` from `Set.mem_iUnion₂.1 he`.

Establish `hxj : x j ≠ 0` using `(Kleiman.mem_support x).1 (I.2.2 hj)`. Take `⟨m, hm⟩` from `Q'.overlap j i hxj hxi e he`. Establish `hr : (x i / x j) ^ m ∈ Kleiman.chartRing S x I` using `pow_mem (div_mem_chartRing_of_mem I hj i) m`. Establish `hc : x i / x j * (x j / x i) = 1` using `by field_simp`. Establish `key : e = (⟨_, hr⟩ : Kleiman.chartRing S x I) • ((x j / x i) ^ m • e)`.

Rewrite using `[Subalgebra.smul_def, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_pow, hc, one_pow, one_mul]`. Rewrite using `[key]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hm)`. Conclude with `Submodule.span_mono fun e he => Set.mem_iUnion₂.2 ⟨i, hi, he⟩`.
-/
theorem subOf_eq {I : Kleiman.Chart x} {i : Fin (N + 1)} (hi : i ∈ I.1) :
    subOf Q' I = Submodule.span _ (Q'.lat i : Set Ω) := by
  have hxi : x i ≠ 0 := (Kleiman.mem_support x).1 (I.2.2 hi)
  apply le_antisymm
  · rw [subOf, Submodule.span_le]
    intro e he
    obtain ⟨j, hj, he⟩ := Set.mem_iUnion₂.1 he
    have hxj : x j ≠ 0 := (Kleiman.mem_support x).1 (I.2.2 hj)
    obtain ⟨m, hm⟩ := Q'.overlap j i hxj hxi e he
    have hr : (x i / x j) ^ m ∈ Kleiman.chartRing S x I := pow_mem (div_mem_chartRing_of_mem I hj i) m
    have hc : x i / x j * (x j / x i) = 1 := by field_simp
    have key : e = (⟨_, hr⟩ : Kleiman.chartRing S x I) • ((x j / x i) ^ m • e) := by
      rw [Subalgebra.smul_def, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_pow, hc, one_pow, one_mul]
    rw [key]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hm)
  · exact Submodule.span_mono fun e he => Set.mem_iUnion₂.2 ⟨i, hi, he⟩

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨i, hi, hz⟩` from `Set.mem_iUnion₂.1 hz`. Conclude with `Submodule.subset_span (Set.mem_iUnion₂.2 ⟨i, h hi, hz⟩)`. Consider the case `zero => exact zero_mem _`.

Consider the case `add u v _ _ hu hv => exact add_mem hu hv`. Consider the case `smul a z _ hz => exact Submodule.smul_mem _ (Kleiman.chartIncl h a) hz`.
-/
theorem subOf_mono (I J : Kleiman.Chart x) (h : I.1 ⊆ J.1) (y : Ω) (hy : y ∈ subOf Q' I) :
    y ∈ subOf Q' J := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, hi, hz⟩ := Set.mem_iUnion₂.1 hz
    exact Submodule.subset_span (Set.mem_iUnion₂.2 ⟨i, h hi, hz⟩)
  | zero => exact zero_mem _
  | add u v _ _ hu hv => exact add_mem hu hv
  | smul a z _ hz => exact Submodule.smul_mem _ (Kleiman.chartIncl h a) hz

/- English proof (translation)
Take `⟨i, hi⟩` from `I.2.1`. Establish `hxi : x i ≠ 0` using `(Kleiman.mem_support x).1 (I.2.2 hi)`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem z hz`. Take `⟨j, hj, hz⟩` from `Set.mem_iUnion₂.1 hz`. Establish `hxj : x j ≠ 0` using `(Kleiman.mem_support x).1 (J.2.2 hj)`. Take `⟨m, hm⟩` from `Q'.overlap j i hxj hxi z hz`. Use `⟨⟨(x j / x i) ^ m, pow_mem (div_mem_chartRing_of_mem I hi j) m⟩, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[isUnit_iff_exists_inv]`. Use `⟨⟨(x i / x j) ^ m, pow_mem (div_mem_chartRing_of_mem J hj i) m⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(x j / x i) ^ m * (x i / x j) ^ m = 1`. Establish `hc : x j / x i * (x i / x j) = 1` using `by field_simp`. Rewrite using `[← mul_pow, hc, one_pow]`.

Rewrite using `[subOf_eq Q' hi]`. Conclude with `Submodule.subset_span hm`. Consider the case `zero => exact ⟨1, by simp, by rw [smul_zero]; exact zero_mem _⟩`. Consider the case `add u v _ _ hu hv`. Take `⟨a, ha, hau⟩` from `hu`.

Take `⟨b, hb, hbv⟩` from `hv`. Use `⟨a * b, by rw [map_mul]; exact ha.mul hb, ?_⟩` and prove the remaining obligations. Establish `: ((a * b : Kleiman.chartRing S x I) : Ω) • (u + v) = b • ((a : Ω) • u) + a • ((b : Ω) • v)`. Simplify using `only [Subalgebra.coe_mul, Subalgebra.smul_def, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Conclude with `add_mem (Submodule.smul_mem _ b hau) (Submodule.smul_mem _ a hbv)`. Consider the case `smul c z _ hz`. Take `⟨a, ha, haz⟩` from `hz`. Take `⟨a', ha', hc⟩` from `Kleiman.exists_isUnit_mul_mem h c`.

Use `⟨a' * a, by rw [map_mul]; exact ha'.mul ha, ?_⟩` and prove the remaining obligations. Establish `: ((a' * a : Kleiman.chartRing S x I) : Ω) • (c • z) = (⟨(a' : Ω) * c, hc⟩ : Kleiman.chartRing S x I) • ((a : Ω) • z)`. Simplify using `only [Subalgebra.coe_mul, Subalgebra.smul_def, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ _ haz`. Introduce and unpack `⟨a, ⟨u, hu⟩, hay⟩`. Establish `hay'` using `subOf_mono Q' I J h _ hay`. Establish `hinv : ((↑u⁻¹ : Kleiman.chartRing S x J) : Ω) * (a : Ω) = 1`. Use `congrArg Subtype.val (Units.inv_mul u)` as an intermediate fact.

Rewrite `this` using `[hu]`. Conclude with `this`. Establish `hy' : y = (↑u⁻¹ : Kleiman.chartRing S x J) • ((a : Ω) • y)`. Rewrite using `[Subalgebra.smul_def, ← mul_smul, hinv, one_smul]`. Rewrite using `[hy']`.

Conclude with `Submodule.smul_mem _ _ hay'`.
-/
theorem subOf_mem_iff (I J : Kleiman.Chart x) (h : I.1 ⊆ J.1) (y : Ω) :
    y ∈ subOf Q' J ↔
      ∃ a : Kleiman.chartRing S x I, IsUnit (Kleiman.chartIncl h a) ∧ (a : Ω) • y ∈ subOf Q' I := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (Kleiman.mem_support x).1 (I.2.2 hi)
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, hj, hz⟩ := Set.mem_iUnion₂.1 hz
      have hxj : x j ≠ 0 := (Kleiman.mem_support x).1 (J.2.2 hj)
      obtain ⟨m, hm⟩ := Q'.overlap j i hxj hxi z hz
      refine ⟨⟨(x j / x i) ^ m, pow_mem (div_mem_chartRing_of_mem I hi j) m⟩, ?_, ?_⟩
      · rw [isUnit_iff_exists_inv]
        refine ⟨⟨(x i / x j) ^ m, pow_mem (div_mem_chartRing_of_mem J hj i) m⟩, Subtype.ext ?_⟩
        change (x j / x i) ^ m * (x i / x j) ^ m = 1
        have hc : x j / x i * (x i / x j) = 1 := by field_simp
        rw [← mul_pow, hc, one_pow]
      · rw [subOf_eq Q' hi]
        exact Submodule.subset_span hm
    | zero => exact ⟨1, by simp, by rw [smul_zero]; exact zero_mem _⟩
    | add u v _ _ hu hv =>
      obtain ⟨a, ha, hau⟩ := hu
      obtain ⟨b, hb, hbv⟩ := hv
      refine ⟨a * b, by rw [map_mul]; exact ha.mul hb, ?_⟩
      have : ((a * b : Kleiman.chartRing S x I) : Ω) • (u + v) = b • ((a : Ω) • u) + a • ((b : Ω) • v) := by
        simp only [Subalgebra.coe_mul, Subalgebra.smul_def, smul_eq_mul]
        ring
      rw [this]
      exact add_mem (Submodule.smul_mem _ b hau) (Submodule.smul_mem _ a hbv)
    | smul c z _ hz =>
      obtain ⟨a, ha, haz⟩ := hz
      obtain ⟨a', ha', hc⟩ := Kleiman.exists_isUnit_mul_mem h c
      refine ⟨a' * a, by rw [map_mul]; exact ha'.mul ha, ?_⟩
      have : ((a' * a : Kleiman.chartRing S x I) : Ω) • (c • z) =
          (⟨(a' : Ω) * c, hc⟩ : Kleiman.chartRing S x I) • ((a : Ω) • z) := by
        simp only [Subalgebra.coe_mul, Subalgebra.smul_def, smul_eq_mul]
        ring
      rw [this]
      exact Submodule.smul_mem _ _ haz
  · rintro ⟨a, ⟨u, hu⟩, hay⟩
    have hay' := subOf_mono Q' I J h _ hay
    have hinv : ((↑u⁻¹ : Kleiman.chartRing S x J) : Ω) * (a : Ω) = 1 := by
      have := congrArg Subtype.val (Units.inv_mul u)
      rw [hu] at this
      exact this
    have hy' : y = (↑u⁻¹ : Kleiman.chartRing S x J) • ((a : Ω) • y) := by
      rw [Subalgebra.smul_def, ← mul_smul, hinv, one_smul]
    rw [hy']
    exact Submodule.smul_mem _ _ hay'

/- English proof (translation)
Take `⟨k, f, c, hf, hc, hs, hb⟩` from `Q'.frame i h`. Establish `hA : ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x i = Kleiman.chartRing S x (Kleiman.singleChart h)` using `chartRing.equiv S x h`. Simplify using `only [hA] at hf hc hb`. Use `choose b hbli _ hiff using hb`. Use `fg_and_invertible_of_frame _ f c (latSub Q' h) (fun l => b l 0) hf hc hs (fun l => linearIndependent_unique_iff.1 (hbli l)) (fun l e => ?_)` and prove the remaining obligations.

Use `hiff l e` as an intermediate fact. Simplify using `only [Fin.sum_univ_one, smul_eq_mul] at this`. Prove the components needed by the constructor for the conclusion. Introduce `hn`. Take `⟨a, ha, he⟩` from `this.1 hn`.

Conclude with `⟨a 0, ha 0, he⟩`. Introduce and unpack `⟨a, ha, he⟩`. Conclude with `this.2 ⟨fun _ => a, fun _ => ha, he⟩`.
-/
theorem latSub_fg_invertible {i : Fin (N + 1)} (h : x i ≠ 0) :
    (latSub Q' h).FG ∧ ∃ L' : Submodule (Kleiman.chartRing S x (Kleiman.singleChart h)) Ω,
      latSub Q' h * L' = 1 := by
  obtain ⟨k, f, c, hf, hc, hs, hb⟩ := Q'.frame i h
  have hA : ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x i = Kleiman.chartRing S x (Kleiman.singleChart h) :=
    chartRing.equiv S x h
  simp only [hA] at hf hc hb
  choose b hbli _ hiff using hb
  refine fg_and_invertible_of_frame _ f c (latSub Q' h) (fun l => b l 0) hf hc hs
    (fun l => linearIndependent_unique_iff.1 (hbli l)) (fun l e => ?_)
  have := hiff l e
  simp only [Fin.sum_univ_one, smul_eq_mul] at this
  constructor
  · intro hn
    obtain ⟨a, ha, he⟩ := this.1 hn
    exact ⟨a 0, ha 0, he⟩
  · rintro ⟨a, ha, he⟩
    exact this.2 ⟨fun _ => a, fun _ => ha, he⟩

/- English proof (translation)
Take `⟨i, hi⟩` from `I.2.1`. Establish `hxi : x i ≠ 0` using `(Kleiman.mem_support x).1 (I.2.2 hi)`. Establish `hle : Kleiman.chartRing S x (Kleiman.singleChart hxi) ≤ Kleiman.chartRing S x I` using `Kleiman.chartRing_mono (I := Kleiman.singleChart hxi) (J := I) (Finset.singleton_subset_iff.2 hi)`. Rewrite using `[subOf_eq Q' hi]`. Conclude with `fg_span_of_le hle (latSub_fg_invertible Q' hxi).1`.
-/
theorem subOf_fg (I : Kleiman.Chart x) : (subOf Q' I).FG := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (Kleiman.mem_support x).1 (I.2.2 hi)
  have hle : Kleiman.chartRing S x (Kleiman.singleChart hxi) ≤ Kleiman.chartRing S x I :=
    Kleiman.chartRing_mono (I := Kleiman.singleChart hxi) (J := I) (Finset.singleton_subset_iff.2 hi)
  rw [subOf_eq Q' hi]
  exact fg_span_of_le hle (latSub_fg_invertible Q' hxi).1

/- English proof (translation)
Take `⟨i, hi⟩` from `I.2.1`. Establish `hxi : x i ≠ 0` using `(Kleiman.mem_support x).1 (I.2.2 hi)`. Establish `hle : Kleiman.chartRing S x (Kleiman.singleChart hxi) ≤ Kleiman.chartRing S x I` using `Kleiman.chartRing_mono (I := Kleiman.singleChart hxi) (J := I) (Finset.singleton_subset_iff.2 hi)`. Take `⟨L', hL'⟩` from `(latSub_fg_invertible Q' hxi).2`. Establish `key` using `mul_span_eq_one_of_le (B := Kleiman.chartRing S x I) hle hL'`.

Rewrite `key` using `[coe_latSub]`. Use `⟨Submodule.span (Kleiman.chartRing S x I) (L' : Set Ω), ?_⟩` and prove the remaining obligations. Rewrite using `[subOf_eq Q' hi]`. Conclude with `key`.
-/
theorem subOf_invertible (I : Kleiman.Chart x) :
    ∃ L' : Submodule (Kleiman.chartRing S x I) Ω, subOf Q' I * L' = 1 := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (Kleiman.mem_support x).1 (I.2.2 hi)
  have hle : Kleiman.chartRing S x (Kleiman.singleChart hxi) ≤ Kleiman.chartRing S x I :=
    Kleiman.chartRing_mono (I := Kleiman.singleChart hxi) (J := I) (Finset.singleton_subset_iff.2 hi)
  obtain ⟨L', hL'⟩ := (latSub_fg_invertible Q' hxi).2
  have key := mul_span_eq_one_of_le (B := Kleiman.chartRing S x I) hle hL'
  rw [coe_latSub] at key
  refine ⟨Submodule.span (Kleiman.chartRing S x I) (L' : Set Ω), ?_⟩
  rw [subOf_eq Q' hi]
  exact key

def ofSecond : Kleiman.LineBundle S x where
  sub := subOf Q'
  mono := subOf_mono Q'
  mem_iff := subOf_mem_iff Q'
  fg I := subOf_fg Q' I
  invertible I := subOf_invertible Q' I

/- English proof (translation)
Rewrite using `[chartModule_of_ne_zero _ h]`. Use extensionality with `z`. Express the relevant statement in the definitionally equal form `z ∈ Submodule.span S (Q'.lat i : Set Ω) ↔ z ∈ subOf Q' (Kleiman.singleChart h)`. Rewrite using `[subOf_eq Q' (Finset.mem_singleton_self i)]`. Prove the components needed by the constructor for the conclusion.

Introduce `hz`. Establish `hle : Submodule.span S (Q'.lat i : Set Ω) ≤ (latSub Q' h).restrictScalars S` using `Submodule.span_le.2 fun e he => he`. Conclude with `Submodule.subset_span (hle hz)`. Introduce `hz`. Establish `hle : Submodule.span (Kleiman.chartRing S x (Kleiman.singleChart h)) (Q'.lat i : Set Ω) ≤ latSub Q' h` using `Submodule.span_le.2 fun e he => he`.

Conclude with `Submodule.subset_span (hle hz)`.
-/
theorem ofSecond_mods {i : Fin (N + 1)} (h : x i ≠ 0) : Q'.mods i = toIndefiniteRowSideFullHecke (ofSecond Q').toSubSystem i := by
  rw [chartModule_of_ne_zero _ h]
  ext z
  change z ∈ Submodule.span S (Q'.lat i : Set Ω) ↔ z ∈ subOf Q' (Kleiman.singleChart h)
  rw [subOf_eq Q' (Finset.mem_singleton_self i)]
  constructor
  · intro hz
    have hle : Submodule.span S (Q'.lat i : Set Ω) ≤ (latSub Q' h).restrictScalars S :=
      Submodule.span_le.2 fun e he => he
    exact Submodule.subset_span (hle hz)
  · intro hz
    have hle : Submodule.span (Kleiman.chartRing S x (Kleiman.singleChart h)) (Q'.lat i : Set Ω) ≤
        latSub Q' h := Submodule.span_le.2 fun e he => he
    exact Submodule.subset_span (hle hz)

end Second

end

/- English proof (translation)
Introduce `S _ N Ω _ _ x`. Conclude with `⟨fun Q => ⟨ofFirst Q, ofFirst_mods Q⟩, fun Q' => ⟨ofSecond Q', fun i h => ofSecond_mods Q' h⟩⟩`.
-/
theorem LineBundle.proof : LineBundle.Statement := by
  intro S _ N Ω _ _ x
  exact ⟨fun Q => ⟨ofFirst Q, ofFirst_mods Q⟩, fun Q' => ⟨ofSecond Q', fun i h => ofSecond_mods Q' h⟩⟩

end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
