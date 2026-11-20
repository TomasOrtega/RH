import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

/- English proof (translation)
Establish `h` using `congrArg norm hx`. Rewrite `h` using `[norm_pow, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 h`.
-/
private theorem cf_norm_root {v : ℕ} [Fact v.Prime] {n : ℕ} (hn : n ≠ 0) {x : Om v} (hx : x ^ n = 1) :
    ‖x‖ = 1 := by
  have h := congrArg norm hx
  rw [norm_pow, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 h

/- English proof (translation)
Establish `hn0 : n ≠ 0` using `by rintro rfl; exact hn (dvd_zero v)`. Assume the negation of the conclusion as `hne`. Establish `hx1` using `cf_norm_root hn0 hx`. Establish `hs : ∑ i ∈ Finset.range n, x ^ i = 0`. Use `mul_geom_sum x n` as an intermediate fact.

Rewrite `this` using `[hx, sub_self]`. Conclude with `(mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)`. Establish `hp : ∀ i : ℕ, ‖x ^ i - 1‖ < 1`. Introduce `i`. Proceed by induction on `i with`.

Consider the case `zero => simp`. Consider the case `succ i ih`. Establish `e : x ^ (i + 1) - 1 = x * (x ^ i - 1) + (x - 1)` using `by ring`. Rewrite using `[e]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ h)` and prove the remaining obligations.

Rewrite using `[norm_mul, hx1, one_mul]` and apply the resulting hypothesis. Establish `hq : ∀ k : ℕ, ‖∑ i ∈ Finset.range k, x ^ i - (k : Om v)‖ < 1`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`.

Consider the case `succ k ih`. Establish `e : ∑ i ∈ Finset.range (k + 1), x ^ i - ((k + 1 : ℕ) : Om v) = (∑ i ∈ Finset.range k, x ^ i - (k : Om v)) + (x ^ k - 1)`. Rewrite using `[Finset.sum_range_succ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ih (hp k))`. Establish `h1` using `hq n`. Rewrite `h1` using `[hs, zero_sub, norm_neg]`. Establish `h2 : ((n : ℕ) : Om v) = algebraMap ℚ_[v] (Om v) (n : ℚ_[v])` using `by simp`.

Rewrite `h1` using `[h2, PadicAlgCl.norm_extends, Padic.norm_natCast_lt_one_iff]`. Conclude with `hn h1`.
-/
private theorem cf_root_one {v : ℕ} [Fact v.Prime] {n : ℕ} (hn : ¬ v ∣ n) {x : Om v} (hx : x ^ n = 1)
    (h : ‖x - 1‖ < 1) : x = 1 := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero v)
  by_contra hne
  have hx1 := cf_norm_root hn0 hx
  have hs : ∑ i ∈ Finset.range n, x ^ i = 0 := by
    have := mul_geom_sum x n
    rw [hx, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have hp : ∀ i : ℕ, ‖x ^ i - 1‖ < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : x ^ (i + 1) - 1 = x * (x ^ i - 1) + (x - 1) := by ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ h)
      rwa [norm_mul, hx1, one_mul]
  have hq : ∀ k : ℕ, ‖∑ i ∈ Finset.range k, x ^ i - (k : Om v)‖ < 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : ∑ i ∈ Finset.range (k + 1), x ^ i - ((k + 1 : ℕ) : Om v) =
          (∑ i ∈ Finset.range k, x ^ i - (k : Om v)) + (x ^ k - 1) := by
        rw [Finset.sum_range_succ]; push_cast; ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ih (hp k))
  have h1 := hq n
  rw [hs, zero_sub, norm_neg] at h1
  have h2 : ((n : ℕ) : Om v) = algebraMap ℚ_[v] (Om v) (n : ℚ_[v]) := by simp
  rw [h2, PadicAlgCl.norm_extends, Padic.norm_natCast_lt_one_iff] at h1
  exact hn h1

/- English proof (translation)
Establish `hn0 : n ≠ 0` using `by rintro rfl; exact hn (dvd_zero v)`. Establish `hy1` using `cf_norm_root hn0 hy`. Establish `hy0 : y ≠ 0` using `by rintro rfl; simp at hy1`. Establish `h1 : x / y = 1`. Use `cf_root_one hn (by rw [div_pow, hx, hy, div_one]) ?_` and prove the remaining obligations.

Rewrite using `[div_sub_one hy0, norm_div, hy1, div_one]`. Conclude with `h`. Conclude with `(div_eq_one_iff_eq hy0).1 h1`.
-/
private theorem cf_root_eq {v : ℕ} [Fact v.Prime] {n : ℕ} (hn : ¬ v ∣ n) {x y : Om v} (hx : x ^ n = 1)
    (hy : y ^ n = 1) (h : ‖x - y‖ < 1) : x = y := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero v)
  have hy1 := cf_norm_root hn0 hy
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy1
  have h1 : x / y = 1 := by
    refine cf_root_one hn (by rw [div_pow, hx, hy, div_one]) ?_
    rw [div_sub_one hy0, norm_div, hy1, div_one]
    exact h
  exact (div_eq_one_iff_eq hy0).1 h1

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Use `haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (Om v) (l ^ m)`. Establish `hs` using `cyclotomicCharacter.spec l (n := m) (MulSemiringAction.toRingAut (GQ v) (Om v) g) ζ hζ.pow_eq_one`. Use `set c : ℤ_[l] := ((cyc v l g : ℤ_[l]ˣ) : ℤ_[l]) with hc`.

Establish `hs' : g ζ = ζ ^ (PadicInt.toZModPow m c).val` using `hs`. Establish `h3` using `hs'.symm.trans (h ζ hζ)`. Establish `h4 : (PadicInt.toZModPow m c).val ≡ a [MOD l ^ m]`. Use `(hζ.isOfFinOrder (NeZero.ne _)).pow_eq_pow_iff_modEq.mp h3` as an intermediate fact. Rewrite `this` using `[← hζ.eq_orderOf]`. Then use the resulting hypothesis.

Rewrite using `[← (ZMod.natCast_eq_natCast_iff _ _ _).mpr h4, ZMod.natCast_zmod_val]`.
-/
private theorem cf_toZModPow (v l : ℕ) [Fact v.Prime] [Fact l.Prime] (g : GQ v) (m a : ℕ)
    (h : ∀ ζ : Om v, IsPrimitiveRoot ζ (l ^ m) → g ζ = ζ ^ a) :
    PadicInt.toZModPow m ((cyc v l g : ℤ_[l]ˣ) : ℤ_[l]) = (a : ZMod (l ^ m)) := by
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om v) (l ^ m)
  have hs := cyclotomicCharacter.spec l (n := m)
    (MulSemiringAction.toRingAut (GQ v) (Om v) g) ζ hζ.pow_eq_one
  set c : ℤ_[l] := ((cyc v l g : ℤ_[l]ˣ) : ℤ_[l]) with hc
  have hs' : g ζ = ζ ^ (PadicInt.toZModPow m c).val := hs
  have h3 := hs'.symm.trans (h ζ hζ)
  have h4 : (PadicInt.toZModPow m c).val ≡ a [MOD l ^ m] := by
    have := (hζ.isOfFinOrder (NeZero.ne _)).pow_eq_pow_iff_modEq.mp h3
    rwa [← hζ.eq_orderOf] at this
  rw [← (ZMod.natCast_eq_natCast_iff _ _ _).mpr h4, ZMod.natCast_zmod_val]

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Establish `key : ∀ m : ℕ, ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - (((cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ))`. Introduce `m`. Use `haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ m)`.

Take `⟨a, ha, hga⟩` from `P.χQ_cyc g m ζ hζ.pow_eq_one`. Establish `h4` using `cf_toZModPow l l g m a (fun ξ hξ => by`. Take `⟨i, -, rfl⟩` from `hζ.eq_pow_of_pow_eq_one hξ.pow_eq_one`. Rewrite using `[map_pow, hga, ← pow_mul, ← pow_mul, mul_comm])`. Use `set c : ℤ_[l] := ((cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) with hc`.

Establish `h5 : PadicInt.toZModPow m ((a : ℤ_[l]) - c) = 0`. Rewrite using `[map_sub, map_natCast, h4, sub_self]`. Establish `h6 : ‖(a : ℤ_[l]) - c‖ ≤ (l : ℝ) ^ (-(m : ℤ))`. Rewrite using `[PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow]`. Conclude with `h5`.

Establish `h7 : ‖(a : ℚ_[l]) - (c : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ))`. Establish `: (((a : ℤ_[l]) - c : ℤ_[l]) : ℚ_[l]) = (a : ℚ_[l]) - (c : ℚ_[l])` using `by push_cast; rfl`. Rewrite using `[← this]`. Conclude with `h6`. Establish `h8` using `IsUltrametricDist.norm_add_le_max (((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - a) ((a : ℚ_[l]) - c)`.

Rewrite `h8` using `[sub_add_sub_cancel]`. Conclude with `h8.trans (max_le ha h7)`. Rewrite using `[← sub_eq_zero, ← norm_le_zero_iff]`. Establish `hlt : ((l : ℝ))⁻¹ < 1` using `inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.one_lt)`. Use `ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hlt) fun m => ?_` and prove the remaining obligations.

Use `key m` as an intermediate fact. Rewrite `this` using `[zpow_neg, zpow_natCast, ← inv_pow]`. Then use the resulting hypothesis.
-/
private theorem cf_chi (l : ℕ) [Fact l.Prime] (P : LocPrime l) (g : GQ l) :
    ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) = (((cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := by
  have hl : l.Prime := Fact.out
  have key : ∀ m : ℕ, ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) -
      (((cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
    intro m
    haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ m)
    obtain ⟨a, ha, hga⟩ := P.χQ_cyc g m ζ hζ.pow_eq_one
    have h4 := cf_toZModPow l l g m a (fun ξ hξ => by
      obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ.pow_eq_one
      rw [map_pow, hga, ← pow_mul, ← pow_mul, mul_comm])
    set c : ℤ_[l] := ((cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) with hc
    have h5 : PadicInt.toZModPow m ((a : ℤ_[l]) - c) = 0 := by
      rw [map_sub, map_natCast, h4, sub_self]
    have h6 : ‖(a : ℤ_[l]) - c‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow]
      exact h5
    have h7 : ‖(a : ℚ_[l]) - (c : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      have : (((a : ℤ_[l]) - c : ℤ_[l]) : ℚ_[l]) = (a : ℚ_[l]) - (c : ℚ_[l]) := by push_cast; rfl
      rw [← this]; exact h6
    have h8 := IsUltrametricDist.norm_add_le_max (((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - a) ((a : ℚ_[l]) - c)
    rw [sub_add_sub_cancel] at h8
    exact h8.trans (max_le ha h7)
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  have hlt : ((l : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.one_lt)
  refine ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hlt) fun m => ?_
  have := key m
  rwa [zpow_neg, zpow_natCast, ← inv_pow] at this

/- English proof (translation)
Introduce `v l _ _`. Establish `hl : l.Prime` using `Fact.out`. Establish `hv : v.Prime` using `Fact.out`. Use `⟨cyclotomicCharacter.continuous l ℚ_[v] (Om v), fun hvl => ?_, cf_chi l (PP l)⟩` and prove the remaining obligations. Establish `hnd : ∀ m : ℕ, ¬ v ∣ l ^ m` using `fun m h => hvl ((Nat.prime_dvd_prime_iff_eq hv hl).1 (hv.dvd_of_dvd_pow h))`.

Use `⟨fun g hg => ?_, fun σ hσ => ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Use `PadicInt.ext_of_toZModPow.1 fun m => ?_` and prove the remaining obligations. Rewrite using `[cf_toZModPow v l g m 1 (fun ζ hζ => ?_)]`. Simplify using the standard rewrite rules.

Rewrite using `[pow_one]`. Establish `hm : ζ ∈ MaximalUnramifiedExtension v` using `IntermediateField.subset_adjoin _ _ ⟨l ^ m, pow_pos hl.pos m, hnd m, hζ.pow_eq_one⟩`. Conclude with `(IntermediateField.mem_fixingSubgroup_iff _ _).1 hg ζ hm`. Use `PadicInt.ext_of_toZModPow.1 fun m => ?_` and prove the remaining obligations. Rewrite using `[cf_toZModPow v l σ m v (fun ζ hζ => ?_)]`.

Simplify using the standard rewrite rules. Establish `h1` using `cf_norm_root (pow_ne_zero m hl.ne_zero) hζ.pow_eq_one`. Use `cf_root_eq (hnd m) ?_ ?_ (hσ ζ h1.le)` and prove the remaining obligations. Rewrite using `[← map_pow, hζ.pow_eq_one, map_one]`. Rewrite using `[← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]`.
-/
theorem UpperTheory.V.Loc.cycFacts :
    ∀ (v l : ℕ) [Fact v.Prime] [Fact l.Prime], Continuous (cyc v l) ∧ (v ≠ l → (∀ g ∈ Iq v, cyc v l g = 1) ∧ ∀ σ : GQ v, IsFrob σ → ((cyc v l σ : ℤ_[l]ˣ) : ℤ_[l]) = (v : ℤ_[l])) ∧ ∀ g : GQ l, (((PP l).χQ g : ℚ_[l]ˣ) : ℚ_[l]) = (((cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := by
  intro v l _ _
  have hl : l.Prime := Fact.out
  have hv : v.Prime := Fact.out
  refine ⟨cyclotomicCharacter.continuous l ℚ_[v] (Om v), fun hvl => ?_, cf_chi l (PP l)⟩
  have hnd : ∀ m : ℕ, ¬ v ∣ l ^ m := fun m h =>
    hvl ((Nat.prime_dvd_prime_iff_eq hv hl).1 (hv.dvd_of_dvd_pow h))
  refine ⟨fun g hg => ?_, fun σ hσ => ?_⟩
  · apply Units.ext
    refine PadicInt.ext_of_toZModPow.1 fun m => ?_
    rw [cf_toZModPow v l g m 1 (fun ζ hζ => ?_)]
    · simp
    · rw [pow_one]
      have hm : ζ ∈ MaximalUnramifiedExtension v :=
        IntermediateField.subset_adjoin _ _ ⟨l ^ m, pow_pos hl.pos m, hnd m, hζ.pow_eq_one⟩
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg ζ hm
  · refine PadicInt.ext_of_toZModPow.1 fun m => ?_
    rw [cf_toZModPow v l σ m v (fun ζ hζ => ?_)]
    · simp
    · have h1 := cf_norm_root (pow_ne_zero m hl.ne_zero) hζ.pow_eq_one
      refine cf_root_eq (hnd m) ?_ ?_ (hσ ζ h1.le)
      · rw [← map_pow, hζ.pow_eq_one, map_one]
      · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
