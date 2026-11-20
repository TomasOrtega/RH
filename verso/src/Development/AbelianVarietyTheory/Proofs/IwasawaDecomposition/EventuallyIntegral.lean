import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisGaloisActionFontaineTEqCyclotomic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRGaloisInvariantsEqFinExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffEqMkRootT
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Pst.KummerIndep

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `h : Filter.Tendsto (fun N : ℕ => ‖(l : ℚ_[l]) ^ N * x‖) Filter.atTop (nhds 0)`. Use `((tendsto_pow_atTop_nhds_zero_of_norm_lt_one (Padic.norm_p_lt_one (p := l))).mul_const x).norm` as an intermediate fact. Simplify using `using this`. Use `filter_upwards [h.eventually (ge_mem_nhds zero_lt_one)] with N hN`. Conclude with `⟨⟨_, hN⟩, rfl⟩`.
-/
theorem eventually_integral (x : ℚ_[l]) :
    ∀ᶠ N : ℕ in Filter.atTop, ∃ y : ℤ_[l], (y : ℚ_[l]) = (l : ℚ_[l]) ^ N * x := by
  have h : Filter.Tendsto (fun N : ℕ => ‖(l : ℚ_[l]) ^ N * x‖) Filter.atTop (nhds 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      (Padic.norm_p_lt_one (p := l))).mul_const x).norm
    simpa using this
  filter_upwards [h.eventually (ge_mem_nhds zero_lt_one)] with N hN
  exact ⟨⟨_, hN⟩, rfl⟩

/- English proof (translation)
Establish `: NeZero (l ^ k)` using `⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`. Establish `: IsGalois ℚ_[l] (Om l)` using `{}`. Take `⟨S, hS⟩ : ∃ S : ℕ, PadicInt.toZModPow k (-r) = S` from `⟨_, (ZMod.natCast_zmod_val _).symm⟩`. Take `⟨x, hx⟩` from `(InfiniteGalois.mem_range_algebraMap_iff_fixed (k := ℚ_[l]) (lRoot l k ^ A * μ k ^ B * P.ζQ k ^ S)).2 fun g => by`. Establish `hx : ‖(P.χQ g : ℚ_[l])‖ ≤ 1`.

Take `⟨a, ha, -⟩` from `P.χQ_cyc g 0 1 (by simp)`. Establish `e : (P.χQ g : ℚ_[l]) = ((P.χQ g : ℚ_[l]) - a) + a` using `by ring`. Rewrite using `[e]`. Use `(Padic.nonarchimedean _ _).trans (max_le (by simpa using ha) ?_)` and prove the remaining obligations. Conclude with `Padic.norm_int_le_one (p := l) (a : ℤ)` after adjusting the coercions.

Set `x : ℤ_[l]` to `⟨P.χQ g, hx⟩`. Take `⟨a, ha, hg⟩` from `P.χQ_cyc g k (P.ζQ k) (isPrimitiveRoot_zeta P k).pow_eq_one`. Establish `hxa : PadicInt.toZModPow k x = a`. Rewrite using `[← sub_eq_zero, ← map_natCast (PadicInt.toZModPow k), ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]`. Conclude with `ha`.

Establish `h1 : α * kummer P g + β * d g + (-r) * x = -r`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `e : (x : ℚ_[l]) = P.χQ g` using `rfl`. Use `h g` as an intermediate fact. Use `push_cast`.

Rewrite using `[e]`. Take the linear combination `this`. Establish `h2` using `congrArg (PadicInt.toZModPow k) h1`. Rewrite `h2` using `[map_add, map_add, map_mul, map_mul, map_mul, hA, hB, hS, hxa]`. Establish `h3 : P.ζQ k ^ ((PadicInt.toZModPow k (kummer P g)).val * A + (PadicInt.toZModPow k (d g)).val * B + a * S) = P.ζQ k ^ S`.

Rewrite using `[zeta_pow_eq_iff]`. Use `push_cast`. Rewrite using `[ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]`. Take the linear combination `h2`. Rewrite using `[map_mul, map_mul, map_pow, map_pow, map_pow, hg, isKummer_kummer P g k, hd g k, ← h3]`.

Simplify using `only [mul_pow, ← pow_mul, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨x, (algebraMap ℚ_[l] (Om l)).injective ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow, hx, mul_pow, mul_pow, pow_right_comm (lRoot l k), pow_right_comm (μ k), pow_right_comm (P.ζQ k), lRoot_pow, hμ, (isPrimitiveRoot_zeta P k).pow_eq_one]`. Simplify using the standard rewrite rules.
-/
theorem exists_root (P : LocPrime l) (μ : ℕ → Om l) (d : GQ l → ℤ_[l])
    (hμ : ∀ m : ℕ, μ m ^ (l ^ m) = ((l + 1 : ℕ) : Om l))
    (hd : ∀ (g : GQ l) (m : ℕ), g (μ m) = P.ζQ m ^ (PadicInt.toZModPow m (d g)).val * μ m)
    (α β r : ℤ_[l])
    (h : ∀ g : GQ l, (α : ℚ_[l]) * (kummer P g : ℚ_[l]) + β * (d g : ℚ_[l]) =
      r * ((P.χQ g : ℚ_[l]) - 1))
    (k A B : ℕ) (hA : PadicInt.toZModPow k α = A) (hB : PadicInt.toZModPow k β = B) :
    ∃ q : ℚ_[l], q ^ (l ^ k) = (l : ℚ_[l]) ^ A * ((l + 1 : ℕ) : ℚ_[l]) ^ B := by
  have : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have : IsGalois ℚ_[l] (Om l) := {}
  obtain ⟨S, hS⟩ : ∃ S : ℕ, PadicInt.toZModPow k (-r) = S := ⟨_, (ZMod.natCast_zmod_val _).symm⟩
  obtain ⟨x, hx⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := ℚ_[l])
    (lRoot l k ^ A * μ k ^ B * P.ζQ k ^ S)).2 fun g => by
      have hx : ‖(P.χQ g : ℚ_[l])‖ ≤ 1 := by
        obtain ⟨a, ha, -⟩ := P.χQ_cyc g 0 1 (by simp)
        have e : (P.χQ g : ℚ_[l]) = ((P.χQ g : ℚ_[l]) - a) + a := by ring
        rw [e]
        refine (Padic.nonarchimedean _ _).trans (max_le (by simpa using ha) ?_)
        exact_mod_cast Padic.norm_int_le_one (p := l) (a : ℤ)
      let x : ℤ_[l] := ⟨P.χQ g, hx⟩
      obtain ⟨a, ha, hg⟩ := P.χQ_cyc g k (P.ζQ k) (isPrimitiveRoot_zeta P k).pow_eq_one
      have hxa : PadicInt.toZModPow k x = a := by
        rw [← sub_eq_zero, ← map_natCast (PadicInt.toZModPow k), ← map_sub, ← RingHom.mem_ker,
          PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]
        exact ha
      have h1 : α * kummer P g + β * d g + (-r) * x = -r := by
        apply Subtype.ext
        have e : (x : ℚ_[l]) = P.χQ g := rfl
        have := h g
        push_cast
        rw [e]
        linear_combination this
      have h2 := congrArg (PadicInt.toZModPow k) h1
      rw [map_add, map_add, map_mul, map_mul, map_mul, hA, hB, hS, hxa] at h2
      have h3 : P.ζQ k ^ ((PadicInt.toZModPow k (kummer P g)).val * A +
          (PadicInt.toZModPow k (d g)).val * B + a * S) = P.ζQ k ^ S := by
        rw [zeta_pow_eq_iff]
        push_cast
        rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
        linear_combination h2
      rw [map_mul, map_mul, map_pow, map_pow, map_pow, hg, isKummer_kummer P g k, hd g k, ← h3]
      simp only [mul_pow, ← pow_mul, pow_add]
      ring
  refine ⟨x, (algebraMap ℚ_[l] (Om l)).injective ?_⟩
  rw [map_pow, hx, mul_pow, mul_pow, pow_right_comm (lRoot l k), pow_right_comm (μ k),
    pow_right_comm (P.ζQ k), lRoot_pow, hμ, (isPrimitiveRoot_zeta P k).pow_eq_one]
  simp

/- English proof (translation)
Rewrite using `[Padic.norm_natCast_eq_one_iff]`. Simplify using the standard rewrite rules.
-/
theorem norm_succ : ‖((l + 1 : ℕ) : ℚ_[l])‖ = 1 := by
  rw [Padic.norm_natCast_eq_one_iff]
  simp

/- English proof (translation)
Establish `hl : (l : ℚ_[l]) ≠ 0` using `Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero`. Establish `hl1 : ((l + 1 : ℕ) : ℚ_[l]) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)`. Establish `hv : ((l + 1 : ℕ) : ℚ_[l]).valuation = 0`. Rewrite using `[Padic.valuation_natCast, padicValNat.eq_zero_of_not_dvd]`. Simplify using the standard rewrite rules.

Rewrite using `[Nat.dvd_add_right dvd_rfl]`. Conclude with `(Fact.out : l.Prime).not_dvd_one`. Establish `h2` using `congrArg Padic.valuation h`. Rewrite `h2` using `[Padic.valuation_mul (pow_ne_zero _ hl) (pow_ne_zero _ hl1), Padic.valuation_pow, Padic.valuation_pow, Padic.valuation_pow, Padic.valuation_p, hv, mul_one, mul_zero, add_zero]`. Conclude with `Int.natCast_dvd_natCast.mp ⟨_, h2.symm⟩`.
-/
theorem dvd_of_root {k A B : ℕ} {q : ℚ_[l]}
    (h : q ^ (l ^ k) = (l : ℚ_[l]) ^ A * ((l + 1 : ℕ) : ℚ_[l]) ^ B) : l ^ k ∣ A := by
  have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have hl1 : ((l + 1 : ℕ) : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  have hv : ((l + 1 : ℕ) : ℚ_[l]).valuation = 0 := by
    rw [Padic.valuation_natCast, padicValNat.eq_zero_of_not_dvd]
    · simp
    · rw [Nat.dvd_add_right dvd_rfl]
      exact (Fact.out : l.Prime).not_dvd_one
  have h2 := congrArg Padic.valuation h
  rw [Padic.valuation_mul (pow_ne_zero _ hl) (pow_ne_zero _ hl1), Padic.valuation_pow,
    Padic.valuation_pow, Padic.valuation_pow, Padic.valuation_p, hv, mul_one, mul_zero,
    add_zero] at h2
  exact Int.natCast_dvd_natCast.mp ⟨_, h2.symm⟩

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Establish `key : ((((l + 1) ^ B) ^ (l - 1) : ℕ) : ℤ_[l]) = ((1 : ℕ) : ℤ_[l])`. Use `PadicInt.ext_of_toZModPow.mp fun n => ?_` and prove the remaining obligations. Consider the cases of `n with`. Consider the case `zero`.

Establish `: Subsingleton (ZMod (l ^ 0))` using `by rw [pow_zero]; infer_instance`. Conclude with `Subsingleton.elim _ _`. Consider the case `succ k`. Take `⟨q, hq⟩` from `h k`. Establish `hn : ‖q‖ ≤ 1`.

Use `congrArg norm hq` as an intermediate fact. Rewrite `this` using `[norm_pow, norm_pow, norm_succ, one_pow]`. Conclude with `(pow_le_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ hp.ne_zero)).mp this.le`. Set `y : ℤ_[l]` to `⟨q, hn⟩`. Establish `hy : y ^ (l ^ k) = (((l + 1) ^ B : ℕ) : ℤ_[l])`.

Apply `Subtype.ext` to reduce the goal to its premises. Establish `e : (y : ℚ_[l]) = q` using `rfl`. Move the coercions through the operations in `at hq ⊢`. Rewrite using `[e, hq]`. Establish `hu : IsUnit y`.

Rewrite using `[← isUnit_pow_iff (pow_ne_zero k hp.ne_zero), hy, PadicInt.isUnit_iff]`. Use `norm_succ (l := l)` as an intermediate fact. Rewrite using `[Nat.cast_pow, norm_pow]`. Establish `e : ‖((l + 1 : ℕ) : ℤ_[l])‖ = 1`. Rewrite using `[PadicInt.norm_def, PadicInt.coe_natCast, this]`.

Rewrite using `[e, one_pow]`. Take `⟨u, hu⟩` from `hu.map (PadicInt.toZModPow (k + 1))`. Establish `h1` using `congrArg Units.val (ZMod.pow_totient u)`. Rewrite `h1` using `[Nat.totient_prime_pow_succ hp, Units.val_pow_eq_pow_val, hu, pow_mul, ← map_pow, hy, ← map_pow]`. Rewrite using `[Nat.cast_pow, h1]`.

Simplify using the standard rewrite rules. Establish `h2 : ((l + 1) ^ B) ^ (l - 1) = 1` using `Nat.cast_injective key`. Use `hp.two_le` as an intermediate fact. Rewrite `h2` using `[← pow_mul, Nat.pow_eq_one]`. Break down `h2 with h2 | h2` into its components or cases.

Use linear arithmetic over natural numbers and integers. Apply the tactic sequence `rcases Nat.mul_eq_zero.mp h2 with h3 | h3 <;> omega`.
-/
theorem not_forall_root {B : ℕ} (hB : B ≠ 0)
    (h : ∀ k, ∃ q : ℚ_[l], q ^ (l ^ k) = ((l + 1 : ℕ) : ℚ_[l]) ^ B) : False := by
  have hp : l.Prime := Fact.out
  have key : ((((l + 1) ^ B) ^ (l - 1) : ℕ) : ℤ_[l]) = ((1 : ℕ) : ℤ_[l]) := by
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    cases n with
    | zero =>
      have : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
      exact Subsingleton.elim _ _
    | succ k =>
      obtain ⟨q, hq⟩ := h k
      have hn : ‖q‖ ≤ 1 := by
        have := congrArg norm hq
        rw [norm_pow, norm_pow, norm_succ, one_pow] at this
        exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ hp.ne_zero)).mp this.le
      let y : ℤ_[l] := ⟨q, hn⟩
      have hy : y ^ (l ^ k) = (((l + 1) ^ B : ℕ) : ℤ_[l]) := by
        apply Subtype.ext
        have e : (y : ℚ_[l]) = q := rfl
        push_cast at hq ⊢
        rw [e, hq]
      have hu : IsUnit y := by
        rw [← isUnit_pow_iff (pow_ne_zero k hp.ne_zero), hy, PadicInt.isUnit_iff]
        have := norm_succ (l := l)
        rw [Nat.cast_pow, norm_pow]
        have e : ‖((l + 1 : ℕ) : ℤ_[l])‖ = 1 := by
          rw [PadicInt.norm_def, PadicInt.coe_natCast, this]
        rw [e, one_pow]
      obtain ⟨u, hu⟩ := hu.map (PadicInt.toZModPow (k + 1))
      have h1 := congrArg Units.val (ZMod.pow_totient u)
      rw [Nat.totient_prime_pow_succ hp, Units.val_pow_eq_pow_val, hu, pow_mul, ← map_pow, hy,
        ← map_pow] at h1
      rw [Nat.cast_pow, h1]
      simp
  have h2 : ((l + 1) ^ B) ^ (l - 1) = 1 := Nat.cast_injective key
  have := hp.two_le
  rw [← pow_mul, Nat.pow_eq_one] at h2
  rcases h2 with h2 | h2
  · omega
  · rcases Nat.mul_eq_zero.mp h2 with h3 | h3 <;> omega

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Establish `hl : (l : ℚ_[l]) ≠ 0` using `Nat.cast_ne_zero.mpr hp.ne_zero`. Establish `hα : α = 0`. Take `⟨N, ⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩` from `((eventually_integral α).and ((eventually_integral β).and (eventually_integral r))).exists`. Establish `h0 : a = 0`.

Use `PadicInt.ext_of_toZModPow.mp fun k => ?_` and prove the remaining obligations. Establish `: NeZero (l ^ k)` using `⟨pow_ne_zero _ hp.ne_zero⟩`. Take `⟨q, hq⟩` from `exists_root P μ d hμ hd a b c (fun g => by rw [ha, hb, hc]; linear_combination (l : ℚ_[l]) ^ N * h g) k _ _ (ZMod.natCast_zmod_val _).symm (ZMod.natCast_zmod_val _).symm`. Rewrite using `[← ZMod.natCast_zmod_val (PadicInt.toZModPow k a), map_zero, ZMod.natCast_eq_zero_iff]`. Conclude with `dvd_of_root hq`.

Rewrite `ha` using `[h0]`. Conclude with `(mul_eq_zero.mp ha.symm).resolve_left (pow_ne_zero _ hl)`. Use `⟨hα, by_contra fun hβ => ?_⟩` and prove the remaining obligations. Take `⟨N, c, hc⟩` from `(eventually_integral (r / β)).exists`. Use `not_forall_root (l := l) (B := l ^ N) (pow_ne_zero _ hp.ne_zero) fun k => ?_` and prove the remaining obligations.

Use `exists_root P μ d hμ hd 0 ((l ^ N : ℕ) : ℤ_[l]) c (fun g => by` as an intermediate fact. Establish `h1` using `h g`. Rewrite `h1` using `[hα]`. Rewrite using `[hc]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `(l : ℚ_[l]) ^ N * h1) k 0 (l ^ N) (by simp) (map_natCast _ _)`. Simplify `this` using `only [pow_zero, one_mul]`.
-/
theorem kummer_indep (l : ℕ) [Fact l.Prime] (P : LocPrime l) (μ : ℕ → Om l) (d : GQ l → ℤ_[l])
    (hμ : ∀ m : ℕ, μ m ^ (l ^ m) = ((l + 1 : ℕ) : Om l))
    (hd : ∀ (g : GQ l) (m : ℕ), g (μ m) = P.ζQ m ^ (PadicInt.toZModPow m (d g)).val * μ m)
    (α β r : ℚ_[l])
    (h : ∀ g : GQ l, α * (kummer P g : ℚ_[l]) + β * (d g : ℚ_[l]) =
      r * ((P.χQ g : ℚ_[l]) - 1)) : α = 0 ∧ β = 0 := by
  have hp : l.Prime := Fact.out
  have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hα : α = 0 := by
    obtain ⟨N, ⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ := ((eventually_integral α).and
      ((eventually_integral β).and (eventually_integral r))).exists
    have h0 : a = 0 := by
      refine PadicInt.ext_of_toZModPow.mp fun k => ?_
      have : NeZero (l ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
      obtain ⟨q, hq⟩ := exists_root P μ d hμ hd a b c
        (fun g => by rw [ha, hb, hc]; linear_combination (l : ℚ_[l]) ^ N * h g) k _ _
        (ZMod.natCast_zmod_val _).symm (ZMod.natCast_zmod_val _).symm
      rw [← ZMod.natCast_zmod_val (PadicInt.toZModPow k a), map_zero, ZMod.natCast_eq_zero_iff]
      exact dvd_of_root hq
    rw [h0] at ha
    exact (mul_eq_zero.mp ha.symm).resolve_left (pow_ne_zero _ hl)
  refine ⟨hα, by_contra fun hβ => ?_⟩
  obtain ⟨N, c, hc⟩ := (eventually_integral (r / β)).exists
  refine not_forall_root (l := l) (B := l ^ N) (pow_ne_zero _ hp.ne_zero) fun k => ?_
  have := exists_root P μ d hμ hd 0 ((l ^ N : ℕ) : ℤ_[l]) c (fun g => by
    have h1 := h g
    rw [hα] at h1
    rw [hc]
    push_cast
    field_simp
    linear_combination (l : ℚ_[l]) ^ N * h1) k 0 (l ^ N) (by simp) (map_natCast _ _)
  simpa only [pow_zero, one_mul] using this

end GlobalTheory.Pst.KummerIndep
