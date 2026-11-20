import Formalism.GaussJetBounds.GenLogInverse
import Formalism.FormalGroupWitt.WeightInvariance

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open MvPowerSeries Formalism.IncomingBounds

/- English proof (translation)
Rewrite using `[add_pow, map_sum]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Establish `e : (C a * X x : MvPowerSeries σ K) ^ r * (C b * X y) ^ (k - r) * ((k.choose r : ℕ) : MvPowerSeries σ K) = C (a ^ r * b ^ (k - r) * (k.choose r : K)) * (X x ^ r * X y ^ (k - r))`. Simplify using `only [map_mul, map_pow, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, coeff_C_mul, X_pow_eq, X_pow_eq, monomial_mul_monomial, one_mul, coeff_monomial]`. Distinguish the cases in `h : Finsupp.single x r + Finsupp.single y (k - r) = μ`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg (Ne.symm h), if_neg h, mul_zero]`.
-/
theorem bnx_lin_pow {K : Type u} [Field K] {σ : Type*} [DecidableEq σ] (x y : σ) (a b : K) (k : ℕ)
    (μ : σ →₀ ℕ) :
    coeff μ ((C a * X x + C b * X y : MvPowerSeries σ K) ^ k) =
      ∑ r ∈ Finset.range (k + 1),
        if Finsupp.single x r + Finsupp.single y (k - r) = μ then
          a ^ r * b ^ (k - r) * (k.choose r : K) else 0 := by
  rw [add_pow, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have e : (C a * X x : MvPowerSeries σ K) ^ r * (C b * X y) ^ (k - r) *
      ((k.choose r : ℕ) : MvPowerSeries σ K) =
      C (a ^ r * b ^ (k - r) * (k.choose r : K)) * (X x ^ r * X y ^ (k - r)) := by
    simp only [map_mul, map_pow, map_natCast]
    ring
  rw [e, coeff_C_mul, X_pow_eq, X_pow_eq, monomial_mul_monomial, one_mul, coeff_monomial]
  by_cases h : Finsupp.single x r + Finsupp.single y (k - r) = μ
  · subst h
    simp
  · rw [if_neg (Ne.symm h), if_neg h, mul_zero]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1` using `DFunLike.congr_fun h x`. Establish `h2` using `DFunLike.congr_fun h y`. Simplify using `[Finsupp.single_apply, hxy, hxy.symm] at h1 h2`.

Conclude with `⟨h1, h2⟩`. Introduce and unpack `⟨rfl, rfl⟩`. Both sides reduce to the same expression.
-/
theorem bnx_single_add_single_eq {σ : Type*} {x y : σ} (hxy : x ≠ y) (r s i j : ℕ) :
    Finsupp.single x r + Finsupp.single y s = Finsupp.single x i + Finsupp.single y j ↔
      r = i ∧ s = j := by
  constructor
  · intro h
    have h1 := DFunLike.congr_fun h x
    have h2 := DFunLike.congr_fun h y
    simp [Finsupp.single_apply, hxy, hxy.symm] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/- English proof (translation)
Rewrite using `[bnx_lin_pow]`. Repeatedly rewrite using `[bnx_single_add_single_eq hxy]`. Use `split_ifs with hk`. Rewrite using `[Finset.sum_eq_single i]`. Establish `hj : k - i = j` using `by omega`.

Rewrite using `[if_pos ⟨rfl, hj⟩, hj]`. Introduce `r _ hr`. Rewrite using `[if_neg]`. Introduce and unpack `⟨h1, _⟩`. Conclude with `hr h1`.

Introduce `hi`. Simplify using `only [Finset.mem_range] at hi`. Use linear arithmetic over natural numbers and integers. Use `Finset.sum_eq_zero fun r hr => ?_` and prove the remaining obligations. Rewrite using `[if_neg]`.

Introduce and unpack `⟨h1, h2⟩`. Simplify using `only [Finset.mem_range] at hr`. Use linear arithmetic over natural numbers and integers.
-/
theorem bnx_lin_pow_val {K : Type u} [Field K] {σ : Type*} [DecidableEq σ] {x y : σ} (hxy : x ≠ y)
    (a b : K) (k i j : ℕ) :
    coeff (Finsupp.single x i + Finsupp.single y j) ((C a * X x + C b * X y : MvPowerSeries σ K) ^ k) =
      if i + j = k then a ^ i * b ^ j * (k.choose i : K) else 0 := by
  rw [bnx_lin_pow]
  simp_rw [bnx_single_add_single_eq hxy]
  split_ifs with hk
  · rw [Finset.sum_eq_single i]
    · have hj : k - i = j := by omega
      rw [if_pos ⟨rfl, hj⟩, hj]
    · intro r _ hr
      rw [if_neg]
      rintro ⟨h1, _⟩
      exact hr h1
    · intro hi
      simp only [Finset.mem_range] at hi
      omega
  · refine Finset.sum_eq_zero fun r hr => ?_
    rw [if_neg]
    rintro ⟨h1, h2⟩
    simp only [Finset.mem_range] at hr
    omega

/- English proof (translation)
Rewrite `h` using `[bnx_lin_pow]`. Take `⟨r, _, hr⟩` from `Finset.exists_ne_zero_of_sum_ne_zero h`. Use `split_ifs at hr with hμ`. Substitute `hμ` using the available equality. Assume the negation of the conclusion as `hne`.

Use `push_neg at hne`. Apply `hz` to reduce the goal to its premises. Simplify using `[Finsupp.single_apply, Ne.symm hne.1, Ne.symm hne.2]`. Conclude with `absurd rfl hr`.
-/
theorem bnx_lin_pow_supp {K : Type u} [Field K] {σ : Type*} [DecidableEq σ] (x y : σ)
    (a b : K) (k : ℕ) (μ : σ →₀ ℕ)
    (h : coeff μ ((C a * X x + C b * X y : MvPowerSeries σ K) ^ k) ≠ 0) (z : σ) (hz : μ z ≠ 0) :
    z = x ∨ z = y := by
  rw [bnx_lin_pow] at h
  obtain ⟨r, _, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  split_ifs at hr with hμ
  · subst hμ
    by_contra hne
    push_neg at hne
    apply hz
    simp [Finsupp.single_apply, Ne.symm hne.1, Ne.symm hne.2]
  · exact absurd rfl hr

section Blocks

variable {K : Type u} [Field K] {d : ℕ} [NeZero d]

def bnxA (a b : ZMod d → K) (s : ZMod d) : MvPowerSeries (V2 d) K :=
  C (a s) * X (false, s) + C (b s) * X (true, s)

def bnxRes (m : V2 d →₀ ℕ) (s : ZMod d) : V2 d →₀ ℕ :=
  Finsupp.single (false, s) (m (false, s)) + Finsupp.single (true, s) (m (true, s))

/- English proof (translation)
Take `⟨b, t⟩` from `z`. Distinguish the cases in `h : t = s`. Substitute `h` using the available equality. Apply the tactic sequence `cases b <;> simp [bnxRes, Finsupp.single_apply]`. Apply the tactic sequence `cases b <;> simp [bnxRes, Finsupp.single_apply, h, Ne.symm h]`.
-/
theorem bnxRes_apply (m : V2 d →₀ ℕ) (s : ZMod d) (z : V2 d) :
    bnxRes m s z = if z.2 = s then m z else 0 := by
  obtain ⟨b, t⟩ := z
  by_cases h : t = s
  · subst h
    cases b <;> simp [bnxRes, Finsupp.single_apply]
  · cases b <;> simp [bnxRes, Finsupp.single_apply, h, Ne.symm h]

/- English proof (translation)
Use `revert m`. Use `Finset.induction_on S ?_ ?_` and prove the remaining obligations. Introduce `m`. Rewrite using `[Finset.prod_empty, Finset.prod_empty, coeff_one]`. Distinguish the cases in `hm : m = 0`.

Substitute `hm` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg hm, if_neg]`. Introduce `h`. Apply `hm` to reduce the goal to its premises.

Use extensionality with `z`. Conclude with `h z (by simp)`. Introduce `c S ha ih m`. Establish `hr : ∀ z, bnxRes m c z = if z.2 = c then m z else 0` using `bnxRes_apply m c`. Rewrite using `[Finset.prod_insert ha, Finset.prod_insert ha, coeff_mul]`.

Rewrite using `[Finset.sum_eq_single (bnxRes m c, m - bnxRes m c)]`. Rewrite using `[ih]`. Establish `hcond : (∀ z : V2 d, z.2 ∉ S → (m - bnxRes m c) z = 0) ↔ (∀ z : V2 d, z.2 ∉ insert c S → m z = 0)`. Prove the components needed by the constructor for the conclusion. Introduce `h z hz`.

Establish `h1` using `h z (fun hS => hz (Finset.mem_insert_of_mem hS))`. Establish `hza : z.2 ≠ c` using `fun e => hz (by rw [e]; exact Finset.mem_insert_self c S)`. Rewrite `h1` using `[Finsupp.tsub_apply, hr, if_neg hza]`. Use linear arithmetic over natural numbers and integers. Introduce `h z hz`.

Rewrite using `[Finsupp.tsub_apply, hr]`. Use `split_ifs with hza`. Use linear arithmetic over natural numbers and integers. Establish `h2` using `h z (by simp [hza, hz])`. Use linear arithmetic over natural numbers and integers.

Distinguish the cases in `hc : ∀ z : V2 d, z.2 ∉ insert c S → m z = 0`. Rewrite using `[if_pos (hcond.2 hc), if_pos hc]`. Use `congr 1`. Use `Finset.prod_congr rfl fun s hs => ?_` and prove the remaining obligations. Establish `hsa : s ≠ c` using `fun e => ha (by rw [← e]; exact hs)`.

Establish `hres : bnxRes (m - bnxRes m c) s = bnxRes m s`. Use extensionality with `z`. Simplify using `only [bnxRes_apply, Finsupp.tsub_apply]`. Distinguish the cases in `h1 : z.2 = s`. Simplify using `[h1, hsa]`.

Simplify using `[h1]`. Rewrite using `[hres]`. Rewrite using `[if_neg (mt hcond.1 hc), if_neg hc, mul_zero]`. Introduce `p hp hne first`. Consider the case `rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp`.

Consider the case `simp only [Finset.mem_antidiagonal] at hp`. Assume the negation of the conclusion as `hnz`. Establish `h1 : coeff p.1 (bnxA a b c ^ k c) ≠ 0` using `left_ne_zero_of_mul hnz`. Establish `h2 : coeff p.2 (∏ s ∈ S, bnxA a b s ^ k s) ≠ 0` using `right_ne_zero_of_mul hnz`. Rewrite `h2` using `[ih]`.

Establish `hP : ∀ z : V2 d, z.2 ∉ S → p.2 z = 0`. Assume the negation of the conclusion as `hP`. Conclude with `h2 (if_neg hP)`. Establish `hs1 : ∀ z : V2 d, z.2 ≠ c → p.1 z = 0`. Introduce `z hz`.

Assume the negation of the conclusion as `hz0`. Apply the tactic sequence `rcases bnx_lin_pow_supp (false, c) (true, c) (a c) (b c) (k c) p.1 h1 z hz0 with h | h <;> (subst h; exact hz rfl)`. Apply `hne` to reduce the goal to its premises. Establish `e1 : p.1 = bnxRes m c`. Use extensionality with `z`.

Rewrite using `[hr]`. Use `split_ifs with hz`. Establish `h4` using `hP z (by rw [hz]; exact ha)`. Establish `h3` using `DFunLike.congr_fun hp z`. Rewrite `h3` using `[Finsupp.add_apply]`.

Use linear arithmetic over natural numbers and integers. Conclude with `hs1 z hz`. Establish `e2 : p.2 = m - bnxRes m c`. Use extensionality with `z`. Establish `h3` using `DFunLike.congr_fun hp z`.

Rewrite `h3` using `[Finsupp.add_apply]`. Rewrite using `[Finsupp.tsub_apply, ← e1]`. Use linear arithmetic over natural numbers and integers. Conclude with `Prod.ext e1 e2`. Introduce `h`.

It suffices to derive a contradiction. Apply `h` to reduce the goal to its premises. Use `first`. Consider the case `rw [Finset.HasAntidiagonal.mem_antidiagonal]`. Consider the case `simp only [Finset.mem_antidiagonal]`.

Use extensionality with `z`. Rewrite using `[Finsupp.add_apply, Finsupp.tsub_apply, hr]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
private theorem coeff_prod_bnxA_pow_eq_ite {K : Type u} [Field K] {d : ℕ} [NeZero d]
    (a b : ZMod d → K) (k : ZMod d → ℕ) (S : Finset (ZMod d)) (m : V2 d →₀ ℕ) :
    coeff m (∏ s ∈ S, bnxA a b s ^ k s) =
      if ∀ z : V2 d, z.2 ∉ S → m z = 0 then
        ∏ s ∈ S, coeff (bnxRes m s) (bnxA a b s ^ k s) else 0 := by
  revert m
  refine Finset.induction_on S ?_ ?_
  · intro m
    rw [Finset.prod_empty, Finset.prod_empty, coeff_one]
    by_cases hm : m = 0
    · subst hm
      simp
    · rw [if_neg hm, if_neg]
      intro h
      apply hm
      ext z
      exact h z (by simp)
  · intro c S ha ih m
    have hr : ∀ z, bnxRes m c z = if z.2 = c then m z else 0 := bnxRes_apply m c
    rw [Finset.prod_insert ha, Finset.prod_insert ha, coeff_mul]
    rw [Finset.sum_eq_single (bnxRes m c, m - bnxRes m c)]
    · rw [ih]
      have hcond : (∀ z : V2 d, z.2 ∉ S → (m - bnxRes m c) z = 0) ↔
          (∀ z : V2 d, z.2 ∉ insert c S → m z = 0) := by
        constructor
        · intro h z hz
          have h1 := h z (fun hS => hz (Finset.mem_insert_of_mem hS))
          have hza : z.2 ≠ c := fun e => hz (by rw [e]; exact Finset.mem_insert_self c S)
          rw [Finsupp.tsub_apply, hr, if_neg hza] at h1
          omega
        · intro h z hz
          rw [Finsupp.tsub_apply, hr]
          split_ifs with hza
          · omega
          · have h2 := h z (by simp [hza, hz])
            omega
      by_cases hc : ∀ z : V2 d, z.2 ∉ insert c S → m z = 0
      · rw [if_pos (hcond.2 hc), if_pos hc]
        congr 1
        refine Finset.prod_congr rfl fun s hs => ?_
        have hsa : s ≠ c := fun e => ha (by rw [← e]; exact hs)
        have hres : bnxRes (m - bnxRes m c) s = bnxRes m s := by
          ext z
          simp only [bnxRes_apply, Finsupp.tsub_apply]
          by_cases h1 : z.2 = s
          · simp [h1, hsa]
          · simp [h1]
        rw [hres]
      · rw [if_neg (mt hcond.1 hc), if_neg hc, mul_zero]
    · intro p hp hne
      first
        | rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
        | simp only [Finset.mem_antidiagonal] at hp
      by_contra hnz
      have h1 : coeff p.1 (bnxA a b c ^ k c) ≠ 0 := left_ne_zero_of_mul hnz
      have h2 : coeff p.2 (∏ s ∈ S, bnxA a b s ^ k s) ≠ 0 := right_ne_zero_of_mul hnz
      rw [ih] at h2
      have hP : ∀ z : V2 d, z.2 ∉ S → p.2 z = 0 := by
        by_contra hP
        exact h2 (if_neg hP)
      have hs1 : ∀ z : V2 d, z.2 ≠ c → p.1 z = 0 := by
        intro z hz
        by_contra hz0
        rcases bnx_lin_pow_supp (false, c) (true, c) (a c) (b c) (k c) p.1 h1 z hz0 with h | h <;>
          (subst h; exact hz rfl)
      apply hne
      have e1 : p.1 = bnxRes m c := by
        ext z
        rw [hr]
        split_ifs with hz
        · have h4 := hP z (by rw [hz]; exact ha)
          have h3 := DFunLike.congr_fun hp z
          rw [Finsupp.add_apply] at h3
          omega
        · exact hs1 z hz
      have e2 : p.2 = m - bnxRes m c := by
        ext z
        have h3 := DFunLike.congr_fun hp z
        rw [Finsupp.add_apply] at h3
        rw [Finsupp.tsub_apply, ← e1]
        omega
      exact Prod.ext e1 e2
    · intro h
      exfalso
      apply h
      first
      | rw [Finset.HasAntidiagonal.mem_antidiagonal]
      | simp only [Finset.mem_antidiagonal]
      ext z
      rw [Finsupp.add_apply, Finsupp.tsub_apply, hr]
      split_ifs <;> omega

/- English proof (translation)
Rewrite using `[coeff_prod_bnxA_pow_eq_ite, if_pos (fun z hz => absurd (Finset.mem_univ _) hz)]`.
-/
theorem bnx_coeff_prod (a b : ZMod d → K) (k : ZMod d → ℕ) (m : V2 d →₀ ℕ) :
    coeff m (∏ s, bnxA a b s ^ k s) = ∏ s, coeff (bnxRes m s) (bnxA a b s ^ k s) := by
  rw [coeff_prod_bnxA_pow_eq_ite, if_pos (fun z hz => absurd (Finset.mem_univ _) hz)]

end Blocks

section Subst

variable {K : Type u} [Field K] {d : ℕ} [NeZero d]

def bnxN (m : V2 d →₀ ℕ) : ZMod d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun s => m (false, s) + m (true, s)

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `simp [bnxN]`.
-/
theorem bnxN_apply (m : V2 d →₀ ℕ) (s : ZMod d) : bnxN m s = m (false, s) + m (true, s) := by
  first
  | rfl
  | simp [bnxN]

/- English proof (translation)
Establish `ha : HasSubst (bnxA a b)` using `hasSubst_of_constantCoeff_zero fun s => by simp [bnxA]`. Rewrite using `[coeff_subst ha]`. Establish `hterm : ∀ dd : ZMod d →₀ ℕ, coeff m (dd.prod fun s e => bnxA a b s ^ e) = ∏ s, (if m (false, s) + m (true, s) = dd s then a s ^ m (false, s) * b s ^ m (true, s) * ((dd s).choose (m (false, s)) : K) else 0)`. Introduce `dd`. Rewrite using `[Finsupp.prod_fintype _ _ (fun s => pow_zero _), bnx_coeff_prod]`.

Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Establish `hres : bnxRes m s = Finsupp.single (false, s) (m (false, s)) + Finsupp.single (true, s) (m (true, s))` using `rfl`. Rewrite using `[hres]`. Conclude with `bnx_lin_pow_val (x := (false, s)) (y := (true, s)) (by simp) (a s) (b s) (dd s) _ _`. Rewrite using `[finsum_eq_single _ (bnxN m)]`.

Rewrite using `[hterm, smul_eq_mul]`. Use `congr 1`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[if_pos (bnxN_apply m s).symm, bnxN_apply]`. Introduce `dd hdd`.

Establish `hex : ∃ s, dd s ≠ bnxN m s`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hdd (Finsupp.ext hc)`. Take `⟨s, hs⟩` from `hex`.

Rewrite using `[hterm, Finset.prod_eq_zero (Finset.mem_univ s), smul_zero]`. Rewrite using `[if_neg]`. Introduce `h`. Apply `hs` to reduce the goal to its premises. Rewrite using `[← h, bnxN_apply]`.
-/
theorem bnx_coeff_subst (a b : ZMod d → K) (f : MvPowerSeries (ZMod d) K) (m : V2 d →₀ ℕ) :
    coeff m (subst (bnxA a b) f) = coeff (bnxN m) f *
      ∏ s, (a s ^ m (false, s) * b s ^ m (true, s) *
        ((m (false, s) + m (true, s)).choose (m (false, s)) : K)) := by
  have ha : HasSubst (bnxA a b) := hasSubst_of_constantCoeff_zero fun s => by simp [bnxA]
  rw [coeff_subst ha]
  have hterm : ∀ dd : ZMod d →₀ ℕ, coeff m (dd.prod fun s e => bnxA a b s ^ e) =
      ∏ s, (if m (false, s) + m (true, s) = dd s then
        a s ^ m (false, s) * b s ^ m (true, s) * ((dd s).choose (m (false, s)) : K) else 0) := by
    intro dd
    rw [Finsupp.prod_fintype _ _ (fun s => pow_zero _), bnx_coeff_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    have hres : bnxRes m s = Finsupp.single (false, s) (m (false, s)) +
        Finsupp.single (true, s) (m (true, s)) := rfl
    rw [hres]
    exact bnx_lin_pow_val (x := (false, s)) (y := (true, s)) (by simp) (a s) (b s) (dd s) _ _
  rw [finsum_eq_single _ (bnxN m)]
  · rw [hterm, smul_eq_mul]
    congr 1
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [if_pos (bnxN_apply m s).symm, bnxN_apply]
  · intro dd hdd
    have hex : ∃ s, dd s ≠ bnxN m s := by
      by_contra hc
      push_neg at hc
      exact hdd (Finsupp.ext hc)
    obtain ⟨s, hs⟩ := hex
    rw [hterm, Finset.prod_eq_zero (Finset.mem_univ s), smul_zero]
    rw [if_neg]
    intro h
    apply hs
    rw [← h, bnxN_apply]

/- English proof (translation)
Use function extensionality and compare the values at `s`. Simplify using `only [s1, bnxA]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem evenIndicator_series_binomial_form : (s1 : ZMod d → MvPowerSeries (V2 d) K) =
    bnxA (fun _ => 1) (fun s => if s.val % 2 = 0 then 1 else 0) := by
  funext s
  simp only [s1, bnxA]
  split_ifs <;> simp

/- English proof (translation)
Use function extensionality and compare the values at `s`. Simplify using `[s0, bnxA]`.
-/
theorem zero_series_binomial_form : (s0 : ZMod d → MvPowerSeries (V2 d) K) = bnxA (fun _ => 1) (fun _ => 0) := by
  funext s
  simp [s0, bnxA]

/- English proof (translation)
Use function extensionality and compare the values at `s`. Simplify using `only [s2, bnxA]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem swapped_parity_series_binomial_form : (s2 : ZMod d → MvPowerSeries (V2 d) K) =
    bnxA (fun s => if s.val % 2 = 0 then 0 else 1) (fun s => if s.val % 2 = 0 then 1 else 0) := by
  funext s
  simp only [s2, bnxA]
  split_ifs <;> simp

/- English proof (translation)
Use function extensionality and compare the values at `s`. Simplify using `only [s1', bnxA]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem oddIndicator_series_binomial_form : (s1' : ZMod d → MvPowerSeries (V2 d) K) =
    bnxA (fun _ => 1) (fun s => if s.val % 2 = 0 then 0 else 1) := by
  funext s
  simp only [s1', bnxA]
  split_ifs <;> simp

/- English proof (translation)
Use function extensionality and compare the values at `s`. Simplify using `only [s2', bnxA]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem parity_series_binomial_form : (s2' : ZMod d → MvPowerSeries (V2 d) K) =
    bnxA (fun s => if s.val % 2 = 0 then 1 else 0) (fun s => if s.val % 2 = 0 then 0 else 1) := by
  funext s
  simp only [s2', bnxA]
  split_ifs <;> simp

def bnxM (n : ZMod d →₀ ℕ) (k : ZMod d → ℕ) : V2 d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun x => if x.1 then n x.2 - k x.2 else k x.2

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `simp [bnxM]`.
-/
theorem bnxM_false (n : ZMod d →₀ ℕ) (k : ZMod d → ℕ) (s : ZMod d) : bnxM n k (false, s) = k s := by
  first
  | rfl
  | simp [bnxM]

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `simp [bnxM]`.
-/
theorem bnxM_true (n : ZMod d →₀ ℕ) (k : ZMod d → ℕ) (s : ZMod d) :
    bnxM n k (true, s) = n s - k s := by
  first
  | rfl
  | simp [bnxM]

/- English proof (translation)
Use extensionality with `s`. Rewrite using `[bnxN_apply, bnxM_false, bnxM_true]`. Use `hk s` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem bnxN_bnxM (n : ZMod d →₀ ℕ) (k : ZMod d → ℕ) (hk : ∀ s, k s ≤ n s) : bnxN (bnxM n k) = n := by
  ext s
  rw [bnxN_apply, bnxM_false, bnxM_true]
  have := hk s
  omega

/- English proof (translation)
Rewrite using `[Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fintype.sum_prod_type]`. Simplify using `only [Fintype.sum_bool, bnxM_true, bnxM_false]`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun s _ => by have := hk s; omega`.
-/
theorem bnx_degree_bnxM (n : ZMod d →₀ ℕ) (k : ZMod d → ℕ) (hk : ∀ s, k s ≤ n s) :
    (bnxM n k).degree = n.degree := by
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, bnxM_true, bnxM_false]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by have := hk s; omega

end Subst

section De

variable {K : Type u} [Field K] {d : ℕ} [NeZero d]

/- English proof (translation)
Introduce `t`. Rewrite using `[Function.update_apply]`. Use `split_ifs with h`. Substitute `h` using the available equality. Conclude with `hj.le`.

Conclude with `le_rfl`.
-/
theorem bnx_update_le (n : ZMod d →₀ ℕ) (s : ZMod d) (j : ℕ) (hj : j < n s) :
    ∀ t, Function.update (⇑n) s j t ≤ n t := by
  intro t
  rw [Function.update_apply]
  split_ifs with h
  · subst h
    exact hj.le
  · exact le_rfl

/- English proof (translation)
Rewrite using `[Finset.prod_eq_single s]`. Use `first`. Consider the case `(rw [Function.update_apply, if_pos rfl, he, one_pow, one_pow, one_mul, one_mul, Nat.add_sub_cancel' hj.le])`. Consider the case `simp [Function.update_apply, he, Nat.add_sub_cancel' hj.le]`. Introduce `t _ hts`.

Simplify using `[Function.update_apply, hts]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ s) h`.
-/
theorem bnx_prod_choose (n : ZMod d →₀ ℕ) (s : ZMod d) (j : ℕ) (hj : j < n s) (e : ZMod d → K)
    (he : e s = 1) :
    ∏ t, ((1 : K) ^ Function.update (⇑n) s j t * e t ^ (n t - Function.update (⇑n) s j t) *
      ((Function.update (⇑n) s j t + (n t - Function.update (⇑n) s j t)).choose
        (Function.update (⇑n) s j t) : K)) = ((n s).choose j : K) := by
  rw [Finset.prod_eq_single s]
  · first
    | (rw [Function.update_apply, if_pos rfl, he, one_pow, one_pow, one_mul, one_mul,
        Nat.add_sub_cancel' hj.le])
    | simp [Function.update_apply, he, Nat.add_sub_cancel' hj.le]
  · intro t _ hts
    simp [Function.update_apply, hts]
  · intro h
    exact absurd (Finset.mem_univ s) h

/- English proof (translation)
Establish `hk` using `bnx_update_le n s j hj`. Unfold `de1`. Rewrite using `[map_sub, map_sub, evenIndicator_series_binomial_form, zero_series_binomial_form, swapped_parity_series_binomial_form, bnx_coeff_subst, bnx_coeff_subst, bnx_coeff_subst, bnxN_bnxM n _ hk]`. Simplify using `only [bnxM_false, bnxM_true]`. Rewrite using `[bnx_prod_choose n s j hj (fun t => if t.val % 2 = 0 then (1 : K) else 0) (by simp [hs])]`.

Establish `hz0 : ∏ t, ((1 : K) ^ Function.update (⇑n) s j t * (0 : K) ^ (n t - Function.update (⇑n) s j t) * ((Function.update (⇑n) s j t + (n t - Function.update (⇑n) s j t)).choose (Function.update (⇑n) s j t) : K)) = 0`. Apply `Finset.prod_eq_zero (Finset.mem_univ s)` to reduce the goal to its premises. Rewrite using `[Function.update_apply, if_pos rfl, zero_pow (by omega)]`. Simplify using the standard rewrite rules. Establish `hz2 : ∏ t, ((if t.val % 2 = 0 then (0 : K) else 1) ^ Function.update (⇑n) s j t * (if t.val % 2 = 0 then (1 : K) else 0) ^ (n t - Function.update (⇑n) s j t) * ((Function.update (⇑n) s j t + (n t - Function.update (⇑n) s j t)).choose (Function.update (⇑n) s j t) : K)) = 0`.

Break down `hpos with hj0 | ⟨t, ht, hts, hnt⟩` into its components or cases. Apply `Finset.prod_eq_zero (Finset.mem_univ s)` to reduce the goal to its premises. Rewrite using `[Function.update_apply, if_pos rfl, if_pos hs, zero_pow (by omega)]`. Simplify using the standard rewrite rules. Apply `Finset.prod_eq_zero (Finset.mem_univ t)` to reduce the goal to its premises.

Rewrite using `[Function.update_apply, if_neg hts, if_pos ht, zero_pow hnt]`. Simplify using the standard rewrite rules. Rewrite using `[hz0, hz2, mul_zero, sub_zero, sub_zero]`.
-/
theorem evenDerivative_binomial_coeff (be : MvPowerSeries (ZMod d) K) (n : ZMod d →₀ ℕ) (s : ZMod d)
    (hs : s.val % 2 = 0) (j : ℕ) (hj : j < n s)
    (hpos : 0 < j ∨ ∃ t : ZMod d, t.val % 2 = 0 ∧ t ≠ s ∧ n t ≠ 0) :
    coeff (bnxM n (Function.update (⇑n) s j)) (de1 be) = coeff n be * ((n s).choose j : K) := by
  have hk := bnx_update_le n s j hj
  unfold de1
  rw [map_sub, map_sub, evenIndicator_series_binomial_form, zero_series_binomial_form, swapped_parity_series_binomial_form, bnx_coeff_subst, bnx_coeff_subst, bnx_coeff_subst,
    bnxN_bnxM n _ hk]
  simp only [bnxM_false, bnxM_true]
  rw [bnx_prod_choose n s j hj (fun t => if t.val % 2 = 0 then (1 : K) else 0) (by simp [hs])]
  have hz0 : ∏ t, ((1 : K) ^ Function.update (⇑n) s j t * (0 : K) ^ (n t - Function.update (⇑n) s j t) *
      ((Function.update (⇑n) s j t + (n t - Function.update (⇑n) s j t)).choose
        (Function.update (⇑n) s j t) : K)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ s)
    rw [Function.update_apply, if_pos rfl, zero_pow (by omega)]
    simp
  have hz2 : ∏ t, ((if t.val % 2 = 0 then (0 : K) else 1) ^ Function.update (⇑n) s j t *
      (if t.val % 2 = 0 then (1 : K) else 0) ^ (n t - Function.update (⇑n) s j t) *
      ((Function.update (⇑n) s j t + (n t - Function.update (⇑n) s j t)).choose
        (Function.update (⇑n) s j t) : K)) = 0 := by
    rcases hpos with hj0 | ⟨t, ht, hts, hnt⟩
    · apply Finset.prod_eq_zero (Finset.mem_univ s)
      rw [Function.update_apply, if_pos rfl, if_pos hs, zero_pow (by omega)]
      simp
    · apply Finset.prod_eq_zero (Finset.mem_univ t)
      rw [Function.update_apply, if_neg hts, if_pos ht, zero_pow hnt]
      simp
  rw [hz0, hz2, mul_zero, sub_zero, sub_zero]

/- English proof (translation)
Establish `hk` using `bnx_update_le n s j hj`. Unfold `de2`. Rewrite using `[map_sub, map_sub, oddIndicator_series_binomial_form, zero_series_binomial_form, parity_series_binomial_form, bnx_coeff_subst, bnx_coeff_subst, bnx_coeff_subst, bnxN_bnxM n _ hk]`. Simplify using `only [bnxM_false, bnxM_true]`. Rewrite using `[bnx_prod_choose n s j hj (fun t => if t.val % 2 = 0 then (0 : K) else 1) (by simp [hs])]`.

Establish `hz0 : ∏ t, ((1 : K) ^ Function.update (⇑n) s j t * (0 : K) ^ (n t - Function.update (⇑n) s j t) * ((Function.update (⇑n) s j t + (n t - Function.update (⇑n) s j t)).choose (Function.update (⇑n) s j t) : K)) = 0`. Apply `Finset.prod_eq_zero (Finset.mem_univ s)` to reduce the goal to its premises. Rewrite using `[Function.update_apply, if_pos rfl, zero_pow (by omega)]`. Simplify using the standard rewrite rules. Establish `hz2 : ∏ t, ((if t.val % 2 = 0 then (1 : K) else 0) ^ Function.update (⇑n) s j t * (if t.val % 2 = 0 then (0 : K) else 1) ^ (n t - Function.update (⇑n) s j t) * ((Function.update (⇑n) s j t + (n t - Function.update (⇑n) s j t)).choose (Function.update (⇑n) s j t) : K)) = 0`.

Break down `hpos with hj0 | ⟨t, ht, hts, hnt⟩` into its components or cases. Apply `Finset.prod_eq_zero (Finset.mem_univ s)` to reduce the goal to its premises. Rewrite using `[Function.update_apply, if_pos rfl, if_neg hs, zero_pow (by omega)]`. Simplify using the standard rewrite rules. Apply `Finset.prod_eq_zero (Finset.mem_univ t)` to reduce the goal to its premises.

Rewrite using `[Function.update_apply, if_neg hts, if_neg ht, zero_pow hnt]`. Simplify using the standard rewrite rules. Rewrite using `[hz0, hz2, mul_zero, sub_zero, sub_zero]`.
-/
theorem oddDerivative_binomial_coeff (be : MvPowerSeries (ZMod d) K) (n : ZMod d →₀ ℕ) (s : ZMod d)
    (hs : s.val % 2 ≠ 0) (j : ℕ) (hj : j < n s)
    (hpos : 0 < j ∨ ∃ t : ZMod d, t.val % 2 ≠ 0 ∧ t ≠ s ∧ n t ≠ 0) :
    coeff (bnxM n (Function.update (⇑n) s j)) (de2 be) = coeff n be * ((n s).choose j : K) := by
  have hk := bnx_update_le n s j hj
  unfold de2
  rw [map_sub, map_sub, oddIndicator_series_binomial_form, zero_series_binomial_form, parity_series_binomial_form, bnx_coeff_subst, bnx_coeff_subst, bnx_coeff_subst,
    bnxN_bnxM n _ hk]
  simp only [bnxM_false, bnxM_true]
  rw [bnx_prod_choose n s j hj (fun t => if t.val % 2 = 0 then (0 : K) else 1) (by simp [hs])]
  have hz0 : ∏ t, ((1 : K) ^ Function.update (⇑n) s j t * (0 : K) ^ (n t - Function.update (⇑n) s j t) *
      ((Function.update (⇑n) s j t + (n t - Function.update (⇑n) s j t)).choose
        (Function.update (⇑n) s j t) : K)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ s)
    rw [Function.update_apply, if_pos rfl, zero_pow (by omega)]
    simp
  have hz2 : ∏ t, ((if t.val % 2 = 0 then (1 : K) else 0) ^ Function.update (⇑n) s j t *
      (if t.val % 2 = 0 then (0 : K) else 1) ^ (n t - Function.update (⇑n) s j t) *
      ((Function.update (⇑n) s j t + (n t - Function.update (⇑n) s j t)).choose
        (Function.update (⇑n) s j t) : K)) = 0 := by
    rcases hpos with hj0 | ⟨t, ht, hts, hnt⟩
    · apply Finset.prod_eq_zero (Finset.mem_univ s)
      rw [Function.update_apply, if_pos rfl, if_neg hs, zero_pow (by omega)]
      simp
    · apply Finset.prod_eq_zero (Finset.mem_univ t)
      rw [Function.update_apply, if_neg hts, if_neg ht, zero_pow hnt]
      simp
  rw [hz0, hz2, mul_zero, sub_zero, sub_zero]

end De

section NormNat

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

/- English proof (translation)
Establish `hcop : Nat.Coprime l B` using `(Nat.Prime.coprime_iff_not_dvd hl).2 hB`. Take `⟨u, v, huv⟩` from `Nat.isCoprime_iff_coprime.2 hcop`. Establish `h1 : (u : K) * (l : K) + (v : K) * (B : K) = 1`. Use `congrArg (fun z : ℤ => (z : K)) huv` as an intermediate fact. Move the coercions through the operations in `at this`.

Conclude with `this`. Establish `hu : ‖(u : K)‖ ≤ 1` using `IsUltrametricDist.norm_intCast_le_one K u`. Establish `hv : ‖(v : K)‖ ≤ 1` using `IsUltrametricDist.norm_intCast_le_one K v`. Establish `key : ‖(1 : K)‖ ≤ max ‖(u : K) * (l : K)‖ ‖(v : K) * (B : K)‖`. Rewrite using `[← h1]`.

Conclude with `IsUltrametricDist.norm_add_le_max _ _`. Rewrite `key` using `[norm_one, norm_mul, norm_mul]`. Establish `hl0 : 0 ≤ ‖(l : K)‖` using `norm_nonneg _`. Establish `hB0 : 0 ≤ ‖(B : K)‖` using `norm_nonneg _`. Establish `hA : ‖(u : K)‖ * ‖(l : K)‖ < 1`.

Combine the equalities or inequalities in the displayed calculation. Establish `hC : ‖(v : K)‖ * ‖(B : K)‖ ≤ ‖(B : K)‖`. Combine the equalities or inequalities in the displayed calculation. Break down `le_max_iff.1 key with h | h` into its components or cases. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem bnx_norm_one {l : ℕ} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) (B : ℕ) (hB : ¬ l ∣ B) :
    1 ≤ ‖(B : K)‖ := by
  have hcop : Nat.Coprime l B := (Nat.Prime.coprime_iff_not_dvd hl).2 hB
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have h1 : (u : K) * (l : K) + (v : K) * (B : K) = 1 := by
    have := congrArg (fun z : ℤ => (z : K)) huv
    push_cast at this
    exact this
  have hu : ‖(u : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one K u
  have hv : ‖(v : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one K v
  have key : ‖(1 : K)‖ ≤ max ‖(u : K) * (l : K)‖ ‖(v : K) * (B : K)‖ := by
    rw [← h1]
    exact IsUltrametricDist.norm_add_le_max _ _
  rw [norm_one, norm_mul, norm_mul] at key
  have hl0 : 0 ≤ ‖(l : K)‖ := norm_nonneg _
  have hB0 : 0 ≤ ‖(B : K)‖ := norm_nonneg _
  have hA : ‖(u : K)‖ * ‖(l : K)‖ < 1 := by
    calc ‖(u : K)‖ * ‖(l : K)‖ ≤ 1 * ‖(l : K)‖ := mul_le_mul_of_nonneg_right hu hl0
      _ < 1 := by rw [one_mul]; exact hl1
  have hC : ‖(v : K)‖ * ‖(B : K)‖ ≤ ‖(B : K)‖ := by
    calc ‖(v : K)‖ * ‖(B : K)‖ ≤ 1 * ‖(B : K)‖ := mul_le_mul_of_nonneg_right hv hB0
      _ = ‖(B : K)‖ := one_mul _
  rcases le_max_iff.1 key with h | h
  · linarith
  · linarith

/- English proof (translation)
Distinguish the cases in `hd : l ∣ B`. Take `⟨B', rfl⟩` from `hd`. Establish `hB' : ¬ l ∣ B'` using `fun h => hB (by rw [pow_two]; exact mul_dvd_mul_left l h)`. Rewrite using `[Nat.cast_mul, norm_mul]`. Establish `h1` using `bnx_norm_one hl hl1 B' hB'`.

Establish `h0 : 0 ≤ ‖(l : K)‖` using `norm_nonneg _`. Use the polynomial consequences of the given equalities and inequalities. Establish `h1` using `bnx_norm_one hl hl1 B hd`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem bnx_norm_ge {l : ℕ} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) (B : ℕ) (hB0 : B ≠ 0)
    (hB : ¬ l ^ 2 ∣ B) : ‖(l : K)‖ ≤ ‖(B : K)‖ := by
  by_cases hd : l ∣ B
  · obtain ⟨B', rfl⟩ := hd
    have hB' : ¬ l ∣ B' := fun h => hB (by rw [pow_two]; exact mul_dvd_mul_left l h)
    rw [Nat.cast_mul, norm_mul]
    have h1 := bnx_norm_one hl hl1 B' hB'
    have h0 : 0 ≤ ‖(l : K)‖ := norm_nonneg _
    nlinarith
  · have h1 := bnx_norm_one hl hl1 B hd
    linarith

end NormNat

/- English proof (translation)
Use `haveI := Fact.mk hl`. Introduce `a`. Proceed by induction on `a with`. Consider the case `zero => simp [Nat.ModEq]`. Consider the case `succ a ih`.

Establish `h` using `Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := l * (l ^ a * c)) (k := l * l ^ a) (p := l)`. Rewrite `h` using `[Nat.mul_mod_right, Nat.mul_mod_right, Nat.mul_div_cancel_left _ hl.pos, Nat.mul_div_cancel_left _ hl.pos, Nat.choose_self, one_mul]`. Rewrite using `[pow_succ', mul_assoc]`. Conclude with `h.trans ih`.
-/
theorem bnx_choose_lucas {l : ℕ} (hl : l.Prime) (c : ℕ) :
    ∀ a : ℕ, (l ^ a * c).choose (l ^ a) ≡ c [MOD l] := by
  haveI := Fact.mk hl
  intro a
  induction a with
  | zero => simp [Nat.ModEq]
  | succ a ih =>
    have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := l * (l ^ a * c))
      (k := l * l ^ a) (p := l)
    rw [Nat.mul_mod_right, Nat.mul_mod_right, Nat.mul_div_cancel_left _ hl.pos,
      Nat.mul_div_cancel_left _ hl.pos, Nat.choose_self, one_mul] at h
    rw [pow_succ', mul_assoc]
    exact h.trans ih

/- English proof (translation)
Take `⟨v, c, hc, hm'⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hm0 l hl.ne_one`. Establish `hc1 : c ≠ 1`. Introduce and unpack `rfl`. Conclude with `hm v (by rw [hm', mul_one])`. Establish `hc0 : c ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hm0 (by rw [hm', mul_zero])`. Establish `hp` using `pow_pos hl.pos v`. Use `⟨l ^ v, hp, ?_, ?_⟩` and prove the remaining obligations. Establish `h2 : 2 ≤ c` using `by omega`.

Rewrite using `[hm']`. Use the polynomial consequences of the given equalities and inequalities. Introduce `hd`. Establish `h` using `bnx_choose_lucas hl c v`. Rewrite `h` using `[← hm']`.

Conclude with `hc (Nat.modEq_zero_iff_dvd.1 (h.symm.trans (Nat.modEq_zero_iff_dvd.2 hd)))`.
-/
theorem bnx_choose_nonpow {l : ℕ} (hl : l.Prime) (m : ℕ) (hm0 : m ≠ 0) (hm : ∀ e, m ≠ l ^ e) :
    ∃ j, 0 < j ∧ j < m ∧ ¬ l ∣ m.choose j := by
  obtain ⟨v, c, hc, hm'⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 l hl.ne_one
  have hc1 : c ≠ 1 := by
    rintro rfl
    exact hm v (by rw [hm', mul_one])
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hm0 (by rw [hm', mul_zero])
  have hp := pow_pos hl.pos v
  refine ⟨l ^ v, hp, ?_, ?_⟩
  · have h2 : 2 ≤ c := by omega
    rw [hm']
    nlinarith
  · intro hd
    have h := bnx_choose_lucas hl c v
    rw [← hm'] at h
    exact hc (Nat.modEq_zero_iff_dvd.1 (h.symm.trans (Nat.modEq_zero_iff_dvd.2 hd)))

/- English proof (translation)
Establish `hlp` using `hl.pos`. Establish `hk0 : 0 < l ^ (e - 1)` using `pow_pos hlp _`. Establish `hN : l ^ e = l * l ^ (e - 1)`. Rewrite using `[← pow_succ']`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers. Establish `hlt : l ^ (e - 1) < l ^ e`. Rewrite using `[hN]`. Use `hl.two_le` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Use `⟨hk0, hlt, (Nat.choose_pos hlt.le).ne', ?_⟩` and prove the remaining obligations. Establish `hnd : ∀ f i, i ≤ l ^ f - 1 → ¬ l ∣ (l ^ f - 1).choose i` using `by haveI := Fact.mk hl`. Introduce `f`. Proceed by induction on `f with`. Consider the case `zero`.

Introduce `i hi`. Establish `hi0 : i = 0`. Rewrite `hi` using `[pow_zero]`. Use linear arithmetic over natural numbers and integers. Substitute `hi0` using the available equality.

Rewrite using `[Nat.choose_zero_right]`. Conclude with `hl.not_dvd_one`. Consider the case `succ f ih`. Introduce `i hi hd`. Establish `hA : 1 ≤ l ^ f` using `Nat.one_le_pow _ _ hlp`.

Establish `hsplit : l ^ (f + 1) - 1 = (l - 1) + l * (l ^ f - 1)`. Rewrite using `[pow_succ']`. Establish `h4 : l * l ^ f = l * (l ^ f - 1) + l`. Rewrite using `[Nat.mul_sub_one]`. Establish `: l ≤ l * l ^ f` using `by nlinarith`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[h4]`. Use linear arithmetic over natural numbers and integers. Establish `hm1 : (l ^ (f + 1) - 1) % l = l - 1`. Rewrite using `[hsplit, Nat.add_mul_mod_self_left]`.

Conclude with `Nat.mod_eq_of_lt (by omega)`. Establish `hd1 : (l ^ (f + 1) - 1) / l = l ^ f - 1`. Rewrite using `[hsplit, Nat.add_mul_div_left _ _ hlp, Nat.div_eq_of_lt (by omega), zero_add]`. Establish `h` using `Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := l ^ (f + 1) - 1) (k := i) (p := l)`. Rewrite `h` using `[hm1, hd1]`.

Establish `h2 : l ∣ (l - 1).choose (i % l) * (l ^ f - 1).choose (i / l)` using `Nat.modEq_zero_iff_dvd.1 (h.symm.trans (Nat.modEq_zero_iff_dvd.2 hd))`. Break down `(Nat.Prime.dvd_mul hl).1 h2 with h3 | h3` into its components or cases. Establish `hi' : i % l ≤ l - 1`. Use `Nat.mod_lt i hlp` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `h4` using `Nat.choose_mul_factorial_mul_factorial hi'`. Establish `h5 : l ∣ (l - 1).factorial`. Rewrite using `[← h4]`. Conclude with `Dvd.dvd.mul_right (Dvd.dvd.mul_right h3 _) _`. Rewrite `h5` using `[hl.dvd_factorial]`.

Use linear arithmetic over natural numbers and integers. Use `ih (i / l) ?_ h3` and prove the remaining obligations. Establish `h6 : i / l ≤ (l ^ (f + 1) - 1) / l` using `Nat.div_le_div_right hi`. Rewrite `h6` using `[hd1]`. Conclude with `h6`.

Introduce `hdiv`. Establish `hid : (l ^ e - 1 + 1) * (l ^ e - 1).choose (l ^ (e - 1) - 1) = (l ^ e - 1 + 1).choose (l ^ (e - 1) - 1 + 1) * (l ^ (e - 1) - 1 + 1)` using `by first`. Consider the case `exact Nat.add_one_mul_choose_eq _ _`. Consider the case `exact Nat.succ_mul_choose_eq' _ _`. Consider the case `exact (Nat.choose_mul_succ_eq _ _).symm`.

Establish `e1 : l ^ e - 1 + 1 = l ^ e` using `by omega`. Establish `e2 : l ^ (e - 1) - 1 + 1 = l ^ (e - 1)` using `by omega`. Rewrite `hid` using `[e1, e2]`. Establish `hC : (l ^ e).choose (l ^ (e - 1)) = l * (l ^ e - 1).choose (l ^ (e - 1) - 1)`. Apply `Nat.eq_of_mul_eq_mul_right hk0` to reduce the goal to its premises.

Rewrite using `[← hid, hN]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hdiv` using `[hC, pow_two]`. Establish `h7 : l ∣ (l ^ e - 1).choose (l ^ (e - 1) - 1)` using `by first`. Consider the case `exact Nat.dvd_of_mul_dvd_mul_left hlp hdiv`.

Consider the case `exact (Nat.mul_dvd_mul_iff_left hlp).1 hdiv`. Conclude with `hnd e _ (by omega) h7`.
-/
theorem bnx_choose_pow {l : ℕ} (hl : l.Prime) (e : ℕ) (he : 1 ≤ e) :
    0 < l ^ (e - 1) ∧ l ^ (e - 1) < l ^ e ∧ (l ^ e).choose (l ^ (e - 1)) ≠ 0 ∧
      ¬ l ^ 2 ∣ (l ^ e).choose (l ^ (e - 1)) := by
  have hlp := hl.pos
  have hk0 : 0 < l ^ (e - 1) := pow_pos hlp _
  have hN : l ^ e = l * l ^ (e - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hlt : l ^ (e - 1) < l ^ e := by
    rw [hN]
    have := hl.two_le
    nlinarith
  refine ⟨hk0, hlt, (Nat.choose_pos hlt.le).ne', ?_⟩
  have hnd : ∀ f i, i ≤ l ^ f - 1 → ¬ l ∣ (l ^ f - 1).choose i := by
    haveI := Fact.mk hl
    intro f
    induction f with
    | zero =>
      intro i hi
      have hi0 : i = 0 := by
        rw [pow_zero] at hi
        omega
      subst hi0
      rw [Nat.choose_zero_right]
      exact hl.not_dvd_one
    | succ f ih =>
      intro i hi hd
      have hA : 1 ≤ l ^ f := Nat.one_le_pow _ _ hlp
      have hsplit : l ^ (f + 1) - 1 = (l - 1) + l * (l ^ f - 1) := by
        rw [pow_succ']
        have h4 : l * l ^ f = l * (l ^ f - 1) + l := by
          rw [Nat.mul_sub_one]
          have : l ≤ l * l ^ f := by nlinarith
          omega
        rw [h4]
        omega
      have hm1 : (l ^ (f + 1) - 1) % l = l - 1 := by
        rw [hsplit, Nat.add_mul_mod_self_left]
        exact Nat.mod_eq_of_lt (by omega)
      have hd1 : (l ^ (f + 1) - 1) / l = l ^ f - 1 := by
        rw [hsplit, Nat.add_mul_div_left _ _ hlp, Nat.div_eq_of_lt (by omega), zero_add]
      have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := l ^ (f + 1) - 1) (k := i) (p := l)
      rw [hm1, hd1] at h
      have h2 : l ∣ (l - 1).choose (i % l) * (l ^ f - 1).choose (i / l) :=
        Nat.modEq_zero_iff_dvd.1 (h.symm.trans (Nat.modEq_zero_iff_dvd.2 hd))
      rcases (Nat.Prime.dvd_mul hl).1 h2 with h3 | h3
      · have hi' : i % l ≤ l - 1 := by
          have := Nat.mod_lt i hlp
          omega
        have h4 := Nat.choose_mul_factorial_mul_factorial hi'
        have h5 : l ∣ (l - 1).factorial := by
          rw [← h4]
          exact Dvd.dvd.mul_right (Dvd.dvd.mul_right h3 _) _
        rw [hl.dvd_factorial] at h5
        omega
      · refine ih (i / l) ?_ h3
        have h6 : i / l ≤ (l ^ (f + 1) - 1) / l := Nat.div_le_div_right hi
        rw [hd1] at h6
        exact h6
  intro hdiv
  have hid : (l ^ e - 1 + 1) * (l ^ e - 1).choose (l ^ (e - 1) - 1) =
      (l ^ e - 1 + 1).choose (l ^ (e - 1) - 1 + 1) * (l ^ (e - 1) - 1 + 1) := by
    first
    | exact Nat.add_one_mul_choose_eq _ _
    | exact Nat.succ_mul_choose_eq' _ _
    | exact (Nat.choose_mul_succ_eq _ _).symm
  have e1 : l ^ e - 1 + 1 = l ^ e := by omega
  have e2 : l ^ (e - 1) - 1 + 1 = l ^ (e - 1) := by omega
  rw [e1, e2] at hid
  have hC : (l ^ e).choose (l ^ (e - 1)) = l * (l ^ e - 1).choose (l ^ (e - 1) - 1) := by
    apply Nat.eq_of_mul_eq_mul_right hk0
    rw [← hid, hN]
    ring
  rw [hC, pow_two] at hdiv
  have h7 : l ∣ (l ^ e - 1).choose (l ^ (e - 1) - 1) := by
    first
    | exact Nat.dvd_of_mul_dvd_mul_left hlp hdiv
    | exact (Nat.mul_dvd_mul_iff_left hlp).1 hdiv
  exact hnd e _ (by omega) h7

/- English proof (translation)
Establish `h1 : l ^ d ≡ 1 [MOD l ^ d - 1]`. Establish `: 1 ≤ l ^ d` using `Nat.one_le_pow _ _ (by omega)`. Conclude with `((Nat.modEq_iff_dvd' this).2 dvd_rfl).symm`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← pow_mul, ← pow_add, Nat.div_add_mod]`.

Use `_ ≡ 1 ^ (x / d) * l ^ (x % d) [MOD l ^ d - 1] := (h1.pow _).mul_right _`. Use `_ = l ^ (x % d) := by rw [one_pow, one_mul]`.
-/
theorem bnx_pow_reduce (l d x : ℕ) (hl : 1 ≤ l) : l ^ x ≡ l ^ (x % d) [MOD l ^ d - 1] := by
  have h1 : l ^ d ≡ 1 [MOD l ^ d - 1] := by
    have : 1 ≤ l ^ d := Nat.one_le_pow _ _ (by omega)
    exact ((Nat.modEq_iff_dvd' this).2 dvd_rfl).symm
  calc l ^ x = (l ^ d) ^ (x / d) * l ^ (x % d) := by
        rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    _ ≡ 1 ^ (x / d) * l ^ (x % d) [MOD l ^ d - 1] := (h1.pow _).mul_right _
    _ = l ^ (x % d) := by rw [one_pow, one_mul]

/- English proof (translation)
Establish `hx` using `bnx_pow_reduce l d x (by omega)`. Establish `hy` using `bnx_pow_reduce l d y (by omega)`. Establish `h' : l ^ (x % d) ≡ l ^ (y % d) [MOD l ^ d - 1]` using `hx.symm.trans (h.trans hy)`. Establish `hxd : x % d < d` using `Nat.mod_lt _ (by omega)`. Establish `hyd : y % d < d` using `Nat.mod_lt _ (by omega)`.

Establish `hlt : ∀ k, k < d → l ^ k < l ^ d - 1`. Introduce `k hk`. Establish `h1 : l ^ k ≤ l ^ (d - 1)` using `Nat.pow_le_pow_right (by omega) (by omega)`. Establish `h2 : l ^ d = l * l ^ (d - 1)`. Rewrite using `[← pow_succ']`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `h3 : 1 ≤ l ^ (d - 1)` using `Nat.one_le_pow _ _ (by omega)`. Establish `h4 : 3 * l ^ (d - 1) ≤ l * l ^ (d - 1)` using `Nat.mul_le_mul_right _ hl`. Rewrite using `[h2]`.

Generalize the expression as in `l * l ^ (d - 1) = P at h4 ⊢`. Generalize the expression as in `l ^ (d - 1) = L at h1 h3 h4`. Generalize the expression as in `l ^ k = A at h1 ⊢`. Use linear arithmetic over natural numbers and integers. Establish `heq : l ^ (x % d) = l ^ (y % d)`.

Establish `h5` using `h'`. Unfold `Nat.ModEq at h5`. Rewrite `h5` using `[Nat.mod_eq_of_lt (hlt _ hxd), Nat.mod_eq_of_lt (hlt _ hyd)]`. Then use the resulting hypothesis. Conclude with `Nat.pow_right_injective (by omega : 2 ≤ l) heq`.
-/
theorem bnx_pow_mod (l d x y : ℕ) (hl : 3 ≤ l) (hd : 1 ≤ d)
    (h : l ^ x ≡ l ^ y [MOD l ^ d - 1]) : x % d = y % d := by
  have hx := bnx_pow_reduce l d x (by omega)
  have hy := bnx_pow_reduce l d y (by omega)
  have h' : l ^ (x % d) ≡ l ^ (y % d) [MOD l ^ d - 1] := hx.symm.trans (h.trans hy)
  have hxd : x % d < d := Nat.mod_lt _ (by omega)
  have hyd : y % d < d := Nat.mod_lt _ (by omega)
  have hlt : ∀ k, k < d → l ^ k < l ^ d - 1 := by
    intro k hk
    have h1 : l ^ k ≤ l ^ (d - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : l ^ d = l * l ^ (d - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have h3 : 1 ≤ l ^ (d - 1) := Nat.one_le_pow _ _ (by omega)
    have h4 : 3 * l ^ (d - 1) ≤ l * l ^ (d - 1) := Nat.mul_le_mul_right _ hl
    rw [h2]
    generalize l * l ^ (d - 1) = P at h4 ⊢
    generalize l ^ (d - 1) = L at h1 h3 h4
    generalize l ^ k = A at h1 ⊢
    omega
  have heq : l ^ (x % d) = l ^ (y % d) := by
    have h5 := h'
    unfold Nat.ModEq at h5
    rwa [Nat.mod_eq_of_lt (hlt _ hxd), Nat.mod_eq_of_lt (hlt _ hyd)] at h5
  exact Nat.pow_right_injective (by omega : 2 ≤ l) heq

/- English proof (translation)
Rewrite using `[Finsupp.prod_fintype _ _ (fun t => pow_zero _)]`. Simplify using `only [torus, mul_pow, ← map_pow, Finset.prod_mul_distrib, map_prod]`. Use `congr 1`. Establish `hmono : ∀ S : Finset (ZMod d), ∏ t ∈ S, (X t ^ dd t : MvPowerSeries (ZMod d) K) = monomial (∑ t ∈ S, Finsupp.single t (dd t)) 1`. Introduce `S`.

Use `Finset.induction_on S ?_ ?_` and prove the remaining obligations. Simplify using `[monomial_zero_eq_C_apply]`. Introduce `a S ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, ih, X_pow_eq, monomial_mul_monomial, one_mul]`. Rewrite using `[hmono]`.

Rewrite using `[show ∑ t, Finsupp.single t (dd t) = dd from by`. Use extensionality with `u`. Simplify using `[Finsupp.finset_sum_apply, Finsupp.single_apply]]`.
-/
private theorem finsupp_prod_torus_pow_eq_C_mul_monomial {K : Type u} [Field K] {d : ℕ} [NeZero d] (l : ℕ) (ζ : K)
    (dd : ZMod d →₀ ℕ) :
    (dd.prod fun t e => (torus l ζ t : MvPowerSeries (ZMod d) K) ^ e) =
      C (∏ t, (ζ ^ lw l t) ^ dd t) * monomial dd 1 := by
  rw [Finsupp.prod_fintype _ _ (fun t => pow_zero _)]
  simp only [torus, mul_pow, ← map_pow, Finset.prod_mul_distrib, map_prod]
  congr 1
  have hmono : ∀ S : Finset (ZMod d), ∏ t ∈ S, (X t ^ dd t : MvPowerSeries (ZMod d) K) =
      monomial (∑ t ∈ S, Finsupp.single t (dd t)) 1 := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · simp [monomial_zero_eq_C_apply]
    · intro a S ha ih
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, X_pow_eq, monomial_mul_monomial, one_mul]
  rw [hmono]
  rw [show ∑ t, Finsupp.single t (dd t) = dd from by
    ext u
    simp [Finsupp.finset_sum_apply, Finsupp.single_apply]]

/- English proof (translation)
Establish `hk0 : 0 < l ^ d - 1`. Establish `: l ≤ l ^ d` using `Nat.le_self_pow (by omega) l`. Use linear arithmetic over natural numbers and integers. Establish `hss : s ≠ s'`. Introduce and unpack `rfl`.

Conclude with `hs' hs`. Establish `ha : HasSubst (torus l ζ : ZMod d → MvPowerSeries (ZMod d) K)` using `hasSubst_of_constantCoeff_zero fun t => by simp [torus]`. Establish `hcoef` using `congrArg (coeff (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β))) htor`. Rewrite `hcoef` using `[coeff_subst ha, finsum_eq_single _ (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β))]`. Use `swap`.

Introduce `dd hdd`. Rewrite using `[finsupp_prod_torus_pow_eq_C_mul_monomial, coeff_C_mul, coeff_monomial, if_neg (Ne.symm hdd), mul_zero, smul_zero]`. Rewrite `hcoef` using `[finsupp_prod_torus_pow_eq_C_mul_monomial, coeff_C_mul, coeff_monomial, if_pos rfl, mul_one, smul_eq_mul]`. Establish `hprod` using `mul_left_cancel₀ hc (hcoef.trans (mul_one _).symm)`. Rewrite `hprod` using `[Finset.prod_eq_mul s s' hss (fun t _ ht => by simp [Finsupp.single_apply, Ne.symm ht.1, Ne.symm ht.2]) (fun h => absurd (Finset.mem_univ s) h) (fun h => absurd (Finset.mem_univ s') h)]`.

Establish `hv1 : (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β)) s = l ^ α`. Simplify using `[Finsupp.single_apply, Ne.symm hss]`. Establish `hv2 : (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β)) s' = l ^ β`. Simplify using `[Finsupp.single_apply, hss]`. Rewrite `hprod` using `[hv1, hv2]`.

Establish `hζ0 : ζ ≠ 0` using `hζ.ne_zero hk0.ne'`. Rewrite `hprod` using `[← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hζ0, hζ.zpow_eq_one_iff_dvd]`. Unfold `lw at hprod`. Rewrite `hprod` using `[if_pos hs, if_neg hs']`. Establish `hmod : l ^ (s.val + α) ≡ l ^ (s'.val + β) [MOD l ^ d - 1]`.

Rewrite using `[Nat.modEq_iff_dvd]`. Establish `e : ((l ^ (s'.val + β) : ℕ) : ℤ) - ((l ^ (s.val + α) : ℕ) : ℤ) = -((1 : ℤ) * (l : ℤ) ^ s.val * ((l ^ α : ℕ) : ℤ) + (-1) * (l : ℤ) ^ s'.val * ((l ^ β : ℕ) : ℤ))`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Use `first`. Consider the case `exact dvd_neg.2 hprod`. Consider the case `exact dvd_neg.2 (by exact_mod_cast hprod)`. Establish `key` using `bnx_pow_mod l d _ _ hl3 (by omega) hmod`. Establish `h2` using `congrArg (fun x : ℕ => (x : ZMod d)) key`.

Use `first`. Consider the case `(simp only [ZMod.natCast_mod, Nat.cast_add, ZMod.natCast_zmod_val] at h2; exact h2)`. Consider the case `(simp at h2; exact h2)`.
-/
theorem bnx_torus_cong {K : Type u} [Field K] (l d : ℕ) [NeZero d] (hl : l.Prime) (hl3 : 3 ≤ l)
    (hd2 : 2 ≤ d) (hde : Even d) (ζ : K) (hζ : IsPrimitiveRoot ζ (l ^ d - 1))
    (be : MvPowerSeries (ZMod d) K) (htor : subst (torus l ζ) be = be)
    (s s' : ZMod d) (hs : s.val % 2 = 0) (hs' : s'.val % 2 ≠ 0) (α β : ℕ)
    (hc : coeff (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β)) be ≠ 0) :
    s + (α : ZMod d) = s' + (β : ZMod d) := by
  have hk0 : 0 < l ^ d - 1 := by
    have : l ≤ l ^ d := Nat.le_self_pow (by omega) l
    omega
  have hss : s ≠ s' := by
    rintro rfl
    exact hs' hs
  have ha : HasSubst (torus l ζ : ZMod d → MvPowerSeries (ZMod d) K) :=
    hasSubst_of_constantCoeff_zero fun t => by simp [torus]
  have hcoef := congrArg (coeff (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β))) htor
  rw [coeff_subst ha, finsum_eq_single _ (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β))] at hcoef
  swap
  · intro dd hdd
    rw [finsupp_prod_torus_pow_eq_C_mul_monomial, coeff_C_mul, coeff_monomial, if_neg (Ne.symm hdd), mul_zero, smul_zero]
  rw [finsupp_prod_torus_pow_eq_C_mul_monomial, coeff_C_mul, coeff_monomial, if_pos rfl, mul_one, smul_eq_mul] at hcoef
  have hprod := mul_left_cancel₀ hc (hcoef.trans (mul_one _).symm)
  rw [Finset.prod_eq_mul s s' hss
    (fun t _ ht => by simp [Finsupp.single_apply, Ne.symm ht.1, Ne.symm ht.2])
    (fun h => absurd (Finset.mem_univ s) h) (fun h => absurd (Finset.mem_univ s') h)] at hprod
  have hv1 : (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β)) s = l ^ α := by
    simp [Finsupp.single_apply, Ne.symm hss]
  have hv2 : (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β)) s' = l ^ β := by
    simp [Finsupp.single_apply, hss]
  rw [hv1, hv2] at hprod
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hk0.ne'
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hζ0,
    hζ.zpow_eq_one_iff_dvd] at hprod
  unfold lw at hprod
  rw [if_pos hs, if_neg hs'] at hprod
  have hmod : l ^ (s.val + α) ≡ l ^ (s'.val + β) [MOD l ^ d - 1] := by
    rw [Nat.modEq_iff_dvd]
    have e : ((l ^ (s'.val + β) : ℕ) : ℤ) - ((l ^ (s.val + α) : ℕ) : ℤ) =
        -((1 : ℤ) * (l : ℤ) ^ s.val * ((l ^ α : ℕ) : ℤ) +
          (-1) * (l : ℤ) ^ s'.val * ((l ^ β : ℕ) : ℤ)) := by
      push_cast
      ring
    rw [e]
    first
    | exact dvd_neg.2 hprod
    | exact dvd_neg.2 (by exact_mod_cast hprod)
  have key := bnx_pow_mod l d _ _ hl3 (by omega) hmod
  have h2 := congrArg (fun x : ℕ => (x : ZMod d)) key
  first
  | (simp only [ZMod.natCast_mod, Nat.cast_add, ZMod.natCast_zmod_val] at h2; exact h2)
  | (simp at h2; exact h2)

/- English proof (translation)
Unfold `dot`. Rewrite using `[Finsupp.sum, ← Finset.sum_mul]`. Use `congr 1`. Use `first`. Consider the case `simp [Finsupp.degree_apply]`.

Consider the case `simp [Finsupp.degree, Finsupp.sum]`. Consider the case `(rw [Finsupp.degree_apply]; push_cast; rfl)`.
-/
theorem bnx_dot_const {ι : Type*} (n : ι →₀ ℕ) (c : ℝ) :
    dot n (fun _ => c) = (n.degree : ℝ) * c := by
  unfold dot
  rw [Finsupp.sum, ← Finset.sum_mul]
  congr 1
  first
  | simp [Finsupp.degree_apply]
  | simp [Finsupp.degree, Finsupp.sum]
  | (rw [Finsupp.degree_apply]; push_cast; rfl)

section Sides

variable {K : Type u} [NormedField K] {d : ℕ} [NeZero d]

/- English proof (translation)
Establish `h` using `h1 (bnxM n (Function.update (⇑n) s j))`. Unfold `MonoWtGe at h`. Rewrite `h` using `[evenDerivative_binomial_coeff be n s hs j hj hpos, norm_mul, bnx_dot_const, bnx_degree_bnxM n _ (bnx_update_le n s j hj), ← bnx_dot_const]`. Conclude with `h`.
-/
theorem bnx_sideE (be : MvPowerSeries (ZMod d) K) (pi r w : ℝ) (h1 : WtGe pi (fun _ => r) w (de1 be))
    (n : ZMod d →₀ ℕ) (s : ZMod d) (hs : s.val % 2 = 0) (j : ℕ) (hj : j < n s)
    (hpos : 0 < j ∨ ∃ t : ZMod d, t.val % 2 = 0 ∧ t ≠ s ∧ n t ≠ 0) :
    ‖coeff n be‖ * ‖((n s).choose j : K)‖ ≤ pi ^ (w - dot n (fun _ => r)) := by
  have h := h1 (bnxM n (Function.update (⇑n) s j))
  unfold MonoWtGe at h
  rw [evenDerivative_binomial_coeff be n s hs j hj hpos, norm_mul, bnx_dot_const,
    bnx_degree_bnxM n _ (bnx_update_le n s j hj), ← bnx_dot_const] at h
  exact h

/- English proof (translation)
Establish `h` using `h2 (bnxM n (Function.update (⇑n) s j))`. Unfold `MonoWtGe at h`. Rewrite `h` using `[oddDerivative_binomial_coeff be n s hs j hj hpos, norm_mul, bnx_dot_const, bnx_degree_bnxM n _ (bnx_update_le n s j hj), ← bnx_dot_const]`. Conclude with `h`.
-/
theorem bnx_sideO (be : MvPowerSeries (ZMod d) K) (pi r w : ℝ) (h2 : WtGe pi (fun _ => r) w (de2 be))
    (n : ZMod d →₀ ℕ) (s : ZMod d) (hs : s.val % 2 ≠ 0) (j : ℕ) (hj : j < n s)
    (hpos : 0 < j ∨ ∃ t : ZMod d, t.val % 2 ≠ 0 ∧ t ≠ s ∧ n t ≠ 0) :
    ‖coeff n be‖ * ‖((n s).choose j : K)‖ ≤ pi ^ (w - dot n (fun _ => r)) := by
  have h := h2 (bnxM n (Function.update (⇑n) s j))
  unfold MonoWtGe at h
  rw [oddDerivative_binomial_coeff be n s hs j hj hpos, norm_mul, bnx_dot_const,
    bnx_degree_bnxM n _ (bnx_update_le n s j hj), ← bnx_dot_const] at h
  exact h

end Sides

/- English proof (translation)
Establish `hp : 0 < pi ^ v` using `Real.rpow_pos_of_pos h0 v`. Rewrite using `[le_div_iff₀ hp]`. Conclude with `(mul_le_mul_of_nonneg_left hb ha).trans h`.
-/
theorem bnx_div {pi a b X v : ℝ} (h0 : 0 < pi) (hb : pi ^ v ≤ b) (ha : 0 ≤ a) (h : a * b ≤ X) :
    a ≤ X / pi ^ v := by
  have hp : 0 < pi ^ v := Real.rpow_pos_of_pos h0 v
  rw [le_div_iff₀ hp]
  exact (mul_le_mul_of_nonneg_left hb ha).trans h

/- English proof (translation)
Take `⟨s, hs, hns⟩` from `h`. Distinguish the cases in `hex : ∃ t, P t ∧ t ≠ s ∧ n t ≠ 0`. Use `left`. Use `⟨s, 0, hs, Nat.pos_of_ne_zero hns, Or.inr hex, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.choose_zero_right]`.

Conclude with `hl.not_dvd_one`. Use `push_neg at hex`. Distinguish the cases in `hpow : ∃ e, n s = l ^ e`. Use `right`. Take `⟨e, he⟩` from `hpow`.

Conclude with `⟨s, e, hs, fun t ht hts => hex t ht hts, he⟩`. Use `left push_neg at hpow`. Take `⟨j, hj0, hjn, hjd⟩` from `bnx_choose_nonpow hl (n s) hns hpow`. Conclude with `⟨s, j, hs, hjn, Or.inl hj0, hjd⟩`.
-/
theorem bnx_side_cases {d : ℕ} {l : ℕ} (hl : l.Prime) (P : ZMod d → Prop) (n : ZMod d →₀ ℕ)
    (h : ∃ s, P s ∧ n s ≠ 0) :
    (∃ s j, P s ∧ j < n s ∧ (0 < j ∨ ∃ t, P t ∧ t ≠ s ∧ n t ≠ 0) ∧ ¬ l ∣ (n s).choose j) ∨
    (∃ s e, P s ∧ (∀ t, P t → t ≠ s → n t = 0) ∧ n s = l ^ e) := by
  obtain ⟨s, hs, hns⟩ := h
  by_cases hex : ∃ t, P t ∧ t ≠ s ∧ n t ≠ 0
  · left
    refine ⟨s, 0, hs, Nat.pos_of_ne_zero hns, Or.inr hex, ?_⟩
    rw [Nat.choose_zero_right]
    exact hl.not_dvd_one
  · push_neg at hex
    by_cases hpow : ∃ e, n s = l ^ e
    · right
      obtain ⟨e, he⟩ := hpow
      exact ⟨s, e, hs, fun t ht hts => hex t ht hts, he⟩
    · left
      push_neg at hpow
      obtain ⟨j, hj0, hjn, hjd⟩ := bnx_choose_nonpow hl (n s) hns hpow
      exact ⟨s, j, hs, hjn, Or.inl hj0, hjd⟩

/- English proof (translation)
Unfold `degE`. Rewrite using `[Finset.sum_eq_single s]`. Rewrite using `[if_pos hs]`. Introduce `t _ hts split_ifs with ht`. Conclude with `hu t ht hts`.

Both sides reduce to the same expression. Introduce `h`. Conclude with `absurd (Finset.mem_univ s) h`.
-/
theorem bnx_degE_eq {d : ℕ} [NeZero d] (n : ZMod d →₀ ℕ) (s : ZMod d) (hs : s.val % 2 = 0)
    (hu : ∀ t : ZMod d, t.val % 2 = 0 → t ≠ s → n t = 0) : degE n = n s := by
  unfold degE
  rw [Finset.sum_eq_single s]
  · rw [if_pos hs]
  · intro t _ hts
    split_ifs with ht
    · exact hu t ht hts
    · rfl
  · intro h
    exact absurd (Finset.mem_univ s) h

/- English proof (translation)
Unfold `degO`. Rewrite using `[Finset.sum_eq_single s]`. Rewrite using `[if_neg hs]`. Introduce `t _ hts split_ifs with ht`. Both sides reduce to the same expression.

Conclude with `hu t ht hts`. Introduce `h`. Conclude with `absurd (Finset.mem_univ s) h`.
-/
theorem bnx_degO_eq {d : ℕ} [NeZero d] (n : ZMod d →₀ ℕ) (s : ZMod d) (hs : s.val % 2 ≠ 0)
    (hu : ∀ t : ZMod d, t.val % 2 ≠ 0 → t ≠ s → n t = 0) : degO n = n s := by
  unfold degO
  rw [Finset.sum_eq_single s]
  · rw [if_neg hs]
  · intro t _ hts
    split_ifs with ht
    · rfl
    · exact hu t ht hts
  · intro h
    exact absurd (Finset.mem_univ s) h

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `h0 : degE n = 0`. Unfold `degE`. Use `Finset.sum_eq_zero fun s _ => ?_` and prove the remaining obligations.

Use `split_ifs with hs`. Conclude with `hne s hs`. Both sides reduce to the same expression. Use linear arithmetic over natural numbers and integers.
-/
theorem bnx_exE {d : ℕ} [NeZero d] (n : ZMod d →₀ ℕ) (h : 0 < degE n) :
    ∃ s : ZMod d, s.val % 2 = 0 ∧ n s ≠ 0 := by
  by_contra hne
  push_neg at hne
  have h0 : degE n = 0 := by
    unfold degE
    refine Finset.sum_eq_zero fun s _ => ?_
    split_ifs with hs
    · exact hne s hs
    · rfl
  omega

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `h0 : degO n = 0`. Unfold `degO`. Use `Finset.sum_eq_zero fun s _ => ?_` and prove the remaining obligations.

Use `split_ifs with hs`. Both sides reduce to the same expression. Conclude with `hne s hs`. Use linear arithmetic over natural numbers and integers.
-/
theorem bnx_exO {d : ℕ} [NeZero d] (n : ZMod d →₀ ℕ) (h : 0 < degO n) :
    ∃ s : ZMod d, s.val % 2 ≠ 0 ∧ n s ≠ 0 := by
  by_contra hne
  push_neg at hne
  have h0 : degO n = 0 := by
    unfold degO
    refine Finset.sum_eq_zero fun s _ => ?_
    split_ifs with hs
    · rfl
    · exact hne s hs
  omega

/- English proof (translation)
Establish `hpi0 : 0 < ‖(l : K)‖` using `norm_pos_iff.2 (Nat.cast_ne_zero.2 hl.ne_zero)`. Take `⟨hE, hO, hEO⟩` from `hlow n hn`. Establish `hc0` using `norm_nonneg (coeff n be)`. Unfold `MonoWtGe`. Break down `bnx_side_cases hl (fun s : ZMod d => s.val % 2 = 0) n (bnx_exE n hE) with ⟨s, j, hs, hj, hpos, hnd⟩ | ⟨s, α, hs, hu, hα⟩` into its components or cases.

Use `left`. Establish `hb` using `bnx_sideE be _ _ _ h1 n s hs j hj hpos`. Establish `hC` using `bnx_norm_one hl hl1 _ hnd`. Use the polynomial consequences of the given equalities and inequalities. Break down `bnx_side_cases hl (fun s : ZMod d => s.val % 2 ≠ 0) n (bnx_exO n hO) with ⟨s', j, hs', hj, hpos, hnd⟩ | ⟨s', β, hs', hu', hβ⟩` into its components or cases.

Use `left`. Establish `hb` using `bnx_sideO be _ _ _ h2 n s' hs' j hj hpos`. Establish `hC` using `bnx_norm_one hl hl1 _ hnd`. Use the polynomial consequences of the given equalities and inequalities. Establish `hss : s ≠ s'`.

Introduce and unpack `rfl`. Conclude with `hs' hs`. Establish `hneq : n = Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β)`. Use extensionality with `t`. Simplify using `only [Finsupp.add_apply, Finsupp.single_apply]`.

Distinguish the cases in `ht : t.val % 2 = 0`. Distinguish the cases in `hts : t = s`. Substitute `hts` using the available equality. Simplify using `[hss, Ne.symm hss, hα]`. Establish `h0` using `hu t ht hts`.

Establish `hts' : t ≠ s'`. Introduce and unpack `rfl`. Conclude with `hs' ht`. Simplify using `[Ne.symm hts, Ne.symm hts', h0]`. Distinguish the cases in `hts : t = s'`.

Substitute `hts` using the available equality. Simplify using `[hss, Ne.symm hss, hβ]`. Establish `h0` using `hu' t ht hts`. Establish `hts2 : t ≠ s`. Introduce and unpack `rfl`.

Conclude with `ht hs`. Simplify using `[Ne.symm hts, Ne.symm hts2, h0]`. Establish `hαβ : α ≠ 0 ∨ β ≠ 0`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Take `⟨rfl, rfl⟩` from `hc`. Apply `hEO` to reduce the goal to its premises. Rewrite using `[bnx_degE_eq n s hs hu, bnx_degO_eq n s' hs' hu', hα, hβ]`. Simplify using the standard rewrite rules. Establish `hc' : coeff (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β)) be ≠ 0`.

Rewrite using `[← hneq]`. Conclude with `hn`. Establish `hcong` using `bnx_torus_cong l d hl hl3 hd2 hde ζ hζ be htor s s' hs hs' α β hc'`. Establish `hbi : IsBiPower l n`. Unfold `IsBiPower`.

Conclude with `⟨s, s', α, β, hs, Nat.mod_two_ne_zero.1 hs', hαβ, hcong, hneq⟩`. Use `right`. Use `⟨hbi, ?_⟩` and prove the remaining obligations. Break down `hαβ with hα0 | hβ0` into its components or cases. Take `⟨hj0, hjlt, hCne, hC2⟩` from `bnx_choose_pow hl α (Nat.one_le_iff_ne_zero.2 hα0)`.

Establish `hb` using `bnx_sideE be _ _ _ h1 n s hs (l ^ (α - 1)) (by rw [hα]; exact hjlt) (Or.inl hj0)`. Rewrite `hb` using `[hα]`. Establish `hC` using `bnx_norm_ge hl hl1 _ hCne hC2`. Establish `hb'` using `le_trans (mul_le_mul_of_nonneg_left hC hc0) hb`. Establish `h3` using `bnx_div (v := 1) hpi0 (le_of_eq (Real.rpow_one _)) hc0 hb'`.

Rewrite `h3` using `[← Real.rpow_sub hpi0]`. Use `h3 using 2` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Take `⟨hj0, hjlt, hCne, hC2⟩` from `bnx_choose_pow hl β (Nat.one_le_iff_ne_zero.2 hβ0)`. Establish `hb` using `bnx_sideO be _ _ _ h2 n s' hs' (l ^ (β - 1)) (by rw [hβ]; exact hjlt) (Or.inl hj0)`.

Rewrite `hb` using `[hβ]`. Establish `hC` using `bnx_norm_ge hl hl1 _ hCne hC2`. Establish `hb'` using `le_trans (mul_le_mul_of_nonneg_left hC hc0) hb`. Establish `h3` using `bnx_div (v := 1) hpi0 (le_of_eq (Real.rpow_one _)) hc0 hb'`. Rewrite `h3` using `[← Real.rpow_sub hpi0]`.

Use `h3 using 2` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem monoWtGe_or_biPower_of_wtGe_de1_de2 {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]
    {l d : ℕ} [NeZero d] (hl : l.Prime) (hl3 : 3 ≤ l) (hd2 : 2 ≤ d) (hde : Even d)
    (hl1 : ‖(l : K)‖ < 1) (ζ : K) (hζ : IsPrimitiveRoot ζ (l ^ d - 1))
    (be : MvPowerSeries (ZMod d) K) (htor : subst (torus l ζ) be = be) (hlow : NoLowBidegree be)
    (r w : ℝ) (h1 : WtGe ‖(l : K)‖ (fun _ => r) w (de1 be))
    (h2 : WtGe ‖(l : K)‖ (fun _ => r) w (de2 be))
    (n : ZMod d →₀ ℕ) (hn : coeff n be ≠ 0) :
    MonoWtGe ‖(l : K)‖ (fun _ => r) w n (coeff n be) ∨
      (IsBiPower l n ∧ MonoWtGe ‖(l : K)‖ (fun _ => r) (w - 1) n (coeff n be)) := by
  have hpi0 : 0 < ‖(l : K)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hl.ne_zero)
  obtain ⟨hE, hO, hEO⟩ := hlow n hn
  have hc0 := norm_nonneg (coeff n be)
  unfold MonoWtGe
  rcases bnx_side_cases hl (fun s : ZMod d => s.val % 2 = 0) n (bnx_exE n hE) with
    ⟨s, j, hs, hj, hpos, hnd⟩ | ⟨s, α, hs, hu, hα⟩
  · left
    have hb := bnx_sideE be _ _ _ h1 n s hs j hj hpos
    have hC := bnx_norm_one hl hl1 _ hnd
    nlinarith
  rcases bnx_side_cases hl (fun s : ZMod d => s.val % 2 ≠ 0) n (bnx_exO n hO) with
    ⟨s', j, hs', hj, hpos, hnd⟩ | ⟨s', β, hs', hu', hβ⟩
  · left
    have hb := bnx_sideO be _ _ _ h2 n s' hs' j hj hpos
    have hC := bnx_norm_one hl hl1 _ hnd
    nlinarith
  have hss : s ≠ s' := by
    rintro rfl
    exact hs' hs
  have hneq : n = Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β) := by
    ext t
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    by_cases ht : t.val % 2 = 0
    · by_cases hts : t = s
      · subst hts
        simp [hss, Ne.symm hss, hα]
      · have h0 := hu t ht hts
        have hts' : t ≠ s' := by
          rintro rfl
          exact hs' ht
        simp [Ne.symm hts, Ne.symm hts', h0]
    · by_cases hts : t = s'
      · subst hts
        simp [hss, Ne.symm hss, hβ]
      · have h0 := hu' t ht hts
        have hts2 : t ≠ s := by
          rintro rfl
          exact ht hs
        simp [Ne.symm hts, Ne.symm hts2, h0]
  have hαβ : α ≠ 0 ∨ β ≠ 0 := by
    by_contra hc
    push_neg at hc
    obtain ⟨rfl, rfl⟩ := hc
    apply hEO
    rw [bnx_degE_eq n s hs hu, bnx_degO_eq n s' hs' hu', hα, hβ]
    simp
  have hc' : coeff (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β)) be ≠ 0 := by
    rw [← hneq]
    exact hn
  have hcong := bnx_torus_cong l d hl hl3 hd2 hde ζ hζ be htor s s' hs hs' α β hc'
  have hbi : IsBiPower l n := by
    unfold IsBiPower
    exact ⟨s, s', α, β, hs, Nat.mod_two_ne_zero.1 hs', hαβ, hcong, hneq⟩
  right
  refine ⟨hbi, ?_⟩
  rcases hαβ with hα0 | hβ0
  · obtain ⟨hj0, hjlt, hCne, hC2⟩ := bnx_choose_pow hl α (Nat.one_le_iff_ne_zero.2 hα0)
    have hb := bnx_sideE be _ _ _ h1 n s hs (l ^ (α - 1)) (by rw [hα]; exact hjlt) (Or.inl hj0)
    rw [hα] at hb
    have hC := bnx_norm_ge hl hl1 _ hCne hC2
    have hb' := le_trans (mul_le_mul_of_nonneg_left hC hc0) hb
    have h3 := bnx_div (v := 1) hpi0 (le_of_eq (Real.rpow_one _)) hc0 hb'
    rw [← Real.rpow_sub hpi0] at h3
    convert h3 using 2
    ring
  · obtain ⟨hj0, hjlt, hCne, hC2⟩ := bnx_choose_pow hl β (Nat.one_le_iff_ne_zero.2 hβ0)
    have hb := bnx_sideO be _ _ _ h2 n s' hs' (l ^ (β - 1)) (by rw [hβ]; exact hjlt) (Or.inl hj0)
    rw [hβ] at hb
    have hC := bnx_norm_ge hl hl1 _ hCne hC2
    have hb' := le_trans (mul_le_mul_of_nonneg_left hC hc0) hb
    have h3 := bnx_div (v := 1) hpi0 (le_of_eq (Real.rpow_one _)) hc0 hb'
    rw [← Real.rpow_sub hpi0] at h3
    convert h3 using 2
    ring

/- English proof (translation)
Unfold `BinomExtract`. Introduce `K _ _ _ l d _ hl hlo hd2 hde hl1 ζ hζ be htor hlow h1 h2`. Establish `hl3 : 3 ≤ l`. Use `hl.two_le` as an intermediate fact. Take `⟨m, hm⟩` from `hlo`.

Use linear arithmetic over natural numbers and integers. Establish `hpi0 : 0 < ‖(l : K)‖` using `norm_pos_iff.2 (Nat.cast_ne_zero.2 hl.ne_zero)`. Establish `key` using `fun n hn => monoWtGe_or_biPower_of_wtGe_de1_de2 hl hl3 hd2 hde hl1 ζ hζ be htor hlow _ _ h1 h2 n hn`. Prove the components needed by the constructor for the conclusion. Unfold `WtGe`.

Introduce `n`. Distinguish the cases in `hn : coeff n be = 0`. Unfold `MonoWtGe`. Rewrite using `[hn, norm_zero]`. Check the signs of the components of the expression.

Break down `key n hn with h | ⟨_, h⟩` into its components or cases. Unfold `MonoWtGe at h ⊢`. Use `h.trans ?_` and prove the remaining obligations. Use `first`. Consider the case `exact Real.rpow_le_rpow_of_exponent_ge hpi0 hl1.le (by linarith)`.

Consider the case `exact (Real.rpow_le_rpow_left_iff_of_base_lt_one hpi0 hl1).2 (by linarith)`. Conclude with `h`. Introduce `n hnb`. Distinguish the cases in `hn : coeff n be = 0`. Unfold `MonoWtGe`.

Rewrite using `[hn, norm_zero]`. Check the signs of the components of the expression. Break down `key n hn with h | ⟨hb, _⟩` into its components or cases. Conclude with `h`. Conclude with `absurd hb hnb`.
-/
theorem binomial_coefficient_extraction : BinomExtract.{u} := by
  unfold BinomExtract
  intro K _ _ _ l d _ hl hlo hd2 hde hl1 ζ hζ be htor hlow h1 h2
  have hl3 : 3 ≤ l := by
    have := hl.two_le
    obtain ⟨m, hm⟩ := hlo
    omega
  have hpi0 : 0 < ‖(l : K)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hl.ne_zero)
  have key := fun n hn => monoWtGe_or_biPower_of_wtGe_de1_de2 hl hl3 hd2 hde hl1 ζ hζ be htor hlow _ _ h1 h2 n hn
  constructor
  · unfold WtGe
    intro n
    by_cases hn : coeff n be = 0
    · unfold MonoWtGe
      rw [hn, norm_zero]
      positivity
    · rcases key n hn with h | ⟨_, h⟩
      · unfold MonoWtGe at h ⊢
        refine h.trans ?_
        first
        | exact Real.rpow_le_rpow_of_exponent_ge hpi0 hl1.le (by linarith)
        | exact (Real.rpow_le_rpow_left_iff_of_base_lt_one hpi0 hl1).2 (by linarith)
      · exact h
  · intro n hnb
    by_cases hn : coeff n be = 0
    · unfold MonoWtGe
      rw [hn, norm_zero]
      positivity
    · rcases key n hn with h | ⟨hb, _⟩
      · exact h
      · exact absurd hb hnb

end Formalism.DworkPowerSeriesWeights
