import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.SpanNatCastLeComap

noncomputable section

open Ideal
open scoped Nat

namespace Reformulated.AutPerF

section DP

variable {B : Type*} [CommRing B] [Algebra ℚ B]

def dp (m : ℕ) (x : B) : B := ((m ! : ℚ)⁻¹) • x ^ m

/- English proof (translation)
Simplify using `[dp]`.
-/
theorem dp_zero (x : B) : dp 0 x = 1 := by simp [dp]

/- English proof (translation)
Establish `h : ((a + b).choose a : ℚ) * ((a + b)! : ℚ)⁻¹ = (a ! : ℚ)⁻¹ * (b ! : ℚ)⁻¹`. Establish `h1` using `Nat.add_choose_mul_factorial_mul_factorial b a`. Rewrite `h1` using `[add_comm b a]`. Establish `h2 : ((a + b)! : ℚ) = ((a + b).choose a : ℚ) * b ! * a !` using `by exact_mod_cast h1.symm`. Establish `ha : (a ! : ℚ) ≠ 0` using `by positivity`.

Establish `hb : (b ! : ℚ) ≠ 0` using `by positivity`. Establish `hc : ((a + b).choose a : ℚ) ≠ 0`. Conclude with `(Nat.choose_pos (Nat.le_add_right a b)).ne'` after adjusting the coercions. Rewrite using `[h2]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[dp, dp, dp, smul_mul_smul_comm, ← pow_add, ← h, mul_smul, ← nsmul_eq_mul, Nat.cast_smul_eq_nsmul]`.
-/
theorem dp_mul_dp (a b : ℕ) (x : B) : dp a x * dp b x = ((a + b).choose a : ℕ) * dp (a + b) x := by
  have h : ((a + b).choose a : ℚ) * ((a + b)! : ℚ)⁻¹ = (a ! : ℚ)⁻¹ * (b ! : ℚ)⁻¹ := by
    have h1 := Nat.add_choose_mul_factorial_mul_factorial b a
    rw [add_comm b a] at h1
    have h2 : ((a + b)! : ℚ) = ((a + b).choose a : ℚ) * b ! * a ! := by exact_mod_cast h1.symm
    have ha : (a ! : ℚ) ≠ 0 := by positivity
    have hb : (b ! : ℚ) ≠ 0 := by positivity
    have hc : ((a + b).choose a : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (Nat.le_add_right a b)).ne'
    rw [h2]; field_simp
  rw [dp, dp, dp, smul_mul_smul_comm, ← pow_add, ← h, mul_smul, ← nsmul_eq_mul,
    Nat.cast_smul_eq_nsmul]

/- English proof (translation)
Use `dp_mul_dp m 1 x` as an intermediate fact. Rewrite `this` using `[Nat.choose_succ_self_right]`. Rewrite using `[← this, mul_comm]`. Simplify using `[dp]`.
-/
theorem mul_dp (m : ℕ) (x : B) : x * dp m x = ((m + 1 : ℕ) : B) * dp (m + 1) x := by
  have := dp_mul_dp m 1 x
  rw [Nat.choose_succ_self_right] at this
  rw [← this, mul_comm]; simp [dp]

/- English proof (translation)
Rewrite using `[dp, dp, mul_pow, mul_smul_comm]`.
-/
theorem dp_mul (m : ℕ) (a x : B) : dp m (a * x) = a ^ m * dp m x := by
  rw [dp, dp, mul_pow, mul_smul_comm]

/- English proof (translation)
Establish `hm : (m ! : ℚ) ≠ 0` using `by positivity`. Rewrite using `[dp, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ hm, one_smul]`.
-/
theorem factorial_mul_dp (m : ℕ) (x : B) : (m ! : B) * dp m x = x ^ m := by
  have hm : (m ! : ℚ) ≠ 0 := by positivity
  rw [dp, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ hm, one_smul]

/- English proof (translation)
Rewrite using `[dp, Algebra.smul_def]`. Conclude with `(pow_dvd_pow x h).mul_left _`.
-/
theorem pow_dvd_dp {n m : ℕ} (h : n ≤ m) (x : B) : x ^ n ∣ dp m x := by
  rw [dp, Algebra.smul_def]
  exact (pow_dvd_pow x h).mul_left _

variable {A : Type*} [CommRing A] [Algebra A B]

def dpSpan (B : Type*) [CommRing B] [Algebra ℚ B] [Algebra A B] (ξ : A) (s : Set ℕ) :
    Submodule A B :=
  Submodule.span A ((fun m => dp m (algebraMap A B ξ)) '' s)

variable {ξ : A}

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_mono h)`.
-/
theorem dpSpan_mono {s t : Set ℕ} (h : s ⊆ t) : dpSpan B ξ s ≤ dpSpan B ξ t :=
  Submodule.span_mono (Set.image_mono h)

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨m, h, rfl⟩`.
-/
theorem dp_mem_dpSpan {s : Set ℕ} {m : ℕ} (h : m ∈ s) : dp m (algebraMap A B ξ) ∈ dpSpan B ξ s :=
  Submodule.subset_span ⟨m, h, rfl⟩

/- English proof (translation)
Rewrite using `[← nsmul_eq_mul]`. Conclude with `nsmul_mem h n`.
-/
theorem natCast_mul_mem {M : Submodule A B} (n : ℕ) {x : B} (h : x ∈ M) : (n : B) * x ∈ M := by
  rw [← nsmul_eq_mul]; exact nsmul_mem h n

/- English proof (translation)
Use `Submodule.mul_mem_mul hx hy` as an intermediate fact. Rewrite `this` using `[dpSpan, Submodule.span_mul_span]`. Use `(Submodule.span_le.2 ?_) this` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨a, -, rfl⟩, _, ⟨b, -, rfl⟩, rfl⟩`. Express the relevant statement in the definitionally equal form `dp a _ * dp b _ ∈ dpSpan B ξ Set.univ`.

Rewrite using `[dp_mul_dp]`. Conclude with `natCast_mul_mem _ (dp_mem_dpSpan trivial)`.
-/
theorem mul_mem_dpSpan {x y : B} (hx : x ∈ dpSpan B ξ Set.univ) (hy : y ∈ dpSpan B ξ Set.univ) :
    x * y ∈ dpSpan B ξ Set.univ := by
  have := Submodule.mul_mem_mul hx hy
  rw [dpSpan, Submodule.span_mul_span] at this
  refine (Submodule.span_le.2 ?_) this
  rintro _ ⟨_, ⟨a, -, rfl⟩, _, ⟨b, -, rfl⟩, rfl⟩
  change dp a _ * dp b _ ∈ dpSpan B ξ Set.univ
  rw [dp_mul_dp]
  exact natCast_mul_mem _ (dp_mem_dpSpan trivial)

/- English proof (translation)
Use `dpSpan_mono h hx` as an intermediate fact. Rewrite `this` using `[dpSpan, Set.image_insert_eq, Submodule.mem_span_insert]`. Conclude with `this`.
-/
theorem exists_eq_of_mem_dpSpan {s t : Set ℕ} {m : ℕ} (h : s ⊆ insert m t) {x : B}
    (hx : x ∈ dpSpan B ξ s) : ∃ a : A, ∃ z ∈ dpSpan B ξ t, x = a • dp m (algebraMap A B ξ) + z := by
  have := dpSpan_mono h hx
  rw [dpSpan, Set.image_insert_eq, Submodule.mem_span_insert] at this
  exact this

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨m, hm, rfl⟩ := hx`. Conclude with `pow_dvd_dp (h m hm) _`. Consider the case `zero => exact dvd_zero _`. Consider the case `add x y _ _ hx hy => exact dvd_add hx hy`.

Consider the case `smul a x _ hx => rw [Algebra.smul_def]`. Conclude with `hx.mul_left _`.
-/
theorem pow_dvd_of_mem_dpSpan {s : Set ℕ} {n : ℕ} (h : ∀ m ∈ s, n ≤ m) {x : B}
    (hx : x ∈ dpSpan B ξ s) : algebraMap A B ξ ^ n ∣ x := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨m, hm, rfl⟩ := hx; exact pow_dvd_dp (h m hm) _
  | zero => exact dvd_zero _
  | add x y _ _ hx hy => exact dvd_add hx hy
  | smul a x _ hx => rw [Algebra.smul_def]; exact hx.mul_left _

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨m, -, rfl⟩ := hx; exact ⟨m + 1, dp_mem_dpSpan (by simp)⟩`. Consider the case `zero => exact ⟨0, zero_mem _⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨M, hM⟩` from `hx`.

Take `⟨N, hN⟩` from `hy`. Conclude with `⟨max M N, add_mem (dpSpan_mono (Set.Ico_subset_Ico_right (le_max_left _ _)) hM) (dpSpan_mono (Set.Ico_subset_Ico_right (le_max_right _ _)) hN)⟩`. Consider the case `smul a x _ hx => obtain ⟨M, hM⟩ := hx`. Conclude with `⟨M, Submodule.smul_mem _ a hM⟩`.
-/
theorem exists_mem_dpSpan_Ico {x : B} (hx : x ∈ dpSpan B ξ Set.univ) :
    ∃ M, x ∈ dpSpan B ξ (Set.Ico 0 M) := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨m, -, rfl⟩ := hx; exact ⟨m + 1, dp_mem_dpSpan (by simp)⟩
  | zero => exact ⟨0, zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨M, hM⟩ := hx
    obtain ⟨N, hN⟩ := hy
    exact ⟨max M N, add_mem (dpSpan_mono (Set.Ico_subset_Ico_right (le_max_left _ _)) hM)
      (dpSpan_mono (Set.Ico_subset_Ico_right (le_max_right _ _)) hN)⟩
  | smul a x _ hx => obtain ⟨M, hM⟩ := hx; exact ⟨M, Submodule.smul_mem _ a hM⟩

/- English proof (translation)
Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul, mul_left_comm, ← mul_dp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem smul_dp_of_eq (m : ℕ) (c : A) : (ξ * c) • dp m (algebraMap A B ξ) =
    ((m + 1 : ℕ) : B) * (c • dp (m + 1) (algebraMap A B ξ)) := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, mul_left_comm, ← mul_dp]; ring

variable [IsDomain B] (h0 : algebraMap A B ξ ≠ 0)
  (hξ : ∀ a : A, algebraMap A B ξ ∣ algebraMap A B a → ξ ∣ a)
include h0 hξ

/- English proof (translation)
Establish `h1` using `h.mul_left (m ! : B)`. Rewrite `h1` using `[Algebra.smul_def, mul_left_comm, factorial_mul_dp, pow_succ']`. Conclude with `hξ a ((mul_dvd_mul_iff_right (pow_ne_zero m h0)).1 h1)`.
-/
theorem dvd_of_pow_succ_dvd_smul_dp {m : ℕ} {a : A}
    (h : algebraMap A B ξ ^ (m + 1) ∣ a • dp m (algebraMap A B ξ)) : ξ ∣ a := by
  have h1 := h.mul_left (m ! : B)
  rw [Algebra.smul_def, mul_left_comm, factorial_mul_dp, pow_succ'] at h1
  exact hξ a ((mul_dvd_mul_iff_right (pow_ne_zero m h0)).1 h1)

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => exact dpSpan_mono (fun _ _ => Nat.zero_le _) hz`. Consider the case `succ m ih`. Take `⟨a, w, hw, rfl⟩` from `exists_eq_of_mem_dpSpan (m := m) (t := Set.Ici (m + 1)) (fun k hk => by simp at hk ⊢; omega) (ih ((pow_dvd_pow _ m.le_succ).trans h))`. Establish `hw'` using `pow_dvd_of_mem_dpSpan (n := m + 1) (fun _ hk => hk) hw`.

Take `⟨c, rfl⟩` from `dvd_of_pow_succ_dvd_smul_dp h0 hξ ((dvd_add_left hw').1 h)`. Rewrite using `[smul_dp_of_eq]`. Conclude with `add_mem (natCast_mul_mem _ (Submodule.smul_mem _ _ (dp_mem_dpSpan (by simp)))) hw`.
-/
theorem mem_dpSpan_Ici {m : ℕ} {z : B} (hz : z ∈ dpSpan B ξ Set.univ)
    (h : algebraMap A B ξ ^ m ∣ z) : z ∈ dpSpan B ξ (Set.Ici m) := by
  induction m with
  | zero => exact dpSpan_mono (fun _ _ => Nat.zero_le _) hz
  | succ m ih =>
    obtain ⟨a, w, hw, rfl⟩ := exists_eq_of_mem_dpSpan (m := m) (t := Set.Ici (m + 1))
      (fun k hk => by simp at hk ⊢; omega) (ih ((pow_dvd_pow _ m.le_succ).trans h))
    have hw' := pow_dvd_of_mem_dpSpan (n := m + 1) (fun _ hk => hk) hw
    obtain ⟨c, rfl⟩ := dvd_of_pow_succ_dvd_smul_dp h0 hξ ((dvd_add_left hw').1 h)
    rw [smul_dp_of_eq]
    exact add_mem (natCast_mul_mem _ (Submodule.smul_mem _ _ (dp_mem_dpSpan (by simp)))) hw

/- English proof (translation)
Take `⟨M, hM⟩` from `exists_mem_dpSpan_Ico hx`. Establish `key : ∀ m ≤ q * M, ∃ z ∈ dpSpan B ξ Set.univ, x - q * z ∈ dpSpan B ξ (Set.Ico m (q * M))`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`.

Introduce `_`. Conclude with `⟨0, zero_mem _, by`. Simplify using `using dpSpan_mono (Set.Ico_subset_Ico_right (Nat.le_mul_of_pos_left M hq0)) hM⟩`. Consider the case `succ m ih`. Introduce `hm`.

Take `⟨z, hz, hz'⟩` from `ih (by omega)`. Take `⟨a, w, hw, e⟩` from `exists_eq_of_mem_dpSpan (m := m) (t := Set.Ico (m + 1) (q * M)) (fun k hk => by simp at hk ⊢; omega) hz'`. Establish `hw'` using `pow_dvd_of_mem_dpSpan (n := m + 1) (fun _ hk => hk.1) hw`. Take `⟨y, hy, hy'⟩` from `h (m + 1)`. Establish `h1 : algebraMap A B ξ ^ (m + 1) ∣ a • dp m (algebraMap A B ξ) - q * (y - z)`.

Establish `: a • dp m (algebraMap A B ξ) - q * (y - z) = (x - q * y) - w`. Take the linear combination `-e`. Rewrite using `[this]`. Conclude with `dvd_sub hy' hw'`. Establish `h2 : algebraMap A B ξ ^ m ∣ y - z`.

Establish `h3 : algebraMap A B ξ ^ m ∣ a • dp m (algebraMap A B ξ)`. Rewrite using `[Algebra.smul_def]`. Conclude with `(pow_dvd_dp le_rfl _).mul_left _`. Use `dvd_sub h3 ((pow_dvd_pow _ m.le_succ).trans h1)` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`.

Conclude with `(hq.dvd_mul_left).1 this`. Take `⟨c, v, hv, e2⟩` from `exists_eq_of_mem_dpSpan (m := m) (t := Set.Ici (m + 1)) (fun k hk => by simp at hk ⊢; omega) (mem_dpSpan_Ici h0 hξ (sub_mem hy hz) h2)`. Establish `hv'` using `pow_dvd_of_mem_dpSpan (n := m + 1) (fun _ hk => hk) hv`. Establish `h4 : algebraMap A B ξ ^ (m + 1) ∣ (a - q * c) • dp m (algebraMap A B ξ)`. Establish `: (a - q * c) • dp m (algebraMap A B ξ) = (a • dp m (algebraMap A B ξ) - q * (y - z)) + q * v`.

Rewrite using `[e2]`. Simplify using `only [Algebra.smul_def, map_sub, map_mul, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `dvd_add h1 (hv'.mul_left _)`.

Take `⟨d, hd⟩` from `dvd_of_pow_succ_dvd_smul_dp h0 hξ h4`. Establish `e3 : x - q * (z + c • dp m (algebraMap A B ξ)) = ((m + 1 : ℕ) : B) * (d • dp (m + 1) (algebraMap A B ξ)) + w`. Rewrite using `[← smul_dp_of_eq, ← hd]`. Simplify using `only [Algebra.smul_def, map_sub, map_mul, map_natCast] at e ⊢`. Take the linear combination `e`.

Establish `hc : z + c • dp m (algebraMap A B ξ) ∈ dpSpan B ξ Set.univ` using `add_mem hz (Submodule.smul_mem _ _ (dp_mem_dpSpan trivial))`. Break down `hm.lt_or_eq with hlt | heq` into its components or cases. Use `⟨_, hc, ?_⟩` and prove the remaining obligations. Rewrite using `[e3]`. Conclude with `add_mem (natCast_mul_mem _ (Submodule.smul_mem _ _ (dp_mem_dpSpan ⟨le_rfl, hlt⟩))) hw`.

Use `⟨_, add_mem hc (natCast_mul_mem M (Submodule.smul_mem _ d (dp_mem_dpSpan (m := m + 1) trivial))), ?_⟩` and prove the remaining obligations. Establish `: x - q * (z + c • dp m (algebraMap A B ξ) + M * d • dp (m + 1) (algebraMap A B ξ)) = w`. Rewrite `e3` using `[show ((m + 1 : ℕ) : B) = q * M by rw [heq]; push_cast; rfl]`. Take the linear combination `e3`. Rewrite using `[this]`.

Conclude with `hw`. Take `⟨z, hz, hz'⟩` from `key _ le_rfl`. Use `⟨z, hz, sub_eq_zero.1 ?_⟩` and prove the remaining obligations. Simplify `hz'` using `[dpSpan]`.
-/
theorem exists_eq_mul_of_forall {q : ℕ} (hq0 : 0 < q) (hq : IsUnit (q : B)) {x : B}
    (hx : x ∈ dpSpan B ξ Set.univ)
    (h : ∀ n, ∃ z ∈ dpSpan B ξ Set.univ, algebraMap A B ξ ^ n ∣ x - q * z) :
    ∃ z ∈ dpSpan B ξ Set.univ, x = q * z := by
  obtain ⟨M, hM⟩ := exists_mem_dpSpan_Ico hx
  have key : ∀ m ≤ q * M, ∃ z ∈ dpSpan B ξ Set.univ, x - q * z ∈ dpSpan B ξ (Set.Ico m (q * M)) := by
    intro m
    induction m with
    | zero =>
      intro _
      exact ⟨0, zero_mem _, by
        simpa using dpSpan_mono (Set.Ico_subset_Ico_right (Nat.le_mul_of_pos_left M hq0)) hM⟩
    | succ m ih =>
      intro hm
      obtain ⟨z, hz, hz'⟩ := ih (by omega)
      obtain ⟨a, w, hw, e⟩ := exists_eq_of_mem_dpSpan (m := m) (t := Set.Ico (m + 1) (q * M))
        (fun k hk => by simp at hk ⊢; omega) hz'
      have hw' := pow_dvd_of_mem_dpSpan (n := m + 1) (fun _ hk => hk.1) hw
      obtain ⟨y, hy, hy'⟩ := h (m + 1)
      have h1 : algebraMap A B ξ ^ (m + 1) ∣ a • dp m (algebraMap A B ξ) - q * (y - z) := by
        have : a • dp m (algebraMap A B ξ) - q * (y - z) = (x - q * y) - w := by
          linear_combination -e
        rw [this]; exact dvd_sub hy' hw'
      have h2 : algebraMap A B ξ ^ m ∣ y - z := by
        have h3 : algebraMap A B ξ ^ m ∣ a • dp m (algebraMap A B ξ) := by
          rw [Algebra.smul_def]; exact (pow_dvd_dp le_rfl _).mul_left _
        have := dvd_sub h3 ((pow_dvd_pow _ m.le_succ).trans h1)
        rw [sub_sub_cancel] at this
        exact (hq.dvd_mul_left).1 this
      obtain ⟨c, v, hv, e2⟩ := exists_eq_of_mem_dpSpan (m := m) (t := Set.Ici (m + 1))
        (fun k hk => by simp at hk ⊢; omega) (mem_dpSpan_Ici h0 hξ (sub_mem hy hz) h2)
      have hv' := pow_dvd_of_mem_dpSpan (n := m + 1) (fun _ hk => hk) hv
      have h4 : algebraMap A B ξ ^ (m + 1) ∣ (a - q * c) • dp m (algebraMap A B ξ) := by
        have : (a - q * c) • dp m (algebraMap A B ξ) =
            (a • dp m (algebraMap A B ξ) - q * (y - z)) + q * v := by
          rw [e2]; simp only [Algebra.smul_def, map_sub, map_mul, map_natCast]; ring
        rw [this]; exact dvd_add h1 (hv'.mul_left _)
      obtain ⟨d, hd⟩ := dvd_of_pow_succ_dvd_smul_dp h0 hξ h4
      have e3 : x - q * (z + c • dp m (algebraMap A B ξ)) =
          ((m + 1 : ℕ) : B) * (d • dp (m + 1) (algebraMap A B ξ)) + w := by
        rw [← smul_dp_of_eq, ← hd]
        simp only [Algebra.smul_def, map_sub, map_mul, map_natCast] at e ⊢
        linear_combination e
      have hc : z + c • dp m (algebraMap A B ξ) ∈ dpSpan B ξ Set.univ :=
        add_mem hz (Submodule.smul_mem _ _ (dp_mem_dpSpan trivial))
      rcases hm.lt_or_eq with hlt | heq
      · refine ⟨_, hc, ?_⟩
        rw [e3]
        exact add_mem (natCast_mul_mem _ (Submodule.smul_mem _ _ (dp_mem_dpSpan ⟨le_rfl, hlt⟩))) hw
      · refine ⟨_, add_mem hc (natCast_mul_mem M (Submodule.smul_mem _ d
          (dp_mem_dpSpan (m := m + 1) trivial))), ?_⟩
        have : x - q * (z + c • dp m (algebraMap A B ξ) + M * d • dp (m + 1) (algebraMap A B ξ))
            = w := by
          rw [show ((m + 1 : ℕ) : B) = q * M by rw [heq]; push_cast; rfl] at e3
          linear_combination e3
        rw [this]; exact hw
  obtain ⟨z, hz, hz'⟩ := key _ le_rfl
  refine ⟨z, hz, sub_eq_zero.1 ?_⟩
  simpa [dpSpan] using hz'

end DP

section Lattice

variable {A Q : Type*} [CommRing A] [CommRing Q]

/- English proof (translation)
Rewrite using `[smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`.
-/
theorem mem_span_natCast_pow_iff {D : Type*} [CommRing D] (p n : ℕ) (x : D) :
    x ∈ (span {(p : D)} ^ n • ⊤ : Submodule D D) ↔ (p : D) ^ n ∣ x := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

/- English proof (translation)
Simplify using `only [SModEq.zero, mem_span_natCast_pow_iff] at hx`. Take `⟨a, ha⟩` from `h₂ x x.2`. Establish `: f a = 0` using `h₃ a fun k => by`. Take `⟨y, hy⟩` from `hx k`. Take `⟨b, hb⟩` from `h₂ y y.2`.

Use `⟨b, ?_⟩` and prove the remaining obligations. Rewrite using `[ha, hb, hy]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `this` using `[ha]`.

Conclude with `Subtype.ext ((hp.pow N).mul_right_eq_zero.1 this)`. Use the proof step `prec' d hd := by`. Simplify using `only [SModEq.sub_mem, mem_span_natCast_pow_iff] at hd ⊢`. Establish `hs : ∀ k, ∃ b, (p : Q) ^ k * f b = (p : Q) ^ N * ((d (k + 1) : Q) - d k)`. Introduce `k`.

Take `⟨y, hy⟩` from `(dvd_neg.2 (hd k.le_succ))`. Take `⟨b, hb⟩` from `h₂ y y.2`. Use `⟨b, ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val hy` as an intermediate fact. Move the coercions through the operations in `at this`.

Rewrite using `[hb, mul_left_comm, ← this]`. Expand and normalize the polynomial expressions, which then agree. Use `choose b hb using hs`. Take `⟨a0, ha0⟩` from `h₂ (d 0) (d 0).2`. Set `a : ℕ → A` to `fun k => a0 + ∑ i ∈ Finset.range k, (p : A) ^ i * b i`.

Establish `ha : ∀ k, f (a k) = (p : Q) ^ N * d k`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simpa [a] using ha0`. Consider the case `succ k ih`.

Establish `: a (k + 1) = a k + (p : A) ^ k * b k`. Simplify using `only [a, Finset.sum_range_succ, add_assoc]`. Rewrite using `[this, map_add, ih, map_mul, map_pow, map_natCast, hb]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨L, hL⟩` from `IsPrecomplete.prec' (I := span {(p : A)}) a (fun {m n} hmn => by`.

Rewrite using `[SModEq.sub_mem, mem_span_natCast_pow_iff, ← dvd_neg, neg_sub]`. Simplify using `only [a, add_sub_add_left_eq_sub]`. Rewrite using `[← Finset.sum_Ico_eq_sub _ hmn]`. Conclude with `Finset.dvd_sum fun i hi => (pow_dvd_pow _ (Finset.mem_Ico.1 hi).1).mul_right _)`. Simplify using `only [SModEq.sub_mem, mem_span_natCast_pow_iff] at hL`.

Take `⟨c, hc⟩` from `hL N`. Use `⟨d N - ⟨f c, h₁ c⟩, fun k => ?_⟩` and prove the remaining obligations. Take `⟨e, he⟩` from `hL (N + k)`. Establish `h5 : (p : D) ^ k ∣ d (N + k) - (d N - ⟨f c, h₁ c⟩)`. Use `⟨⟨f e, h₁ e⟩, Subtype.ext ((hp.pow N).mul_left_cancel ?_)⟩` and prove the remaining obligations.

Establish `e1` using `congrArg f hc`. Establish `e2` using `congrArg f he`. Rewrite `e1`, `e2` using `[map_sub, ha, map_mul, map_pow, map_natCast]`. Use `push_cast`. Take the linear combination `e2 - e1`.

Use `dvd_add (hd (Nat.le_add_left k N)) h5` as an intermediate fact. Rewrite `this` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem isAdicComplete_of_lattice (p N : ℕ) [IsAdicComplete (span {(p : A)}) A] (f : A →+* Q)
    (hp : IsUnit (p : Q)) (D : Subring Q) (h₁ : ∀ a, f a ∈ D)
    (h₂ : ∀ d ∈ D, ∃ a, f a = (p : Q) ^ N * d)
    (h₃ : ∀ x, (∀ k : ℕ, ∃ a, f x = (p : Q) ^ k * f a) → f x = 0) :
    IsAdicComplete (span {(p : D)}) D where
  haus' x hx := by
    simp only [SModEq.zero, mem_span_natCast_pow_iff] at hx
    obtain ⟨a, ha⟩ := h₂ x x.2
    have : f a = 0 := h₃ a fun k => by
      obtain ⟨y, hy⟩ := hx k
      obtain ⟨b, hb⟩ := h₂ y y.2
      refine ⟨b, ?_⟩
      rw [ha, hb, hy]; push_cast; ring
    rw [ha] at this
    exact Subtype.ext ((hp.pow N).mul_right_eq_zero.1 this)
  prec' d hd := by
    simp only [SModEq.sub_mem, mem_span_natCast_pow_iff] at hd ⊢
    have hs : ∀ k, ∃ b, (p : Q) ^ k * f b = (p : Q) ^ N * ((d (k + 1) : Q) - d k) := by
      intro k
      obtain ⟨y, hy⟩ := (dvd_neg.2 (hd k.le_succ))
      obtain ⟨b, hb⟩ := h₂ y y.2
      refine ⟨b, ?_⟩
      have := congrArg Subtype.val hy
      push_cast at this
      rw [hb, mul_left_comm, ← this]; ring
    choose b hb using hs
    obtain ⟨a0, ha0⟩ := h₂ (d 0) (d 0).2
    let a : ℕ → A := fun k => a0 + ∑ i ∈ Finset.range k, (p : A) ^ i * b i
    have ha : ∀ k, f (a k) = (p : Q) ^ N * d k := by
      intro k
      induction k with
      | zero => simpa [a] using ha0
      | succ k ih =>
        have : a (k + 1) = a k + (p : A) ^ k * b k := by
          simp only [a, Finset.sum_range_succ, add_assoc]
        rw [this, map_add, ih, map_mul, map_pow, map_natCast, hb]; ring
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := span {(p : A)}) a (fun {m n} hmn => by
      rw [SModEq.sub_mem, mem_span_natCast_pow_iff, ← dvd_neg, neg_sub]
      simp only [a, add_sub_add_left_eq_sub]
      rw [← Finset.sum_Ico_eq_sub _ hmn]
      exact Finset.dvd_sum fun i hi => (pow_dvd_pow _ (Finset.mem_Ico.1 hi).1).mul_right _)
    simp only [SModEq.sub_mem, mem_span_natCast_pow_iff] at hL
    obtain ⟨c, hc⟩ := hL N
    refine ⟨d N - ⟨f c, h₁ c⟩, fun k => ?_⟩
    obtain ⟨e, he⟩ := hL (N + k)
    have h5 : (p : D) ^ k ∣ d (N + k) - (d N - ⟨f c, h₁ c⟩) := by
      refine ⟨⟨f e, h₁ e⟩, Subtype.ext ((hp.pow N).mul_left_cancel ?_)⟩
      have e1 := congrArg f hc
      have e2 := congrArg f he
      rw [map_sub, ha, map_mul, map_pow, map_natCast] at e1 e2
      push_cast
      linear_combination e2 - e1
    have := dvd_add (hd (Nat.le_add_left k N)) h5
    rwa [sub_add_sub_cancel] at this

def adicLift (p : ℕ) [IsAdicComplete (span {(p : Q)}) Q] (g : A →+* Q) :
    AdicCompletion (span {(p : A)}) A →+* Q :=
  (AdicCompletion.ofAlgEquiv (span {(p : Q)})).symm.toRingEquiv.toRingHom.comp
    (adicMap _ _ g (span_natCast_le_comap p g))

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(AdicCompletion.ofAlgEquiv (span {(p : Q)})).symm (adicMap _ _ g _ _) = _`. Rewrite using `[adicMap_algebraMap, AlgEquiv.commutes]`. Both sides reduce to the same expression.
-/
theorem adicLift_algebraMap (p : ℕ) [IsAdicComplete (span {(p : Q)}) Q] (g : A →+* Q) (a : A) :
    adicLift p g (algebraMap A _ a) = g a := by
  change (AdicCompletion.ofAlgEquiv (span {(p : Q)})).symm (adicMap _ _ g _ _) = _
  rw [adicMap_algebraMap, AlgEquiv.commutes]; rfl

end Lattice

end Reformulated.AutPerF
