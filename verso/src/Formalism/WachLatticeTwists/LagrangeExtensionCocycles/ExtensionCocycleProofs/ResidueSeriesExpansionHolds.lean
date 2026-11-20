import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.ResidueQuotientHolds

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

section Weight

variable {A : Type} [CommRing A]

def wI (L Q : A) (W e : ℕ) : Ideal A :=
  Ideal.span {z | ∃ a b : ℕ, e ≤ a * W + b ∧ z = L ^ a * Q ^ b}

/- English proof (translation)
Establish `hle : wI L Q W e * wI L Q W e' ≤ wI L Q W (e + e')`. Unfold `wI`. Rewrite using `[Ideal.span_mul_span']`. Apply `Ideal.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, ⟨a, b, hab, rfl⟩, y, ⟨a', b', hab', rfl⟩, rfl⟩`.

Use `⟨a + a', b + b', ?_, by ring⟩` and prove the remaining obligations. Rewrite using `[add_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `hle (Ideal.mul_mem_mul hz hz')`.
-/
theorem wI_mul (L Q : A) (W : ℕ) {e e' : ℕ} {z z' : A} (hz : z ∈ wI L Q W e)
    (hz' : z' ∈ wI L Q W e') : z * z' ∈ wI L Q W (e + e') := by
  have hle : wI L Q W e * wI L Q W e' ≤ wI L Q W (e + e') := by
    unfold wI
    rw [Ideal.span_mul_span']
    apply Ideal.span_mono
    rintro _ ⟨x, ⟨a, b, hab, rfl⟩, y, ⟨a', b', hab', rfl⟩, rfl⟩
    refine ⟨a + a', b + b', ?_, by ring⟩
    rw [add_mul]
    linarith
  exact hle (Ideal.mul_mem_mul hz hz')

/- English proof (translation)
Establish `h1 : (1 : A) ∈ wI L Q W 0` using `Ideal.subset_span ⟨0, 0, Nat.zero_le _, by simp⟩`. Simplify using `using Ideal.mul_mem_left _ z h1`.
-/
theorem wI_zero (L Q : A) (W : ℕ) (z : A) : z ∈ wI L Q W 0 := by
  have h1 : (1 : A) ∈ wI L Q W 0 := Ideal.subset_span ⟨0, 0, Nat.zero_le _, by simp⟩
  simpa using Ideal.mul_mem_left _ z h1

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using wI_zero L Q W 1`. Consider the case `succ n ih`. Rewrite using `[pow_succ, Nat.succ_mul]`. Conclude with `wI_mul L Q W ih hz`.
-/
theorem wI_pow (L Q : A) (W : ℕ) {e : ℕ} {z : A} (hz : z ∈ wI L Q W e) (n : ℕ) :
    z ^ n ∈ wI L Q W (n * e) := by
  induction n with
  | zero => simpa using wI_zero L Q W 1
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact wI_mul L Q W ih hz

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simpa using wI_zero L Q W 1`. Consider the case `succ j ih`. Rewrite using `[Finset.prod_range_succ, Finset.sum_range_succ]`. Conclude with `wI_mul L Q W (ih fun k hk => h k (by omega)) (h j (by omega))`.
-/
theorem wI_prod (L Q : A) (W : ℕ) (f : ℕ → A) (e : ℕ → ℕ) (j : ℕ)
    (h : ∀ k < j, f k ∈ wI L Q W (e k)) :
    ∏ k ∈ Finset.range j, f k ∈ wI L Q W (∑ k ∈ Finset.range j, e k) := by
  induction j with
  | zero => simpa using wI_zero L Q W 1
  | succ j ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ]
    exact wI_mul L Q W (ih fun k hk => h k (by omega)) (h j (by omega))

/- English proof (translation)
Rewrite using `[wI, Ideal.span_le]`. Introduce and unpack `_ ⟨a, b, hab, rfl⟩`. Distinguish the cases in `hca : c ≤ a`. Establish `e1 : L ^ a * Q ^ b = L ^ c * (L ^ (a - c) * Q ^ b)`. Rewrite using `[← mul_assoc, ← pow_add, Nat.add_sub_cancel' hca]`.

Rewrite using `[SetLike.mem_coe, e1]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))`. Use `push_neg at hca`. Establish `h1 : (a + 1) * W ≤ c * W` using `Nat.mul_le_mul_right W hca`. Rewrite `h1` using `[add_mul, one_mul]`.

Establish `hyb : y ≤ b` using `by linarith`. Establish `e1 : L ^ a * Q ^ b = Q ^ y * (L ^ a * Q ^ (b - y))`. Rewrite using `[mul_left_comm, ← pow_add, Nat.add_sub_cancel' hyb]`. Rewrite using `[SetLike.mem_coe, e1]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))`.
-/
theorem wI_le (L Q : A) (W e c y : ℕ) (hW : 1 ≤ W) (h : c * W + y ≤ e + 1) :
    wI L Q W e ≤ Ideal.span {L ^ c, Q ^ y} := by
  rw [wI, Ideal.span_le]
  rintro _ ⟨a, b, hab, rfl⟩
  by_cases hca : c ≤ a
  · have e1 : L ^ a * Q ^ b = L ^ c * (L ^ (a - c) * Q ^ b) := by
      rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hca]
    rw [SetLike.mem_coe, e1]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
  · push_neg at hca
    have h1 : (a + 1) * W ≤ c * W := Nat.mul_le_mul_right W hca
    rw [add_mul, one_mul] at h1
    have hyb : y ≤ b := by linarith
    have e1 : L ^ a * Q ^ b = Q ^ y * (L ^ a * Q ^ (b - y)) := by
      rw [mul_left_comm, ← pow_add, Nat.add_sub_cancel' hyb]
    rw [SetLike.mem_coe, e1]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

end Weight

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih`. Rewrite using `[Finset.sum_range_succ, add_right_comm, ih, pow_succ]`. Take `⟨m, rfl⟩ : ∃ m, ℓ = m + 1` from `⟨ℓ - 1, by omega⟩`.

Simplify using `only [Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem geom_nat (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (j : ℕ) :
    (∑ k ∈ Finset.range j, (ℓ - 1) * ℓ ^ k) + 1 = ℓ ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, add_right_comm, ih, pow_succ]
    obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring

/- English proof (translation)
Introduce `A _ ℓ hℓ x U p j y r c hj hr hp hcy`. Establish `hW : 1 ≤ ℓ ^ (j - 1)` using `Nat.one_le_pow _ _ (by omega)`. Establish `hpk : ∀ k < j, p k ∈ wI (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) (ℓ ^ k)`. Introduce `k hk`. Use `(Ideal.span_le.mpr ?_) (hp k hk)` and prove the remaining obligations.

Introduce `z hz`. Break down `hz with rfl | rfl` into its components or cases. Use `Ideal.subset_span ⟨1, 0, ?_, by simp⟩` and prove the remaining obligations. Simplify using `only [one_mul, add_zero]`. Conclude with `Nat.pow_le_pow_right (by omega) (by omega)`.

Conclude with `Ideal.subset_span ⟨0, ℓ ^ k, by simp, by simp⟩`. Establish `hP : ∏ k ∈ Finset.range j, p k ^ (ℓ - 1) ∈ wI (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) (ℓ ^ j - 1)`. Establish `h1` using `wI_prod (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) (fun k => p k ^ (ℓ - 1)) (fun k => (ℓ - 1) * ℓ ^ k) j (fun k hk => by`. Establish `h2` using `wI_pow (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) (hpk k hk) (ℓ - 1)`. Conclude with `h2)`.

Establish `hg` using `geom_nat ℓ (by omega) j`. Establish `e : ∑ k ∈ Finset.range j, (ℓ - 1) * ℓ ^ k = ℓ ^ j - 1` using `by omega`. Rewrite `h1` using `[e]`. Conclude with `h1`. Establish `hx : x ∈ wI (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) 1`.

Establish `hQ : x + (ℓ : A) ∈ wI (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) 1` using `Ideal.subset_span ⟨0, 1, by simp, by simp⟩`. Establish `hL : (ℓ : A) ∈ wI (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) 1` using `Ideal.subset_span ⟨1, 0, by simpa using hW, by simp⟩`. Establish `h` using `Ideal.sub_mem _ hQ hL`. Rewrite `h` using `[add_sub_cancel_right]`. Then use the resulting hypothesis. Take `⟨r', rfl⟩ : ∃ r', r = r' + 1` from `⟨r - 1, by omega⟩`.

Establish `hmain` using `wI_mul (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) (wI_pow (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) hx r') (wI_pow (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) hP (r' + 1))`. Establish `hN : 1 ≤ ℓ ^ j` using `Nat.one_le_pow _ _ (by omega)`. Establish `e2 : r' * 1 + (r' + 1) * (ℓ ^ j - 1) + 1 = (r' + 1) * ℓ ^ j`. Rewrite using `[Nat.mul_sub_one]`. Establish `h5 : (r' + 1) * 1 ≤ (r' + 1) * ℓ ^ j` using `Nat.mul_le_mul_left _ hN`.

Rewrite `h5` using `[mul_one]`. Use linear arithmetic over natural numbers and integers. Establish `hin` using `wI_le (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) _ c y hW (by rw [e2]; exact hcy) hmain`. Establish `hfin : x * (x ^ r' * (∏ k ∈ Finset.range j, p k ^ (ℓ - 1)) ^ (r' + 1)) ∈ Ideal.span {(ℓ : A) ^ c * x, x * (x + (ℓ : A)) ^ y}`. Establish `h1` using `Ideal.mul_mem_mul (Ideal.mem_span_singleton_self x) hin`.

Rewrite `h1` using `[Ideal.span_mul_span']`. Use `Ideal.span_mono ?_ h1` and prove the remaining obligations. Introduce and unpack `_ ⟨u, hu, v, hv, rfl⟩`. Rewrite `hu` using `[Set.mem_singleton_iff]`. Substitute `hu` using the available equality.

Break down `hv with rfl | rfl` into its components or cases. Conclude with `Or.inl (mul_comm _ _)`. Conclude with `Or.inr rfl`. Establish `e3 : (U * x * ∏ k ∈ Finset.range j, p k ^ (ℓ - 1)) ^ (r' + 1) = U ^ (r' + 1) * (x * (x ^ r' * (∏ k ∈ Finset.range j, p k ^ (ℓ - 1)) ^ (r' + 1)))` using `by ring`. Rewrite using `[e3]`.

Conclude with `Ideal.mul_mem_left _ _ hfin`.
-/
theorem sign_character_at_j_holds : StatSigJ := by
  intro A _ ℓ hℓ x U p j y r c hj hr hp hcy
  have hW : 1 ≤ ℓ ^ (j - 1) := Nat.one_le_pow _ _ (by omega)
  have hpk : ∀ k < j, p k ∈ wI (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) (ℓ ^ k) := by
    intro k hk
    refine (Ideal.span_le.mpr ?_) (hp k hk)
    intro z hz
    rcases hz with rfl | rfl
    · refine Ideal.subset_span ⟨1, 0, ?_, by simp⟩
      simp only [one_mul, add_zero]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    · exact Ideal.subset_span ⟨0, ℓ ^ k, by simp, by simp⟩
  have hP : ∏ k ∈ Finset.range j, p k ^ (ℓ - 1) ∈
      wI (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) (ℓ ^ j - 1) := by
    have h1 := wI_prod (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) (fun k => p k ^ (ℓ - 1))
      (fun k => (ℓ - 1) * ℓ ^ k) j (fun k hk => by
        have h2 := wI_pow (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) (hpk k hk) (ℓ - 1)
        exact h2)
    have hg := geom_nat ℓ (by omega) j
    have e : ∑ k ∈ Finset.range j, (ℓ - 1) * ℓ ^ k = ℓ ^ j - 1 := by omega
    rw [e] at h1
    exact h1
  have hx : x ∈ wI (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) 1 := by
    have hQ : x + (ℓ : A) ∈ wI (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) 1 :=
      Ideal.subset_span ⟨0, 1, by simp, by simp⟩
    have hL : (ℓ : A) ∈ wI (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) 1 :=
      Ideal.subset_span ⟨1, 0, by simpa using hW, by simp⟩
    have h := Ideal.sub_mem _ hQ hL
    rwa [add_sub_cancel_right] at h
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have hmain := wI_mul (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1))
    (wI_pow (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) hx r') (wI_pow (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) hP (r' + 1))
  have hN : 1 ≤ ℓ ^ j := Nat.one_le_pow _ _ (by omega)
  have e2 : r' * 1 + (r' + 1) * (ℓ ^ j - 1) + 1 = (r' + 1) * ℓ ^ j := by
    rw [Nat.mul_sub_one]
    have h5 : (r' + 1) * 1 ≤ (r' + 1) * ℓ ^ j := Nat.mul_le_mul_left _ hN
    rw [mul_one] at h5
    omega
  have hin := wI_le (ℓ : A) (x + (ℓ : A)) (ℓ ^ (j - 1)) _ c y hW (by rw [e2]; exact hcy) hmain
  have hfin : x * (x ^ r' * (∏ k ∈ Finset.range j, p k ^ (ℓ - 1)) ^ (r' + 1)) ∈
      Ideal.span {(ℓ : A) ^ c * x, x * (x + (ℓ : A)) ^ y} := by
    have h1 := Ideal.mul_mem_mul (Ideal.mem_span_singleton_self x) hin
    rw [Ideal.span_mul_span'] at h1
    refine Ideal.span_mono ?_ h1
    rintro _ ⟨u, hu, v, hv, rfl⟩
    rw [Set.mem_singleton_iff] at hu
    subst hu
    rcases hv with rfl | rfl
    · exact Or.inl (mul_comm _ _)
    · exact Or.inr rfl
  have e3 : (U * x * ∏ k ∈ Finset.range j, p k ^ (ℓ - 1)) ^ (r' + 1) =
      U ^ (r' + 1) * (x * (x ^ r' * (∏ k ∈ Finset.range j, p k ^ (ℓ - 1)) ^ (r' + 1))) := by ring
  rw [e3]
  exact Ideal.mul_mem_left _ _ hfin

/- English proof (translation)
Introduce `n _ ℓ c s H hℓ hc hH hs i`. Establish `hq : 0 < ℓ - 1` using `by linarith`. Establish `hq1 : 1 < ℓ - 1` using `by linarith`. Use `set f : ℕ → ℝ := fun a => (H (i + ((a + 1 : ℕ) : ZMod n)) + c + 3) / (ℓ - 1) ^ a with hf`. Establish `hHle : ∀ k, H k ≤ ∑ k', H k'` using `fun k => Finset.single_le_sum (f := H) (fun k _ => hH k) (Finset.mem_univ k)`.

Establish `hf0 : ∀ a, 0 ≤ f a` using `fun a => div_nonneg (by linarith [hH (i + ((a + 1 : ℕ) : ZMod n))]) (pow_nonneg hq.le _)`. Establish `hsum : Summable f`. Use `Summable.of_nonneg_of_le hf0 (fun a => ?_) ((summable_geometric_of_lt_one (inv_nonneg.mpr hq.le) (inv_lt_one_of_one_lt₀ hq1)).mul_left ((∑ k', H k') + c + 3))` and prove the remaining obligations. Simplify using `only [hf]`. Rewrite using `[inv_pow, ← div_eq_mul_inv]`.

Conclude with `div_le_div_of_nonneg_right (by linarith [hHle (i + ((a + 1 : ℕ) : ZMod n))]) (pow_nonneg hq.le _)`. Establish `hunroll : ∀ N : ℕ, s i ≤ ∑ a ∈ Finset.range N, f a + s (i + (N : ZMod n)) / (ℓ - 1) ^ N`. Introduce `N`. Proceed by induction on `N with`. Consider the case `zero => simp`.

Consider the case `succ N ih`. Establish `hk` using `hs (i + ((N + 1 : ℕ) : ZMod n))`. Establish `e : i + ((N + 1 : ℕ) : ZMod n) - 1 = i + (N : ZMod n)` using `by push_cast; ring`. Rewrite `hk` using `[e]`. Establish `hpos : 0 < (ℓ - 1) ^ N` using `pow_pos hq N`.

Establish `h2 : s (i + (N : ZMod n)) / (ℓ - 1) ^ N ≤ f N + s (i + ((N + 1 : ℕ) : ZMod n)) / (ℓ - 1) ^ (N + 1)`. Establish `h3` using `div_le_div_of_nonneg_right hk hpos.le`. Rewrite `h3` using `[add_div, div_div, ← pow_succ']`. Simplify `h3` using `only [hf]`. Rewrite using `[Finset.sum_range_succ]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hrem : Filter.Tendsto (fun N : ℕ => s (i + (N : ZMod n)) / (ℓ - 1) ^ N) Filter.atTop (nhds 0)`. Use `squeeze_zero_norm (a := fun N => (∑ k, |s k|) * ((ℓ - 1)⁻¹) ^ N) (fun N => ?_) ?_` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hq N), inv_pow, ← div_eq_mul_inv]`. Conclude with `div_le_div_of_nonneg_right (Finset.single_le_sum (f := fun k => |s k|) (fun k _ => abs_nonneg _) (Finset.mem_univ _)) (pow_nonneg hq.le _)`.

Simplify using `using (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hq.le) (inv_lt_one_of_one_lt₀ hq1)).const_mul (∑ k, |s k|)`. Establish `hlim : Filter.Tendsto (fun N : ℕ => s i - s (i + (N : ZMod n)) / (ℓ - 1) ^ N) Filter.atTop (nhds (s i - 0))` using `tendsto_const_nhds.sub hrem`. Establish `hfin` using `le_of_tendsto' hlim (fun N => by`. Establish `h1` using `hunroll N`. Establish `h2` using `hsum.sum_le_tsum (Finset.range N) (fun a _ => hf0 a)`.

Use the proof step `linarith)`. Rewrite `hfin` using `[sub_zero]`. Conclude with `hfin`.
-/
theorem residue_series_expansion_holds : StatResSeries := by
  intro n _ ℓ c s H hℓ hc hH hs i
  have hq : 0 < ℓ - 1 := by linarith
  have hq1 : 1 < ℓ - 1 := by linarith
  set f : ℕ → ℝ := fun a => (H (i + ((a + 1 : ℕ) : ZMod n)) + c + 3) / (ℓ - 1) ^ a with hf
  have hHle : ∀ k, H k ≤ ∑ k', H k' := fun k =>
    Finset.single_le_sum (f := H) (fun k _ => hH k) (Finset.mem_univ k)
  have hf0 : ∀ a, 0 ≤ f a := fun a =>
    div_nonneg (by linarith [hH (i + ((a + 1 : ℕ) : ZMod n))]) (pow_nonneg hq.le _)
  have hsum : Summable f := by
    refine Summable.of_nonneg_of_le hf0 (fun a => ?_)
      ((summable_geometric_of_lt_one (inv_nonneg.mpr hq.le) (inv_lt_one_of_one_lt₀ hq1)).mul_left
        ((∑ k', H k') + c + 3))
    simp only [hf]
    rw [inv_pow, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (by linarith [hHle (i + ((a + 1 : ℕ) : ZMod n))])
      (pow_nonneg hq.le _)
  have hunroll : ∀ N : ℕ, s i ≤ ∑ a ∈ Finset.range N, f a + s (i + (N : ZMod n)) / (ℓ - 1) ^ N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      have hk := hs (i + ((N + 1 : ℕ) : ZMod n))
      have e : i + ((N + 1 : ℕ) : ZMod n) - 1 = i + (N : ZMod n) := by push_cast; ring
      rw [e] at hk
      have hpos : 0 < (ℓ - 1) ^ N := pow_pos hq N
      have h2 : s (i + (N : ZMod n)) / (ℓ - 1) ^ N ≤
          f N + s (i + ((N + 1 : ℕ) : ZMod n)) / (ℓ - 1) ^ (N + 1) := by
        have h3 := div_le_div_of_nonneg_right hk hpos.le
        rw [add_div, div_div, ← pow_succ'] at h3
        simpa only [hf] using h3
      rw [Finset.sum_range_succ]
      linarith
  have hrem : Filter.Tendsto (fun N : ℕ => s (i + (N : ZMod n)) / (ℓ - 1) ^ N) Filter.atTop
      (nhds 0) := by
    refine squeeze_zero_norm (a := fun N => (∑ k, |s k|) * ((ℓ - 1)⁻¹) ^ N) (fun N => ?_) ?_
    · rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hq N), inv_pow, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right (Finset.single_le_sum (f := fun k => |s k|)
        (fun k _ => abs_nonneg _) (Finset.mem_univ _)) (pow_nonneg hq.le _)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hq.le)
        (inv_lt_one_of_one_lt₀ hq1)).const_mul (∑ k, |s k|)
  have hlim : Filter.Tendsto (fun N : ℕ => s i - s (i + (N : ZMod n)) / (ℓ - 1) ^ N)
      Filter.atTop (nhds (s i - 0)) := tendsto_const_nhds.sub hrem
  have hfin := le_of_tendsto' hlim (fun N => by
    have h1 := hunroll N
    have h2 := hsum.sum_le_tsum (Finset.range N) (fun a _ => hf0 a)
    linarith)
  rw [sub_zero] at hfin
  exact hfin

end Formalism.RepresentationBoundsCohomology.N2
