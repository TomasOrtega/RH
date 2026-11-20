import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ReducedBasisStatement
import ReciprocityTheory.ReducedBases.LatticeReduction

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.H1.RB

open Finset InnerProductSpace Submodule Module ReciprocityTheory.ReducedBases.T2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def V {d : ℕ} (u : Fin d → E) (n : ℕ) : Submodule ℝ E := span ℝ (u '' {l | l.val < n})

/- English proof (translation)
Conclude with `Submodule.span_mono (Set.image_mono fun l hl => show l.val < n from lt_of_lt_of_le (show l.val < m from hl) h)`.
-/
lemma V_mono {d : ℕ} (u : Fin d → E) {m n : ℕ} (h : m ≤ n) : V u m ≤ V u n := by
  exact Submodule.span_mono (Set.image_mono fun l hl => show l.val < n from lt_of_lt_of_le (show l.val < m from hl) h)

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `(simp only [V]; congr 1; congr 1; ext l; exact Iff.rfl)`.
-/
lemma V_eq {d : ℕ} (u : Fin d → E) (k : Fin d) : span ℝ (u '' Set.Iio k) = V u k.val := by
  first
  | rfl
  | (simp only [V]; congr 1; congr 1; ext l; exact Iff.rfl)

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨l, h, rfl⟩`.
-/
lemma mem_V_of_lt {d : ℕ} (u : Fin d → E) {l : Fin d} {n : ℕ} (h : l.val < n) : u l ∈ V u n := Submodule.subset_span ⟨l, h, rfl⟩

/- English proof (translation)
Use `haveI : DiscreteTopology X.toAddSubgroup := ‹DiscreteTopology X›`. Establish `hc : IsClosed (X : Set E)` using `AddSubgroup.isClosed_of_discrete (H := X.toAddSubgroup)`. Establish `hdisc : IsDiscrete (X : Set E)` using `by first`. Consider the case `exact ⟨‹DiscreteTopology X›⟩`. Consider the case `exact isDiscrete_iff_discreteTopology.2 ‹DiscreteTopology X›`.

Consider the case `exact ‹DiscreteTopology X›`. Conclude with `Metric.finite_isBounded_inter_isClosed hdisc Metric.isBounded_closedBall hc`.
-/
lemma finite_ball [FiniteDimensional ℝ E] (X : Submodule ℤ E) [DiscreteTopology X] (R : ℝ) :
    (Metric.closedBall (0 : E) R ∩ (X : Set E)).Finite := by
  haveI : DiscreteTopology X.toAddSubgroup := ‹DiscreteTopology X›
  have hc : IsClosed (X : Set E) := AddSubgroup.isClosed_of_discrete (H := X.toAddSubgroup)
  have hdisc : IsDiscrete (X : Set E) := by
    first
    | exact ⟨‹DiscreteTopology X›⟩
    | exact isDiscrete_iff_discreteTopology.2 ‹DiscreteTopology X›
    | exact ‹DiscreteTopology X›
  exact Metric.finite_isBounded_inter_isClosed hdisc Metric.isBounded_closedBall hc

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Set `s` to `Finset.univ.filter (fun l => g l ≠ 0)`.

Establish `hs : s.Nonempty`. Take `⟨i, hi⟩` from `hne`. Conclude with `⟨i, by simp [s, hi]⟩`. Set `k` to `s.max' hs`. Establish `hk : g k ≠ 0`.

Use `s.max'_mem hs` as an intermediate fact. Simplify `this` using `[s]`. Establish `hgt : ∀ l, k < l → g l = 0`. Introduce `l hl`. Assume the negation of the conclusion as `h0`.

Conclude with `absurd (s.le_max' l (by simp [s, h0])) (not_le.2 hl)`. Establish `hsplit : ∀ l, g l • f l = (if l = k then g k • f k else 0) + (if l < k then g l • f l else 0)`. Introduce `l`. Break down `lt_trichotomy l k with h1 | h1 | h1` into its components or cases. Simplify using `[h1, h1.ne]`.

Rewrite using `[h1]`. Simplify using the standard rewrite rules. Simplify using `[hgt l h1, h1.ne', not_lt.2 h1.le]`. Establish `h2 : g k • f k + ∑ l ∈ Finset.univ.filter (· < k), g l • f l = 0`. Establish `e : ∑ l, g l • f l = g k • f k + ∑ l ∈ Finset.univ.filter (· < k), g l • f l`.

Rewrite using `[Finset.sum_congr (s₁ := Finset.univ) rfl (fun l _ => hsplit l), Finset.sum_add_distrib, Finset.sum_filter]`. Simplify using the standard rewrite rules. Rewrite using `[← e]`. Conclude with `hg`. Establish `hmem : g k • f k ∈ V f k.val`.

Rewrite using `[eq_neg_of_add_eq_zero_left h2]`. Use `Submodule.neg_mem _ (_root_.sum_mem fun l hl => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, ?_, rfl⟩))` and prove the remaining obligations. Establish `hl' : l < k` using `by simpa using hl`. Conclude with `Fin.lt_iff_val_lt_val.1 hl'`. Establish `h3` using `Submodule.smul_mem (V f k.val) (g k)⁻¹ hmem`.

Rewrite `h3` using `[smul_smul, inv_mul_cancel₀ hk, one_smul]`. Conclude with `h k h3`.
-/
lemma indep_of_flag [FiniteDimensional ℝ E] {d : ℕ} (hd : d = finrank ℝ E) (f : Fin d → E)
    (h : ∀ k, f k ∉ V f k.val) : LinearIndependent ℝ f := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  push_neg at hne
  let s := Finset.univ.filter (fun l => g l ≠ 0)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, by simp [s, hi]⟩
  let k := s.max' hs
  have hk : g k ≠ 0 := by
    have := s.max'_mem hs
    simpa [s] using this
  have hgt : ∀ l, k < l → g l = 0 := by
    intro l hl
    by_contra h0
    exact absurd (s.le_max' l (by simp [s, h0])) (not_le.2 hl)
  have hsplit : ∀ l, g l • f l =
      (if l = k then g k • f k else 0) + (if l < k then g l • f l else 0) := by
    intro l
    rcases lt_trichotomy l k with h1 | h1 | h1
    · simp [h1, h1.ne]
    · rw [h1]; simp
    · simp [hgt l h1, h1.ne', not_lt.2 h1.le]
  have h2 : g k • f k + ∑ l ∈ Finset.univ.filter (· < k), g l • f l = 0 := by
    have e : ∑ l, g l • f l = g k • f k + ∑ l ∈ Finset.univ.filter (· < k), g l • f l := by
      rw [Finset.sum_congr (s₁ := Finset.univ) rfl (fun l _ => hsplit l), Finset.sum_add_distrib,
        Finset.sum_filter]
      simp
    rw [← e]
    exact hg
  have hmem : g k • f k ∈ V f k.val := by
    rw [eq_neg_of_add_eq_zero_left h2]
    refine Submodule.neg_mem _ (_root_.sum_mem fun l hl => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, ?_, rfl⟩))
    have hl' : l < k := by simpa using hl
    exact Fin.lt_iff_val_lt_val.1 hl'
  have h3 := Submodule.smul_mem (V f k.val) (g k)⁻¹ hmem
  rw [smul_smul, inv_mul_cancel₀ hk, one_smul] at h3
  exact h k h3

def phi {d : ℕ} (u : Fin d → E) (k : Fin d) (x : E) : ℝ := ⟪gs u k, x⟫_ℝ / ‖gs u k‖ ^ 2

section phi
variable {d : ℕ} (u : Fin d → E) (k : Fin d)

/- English proof (translation)
Simplify using `only [phi, inner_add_right, add_div]`.
-/
lemma phi_add (x y : E) : phi u k (x + y) = phi u k x + phi u k y := by
  simp only [phi, inner_add_right, add_div]

/- English proof (translation)
Simplify using `only [phi, inner_sub_right, sub_div]`.
-/
lemma phi_sub (x y : E) : phi u k (x - y) = phi u k x - phi u k y := by
  simp only [phi, inner_sub_right, sub_div]

/- English proof (translation)
Simplify using `only [phi, real_inner_smul_right, mul_div_assoc]`.
-/
lemma phi_smul (a : ℝ) (x : E) : phi u k (a • x) = a * phi u k x := by
  simp only [phi, real_inner_smul_right, mul_div_assoc]

/- English proof (translation)
Establish `hx' : x ∈ span ℝ (gramSchmidt ℝ u '' Set.Iio k)`. Rewrite using `[span_gramSchmidt_Iio, V_eq]`. Conclude with `hx`. Establish `hle : span ℝ (gramSchmidt ℝ u '' Set.Iio k) ≤ (ℝ ∙ gramSchmidt ℝ u k)ᗮ`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨j, hj, rfl⟩`. Rewrite using `[SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]`. Conclude with `gramSchmidt_orthogonal ℝ u (ne_of_gt hj)`. Conclude with `Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hx')`.
-/
private lemma inner_gs_eq_zero_of_mem_V {x : E} (hx : x ∈ V u k.val) : ⟪gs u k, x⟫_ℝ = 0 := by
  have hx' : x ∈ span ℝ (gramSchmidt ℝ u '' Set.Iio k) := by
    rw [span_gramSchmidt_Iio, V_eq]
    exact hx
  have hle : span ℝ (gramSchmidt ℝ u '' Set.Iio k) ≤ (ℝ ∙ gramSchmidt ℝ u k)ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact gramSchmidt_orthogonal ℝ u (ne_of_gt hj)
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hx')

/- English proof (translation)
Simplify using `[phi, inner_gs_eq_zero_of_mem_V u k hx]`.
-/
lemma phi_V {x : E} (hx : x ∈ V u k.val) : phi u k x = 0 := by
  simp [phi, inner_gs_eq_zero_of_mem_V u k hx]

/- English proof (translation)
Rewrite using `[← V_eq, ← span_gramSchmidt_Iio ℝ u k]`. Use `show u k - gramSchmidt ℝ u k ∈ span ℝ (gramSchmidt ℝ u '' Set.Iio k)`. Rewrite using `[gramSchmidt_def ℝ u k, sub_sub_cancel]`. Use `_root_.sum_mem fun i hi => ?_` and prove the remaining obligations. Establish `hsub : (ℝ ∙ gramSchmidt ℝ u i) ≤ span ℝ (gramSchmidt ℝ u '' Set.Iio k)` using `Submodule.span_mono (Set.singleton_subset_iff.2 ⟨i, Finset.mem_Iio.1 hi, rfl⟩)`.

Apply `hsub` to reduce the goal to its premises. Use `first`. Consider the case `exact Submodule.starProjection_apply_mem _ _`. Consider the case `(rw [Submodule.starProjection_apply]; exact Submodule.coe_mem _)`. Consider the case `simp`.
-/
private lemma sub_gs_mem_V : u k - gs u k ∈ V u k.val := by
  rw [← V_eq, ← span_gramSchmidt_Iio ℝ u k]
  show u k - gramSchmidt ℝ u k ∈ span ℝ (gramSchmidt ℝ u '' Set.Iio k)
  rw [gramSchmidt_def ℝ u k, sub_sub_cancel]
  refine _root_.sum_mem fun i hi => ?_
  have hsub : (ℝ ∙ gramSchmidt ℝ u i) ≤ span ℝ (gramSchmidt ℝ u '' Set.Iio k) :=
    Submodule.span_mono (Set.singleton_subset_iff.2 ⟨i, Finset.mem_Iio.1 hi, rfl⟩)
  apply hsub
  first
  | exact Submodule.starProjection_apply_mem _ _
  | (rw [Submodule.starProjection_apply]; exact Submodule.coe_mem _)
  | simp

/- English proof (translation)
Establish `hne : gs u k ≠ 0` using `by first`. Consider the case `exact gramSchmidt_ne_zero ℝ k hu`. Consider the case `exact gramSchmidt_ne_zero k hu`. Consider the case `exact gramSchmidt_ne_zero (𝕜 := ℝ) (n := k) hu`. Establish `h1 : phi u k (u k) = phi u k (gs u k) + phi u k (u k - gs u k)`.

Rewrite using `[← phi_add]`. Use `congr 1`. Normalize the expressions using the abelian group laws. Rewrite using `[h1, phi_V u k (sub_gs_mem_V u k), add_zero, phi, real_inner_self_eq_norm_sq, div_self (pow_ne_zero 2 (norm_ne_zero_iff.2 hne))]`.
-/
lemma phi_self (hu : LinearIndependent ℝ u) : phi u k (u k) = 1 := by
  have hne : gs u k ≠ 0 := by
    first
    | exact gramSchmidt_ne_zero ℝ k hu
    | exact gramSchmidt_ne_zero k hu
    | exact gramSchmidt_ne_zero (𝕜 := ℝ) (n := k) hu
  have h1 : phi u k (u k) = phi u k (gs u k) + phi u k (u k - gs u k) := by
    rw [← phi_add]; congr 1; abel
  rw [h1, phi_V u k (sub_gs_mem_V u k), add_zero, phi, real_inner_self_eq_norm_sq,
    div_self (pow_ne_zero 2 (norm_ne_zero_iff.2 hne))]

/- English proof (translation)
Establish `h : phi u k (∑ l, a l • u l) = ∑ l, a l * phi u k (u l)`. Simplify using `only [phi, inner_sum, real_inner_smul_right, Finset.sum_div, mul_div_assoc]`. Rewrite using `[h, Finset.sum_eq_single k]`. Rewrite using `[phi_self u k hu, mul_one]`. Introduce `l _ hlk`.

Break down `lt_or_gt_of_ne hlk with h1 | h1` into its components or cases. Rewrite using `[phi_V u k (mem_V_of_lt u (Fin.lt_iff_val_lt_val.1 h1)), mul_zero]`. Rewrite using `[ha l h1, zero_mul]`. Simplify using the standard rewrite rules.
-/
lemma phi_comb (hu : LinearIndependent ℝ u) (a : Fin d → ℝ) (ha : ∀ l, k < l → a l = 0) :
    phi u k (∑ l, a l • u l) = a k := by
  have h : phi u k (∑ l, a l • u l) = ∑ l, a l * phi u k (u l) := by
    simp only [phi, inner_sum, real_inner_smul_right, Finset.sum_div, mul_div_assoc]
  rw [h, Finset.sum_eq_single k]
  · rw [phi_self u k hu, mul_one]
  · intro l _ hlk
    rcases lt_or_gt_of_ne hlk with h1 | h1
    · rw [phi_V u k (mem_V_of_lt u (Fin.lt_iff_val_lt_val.1 h1)), mul_zero]
    · rw [ha l h1, zero_mul]
  · simp

/- English proof (translation)
Rewrite `hx` using `[V, Finsupp.mem_span_image_iff_linearCombination]`. Take `⟨c, hc, rfl⟩` from `hx`. Use `⟨c, fun l hl => ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Use `(Finsupp.mem_supported ℝ c).1 hc (Finsupp.mem_support_iff.2 h)` as an intermediate fact.

Conclude with `absurd this (not_lt.2 hl)`. Rewrite using `[Finsupp.linearCombination_apply, Finsupp.sum_fintype]`. Introduce `i`. Conclude with `zero_smul _ _`.
-/
private lemma exists_coeffs_of_mem_V {d : ℕ} (u : Fin d → E) {n : ℕ} {x : E} (hx : x ∈ V u n) :
    ∃ c : Fin d → ℝ, (∀ l : Fin d, n ≤ l.val → c l = 0) ∧ x = ∑ l, c l • u l := by
  rw [V, Finsupp.mem_span_image_iff_linearCombination] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  refine ⟨c, fun l hl => ?_, ?_⟩
  · by_contra h
    have := (Finsupp.mem_supported ℝ c).1 hc (Finsupp.mem_support_iff.2 h)
    exact absurd this (not_lt.2 hl)
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i
    exact zero_smul _ _

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `exists_coeffs_of_mem_V u hx`. Rewrite using `[phi_comb u k hu c (fun l hl => hc l (Fin.lt_iff_val_lt_val.1 hl))]`. Rewrite using `[← Finset.add_sum_erase _ _ (Finset.mem_univ k), add_sub_cancel_left]`. Use `_root_.sum_mem fun l hl => ?_` and prove the remaining obligations. Establish `hlk : l ≠ k` using `Finset.ne_of_mem_erase hl`.

Break down `lt_or_gt_of_ne hlk with h1 | h1` into its components or cases. Conclude with `Submodule.smul_mem _ _ (mem_V_of_lt u (Fin.lt_iff_val_lt_val.1 h1))`. Rewrite using `[hc l (Fin.lt_iff_val_lt_val.1 h1), zero_smul]`. Conclude with `Submodule.zero_mem _`.
-/
lemma decomp (hu : LinearIndependent ℝ u) {x : E} (hx : x ∈ V u (k.val + 1)) :
    x - phi u k x • u k ∈ V u k.val := by
  obtain ⟨c, hc, rfl⟩ := exists_coeffs_of_mem_V u hx
  rw [phi_comb u k hu c (fun l hl => hc l (Fin.lt_iff_val_lt_val.1 hl))]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), add_sub_cancel_left]
  refine _root_.sum_mem fun l hl => ?_
  have hlk : l ≠ k := Finset.ne_of_mem_erase hl
  rcases lt_or_gt_of_ne hlk with h1 | h1
  · exact Submodule.smul_mem _ _ (mem_V_of_lt u (Fin.lt_iff_val_lt_val.1 h1))
  · rw [hc l (Fin.lt_iff_val_lt_val.1 h1), zero_smul]
    exact Submodule.zero_mem _

end phi

/- English proof (translation)
The claim follows from `exists_coeffs_of_mem_V u hx`.
-/
lemma exists_coeffs {d : ℕ} (u : Fin d → E) {n : ℕ} {x : E} (hx : x ∈ V u n) :
    ∃ c : Fin d → ℝ, (∀ l : Fin d, n ≤ l.val → c l = 0) ∧ x = ∑ l, c l • u l := exists_coeffs_of_mem_V u hx

/- English proof (translation)
Establish `h' : ⟪a, g⟫_ℝ = 0` using `by rw [real_inner_comm]; exact h`. Rewrite using `[norm_add_sq_real, real_inner_smul_right, h', mul_zero, mul_zero, add_zero, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]`.
-/
private lemma norm_add_smul_sq_of_real_inner_eq_zero (a g : E) (t : ℝ) (h : ⟪g, a⟫_ℝ = 0) :
    ‖a + t • g‖ ^ 2 = ‖a‖ ^ 2 + t ^ 2 * ‖g‖ ^ 2 := by
  have h' : ⟪a, g⟫_ℝ = 0 := by rw [real_inner_comm]; exact h
  rw [norm_add_sq_real, real_inner_smul_right, h', mul_zero, mul_zero, add_zero, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs]

/- English proof (translation)
Establish `h` using `norm_add_smul_sq_of_real_inner_eq_zero (u k - gs u k) (gs u k) 1 (inner_gs_eq_zero_of_mem_V u k (sub_gs_mem_V u k))`. Rewrite `h` using `[one_smul, sub_add_cancel, one_pow, one_mul]`. Rewrite using `[h]`. Use polynomial arithmetic with `[sq_nonneg ‖u k - gs u k‖]`.
-/
private lemma norm_gs_sq_le_norm_sq {d : ℕ} (u : Fin d → E) (k : Fin d) : ‖gs u k‖ ^ 2 ≤ ‖u k‖ ^ 2 := by
  have h := norm_add_smul_sq_of_real_inner_eq_zero (u k - gs u k) (gs u k) 1 (inner_gs_eq_zero_of_mem_V u k (sub_gs_mem_V u k))
  rw [one_smul, sub_add_cancel, one_pow, one_mul] at h
  rw [h]
  nlinarith [sq_nonneg ‖u k - gs u k‖]

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `_ w hw`. Use `⟨0, X.zero_mem, Submodule.zero_mem _, ?_⟩` and prove the remaining obligations.

Establish `h0 : V u 0 = ⊥` using `by simp [V]`. Rewrite `hw` using `[h0, Submodule.mem_bot]`. Simplify using `[hw]`. Consider the case `succ n ih`. Introduce `hn w hw`.

Establish `hjn : n < d` using `by omega`. Set `j : Fin d` to `⟨n, hjn⟩`. Take `⟨m, hm⟩ : ∃ m : ℤ, |phi u j w - m| ≤ 1` from `⟨round (phi u j w), by have := abs_sub_round (phi u j w); linarith⟩`. Establish `hw1 : w - (m : ℝ) • u j ∈ V u (j.val + 1)` using `Submodule.sub_mem _ hw (Submodule.smul_mem _ _ (mem_V_of_lt u (Nat.lt_succ_self n)))`. Establish `ht : phi u j (w - (m : ℝ) • u j) = phi u j w - m`.

Rewrite using `[phi_sub, phi_smul, phi_self u j hu, mul_one]`. Establish `hw2 : w - (m : ℝ) • u j - phi u j (w - (m : ℝ) • u j) • gs u j ∈ V u n`. Establish `h1` using `decomp u j hu hw1`. Establish `h2 : phi u j (w - (m : ℝ) • u j) • (u j - gs u j) ∈ V u n` using `Submodule.smul_mem _ _ (sub_gs_mem_V u j)`. Establish `h3` using `Submodule.add_mem _ h1 h2`.

Establish `h4 : w - (m : ℝ) • u j - phi u j (w - (m : ℝ) • u j) • gs u j = (w - (m : ℝ) • u j - phi u j (w - (m : ℝ) • u j) • u j) + phi u j (w - (m : ℝ) • u j) • (u j - gs u j)`. Rewrite using `[smul_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[h4]`. Conclude with `h3`.

Take `⟨z, hzX, hzV, hz⟩` from `ih (by omega) _ hw2`. Use `⟨(m : ℝ) • u j + z, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Int.cast_smul_eq_zsmul]`. Conclude with `X.add_mem (X.smul_mem m (hX j)) hzX`. Conclude with `Submodule.add_mem _ (Submodule.smul_mem _ _ (mem_V_of_lt u (Nat.lt_succ_self n))) (V_mono u (Nat.le_succ n) hzV)`.

Establish `hsplit : w - ((m : ℝ) • u j + z) = (w - (m : ℝ) • u j - phi u j (w - (m : ℝ) • u j) • gs u j - z) + phi u j (w - (m : ℝ) • u j) • gs u j` using `by abel`. Establish `horth : ⟪gs u j, w - (m : ℝ) • u j - phi u j (w - (m : ℝ) • u j) • gs u j - z⟫_ℝ = 0` using `inner_gs_eq_zero_of_mem_V u j (Submodule.sub_mem _ hw2 hzV)`. Rewrite using `[hsplit, norm_add_smul_sq_of_real_inner_eq_zero _ _ _ horth]`. Establish `ht2 : phi u j (w - (m : ℝ) • u j) ^ 2 ≤ 1`. Rewrite using `[ht]`.

Use `abs_le.1 hm` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hMj : ‖u j‖ ^ 2 ≤ M` using `hM j (show n < N by omega)`. Establish `hprod : phi u j (w - (m : ℝ) • u j) ^ 2 * ‖gs u j‖ ^ 2 ≤ 1 * M` using `mul_le_mul ht2 ((norm_gs_sq_le_norm_sq u j).trans hMj) (by positivity) zero_le_one`. Use `push_cast`.

Use the polynomial consequences of the given equalities and inequalities.
-/
private lemma exists_lattice_mem_V_norm_sub_sq_le {d : ℕ} (u : Fin d → E) (hu : LinearIndependent ℝ u) (X : Submodule ℤ E)
    (hX : ∀ l, u l ∈ X) (M : ℝ) (N : ℕ) (hN : N ≤ d) (hM : ∀ j : Fin d, j.val < N → ‖u j‖ ^ 2 ≤ M) :
    ∀ n : ℕ, n ≤ N → ∀ w ∈ V u n, ∃ z ∈ X, z ∈ V u n ∧ ‖w - z‖ ^ 2 ≤ n * M := by
  intro n
  induction n with
  | zero =>
    intro _ w hw
    refine ⟨0, X.zero_mem, Submodule.zero_mem _, ?_⟩
    have h0 : V u 0 = ⊥ := by simp [V]
    rw [h0, Submodule.mem_bot] at hw
    simp [hw]
  | succ n ih =>
    intro hn w hw
    have hjn : n < d := by omega
    let j : Fin d := ⟨n, hjn⟩
    obtain ⟨m, hm⟩ : ∃ m : ℤ, |phi u j w - m| ≤ 1 :=
      ⟨round (phi u j w), by have := abs_sub_round (phi u j w); linarith⟩
    have hw1 : w - (m : ℝ) • u j ∈ V u (j.val + 1) :=
      Submodule.sub_mem _ hw (Submodule.smul_mem _ _ (mem_V_of_lt u (Nat.lt_succ_self n)))
    have ht : phi u j (w - (m : ℝ) • u j) = phi u j w - m := by
      rw [phi_sub, phi_smul, phi_self u j hu, mul_one]
    have hw2 : w - (m : ℝ) • u j - phi u j (w - (m : ℝ) • u j) • gs u j ∈ V u n := by
      have h1 := decomp u j hu hw1
      have h2 : phi u j (w - (m : ℝ) • u j) • (u j - gs u j) ∈ V u n :=
        Submodule.smul_mem _ _ (sub_gs_mem_V u j)
      have h3 := Submodule.add_mem _ h1 h2
      have h4 : w - (m : ℝ) • u j - phi u j (w - (m : ℝ) • u j) • gs u j =
          (w - (m : ℝ) • u j - phi u j (w - (m : ℝ) • u j) • u j) +
            phi u j (w - (m : ℝ) • u j) • (u j - gs u j) := by
        rw [smul_sub]; abel
      rw [h4]; exact h3
    obtain ⟨z, hzX, hzV, hz⟩ := ih (by omega) _ hw2
    refine ⟨(m : ℝ) • u j + z, ?_, ?_, ?_⟩
    · rw [Int.cast_smul_eq_zsmul]
      exact X.add_mem (X.smul_mem m (hX j)) hzX
    · exact Submodule.add_mem _ (Submodule.smul_mem _ _ (mem_V_of_lt u (Nat.lt_succ_self n)))
        (V_mono u (Nat.le_succ n) hzV)
    · have hsplit : w - ((m : ℝ) • u j + z) =
          (w - (m : ℝ) • u j - phi u j (w - (m : ℝ) • u j) • gs u j - z) +
            phi u j (w - (m : ℝ) • u j) • gs u j := by abel
      have horth : ⟪gs u j, w - (m : ℝ) • u j - phi u j (w - (m : ℝ) • u j) • gs u j - z⟫_ℝ = 0 :=
        inner_gs_eq_zero_of_mem_V u j (Submodule.sub_mem _ hw2 hzV)
      rw [hsplit, norm_add_smul_sq_of_real_inner_eq_zero _ _ _ horth]
      have ht2 : phi u j (w - (m : ℝ) • u j) ^ 2 ≤ 1 := by
        rw [ht]
        have := abs_le.1 hm
        nlinarith
      have hMj : ‖u j‖ ^ 2 ≤ M := hM j (show n < N by omega)
      have hprod : phi u j (w - (m : ℝ) • u j) ^ 2 * ‖gs u j‖ ^ 2 ≤ 1 * M :=
        mul_le_mul ht2 ((norm_gs_sq_le_norm_sq u j).trans hMj) (by positivity) zero_le_one
      push_cast
      nlinarith

/- English proof (translation)
Establish `hkd : k.val < d` using `k.isLt`. Establish `hM : ∀ j : Fin d, j.val < k.val → ‖u j‖ ^ 2 ≤ ‖u k‖ ^ 2` using `fun j hj => pow_le_pow_left₀ (norm_nonneg _) (hmono j (Fin.lt_iff_val_lt_val.2 hj)) 2`. Establish `hw2 : x - phi u k x • gs u k ∈ V u k.val`. Establish `h1` using `decomp u k hu hxV`. Establish `h2 : phi u k x • (u k - gs u k) ∈ V u k.val` using `Submodule.smul_mem _ _ (sub_gs_mem_V u k)`.

Establish `h3 : x - phi u k x • gs u k = (x - phi u k x • u k) + phi u k x • (u k - gs u k)`. Rewrite using `[smul_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[h3]`. Conclude with `Submodule.add_mem _ h1 h2`.

Take `⟨z, hzX, hzV, hz⟩` from `exists_lattice_mem_V_norm_sub_sq_le u hu X hX (‖u k‖ ^ 2) k.val hkd.le hM k.val le_rfl _ hw2`. Use `⟨x - z, X.sub_mem hxX hzX, Submodule.sub_mem _ hxV (V_mono u (Nat.le_succ _) hzV), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[phi_sub, phi_V u k hzV, sub_zero]`. Establish `hsplit : x - z = (x - phi u k x • gs u k - z) + phi u k x • gs u k` using `by abel`. Rewrite using `[hsplit, norm_add_smul_sq_of_real_inner_eq_zero _ _ _ (inner_gs_eq_zero_of_mem_V u k (Submodule.sub_mem _ hw2 hzV))]`.

Establish `hp2 : phi u k x ^ 2 ≤ 1`. Use `abs_le.1 hphi` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hprod : phi u k x ^ 2 * ‖gs u k‖ ^ 2 ≤ 1 * ‖u k‖ ^ 2` using `mul_le_mul hp2 (norm_gs_sq_le_norm_sq u k) (by positivity) zero_le_one`. Establish `hd : (k.val : ℝ) + 1 ≤ d` using `by exact_mod_cast hkd`.

Establish `hu0 : 0 ≤ ‖u k‖ ^ 2` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma reduce {d : ℕ} (u : Fin d → E) (hu : LinearIndependent ℝ u) (X : Submodule ℤ E)
    (hX : ∀ l, u l ∈ X) (k : Fin d) (hmono : ∀ j : Fin d, j < k → ‖u j‖ ≤ ‖u k‖) {x : E}
    (hxX : x ∈ X) (hxV : x ∈ V u (k.val + 1)) (hphi : |phi u k x| ≤ 1) :
    ∃ y ∈ X, y ∈ V u (k.val + 1) ∧ phi u k y = phi u k x ∧ ‖y‖ ^ 2 ≤ d * ‖u k‖ ^ 2 := by
  have hkd : k.val < d := k.isLt
  have hM : ∀ j : Fin d, j.val < k.val → ‖u j‖ ^ 2 ≤ ‖u k‖ ^ 2 := fun j hj =>
    pow_le_pow_left₀ (norm_nonneg _) (hmono j (Fin.lt_iff_val_lt_val.2 hj)) 2
  have hw2 : x - phi u k x • gs u k ∈ V u k.val := by
    have h1 := decomp u k hu hxV
    have h2 : phi u k x • (u k - gs u k) ∈ V u k.val :=
      Submodule.smul_mem _ _ (sub_gs_mem_V u k)
    have h3 : x - phi u k x • gs u k = (x - phi u k x • u k) + phi u k x • (u k - gs u k) := by
      rw [smul_sub]; abel
    rw [h3]; exact Submodule.add_mem _ h1 h2
  obtain ⟨z, hzX, hzV, hz⟩ :=
    exists_lattice_mem_V_norm_sub_sq_le u hu X hX (‖u k‖ ^ 2) k.val hkd.le hM k.val le_rfl _ hw2
  refine ⟨x - z, X.sub_mem hxX hzX, Submodule.sub_mem _ hxV (V_mono u (Nat.le_succ _) hzV), ?_, ?_⟩
  · rw [phi_sub, phi_V u k hzV, sub_zero]
  · have hsplit : x - z = (x - phi u k x • gs u k - z) + phi u k x • gs u k := by abel
    rw [hsplit, norm_add_smul_sq_of_real_inner_eq_zero _ _ _ (inner_gs_eq_zero_of_mem_V u k (Submodule.sub_mem _ hw2 hzV))]
    have hp2 : phi u k x ^ 2 ≤ 1 := by
      have := abs_le.1 hphi
      nlinarith
    have hprod : phi u k x ^ 2 * ‖gs u k‖ ^ 2 ≤ 1 * ‖u k‖ ^ 2 :=
      mul_le_mul hp2 (norm_gs_sq_le_norm_sq u k) (by positivity) zero_le_one
    have hd : (k.val : ℝ) + 1 ≤ d := by exact_mod_cast hkd
    have hu0 : 0 ≤ ‖u k‖ ^ 2 := by positivity
    nlinarith

end ReciprocityTheory.ChartRestriction.G.H1.RB
