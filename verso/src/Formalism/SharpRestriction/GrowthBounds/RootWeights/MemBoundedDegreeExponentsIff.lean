import Formalism.SharpRestriction.GrowthBounds.RootWeights.PadicGeMulNat

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

/- English proof (translation)
Establish `h` using `shift_eq_sum_fwdDiff_iter (1 : ℕ) f m 0`. Simplify using `only [zero_add, smul_eq_mul, mul_one, nsmul_eq_mul] at h`. Rewrite using `[h]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mah, mul_comm]`.
-/
theorem asm_newton (f : ℕ → ℚ) (m : ℕ) :
    f m = ∑ j ∈ range (m + 1), mah f j * (m.choose j : ℚ) := by
  have h := shift_eq_sum_fwdDiff_iter (1 : ℕ) f m 0
  simp only [zero_add, smul_eq_mul, mul_one, nsmul_eq_mul] at h
  rw [h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mah, mul_comm]

/- English proof (translation)
Apply `Finset.sum_subset` to reduce the goal to its premises. Introduce `j hj`. Simplify using `only [Finset.mem_range] at *`. Use linear arithmetic over natural numbers and integers. Introduce `j hj hj'`.

Simplify using `only [Finset.mem_range] at *`. Rewrite using `[Nat.choose_eq_zero_of_lt (by omega)]`. Simplify using the standard rewrite rules.
-/
private theorem ext_lemma (a : ℕ → ℚ) (m N : ℕ) (h : m < N) :
    ∑ j ∈ range (m + 1), a j * (m.choose j : ℚ) = ∑ j ∈ range N, a j * (m.choose j : ℚ) := by
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_range] at *
    omega
  · intro j hj hj'
    simp only [Finset.mem_range] at *
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

/- English proof (translation)
Rewrite using `[asm_newton f m]`. Conclude with `ext_lemma (mah f) m B h`.
-/
theorem asm_newton_big (f : ℕ → ℚ) (m B : ℕ) (h : m < B) :
    f m = ∑ j ∈ range B, mah f j * (m.choose j : ℚ) := by
  rw [asm_newton f m]
  exact ext_lemma (mah f) m B h

/- English proof (translation)
Use `show (1 : ℚ) = 0 ∨ (0 : ℝ) ≤ (padicValRat p 1 : ℝ)`. Use `right`. Simplify using `[padicValRat.one]`.
-/
theorem asm_padicGe_one {p : ℕ} [Fact p.Prime] : PadicGe p 1 0 := by
  show (1 : ℚ) = 0 ∨ (0 : ℝ) ≤ (padicValRat p 1 : ℝ)
  right
  simp [padicValRat.one]

/- English proof (translation)
Use `revert h`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Introduce `_`. Simplify using `using (asm_padicGe_one (p := p))`. Introduce `a s ha ih h`.

Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha]`. Conclude with `padicGe_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem asm_padicGe_prod {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι) (g : ι → ℚ) (r : ι → ℝ)
    (h : ∀ i ∈ s, PadicGe p (g i) (r i)) : PadicGe p (∏ i ∈ s, g i) (∑ i ∈ s, r i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using (asm_padicGe_one (p := p))
  · intro a s ha ih h
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact padicGe_mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

open Classical in

def boundedDegreeExponents (σ : Type*) [Fintype σ] (c : ℕ) : Finset (σ → ℕ) :=
  (Fintype.piFinset fun _ : σ => range (4 * c + 1)).filter fun j => ∑ k, j k ≤ 4 * c

/- English proof (translation)
Unfold `boundedDegreeExponents`. Rewrite using `[Finset.mem_filter, Fintype.mem_piFinset]`. Prove the components needed by the constructor for the conclusion. Conclude with `fun h => h.2`. Introduce `h`.

Use `⟨fun k => ?_, h⟩` and prove the remaining obligations. Rewrite using `[Finset.mem_range]`. Use `Finset.single_le_sum (fun i _ => Nat.zero_le (j i)) (Finset.mem_univ k)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem mem_bounded_degree_exponents_iff {σ : Type*} [Fintype σ] {c : ℕ} {j : σ → ℕ} : j ∈ boundedDegreeExponents σ c ↔ ∑ k, j k ≤ 4 * c := by
  classical
  unfold boundedDegreeExponents
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun k => ?_, h⟩
    rw [Finset.mem_range]
    have := Finset.single_le_sum (fun i _ => Nat.zero_le (j i)) (Finset.mem_univ k)
    omega

/- English proof (translation)
Establish `h` using `asm_padicGe_prod Finset.univ (fun k => mah (f k) (j k)) (fun k => (1 / 4 : ℝ) * (j k : ℝ) + 0) (fun k _ => hf k (j k))`. Use `padicGe_mono h (le_of_eq ?_)` and prove the remaining obligations. Use `push_cast`. Rewrite using `[Finset.sum_div]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`.
-/
theorem asm_q_ge {p : ℕ} [Fact p.Prime] {σ : Type*} [Fintype σ] (f : σ → ℕ → ℚ)
    (hf : ∀ k, Dec p (1 / 4) 0 (f k)) (j : σ → ℕ) :
    PadicGe p (∏ k, mah (f k) (j k)) (((∑ k, j k : ℕ) : ℝ) / 4) := by
  have h := asm_padicGe_prod Finset.univ (fun k => mah (f k) (j k))
    (fun k => (1 / 4 : ℝ) * (j k : ℝ) + 0) (fun k _ => hf k (j k))
  refine padicGe_mono h (le_of_eq ?_)
  push_cast
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun k _ => by ring

/- English proof (translation)
Take `⟨B, hB1, hB2⟩ : ∃ B : ℕ, 4 * c < B ∧ ∀ k, x k < B` from `⟨4 * c + 1 + ∑ k, x k, by omega, fun k => by`. Use `Finset.single_le_sum (fun i _ => Nat.zero_le (x i)) (Finset.mem_univ k)` as an intermediate fact. Use the proof step `omega⟩`. Establish `hexp : ∏ k, f k (x k) = ∑ j ∈ Fintype.piFinset (fun _ : σ => range B), ∏ k, (mah (f k) (j k) * ((x k).choose (j k) : ℚ))`. Use `(Finset.prod_congr rfl fun k _ => asm_newton_big (f k) (x k) B (hB2 k)).trans ?_` and prove the remaining obligations.

Conclude with `Finset.prod_univ_sum (fun _ : σ => range B) (fun k j => mah (f k) j * ((x k).choose j : ℚ))`. Establish `hsub : boundedDegreeExponents σ c ⊆ Fintype.piFinset (fun _ : σ => range B)`. Introduce `j hj`. Rewrite `hj` using `[mem_bounded_degree_exponents_iff]`. Rewrite using `[Fintype.mem_piFinset]`.

Introduce `k`. Rewrite using `[Finset.mem_range]`. Use `Finset.single_le_sum (fun i _ => Nat.zero_le (j i)) (Finset.mem_univ k)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hT : ∑ j ∈ boundedDegreeExponents σ c, (∏ k, mah (f k) (j k)) * ∏ k, ((x k).choose (j k) : ℚ) = ∑ j ∈ boundedDegreeExponents σ c, ∏ k, (mah (f k) (j k) * ((x k).choose (j k) : ℚ))` using `Finset.sum_congr rfl fun j _ => Finset.prod_mul_distrib.symm`.

Rewrite using `[hT, hexp, ← Finset.sum_sdiff hsub, add_sub_cancel_right]`. Apply `padicGe_sum` to reduce the goal to its premises. Introduce `j hj`. Rewrite `hj` using `[Finset.mem_sdiff, mem_bounded_degree_exponents_iff]`. Establish `h1` using `asm_padicGe_prod Finset.univ (fun k => mah (f k) (j k) * ((x k).choose (j k) : ℚ)) (fun k => (1 / 4 : ℝ) * (j k : ℝ) + 0) (fun k _ => padicGe_mul_nat (hf k (j k)) _)`.

Use `padicGe_mono h1 ?_` and prove the remaining obligations. Establish `hs : (∑ k, ((1 / 4 : ℝ) * (j k : ℝ) + 0)) = ((∑ k, j k : ℕ) : ℝ) / 4`. Use `push_cast`. Rewrite using `[Finset.sum_div]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`.

Rewrite using `[hs]`. Establish `hlt : 4 * c < ∑ k, j k` using `not_le.mp hj.2`. Establish `: ((4 * c : ℕ) : ℝ) < ((∑ k, j k : ℕ) : ℝ)` using `by exact_mod_cast hlt`. Move the coercions through the operations in `at this ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem asm_multi {p : ℕ} [Fact p.Prime] {σ : Type*} [Fintype σ] (f : σ → ℕ → ℚ)
    (hf : ∀ k, Dec p (1 / 4) 0 (f k)) (c : ℕ) (x : σ → ℕ) :
    PadicGe p (∏ k, f k (x k) -
      ∑ j ∈ boundedDegreeExponents σ c, (∏ k, mah (f k) (j k)) * ∏ k, ((x k).choose (j k) : ℚ)) c := by
  classical
  obtain ⟨B, hB1, hB2⟩ : ∃ B : ℕ, 4 * c < B ∧ ∀ k, x k < B :=
    ⟨4 * c + 1 + ∑ k, x k, by omega, fun k => by
      have := Finset.single_le_sum (fun i _ => Nat.zero_le (x i)) (Finset.mem_univ k)
      omega⟩
  have hexp : ∏ k, f k (x k) = ∑ j ∈ Fintype.piFinset (fun _ : σ => range B),
      ∏ k, (mah (f k) (j k) * ((x k).choose (j k) : ℚ)) := by
    refine (Finset.prod_congr rfl fun k _ => asm_newton_big (f k) (x k) B (hB2 k)).trans ?_
    exact Finset.prod_univ_sum (fun _ : σ => range B) (fun k j => mah (f k) j * ((x k).choose j : ℚ))
  have hsub : boundedDegreeExponents σ c ⊆ Fintype.piFinset (fun _ : σ => range B) := by
    intro j hj
    rw [mem_bounded_degree_exponents_iff] at hj
    rw [Fintype.mem_piFinset]
    intro k
    rw [Finset.mem_range]
    have := Finset.single_le_sum (fun i _ => Nat.zero_le (j i)) (Finset.mem_univ k)
    omega
  have hT : ∑ j ∈ boundedDegreeExponents σ c, (∏ k, mah (f k) (j k)) * ∏ k, ((x k).choose (j k) : ℚ)
      = ∑ j ∈ boundedDegreeExponents σ c, ∏ k, (mah (f k) (j k) * ((x k).choose (j k) : ℚ)) :=
    Finset.sum_congr rfl fun j _ => Finset.prod_mul_distrib.symm
  rw [hT, hexp, ← Finset.sum_sdiff hsub, add_sub_cancel_right]
  apply padicGe_sum
  intro j hj
  rw [Finset.mem_sdiff, mem_bounded_degree_exponents_iff] at hj
  have h1 := asm_padicGe_prod Finset.univ (fun k => mah (f k) (j k) * ((x k).choose (j k) : ℚ))
    (fun k => (1 / 4 : ℝ) * (j k : ℝ) + 0) (fun k _ => padicGe_mul_nat (hf k (j k)) _)
  refine padicGe_mono h1 ?_
  have hs : (∑ k, ((1 / 4 : ℝ) * (j k : ℝ) + 0)) = ((∑ k, j k : ℕ) : ℝ) / 4 := by
    push_cast
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hs]
  have hlt : 4 * c < ∑ k, j k := not_le.mp hj.2
  have : ((4 * c : ℕ) : ℝ) < ((∑ k, j k : ℕ) : ℝ) := by exact_mod_cast hlt
  push_cast at this ⊢
  linarith

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => rfl`. Consider the case `succ j ih`. Rewrite using `[Function.iterate_succ_apply', ih]`. Use function extensionality and compare the values at `n`.

Simplify using `[fwdDiff]`.
-/
theorem asm_iter_zero (j : ℕ) : (fwdDiff 1)^[j] (fun _ : ℕ => (0 : ℚ)) = fun _ => 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    funext n
    simp [fwdDiff]

/- English proof (translation)
Introduce `j`. Consider the cases of `j with`. Consider the case `zero => show mah (fun _ => (1 : ℚ)) 0 = 0 ∨ θ * ((0 : ℕ) : ℝ) + 0 ≤ (padicValRat p (mah (fun _ => (1 : ℚ)) 0) : ℝ) right`. Simplify using `[mah]`. Consider the case `succ j => left show (fwdDiff 1)^[j + 1] (fun _ : ℕ => (1 : ℚ)) 0 = 0`.

Rewrite using `[Function.iterate_succ_apply]`. Establish `e : fwdDiff 1 (fun _ : ℕ => (1 : ℚ)) = fun _ => 0`. Use function extensionality and compare the values at `n`. Simplify using `[fwdDiff]`. Rewrite using `[e, asm_iter_zero]`.
-/
theorem asm_dec_one {p : ℕ} [Fact p.Prime] {θ : ℝ} : Dec p θ 0 (fun _ => (1 : ℚ)) := by
  intro j
  cases j with
  | zero =>
    show mah (fun _ => (1 : ℚ)) 0 = 0 ∨
      θ * ((0 : ℕ) : ℝ) + 0 ≤ (padicValRat p (mah (fun _ => (1 : ℚ)) 0) : ℝ)
    right
    simp [mah]
  | succ j =>
    left
    show (fwdDiff 1)^[j + 1] (fun _ : ℕ => (1 : ℚ)) 0 = 0
    rw [Function.iterate_succ_apply]
    have e : fwdDiff 1 (fun _ : ℕ => (1 : ℚ)) = fun _ => 0 := by
      funext n
      simp [fwdDiff]
    rw [e, asm_iter_zero]

/- English proof (translation)
Use `revert h`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Introduce `_`. Simplify using `using (asm_dec_one (p := p) (θ := θ))`. Introduce `a s ha ih h`.

Establish `e : (fun n => ∏ i ∈ insert a s, g i n) = fun n => g a n * ∏ i ∈ s, g i n`. Use function extensionality and compare the values at `n`. Rewrite using `[Finset.prod_insert ha]`. Rewrite using `[e]`. Use `hM θ 0 0 (g a) (fun n => ∏ i ∈ s, g i n) hθ (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))` as an intermediate fact.

Rewrite `this` using `[add_zero]`. Then use the resulting hypothesis.
-/
theorem asm_dec_prod {p : ℕ} [Fact p.Prime] (hM : HMul p) {θ : ℝ} (hθ : 0 ≤ θ) {ι : Type*} (s : Finset ι)
    (g : ι → ℕ → ℚ) (h : ∀ i ∈ s, Dec p θ 0 (g i)) : Dec p θ 0 (fun n => ∏ i ∈ s, g i n) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using (asm_dec_one (p := p) (θ := θ))
  · intro a s ha ih h
    have e : (fun n => ∏ i ∈ insert a s, g i n) = fun n => g a n * ∏ i ∈ s, g i n := by
      funext n
      rw [Finset.prod_insert ha]
    rw [e]
    have := hM θ 0 0 (g a) (fun n => ∏ i ∈ s, g i n) hθ (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    rwa [add_zero] at this

/- English proof (translation)
Use `⟨a, fun j => padicGe_mono (h2 j) (by positivity), fun m => ?_⟩` and prove the remaining obligations. Rewrite using `[h1 m, ext_lemma a m (m + 4 * c + 1) (by omega), ← Finset.sum_range_add_sum_Ico _ (by omega : 4 * c + 1 ≤ m + 4 * c + 1), add_sub_cancel_left]`. Apply `padicGe_sum` to reduce the goal to its premises. Introduce `j hj`. Rewrite `hj` using `[Finset.mem_Ico]`.

Use `padicGe_mono (padicGe_mul_nat (h2 j) _) ?_` and prove the remaining obligations. Establish `: ((4 * c + 1 : ℕ) : ℝ) ≤ j` using `by exact_mod_cast hj.1`. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem asm_clause2 (p : ℕ) [Fact p.Prime] (f : ℕ → ℚ) (a : ℕ → ℚ)
    (h1 : ∀ m : ℕ, f m = ∑ j ∈ Finset.range (m + 1), a j * (m.choose j : ℚ))
    (h2 : ∀ j : ℕ, PadicGe p (a j) ((j : ℝ) / 4)) (c : ℕ) :
    ∃ q : ℕ → ℚ, (∀ j, PadicGe p (q j) 0) ∧
        ∀ m : ℕ, PadicGe p (f m - ∑ j ∈ Finset.range (4 * c + 1), q j * (m.choose j : ℚ)) c := by
  refine ⟨a, fun j => padicGe_mono (h2 j) (by positivity), fun m => ?_⟩
  rw [h1 m, ext_lemma a m (m + 4 * c + 1) (by omega),
    ← Finset.sum_range_add_sum_Ico _ (by omega : 4 * c + 1 ≤ m + 4 * c + 1), add_sub_cancel_left]
  apply padicGe_sum
  intro j hj
  rw [Finset.mem_Ico] at hj
  refine padicGe_mono (padicGe_mul_nat (h2 j) _) ?_
  have : ((4 * c + 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast hj.1
  push_cast at this
  linarith

/- English proof (translation)
Introduce `p hp _`. Use `haveI := Fact.mk hp`. Use `⟨fun u hu => ?_, fun N m us var hus c => ?_⟩` and prove the remaining obligations. Establish `hd` using `h1 p hp u hu`. Establish `ha : ∀ j : ℕ, PadicGe p (mah (unitFn p u) j) ((j : ℝ) / 4)` using `fun j => padicGe_mono (hd j) (le_of_eq (by ring))`.

Conclude with `⟨⟨mah (unitFn p u), asm_newton _, ha⟩, fun c => asm_clause2 p (unitFn p u) _ (asm_newton _) ha c⟩`. Set `F : Fin N → ℕ → ℚ` to `fun k n => ∏ i ∈ Finset.univ.filter (fun i => var i = k), unitFn p (us i) n`. Establish `hF : ∀ k, Dec p (1 / 4) 0 (F k)` using `fun k => asm_dec_prod (h2 p hp) (by norm_num) _ _ fun i _ => h1 p hp (us i) (hus i)`. Use `⟨boundedDegreeExponents (Fin N) c, fun j => ∏ k, mah (F k) (j k), fun j hj => ⟨mem_bounded_degree_exponents_iff.mp hj, padicGe_mono (asm_q_ge F hF j) (by positivity)⟩, fun x => ?_⟩` and prove the remaining obligations. Establish `hfib : (∏ i, unitFn p (us i) (x (var i))) = ∏ k, F k (x k)`.

Rewrite using `[← Finset.prod_fiberwise Finset.univ var (fun i => unitFn p (us i) (x (var i)))]`. Use `Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[(Finset.mem_filter.mp hi).2]`. Rewrite using `[hfib]`. Conclude with `asm_multi F hF c x`.
-/
theorem mahler_decay_products_of (D : Formalism.BasicNotions.D7) (h1 : ∀ p, p.Prime → HDec p) (h2 : ∀ p, p.Prime → HMul p) : UnitFunctionExpansion D := by
  intro p hp _
  haveI := Fact.mk hp
  refine ⟨fun u hu => ?_, fun N m us var hus c => ?_⟩
  · have hd := h1 p hp u hu
    have ha : ∀ j : ℕ, PadicGe p (mah (unitFn p u) j) ((j : ℝ) / 4) := fun j =>
      padicGe_mono (hd j) (le_of_eq (by ring))
    exact ⟨⟨mah (unitFn p u), asm_newton _, ha⟩,
      fun c => asm_clause2 p (unitFn p u) _ (asm_newton _) ha c⟩
  · let F : Fin N → ℕ → ℚ := fun k n =>
      ∏ i ∈ Finset.univ.filter (fun i => var i = k), unitFn p (us i) n
    have hF : ∀ k, Dec p (1 / 4) 0 (F k) := fun k =>
      asm_dec_prod (h2 p hp) (by norm_num) _ _ fun i _ => h1 p hp (us i) (hus i)
    refine ⟨boundedDegreeExponents (Fin N) c, fun j => ∏ k, mah (F k) (j k), fun j hj =>
      ⟨mem_bounded_degree_exponents_iff.mp hj, padicGe_mono (asm_q_ge F hF j) (by positivity)⟩, fun x => ?_⟩
    have hfib : (∏ i, unitFn p (us i) (x (var i))) = ∏ k, F k (x k) := by
      rw [← Finset.prod_fiberwise Finset.univ var (fun i => unitFn p (us i) (x (var i)))]
      refine Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun i hi => ?_
      rw [(Finset.mem_filter.mp hi).2]
    rw [hfib]
    exact asm_multi F hF c x

/- English proof (translation)
Use `revert h`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Introduce `_`. Simplify using `[padicValRat.one]`. Introduce `a s ha ih h`.

Take `⟨h1, h2⟩` from `ih fun i hi => h i (Finset.mem_insert_of_mem hi)`. Take `⟨h3, h4⟩` from `h a (Finset.mem_insert_self a s)`. Rewrite using `[Finset.prod_insert ha]`. Conclude with `⟨mul_ne_zero h3 h1, by rw [padicValRat.mul h3 h1, h4, h2, add_zero]⟩`.
-/
theorem asm_unit_prod {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι) (g : ι → ℚ)
    (h : ∀ i ∈ s, g i ≠ 0 ∧ padicValRat p (g i) = 0) :
    (∏ i ∈ s, g i) ≠ 0 ∧ padicValRat p (∏ i ∈ s, g i) = 0 := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp [padicValRat.one]
  · intro a s ha ih h
    obtain ⟨h1, h2⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨h3, h4⟩ := h a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha]
    exact ⟨mul_ne_zero h3 h1, by rw [padicValRat.mul h3 h1, h4, h2, add_zero]⟩

def asm_bin (σ : Type*) (k : σ) (j : ℕ) : MvPolynomial σ ℚ :=
  MvPolynomial.C ((j.factorial : ℚ)⁻¹) * ∏ i ∈ range j, (MvPolynomial.X k - MvPolynomial.C (i : ℚ))

/- English proof (translation)
Unfold `asm_bin`. Use `(MvPolynomial.totalDegree_mul _ _).trans ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.totalDegree_C, zero_add]`. Use `(MvPolynomial.totalDegree_finset_prod _ _).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `i _`. Use `(MvPolynomial.totalDegree_sub _ _).trans ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]`. Simplify using the standard rewrite rules.

Use `_ = j := by simp`.
-/
theorem asm_bin_deg {σ : Type*} (k : σ) (j : ℕ) : (asm_bin σ k j).totalDegree ≤ j := by
  unfold asm_bin
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finset_prod _ _).trans ?_
  calc ∑ i ∈ range j, (MvPolynomial.X k - MvPolynomial.C (i : ℚ)).totalDegree
      ≤ ∑ i ∈ range j, 1 := by
        apply Finset.sum_le_sum
        intro i _
        refine (MvPolynomial.totalDegree_sub _ _).trans ?_
        rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]
        simp
    _ = j := by simp

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih`. Establish `hj : (j.factorial : ℚ) ≠ 0` using `by positivity`.

Establish `key : (n.choose (j + 1) : ℚ) * ((j : ℚ) + 1) = (n.choose j : ℚ) * ((n : ℚ) - j)`. Break down `Nat.lt_or_ge n j with h | h` into its components or cases. Rewrite using `[Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega)]`. Simplify using the standard rewrite rules. Use `congrArg (Nat.cast : ℕ → ℚ) (Nat.choose_succ_right_eq n j)` as an intermediate fact.

Move the coercions through the operations in `[Nat.cast_sub h] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Finset.prod_range_succ, Nat.factorial_succ]`. Use `push_cast`. Establish `e1 : (∏ i ∈ range j, ((n : ℚ) - (i : ℚ))) = (n.choose j : ℚ) * j.factorial`.

Rewrite using `[← ih]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e1, inv_mul_eq_iff_eq_mul₀ (by positivity)]`. Take the linear combination `(-(j.factorial : ℚ)) * key`.
-/
private theorem choose_lemma (n : ℕ) : ∀ j : ℕ,
    ((j.factorial : ℚ))⁻¹ * ∏ i ∈ range j, ((n : ℚ) - (i : ℚ)) = (n.choose j : ℚ) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have hj : (j.factorial : ℚ) ≠ 0 := by positivity
    have key : (n.choose (j + 1) : ℚ) * ((j : ℚ) + 1) = (n.choose j : ℚ) * ((n : ℚ) - j) := by
      rcases Nat.lt_or_ge n j with h | h
      · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega)]
        simp
      · have := congrArg (Nat.cast : ℕ → ℚ) (Nat.choose_succ_right_eq n j)
        push_cast [Nat.cast_sub h] at this
        linarith
    rw [Finset.prod_range_succ, Nat.factorial_succ]
    push_cast
    have e1 : (∏ i ∈ range j, ((n : ℚ) - (i : ℚ))) = (n.choose j : ℚ) * j.factorial := by
      rw [← ih]
      field_simp
    rw [e1, inv_mul_eq_iff_eq_mul₀ (by positivity)]
    linear_combination (-(j.factorial : ℚ)) * key

/- English proof (translation)
Simplify using `only [asm_bin, map_mul, MvPolynomial.eval_C, map_prod, map_sub, MvPolynomial.eval_X]`. Conclude with `choose_lemma (e k) j`.
-/
theorem asm_bin_eval {σ : Type*} (k : σ) (j : ℕ) (e : σ → ℕ) :
    MvPolynomial.eval (fun k => (e k : ℚ)) (asm_bin σ k j) = ((e k).choose j : ℚ) := by
  simp only [asm_bin, map_mul, MvPolynomial.eval_C, map_prod, map_sub, MvPolynomial.eval_X]
  exact choose_lemma (e k) j

def asm_f (p : ℕ) {σ : Type*} (t rho : σ → ℕ) (inv : Bool) (k : σ) (n : ℕ) : ℚ :=
  unitFn p ⟨t k, rho k, true, inv⟩ n * unitFn p ⟨t k, rho k, false, inv⟩ n

/- English proof (translation)
Use `h2 (1 / 4) 0 0 (unitFn p ⟨t k, rho k, true, inv⟩) (unitFn p ⟨t k, rho k, false, inv⟩) (by norm_num) (h1 _ (hr k)) (h1 _ (hr k))` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `this`.
-/
theorem asm_f_dec {p : ℕ} (h1 : HDec p) (h2 : HMul p) {σ : Type*} (t rho : σ → ℕ)
    (hr : ∀ k, rho k < p ^ (t k + 1)) (inv : Bool) (k : σ) : Dec p (1 / 4) 0 (asm_f p t rho inv k) := by
  have := h2 (1 / 4) 0 0 (unitFn p ⟨t k, rho k, true, inv⟩) (unitFn p ⟨t k, rho k, false, inv⟩)
    (by norm_num) (h1 _ (hr k)) (h1 _ (hr k))
  rw [add_zero] at this
  exact this

/- English proof (translation)
Apply the tactic sequence `cases inv <;> simp [asm_f, unitFn, Finset.prod_mul_distrib, Finset.prod_inv_distrib, mul_inv] <;> ring`.
-/
theorem asm_prod_eq (p : ℕ) {σ : Type*} [Fintype σ] (t rho : σ → ℕ) (inv : Bool) (e' : σ → ℕ) :
    (if inv then (∏ k, cUnit (p ^ (t k + 1)) (e' k) * dUnit (p ^ (t k + 1)) (e' k) (rho k))⁻¹
      else (∏ k, cUnit (p ^ (t k + 1)) (e' k) * dUnit (p ^ (t k + 1)) (e' k) (rho k))) =
    ∏ k, asm_f p t rho inv k (e' k) := by
  cases inv <;> simp [asm_f, unitFn, Finset.prod_mul_distrib, Finset.prod_inv_distrib, mul_inv] <;> ring

/- English proof (translation)
Introduce `rho`. Unfold `dUnit`. Proceed by induction on `rho with`. Consider the case `zero`. Rewrite using `[Finset.Icc_eq_empty (by norm_num)]`.

Simplify using the standard rewrite rules. Consider the case `succ r ih`. Rewrite using `[Finset.prod_Icc_succ_top (by omega), Nat.factorial_succ r, show P * n + (r + 1) = (P * n + r) + 1 by ring, Nat.factorial_succ (P * n + r)]`. Use `push_cast`. Rewrite using `[← ih]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem dUnit_lemma (P n : ℕ) : ∀ rho : ℕ,
    dUnit P n rho * ((P * n).factorial : ℚ) * (rho.factorial : ℚ) = ((P * n + rho).factorial : ℚ) := by
  intro rho
  unfold dUnit
  induction rho with
  | zero =>
    rw [Finset.Icc_eq_empty (by norm_num)]
    simp
  | succ r ih =>
    rw [Finset.prod_Icc_succ_top (by omega), Nat.factorial_succ r,
      show P * n + (r + 1) = (P * n + r) + 1 by ring, Nat.factorial_succ (P * n + r)]
    push_cast
    rw [← ih]
    field_simp
    ring

/- English proof (translation)
Establish `hd` using `dUnit_lemma P e rho`. Unfold `cUnit`. Establish `h1 : (P.factorial : ℚ) ^ e ≠ 0` using `pow_ne_zero _ (by positivity)`. Establish `h2 : (e.factorial : ℚ) ≠ 0` using `by positivity`. Establish `h3 : ((P * e).factorial : ℚ) ≠ 0` using `by positivity`.

Establish `h4 : (rho.factorial : ℚ) ≠ 0` using `by positivity`. Rewrite using `[add_comm rho, ← hd]`. Clear the denominators using the available nonvanishing facts.
-/
private theorem fact_lemma_2 (P e rho : ℕ) :
    (((rho + P * e).factorial : ℕ) : ℚ) =
      (rho.factorial : ℚ) * (e.factorial : ℚ) * ((P.factorial : ℚ)) ^ e * cUnit P e * dUnit P e rho := by
  have hd := dUnit_lemma P e rho
  unfold cUnit
  have h1 : (P.factorial : ℚ) ^ e ≠ 0 := pow_ne_zero _ (by positivity)
  have h2 : (e.factorial : ℚ) ≠ 0 := by positivity
  have h3 : ((P * e).factorial : ℚ) ≠ 0 := by positivity
  have h4 : (rho.factorial : ℚ) ≠ 0 := by positivity
  rw [add_comm rho, ← hd]
  field_simp

/- English proof (translation)
Rewrite using `[← Finset.prod_div_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[fact_lemma_2 (p ^ (t k + 1)) (e' k) (rho k)]`. Establish `h0 : ((rho k).factorial : ℚ) * ((e' k).factorial : ℚ) * ((p ^ (t k + 1)).factorial : ℚ) ^ (e' k) ≠ 0` using `by positivity`. Rewrite using `[div_eq_iff h0]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem asm_ratio (p : ℕ) (hp : p.Prime) {σ : Type*} [Fintype σ] (t rho : σ → ℕ)
    (hr : ∀ k, rho k < p ^ (t k + 1)) (e' : σ → ℕ) :
    ((∏ k, (((rho k + p ^ (t k + 1) * e' k).factorial : ℕ) : ℚ)) /
      (∏ k, ((rho k).factorial : ℚ) * ((e' k).factorial : ℚ) * ((p ^ (t k + 1)).factorial : ℚ) ^ (e' k))) =
    ∏ k, cUnit (p ^ (t k + 1)) (e' k) * dUnit (p ^ (t k + 1)) (e' k) (rho k) := by
  rw [← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [fact_lemma_2 (p ^ (t k + 1)) (e' k) (rho k)]
  have h0 : ((rho k).factorial : ℚ) * ((e' k).factorial : ℚ) *
      ((p ^ (t k + 1)).factorial : ℚ) ^ (e' k) ≠ 0 := by positivity
  rw [div_eq_iff h0]
  ring

/- English proof (translation)
Introduce `p hp _`. Use `haveI := Fact.mk hp`. Use `⟨fun t rho e' _ => fact_lemma_2 _ _ _, fun σ _ t rho hr => ⟨fun e' => ?_, fun inv c => ?_, fun inv c => ?_⟩⟩` and prove the remaining obligations. Use `asm_unit_prod Finset.univ (fun k => cUnit (p ^ (t k + 1)) (e' k) * dUnit (p ^ (t k + 1)) (e' k) (rho k)) ?_` and prove the remaining obligations. Introduce `k _`.

Establish `hc` using `h3 p hp ⟨t k, rho k, true, false⟩ (hr k) (e' k)`. Establish `hd` using `h3 p hp ⟨t k, rho k, false, false⟩ (hr k) (e' k)`. Simplify using `only [unitFn, if_true, if_false, Bool.false_eq_true, ↓reduceIte] at hc hd`. Use `⟨mul_ne_zero hc.1 hd.1, ?_⟩` and prove the remaining obligations. Rewrite using `[padicValRat.mul hc.1 hd.1, hc.2, hd.2, add_zero]`.

Establish `hf` using `fun k => asm_f_dec (h1 p hp) (h2 p hp) t rho hr inv k`. Establish `hm` using `asm_multi (asm_f p t rho inv) hf c`. Use `⟨∑ j ∈ boundedDegreeExponents σ c, MvPolynomial.C (∏ k, mah (asm_f p t rho inv k) (j k)) * ∏ k, asm_bin σ k (j k), ?_, fun e' => ?_⟩` and prove the remaining obligations. Use `(MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun j hj => ?_)` and prove the remaining obligations. Use `(MvPolynomial.totalDegree_mul _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[MvPolynomial.totalDegree_C, zero_add]`. Use `(MvPolynomial.totalDegree_finset_prod _ _).trans ?_` and prove the remaining obligations. Use `(Finset.sum_le_sum fun k _ => asm_bin_deg k (j k)).trans ?_` and prove the remaining obligations. Conclude with `mem_bounded_degree_exponents_iff.mp hj`. Rewrite using `[asm_prod_eq]`.

Establish `e : MvPolynomial.eval (fun k => (e' k : ℚ)) (∑ j ∈ boundedDegreeExponents σ c, MvPolynomial.C (∏ k, mah (asm_f p t rho inv k) (j k)) * ∏ k, asm_bin σ k (j k)) = ∑ j ∈ boundedDegreeExponents σ c, (∏ k, mah (asm_f p t rho inv k) (j k)) * ∏ k, ((e' k).choose (j k) : ℚ)`. Simplify using `only [map_sum, map_mul, map_prod, MvPolynomial.eval_C, asm_bin_eval]`. Rewrite using `[e]`. Conclude with `hm e'`. Establish `hf` using `fun k => asm_f_dec (h1 p hp) (h2 p hp) t rho hr inv k`.

Use `⟨boundedDegreeExponents σ c, fun j => ∏ k, mah (asm_f p t rho inv k) (j k), fun j hj => ⟨mem_bounded_degree_exponents_iff.mp hj, padicGe_mono (asm_q_ge _ hf j) (by positivity)⟩, fun e' => ?_⟩` and prove the remaining obligations. Rewrite using `[asm_ratio p hp t rho hr e', asm_prod_eq]`. Conclude with `asm_multi _ hf c e'`.
-/
theorem unit_function_mahler_decay_of (D : Formalism.BasicNotions.D7) (h1 : ∀ p, p.Prime → HDec p) (h2 : ∀ p, p.Prime → HMul p)
    (h3 : ∀ p, p.Prime → HUnit p) : FactorialUnitDecomposition D := by
  intro p hp _
  haveI := Fact.mk hp
  refine ⟨fun t rho e' _ => fact_lemma_2 _ _ _, fun σ _ t rho hr =>
    ⟨fun e' => ?_, fun inv c => ?_, fun inv c => ?_⟩⟩
  · refine asm_unit_prod Finset.univ
      (fun k => cUnit (p ^ (t k + 1)) (e' k) * dUnit (p ^ (t k + 1)) (e' k) (rho k)) ?_
    intro k _
    have hc := h3 p hp ⟨t k, rho k, true, false⟩ (hr k) (e' k)
    have hd := h3 p hp ⟨t k, rho k, false, false⟩ (hr k) (e' k)
    simp only [unitFn, if_true, if_false, Bool.false_eq_true, ↓reduceIte] at hc hd
    refine ⟨mul_ne_zero hc.1 hd.1, ?_⟩
    rw [padicValRat.mul hc.1 hd.1, hc.2, hd.2, add_zero]
  · have hf := fun k => asm_f_dec (h1 p hp) (h2 p hp) t rho hr inv k
    have hm := asm_multi (asm_f p t rho inv) hf c
    refine ⟨∑ j ∈ boundedDegreeExponents σ c, MvPolynomial.C (∏ k, mah (asm_f p t rho inv k) (j k)) *
      ∏ k, asm_bin σ k (j k), ?_, fun e' => ?_⟩
    · refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun j hj => ?_)
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_C, zero_add]
      refine (MvPolynomial.totalDegree_finset_prod _ _).trans ?_
      refine (Finset.sum_le_sum fun k _ => asm_bin_deg k (j k)).trans ?_
      exact mem_bounded_degree_exponents_iff.mp hj
    · rw [asm_prod_eq]
      have e : MvPolynomial.eval (fun k => (e' k : ℚ))
          (∑ j ∈ boundedDegreeExponents σ c, MvPolynomial.C (∏ k, mah (asm_f p t rho inv k) (j k)) *
            ∏ k, asm_bin σ k (j k)) =
          ∑ j ∈ boundedDegreeExponents σ c, (∏ k, mah (asm_f p t rho inv k) (j k)) *
            ∏ k, ((e' k).choose (j k) : ℚ) := by
        simp only [map_sum, map_mul, map_prod, MvPolynomial.eval_C, asm_bin_eval]
      rw [e]
      exact hm e'
  · have hf := fun k => asm_f_dec (h1 p hp) (h2 p hp) t rho hr inv k
    refine ⟨boundedDegreeExponents σ c, fun j => ∏ k, mah (asm_f p t rho inv k) (j k), fun j hj =>
      ⟨mem_bounded_degree_exponents_iff.mp hj, padicGe_mono (asm_q_ge _ hf j) (by positivity)⟩, fun e' => ?_⟩
    rw [asm_ratio p hp t rho hr e', asm_prod_eq]
    exact asm_multi _ hf c e'

end Formalism.MainNotions.G.GLWeightTheory
