import Mathlib
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.XSubXDvdOfVanishOnOpenHyperplane
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly

noncomputable section

namespace GlobalTheory.FlagPoly.WallDiv

section General
variable {σ : Type} [DecidableEq σ]

/- English proof (translation)
Proceed by induction on `Q using MvPolynomial.induction_on with`. Consider the case `C c => simp`. Consider the case `add p q hp hq`. Use `dvd_add hp hq` as an intermediate fact. Rewrite using `[map_add]`.

Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul_X p i hp`. Rewrite using `[map_mul, rename_X]`. Establish `h2 : (X a - X b : MvPolynomial σ ℝ) ∣ X i - X (Function.update id a b i)`.

Distinguish the cases in `h : i = a`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`. Use `dvd_add (hp.mul_right (X i)) (h2.mul_left (rename (Function.update id a b) p))` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sub_dvd_sub_rename (a b : σ) (Q : MvPolynomial σ ℝ) :
    (X a - X b : MvPolynomial σ ℝ) ∣ Q - rename (Function.update id a b) Q := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    have := dvd_add hp hq
    rw [map_add]; convert this using 1; ring
  | mul_X p i hp =>
    rw [map_mul, rename_X]
    have h2 : (X a - X b : MvPolynomial σ ℝ) ∣ X i - X (Function.update id a b i) := by
      by_cases h : i = a
      · subst h; simp
      · simp [h]
    have := dvd_add (hp.mul_right (X i)) (h2.mul_left (rename (Function.update id a b) p))
    convert this using 1; ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨R, rfl⟩`. Simplify using `[hab.symm]`. Introduce `h`. Simplify `sub_dvd_sub_rename a b Q` using `[h]`.
-/
theorem sub_dvd_iff {a b : σ} (hab : a ≠ b) (Q : MvPolynomial σ ℝ) :
    (X a - X b : MvPolynomial σ ℝ) ∣ Q ↔ rename (Function.update id a b) Q = 0 := by
  constructor
  · rintro ⟨R, rfl⟩
    simp [hab.symm]
  · intro h
    simpa [h] using sub_dvd_sub_rename a b Q

/- English proof (translation)
Rewrite using `[sub_ne_zero]`. Conclude with `fun h => hab (X_injective h)`.
-/
theorem sub_ne_zero' {a b : σ} (hab : a ≠ b) : (X a - X b : MvPolynomial σ ℝ) ≠ 0 := by
  rw [sub_ne_zero]; exact fun h => hab (X_injective h)

/- English proof (translation)
Use `⟨sub_ne_zero' hab, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Use `(sub_dvd_iff hab 1).1 h.dvd` as an intermediate fact. Simplify using `at this`. Introduce `p q h`.

Rewrite `h` using `[sub_dvd_iff hab, map_mul, mul_eq_zero]`. Rewrite using `[sub_dvd_iff hab, sub_dvd_iff hab]`. Conclude with `h`.
-/
theorem prime_sub {a b : σ} (hab : a ≠ b) : Prime (X a - X b : MvPolynomial σ ℝ) := by
  refine ⟨sub_ne_zero' hab, ?_, ?_⟩
  · intro h
    have := (sub_dvd_iff hab 1).1 h.dvd
    simp at this
  · intro p q h
    rw [sub_dvd_iff hab, map_mul, mul_eq_zero] at h
    rw [sub_dvd_iff hab, sub_dvd_iff hab]; exact h

/- English proof (translation)
Rewrite using `[sub_dvd_iff hab]`. Use `congrArg (rename (Function.update id a b)) hP` as an intermediate fact. Rewrite `this` using `[rename_rename, hs, map_neg]`. Conclude with `self_eq_neg.1 this`.
-/
theorem sub_dvd_of_anti {a b : σ} (hab : a ≠ b) (s : σ → σ)
    (hs : Function.update id a b ∘ s = Function.update id a b) (P : MvPolynomial σ ℝ)
    (hP : rename s P = -P) : (X a - X b : MvPolynomial σ ℝ) ∣ P := by
  rw [sub_dvd_iff hab]
  have := congrArg (rename (Function.update id a b)) hP
  rw [rename_rename, hs, map_neg] at this
  exact self_eq_neg.1 this

end General

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `⟨t, i⟩`. Distinguish the cases in `h : t = τ`. Substitute `h` using the available equality. Simplify using `only [swapAt, Function.comp, if_true, Prod.mk.injEq, true_and]`. Simplify using `only [Equiv.swap_apply_def]`.

Use `grind`. Simplify using `[swapAt, h]`.
-/
theorem swapAt_conj (τ : ι) (a c b : Fin N) (hac : a ≠ c) (hab : a ≠ b) :
    swapAt τ a b = swapAt τ c b ∘ swapAt τ a c ∘ swapAt τ c b := by
  funext ⟨t, i⟩
  by_cases h : t = τ
  · subst h
    simp only [swapAt, Function.comp, if_true, Prod.mk.injEq, true_and]
    simp only [Equiv.swap_apply_def]
    grind
  · simp [swapAt, h]

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro b hb hj; exact hP τ a b hb (by omega)`. Consider the case `succ k ih`. Introduce `b hb hj`.

Establish `hbN` using `b.isLt`. Use `set c : Fin N := ⟨a + k + 1, by omega⟩ with hc`. Establish `hcv : (c : ℕ) = a + k + 1` using `rfl`. Establish `h1` using `ih c hcv (by omega)`. Establish `h2` using `hP τ c b (by omega) (by omega)`.

Rewrite using `[swapAt_conj τ a c b (by intro h; rw [← h] at hcv; omega) (by intro h; rw [← h] at hb; omega), ← rename_rename, ← rename_rename, h2, map_neg, h1, neg_neg, h2]`.
-/
theorem anti_of_same_block {j : ℕ} {P : Pol ι N} (hP : AntiL j P) (τ : ι) (a : Fin N) :
    ∀ (k : ℕ) (b : Fin N), (b : ℕ) = a + k + 1 → ¬ ((a : ℕ) < j ∧ j ≤ (b : ℕ)) →
      rename (swapAt τ a b) P = -P := by
  intro k
  induction k with
  | zero => intro b hb hj; exact hP τ a b hb (by omega)
  | succ k ih =>
    intro b hb hj
    have hbN := b.isLt
    set c : Fin N := ⟨a + k + 1, by omega⟩ with hc
    have hcv : (c : ℕ) = a + k + 1 := rfl
    have h1 := ih c hcv (by omega)
    have h2 := hP τ c b (by omega) (by omega)
    rw [swapAt_conj τ a c b (by intro h; rw [← h] at hcv; omega) (by intro h; rw [← h] at hb; omega),
      ← rename_rename, ← rename_rename, h2, map_neg, h1, neg_neg, h2]

/- English proof (translation)
Use function extensionality and compare the values at `⟨t, i⟩`. Distinguish the cases in `h : t = τ`. Substitute `h` using the available equality. Simplify using `only [swapAt, Function.comp, if_true, Function.update_apply, Prod.mk.injEq, true_and, id]`. Simplify using `only [Equiv.swap_apply_def]`.

Use `grind`. Simplify using `[swapAt, h, Function.update_apply]`.
-/
theorem update_comp_swapAt (τ : ι) (a b : Fin N) :
    Function.update id (τ, a) (τ, b) ∘ swapAt τ a b = Function.update id (τ, a) (τ, b) := by
  funext ⟨t, i⟩
  by_cases h : t = τ
  · subst h
    simp only [swapAt, Function.comp, if_true, Function.update_apply, Prod.mk.injEq, true_and, id]
    simp only [Equiv.swap_apply_def]
    grind
  · simp [swapAt, h, Function.update_apply]

/- English proof (translation)
Establish `hne : (τ, a) ≠ (τ, b)` using `by simp [hab.ne]`. Distinguish the cases in `h : (a : ℕ) < j ∧ j ≤ (b : ℕ)`. Take `⟨U, hUo, ⟨x, hx, hxe⟩, hv⟩` from `hU τ a b h.1 h.2`. Use `GlobalTheory.X_sub_X_dvd_of_vanish_on_open_hyperplane _ _ _ P ((fun (y : ι × Fin N → ℝ) t i => y (t, i)) ⁻¹' U) hne (hUo.preimage (by fun_prop)) ⟨fun p => x p.1 p.2, hx, hxe⟩ ?_` and prove the remaining obligations. Introduce `y hy hye`.

Conclude with `hv _ hy hye`. Establish `hlt : (a : ℕ) < b` using `hab`. Conclude with `sub_dvd_of_anti hne _ (update_comp_swapAt τ a b) P (anti_of_same_block hP τ a (b - a - 1) b (by omega) h)`.
-/
theorem root_dvd {j : ℕ} {P : Pol ι N} (hP : AntiL j P)
    (hU : ∀ (τ : ι) (a b : Fin N), (a : ℕ) < j → j ≤ (b : ℕ) → ∃ U : Set (ι → Fin N → ℝ), IsOpen U ∧
      (∃ x ∈ U, x τ a = x τ b) ∧ ∀ x ∈ U, x τ a = x τ b → ev x P = 0)
    (τ : ι) (a b : Fin N) (hab : a < b) : (X (τ, a) - X (τ, b) : Pol ι N) ∣ P := by
  have hne : (τ, a) ≠ (τ, b) := by simp [hab.ne]
  by_cases h : (a : ℕ) < j ∧ j ≤ (b : ℕ)
  · obtain ⟨U, hUo, ⟨x, hx, hxe⟩, hv⟩ := hU τ a b h.1 h.2
    refine GlobalTheory.X_sub_X_dvd_of_vanish_on_open_hyperplane _ _ _ P ((fun (y : ι × Fin N → ℝ) t i => y (t, i)) ⁻¹' U) hne
      (hUo.preimage (by fun_prop)) ⟨fun p => x p.1 p.2, hx, hxe⟩ ?_
    intro y hy hye
    exact hv _ hy hye
  · have hlt : (a : ℕ) < b := hab
    exact sub_dvd_of_anti hne _ (update_comp_swapAt τ a b) P
      (anti_of_same_block hP τ a (b - a - 1) b (by omega) h)

/- English proof (translation)
Establish `e : delPol ι N = ∏ x : ι × Fin N × Fin N, (if x.2.1 < x.2.2 then X (x.1, x.2.1) - X (x.1, x.2.2) else 1 : Pol ι N)`. Simplify using `only [delPol, Fintype.prod_prod_type]`. Rewrite using `[e]`. Apply `Fintype.prod_dvd_of_isRelPrime` to reduce the goal to its premises. Introduce and unpack `⟨τ, a, b⟩ ⟨τ', a', b'⟩ hne`.

Simplify using `only [Function.onFun]`. Use `split_ifs with h1 h2`. Establish `hne1 : (τ, a) ≠ (τ, b)` using `by simp [h1.ne]`. Rewrite using `[(prime_sub hne1).irreducible.isRelPrime_iff_not_dvd, sub_dvd_iff hne1]`. Simplify using `only [map_sub, rename_X]`.

Apply `sub_ne_zero'` to reduce the goal to its premises. Simplify using `only [Function.update_apply, id, ne_eq, Prod.mk.injEq] at hne ⊢`. Use `grind`. Conclude with `isRelPrime_one_right`. Conclude with `isRelPrime_one_left`.

Conclude with `isRelPrime_one_left`. Introduce and unpack `⟨τ, a, b⟩`. Simplify using `only`. Use `split_ifs with h1`. Conclude with `h τ a b h1`.

Conclude with `one_dvd _`.
-/
theorem delPol_dvd {P : Pol ι N}
    (h : ∀ (τ : ι) (a b : Fin N), a < b → (X (τ, a) - X (τ, b) : Pol ι N) ∣ P) : delPol ι N ∣ P := by
  have e : delPol ι N = ∏ x : ι × Fin N × Fin N,
      (if x.2.1 < x.2.2 then X (x.1, x.2.1) - X (x.1, x.2.2) else 1 : Pol ι N) := by
    simp only [delPol, Fintype.prod_prod_type]
  rw [e]
  apply Fintype.prod_dvd_of_isRelPrime
  · rintro ⟨τ, a, b⟩ ⟨τ', a', b'⟩ hne
    simp only [Function.onFun]
    split_ifs with h1 h2
    · have hne1 : (τ, a) ≠ (τ, b) := by simp [h1.ne]
      rw [(prime_sub hne1).irreducible.isRelPrime_iff_not_dvd, sub_dvd_iff hne1]
      simp only [map_sub, rename_X]
      apply sub_ne_zero'
      simp only [Function.update_apply, id, ne_eq, Prod.mk.injEq] at hne ⊢
      grind
    · exact isRelPrime_one_right
    · exact isRelPrime_one_left
    · exact isRelPrime_one_left
  · rintro ⟨τ, a, b⟩
    simp only
    split_ifs with h1
    · exact h τ a b h1
    · exact one_dvd _

/- English proof (translation)
Unfold `delPol`. Use `Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_filter]`. Use `congr 1`. Use extensionality with `b`.

Simplify using the standard rewrite rules.
-/
theorem delPol_eq : delPol ι N =
    ∏ τ : ι, ∏ a : Fin N, ∏ b ∈ Finset.Ioi a, (X (τ, a) - X (τ, b) : Pol ι N) := by
  unfold delPol
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_filter]
  congr 1; ext b; simp

/- English proof (translation)
Rewrite using `[delPol_eq]`. Simplify using `only [Finset.prod_ne_zero_iff]`. Introduce `τ _ a _ b hb`. Conclude with `sub_ne_zero' (by simp [(Finset.mem_Ioi.1 hb).ne])`.
-/
theorem delPol_ne_zero : delPol ι N ≠ 0 := by
  rw [delPol_eq]
  simp only [Finset.prod_ne_zero_iff]
  intro τ _ a _ b hb
  exact sub_ne_zero' (by simp [(Finset.mem_Ioi.1 hb).ne])

/- English proof (translation)
Rewrite using `[delPol_eq]`. Establish `: dimFl ι N = ∑ _τ : ι, ∑ a : Fin N, ∑ _b ∈ Finset.Ioi a, 1`. Simplify using `[dimFl, ← PermutationPointDegree.sum_delta]`. Rewrite using `[this]`. Use `IsHomogeneous.prod _ _ _ fun τ _ => IsHomogeneous.prod _ _ _ fun a _ => IsHomogeneous.prod _ _ _ fun b _ => (isHomogeneous_X _ _).sub (isHomogeneous_X _ _)` and prove the remaining obligations.
-/
theorem delPol_homog : (delPol ι N).IsHomogeneous (dimFl ι N) := by
  rw [delPol_eq]
  have : dimFl ι N = ∑ _τ : ι, ∑ a : Fin N, ∑ _b ∈ Finset.Ioi a, 1 := by
    simp [dimFl, ← PermutationPointDegree.sum_delta]
  rw [this]
  refine IsHomogeneous.prod _ _ _ fun τ _ => IsHomogeneous.prod _ _ _ fun a _ =>
    IsHomogeneous.prod _ _ _ fun b _ => (isHomogeneous_X _ _).sub (isHomogeneous_X _ _)

/- English proof (translation)
Rewrite using `[delPol_eq, map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), ← neg_mul]`. Use `congr 1`. Use `(Equiv.swap a b).prod_Ioi_comp_eq_sign_mul_prod (f := fun i k => (X (τ, i) - X (τ, k) : Pol ι N)) (by intro i k; ring)` as an intermediate fact. Rewrite `this` using `[Equiv.Perm.sign_swap hab]`. Simplify `this` using `[map_prod, swapAt]`.

Use `Finset.prod_congr rfl fun t ht => ?_` and prove the remaining obligations. Simplify using `[map_prod, swapAt, (Finset.mem_erase.1 ht).1]`.
-/
theorem rename_delPol (τ : ι) {a b : Fin N} (hab : a ≠ b) :
    rename (swapAt τ a b) (delPol ι N) = -delPol ι N := by
  rw [delPol_eq, map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), ← neg_mul]
  congr 1
  · have := (Equiv.swap a b).prod_Ioi_comp_eq_sign_mul_prod
      (f := fun i k => (X (τ, i) - X (τ, k) : Pol ι N)) (by intro i k; ring)
    rw [Equiv.Perm.sign_swap hab] at this
    simpa [map_prod, swapAt] using this
  · refine Finset.prod_congr rfl fun t ht => ?_
    simp [map_prod, swapAt, (Finset.mem_erase.1 ht).1]

/- English proof (translation)
Take `⟨l, rfl⟩` from `h`. Use `letI := (MvPolynomial.gradedAlgebra : GradedAlgebra (homogeneousSubmodule (ι × Fin N) ℝ))`. Establish `h1` using `DirectSum.coe_decompose_mul_add_of_left_mem (homogeneousSubmodule (ι × Fin N) ℝ) (b := l) (j := 1) ((mem_homogeneousSubmodule _ _).2 (delPol_homog (ι := ι) (N := N)))`. Rewrite `h1` using `[DirectSum.decompose_of_mem_same _ ((mem_homogeneousSubmodule _ _).2 hP)]`. Establish `h2` using `(DirectSum.decompose (homogeneousSubmodule (ι × Fin N) ℝ) l 1).2`.

Generalize the expression as in `(DirectSum.decompose (homogeneousSubmodule (ι × Fin N) ℝ) l 1 : Pol ι N) = m at h1 h2`. Rewrite `h2` using `[homogeneousSubmodule_one_eq_span_X, Submodule.mem_span_range_iff_exists_fun]`. Take `⟨c, rfl⟩` from `h2`. Conclude with `⟨c, h1⟩`.
-/
theorem exists_linear {P : Pol ι N} (hP : P.IsHomogeneous (dimFl ι N + 1)) (h : delPol ι N ∣ P) :
    ∃ c : ι × Fin N → ℝ, P = delPol ι N * ∑ x, c x • X x := by
  obtain ⟨l, rfl⟩ := h
  letI := (MvPolynomial.gradedAlgebra : GradedAlgebra (homogeneousSubmodule (ι × Fin N) ℝ))
  have h1 := DirectSum.coe_decompose_mul_add_of_left_mem (homogeneousSubmodule (ι × Fin N) ℝ)
    (b := l) (j := 1) ((mem_homogeneousSubmodule _ _).2 (delPol_homog (ι := ι) (N := N)))
  rw [DirectSum.decompose_of_mem_same _ ((mem_homogeneousSubmodule _ _).2 hP)] at h1
  have h2 := (DirectSum.decompose (homogeneousSubmodule (ι × Fin N) ℝ) l 1).2
  generalize (DirectSum.decompose (homogeneousSubmodule (ι × Fin N) ℝ) l 1 : Pol ι N) = m at h1 h2
  rw [homogeneousSubmodule_one_eq_span_X, Submodule.mem_span_range_iff_exists_fun] at h2
  obtain ⟨c, rfl⟩ := h2
  exact ⟨c, h1⟩

/- English proof (translation)
Simplify using `[Pi.single_apply]`.
-/
theorem coeff_linear (c : ι × Fin N → ℝ) (y : ι × Fin N) :
    eval (Pi.single y 1) (∑ x, c x • X x : Pol ι N) = c y := by
  simp [Pi.single_apply]

/- English proof (translation)
Establish `hab : a ≠ b` using `by intro h; rw [h] at hb; omega`. Establish `h1` using `h τ a b hb hj`. Rewrite `h1` using `[map_mul, rename_delPol τ hab, neg_mul, neg_inj, mul_right_inj' delPol_ne_zero]`. Establish `h2` using `congrArg (eval (Pi.single (τ, b) 1)) h1`. Rewrite `h2` using `[eval_rename, coeff_linear]`.

Rewrite using `[← h2, ← coeff_linear c (τ, a)]`. Use `congr 2`. Use function extensionality and compare the values at `⟨t, i⟩`. Distinguish the cases in `h : t = τ`. Substitute `h` using the available equality.

Simplify using `only [swapAt, Function.comp, if_true, Pi.single_apply, Prod.mk.injEq, true_and]`. Simplify using `only [Equiv.swap_apply_def]`. Use `grind`. Simplify using `[swapAt, h, Pi.single_apply]`.
-/
theorem coef_step {j : ℕ} {c : ι × Fin N → ℝ} (h : AntiL j (delPol ι N * ∑ x, c x • X x))
    (τ : ι) (a b : Fin N) (hb : (b : ℕ) = a + 1) (hj : (b : ℕ) ≠ j) : c (τ, a) = c (τ, b) := by
  have hab : a ≠ b := by intro h; rw [h] at hb; omega
  have h1 := h τ a b hb hj
  rw [map_mul, rename_delPol τ hab, neg_mul, neg_inj, mul_right_inj' delPol_ne_zero] at h1
  have h2 := congrArg (eval (Pi.single (τ, b) 1)) h1
  rw [eval_rename, coeff_linear] at h2
  rw [← h2, ← coeff_linear c (τ, a)]
  congr 2
  funext ⟨t, i⟩
  by_cases h : t = τ
  · subst h
    simp only [swapAt, Function.comp, if_true, Pi.single_apply, Prod.mk.injEq, true_and]
    simp only [Equiv.swap_apply_def]
    grind
  · simp [swapAt, h, Pi.single_apply]

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro b hb _`. Rewrite using `[show b = a from Fin.ext hb]`. Consider the case `succ k ih`.

Introduce `b hb hj`. Establish `hbN` using `b.isLt`. Use `set d : Fin N := ⟨a + k, by omega⟩ with hd`. Establish `hdv : (d : ℕ) = a + k` using `rfl`. Rewrite using `[ih d hdv (by omega)]`.

Conclude with `coef_step h τ d b (by omega) (by omega)`.
-/
theorem coef_block {j : ℕ} {c : ι × Fin N → ℝ} (h : AntiL j (delPol ι N * ∑ x, c x • X x))
    (τ : ι) (a : Fin N) : ∀ (k : ℕ) (b : Fin N), (b : ℕ) = a + k → ¬ ((a : ℕ) < j ∧ j ≤ (b : ℕ)) →
      c (τ, a) = c (τ, b) := by
  intro k
  induction k with
  | zero => intro b hb _; rw [show b = a from Fin.ext hb]
  | succ k ih =>
    intro b hb hj
    have hbN := b.isLt
    set d : Fin N := ⟨a + k, by omega⟩ with hd
    have hdv : (d : ℕ) = a + k := rfl
    rw [ih d hdv (by omega)]
    exact coef_step h τ d b (by omega) (by omega)

end GlobalTheory.FlagPoly.WallDiv

open GlobalTheory.FlagPoly.WallDiv in

/- English proof (translation)
Introduce `ι _ _ N j P hP hA hU`. Take `⟨c, rfl⟩` from `exists_linear hP (delPol_dvd (root_dvd hA hU))`. Use `⟨fun τ => if h : 0 < N then c (τ, ⟨0, h⟩) else 0, fun τ => if h : 0 < N then c (τ, ⟨N - 1, by omega⟩) else 0, ?_⟩` and prove the remaining obligations. Use `congr 1`. Rewrite using `[Fintype.sum_prod_type, invForm]`.

Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Simplify using `only [pLow, pHigh, Finset.mul_sum, Finset.sum_filter, pow_one, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hi` using `i.isLt`. Establish `hN : 0 < N` using `by omega`.

Simplify using `only [dif_pos hN, smul_eq_C_mul]`. Distinguish the cases in `hij : (i : ℕ) < j`. Rewrite using `[if_pos hij, if_neg (by omega), mul_zero, add_zero, coef_block hA τ ⟨0, hN⟩ i i (by simp) (by omega)]`. Rewrite using `[if_neg hij, if_pos (by omega), mul_zero, zero_add, coef_block hA τ i (N - 1 - i) ⟨N - 1, by omega⟩ (by simp; omega) (by omega)]`.
-/
theorem GlobalTheory.FlagPoly.eq_delPol_mul_invForm : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (j : ℕ) (P : Pol ι N), P.IsHomogeneous (dimFl ι N + 1) → AntiL j P → (∀ (τ : ι) (a b : Fin N), (a : ℕ) < j → j ≤ (b : ℕ) → ∃ U : Set (ι → Fin N → ℝ), IsOpen U ∧ (∃ x ∈ U, x τ a = x τ b) ∧ ∀ x ∈ U, x τ a = x τ b → ev x P = 0) → ∃ al be : ι → ℝ, P = delPol ι N * invForm j al be := by
  intro ι _ _ N j P hP hA hU
  obtain ⟨c, rfl⟩ := exists_linear hP (delPol_dvd (root_dvd hA hU))
  refine ⟨fun τ => if h : 0 < N then c (τ, ⟨0, h⟩) else 0,
    fun τ => if h : 0 < N then c (τ, ⟨N - 1, by omega⟩) else 0, ?_⟩
  congr 1
  rw [Fintype.sum_prod_type, invForm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [pLow, pHigh, Finset.mul_sum, Finset.sum_filter, pow_one, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := i.isLt
  have hN : 0 < N := by omega
  simp only [dif_pos hN, smul_eq_C_mul]
  by_cases hij : (i : ℕ) < j
  · rw [if_pos hij, if_neg (by omega), mul_zero, add_zero,
      coef_block hA τ ⟨0, hN⟩ i i (by simp) (by omega)]
  · rw [if_neg hij, if_pos (by omega), mul_zero, zero_add,
      coef_block hA τ i (N - 1 - i) ⟨N - 1, by omega⟩ (by simp; omega) (by omega)]
