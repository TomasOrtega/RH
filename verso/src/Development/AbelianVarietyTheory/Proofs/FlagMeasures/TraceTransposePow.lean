import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScalarOfMultOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothAddSmul
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder

noncomputable section
namespace GlobalTheory.Dec.FormF

/- English proof (translation)
Proceed by induction on `k generalizing b with`. Consider the case `zero => simp [Formalism.REAL.epow, Matrix.one_apply]`. Consider the case `succ k ih`. Rewrite using `[pow_succ, Matrix.mul_apply]`. Simplify using `only [ih, Matrix.of_apply, Formalism.REAL.epow]`.
-/
private lemma matrix_of_pow_apply_eq_epow {n : ℕ} {A : Type} [Ring A] (E : Fin n → Fin n → A) (k : ℕ) (a b : Fin n) :
    (Matrix.of E ^ k) a b = Formalism.REAL.epow E k a b := by
  induction k generalizing b with
  | zero => simp [Formalism.REAL.epow, Matrix.one_apply]
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    simp only [ih, Matrix.of_apply, Formalism.REAL.epow]

/- English proof (translation)
Simplify using `only [matrix_of_pow_apply_eq_epow]`. Establish `h1 : ∀ c, E c a * Formalism.REAL.epow E j b c = Formalism.REAL.epow E j b c * E c a + ((if a = b then Formalism.REAL.epow E j c c else 0) - Formalism.REAL.epow E j b a)`. Introduce `c`. Use `Formalism.REAL.epowCov (Module.End ℂ V) n E hE j b c c a` as an intermediate fact. Rewrite `this` using `[if_pos rfl]`.

Rewrite using `[← this]`. Normalize the expressions using the abelian group laws. Rewrite using `[Finset.sum_congr rfl fun c _ => h1 c]`. Simplify using `only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]`. Rewrite using `[show Formalism.REAL.epow E (j + 1) b a = ∑ c, Formalism.REAL.epow E j b c * E c a from rfl]`.

Distinguish the cases in `hab : a = b`. Simplify using `only [hab, if_true]`. Normalize the expressions using the abelian group laws. Simplify using `only [hab, if_false, Finset.sum_const_zero]`. Normalize the expressions using the abelian group laws.
-/
private lemma matrix_of_pow_succ_apply_sub_nsmul_add_trace {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (hE : Formalism.REAL.GlRel E) (j : ℕ) (a b : Fin n) :
    ∑ c, E c a * (Matrix.of E ^ j) b c =
      (Matrix.of E ^ (j + 1)) b a - n • (Matrix.of E ^ j) b a +
        if a = b then ∑ c, (Matrix.of E ^ j) c c else 0 := by
  simp only [matrix_of_pow_apply_eq_epow]
  have h1 : ∀ c, E c a * Formalism.REAL.epow E j b c = Formalism.REAL.epow E j b c * E c a +
      ((if a = b then Formalism.REAL.epow E j c c else 0) - Formalism.REAL.epow E j b a) := by
    intro c
    have := Formalism.REAL.epowCov (Module.End ℂ V) n E hE j b c c a
    rw [if_pos rfl] at this
    rw [← this]
    abel
  rw [Finset.sum_congr rfl fun c _ => h1 c]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [show Formalism.REAL.epow E (j + 1) b a = ∑ c, Formalism.REAL.epow E j b c * E c a from rfl]
  by_cases hab : a = b
  · simp only [hab, if_true]
    abel
  · simp only [hab, if_false, Finset.sum_const_zero]
    abel

/- English proof (translation)
Use `congrArg (fun T : Module.End ℂ V => T w) (matrix_of_pow_succ_apply_sub_nsmul_add_trace E hE j a b)` as an intermediate fact. Simplify using `only [LinearMap.sum_apply, Module.End.mul_apply] at this`. Rewrite using `[this]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private lemma ite_eq_trace_matrix_of_pow_apply {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (hE : Formalism.REAL.GlRel E) (j : ℕ) (a b : Fin n) (w : V) :
    ∑ c, E c a ((Matrix.of E ^ j) b c w) = (Matrix.of E ^ (j + 1)) b a w - n • (Matrix.of E ^ j) b a w +
      if a = b then (∑ c, (Matrix.of E ^ j) c c) w else 0 := by
  have := congrArg (fun T : Module.End ℂ V => T w) (matrix_of_pow_succ_apply_sub_nsmul_add_trace E hE j a b)
  simp only [LinearMap.sum_apply, Module.End.mul_apply] at this
  rw [this]
  split_ifs <;> simp

/- English proof (translation)
Simplify using `only [add_smul, sub_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum]`. Establish `h1 : ∑ j ∈ Finset.range (m + 2), (if 1 ≤ j then α (j - 1) else 0) • y j = ∑ j ∈ Finset.range (m + 1), α j • y (j + 1)`. Rewrite using `[Finset.sum_range_succ']`. Simplify using the standard rewrite rules. Establish `h2 : ∑ j ∈ Finset.range (m + 2), (if j ≤ m then α j else 0) • y j = ∑ j ∈ Finset.range (m + 1), α j • y j`.

Rewrite using `[Finset.sum_range_succ]`. Simplify using `only [show ¬ (m + 1 ≤ m) from by omega, if_false, zero_smul, add_zero]`. Conclude with `Finset.sum_congr rfl fun j hj => by`. Rewrite using `[if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]`. Establish `h3 : ∑ j ∈ Finset.range (m + 2), (if j = 0 then φ else 0) • y j = φ • y 0`.

Rewrite using `[Finset.sum_range_succ']`. Simplify using the standard rewrite rules. Rewrite using `[h1, h2, h3]`.
-/
private lemma sum_range_shift_smul_eq_sub_add {Y : Type} [AddCommGroup Y] [Module ℂ Y] (α : ℕ → ℂ) (m : ℕ) (N φ : ℂ)
    (y : ℕ → Y) :
    ∑ j ∈ Finset.range (m + 2), ((if 1 ≤ j then α (j - 1) else 0) - N * (if j ≤ m then α j else 0) +
        (if j = 0 then φ else 0)) • y j =
      ∑ j ∈ Finset.range (m + 1), α j • y (j + 1) - N • ∑ j ∈ Finset.range (m + 1), α j • y j + φ • y 0 := by
  simp only [add_smul, sub_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum]
  have h1 : ∑ j ∈ Finset.range (m + 2), (if 1 ≤ j then α (j - 1) else 0) • y j =
      ∑ j ∈ Finset.range (m + 1), α j • y (j + 1) := by
    rw [Finset.sum_range_succ']
    simp
  have h2 : ∑ j ∈ Finset.range (m + 2), (if j ≤ m then α j else 0) • y j =
      ∑ j ∈ Finset.range (m + 1), α j • y j := by
    rw [Finset.sum_range_succ]
    simp only [show ¬ (m + 1 ≤ m) from by omega, if_false, zero_smul, add_zero]
    exact Finset.sum_congr rfl fun j hj => by
      rw [if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
  have h3 : ∑ j ∈ Finset.range (m + 2), (if j = 0 then φ else 0) • y j = φ • y 0 := by
    rw [Finset.sum_range_succ']
    simp
  rw [h1, h2, h3]

/- English proof (translation)
Simplify using `[Matrix.mulVec, dotProduct]`.
-/
private lemma sum_mulVec_one_eq_sum_entries {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) :
    ∑ i, (P *ᵥ fun _ => (1 : ℂ)) i = ∑ a, ∑ b, P a b := by
  simp [Matrix.mulVec, dotProduct]

open Polynomial in

/- English proof (translation)
Use `set Am := Formalism.REAL.Amat (fun c => χ c + ((n : ℂ) - 1) / 2) with hAm`. Use `set M : Matrix (Fin n) (Fin n) ℂ := Am - (n : ℂ) • 1 + Matrix.of (fun _ _ => (1 : ℂ)) with hM`. Establish `hgv : ∀ k, gelfVal χ k = ∑ a, ∑ b, (Am ^ k) a b` using `fun k => rfl`. Establish `hsumvec : ∀ (m : ℕ) (α : ℕ → ℂ), ∑ i, ((∑ j ∈ Finset.range (m + 1), α j • Am ^ j) *ᵥ fun _ => (1 : ℂ)) i = ∑ j ∈ Finset.range (m + 1), α j * gelfVal χ j`. Introduce `m α`.

Rewrite using `[sum_mulVec_one_eq_sum_entries]`. Establish `hab : ∀ a b, (∑ j ∈ Finset.range (m + 1), α j • Am ^ j) a b = ∑ j ∈ Finset.range (m + 1), α j * (Am ^ j) a b`. Introduce `a b`. Simplify using `[Matrix.sum_apply]`. Simplify using `only [hab, hgv, Finset.mul_sum]`.

Use `conv_rhs => rw [Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_comm`. Establish `key : ∀ m : ℕ, ∃ α : ℕ → ℂ, (∀ a b, (Matrix.of (fun a b => E b a) ^ m) a b v = ∑ j ∈ Finset.range (m + 1), α j • (Matrix.of E ^ j) b a v) ∧ (∑ j ∈ Finset.range (m + 1), α j • Am ^ j) *ᵥ (fun _ => (1 : ℂ)) = M ^ m *ᵥ (fun _ => 1)`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero`. Use `⟨fun _ => 1, fun a b => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Matrix.one_apply, hab, Ne.symm hab]`. Simplify using the standard rewrite rules. Consider the case `succ m ih`. Take `⟨α, h1, h2⟩` from `ih`. Use `set φ : ℂ := ∑ j ∈ Finset.range (m + 1), α j * gelfVal χ j with hφ`.

Use `⟨fun j => (if 1 ≤ j then α (j - 1) else 0) - (n : ℂ) * (if j ≤ m then α j else 0) + (if j = 0 then φ else 0), fun a b => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[sum_range_shift_smul_eq_sub_add α m (n : ℂ) φ (fun j => (Matrix.of E ^ j) b a v)]`. Rewrite using `[pow_succ', Matrix.mul_apply, LinearMap.sum_apply]`. Simplify using `only [Module.End.mul_apply, Matrix.of_apply, h1, map_sum, map_smul]`. Rewrite using `[Finset.sum_comm]`.

Simplify using `only [← Finset.smul_sum]`. Simplify using `only [ite_eq_trace_matrix_of_pow_apply E hE, hv]`. Simplify using `only [smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]`. Use `congr 1`. Use `congr 1`.

Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_comm, Nat.cast_smul_eq_nsmul]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Simplify using `[hφ, Finset.sum_smul, smul_smul]`. Simplify using `[hab, Ne.symm hab, Matrix.one_apply_ne (Ne.symm hab)]`. Rewrite using `[sum_range_shift_smul_eq_sub_add α m (n : ℂ) φ (fun j => Am ^ j), pow_succ', ← Matrix.mulVec_mulVec, ← h2, Matrix.mulVec_mulVec]`. Establish `hP : ∑ j ∈ Finset.range (m + 1), α j • Am ^ (j + 1) = Am * ∑ j ∈ Finset.range (m + 1), α j • Am ^ j`. Rewrite using `[Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun j _ => by rw [Matrix.mul_smul, pow_succ']`. Rewrite using `[hP, pow_zero, hM, Matrix.add_mul, Matrix.sub_mul, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mul, Matrix.one_mul]`. Use `congr 1`. Rewrite using `[← Matrix.mulVec_mulVec]`. Use extensionality with `i`.

Use `hsumvec m α` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.of_apply, one_mul, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_one] at this ⊢`. Rewrite using `[this, hφ]`. Simplify using the standard rewrite rules. Take `⟨α, h1, h2⟩` from `key m`.

Establish `hM' : M = (-Formalism.REAL.Amat (fun c => -χ c + ((n : ℂ) - 1) / 2))ᵀ`. Use extensionality with `a b`. Simplify using `only [hM, hAm, Formalism.REAL.Amat, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.neg_apply, smul_eq_mul]`. Break down `lt_trichotomy a b with h | rfl | h` into its components or cases. Simplify using `[h, h.ne, h.ne', not_lt.2 h.le]`.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Simplify using `[h, h.ne, h.ne', not_lt.2 h.le]`. Establish `hval : ∑ j ∈ Finset.range (m + 1), α j * gelfVal χ j = (-1) ^ m * gelfVal (fun a => -χ a) m`. Rewrite using `[← hsumvec m α, h2, sum_mulVec_one_eq_sum_entries, hM', ← Matrix.transpose_pow]`.

Establish `hneg : (-Formalism.REAL.Amat (fun c => -χ c + ((n : ℂ) - 1) / 2)) ^ m = ((-1 : ℂ) ^ m) • Formalism.REAL.Amat (fun c => -χ c + ((n : ℂ) - 1) / 2) ^ m`. Rewrite using `[← _root_.smul_pow, neg_one_smul]`. Rewrite using `[hneg]`. Simplify using `only [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, gelfVal, Finset.mul_sum]`. Conclude with `Finset.sum_comm`.

Rewrite using `[LinearMap.sum_apply]`. Simplify using `only [h1]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.smul_sum, ← LinearMap.sum_apply, hv, smul_smul, ← Finset.sum_smul]`. Rewrite using `[hval]`.
-/
theorem trace_transpose_pow {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V)
    (hE : Formalism.REAL.GlRel E) (χ : Fin n → ℂ) (v : V)
    (hv : ∀ k : ℕ, (∑ c, (Matrix.of E ^ k) c c) v = gelfVal χ k • v) (m : ℕ) :
    (∑ c, (Matrix.of (fun a b => E b a) ^ m) c c) v = ((-1) ^ m * gelfVal (fun a => -χ a) m) • v := by
  set Am := Formalism.REAL.Amat (fun c => χ c + ((n : ℂ) - 1) / 2) with hAm
  set M : Matrix (Fin n) (Fin n) ℂ := Am - (n : ℂ) • 1 + Matrix.of (fun _ _ => (1 : ℂ)) with hM
  have hgv : ∀ k, gelfVal χ k = ∑ a, ∑ b, (Am ^ k) a b := fun k => rfl
  have hsumvec : ∀ (m : ℕ) (α : ℕ → ℂ), ∑ i, ((∑ j ∈ Finset.range (m + 1), α j • Am ^ j) *ᵥ fun _ => (1 : ℂ)) i =
      ∑ j ∈ Finset.range (m + 1), α j * gelfVal χ j := by
    intro m α
    rw [sum_mulVec_one_eq_sum_entries]
    have hab : ∀ a b, (∑ j ∈ Finset.range (m + 1), α j • Am ^ j) a b =
        ∑ j ∈ Finset.range (m + 1), α j * (Am ^ j) a b := by
      intro a b
      simp [Matrix.sum_apply]
    simp only [hab, hgv, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
  have key : ∀ m : ℕ, ∃ α : ℕ → ℂ,
      (∀ a b, (Matrix.of (fun a b => E b a) ^ m) a b v =
        ∑ j ∈ Finset.range (m + 1), α j • (Matrix.of E ^ j) b a v) ∧
      (∑ j ∈ Finset.range (m + 1), α j • Am ^ j) *ᵥ (fun _ => (1 : ℂ)) = M ^ m *ᵥ (fun _ => 1) := by
    intro m
    induction m with
    | zero =>
      refine ⟨fun _ => 1, fun a b => ?_, ?_⟩
      · by_cases hab : a = b
        · subst hab
          simp
        · simp [Matrix.one_apply, hab, Ne.symm hab]
      · simp
    | succ m ih =>
      obtain ⟨α, h1, h2⟩ := ih
      set φ : ℂ := ∑ j ∈ Finset.range (m + 1), α j * gelfVal χ j with hφ
      refine ⟨fun j => (if 1 ≤ j then α (j - 1) else 0) - (n : ℂ) * (if j ≤ m then α j else 0) +
        (if j = 0 then φ else 0), fun a b => ?_, ?_⟩
      · rw [sum_range_shift_smul_eq_sub_add α m (n : ℂ) φ (fun j => (Matrix.of E ^ j) b a v)]
        rw [pow_succ', Matrix.mul_apply, LinearMap.sum_apply]
        simp only [Module.End.mul_apply, Matrix.of_apply, h1, map_sum, map_smul]
        rw [Finset.sum_comm]
        simp only [← Finset.smul_sum]
        simp only [ite_eq_trace_matrix_of_pow_apply E hE, hv]
        simp only [smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
        congr 1
        · congr 1
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [smul_comm, Nat.cast_smul_eq_nsmul]
        · by_cases hab : a = b
          · subst hab
            simp [hφ, Finset.sum_smul, smul_smul]
          · simp [hab, Ne.symm hab, Matrix.one_apply_ne (Ne.symm hab)]
      · rw [sum_range_shift_smul_eq_sub_add α m (n : ℂ) φ (fun j => Am ^ j), pow_succ', ← Matrix.mulVec_mulVec, ← h2,
          Matrix.mulVec_mulVec]
        have hP : ∑ j ∈ Finset.range (m + 1), α j • Am ^ (j + 1) = Am * ∑ j ∈ Finset.range (m + 1), α j • Am ^ j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [Matrix.mul_smul, pow_succ']
        rw [hP, pow_zero, hM, Matrix.add_mul, Matrix.sub_mul, Matrix.add_mulVec, Matrix.sub_mulVec,
          Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mul, Matrix.one_mul]
        congr 1
        rw [← Matrix.mulVec_mulVec]
        ext i
        have := hsumvec m α
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, one_mul, Matrix.smul_apply, Matrix.one_apply,
          smul_eq_mul, mul_one] at this ⊢
        rw [this, hφ]
        simp
  obtain ⟨α, h1, h2⟩ := key m
  have hM' : M = (-Formalism.REAL.Amat (fun c => -χ c + ((n : ℂ) - 1) / 2))ᵀ := by
    ext a b
    simp only [hM, hAm, Formalism.REAL.Amat, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.of_apply, Matrix.transpose_apply, Matrix.neg_apply, smul_eq_mul]
    rcases lt_trichotomy a b with h | rfl | h
    · simp [h, h.ne, h.ne', not_lt.2 h.le]
    · simp
      ring
    · simp [h, h.ne, h.ne', not_lt.2 h.le]
  have hval : ∑ j ∈ Finset.range (m + 1), α j * gelfVal χ j = (-1) ^ m * gelfVal (fun a => -χ a) m := by
    rw [← hsumvec m α, h2, sum_mulVec_one_eq_sum_entries, hM', ← Matrix.transpose_pow]
    have hneg : (-Formalism.REAL.Amat (fun c => -χ c + ((n : ℂ) - 1) / 2)) ^ m =
        ((-1 : ℂ) ^ m) • Formalism.REAL.Amat (fun c => -χ c + ((n : ℂ) - 1) / 2) ^ m := by
      rw [← _root_.smul_pow, neg_one_smul]
    rw [hneg]
    simp only [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, gelfVal, Finset.mul_sum]
    exact Finset.sum_comm
  rw [LinearMap.sum_apply]
  simp only [h1]
  rw [Finset.sum_comm]
  simp only [← Finset.smul_sum, ← LinearMap.sum_apply, hv, smul_smul, ← Finset.sum_smul]
  rw [hval]

variable {n : ℕ}

open GlobalTheory.CapelliCentral in

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil`. Introduce `g hg`. Simplify `h g hg` using `[Formalism.REAL.Eword]`. Consider the case `cons p w ih`.

Introduce `g hg`. Simplify using `only [List.map_cons, List.prod_cons, Module.End.mul_apply, Formalism.REAL.Eword]`. Rewrite using `[eabEnd_apply p.1 p.2 _ ih hg, Formalism.REAL.eabV_eq]`.
-/
lemma word_apply {ε : Fin n → Bool} (w : List (Fin n × Fin n)) (F : smoothSpace ε ℂ) {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ g, inUJ ε g → F.1 g = f g) :
    ∀ g, inUJ ε g → ((w.map fun p => eabEnd ε ℂ p.1 p.2).prod F).1 g = Eword ε w f g := by
  induction w with
  | nil =>
    intro g hg
    simpa [Formalism.REAL.Eword] using h g hg
  | cons p w ih =>
    intro g hg
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, Formalism.REAL.Eword]
    rw [eabEnd_apply p.1 p.2 _ ih hg, Formalism.REAL.eabV_eq]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `i j`. Rewrite using `[pow_succ, pow_zero, Matrix.one_mul, Matrix.of_apply]`. Rewrite using `[Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n)) _ (fun c => if c = i then E c j else 0) (fun a => by simp [Fin.snoc, Equiv.funUnique, Fin.default_eq_zero])]`.

Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `i j`. Rewrite using `[pow_succ, Matrix.mul_apply]`. Repeatedly rewrite using `[ih, Finset.sum_mul, ite_mul, zero_mul]`.

Rewrite using `[← (Fin.snocEquiv (fun _ => Fin n)).sum_comp, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Establish `h0 : (Fin.snoc a c : Fin (k + 2) → Fin n) 0 = a 0`. Simplify `Fin.snoc_castSucc (α := fun _ => Fin n) c a 0` using `only [Fin.castSucc_zero]`. Simplify using `only [Fin.snocEquiv, Equiv.coe_fn_mk, h0]`.

Use `split_ifs with hi`. Use `conv_rhs => rw [List.ofFn_succ', List.prod_concat]`. Simplify using `only [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_last, Fin.succ_last, Matrix.of_apply]`. Both sides reduce to the same expression.
-/
private lemma matrix_of_pow_succ_apply_eq_sum_prod {A : Type} [Ring A] (E : Fin n → Fin n → A) (k : ℕ) :
    ∀ i j : Fin n, (Matrix.of E ^ (k + 1)) i j = ∑ a : Fin (k + 1) → Fin n, if a 0 = i then
      (List.ofFn fun t : Fin (k + 1) =>
        E ((Fin.snoc a j : Fin (k + 2) → Fin n) t.castSucc) ((Fin.snoc a j : Fin (k + 2) → Fin n) t.succ)).prod
      else 0 := by
  induction k with
  | zero =>
    intro i j
    rw [pow_succ, pow_zero, Matrix.one_mul, Matrix.of_apply]
    rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n)) _ (fun c => if c = i then E c j else 0)
      (fun a => by simp [Fin.snoc, Equiv.funUnique, Fin.default_eq_zero])]
    simp
  | succ k ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    simp_rw [ih, Finset.sum_mul, ite_mul, zero_mul]
    rw [← (Fin.snocEquiv (fun _ => Fin n)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
    have h0 : (Fin.snoc a c : Fin (k + 2) → Fin n) 0 = a 0 := by
      simpa only [Fin.castSucc_zero] using Fin.snoc_castSucc (α := fun _ => Fin n) c a 0
    simp only [Fin.snocEquiv, Equiv.coe_fn_mk, h0]
    split_ifs with hi
    · conv_rhs => rw [List.ofFn_succ', List.prod_concat]
      simp only [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_last, Fin.succ_last, Matrix.of_apply]
    · rfl

/- English proof (translation)
Repeatedly rewrite using `[matrix_of_pow_succ_apply_eq_sum_prod E m]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_ite_eq]`. Simplify using `only [Finset.mem_univ, if_true, cycWord, List.map_ofFn]`.

Use `congr 1`. Use `List.ofFn_inj.mpr ?_` and prove the remaining obligations. Use function extensionality and compare the values at `t`. Simplify using `only [Function.comp_apply]`. Distinguish the cases in `ht : t = Fin.last m`.

Substitute `ht` using the available equality. Simplify using `[Fin.snoc_last]`. Establish `hs : t.succ = (finRotate (m + 1) t).castSucc`. Use `ext`. Simplify using `[Fin.val_add_one_of_lt (Fin.lt_last_iff_ne_last.2 ht)]`.

Rewrite using `[hs, Fin.snoc_castSucc, Fin.snoc_castSucc]`.
-/
lemma sum_cycWord {A : Type} [Ring A] (E : Fin n → Fin n → A) (m : ℕ) :
    ∑ a : Fin (m + 1) → Fin n, ((cycWord a).map fun p => E p.1 p.2).prod = ∑ c, (Matrix.of E ^ (m + 1)) c c := by
  simp_rw [matrix_of_pow_succ_apply_eq_sum_prod E m]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true, cycWord, List.map_ofFn]
  congr 1
  refine List.ofFn_inj.mpr ?_
  funext t
  simp only [Function.comp_apply]
  by_cases ht : t = Fin.last m
  · subst ht
    simp [Fin.snoc_last]
  · have hs : t.succ = (finRotate (m + 1) t).castSucc := by
      ext
      simp [Fin.val_add_one_of_lt (Fin.lt_last_iff_ne_last.2 ht)]
    rw [hs, Fin.snoc_castSucc, Fin.snoc_castSucc]

open GlobalTheory.CapelliCentral in

/- English proof (translation)
Rewrite using `[← sum_cycWord, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]`. Unfold `gelf`. Conclude with `Finset.sum_congr rfl fun a _ => word_apply (cycWord a) F h g hg`.
-/
lemma gelf_apply {ε : Fin n → Bool} (m : ℕ) (F : smoothSpace ε ℂ) {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ g, inUJ ε g → F.1 g = f g) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    ((∑ c, (Matrix.of (eabEnd ε ℂ) ^ (m + 1)) c c) F).1 g = gelf ε m f g := by
  rw [← sum_cycWord, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  unfold gelf
  exact Finset.sum_congr rfl fun a _ => word_apply (cycWord a) F h g hg

open GlobalTheory.CapelliCentral in
/- English proof (translation)
Consider the cases of `k with`. Consider the case `zero`. Apply `ext_on` to reduce the goal to its premises. Introduce `g hg`. Simplify using `[gelfVal, Matrix.one_apply, mk_apply f h.1 hg]`.

Consider the case `succ m`. Apply `ext_on` to reduce the goal to its premises. Introduce `g hg`. Rewrite using `[gelf_apply m _ (fun g' hg' => mk_apply f h.1 hg') hg, h.2 m g hg]`. Simplify using `[mk_apply f h.1 hg]`.
-/
lemma gelf_mk {ε : Fin n → Bool} {χ : Fin n → ℂ} {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (h : IsZEigen ε χ f) (k : ℕ) :
    (∑ c, (Matrix.of (eabEnd ε ℂ) ^ k) c c) (mk f h.1) = gelfVal χ k • mk f h.1 := by
  cases k with
  | zero =>
    apply ext_on
    intro g hg
    simp [gelfVal, Matrix.one_apply, mk_apply f h.1 hg]
  | succ m =>
    apply ext_on
    intro g hg
    rw [gelf_apply m _ (fun g' hg' => mk_apply f h.1 hg') hg, h.2 m g hg]
    simp [mk_apply f h.1 hg]

/- English proof (translation)
Unfold `Formalism.REAL.Rd`. Establish `h : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • -X))) = fun t : ℝ => (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) (-t)`. Use function extensionality and compare the values at `t`. Simplify using `only [Complex.ofReal_neg, neg_smul, smul_neg]`. Rewrite using `[h]`.

Conclude with `(deriv_comp_neg (f := fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) (x := (0 : ℝ))).trans (by rw [neg_zero])`.
-/
lemma Rd_neg (X : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) : Rd (-X) f g = -Rd X f g := by
  unfold Formalism.REAL.Rd
  have h : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • -X))) =
      fun t : ℝ => (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) (-t) := by
    funext t
    simp only [Complex.ofReal_neg, neg_smul, smul_neg]
  rw [h]
  exact (deriv_comp_neg (f := fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) (x := (0 : ℝ))).trans
    (by rw [neg_zero])

/- English proof (translation)
Unfold `Formalism.REAL.Rd`. Establish `h : (fun t : ℝ => c * f ((g * NormedSpace.exp ((t : ℂ) • X)).map star)) = fun t : ℝ => c * f (g.map star * NormedSpace.exp ((t : ℂ) • X.map star))`. Use function extensionality and compare the values at `t`. Rewrite using `[map_star_mul, exp_star]`. Use `congr 4`.

Use extensionality with `i j`. Simplify using `[Matrix.map_apply, Matrix.smul_apply, Complex.conj_ofReal]`. Simplify using `only [h]`. Conclude with `deriv_const_mul_field c`.
-/
lemma Rd_conj (X : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (c : ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Rd X (fun x => c * f (x.map star)) g = c * Rd (X.map star) f (g.map star) := by
  unfold Formalism.REAL.Rd
  have h : (fun t : ℝ => c * f ((g * NormedSpace.exp ((t : ℂ) • X)).map star)) =
      fun t : ℝ => c * f (g.map star * NormedSpace.exp ((t : ℂ) • X.map star)) := by
    funext t
    rw [map_star_mul, exp_star]
    congr 4
    ext i j
    simp [Matrix.map_apply, Matrix.smul_apply, Complex.conj_ofReal]
  simp only [h]
  exact deriv_const_mul_field c

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Formalism.REAL.Jm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.single_apply, Formalism.REAL.sgn, smul_eq_mul]`. Distinguish the cases in `h : b = i ∧ a = j`. Take `⟨rfl, rfl⟩` from `h`. Apply the tactic sequence `by_cases ha : ε a <;> by_cases hb : ε b <;> simp [ha, hb]`.

Establish `h' : ¬ (a = j ∧ b = i)` using `fun h'' => h ⟨h''.2, h''.1⟩`. Simplify using `[h, h']`.
-/
lemma Jm_single (ε : Fin n → Bool) (a b : Fin n) :
    Jm ε * (Matrix.single a b (1 : ℂ))ᴴ * Jm ε = ((Formalism.REAL.sgn ε a b : ℝ) : ℂ) • Matrix.single b a (1 : ℂ) := by
  ext i j
  simp only [Formalism.REAL.Jm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply,
    Matrix.smul_apply, Matrix.single_apply, Formalism.REAL.sgn, smul_eq_mul]
  by_cases h : b = i ∧ a = j
  · obtain ⟨rfl, rfl⟩ := h
    by_cases ha : ε a <;> by_cases hb : ε b <;> simp [ha, hb]
  · have h' : ¬ (a = j ∧ b = i) := fun h'' => h ⟨h''.2, h''.1⟩
    simp [h, h']

/- English proof (translation)
Break down `hr with rfl | rfl` into its components or cases. Simplify using the standard rewrite rules. Simplify using `only [Complex.ofReal_neg, Complex.ofReal_one, neg_smul, one_smul, Rd_neg]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma rd_smul_sign_eq_mul (Y : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) (hr : r = 1 ∨ r = -1) :
    Rd ((r : ℂ) • Y) f g = r * Rd Y f g := by
  rcases hr with rfl | rfl
  · simp
  · simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_smul, one_smul, Rd_neg]
    ring

/- English proof (translation)
Simplify using `only [Formalism.REAL.cpart1, Formalism.REAL.cpart2, Jm_single]`. Establish `hs : Formalism.REAL.sgn ε b a = Formalism.REAL.sgn ε a b`. Simplify using `only [Formalism.REAL.sgn, eq_comm]`. Rewrite using `[hs]`. Distinguish the cases in `hab : ε a = ε b`.

Establish `h1 : Formalism.REAL.sgn ε a b = 1` using `by simp [Formalism.REAL.sgn, hab]`. Rewrite using `[h1]`. Apply the tactic sequence `constructor <;> ext i j <;>`. Apply the tactic sequence `simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.single_apply, smul_eq_mul] <;> split_ifs <;> simp`. Establish `h1 : Formalism.REAL.sgn ε a b = -1` using `by simp [Formalism.REAL.sgn, hab]`.

Rewrite using `[h1]`. Apply the tactic sequence `constructor <;> ext i j <;>`. Apply the tactic sequence `simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.single_apply, smul_eq_mul] <;> split_ifs <;> simp`.
-/
private lemma map_star_cpart_single_eq_neg_sgn_smul_swap (ε : Fin n → Bool) (a b : Fin n) :
    (Formalism.REAL.cpart1 ε (Matrix.single a b 1)).map star =
              ((-Formalism.REAL.sgn ε a b : ℝ) : ℂ) • Formalism.REAL.cpart1 ε (Matrix.single b a 1) ∧
      (Formalism.REAL.cpart2 ε (Matrix.single a b 1)).map star =
        ((-Formalism.REAL.sgn ε a b : ℝ) : ℂ) • Formalism.REAL.cpart2 ε (Matrix.single b a 1) := by
  simp only [Formalism.REAL.cpart1, Formalism.REAL.cpart2, Jm_single]
  have hs : Formalism.REAL.sgn ε b a = Formalism.REAL.sgn ε a b := by
    simp only [Formalism.REAL.sgn, eq_comm]
  rw [hs]
  by_cases hab : ε a = ε b
  · have h1 : Formalism.REAL.sgn ε a b = 1 := by simp [Formalism.REAL.sgn, hab]
    rw [h1]
    constructor <;> ext i j <;>
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.single_apply,
        smul_eq_mul] <;> split_ifs <;> simp
  · have h1 : Formalism.REAL.sgn ε a b = -1 := by simp [Formalism.REAL.sgn, hab]
    rw [h1]
    constructor <;> ext i j <;>
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.single_apply,
        smul_eq_mul] <;> split_ifs <;> simp

/- English proof (translation)
Take `⟨h1, h2⟩` from `map_star_cpart_single_eq_neg_sgn_smul_swap ε a b`. Establish `hr : (-Formalism.REAL.sgn ε a b) = 1 ∨ (-Formalism.REAL.sgn ε a b) = -1`. Unfold `Formalism.REAL.sgn`. Apply the tactic sequence `split_ifs <;> norm_num`. Simplify using `only [Formalism.REAL.Eab, Formalism.REAL.Ec, Rd_conj, h1, h2, rd_smul_sign_eq_mul _ _ _ _ hr]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma Eab_conj (ε : Fin n → Bool) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (c : ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Eab ε a b (fun x => c * f (x.map star)) g =
      -((Formalism.REAL.sgn ε a b : ℝ) : ℂ) * c * Eab ε b a f (g.map star) := by
  obtain ⟨h1, h2⟩ := map_star_cpart_single_eq_neg_sgn_smul_swap ε a b
  have hr : (-Formalism.REAL.sgn ε a b) = 1 ∨ (-Formalism.REAL.sgn ε a b) = -1 := by
    unfold Formalism.REAL.sgn
    split_ifs <;> norm_num
  simp only [Formalism.REAL.Eab, Formalism.REAL.Ec, Rd_conj, h1, h2, rd_smul_sign_eq_mul _ _ _ _ hr]
  push_cast
  ring

/- English proof (translation)
Use `set e : Fin n → ℂ := fun x => if ε x then 1 else -1 with he`. Establish `hs : ∀ x y, -((Formalism.REAL.sgn ε x y : ℝ) : ℂ) = -1 * (e x * e y)`. Introduce `x y`. Simplify using `only [he, Formalism.REAL.sgn]`. Apply the tactic sequence `by_cases hx : ε x <;> by_cases hy : ε y <;> simp [hx, hy]`.

Establish `hr : ∏ i, e (a (finRotate (m + 1) i)) = ∏ i, e (a i)` using `Fintype.prod_equiv (finRotate (m + 1)) _ _ (fun _ => rfl)`. Establish `h1 : (∏ i, e (a i)) * ∏ i, e (a i) = 1`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Simplify using `only [he]`.

Apply the tactic sequence `split_ifs <;> norm_num`. Simplify using `only [cycWord, List.map_ofFn, List.prod_ofFn, Function.comp_def, hs]`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_mul_distrib, hr, h1, mul_one]`.
-/
lemma sgn_cycWord (ε : Fin n → Bool) {m : ℕ} (a : Fin (m + 1) → Fin n) :
    ((cycWord a).map fun p => -((Formalism.REAL.sgn ε p.1 p.2 : ℝ) : ℂ)).prod = (-1) ^ (m + 1) := by
  set e : Fin n → ℂ := fun x => if ε x then 1 else -1 with he
  have hs : ∀ x y, -((Formalism.REAL.sgn ε x y : ℝ) : ℂ) = -1 * (e x * e y) := by
    intro x y
    simp only [he, Formalism.REAL.sgn]
    by_cases hx : ε x <;> by_cases hy : ε y <;> simp [hx, hy]
  have hr : ∏ i, e (a (finRotate (m + 1) i)) = ∏ i, e (a i) :=
    Fintype.prod_equiv (finRotate (m + 1)) _ _ (fun _ => rfl)
  have h1 : (∏ i, e (a i)) * ∏ i, e (a i) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ => ?_
    simp only [he]
    split_ifs <;> norm_num
  simp only [cycWord, List.map_ofFn, List.prod_ofFn, Function.comp_def, hs]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_mul_distrib, hr, h1, mul_one]

/- English proof (translation)
Unfold `Formalism.REAL.Jm`. Rewrite using `[Matrix.submatrix_diagonal_equiv]`. Both sides reduce to the same expression.
-/
lemma Jm_perm (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) : Jm (ε ∘ s) = (Jm ε).submatrix s s := by
  unfold Formalism.REAL.Jm
  rw [Matrix.submatrix_diagonal_equiv]
  rfl

/- English proof (translation)
Establish `h' : Formalism.REAL.inUJ ε g` using `h`. Use `show Formalism.REAL.inUJ (ε ∘ s) (g.submatrix s s)`. Unfold `Formalism.REAL.inUJ at h' ⊢`. Rewrite using `[Jm_perm, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h']`.
-/
lemma UJ_perm {ε : Fin n → Bool} (s : Equiv.Perm (Fin n)) {g : Matrix (Fin n) (Fin n) ℂ} (h : g ∈ UJset ε) :
    g.submatrix s s ∈ UJset (ε ∘ s) := by
  have h' : Formalism.REAL.inUJ ε g := h
  show Formalism.REAL.inUJ (ε ∘ s) (g.submatrix s s)
  unfold Formalism.REAL.inUJ at h' ⊢
  rw [Jm_perm, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h']

/- English proof (translation)
Take `⟨hu, hc⟩` from `h`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite `hu`, the goal using `[Matrix.mem_unitaryGroup_iff]`. Rewrite using `[Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, ← Matrix.star_eq_conjTranspose, hu, Matrix.submatrix_one_equiv]`. Rewrite using `[Jm_perm, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hc]`.
-/
lemma K_perm {ε : Fin n → Bool} (s : Equiv.Perm (Fin n)) {g : Matrix (Fin n) (Fin n) ℂ} (h : g ∈ Kset ε) :
    g.submatrix s s ∈ Kset (ε ∘ s) := by
  obtain ⟨hu, hc⟩ := h
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff] at hu ⊢
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      ← Matrix.star_eq_conjTranspose, hu, Matrix.submatrix_one_equiv]
  · rw [Jm_perm, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hc]

/- English proof (translation)
Establish `hconj : ∀ Y : Matrix (Fin n) (Fin n) ℂ, Y.submatrix s s = (1 : Matrix (Fin n) (Fin n) ℂ).submatrix s id * Y * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id s`. Introduce `Y`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Matrix.one_apply]`. Establish `hPQ : (1 : Matrix (Fin n) (Fin n) ℂ).submatrix s id * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id s = 1`.

Use `hconj 1` as an intermediate fact. Rewrite `this` using `[Matrix.mul_one]`. Rewrite using `[← this, Matrix.submatrix_one_equiv]`. Establish `hQP : (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id s * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix s id = 1` using `mul_eq_one_comm.mp hPQ`. Establish `hinv : ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix s id)⁻¹ = (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id s` using `Matrix.inv_eq_right_inv hPQ`.

Establish `hU : IsUnit ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix s id)` using `⟨⟨_, _, hPQ, hQP⟩, rfl⟩`. Rewrite using `[hconj, hconj, ← hinv, Matrix.exp_conj _ _ hU]`.
-/
lemma exp_perm (s : Equiv.Perm (Fin n)) (X : Matrix (Fin n) (Fin n) ℂ) :
    (NormedSpace.exp X).submatrix s s = NormedSpace.exp (X.submatrix s s) := by
  have hconj : ∀ Y : Matrix (Fin n) (Fin n) ℂ, Y.submatrix s s =
      (1 : Matrix (Fin n) (Fin n) ℂ).submatrix s id * Y * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id s := by
    intro Y
    ext i j
    simp [Matrix.mul_apply, Matrix.one_apply]
  have hPQ : (1 : Matrix (Fin n) (Fin n) ℂ).submatrix s id * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id s = 1 := by
    have := hconj 1
    rw [Matrix.mul_one] at this
    rw [← this, Matrix.submatrix_one_equiv]
  have hQP : (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id s * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix s id = 1 :=
    mul_eq_one_comm.mp hPQ
  have hinv : ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix s id)⁻¹ = (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id s :=
    Matrix.inv_eq_right_inv hPQ
  have hU : IsUnit ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix s id) := ⟨⟨_, _, hPQ, hQP⟩, rfl⟩
  rw [hconj, hconj, ← hinv, Matrix.exp_conj _ _ hU]

/- English proof (translation)
Unfold `Formalism.REAL.Rd`. Use `congr 1`. Use function extensionality and compare the values at `t`. Use `beta_reduce`. Rewrite using `[← Matrix.submatrix_mul_equiv (e₂ := s), exp_perm]`.

Both sides reduce to the same expression.
-/
private lemma rd_submatrix_perm (s : Equiv.Perm (Fin n)) (X : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Rd X (fun x => f (x.submatrix s s)) g = Rd (X.submatrix s s) f (g.submatrix s s) := by
  unfold Formalism.REAL.Rd
  congr 1
  funext t
  beta_reduce
  rw [← Matrix.submatrix_mul_equiv (e₂ := s), exp_perm]
  rfl

/- English proof (translation)
Establish `hsub : ∀ A B : Matrix (Fin n) (Fin n) ℂ, (A - B).submatrix s s = A.submatrix s s - B.submatrix s s` using `fun _ _ => rfl`. Establish `hsm : ∀ (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ), (c • A).submatrix s s = c • A.submatrix s s` using `fun _ _ => rfl`. Simplify using `only [Formalism.REAL.cpart1, hsm, hsub, Jm_perm, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]`.
-/
private lemma cpart1_submatrix_perm (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) (Z : Matrix (Fin n) (Fin n) ℂ) :
    (Formalism.REAL.cpart1 ε Z).submatrix s s = Formalism.REAL.cpart1 (ε ∘ s) (Z.submatrix s s) := by
  have hsub : ∀ A B : Matrix (Fin n) (Fin n) ℂ, (A - B).submatrix s s = A.submatrix s s - B.submatrix s s :=
    fun _ _ => rfl
  have hsm : ∀ (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ), (c • A).submatrix s s = c • A.submatrix s s :=
    fun _ _ => rfl
  simp only [Formalism.REAL.cpart1, hsm, hsub, Jm_perm,
    Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]

/- English proof (translation)
Establish `hadd : ∀ A B : Matrix (Fin n) (Fin n) ℂ, (A + B).submatrix s s = A.submatrix s s + B.submatrix s s` using `fun _ _ => rfl`. Establish `hsm : ∀ (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ), (c • A).submatrix s s = c • A.submatrix s s` using `fun _ _ => rfl`. Simplify using `only [Formalism.REAL.cpart2, hsm, hadd, Jm_perm, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]`.
-/
private lemma cpart2_submatrix_perm (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) (Z : Matrix (Fin n) (Fin n) ℂ) :
    (Formalism.REAL.cpart2 ε Z).submatrix s s = Formalism.REAL.cpart2 (ε ∘ s) (Z.submatrix s s) := by
  have hadd : ∀ A B : Matrix (Fin n) (Fin n) ℂ, (A + B).submatrix s s = A.submatrix s s + B.submatrix s s :=
    fun _ _ => rfl
  have hsm : ∀ (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ), (c • A).submatrix s s = c • A.submatrix s s :=
    fun _ _ => rfl
  simp only [Formalism.REAL.cpart2, hsm, hadd, Jm_perm,
    Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]

/- English proof (translation)
Establish `hsg : (Matrix.single (s a) (s b) (1 : ℂ)).submatrix s s = Matrix.single a b 1`. Use extensionality with `i j`. Simplify using `[Matrix.single_apply, s.injective.eq_iff]`. Simplify using `only [Formalism.REAL.Eab, Formalism.REAL.Ec, rd_submatrix_perm, cpart1_submatrix_perm, cpart2_submatrix_perm, hsg]`.
-/
lemma Eab_perm (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Eab ε (s a) (s b) (fun x => f (x.submatrix s s)) g = Eab (ε ∘ s) a b f (g.submatrix s s) := by
  have hsg : (Matrix.single (s a) (s b) (1 : ℂ)).submatrix s s = Matrix.single a b 1 := by
    ext i j
    simp [Matrix.single_apply, s.injective.eq_iff]
  simp only [Formalism.REAL.Eab, Formalism.REAL.Ec, rd_submatrix_perm, cpart1_submatrix_perm, cpart2_submatrix_perm, hsg]

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => rfl`. Consider the case `cons p w ih`. Use function extensionality and compare the values at `g`. Simplify using `only [List.map_cons, Formalism.REAL.Eword]`.

Rewrite using `[ih]`. Conclude with `Eab_perm ε s p.1 p.2 _ g`.
-/
lemma Eword_perm (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (w : List (Fin n × Fin n)) :
    Eword ε (w.map fun p => (s p.1, s p.2)) (fun x => f (x.submatrix s s)) =
      fun g => Eword (ε ∘ s) w f (g.submatrix s s) := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    funext g
    simp only [List.map_cons, Formalism.REAL.Eword]
    rw [ih]
    exact Eab_perm ε s p.1 p.2 _ g

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
/- English proof (translation)
Take `⟨hsm, hev⟩` from `h`. Establish `hc : ∀ {k : WithTop ℕ∞}, ContDiff ℝ k (fun x : Matrix (Fin n) (Fin n) ℂ => x.submatrix s s)` using `contDiff_pi.2 fun i => contDiff_pi.2 fun j => contDiff_apply_apply ℝ ℂ (s i) (s j)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `g₀ hg₀`. Take `⟨U, F, hU, hgU, hF, hfF⟩` from `hsm (g₀.submatrix s s) (UJ_perm s hg₀)`.

Conclude with `⟨(fun x : Matrix (Fin n) (Fin n) ℂ => x.submatrix s s) ⁻¹' U, fun x => F (x.submatrix s s), hU.preimage (hc (k := 0)).continuous, hgU, hF.comp hc.contDiffOn (fun x hx => hx), fun g hg hgu => hfF _ hg (UJ_perm s hgu)⟩`. Introduce `m g hg`. Establish `hg' : g.submatrix s s ∈ UJset (ε ∘ s)` using `UJ_perm s hg`. Establish `key : gelf ε m (fun x => f (x.submatrix s s)) g = gelf (ε ∘ s) m f (g.submatrix s s)`. Unfold `gelf`.

Use `symm`. Use `Fintype.sum_equiv (Equiv.piCongrRight fun _ => s) _ _ (fun a => ?_)` and prove the remaining obligations. Establish `hw : cycWord ((Equiv.piCongrRight fun _ => s) a) = (cycWord a).map fun p => (s p.1, s p.2)`. Simplify using `[cycWord, List.map_ofFn, Function.comp_def]`. Rewrite using `[hw, Eword_perm]`.

Rewrite using `[key, hev m _ hg']`.
-/
lemma isZEigen_perm {ε : Fin n → Bool} (s : Equiv.Perm (Fin n)) {χ : Fin n → ℂ} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : IsZEigen (ε ∘ s) χ f) : IsZEigen ε χ (fun x => f (x.submatrix s s)) := by
  obtain ⟨hsm, hev⟩ := h
  have hc : ∀ {k : WithTop ℕ∞}, ContDiff ℝ k (fun x : Matrix (Fin n) (Fin n) ℂ => x.submatrix s s) :=
    contDiff_pi.2 fun i => contDiff_pi.2 fun j => contDiff_apply_apply ℝ ℂ (s i) (s j)
  refine ⟨?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hsm (g₀.submatrix s s) (UJ_perm s hg₀)
    exact ⟨(fun x : Matrix (Fin n) (Fin n) ℂ => x.submatrix s s) ⁻¹' U, fun x => F (x.submatrix s s),
      hU.preimage (hc (k := 0)).continuous, hgU, hF.comp hc.contDiffOn (fun x hx => hx),
      fun g hg hgu => hfF _ hg (UJ_perm s hgu)⟩
  · intro m g hg
    have hg' : g.submatrix s s ∈ UJset (ε ∘ s) := UJ_perm s hg
    have key : gelf ε m (fun x => f (x.submatrix s s)) g = gelf (ε ∘ s) m f (g.submatrix s s) := by
      unfold gelf
      symm
      refine Fintype.sum_equiv (Equiv.piCongrRight fun _ => s) _ _ (fun a => ?_)
      have hw : cycWord ((Equiv.piCongrRight fun _ => s) a) = (cycWord a).map fun p => (s p.1, s p.2) := by
        simp [cycWord, List.map_ofFn, Function.comp_def]
      rw [hw, Eword_perm]
    rw [key, hev m _ hg']

/- English proof (translation)
Introduce `n ε χ f hf hz m g hg`. Establish `hT` using `trace_transpose_pow (GlobalTheory.CapelliCentral.eabEnd ε ℂ) GlobalTheory.CapelliCentral.eabEnd_glRel χ (GlobalTheory.CapelliCentral.mk f hz.1) (fun k => gelf_mk hz k) (m + 1)`. Establish `h2` using `congrArg (fun F : GlobalTheory.CapelliCentral.smoothSpace ε ℂ => F.1 g) hT`. Rewrite `h2` using `[← sum_cycWord (fun a b => GlobalTheory.CapelliCentral.eabEnd ε ℂ b a), LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]`. Rewrite `h2` using `[Submodule.coe_smul, Pi.smul_apply, GlobalTheory.CapelliCentral.mk_apply f hz.1 hg, smul_eq_mul]`.

Rewrite using `[← h2]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Establish `hw : ((cycWord a).map fun p => GlobalTheory.CapelliCentral.eabEnd ε ℂ p.2 p.1) = (((cycWord a).map Prod.swap).map fun p => GlobalTheory.CapelliCentral.eabEnd ε ℂ p.1 p.2)`. Simplify using `[List.map_map, Function.comp_def]`. Rewrite using `[hw, word_apply ((cycWord a).map Prod.swap) (GlobalTheory.CapelliCentral.mk f hz.1) (fun g' hg' => GlobalTheory.CapelliCentral.mk_apply f hz.1 hg') g hg]`.
-/
theorem trWord : ∀ (n : ℕ) (ε : Fin n → Bool) (χ : Fin n → ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ), SmoothOnG ε f → IsZEigen ε χ f → ∀ m : ℕ, ∀ g ∈ UJset ε, ∑ a : Fin (m + 1) → Fin n, Eword ε ((cycWord a).map Prod.swap) f g = (-1) ^ (m + 1) * gelfVal (fun a => -χ a) (m + 1) * f g := by
  intro n ε χ f hf hz m g hg
  have hT := trace_transpose_pow (GlobalTheory.CapelliCentral.eabEnd ε ℂ) GlobalTheory.CapelliCentral.eabEnd_glRel χ (GlobalTheory.CapelliCentral.mk f hz.1) (fun k => gelf_mk hz k) (m + 1)
  have h2 := congrArg (fun F : GlobalTheory.CapelliCentral.smoothSpace ε ℂ => F.1 g) hT
  rw [← sum_cycWord (fun a b => GlobalTheory.CapelliCentral.eabEnd ε ℂ b a), LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply] at h2
  rw [Submodule.coe_smul, Pi.smul_apply, GlobalTheory.CapelliCentral.mk_apply f hz.1 hg, smul_eq_mul] at h2
  rw [← h2]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hw : ((cycWord a).map fun p => GlobalTheory.CapelliCentral.eabEnd ε ℂ p.2 p.1) =
      (((cycWord a).map Prod.swap).map fun p => GlobalTheory.CapelliCentral.eabEnd ε ℂ p.1 p.2) := by
    simp [List.map_map, Function.comp_def]
  rw [hw, word_apply ((cycWord a).map Prod.swap) (GlobalTheory.CapelliCentral.mk f hz.1) (fun g' hg' => GlobalTheory.CapelliCentral.mk_apply f hz.1 hg') g hg]

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil`. Use function extensionality and compare the values at `g`. Simplify using `[Formalism.REAL.Eword]`. Consider the case `cons p w ih`.

Use function extensionality and compare the values at `g`. Simplify using `only [List.map_cons, List.prod_cons, Formalism.REAL.Eword]`. Rewrite using `[ih, Eab_conj]`. Simplify using `only [Prod.fst_swap, Prod.snd_swap]`.
-/
private lemma eword_map_star_eq_prod_neg_sgn_mul_swap (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (w : List (Fin n × Fin n)) :
    Formalism.REAL.Eword ε w (fun x => f (x.map star)) = fun g =>
      (w.map fun p => -((Formalism.REAL.sgn ε p.1 p.2 : ℝ) : ℂ)).prod *
        Formalism.REAL.Eword ε (w.map Prod.swap) f (g.map star) := by
  induction w with
  | nil =>
    funext g
    simp [Formalism.REAL.Eword]
  | cons p w ih =>
    funext g
    simp only [List.map_cons, List.prod_cons, Formalism.REAL.Eword]
    rw [ih, Eab_conj]
    simp only [Prod.fst_swap, Prod.snd_swap]

/- English proof (translation)
Introduce `n ε f w g`. Conclude with `congrFun (eword_map_star_eq_prod_neg_sgn_mul_swap ε f w) g`.
-/
theorem wordConj : ∀ (n : ℕ) (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (w : List (Fin n × Fin n)) (g : Matrix (Fin n) (Fin n) ℂ), Eword ε w (fun x => f (x.map star)) g = (w.map fun p => -((Formalism.REAL.sgn ε p.1 p.2 : ℝ) : ℂ)).prod * Eword ε (w.map Prod.swap) f (g.map star) := by
  intro n ε f w g
  exact congrFun (eword_map_star_eq_prod_neg_sgn_mul_swap ε f w) g

/- English proof (translation)
Introduce `n ε χ f hf hz`. Establish `hsm : SmoothOnG ε (fun x => f (x.map star))`. Use `letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedAddCommGroup`. Use `letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedSpace`. Introduce `g₀ hg₀`.

Take `⟨U, F, hU, hgU, hF, hfF⟩` from `hf (g₀.map star) (UJ_star hg₀)`. Establish `hc : ∀ {k : WithTop ℕ∞}, ContDiff ℝ k (fun x : Matrix (Fin n) (Fin n) ℂ => x.map star)` using `contDiff_pi.2 fun i => contDiff_pi.2 fun j => (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp (contDiff_apply_apply ℝ ℂ i j)`. Use `⟨(fun x : Matrix (Fin n) (Fin n) ℂ => x.map star) ⁻¹' U, fun x => F (x.map star), hU.preimage (hc (k := 0)).continuous, by simpa using hgU, hF.comp hc.contDiffOn (fun x hx => hx), ?_⟩` and prove the remaining obligations. Introduce `g hg hgu`. Conclude with `hfF _ hg (UJ_star hgu)`.

Use `⟨hsm, hsm, ?_⟩` and prove the remaining obligations. Introduce `m g hg`. Establish `hg' : g.map star ∈ UJset ε` using `UJ_star hg`. Unfold `gelf`. Simplify using `only [wordConj, sgn_cycWord]`.

Rewrite using `[← Finset.mul_sum, trWord n ε χ f hf hz m _ hg']`. Establish `h1 : ((-1 : ℂ) ^ (m + 1)) * (-1) ^ (m + 1) = 1`. Rewrite using `[← mul_pow]`. Simplify using the standard rewrite rules. Take the linear combination `(gelfVal (fun a => -χ a) (m + 1) * f (g.map star)) * h1`.
-/
theorem eigConj : ∀ (n : ℕ) (ε : Fin n → Bool) (χ : Fin n → ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ), SmoothOnG ε f → IsZEigen ε χ f → SmoothOnG ε (fun x => f (x.map star)) ∧ IsZEigen ε (fun a => -χ a) (fun x => f (x.map star)) := by
  intro n ε χ f hf hz
  have hsm : SmoothOnG ε (fun x => f (x.map star)) := by
    letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedAddCommGroup
    letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedSpace
    intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf (g₀.map star) (UJ_star hg₀)
    have hc : ∀ {k : WithTop ℕ∞}, ContDiff ℝ k (fun x : Matrix (Fin n) (Fin n) ℂ => x.map star) :=
      contDiff_pi.2 fun i => contDiff_pi.2 fun j =>
        (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp (contDiff_apply_apply ℝ ℂ i j)
    refine ⟨(fun x : Matrix (Fin n) (Fin n) ℂ => x.map star) ⁻¹' U, fun x => F (x.map star),
      hU.preimage (hc (k := 0)).continuous, by simpa using hgU, hF.comp hc.contDiffOn (fun x hx => hx), ?_⟩
    intro g hg hgu
    exact hfF _ hg (UJ_star hgu)
  refine ⟨hsm, hsm, ?_⟩
  intro m g hg
  have hg' : g.map star ∈ UJset ε := UJ_star hg
  unfold gelf
  simp only [wordConj, sgn_cycWord]
  rw [← Finset.mul_sum, trWord n ε χ f hf hz m _ hg']
  have h1 : ((-1 : ℂ) ^ (m + 1)) * (-1) ^ (m + 1) = 1 := by
    rw [← mul_pow]
    simp
  linear_combination (gelfVal (fun a => -χ a) (m + 1) * f (g.map star)) * h1

end GlobalTheory.Dec.FormF
