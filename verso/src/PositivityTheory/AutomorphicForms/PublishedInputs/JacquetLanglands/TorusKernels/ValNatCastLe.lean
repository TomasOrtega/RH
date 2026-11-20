import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FirstStatementE

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.adelicTermLemmas

/- English proof (translation)
Establish `key : ∀ n, f (ch a b n) = ch (f a) (f b) n ∧ f (ch a b (n + 1)) = ch (f a) (f b) (n + 1)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp [ch]`. Consider the case `succ n ih`.

Use `⟨ih.2, ?_⟩` and prove the remaining obligations. Simplify using `only [ch, map_sub, map_mul, ih.1, ih.2]`. Conclude with `(key n).1`.
-/
theorem ch_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a b : R) (n : ℕ) :
    f (ch a b n) = ch (f a) (f b) n := by
  have key : ∀ n, f (ch a b n) = ch (f a) (f b) n ∧ f (ch a b (n + 1)) = ch (f a) (f b) (n + 1) := by
    intro n
    induction n with
    | zero => simp [ch]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      simp only [ch, map_sub, map_mul, ih.1, ih.2]
  exact (key n).1

/- English proof (translation)
Establish `key : ∀ n, ch (s * τ) (s ^ 2 * δ) (n + 1) = s ^ n * ch τ δ (n + 1) ∧ ch (s * τ) (s ^ 2 * δ) (n + 2) = s ^ (n + 1) * ch τ δ (n + 2)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp [ch]`. Consider the case `succ n ih`.

Use `⟨ih.2, ?_⟩` and prove the remaining obligations. Establish `e : ch (s * τ) (s ^ 2 * δ) (n + 1 + 2) = s * τ * ch (s * τ) (s ^ 2 * δ) (n + 2) - s ^ 2 * δ * ch (s * τ) (s ^ 2 * δ) (n + 1)` using `rfl`. Establish `e' : ch τ δ (n + 1 + 2) = τ * ch τ δ (n + 2) - δ * ch τ δ (n + 1)` using `rfl`. Rewrite using `[e, e', ih.1, ih.2]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `(key n).1`.
-/
theorem ch_hom {R : Type*} [CommRing R] (s τ δ : R) (n : ℕ) :
    ch (s * τ) (s ^ 2 * δ) (n + 1) = s ^ n * ch τ δ (n + 1) := by
  have key : ∀ n, ch (s * τ) (s ^ 2 * δ) (n + 1) = s ^ n * ch τ δ (n + 1) ∧
      ch (s * τ) (s ^ 2 * δ) (n + 2) = s ^ (n + 1) * ch τ δ (n + 2) := by
    intro n
    induction n with
    | zero => simp [ch]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have e : ch (s * τ) (s ^ 2 * δ) (n + 1 + 2) =
          s * τ * ch (s * τ) (s ^ 2 * δ) (n + 2) - s ^ 2 * δ * ch (s * τ) (s ^ 2 * δ) (n + 1) := rfl
      have e' : ch τ δ (n + 1 + 2) = τ * ch τ δ (n + 2) - δ * ch τ δ (n + 1) := rfl
      rw [e, e', ih.1, ih.2]
      ring
  exact (key n).1

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.ProdSubProdLeOfFactorsClose.main ν s f g m hf hg hfg`.
-/
theorem val_prod_sub {ι : Type*} (ν : Valuation ℂ ℝ≥0) (s : Finset ι) (f g : ι → ℂ) (m : ℝ≥0)
    (hf : ∀ i ∈ s, ν (f i) ≤ 1) (hg : ∀ i ∈ s, ν (g i) ≤ 1) (hfg : ∀ i ∈ s, ν (f i - g i) ≤ m) :
    ν (∏ i ∈ s, f i) ≤ 1 ∧ ν (∏ i ∈ s, g i) ≤ 1 ∧ ν (∏ i ∈ s, f i - ∏ i ∈ s, g i) ≤ m :=
  _root_.UpperTheory.Reformulated.B.ProdSubProdLeOfFactorsClose.main ν s f g m hf hg hfg

open Classical in
/- English proof (translation)
Proceed by induction on `W with`. Consider the case `nil => simp`. Consider the case `cons w W ih`. Rewrite using `[List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons]`. Establish `e : ∀ v, (l : ℂ) ^ (t v * (w :: W).count (D.pl v)) = (if D.pl v = w then (l : ℂ) ^ t v else 1) * (l : ℂ) ^ (t v * W.count (D.pl v))`.

Introduce `v`. Rewrite using `[List.count_cons]`. Distinguish the cases in `h : D.pl v = w`. Substitute `h` using the available equality. Rewrite using `[if_pos rfl]`.

Simplify using `[mul_add, pow_add]`. Apply the tactic sequence `try ring`. Establish `h' : ¬ (w == D.pl v) = true`. Rewrite using `[beq_iff_eq]`. Conclude with `fun e => h e.symm`.

Simplify using `[h, h']`. Simplify using `only [e, Finset.prod_mul_distrib, nz]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem nz_prod {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} (D : LDat F ι) (k₀ : ℕ)
    (t : InfinitePlace F → ℕ) (W : List (Pl F)) :
    (W.map (nz D k₀ t)).prod =
      (W.map fun w => ((((normV w : ℝ) ^ ((k₀ : ℝ) / 2 - 1) : ℝ)) : ℂ)).prod * ∏ v, (l : ℂ) ^ (t v * W.count (D.pl v)) := by
  induction W with
  | nil => simp
  | cons w W ih =>
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons]
    have e : ∀ v, (l : ℂ) ^ (t v * (w :: W).count (D.pl v)) =
        (if D.pl v = w then (l : ℂ) ^ t v else 1) * (l : ℂ) ^ (t v * W.count (D.pl v)) := by
      intro v
      rw [List.count_cons]
      by_cases h : D.pl v = w
      · subst h
        rw [if_pos rfl]
        simp [mul_add, pow_add]
        try ring
      · have h' : ¬ (w == D.pl v) = true := by
          rw [beq_iff_eq]; exact fun e => h e.symm
        simp [h, h']
    simp only [e, Finset.prod_mul_distrib, nz]
    ring

/- English proof (translation)
Take `⟨n, rfl⟩ : ∃ n, k₀ = n + 2` from `⟨k₀ - 2, by omega⟩`. Establish `e0 : n + 2 - 1 = n + 1` using `by omega`. Establish `e1 : n + 2 + 2 * t - 1 = (n + 2 * t) + 1` using `by omega`. Rewrite using `[e0, e1]`. Take `⟨A1, A2⟩` from `hG ν τ δ hτ hδ1 n`.

Take `⟨B1, B2⟩` from `hG ν τ δ hτ hδ1 (n + 2 * t)`. Establish `hUt : ν (U ^ t) ≤ 1` using `by rw [map_pow]; exact pow_le_one₀ (by positivity) hU1`. Use `⟨A1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `mul_le_one' B1 hUt`.

Establish `e : ch τ δ (n + 1) - ch τ δ (n + 2 * t + 1) * U ^ t = (ch τ δ (n + 1) - τ ^ n) + (τ ^ n * (1 - τ ^ (2 * t))) + (τ ^ (n + 2 * t) - ch τ δ (n + 2 * t + 1)) + ch τ δ (n + 2 * t + 1) * (1 - U ^ t)` using `by ring`. Rewrite using `[e]`. Establish `hτn : ν (τ ^ n) ≤ 1` using `by rw [map_pow]; exact pow_le_one₀ (by positivity) hτ`. Use `ν.map_add_le (ν.map_add_le (ν.map_add_le (A2.trans hδ) ?_) ?_) ?_` and prove the remaining obligations. Rewrite using `[map_mul, ν.map_sub_swap]`.

Conclude with `(mul_le_of_le_one_left (by positivity) hτn).trans hτt`. Rewrite using `[ν.map_sub_swap]`. Conclude with `B2.trans hδ`. Rewrite using `[map_mul, ν.map_sub_swap]`. Conclude with `(mul_le_of_le_one_left (by positivity) B1).trans hU`.
-/
theorem local_cong (ν : Valuation ℂ ℝ≥0) (hG : GCh) (τ δ U : ℂ) (m : ℝ≥0) (k₀ t : ℕ) (hk : 2 ≤ k₀) (hτ : ν τ ≤ 1)
    (hδ1 : ν δ ≤ 1) (hδ : ν δ ≤ m) (hτt : ν (τ ^ (2 * t) - 1) ≤ m) (hU1 : ν U ≤ 1) (hU : ν (U ^ t - 1) ≤ m) :
    ν (ch τ δ (k₀ - 1)) ≤ 1 ∧ ν (ch τ δ (k₀ + 2 * t - 1) * U ^ t) ≤ 1 ∧
      ν (ch τ δ (k₀ - 1) - ch τ δ (k₀ + 2 * t - 1) * U ^ t) ≤ m := by
  obtain ⟨n, rfl⟩ : ∃ n, k₀ = n + 2 := ⟨k₀ - 2, by omega⟩
  have e0 : n + 2 - 1 = n + 1 := by omega
  have e1 : n + 2 + 2 * t - 1 = (n + 2 * t) + 1 := by omega
  rw [e0, e1]
  obtain ⟨A1, A2⟩ := hG ν τ δ hτ hδ1 n
  obtain ⟨B1, B2⟩ := hG ν τ δ hτ hδ1 (n + 2 * t)
  have hUt : ν (U ^ t) ≤ 1 := by rw [map_pow]; exact pow_le_one₀ (by positivity) hU1
  refine ⟨A1, ?_, ?_⟩
  · rw [map_mul]; exact mul_le_one' B1 hUt
  · have e : ch τ δ (n + 1) - ch τ δ (n + 2 * t + 1) * U ^ t =
        (ch τ δ (n + 1) - τ ^ n) + (τ ^ n * (1 - τ ^ (2 * t))) + (τ ^ (n + 2 * t) - ch τ δ (n + 2 * t + 1)) +
          ch τ δ (n + 2 * t + 1) * (1 - U ^ t) := by ring
    rw [e]
    have hτn : ν (τ ^ n) ≤ 1 := by rw [map_pow]; exact pow_le_one₀ (by positivity) hτ
    refine ν.map_add_le (ν.map_add_le (ν.map_add_le (A2.trans hδ) ?_) ?_) ?_
    · rw [map_mul, ν.map_sub_swap]
      exact (mul_le_of_le_one_left (by positivity) hτn).trans hτt
    · rw [ν.map_sub_swap]; exact B2.trans hδ
    · rw [map_mul, ν.map_sub_swap]
      exact (mul_le_of_le_one_left (by positivity) B1).trans hU

end UpperTheory.Esk.adelicTermLemmas
