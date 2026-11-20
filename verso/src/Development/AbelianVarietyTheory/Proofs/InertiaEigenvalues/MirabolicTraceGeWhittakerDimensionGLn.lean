import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraTracePatternIdempotentExchangeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceUnitriangularColumnVanishingIdempotentEqSumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerJacquetIdempotentsPropertiesPrimeFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraInductionCharacterRestrictionDecompStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraTraceIdempotentAndIrreducibleDegreeStatement
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.MirabolicComparison

/- English proof (translation)
Simplify using `[tr, mul_add, Finset.sum_add_distrib]`.
-/
theorem tr_add {G : Type} [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (f h : G → ℂ) :
    tr a (fun x => f x + h x) = tr a f + tr a h := by
  simp [tr, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [tr, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun x _ => by ring`.
-/
theorem tr_mul_const {G : Type} [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (f : G → ℂ) (c : ℂ) :
    tr a (fun x => f x * c) = tr a f * c := by
  simp only [tr, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => by ring

/- English proof (translation)
Introduce `L`. Proceed by induction on `L with`. Consider the case `nil`. Introduce `_`. Conclude with `⟨0, by simp [tr]⟩`.

Consider the case `cons p L ih`. Introduce `hL`. Take `⟨m, hm⟩` from `ih (fun q hq => hL q (List.mem_cons_of_mem _ hq))`. Take `⟨n₁, hn₁⟩` from `(GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree G a p.1).1 ha (hL p (List.mem_cons_self ..)).1`. Take `⟨n₂, hn₂⟩` from `(GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree H b p.2).1 hb (hL p (List.mem_cons_self ..)).2`.

Use `⟨n₁ * n₂ + m, ?_⟩` and prove the remaining obligations. Simplify using `only [List.map_cons, List.sum_cons]`. Rewrite using `[show (fun x => tr b (fun y => p.1 x * p.2 y + (L.map fun p => p.1 x * p.2 y).sum)) = (fun x => p.1 x * tr b p.2 + tr b (fun y => (L.map fun p => p.1 x * p.2 y).sum)) from by`. Use function extensionality and compare the values at `x`. Rewrite using `[tr_add]`.

Use `congr 1`. Simplify using `only [tr, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun y _ => by ring]`. Rewrite using `[tr_add, tr_mul_const, hm, hn₁, hn₂]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem tr_tr_list_nat {G H : Type} [Group G] [Fintype G] [Group H] [Fintype H]
    (a : MonoidAlgebra ℂ G) (b : MonoidAlgebra ℂ H) (ha : a * a = a) (hb : b * b = b) :
    ∀ L : List ((G → ℂ) × (H → ℂ)), (∀ p ∈ L, IsChar p.1 ∧ IsChar p.2) →
      ∃ n : ℕ, tr a (fun x => tr b (fun y => (L.map fun p => p.1 x * p.2 y).sum)) = n := by
  intro L
  induction L with
  | nil =>
    intro _
    exact ⟨0, by simp [tr]⟩
  | cons p L ih =>
    intro hL
    obtain ⟨m, hm⟩ := ih (fun q hq => hL q (List.mem_cons_of_mem _ hq))
    obtain ⟨n₁, hn₁⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree G a p.1).1 ha (hL p (List.mem_cons_self ..)).1
    obtain ⟨n₂, hn₂⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree H b p.2).1 hb (hL p (List.mem_cons_self ..)).2
    refine ⟨n₁ * n₂ + m, ?_⟩
    simp only [List.map_cons, List.sum_cons]
    rw [show (fun x => tr b (fun y => p.1 x * p.2 y + (L.map fun p => p.1 x * p.2 y).sum)) =
        (fun x => p.1 x * tr b p.2 + tr b (fun y => (L.map fun p => p.1 x * p.2 y).sum)) from by
      funext x
      rw [tr_add]
      congr 1
      simp only [tr, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring]
    rw [tr_add, tr_mul_const, hm, hn₁, hn₂]
    push_cast
    ring

end GlobalTheory.GLq.MirabolicComparison

namespace GlobalTheory.GLq.MirabolicComparison

/- English proof (translation)
Take `⟨V, hV⟩` from `h`. Introduce `x y`. Rewrite using `[← hV, ← hV]`. Conclude with `FDRep.char_conj V x y`.
-/
theorem isClass_of_isChar {G : Type} [Group G] {χ : G → ℂ} (h : IsChar χ) : IsClass χ := by
  obtain ⟨V, hV⟩ := h
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

/- English proof (translation)
Take `⟨V, _, hV⟩` from `h`. Conclude with `⟨V, hV⟩`.
-/
theorem isChar_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsChar χ := by
  obtain ⟨V, _, hV⟩ := h
  exact ⟨V, hV⟩

/- English proof (translation)
Take `⟨L, hL, hLeq⟩` from `(GlobalTheory.T.harishChandra_induction_character_restriction_decomp g i (N - i) N (by omega)).2 χ hχ`. Establish `hres : (fun h : Gn g i => wh ψ (res i (N - i) χ h)) = fun h => tr (eU g (N - i) ψ) (fun y => (L.map fun p => p.1 h * p.2 y).sum)`. Use function extensionality and compare the values at `h`. Simplify using `only [wh]`. Use `congr 1`.

Use function extensionality and compare the values at `y`. Conclude with `hLeq h y`. Use `show ∃ n : ℕ, tr (eU g i ψ) (fun h => wh ψ (res i (N - i) χ h)) = n`. Rewrite using `[hres]`. Conclude with `tr_tr_list_nat _ _ (GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g i 0 0 ψ).1 (GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g (N - i) 0 0 ψ).1 L (fun p hp => ⟨isChar_of_isIrr (hL p hp).1, isChar_of_isIrr (hL p hp).2⟩)`.
-/
theorem wh_der_nat (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (N i : ℕ) (hi : i ≤ N)
    (χ : Gn g N → ℂ) (hχ : IsChar χ) : ∃ n : ℕ, wh ψ (der ψ i χ) = n := by
  obtain ⟨L, hL, hLeq⟩ := (GlobalTheory.T.harishChandra_induction_character_restriction_decomp g i (N - i) N (by omega)).2 χ hχ
  have hres : (fun h : Gn g i => wh ψ (res i (N - i) χ h)) =
      fun h => tr (eU g (N - i) ψ) (fun y => (L.map fun p => p.1 h * p.2 y).sum) := by
    funext h
    simp only [wh]
    congr 1
    funext y
    exact hLeq h y
  show ∃ n : ℕ, tr (eU g i ψ) (fun h => wh ψ (res i (N - i) χ h)) = n
  rw [hres]
  exact tr_tr_list_nat _ _ (GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g i 0 0 ψ).1 (GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g (N - i) 0 0 ψ).1 L
    (fun p hp => ⟨isChar_of_isIrr (hL p hp).1, isChar_of_isIrr (hL p hp).2⟩)

/- English proof (translation)
Use `haveI : Subsingleton (Gn g 0) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩`. Establish `h1 : (eU g 0 ψ).coeff 1 = 1`. Rewrite using `[(GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g 0 0 0 ψ).2.1]`. Simplify using the standard rewrite rules. Establish `hres : res 0 (N - 0) χ 1 = χ`.

Use function extensionality and compare the values at `y`. Express the relevant statement in the definitionally equal form `Gn g N at y`. Simplify using `only [res, Nat.zero_mul, pow_zero, inv_one, one_mul]`. Rewrite using `[Finset.sum_eq_single y]`. Establish `: InPar 0 ((y : Gn g N) : Mt g N) ∧ tl 0 ((y : Gn g N) : Mt g N) = ((1 : Gn g 0) : Mt g 0) ∧ br 0 (N - 0) ((y : Gn g N) : Mt g N) = ((y : Gn g (N - 0)) : Mt g (N - 0))`.

Use `⟨fun i j hj _ => absurd hj (Nat.not_lt_zero _), Subsingleton.elim _ _, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i j`. Simplify using `[br, entN]`. Rewrite using `[if_pos this]`. Introduce `x _ hx`.

Rewrite using `[if_neg]`. Introduce and unpack `⟨_, _, hb⟩`. Apply `hx` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[← hb]`.

Use function extensionality and compare the values at `i j`. Simplify using `[br, entN]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Use `show tr (eU g 0 ψ) (fun h => wh ψ (res 0 (N - 0) χ h)) = wh ψ χ`.

Simplify using `only [tr]`. Rewrite using `[Fintype.sum_subsingleton _ 1, h1, one_mul, hres]`.
-/
theorem wh_der_zero (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (N : ℕ) (χ : Gn g N → ℂ) :
    wh ψ (der ψ 0 χ) = wh ψ χ := by
  haveI : Subsingleton (Gn g 0) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
  have h1 : (eU g 0 ψ).coeff 1 = 1 := by
    rw [(GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g 0 0 0 ψ).2.1]; simp
  have hres : res 0 (N - 0) χ 1 = χ := by
    funext y
    change Gn g N at y
    simp only [res, Nat.zero_mul, pow_zero, inv_one, one_mul]
    rw [Finset.sum_eq_single y]
    · have : InPar 0 ((y : Gn g N) : Mt g N) ∧ tl 0 ((y : Gn g N) : Mt g N) = ((1 : Gn g 0) : Mt g 0) ∧
          br 0 (N - 0) ((y : Gn g N) : Mt g N) = ((y : Gn g (N - 0)) : Mt g (N - 0)) := by
        refine ⟨fun i j hj _ => absurd hj (Nat.not_lt_zero _), Subsingleton.elim _ _, ?_⟩
        funext i j
        simp [br, entN]
      rw [if_pos this]
    · intro x _ hx
      rw [if_neg]
      rintro ⟨_, _, hb⟩
      apply hx
      apply Units.ext
      rw [← hb]
      funext i j
      simp [br, entN]
    · intro h; exact absurd (Finset.mem_univ _) h
  show tr (eU g 0 ψ) (fun h => wh ψ (res 0 (N - 0) χ h)) = wh ψ χ
  simp only [tr]
  rw [Fintype.sum_subsingleton _ 1, h1, one_mul, hres]

end GlobalTheory.GLq.MirabolicComparison

namespace GlobalTheory.GLq.MirabolicComparison

/- English proof (translation)
Introduce `g _ ψ hψ N k s hN hk χ hχ`. Establish `hcl` using `isClass_of_isChar hχ`. Rewrite using `[GlobalTheory.T.groupAlgebraTrace_patternIdempotent_exchange g ψ hψ N k s hN χ hcl, GlobalTheory.T.trace_unitriangularColumnVanishingIdempotent_eq_sum_derivatives g ψ hψ N k hk (by omega) χ hcl]`. Establish `hg1 : (1 : ℝ) ≤ g` using `by exact_mod_cast (Fact.out : g.Prime).one_lt.le`. Establish `hterm : ∀ i a b, (wh ψ (der ψ i χ) * ((g : ℂ) ^ a - (g : ℂ) ^ b)).re = (wh ψ (der ψ i χ)).re * ((g : ℝ) ^ a - (g : ℝ) ^ b)`.

Introduce `i a b`. Rewrite using `[show ((g : ℂ) ^ a - (g : ℂ) ^ b) = (((g : ℝ) ^ a - (g : ℝ) ^ b : ℝ) : ℂ) by push_cast; ring]`. Conclude with `Complex.re_mul_ofReal _ _`. Establish `hnn : ∀ i, i ≤ N → 0 ≤ (wh ψ (der ψ i χ)).re`. Introduce `i hi`.

Take `⟨n, hn⟩` from `wh_der_nat g ψ N i hi χ hχ`. Rewrite using `[hn]`. Simplify using the standard rewrite rules. Take `⟨k', rfl⟩ : ∃ k', k = k' + 1` from `⟨k - 1, by omega⟩`. Rewrite using `[Finset.sum_range_succ', Complex.add_re, Complex.add_re, Complex.re_sum, hterm 0, wh_der_zero]`.

Establish `hrest : 0 ≤ ∑ i ∈ Finset.range k', (wh ψ (der ψ (i + 1) χ) * ((g : ℂ) ^ (k' + 1 - (i + 1)) - (g : ℂ) ^ (k' + 1 - (i + 1) - 1))).re`. Apply `Finset.sum_nonneg` to reduce the goal to its premises. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_range]`. Rewrite using `[hterm]`.

Apply `mul_nonneg (hnn _ (by omega))` to reduce the goal to its premises. Rewrite using `[sub_nonneg]`. Conclude with `pow_le_pow_right₀ hg1 (by omega)`. Establish `hlast` using `hnn (k' + 1) (by omega)`. Establish `h0 : (wh ψ χ).re * ((g : ℝ) ^ (k' + 1 - 0) - (g : ℝ) ^ (k' + 1 - 0 - 1)) = ((g : ℝ) ^ (k' + 1) - (g : ℝ) ^ (k' + 1 - 1)) * (wh ψ χ).re`.

Simplify using `only [Nat.sub_zero]`. Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem mirabolic_comparison : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (N k s : ℕ),
    N = k + 2 * s + 1 → 1 ≤ k → ∀ χ : Gn g N → ℂ, IsChar χ →
      ((g : ℝ) ^ k - (g : ℝ) ^ (k - 1)) * (wh ψ χ).re ≤ (tr (eJ g N k s ψ) χ).re := by
  intro g _ ψ hψ N k s hN hk χ hχ
  have hcl := isClass_of_isChar hχ
  rw [GlobalTheory.T.groupAlgebraTrace_patternIdempotent_exchange g ψ hψ N k s hN χ hcl, GlobalTheory.T.trace_unitriangularColumnVanishingIdempotent_eq_sum_derivatives g ψ hψ N k hk (by omega) χ hcl]
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast (Fact.out : g.Prime).one_lt.le
  have hterm : ∀ i a b, (wh ψ (der ψ i χ) * ((g : ℂ) ^ a - (g : ℂ) ^ b)).re =
      (wh ψ (der ψ i χ)).re * ((g : ℝ) ^ a - (g : ℝ) ^ b) := by
    intro i a b
    rw [show ((g : ℂ) ^ a - (g : ℂ) ^ b) = (((g : ℝ) ^ a - (g : ℝ) ^ b : ℝ) : ℂ) by push_cast; ring]
    exact Complex.re_mul_ofReal _ _
  have hnn : ∀ i, i ≤ N → 0 ≤ (wh ψ (der ψ i χ)).re := by
    intro i hi
    obtain ⟨n, hn⟩ := wh_der_nat g ψ N i hi χ hχ
    rw [hn]
    simp
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Finset.sum_range_succ', Complex.add_re, Complex.add_re, Complex.re_sum, hterm 0, wh_der_zero]
  have hrest : 0 ≤ ∑ i ∈ Finset.range k', (wh ψ (der ψ (i + 1) χ) *
      ((g : ℂ) ^ (k' + 1 - (i + 1)) - (g : ℂ) ^ (k' + 1 - (i + 1) - 1))).re := by
    apply Finset.sum_nonneg
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hterm]
    apply mul_nonneg (hnn _ (by omega))
    rw [sub_nonneg]
    exact pow_le_pow_right₀ hg1 (by omega)
  have hlast := hnn (k' + 1) (by omega)
  have h0 : (wh ψ χ).re * ((g : ℝ) ^ (k' + 1 - 0) - (g : ℝ) ^ (k' + 1 - 0 - 1)) =
      ((g : ℝ) ^ (k' + 1) - (g : ℝ) ^ (k' + 1 - 1)) * (wh ψ χ).re := by
    simp only [Nat.sub_zero]
    ring
  linarith

end GlobalTheory.GLq.MirabolicComparison
