import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineThetaEqZeroIffFontaineXiElementDvdStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

/- English proof (translation)
Use `set S : Set A := {y : A | ∃ n : ℕ, ((n.factorial : ℕ) : A) * y = algebraMap R A ξ ^ n} with hS`. Establish `hγ : ∀ n : ℕ, ∃ g : A, ((n.factorial : ℕ) : A) * g = algebraMap R A ξ ^ n` using `fun n => by`. Take `⟨u, hu'⟩` from `(hu n).exists_right_inv`. Conclude with `⟨u * algebraMap R A ξ ^ n, by rw [← mul_assoc, hu', one_mul]⟩`. Establish `hone : (1 : A) ∈ Submodule.span R S` using `Submodule.subset_span ⟨0, by simp⟩`.

Establish `hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ Submodule.span R S`. Introduce and unpack `x ⟨m, hm⟩ y ⟨n, hn⟩`. Take `⟨g, hg⟩` from `hγ (m + n)`. Establish `hf : (((m + n).factorial : ℕ) : A) = (((m + n).choose n : ℕ) : A) * (m.factorial : ℕ) * (n.factorial : ℕ)`. Rewrite using `[← Nat.add_choose_mul_factorial_mul_factorial m n]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `: x * y = ((m + n).choose n : R) • g`. Use `((hu m).mul (hu n)).mul_left_cancel ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_natCast]`.

Rewrite `hg` using `[hf, pow_add, ← hm, ← hn]`. Take the linear combination `-hg`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨m + n, hg⟩)`. Prove the components needed by the constructor for the conclusion.

Introduce `hs`. Proceed by induction on `hs using Algebra.adjoin_induction with`. Consider the case `mem y hy`. Take `⟨x, hx, n, hn⟩` from `hy`. Take `⟨a, rfl⟩` from `(hP x).1 hx`.

Take `⟨g, hg⟩` from `hγ n`. Establish `: y = (a ^ n) • g`. Use `(hu n).mul_left_cancel ?_` and prove the remaining obligations. Rewrite using `[hn, Algebra.smul_def, map_mul, mul_pow, ← hg, map_pow]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, hg⟩)`. Consider the case `algebraMap r`. Rewrite using `[Algebra.algebraMap_eq_smul_one]`. Conclude with `Submodule.smul_mem _ _ hone`.

Consider the case `add x y _ _ hx hy => exact Submodule.add_mem _ hx hy`. Consider the case `mul x y _ _ hx hy`. Use `Submodule.mul_mem_mul hx hy` as an intermediate fact. Rewrite `this` using `[Submodule.span_mul_span]`. Use `Submodule.span_le.2 ?_ this` and prove the remaining obligations.

Introduce and unpack `_ ⟨a, ha, b, hb, rfl⟩`. Conclude with `hmul a ha b hb`. Introduce `hs`. Use `(Submodule.span_le (p := Subalgebra.toSubmodule (Algebra.adjoin R _))).2 ?_ hs` and prove the remaining obligations. Introduce and unpack `y ⟨n, hn⟩`.

Conclude with `Algebra.subset_adjoin ⟨ξ, (hP ξ).2 dvd_rfl, n, hn⟩`.
-/
theorem adjoin_dividedPowers_iff_span {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (hu : ∀ n : ℕ, IsUnit ((n.factorial : ℕ) : A)) (ξ : R) (P : R → Prop) (hP : ∀ a, P a ↔ ξ ∣ a) (s : A) :
    s ∈ Algebra.adjoin R {y : A | ∃ x : R, P x ∧ ∃ n : ℕ, ((n.factorial : ℕ) : A) * y = algebraMap R A x ^ n} ↔
      s ∈ Submodule.span R {y : A | ∃ n : ℕ, ((n.factorial : ℕ) : A) * y = algebraMap R A ξ ^ n} := by
  set S : Set A := {y : A | ∃ n : ℕ, ((n.factorial : ℕ) : A) * y = algebraMap R A ξ ^ n} with hS
  have hγ : ∀ n : ℕ, ∃ g : A, ((n.factorial : ℕ) : A) * g = algebraMap R A ξ ^ n := fun n => by
    obtain ⟨u, hu'⟩ := (hu n).exists_right_inv
    exact ⟨u * algebraMap R A ξ ^ n, by rw [← mul_assoc, hu', one_mul]⟩
  have hone : (1 : A) ∈ Submodule.span R S := Submodule.subset_span ⟨0, by simp⟩
  have hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ Submodule.span R S := by
    rintro x ⟨m, hm⟩ y ⟨n, hn⟩
    obtain ⟨g, hg⟩ := hγ (m + n)
    have hf : (((m + n).factorial : ℕ) : A) =
        (((m + n).choose n : ℕ) : A) * (m.factorial : ℕ) * (n.factorial : ℕ) := by
      rw [← Nat.add_choose_mul_factorial_mul_factorial m n]; push_cast; ring
    have : x * y = ((m + n).choose n : R) • g := by
      refine ((hu m).mul (hu n)).mul_left_cancel ?_
      rw [Algebra.smul_def, map_natCast]
      rw [hf, pow_add, ← hm, ← hn] at hg
      linear_combination -hg
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m + n, hg⟩)
  constructor
  · intro hs
    induction hs using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨x, hx, n, hn⟩ := hy
      obtain ⟨a, rfl⟩ := (hP x).1 hx
      obtain ⟨g, hg⟩ := hγ n
      have : y = (a ^ n) • g := by
        refine (hu n).mul_left_cancel ?_
        rw [hn, Algebra.smul_def, map_mul, mul_pow, ← hg, map_pow]
        ring
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, hg⟩)
    | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ hone
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | mul x y _ _ hx hy =>
      have := Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at this
      refine Submodule.span_le.2 ?_ this
      rintro _ ⟨a, ha, b, hb, rfl⟩
      exact hmul a ha b hb
  · intro hs
    refine (Submodule.span_le (p := Subalgebra.toSubmodule (Algebra.adjoin R _))).2 ?_ hs
    rintro y ⟨n, hn⟩
    exact Algebra.subset_adjoin ⟨ξ, (hP ξ).2 dvd_rfl, n, hn⟩

/- English proof (translation)
Introduce `l _ e he s`. Use `Iff.trans ?_ (adjoin_dividedPowers_iff_span (fun n => GlobalTheory.RingBasics.isUnit_nat l _ n.factorial_ne_zero) (xi e) (fun a => Per.θ l a = 0) (GlobalTheory.T.fontaineTheta_eq_zero_iff_fontaineXiElement_dvd l e he) s)` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce `hs`. Use `(?_ : Per.Acris0 l ≤ _) hs` and prove the remaining obligations.

Use `GlobalTheory.RingIface.Acris0_le_of_dividedPowers l _ fun x n y hx hy => ?_` and prove the remaining obligations. Conclude with `Algebra.subset_adjoin ⟨x, hx, n, hy⟩`. Introduce `hs`. Use `Algebra.adjoin_le (S := Per.Acris0 l) ?_ hs` and prove the remaining obligations. Introduce and unpack `y ⟨x, hx, n, hy⟩`.

Conclude with `GlobalTheory.RingIface.dividedPower_mem_Acris0 l x n y hx hy`.
-/
theorem mem_Acris0_iff_span : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ s : Per.AinfP l,
    s ∈ Per.Acris0 l ↔ s ∈ Submodule.span (Per.Ainf l) {y : Per.AinfP l | ∃ n : ℕ,
      ((n.factorial : ℕ) : Per.AinfP l) * y = algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ^ n} := by
  intro l _ e he s
  refine Iff.trans ?_ (adjoin_dividedPowers_iff_span (fun n => GlobalTheory.RingBasics.isUnit_nat l _ n.factorial_ne_zero) (xi e)
    (fun a => Per.θ l a = 0) (GlobalTheory.T.fontaineTheta_eq_zero_iff_fontaineXiElement_dvd l e he) s)
  constructor
  · intro hs
    refine (?_ : Per.Acris0 l ≤ _) hs
    refine GlobalTheory.RingIface.Acris0_le_of_dividedPowers l _ fun x n y hx hy => ?_
    exact Algebra.subset_adjoin ⟨x, hx, n, hy⟩
  · intro hs
    refine Algebra.adjoin_le (S := Per.Acris0 l) ?_ hs
    rintro y ⟨x, hx, n, hy⟩
    exact GlobalTheory.RingIface.dividedPower_mem_Acris0 l x n y hx hy

end GlobalTheory.MemLoc
