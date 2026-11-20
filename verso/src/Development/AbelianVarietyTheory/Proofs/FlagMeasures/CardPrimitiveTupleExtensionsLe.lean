import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPrimitiveAddCharInvolutionInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardDependentVectorsAffineGramLeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrimitiveTupleOfLinearIndependentFiniteRingStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardHermitianQuadricAffineSubspaceResidueRingStatement

open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

/- English proof (translation)
Introduce `B _ _ c hc ω hω hf q hq hB k n hkn x hx g t ht`. Take `⟨χ, hχ, hχc⟩` from `GlobalTheory.T.exists_primitive_addChar_involution_invariant c hc ω hω hf`. Establish `hZ` using `GlobalTheory.T.card_hermitianQuadric_affineSubspace_residueRing c hc ω hω hf q hq hB χ hχ hχc k n (by omega) x hx g t ht`. Establish `hD` using `GlobalTheory.T.ncard_dependent_vectors_affine_gram_le c hc ω hω hf q hq hB k n (by omega) x hx g`. Use `set S := {y : Fin n → B | Prim c (Fin.cons y x : Fin (k + 1) → Fin n → B) ∧ (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} with hS`.

Use `set Z := {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} with hZd`. Use `set D := {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧ ∃ a : B, a ≠ 0 ∧ ∃ s : Fin k → B, a • y = ∑ i, s i • x i} with hDd`. Establish `h1 : S ⊆ Z` using `fun y hy => hy.2`. Establish `h2 : Z ⊆ S ∪ D`. Introduce `y hy`.

Distinguish the cases in `hp : Prim c (Fin.cons y x : Fin (k + 1) → Fin n → B)`. Conclude with `Or.inl ⟨hp, hy⟩`. Use `right`. Establish `hne : ¬ ∀ s : Fin (k + 1) → B, ∑ a, s a • (Fin.cons y x : Fin (k + 1) → Fin n → B) a = 0 → s = 0` using `fun h => hp (GlobalTheory.T.isPrimitiveTuple_of_linearIndependent_finite_ring c hc χ hχ (k + 1) n _ h)`. Use `push Not at hne`.

Take `⟨s, hs, hs0⟩` from `hne`. Rewrite `hs` using `[Fin.sum_univ_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ] at hs`. Use `⟨hy.1, s 0, ?_, fun i => -s i.succ, ?_⟩` and prove the remaining obligations. Introduce `h0`.

Apply `hs0` to reduce the goal to its premises. Rewrite `hs` using `[h0, zero_smul, zero_add]`. Establish `h3` using `hx.eq_zero c (fun i => s i.succ) hs`. Use function extensionality and compare the values at `i`. Use `Fin.cases h0 (fun j => ?_) i` and prove the remaining obligations.

Conclude with `congrFun h3 j`. Simplify using `only [neg_smul, Finset.sum_neg_distrib]`. Conclude with `eq_neg_of_add_eq_zero_left hs`. Establish `h3 : S.ncard ≤ Z.ncard` using `Set.ncard_le_ncard h1 (Set.toFinite _)`. Establish `h4 : Z.ncard ≤ S.ncard + 2 * q ^ n` using `(Set.ncard_le_ncard h2 (Set.toFinite _)).trans ((Set.ncard_union_le _ _).trans (Nat.add_le_add_left hD _))`.

Establish `h3' : (S.ncard : ℝ) ≤ Z.ncard` using `by exact_mod_cast h3`. Establish `h4' : (Z.ncard : ℝ) ≤ S.ncard + 2 * (q : ℝ) ^ n` using `by exact_mod_cast h4`. Establish `h5 : (0 : ℝ) ≤ (q : ℝ) ^ n` using `by positivity`. Rewrite `hZ`, the goal using `[abs_le]`. Apply the tactic sequence `constructor <;> linarith [hZ.1, hZ.2]`.
-/
theorem ncard_extend_prim_one : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (k n : ℕ), 2 * k + 1 ≤ n → ∀ (x : Fin k → Fin n → B), Prim c x → ∀ (g : Fin k → B) (t : B), c t = t → |(Set.ncard {y : Fin n → B | Prim c (Fin.cons y x : Fin (k + 1) → Fin n → B) ∧ (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} : ℝ) - (q : ℝ) ^ (2 * n - (2 * k + 1))| ≤ 3 * (q : ℝ) ^ n := by
  intro B _ _ c hc ω hω hf q hq hB k n hkn x hx g t ht
  obtain ⟨χ, hχ, hχc⟩ := GlobalTheory.T.exists_primitive_addChar_involution_invariant c hc ω hω hf
  have hZ := GlobalTheory.T.card_hermitianQuadric_affineSubspace_residueRing c hc ω hω hf q hq hB χ hχ hχc k n (by omega) x hx g t ht
  have hD := GlobalTheory.T.ncard_dependent_vectors_affine_gram_le c hc ω hω hf q hq hB k n (by omega) x hx g
  set S := {y : Fin n → B | Prim c (Fin.cons y x : Fin (k + 1) → Fin n → B) ∧ (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} with hS
  set Z := {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} with hZd
  set D := {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧ ∃ a : B, a ≠ 0 ∧ ∃ s : Fin k → B, a • y = ∑ i, s i • x i} with hDd
  have h1 : S ⊆ Z := fun y hy => hy.2
  have h2 : Z ⊆ S ∪ D := by
    intro y hy
    by_cases hp : Prim c (Fin.cons y x : Fin (k + 1) → Fin n → B)
    · exact Or.inl ⟨hp, hy⟩
    · right
      have hne : ¬ ∀ s : Fin (k + 1) → B,
          ∑ a, s a • (Fin.cons y x : Fin (k + 1) → Fin n → B) a = 0 → s = 0 :=
        fun h => hp (GlobalTheory.T.isPrimitiveTuple_of_linearIndependent_finite_ring c hc χ hχ (k + 1) n _ h)
      push Not at hne
      obtain ⟨s, hs, hs0⟩ := hne
      rw [Fin.sum_univ_succ] at hs
      simp only [Fin.cons_zero, Fin.cons_succ] at hs
      refine ⟨hy.1, s 0, ?_, fun i => -s i.succ, ?_⟩
      · intro h0
        apply hs0
        rw [h0, zero_smul, zero_add] at hs
        have h3 := hx.eq_zero c (fun i => s i.succ) hs
        funext i
        refine Fin.cases h0 (fun j => ?_) i
        exact congrFun h3 j
      · simp only [neg_smul, Finset.sum_neg_distrib]
        exact eq_neg_of_add_eq_zero_left hs
  have h3 : S.ncard ≤ Z.ncard := Set.ncard_le_ncard h1 (Set.toFinite _)
  have h4 : Z.ncard ≤ S.ncard + 2 * q ^ n :=
    (Set.ncard_le_ncard h2 (Set.toFinite _)).trans
      ((Set.ncard_union_le _ _).trans (Nat.add_le_add_left hD _))
  have h3' : (S.ncard : ℝ) ≤ Z.ncard := by exact_mod_cast h3
  have h4' : (Z.ncard : ℝ) ≤ S.ncard + 2 * (q : ℝ) ^ n := by exact_mod_cast h4
  have h5 : (0 : ℝ) ≤ (q : ℝ) ^ n := by positivity
  rw [abs_le] at hZ ⊢
  constructor <;> linarith [hZ.1, hZ.2]

end GlobalTheory.GramCount
