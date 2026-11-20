import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.DivChain

section
variable {X : Type} [AddCommGroup X]

def DivAll (l : ℕ) (y : X) : Prop := ∀ m : ℕ, ∃ w : X, l ^ m • w = y

/- English proof (translation)
Take `⟨w, rfl⟩` from `hz`. Use `⟨l ^ (M - m) • w, ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_smul, ← pow_add, Nat.add_sub_cancel' h]`.
-/
lemma divBy_mono {l M m : ℕ} {z : X} (h : m ≤ M) (hz : ∃ w : X, l ^ M • w = z) :
    ∃ w : X, l ^ m • w = z := by
  obtain ⟨w, rfl⟩ := hz
  refine ⟨l ^ (M - m) • w, ?_⟩
  rw [← mul_smul, ← pow_add, Nat.add_sub_cancel' h]

/- English proof (translation)
Use `Finite.of_injective (fun z : {z : X // l • z = y} => (⟨z.1 - z0, by rw [smul_sub, z.2, hz0, sub_self]⟩ : {x : X // l • x = 0})) ?_` and prove the remaining obligations. Introduce `a b hab`. Apply `Subtype.ext` to reduce the goal to its premises. Use `congrArg Subtype.val hab` as an intermediate fact. Simplify using `using this`.
-/
lemma finite_fiber {l : ℕ} (hfin : Finite {x : X // l • x = 0}) (y z0 : X) (hz0 : l • z0 = y) :
    Finite {z : X // l • z = y} := by
  refine Finite.of_injective (fun z : {z : X // l • z = y} =>
    (⟨z.1 - z0, by rw [smul_sub, z.2, hz0, sub_self]⟩ : {x : X // l • x = 0})) ?_
  intro a b hab
  apply Subtype.ext
  have := congrArg Subtype.val hab
  simpa using this

/- English proof (translation)
Take `⟨z0, hz0⟩` from `hy 1`. Rewrite `hz0` using `[pow_one]`. Use `haveI := finite_fiber hfin y z0 hz0`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Establish `hm : ∀ z : {z : X // l • z = y}, ∃ m : ℕ, ∀ w : X, l ^ m • w ≠ z.1`. Introduce `z`. Use `hcon z.1 z.2` as an intermediate fact. Simplify using `only [DivAll, not_forall, not_exists] at this`. Conclude with `this`.

Use `choose f hf using hm`. Take `⟨M, hM⟩` from `(Set.finite_range f).bddAbove`. Take `⟨w, hw⟩` from `hy (M + 1)`. Establish `hz : l • (l ^ M • w) = y` using `by rw [← mul_smul, ← pow_succ']; exact hw`. Establish `hle : f ⟨l ^ M • w, hz⟩ ≤ M` using `hM ⟨⟨l ^ M • w, hz⟩, rfl⟩`.

Take `⟨w', hw'⟩` from `divBy_mono (z := l ^ M • w) hle ⟨w, rfl⟩`. Conclude with `hf ⟨l ^ M • w, hz⟩ w' hw'`.
-/
lemma exists_preimage {l : ℕ} (hfin : Finite {x : X // l • x = 0}) {y : X} (hy : DivAll l y) :
    ∃ z : X, l • z = y ∧ DivAll l z := by
  obtain ⟨z0, hz0⟩ := hy 1
  rw [pow_one] at hz0
  haveI := finite_fiber hfin y z0 hz0
  by_contra hcon
  push_neg at hcon
  have hm : ∀ z : {z : X // l • z = y}, ∃ m : ℕ, ∀ w : X, l ^ m • w ≠ z.1 := by
    intro z
    have := hcon z.1 z.2
    simp only [DivAll, not_forall, not_exists] at this
    exact this
  choose f hf using hm
  obtain ⟨M, hM⟩ := (Set.finite_range f).bddAbove
  obtain ⟨w, hw⟩ := hy (M + 1)
  have hz : l • (l ^ M • w) = y := by rw [← mul_smul, ← pow_succ']; exact hw
  have hle : f ⟨l ^ M • w, hz⟩ ≤ M := hM ⟨⟨l ^ M • w, hz⟩, rfl⟩
  obtain ⟨w', hw'⟩ := divBy_mono (z := l ^ M • w) hle ⟨w, rfl⟩
  exact hf ⟨l ^ M • w, hz⟩ w' hw'

/- English proof (translation)
The claim follows from `| 0, h => by simp at h; exact absurd h hz | n + 1, h => by by_cases hk : l ^ n • z = 0 · exact exists_last hz n hk · exact ⟨n, hk, h⟩`.
-/
lemma exists_last {l : ℕ} {z : X} (hz : z ≠ 0) :
    ∀ n : ℕ, l ^ n • z = 0 → ∃ k, l ^ k • z ≠ 0 ∧ l ^ (k + 1) • z = 0
  | 0, h => by simp at h; exact absurd h hz
  | n + 1, h => by
    by_cases hk : l ^ n • z = 0
    · exact exists_last hz n hk
    · exact ⟨n, hk, h⟩

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hm : ∀ y : {x : X // l • x = 0}, ∃ m : ℕ, y.1 ≠ 0 → ∀ w : X, l ^ m • w ≠ y.1`. Introduce `y`. Distinguish the cases in `hy0 : y.1 = 0`.

Conclude with `⟨0, fun h => absurd hy0 h⟩`. Use `hcon y.1 hy0 y.2` as an intermediate fact. Simplify using `only [DivAll, not_forall, not_exists] at this`. Take `⟨m, hm⟩` from `this`. Conclude with `⟨m, fun _ => hm⟩`.

Use `choose f hf using hm`. Take `⟨M, hM⟩` from `(Set.finite_range f).bddAbove`. Take `⟨x, hx⟩` from `hunb M`. Take `⟨n, hn⟩` from `htors (l ^ M • x)`. Take `⟨k, hk1, hk2⟩` from `exists_last hx n hn`.

Establish `hy : l • (l ^ k • (l ^ M • x)) = 0` using `by rw [← mul_smul, ← pow_succ']; exact hk2`. Establish `hle : f ⟨_, hy⟩ ≤ M` using `hM ⟨⟨_, hy⟩, rfl⟩`. Apply `hf ⟨_, hy⟩ hk1 (l ^ (M - f ⟨_, hy⟩) • (l ^ k • x))` to reduce the goal to its premises. Use `show l ^ f ⟨_, hy⟩ • l ^ (M - f ⟨_, hy⟩) • l ^ k • x = l ^ k • l ^ M • x`. Rewrite using `[← mul_smul, ← pow_add, Nat.add_sub_cancel' hle, ← mul_smul, ← mul_smul, mul_comm]`.
-/
lemma exists_start {l : ℕ} (htors : ∀ x : X, ∃ n : ℕ, l ^ n • x = 0)
    (hfin : Finite {x : X // l • x = 0}) (hunb : ∀ m : ℕ, ∃ x : X, l ^ m • x ≠ 0) :
    ∃ y : X, y ≠ 0 ∧ l • y = 0 ∧ DivAll l y := by
  by_contra hcon
  push_neg at hcon
  have hm : ∀ y : {x : X // l • x = 0}, ∃ m : ℕ, y.1 ≠ 0 → ∀ w : X, l ^ m • w ≠ y.1 := by
    intro y
    by_cases hy0 : y.1 = 0
    · exact ⟨0, fun h => absurd hy0 h⟩
    · have := hcon y.1 hy0 y.2
      simp only [DivAll, not_forall, not_exists] at this
      obtain ⟨m, hm⟩ := this
      exact ⟨m, fun _ => hm⟩
  choose f hf using hm
  obtain ⟨M, hM⟩ := (Set.finite_range f).bddAbove
  obtain ⟨x, hx⟩ := hunb M
  obtain ⟨n, hn⟩ := htors (l ^ M • x)
  obtain ⟨k, hk1, hk2⟩ := exists_last hx n hn
  have hy : l • (l ^ k • (l ^ M • x)) = 0 := by rw [← mul_smul, ← pow_succ']; exact hk2
  have hle : f ⟨_, hy⟩ ≤ M := hM ⟨⟨_, hy⟩, rfl⟩
  apply hf ⟨_, hy⟩ hk1 (l ^ (M - f ⟨_, hy⟩) • (l ^ k • x))
  show l ^ f ⟨_, hy⟩ • l ^ (M - f ⟨_, hy⟩) • l ^ k • x = l ^ k • l ^ M • x
  rw [← mul_smul, ← pow_add, Nat.add_sub_cancel' hle, ← mul_smul, ← mul_smul, mul_comm]

end

/- English proof (translation)
Introduce `l _ X _ htors hfin hunb`. Take `⟨y0, hy0, -, hdiv⟩` from `exists_start htors hfin hunb`. Establish `H : ∀ y : {y : X // DivAll l y}, ∃ z : X, l • z = y.1 ∧ DivAll l z` using `fun y => exists_preimage hfin y.2`. Use `choose g hg hgd using H`. Set `s : ℕ → {y : X // DivAll l y}` to `fun n => Nat.rec ⟨y0, hdiv⟩ (fun _ y => ⟨g y, hgd y⟩) n`.

Conclude with `⟨fun n => (s n).1, hy0, fun n => hg (s n)⟩`.
-/
theorem exists_divisible_chain : ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X],
    (∀ x : X, ∃ n : ℕ, l ^ n • x = 0) → Finite {x : X // l • x = 0} →
    (∀ m : ℕ, ∃ x : X, l ^ m • x ≠ 0) → ∃ x : ℕ → X, x 0 ≠ 0 ∧ ∀ n, l • x (n + 1) = x n := by
  intro l _ X _ htors hfin hunb
  obtain ⟨y0, hy0, -, hdiv⟩ := exists_start htors hfin hunb
  have H : ∀ y : {y : X // DivAll l y}, ∃ z : X, l • z = y.1 ∧ DivAll l z :=
    fun y => exists_preimage hfin y.2
  choose g hg hgd using H
  let s : ℕ → {y : X // DivAll l y} := fun n => Nat.rec ⟨y0, hdiv⟩ (fun _ y => ⟨g y, hgd y⟩) n
  exact ⟨fun n => (s n).1, hy0, fun n => hg (s n)⟩

end GlobalTheory.Ord2.DivChain
