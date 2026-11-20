import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero

open MvPolynomial Filter

namespace GlobalTheory

namespace SatHilb

attribute [local instance] MvPolynomial.gradedAlgebra

variable {ι K : Type*} [Field K]

end SatHilb

open MvPolynomial Filter in
attribute [local instance] MvPolynomial.gradedAlgebra in
/- English proof (translation)
Use `conv_lhs => rw [← sum_homogeneousComponent g, Finset.mul_sum, map_sum]`. Establish `hterm : ∀ i, homogeneousComponent (n + m) (X j ^ m * homogeneousComponent i g) = if n + m = m + i then X j ^ m * homogeneousComponent i g else 0` using `fun i => homogeneousComponent_of_mem (((isHomogeneous_X_pow j m).mul (homogeneousComponent_isHomogeneous i g)))`. Repeatedly rewrite using `[hterm]`. Rewrite using `[Finset.sum_eq_single n]`. Simplify using `[add_comm]`.

Introduce `i _ hi`. Rewrite using `[if_neg (by omega)]`. Introduce `hn`. Rewrite `hn` using `[Finset.mem_range, not_lt]`. Rewrite using `[homogeneousComponent_eq_zero n g (by omega), mul_zero, ite_self]`.
-/
private lemma homogeneousComponent_add_X_pow_mul {K : Type} [Field K] {N : ℕ} (j : Fin N) (m n : ℕ)
    (g : MvPolynomial (Fin N) K) :
    homogeneousComponent (n + m) (X j ^ m * g) = X j ^ m * homogeneousComponent n g := by
  conv_lhs => rw [← sum_homogeneousComponent g, Finset.mul_sum, map_sum]
  have hterm : ∀ i, homogeneousComponent (n + m) (X j ^ m * homogeneousComponent i g) =
      if n + m = m + i then X j ^ m * homogeneousComponent i g else 0 := fun i =>
    homogeneousComponent_of_mem
      (((isHomogeneous_X_pow j m).mul (homogeneousComponent_isHomogeneous i g)))
  simp_rw [hterm]
  rw [Finset.sum_eq_single n]
  · simp [add_comm]
  · intro i _ hi
    rw [if_neg (by omega)]
  · intro hn
    rw [Finset.mem_range, not_lt] at hn
    rw [homogeneousComponent_eq_zero n g (by omega), mul_zero, ite_self]

open MvPolynomial Filter in
attribute [local instance] MvPolynomial.gradedAlgebra in
/- English proof (translation)
Distinguish the cases in `hX : ∀ j, X j ∈ Q`. Establish `hspan : Ideal.span (X '' Set.univ) ≤ Q`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨j, -, rfl⟩`. Conclude with `hX j`.

Introduce `g hg n`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Establish `hsub : g - C (coeff 0 g) ∈ Q`. Apply `hspan` to reduce the goal to its premises. Rewrite using `[mem_ideal_span_X_image]`.

Introduce `e he`. Establish `he0 : e ≠ 0`. Introduce and unpack `rfl`. Simplify using `at he`. Take `⟨i, hi⟩` from `Finsupp.ne_iff.mp he0`.

Conclude with `⟨i, Set.mem_univ _, hi⟩`. Rewrite using `[homogeneousComponent_zero]`. Use `Q.sub_mem hg hsub` as an intermediate fact. Simplify using `using this`. Apply `hspan` to reduce the goal to its premises.

Rewrite using `[mem_ideal_span_X_image]`. Introduce `e he`. Rewrite `he` using `[mem_support_iff, coeff_homogeneousComponent]`. Establish `hdeg : e.degree = n`. Assume the negation of the conclusion as `hne`.

Conclude with `he (if_neg hne)`. Establish `he0 : e ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hdeg`. Use linear arithmetic over natural numbers and integers.

Take `⟨i, hi⟩` from `Finsupp.ne_iff.mp he0`. Conclude with `⟨i, Set.mem_univ _, hi⟩`. Use `push_neg at hX`. Take `⟨j, hj⟩` from `hX`. Introduce `g hg n`.

Take `⟨m, hm⟩` from `hs g hg j`. Establish `hmem` using `hIQ (hI _ hm (n + m))`. Rewrite `hmem` using `[homogeneousComponent_add_X_pow_mul]`. Break down `hQ.mem_or_mem hmem with h | h` into its components or cases. Conclude with `absurd (hQ.mem_of_pow_mem m h) hj`.

Conclude with `h`.
-/
private lemma homogeneousComponent_mem_of_isPrime_of_X_pow_saturation {K : Type} [Field K] {N : ℕ}
    {I Q : Ideal (MvPolynomial (Fin N) K)}
    (hI : ∀ g ∈ I, ∀ n : ℕ, homogeneousComponent n g ∈ I) (hQ : Q.IsPrime) (hIQ : I ≤ Q)
    (hs : ∀ g ∈ Q, ∀ j, ∃ m : ℕ, X j ^ m * g ∈ I) :
    ∀ g ∈ Q, ∀ n : ℕ, homogeneousComponent n g ∈ Q := by
  by_cases hX : ∀ j, X j ∈ Q
  · have hspan : Ideal.span (X '' Set.univ) ≤ Q := by
      rw [Ideal.span_le]
      rintro _ ⟨j, -, rfl⟩
      exact hX j
    intro g hg n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hsub : g - C (coeff 0 g) ∈ Q := by
        apply hspan
        rw [mem_ideal_span_X_image]
        intro e he
        have he0 : e ≠ 0 := by
          rintro rfl
          simp at he
        obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp he0
        exact ⟨i, Set.mem_univ _, hi⟩
      rw [homogeneousComponent_zero]
      have := Q.sub_mem hg hsub
      simpa using this
    · apply hspan
      rw [mem_ideal_span_X_image]
      intro e he
      rw [mem_support_iff, coeff_homogeneousComponent] at he
      have hdeg : e.degree = n := by
        by_contra hne
        exact he (if_neg hne)
      have he0 : e ≠ 0 := by
        rintro rfl
        simp at hdeg
        omega
      obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp he0
      exact ⟨i, Set.mem_univ _, hi⟩
  · push_neg at hX
    obtain ⟨j, hj⟩ := hX
    intro g hg n
    obtain ⟨m, hm⟩ := hs g hg j
    have hmem := hIQ (hI _ hm (n + m))
    rw [homogeneousComponent_add_X_pow_mul] at hmem
    rcases hQ.mem_or_mem hmem with h | h
    · exact absurd (hQ.mem_of_pow_mem m h) hj
    · exact h

open MvPolynomial Filter in
attribute [local instance] MvPolynomial.gradedAlgebra in
/- English proof (translation)
Take `⟨G, hG⟩` from `(IsNoetherian.noetherian Q : Q.FG)`. Use `choose! mexp hmexp using hs`. Use `set M := G.sup fun g => Finset.univ.sup (mexp g)`. Use `set D := G.sup totalDegree`. Use `set B := N * M + 1`.

Establish `hkey : ∀ g ∈ G, ∀ e : Fin N →₀ ℕ, B ≤ (e.sum fun _ k => k) → ∀ a : K, monomial e a * g ∈ I`. Introduce `g hgG e he a`. Establish `hgQ : g ∈ Q` using `hG ▸ Submodule.subset_span hgG`. Establish `hj : ∃ j, M ≤ e j`. Assume the negation of the conclusion as `hne`.

Use `push_neg at hne`. Establish `hsum : (e.sum fun _ k => k) ≤ N * M`. Rewrite using `[Finsupp.sum_fintype _ _ (fun _ => rfl)]`. Combine the equalities or inequalities in the displayed calculation. Use linear arithmetic over natural numbers and integers.

Take `⟨j, hjM⟩` from `hj`. Establish `hle : mexp g j ≤ e j` using `le_trans (le_trans (Finset.le_sup (f := mexp g) (Finset.mem_univ j)) (Finset.le_sup (f := fun g => Finset.univ.sup (mexp g)) hgG)) hjM`. Establish `hsingle : Finsupp.single j (mexp g j) ≤ e`. Rewrite using `[Finsupp.single_le_iff]`. Conclude with `hle`.

Establish `hsplit : monomial e a = monomial (e - Finsupp.single j (mexp g j)) a * X j ^ mexp g j`. Rewrite using `[X_pow_eq_monomial, monomial_mul, mul_one, tsub_add_cancel_of_le hsingle]`. Rewrite using `[hsplit, mul_assoc]`. Conclude with `I.mul_mem_left _ (hmexp g hgQ j)`. Use `⟨B + D, fun n hn h hQ hh => ?_⟩` and prove the remaining obligations.

Establish `hhn : h = homogeneousComponent n h`. Rewrite using `[homogeneousComponent_of_mem hh, if_pos rfl]`. Rewrite `hQ` using `[← hG]`. Take `⟨f, -, hf⟩` from `Submodule.mem_span_finset.mp hQ`. Rewrite using `[hhn, ← hf, map_sum]`.

Use `I.sum_mem fun g hgG => ?_` and prove the remaining obligations. Rewrite using `[smul_eq_mul, as_sum (f g), Finset.sum_mul, map_sum]`. Use `I.sum_mem fun e _ => ?_` and prove the remaining obligations. Distinguish the cases in `hdeg : B ≤ (e.sum fun _ k => k)`. Conclude with `hI _ (hkey g hgG e hdeg _) n`.

Rewrite using `[homogeneousComponent_eq_zero]`. Conclude with `I.zero_mem`. Establish `h1` using `totalDegree_mul (monomial e (coeff e (f g))) g`. Establish `h2` using `totalDegree_monomial_le e (coeff e (f g))`. Establish `h3 : g.totalDegree ≤ D` using `Finset.le_sup (f := totalDegree) hgG`.

Establish `h4 : (e.sum fun _ => id) = (e.sum fun _ k => k)` using `rfl`. Use linear arithmetic over natural numbers and integers.
-/
private lemma exists_homogeneous_mem_of_X_pow_mul_mem_of_homogeneous {K : Type} [Field K] {N : ℕ}
    {I Q : Ideal (MvPolynomial (Fin N) K)}
    (hI : ∀ g ∈ I, ∀ n : ℕ, homogeneousComponent n g ∈ I)
    (hs : ∀ g ∈ Q, ∀ j, ∃ m : ℕ, X j ^ m * g ∈ I) :
    ∃ L : ℕ, ∀ n ≥ L, ∀ h ∈ Q, h ∈ homogeneousSubmodule (Fin N) K n → h ∈ I := by
  classical
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian Q : Q.FG)
  choose! mexp hmexp using hs
  set M := G.sup fun g => Finset.univ.sup (mexp g)
  set D := G.sup totalDegree
  set B := N * M + 1
  have hkey : ∀ g ∈ G, ∀ e : Fin N →₀ ℕ, B ≤ (e.sum fun _ k => k) → ∀ a : K,
      monomial e a * g ∈ I := by
    intro g hgG e he a
    have hgQ : g ∈ Q := hG ▸ Submodule.subset_span hgG
    have hj : ∃ j, M ≤ e j := by
      by_contra hne
      push_neg at hne
      have hsum : (e.sum fun _ k => k) ≤ N * M := by
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
        calc ∑ j, e j ≤ ∑ _j : Fin N, M := Finset.sum_le_sum fun j _ => (hne j).le
          _ = N * M := by simp
      omega
    obtain ⟨j, hjM⟩ := hj
    have hle : mexp g j ≤ e j :=
      le_trans (le_trans (Finset.le_sup (f := mexp g) (Finset.mem_univ j))
        (Finset.le_sup (f := fun g => Finset.univ.sup (mexp g)) hgG)) hjM
    have hsingle : Finsupp.single j (mexp g j) ≤ e := by
      rw [Finsupp.single_le_iff]
      exact hle
    have hsplit : monomial e a =
        monomial (e - Finsupp.single j (mexp g j)) a * X j ^ mexp g j := by
      rw [X_pow_eq_monomial, monomial_mul, mul_one, tsub_add_cancel_of_le hsingle]
    rw [hsplit, mul_assoc]
    exact I.mul_mem_left _ (hmexp g hgQ j)
  refine ⟨B + D, fun n hn h hQ hh => ?_⟩
  have hhn : h = homogeneousComponent n h := by
    rw [homogeneousComponent_of_mem hh, if_pos rfl]
  rw [← hG] at hQ
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp hQ
  rw [hhn, ← hf, map_sum]
  refine I.sum_mem fun g hgG => ?_
  rw [smul_eq_mul, as_sum (f g), Finset.sum_mul, map_sum]
  refine I.sum_mem fun e _ => ?_
  by_cases hdeg : B ≤ (e.sum fun _ k => k)
  · exact hI _ (hkey g hgG e hdeg _) n
  · rw [homogeneousComponent_eq_zero]
    · exact I.zero_mem
    · have h1 := totalDegree_mul (monomial e (coeff e (f g))) g
      have h2 := totalDegree_monomial_le e (coeff e (f g))
      have h3 : g.totalDegree ≤ D := Finset.le_sup (f := totalDegree) hgG
      have h4 : (e.sum fun _ => id) = (e.sum fun _ k => k) := rfl
      omega

open MvPolynomial Filter in
attribute [local instance] MvPolynomial.gradedAlgebra in
/- English proof (translation)
Use `conv_lhs => rw [← sum_homogeneousComponent g]`. Rewrite using `[DirectSum.decompose_sum, DFinsupp.finset_sum_apply, AddSubmonoidClass.coe_finset_sum, Finset.sum_eq_single n]`. Conclude with `DirectSum.decompose_of_mem_same _ (homogeneousComponent_mem n g)`. Introduce `i _ hi`. Conclude with `DirectSum.decompose_of_mem_ne _ (homogeneousComponent_mem i g) hi`.

Introduce `hn`. Rewrite `hn` using `[Finset.mem_range, not_lt]`. Rewrite using `[DirectSum.decompose_of_mem_same _ (homogeneousComponent_mem n g), homogeneousComponent_eq_zero n g (by omega)]`.
-/
private lemma coe_decompose_homogeneousSubmodule_eq_homogeneousComponent {K : Type} [Field K] {N : ℕ}
    (g : MvPolynomial (Fin N) K) (n : ℕ) :
    ((DirectSum.decompose (homogeneousSubmodule (Fin N) K) g n : MvPolynomial (Fin N) K)) =
      homogeneousComponent n g := by
  conv_lhs => rw [← sum_homogeneousComponent g]
  rw [DirectSum.decompose_sum, DFinsupp.finset_sum_apply, AddSubmonoidClass.coe_finset_sum,
    Finset.sum_eq_single n]
  · exact DirectSum.decompose_of_mem_same _ (homogeneousComponent_mem n g)
  · intro i _ hi
    exact DirectSum.decompose_of_mem_ne _ (homogeneousComponent_mem i g) hi
  · intro hn
    rw [Finset.mem_range, not_lt] at hn
    rw [DirectSum.decompose_of_mem_same _ (homogeneousComponent_mem n g),
      homogeneousComponent_eq_zero n g (by omega)]

open MvPolynomial Filter in
attribute [local instance] MvPolynomial.gradedAlgebra in
/- English proof (translation)
Introduce `n g hg`. Rewrite using `[coe_decompose_homogeneousSubmodule_eq_homogeneousComponent]`. Conclude with `hI g hg n`.
-/
private lemma isHomogeneous_of_forall_homogeneousComponent_mem {K : Type} [Field K] {N : ℕ}
    {I : Ideal (MvPolynomial (Fin N) K)} (hI : ∀ g ∈ I, ∀ n : ℕ, homogeneousComponent n g ∈ I) :
    Ideal.IsHomogeneous (homogeneousSubmodule (Fin N) K) I := by
  intro n g hg
  rw [coe_decompose_homogeneousSubmodule_eq_homogeneousComponent]
  exact hI g hg n

open MvPolynomial Filter in
attribute [local instance] MvPolynomial.gradedAlgebra in

/- English proof (translation)
Establish `hQh` using `homogeneousComponent_mem_of_isPrime_of_X_pow_saturation hI hQ hIQ hs`. Use `⟨hQh, ?_⟩` and prove the remaining obligations. Take `⟨L, hL⟩` from `exists_homogeneous_mem_of_X_pow_mul_mem_of_homogeneous hI hs`. Establish `hIh` using `isHomogeneous_of_forall_homogeneousComponent_mem hI`. Establish `hQh'` using `isHomogeneous_of_forall_homogeneousComponent_mem hQh`.

Take `⟨n0, hn0⟩` from `eventually_atTop.mp (((_root_.GlobalTheory.eventually_finrank_quotPiece hQh').and (_root_.GlobalTheory.eventually_finrank_quotPiece hIh)).and (eventually_ge_atTop L))`. Apply `Polynomial.eq_of_infinite_eval_eq` to reduce the goal to its premises. Use `Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n0 + n : ℕ) : ℚ)) (fun a b hab => by simpa using hab) fun n => ?_` and prove the remaining obligations. Take `⟨⟨hq, hi⟩, hLn⟩` from `hn0 (n0 + n) (by omega)`. Use `show Polynomial.eval _ _ = Polynomial.eval _ _`.

Rewrite using `[← hq, ← hi]`. Establish `hint : Submodule.restrictScalars K Q ⊓ homogeneousSubmodule (Fin N) K (n0 + n) = Submodule.restrictScalars K I ⊓ homogeneousSubmodule (Fin N) K (n0 + n)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `h hh`. Rewrite `hh`, the goal using `[Submodule.mem_inf]`.

Conclude with `⟨hL (n0 + n) hLn h hh.1 hh.2, hh.2⟩`. Introduce `h hh`. Rewrite `hh`, the goal using `[Submodule.mem_inf]`. Conclude with `⟨hIQ hh.1, hh.2⟩`. Establish `e1` using `_root_.GlobalTheory.finrank_quotPiece_add Q (n0 + n)`.

Establish `e2` using `_root_.GlobalTheory.finrank_quotPiece_add I (n0 + n)`. Rewrite `e1` using `[hint]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.
-/
theorem _root_.GlobalTheory.prime_saturation_homogeneous_and_hilbertPoly_eq (K : Type) [Field K] (N : ℕ)
    (I Q : Ideal (MvPolynomial (Fin N) K))
    (hI : ∀ g ∈ I, ∀ n : ℕ, homogeneousComponent n g ∈ I) (hQ : Q.IsPrime) (hIQ : I ≤ Q)
    (hs : ∀ g ∈ Q, ∀ j, ∃ m : ℕ, X j ^ m * g ∈ I) :
    (∀ g ∈ Q, ∀ n : ℕ, homogeneousComponent n g ∈ Q) ∧
      _root_.GlobalTheory.idealHilbertPoly Q = _root_.GlobalTheory.idealHilbertPoly I := by
  have hQh := homogeneousComponent_mem_of_isPrime_of_X_pow_saturation hI hQ hIQ hs
  refine ⟨hQh, ?_⟩
  obtain ⟨L, hL⟩ := exists_homogeneous_mem_of_X_pow_mul_mem_of_homogeneous hI hs
  have hIh := isHomogeneous_of_forall_homogeneousComponent_mem hI
  have hQh' := isHomogeneous_of_forall_homogeneousComponent_mem hQh
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp
    (((_root_.GlobalTheory.eventually_finrank_quotPiece hQh').and
      (_root_.GlobalTheory.eventually_finrank_quotPiece hIh)).and (eventually_ge_atTop L))
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n0 + n : ℕ) : ℚ))
    (fun a b hab => by simpa using hab) fun n => ?_
  obtain ⟨⟨hq, hi⟩, hLn⟩ := hn0 (n0 + n) (by omega)
  show Polynomial.eval _ _ = Polynomial.eval _ _
  rw [← hq, ← hi]
  have hint : Submodule.restrictScalars K Q ⊓ homogeneousSubmodule (Fin N) K (n0 + n) =
      Submodule.restrictScalars K I ⊓ homogeneousSubmodule (Fin N) K (n0 + n) := by
    apply le_antisymm
    · intro h hh
      rw [Submodule.mem_inf] at hh ⊢
      exact ⟨hL (n0 + n) hLn h hh.1 hh.2, hh.2⟩
    · intro h hh
      rw [Submodule.mem_inf] at hh ⊢
      exact ⟨hIQ hh.1, hh.2⟩
  have e1 := _root_.GlobalTheory.finrank_quotPiece_add Q (n0 + n)
  have e2 := _root_.GlobalTheory.finrank_quotPiece_add I (n0 + n)
  rw [hint] at e1
  congr 1
  omega

end GlobalTheory
