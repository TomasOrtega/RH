import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal
open GlobalTheory

namespace GlobalTheory

open MvPolynomial

variable {R : Type} [CommRing R] {n : ℕ}

/- English proof (translation)
Rewrite using `[MvPolynomial.eval_eq]`. Use `Ideal.sum_mem _ fun β hβ => ?_` and prove the remaining obligations. Establish `h1` using `monoVal_mem_pow z (⟨β, rfl⟩ : MonoDeg (Fin n) β.degree)`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right (hP β (MvPolynomial.mem_support_iff.mp hβ)) h1)`.
-/
theorem eval_mem_span_pow_of_le_degree (z : Fin n → R) (m : ℕ) (P : MvPolynomial (Fin n) R)
    (hP : ∀ β, P.coeff β ≠ 0 → m ≤ β.degree) :
    MvPolynomial.eval z P ∈ Ideal.span (Set.range z) ^ m := by
  rw [MvPolynomial.eval_eq]
  refine Ideal.sum_mem _ fun β hβ => ?_
  have h1 := monoVal_mem_pow z (⟨β, rfl⟩ : MonoDeg (Fin n) β.degree)
  exact Ideal.mul_mem_left _ _
    (Ideal.pow_le_pow_right (hP β (MvPolynomial.mem_support_iff.mp hβ)) h1)

/- English proof (translation)
Use `choose g hg using fun β => (Ideal.mem_span_range_iff_exists_fun).mp (hP β)`. Use `⟨∑ β ∈ P.support, ∑ j, MvPolynomial.monomial (β + Finsupp.single j 1) (g β j), ?_, ?_⟩` and prove the remaining obligations. Establish `key : ∀ β j, MvPolynomial.eval z (MvPolynomial.monomial (β + Finsupp.single j 1) (g β j)) = g β j * z j * monoVal z β`. Introduce `β j`. Rewrite using `[MvPolynomial.eval_monomial]`.

Express the relevant statement in the definitionally equal form `_ * monoVal z _ = _`. Rewrite using `[monoVal_add, monoVal_single, pow_one]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [map_sum, key]`. Rewrite using `[MvPolynomial.eval_eq]`.

Use `Finset.sum_congr rfl fun β _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_mul, hg β]`. Both sides reduce to the same expression. Introduce `γ hγ`. Rewrite `hγ` using `[MvPolynomial.coeff_sum]`.

Take `⟨β, hβ, hβ'⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hγ`. Rewrite `hβ'` using `[MvPolynomial.coeff_sum]`. Take `⟨j, -, hj⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hβ'`. Rewrite `hj` using `[MvPolynomial.coeff_monomial]`. Use `split_ifs at hj with h`.

Conclude with `⟨β, j, MvPolynomial.mem_support_iff.mp hβ, h.symm⟩`. Conclude with `absurd rfl hj`.
-/
theorem exists_eval_eq_shift (z : Fin n → R) (P : MvPolynomial (Fin n) R)
    (hP : ∀ β, P.coeff β ∈ Ideal.span (Set.range z)) :
    ∃ G : MvPolynomial (Fin n) R, MvPolynomial.eval z G = MvPolynomial.eval z P ∧
      ∀ γ, G.coeff γ ≠ 0 → ∃ β j, P.coeff β ≠ 0 ∧ γ = β + Finsupp.single j 1 := by
  classical
  choose g hg using fun β => (Ideal.mem_span_range_iff_exists_fun).mp (hP β)
  refine ⟨∑ β ∈ P.support, ∑ j, MvPolynomial.monomial (β + Finsupp.single j 1) (g β j), ?_, ?_⟩
  · have key : ∀ β j, MvPolynomial.eval z (MvPolynomial.monomial (β + Finsupp.single j 1) (g β j))
        = g β j * z j * monoVal z β := by
      intro β j
      rw [MvPolynomial.eval_monomial]
      change _ * monoVal z _ = _
      rw [monoVal_add, monoVal_single, pow_one]
      ring
    simp only [map_sum, key]
    rw [MvPolynomial.eval_eq]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [← Finset.sum_mul, hg β]
    rfl
  · intro γ hγ
    rw [MvPolynomial.coeff_sum] at hγ
    obtain ⟨β, hβ, hβ'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hγ
    rw [MvPolynomial.coeff_sum] at hβ'
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hβ'
    rw [MvPolynomial.coeff_monomial] at hj
    split_ifs at hj with h
    · exact ⟨β, j, MvPolynomial.mem_support_iff.mp hβ, h.symm⟩
    · exact absurd rfl hj

/- English proof (translation)
Use `set Hk := MvPolynomial.homogeneousComponent k H with hHk`. Establish `hcoeffk : ∀ β, Hk.coeff β = if β.degree = k then H.coeff β else 0` using `fun β => MvPolynomial.coeff_homogeneousComponent _ _ _`. Establish `hrest : ∀ β, (H - Hk).coeff β = if β.degree = k then 0 else H.coeff β`. Introduce `β`. Rewrite using `[MvPolynomial.coeff_sub, hcoeffk]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `hrest' : ∀ β, (H - Hk).coeff β ≠ 0 → k + 1 ≤ β.degree ∧ D ≤ Finsupp.weight w β`. Introduce `β hβ`. Rewrite `hβ` using `[hrest]`. Use `split_ifs at hβ with h`.

Conclude with `absurd rfl hβ`. Use `hH β hβ` as an intermediate fact. Conclude with `⟨by omega, this.2⟩`. Establish `hmem : MvPolynomial.eval z Hk ∈ Ideal.span (Set.range z) ^ (k + 1)`. Establish `h1` using `eval_mem_span_pow_of_le_degree z (k + 1) (H - Hk) fun β hβ => (hrest' β hβ).1`.

Establish `h2 : MvPolynomial.eval z Hk = - MvPolynomial.eval z (H - Hk)`. Rewrite using `[map_sub, h0]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`. Conclude with `neg_mem h1`.

Establish `hI : ∀ β, Hk.coeff β ∈ Ideal.span (Set.range z)` using `(isQuasiRegularSeq_self_iff z).mp hz k Hk (MvPolynomial.homogeneousComponent_isHomogeneous k H) hmem`. Use `⟨fun β hβ => ?_, ?_⟩` and prove the remaining obligations. Use `hI β` as an intermediate fact. Rewrite `this` using `[hcoeffk, if_pos hβ]`. Then use the resulting hypothesis. Take `⟨G, hG, hGs⟩` from `exists_eval_eq_shift z Hk hI`.

Establish `hGw : ∀ γ, G.coeff γ ≠ 0 → k + 1 ≤ γ.degree ∧ D + 1 ≤ Finsupp.weight w γ`. Introduce `γ hγ`. Take `⟨β, j, hβ, rfl⟩` from `hGs γ hγ`. Rewrite `hβ` using `[hcoeffk]`. Use `split_ifs at hβ with hd`.

Use `hH β hβ` as an intermediate fact. Establish `hj` using `hw j`. Simplify using `only [map_add, Finsupp.degree_single, Finsupp.weight_single, one_smul, hd]`. Conclude with `⟨le_rfl, by omega⟩`. Conclude with `absurd rfl hβ`.

Use `⟨(H - Hk) + G, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `β hβ`. Rewrite `hβ` using `[MvPolynomial.coeff_add]`. Distinguish the cases in `h1 : (H - Hk).coeff β = 0`. Rewrite `hβ` using `[h1, zero_add]`.

Use `hGw β hβ` as an intermediate fact. Conclude with `⟨this.1, by omega⟩`. Conclude with `hrest' β h1`. Rewrite using `[map_add, hG, ← map_add, sub_add_cancel, h0]`. Introduce `β hβw hβd`.

Rewrite using `[MvPolynomial.coeff_add, hrest, if_neg (by omega)]`. Distinguish the cases in `h : G.coeff β = 0`. Rewrite using `[h, add_zero]`. Use `hGw β h` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem weightedRelation_step (z : Fin n → R) (w : Fin n → ℕ) (hw : ∀ i, 1 ≤ w i)
    (hz : IsQuasiRegularSeq R z) (D k : ℕ) (H : MvPolynomial (Fin n) R)
    (hH : ∀ β, H.coeff β ≠ 0 → k ≤ β.degree ∧ D ≤ Finsupp.weight w β)
    (h0 : MvPolynomial.eval z H = 0) :
    (∀ β : Fin n →₀ ℕ, β.degree = k → H.coeff β ∈ Ideal.span (Set.range z)) ∧
      ∃ H' : MvPolynomial (Fin n) R,
        (∀ β, H'.coeff β ≠ 0 → k + 1 ≤ β.degree ∧ D ≤ Finsupp.weight w β) ∧
        MvPolynomial.eval z H' = 0 ∧
        ∀ β : Fin n →₀ ℕ, Finsupp.weight w β = D → k + 1 ≤ β.degree → H'.coeff β = H.coeff β := by
  classical
  set Hk := MvPolynomial.homogeneousComponent k H with hHk
  have hcoeffk : ∀ β, Hk.coeff β = if β.degree = k then H.coeff β else 0 := fun β =>
    MvPolynomial.coeff_homogeneousComponent _ _ _
  have hrest : ∀ β, (H - Hk).coeff β = if β.degree = k then 0 else H.coeff β := by
    intro β
    rw [MvPolynomial.coeff_sub, hcoeffk]
    split_ifs <;> simp
  have hrest' : ∀ β, (H - Hk).coeff β ≠ 0 → k + 1 ≤ β.degree ∧ D ≤ Finsupp.weight w β := by
    intro β hβ
    rw [hrest] at hβ
    split_ifs at hβ with h
    · exact absurd rfl hβ
    · have := hH β hβ
      exact ⟨by omega, this.2⟩
  have hmem : MvPolynomial.eval z Hk ∈ Ideal.span (Set.range z) ^ (k + 1) := by
    have h1 := eval_mem_span_pow_of_le_degree z (k + 1) (H - Hk) fun β hβ => (hrest' β hβ).1
    have h2 : MvPolynomial.eval z Hk = - MvPolynomial.eval z (H - Hk) := by
      rw [map_sub, h0]
      ring
    rw [h2]
    exact neg_mem h1
  have hI : ∀ β, Hk.coeff β ∈ Ideal.span (Set.range z) :=
    (isQuasiRegularSeq_self_iff z).mp hz k Hk
      (MvPolynomial.homogeneousComponent_isHomogeneous k H) hmem
  refine ⟨fun β hβ => ?_, ?_⟩
  · have := hI β
    rwa [hcoeffk, if_pos hβ] at this
  obtain ⟨G, hG, hGs⟩ := exists_eval_eq_shift z Hk hI
  have hGw : ∀ γ, G.coeff γ ≠ 0 → k + 1 ≤ γ.degree ∧ D + 1 ≤ Finsupp.weight w γ := by
    intro γ hγ
    obtain ⟨β, j, hβ, rfl⟩ := hGs γ hγ
    rw [hcoeffk] at hβ
    split_ifs at hβ with hd
    · have := hH β hβ
      have hj := hw j
      simp only [map_add, Finsupp.degree_single, Finsupp.weight_single, one_smul, hd]
      exact ⟨le_rfl, by omega⟩
    · exact absurd rfl hβ
  refine ⟨(H - Hk) + G, ?_, ?_, ?_⟩
  · intro β hβ
    rw [MvPolynomial.coeff_add] at hβ
    by_cases h1 : (H - Hk).coeff β = 0
    · rw [h1, zero_add] at hβ
      have := hGw β hβ
      exact ⟨this.1, by omega⟩
    · exact hrest' β h1
  · rw [map_add, hG, ← map_add, sub_add_cancel, h0]
  · intro β hβw hβd
    rw [MvPolynomial.coeff_add, hrest, if_neg (by omega)]
    by_cases h : G.coeff β = 0
    · rw [h, add_zero]
    · have := hGw β h
      omega

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero`. Introduce `k H hH h0 α hα _`. Conclude with `(weightedRelation_step z w hw hz D k H hH h0).1 α hα`. Consider the case `succ j ih`.

Introduce `k H hH h0 α hα hαw`. Take `⟨-, H', h1, h2, h3⟩` from `weightedRelation_step z w hw hz D k H hH h0`. Rewrite using `[← h3 α hαw (by omega)]`. Conclude with `ih (k + 1) H' h1 h2 α (by omega) hαw`.
-/
theorem weightedRelation_coeff_mem (z : Fin n → R) (w : Fin n → ℕ) (hw : ∀ i, 1 ≤ w i)
    (hz : IsQuasiRegularSeq R z) (D : ℕ) (j : ℕ) : ∀ (k : ℕ) (H : MvPolynomial (Fin n) R),
    (∀ β, H.coeff β ≠ 0 → k ≤ β.degree ∧ D ≤ Finsupp.weight w β) →
    MvPolynomial.eval z H = 0 → ∀ α : Fin n →₀ ℕ, α.degree = k + j →
    Finsupp.weight w α = D → H.coeff α ∈ Ideal.span (Set.range z) := by
  induction j with
  | zero =>
    intro k H hH h0 α hα _
    exact (weightedRelation_step z w hw hz D k H hH h0).1 α hα
  | succ j ih =>
    intro k H hH h0 α hα hαw
    obtain ⟨-, H', h1, h2, h3⟩ := weightedRelation_step z w hw hz D k H hH h0
    rw [← h3 α hαw (by omega)]
    exact ih (k + 1) H' h1 h2 α (by omega) hαw

/- English proof (translation)
Distinguish the cases in `hα : F.coeff α = 0`. Rewrite using `[hα]`. Conclude with `zero_mem _`. Conclude with `weightedRelation_coeff_mem z w hw hz D α.degree 0 F (fun β hβ => ⟨Nat.zero_le _, (hF hβ).ge⟩) h0 α (zero_add _).symm (hF hα)`.
-/
theorem coeff_mem_span_of_isWeightedHomogeneous_of_eval_eq_zero {R : Type} [CommRing R] {n : ℕ}
    (z : Fin n → R) (w : Fin n → ℕ) (hw : ∀ i, 1 ≤ w i) (hz : IsQuasiRegularSeq R z) (D : ℕ)
    (F : MvPolynomial (Fin n) R) (hF : F.IsWeightedHomogeneous w D)
    (h0 : MvPolynomial.eval z F = 0) (α : Fin n →₀ ℕ) :
    F.coeff α ∈ Ideal.span (Set.range z) := by
  by_cases hα : F.coeff α = 0
  · rw [hα]
    exact zero_mem _
  exact weightedRelation_coeff_mem z w hw hz D α.degree 0 F
    (fun β hβ => ⟨Nat.zero_le _, (hF hβ).ge⟩) h0 α (zero_add _).symm (hF hα)

/- English proof (translation)
Introduce `z w hw hz D F hF h0 α` and use `coeff_mem_span_of_isWeightedHomogeneous_of_eval_eq_zero z w hw hz D F hF h0 α`.
-/
theorem weightedRelation_coeff_mem_span : ∀ {R : Type} [CommRing R] {n : ℕ} (z : Fin n → R)
    (w : Fin n → ℕ), (∀ i, 1 ≤ w i) →
    IsQuasiRegularSeq R z → ∀ (D : ℕ) (F : MvPolynomial (Fin n) R),
    F.IsWeightedHomogeneous w D → MvPolynomial.eval z F = 0 →
    ∀ α : Fin n →₀ ℕ, F.coeff α ∈ Ideal.span (Set.range z) :=
  fun z w hw hz D F hF h0 α =>
    coeff_mem_span_of_isWeightedHomogeneous_of_eval_eq_zero z w hw hz D F hF h0 α

end GlobalTheory
