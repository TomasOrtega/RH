import Development.EtaleCohomology.EtaleTrace.LCoverCut

noncomputable section
open MvPolynomial

namespace LateralTheory.EtaleTrace.Cov

variable {k K : Type} [Field k] [Field K] [Algebra k K]

/- English proof (translation)
Proceed by induction on `F using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add f g hf hg => simp [hf, hg, add_smul, Finset.sum_add_distrib]`. Consider the case `mul_X f i hf`. Simplify using `only [map_mul, aeval_X, Derivation.leibniz, hf, pderiv_X, Finset.sum_add_distrib, mul_smul, Finset.smul_sum, Derivation.leibniz]`.

Simplify using `[Pi.single_apply]`. Simplify using `only [apply_ite (aeval w), map_zero, add_smul, ite_smul, zero_smul, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_smul]`.
-/
theorem jetIndep_chain {n : ℕ} (w : Fin n → K) (F : MvPolynomial (Fin n) k) :
    KaehlerDifferential.D k K (aeval w F) =
      ∑ j, aeval w (pderiv j F) • KaehlerDifferential.D k K (w j) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf, hg, add_smul, Finset.sum_add_distrib]
  | mul_X f i hf =>
    simp only [map_mul, aeval_X, Derivation.leibniz, hf, pderiv_X, Finset.sum_add_distrib, mul_smul, Finset.smul_sum, Derivation.leibniz]
    simp [Pi.single_apply]
    simp only [apply_ite (aeval w), map_zero, add_smul, ite_smul, zero_smul, Finset.sum_add_distrib,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_smul]

/- English proof (translation)
Establish `e1` using `congrArg (aeval w) hF.sum_X_mul_pderiv`. Simplify using `only [map_sum, map_mul, aeval_X, map_nsmul, h0, smul_zero] at e1`. Establish `e2` using `jetIndep_chain w F`. Rewrite `e2` using `[h0, Derivation.map_zero]`. Use `Fintype.linearIndependent_iff.1 hw (fun j => aeval w (pderiv j F)) ?_ j` and prove the remaining obligations.

Use `ext`. Simplify using `only [jet, Prod.fst_sum, Prod.smul_fst, smul_eq_mul, Prod.fst_zero]`. Rewrite using `[← e1]`. Conclude with `Finset.sum_congr rfl fun _ _ => mul_comm _ _`. Simplify using `only [jet, Prod.snd_sum, Prod.smul_snd, Prod.snd_zero]`.

Conclude with `e2.symm`.
-/
theorem jetIndep_pderiv {n : ℕ} (w : Fin n → K) (hw : LinearIndependent K (jet k w)) {m : ℕ}
    (F : MvPolynomial (Fin n) k) (hF : F.IsHomogeneous m) (h0 : aeval w F = 0) (j : Fin n) :
    aeval w (pderiv j F) = 0 := by
  have e1 := congrArg (aeval w) hF.sum_X_mul_pderiv
  simp only [map_sum, map_mul, aeval_X, map_nsmul, h0, smul_zero] at e1
  have e2 := jetIndep_chain w F
  rw [h0, Derivation.map_zero] at e2
  refine Fintype.linearIndependent_iff.1 hw (fun j => aeval w (pderiv j F)) ?_ j
  ext
  · simp only [jet, Prod.fst_sum, Prod.smul_fst, smul_eq_mul, Prod.fst_zero]
    rw [← e1]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  · simp only [jet, Prod.snd_sum, Prod.smul_snd, Prod.snd_zero]
    exact e2.symm

/- English proof (translation)
Break down `Nat.eq_zero_or_pos (α i) with h0 | hpos` into its components or cases. Simplify using `[h0]`. Establish `hc` using `congrArg (coeff (α - Finsupp.single i 1)) (h i)`. Rewrite `hc` using `[coeff_pderiv, coeff_zero]`. Establish `hα' : α - Finsupp.single i 1 + Finsupp.single i 1 = α`.

Use extensionality with `l`. Distinguish the cases in `hl : i = l`. Substitute `hl` using the available equality. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Simplify using `[hl]`. Rewrite `hc` using `[hα']`. Establish `hne : coeff α F ≠ 0` using `mem_support_iff.1 hα`. Establish `h1 : (((α - Finsupp.single i 1 : Fin n →₀ ℕ) i : ℕ) : k) + 1 = 0` using `(mul_eq_zero.1 hc).resolve_left hne`. Establish `e : (α - Finsupp.single i 1 : Fin n →₀ ℕ) i + 1 = α i` using `by simp; omega`.

Rewrite using `[← CharP.cast_eq_zero_iff k p, ← e]`. Conclude with `h1` after adjusting the coercions.
-/
theorem jetIndep_dvd {n p : ℕ} [CharP k p] (F : MvPolynomial (Fin n) k) (h : ∀ j, pderiv j F = 0)
    (α : Fin n →₀ ℕ) (hα : α ∈ F.support) (i : Fin n) : p ∣ α i := by
  rcases Nat.eq_zero_or_pos (α i) with h0 | hpos
  · simp [h0]
  have hc := congrArg (coeff (α - Finsupp.single i 1)) (h i)
  rw [coeff_pderiv, coeff_zero] at hc
  have hα' : α - Finsupp.single i 1 + Finsupp.single i 1 = α := by
    ext l
    by_cases hl : i = l
    · subst hl; simp; omega
    · simp [hl]
  rw [hα'] at hc
  have hne : coeff α F ≠ 0 := mem_support_iff.1 hα
  have h1 : (((α - Finsupp.single i 1 : Fin n →₀ ℕ) i : ℕ) : k) + 1 = 0 := (mul_eq_zero.1 hc).resolve_left hne
  have e : (α - Finsupp.single i 1 : Fin n →₀ ℕ) i + 1 = α i := by simp; omega
  rw [← CharP.cast_eq_zero_iff k p, ← e]
  exact_mod_cast h1

/- English proof (translation)
Establish `hp : 0 < p` using `(Fact.out : p.Prime).pos`. Set `q : (Fin n →₀ ℕ) → (Fin n →₀ ℕ)` to `fun α => Finsupp.mapRange (· / p) (Nat.zero_div p) α`. Establish `hq : ∀ α ∈ F.support, p • q α = α`. Introduce `α hα`. Use extensionality with `i`.

Simplify using `[q, Nat.mul_div_cancel' (hd α hα i)]`. Use `⟨∑ α ∈ F.support, monomial (q α) ((frobeniusEquiv k p).symm (coeff α F)), ?_, ?_⟩` and prove the remaining obligations. Apply `IsHomogeneous.sum` to reduce the goal to its premises. Introduce `α hα`. Apply `isHomogeneous_monomial` to reduce the goal to its premises.

Establish `hm : α.degree = m`. Use `hF (mem_support_iff.1 hα)` as an intermediate fact. Rewrite using `[Finsupp.degree_eq_weight_one]`. Conclude with `this`. Establish `: p * (q α).degree = m`.

Establish `h2` using `congrArg Finsupp.degree (hq α hα)`. Rewrite `h2` using `[map_nsmul, smul_eq_mul]`. Rewrite using `[h2, hm]`. Rewrite using `[← this, Nat.mul_div_cancel_left _ hp]`. Rewrite using `[sum_pow_char] conv_lhs => rw [F.as_sum]`.

Use `Finset.sum_congr rfl fun α hα => ?_` and prove the remaining obligations. Rewrite using `[monomial_pow, frobeniusEquiv_symm_pow_p, hq α hα]`.
-/
theorem jetIndep_root {n p : ℕ} [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (F : MvPolynomial (Fin n) k) {m : ℕ} (hF : F.IsHomogeneous m) (hd : ∀ α ∈ F.support, ∀ i, p ∣ α i) :
    ∃ G : MvPolynomial (Fin n) k, G.IsHomogeneous (m / p) ∧ F = G ^ p := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  let q : (Fin n →₀ ℕ) → (Fin n →₀ ℕ) := fun α => Finsupp.mapRange (· / p) (Nat.zero_div p) α
  have hq : ∀ α ∈ F.support, p • q α = α := by
    intro α hα; ext i; simp [q, Nat.mul_div_cancel' (hd α hα i)]
  refine ⟨∑ α ∈ F.support, monomial (q α) ((frobeniusEquiv k p).symm (coeff α F)), ?_, ?_⟩
  · apply IsHomogeneous.sum
    intro α hα
    apply isHomogeneous_monomial
    have hm : α.degree = m := by
      have := hF (mem_support_iff.1 hα)
      rw [Finsupp.degree_eq_weight_one]; exact this
    have : p * (q α).degree = m := by
      have h2 := congrArg Finsupp.degree (hq α hα)
      rw [map_nsmul, smul_eq_mul] at h2
      rw [h2, hm]
    rw [← this, Nat.mul_div_cancel_left _ hp]
  · rw [sum_pow_char]
    conv_lhs => rw [F.as_sum]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [monomial_pow, frobeniusEquiv_symm_pow_p, hq α hα]

/- English proof (translation)
Introduce `k K _ _ _ _ n w hw m`. Proceed by induction on `m using Nat.strong_induction_on with`. Consider the case `_ m ih`. Introduce `F hF h0`. Break down `Nat.eq_zero_or_pos m with rfl | hm` into its components or cases.

Assume the negation of the conclusion as `hne`. Establish `ht` using `hF.totalDegree hne`. Rewrite `ht` using `[totalDegree_eq_zero_iff_eq_C]`. Rewrite `h0` using `[ht, aeval_C, map_eq_zero_iff _ (algebraMap k K).injective]`. Conclude with `hne (by rw [ht, h0, C_0])`.

Establish `hpd : ∀ j, pderiv j F = 0` using `fun j => ih (m - 1) (by omega) _ hF.pderiv (jetIndep_pderiv w hw F hF h0 j)`. Take `⟨p, hcp⟩` from `CharP.exists k`. Break down `CharP.char_is_prime_or_zero k p with hpp | rfl` into its components or cases. Use `Fact.mk hpp` as an intermediate fact. Establish `: ExpChar k p` using `ExpChar.prime hpp`.

Establish `: PerfectRing k p` using `PerfectField.toPerfectRing p`. Take `⟨G, hG, rfl⟩` from `jetIndep_root F hF (fun α hα i => jetIndep_dvd F hpd α hα i)`. Rewrite `h0` using `[map_pow]`. Establish `hG0` using `ih (m / p) (Nat.div_lt_self hm hpp.one_lt) G hG (pow_eq_zero_iff hpp.ne_zero |>.1 h0)`. Rewrite using `[hG0, zero_pow hpp.ne_zero]`.

Use extensionality with `α`. Rewrite using `[coeff_zero]`. Assume the negation of the conclusion as `hc`. Establish `hα0 : α = 0`. Use extensionality with `i`.

Simplify using `using jetIndep_dvd (p := 0) F hpd α (mem_support_iff.2 hc) i`. Use `hF hc` as an intermediate fact. Substitute `hα0` using the available equality. Simplify using `at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem JetIndep_of : JetIndep := by
  intro k K _ _ _ _ n w hw m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro F hF h0
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · by_contra hne
    have ht := hF.totalDegree hne
    rw [totalDegree_eq_zero_iff_eq_C] at ht
    rw [ht, aeval_C, map_eq_zero_iff _ (algebraMap k K).injective] at h0
    exact hne (by rw [ht, h0, C_0])
  have hpd : ∀ j, pderiv j F = 0 := fun j =>
    ih (m - 1) (by omega) _ hF.pderiv (jetIndep_pderiv w hw F hF h0 j)
  obtain ⟨p, hcp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with hpp | rfl
  · have := Fact.mk hpp
    have : ExpChar k p := ExpChar.prime hpp
    have : PerfectRing k p := PerfectField.toPerfectRing p
    obtain ⟨G, hG, rfl⟩ := jetIndep_root F hF (fun α hα i => jetIndep_dvd F hpd α hα i)
    rw [map_pow] at h0
    have hG0 := ih (m / p) (Nat.div_lt_self hm hpp.one_lt) G hG (pow_eq_zero_iff hpp.ne_zero |>.1 h0)
    rw [hG0, zero_pow hpp.ne_zero]
  · ext α
    rw [coeff_zero]
    by_contra hc
    have hα0 : α = 0 := by
      ext i; simpa using jetIndep_dvd (p := 0) F hpd α (mem_support_iff.2 hc) i
    have := hF hc
    subst hα0
    simp at this
    omega

end LateralTheory.EtaleTrace.Cov
