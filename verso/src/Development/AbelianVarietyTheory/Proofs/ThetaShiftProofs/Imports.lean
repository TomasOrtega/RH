import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexConjugate

namespace GlobalTheory.ComplementTypes

open NumberField in
open scoped ComplexConjugate in

/- English proof (translation)
Set `c : E →+* E` to `(IsCMField.complexConj E).toAlgHom.toRingHom`. Establish `hcc : ∀ x, c (c x) = x` using `fun x => by simp [c]`. Set `t : (Fin r × (E →+* ℂ)) ⊕ Fin g' → (E →+* ℂ)` to `Sum.elim (fun k => k.2.comp c) ty'`. Establish `hsum : ∀ a : 𝓞 E, ∑ i, ty i (a : E) = ∑ k, t k (a : E)`. Introduce `a`.

Rewrite using `[h a, Fintype.sum_sum_type, Fintype.sum_prod_type]`. Simplify using `[t, c, H.bar_eq]`. Take `⟨e, he⟩` from `_root_.GlobalTheory.PeriodNonempty.exists_equiv_of_sum_eq ty t hsum`. Establish `key : ∀ τ : E →+* ℂ, Nat.card {i // ty i = τ} = r + Nat.card {j // ty' j = τ}`. Introduce `τ`.

Establish `hc1 : ∀ σ : E →+* ℂ, σ.comp c = τ ↔ σ = τ.comp c` using `fun σ => ⟨fun hσ => by ext x; rw [← hσ]; simp [hcc], fun hσ => by ext x; rw [hσ]; simp [hcc]⟩`. Rewrite using `[Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_congr (e.subtypeEquiv (p := fun i => ty i = τ) (q := fun k => t k = τ) fun i => by`. Simplify using `only [he]), Fintype.card_subtype,`. Use the proof step `Fintype.card_subtype, Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type,`. Use the proof step `Fintype.sum_prod_type]`.

Simplify using `only [t, Sum.elim_inl, Sum.elim_inr, hc1, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]`. Use `congr 1`. Establish `hd : (2 : ℝ) ≤ H.d` using `by exact_mod_cast H.d_prime.two_le`. Establish `hconj : conj H.rt0 = -H.rt0`. Establish `hsq : conj H.rt0 ^ 2 = H.rt0 ^ 2` using `by rw [← map_pow, H.sqrt_neg_disc_sq]; simp`.

Break down `sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h' | h'` into its components or cases. It suffices to derive a contradiction. Establish `hre` using `Complex.conj_eq_iff_re.1 h'`. Establish `h2` using `H.sqrt_neg_disc_sq`. Rewrite `h2` using `[← hre]`.

Establish `h3` using `congrArg Complex.re h2`. Simplify using `[pow_two] at h3`. Use polynomial arithmetic with `[mul_self_nonneg H.rt0.re]`. Conclude with `h'`. Establish `hne : -H.rt0 ≠ H.rt0`.

Introduce `h0`. Establish `h1 : H.rt0 = 0` using `by linear_combination -h0 / 2`. Establish `h2` using `H.sqrt_neg_disc_sq`. Rewrite `h2` using `[h1]`. Establish `h3` using `congrArg Complex.re h2`.

Simplify using `at h3`. Use `H.d_prime.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hroot : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0`. Introduce `τ`.

Apply `sq_eq_sq_iff_eq_or_eq_neg.1` to reduce the goal to its premises. Establish `h1 : ((H.rt : E)) ^ 2 = -(H.d : E)`. Use `congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq` as an intermediate fact. Simplify using `using this`. Rewrite using `[← map_pow, h1, H.sqrt_neg_disc_sq]`.

Simplify using the standard rewrite rules. Take `⟨τ0⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Choose the witnesses or unpack the hypotheses as in `⟨τ1, h1⟩ : ∃ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 := by`. Break down `hroot τ0 with h0 | h0` into its components or cases. Conclude with `⟨τ0, h0⟩`.

Conclude with `⟨(starRingEnd ℂ).comp τ0, by simp [h0, hconj]⟩`. Choose the witnesses or unpack the hypotheses as in `⟨τ2, h2⟩ : ∃ τ : E →+* ℂ, τ (H.rt : E) ≠ H.rt0 := by`. Break down `hroot τ0 with h0 | h0` into its components or cases. Conclude with `⟨(starRingEnd ℂ).comp τ0, by simp [h0, hconj, hne]⟩`. Conclude with `⟨τ0, by rw [h0]; exact hne⟩`.

Establish `hp` using `(hty τ1).1 h1`. Establish `hq` using `(hty τ2).2 h2`. Establish `k1` using `key τ1`. Establish `k2` using `key τ2`. Use `⟨by omega, by omega, fun τ => ⟨fun hτ => ?_, fun hτ => ?_⟩⟩` and prove the remaining obligations.

Use `(hty τ).1 hτ` as an intermediate fact. Use `key τ` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `(hty τ).2 hτ` as an intermediate fact. Use `key τ` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem _root_.GlobalTheory.ComplementTypes.types (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p q r g g' : ℕ)
    (ty : Fin g → (E →+* ℂ)) (ty' : Fin g' → (E →+* ℂ)) (hty : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTypeFn H p q ty)
    (h : ∀ a : 𝓞 E, ∑ i, ty i (a : E) = (r : ℂ) * ∑ τ : E →+* ℂ, τ (H.bar a : E) + ∑ j, ty' j (a : E)) :
    r ≤ p ∧ r ≤ q ∧ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTypeFn H (p - r) (q - r) ty' := by
  classical
  let c : E →+* E := (IsCMField.complexConj E).toAlgHom.toRingHom
  have hcc : ∀ x, c (c x) = x := fun x => by simp [c]
  let t : (Fin r × (E →+* ℂ)) ⊕ Fin g' → (E →+* ℂ) := Sum.elim (fun k => k.2.comp c) ty'
  have hsum : ∀ a : 𝓞 E, ∑ i, ty i (a : E) = ∑ k, t k (a : E) := by
    intro a
    rw [h a, Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp [t, c, H.bar_eq]
  obtain ⟨e, he⟩ := _root_.GlobalTheory.PeriodNonempty.exists_equiv_of_sum_eq ty t hsum
  have key : ∀ τ : E →+* ℂ, Nat.card {i // ty i = τ} = r + Nat.card {j // ty' j = τ} := by
    intro τ
    have hc1 : ∀ σ : E →+* ℂ, σ.comp c = τ ↔ σ = τ.comp c := fun σ =>
      ⟨fun hσ => by ext x; rw [← hσ]; simp [hcc], fun hσ => by ext x; rw [hσ]; simp [hcc]⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_congr (e.subtypeEquiv (p := fun i => ty i = τ) (q := fun k => t k = τ) fun i => by
        simp only [he]), Fintype.card_subtype,
      Fintype.card_subtype, Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type,
      Fintype.sum_prod_type]
    simp only [t, Sum.elim_inl, Sum.elim_inr, hc1, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one]
    congr 1
  have hd : (2 : ℝ) ≤ H.d := by exact_mod_cast H.d_prime.two_le
  have hconj : conj H.rt0 = -H.rt0 := by
    have hsq : conj H.rt0 ^ 2 = H.rt0 ^ 2 := by rw [← map_pow, H.sqrt_neg_disc_sq]; simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h' | h'
    · exfalso
      have hre := Complex.conj_eq_iff_re.1 h'
      have h2 := H.sqrt_neg_disc_sq
      rw [← hre] at h2
      have h3 := congrArg Complex.re h2
      simp [pow_two] at h3
      nlinarith [mul_self_nonneg H.rt0.re]
    · exact h'
  have hne : -H.rt0 ≠ H.rt0 := by
    intro h0
    have h1 : H.rt0 = 0 := by linear_combination -h0 / 2
    have h2 := H.sqrt_neg_disc_sq
    rw [h1] at h2
    have h3 := congrArg Complex.re h2
    simp at h3
    have := H.d_prime.two_le
    omega
  have hroot : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
    intro τ
    apply sq_eq_sq_iff_eq_or_eq_neg.1
    have h1 : ((H.rt : E)) ^ 2 = -(H.d : E) := by
      have := congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq
      simpa using this
    rw [← map_pow, h1, H.sqrt_neg_disc_sq]
    simp
  obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨τ1, h1⟩ : ∃ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 := by
    rcases hroot τ0 with h0 | h0
    · exact ⟨τ0, h0⟩
    · exact ⟨(starRingEnd ℂ).comp τ0, by simp [h0, hconj]⟩
  obtain ⟨τ2, h2⟩ : ∃ τ : E →+* ℂ, τ (H.rt : E) ≠ H.rt0 := by
    rcases hroot τ0 with h0 | h0
    · exact ⟨(starRingEnd ℂ).comp τ0, by simp [h0, hconj, hne]⟩
    · exact ⟨τ0, by rw [h0]; exact hne⟩
  have hp := (hty τ1).1 h1
  have hq := (hty τ2).2 h2
  have k1 := key τ1
  have k2 := key τ2
  refine ⟨by omega, by omega, fun τ => ⟨fun hτ => ?_, fun hτ => ?_⟩⟩
  · have := (hty τ).1 hτ
    have := key τ
    omega
  · have := (hty τ).2 hτ
    have := key τ
    omega

end GlobalTheory.ComplementTypes
