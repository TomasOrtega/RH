import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapQuotBijective
open Polynomial

namespace GlobalTheory.PicDiv

/- English proof (translation)
Introduce `k A _ _ _ _ _ _ N I _ D P₀ P Q Q' f₀ f hP₀ hP hQ hQ' hinj hQ'P hDQ' hDP hf₀ hf hspan hfD hfP hfQ' hdeg`. Take `⟨_hfin, hmax, hmul, hle⟩` from `GlobalTheory.DedekindCodimG.dedekind_finiteType_codim k A`. Establish `hPne : P ≠ ⊥`. Introduce `h`. Apply `hf` to reduce the goal to its premises.

Rewrite `hfP` using `[h]`. Simplify using `using hfP`. Establish `hmaxne : ∀ M : Ideal A, M.IsMaximal → M ≠ ⊥`. Introduce `M hM h`. Substitute `h` using the available equality.

Conclude with `hPne (hM.eq_of_le hP.ne_top bot_le).symm`. Establish `hDne : D ≠ ⊥`. Introduce `h`. Conclude with `hDP (h ▸ bot_le)`. Establish `hprodne : ∀ (s : Finset I) (g : I → Ideal A), (∀ i, g i ≠ ⊥) → (∏ i ∈ s, g i) ≠ ⊥`.

Introduce `s g hg`. Rewrite using `[← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]`. Introduce `i _`. Rewrite using `[Ideal.zero_eq_bot]`. Conclude with `hg i`.

Establish `hpowne : ∀ (M : Ideal A) (n : ℕ), M ≠ ⊥ → M ^ n ≠ ⊥`. Introduce `M n hM`. Rewrite `hM`, the goal using `[← Ideal.zero_eq_bot]`. Conclude with `pow_ne_zero n hM`. Establish `hmulne : ∀ (M M' : Ideal A), M ≠ ⊥ → M' ≠ ⊥ → M * M' ≠ ⊥`.

Introduce `M M' hM hM'`. Rewrite `hM`, `hM'`, the goal using `[← Ideal.zero_eq_bot]`. Conclude with `mul_ne_zero hM hM'`. Establish `htop : Module.finrank k (A ⧸ (⊤ : Ideal A)) = 0` using `by haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl`. Conclude with `Module.finrank_zero_of_subsingleton`.

Establish `hpow : ∀ (M : Ideal A) (n : ℕ), M.IsMaximal → Module.finrank k (A ⧸ M ^ n) = n`. Introduce `M n hM`. Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, Ideal.one_eq_top, htop]`. Consider the case `succ n ih`.

Rewrite using `[pow_succ, hmul _ _ (hpowne M n (hmaxne M hM)) (hmaxne M hM), ih, (hmax M hM).1]`. Establish `hprod : ∀ (s : Finset I) (g : I → Ideal A), (∀ i, g i ≠ ⊥) → Module.finrank k (A ⧸ ∏ i ∈ s, g i) = ∑ i ∈ s, Module.finrank k (A ⧸ g i)`. Introduce `s g hg`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => rw [Finset.prod_empty, Finset.sum_empty, Ideal.one_eq_top, htop]`.

Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, hmul _ _ (hg a) (hprodne s g hg), ih]`. Establish `hPowProd : ∀ (R : I → Ideal A), (∀ i, (R i).IsMaximal) → Module.finrank k (A ⧸ ∏ i, R i ^ N) = N * Fintype.card I`. Introduce `R hR`. Rewrite using `[hprod _ _ (fun i => hpowne _ _ (hmaxne _ (hR i)))]`.

Simplify using `only [hpow _ _ (hR _), Finset.sum_const, Finset.card_univ, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hPowNe : ∀ (R : I → Ideal A), (∀ i, (R i).IsMaximal) → (∏ i, R i ^ N) ≠ ⊥` using `fun R hR => hprodne _ _ (fun i => hpowne _ _ (hmaxne _ (hR i)))`. Establish `h0 : Module.finrank k (A ⧸ Ideal.span {f₀}) = 1 + Module.finrank k (A ⧸ D) + N * Fintype.card I`. Rewrite using `[hspan, hmul _ _ (hmulne _ _ (hmaxne _ hP₀) hDne) (hPowNe Q hQ), hmul _ _ (hmaxne _ hP₀) hDne, (hmax _ hP₀).1, hPowProd Q hQ]`.

Establish `hcop_max : ∀ M M' : Ideal A, M.IsMaximal → M'.IsMaximal → M ≠ M' → IsCoprime M M'`. Introduce `M M' hM hM' hne`. Rewrite using `[Ideal.isCoprime_iff_sup_eq]`. Assume the negation of the conclusion as `h`. Establish `h1` using `hM.eq_of_le h le_sup_left`.

Establish `h2` using `hM'.eq_of_le h le_sup_right`. Conclude with `hne (h1.trans h2.symm)`. Establish `hcopD : ∀ M : Ideal A, M.IsMaximal → ¬ D ≤ M → IsCoprime M D`. Introduce `M hM hDM`. Rewrite using `[Ideal.isCoprime_iff_sup_eq]`.

Assume the negation of the conclusion as `h`. Conclude with `hDM (le_sup_right.trans (hM.eq_of_le h le_sup_left).ge)`. Establish `hdvd : ∀ M : Ideal A, f ∈ M → M ∣ Ideal.span {f}` using `fun M hM => Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hM)`. Establish `hX : (∏ i, Q' i ^ N) ∣ Ideal.span {f}`. Apply `Finset.prod_dvd_of_coprime` to reduce the goal to its premises.

Introduce `i _ j _ hij`. Conclude with `(hcop_max _ _ (hQ' i) (hQ' j) (hinj.ne hij)).pow`. Introduce `i _`. Conclude with `hdvd _ (hfQ' i)`. Establish `hPD : P * D ∣ Ideal.span {f}` using `(hcopD P hP hDP).mul_dvd (hdvd _ hfP) (hdvd _ hfD)`.

Establish `hPDX : IsCoprime (P * D) (∏ i, Q' i ^ N)` using `IsCoprime.mul_left (IsCoprime.prod_right fun i _ => (hcop_max P (Q' i) hP (hQ' i) (hQ'P i).symm).pow_right) (IsCoprime.prod_right fun i _ => (hcopD (Q' i) (hQ' i) (hDQ' i)).symm.pow_right)`. Establish `hJ : P * D * ∏ i, Q' i ^ N ∣ Ideal.span {f}` using `hPDX.mul_dvd hPD hX`. Apply `hle _ _ _ (Ideal.le_of_dvd hJ)` to reduce the goal to its premises. Rewrite using `[hmul _ _ (hmulne _ _ hPne hDne) (hPowNe Q' hQ'), hmul _ _ hPne hDne, (hmax _ hP).1, hPowProd Q' hQ']`. Rewrite `hdeg` using `[h0]`.

Conclude with `hdeg`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hf`.
-/
theorem degree_count_generates : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ) (I : Type) [Fintype I] (D P₀ P : Ideal A) (Q Q' : I → Ideal A) (f₀ f : A), P₀.IsMaximal → P.IsMaximal → (∀ i, (Q i).IsMaximal) → (∀ i, (Q' i).IsMaximal) → Function.Injective Q' → (∀ i, Q' i ≠ P) → (∀ i, ¬ D ≤ Q' i) → ¬ D ≤ P →
 f₀ ≠ 0 → f ≠ 0 → Ideal.span {f₀} = P₀ * D * ∏ i, Q i ^ N → f ∈ D → f ∈ P → (∀ i, f ∈ Q' i ^ N) → Module.finrank k (A ⧸ Ideal.span {f}) ≤ Module.finrank k (A ⧸ Ideal.span {f₀}) →
 Ideal.span {f} = P * D * ∏ i, Q' i ^ N := by
  intro k A _ _ _ _ _ _ N I _ D P₀ P Q Q' f₀ f hP₀ hP hQ hQ' hinj hQ'P hDQ' hDP hf₀ hf hspan hfD hfP hfQ' hdeg
  obtain ⟨_hfin, hmax, hmul, hle⟩ := GlobalTheory.DedekindCodimG.dedekind_finiteType_codim k A
  have hPne : P ≠ ⊥ := by
    intro h; apply hf; rw [h] at hfP; simpa using hfP
  have hmaxne : ∀ M : Ideal A, M.IsMaximal → M ≠ ⊥ := by
    intro M hM h
    subst h
    exact hPne (hM.eq_of_le hP.ne_top bot_le).symm
  have hDne : D ≠ ⊥ := by
    intro h; exact hDP (h ▸ bot_le)
  have hprodne : ∀ (s : Finset I) (g : I → Ideal A), (∀ i, g i ≠ ⊥) → (∏ i ∈ s, g i) ≠ ⊥ := by
    intro s g hg
    rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    intro i _; rw [Ideal.zero_eq_bot]; exact hg i
  have hpowne : ∀ (M : Ideal A) (n : ℕ), M ≠ ⊥ → M ^ n ≠ ⊥ := by
    intro M n hM
    rw [← Ideal.zero_eq_bot] at hM ⊢
    exact pow_ne_zero n hM
  have hmulne : ∀ (M M' : Ideal A), M ≠ ⊥ → M' ≠ ⊥ → M * M' ≠ ⊥ := by
    intro M M' hM hM'
    rw [← Ideal.zero_eq_bot] at hM hM' ⊢
    exact mul_ne_zero hM hM'
  have htop : Module.finrank k (A ⧸ (⊤ : Ideal A)) = 0 := by
    haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Module.finrank_zero_of_subsingleton
  have hpow : ∀ (M : Ideal A) (n : ℕ), M.IsMaximal → Module.finrank k (A ⧸ M ^ n) = n := by
    intro M n hM
    induction n with
    | zero => rw [pow_zero, Ideal.one_eq_top, htop]
    | succ n ih =>
      rw [pow_succ, hmul _ _ (hpowne M n (hmaxne M hM)) (hmaxne M hM), ih, (hmax M hM).1]
  have hprod : ∀ (s : Finset I) (g : I → Ideal A), (∀ i, g i ≠ ⊥) →
      Module.finrank k (A ⧸ ∏ i ∈ s, g i) = ∑ i ∈ s, Module.finrank k (A ⧸ g i) := by
    intro s g hg
    classical
    induction s using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.sum_empty, Ideal.one_eq_top, htop]
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, hmul _ _ (hg a) (hprodne s g hg), ih]
  have hPowProd : ∀ (R : I → Ideal A), (∀ i, (R i).IsMaximal) →
      Module.finrank k (A ⧸ ∏ i, R i ^ N) = N * Fintype.card I := by
    intro R hR
    rw [hprod _ _ (fun i => hpowne _ _ (hmaxne _ (hR i)))]
    simp only [hpow _ _ (hR _), Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  have hPowNe : ∀ (R : I → Ideal A), (∀ i, (R i).IsMaximal) → (∏ i, R i ^ N) ≠ ⊥ :=
    fun R hR => hprodne _ _ (fun i => hpowne _ _ (hmaxne _ (hR i)))
  have h0 : Module.finrank k (A ⧸ Ideal.span {f₀}) =
      1 + Module.finrank k (A ⧸ D) + N * Fintype.card I := by
    rw [hspan, hmul _ _ (hmulne _ _ (hmaxne _ hP₀) hDne) (hPowNe Q hQ),
      hmul _ _ (hmaxne _ hP₀) hDne, (hmax _ hP₀).1, hPowProd Q hQ]
  have hcop_max : ∀ M M' : Ideal A, M.IsMaximal → M'.IsMaximal → M ≠ M' → IsCoprime M M' := by
    intro M M' hM hM' hne
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    have h1 := hM.eq_of_le h le_sup_left
    have h2 := hM'.eq_of_le h le_sup_right
    exact hne (h1.trans h2.symm)
  have hcopD : ∀ M : Ideal A, M.IsMaximal → ¬ D ≤ M → IsCoprime M D := by
    intro M hM hDM
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    exact hDM (le_sup_right.trans (hM.eq_of_le h le_sup_left).ge)
  have hdvd : ∀ M : Ideal A, f ∈ M → M ∣ Ideal.span {f} := fun M hM =>
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hM)
  have hX : (∏ i, Q' i ^ N) ∣ Ideal.span {f} := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      exact (hcop_max _ _ (hQ' i) (hQ' j) (hinj.ne hij)).pow
    · intro i _; exact hdvd _ (hfQ' i)
  have hPD : P * D ∣ Ideal.span {f} := (hcopD P hP hDP).mul_dvd (hdvd _ hfP) (hdvd _ hfD)
  have hPDX : IsCoprime (P * D) (∏ i, Q' i ^ N) :=
    IsCoprime.mul_left
      (IsCoprime.prod_right fun i _ => (hcop_max P (Q' i) hP (hQ' i) (hQ'P i).symm).pow_right)
      (IsCoprime.prod_right fun i _ => (hcopD (Q' i) (hQ' i) (hDQ' i)).symm.pow_right)
  have hJ : P * D * ∏ i, Q' i ^ N ∣ Ideal.span {f} := hPDX.mul_dvd hPD hX
  apply hle _ _ _ (Ideal.le_of_dvd hJ)
  · rw [hmul _ _ (hmulne _ _ hPne hDne) (hPowNe Q' hQ'), hmul _ _ hPne hDne, (hmax _ hP).1,
      hPowProd Q' hQ']
    rw [h0] at hdeg; exact hdeg
  · rw [Ne, Ideal.span_singleton_eq_bot]; exact hf

end GlobalTheory.PicDiv
