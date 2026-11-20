import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelMulOfPosLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelCoeffAndFunctionUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionsCoeffwiseConjugateRingClosure
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQOfIntegralQuotStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN

/- English proof (translation)
Introduce `_` and use `by simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)`.
-/
theorem conjEx_hasQ_zero (N : ℕ) : HasQ N (fun _ => (0 : ℂ)) (fun _ => 0) := fun _ => by
  simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)

/- English proof (translation)
Simplify using `[conv, PowerSeries.coeff_mul]`.
-/
theorem conjEx_conv_coeff (a b : ℕ → ℂ) (n : ℕ) :
    conv a b n = PowerSeries.coeff n (PowerSeries.mk a * PowerSeries.mk b) := by
  simp [conv, PowerSeries.coeff_mul]

/- English proof (translation)
Use function extensionality and compare the values at `n`. Simplify using `[conv, map_sum, map_mul]`.
-/
theorem conjEx_conv_map (g : ℂ ≃+* ℂ) (a b : ℕ → ℂ) :
    (fun n => g (conv a b n)) = conv (fun n => g (a n)) (fun n => g (b n)) := by
  funext n; simp [conv, map_sum, map_mul]

/- English proof (translation)
Establish `hmk : PowerSeries.mk d ≠ 0`. Introduce `h0`. Apply `hd` to reduce the goal to its premises. Use function extensionality and compare the values at `n`. Use `congrArg (PowerSeries.coeff n) h0` as an intermediate fact.

Simplify using `using this`. Establish `hm : PowerSeries.mk a * PowerSeries.mk d = PowerSeries.mk b * PowerSeries.mk d`. Use extensionality with `n`. Use `congrFun h n` as an intermediate fact. Rewrite `this` using `[conjEx_conv_coeff, conjEx_conv_coeff]`. Then use the resulting hypothesis.

Use `mul_right_cancel₀ hmk hm` as an intermediate fact. Use function extensionality and compare the values at `n`. Use `congrArg (PowerSeries.coeff n) this` as an intermediate fact. Simplify using `using this`.
-/
theorem conjEx_conv_cancel (a b d : ℕ → ℂ) (hd : d ≠ 0) (h : conv a d = conv b d) : a = b := by
  have hmk : PowerSeries.mk d ≠ 0 := by
    intro h0; apply hd; funext n
    have := congrArg (PowerSeries.coeff n) h0
    simpa using this
  have hm : PowerSeries.mk a * PowerSeries.mk d = PowerSeries.mk b * PowerSeries.mk d := by
    ext n
    have := congrFun h n
    rwa [conjEx_conv_coeff, conjEx_conv_coeff] at this
  have := mul_right_cancel₀ hmk hm
  funext n
  have := congrArg (PowerSeries.coeff n) this
  simpa using this

/- English proof (translation)
Introduce `g N n f D D' A A' s s' hN ⟨a, ha⟩ ⟨d, hd, hd'⟩ ⟨e, he, he'⟩ hs hD hfA hpol`. Take `⟨uc, uf⟩` from `GlobalTheory.QFam.hasQ_unique_both`. Establish `hz` using `conjEx_hasQ_zero N`. Establish `hd0 : d ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hD (uf N D (fun _ => 0) _ hd hz)`. Establish `hgd0 : (fun n => g (d n)) ≠ 0`. Introduce `h0`. Apply `hd0` to reduce the goal to its premises. Use function extensionality and compare the values at `k`.

Use `congrFun h0 k` as an intermediate fact. Simplify using `using this`. Establish `hD' : D' ≠ 0`. Introduce and unpack `rfl`. Conclude with `hgd0 (uc N (fun _ => 0) _ _ hN hd' hz)`.

Take `⟨_, hadd, _, hmul, hpow, hsumprod⟩` from `GlobalTheory.QFam.qConj_ring g N hN`. Establish `hA : QConj g N A A'` using `⟨e, he, he'⟩`. Establish `hDD : QConj g N D D'` using `⟨d, hd, hd'⟩`. Establish `hP : QConj g N (fun τ => A τ ^ n + ∑ j, s j τ * A τ ^ (j : ℕ) * D τ ^ (n - j)) (fun τ => A' τ ^ n + ∑ j, s' j τ * A' τ ^ (j : ℕ) * D' τ ^ (n - j))`. Use `hadd _ _ _ _ (hpow _ _ n hA) ?_` and prove the remaining obligations.

Use `(hsumprod (Fin n) Finset.univ (fun j τ => s j τ * A τ ^ (j : ℕ) * D τ ^ (n - j)) (fun j τ => s' j τ * A' τ ^ (j : ℕ) * D' τ ^ (n - j)) ?_).1` and prove the remaining obligations. Introduce `j _`. Conclude with `hmul _ _ _ _ (hmul _ _ _ _ (hs j) (hpow _ _ _ hA)) (hpow _ _ _ hDD)`. Establish `hP0 : (fun τ => A τ ^ n + ∑ j, s j τ * A τ ^ (j : ℕ) * D τ ^ (n - j)) = fun _ => 0`. Use function extensionality and compare the values at `τ`.

Establish `hx : A τ ^ n + ∑ j, s j τ * A τ ^ (j : ℕ) * D τ ^ (n - j) = D τ ^ n * (f τ ^ n + ∑ j, s j τ * f τ ^ (j : ℕ))`. Rewrite using `[mul_add, Finset.mul_sum, ← hfA τ, mul_pow]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `j _`. Rewrite using `[mul_pow, show D τ ^ n = D τ ^ (j : ℕ) * D τ ^ (n - j) by`. Rewrite using `[← pow_add, Nat.add_sub_cancel' j.2.le]]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hx, hpol τ, mul_zero]`.

Establish `hP'0 : ∀ τ, A' τ ^ n + ∑ j, s' j τ * A' τ ^ (j : ℕ) * D' τ ^ (n - j) = 0`. Take `⟨c, hc, hc'⟩` from `hP`. Rewrite `hc` using `[hP0]`. Establish `hc0 : c = fun _ => 0` using `uc N _ _ _ hN hc hz`. Substitute `hc0` using the available equality.

Simplify using `only [map_zero] at hc'`. Use `uf N _ _ _ hc' hz` as an intermediate fact. Conclude with `fun τ => congrFun this τ`. Take `⟨h, b, hb, hAh⟩` from `GlobalTheory.T.exists_hasQ_quotient_of_integral N n A' D' s' hN ⟨_, he'⟩ ⟨_, hd'⟩ (fun j => by obtain ⟨c, _, hc'⟩ := hs j; exact ⟨_, hc'⟩) hD' hP'0`. Establish `hfD : HasQ N A (conv a d)`.

Use `GlobalTheory.QFam.hasQ_mul_conv N f D a d hN ha hd` as an intermediate fact. Establish `hAe : (fun τ => f τ * D τ) = A` using `funext hfA`. Rewrite `this` using `[hAe]`. Then use the resulting hypothesis. Establish `he1 : e = conv a d` using `uc N A _ _ hN he hfD`. Establish `hhD : HasQ N A' (conv b fun n => g (d n))`.

Use `GlobalTheory.QFam.hasQ_mul_conv N h D' b _ hN hb hd'` as an intermediate fact. Establish `hAe : (fun τ => h τ * D' τ) = A'` using `funext fun τ => (hAh τ).symm`. Rewrite `this` using `[hAe]`. Then use the resulting hypothesis. Establish `he2 : (fun n => g (e n)) = conv b fun n => g (d n)` using `uc N A' _ _ hN he' hhD`. Rewrite `he2` using `[he1, conjEx_conv_map]`.

Establish `hba : b = fun n => g (a n)` using `(conjEx_conv_cancel _ _ _ hgd0 he2).symm`. Use `⟨h, ⟨a, ha, hba ▸ hb⟩, fun τ => (hAh τ).symm⟩` and prove the remaining obligations.
-/
theorem conj_exists : ∀ (g : ℂ ≃+* ℂ) (N n : ℕ) (f D D' A A' : ℍ → ℂ) (s s' : Fin n → ℍ → ℂ), 0 < N → (∃ a, HasQ N f a) → QConj g N D D' → QConj g N A A' → (∀ j, QConj g N (s j) (s' j)) → D ≠ 0 → (∀ τ, f τ * D τ = A τ) → (∀ τ, f τ ^ n + ∑ j, s j τ * f τ ^ (j : ℕ) = 0) → ∃ f' : ℍ → ℂ, QConj g N f f' ∧ ∀ τ, f' τ * D' τ = A' τ := by
  intro g N n f D D' A A' s s' hN ⟨a, ha⟩ ⟨d, hd, hd'⟩ ⟨e, he, he'⟩ hs hD hfA hpol
  obtain ⟨uc, uf⟩ := GlobalTheory.QFam.hasQ_unique_both
  have hz := conjEx_hasQ_zero N
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hD (uf N D (fun _ => 0) _ hd hz)
  have hgd0 : (fun n => g (d n)) ≠ 0 := by
    intro h0; apply hd0; funext k
    have := congrFun h0 k
    simpa using this
  have hD' : D' ≠ 0 := by
    rintro rfl
    exact hgd0 (uc N (fun _ => 0) _ _ hN hd' hz)
  obtain ⟨_, hadd, _, hmul, hpow, hsumprod⟩ := GlobalTheory.QFam.qConj_ring g N hN
  have hA : QConj g N A A' := ⟨e, he, he'⟩
  have hDD : QConj g N D D' := ⟨d, hd, hd'⟩
  have hP : QConj g N (fun τ => A τ ^ n + ∑ j, s j τ * A τ ^ (j : ℕ) * D τ ^ (n - j))
      (fun τ => A' τ ^ n + ∑ j, s' j τ * A' τ ^ (j : ℕ) * D' τ ^ (n - j)) := by
    refine hadd _ _ _ _ (hpow _ _ n hA) ?_
    refine (hsumprod (Fin n) Finset.univ (fun j τ => s j τ * A τ ^ (j : ℕ) * D τ ^ (n - j))
      (fun j τ => s' j τ * A' τ ^ (j : ℕ) * D' τ ^ (n - j)) ?_).1
    intro j _
    exact hmul _ _ _ _ (hmul _ _ _ _ (hs j) (hpow _ _ _ hA)) (hpow _ _ _ hDD)
  have hP0 : (fun τ => A τ ^ n + ∑ j, s j τ * A τ ^ (j : ℕ) * D τ ^ (n - j)) = fun _ => 0 := by
    funext τ
    have hx : A τ ^ n + ∑ j, s j τ * A τ ^ (j : ℕ) * D τ ^ (n - j) =
        D τ ^ n * (f τ ^ n + ∑ j, s j τ * f τ ^ (j : ℕ)) := by
      rw [mul_add, Finset.mul_sum, ← hfA τ, mul_pow]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro j _
        rw [mul_pow, show D τ ^ n = D τ ^ (j : ℕ) * D τ ^ (n - j) by
          rw [← pow_add, Nat.add_sub_cancel' j.2.le]]
        ring
    rw [hx, hpol τ, mul_zero]
  have hP'0 : ∀ τ, A' τ ^ n + ∑ j, s' j τ * A' τ ^ (j : ℕ) * D' τ ^ (n - j) = 0 := by
    obtain ⟨c, hc, hc'⟩ := hP
    rw [hP0] at hc
    have hc0 : c = fun _ => 0 := uc N _ _ _ hN hc hz
    subst hc0
    simp only [map_zero] at hc'
    have := uf N _ _ _ hc' hz
    exact fun τ => congrFun this τ
  obtain ⟨h, b, hb, hAh⟩ := GlobalTheory.T.exists_hasQ_quotient_of_integral N n A' D' s' hN ⟨_, he'⟩ ⟨_, hd'⟩
    (fun j => by obtain ⟨c, _, hc'⟩ := hs j; exact ⟨_, hc'⟩) hD' hP'0
  have hfD : HasQ N A (conv a d) := by
    have := GlobalTheory.QFam.hasQ_mul_conv N f D a d hN ha hd
    have hAe : (fun τ => f τ * D τ) = A := funext hfA
    rwa [hAe] at this
  have he1 : e = conv a d := uc N A _ _ hN he hfD
  have hhD : HasQ N A' (conv b fun n => g (d n)) := by
    have := GlobalTheory.QFam.hasQ_mul_conv N h D' b _ hN hb hd'
    have hAe : (fun τ => h τ * D' τ) = A' := funext fun τ => (hAh τ).symm
    rwa [hAe] at this
  have he2 : (fun n => g (e n)) = conv b fun n => g (d n) := uc N A' _ _ hN he' hhD
  rw [he1, conjEx_conv_map] at he2
  have hba : b = fun n => g (a n) := (conjEx_conv_cancel _ _ _ hgd0 he2).symm
  refine ⟨h, ⟨a, ha, hba ▸ hb⟩, fun τ => (hAh τ).symm⟩

end GlobalTheory.FN
