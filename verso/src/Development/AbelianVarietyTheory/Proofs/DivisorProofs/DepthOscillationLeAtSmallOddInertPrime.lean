import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDepthSumRoundingOscillationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorDepthBetweenZeroAndBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorDepthBoundedOddInertPrimeCmTypeStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
open GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification (IsBig IsSmall IsSpread sumSmallSpread not_isBig_iff)

namespace GlobalTheory.RefSum.OscInert

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

open Classical in

/- English proof (translation)
Establish `hne : starRingEnd ℂ H.rt0 ≠ H.rt0`. Introduce `h`. Establish `him : H.rt0.im = 0` using `Complex.conj_eq_iff_im.1 h`. Establish `h2` using `congrArg Complex.re H.sqrt_neg_disc_sq`. Simplify using `[pow_two, Complex.mul_re, him] at h2`.

Establish `hd : (2:ℝ) ≤ H.d` using `by exact_mod_cast H.d_prime.two_le`. Use polynomial arithmetic with `[sq_nonneg H.rt0.re]`. Establish `hinj : (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card ≤ (Finset.univ.filter (fun τ : E →+* ℂ => ¬ InPsi H τ)).card`. Use `Finset.card_le_card_of_injOn (fun τ => (starRingEnd ℂ).comp τ) ?_ ?_` and prove the remaining obligations. Introduce `τ hτ`.

Simplify using `only [Finset.coe_filter, Finset.mem_filter, Finset.mem_coe, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hτ ⊢`. Unfold `InPsi at hτ ⊢`. Simplify using `only [RingHom.coe_comp, Function.comp_apply, hτ]`. Conclude with `hne`. Introduce `τ _ σ _ h`.

Use extensionality with `x`. Use `congrArg (fun g : E →+* ℂ => starRingEnd ℂ (g x)) h` as an intermediate fact. Simplify using `using this`. Establish `htot` using `Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (E →+* ℂ))) (fun τ => InPsi H τ)`. Rewrite `htot` using `[Finset.card_univ, NumberField.Embeddings.card]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem two_mul_card_psi_le :
    2 * (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card ≤ Module.finrank ℚ E := by
  have hne : starRingEnd ℂ H.rt0 ≠ H.rt0 := by
    intro h
    have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h
    have h2 := congrArg Complex.re H.sqrt_neg_disc_sq
    simp [pow_two, Complex.mul_re, him] at h2
    have hd : (2:ℝ) ≤ H.d := by exact_mod_cast H.d_prime.two_le
    nlinarith [sq_nonneg H.rt0.re]
  have hinj : (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card ≤
      (Finset.univ.filter (fun τ : E →+* ℂ => ¬ InPsi H τ)).card := by
    refine Finset.card_le_card_of_injOn (fun τ => (starRingEnd ℂ).comp τ) ?_ ?_
    · intro τ hτ
      simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_coe, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hτ ⊢
      unfold InPsi at hτ ⊢
      simp only [RingHom.coe_comp, Function.comp_apply, hτ]
      exact hne
    · intro τ _ σ _ h
      ext x
      have := congrArg (fun g : E →+* ℂ => starRingEnd ℂ (g x)) h
      simpa using this
  have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (E →+* ℂ)))
    (fun τ => InPsi H τ)
  rw [Finset.card_univ, NumberField.Embeddings.card] at htot
  omega

open Classical in

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5, h6⟩` from `hS`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.card_le_card_of_injOn (fun f => f.2.val) ?_ ?_` and prove the remaining obligations. Introduce `f hf`. Simplify using `only [Finset.coe_filter, Finset.mem_filter, Finset.mem_coe, Finset.mem_univ, true_and, Set.mem_setOf_eq, Finset.mem_Ico] at hf ⊢`.

Take `⟨⟨hpsi, hk⟩, -⟩` from `hf`. Establish `hlt` using `f.2.isLt`. Establish `hm : Dw.mult f.1 = Dw.p` using `if_pos hpsi`. Establish `hk' : k ≤ f.2.val + 1 + 1` using `hk`. Use linear arithmetic over natural numbers and integers.

Introduce `f hf g hg hfg`. Simplify using `only [Finset.coe_filter, Finset.mem_filter, Finset.mem_coe, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hf hg`. Take `⟨τ1, j1⟩` from `f`. Take `⟨τ2, j2⟩` from `g`. Take `⟨-, h1'⟩` from `hf`.

Take `⟨-, h2'⟩` from `hg`. Simplify using `only at h1' h2' hfg`. Substitute `h1' h2'` using the available equality. Conclude with `Sigma.ext rfl (heq_of_eq (Fin.ext hfg))`. Use `_ ≤ m + 1 := by rw [Nat.card_Ico]; omega`.
-/
theorem card_big_fiber_le {Dw : Datum H} {F k m : ℕ} (hS : Shape Dw F k m) (τ : E →+* ℂ) :
    (Finset.univ.filter (fun f : Lt1 Dw => IsBig k f ∧ f.1 = τ)).card ≤ m + 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS
  calc _ ≤ (Finset.Ico (k - 2) Dw.p).card := by
        refine Finset.card_le_card_of_injOn (fun f => f.2.val) ?_ ?_
        · intro f hf
          simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_coe, Finset.mem_univ, true_and,
            Set.mem_setOf_eq, Finset.mem_Ico] at hf ⊢
          obtain ⟨⟨hpsi, hk⟩, -⟩ := hf
          have hlt := f.2.isLt
          have hm : Dw.mult f.1 = Dw.p := if_pos hpsi
          have hk' : k ≤ f.2.val + 1 + 1 := hk
          omega
        · intro f hf g hg hfg
          simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_coe, Finset.mem_univ, true_and,
            Set.mem_setOf_eq] at hf hg
          obtain ⟨τ1, j1⟩ := f
          obtain ⟨τ2, j2⟩ := g
          obtain ⟨-, h1'⟩ := hf
          obtain ⟨-, h2'⟩ := hg
          simp only at h1' h2' hfg
          subst h1' h2'
          exact Sigma.ext rfl (heq_of_eq (Fin.ext hfg))
    _ ≤ m + 1 := by rw [Nat.card_Ico]; omega

/- English proof (translation)
Establish `hp' : (2 : ℝ) ≤ p` using `by exact_mod_cast hp`. Establish `hq' : (q : ℝ) ≤ m` using `by exact_mod_cast hq`. Establish `hi' : (N : ℝ) ≤ m + i` using `by exact_mod_cast hi`. Establish `hiN' : (i : ℝ) ≤ N` using `by exact_mod_cast hiN`. Establish `hc' : (1 : ℝ) ≤ c` using `by exact_mod_cast hc`.

Establish `hcM' : (c : ℝ) ≤ M` using `by exact_mod_cast hcM`. Establish `hq0 : (0 : ℝ) ≤ q` using `Nat.cast_nonneg _`. Establish `hm0 : (0 : ℝ) ≤ m` using `Nat.cast_nonneg _`. Establish `hl0 : 0 ≤ Real.logb p c` using `Real.logb_nonneg (by linarith) hc'`. Establish `hl : Real.logb p c ≤ Real.logb p M` using `Real.logb_le_logb_of_le (by linarith) (by linarith) hcM'`.

Establish `hp1 : (0 : ℝ) < (p : ℝ) - 1` using `by linarith`. Establish `hp2 : (0 : ℝ) < (p : ℝ) ^ 2 - 1` using `by nlinarith`. Establish `hcm : (0 : ℝ) ≤ c * m` using `by positivity`. Establish `t1 : (c : ℝ) * ((N : ℝ) - 2 * q - i) * p / ((p : ℝ) ^ 2 - 1) ≤ c * m / ((p : ℝ) - 1)`. Combine the equalities or inequalities in the displayed calculation.

Combine the linear equalities and inequalities to obtain the conclusion. Use `_ ≤ _ := by`. Rewrite using `[div_le_div_iff₀ hp2 hp1]`. Use polynomial arithmetic with `[mul_nonneg hcm hp1.le]`. Establish `t2 : (c : ℝ) * q * (3 + 1 / 2 * Real.logb p c) / ((p : ℝ) - 1) ≤ c * m * (3 + 1 / 2 * Real.logb p M) / ((p : ℝ) - 1)` using `by gcongr`.

Establish `t3 : (i : ℝ) ^ 2 * (Real.logb p c + 1) ≤ (N : ℝ) ^ 2 * (Real.logb p M + 1)` using `by gcongr`. Establish `e : (c : ℝ) * (m * (4 + Real.logb p M / 2) / ((p : ℝ) - 1)) = c * m / ((p : ℝ) - 1) + c * m * (3 + 1 / 2 * Real.logb p M) / ((p : ℝ) - 1)` using `by ring`. Unfold `boundFine`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem boundFine_le {p N q i c m M : ℕ} (hp : 2 ≤ p) (hq : q ≤ m) (hi : N ≤ m + i) (hiN : i ≤ N) (hc : 1 ≤ c)
    (hcM : c ≤ M) :
    boundFine p N q i c ≤ (c : ℝ) * (m * (4 + Real.logb p M / 2) / ((p : ℝ) - 1)) + (N : ℝ) ^ 2 * (Real.logb p M + 1) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hq' : (q : ℝ) ≤ m := by exact_mod_cast hq
  have hi' : (N : ℝ) ≤ m + i := by exact_mod_cast hi
  have hiN' : (i : ℝ) ≤ N := by exact_mod_cast hiN
  have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hcM' : (c : ℝ) ≤ M := by exact_mod_cast hcM
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hl0 : 0 ≤ Real.logb p c := Real.logb_nonneg (by linarith) hc'
  have hl : Real.logb p c ≤ Real.logb p M := Real.logb_le_logb_of_le (by linarith) (by linarith) hcM'
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp2 : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hcm : (0 : ℝ) ≤ c * m := by positivity
  have t1 : (c : ℝ) * ((N : ℝ) - 2 * q - i) * p / ((p : ℝ) ^ 2 - 1) ≤ c * m / ((p : ℝ) - 1) := by
    calc _ ≤ (c : ℝ) * m * p / ((p : ℝ) ^ 2 - 1) := by
          gcongr
          linarith
      _ ≤ _ := by
          rw [div_le_div_iff₀ hp2 hp1]
          nlinarith [mul_nonneg hcm hp1.le]
  have t2 : (c : ℝ) * q * (3 + 1 / 2 * Real.logb p c) / ((p : ℝ) - 1) ≤
      c * m * (3 + 1 / 2 * Real.logb p M) / ((p : ℝ) - 1) := by
    gcongr
  have t3 : (i : ℝ) ^ 2 * (Real.logb p c + 1) ≤ (N : ℝ) ^ 2 * (Real.logb p M + 1) := by
    gcongr
  have e : (c : ℝ) * (m * (4 + Real.logb p M / 2) / ((p : ℝ) - 1)) =
      c * m / ((p : ℝ) - 1) + c * m * (3 + 1 / 2 * Real.logb p M) / ((p : ℝ) - 1) := by ring
  unfold boundFine
  linarith

open Classical in

/- English proof (translation)
Establish `hfib` using `card_big_fiber_le hS`. Take `⟨h1, h2, h3, h4, h5, h6⟩` from `hS`. Take `⟨hMb, hτ, hSm, hcM⟩` from `hB`. Establish `hp' : (2 : ℝ) ≤ p` using `by exact_mod_cast hp`. Establish `hp1 : (0 : ℝ) < (p : ℝ) - 1` using `by linarith`.

Establish `hL : 0 ≤ Real.logb p M` using `Real.logb_nonneg (by linarith) (by exact_mod_cast hM)`. Establish `hF : (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card ≤ F`. Use `two_mul_card_psi_le (H := H)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hF' : ((Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card : ℝ) ≤ F` using `by exact_mod_cast hF`.

Use `set X : ℝ := m * (4 + Real.logb p M / 2) / ((p : ℝ) - 1) with hX`. Use `set Y : ℝ := ((Dw.p + Dw.q : ℕ) : ℝ) ^ 2 * (Real.logb p M + 1) with hY`. Establish `hX0 : 0 ≤ X` using `by positivity`. Establish `hY0 : 0 ≤ Y` using `by positivity`. Establish `hmaps : ∀ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f), f.1 ∈ Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)` using `fun f hf => Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hf).2.1⟩`.

Establish `hbig : ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f), ((cx f : ℝ) * X + Y) ≤ F * (Mb * X + (m + 1) * Y)`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to hmaps]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.filter_filter, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]`.

Establish `a1` using `hτ τ`. Establish `a2 : ((Finset.univ.filter (fun f : Lt1 Dw => IsBig k f ∧ f.1 = τ)).card : ℝ) ≤ m + 1`. Conclude with `hfib τ` after adjusting the coercions. Rewrite `a1` using `[Nat.cast_sum]`. Use `add_le_add (mul_le_mul_of_nonneg_right ?_ hX0) (mul_le_mul_of_nonneg_right ?_ hY0)` and prove the remaining obligations.

Use `a1` and compare the differences between its conclusion and the goal. Use `a2` and compare the differences between its conclusion and the goal. Use `_ ≤ _ := by`. Rewrite using `[Finset.sum_const, nsmul_eq_mul]`. Conclude with `mul_le_mul_of_nonneg_right hF' (by positivity)`.

Establish `hsm : ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => ¬ IsBig k f), boundAll p (rk f) (cx f) ≤ Sm / ((p : ℝ) - 1)`. Use `le_trans (le_of_eq ?_) (div_le_div_of_nonneg_right hSm hp1.le)` and prove the remaining obligations. Unfold `sumSmallSpread boundAll`. Rewrite using `[Nat.cast_sum, Finset.sum_div]`. Use `Finset.sum_congr ?_ fun f _ => by rw [Nat.cast_mul]` and prove the remaining obligations.

Use extensionality with `f`. Simplify using `only [Finset.mem_filter, not_isBig_iff]`. Rewrite using `[← Finset.sum_filter_add_sum_filter_not Finset.univ (fun f : Lt1 Dw => IsBig k f)]`. Establish `e : eSmall F (Dw.p + Dw.q) m Mb Sm M p = F * (Mb * X + (m + 1) * Y) + Sm / ((p : ℝ) - 1)`. Rewrite using `[hX, hY]`.

Unfold `eSmall`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `add_le_add (le_trans (Finset.sum_le_sum fun f hf => ?_) hbig) (le_trans (le_of_eq ?_) hsm)` and prove the remaining obligations. Establish `hb : IsBig k f` using `(Finset.mem_filter.1 hf).2`.

Establish `hm : Dw.mult f.1 = Dw.p` using `if_pos hb.1`. Establish `hr` using `rk_le f`. Establish `hk` using `hb.2`. Use `split_ifs with h`. Conclude with `boundFine_le hp h2 (by omega) (by omega) h.2 (hcM f)`.

Establish `h0 : cx f = 0`. Assume the negation of the conclusion as `hne`. Conclude with `h ⟨hb, by omega⟩`. Simplify using `[boundAll, h0, hY0]`. Conclude with `Finset.sum_congr rfl fun f hf => if_neg fun h => (Finset.mem_filter.1 hf).2 h.1`.
-/
theorem sum_bound_le {Dw : Datum H} {F k m M : ℕ} {Mb Sm : ℝ} {cx : Lt1 Dw → ℕ} {p : ℕ}
    (hS : Shape Dw F k m) (hB : ExpBd Dw k cx Mb Sm M) (hp : 2 ≤ p) (hM : 1 ≤ M) :
    ∑ f, (if IsBig k f ∧ 1 ≤ cx f then boundFine p (Dw.p + Dw.q) Dw.q (rk f) (cx f) else boundAll p (rk f) (cx f))
      ≤ eSmall F (Dw.p + Dw.q) m Mb Sm M p := by
  have hfib := card_big_fiber_le hS
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS
  obtain ⟨hMb, hτ, hSm, hcM⟩ := hB
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hL : 0 ≤ Real.logb p M := Real.logb_nonneg (by linarith) (by exact_mod_cast hM)
  have hF : (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card ≤ F := by
    have := two_mul_card_psi_le (H := H)
    omega
  have hF' : ((Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card : ℝ) ≤ F := by exact_mod_cast hF
  set X : ℝ := m * (4 + Real.logb p M / 2) / ((p : ℝ) - 1) with hX
  set Y : ℝ := ((Dw.p + Dw.q : ℕ) : ℝ) ^ 2 * (Real.logb p M + 1) with hY
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have hmaps : ∀ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f),
      f.1 ∈ Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ) := fun f hf =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hf).2.1⟩
  have hbig : ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f), ((cx f : ℝ) * X + Y) ≤
      F * (Mb * X + (m + 1) * Y) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    calc _ ≤ ∑ _τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ), (Mb * X + (m + 1) * Y) := by
          refine Finset.sum_le_sum fun τ _ => ?_
          rw [Finset.filter_filter, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
          have a1 := hτ τ
          have a2 : ((Finset.univ.filter (fun f : Lt1 Dw => IsBig k f ∧ f.1 = τ)).card : ℝ) ≤ m + 1 := by
            exact_mod_cast hfib τ
          rw [Nat.cast_sum] at a1
          refine add_le_add (mul_le_mul_of_nonneg_right ?_ hX0) (mul_le_mul_of_nonneg_right ?_ hY0)
          · convert a1
          · convert a2
      _ ≤ _ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right hF' (by positivity)
  have hsm : ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => ¬ IsBig k f), boundAll p (rk f) (cx f) ≤
      Sm / ((p : ℝ) - 1) := by
    refine le_trans (le_of_eq ?_) (div_le_div_of_nonneg_right hSm hp1.le)
    unfold sumSmallSpread boundAll
    rw [Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr ?_ fun f _ => by rw [Nat.cast_mul]
    ext f
    simp only [Finset.mem_filter, not_isBig_iff]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun f : Lt1 Dw => IsBig k f)]
  have e : eSmall F (Dw.p + Dw.q) m Mb Sm M p = F * (Mb * X + (m + 1) * Y) + Sm / ((p : ℝ) - 1) := by
    rw [hX, hY]
    unfold eSmall
    ring
  rw [e]
  refine add_le_add (le_trans (Finset.sum_le_sum fun f hf => ?_) hbig) (le_trans (le_of_eq ?_) hsm)
  · have hb : IsBig k f := (Finset.mem_filter.1 hf).2
    have hm : Dw.mult f.1 = Dw.p := if_pos hb.1
    have hr := rk_le f
    have hk := hb.2
    split_ifs with h
    · exact boundFine_le hp h2 (by omega) (by omega) h.2 (hcM f)
    · have h0 : cx f = 0 := by
        by_contra hne
        exact h ⟨hb, by omega⟩
      simp [boundAll, h0, hY0]
  · exact Finset.sum_congr rfl fun f hf => if_neg fun h => (Finset.mem_filter.1 hf).2 h.1

end GlobalTheory.RefSum.OscInert

namespace GlobalTheory.RefSum

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c F k m M Mb Sm cx hS hB p hp hp2 hpd hin hM la`. Establish `key : ∀ f : Lt1 Dw, ∃ A B : ℝ, FacBetween Xo la f (cx f) A B ∧ B - A ≤ (if IsBig k f ∧ 1 ≤ cx f then boundFine p (Dw.p + Dw.q) Dw.q (rk f) (cx f) else boundAll p (rk f) (cx f))`. Introduce `f`. Use `split_ifs with h`. Conclude with `GlobalTheory.T.factor_depth_bounded_odd_inert_prime_cmType E H Dw l Xo c p la hp2 hpd hin f (cx f) h.1.1 h.2`.

Conclude with `⟨0, _, (GlobalTheory.T.factorDepth_between_zero_and_bound E H Dw l Xo c p la f (cx f)).1, (sub_zero _).le⟩`. Use `choose A B hAB hle using key`. Take `⟨-, n, hn⟩` from `(GlobalTheory.T.productDepth_sum_rounding_oscillation E H Dw l Xo c p la cx).1 A B hAB`. Establish `h1` using `OscInert.sum_bound_le hS hB hp.out.two_le hM`. Establish `h2` using `(Finset.sum_le_sum fun f (_ : f ∈ Finset.univ) => hle f).trans (by convert h1)`.

Conclude with `⟨n, fun T io e ho y => ⟨(hn T io e ho y).1, fun ha => ((hn T io e ho y).2 ha).trans (EReal.coe_le_coe_iff.2 (by linarith))⟩⟩`.
-/
theorem oscLe_eSmall_of_inert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ (p : ℤ) ∣ discr E → InertInK H p → 1 ≤ M → OscLe Xo c p cx (eSmall F (Dw.p + Dw.q) m Mb Sm M p + 1) := by
  intro E _ _ _ H Dw l Xo c F k m M Mb Sm cx hS hB p hp hp2 hpd hin hM la
  classical
  have key : ∀ f : Lt1 Dw, ∃ A B : ℝ, FacBetween Xo la f (cx f) A B ∧ B - A ≤
      (if IsBig k f ∧ 1 ≤ cx f then boundFine p (Dw.p + Dw.q) Dw.q (rk f) (cx f) else boundAll p (rk f) (cx f)) := by
    intro f
    split_ifs with h
    · exact GlobalTheory.T.factor_depth_bounded_odd_inert_prime_cmType E H Dw l Xo c p la hp2 hpd hin f (cx f) h.1.1 h.2
    · exact ⟨0, _, (GlobalTheory.T.factorDepth_between_zero_and_bound E H Dw l Xo c p la f (cx f)).1, (sub_zero _).le⟩
  choose A B hAB hle using key
  obtain ⟨-, n, hn⟩ := (GlobalTheory.T.productDepth_sum_rounding_oscillation E H Dw l Xo c p la cx).1 A B hAB
  have h1 := OscInert.sum_bound_le hS hB hp.out.two_le hM
  have h2 := (Finset.sum_le_sum fun f (_ : f ∈ Finset.univ) => hle f).trans (by convert h1)
  exact ⟨n, fun T io e ho y => ⟨(hn T io e ho y).1, fun ha => ((hn T io e ho y).2 ha).trans
    (EReal.coe_le_coe_iff.2 (by linarith))⟩⟩

end GlobalTheory.RefSum

end
