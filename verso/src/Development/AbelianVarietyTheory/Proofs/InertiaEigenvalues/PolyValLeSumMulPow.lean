import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Formalism.SharpRestriction.GlobalTheoremInputs

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

/- English proof (translation)
Unfold `EmbeddingTypeJumps.polyVal`. Rewrite using `[MvPolynomial.eval_eq', Finset.sum_mul]`. Use `Finset.sum_le_sum fun m hm => ?_` and prove the remaining obligations. Use `Nat.mul_le_mul_left _ ?_` and prove the remaining obligations. Establish `hM : ∀ i : Fin 3, (![f, r, t] : Fin 3 → ℕ) i ≤ f * r * t`.

Introduce `i`. Use `fin_cases i`. Use `show f ≤ f * r * t`. Simplify using `using Nat.mul_le_mul (Nat.mul_le_mul (le_refl f) hr) ht`. Use `show r ≤ f * r * t`.

Simplify using `using Nat.mul_le_mul (Nat.mul_le_mul hf (le_refl r)) ht`. Use `show t ≤ f * r * t`. Simplify using `using Nat.mul_le_mul (Nat.mul_le_mul hf hr) (le_refl t)`. Establish `hpos : 0 < f * r * t` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.

Apply `Nat.pow_le_pow_right hpos` to reduce the goal to its premises. Use `MvPolynomial.le_totalDegree hm` as an intermediate fact. Rewrite `this` using `[Finsupp.sum_fintype _ _ (by simp)]`. Then use the resulting hypothesis.
-/
theorem polyVal_le_sum_mul_pow (Q : MvPolynomial (Fin 3) ℕ) (f r t : ℕ) (hf : 1 ≤ f) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    EmbeddingTypeJumps.polyVal Q f r t ≤ (∑ m ∈ Q.support, Q.coeff m) * (f * r * t) ^ Q.totalDegree := by
  unfold EmbeddingTypeJumps.polyVal
  rw [MvPolynomial.eval_eq', Finset.sum_mul]
  refine Finset.sum_le_sum fun m hm => ?_
  refine Nat.mul_le_mul_left _ ?_
  have hM : ∀ i : Fin 3, (![f, r, t] : Fin 3 → ℕ) i ≤ f * r * t := by
    intro i
    fin_cases i
    · show f ≤ f * r * t
      simpa using Nat.mul_le_mul (Nat.mul_le_mul (le_refl f) hr) ht
    · show r ≤ f * r * t
      simpa using Nat.mul_le_mul (Nat.mul_le_mul hf (le_refl r)) ht
    · show t ≤ f * r * t
      simpa using Nat.mul_le_mul (Nat.mul_le_mul hf hr) (le_refl t)
  have hpos : 0 < f * r * t := by positivity
  calc ∏ i, (![f, r, t] : Fin 3 → ℕ) i ^ m i ≤ ∏ i : Fin 3, (f * r * t) ^ m i :=
        Finset.prod_le_prod' fun i _ => Nat.pow_le_pow_left (hM i) _
    _ = (f * r * t) ^ (∑ i, m i) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ (f * r * t) ^ Q.totalDegree := by
        apply Nat.pow_le_pow_right hpos
        have := MvPolynomial.le_totalDegree hm
        rwa [Finsupp.sum_fintype _ _ (by simp)] at this

/- English proof (translation)
Introduce `D L P ρ constantFirstHub C Q hCG hB hK hSha`. Unfold `StarG`. Introduce `i hi hl π hπ`. Unfold `Bd`. Unfold `FamilyRepresentationConstants.CG at hCG`.

Establish `hC67 : constantFirstHub ≤ C` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCG`. Establish `hS : ((∑ m ∈ Q.support, Q.coeff m : ℕ) : ℝ) ≤ C` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCG`. Establish `hdeg : (Q.totalDegree : ℝ) ≤ C` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCG`. Establish `hC1 : (1 : ℝ) ≤ C` using `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCG`. Establish `ht1 : 1 ≤ D.R.t` using `D.R.t_odd.pos`.

Establish `hr1 : 1 ≤ D.R.r`. Unfold `Ranks.r`. Use `D.R.m_add_three_le_k` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hf1 : 1 ≤ D.R.f`.

Establish `: 0 < D.R.f` using `by unfold Ranks.f Ranks.n; positivity`. Use linear arithmetic over natural numbers and integers. Establish `htr : 1 ≤ D.R.t * D.R.r` using `by simpa using Nat.mul_le_mul ht1 hr1`. Establish `hlp : (D.nd.l i).Prime`. Apply the tactic sequence `rcases hl with h | h <;> rw [h]`.

Use `exacts [D.host.hyp.1, D.host.hyp.2.1]`. Establish `hl2 : 2 < D.nd.l i`. Establish `hqd` using `D.host.qd_big`. Apply the tactic sequence `rcases hl with h | h <;> rw [h] <;> nlinarith [hqd.1, hqd.2]`. Establish `hodd : Odd (D.nd.l i)` using `hlp.odd_of_ne_two (by omega)`.

Establish `hlbig : L.sc.x ^ (2 * L.Ct + 5) < (D.nd.l i : ℝ)`. Apply the tactic sequence `rcases hl with h | h <;> rw [h]`. Use `exacts [P.qd_pow.1, P.qd_pow.2]`. Establish `hsha : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤`. Introduce `e he`.

Rewrite `he` using `[Finset.mem_Ioo]`. Use `haveI : Fact (D.nd.l i).Prime := ⟨hlp⟩`. Conclude with `lt_top_iff_ne_top.2 (hSha (D.nd.l i) e he.1 he.2)`. Establish `hK'` using `(hK i hi).1 π hπ`. Establish `h` using `hB i hl hi hlbig π hπ hK'.1 hsha`.

Establish `hVV : TwistedPlaces.VVr D (D.nd.l i) = ((∑ e ∈ Finset.Ioo 0 D.R.t, D.what₂.shaLen (D.nd.l i) e : ℚ) : ℝ)` using `by show ((∑ e ∈ Finset.Ico 1 D.R.t, D.what₂.shaLen (D.nd.l i) e : ℚ) : ℝ) = _`. Use `congr 2`. Establish `hvh : TwistedPlaces.vhE D (D.nd.l i) = (padicValNat (D.nd.l i) (hE D.host) : ℝ)` using `rfl`. Establish `heps : TwistedPlaces.epsL (D.nd.l i) = EmbeddingTypeJumps.epsL (D.nd.l i)`. Unfold `TwistedPlaces.epsL EmbeddingTypeJumps.epsL`.

Rewrite using `[one_div]`. Establish `hLpos : 0 < TwistedPlaces.large₂ L` using `Real.rpow_pos_of_pos (by linarith [L.sc.one_lt_alt]) _`. Establish `hlog : Real.log L.sc.b = TwistedPlaces.large₂ L` using `Real.log_exp _`. Establish `hbpos : 0 < L.sc.b` using `Real.exp_pos _`. Establish `hlpos : (0 : ℝ) < D.nd.l i` using `by exact_mod_cast hlp.pos`.

Establish `hbr : 0 ≤ (D.R.r : ℝ) * (L.sc.b / (D.nd.l i) + L.Sc + D.R.t + L.etaSz + TwistedPlaces.large₂ L) + D.R.m * L.sc.b`. Establish `h1` using `L.Sc_pos`. Establish `h2` using `L.etaSz_pos`. Establish `h3 : 0 ≤ L.sc.b / (D.nd.l i)` using `div_nonneg hbpos.le hlpos.le`. Establish `h4 : (0 : ℝ) ≤ D.R.t` using `Nat.cast_nonneg _`.

Establish `h5 : 0 ≤ L.sc.b / (D.nd.l i) + L.Sc + D.R.t + L.etaSz + TwistedPlaces.large₂ L` using `by linarith`. Check the signs of the components of the expression. Establish `hM1 : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * D.R.t` using `by exact_mod_cast Nat.mul_le_mul (Nat.mul_le_mul hf1 hr1) ht1`. Establish `hpoly : ((EmbeddingTypeJumps.polyVal Q D.R.f D.R.r D.R.t : ℕ) : ℝ) ≤ C * ((D.R.f : ℝ) * D.R.r * D.R.t) ^ C`. Establish `h1 : ((EmbeddingTypeJumps.polyVal Q D.R.f D.R.r D.R.t : ℕ) : ℝ) ≤ ((∑ m ∈ Q.support, Q.coeff m : ℕ) : ℝ) * ((D.R.f : ℝ) * D.R.r * D.R.t) ^ Q.totalDegree`.

Conclude with `polyVal_le_sum_mul_pow Q _ _ _ hf1 hr1 ht1` after adjusting the coercions. Establish `hpow : ((D.R.f : ℝ) * D.R.r * D.R.t) ^ Q.totalDegree ≤ ((D.R.f : ℝ) * D.R.r * D.R.t) ^ C`. Rewrite using `[← Real.rpow_natCast]`. Conclude with `Real.rpow_le_rpow_of_exponent_le hM1 hdeg`. Conclude with `h1.trans (mul_le_mul hS hpow (by positivity) (by linarith))`.

Establish `hbnd : EmbeddingTypeJumps.bndB D L constantFirstHub Q (D.nd.l i) ≤ TwistedPlaces.midG L C (D.nd.l i)`. Unfold `EmbeddingTypeJumps.bndB TwistedPlaces.midG`. Rewrite using `[hlog]`. Establish `e1` using `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC67 (Nat.cast_nonneg D.R.f)) hbr`. Establish `e2` using `mul_le_mul_of_nonneg_right hpoly hLpos.le`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hVV, hvh, heps]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem starG_of_thmB : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (ρ : FamilyRepresentationConstants.RhoFam D) (constantFirstHub C : ℝ)
    (Q : MvPolynomial (Fin 3) ℕ), FamilyRepresentationConstants.CG constantFirstHub Q ≤ C → EmbeddingTypeJumps.Conclusion2 ρ L constantFirstHub Q → KillingConditions.KillAt ρ →
    TwistedPlaces.ShaFinOdd D → StarG L ρ C := by
  intro D L P ρ constantFirstHub C Q hCG hB hK hSha
  unfold StarG
  intro i hi hl π hπ
  unfold Bd
  unfold FamilyRepresentationConstants.CG at hCG
  have hC67 : constantFirstHub ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCG
  have hS : ((∑ m ∈ Q.support, Q.coeff m : ℕ) : ℝ) ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCG
  have hdeg : (Q.totalDegree : ℝ) ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCG
  have hC1 : (1 : ℝ) ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCG

  have ht1 : 1 ≤ D.R.t := D.R.t_odd.pos
  have hr1 : 1 ≤ D.R.r := by
    unfold Ranks.r
    have := D.R.m_add_three_le_k
    omega
  have hf1 : 1 ≤ D.R.f := by
    have : 0 < D.R.f := by unfold Ranks.f Ranks.n; positivity
    omega
  have htr : 1 ≤ D.R.t * D.R.r := by simpa using Nat.mul_le_mul ht1 hr1

  have hlp : (D.nd.l i).Prime := by
    rcases hl with h | h <;> rw [h]
    exacts [D.host.hyp.1, D.host.hyp.2.1]
  have hl2 : 2 < D.nd.l i := by
    have hqd := D.host.qd_big
    rcases hl with h | h <;> rw [h] <;> nlinarith [hqd.1, hqd.2]
  have hodd : Odd (D.nd.l i) := hlp.odd_of_ne_two (by omega)
  have hlbig : L.sc.x ^ (2 * L.Ct + 5) < (D.nd.l i : ℝ) := by
    rcases hl with h | h <;> rw [h]
    exacts [P.qd_pow.1, P.qd_pow.2]
  have hsha : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤ := by
    intro e he
    rw [Finset.mem_Ioo] at he
    haveI : Fact (D.nd.l i).Prime := ⟨hlp⟩
    exact lt_top_iff_ne_top.2 (hSha (D.nd.l i) e he.1 he.2)
  have hK' := (hK i hi).1 π hπ
  have h := hB i hl hi hlbig π hπ hK'.1 hsha

  have hVV : TwistedPlaces.VVr D (D.nd.l i) =
      ((∑ e ∈ Finset.Ioo 0 D.R.t, D.what₂.shaLen (D.nd.l i) e : ℚ) : ℝ) := by
    show ((∑ e ∈ Finset.Ico 1 D.R.t, D.what₂.shaLen (D.nd.l i) e : ℚ) : ℝ) = _
    congr 2
  have hvh : TwistedPlaces.vhE D (D.nd.l i) = (padicValNat (D.nd.l i) (hE D.host) : ℝ) := rfl
  have heps : TwistedPlaces.epsL (D.nd.l i) = EmbeddingTypeJumps.epsL (D.nd.l i) := by
    unfold TwistedPlaces.epsL EmbeddingTypeJumps.epsL
    rw [one_div]

  have hLpos : 0 < TwistedPlaces.large₂ L := Real.rpow_pos_of_pos (by linarith [L.sc.one_lt_alt]) _
  have hlog : Real.log L.sc.b = TwistedPlaces.large₂ L := Real.log_exp _
  have hbpos : 0 < L.sc.b := Real.exp_pos _
  have hlpos : (0 : ℝ) < D.nd.l i := by exact_mod_cast hlp.pos
  have hbr : 0 ≤ (D.R.r : ℝ) * (L.sc.b / (D.nd.l i) + L.Sc + D.R.t + L.etaSz + TwistedPlaces.large₂ L) +
      D.R.m * L.sc.b := by
    have h1 := L.Sc_pos
    have h2 := L.etaSz_pos
    have h3 : 0 ≤ L.sc.b / (D.nd.l i) := div_nonneg hbpos.le hlpos.le
    have h4 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    have h5 : 0 ≤ L.sc.b / (D.nd.l i) + L.Sc + D.R.t + L.etaSz + TwistedPlaces.large₂ L := by linarith
    positivity
  have hM1 : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * D.R.t := by exact_mod_cast Nat.mul_le_mul (Nat.mul_le_mul hf1 hr1) ht1
  have hpoly : ((EmbeddingTypeJumps.polyVal Q D.R.f D.R.r D.R.t : ℕ) : ℝ) ≤ C * ((D.R.f : ℝ) * D.R.r * D.R.t) ^ C := by
    have h1 : ((EmbeddingTypeJumps.polyVal Q D.R.f D.R.r D.R.t : ℕ) : ℝ) ≤
        ((∑ m ∈ Q.support, Q.coeff m : ℕ) : ℝ) * ((D.R.f : ℝ) * D.R.r * D.R.t) ^ Q.totalDegree := by
      exact_mod_cast polyVal_le_sum_mul_pow Q _ _ _ hf1 hr1 ht1
    have hpow : ((D.R.f : ℝ) * D.R.r * D.R.t) ^ Q.totalDegree ≤ ((D.R.f : ℝ) * D.R.r * D.R.t) ^ C := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hM1 hdeg
    exact h1.trans (mul_le_mul hS hpow (by positivity) (by linarith))
  have hbnd : EmbeddingTypeJumps.bndB D L constantFirstHub Q (D.nd.l i) ≤ TwistedPlaces.midG L C (D.nd.l i) := by
    unfold EmbeddingTypeJumps.bndB TwistedPlaces.midG
    rw [hlog]
    have e1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC67 (Nat.cast_nonneg D.R.f)) hbr
    have e2 := mul_le_mul_of_nonneg_right hpoly hLpos.le
    linarith
  rw [hVV, hvh, heps]
  linarith

end GlobalTheory.NLink

end
