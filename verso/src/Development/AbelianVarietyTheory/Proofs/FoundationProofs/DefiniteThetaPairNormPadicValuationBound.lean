import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryRationalConjIntersectionCardDvdInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresentaStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationDenominatorsAndHostFieldSizesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBoundStatement

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormVal

def Bd (p : ℕ) [Fact p.Prime] (r : ℝ) (x : ℂ) : Prop :=
  x ∈ Qbar ∧ ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam x‖ ≤ r

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Unfold `lamC`. Rewrite using `[dif_pos h]`.
-/
lemma lamC_of_mem (lam : Qbar →+* ℂ_[p]) {x : ℂ} (h : x ∈ Qbar) : lamC lam x = lam ⟨x, h⟩ := by
  unfold lamC
  rw [dif_pos h]

/- English proof (translation)
Use `⟨zero_mem _, fun lam => ?_⟩` and prove the remaining obligations. Rewrite using `[lamC_of_mem lam (zero_mem _)]`. Establish `: (⟨0, zero_mem _⟩ : Qbar) = 0` using `rfl`. Rewrite using `[this, map_zero, norm_zero]`. Conclude with `hr`.
-/
lemma Bd.zero {r : ℝ} (hr : 0 ≤ r) : Bd p r 0 := by
  refine ⟨zero_mem _, fun lam => ?_⟩
  rw [lamC_of_mem lam (zero_mem _)]
  have : (⟨0, zero_mem _⟩ : Qbar) = 0 := rfl
  rw [this, map_zero, norm_zero]
  exact hr

/- English proof (translation)
Use `⟨add_mem hx.1 hy.1, fun lam => ?_⟩` and prove the remaining obligations. Establish `h1` using `hx.2 lam`. Establish `h2` using `hy.2 lam`. Rewrite `h1` using `[lamC_of_mem lam hx.1]`. Rewrite `h2` using `[lamC_of_mem lam hy.1]`.

Rewrite using `[lamC_of_mem lam (add_mem hx.1 hy.1)]`. Establish `: (⟨x + y, add_mem hx.1 hy.1⟩ : Qbar) = ⟨x, hx.1⟩ + ⟨y, hy.1⟩` using `rfl`. Rewrite using `[this, map_add]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)`.
-/
lemma Bd.add {r : ℝ} {x y : ℂ} (hx : Bd p r x) (hy : Bd p r y) : Bd p r (x + y) := by
  refine ⟨add_mem hx.1 hy.1, fun lam => ?_⟩
  have h1 := hx.2 lam
  have h2 := hy.2 lam
  rw [lamC_of_mem lam hx.1] at h1
  rw [lamC_of_mem lam hy.1] at h2
  rw [lamC_of_mem lam (add_mem hx.1 hy.1)]
  have : (⟨x + y, add_mem hx.1 hy.1⟩ : Qbar) = ⟨x, hx.1⟩ + ⟨y, hy.1⟩ := rfl
  rw [this, map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)

/- English proof (translation)
Use `⟨mul_mem hx.1 hy.1, fun lam => ?_⟩` and prove the remaining obligations. Establish `h1` using `hx.2 lam`. Establish `h2` using `hy.2 lam`. Rewrite `h1` using `[lamC_of_mem lam hx.1]`. Rewrite `h2` using `[lamC_of_mem lam hy.1]`.

Rewrite using `[lamC_of_mem lam (mul_mem hx.1 hy.1)]`. Establish `: (⟨x * y, mul_mem hx.1 hy.1⟩ : Qbar) = ⟨x, hx.1⟩ * ⟨y, hy.1⟩` using `rfl`. Rewrite using `[this, map_mul, norm_mul]`. Conclude with `mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)`.
-/
lemma Bd.mul {r s : ℝ} {x y : ℂ} (hx : Bd p r x) (hy : Bd p s y) : Bd p (r * s) (x * y) := by
  refine ⟨mul_mem hx.1 hy.1, fun lam => ?_⟩
  have h1 := hx.2 lam
  have h2 := hy.2 lam
  rw [lamC_of_mem lam hx.1] at h1
  rw [lamC_of_mem lam hy.1] at h2
  rw [lamC_of_mem lam (mul_mem hx.1 hy.1)]
  have : (⟨x * y, mul_mem hx.1 hy.1⟩ : Qbar) = ⟨x, hx.1⟩ * ⟨y, hy.1⟩ := rfl
  rw [this, map_mul, norm_mul]
  exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)

/- English proof (translation)
Assemble the required witnesses or components as `⟨hx.1, fun lam => (hx.2 lam).trans h⟩`.
-/
lemma Bd.mono {r s : ℝ} {x : ℂ} (hx : Bd p r x) (h : r ≤ s) : Bd p s x :=
  ⟨hx.1, fun lam => (hx.2 lam).trans h⟩

/- English proof (translation)
Rewrite `hx`, the goal using `[mem_algebraicClosure_iff]`. Conclude with `hx.algHom ((starRingEnd ℂ).toRatAlgHom)`.
-/
lemma conj_mem {x : ℂ} (hx : x ∈ Qbar) : (starRingEnd ℂ) x ∈ Qbar := by
  rw [mem_algebraicClosure_iff] at hx ⊢
  exact hx.algHom ((starRingEnd ℂ).toRatAlgHom)

noncomputable def conjQ : Qbar →+* Qbar :=
  ((starRingEnd ℂ).comp (algebraMap Qbar ℂ)).codRestrict Qbar (fun x => conj_mem x.2)

/- English proof (translation)
Use `⟨conj_mem hx.1, fun lam => ?_⟩` and prove the remaining obligations. Establish `h1` using `hx.2 (lam.comp conjQ)`. Rewrite `h1` using `[lamC_of_mem _ hx.1]`. Rewrite using `[lamC_of_mem lam (conj_mem hx.1)]`. Conclude with `h1`.
-/
lemma Bd.conj {r : ℝ} {x : ℂ} (hx : Bd p r x) : Bd p r ((starRingEnd ℂ) x) := by
  refine ⟨conj_mem hx.1, fun lam => ?_⟩
  have h1 := hx.2 (lam.comp conjQ)
  rw [lamC_of_mem _ hx.1] at h1
  rw [lamC_of_mem lam (conj_mem hx.1)]
  exact h1

/- English proof (translation)
Establish `hn : n ≠ 0` using `fun h0 => hM (by simpa [h0] using h)`. Establish `hm : (n : ℂ)⁻¹ ∈ Qbar` using `inv_mem (natCast_mem _ n)`. Use `⟨hm, fun lam => ?_⟩` and prove the remaining obligations. Rewrite using `[lamC_of_mem lam hm]`. Establish `: (⟨(n : ℂ)⁻¹, hm⟩ : Qbar) = (n : Qbar)⁻¹`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Rewrite using `[this, map_inv₀, map_natCast, norm_inv]`. Establish `h2 : ‖(n : ℂ_[p])‖ = ‖(n : ℚ_[p])‖`. Rewrite using `[← map_natCast (algebraMap ℚ_[p] ℂ_[p]) n, norm_algebraMap']`.

Establish `hn' : (n : ℚ_[p]) ≠ 0` using `by exact_mod_cast hn`. Rewrite using `[h2, Padic.norm_eq_zpow_neg_valuation hn', Padic.valuation_natCast, zpow_neg, inv_inv, zpow_natCast, Real.rpow_natCast]`. Establish `hp : (1 : ℝ) ≤ p` using `by exact_mod_cast (Fact.out : p.Prime).one_le`. Apply `pow_le_pow_right₀ hp` to reduce the goal to its premises. Rewrite using `[← padicValNat_dvd_iff_le hM]`.

Conclude with `pow_padicValNat_dvd.trans h`.
-/
lemma Bd.inv_nat {n M : ℕ} (hM : M ≠ 0) (h : n ∣ M) :
    Bd p ((p : ℝ) ^ (padicValNat p M : ℝ)) ((n : ℂ)⁻¹) := by
  have hn : n ≠ 0 := fun h0 => hM (by simpa [h0] using h)
  have hm : (n : ℂ)⁻¹ ∈ Qbar := inv_mem (natCast_mem _ n)
  refine ⟨hm, fun lam => ?_⟩
  rw [lamC_of_mem lam hm]
  have : (⟨(n : ℂ)⁻¹, hm⟩ : Qbar) = (n : Qbar)⁻¹ := by
    apply Subtype.ext
    simp
  rw [this, map_inv₀, map_natCast, norm_inv]
  have h2 : ‖(n : ℂ_[p])‖ = ‖(n : ℚ_[p])‖ := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]) n, norm_algebraMap']
  have hn' : (n : ℚ_[p]) ≠ 0 := by exact_mod_cast hn
  rw [h2, Padic.norm_eq_zpow_neg_valuation hn', Padic.valuation_natCast, zpow_neg, inv_inv,
    zpow_natCast, Real.rpow_natCast]
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  apply pow_le_pow_right₀ hp
  rw [← padicValNat_dvd_iff_le hM]
  exact pow_padicValNat_dvd.trans h

/- English proof (translation)
Establish `h1 : f * r ≤ f * (2 * N)` using `Nat.mul_le_mul_left _ h`. Apply `mul_dvd_mul` to reduce the goal to its premises. Apply `pow_dvd_pow` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Apply `Nat.factorial_dvd_factorial` to reduce the goal to its premises.

Use the polynomial consequences of the given equalities and inequalities.
-/
lemma order_dvd {f r N : ℕ} (h : r ≤ 2 * N) :
    8 ^ (2 * f * r) * (2 * (2 * f * r)).factorial ∣ 8 ^ (4 * f * N) * (8 * f * N).factorial := by
  have h1 : f * r ≤ f * (2 * N) := Nat.mul_le_mul_left _ h
  apply mul_dvd_mul
  · apply pow_dvd_pow
    nlinarith
  · apply Nat.factorial_dvd_factorial
    nlinarith

/- English proof (translation)
Introduce `D hI S dl hL δ t0 Q hC hT hQ P N B hS p _ lam`. Use `set M : ℕ := 8 ^ (4 * fF D * N) * (8 * fF D * N).factorial with hMdef`. Establish `hM : M ≠ 0` using `by positivity`. Use `set c : ℝ := dl p + (if p = D.host.d then 1 / 4 else 0) + (padicValNat p Q : ℝ) with hc`. Use `set v : ℝ := (padicValNat p M : ℝ) with hv`.

Use `set w : ℝ := (padicValNat p Q : ℝ) with hw`. Establish `hw0 : 0 ≤ w` using `Nat.cast_nonneg _`. Establish `hv0 : 0 ≤ v` using `Nat.cast_nonneg _`. Establish `hc0 : 0 ≤ c`. Use `hL.2.1 p` as an intermediate fact.

Apply the tactic sequence `have h2 : (0 : ℝ) ≤ (if p = D.host.d then 1 / 4 else 0) := by split_ifs <;> norm_num`. Rewrite using `[hc]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hp1 : (1 : ℝ) ≤ p` using `by exact_mod_cast (Fact.out : p.Prime).one_le`. Establish `hp0 : (0 : ℝ) < p` using `by linarith`.

Use `set e : ℝ := ((P.a * ∑ τ, P.n τ : ℕ) : ℝ) * c + ((P.a * P.d : ℕ) : ℝ) * w with he`. Establish `he0 : 0 ≤ e` using `by positivity`. Establish `ha : P.a ≤ 2 * N` using `P.a_le.trans hS.1`. Establish `heE : e ≤ 4 * fF D * N * B * c + 4 * (N : ℝ) ^ 2 * w`. Establish `hcard` using `(GlobalTheory.T.derivationDenominators_and_hostField_sizes D hI.g1).2.2.2.2.1`.

Establish `h1 : ((∑ τ, P.n τ : ℕ) : ℝ) ≤ fF D * (2 * B)`. Rewrite using `[Nat.cast_sum, ← hcard]`. Use `Finset.sum_le_card_nsmul Finset.univ (fun τ => (P.n τ : ℝ)) (2 * B) (fun τ _ => hS.2 τ)` as an intermediate fact. Simplify using `using this`. Establish `haR : (P.a : ℝ) ≤ 2 * N` using `by exact_mod_cast ha`.

Establish `hdR : (P.d : ℝ) ≤ 2 * N` using `by exact_mod_cast hS.1`. Establish `h2 : ((P.a * ∑ τ, P.n τ : ℕ) : ℝ) ≤ 4 * fF D * N * B`. Rewrite using `[Nat.cast_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `h3 : ((P.a * P.d : ℕ) : ℝ) ≤ 4 * (N : ℝ) ^ 2`.

Rewrite using `[Nat.cast_mul]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `add_le_add (mul_le_mul_of_nonneg_right h2 hc0) (mul_le_mul_of_nonneg_right h3 hw0)`. Take `⟨hterm, hsq, -⟩` from `GlobalTheory.T.definiteThetaPair_terms_norms_independent_representatives D hI ⊤ δ t0 Q hC hT P hQ.1`. Establish `hgam : ∀ (r : ℕ), r ≤ 2 * N → ∀ (J : Subgroup (GA D r)), J ≤ intG D r → ∀ g, Bd p ((p : ℝ) ^ v) ((gam D J g : ℂ)⁻¹)` using `fun r hr J hJ g => Bd.inv_nat hM ((GlobalTheory.T.unitaryRationalConjIntersectionCard_dvd_invariant D r J hJ g).2.1.trans (order_dvd hr))`.

Establish `hcoord : ∀ (h k' : GA D P.d), k' ∈ intG D P.d → TrivAt D p ((h * k' : GA D P.d) : GL (Fin P.d) (AE D)) → ∀ T, Bd p ((p : ℝ) ^ v * (p : ℝ) ^ e) (P.coord h T)`. Introduce `h k' hk' htr T`. Unfold `Pair.coord`. Use `finsum_induction (Bd p ((p : ℝ) ^ v * (p : ℝ) ^ e)) (Bd.zero (by positivity)) (fun x y => Bd.add) (fun x => ?_)` and prove the remaining obligations. Use `Bd.mul (hgam _ ha _ le_rfl _) ?_` and prove the remaining obligations.

Take `⟨γ, k, γ', h1, h2, h3⟩` from `hI.rep P.a p Fact.out x.out`. Rewrite using `[← hterm γ (Subgroup.subset_closure ⟨γ', h1⟩) k (Subgroup.subset_closure h2)]`. Conclude with `⟨(GlobalTheory.T.padicValuation_thetaKernelJet_bound D hI S dl hL δ t0 Q hC hT hQ P p lam _ h k' hk' h3 htr T).1, fun lam' => (GlobalTheory.T.padicValuation_thetaKernelJet_bound D hI S dl hL δ t0 Q hC hT hQ P p lam' _ h k' hk' h3 htr T).2⟩`. Establish `hsqb : ∀ h : GA D P.d, Bd p (((p : ℝ) ^ v * (p : ℝ) ^ e) * ((p : ℝ) ^ v * (p : ℝ) ^ e)) ((P.sq h : ℝ) : ℂ)`. Introduce `h`.

Take `⟨γ, k, γ', h1, h2, h3⟩` from `hI.rep P.d p Fact.out h`. Rewrite using `[← hsq γ (Subgroup.subset_closure ⟨γ', h1⟩) 1 (one_mem _) h, mul_one]`. Unfold `Pair.sq`. Rewrite using `[Complex.ofReal_sum]`. Use `Finset.sum_induction _ _ (fun x y => Bd.add) (Bd.zero (by positivity)) (fun T _ => ?_)` and prove the remaining obligations.

Establish `hb` using `hcoord (γ * h) k (Subgroup.subset_closure h2) h3 T`. Rewrite using `[Complex.ofReal_pow, ← Complex.mul_conj']`. Conclude with `hb.mul hb.conj`. Establish `hfin : Bd p ((p : ℝ) ^ v * (((p : ℝ) ^ v * (p : ℝ) ^ e) * ((p : ℝ) ^ v * (p : ℝ) ^ e))) ((P.norm : ℝ) : ℂ)`. Unfold `Pair.norm`.

Use `finsum_induction (fun x : ℝ => Bd p ((p : ℝ) ^ v * (((p : ℝ) ^ v * (p : ℝ) ^ e) * ((p : ℝ) ^ v * (p : ℝ) ^ e))) (x : ℂ)) ?_ (fun x y hx hy => ?_) (fun x => ?_)` and prove the remaining obligations. Rewrite using `[Complex.ofReal_zero]`. Conclude with `Bd.zero (by positivity)`. Rewrite using `[Complex.ofReal_add]`. Conclude with `hx.add hy`.

Rewrite using `[Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]`. Conclude with `(hgam _ hS.1 _ P.J_le _).mul (hsqb _)`. Use `⟨hfin.1, (hfin.2 lam).trans ?_⟩` and prove the remaining obligations. Rewrite using `[← Real.rpow_add hp0, ← Real.rpow_add hp0, ← Real.rpow_add hp0]`. Apply `Real.rpow_le_rpow_of_exponent_le hp1` to reduce the goal to its premises.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_mem_and_le : ∀ (D : D7), Inp D → ∀ (S : Finset ℕ) (dl : ℕ → ℝ), Letters D S dl → ∀ (δ t0 : ℂ) (Q : ℕ), Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → GoodLevel D Q → ∀ (P : Pair D ⊤ δ t0 Q) (N : ℕ) (B : ℝ), P.Small N B → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ((P.norm : ℝ) : ℂ) ∈ Qbar ∧ ‖lamC lam ((P.norm : ℝ) : ℂ)‖ ≤ (p : ℝ) ^ (3 * ((padicValNat p (8 ^ (4 * fF D * N) * (8 * fF D * N).factorial) : ℝ) + 4 * fF D * N * B * (dl p + (if p = D.host.d then 1 / 4 else 0) + (padicValNat p Q : ℝ)) + 4 * (N : ℝ) ^ 2 * (padicValNat p Q : ℝ))) := by
  intro D hI S dl hL δ t0 Q hC hT hQ P N B hS p _ lam
  set M : ℕ := 8 ^ (4 * fF D * N) * (8 * fF D * N).factorial with hMdef
  have hM : M ≠ 0 := by positivity
  set c : ℝ := dl p + (if p = D.host.d then 1 / 4 else 0) + (padicValNat p Q : ℝ) with hc
  set v : ℝ := (padicValNat p M : ℝ) with hv
  set w : ℝ := (padicValNat p Q : ℝ) with hw
  have hw0 : 0 ≤ w := Nat.cast_nonneg _
  have hv0 : 0 ≤ v := Nat.cast_nonneg _
  have hc0 : 0 ≤ c := by
    have := hL.2.1 p
    have h2 : (0 : ℝ) ≤ (if p = D.host.d then 1 / 4 else 0) := by split_ifs <;> norm_num
    rw [hc]
    linarith
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  have hp0 : (0 : ℝ) < p := by linarith
  set e : ℝ := ((P.a * ∑ τ, P.n τ : ℕ) : ℝ) * c + ((P.a * P.d : ℕ) : ℝ) * w with he
  have he0 : 0 ≤ e := by positivity
  have ha : P.a ≤ 2 * N := P.a_le.trans hS.1
  have heE : e ≤ 4 * fF D * N * B * c + 4 * (N : ℝ) ^ 2 * w := by
    have hcard := (GlobalTheory.T.derivationDenominators_and_hostField_sizes D hI.g1).2.2.2.2.1
    have h1 : ((∑ τ, P.n τ : ℕ) : ℝ) ≤ fF D * (2 * B) := by
      rw [Nat.cast_sum, ← hcard]
      have := Finset.sum_le_card_nsmul Finset.univ (fun τ => (P.n τ : ℝ)) (2 * B)
        (fun τ _ => hS.2 τ)
      simpa using this
    have haR : (P.a : ℝ) ≤ 2 * N := by exact_mod_cast ha
    have hdR : (P.d : ℝ) ≤ 2 * N := by exact_mod_cast hS.1
    have h2 : ((P.a * ∑ τ, P.n τ : ℕ) : ℝ) ≤ 4 * fF D * N * B := by
      rw [Nat.cast_mul]
      calc (P.a : ℝ) * ((∑ τ, P.n τ : ℕ) : ℝ) ≤ (2 * N) * (fF D * (2 * B)) :=
            mul_le_mul haR h1 (Nat.cast_nonneg _) (by positivity)
        _ = _ := by ring
    have h3 : ((P.a * P.d : ℕ) : ℝ) ≤ 4 * (N : ℝ) ^ 2 := by
      rw [Nat.cast_mul]
      calc (P.a : ℝ) * (P.d : ℝ) ≤ (2 * N) * (2 * N) :=
            mul_le_mul haR hdR (Nat.cast_nonneg _) (by positivity)
        _ = _ := by ring
    exact add_le_add (mul_le_mul_of_nonneg_right h2 hc0) (mul_le_mul_of_nonneg_right h3 hw0)
  obtain ⟨hterm, hsq, -⟩ := GlobalTheory.T.definiteThetaPair_terms_norms_independent_representatives D hI ⊤ δ t0 Q hC hT P hQ.1
  have hgam : ∀ (r : ℕ), r ≤ 2 * N → ∀ (J : Subgroup (GA D r)), J ≤ intG D r → ∀ g,
      Bd p ((p : ℝ) ^ v) ((gam D J g : ℂ)⁻¹) := fun r hr J hJ g =>
    Bd.inv_nat hM ((GlobalTheory.T.unitaryRationalConjIntersectionCard_dvd_invariant D r J hJ g).2.1.trans (order_dvd hr))
  have hcoord : ∀ (h k' : GA D P.d), k' ∈ intG D P.d →
      TrivAt D p ((h * k' : GA D P.d) : GL (Fin P.d) (AE D)) → ∀ T,
      Bd p ((p : ℝ) ^ v * (p : ℝ) ^ e) (P.coord h T) := by
    intro h k' hk' htr T
    unfold Pair.coord
    refine finsum_induction (Bd p ((p : ℝ) ^ v * (p : ℝ) ^ e)) (Bd.zero (by positivity))
      (fun x y => Bd.add) (fun x => ?_)
    refine Bd.mul (hgam _ ha _ le_rfl _) ?_
    obtain ⟨γ, k, γ', h1, h2, h3⟩ := hI.rep P.a p Fact.out x.out
    rw [← hterm γ (Subgroup.subset_closure ⟨γ', h1⟩) k (Subgroup.subset_closure h2)]
    exact ⟨(GlobalTheory.T.padicValuation_thetaKernelJet_bound D hI S dl hL δ t0 Q hC hT hQ P p lam _ h k' hk' h3 htr T).1,
      fun lam' => (GlobalTheory.T.padicValuation_thetaKernelJet_bound D hI S dl hL δ t0 Q hC hT hQ P p lam' _ h k' hk' h3 htr T).2⟩
  have hsqb : ∀ h : GA D P.d,
      Bd p (((p : ℝ) ^ v * (p : ℝ) ^ e) * ((p : ℝ) ^ v * (p : ℝ) ^ e)) ((P.sq h : ℝ) : ℂ) := by
    intro h
    obtain ⟨γ, k, γ', h1, h2, h3⟩ := hI.rep P.d p Fact.out h
    rw [← hsq γ (Subgroup.subset_closure ⟨γ', h1⟩) 1 (one_mem _) h, mul_one]
    unfold Pair.sq
    rw [Complex.ofReal_sum]
    refine Finset.sum_induction _ _ (fun x y => Bd.add) (Bd.zero (by positivity)) (fun T _ => ?_)
    have hb := hcoord (γ * h) k (Subgroup.subset_closure h2) h3 T
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    exact hb.mul hb.conj
  have hfin : Bd p ((p : ℝ) ^ v * (((p : ℝ) ^ v * (p : ℝ) ^ e) * ((p : ℝ) ^ v * (p : ℝ) ^ e)))
      ((P.norm : ℝ) : ℂ) := by
    unfold Pair.norm
    refine finsum_induction (fun x : ℝ => Bd p ((p : ℝ) ^ v * (((p : ℝ) ^ v * (p : ℝ) ^ e) *
      ((p : ℝ) ^ v * (p : ℝ) ^ e))) (x : ℂ)) ?_ (fun x y hx hy => ?_) (fun x => ?_)
    · rw [Complex.ofReal_zero]
      exact Bd.zero (by positivity)
    · rw [Complex.ofReal_add]
      exact hx.add hy
    · rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
      exact (hgam _ hS.1 _ P.J_le _).mul (hsqb _)
  refine ⟨hfin.1, (hfin.2 lam).trans ?_⟩
  rw [← Real.rpow_add hp0, ← Real.rpow_add hp0, ← Real.rpow_add hp0]
  apply Real.rpow_le_rpow_of_exponent_le hp1
  linarith

end GlobalTheory.NormVal
