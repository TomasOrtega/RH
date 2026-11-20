import Formalism.LocalToGlobal.ExponentGrids.ScaledCoordinatesValuationLemma
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneqMean
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DualPl
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu
import Formalism.SizeWindowBrackets.ChainSlopeWindows.TruncatedLatticeHolds
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.KappaNormalise
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondComplementParameterBounds
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ProdFormula
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Formalism.PairingDivisors.PairingDivisorProofs.Height
import Formalism.PairingDivisors.PairingDivisorProofs.SumValuationNat
import Formalism.PairingDivisors.PairingDivisorProofs.ValAdd
import Formalism.TowerValuationBounds.TowerValuationProofs.SumAdditiveCharacterEqZero
import Lemmata.PlaneOverMembership.PlOverOfMem

open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw PlOver meanLog)
open Formalism.PairingDivisionLocalBalance (Pl wt HtLe meanInf)
open Formalism.HN (muMaxDef muMinDef htMap dualLat dualFrame)

noncomputable section

namespace Formalism.AtG

/- English proof (translation)
Establish `hc : ((g : 𝓞 K) : K) = (g : K)` using `by simp`. Establish `hg0 : (g : 𝓞 K) ≠ 0` using `by exact_mod_cast hg.ne'`. Establish `hJ : (Ideal.span {(g : 𝓞 K)} : Ideal (𝓞 K)) ≠ 0`. Rewrite using `[ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]` and apply the resulting hypothesis. Establish `hm : Associates.mk (Ideal.span {(g : 𝓞 K)}) ≠ 0` using `by rwa [ne_eq, Associates.mk_eq_zero]`.

Establish `h1 : 1 ≤ (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {(g : 𝓞 K)})).factors`. Rewrite using `[← Associates.prime_pow_dvd_iff_le hm w.associates_irreducible, pow_one, Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`. Conclude with `h`. Unfold `Formalism.DivisionValues.PlOver Formalism.DivisionValues.vw`. Rewrite using `[← hc, ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K _ hJ]`.

Establish `h2 : 0 < (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {(g : 𝓞 K)})).factors` using `h1`. Conclude with `h2` after adjusting the coercions.
-/
theorem plOver_of_mem {K : Type} [Field K] [NumberField K] {g : ℕ} (hg : 0 < g) (w : Pl K)
    (h : (g : 𝓞 K) ∈ w.asIdeal) : PlOver g w := by
  classical
  have hc : ((g : 𝓞 K) : K) = (g : K) := by simp
  have hg0 : (g : 𝓞 K) ≠ 0 := by exact_mod_cast hg.ne'
  have hJ : (Ideal.span {(g : 𝓞 K)} : Ideal (𝓞 K)) ≠ 0 := by
    rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  have hm : Associates.mk (Ideal.span {(g : 𝓞 K)}) ≠ 0 := by rwa [ne_eq, Associates.mk_eq_zero]
  have h1 : 1 ≤ (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {(g : 𝓞 K)})).factors := by
    rw [← Associates.prime_pow_dvd_iff_le hm w.associates_irreducible, pow_one,
      Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact h
  unfold Formalism.DivisionValues.PlOver Formalism.DivisionValues.vw
  rw [← hc, ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K _ hJ]
  have h2 : 0 < (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {(g : 𝓞 K)})).factors := h1
  exact_mod_cast h2

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.PlaneOverMembership.goal1 .. | (apply Bl.PlaneOverMembership.goal1 <;> assumption) | (intros; apply Bl.PlaneOverMembership.goal1 <;> assumption) | (apply @Bl.PlaneOverMembership.goal1 <;> assumption) | (intros; apply @Bl.PlaneOverMembership.goal1 <;> assumption) …`.
-/
theorem grid_ell_bound : FinitePlaceLiesOverPrime := by
  first | exact Bl.PlaneOverMembership.goal1 .. | (apply Bl.PlaneOverMembership.goal1 <;> assumption) | (intros; apply Bl.PlaneOverMembership.goal1 <;> assumption) | (apply @Bl.PlaneOverMembership.goal1 <;> assumption) | (intros; apply @Bl.PlaneOverMembership.goal1 <;> assumption) | (apply @Bl.PlaneOverMembership.goal1 <;> first | assumption | infer_instance)

/- English proof (translation)
Rewrite using `[finsum_eq_sum_of_support_subset f (s := hs.toFinset ∪ F) (by`. Introduce `x hx`. Simplify using `only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Set.Finite.mem_toFinset]`. Conclude with `Or.inl hx)]`. Conclude with `Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right (fun a _ _ => hf a)`.
-/
theorem sum_le_finsum' {α : Type} (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) (hs : (Function.support f).Finite)
    (F : Finset α) : ∑ a ∈ F, f a ≤ ∑ᶠ a, f a := by
  classical
  rw [finsum_eq_sum_of_support_subset f (s := hs.toFinset ∪ F) (by
    intro x hx
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Set.Finite.mem_toFinset]
    exact Or.inl hx)]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right (fun a _ _ => hf a)

/- English proof (translation)
Take `⟨h1, h2⟩` from `Formalism.PairingDivisionLocalBalance.sum_valuation_nat K n`. Rewrite using `[← h2]`. Conclude with `sum_le_finsum' _ (fun w => mul_nonneg (Formalism.PairingDivisionLocalBalance.lw_nonneg w) (by exact_mod_cast Formalism.PairingDivisionLocalBalance.vw_natCast_nonneg w n)) h1 F`.
-/
theorem partial_nat (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (n : ℕ)
    (F : Finset (Pl K)) : ∑ w ∈ F, lw w * (vw w (n : K) : ℝ) ≤ Real.log n := by
  obtain ⟨h1, h2⟩ := Formalism.PairingDivisionLocalBalance.sum_valuation_nat K n
  rw [← h2]
  exact sum_le_finsum' _ (fun w => mul_nonneg (Formalism.PairingDivisionLocalBalance.lw_nonneg w)
    (by exact_mod_cast Formalism.PairingDivisionLocalBalance.vw_natCast_nonneg w n)) h1 F

/- English proof (translation)
The claim follows from `(sum_le_finsum' _ (fun w => mul_nonneg (Formalism.PairingDivisionLocalBalance.lw_nonneg w) (abs_nonneg _)) h.1 F).trans h.2`.
-/
theorem partial_ht {K : Type} [Field K] [NumberField K] [StarRing K] {g : Pl K → ℤ} {z : K} {B : ℝ}
    (h : HtLe g z B) (F : Finset (Pl K)) :
    ∑ w ∈ F, lw w * |((vw w z + g w : ℤ) : ℝ)| ≤ B :=
  (sum_le_finsum' _ (fun w => mul_nonneg (Formalism.PairingDivisionLocalBalance.lw_nonneg w) (abs_nonneg _)) h.1 F).trans h.2

/- English proof (translation)
Introduce `K _ _ _ ell hell S c hS w`. Establish `hz : ∀ l ∈ S, l ≠ ell w → (vw w (l : K) : ℝ) = 0`. Introduce `l hl hne`. Establish `hco : Nat.Coprime l (ell w)` using `(Nat.coprime_primes (hS l hl) (hell w).1).2 hne`. Establish `h1` using `Formalism.DivisionValues.places_over_coprime K l (ell w) hco w`.

Establish `h2 : ¬ PlOver l w` using `fun h => h1 ⟨h, (hell w).2⟩`. Establish `h3` using `Formalism.PairingDivisionLocalBalance.vw_natCast_nonneg w l`. Unfold `Formalism.DivisionValues.PlOver at h2`. Establish `: vw w (l : K) = 0` using `by omega`. Conclude with `this` after adjusting the coercions.

Unfold `Formalism.PairingDivisionLocalBalance.wt`. Distinguish the cases in `h : ell w ∈ S`. Rewrite using `[if_pos h, Finset.sum_eq_single_of_mem (ell w) h]`. Introduce `l hl hne`. Rewrite using `[hz l hl hne, mul_zero]`.

Rewrite using `[if_neg h, zero_mul]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `l hl`. Rewrite using `[hz l hl (fun e => h (e ▸ hl)), mul_zero]`.
-/
theorem j3Wt : NormalisedPrimeUnitWeight := by
  intro K _ _ _ ell hell S c hS w
  classical
  have hz : ∀ l ∈ S, l ≠ ell w → (vw w (l : K) : ℝ) = 0 := by
    intro l hl hne
    have hco : Nat.Coprime l (ell w) := (Nat.coprime_primes (hS l hl) (hell w).1).2 hne
    have h1 := Formalism.DivisionValues.places_over_coprime K l (ell w) hco w
    have h2 : ¬ PlOver l w := fun h => h1 ⟨h, (hell w).2⟩
    have h3 := Formalism.PairingDivisionLocalBalance.vw_natCast_nonneg w l
    unfold Formalism.DivisionValues.PlOver at h2
    have : vw w (l : K) = 0 := by omega
    exact_mod_cast this
  unfold Formalism.PairingDivisionLocalBalance.wt
  by_cases h : ell w ∈ S
  · rw [if_pos h, Finset.sum_eq_single_of_mem (ell w) h]
    intro l hl hne
    rw [hz l hl hne, mul_zero]
  · rw [if_neg h, zero_mul]
    apply Finset.sum_eq_zero
    intro l hl
    rw [hz l hl (fun e => h (e ▸ hl)), mul_zero]

/- English proof (translation)
Introduce `K _ _ _ _ x dl Bδ hx hdl hden hB`. Take `⟨hfin, hpf⟩` from `Formalism.DivisionValues.prod_formula' K x hx`. Establish `hc : (Fintype.card (InfinitePlace K) : ℝ) * 2 = (finrank ℚ K : ℝ)`. Establish `h3` using `IsTotallyComplex.finrank K`. Establish `h4` using `InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K`.

Establish `h5` using `IsTotallyComplex.nrRealPlaces_eq_zero K`. Rewrite using `[h3, h4, h5]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hpos : (0 : ℝ) < finrank ℚ K` using `by exact_mod_cast finrank_pos`.

Establish `hcard : (Fintype.card (InfinitePlace K) : ℝ) ≠ 0`. Introduce `h0`. Rewrite `hc` using `[h0, zero_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmean : ∀ φ : InfinitePlace K → ℝ, (2 / (finrank ℚ K : ℝ)) * ∑ v, φ v = (∑ v, φ v) / Fintype.card (InfinitePlace K)`.

Introduce `φ`. Rewrite using `[← hc]`. Clear the denominators using the available nonvanishing facts. Establish `hsupp : ∀ w, w ∉ hfin.toFinset → ((vw w x : ℤ) : ℝ) = 0`. Introduce `w hw`.

Establish `h0 : lw w * (vw w x : ℝ) = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hw (hfin.mem_toFinset.2 hne)`. Break down `mul_eq_zero.1 h0 with h | h` into its components or cases. Conclude with `absurd h (Formalism.DivisionValues.PlaceSumConjugation.lw_pos w).ne'`.

Conclude with `h`. Establish `hsum : ∑ w ∈ hfin.toFinset, lw w * (vw w x : ℝ) = (∑ v : InfinitePlace K, Real.log ‖v.embedding x‖) / Fintype.card (InfinitePlace K)`. Rewrite using `[← hmean, hpf, finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by simp)]`. Take `⟨_, _, h3⟩` from `Formalism.ValuationGridEstimates.height_bound_alt (Pl K) (InfinitePlace K) (fun w => lw w) (fun w => (vw w x : ℝ)) dl (fun v => ‖v.embedding x‖) hfin.toFinset Bδ (fun w => Formalism.PairingDivisionLocalBalance.lw_nonneg w) hsupp hsum`. Establish `h4` using `h3 hdl hden hB hfin.toFinset`.

Establish `hsub : (Function.support fun w : Pl K => lw w * |((vw w x + 0 : ℤ) : ℝ)|) ⊆ (hfin.toFinset : Set (Pl K))`. Introduce `w hw`. Assume the negation of the conclusion as `hne`. Apply `hw` to reduce the goal to its premises. Use `hsupp w hne` as an intermediate fact.

Simplify using `only [add_zero]`. Rewrite using `[this, abs_zero, mul_zero]`. Use `⟨(hfin.toFinset.finite_toSet).subset hsub, ?_⟩` and prove the remaining obligations. Rewrite using `[finsum_eq_sum_of_support_subset _ hsub]`. Unfold `Formalism.PairingDivisionLocalBalance.meanInf`.

Rewrite using `[hmean]`. Simplify `h4` using `only [add_zero]`.
-/
theorem norm_height_bound : DisjointUnionFactorProduct := by
  intro K _ _ _ _ x dl Bδ hx hdl hden hB
  classical
  obtain ⟨hfin, hpf⟩ := Formalism.DivisionValues.prod_formula' K x hx
  have hc : (Fintype.card (InfinitePlace K) : ℝ) * 2 = (finrank ℚ K : ℝ) := by
    have h3 := IsTotallyComplex.finrank K
    have h4 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
    have h5 := IsTotallyComplex.nrRealPlaces_eq_zero K
    rw [h3, h4, h5]; push_cast; ring
  have hpos : (0 : ℝ) < finrank ℚ K := by exact_mod_cast finrank_pos
  have hcard : (Fintype.card (InfinitePlace K) : ℝ) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hc; linarith
  have hmean : ∀ φ : InfinitePlace K → ℝ,
      (2 / (finrank ℚ K : ℝ)) * ∑ v, φ v = (∑ v, φ v) / Fintype.card (InfinitePlace K) := by
    intro φ
    rw [← hc]
    field_simp
  have hsupp : ∀ w, w ∉ hfin.toFinset → ((vw w x : ℤ) : ℝ) = 0 := by
    intro w hw
    have h0 : lw w * (vw w x : ℝ) = 0 := by
      by_contra hne
      exact hw (hfin.mem_toFinset.2 hne)
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h (Formalism.DivisionValues.PlaceSumConjugation.lw_pos w).ne'
    · exact h
  have hsum : ∑ w ∈ hfin.toFinset, lw w * (vw w x : ℝ) =
      (∑ v : InfinitePlace K, Real.log ‖v.embedding x‖) / Fintype.card (InfinitePlace K) := by
    rw [← hmean, hpf, finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by simp)]
  obtain ⟨_, _, h3⟩ := Formalism.ValuationGridEstimates.height_bound_alt (Pl K) (InfinitePlace K) (fun w => lw w)
    (fun w => (vw w x : ℝ)) dl (fun v => ‖v.embedding x‖) hfin.toFinset Bδ
    (fun w => Formalism.PairingDivisionLocalBalance.lw_nonneg w) hsupp hsum
  have h4 := h3 hdl hden hB hfin.toFinset
  have hsub : (Function.support fun w : Pl K => lw w * |((vw w x + 0 : ℤ) : ℝ)|) ⊆
      (hfin.toFinset : Set (Pl K)) := by
    intro w hw
    by_contra hne
    apply hw
    have := hsupp w hne
    simp only [add_zero]
    rw [this, abs_zero, mul_zero]
  refine ⟨(hfin.toFinset.finite_toSet).subset hsub, ?_⟩
  rw [finsum_eq_sum_of_support_subset _ hsub]
  unfold Formalism.PairingDivisionLocalBalance.meanInf
  rw [hmean]
  simpa only [add_zero] using h4

/- English proof (translation)
Introduce `K _ _ _ _ Sq m N dl S Se N0 rr zA zA' zT zTd gT ch dd hh yy S0 cc ee qq B BN0 Bδ W0 hdl hS hSe hrr hdd hddN hyy hcc hsq hA hT hTd hN0 hBδ`. Take `⟨ell, hell⟩` from `grid_ell_bound K`. Establish `he : ∀ w : Pl K, (0 : ℝ) < (vw w (ell w : K) : ℝ)`. Introduce `w`. Use `(hell w).2` as an intermediate fact.

Unfold `Formalism.DivisionValues.PlOver at this`. Conclude with `this` after adjusting the coercions. Establish `hlam : ∀ (w : Pl K) (t : ℝ), lw w * (vw w (ell w : K) : ℝ) * (t / (vw w (ell w : K) : ℝ)) = lw w * t`. Introduce `w t`. Use `(he w).ne'` as an intermediate fact.

Clear the denominators using the available nonvanishing facts. Establish `habs : ∀ (w : Pl K) (t : ℝ), |t / (vw w (ell w : K) : ℝ)| = |t| / (vw w (ell w : K) : ℝ)`. Introduce `w t`. Rewrite using `[abs_div, abs_of_pos (he w)]`. Establish `hbud : ∀ P : Finset ℕ, (∀ l ∈ P, l.Prime) → ∑ l ∈ P, (if l ∈ S then N0 l else 0) * Real.log l ≤ BN0`.

Introduce `P _`. Use `le_trans ?_ hN0` and prove the remaining obligations. Establish `h1 : ∑ l ∈ P, (if l ∈ S then N0 l else 0) * Real.log l = ∑ l ∈ P.filter (· ∈ S), N0 l * Real.log l`. Rewrite using `[Finset.sum_filter]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `l _`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[h1]`. Apply `Finset.sum_le_sum_of_subset_of_nonneg` to reduce the goal to its premises. Introduce `l hl`.

Conclude with `(Finset.mem_filter.1 hl).2`. Introduce `l hl _`. Conclude with `mul_nonneg (hS l hl).2 (Real.log_natCast_nonneg l)`. Establish `key` using `Formalism.ValuationGridEstimates.grid_squares_bound (Pl K) Sq m N (fun w => lw w * (vw w (ell w : K) : ℝ)) (fun w => dl w / (vw w (ell w : K) : ℝ)) ell (fun l => if l ∈ S then N0 l else 0) (fun w ij => (vw w (rr w ij) : ℝ) / (vw w (ell w : K) : ℝ)) (fun w ij => (vw w (zA ij) : ℝ) …`. Conclude with `(hS l h).2`.

Conclude with `le_rfl)`. Use the proof step `(fun w s => div_nonneg (by exact_mod_cast Formalism.PairingDivisionLocalBalance.vw_natCast_nonneg w (qq s)) (he w).le)`. Use the proof step `(fun w => (hell w).1)`. Use the proof step `(fun l F hF => by`. Use `le_trans (le_of_eq ?_) (partial_nat K l F)` and prove the remaining obligations.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `w hw`. Rewrite using `[hF w hw])`. Use `hdd hddN hyy hcc`. Use the proof step `(fun w hw ij => by`.

Establish `hE` using `he w`. Establish `h0` using `hsq w hw ij`. Rewrite `h0` using `[j3Wt K ell hell S N0 (fun l hl => (hS l hl).1) w, j3Wt K ell hell Se (fun l => 1 / (l : ℝ) ^ 2) hSe w]`. Simplify using `only [habs]`. Establish `hs1 : ∑ s ∈ Icc (1 : ℤ) (hh ij), (|((vw w (zT ij s) + gT ij s w : ℤ) : ℝ)| / (vw w (ell w : K) : ℝ) + |((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ)| / (vw w (ell w : K) : ℝ)) = (∑ s ∈ Icc (1 : ℤ) (hh ij), (|((vw w (zT ij s) + gT ij s w : ℤ) : ℝ)| + |((vw w (zTd ij (ch w) s) + g …`.

Rewrite using `[Finset.sum_div]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `s _`. Expand and normalize the polynomial expressions, which then agree. Establish `hs2 : ∑ s ∈ S0, (cc s : ℝ) * ((vw w (qq s : K) : ℝ) / (vw w (ell w : K) : ℝ)) = (∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ)) / (vw w (ell w : K) : ℝ)`.

Rewrite using `[Finset.sum_div]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `s _`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hs1, hs2, div_le_iff₀ hE]`.

Use `le_trans h0 ?_` and prove the remaining obligations. Generalize the expression as in `(∑ s ∈ Icc (1 : ℤ) (hh ij), (|((vw w (zT ij s) + gT ij s w : ℤ) : ℝ)| + |((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ)|)) = T1`. Generalize the expression as in `(∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ)) = T2`. Generalize the expression as in `(vw w (ell w : K) : ℝ) = E at hE ⊢`. Establish `hε : (if ell w ∈ Se then 1 / ((ell w : ℕ) : ℝ) ^ 2 else 0) ≤ (((ell w : ℕ) : ℝ) ^ 2)⁻¹` using `by split_ifs`.

Rewrite using `[one_div]`. Check the signs of the components of the expression. Establish `hdd0 : (0 : ℝ) ≤ (dd ij : ℝ)` using `Nat.cast_nonneg _`. Establish `h5 : (dd ij : ℝ) * ((if ell w ∈ Se then 1 / ((ell w : ℕ) : ℝ) ^ 2 else 0) * E) ≤ (dd ij : ℝ) * ((((ell w : ℕ) : ℝ) ^ 2)⁻¹ * E)` using `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hε hE.le) hdd0`. Establish `h6 : (|(vw w (zA ij) : ℝ)| / E + |(vw w (zA' ij) : ℝ)| / E + 4 * (T1 / E) + (dd ij : ℝ) * ((if ell w ∈ S then N0 (ell w) else 0) + (((ell w : ℕ) : ℝ) ^ 2)⁻¹) + 6 * (dl w / E) + (yy ij : ℝ) * (2 * (T2 / E))) * E = |(vw w (zA ij) : ℝ)| + |(vw w (zA' ij) : ℝ)| + 4 * T1 + (dd ij : ℝ) …`.

Use `hE.ne'` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Rewrite using `[h6]`. Use the proof step `linarith)`. Use the proof step `(fun ij F => by`.

Use `le_trans (le_of_eq ?_) (partial_ht (hA ij).1 F)` and prove the remaining obligations. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `w _`. Simplify using `only [habs, hlam, add_zero])`. Use the proof step `(fun ij F => by`.

Use `le_trans (le_of_eq ?_) (partial_ht (hA ij).2 F)` and prove the remaining obligations. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `w _`. Simplify using `only [habs, hlam, add_zero])`. Use the proof step `(fun ij s F => by`.

Use `le_trans (le_of_eq ?_) (partial_ht (hT ij s) F)` and prove the remaining obligations. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `w _`. Simplify using `only [habs, hlam])`. Use the proof step `(fun ij b s F => by`.

Use `le_trans (le_of_eq ?_) (partial_ht (hTd ij b s) F)` and prove the remaining obligations. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `w _`. Simplify using `only [habs, hlam])`. Use the proof step `(Formalism.ValuationGridEstimates.prime_budget_bound (fun l => if l ∈ S then N0 l else 0) BN0 hbud)`.

Use the proof step `(fun F => by`. Use `le_trans (le_of_eq ?_) (hBδ F)` and prove the remaining obligations. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `w _`. Simplify using `only [hlam])`.

Use the proof step `(fun s _ F => by`. Use `le_trans (le_of_eq ?_) (partial_nat K (qq s) F)` and prove the remaining obligations. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `w _`. Simplify using `only [hlam])`.

Unfold `gridBudget`. Use `le_trans (le_of_eq ?_) key` and prove the remaining obligations. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `w _`. Rewrite using `[Formalism.PairingDivisionLocalBalance.vw_prod w Finset.univ (fun ij => rr w ij) (fun ij _ => hrr w ij), ← Finset.sum_div, hlam]`.

Use `push_cast`. Both sides reduce to the same expression.
-/
theorem grid_bound_general : GridHeightBound := by
  intro K _ _ _ _ Sq m N dl S Se N0 rr zA zA' zT zTd gT ch dd hh yy S0 cc ee qq B BN0 Bδ W0
    hdl hS hSe hrr hdd hddN hyy hcc hsq hA hT hTd hN0 hBδ
  obtain ⟨ell, hell⟩ := grid_ell_bound K
  classical
  have he : ∀ w : Pl K, (0 : ℝ) < (vw w (ell w : K) : ℝ) := by
    intro w
    have := (hell w).2
    unfold Formalism.DivisionValues.PlOver at this
    exact_mod_cast this
  have hlam : ∀ (w : Pl K) (t : ℝ),
      lw w * (vw w (ell w : K) : ℝ) * (t / (vw w (ell w : K) : ℝ)) = lw w * t := by
    intro w t
    have := (he w).ne'
    field_simp
  have habs : ∀ (w : Pl K) (t : ℝ),
      |t / (vw w (ell w : K) : ℝ)| = |t| / (vw w (ell w : K) : ℝ) := by
    intro w t
    rw [abs_div, abs_of_pos (he w)]
  have hbud : ∀ P : Finset ℕ, (∀ l ∈ P, l.Prime) →
      ∑ l ∈ P, (if l ∈ S then N0 l else 0) * Real.log l ≤ BN0 := by
    intro P _
    refine le_trans ?_ hN0
    have h1 : ∑ l ∈ P, (if l ∈ S then N0 l else 0) * Real.log l =
        ∑ l ∈ P.filter (· ∈ S), N0 l * Real.log l := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro l _
      split_ifs <;> simp
    rw [h1]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro l hl
      exact (Finset.mem_filter.1 hl).2
    · intro l hl _
      exact mul_nonneg (hS l hl).2 (Real.log_natCast_nonneg l)
  have key := Formalism.ValuationGridEstimates.grid_squares_bound (Pl K) Sq m N
    (fun w => lw w * (vw w (ell w : K) : ℝ)) (fun w => dl w / (vw w (ell w : K) : ℝ)) ell
    (fun l => if l ∈ S then N0 l else 0)
    (fun w ij => (vw w (rr w ij) : ℝ) / (vw w (ell w : K) : ℝ))
    (fun w ij => (vw w (zA ij) : ℝ) / (vw w (ell w : K) : ℝ))
    (fun w ij => (vw w (zA' ij) : ℝ) / (vw w (ell w : K) : ℝ))
    (fun w ij s => ((vw w (zT ij s) + gT ij s w : ℤ) : ℝ) / (vw w (ell w : K) : ℝ))
    (fun w ij b s => ((vw w (zTd ij b s) + gT ij s w : ℤ) : ℝ) / (vw w (ell w : K) : ℝ))
    ch dd hh yy S0 cc ee qq
    (fun w s => (vw w (qq s : K) : ℝ) / (vw w (ell w : K) : ℝ)) B (BN0 + 1) Bδ W0
    (fun w => mul_nonneg (Formalism.PairingDivisionLocalBalance.lw_nonneg w) (he w).le)
    (fun w => div_nonneg (hdl w) (he w).le)
    (fun l => by
      show (0 : ℝ) ≤ if l ∈ S then N0 l else 0
      split_ifs with h
      · exact (hS l h).2
      · exact le_rfl)
    (fun w s => div_nonneg (by exact_mod_cast Formalism.PairingDivisionLocalBalance.vw_natCast_nonneg w (qq s)) (he w).le)
    (fun w => (hell w).1)
    (fun l F hF => by
      refine le_trans (le_of_eq ?_) (partial_nat K l F)
      apply Finset.sum_congr rfl
      intro w hw
      rw [hF w hw])
    hdd hddN hyy hcc
    (fun w hw ij => by
      have hE := he w
      have h0 := hsq w hw ij
      rw [j3Wt K ell hell S N0 (fun l hl => (hS l hl).1) w,
        j3Wt K ell hell Se (fun l => 1 / (l : ℝ) ^ 2) hSe w] at h0
      simp only [habs]
      have hs1 : ∑ s ∈ Icc (1 : ℤ) (hh ij),
          (|((vw w (zT ij s) + gT ij s w : ℤ) : ℝ)| / (vw w (ell w : K) : ℝ) +
            |((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ)| / (vw w (ell w : K) : ℝ)) =
          (∑ s ∈ Icc (1 : ℤ) (hh ij), (|((vw w (zT ij s) + gT ij s w : ℤ) : ℝ)| +
            |((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ)|)) / (vw w (ell w : K) : ℝ) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro s _
        ring
      have hs2 : ∑ s ∈ S0, (cc s : ℝ) * ((vw w (qq s : K) : ℝ) / (vw w (ell w : K) : ℝ)) =
          (∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ)) / (vw w (ell w : K) : ℝ) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro s _
        ring
      rw [hs1, hs2, div_le_iff₀ hE]
      refine le_trans h0 ?_
      generalize (∑ s ∈ Icc (1 : ℤ) (hh ij), (|((vw w (zT ij s) + gT ij s w : ℤ) : ℝ)| +
            |((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ)|)) = T1
      generalize (∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ)) = T2
      generalize (vw w (ell w : K) : ℝ) = E at hE ⊢
      have hε : (if ell w ∈ Se then 1 / ((ell w : ℕ) : ℝ) ^ 2 else 0) ≤ (((ell w : ℕ) : ℝ) ^ 2)⁻¹ := by
        split_ifs
        · rw [one_div]
        · positivity
      have hdd0 : (0 : ℝ) ≤ (dd ij : ℝ) := Nat.cast_nonneg _
      have h5 : (dd ij : ℝ) * ((if ell w ∈ Se then 1 / ((ell w : ℕ) : ℝ) ^ 2 else 0) * E) ≤
          (dd ij : ℝ) * ((((ell w : ℕ) : ℝ) ^ 2)⁻¹ * E) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hε hE.le) hdd0
      have h6 : (|(vw w (zA ij) : ℝ)| / E + |(vw w (zA' ij) : ℝ)| / E + 4 * (T1 / E) +
          (dd ij : ℝ) * ((if ell w ∈ S then N0 (ell w) else 0) + (((ell w : ℕ) : ℝ) ^ 2)⁻¹) +
          6 * (dl w / E) + (yy ij : ℝ) * (2 * (T2 / E))) * E =
          |(vw w (zA ij) : ℝ)| + |(vw w (zA' ij) : ℝ)| + 4 * T1 +
          (dd ij : ℝ) * ((if ell w ∈ S then N0 (ell w) else 0) * E + (((ell w : ℕ) : ℝ) ^ 2)⁻¹ * E) +
          6 * dl w + (yy ij : ℝ) * (2 * T2) := by
        have := hE.ne'
        field_simp
      rw [h6]
      linarith)
    (fun ij F => by
      refine le_trans (le_of_eq ?_) (partial_ht (hA ij).1 F)
      apply Finset.sum_congr rfl
      intro w _
      simp only [habs, hlam, add_zero])
    (fun ij F => by
      refine le_trans (le_of_eq ?_) (partial_ht (hA ij).2 F)
      apply Finset.sum_congr rfl
      intro w _
      simp only [habs, hlam, add_zero])
    (fun ij s F => by
      refine le_trans (le_of_eq ?_) (partial_ht (hT ij s) F)
      apply Finset.sum_congr rfl
      intro w _
      simp only [habs, hlam])
    (fun ij b s F => by
      refine le_trans (le_of_eq ?_) (partial_ht (hTd ij b s) F)
      apply Finset.sum_congr rfl
      intro w _
      simp only [habs, hlam])
    (Formalism.ValuationGridEstimates.prime_budget_bound (fun l => if l ∈ S then N0 l else 0) BN0 hbud)
    (fun F => by
      refine le_trans (le_of_eq ?_) (hBδ F)
      apply Finset.sum_congr rfl
      intro w _
      simp only [hlam])
    (fun s _ F => by
      refine le_trans (le_of_eq ?_) (partial_nat K (qq s) F)
      apply Finset.sum_congr rfl
      intro w _
      simp only [hlam])
  unfold gridBudget
  refine le_trans (le_of_eq ?_) key
  apply Finset.sum_congr rfl
  intro w _
  rw [Formalism.PairingDivisionLocalBalance.vw_prod w Finset.univ (fun ij => rr w ij) (fun ij _ => hrr w ij), ← Finset.sum_div, hlam]
  push_cast
  rfl

/- English proof (translation)
Unfold `Formalism.PairingDivisionLocalBalance.wt`. Use `Finset.sum_nonneg fun l hl => mul_nonneg (hc l hl) ?_` and prove the remaining obligations. Use `(Formalism.DivisionValues.valuation_basic_properties K w).2.2.2.2.2.2 (l : 𝓞 K)` as an intermediate fact. Establish `h2 : (((l : 𝓞 K)) : K) = (l : K)` using `by simp`. Rewrite `this` using `[h2]`.

Conclude with `this` after adjusting the coercions.
-/
theorem wt_nonneg' {K : Type} [Field K] [NumberField K] [StarRing K] (S : Finset ℕ) (c : ℕ → ℝ)
    (hc : ∀ l ∈ S, 0 ≤ c l) (w : Pl K) : 0 ≤ wt S c w := by
  unfold Formalism.PairingDivisionLocalBalance.wt
  refine Finset.sum_nonneg fun l hl => mul_nonneg (hc l hl) ?_
  have := (Formalism.DivisionValues.valuation_basic_properties K w).2.2.2.2.2.2 (l : 𝓞 K)
  have h2 : (((l : 𝓞 K)) : K) = (l : K) := by simp
  rw [h2] at this
  exact_mod_cast this

/- English proof (translation)
Introduce `K _ _ _ w a a' d h p q e h1 h2 h3 h4 h5 x xd y E g S Se N0 δ σ hN0 hne hy hE c0 c00 A A0 A0' hc0 hc00 hA hA0 hA0' hcA hcA' hAA ub ua hu hub hua r hr`. Take `⟨vmul, -, -, -, vone, vinv, -⟩` from `Formalism.DivisionValues.valuation_basic_properties K w`. Set `M : K → Multiplicative ℝ` to `fun z => Multiplicative.ofAdd ((vw w z : ℤ) : ℝ)`. Establish `Mmul : ∀ a b : K, a ≠ 0 → b ≠ 0 → M (a * b) = M a * M b`. Introduce `a b ha hb`.

Simplify using `only [M, vmul a b ha hb, Int.cast_add, ofAdd_add]`. Establish `Minv : ∀ a : K, M a⁻¹ = (M a)⁻¹`. Introduce `a`. Simplify using `only [M, vinv a, Int.cast_neg, ofAdd_neg]`. Establish `Mdiv : ∀ a b : K, a ≠ 0 → b ≠ 0 → M (a / b) = M a / M b`.

Introduce `a b ha hb`. Rewrite using `[div_eq_mul_inv, Mmul a _ ha (inv_ne_zero hb), Minv, div_eq_mul_inv]`. Establish `Mprod : ∀ (ι : Type) (s : Finset ι) (f : ι → K), (∀ i ∈ s, f i ≠ 0) → M (∏ i ∈ s, f i) = ∏ i ∈ s, M (f i)`. Introduce `ι s f`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty => intro _`. Simplify using `[M, vone]`. Consider the case `insert i s hi ih`. Introduce `hf`. Rewrite using `[Finset.prod_insert hi, Finset.prod_insert hi, Mmul _ _ (hf i (by simp)) (Finset.prod_ne_zero_iff.2 fun j hj => hf j (by simp [hj])), ih (fun j hj => hf j (by simp [hj]))]`.

Establish `hρ : ∀ s, rhoAt x y E s ≠ 0`. Introduce `s`. Unfold `rhoAt`. Use `split_ifs`. Conclude with `div_ne_zero (hne s).2.2.1 (hne s).1`.

Conclude with `mul_ne_zero (hne s).2.2.2 (div_ne_zero (hne _).2.2.1 (hne _).1)`. Establish `s1 : ∀ s : ℤ, 1 ≤ s → s ≤ h → M (rhoAt x y E s) = Multiplicative.ofAdd (((vw w (y s) + g s : ℤ)) : ℝ) / Multiplicative.ofAdd (((vw w (x s) + g s : ℤ)) : ℝ) ∧ - wt S N0 w ≤ Multiplicative.toAdd (Multiplicative.ofAdd (((vw w (y s) + g s : ℤ)) : ℝ)) ∧ Multiplicative.toAdd (Multiplic …`. Introduce `s hs1 hs2`. Use `⟨?_, (hy s hs1 hs2).1, (hy s hs1 hs2).2⟩` and prove the remaining obligations. Establish `: rhoAt x y E s = y s / x s` using `by unfold rhoAt; rw [if_pos hs1]`.

Rewrite using `[this, Mdiv _ _ (hne s).2.2.1 (hne s).1]`. Simplify using `only [M, ← ofAdd_sub]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `s2 : ∀ s : ℤ, 1 - ((e : ℤ) + q - p) ≤ s → s ≤ 0 → M (rhoAt x y E s) = M (E s) * M (rhoAt x y E (1 - s)) ∧ Multiplicative.toAdd (M (E s)) = 0`. Introduce `s hs1 hs2`. Prove the components needed by the constructor for the conclusion. Establish `e1 : rhoAt x y E s = E s * (y (1 - s) / x (1 - s))`. Unfold `rhoAt; rw [if_neg (by omega)]`.

Establish `e2 : rhoAt x y E (1 - s) = y (1 - s) / x (1 - s)`. Unfold `rhoAt; rw [if_pos (by omega)]`. Rewrite using `[e1, e2, Mmul _ _ (hne s).2.2.2 (div_ne_zero (hne _).2.2.1 (hne _).1)]`. Simplify using `[M, hE s hs1 hs2]`. Establish `s3 : M A / M A0 = ∏ s ∈ Icc (1 - ((e : ℤ) + q - p)) ((h : ℤ) - (p + q)), M (rhoAt x y E s)`.

Rewrite using `[← Mdiv _ _ hA hA0, hAA, Mprod _ _ _ (fun s _ => hρ s)]`. Establish `n1 : (∏ j ∈ range q, ub j) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun j _ => (hu j).1`. Establish `n2 : (∏ i ∈ range p, ua i) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun j _ => (hu j).2`. Establish `n3 : c0 / c00 ≠ 0` using `div_ne_zero hc0 hc00`. Establish `n4 : (∏ k ∈ Icc 1 p, rhoAt x y E ((e : ℤ) + q - k + 1)) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun j _ => hρ _`.

Establish `n5 : (∏ k ∈ Icc 1 q, rhoAt x y E ((e : ℤ) + k)) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun j _ => hρ _`. Establish `s4 : M r = ((∏ j ∈ range q, M (ub j)) * ∏ i ∈ range p, M (ua i)) * (M c0 / M c00) * (∏ k ∈ Icc 1 p, M (rhoAt x y E ((e : ℤ) + q - k + 1))) * (∏ k ∈ Icc 1 q, M (rhoAt x y E ((e : ℤ) + k)))⁻¹`. Rewrite using `[hr, Mmul _ _ (mul_ne_zero (mul_ne_zero (mul_ne_zero n1 n2) n3) n4) (inv_ne_zero n5), Mmul _ _ (mul_ne_zero (mul_ne_zero n1 n2) n3) n4, Mmul _ _ (mul_ne_zero n1 n2) n3, Mmul _ _ n1 n2, Minv, Mdiv _ _ hc0 hc00, Mprod _ _ _ (fun j _ => (hu j).1), Mprod _ _ _ (fun j _ => (hu j).2), …`. Conclude with `Formalism.ValuationGridEstimates.valuation_ratio_bound (Multiplicative ℝ) (fun z => Multiplicative.toAdd z) (fun _ _ => rfl) a a' d h p q e h1 h2 h3 h4 h5 (fun s => Multiplicative.ofAdd (((vw w (x s) + g s : ℤ)) : ℝ)) (fun s => Multiplicative.ofAdd (((vw w (xd s) + g s : ℤ)) : ℝ) …`.
-/
theorem grid_square_bound : SquareAtPlaceBound := by
  intro K _ _ _ w a a' d h p q e h1 h2 h3 h4 h5 x xd y E g S Se N0 δ σ hN0 hne hy hE
    c0 c00 A A0 A0' hc0 hc00 hA hA0 hA0' hcA hcA' hAA ub ua hu hub hua r hr
  obtain ⟨vmul, -, -, -, vone, vinv, -⟩ := Formalism.DivisionValues.valuation_basic_properties K w
  let M : K → Multiplicative ℝ := fun z => Multiplicative.ofAdd ((vw w z : ℤ) : ℝ)
  have Mmul : ∀ a b : K, a ≠ 0 → b ≠ 0 → M (a * b) = M a * M b := by
    intro a b ha hb
    simp only [M, vmul a b ha hb, Int.cast_add, ofAdd_add]
  have Minv : ∀ a : K, M a⁻¹ = (M a)⁻¹ := by
    intro a; simp only [M, vinv a, Int.cast_neg, ofAdd_neg]
  have Mdiv : ∀ a b : K, a ≠ 0 → b ≠ 0 → M (a / b) = M a / M b := by
    intro a b ha hb
    rw [div_eq_mul_inv, Mmul a _ ha (inv_ne_zero hb), Minv, div_eq_mul_inv]
  have Mprod : ∀ (ι : Type) (s : Finset ι) (f : ι → K), (∀ i ∈ s, f i ≠ 0) →
      M (∏ i ∈ s, f i) = ∏ i ∈ s, M (f i) := by
    intro ι s f
    classical
    induction s using Finset.induction_on with
    | empty => intro _; simp [M, vone]
    | insert i s hi ih =>
      intro hf
      rw [Finset.prod_insert hi, Finset.prod_insert hi,
        Mmul _ _ (hf i (by simp)) (Finset.prod_ne_zero_iff.2 fun j hj => hf j (by simp [hj])),
        ih (fun j hj => hf j (by simp [hj]))]
  have hρ : ∀ s, rhoAt x y E s ≠ 0 := by
    intro s; unfold rhoAt; split_ifs
    · exact div_ne_zero (hne s).2.2.1 (hne s).1
    · exact mul_ne_zero (hne s).2.2.2 (div_ne_zero (hne _).2.2.1 (hne _).1)
  have s1 : ∀ s : ℤ, 1 ≤ s → s ≤ h →
      M (rhoAt x y E s) = Multiplicative.ofAdd (((vw w (y s) + g s : ℤ)) : ℝ) /
        Multiplicative.ofAdd (((vw w (x s) + g s : ℤ)) : ℝ) ∧
      - wt S N0 w ≤ Multiplicative.toAdd (Multiplicative.ofAdd (((vw w (y s) + g s : ℤ)) : ℝ)) ∧
      Multiplicative.toAdd (Multiplicative.ofAdd (((vw w (y s) + g s : ℤ)) : ℝ)) ≤
        Multiplicative.toAdd (Multiplicative.ofAdd (((vw w (xd s) + g s : ℤ)) : ℝ)) +
          wt Se (fun l => 1 / (l : ℝ) ^ 2) w := by
    intro s hs1 hs2
    refine ⟨?_, (hy s hs1 hs2).1, (hy s hs1 hs2).2⟩
    have : rhoAt x y E s = y s / x s := by unfold rhoAt; rw [if_pos hs1]
    rw [this, Mdiv _ _ (hne s).2.2.1 (hne s).1]
    simp only [M, ← ofAdd_sub]
    congr 1
    push_cast
    ring
  have s2 : ∀ s : ℤ, 1 - ((e : ℤ) + q - p) ≤ s → s ≤ 0 →
      M (rhoAt x y E s) = M (E s) * M (rhoAt x y E (1 - s)) ∧
      Multiplicative.toAdd (M (E s)) = 0 := by
    intro s hs1 hs2
    constructor
    · have e1 : rhoAt x y E s = E s * (y (1 - s) / x (1 - s)) := by
        unfold rhoAt; rw [if_neg (by omega)]
      have e2 : rhoAt x y E (1 - s) = y (1 - s) / x (1 - s) := by
        unfold rhoAt; rw [if_pos (by omega)]
      rw [e1, e2, Mmul _ _ (hne s).2.2.2 (div_ne_zero (hne _).2.2.1 (hne _).1)]
    · simp [M, hE s hs1 hs2]
  have s3 : M A / M A0 =
      ∏ s ∈ Icc (1 - ((e : ℤ) + q - p)) ((h : ℤ) - (p + q)), M (rhoAt x y E s) := by
    rw [← Mdiv _ _ hA hA0, hAA, Mprod _ _ _ (fun s _ => hρ s)]
  have n1 : (∏ j ∈ range q, ub j) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => (hu j).1
  have n2 : (∏ i ∈ range p, ua i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => (hu j).2
  have n3 : c0 / c00 ≠ 0 := div_ne_zero hc0 hc00
  have n4 : (∏ k ∈ Icc 1 p, rhoAt x y E ((e : ℤ) + q - k + 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => hρ _
  have n5 : (∏ k ∈ Icc 1 q, rhoAt x y E ((e : ℤ) + k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => hρ _
  have s4 : M r = ((∏ j ∈ range q, M (ub j)) * ∏ i ∈ range p, M (ua i)) * (M c0 / M c00) *
        (∏ k ∈ Icc 1 p, M (rhoAt x y E ((e : ℤ) + q - k + 1))) *
        (∏ k ∈ Icc 1 q, M (rhoAt x y E ((e : ℤ) + k)))⁻¹ := by
    rw [hr, Mmul _ _ (mul_ne_zero (mul_ne_zero (mul_ne_zero n1 n2) n3) n4) (inv_ne_zero n5),
      Mmul _ _ (mul_ne_zero (mul_ne_zero n1 n2) n3) n4, Mmul _ _ (mul_ne_zero n1 n2) n3,
      Mmul _ _ n1 n2, Minv, Mdiv _ _ hc0 hc00, Mprod _ _ _ (fun j _ => (hu j).1),
      Mprod _ _ _ (fun j _ => (hu j).2), Mprod _ _ _ (fun j _ => hρ _),
      Mprod _ _ _ (fun j _ => hρ _)]
  exact Formalism.ValuationGridEstimates.valuation_ratio_bound (Multiplicative ℝ) (fun z => Multiplicative.toAdd z)
    (fun _ _ => rfl) a a' d h p q e h1 h2 h3 h4 h5
    (fun s => Multiplicative.ofAdd (((vw w (x s) + g s : ℤ)) : ℝ))
    (fun s => Multiplicative.ofAdd (((vw w (xd s) + g s : ℤ)) : ℝ))
    (fun s => Multiplicative.ofAdd (((vw w (y s) + g s : ℤ)) : ℝ))
    (fun s => M (rhoAt x y E s)) (fun s => M (E s))
    (wt S N0 w) (wt Se (fun l => 1 / (l : ℝ) ^ 2) w) δ σ
    (wt_nonneg' S N0 hN0 w) (wt_nonneg' Se _ (fun l _ => by positivity) w)
    s1 s2 (M c0) (M c00) (M A) (M A0) (M A0') hcA hcA' s3
    (fun j => M (ub j)) (fun i => M (ua i)) hub hua (M r) s4

/- English proof (translation)
Unfold `denIdeal`. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `w _`. Conclude with `zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot)`.
-/
theorem denIdeal_ne_zero {K : Type} [Field K] [NumberField K] (T : Finset (Pl K)) (a : Pl K → ℤ) :
    denIdeal T a ≠ 0 := by
  unfold denIdeal
  rw [Finset.prod_ne_zero_iff]
  intro w _
  exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot)

/- English proof (translation)
Establish `h : Ideal.absNorm w.asIdeal ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `w.ne_bot`. Conclude with `h` after adjusting the coercions.
-/
theorem absNorm_pl_ne_zero {K : Type} [Field K] [NumberField K] (w : Pl K) :
    (Ideal.absNorm w.asIdeal : ℝ) ≠ 0 := by
  have h : Ideal.absNorm w.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact w.ne_bot
  exact_mod_cast h

/- English proof (translation)
Unfold `denIdeal`. Rewrite using `[map_prod, Rat.cast_prod, Real.log_prod]`. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[map_zpow₀, FractionalIdeal.coeIdeal_absNorm, Rat.cast_zpow, Real.log_zpow]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `w _`. Rewrite using `[map_zpow₀, FractionalIdeal.coeIdeal_absNorm, Rat.cast_zpow]`. Apply `zpow_ne_zero` to reduce the goal to its premises.

Use `absNorm_pl_ne_zero w` as an intermediate fact. Conclude with `this` after adjusting the coercions.
-/
theorem log_absNorm_denIdeal {K : Type} [Field K] [NumberField K] (T : Finset (Pl K))
    (a : Pl K → ℤ) :
    Real.log ((FractionalIdeal.absNorm (denIdeal T a) : ℚ) : ℝ) =
      -∑ w ∈ T, Real.log (Ideal.absNorm w.asIdeal : ℝ) * (a w : ℝ) := by
  unfold denIdeal
  rw [map_prod, Rat.cast_prod, Real.log_prod]
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm, Rat.cast_zpow, Real.log_zpow]
    push_cast
    ring
  · intro w _
    rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm, Rat.cast_zpow]
    apply zpow_ne_zero
    have := absNorm_pl_ne_zero w
    exact_mod_cast this

/- English proof (translation)
Unfold `Formalism.DivisionValues.lw`. Conclude with `div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)`.
-/
theorem lw_nonneg' {K : Type} [Field K] [NumberField K] (w : Pl K) : 0 ≤ lw w := by
  unfold Formalism.DivisionValues.lw
  exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

/- English proof (translation)
Introduce `K V ι W κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b X b' X' hX hX' φ A B T a hA hA0 hB hB0 hφ hincl`. Establish `hI : denIdeal T a ≠ 0` using `denIdeal_ne_zero T a`. Take `⟨hfg, -, hmax, -⟩` from `Formalism.LFunctionChainParameters.LLcv.ideal_scaling_holds K W κ b' X' hX' (denIdeal T a) hI B hB hB0`. Establish `hmap : A.map (φ.restrictScalars (𝓞 K)) ≠ ⊥`. Introduce `h`.

Apply `hA0` to reduce the goal to its premises. Rewrite using `[Submodule.eq_bot_iff]`. Introduce `x hx`. Establish `h1 : (φ.restrictScalars (𝓞 K)) x ∈ A.map (φ.restrictScalars (𝓞 K))` using `Submodule.mem_map_of_mem hx`. Rewrite `h1` using `[h, Submodule.mem_bot]`.

Apply `hφ` to reduce the goal to its premises. Rewrite using `[map_zero]`. Conclude with `h1`. Take `⟨-, h2⟩` from `Formalism.HN.slope_inequality_mean K V ι W κ b X b' X' hX hX' φ A hA hmap`. Establish `h3` using `(h2 _ hfg hincl).2 hφ.injOn`.

Rewrite `h3` using `[hmax, log_absNorm_denIdeal]`. Establish `e : ∑ w ∈ T, lw w * (a w : ℝ) = (∑ w ∈ T, Real.log (Ideal.absNorm w.asIdeal : ℝ) * (a w : ℝ)) / (finrank ℚ K : ℝ)`. Rewrite using `[Finset.sum_div]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Unfold `Formalism.DivisionValues.lw`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Generalize the expression as in `(∑ w ∈ T, Real.log (Ideal.absNorm w.asIdeal : ℝ) * (a w : ℝ)) = sm at h3 ⊢`. Establish `e2 : (2 * -sm) / (finrank ℚ K : ℝ) = -(2 * (sm / (finrank ℚ K : ℝ)))` using `by ring`. Rewrite `h3` using `[e2]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem grid_lemma_A : SlopeInequalityDenominators := by
  intro K V ι W κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b X b' X' hX hX' φ A B T a hA hA0 hB hB0 hφ hincl
  have hI : denIdeal T a ≠ 0 := denIdeal_ne_zero T a
  obtain ⟨hfg, -, hmax, -⟩ :=
    Formalism.LFunctionChainParameters.LLcv.ideal_scaling_holds K W κ b' X' hX' (denIdeal T a) hI B hB hB0
  have hmap : A.map (φ.restrictScalars (𝓞 K)) ≠ ⊥ := by
    intro h
    apply hA0
    rw [Submodule.eq_bot_iff]
    intro x hx
    have h1 : (φ.restrictScalars (𝓞 K)) x ∈ A.map (φ.restrictScalars (𝓞 K)) :=
      Submodule.mem_map_of_mem hx
    rw [h, Submodule.mem_bot] at h1
    apply hφ
    rw [map_zero]
    exact h1
  obtain ⟨-, h2⟩ := Formalism.HN.slope_inequality_mean K V ι W κ b X b' X' hX hX' φ A hA hmap
  have h3 := (h2 _ hfg hincl).2 hφ.injOn
  rw [hmax, log_absNorm_denIdeal] at h3
  have e : ∑ w ∈ T, lw w * (a w : ℝ) =
      (∑ w ∈ T, Real.log (Ideal.absNorm w.asIdeal : ℝ) * (a w : ℝ)) / (finrank ℚ K : ℝ) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun w _ => ?_
    unfold Formalism.DivisionValues.lw
    ring
  rw [e]
  generalize (∑ w ∈ T, Real.log (Ideal.absNorm w.asIdeal : ℝ) * (a w : ℝ)) = sm at h3 ⊢
  have e2 : (2 * -sm) / (finrank ℚ K : ℝ) = -(2 * (sm / (finrank ℚ K : ℝ))) := by ring
  rw [e2] at h3
  linarith

/- English proof (translation)
Introduce `K V ι W κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b X b' X' hX hX' R M Ψ T a r dF EM hInf Gr BF hfg hne hM hM0 hΨ hincl ha hEM hh hGr hBF`. Establish `h` using `grid_lemma_A K V ι W κ b X b' X' hX hX' Ψ R M T a hfg hne hM hM0 hΨ hincl`. Establish `hs : ∑ w ∈ T, lw w * (a w : ℝ) ≤ Gr + BF`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun w hw => ?_` and prove the remaining obligations.

Establish `h1` using `ha w hw`. Establish `hl : 0 ≤ lw w` using `lw_nonneg' w`. Use the polynomial consequences of the given equalities and inequalities. Use `_ = ∑ w ∈ T, lw w * (vw w (r w) : ℝ) + ∑ w ∈ T, lw w * dF w := Finset.sum_add_distrib`. Use `_ ≤ Gr + BF := add_le_add hGr hBF`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem grid_function_values : LargestSlopeFunctionSpace := by
  intro K V ι W κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b X b' X' hX hX' R M Ψ T a r dF EM hInf Gr BF
    hfg hne hM hM0 hΨ hincl ha hEM hh hGr hBF
  have h := grid_lemma_A K V ι W κ b X b' X' hX hX' Ψ R M T a hfg hne hM hM0 hΨ hincl
  have hs : ∑ w ∈ T, lw w * (a w : ℝ) ≤ Gr + BF := by
    calc ∑ w ∈ T, lw w * (a w : ℝ)
        ≤ ∑ w ∈ T, (lw w * (vw w (r w) : ℝ) + lw w * dF w) := by
          refine Finset.sum_le_sum fun w hw => ?_
          have h1 := ha w hw
          have hl : 0 ≤ lw w := lw_nonneg' w
          nlinarith
      _ = ∑ w ∈ T, lw w * (vw w (r w) : ℝ) + ∑ w ∈ T, lw w * dF w := Finset.sum_add_distrib
      _ ≤ Gr + BF := add_le_add hGr hBF
  linarith

/- English proof (translation)
Introduce `K W κ _ _ _ _ _ _ _ _ _ _ D hD XE kap b' X' hXE hkap hX' R M Ψ T a r dF EM hInf Gr BF hR hM hM0 hΨ hincl ha hEM hh hGr hBF`. Take `⟨hfg, hne⟩` from `Formalism.DivisionValues.lattice_fg_ne_bot hD R hR`. Take `⟨hu, -, -, -, h5⟩` from `Formalism.DivisionValues.kappa_normalise K D hD XE hXE kap hkap`. Take `⟨-, e2, -⟩` from `h5 R hR`. Establish `h` using `hA K (Fin D → K) (Fin D) W κ (Pi.basisFun K (Fin D)) (Formalism.DivisionValues.scaleFrame (fun v => (kap v)⁻¹) XE) b' X' hu hX' Ψ R M T a hfg hne hM hM0 hΨ hincl`.

Establish `hs : ∑ w ∈ T, lw w * (a w : ℝ) ≤ Gr + BF`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun w hw => ?_` and prove the remaining obligations. Establish `h1` using `ha w hw`. Establish `hl : 0 ≤ lw w` using `lw_nonneg' w`.

Use the polynomial consequences of the given equalities and inequalities. Use `_ = ∑ w ∈ T, lw w * (vw w (r w) : ℝ) + ∑ w ∈ T, lw w * dF w := Finset.sum_add_distrib`. Use `_ ≤ Gr + BF := add_le_add hGr hBF`. Rewrite using `[e2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem grid_function_of_lemma_A (hA : SlopeInequalityDenominators) : LargestSlopeLatticeFrames := by
  intro K W κ _ _ _ _ _ _ _ _ _ _ D hD XE kap b' X' hXE hkap hX' R M Ψ T a r dF EM hInf Gr BF
    hR hM hM0 hΨ hincl ha hEM hh hGr hBF
  obtain ⟨hfg, hne⟩ := Formalism.DivisionValues.lattice_fg_ne_bot hD R hR
  obtain ⟨hu, -, -, -, h5⟩ := Formalism.DivisionValues.kappa_normalise K D hD XE hXE kap hkap
  obtain ⟨-, e2, -⟩ := h5 R hR
  have h := hA K (Fin D → K) (Fin D) W κ (Pi.basisFun K (Fin D))
    (Formalism.DivisionValues.scaleFrame (fun v => (kap v)⁻¹) XE) b' X' hu hX' Ψ R M T a hfg hne hM hM0 hΨ hincl
  have hs : ∑ w ∈ T, lw w * (a w : ℝ) ≤ Gr + BF := by
    calc ∑ w ∈ T, lw w * (a w : ℝ)
        ≤ ∑ w ∈ T, (lw w * (vw w (r w) : ℝ) + lw w * dF w) := by
          refine Finset.sum_le_sum fun w hw => ?_
          have h1 := ha w hw
          have hl : 0 ≤ lw w := lw_nonneg' w
          nlinarith
      _ = ∑ w ∈ T, lw w * (vw w (r w) : ℝ) + ∑ w ∈ T, lw w * dF w := Finset.sum_add_distrib
      _ ≤ Gr + BF := add_le_add hGr hBF
  rw [e2]
  linarith

/- English proof (translation)
The claim follows from `grid_function_of_lemma_A grid_lemma_A`.
-/
theorem grid_function_bound : LargestSlopeLatticeFrames := grid_function_of_lemma_A grid_lemma_A

/- English proof (translation)
Introduce `K W κ _ _ _ _ _ _ _ _ _ _ D hD XE kap b' X' hXE hkap hX' R M Ψ T a dF EM hInf BF p2 bb hR hM hM0 hΨ hincl hEM hh hBF Sq m N dl S Se N0 rr zA zA' zT zTd gT ch dd hh' yy S0 cc ee qq B BN0 Bδ ha hdl hS hSe hrr hdd hddN hyy hcc hsq hHA hHT hHTd hBN0 hBδ hsize`. Establish `hg` using `hG K Sq m N dl S Se N0 rr zA zA' zT zTd gT ch dd hh' yy S0 cc ee qq B BN0 Bδ T hdl hS hSe hrr hdd hddN hyy hcc hsq hHA hHT hHTd hBN0 hBδ`. Establish `h` using `hF K W κ D hD XE kap b' X' hXE hkap hX' R M Ψ T a (fun w => ∏ ij, rr w ij) dF EM hInf (gridBudget m N B BN0 Bδ S0 ee qq) BF hR hM hM0 hΨ hincl ha hEM hh hg hBF`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem height_h0_of_grid (hG : GridHeightBound) (hF : LargestSlopeLatticeFrames) : PassageSizeHypothesis := by
  intro K W κ _ _ _ _ _ _ _ _ _ _ D hD XE kap b' X' hXE hkap hX' R M Ψ T a dF EM hInf BF p2 bb
    hR hM hM0 hΨ hincl hEM hh hBF Sq m N dl S Se N0 rr zA zA' zT zTd gT ch dd hh' yy S0 cc ee qq
    B BN0 Bδ ha hdl hS hSe hrr hdd hddN hyy hcc hsq hHA hHT hHTd hBN0 hBδ hsize
  have hg := hG K Sq m N dl S Se N0 rr zA zA' zT zTd gT ch dd hh' yy S0 cc ee qq B BN0 Bδ T
    hdl hS hSe hrr hdd hddN hyy hcc hsq hHA hHT hHTd hBN0 hBδ
  have h := hF K W κ D hD XE kap b' X' hXE hkap hX' R M Ψ T a (fun w => ∏ ij, rr w ij) dF EM hInf
    (gridBudget m N B BN0 Bδ S0 ee qq) BF hR hM hM0 hΨ hincl ha hEM hh hg hBF
  linarith

/- English proof (translation)
Introduce `h0`. Establish `h2 : Submodule.span K (((⊥ : Submodule (𝓞 K) V)) : Set V) = ⊥` using `by simp`. Rewrite `h` using `[h0, h2]`. Establish `h3` using `congrArg (fun U : Submodule K V => finrank K U) h`. Simplify using `only [finrank_bot, finrank_top, Module.finrank_eq_card_basis b] at h3`.

Establish `: 0 < Fintype.card ι` using `Fintype.card_pos`. Use linear arithmetic over natural numbers and integers.
-/
theorem ne_bot_of_span_top {K V ι : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [Nonempty ι]
    (b : Basis ι K V) (A : Submodule (𝓞 K) V) (h : Submodule.span K (A : Set V) = ⊤) : A ≠ ⊥ := by
  intro h0
  have h2 : Submodule.span K (((⊥ : Submodule (𝓞 K) V)) : Set V) = ⊥ := by simp
  rw [h0, h2] at h
  have h3 := congrArg (fun U : Submodule K V => finrank K U) h
  simp only [finrank_bot, finrank_top, Module.finrank_eq_card_basis b] at h3
  have : 0 < Fintype.card ι := Fintype.card_pos
  omega

/- English proof (translation)
Introduce `K V ι _ _ _ _ _ _ _ _ _ _ _ b X hX A hA hspan`. Establish `hXd : ∀ v, IsUnit (dualFrame X v).det`. Introduce `v`. Simplify using `only [Formalism.HN.dualFrame]`. Rewrite using `[Matrix.isUnit_nonsing_inv_det_iff, Matrix.det_transpose]`.

Conclude with `hX v`. Take `⟨hdfg, hdspan, -, -, -, hlarge, -⟩` from `Formalism.HN.dual_polygon_identity K V ι b X hX A hA hspan`. Establish `hA0 : A ≠ ⊥` using `ne_bot_of_span_top b A hspan`. Establish `hd0 : dualLat A ≠ ⊥` using `ne_bot_of_span_top b.dualBasis (dualLat A) hdspan`. Take `⟨-, -, -, hl, -, -⟩` from `Formalism.HN.size_maximal_slope K V ι b X hX A hA hA0`.

Take `⟨-, -, -, -, hL, -⟩` from `Formalism.HN.size_maximal_slope K (Module.Dual K V) ι b.dualBasis (dualFrame X) hXd (dualLat A) hdfg hd0`. Rewrite `hlarge` using `[hl, hL, ← Real.exp_neg]`. Establish `h` using `Real.exp_injective hlarge`. Unfold `Formalism.HN.muMinDef Formalism.HN.muMaxDef`. Establish `e : Formalism.HN.logDisc K / (2 * (finrank ℚ K : ℝ)) = Formalism.HN.logDisc K / (finrank ℚ K : ℝ) / 2`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem dual_minimal_slope_bound : DualLatticeMinimalSlope := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ _ b X hX A hA hspan
  have hXd : ∀ v, IsUnit (dualFrame X v).det := by
    intro v
    simp only [Formalism.HN.dualFrame]
    rw [Matrix.isUnit_nonsing_inv_det_iff, Matrix.det_transpose]
    exact hX v
  obtain ⟨hdfg, hdspan, -, -, -, hlarge, -⟩ := Formalism.HN.dual_polygon_identity K V ι b X hX A hA hspan
  have hA0 : A ≠ ⊥ := ne_bot_of_span_top b A hspan
  have hd0 : dualLat A ≠ ⊥ := ne_bot_of_span_top b.dualBasis (dualLat A) hdspan
  obtain ⟨-, -, -, hl, -, -⟩ := Formalism.HN.size_maximal_slope K V ι b X hX A hA hA0
  obtain ⟨-, -, -, -, hL, -⟩ :=
    Formalism.HN.size_maximal_slope K (Module.Dual K V) ι b.dualBasis (dualFrame X) hXd (dualLat A) hdfg hd0
  rw [hl, hL, ← Real.exp_neg] at hlarge
  have h := Real.exp_injective hlarge
  unfold Formalism.HN.muMinDef Formalism.HN.muMaxDef
  have e : Formalism.HN.logDisc K / (2 * (finrank ℚ K : ℝ)) = Formalism.HN.logDisc K / (finrank ℚ K : ℝ) / 2 := by
    ring
  rw [e] at h
  linarith

/- English proof (translation)
Introduce `K _ _ _ _ D hD XE hXE R1 HH0 sF logκ lam0 c p2 ps bb hR1 h0 h1 hs hc hlam hbb hp`. Establish `: Nonempty (Fin D)` using `⟨⟨0, hD⟩⟩`. Establish `e` using `hd K (Fin D → K) (Fin D) (Pi.basisFun K (Fin D)) XE hXE R1 (Submodule.IsLattice.fg (self := hR1)) (Submodule.IsLattice.span_eq_top (self := hR1))`. Rewrite using `[e]`. Use `⟨?_, le_max_of_le_left hbb, max_le ?_ ?_⟩` and prove the remaining obligations.

Use `le_max_right bb (sF + muMaxDef (Pi.basisFun K (Fin D)) XE R1)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use the polynomial consequences of the given equalities and inequalities. Establish `: c * lam0 ≤ c * bb` using `mul_le_mul_of_nonneg_left hlam hc`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem frame_height_of_dual_slope (hd : DualLatticeMinimalSlope) : FrameTheoremHeightNumber := by
  intro K _ _ _ _ D hD XE hXE R1 HH0 sF logκ lam0 c p2 ps bb hR1 h0 h1 hs hc hlam hbb hp
  have : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  have e := hd K (Fin D → K) (Fin D) (Pi.basisFun K (Fin D)) XE hXE R1
    (Submodule.IsLattice.fg (self := hR1)) (Submodule.IsLattice.span_eq_top (self := hR1))
  rw [e]
  refine ⟨?_, le_max_of_le_left hbb, max_le ?_ ?_⟩
  · have := le_max_right bb (sF + muMaxDef (Pi.basisFun K (Fin D)) XE R1)
    linarith
  · nlinarith
  · have : c * lam0 ≤ c * bb := mul_le_mul_of_nonneg_left hlam hc
    nlinarith

/- English proof (translation)
The claim follows from `frame_height_of_dual_slope dual_minimal_slope_bound`.
-/
theorem frame_height_bound : FrameTheoremHeightNumber := frame_height_of_dual_slope dual_minimal_slope_bound

/- English proof (translation)
Introduce `K _ _ _ w δ σ p q c0 c00 A A0 A0' P0 P1 P2 hc0 hc00 hA hA0 hA0' hP0 hP1 hP2 hcA hcA' hAA ub ua hu hub hua r hr`. Establish `vmul` using `Formalism.DivisionValues.ValuationRepresentative.vw_mul w`. Establish `vinv` using `Formalism.DivisionValues.ValuationRepresentative.vw_inv w`. Establish `n1 : (∏ j ∈ range q, ub j) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun j _ => (hu j).1`. Establish `n2 : (∏ i ∈ range p, ua i) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun j _ => (hu j).2`.

Establish `n3 : c0 / c00 ≠ 0` using `div_ne_zero hc0 hc00`. Establish `e1 : vw w r = (∑ j ∈ range q, vw w (ub j)) + (∑ i ∈ range p, vw w (ua i)) + (vw w c0 - vw w c00) + vw w P1 - vw w P2`. Rewrite using `[hr, vmul _ _ (mul_ne_zero (mul_ne_zero (mul_ne_zero n1 n2) n3) hP1) (inv_ne_zero hP2), vmul _ _ (mul_ne_zero (mul_ne_zero n1 n2) n3) hP1, vmul _ _ (mul_ne_zero n1 n2) n3, vmul _ _ n1 n2, vinv, div_eq_mul_inv, vmul _ _ hc0 (inv_ne_zero hc00), vinv, Formalism.PairingDivisionLocalB …`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : vw w (P0 * P1 * P2⁻¹) = vw w P0 + vw w P1 - vw w P2`.

Rewrite using `[vmul _ _ (mul_ne_zero hP0 hP1) (inv_ne_zero hP2), vmul _ _ hP0 hP1, vinv]`. Expand and normalize the polynomial expressions, which then agree. Establish `e3 : vw w P0 = vw w A - vw w A0`. Rewrite using `[← hAA, div_eq_mul_inv, vmul _ _ hA (inv_ne_zero hA0), vinv]`. Expand and normalize the polynomial expressions, which then agree.

Establish `b1 : ((∑ j ∈ range q, vw w (ub j) : ℤ) : ℝ) ≤ q * σ`. Use `push_cast`. Combine the equalities or inequalities in the displayed calculation. Establish `b2 : ((∑ i ∈ range p, vw w (ua i) : ℤ) : ℝ) ≤ p * σ`. Use `push_cast`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e1, e2, e3]`. Move the coercions through the operations in `at b1 b2 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem grid_square_bound_cm : SquareAtPlaceRatiosCM := by
  intro K _ _ _ w δ σ p q c0 c00 A A0 A0' P0 P1 P2 hc0 hc00 hA hA0 hA0' hP0 hP1 hP2 hcA hcA' hAA
    ub ua hu hub hua r hr
  have vmul := Formalism.DivisionValues.ValuationRepresentative.vw_mul w
  have vinv := Formalism.DivisionValues.ValuationRepresentative.vw_inv w
  have n1 : (∏ j ∈ range q, ub j) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => (hu j).1
  have n2 : (∏ i ∈ range p, ua i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => (hu j).2
  have n3 : c0 / c00 ≠ 0 := div_ne_zero hc0 hc00
  have e1 : vw w r = (∑ j ∈ range q, vw w (ub j)) + (∑ i ∈ range p, vw w (ua i)) +
      (vw w c0 - vw w c00) + vw w P1 - vw w P2 := by
    rw [hr, vmul _ _ (mul_ne_zero (mul_ne_zero (mul_ne_zero n1 n2) n3) hP1) (inv_ne_zero hP2),
      vmul _ _ (mul_ne_zero (mul_ne_zero n1 n2) n3) hP1, vmul _ _ (mul_ne_zero n1 n2) n3,
      vmul _ _ n1 n2, vinv, div_eq_mul_inv, vmul _ _ hc0 (inv_ne_zero hc00), vinv,
      Formalism.PairingDivisionLocalBalance.vw_prod w _ _ (fun j _ => (hu j).1), Formalism.PairingDivisionLocalBalance.vw_prod w _ _ (fun j _ => (hu j).2)]
    ring
  have e2 : vw w (P0 * P1 * P2⁻¹) = vw w P0 + vw w P1 - vw w P2 := by
    rw [vmul _ _ (mul_ne_zero hP0 hP1) (inv_ne_zero hP2), vmul _ _ hP0 hP1, vinv]; ring
  have e3 : vw w P0 = vw w A - vw w A0 := by
    rw [← hAA, div_eq_mul_inv, vmul _ _ hA (inv_ne_zero hA0), vinv]; ring
  have b1 : ((∑ j ∈ range q, vw w (ub j) : ℤ) : ℝ) ≤ q * σ := by
    push_cast
    calc ∑ j ∈ range q, (vw w (ub j) : ℝ) ≤ ∑ _j ∈ range q, σ :=
          Finset.sum_le_sum fun j hj => hub j (Finset.mem_range.1 hj)
      _ = q * σ := by simp
  have b2 : ((∑ i ∈ range p, vw w (ua i) : ℤ) : ℝ) ≤ p * σ := by
    push_cast
    calc ∑ j ∈ range p, (vw w (ua j) : ℝ) ≤ ∑ _j ∈ range p, σ :=
          Finset.sum_le_sum fun j hj => hua j (Finset.mem_range.1 hj)
      _ = p * σ := by simp
  rw [e1, e2, e3]
  push_cast at b1 b2 ⊢
  linarith

/- English proof (translation)
Introduce `K _ x y E lo hi e p q`. Establish `hf : ∀ s : ℤ, (if 1 ≤ s then (1 : K) else E s) * y (reflArg s) / x (reflArg s) = rhoAt x y E s`. Introduce `s`. Unfold `reflArg rhoAt`. Use `split_ifs`.

Rewrite using `[one_mul]`. Rewrite using `[mul_div_assoc]`. Unfold `Formalism.PairingDivisionLocalBalance.cmFactor`. Simplify using `only [hf]`. Rewrite using `[Fintype.prod_sum_type, Fintype.prod_sum_type]`.

Simplify using `only [Sum.elim_inl, Sum.elim_inr, if_true, sqArg, Bool.false_eq_true, if_false]`. Rewrite using `[Finset.prod_inv_distrib, ← mul_assoc]`. Rewrite using `[Finset.prod_coe_sort (Icc lo hi) (fun s => rhoAt x y E s), Finset.prod_coe_sort (Icc 1 p) (fun k : ℕ => rhoAt x y E (e + q - (k : ℤ) + 1)), Finset.prod_coe_sort (Icc 1 q) (fun k : ℕ => rhoAt x y E (e + (k : ℤ)))]`.
-/
theorem cm_factor_bound : SquareRatioProductFactor := by
  intro K _ x y E lo hi e p q
  have hf : ∀ s : ℤ, (if 1 ≤ s then (1 : K) else E s) * y (reflArg s) / x (reflArg s) = rhoAt x y E s := by
    intro s
    unfold reflArg rhoAt
    split_ifs
    · rw [one_mul]
    · rw [mul_div_assoc]
  unfold Formalism.PairingDivisionLocalBalance.cmFactor
  simp only [hf]
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, if_true, sqArg, Bool.false_eq_true, if_false]
  rw [Finset.prod_inv_distrib, ← mul_assoc]
  rw [Finset.prod_coe_sort (Icc lo hi) (fun s => rhoAt x y E s),
    Finset.prod_coe_sort (Icc 1 p) (fun k : ℕ => rhoAt x y E (e + q - (k : ℤ) + 1)),
    Finset.prod_coe_sort (Icc 1 q) (fun k : ℕ => rhoAt x y E (e + (k : ℤ)))]

/- English proof (translation)
Introduce `K _ J _ I _ al x u y`. Unfold `Formalism.PairingDivisionLocalBalance.cmFactor`. Rewrite using `[Fintype.prod_sigma]`.
-/
theorem cm_sigma_bound : ExplicitSizeInequality := by
  intro K _ J _ I _ al x u y
  unfold Formalism.PairingDivisionLocalBalance.cmFactor
  rw [Fintype.prod_sigma]

/- English proof (translation)
Introduce `K _ _ _ _ Sq m dl rr cf zA zA' yy S0 cc ee qq B Bδ Ex T I _ al x u y hne hyy hcc hsq hHt hδ hcm hEx0`. Establish `hEx : ∑ w ∈ T, lw w * (vw w (∏ ij, cf w ij) : ℝ) ≤ Ex`. Rewrite using `[Finset.sum_congr rfl (fun w hw => by rw [hcm w hw])]`. Conclude with `hEx0`. Establish `hQ1 : ∀ s, ∑ w ∈ T, lw w * (vw w (qq s : K) : ℝ) ≤ Real.log (qq s)` using `fun s => partial_nat K (qq s) T`.

Establish `hQ0 : ∀ s, 0 ≤ ∑ w ∈ T, lw w * (vw w (qq s : K) : ℝ)` using `fun s => Finset.sum_nonneg fun w _ => mul_nonneg (lw_nonneg' w) (by exact_mod_cast Formalism.DivisionValues.PlaceSumConjugation.vw_nat_nonneg (qq s) w)`. Establish `hAbs : ∀ z : K, HtLe (fun _ => 0) z B → ∑ w ∈ T, lw w * (vw w z : ℝ) ≤ B`. Introduce `z hz`. Use `le_trans (Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (le_abs_self _) (lw_nonneg' w)) ?_` and prove the remaining obligations. Use `partial_ht hz T` as an intermediate fact.

Simplify using `using this`. Establish `hone : ∀ ij, ∑ w ∈ T, lw w * ((vw w (zA ij) : ℝ) + (vw w (zA' ij) : ℝ) + 6 * dl w + yy ij * (2 * ∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ))) ≤ 2 * B + 6 * Bδ + 2 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s)`. Introduce `ij`. Establish `e1 : ∑ w ∈ T, lw w * ((vw w (zA ij) : ℝ) + (vw w (zA' ij) : ℝ) + 6 * dl w + yy ij * (2 * ∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ))) = (∑ w ∈ T, lw w * (vw w (zA ij) : ℝ)) + (∑ w ∈ T, lw w * (vw w (zA' ij) : ℝ)) + 6 * (∑ w ∈ T, lw w * dl w) + yy ij * (2 * ∑ s ∈ S0, (cc s : ℝ) …`. Establish `e2 : ∑ w ∈ T, lw w * ((yy ij : ℝ) * (2 * ∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ))) = yy ij * (2 * ∑ s ∈ S0, (cc s : ℝ) * ∑ w ∈ T, lw w * (vw w (qq s : K) : ℝ))`.

Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun w _ => by ring` and prove the remaining obligations. Establish `e3 : ∑ w ∈ T, lw w * (6 * dl w) = 6 * ∑ w ∈ T, lw w * dl w`. Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun w _ => by ring`.

Rewrite using `[← e2, ← e3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun w _ => by ring`. Establish `b3 : ∑ s ∈ S0, (cc s : ℝ) * ∑ w ∈ T, lw w * (vw w (qq s : K) : ℝ) ≤ ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s)` using `Finset.sum_le_sum fun s hs => mul_le_mul (by exact_mod_cast hcc s hs) (hQ1 s) (hQ0 s) (Nat.cast_nonneg _)`. Establish `b4 : 0 ≤ ∑ s ∈ S0, (cc s : ℝ) * ∑ w ∈ T, lw w * (vw w (qq s : K) : ℝ)` using `Finset.sum_nonneg fun s _ => mul_nonneg (Nat.cast_nonneg _) (hQ0 s)`. Establish `b5 : (yy ij : ℝ) * (2 * ∑ s ∈ S0, (cc s : ℝ) * ∑ w ∈ T, lw w * (vw w (qq s : K) : ℝ)) ≤ m * (2 * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s))` using `mul_le_mul (by exact_mod_cast hyy ij) (by linarith) (by linarith) (Nat.cast_nonneg _)`.

Rewrite using `[e1]`. Use `hAbs _ (hHt ij).1` as an intermediate fact. Use `hAbs _ (hHt ij).2` as an intermediate fact. Use `hδ T` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hr : ∀ w, (vw w (∏ ij, rr w ij) : ℝ) = ∑ ij, (vw w (rr w ij) : ℝ)`. Introduce `w`. Rewrite using `[Formalism.PairingDivisionLocalBalance.vw_prod w _ _ (fun ij _ => (hne w ij).1)]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `hc : ∀ w, (vw w (∏ ij, cf w ij) : ℝ) = ∑ ij, (vw w (cf w ij) : ℝ)`. Introduce `w`. Rewrite using `[Formalism.PairingDivisionLocalBalance.vw_prod w _ _ (fun ij _ => (hne w ij).2)]`. Use `push_cast`. Both sides reduce to the same expression.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun w hw => ?_` and prove the remaining obligations. Rewrite using `[hr, hc, ← mul_add, ← Finset.sum_add_distrib]`. Conclude with `mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ij _ => hsq w hw ij) (lw_nonneg' w)`. Use `_ = (∑ ij, ∑ w ∈ T, lw w * ((vw w (zA ij) : ℝ) + (vw w (zA' ij) : ℝ) + 6 * dl w + yy ij * (2 * ∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ)))) + ∑ w ∈ T, lw w * (vw w (∏ ij, cf w ij) : ℝ) := by`.

Rewrite using `[Finset.sum_add_distrib, Finset.sum_comm]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun w _ => by rw [Finset.mul_sum]`. Use `_ ≤ (∑ _ij : Fin m × Fin m, (2 * B + 6 * Bδ + 2 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s))) + Ex := add_le_add (Finset.sum_le_sum fun ij _ => hone ij) hEx`. Use `_ = (m : ℝ) ^ 2 * (2 * B + 6 * Bδ + 2 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s)) + Ex := by`.

Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem grid_bound_cm : GridHeightBoundCM := by
  intro K _ _ _ _ Sq m dl rr cf zA zA' yy S0 cc ee qq B Bδ Ex T I _ al x u y hne hyy hcc hsq hHt hδ hcm hEx0
  have hEx : ∑ w ∈ T, lw w * (vw w (∏ ij, cf w ij) : ℝ) ≤ Ex := by
    rw [Finset.sum_congr rfl (fun w hw => by rw [hcm w hw])]
    exact hEx0
  have hQ1 : ∀ s, ∑ w ∈ T, lw w * (vw w (qq s : K) : ℝ) ≤ Real.log (qq s) :=
    fun s => partial_nat K (qq s) T
  have hQ0 : ∀ s, 0 ≤ ∑ w ∈ T, lw w * (vw w (qq s : K) : ℝ) := fun s =>
    Finset.sum_nonneg fun w _ => mul_nonneg (lw_nonneg' w)
      (by exact_mod_cast Formalism.DivisionValues.PlaceSumConjugation.vw_nat_nonneg (qq s) w)
  have hAbs : ∀ z : K, HtLe (fun _ => 0) z B → ∑ w ∈ T, lw w * (vw w z : ℝ) ≤ B := by
    intro z hz
    refine le_trans (Finset.sum_le_sum fun w _ =>
      mul_le_mul_of_nonneg_left (le_abs_self _) (lw_nonneg' w)) ?_
    have := partial_ht hz T
    simpa using this
  have hone : ∀ ij, ∑ w ∈ T, lw w * ((vw w (zA ij) : ℝ) + (vw w (zA' ij) : ℝ) + 6 * dl w +
      yy ij * (2 * ∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ))) ≤
      2 * B + 6 * Bδ + 2 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s) := by
    intro ij
    have e1 : ∑ w ∈ T, lw w * ((vw w (zA ij) : ℝ) + (vw w (zA' ij) : ℝ) + 6 * dl w +
        yy ij * (2 * ∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ))) =
        (∑ w ∈ T, lw w * (vw w (zA ij) : ℝ)) + (∑ w ∈ T, lw w * (vw w (zA' ij) : ℝ)) +
        6 * (∑ w ∈ T, lw w * dl w) +
        yy ij * (2 * ∑ s ∈ S0, (cc s : ℝ) * ∑ w ∈ T, lw w * (vw w (qq s : K) : ℝ)) := by
      have e2 : ∑ w ∈ T, lw w * ((yy ij : ℝ) * (2 * ∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ))) =
          yy ij * (2 * ∑ s ∈ S0, (cc s : ℝ) * ∑ w ∈ T, lw w * (vw w (qq s : K) : ℝ)) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun w _ => by ring
      have e3 : ∑ w ∈ T, lw w * (6 * dl w) = 6 * ∑ w ∈ T, lw w * dl w := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun w _ => by ring
      rw [← e2, ← e3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun w _ => by ring
    have b3 : ∑ s ∈ S0, (cc s : ℝ) * ∑ w ∈ T, lw w * (vw w (qq s : K) : ℝ) ≤
        ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s) :=
      Finset.sum_le_sum fun s hs => mul_le_mul (by exact_mod_cast hcc s hs) (hQ1 s) (hQ0 s)
        (Nat.cast_nonneg _)
    have b4 : 0 ≤ ∑ s ∈ S0, (cc s : ℝ) * ∑ w ∈ T, lw w * (vw w (qq s : K) : ℝ) :=
      Finset.sum_nonneg fun s _ => mul_nonneg (Nat.cast_nonneg _) (hQ0 s)
    have b5 : (yy ij : ℝ) * (2 * ∑ s ∈ S0, (cc s : ℝ) * ∑ w ∈ T, lw w * (vw w (qq s : K) : ℝ)) ≤
        m * (2 * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s)) :=
      mul_le_mul (by exact_mod_cast hyy ij) (by linarith) (by linarith) (Nat.cast_nonneg _)
    rw [e1]
    have := hAbs _ (hHt ij).1
    have := hAbs _ (hHt ij).2
    have := hδ T
    linarith
  have hr : ∀ w, (vw w (∏ ij, rr w ij) : ℝ) = ∑ ij, (vw w (rr w ij) : ℝ) := by
    intro w
    rw [Formalism.PairingDivisionLocalBalance.vw_prod w _ _ (fun ij _ => (hne w ij).1)]; push_cast; rfl
  have hc : ∀ w, (vw w (∏ ij, cf w ij) : ℝ) = ∑ ij, (vw w (cf w ij) : ℝ) := by
    intro w
    rw [Formalism.PairingDivisionLocalBalance.vw_prod w _ _ (fun ij _ => (hne w ij).2)]; push_cast; rfl
  calc ∑ w ∈ T, lw w * (vw w (∏ ij, rr w ij) : ℝ)
      ≤ ∑ w ∈ T, (lw w * (∑ ij, ((vw w (zA ij) : ℝ) + (vw w (zA' ij) : ℝ) + 6 * dl w +
          yy ij * (2 * ∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ)))) +
          lw w * (vw w (∏ ij, cf w ij) : ℝ)) := by
        refine Finset.sum_le_sum fun w hw => ?_
        rw [hr, hc, ← mul_add, ← Finset.sum_add_distrib]
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ij _ => hsq w hw ij) (lw_nonneg' w)
    _ = (∑ ij, ∑ w ∈ T, lw w * ((vw w (zA ij) : ℝ) + (vw w (zA' ij) : ℝ) + 6 * dl w +
          yy ij * (2 * ∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ)))) +
          ∑ w ∈ T, lw w * (vw w (∏ ij, cf w ij) : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
        congr 1
        exact Finset.sum_congr rfl fun w _ => by rw [Finset.mul_sum]
    _ ≤ (∑ _ij : Fin m × Fin m, (2 * B + 6 * Bδ + 2 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s))) +
          Ex := add_le_add (Finset.sum_le_sum fun ij _ => hone ij) hEx
    _ = (m : ℝ) ^ 2 * (2 * B + 6 * Bδ + 2 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s)) + Ex := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/- English proof (translation)
The claim follows from `height_h0_of_grid grid_bound_general grid_function_bound`.
-/
theorem height_h0_bound : PassageSizeHypothesis := height_h0_of_grid grid_bound_general grid_function_bound

/- English proof (translation)
Introduce `K _ _ _ T Tw r h h1`. Use `symm`. Use `Finset.sum_subset h ?_` and prove the remaining obligations. Introduce `w hw hn`. Rewrite using `[h1 w hw hn, Formalism.DivisionValues.ValuationRepresentative.vw_one]`.

Simplify using the standard rewrite rules.
-/
theorem untwisted_grid_bound : UntwistedPlacesVanish := by
  intro K _ _ _ T Tw r h h1
  symm
  refine Finset.sum_subset h ?_
  intro w hw hn
  rw [h1 w hw hn, Formalism.DivisionValues.ValuationRepresentative.vw_one]
  simp

/- English proof (translation)
Introduce `K W κ _ _ _ _ _ _ _ _ _ _ D hD XE kap b' X' hXE hkap hX' R M Ψ T a dF EM hInf BF p2 bb hR hM hM0 hΨ hincl hEM hh hBF Tw Sq m dl rr cf zA zA' yy S0 cc ee qq B Bδ Ex I _ al x u y ha hsub hun hne hyy hcc hsq hHt hδ hcm hEx hsize`. Establish `hg` using `grid_bound_cm K Sq m dl rr cf zA zA' yy S0 cc ee qq B Bδ Ex Tw I al x u y hne hyy hcc hsq hHt hδ hcm hEx`. Rewrite `hg` using `[← untwisted_grid_bound K T Tw (fun w => ∏ ij, rr w ij) hsub (fun w hw hn => Finset.prod_eq_one fun ij _ => hun w hw hn ij)]`. Establish `h` using `grid_function_bound K W κ D hD XE kap b' X' hXE hkap hX' R M Ψ T a (fun w => ∏ ij, rr w ij) dF EM hInf _ BF hR hM hM0 hΨ hincl ha hEM hh hg hBF`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem height_h0_bound_cm : PassageSizeHypothesisCM := by
  intro K W κ _ _ _ _ _ _ _ _ _ _ D hD XE kap b' X' hXE hkap hX' R M Ψ T a dF EM hInf BF p2 bb
    hR hM hM0 hΨ hincl hEM hh hBF Tw Sq m dl rr cf zA zA' yy S0 cc ee qq B Bδ Ex I _ al x u y
    ha hsub hun hne hyy hcc hsq hHt hδ hcm hEx hsize
  have hg := grid_bound_cm K Sq m dl rr cf zA zA' yy S0 cc ee qq B Bδ Ex Tw I al x u y
    hne hyy hcc hsq hHt hδ hcm hEx
  rw [← untwisted_grid_bound K T Tw (fun w => ∏ ij, rr w ij) hsub
    (fun w hw hn => Finset.prod_eq_one fun ij _ => hun w hw hn ij)] at hg
  have h := grid_function_bound K W κ D hD XE kap b' X' hXE hkap hX' R M Ψ T a (fun w => ∏ ij, rr w ij) dF EM hInf
    _ BF hR hM hM0 hΨ hincl ha hEM hh hg hBF
  linarith

/- English proof (translation)
Introduce `Sq m N S0 ee qq B BN0 Bδ BF EM hInf f bb LL CB CN Cδ Sg pM pI pB hbb h1 hB hN hδ hS hSg hEM hI hBF`. Establish `hm : (0 : ℝ) ≤ m` using `Nat.cast_nonneg _`. Establish `hNn : (0 : ℝ) ≤ N` using `Nat.cast_nonneg _`. Establish `a1 : 2 * (2 + 8 * (N : ℝ)) * B ≤ 2 * (2 + 8 * N) * (CB * f * bb * LL)` using `mul_le_mul_of_nonneg_left hB (by positivity)`. Establish `a2 : 2 * (N : ℝ) * (BN0 + 1) ≤ 2 * N * ((CN + 1) * (f * bb * LL))` using `mul_le_mul_of_nonneg_left (by linarith) (by positivity)`.

Establish `a3 : 4 * (m : ℝ) * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s) ≤ 4 * m * (Sg * bb)` using `mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hSg (sub_nonneg.2 hbb)]) (by positivity)`. Establish `g : gridBudget m N B BN0 Bδ S0 ee qq ≤ (m : ℝ) ^ 2 * (2 * (2 + 8 * N) * (CB * f * bb * LL) + 2 * N * ((CN + 1) * (f * bb * LL)) + 6 * (Cδ * f * bb * LL) + 4 * m * (Sg * bb))`. Unfold `gridBudget`. Conclude with `mul_le_mul_of_nonneg_left (by linarith) (by positivity)`. Combine the equalities or inequalities in the displayed calculation.

Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = _ := by ring`.
-/
theorem j3P2 : UnitRatioAtPlace := by
  intro Sq m N S0 ee qq B BN0 Bδ BF EM hInf f bb LL CB CN Cδ Sg pM pI pB hbb h1 hB hN hδ hS hSg
    hEM hI hBF
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hNn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have a1 : 2 * (2 + 8 * (N : ℝ)) * B ≤ 2 * (2 + 8 * N) * (CB * f * bb * LL) :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have a2 : 2 * (N : ℝ) * (BN0 + 1) ≤ 2 * N * ((CN + 1) * (f * bb * LL)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have a3 : 4 * (m : ℝ) * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s) ≤ 4 * m * (Sg * bb) :=
    mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hSg (sub_nonneg.2 hbb)]) (by positivity)
  have g : gridBudget m N B BN0 Bδ S0 ee qq ≤ (m : ℝ) ^ 2 * (2 * (2 + 8 * N) * (CB * f * bb * LL) +
      2 * N * ((CN + 1) * (f * bb * LL)) + 6 * (Cδ * f * bb * LL) + 4 * m * (Sg * bb)) := by
    unfold gridBudget
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  calc EM + hInf + 2 * (gridBudget m N B BN0 Bδ S0 ee qq + BF)
      ≤ pM * bb + pI * bb + 2 * ((m : ℝ) ^ 2 * (2 * (2 + 8 * N) * (CB * f * bb * LL) +
        2 * N * ((CN + 1) * (f * bb * LL)) + 6 * (Cδ * f * bb * LL) + 4 * m * (Sg * bb)) + pB * bb) := by
        linarith
    _ = _ := by ring

/- English proof (translation)
Introduce `K _ _ _ _ Sq m N dl S Se N0 rr zA zA' zT zTd gT ch aa aa' dd hh pp qp ep yT EE c0 c00 AA ub ua S0 cc ee qq B BN0 Bδ W0 hdl hS hSe hrk hddN hyy hcc hrr hzT hzTd hyE hzA hc hu h2 hE hC hAA hU hr hHA hHT hHTd hBN0 hBδ`. Use `grid_bound_general K Sq m N dl S Se N0 rr zA zA' zT zTd gT ch dd hh (fun ij => pp ij + qp ij) S0 cc ee qq B BN0 Bδ W0 hdl hS hSe hrr (fun ij => (hrk ij).2.2.1) hddN hyy hcc ?_ hHA hHT hHTd hBN0 hBδ` and prove the remaining obligations. Introduce `w hw ij`. Take `⟨r1, r2, r3, r4, r5⟩` from `hrk ij`. Conclude with `grid_square_bound K w (aa ij) (aa' ij) (dd ij) (hh ij) (pp ij) (qp ij) (ep ij) r1 r2 r3 r4 r5 (zT ij) (zTd ij (ch w)) (yT w ij) (EE w ij) (fun s => gT ij s w) S Se N0 (dl w) (2 * ∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ)) (fun l hl => (hS l hl).2) (fun s => ⟨hzT ij s, hzTd ij …`.
-/
theorem grid_squares_bound_alt : GridSquaresHeightBound := by
  intro K _ _ _ _ Sq m N dl S Se N0 rr zA zA' zT zTd gT ch aa aa' dd hh pp qp ep yT EE c0 c00 AA ub ua
    S0 cc ee qq B BN0 Bδ W0 hdl hS hSe hrk hddN hyy hcc hrr hzT hzTd hyE hzA hc hu h2 hE hC hAA hU hr
    hHA hHT hHTd hBN0 hBδ
  refine grid_bound_general K Sq m N dl S Se N0 rr zA zA' zT zTd gT ch dd hh (fun ij => pp ij + qp ij) S0 cc ee qq
    B BN0 Bδ W0 hdl hS hSe hrr (fun ij => (hrk ij).2.2.1) hddN hyy hcc ?_ hHA hHT hHTd hBN0 hBδ
  intro w hw ij
  obtain ⟨r1, r2, r3, r4, r5⟩ := hrk ij
  exact grid_square_bound K w (aa ij) (aa' ij) (dd ij) (hh ij) (pp ij) (qp ij) (ep ij) r1 r2 r3 r4 r5
    (zT ij) (zTd ij (ch w)) (yT w ij) (EE w ij) (fun s => gT ij s w) S Se N0 (dl w)
    (2 * ∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ)) (fun l hl => (hS l hl).2)
    (fun s => ⟨hzT ij s, hzTd ij (ch w) s, (hyE w ij s).1, (hyE w ij s).2⟩)
    (h2 w hw ij) (hE w hw ij) (c0 w ij) (c00 w ij) (AA w ij) (zA ij) (zA' ij)
    (hc w ij).1 (hc w ij).2.1 (hc w ij).2.2 (hzA ij).1 (hzA ij).2 (hC w hw ij).1 (hC w hw ij).2
    (hAA w hw ij) (ub w ij) (ua w ij) (hu w ij) (fun j => (hU w hw ij j).1)
    (fun j => (hU w hw ij j).2) (rr w ij) (hr w hw ij)

/- English proof (translation)
Introduce `K F _ _ ι L L0 c u cb u0 p q e Ω Ω' hΩ hΩ' hL h1 h2 h3 h4 x y E r c0 c00 ub ua hr hc0 hc00 hub hua hP1 hP2`. Apply `ι.injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, map_mul, map_mul, map_inv₀, map_div₀, map_prod, map_prod, map_prod, map_prod, hr, hc0, hc00, Formalism.ValuationGridEstimates.tower_ratio_bound F L L0 c u cb u0 p q e Ω Ω' hΩ hΩ' hL h1 h2 h3 h4, Finset.prod_congr rfl (fun j hj => hub j (Finset.mem_range.1 hj)), …`.
-/
theorem tower_height_bound : CoefficientRatioTowerFormula := by
  intro K F _ _ ι L L0 c u cb u0 p q e Ω Ω' hΩ hΩ' hL h1 h2 h3 h4 x y E r c0 c00 ub ua hr hc0 hc00
    hub hua hP1 hP2
  apply ι.injective
  rw [map_mul, map_mul, map_mul, map_mul, map_inv₀, map_div₀, map_prod, map_prod, map_prod, map_prod,
    hr, hc0, hc00, Formalism.ValuationGridEstimates.tower_ratio_bound F L L0 c u cb u0 p q e Ω Ω' hΩ hΩ' hL h1 h2 h3 h4,
    Finset.prod_congr rfl (fun j hj => hub j (Finset.mem_range.1 hj)),
    Finset.prod_congr rfl (fun i hi => hua i (Finset.mem_range.1 hi)),
    Finset.prod_congr rfl (fun k hk => hP1 k (Finset.mem_Icc.1 hk).1 (Finset.mem_Icc.1 hk).2),
    Finset.prod_congr rfl (fun k hk => hP2 k (Finset.mem_Icc.1 hk).1 (Finset.mem_Icc.1 hk).2)]

/- English proof (translation)
Introduce `K F _ _ ι Ac Ω2 L L0 lo hi hAc hΩ x y E A A0 hA hA0 hρ`. Apply `ι.injective` to reduce the goal to its premises. Rewrite using `[map_div₀, map_prod, hA, hA0, Formalism.ValuationGridEstimates.norm_ratio_bound F Ac Ω2 L L0 lo hi hAc hΩ, Finset.prod_congr rfl hρ]`.
-/
theorem norm_ratio_bound_alt : CoefficientFieldNormRatio := by
  intro K F _ _ ι Ac Ω2 L L0 lo hi hAc hΩ x y E A A0 hA hA0 hρ
  apply ι.injective
  rw [map_div₀, map_prod, hA, hA0, Formalism.ValuationGridEstimates.norm_ratio_bound F Ac Ω2 L L0 lo hi hAc hΩ,
    Finset.prod_congr rfl hρ]

/- English proof (translation)
Introduce `K _ _ _ w Sq S0 ζ Ga Ga' Gb Gb' cc qq hζ hζ0 hq hGa hGb`. Establish `vmul` using `Formalism.DivisionValues.ValuationRepresentative.vw_mul w`. Establish `vinv` using `Formalism.DivisionValues.ValuationRepresentative.vw_inv w`. Establish `hq0 : ∀ s ∈ S0, ((qq s : K) ^ cc s) ≠ 0` using `fun s hs => pow_ne_zero _ (by exact_mod_cast (hq s hs).ne')`. Establish `nGa : ∀ s ∈ S0, Ga s ≠ 0 ∧ Ga' s ≠ 0`.

Introduce `s hs`. Use `hq0 s hs` as an intermediate fact. Rewrite `this` using `[← (hGa s hs).2.2]`. Conclude with `⟨left_ne_zero_of_mul this, right_ne_zero_of_mul this⟩`. Establish `nGb : ∀ s ∈ S0, Gb s ≠ 0 ∧ Gb' s ≠ 0`.

Introduce `s hs`. Use `hq0 s hs` as an intermediate fact. Rewrite `this` using `[← (hGb s hs).2.2]`. Conclude with `⟨left_ne_zero_of_mul this, right_ne_zero_of_mul this⟩`. Set `M : K → Multiplicative ℝ` to `fun z => Multiplicative.ofAdd ((vw w z : ℤ) : ℝ)`.

Establish `Mmul : ∀ a b : K, a ≠ 0 → b ≠ 0 → M (a * b) = M a * M b`. Introduce `a b ha hb`. Simplify using `only [M, vmul a b ha hb, Int.cast_add, ofAdd_add]`. Establish `Mpow : ∀ (a : K) (n : ℕ), a ≠ 0 → M (a ^ n) = M a ^ n`. Introduce `a n ha`.

Proceed by induction on `n with`. Consider the case `zero => simp [M, Formalism.DivisionValues.ValuationRepresentative.vw_one]`. Consider the case `succ n ih => rw [pow_succ, pow_succ, Mmul _ _ (pow_ne_zero _ ha) ha, ih]`. Establish `key` using `(Formalism.ValuationGridEstimates.lemma_u_units (Multiplicative ℝ) (fun z => Multiplicative.toAdd z) (fun _ _ => rfl) Sq S0 (M ζ) (fun s => M (Ga s)) (fun s => M (Ga' s)) (fun s => M (Gb s)) (fun s => M (Gb' s)) (fun s => M (qq s : K)) cc (by simp [M, hζ0]) (fun s hs => ⟨Int.cast …`. Rewrite using `[← Mmul _ _ (nGa s hs).1 (nGa s hs).2, (hGa s hs).2.2, Mpow _ _ (by exact_mod_cast (hq s hs).ne')]⟩)`.

Use the proof step `(fun s hs => ⟨Int.cast_nonneg (R := ℝ) (hGb s hs).1, Int.cast_nonneg (R := ℝ) (hGb s hs).2.1, by`. Rewrite using `[← Mmul _ _ (nGb s hs).1 (nGb s hs).2, (hGb s hs).2.2, Mpow _ _ (by exact_mod_cast (hq s hs).ne')]⟩)).2`. Establish `e1 : M (ζ * ∏ s ∈ S0, Ga s / Gb s) = M ζ * ∏ s ∈ S0, M (Ga s) / M (Gb s)`. Establish `hp : ∀ T : Finset Sq, T ⊆ S0 → (∏ s ∈ T, Ga s / Gb s ≠ 0 ∧ M (∏ s ∈ T, Ga s / Gb s) = ∏ s ∈ T, M (Ga s) / M (Gb s))`. Introduce `T`.

Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => intro _`. Simplify using `[M, Formalism.DivisionValues.ValuationRepresentative.vw_one]`. Consider the case `insert i s hi ih`. Introduce `hT`.

Establish `hi0 : i ∈ S0` using `hT (Finset.mem_insert_self _ _)`. Take `⟨i1, i2⟩` from `ih (fun t ht => hT (Finset.mem_insert_of_mem ht))`. Establish `hd : Ga i / Gb i ≠ 0` using `div_ne_zero (nGa i hi0).1 (nGb i hi0).1`. Use `⟨by rw [Finset.prod_insert hi]; exact mul_ne_zero hd i1, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.prod_insert hi, Finset.prod_insert hi, Mmul _ _ hd i1, i2, div_eq_mul_inv, Mmul _ _ (nGa i hi0).1 (inv_ne_zero (nGb i hi0).1)]`.

Use `congr 1`. Simplify using `only [M, vinv, Int.cast_neg, ofAdd_neg, div_eq_mul_inv]`. Rewrite using `[Mmul _ _ hζ (hp S0 (Finset.Subset.refl _)).1, (hp S0 (Finset.Subset.refl _)).2]`. Rewrite `key` using `[← e1]`. Establish `e2 : ∑ s ∈ S0, 2 * (cc s : ℝ) * (vw w (qq s : K) : ℝ) = 2 * ∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ)`.

Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring`. Rewrite using `[← e2]`. Conclude with `key`.
-/
theorem grid_lemma_U : HeightBoundedDenominators := by
  intro K _ _ _ w Sq S0 ζ Ga Ga' Gb Gb' cc qq hζ hζ0 hq hGa hGb
  have vmul := Formalism.DivisionValues.ValuationRepresentative.vw_mul w
  have vinv := Formalism.DivisionValues.ValuationRepresentative.vw_inv w
  have hq0 : ∀ s ∈ S0, ((qq s : K) ^ cc s) ≠ 0 := fun s hs =>
    pow_ne_zero _ (by exact_mod_cast (hq s hs).ne')
  have nGa : ∀ s ∈ S0, Ga s ≠ 0 ∧ Ga' s ≠ 0 := by
    intro s hs
    have := hq0 s hs
    rw [← (hGa s hs).2.2] at this
    exact ⟨left_ne_zero_of_mul this, right_ne_zero_of_mul this⟩
  have nGb : ∀ s ∈ S0, Gb s ≠ 0 ∧ Gb' s ≠ 0 := by
    intro s hs
    have := hq0 s hs
    rw [← (hGb s hs).2.2] at this
    exact ⟨left_ne_zero_of_mul this, right_ne_zero_of_mul this⟩
  let M : K → Multiplicative ℝ := fun z => Multiplicative.ofAdd ((vw w z : ℤ) : ℝ)
  have Mmul : ∀ a b : K, a ≠ 0 → b ≠ 0 → M (a * b) = M a * M b := by
    intro a b ha hb
    simp only [M, vmul a b ha hb, Int.cast_add, ofAdd_add]
  have Mpow : ∀ (a : K) (n : ℕ), a ≠ 0 → M (a ^ n) = M a ^ n := by
    intro a n ha
    induction n with
    | zero => simp [M, Formalism.DivisionValues.ValuationRepresentative.vw_one]
    | succ n ih => rw [pow_succ, pow_succ, Mmul _ _ (pow_ne_zero _ ha) ha, ih]
  have key := (Formalism.ValuationGridEstimates.lemma_u_units (Multiplicative ℝ) (fun z => Multiplicative.toAdd z) (fun _ _ => rfl)
    Sq S0 (M ζ) (fun s => M (Ga s)) (fun s => M (Ga' s)) (fun s => M (Gb s)) (fun s => M (Gb' s))
    (fun s => M (qq s : K)) cc (by simp [M, hζ0])
    (fun s hs => ⟨Int.cast_nonneg (R := ℝ) (hGa s hs).1, Int.cast_nonneg (R := ℝ) (hGa s hs).2.1, by
      rw [← Mmul _ _ (nGa s hs).1 (nGa s hs).2, (hGa s hs).2.2,
        Mpow _ _ (by exact_mod_cast (hq s hs).ne')]⟩)
    (fun s hs => ⟨Int.cast_nonneg (R := ℝ) (hGb s hs).1, Int.cast_nonneg (R := ℝ) (hGb s hs).2.1, by
      rw [← Mmul _ _ (nGb s hs).1 (nGb s hs).2, (hGb s hs).2.2,
        Mpow _ _ (by exact_mod_cast (hq s hs).ne')]⟩)).2
  have e1 : M (ζ * ∏ s ∈ S0, Ga s / Gb s) = M ζ * ∏ s ∈ S0, M (Ga s) / M (Gb s) := by
    have hp : ∀ T : Finset Sq, T ⊆ S0 →
        (∏ s ∈ T, Ga s / Gb s ≠ 0 ∧ M (∏ s ∈ T, Ga s / Gb s) = ∏ s ∈ T, M (Ga s) / M (Gb s)) := by
      intro T
      classical
      induction T using Finset.induction_on with
      | empty => intro _; simp [M, Formalism.DivisionValues.ValuationRepresentative.vw_one]
      | insert i s hi ih =>
        intro hT
        have hi0 : i ∈ S0 := hT (Finset.mem_insert_self _ _)
        obtain ⟨i1, i2⟩ := ih (fun t ht => hT (Finset.mem_insert_of_mem ht))
        have hd : Ga i / Gb i ≠ 0 := div_ne_zero (nGa i hi0).1 (nGb i hi0).1
        refine ⟨by rw [Finset.prod_insert hi]; exact mul_ne_zero hd i1, ?_⟩
        rw [Finset.prod_insert hi, Finset.prod_insert hi, Mmul _ _ hd i1, i2, div_eq_mul_inv,
          Mmul _ _ (nGa i hi0).1 (inv_ne_zero (nGb i hi0).1)]
        congr 1
        simp only [M, vinv, Int.cast_neg, ofAdd_neg, div_eq_mul_inv]
    rw [Mmul _ _ hζ (hp S0 (Finset.Subset.refl _)).1, (hp S0 (Finset.Subset.refl _)).2]
  rw [← e1] at key
  have e2 : ∑ s ∈ S0, 2 * (cc s : ℝ) * (vw w (qq s : K) : ℝ) =
      2 * ∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
  rw [← e2]
  exact key

open Classical in

def fR {K : Type} [Field K] [NumberField K] (w : Pl K) (a : K) : WithTop ℝ :=
  if a = 0 then ⊤ else (((vw w a : ℤ) : ℝ) : WithTop ℝ)

/- English proof (translation)
Unfold `fR`. Conclude with `if_neg ha`.
-/
theorem fR_ne {K : Type} [Field K] [NumberField K] (w : Pl K) (a : K) (ha : a ≠ 0) :
    fR w a = (((vw w a : ℤ) : ℝ) : WithTop ℝ) := by
  unfold fR
  exact if_neg ha

/- English proof (translation)
Unfold `fR`. Conclude with `if_pos rfl`.
-/
theorem fR_zero {K : Type} [Field K] [NumberField K] (w : Pl K) : fR w (0 : K) = ⊤ := by
  unfold fR
  exact if_pos rfl

def valR {K : Type} [Field K] [NumberField K] [StarRing K] (w : Pl K) : AddValuation K (WithTop ℝ) :=
  AddValuation.of (fR w) (fR_zero w)
    (by rw [fR_ne w 1 one_ne_zero, Formalism.DivisionValues.ValuationRepresentative.vw_one]; simp)
    (by
      intro x y
      by_cases hx : x = 0
      · subst hx; simp
      by_cases hy : y = 0
      · subst hy; simp
      by_cases hxy : x + y = 0
      · rw [hxy]; simp [fR]
      rw [fR_ne w x hx, fR_ne w y hy, fR_ne w _ hxy, ← WithTop.coe_min, WithTop.coe_le_coe]
      have h := Formalism.PairingDivisionLocalBalance.valuation_add K w x y hx hy hxy
      rcases min_le_iff.mp h with h | h
      · exact le_trans (min_le_left _ _) (by exact_mod_cast h)
      · exact le_trans (min_le_right _ _) (by exact_mod_cast h))
    (by
      intro x y
      by_cases hx : x = 0
      · subst hx; simp [fR]
      by_cases hy : y = 0
      · subst hy; simp [fR]
      rw [fR_ne w x hx, fR_ne w y hy, fR_ne w _ (mul_ne_zero hx hy), Formalism.DivisionValues.ValuationRepresentative.vw_mul w x y hx hy,
        ← WithTop.coe_add]
      congr 1
      push_cast
      ring)

/- English proof (translation)
Establish `h : valR w a = fR w a` using `AddValuation.of_apply _`. Rewrite using `[h, fR_ne w a ha]`.
-/
theorem valR_ne {K : Type} [Field K] [NumberField K] [StarRing K] (w : Pl K) (a : K) (ha : a ≠ 0) :
    valR w a = (((vw w a : ℤ) : ℝ) : WithTop ℝ) := by
  have h : valR w a = fR w a := AddValuation.of_apply _
  rw [h, fR_ne w a ha]

/- English proof (translation)
Distinguish the cases in `ha : a = 0`. Substitute `ha` using the available equality. Rewrite using `[AddValuation.map_zero]`. Conclude with `le_top`. Rewrite using `[valR_ne w a ha, WithTop.coe_le_coe]`.

Conclude with `h.resolve_left ha`.
-/
theorem valR_ge {K : Type} [Field K] [NumberField K] [StarRing K] (w : Pl K) (a : K) (t : ℝ)
    (h : a = 0 ∨ t ≤ (vw w a : ℝ)) : (t : WithTop ℝ) ≤ valR w a := by
  by_cases ha : a = 0
  · subst ha; rw [AddValuation.map_zero]; exact le_top
  · rw [valR_ne w a ha, WithTop.coe_le_coe]
    exact h.resolve_left ha

/- English proof (translation)
Introduce `K _ _ _ w ι κ _ X z z' gm c0 δ hc0 hz hi hi' hg A A' hA hA' hA0 hA'0`. Establish `hconj : ∀ x : K, valR w ((starRingEnd K) x) = valR (Formalism.DivisionValues.conjPl w) x`. Introduce `x`. Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[valR_ne _ _ hx, valR_ne _ _ (by simpa using hx), starRingEnd_apply, Formalism.DivisionValues.ValuationRepresentative.vw_star]`. Take `⟨k1, k2, k3, k4⟩` from `Formalism.ValuationGridEstimates.lemma_c_gauss_sum K (valR w) (valR (Formalism.DivisionValues.conjPl w)) (starRingEnd K) hconj ι κ X z z' gm c0 δ hc0 hz (fun x hx k => ⟨valR_ge _ _ _ ((hi x hx k).imp id (·.1)), valR_ge _ _ _ ((hi x hx k).imp id (·.2)), valR_ge _ _ _ ((hi' x hx k) …`. Establish `eA : (∑ x ∈ X, ∑ k, ∑ l, z x k * (starRingEnd K) (z x l) * gm x k l) = A`. Rewrite using `[hA]`.

Both sides reduce to the same expression. Establish `eA' : (∑ x ∈ X, ∑ k, ∑ l, z' x k * (starRingEnd K) (z' x l) * gm x k l) = A'`. Rewrite using `[hA']`. Both sides reduce to the same expression. Rewrite `k1`, `k3` using `[eA]`.

Rewrite `k2`, `k4` using `[eA']`. Rewrite `k1` using `[valR_ne _ _ hc0, valR_ne _ _ hA0, ← WithTop.coe_add, WithTop.coe_le_coe]`. Rewrite `k2` using `[valR_ne _ _ (inv_ne_zero hc0), valR_ne _ _ hA'0, ← WithTop.coe_add, WithTop.coe_le_coe, Formalism.DivisionValues.ValuationRepresentative.vw_inv]`. Rewrite `k3` using `[valR_ne _ _ hA0, WithTop.coe_le_coe]`. Rewrite `k4` using `[valR_ne _ _ hA'0, WithTop.coe_le_coe]`.

Move the coercions through the operations in `at k2`. Conclude with `⟨k1, k2, k3, k4⟩`.
-/
theorem grid_lemma_C : ScaledCoordinatesValuationLemma := by
  intro K _ _ _ w ι κ _ X z z' gm c0 δ hc0 hz hi hi' hg A A' hA hA' hA0 hA'0
  have hconj : ∀ x : K, valR w ((starRingEnd K) x) = valR (Formalism.DivisionValues.conjPl w) x := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp
    · rw [valR_ne _ _ hx, valR_ne _ _ (by simpa using hx), starRingEnd_apply,
        Formalism.DivisionValues.ValuationRepresentative.vw_star]
  obtain ⟨k1, k2, k3, k4⟩ := Formalism.ValuationGridEstimates.lemma_c_gauss_sum K (valR w) (valR (Formalism.DivisionValues.conjPl w)) (starRingEnd K)
    hconj ι κ X z z' gm c0 δ hc0 hz
    (fun x hx k => ⟨valR_ge _ _ _ ((hi x hx k).imp id (·.1)), valR_ge _ _ _ ((hi x hx k).imp id (·.2)),
      valR_ge _ _ _ ((hi' x hx k).imp id (·.1)), valR_ge _ _ _ ((hi' x hx k).imp id (·.2))⟩)
    (fun x hx k l => valR_ge _ _ _ (hg x hx k l))
  have eA : (∑ x ∈ X, ∑ k, ∑ l, z x k * (starRingEnd K) (z x l) * gm x k l) = A := by
    rw [hA]; rfl
  have eA' : (∑ x ∈ X, ∑ k, ∑ l, z' x k * (starRingEnd K) (z' x l) * gm x k l) = A' := by
    rw [hA']; rfl
  rw [eA] at k1 k3
  rw [eA'] at k2 k4
  rw [valR_ne _ _ hc0, valR_ne _ _ hA0, ← WithTop.coe_add, WithTop.coe_le_coe] at k1
  rw [valR_ne _ _ (inv_ne_zero hc0), valR_ne _ _ hA'0, ← WithTop.coe_add, WithTop.coe_le_coe,
    Formalism.DivisionValues.ValuationRepresentative.vw_inv] at k2
  rw [valR_ne _ _ hA0, WithTop.coe_le_coe] at k3
  rw [valR_ne _ _ hA'0, WithTop.coe_le_coe] at k4
  push_cast at k2
  exact ⟨k1, k2, k3, k4⟩

end Formalism.AtG
