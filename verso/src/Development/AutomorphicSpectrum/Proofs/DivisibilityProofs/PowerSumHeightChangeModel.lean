import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.MassFormulaConjugationAction
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DegreeEqCardToMultiset
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FractionRingRingEquiv
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsMultiProjPrimeExtTo
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.UniformizerDivisorCycleNumberStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagM3PadicGlobalStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PowerSumsVanishAtPlacesStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelGeometricGenericNumberStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootPowerSumMixedExpansionStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PowerSumTermDiscreteValuationStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsometricFamilyIntersectionEqStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.Prop6Model

/- English proof (translation)
Take `⟨hadd, hsmul, -, -, hren⟩` from `arNum_linear_arList_symm.1 K ι I P (σ ⊕ σ) (Sum.elim A A')`. Establish `h : mixDiff F = rename Sum.inl F + C (-1) * rename Sum.inr F`. Simplify using `[mixDiff, sub_eq_add_neg]`. Rewrite using `[h, hadd, hsmul, hren, hren, Sum.elim_comp_inl, Sum.elim_comp_inr]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem arNum_mixDiff {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι ℤ)) {σ : Type}
    (A A' : σ → HermLine ι) (F : MvPolynomial σ ℝ) :
    arNum I P (Sum.elim A A') (mixDiff F) = arNum I P A F - arNum I P A' F := by
  obtain ⟨hadd, hsmul, -, -, hren⟩ := arNum_linear_arList_symm.1 K ι I P (σ ⊕ σ) (Sum.elim A A')
  have h : mixDiff F = rename Sum.inl F + C (-1) * rename Sum.inr F := by
    simp [mixDiff, sub_eq_add_neg]
  rw [h, hadd, hsmul, hren, hren, Sum.elim_comp_inl, Sum.elim_comp_inr]
  ring

/- English proof (translation)
Establish `hc : 1 ≤ Fintype.card Ψ` using `Fintype.card_pos_iff.2 ⟨τ⟩`. Establish `h1 : N * (N - 1) / 2 ≤ dimFl Ψ N`. Unfold `dimFl`. Conclude with `Nat.le_mul_of_pos_left _ hc`. Establish `h2 : N ≤ N * (N - 1) / 2 + 1`.

Break down `N with _ | _ | n` into its components or cases. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish `h3 : (n + 1) * 2 ≤ (n + 1 + 1) * (n + 1 + 1 - 1)`. Rewrite using `[Nat.add_sub_cancel]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `h4` using `(Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 h3`. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers.
-/
theorem le_dimFl_succ (Ψ : Type) [Fintype Ψ] (τ : Ψ) (N : ℕ) : N ≤ dimFl Ψ N + 1 := by
  have hc : 1 ≤ Fintype.card Ψ := Fintype.card_pos_iff.2 ⟨τ⟩
  have h1 : N * (N - 1) / 2 ≤ dimFl Ψ N := by
    unfold dimFl
    exact Nat.le_mul_of_pos_left _ hc
  have h2 : N ≤ N * (N - 1) / 2 + 1 := by
    rcases N with _ | _ | n
    · simp
    · simp
    · have h3 : (n + 1) * 2 ≤ (n + 1 + 1) * (n + 1 + 1 - 1) := by
        rw [Nat.add_sub_cancel]
        nlinarith
      have h4 := (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 h3
      omega
  omega

variable {Ψ : Type} {N : ℕ}

/- English proof (translation)
Consider the cases of `l with`. Consider the case `inl τ`. Use `IsHomogeneous.sum _ _ _ fun i _ => ?_` and prove the remaining obligations. Simplify using `using (isHomogeneous_X ℝ (τ, i)).pow m`. Consider the case `inr τ`.

Use `IsHomogeneous.sum _ _ _ fun i _ => ?_` and prove the remaining obligations. Simplify using `using ((isHomogeneous_X ℝ (τ, i)).neg).pow m`.
-/
theorem liePs_isHomogeneous (j m : ℕ) (l : Ψ ⊕ Ψ) :
    (liePs j m l : MvPolynomial (Ψ × Fin N) ℝ).IsHomogeneous m := by
  cases l with
  | inl τ =>
    refine IsHomogeneous.sum _ _ _ fun i _ => ?_
    simpa using (isHomogeneous_X ℝ (τ, i)).pow m
  | inr τ =>
    refine IsHomogeneous.sum _ _ _ fun i _ => ?_
    simpa using ((isHomogeneous_X ℝ (τ, i)).neg).pow m

/- English proof (translation)
Unfold `bracket`. Establish `h` using `(isHomogeneous_C (Ψ × Fin N) (k : ℝ)).mul (IsHomogeneous.sum Finset.univ (fun τ' => C (co φ p k (Sum.inl τ) τ') * liePs j (k - 1) τ') (k - 1) fun τ' _ => by`. Simplify using `using (isHomogeneous_C (Ψ × Fin N) (co φ p k (Sum.inl τ) τ')).mul (liePs_isHomogeneous (N := N) j (k - 1) τ'))`. Simplify using `using h`.
-/
theorem bracket_isHomogeneous [Fintype Ψ] [DecidableEq Ψ] (j : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (p k : ℕ) (τ : Ψ) :
    (bracket j φ p k τ : MvPolynomial (Ψ × Fin N) ℝ).IsHomogeneous (k - 1) := by
  unfold bracket
  have h := (isHomogeneous_C (Ψ × Fin N) (k : ℝ)).mul
    (IsHomogeneous.sum Finset.univ (fun τ' => C (co φ p k (Sum.inl τ) τ') * liePs j (k - 1) τ') (k - 1)
      fun τ' _ => by
        simpa using (isHomogeneous_C (Ψ × Fin N) (co φ p k (Sum.inl τ) τ')).mul
          (liePs_isHomogeneous (N := N) j (k - 1) τ'))
  simpa using h

end GlobalTheory.CompanionTheory.Ar.Num.Prop6Model

namespace GlobalTheory.CompanionTheory.Ar.Num

open Prop6Model in

/- English proof (translation)
Introduce `Ψ _ _ N M R II hII S j φ hCh hLoc t ht τ k hk1 hkN Q hQ`. Establish `hkd : k ≤ dimFl Ψ N + 1` using `hkN.trans (le_dimFl_succ Ψ τ N)`. Establish `hpk : (pk τ k : RP Ψ N).IsHomogeneous k`. Use `IsHomogeneous.sum _ _ _ fun i _ => ?_` and prove the remaining obligations. Simplify using `using (isHomogeneous_X ℝ (τ, i)).pow k`.

Establish `hF : (pk τ k * Q : RP Ψ N).IsHomogeneous (dimFl Ψ N + 1)`. Establish `h` using `hpk.mul hQ`. Rewrite `h` using `[Nat.add_sub_cancel' hkd]`. Then use the resulting hypothesis. Establish `hδ : (M.δ : ℝ) ≠ 0` using `by exact_mod_cast M.δ_pos.ne'`. Establish `e1` using `arFun_toA_eq_arNum Ψ N M II hII t _ hF`.

Establish `e2 : R.model.arFun II t (toA (pk τ k * Q)) = arNum (II M.K M.ι) M.P (R.x t) (pk τ k * Q) / (M.δ : ℝ)` using `arFun_toA_eq_arNum Ψ N R.model II hII t _ hF`. Take `⟨Hs, hHs, hHs0, hexp⟩` from `GlobalTheory.T.root_power_sum_mixed_expansion Ψ N (dimFl Ψ N) k hk1 hkd τ Q hQ`. Take `⟨hvert, hiso⟩` from `hCh`. Establish `hlink` using `GlobalTheory.T.isometric_family_intersection_eq M.K M.ι M.P (dimFl Ψ N) M.arith (II M.K M.ι) (hII M.K M.ι) (Ψ × Fin N) S R.pairs hvert (M.x t) (R.x t) (fun i => M.x_smooth t i) (fun i => R.x_smooth t i) (hiso t ht) _ _ hexp`. Take `⟨A, i1, i2, i3, i4, hinj, hconst, hloc⟩` from `hLoc`.

Establish `hdiff : arNum (II M.K M.ι) M.P (M.x t) (pk τ k * Q) - arNum (II M.K M.ι) M.P (R.x t) (pk τ k * Q) = ∑ p ∈ S, Real.log (p : ℕ) * ((M.δ : ℝ) * M.geoFun (toA (bracket j (φ p) p k τ * Q)))`. Rewrite using `[← arNum_mixDiff]`. Use `Eq.trans hlink (Finset.sum_congr rfl fun p hp => ?_)` and prove the remaining obligations. Use `congr 1`. Take `⟨hirr, hmod, hv⟩` from `zp_model M.K M.ι M.P (dimFl Ψ N) M.arith p`.

Establish `hm3` using `GlobalTheory.T.flag_m3_padic_global M.K M.ι M.Ω M.y A hinj hconst (dimFl Ψ N) M.arith p Ψ N j (φ p) S R.pairs hvert (fun m _ hm O _ _ _ _ _ _ _ => (hloc p hp m hm O).1)`. Establish `hz` using `GlobalTheory.T.power_sums_vanish_at_places M.K M.ι M.Ω M.y A hinj hconst (dimFl Ψ N) M.arith p N (fun i => R.xdeg (τ, i)) (fun m _ hm O _ _ _ _ _ _ _ => (hloc p hp m hm O).2 τ)`. Establish `hH : (bracket j (φ p) p k τ * Q : RP Ψ N).IsHomogeneous (dimFl Ψ N)`. Establish `h` using `(bracket_isHomogeneous (N := N) j (φ p) p k τ).mul hQ`. Establish `e : k - 1 + (dimFl Ψ N + 1 - k) = dimFl Ψ N` using `by omega`.

Rewrite `h` using `[e]`. Then use the resulting hypothesis. Establish `h1` using `GlobalTheory.T.power_sum_term_discrete_valuation (ZP p) _ hirr M.K M.ι _ _ hmod p Ψ N j (φ p) k hk1 hkd τ Q Hs hQ hHs hHs0 _ (hv _ S R.pairs hvert) hm3 hz`. Establish `h2` using `GlobalTheory.T.uniformizer_divisor_cycle_number (ZP p) _ hirr M.K M.ι _ _ hmod 1 1 (Ψ × Fin N) M.xdeg (bracket j (φ p) p k τ * Q) (dimFl Ψ N) hH [] (by simp)`. Simplify using `only [Units.val_one, one_mul, pow_one, Nat.cast_one] at h2`. Establish `h3` using `genNum_zp_eq_rat M.K M.ι M.P p (Ψ × Fin N) M.xdeg (bracket j (φ p) p k τ * Q) []`.

Establish `h4` using `GlobalTheory.T.root_model_geometric_generic_number Ψ N M II hII _ hH`. Use `h1.trans ?_` and prove the remaining obligations. Use `Eq.trans h2 ?_` and prove the remaining obligations. Rewrite using `[h3, h4]`. Clear the denominators using the available nonvanishing facts.

Establish `hsum : ∑ p ∈ S, Real.log (p : ℕ) * ((M.δ : ℝ) * M.geoFun (toA (bracket j (φ p) p k τ * Q))) = (M.δ : ℝ) * ∑ p ∈ S, Real.log (p : ℕ) * M.geoFun (toA (bracket j (φ p) p k τ * Q))`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun p _ => by ring`. Rewrite using `[e1, e2]`. Rewrite `hdiff` using `[hsum]`.

Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem power_sum_height_model_change : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) (R : SecondRoots M) (II : IntersectionSystem), IsIntersectionSystem II → ∀ (S : Finset Nat.Primes) (j : ℕ) (φ : ℕ → Equiv.Perm (Ψ ⊕ Ψ)), R.IsChange S → R.LocalAtPlaces j S φ → ∀ t : ℝ, 0 < t → ∀ (τ : Ψ) (k : ℕ), 1 ≤ k → k ≤ N → ∀ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N + 1 - k) → M.arFun II t (toA (pk τ k * Q)) = R.model.arFun II t (toA (pk τ k * Q)) + ∑ p ∈ S, Real.log (p : ℕ) * M.geoFun (toA (bracket j (φ p) p k τ * Q)) := by
  intro Ψ _ _ N M R II hII S j φ hCh hLoc t ht τ k hk1 hkN Q hQ
  classical
  have hkd : k ≤ dimFl Ψ N + 1 := hkN.trans (le_dimFl_succ Ψ τ N)
  have hpk : (pk τ k : RP Ψ N).IsHomogeneous k := by
    refine IsHomogeneous.sum _ _ _ fun i _ => ?_
    simpa using (isHomogeneous_X ℝ (τ, i)).pow k
  have hF : (pk τ k * Q : RP Ψ N).IsHomogeneous (dimFl Ψ N + 1) := by
    have h := hpk.mul hQ
    rwa [Nat.add_sub_cancel' hkd] at h
  have hδ : (M.δ : ℝ) ≠ 0 := by exact_mod_cast M.δ_pos.ne'
  have e1 := arFun_toA_eq_arNum Ψ N M II hII t _ hF
  have e2 : R.model.arFun II t (toA (pk τ k * Q)) =
      arNum (II M.K M.ι) M.P (R.x t) (pk τ k * Q) / (M.δ : ℝ) :=
    arFun_toA_eq_arNum Ψ N R.model II hII t _ hF
  obtain ⟨Hs, hHs, hHs0, hexp⟩ := GlobalTheory.T.root_power_sum_mixed_expansion Ψ N (dimFl Ψ N) k hk1 hkd τ Q hQ
  obtain ⟨hvert, hiso⟩ := hCh
  have hlink := GlobalTheory.T.isometric_family_intersection_eq M.K M.ι M.P (dimFl Ψ N) M.arith (II M.K M.ι) (hII M.K M.ι) (Ψ × Fin N) S R.pairs
    hvert (M.x t) (R.x t) (fun i => M.x_smooth t i) (fun i => R.x_smooth t i) (hiso t ht) _ _ hexp
  obtain ⟨A, i1, i2, i3, i4, hinj, hconst, hloc⟩ := hLoc
  have hdiff : arNum (II M.K M.ι) M.P (M.x t) (pk τ k * Q) - arNum (II M.K M.ι) M.P (R.x t) (pk τ k * Q) =
      ∑ p ∈ S, Real.log (p : ℕ) * ((M.δ : ℝ) * M.geoFun (toA (bracket j (φ p) p k τ * Q))) := by
    rw [← arNum_mixDiff]
    refine Eq.trans hlink (Finset.sum_congr rfl fun p hp => ?_)
    congr 1
    obtain ⟨hirr, hmod, hv⟩ := zp_model M.K M.ι M.P (dimFl Ψ N) M.arith p
    have hm3 := GlobalTheory.T.flag_m3_padic_global M.K M.ι M.Ω M.y A hinj hconst (dimFl Ψ N) M.arith p Ψ N j (φ p) S R.pairs hvert
      (fun m _ hm O _ _ _ _ _ _ _ => (hloc p hp m hm O).1)
    have hz := GlobalTheory.T.power_sums_vanish_at_places M.K M.ι M.Ω M.y A hinj hconst (dimFl Ψ N) M.arith p N (fun i => R.xdeg (τ, i))
      (fun m _ hm O _ _ _ _ _ _ _ => (hloc p hp m hm O).2 τ)
    have hH : (bracket j (φ p) p k τ * Q : RP Ψ N).IsHomogeneous (dimFl Ψ N) := by
      have h := (bracket_isHomogeneous (N := N) j (φ p) p k τ).mul hQ
      have e : k - 1 + (dimFl Ψ N + 1 - k) = dimFl Ψ N := by omega
      rwa [e] at h
    have h1 := GlobalTheory.T.power_sum_term_discrete_valuation (ZP p) _ hirr M.K M.ι _ _ hmod p Ψ N j (φ p) k hk1 hkd τ Q Hs hQ hHs hHs0 _
      (hv _ S R.pairs hvert) hm3 hz
    have h2 := GlobalTheory.T.uniformizer_divisor_cycle_number (ZP p) _ hirr M.K M.ι _ _ hmod 1 1 (Ψ × Fin N) M.xdeg
      (bracket j (φ p) p k τ * Q) (dimFl Ψ N) hH [] (by simp)
    simp only [Units.val_one, one_mul, pow_one, Nat.cast_one] at h2
    have h3 := genNum_zp_eq_rat M.K M.ι M.P p (Ψ × Fin N) M.xdeg (bracket j (φ p) p k τ * Q) []
    have h4 := GlobalTheory.T.root_model_geometric_generic_number Ψ N M II hII _ hH
    refine h1.trans ?_
    refine Eq.trans h2 ?_
    rw [h3, h4]
    field_simp
  have hsum : ∑ p ∈ S, Real.log (p : ℕ) * ((M.δ : ℝ) * M.geoFun (toA (bracket j (φ p) p k τ * Q))) =
      (M.δ : ℝ) * ∑ p ∈ S, Real.log (p : ℕ) * M.geoFun (toA (bracket j (φ p) p k τ * Q)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [e1, e2]
  rw [hsum] at hdiff
  field_simp
  linarith

end GlobalTheory.CompanionTheory.Ar.Num
