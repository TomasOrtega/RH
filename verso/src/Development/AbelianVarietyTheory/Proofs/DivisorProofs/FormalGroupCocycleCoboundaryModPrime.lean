import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesLiftQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoboundaryOfPullbackNmulCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapCoboundarySwapPullbackCommuteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommFormalGroupLawMapNatMultipleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalChartQuotientByIdealWithPrimePowStatement

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.CobModP

/- English proof (translation)
Establish `ha : HasSubst a` using `hasSubst_of_constantCoeff_zero ha0`. Establish `h` using `constantCoeff_subst_eq_zero ha ha0 (f := f - C (constantCoeff f)) (by simp)`. Rewrite `h` using `[subst_sub ha, subst_C, map_sub, constantCoeff_C, sub_eq_zero]`. Conclude with `h`.
-/
theorem constantCoeff_subst_of_zero' {σ τ R : Type} [CommRing R] [Finite σ]
    {a : σ → MvPowerSeries τ R} (ha0 : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  have h := constantCoeff_subst_eq_zero ha ha0 (f := f - C (constantCoeff f)) (by simp)
  rw [subst_sub ha, subst_C, map_sub, constantCoeff_C, sub_eq_zero] at h
  exact h

/- English proof (translation)
Unfold `cob1 inL inR`. Rewrite using `[map_sub, map_sub, constantCoeff_subst_of_zero' h, constantCoeff_subst_of_zero' (fun _ => constantCoeff_X _), constantCoeff_subst_of_zero' (fun _ => constantCoeff_X _)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem constantCoeff_formalGroupLawCoboundaryOne_eq_zero {R : Type} [CommRing R] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (h : ∀ i, constantCoeff (μ i) = 0)
    (f : MvPowerSeries (Fin d) R) : constantCoeff (cob1 μ f) = -constantCoeff f := by
  unfold cob1 inL inR
  rw [map_sub, map_sub, constantCoeff_subst_of_zero' h,
    constantCoeff_subst_of_zero' (fun _ => constantCoeff_X _),
    constantCoeff_subst_of_zero' (fun _ => constantCoeff_X _)]
  ring

/- English proof (translation)
Introduce `p _ O _ G d c κ B y hκ0 hcoc hdiv hB`. Use `set I : Ideal O := Ideal.span {(p : O)} with hI`. Use `set r : O →+* O ⧸ I := Ideal.Quotient.mk I with hr`. Take `⟨c', hlaw, hev, -⟩` from `GlobalTheory.T.exists_formalChart_quotient_by_ideal_with_primePow p O G d c I 1 (by`. Rewrite using `[pow_one]`.

Conclude with `Ideal.mem_span_singleton_self _)`. Establish `hconst` using `c.isLaw.const`. Take `⟨hm1, hm2, hm3, -, hm5⟩` from `GlobalTheory.T.map_coboundary_swap_pullback_commute O d c.μ hconst (O ⧸ I) r`. Take `⟨-, hn⟩` from `GlobalTheory.T.isCommFormalGroupLaw_map_natMultiple O d c.μ c.isLaw (O ⧸ I) r`. Establish `hnc : ∀ i, constantCoeff (nmul c.μ p i) = 0` using `fun i => (hn p i).1`.

Establish `hcoc' : IsCoc (fun i => map r (c.μ i)) (map r κ)` using `⟨by rw [← hm2, hcoc.1, map_zero], by rw [← hm3, hcoc.2]⟩`. Establish `heq : cob1 (fun i => map r (c.μ i)) (map r B) = pull2 (nmul (fun i => map r (c.μ i)) p) (map r κ)`. Establish `h0 : map r (cob1 c.μ B - pull2 (nmul c.μ p) κ) = 0` using `((GlobalTheory.mvPowerSeries_lift_quotient O (Fin d ⊕ Fin d) I).2.1 _).2 (fun α => Ideal.mem_span_singleton.2 (hdiv α))`. Rewrite `h0` using `[map_sub, hm1, (hm5 _ hnc).1, sub_eq_zero]`. Rewrite using `[h0]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `(hn p i).2`. Establish `hp1 : (p : O) • (1 : O ⧸ I) = 0`. Rewrite using `[Algebra.smul_def, mul_one]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)`. Establish `hev0 : c'.ev 1 (map r B) = 0`. Rewrite using `[hev, hB, toBase_app, ← TensorProduct.smul_tmul, hp1, TensorProduct.zero_tmul]`. Take `⟨s, hs⟩` from `GlobalTheory.T.exists_coboundary_of_pullback_nmul_coboundary p (O ⧸ I) d (G.baseChange (O ⧸ I)) c' _ hlaw (map r κ) (map r B) hcoc' heq hev0`. Establish `hs0 : constantCoeff s = 0`.

Establish `h1 : constantCoeff (map r κ) = 0`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hκ0, map_zero]`. Establish `hc' : ∀ i, constantCoeff (map r (c.μ i)) = 0` using `fun i => by`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hconst i, map_zero]`. Rewrite `h1` using `[hs, constantCoeff_formalGroupLawCoboundaryOne_eq_zero hc']`.

Conclude with `neg_eq_zero.1 h1`. Take `⟨t, ht, ht0⟩` from `(GlobalTheory.mvPowerSeries_lift_quotient O (Fin d) I).1 s`. Use `⟨t, ht0 hs0, fun α => ?_⟩` and prove the remaining obligations. Establish `h2 : map r (κ - cob1 c.μ t) = 0` using `by rw [map_sub, hm1, ht, hs, sub_self]`. Conclude with `Ideal.mem_span_singleton.1 (((GlobalTheory.mvPowerSeries_lift_quotient O (Fin d ⊕ Fin d) I).2.1 _).1 h2 α)`.
-/
theorem coboundary_mod_p : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (κ : MvPowerSeries (Fin d ⊕ Fin d) O) (B : MvPowerSeries (Fin d) O) (y : G.A 1), constantCoeff κ = 0 → IsCoc c.μ κ → (∀ α, (p : O) ∣ coeff α (cob1 c.μ B - pull2 (nmul c.μ p) κ)) → c.ev 1 B = (p : O) • y → ∃ t : MvPowerSeries (Fin d) O, constantCoeff t = 0 ∧ ∀ α, (p : O) ∣ coeff α (κ - cob1 c.μ t) := by
  intro p _ O _ G d c κ B y hκ0 hcoc hdiv hB
  set I : Ideal O := Ideal.span {(p : O)} with hI
  set r : O →+* O ⧸ I := Ideal.Quotient.mk I with hr
  obtain ⟨c', hlaw, hev, -⟩ := GlobalTheory.T.exists_formalChart_quotient_by_ideal_with_primePow p O G d c I 1 (by
    rw [pow_one]; exact Ideal.mem_span_singleton_self _)
  have hconst := c.isLaw.const
  obtain ⟨hm1, hm2, hm3, -, hm5⟩ := GlobalTheory.T.map_coboundary_swap_pullback_commute O d c.μ hconst (O ⧸ I) r
  obtain ⟨-, hn⟩ := GlobalTheory.T.isCommFormalGroupLaw_map_natMultiple O d c.μ c.isLaw (O ⧸ I) r
  have hnc : ∀ i, constantCoeff (nmul c.μ p i) = 0 := fun i => (hn p i).1
  have hcoc' : IsCoc (fun i => map r (c.μ i)) (map r κ) :=
    ⟨by rw [← hm2, hcoc.1, map_zero], by rw [← hm3, hcoc.2]⟩
  have heq : cob1 (fun i => map r (c.μ i)) (map r B) =
      pull2 (nmul (fun i => map r (c.μ i)) p) (map r κ) := by
    have h0 : map r (cob1 c.μ B - pull2 (nmul c.μ p) κ) = 0 :=
      ((GlobalTheory.mvPowerSeries_lift_quotient O (Fin d ⊕ Fin d) I).2.1 _).2
        (fun α => Ideal.mem_span_singleton.2 (hdiv α))
    rw [map_sub, hm1, (hm5 _ hnc).1, sub_eq_zero] at h0
    rw [h0]
    congr 1
    funext i
    exact (hn p i).2
  have hp1 : (p : O) • (1 : O ⧸ I) = 0 := by
    rw [Algebra.smul_def, mul_one]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hev0 : c'.ev 1 (map r B) = 0 := by
    rw [hev, hB, toBase_app, ← TensorProduct.smul_tmul, hp1, TensorProduct.zero_tmul]
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_coboundary_of_pullback_nmul_coboundary p (O ⧸ I) d (G.baseChange (O ⧸ I)) c' _ hlaw (map r κ) (map r B)
    hcoc' heq hev0
  have hs0 : constantCoeff s = 0 := by
    have h1 : constantCoeff (map r κ) = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hκ0,
        map_zero]
    have hc' : ∀ i, constantCoeff (map r (c.μ i)) = 0 := fun i => by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
        hconst i, map_zero]
    rw [hs, constantCoeff_formalGroupLawCoboundaryOne_eq_zero hc'] at h1
    exact neg_eq_zero.1 h1
  obtain ⟨t, ht, ht0⟩ := (GlobalTheory.mvPowerSeries_lift_quotient O (Fin d) I).1 s
  refine ⟨t, ht0 hs0, fun α => ?_⟩
  have h2 : map r (κ - cob1 c.μ t) = 0 := by rw [map_sub, hm1, ht, hs, sub_self]
  exact Ideal.mem_span_singleton.1 (((GlobalTheory.mvPowerSeries_lift_quotient O (Fin d ⊕ Fin d) I).2.1 _).1 h2 α)

end GlobalTheory.CobModP
