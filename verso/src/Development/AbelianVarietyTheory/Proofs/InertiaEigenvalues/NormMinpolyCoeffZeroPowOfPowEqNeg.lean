import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory

open Polynomial

/- English proof (translation)
Introduce `l _ F N x hN hx`. Use `set P : F[X] := Polynomial.X ^ N + Polynomial.C (l : F) with hP`. Establish `hPm : P.Monic` using `monic_X_pow_add_C _ hN.ne'`. Establish `hPx : aeval x P = 0`. Simplify using `[hP, hx]`.

Establish `hint : IsIntegral F x` using `⟨P, hPm, by simpa [aeval_def] using hPx⟩`. Establish `hm : (minpoly F x).Monic` using `minpoly.monic hint`. Establish `hdvd : minpoly F x ∣ P` using `minpoly.dvd F x hPx`. Use `set q : (Om l)[X] := (minpoly F x).map (algebraMap F (Om l)) with hq`. Establish `hqm : q.Monic` using `hm.map _`.

Establish `hs : q.Splits` using `IsAlgClosed.splits q`. Establish `hc : q.coeff 0 = (((minpoly F x).coeff 0 : F) : Om l)`. Rewrite using `[hq, Polynomial.coeff_map]`. Both sides reduce to the same expression. Establish `hdeg : q.natDegree = (minpoly F x).natDegree` using `natDegree_map _`.

Establish `hroot : ∀ r ∈ q.roots, ‖r‖ ^ N = (l : ℝ)⁻¹`. Introduce `r hr`. Establish `hr0 : aeval r (minpoly F x) = 0`. Rewrite `hr` using `[mem_roots hqm.ne_zero, IsRoot, hq, eval_map]`. Simplify `hr` using `[aeval_def]`.

Take `⟨g, hg⟩` from `hdvd`. Establish `hPr : aeval r P = 0` using `by rw [hg, map_mul, hr0, zero_mul]`. Establish `hrN : r ^ N = -(l : Om l)`. Establish `: r ^ N + (l : Om l) = 0` using `by simpa [hP] using hPr`. Conclude with `eq_neg_of_add_eq_zero_left this`.

Rewrite using `[← norm_pow, hrN, norm_neg, ← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends, Padic.norm_p]`. Establish `hprod : ‖q.roots.prod‖ ^ N = (q.roots.map fun r => ‖r‖ ^ N).prod`. Use `map_multiset_prod ((powMonoidHom N : ℝ →* ℝ).comp (normHom : Om l →*₀ ℝ).toMonoidHom) q.roots` as an intermediate fact. Simplify `this` using `[Function.comp_def]`. Rewrite using `[← hc, hs.coeff_zero_eq_prod_roots_of_monic hqm, norm_mul, mul_pow, norm_pow, norm_neg, norm_one, one_pow, one_pow, one_mul, hprod, Multiset.map_congr rfl hroot, Multiset.map_const', Multiset.prod_replicate, ← hs.natDegree_eq_card_roots, hdeg]`.
-/
theorem norm_minpoly_coeff_zero_pow_of_pow_eq_neg :
    ∀ (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (Om l)) (N : ℕ) (x : Om l), 0 < N →
      x ^ N = -(l : Om l) →
      ‖(((minpoly F x).coeff 0 : F) : Om l)‖ ^ N = ((l : ℝ)⁻¹) ^ (minpoly F x).natDegree := by
  intro l _ F N x hN hx
  set P : F[X] := Polynomial.X ^ N + Polynomial.C (l : F) with hP
  have hPm : P.Monic := monic_X_pow_add_C _ hN.ne'
  have hPx : aeval x P = 0 := by
    simp [hP, hx]
  have hint : IsIntegral F x := ⟨P, hPm, by simpa [aeval_def] using hPx⟩
  have hm : (minpoly F x).Monic := minpoly.monic hint
  have hdvd : minpoly F x ∣ P := minpoly.dvd F x hPx
  set q : (Om l)[X] := (minpoly F x).map (algebraMap F (Om l)) with hq
  have hqm : q.Monic := hm.map _
  have hs : q.Splits := IsAlgClosed.splits q
  have hc : q.coeff 0 = (((minpoly F x).coeff 0 : F) : Om l) := by
    rw [hq, Polynomial.coeff_map]; rfl
  have hdeg : q.natDegree = (minpoly F x).natDegree := natDegree_map _
  have hroot : ∀ r ∈ q.roots, ‖r‖ ^ N = (l : ℝ)⁻¹ := by
    intro r hr
    have hr0 : aeval r (minpoly F x) = 0 := by
      rw [mem_roots hqm.ne_zero, IsRoot, hq, eval_map] at hr
      simpa [aeval_def] using hr
    obtain ⟨g, hg⟩ := hdvd
    have hPr : aeval r P = 0 := by rw [hg, map_mul, hr0, zero_mul]
    have hrN : r ^ N = -(l : Om l) := by
      have : r ^ N + (l : Om l) = 0 := by simpa [hP] using hPr
      exact eq_neg_of_add_eq_zero_left this
    rw [← norm_pow, hrN, norm_neg, ← map_natCast (algebraMap ℚ_[l] (Om l)),
      PadicAlgCl.norm_extends, Padic.norm_p]
  have hprod : ‖q.roots.prod‖ ^ N = (q.roots.map fun r => ‖r‖ ^ N).prod := by
    have := map_multiset_prod ((powMonoidHom N : ℝ →* ℝ).comp (normHom : Om l →*₀ ℝ).toMonoidHom) q.roots
    simpa [Function.comp_def] using this
  rw [← hc, hs.coeff_zero_eq_prod_roots_of_monic hqm, norm_mul, mul_pow, norm_pow, norm_neg,
    norm_one, one_pow, one_pow, one_mul, hprod, Multiset.map_congr rfl hroot, Multiset.map_const',
    Multiset.prod_replicate, ← hs.natDegree_eq_card_roots, hdeg]

end GlobalTheory
