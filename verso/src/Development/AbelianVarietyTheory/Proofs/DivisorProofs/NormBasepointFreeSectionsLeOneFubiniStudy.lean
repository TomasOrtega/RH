import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaiseFirstWeightSectionsLociValuesNormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularNonvanishingLocusSectionPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairPowSectionMemAndNormPow

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

/- English proof (translation)
Introduce `k _ X _ p D _ P e x hx n u hn hu`. Establish `he : (0 : ℝ) < e` using `by exact_mod_cast hx.pos`. Establish `hnR : (0 : ℝ) < n` using `by exact_mod_cast hn`. Establish `hn0 : 2 * n ≠ 0` using `by omega`. Establish `hup` using `GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms k X p P u (e : ℤ) 0`.

Establish `hnn : ∀ (Q : Pair p) σ (y : CxPts p σ) f, 0 ≤ Q.nu e 0 σ y f` using `fun Q σ y f => by`. Rewrite using `[← norm_val]`. Conclude with `norm_nonneg _`. Establish `hS : ∀ σ (y : CxPts p σ), 0 < ∑ l, P.nu e 0 σ y (x l) ^ (2 * n)`. Introduce `σ y`.

Take `⟨l, hl⟩` from `hx.cover (under y)`. Establish `h` using `((GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e 0 (x l) (hx.mem l)).2.2.2.2 (x l) (hx.mem l) σ y hl).2`. Conclude with `lt_of_lt_of_le (pow_pos h _) (Finset.single_le_sum (f := fun l => P.nu e 0 σ y (x l) ^ (2 * n)) (fun i _ => pow_nonneg (hnn P σ y _) _) (Finset.mem_univ l))`. Establish `key : ∀ σ (y : CxPts p σ) f, (upperParabolic P u).nu e 0 σ y f ^ (2 * n) = P.nu e 0 σ y f ^ (2 * n) / ∑ l, P.nu e 0 σ y (x l) ^ (2 * n)`. Introduce `σ y f`.

Rewrite using `[(hup.2.2 σ y f).2, mul_pow, ← Real.exp_nat_mul, hu σ y]`. Establish `: ((2 * n : ℕ) : ℝ) * (-(((e : ℤ) : ℝ) * (((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ y (x l) ^ (2 * n)))) / 2) = -Real.log (∑ l, P.nu e 0 σ y (x l) ^ (2 * n))` using `by push_cast; field_simp`. Rewrite using `[this, Real.exp_neg, Real.exp_log (hS σ y), div_eq_mul_inv]`. Use `⟨fun l σ y => ?_, fun σ y => ?_, ⟨hx.pos, fun l => hup.1 ▸ hx.mem l, fun z => ?_⟩, ⟨?_, fun l => ?_, fun z => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← pow_le_pow_iff_left₀ (hnn _ σ y _) zero_le_one hn0, one_pow, key, div_le_one (hS σ y)]`.

Conclude with `Finset.single_le_sum (f := fun l => P.nu e 0 σ y (x l) ^ (2 * n)) (fun i _ => pow_nonneg (hnn P σ y _) _) (Finset.mem_univ l)`. Take `⟨l, -, hl⟩` from `Finset.exists_max_image Finset.univ (fun l => P.nu e 0 σ y (x l)) Finset.univ_nonempty`. Use `⟨l, ?_⟩` and prove the remaining obligations. Rewrite using `[← pow_le_pow_iff_left₀ (Real.exp_pos _).le (hnn _ σ y _) hn0, key, ← Real.exp_nat_mul]`. Establish `e1 : ((2 * n : ℕ) : ℝ) * -(Real.log (D + 1) / (2 * n)) = -Real.log (D + 1)` using `by push_cast; field_simp`.

Establish `hD : (0 : ℝ) < D + 1` using `by positivity`. Rewrite using `[e1, Real.exp_neg, Real.exp_log hD, inv_eq_one_div, div_le_div_iff₀ hD (hS σ y), one_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨l, hl⟩` from `hx.cover z`. Conclude with `⟨l, (hup.2.1 (x l)).symm ▸ hl⟩`. Conclude with `Nat.mul_pos hx.pos hn`. Establish `h` using `(GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P e 0 (x l) (hx.mem l) n).1`.

Apply the tactic sequence `convert h using 2 <;> push_cast <;> ring`. Take `⟨l, hl⟩` from `hx.cover z`. Use `⟨l, ?_⟩` and prove the remaining obligations. Establish `h` using `(GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e 0 (x l) (hx.mem l)).2.2.1 n hn`. Establish `e2 : ((e * n : ℕ) : ℤ) = (n : ℤ) * (e : ℤ)` using `by push_cast; ring`.

Establish `e3 : (0 : ℤ) = (n : ℤ) * 0` using `by ring`. Use `show z ∈ NV P ((e * n : ℕ) : ℤ) 0 (x l ^ n)`. Rewrite using `[e2, e3, h]`. Conclude with `hl`. Introduce `σ y`.

Establish `hp : ∀ l, P.nu ((e * n : ℕ) : ℤ) 0 σ y (x l ^ n) = P.nu e 0 σ y (x l) ^ n` using `fun l => by`. Establish `h` using `(GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P e 0 (x l) (hx.mem l) n).2 σ y`. Apply the tactic sequence `convert h using 2 <;> push_cast <;> ring`. Rewrite using `[hu σ y]`. Simplify using `only [hp, ← pow_mul]`.

Use `push_cast`. Put the polynomial expressions in normal form.
-/
theorem canNorms : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ (n : ℕ) (u : SmFn p), 1 ≤ n → IsCan P e n x u → (∀ l (σ : k →+* ℂ) (y : CxPts p σ), (upperParabolic P u).nu e 0 σ y (x l) ≤ 1) ∧ (∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ l, Real.exp (-(Real.log (D + 1) / (2 * n))) ≤ (upperParabolic P u).nu e 0 σ y (x l)) ∧ Gens (upperParabolic P u) D e x ∧ Gens P D (e * n) (fun l => x l ^ n) ∧ IsCan P (e * n) 1 (fun l => x l ^ n) u := by
  intro k _ X _ p D _ P e x hx n u hn hu
  have he : (0 : ℝ) < e := by exact_mod_cast hx.pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : 2 * n ≠ 0 := by omega
  have hup := GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms k X p P u (e : ℤ) 0
  have hnn : ∀ (Q : Pair p) σ (y : CxPts p σ) f, 0 ≤ Q.nu e 0 σ y f := fun Q σ y f => by
    rw [← norm_val]; exact norm_nonneg _
  have hS : ∀ σ (y : CxPts p σ), 0 < ∑ l, P.nu e 0 σ y (x l) ^ (2 * n) := by
    intro σ y
    obtain ⟨l, hl⟩ := hx.cover (under y)
    have h := ((GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e 0 (x l) (hx.mem l)).2.2.2.2 (x l) (hx.mem l) σ y hl).2
    exact lt_of_lt_of_le (pow_pos h _) (Finset.single_le_sum (f := fun l => P.nu e 0 σ y (x l) ^ (2 * n))
      (fun i _ => pow_nonneg (hnn P σ y _) _) (Finset.mem_univ l))
  have key : ∀ σ (y : CxPts p σ) f, (upperParabolic P u).nu e 0 σ y f ^ (2 * n) =
      P.nu e 0 σ y f ^ (2 * n) / ∑ l, P.nu e 0 σ y (x l) ^ (2 * n) := by
    intro σ y f
    rw [(hup.2.2 σ y f).2, mul_pow, ← Real.exp_nat_mul, hu σ y]
    have : ((2 * n : ℕ) : ℝ) * (-(((e : ℤ) : ℝ) * (((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ y (x l) ^ (2 * n)))) / 2)
        = -Real.log (∑ l, P.nu e 0 σ y (x l) ^ (2 * n)) := by
      push_cast; field_simp
    rw [this, Real.exp_neg, Real.exp_log (hS σ y), div_eq_mul_inv]
  refine ⟨fun l σ y => ?_, fun σ y => ?_, ⟨hx.pos, fun l => hup.1 ▸ hx.mem l, fun z => ?_⟩, ⟨?_, fun l => ?_, fun z => ?_⟩, ?_⟩
  · rw [← pow_le_pow_iff_left₀ (hnn _ σ y _) zero_le_one hn0, one_pow, key, div_le_one (hS σ y)]
    exact Finset.single_le_sum (f := fun l => P.nu e 0 σ y (x l) ^ (2 * n))
      (fun i _ => pow_nonneg (hnn P σ y _) _) (Finset.mem_univ l)
  · obtain ⟨l, -, hl⟩ := Finset.exists_max_image Finset.univ (fun l => P.nu e 0 σ y (x l)) Finset.univ_nonempty
    refine ⟨l, ?_⟩
    rw [← pow_le_pow_iff_left₀ (Real.exp_pos _).le (hnn _ σ y _) hn0, key, ← Real.exp_nat_mul]
    have e1 : ((2 * n : ℕ) : ℝ) * -(Real.log (D + 1) / (2 * n)) = -Real.log (D + 1) := by
      push_cast; field_simp
    have hD : (0 : ℝ) < D + 1 := by positivity
    rw [e1, Real.exp_neg, Real.exp_log hD, inv_eq_one_div, div_le_div_iff₀ hD (hS σ y), one_mul]
    calc ∑ i, P.nu e 0 σ y (x i) ^ (2 * n) ≤ ∑ _i : Fin (D + 1), P.nu e 0 σ y (x l) ^ (2 * n) :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (hnn P σ y _) (hl i (Finset.mem_univ i)) _
      _ = P.nu e 0 σ y (x l) ^ (2 * n) * (D + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  · obtain ⟨l, hl⟩ := hx.cover z
    exact ⟨l, (hup.2.1 (x l)).symm ▸ hl⟩
  · exact Nat.mul_pos hx.pos hn
  · have h := (GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P e 0 (x l) (hx.mem l) n).1
    convert h using 2 <;> push_cast <;> ring
  · obtain ⟨l, hl⟩ := hx.cover z
    refine ⟨l, ?_⟩
    have h := (GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e 0 (x l) (hx.mem l)).2.2.1 n hn
    have e2 : ((e * n : ℕ) : ℤ) = (n : ℤ) * (e : ℤ) := by push_cast; ring
    have e3 : (0 : ℤ) = (n : ℤ) * 0 := by ring
    show z ∈ NV P ((e * n : ℕ) : ℤ) 0 (x l ^ n)
    rw [e2, e3, h]; exact hl
  · intro σ y
    have hp : ∀ l, P.nu ((e * n : ℕ) : ℤ) 0 σ y (x l ^ n) = P.nu e 0 σ y (x l) ^ n := fun l => by
      have h := (GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P e 0 (x l) (hx.mem l) n).2 σ y
      convert h using 2 <;> push_cast <;> ring
    rw [hu σ y]
    simp only [hp, ← pow_mul]
    push_cast
    ring_nf

end GlobalTheory.HSAmp
