import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.DegreeHermitianFormula
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.StepEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.LeExpSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullStepCut
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.LieOneEqZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CutBd
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.BdGrowth
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullRetrFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.QhtFacts
open UpperTheory.V.Lit.Geo NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

/- English proof (translation)
Take `⟨N, hN⟩` from `exists_nat_ge (D * |C| / c)`. Use `⟨N, Real.exp (D * ((1 + |C|) / c + 1)), (Real.exp_pos _).le, fun n x y hx h1 h2 => ?_⟩` and prove the remaining obligations. Establish `hl : 0 ≤ Real.log x` using `Real.log_nonneg hx`. Establish `hx0 : 0 < x` using `one_pos.trans_le hx`. Establish `h3 : y ≤ |C| * (1 + Real.log x)` using `h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith))`.

Establish `h4 : (n : ℝ) ≤ (1 + |C|) / c + |C| / c * Real.log x`. Establish `: (1 + |C|) / c + |C| / c * Real.log x = (1 + |C| * (1 + Real.log x)) / c`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, le_div_iff₀ hc]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h5 : x ^ N = Real.exp (N * Real.log x)`. Rewrite using `[Real.exp_nat_mul, Real.exp_log hx0]`. Rewrite using `[h5, ← Real.exp_add]`. Use `Real.exp_le_exp.2 ?_` and prove the remaining obligations.

Establish `h6 : D * |C| / c * Real.log x ≤ N * Real.log x` using `mul_le_mul_of_nonneg_right hN hl`. Establish `h7` using `mul_le_mul_of_nonneg_left h4 hD`. Establish `h8 : D * ((1 + |C|) / c + |C| / c * Real.log x) = D * ((1 + |C|) / c) + D * |C| / c * Real.log x` using `by ring`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem exp_bound (D C c : ℝ) (hD : 0 ≤ D) (hc : 0 < c) :
    ∃ (N : ℕ) (K : ℝ), 0 ≤ K ∧ ∀ (n : ℕ) (x y : ℝ), 1 ≤ x → y ≤ C * (1 + Real.log x) → n * c - 1 ≤ y →
      Real.exp (D * (n + 1)) ≤ K * x ^ N := by
  obtain ⟨N, hN⟩ := exists_nat_ge (D * |C| / c)
  refine ⟨N, Real.exp (D * ((1 + |C|) / c + 1)), (Real.exp_pos _).le, fun n x y hx h1 h2 => ?_⟩
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have hx0 : 0 < x := one_pos.trans_le hx
  have h3 : y ≤ |C| * (1 + Real.log x) := h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith))
  have h4 : (n : ℝ) ≤ (1 + |C|) / c + |C| / c * Real.log x := by
    have : (1 + |C|) / c + |C| / c * Real.log x = (1 + |C| * (1 + Real.log x)) / c := by
      field_simp
      ring
    rw [this, le_div_iff₀ hc]
    linarith
  have h5 : x ^ N = Real.exp (N * Real.log x) := by
    rw [Real.exp_nat_mul, Real.exp_log hx0]
  rw [h5, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h6 : D * |C| / c * Real.log x ≤ N * Real.log x := mul_le_mul_of_nonneg_right hN hl
  have h7 := mul_le_mul_of_nonneg_left h4 hD
  have h8 : D * ((1 + |C|) / c + |C| / c * Real.log x) = D * ((1 + |C|) / c) + D * |C| / c * Real.log x := by ring
  nlinarith

/- English proof (translation)
Introduce `E _ _ _ a ha U hUo hUc Ξ q η hη hM`. Take `⟨f, Y, C, c, f₀, hS⟩` from `stepEx E a ha U hUc`. Take `⟨D, hD, hP⟩` from `prim E a U hUo Ξ f Y C c f₀ hS q η hη hM`. Take `⟨B, hB, hcut⟩` from `stepCut E a U f Y C c f₀ hS`. Take `⟨N₁, C₁, hC₁, hG⟩` from `(bdGrowth E a Ξ (q + 1) _).1 hM`.

Take `⟨N₂, K, hK, hE⟩` from `exp_bound D C c hD hS.c_pos`. Establish `hq` using `(qhtFacts E a).1`. Establish `hfr : ∀ g, f (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1 = f g` using `fun g => by`. Take `⟨t, ht⟩` from `(retrFacts E a).1 g`. Use `hS.f_left 1 t g` as an intermediate fact.

Rewrite `this` using `[map_one, one_mul]`. Rewrite using `[ht, this]`. Use `⟨N₁ + N₂, C₁ + (q + 1) * B * K, by positivity, fun R => ?_⟩` and prove the remaining obligations. Take `⟨n, hn⟩` from `exists_nat_ge ((|C| * (1 + Real.log (max R 1)) + 1) / c)`. Rewrite `hn` using `[div_le_iff₀ hS.c_pos]`.

Take `⟨η', hη', hd, hb⟩` from `hP n`. Take `⟨u, hu, hU⟩` from `hcut (n * c - 1)`. Take `⟨ζ, hζ, hmul, hdζ⟩` from `mulEx E a U Ξ q u η' hu hη'`. Establish `hfar : ∀ g, Real.exp (|C| * (1 + n * c)) < qht g → n * c - 1 + 1 ≤ f g` using `fun g hg => by`. Assume the negation of the conclusion as `hcon`.

Establish `h0 : f g ≤ n * c` using `by linarith`. Establish `h1 : Real.log (qht g) ≤ |C| * (1 + n * c)` using `(hS.le_f g).trans (mul_le_mul (le_abs_self C) (by linarith) (by linarith [hS.f_nonneg g]) (abs_nonneg C))`. Establish `h2` using `Real.exp_le_exp.2 h1`. Rewrite `h2` using `[Real.exp_log (one_pos.trans_le (hq g))]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `⟨ζ, hζ, ⟨Real.exp (|C| * (1 + n * c)), fun X g hg => ?_⟩, ⟨Real.exp (|C| * (1 + n * c)), fun X g hg => ?_⟩, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[hmul X g, ((hU g).2.2 (hfar g hg)).1, zero_smul]`. Rewrite using `[hdζ X g, ((hU g).2.2 (hfar g hg)).1, zero_smul, zero_add]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[((hU g).2.2 (hfar g hg)).2, mul_zero, zero_smul]`.

Establish `hcb` using `cutBd E a Ξ q u η' ζ hdζ g`. Rewrite `hcb` using `[hd]`. Establish `q1` using `hq g`. Establish `hM' : 0 ≤ C₁ * qht g ^ N₁` using `by positivity`. Establish `near : f g ≤ n * c - 1 → Bd (Ξ` using `Ξ) (dCo (smLie Ξ) η - dCo (smLie Ξ) ζ) g 0 := fun h => by`.

Establish `h1` using `(hU _).2.1 ((hfr g).trans_le h)`. Use `(hcb 0 0 0 _ le_rfl hM' le_rfl (by rw [h1.1]; simp) (fun X => by rw [h1.2]; simp) (Or.inl rfl) (hG g)).mono ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `hs : ‖1 - u.1 (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1‖ ≤ 1`. Take `⟨t, t0, t1, ht⟩` from `hu.range (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1`.

Rewrite using `[ht, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]`. Apply the tactic sequence `constructor <;> linarith`. Establish `p1 : qht g ^ N₁ ≤ qht g ^ (N₁ + N₂)` using `pow_le_pow_right₀ q1 (by omega)`. Establish `p2 : qht g ^ N₂ ≤ qht g ^ (N₁ + N₂)` using `pow_le_pow_right₀ q1 (by omega)`. Establish `p3 : C₁ * qht g ^ N₁ ≤ C₁ * qht g ^ (N₁ + N₂)` using `mul_le_mul_of_nonneg_left p1 hC₁`.

Use `⟨fun hg => near ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : Real.log (qht g) ≤ Real.log (max R 1)` using `Real.log_le_log (one_pos.trans_le q1) (hg.trans (le_max_left _ _))`. Establish `h2 : f g ≤ |C| * (1 + Real.log (max R 1))` using `(hS.f_le g).trans (mul_le_mul (le_abs_self C) (by linarith) (by linarith [Real.log_nonneg q1]) (abs_nonneg C))`. Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `h1 : f g ≤ n * c - 1`.

Conclude with `(near h1).mono (by positivity)`. Distinguish the cases in `h2 : f g ≤ n * c`. Use `(hcb 1 B _ _ (Real.exp_pos _).le hM' hB hs (hU _).1 (Or.inr (hb g h2)) (hG g)).mono ?_` and prove the remaining obligations. Establish `h3` using `(hE n _ _ q1 (hS.f_le g) (not_le.1 h1).le).trans (mul_le_mul_of_nonneg_left p2 hK)`. Establish `h4` using `mul_le_mul_of_nonneg_left h3 (show (0 : ℝ) ≤ (q + 1) * B by positivity)`.

Use the polynomial consequences of the given equalities and inequalities. Establish `h3` using `(hU _).2.2 (show n * c - 1 + 1 ≤ _ by rw [hfr g]; linarith)`. Use `(hcb 1 0 0 _ le_rfl hM' le_rfl hs (fun X => by rw [h3.2]; simp) (Or.inl rfl) (hG g)).mono ?_` and prove the remaining obligations. Establish `h4 : (0 : ℝ) ≤ (q + 1) * B * K * qht g ^ (N₁ + N₂)` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem UpperTheory.V.Lit.Geo.approx :
    Approx := by
  intro E _ _ _ a ha U hUo hUc Ξ q η hη hM
  obtain ⟨f, Y, C, c, f₀, hS⟩ := stepEx E a ha U hUc
  obtain ⟨D, hD, hP⟩ := prim E a U hUo Ξ f Y C c f₀ hS q η hη hM
  obtain ⟨B, hB, hcut⟩ := stepCut E a U f Y C c f₀ hS
  obtain ⟨N₁, C₁, hC₁, hG⟩ := (bdGrowth E a Ξ (q + 1) _).1 hM
  obtain ⟨N₂, K, hK, hE⟩ := exp_bound D C c hD hS.c_pos
  have hq := (qhtFacts E a).1
  have hfr : ∀ g, f (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1 = f g := fun g => by
    obtain ⟨t, ht⟩ := (retrFacts E a).1 g
    have := hS.f_left 1 t g
    rw [map_one, one_mul] at this
    rw [ht, this]
  refine ⟨N₁ + N₂, C₁ + (q + 1) * B * K, by positivity, fun R => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_ge ((|C| * (1 + Real.log (max R 1)) + 1) / c)
  rw [div_le_iff₀ hS.c_pos] at hn
  obtain ⟨η', hη', hd, hb⟩ := hP n
  obtain ⟨u, hu, hU⟩ := hcut (n * c - 1)
  obtain ⟨ζ, hζ, hmul, hdζ⟩ := mulEx E a U Ξ q u η' hu hη'
  have hfar : ∀ g, Real.exp (|C| * (1 + n * c)) < qht g → n * c - 1 + 1 ≤ f g := fun g hg => by
    by_contra hcon
    have h0 : f g ≤ n * c := by linarith
    have h1 : Real.log (qht g) ≤ |C| * (1 + n * c) :=
      (hS.le_f g).trans (mul_le_mul (le_abs_self C) (by linarith) (by linarith [hS.f_nonneg g]) (abs_nonneg C))
    have h2 := Real.exp_le_exp.2 h1
    rw [Real.exp_log (one_pos.trans_le (hq g))] at h2
    linarith
  refine ⟨ζ, hζ, ⟨Real.exp (|C| * (1 + n * c)), fun X g hg => ?_⟩, ⟨Real.exp (|C| * (1 + n * c)), fun X g hg => ?_⟩, fun g => ?_⟩
  · rw [hmul X g, ((hU g).2.2 (hfar g hg)).1, zero_smul]
  · rw [hdζ X g, ((hU g).2.2 (hfar g hg)).1, zero_smul, zero_add]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [((hU g).2.2 (hfar g hg)).2, mul_zero, zero_smul]
  have hcb := cutBd E a Ξ q u η' ζ hdζ g
  rw [hd] at hcb
  have q1 := hq g
  have hM' : 0 ≤ C₁ * qht g ^ N₁ := by positivity
  have near : f g ≤ n * c - 1 → Bd (Ξ := Ξ) (dCo (smLie Ξ) η - dCo (smLie Ξ) ζ) g 0 := fun h => by
    have h1 := (hU _).2.1 ((hfr g).trans_le h)
    refine (hcb 0 0 0 _ le_rfl hM' le_rfl (by rw [h1.1]; simp) (fun X => by rw [h1.2]; simp) (Or.inl rfl) (hG g)).mono ?_
    simp
  have hs : ‖1 - u.1 (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1‖ ≤ 1 := by
    obtain ⟨t, t0, t1, ht⟩ := hu.range (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1
    rw [ht, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have p1 : qht g ^ N₁ ≤ qht g ^ (N₁ + N₂) := pow_le_pow_right₀ q1 (by omega)
  have p2 : qht g ^ N₂ ≤ qht g ^ (N₁ + N₂) := pow_le_pow_right₀ q1 (by omega)
  have p3 : C₁ * qht g ^ N₁ ≤ C₁ * qht g ^ (N₁ + N₂) := mul_le_mul_of_nonneg_left p1 hC₁
  refine ⟨fun hg => near ?_, ?_⟩
  · have h1 : Real.log (qht g) ≤ Real.log (max R 1) :=
      Real.log_le_log (one_pos.trans_le q1) (hg.trans (le_max_left _ _))
    have h2 : f g ≤ |C| * (1 + Real.log (max R 1)) :=
      (hS.f_le g).trans (mul_le_mul (le_abs_self C) (by linarith) (by linarith [Real.log_nonneg q1]) (abs_nonneg C))
    linarith
  by_cases h1 : f g ≤ n * c - 1
  · exact (near h1).mono (by positivity)
  by_cases h2 : f g ≤ n * c
  · refine (hcb 1 B _ _ (Real.exp_pos _).le hM' hB hs (hU _).1 (Or.inr (hb g h2)) (hG g)).mono ?_
    have h3 := (hE n _ _ q1 (hS.f_le g) (not_le.1 h1).le).trans (mul_le_mul_of_nonneg_left p2 hK)
    have h4 := mul_le_mul_of_nonneg_left h3 (show (0 : ℝ) ≤ (q + 1) * B by positivity)
    nlinarith
  · have h3 := (hU _).2.2 (show n * c - 1 + 1 ≤ _ by rw [hfr g]; linarith)
    refine (hcb 1 0 0 _ le_rfl hM' le_rfl hs (fun X => by rw [h3.2]; simp) (Or.inl rfl) (hG g)).mono ?_
    have h4 : (0 : ℝ) ≤ (q + 1) * B * K * qht g ^ (N₁ + N₂) := by positivity
    nlinarith
