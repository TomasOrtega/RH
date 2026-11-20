import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformHeightConstant
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.IntegralCuspSlopePowerBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ShortGeneratorNormComparison
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsCuspRegularLevelDeterminant
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringDomainLatticeRegularity
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TamagawaPeterssonLambdaSqNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformHeightConstantStatement

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.ShortDet
section Weight
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
end Weight
set_option maxHeartbeats 1600000 in
/- English proof (translation)
Introduce `hP hGr hQ hS hK hN`. Take `⟨C₁, hC₁, hb⟩` from `_root_.UpperTheory.Lit.Tam.tamagawa_number_formula hP`. Take `⟨C₃, hC₃, h3⟩` from `_root_.GlobalTheory.T.short_generator_norm_comparison hP`. Use `⟨C₃ + 240 + C₁ + 2 * C₃, by positivity, ?_⟩` and prove the remaining obligations. Introduce `D T hT j hp hq hE hj Y e o hG Lb hL hM hF hfr ho c₁ hc hc' he hg hf hr fr`.

Take `⟨-, -, -, -, -, hdeg, hJ⟩` from `GlobalTheory.PinNum.numerics_of_pins D T.Q hT.pins`. Take `⟨hpq, -, -⟩` from `hJ j hj`. Take `⟨hp', hq', -⟩` from `hT.pins.2.2.2 j hj`. Take `⟨-, h0, hcz⟩` from `cZero_spec D j`. Establish `hgap : ((8 * D.R.f * D.R.r + 10 : ℕ) : ℤ) ≤ cZero D j`.

Establish `h1` using `(cZeroN_isLeast D j).1.2.1`. Establish `h2` using `le_choose hf hr hp hq hpq`. Rewrite `h2` using `[hp', hq']`. Conclude with `Int.ofNat_le.2 (by omega)`. Establish `hanti` using `antitone_smul_hodgeWt (T.Q.Dw j) h0`.

Establish `hgp` using `gap_smul_hodgeWt (T.Q.Dw j) hp hq (cZero D j)`. Establish `hsz` using `size_smul_hodgeWt (T.Q.Dw j) h0`. Establish `hcard` using `card_levelAut_le (T.Q.Dw j) Y.d.l₂`. Rewrite `hsz` using `[hdeg, congrArg (Nat.cast : ℕ → ℝ) hpq]`. Rewrite `hcard` using `[hdeg, hpq, Nat.mul_div_cancel_left _ two_pos]`.

Establish `hf' : (8 : ℝ) ≤ D.R.f` using `by exact_mod_cast hf`. Establish `hr' : (100 : ℝ) ≤ D.R.r` using `by exact_mod_cast hr`. Establish `hcz' : (cZero D j : ℝ) ≤ 22 * (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 4` using `by exact_mod_cast hcz`. Establish `hs0 : 0 ≤ ∑ τ, ∑ k, |((cZero D j • hodgeWt (T.Q.Dw j)) τ k : ℝ)|` using `by positivity`. Establish `hb'` using `hb D T hT j hp hq hE hj Y e o hG Lb hL hM hF hfr ho _ hanti`.

Establish `h3'` using `h3 D T hT j hp hq hE hj Y e o hG Lb hL hM hF hfr ho c₁ hc hc' _ hanti fun τ => (hgp τ).symm ▸ hgap`. Generalize the expression as in `∑ τ, ∑ k, |((cZero D j • hodgeWt (T.Q.Dw j)) τ k : ℝ)| = s at hs0 hsz hb' h3'`. Establish `ha : (1 : ℝ) ≤ D.R.f * D.R.r` using `by nlinarith`. Establish `hs : s ≤ ((D.R.f : ℝ) * D.R.r) ^ 5`. Use `hsz.trans ?_` and prove the remaining obligations.

Use `push_cast`. Combine the equalities or inequalities in the displayed calculation. Establish `hls : Real.log s ≤ 5 * Lb`. Break down `hs0.eq_or_lt with rfl | h` into its components or cases. Rewrite using `[Real.log_zero]`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `(Real.log_le_log h hs).trans ?_` and prove the remaining obligations. Rewrite using `[Real.log_pow]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hcard' : (Nat.card (grpHR fr) : ℝ) ≤ Real.exp (120 * ((D.R.f : ℝ) * D.R.r) ^ 2 * Lb)`. Establish `h1 : (Nat.card (grpHR fr) : ℝ) ≤ (Y.d.l₂.M : ℝ) ^ (2 * (D.R.f * D.R.r)) ^ 2`. Conclude with `(Subgroup.card_le_card_group _).trans hcard` after adjusting the coercions. Use `h1.trans ((pow_le_pow_left₀ (by positivity) ((Real.le_exp_log _).trans (Real.exp_le_exp.2 hM)) _).trans ?_)` and prove the remaining obligations. Rewrite using `[← Real.exp_nat_mul]`.

Use `push_cast`. Conclude with `le_of_eq (by congr 1; ring)`. Establish `haZ : (D.R.f : ℝ) * D.R.r ≤ D.R.f * D.R.r * Lb` using `le_mul_of_one_le_right (by positivity) hL`. Establish `hZ2 : ((D.R.f : ℝ) * D.R.r) ^ 2 * Lb ≤ (D.R.f * D.R.r * Lb) ^ 2`. Rewrite using `[mul_pow _ Lb]`.

Use `gcongr`. Use the polynomial consequences of the given equalities and inequalities. Use `replace hs := hs.trans (pow_le_pow_left₀ (by positivity) haZ 5)`. Establish `hZ` using `ha.trans haZ`. Rewrite `hcard'` using `[mul_assoc]`.

Generalize the expression as in `(D.R.f : ℝ) * D.R.r * Lb = Z at hb' h3' hs hZ hZ2 ⊢`. Establish `hw : ∀ k, k ≤ 9 → Z ^ k ≤ Z ^ 9` using `fun k hk => pow_le_pow_right₀ hZ hk`. Establish `hA : Y.d.l₂.A.Coprime Y.d.l₂.M` using `by rw [hG.lev.2]; exact Nat.coprime_one_left _`. Establish `hpos : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q` using `by omega`. Take `⟨u₀, h₀, hd₀⟩` from `_root_.GlobalTheory.T.orbits_separated_by_regular_cusp hP hGr hQ hS hK hN D T hT j hp hq hE hj Y e o hG he hg fr _ (Or.inl rfl)`.

Take `⟨u, hu, hd, hsup⟩` from `exists_short (β := Real.exp (C₁ * Z ^ 3)) (Λ := Real.exp (2 * C₃ * Z ^ 9)) (N := Real.exp (C₃ * Z ^ 3)) hpos hA hG.unf (grpHR fr) _ (Real.one_le_exp (by positivity)) (Real.exp_pos _).le (Real.exp_pos _).le (fun W => (hb' (by linarith) W).2.1) (fun W => ((_root_.GlobalTheory.T.cov …`. Take `⟨n, w, abelian₂, a1, a2, a3⟩` from `h3' (by linarith) W`. Use `⟨n, w, abelian₂, a1, (Real.le_exp_log _).trans (Real.exp_le_exp.2 (a2.trans ?_)), (Real.le_exp_log _).trans (Real.exp_le_exp.2 a3)⟩` and prove the remaining obligations. Establish `h1 : Z ^ 3 * s ≤ Z ^ 8` using `(mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (by ring)`. Establish `h2` using `hw 8 (by norm_num)`.

Establish `h4` using `hw 5 (by norm_num)`. Rewrite using `[mul_comm 2, mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left (by linarith) hC₃) h₀ hd₀`. Use `⟨u, hu, hd, normW_mul_pull_le hpos hA (fun σ hσ => ?_) (fun G hGe => ?_) (AllWt.even_wtOf _ _) (Real.exp_pos _).le fun σ z => (hsup σ z).trans ?_⟩` and prove the remaining obligations. Take `⟨th, hr, -, h⟩` from `hG.dictU σ hσ`.

Conclude with `h.2.2.2.1`. Take `⟨k₁, k₂⟩` from `GlobalTheory.LevelIsometry.keeps_cusp_lattice_norm D T hT j hp hq hE hj Y e o hG G hGe`. Conclude with `⟨k₁, fun γ f g h => (k₂ γ f g h).2⟩`. Use `(mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hcard' 2) (by positivity)) (by positivity)).trans ?_` and prove the remaining obligations. Rewrite using `[← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]`.

Establish `h1` using `mul_le_mul_of_nonneg_left (hw 3 (by norm_num)) hC₁`. Establish `h2` using `mul_le_mul_of_nonneg_left (hw 3 (by norm_num)) hC₃`. Establish `h4` using `hw 2 (by norm_num)`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_short_integral_vector : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → |c₁| ≤ 9 * D.R.r * Lb → 4 ≤ e → (∀ k, D.R.r + 1 < D.host.g k) → 8 ≤ D.R.f → 100 ≤ D.R.r → ∀ (fr : TypeFrame (T.Q.Dw j) Y.d.l₂), ∃ u : Y.V (wtOf (T.Q.Dw j) (cZero D j • hodgeWt (T.Q.Dw j)) 0), u ∈ AllWt.latW Y.U _ ∧ (∀ f ∈ secRing Y.d.Xo₂ Y.d.c₂, levDet Y.d.Xo₂ Y.d.c₂ (grpHR fr) u * f = 0 → f = 0) ∧ ∀ (γ : (LevelAut (T.Q.Dw j) Y.d.l₂)) (G : WTZ D.host.E) (f : Y.V G) (g : Y.V (G + (wtOf (T.Q.Dw j) (cZero D j • hodgeWt (T.Q.Dw j)) 0))), Even G.2 → (g : Rul Y.d.Xo₂ Y.d.c₂) = f * pull Y.d.Xo₂ Y.d.c₂ γ u → ∀ σ, Y.nrm _ σ g ≤ Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 9) * Y.nrm G σ f := by
  intro hP hGr hQ hS hK hN
  obtain ⟨C₁, hC₁, hb⟩ := _root_.UpperTheory.Lit.Tam.tamagawa_number_formula hP
  obtain ⟨C₃, hC₃, h3⟩ := _root_.GlobalTheory.T.short_generator_norm_comparison hP
  refine ⟨C₃ + 240 + C₁ + 2 * C₃, by positivity, ?_⟩
  intro D T hT j hp hq hE hj Y e o hG Lb hL hM hF hfr ho c₁ hc hc' he hg hf hr fr
  obtain ⟨-, -, -, -, -, hdeg, hJ⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q hT.pins
  obtain ⟨hpq, -, -⟩ := hJ j hj
  obtain ⟨hp', hq', -⟩ := hT.pins.2.2.2 j hj
  obtain ⟨-, h0, hcz⟩ := cZero_spec D j
  have hgap : ((8 * D.R.f * D.R.r + 10 : ℕ) : ℤ) ≤ cZero D j := by
    have h1 := (cZeroN_isLeast D j).1.2.1
    have h2 := le_choose hf hr hp hq hpq
    rw [hp', hq'] at h2
    exact Int.ofNat_le.2 (by omega)
  have hanti := antitone_smul_hodgeWt (T.Q.Dw j) h0
  have hgp := gap_smul_hodgeWt (T.Q.Dw j) hp hq (cZero D j)
  have hsz := size_smul_hodgeWt (T.Q.Dw j) h0
  have hcard := card_levelAut_le (T.Q.Dw j) Y.d.l₂
  rw [hdeg, congrArg (Nat.cast : ℕ → ℝ) hpq] at hsz
  rw [hdeg, hpq, Nat.mul_div_cancel_left _ two_pos] at hcard
  have hf' : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hr' : (100 : ℝ) ≤ D.R.r := by exact_mod_cast hr
  have hcz' : (cZero D j : ℝ) ≤ 22 * (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 4 := by exact_mod_cast hcz
  have hs0 : 0 ≤ ∑ τ, ∑ k, |((cZero D j • hodgeWt (T.Q.Dw j)) τ k : ℝ)| := by positivity
  have hb' := hb D T hT j hp hq hE hj Y e o hG Lb hL hM hF hfr ho _ hanti
  have h3' := h3 D T hT j hp hq hE hj Y e o hG Lb hL hM hF hfr ho c₁ hc hc' _ hanti fun τ => (hgp τ).symm ▸ hgap
  generalize ∑ τ, ∑ k, |((cZero D j • hodgeWt (T.Q.Dw j)) τ k : ℝ)| = s at hs0 hsz hb' h3'
  have ha : (1 : ℝ) ≤ D.R.f * D.R.r := by nlinarith
  have hs : s ≤ ((D.R.f : ℝ) * D.R.r) ^ 5 := by
    refine hsz.trans ?_
    push_cast
    calc _ ≤ 2 * (D.R.f : ℝ) * (D.R.r * (22 * (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 4)) := by gcongr
      _ = 44 * ((D.R.f : ℝ) ^ 3 * (D.R.r : ℝ) ^ 5) := by ring
      _ ≤ (D.R.f : ℝ) ^ 2 * ((D.R.f : ℝ) ^ 3 * (D.R.r : ℝ) ^ 5) := by gcongr; nlinarith
      _ = _ := by ring
  have hls : Real.log s ≤ 5 * Lb := by
    rcases hs0.eq_or_lt with rfl | h
    · rw [Real.log_zero]; linarith
    · refine (Real.log_le_log h hs).trans ?_
      rw [Real.log_pow]; push_cast; linarith
  have hcard' : (Nat.card (grpHR fr) : ℝ) ≤ Real.exp (120 * ((D.R.f : ℝ) * D.R.r) ^ 2 * Lb) := by
    have h1 : (Nat.card (grpHR fr) : ℝ) ≤ (Y.d.l₂.M : ℝ) ^ (2 * (D.R.f * D.R.r)) ^ 2 := by
      exact_mod_cast (Subgroup.card_le_card_group _).trans hcard
    refine h1.trans ((pow_le_pow_left₀ (by positivity) ((Real.le_exp_log _).trans (Real.exp_le_exp.2 hM)) _).trans ?_)
    rw [← Real.exp_nat_mul]
    push_cast
    exact le_of_eq (by congr 1; ring)
  have haZ : (D.R.f : ℝ) * D.R.r ≤ D.R.f * D.R.r * Lb := le_mul_of_one_le_right (by positivity) hL
  have hZ2 : ((D.R.f : ℝ) * D.R.r) ^ 2 * Lb ≤ (D.R.f * D.R.r * Lb) ^ 2 := by
    rw [mul_pow _ Lb]; gcongr; nlinarith
  replace hs := hs.trans (pow_le_pow_left₀ (by positivity) haZ 5)
  have hZ := ha.trans haZ
  rw [mul_assoc] at hcard'
  generalize (D.R.f : ℝ) * D.R.r * Lb = Z at hb' h3' hs hZ hZ2 ⊢
  have hw : ∀ k, k ≤ 9 → Z ^ k ≤ Z ^ 9 := fun k hk => pow_le_pow_right₀ hZ hk
  have hA : Y.d.l₂.A.Coprime Y.d.l₂.M := by rw [hG.lev.2]; exact Nat.coprime_one_left _
  have hpos : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  obtain ⟨u₀, h₀, hd₀⟩ := _root_.GlobalTheory.T.orbits_separated_by_regular_cusp hP hGr hQ hS hK hN D T hT j hp hq hE hj Y e o hG he hg fr _ (Or.inl rfl)
  obtain ⟨u, hu, hd, hsup⟩ := exists_short (β := Real.exp (C₁ * Z ^ 3)) (Λ := Real.exp (2 * C₃ * Z ^ 9))
    (N := Real.exp (C₃ * Z ^ 3)) hpos hA hG.unf (grpHR fr) _ (Real.one_le_exp (by positivity)) (Real.exp_pos _).le
    (Real.exp_pos _).le (fun W => (hb' (by linarith) W).2.1)
    (fun W => ((_root_.GlobalTheory.T.covering_domain_lattice_regularity hP D T hT j hp hq hE hj Y e o hG _ hanti fun τ => by rw [hgp]; omega).2 W).2.2)
    (fun W => by
      obtain ⟨n, w, abelian₂, a1, a2, a3⟩ := h3' (by linarith) W
      refine ⟨n, w, abelian₂, a1, (Real.le_exp_log _).trans (Real.exp_le_exp.2 (a2.trans ?_)),
        (Real.le_exp_log _).trans (Real.exp_le_exp.2 a3)⟩
      have h1 : Z ^ 3 * s ≤ Z ^ 8 := (mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (by ring)
      have h2 := hw 8 (by norm_num)
      have h4 := hw 5 (by norm_num)
      rw [mul_comm 2, mul_assoc]
      exact mul_le_mul_of_nonneg_left (by linarith) hC₃) h₀ hd₀
  refine ⟨u, hu, hd, normW_mul_pull_le hpos hA (fun σ hσ => ?_) (fun G hGe => ?_) (AllWt.even_wtOf _ _) (Real.exp_pos _).le
    fun σ z => (hsup σ z).trans ?_⟩
  · obtain ⟨th, hr, -, h⟩ := hG.dictU σ hσ
    exact h.2.2.2.1
  · obtain ⟨k₁, k₂⟩ := GlobalTheory.LevelIsometry.keeps_cusp_lattice_norm D T hT j hp hq hE hj Y e o hG G hGe
    exact ⟨k₁, fun γ f g h => (k₂ γ f g h).2⟩
  · refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hcard' 2)
      (by positivity)) (by positivity)).trans ?_
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    have h1 := mul_le_mul_of_nonneg_left (hw 3 (by norm_num)) hC₁
    have h2 := mul_le_mul_of_nonneg_left (hw 3 (by norm_num)) hC₃
    have h4 := hw 2 (by norm_num)
    push_cast
    linarith
end GlobalTheory.ShortDet
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.ShortDet.exists_short_integral_vector | exact _root_.GlobalTheory.ShortDet.exists_short_integral_vector | (intros; apply _root_.GlobalTheory.ShortDet.exists_short_integral_vector <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.exists_short_integral_vector_of_determinant_bound : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → |c₁| ≤ 9 * D.R.r * Lb → 4 ≤ e → (∀ k, D.R.r + 1 < D.host.g k) → 8 ≤ D.R.f → 100 ≤ D.R.r → ∀ (fr : TypeFrame (T.Q.Dw j) Y.d.l₂), ∃ u : Y.V (wtOf (T.Q.Dw j) (cZero D j • hodgeWt (T.Q.Dw j)) 0), u ∈ AllWt.latW Y.U _ ∧ (∀ f ∈ secRing Y.d.Xo₂ Y.d.c₂, levDet Y.d.Xo₂ Y.d.c₂ (grpHR fr) u * f = 0 → f = 0) ∧ ∀ (γ : (LevelAut (T.Q.Dw j) Y.d.l₂)) (G : WTZ D.host.E) (f : Y.V G) (g : Y.V (G + (wtOf (T.Q.Dw j) (cZero D j • hodgeWt (T.Q.Dw j)) 0))), Even G.2 → (g : Rul Y.d.Xo₂ Y.d.c₂) = f * pull Y.d.Xo₂ Y.d.c₂ γ u → ∀ σ, Y.nrm _ σ g ≤ Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 9) * Y.nrm G σ f := by
  first | exact @_root_.GlobalTheory.ShortDet.exists_short_integral_vector | exact _root_.GlobalTheory.ShortDet.exists_short_integral_vector | (intros; apply _root_.GlobalTheory.ShortDet.exists_short_integral_vector <;> assumption)
end
