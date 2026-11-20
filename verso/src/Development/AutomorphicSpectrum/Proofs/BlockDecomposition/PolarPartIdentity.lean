import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableSchwartzAHaar

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.RswPolar

variable {D : D7} {n ρ p : ℕ}

/- English proof (translation)
Simplify using `only [npow, NNReal.coe_mul, Complex.ofReal_mul]`. Conclude with `Complex.mul_cpow_ofReal_nonneg a.2 b.2 w`.
-/
theorem npow_mul' {a b : ℝ≥0} (w : ℂ) : npow (a * b) w = npow a w * npow b w := by
  simp only [npow, NNReal.coe_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg a.2 b.2 w

/- English proof (translation)
Simplify using `only [npow]`. Conclude with `Complex.cpow_add _ _ (by exact_mod_cast ha)`.
-/
theorem npow_add' {a : ℝ≥0} (ha : a ≠ 0) (v w : ℂ) : npow a (v + w) = npow a v * npow a w := by
  simp only [npow]
  exact Complex.cpow_add _ _ (by exact_mod_cast ha)

/- English proof (translation)
Introduce `h0`. Establish `h1` using `hH.2.1 (q * 1)`. Rewrite `h1` using `[hH.2.2 q hq a ha 1, h0, zero_mul]`. Conclude with `lt_irrefl _ h1`.
-/
theorem absA_ne_zero_of_ht {H : G D n → ℝ≥0} (hH : IsHt H) {q : G D n} (hq : q ∈ P D n)
    {a : GL (Fin n) (AE D)} (ha : blkA (mat q) = a.1) :
    absA D (Matrix.GeneralLinearGroup.det a) ≠ 0 := by
  intro h0
  have h1 := hH.2.1 (q * 1)
  rw [hH.2.2 q hq a ha 1, h0, zero_mul] at h1
  exact lt_irrefl _ h1

/- English proof (translation)
Introduce `q hq a ha g`. Establish `hA` using `absA_ne_zero_of_ht hH hq ha`. Establish `e : npow (absA D (Matrix.GeneralLinearGroup.det a)) (z + (n : ℂ) / 2) = npow (absA D (Matrix.GeneralLinearGroup.det a)) (z - s₁) * npow (absA D (Matrix.GeneralLinearGroup.det a)) (s₁ + (n : ℂ) / 2)`. Rewrite using `[← npow_add' hA]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [fam]`. Rewrite using `[hH.2.2 q hq a ha g, hφ q hq a ha g, npow_mul', e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isLaw_fam {H : G D n → ℝ≥0} (hH : IsHt H) {χ : (AE D)ˣ →* Circle} {s₁ : ℂ} {φ : G D n → ℂ}
    (hφ : IsLaw χ s₁ φ) (z : ℂ) : IsLaw χ z (fam H φ s₁ z) := by
  intro q hq a ha g
  have hA := absA_ne_zero_of_ht hH hq ha
  have e : npow (absA D (Matrix.GeneralLinearGroup.det a)) (z + (n : ℂ) / 2) =
      npow (absA D (Matrix.GeneralLinearGroup.det a)) (z - s₁) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) (s₁ + (n : ℂ) / 2) := by
    rw [← npow_add' hA]
    congr 1
    ring
  simp only [fam]
  rw [hH.2.2 q hq a ha g, hφ q hq a ha g, npow_mul', e]
  ring

/- English proof (translation)
Establish `h1 : Continuous fun g => ((H g : ℝ) : ℂ)` using `Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp hH.1)`. Use `Continuous.mul (h1.cpow continuous_const fun g => ?_) hφ` and prove the remaining obligations. Conclude with `Complex.ofReal_mem_slitPlane.2 (by exact_mod_cast hH.2.1 g)`.
-/
theorem continuous_fam {H : G D n → ℝ≥0} (hH : IsHt H) {φ : G D n → ℂ} (hφ : Continuous φ) (s₁ z : ℂ) :
    Continuous (fam H φ s₁ z) := by
  have h1 : Continuous fun g => ((H g : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp hH.1)
  refine Continuous.mul (h1.cpow continuous_const fun g => ?_) hφ
  exact Complex.ofReal_mem_slitPlane.2 (by exact_mod_cast hH.2.1 g)

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `[fam, npow]`.
-/
theorem fam_self (H : G D n → ℝ≥0) (φ : G D n → ℂ) (s₁ : ℂ) : fam H φ s₁ s₁ = φ := by
  funext g
  simp [fam, npow]

section Homog

variable {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ)

/- English proof (translation)
Simplify using `only [zc, mul_assoc]`. Conclude with `integral_const_mul _ _`.
-/
theorem zc_const_mul (c : ℂ) (F : G D n → ℂ) (g : G D n) :
    zc M m ψ b₀ (fun x => c * F x) g = c * zc M m ψ b₀ F g := by
  simp only [zc, mul_assoc]
  exact integral_const_mul _ _

/- English proof (translation)
Simplify using `only [PositivityTheory.Rg.Rsw.pc, zc_const_mul]`. Conclude with `integral_const_mul _ _`.
-/
theorem pc_const_mul (c : ℂ) (F : G D n → ℂ) (g : G D n) :
    pc M m ψ b₀ (fun x => c * F x) g = c * pc M m ψ b₀ F g := by
  simp only [PositivityTheory.Rg.Rsw.pc, zc_const_mul]
  exact integral_const_mul _ _

/- English proof (translation)
Simplify using `only [FJ, pc_const_mul, mul_assoc]`. Conclude with `integral_const_mul _ _`.
-/
theorem FJ_const_mul (c : ℂ) (F : G D n → ℂ) (g : G D n) (η : Mx D ρ p → ℂ) :
    FJ M m ψ b₀ (fun x => c * F x) g η = c * FJ M m ψ b₀ F g η := by
  simp only [FJ, pc_const_mul, mul_assoc]
  exact integral_const_mul _ _

end Homog

/- English proof (translation)
Use `haveI := m.hμ.1`. Conclude with `GlobalTheory.CompanionTheory.WSum.integrable_schwartzA_haar D θ hθ ρ p m.μ _ (hΩ.mem 1)`.
-/
theorem integrable_th {ψ : AddChar (AF D.host.F) ℂ} {χ' : (AE D)ˣ →* Circle} {θ : InfFam D} (hθ : IsInfFam θ)
    {b₀ : HermE D ρ} (m : Meas D ρ p) {Ω : G D p → Mx D ρ p → ℂ} (hΩ : IsTh ψ χ' θ b₀ m.μ Ω) :
    Integrable (Ω 1) m.μ := by
  haveI := m.hμ.1
  exact GlobalTheory.CompanionTheory.WSum.integrable_schwartzA_haar D θ hθ ρ p m.μ _ (hΩ.mem 1)

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1.mul h'.1.inv, fun x => by show χ _ * (χ' _)⁻¹ = 1 rw [h.2 x, h'.2 x] simp⟩`.
-/
theorem hecke_mul_inv {χ χ' : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) (h' : IsHeckeChar D χ') :
    IsHeckeChar D (χ * χ'⁻¹) :=
  ⟨h.1.mul h'.1.inv, fun x => by
    show χ _ * (χ' _)⁻¹ = 1
    rw [h.2 x, h'.2 x]
    simp⟩

/- English proof (translation)
Take `⟨hRc, hRd, hRl⟩` from `hRS D n ρ p hn M m ψ hψ b₀ hb χ χ' hχ hχ' θ hθ Ω hΩ H hH s₀ φ hφ hlaw g`. Establish `hGd : DifferentiableOn ℂ (fun z => eisS (Rsec M m ψ b₀ (fam H φ s₀ z) g Ω) 1) {z : ℂ | max (((ρ : ℝ) - p) / 2) ((p : ℝ) / 2) < z.re}` using `(hEH D p (χ * χ'⁻¹) (hecke_mul_inv hχ hχ') (((ρ : ℝ) - p) / 2) (fun z => Rsec M m ψ b₀ (fam H φ s₀ z) g Ω) hRc hRd hRl 1).mono fun z hz => ⟨(le_max_left _ _).trans_lt hz, (le_max_right _ _).trans_lt hz⟩`. Establish `hHd : DifferentiableOn ℂ (fun z => FJ M m ψ b₀ (E z) g (Ω 1)) U` using `((hCf D n H φ s₀ U d E σ hc ε hrad).2.2 ρ p hn M m ψ hψ b₀ g (Ω 1) (integrable_th hθ m hΩ)).1`. Use `⟨hHd, hGd, ?_⟩` and prove the remaining obligations. Introduce `z hz hzc`.

Use `hId U _ (fun z => d.eval z * eisS (Rsec M m ψ b₀ (fam H φ s₀ z) g Ω) 1) (max (((ρ : ℝ) - p) / 2) ((p : ℝ) / 2)) (max σ ((n : ℝ) / 2)) hc.isOpen hc.right hHd (d.differentiable.differentiableOn.mul hGd) ?_ z hz hzc` and prove the remaining obligations. Introduce `w hw`. Establish `h1 : σ < w.re` using `(le_max_left _ _).trans_lt hw`. Establish `h2 : (n : ℝ) / 2 < w.re` using `(le_max_right _ _).trans_lt hw`. Establish `e : E w = fun x => d.eval w * eisS (fam H φ s₀ w) x` using `funext fun x => hc.eq w h1 x`.

Simplify using `only [e]`. Rewrite using `[FJ_const_mul, hFJ D n ρ p hn M m ψ hψ b₀ hb χ χ' hχ hχ' θ hθ Ω hΩ w _ (continuous_fam hH hφ s₀ w) (isLaw_fam hH hlaw w) h2 g]`.
-/
theorem fj_eq (hFJ : FJEis) (hRS : RSec) (hEH : EisHol) (hId : RightId) (hCf : CfFJ)
    {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    {b₀ : HermE D ρ} (hb : b₀.1.det ≠ 0) {χ χ' : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hχ' : IsHeckeChar D χ')
    {θ : InfFam D} (hθ : IsInfFam θ) {Ω : G D p → Mx D ρ p → ℂ} (hΩ : IsTh ψ χ' θ b₀ m.μ Ω)
    {H : G D n → ℝ≥0} (hH : IsHt H) {φ : G D n → ℂ} (hφ : Continuous φ) {s₀ : ℂ} (hlaw : IsLaw χ s₀ φ)
    {U : Set ℂ} {d : Polynomial ℂ} {E : ℂ → G D n → ℂ} {σ : ℝ} (hc : IsCont H φ s₀ U d E σ)
    {ε : ℝ} (hrad : IsRad U d s₀ ε) (g : G D n) :
    DifferentiableOn ℂ (fun z => FJ M m ψ b₀ (E z) g (Ω 1)) U ∧
    DifferentiableOn ℂ (fun z => eisS (Rsec M m ψ b₀ (fam H φ s₀ z) g Ω) 1)
      {z : ℂ | max (((ρ : ℝ) - p) / 2) ((p : ℝ) / 2) < z.re} ∧
    ∀ z ∈ U, max (((ρ : ℝ) - p) / 2) ((p : ℝ) / 2) < z.re →
      FJ M m ψ b₀ (E z) g (Ω 1) = d.eval z * eisS (Rsec M m ψ b₀ (fam H φ s₀ z) g Ω) 1 := by
  obtain ⟨hRc, hRd, hRl⟩ := hRS D n ρ p hn M m ψ hψ b₀ hb χ χ' hχ hχ' θ hθ Ω hΩ H hH s₀ φ hφ hlaw g
  have hGd : DifferentiableOn ℂ (fun z => eisS (Rsec M m ψ b₀ (fam H φ s₀ z) g Ω) 1)
      {z : ℂ | max (((ρ : ℝ) - p) / 2) ((p : ℝ) / 2) < z.re} :=
    (hEH D p (χ * χ'⁻¹) (hecke_mul_inv hχ hχ') (((ρ : ℝ) - p) / 2)
      (fun z => Rsec M m ψ b₀ (fam H φ s₀ z) g Ω) hRc hRd hRl 1).mono
      fun z hz => ⟨(le_max_left _ _).trans_lt hz, (le_max_right _ _).trans_lt hz⟩
  have hHd : DifferentiableOn ℂ (fun z => FJ M m ψ b₀ (E z) g (Ω 1)) U :=
    ((hCf D n H φ s₀ U d E σ hc ε hrad).2.2 ρ p hn M m ψ hψ b₀ g (Ω 1) (integrable_th hθ m hΩ)).1
  refine ⟨hHd, hGd, ?_⟩
  intro z hz hzc
  refine hId U _ (fun z => d.eval z * eisS (Rsec M m ψ b₀ (fam H φ s₀ z) g Ω) 1)
    (max (((ρ : ℝ) - p) / 2) ((p : ℝ) / 2)) (max σ ((n : ℝ) / 2)) hc.isOpen hc.right hHd
    (d.differentiable.differentiableOn.mul hGd) ?_ z hz hzc
  intro w hw
  have h1 : σ < w.re := (le_max_left _ _).trans_lt hw
  have h2 : (n : ℝ) / 2 < w.re := (le_max_right _ _).trans_lt hw
  have e : E w = fun x => d.eval w * eisS (fam H φ s₀ w) x := funext fun x => hc.eq w h1 x
  simp only [e]
  rw [FJ_const_mul,
    hFJ D n ρ p hn M m ψ hψ b₀ hb χ χ' hχ hχ' θ hθ Ω hΩ w _ (continuous_fam hH hφ s₀ w) (isLaw_fam hH hlaw w) h2 g]

/- English proof (translation)
Use `(hPc D n ρ p hn M m ψ hψ F hF hl).1 ?_` and prove the remaining obligations. Introduce `b₀ hb g`. Take `⟨hc, hbd⟩` from `hPB D n ρ p hn M m ψ hψ b₀`. Establish `key : ∀ g', (fun y => pc M m ψ b₀ F (M.sh y * g')) = 0`. Introduce `g'`.

Take `⟨C, hC, -, hB⟩` from `hbd g'`. Take `⟨B, hBC⟩` from `hC.exists_bound_of_continuousOn hF.continuousOn`. Use `hTh D ρ p m ψ hψ b₀ hb χ' hχ' hres h0 θ hθ _ ?_ ⟨B, fun y => hB F hF hl B hBC y⟩ ?_` and prove the remaining obligations. Conclude with `(hc F hF hl).comp (M.sh_cont.mul continuous_const)`. Introduce `Ω hΩ`.

Conclude with `hv b₀ hb Ω hΩ g'`. Establish `h1` using `congrFun (key ((M.sh 0)⁻¹ * g)) 0`. Simplify using `using h1`.
-/
theorem rank_of_FJ (hPB : PcBound) (hTh : ThTotal) (hPc : PcFc)
    {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    {χ' : (AE D)ˣ →* Circle} (hχ' : IsHeckeChar D χ') (hres : ResEta D χ' ρ) (h0 : ρ = 0 → χ' = 1)
    {θ : InfFam D} (hθ : IsInfFam θ) {F : G D n → ℂ} (hF : Continuous F) (hl : LeftInv (GF D n) F)
    (hv : ∀ b₀ : HermE D ρ, IsDiagInv b₀ → ∀ Ω, IsTh ψ χ' θ b₀ m.μ Ω → ∀ g, FJ M m ψ b₀ F g (Ω 1) = 0) :
    RankLT ψ F ρ := by
  refine (hPc D n ρ p hn M m ψ hψ F hF hl).1 ?_
  intro b₀ hb g
  obtain ⟨hc, hbd⟩ := hPB D n ρ p hn M m ψ hψ b₀
  have key : ∀ g', (fun y => pc M m ψ b₀ F (M.sh y * g')) = 0 := by
    intro g'
    obtain ⟨C, hC, -, hB⟩ := hbd g'
    obtain ⟨B, hBC⟩ := hC.exists_bound_of_continuousOn hF.continuousOn
    refine hTh D ρ p m ψ hψ b₀ hb χ' hχ' hres h0 θ hθ _ ?_ ⟨B, fun y => hB F hF hl B hBC y⟩ ?_
    · exact (hc F hF hl).comp (M.sh_cont.mul continuous_const)
    · intro Ω hΩ
      exact hv b₀ hb Ω hΩ g'
  have h1 := congrFun (key ((M.sh 0)⁻¹ * g)) 0
  simpa using h1

/- English proof (translation)
Take `⟨⟨H', hH'⟩, C, hCc, hPC⟩` from `hHt D p`. Take `⟨B₁, hB₁⟩` from `hS D p hp H' hH' {1} isCompact_singleton`. Establish `hHpos : ∀ x, 0 < (H' x : ℝ)` using `fun x => by exact_mod_cast hH'.2.1 x`. Establish `hden : Continuous fun u : ℝ × G D p => (H' u.2 : ℝ) ^ (u.1 + (p : ℝ) / 2)` using `Continuous.rpow (NNReal.continuous_coe.comp (hH'.1.comp continuous_snd)) (continuous_fst.add continuous_const) fun u => Or.inl (hHpos _).ne'`. Establish `hRc : ContinuousOn (fun u : ℝ × G D p => ‖f u.1 u.2‖ / (H' u.2 : ℝ) ^ (u.1 + (p : ℝ) / 2)) (Set.Icc ((p : ℝ) / 2) (p / 2 + 1) ×ˢ C)` using `ContinuousOn.div ((hcont.mono (Set.prod_mono subset_rfl (Set.subset_univ _))).norm) hden.continuousOn fun u _ => (Real.rpow_pos_of_pos (hHpos _) _).ne'`.

Take `⟨B₀, hB₀⟩` from `(isCompact_Icc.prod hCc).exists_bound_of_continuousOn hRc`. Establish `hpt : ∀ σ ∈ Set.Icc ((p : ℝ) / 2) (p / 2 + 1), ∀ x, ‖f σ x‖ ≤ |B₀| * (H' x : ℝ) ^ (σ + (p : ℝ) / 2)`. Introduce `σ hσ x`. Take `⟨q, hq, c, hc, rfl⟩` from `hPC x`. Take `⟨a, ha⟩` from `GlobalTheory.StdUnn.LeftInvSect.exists_blkA hq`.

Establish `hA0` using `absA_ne_zero_of_ht hH' hq ha`. Establish `hA : 0 < (absA D (Matrix.GeneralLinearGroup.det a) : ℝ)`. Conclude with `pos_iff_ne_zero.2 hA0` after adjusting the coercions. Establish `hc1 : ‖f σ c‖ ≤ |B₀| * (H' c : ℝ) ^ (σ + (p : ℝ) / 2)`. Establish `h1` using `(hB₀ (σ, c) ⟨hσ, hc⟩)`.

Establish `hpos` using `Real.rpow_pos_of_pos (hHpos c) (σ + (p : ℝ) / 2)`. Establish `h2 : ‖f σ c‖ / (H' c : ℝ) ^ (σ + (p : ℝ) / 2) ≤ |B₀|` using `(le_abs_self _).trans (h1.trans (le_abs_self _))`. Conclude with `(div_le_iff₀ hpos).1 h2`. Establish `hn : ‖npow (absA D (Matrix.GeneralLinearGroup.det a)) ((σ : ℂ) + (p : ℂ) / 2)‖ = (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ (σ + (p : ℝ) / 2)`. Simplify using `only [npow]`.

Rewrite using `[Complex.norm_cpow_eq_rpow_re_of_pos hA]`. Simplify using the standard rewrite rules. Rewrite using `[hlaw σ hσ q hq a ha c, hH'.2.2 q hq a ha c, NNReal.coe_mul, Real.mul_rpow hA.le (hHpos c).le, norm_mul, norm_mul, hn]`. Establish `hone : ‖(((1 : (AE D)ˣ →* Circle) (Matrix.GeneralLinearGroup.det a) : Circle) : ℂ)‖ = 1` using `by simp`. Rewrite using `[hone, one_mul]`.

Establish `hAp` using `Real.rpow_pos_of_pos hA (σ + (p : ℝ) / 2)`. Combine the equalities or inequalities in the displayed calculation. Use `⟨|B₀| * B₁, fun σ hσ => ?_⟩` and prove the remaining obligations. Take `⟨hsum, hle⟩` from `hB₁ σ hσ 1 rfl`. Establish `hσ' : σ ∈ Set.Icc ((p : ℝ) / 2) (p / 2 + 1)` using `⟨hσ.1.le, hσ.2⟩`.

Establish `hpos : 0 ≤ σ - (p : ℝ) / 2` using `by linarith [hσ.1]`. Establish `hE : ‖eisS (f σ) 1‖ ≤ |B₀| * ∑' q : GlobalTheory.Eis.Cosets (P D p) (GF D p), (H' ((q.out : GF D p) * 1) : ℝ) ^ (σ + (p : ℝ) / 2)`. Rewrite using `[← tsum_mul_left]`. Conclude with `tsum_of_norm_bounded (hsum.mul_left _).hasSum fun q => hpt σ hσ' _`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem sph_bound (hHt : HtExist) (hS : SphBound) (hp : 1 ≤ p) (f : ℝ → G D p → ℂ)
    (hcont : ContinuousOn (fun u : ℝ × G D p => f u.1 u.2) (Set.Icc ((p : ℝ) / 2) (p / 2 + 1) ×ˢ Set.univ))
    (hlaw : ∀ σ ∈ Set.Icc ((p : ℝ) / 2) (p / 2 + 1), IsLaw 1 (σ : ℂ) (f σ)) :
    ∃ B : ℝ, ∀ σ ∈ Set.Ioc ((p : ℝ) / 2) (p / 2 + 1), ‖((σ - p / 2 : ℝ) : ℂ) * eisS (f σ) 1‖ ≤ B := by
  obtain ⟨⟨H', hH'⟩, C, hCc, hPC⟩ := hHt D p
  obtain ⟨B₁, hB₁⟩ := hS D p hp H' hH' {1} isCompact_singleton
  have hHpos : ∀ x, 0 < (H' x : ℝ) := fun x => by exact_mod_cast hH'.2.1 x
  have hden : Continuous fun u : ℝ × G D p => (H' u.2 : ℝ) ^ (u.1 + (p : ℝ) / 2) :=
    Continuous.rpow (NNReal.continuous_coe.comp (hH'.1.comp continuous_snd))
      (continuous_fst.add continuous_const) fun u => Or.inl (hHpos _).ne'
  have hRc : ContinuousOn (fun u : ℝ × G D p => ‖f u.1 u.2‖ / (H' u.2 : ℝ) ^ (u.1 + (p : ℝ) / 2))
      (Set.Icc ((p : ℝ) / 2) (p / 2 + 1) ×ˢ C) :=
    ContinuousOn.div ((hcont.mono (Set.prod_mono subset_rfl (Set.subset_univ _))).norm) hden.continuousOn
      fun u _ => (Real.rpow_pos_of_pos (hHpos _) _).ne'
  obtain ⟨B₀, hB₀⟩ := (isCompact_Icc.prod hCc).exists_bound_of_continuousOn hRc
  have hpt : ∀ σ ∈ Set.Icc ((p : ℝ) / 2) (p / 2 + 1), ∀ x, ‖f σ x‖ ≤ |B₀| * (H' x : ℝ) ^ (σ + (p : ℝ) / 2) := by
    intro σ hσ x
    obtain ⟨q, hq, c, hc, rfl⟩ := hPC x
    obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hq
    have hA0 := absA_ne_zero_of_ht hH' hq ha
    have hA : 0 < (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) := by
      exact_mod_cast pos_iff_ne_zero.2 hA0
    have hc1 : ‖f σ c‖ ≤ |B₀| * (H' c : ℝ) ^ (σ + (p : ℝ) / 2) := by
      have h1 := (hB₀ (σ, c) ⟨hσ, hc⟩)
      have hpos := Real.rpow_pos_of_pos (hHpos c) (σ + (p : ℝ) / 2)
      have h2 : ‖f σ c‖ / (H' c : ℝ) ^ (σ + (p : ℝ) / 2) ≤ |B₀| :=
        (le_abs_self _).trans (h1.trans (le_abs_self _))
      exact (div_le_iff₀ hpos).1 h2
    have hn : ‖npow (absA D (Matrix.GeneralLinearGroup.det a)) ((σ : ℂ) + (p : ℂ) / 2)‖ =
        (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ (σ + (p : ℝ) / 2) := by
      simp only [npow]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hA]
      simp
    rw [hlaw σ hσ q hq a ha c, hH'.2.2 q hq a ha c, NNReal.coe_mul,
      Real.mul_rpow hA.le (hHpos c).le, norm_mul, norm_mul, hn]
    have hone : ‖(((1 : (AE D)ˣ →* Circle) (Matrix.GeneralLinearGroup.det a) : Circle) : ℂ)‖ = 1 := by simp
    rw [hone, one_mul]
    have hAp := Real.rpow_pos_of_pos hA (σ + (p : ℝ) / 2)
    calc _ ≤ (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ (σ + (p : ℝ) / 2) *
          (|B₀| * (H' c : ℝ) ^ (σ + (p : ℝ) / 2)) := mul_le_mul_of_nonneg_left hc1 hAp.le
      _ = _ := by ring
  refine ⟨|B₀| * B₁, fun σ hσ => ?_⟩
  obtain ⟨hsum, hle⟩ := hB₁ σ hσ 1 rfl
  have hσ' : σ ∈ Set.Icc ((p : ℝ) / 2) (p / 2 + 1) := ⟨hσ.1.le, hσ.2⟩
  have hpos : 0 ≤ σ - (p : ℝ) / 2 := by linarith [hσ.1]
  have hE : ‖eisS (f σ) 1‖ ≤
      |B₀| * ∑' q : GlobalTheory.Eis.Cosets (P D p) (GF D p), (H' ((q.out : GF D p) * 1) : ℝ) ^ (σ + (p : ℝ) / 2) := by
    rw [← tsum_mul_left]
    exact tsum_of_norm_bounded (hsum.mul_left _).hasSum fun q => hpt σ hσ' _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos]
  calc _ ≤ (σ - (p : ℝ) / 2) * (|B₀| *
        ∑' q : GlobalTheory.Eis.Cosets (P D p) (GF D p), (H' ((q.out : GF D p) * 1) : ℝ) ^ (σ + (p : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hE hpos
    _ = |B₀| * ((σ - (p : ℝ) / 2) *
        ∑' q : GlobalTheory.Eis.Cosets (P D p) (GF D p), (H' ((q.out : GF D p) * 1) : ℝ) ^ (σ + (p : ℝ) / 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hle (abs_nonneg _)

/- English proof (translation)
Introduce `x hx`. Establish `hx1 : x - s ≤ ε` using `by linarith [hx.2, min_le_left ε 1]`. Establish `hmem : (x : ℂ) ∈ Metric.closedBall (s : ℂ) ε`. Rewrite using `[Metric.mem_closedBall, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith [hx.1])]`. Conclude with `hx1`.

Establish `hne : (x : ℂ) ≠ s`. Introduce `e`. Use `Complex.ofReal_injective e` as an intermediate fact. Combine the linear relations using `[hx.1]`. Establish `hd` using `hrad.2.2 _ hmem hne`.

Rewrite using `[hid _ (hrad.2.1 hmem) (by simpa using hcs.trans_lt hx.1), mul_div_cancel_left₀ _ hd]`.
-/
theorem quot_eq {U : Set ℂ} {d : Polynomial ℂ} {s ε c : ℝ} (hrad : IsRad U d (s : ℂ) ε) (hcs : c ≤ s) {h G' : ℂ → ℂ}
    (hid : ∀ z ∈ U, c < z.re → h z = d.eval z * G' z) :
    ∀ x ∈ Set.Ioc s (s + min ε 1), h (x : ℂ) / d.eval (x : ℂ) = G' (x : ℂ) := by
  intro x hx
  have hx1 : x - s ≤ ε := by linarith [hx.2, min_le_left ε 1]
  have hmem : (x : ℂ) ∈ Metric.closedBall (s : ℂ) ε := by
    rw [Metric.mem_closedBall, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (by linarith [hx.1])]
    exact hx1
  have hne : (x : ℂ) ≠ s := by
    intro e
    have := Complex.ofReal_injective e
    linarith [hx.1]
  have hd := hrad.2.2 _ hmem hne
  rw [hid _ (hrad.2.1 hmem) (by simpa using hcs.trans_lt hx.1), mul_div_cancel_left₀ _ hd]

/- English proof (translation)
The claim follows from `Ioc_mem_nhdsGT (by have := lt_min hε one_pos; linarith)`.
-/
theorem ev_Ioc {s ε : ℝ} (hε : 0 < ε) : ∀ᶠ x : ℝ in 𝓝[>] s, x ∈ Set.Ioc s (s + min ε 1) :=
  Ioc_mem_nhdsGT (by have := lt_min hε one_pos; linarith)

/- English proof (translation)
The claim follows from `hPR h d s ε hrad.1 hd (hh.mono hrad.2.1) (fun z hz => (hh z (hrad.2.1 (Metric.sphere_subset_closedBall hz))).differentiableAt (hU.mem_nhds (hrad.2.1 (Metric.sphere_subset_closedBall hz)))) hrad.2.2`.
-/
theorem pole_at (hPR : PoleReal) {U : Set ℂ} {d : Polynomial ℂ} {s ε : ℝ} (hU : IsOpen U) (hd : d ≠ 0)
    (hrad : IsRad U d (s : ℂ) ε) {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h U) :
    ((∃ B : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] s, ‖((σ - s : ℝ) : ℂ) * (h σ / d.eval (σ : ℂ))‖ ≤ B) →
      (∀ k : ℕ, 2 ≤ k → ∮ z in C((s : ℂ), ε), (z - s) ^ (k - 1) * (h z / d.eval z) = 0) ∧
      Tendsto (fun σ : ℝ => ((σ - s : ℝ) : ℂ) * (h σ / d.eval (σ : ℂ))) (𝓝[>] s)
        (𝓝 ((2 * Real.pi * Complex.I)⁻¹ * ∮ z in C((s : ℂ), ε), (z - s) ^ (1 - 1) * (h z / d.eval z)))) ∧
    ((∃ B : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] s, ‖h σ / d.eval (σ : ℂ)‖ ≤ B) →
      ∀ k : ℕ, 1 ≤ k → ∮ z in C((s : ℂ), ε), (z - s) ^ (k - 1) * (h z / d.eval z) = 0) :=
  hPR h d s ε hrad.1 hd (hh.mono hrad.2.1)
    (fun z hz => (hh z (hrad.2.1 (Metric.sphere_subset_closedBall hz))).differentiableAt
      (hU.mem_nhds (hrad.2.1 (Metric.sphere_subset_closedBall hz)))) hrad.2.2

/- English proof (translation)
Establish `hop : IsOpen {z : ℂ | c < z.re}` using `isOpen_lt continuous_const Complex.continuous_re`. Establish `hc : ContinuousAt G' (s : ℂ)` using `(hG _ (by simpa using hcs)).differentiableAt (hop.mem_nhds (by simpa using hcs)) |>.continuousAt`. Establish `h1 : ∀ᶠ z in 𝓝 (s : ℂ), ‖G' z‖ < ‖G' (s : ℂ)‖ + 1` using `Filter.Tendsto.eventually_lt_const (lt_add_one _) hc.norm`. Establish `h2 : ∀ᶠ x : ℝ in 𝓝 s, ‖G' (x : ℂ)‖ < ‖G' (s : ℂ)‖ + 1` using `(Complex.continuous_ofReal.tendsto s).eventually h1`. Conclude with `⟨_, (h2.filter_mono nhdsWithin_le_nhds).mono fun x hx => hx.le⟩`.
-/
theorem bdd_right {c s : ℝ} (hcs : c < s) {G' : ℂ → ℂ} (hG : DifferentiableOn ℂ G' {z : ℂ | c < z.re}) :
    ∃ B : ℝ, ∀ᶠ x : ℝ in 𝓝[>] s, ‖G' (x : ℂ)‖ ≤ B := by
  have hop : IsOpen {z : ℂ | c < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hc : ContinuousAt G' (s : ℂ) :=
    (hG _ (by simpa using hcs)).differentiableAt (hop.mem_nhds (by simpa using hcs)) |>.continuousAt
  have h1 : ∀ᶠ z in 𝓝 (s : ℂ), ‖G' z‖ < ‖G' (s : ℂ)‖ + 1 :=
    Filter.Tendsto.eventually_lt_const (lt_add_one _) hc.norm
  have h2 : ∀ᶠ x : ℝ in 𝓝 s, ‖G' (x : ℂ)‖ < ‖G' (s : ℂ)‖ + 1 :=
    (Complex.continuous_ofReal.tendsto s).eventually h1
  exact ⟨_, (h2.filter_mono nhdsWithin_le_nhds).mono fun x hx => hx.le⟩

/- English proof (translation)
Take `⟨hRc, -, hRl⟩` from `hRS D n ρ p hn M m ψ hψ b₀ hb χ χ hχ hχ θ hθ Ω hΩ H hH s₀ φ hφ hlaw g`. Establish `hlt : ((ρ : ℝ) - p) / 2 < (p : ℝ) / 2`. Establish `: (ρ : ℝ) < 2 * p` using `by exact_mod_cast hρp`. Combine the linear equalities and inequalities to obtain the conclusion. Prove the components needed by the constructor for the conclusion.

Use `hRc.comp (f := fun u : ℝ × G D p => ((u.1 : ℂ), u.2)) ((Complex.continuous_ofReal.comp continuous_fst).prodMk continuous_snd).continuousOn ?_` and prove the remaining obligations. Introduce `u hu`. Conclude with `⟨by simpa using hlt.trans_le hu.1.1, Set.mem_univ _⟩`. Introduce `σ hσ`. Use `hRl (σ : ℂ) (by simpa using hlt.trans_le hσ.1)` as an intermediate fact.

Rewrite `this` using `[mul_inv_cancel]`. Then use the resulting hypothesis.
-/
theorem rsec_real (hRS : RSec) {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsCharAF D.host.F ψ) {b₀ : HermE D ρ} (hb : b₀.1.det ≠ 0) {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ)
    {θ : InfFam D} (hθ : IsInfFam θ) {Ω : G D p → Mx D ρ p → ℂ} (hΩ : IsTh ψ χ θ b₀ m.μ Ω)
    {H : G D n → ℝ≥0} (hH : IsHt H) {φ : G D n → ℂ} (hφ : Continuous φ) {s₀ : ℂ} (hlaw : IsLaw χ s₀ φ)
    (hρp : ρ < 2 * p) (g : G D n) :
    ContinuousOn (fun u : ℝ × G D p => Rsec M m ψ b₀ (fam H φ s₀ (u.1 : ℂ)) g Ω u.2)
      (Set.Icc ((p : ℝ) / 2) (p / 2 + 1) ×ˢ Set.univ) ∧
    ∀ σ ∈ Set.Icc ((p : ℝ) / 2) (p / 2 + 1), IsLaw 1 (σ : ℂ) (Rsec M m ψ b₀ (fam H φ s₀ (σ : ℂ)) g Ω) := by
  obtain ⟨hRc, -, hRl⟩ := hRS D n ρ p hn M m ψ hψ b₀ hb χ χ hχ hχ θ hθ Ω hΩ H hH s₀ φ hφ hlaw g
  have hlt : ((ρ : ℝ) - p) / 2 < (p : ℝ) / 2 := by
    have : (ρ : ℝ) < 2 * p := by exact_mod_cast hρp
    linarith
  constructor
  · refine hRc.comp (f := fun u : ℝ × G D p => ((u.1 : ℂ), u.2))
      ((Complex.continuous_ofReal.comp continuous_fst).prodMk continuous_snd).continuousOn ?_
    intro u hu
    exact ⟨by simpa using hlt.trans_le hu.1.1, Set.mem_univ _⟩
  · intro σ hσ
    have := hRl (σ : ℂ) (by simpa using hlt.trans_le hσ.1)
    rwa [mul_inv_cancel] at this

/- English proof (translation)
Introduce `hMaps hHt hEta hId hPR hFJ hPB hRS hEH hTh hCf hPc hS`. Introduce `D n r t hn hrt ψ hψ χ hχ hres hr0 θ hθ H hH φ hφ hlaw U d E σ hc ε hrad`. Take `⟨s, hs, hs'⟩ : ∃ s : ℝ, s = (t : ℝ) / 2 ∧ (t : ℂ) / 2 = (s : ℂ)` from `⟨_, rfl, by push_cast; rfl⟩`. Rewrite `hlaw`, `hc`, `hrad`, the goal using `[hs']`. Establish `ht : 2 ≤ t` using `by omega`.

Establish `htR : (r : ℝ) + 2 < 2 * t` using `by exact_mod_cast hrt`. Take `⟨hcf, -, hfj⟩` from `hCf D n H φ _ U d E σ hc ε hrad`. Establish `hR : ∀ (M : Maps D hn) (m : Meas D r t) (b₀ : HermE D r), b₀.1.det ≠ 0 → ∀ Ω, IsTh ψ χ θ b₀ m.μ Ω → ∀ g, (∀ k : ℕ, 2 ≤ k → ∮ z in C((s : ℂ), ε), (z - s) ^ (k - 1) * (FJ M m ψ b₀ (E z) g (Ω 1) / d.eval z) = 0) ∧ Tendsto (fun x : ℝ => ((x - s : ℝ) : ℂ) * eisS (Rsec M m ψ b₀ (fam H …`. Introduce `M m b₀ hb Ω hΩ g`. Take `⟨hHd, -, hid⟩` from `fj_eq hFJ hRS hEH hId hCf M m hψ hb hχ hχ hθ hΩ hH hφ hlaw hc hrad g`.

Establish `hmax : max (((r : ℝ) - t) / 2) ((t : ℝ) / 2) ≤ s`. Rewrite using `[hs]`. Conclude with `max_le (by linarith) le_rfl`. Establish `hq` using `quot_eq hrad hmax hid`. Take `⟨hcr, hlw⟩` from `rsec_real hRS M m hψ hb hχ hθ hΩ hH hφ hlaw (by omega) g`.

Take `⟨B, hB⟩` from `sph_bound hHt hS (by omega) (fun x => Rsec M m ψ b₀ (fam H φ (s : ℂ) (x : ℂ)) g Ω) hcr hlw`. Establish `hpole` using `(pole_at hPR hc.isOpen hc.ne hrad hHd).1 ⟨B, (ev_Ioc hrad.1).mono fun x hx => by`. Rewrite using `[hq x hx]`. Establish `h1` using `min_le_right ε 1`. Establish `h2` using `hx.2`.

Establish `h3` using `hB x ⟨by rw [← hs]; exact hx.1, by rw [← hs]; linarith⟩`. Rewrite using `[← hs] at h3⟩` and apply the resulting hypothesis. Conclude with `⟨hpole.1, hpole.2.congr' ((ev_Ioc hrad.1).mono fun x hx => by simp only; rw [hq x hx])⟩`. Establish `P1 : ∀ k, 1 ≤ k → RankLT ψ (cf d E (s : ℂ) ε k) (r + 1)`. Introduce `k hk`.

Take `⟨χ', hχ', hres'⟩` from `hEta D (r + 1)`. Establish `hn' : (r + 1) + (t - 1) = n` using `by omega`. Take `⟨⟨M⟩, ⟨m⟩⟩` from `hMaps D n (r + 1) (t - 1) hn'`. Use `rank_of_FJ hPB hTh hPc M m hψ hχ' hres' (by omega) hθ (hcf k).1 (hcf k).2 ?_` and prove the remaining obligations. Introduce `b₀ hb Ω hΩ g`.

Take `⟨hHd, hGd, hid⟩` from `fj_eq hFJ hRS hEH hId hCf M m hψ hb.2 hχ hχ' hθ hΩ hH hφ hlaw hc hrad g`. Establish `hcast : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1`. Rewrite using `[Nat.cast_sub (by omega)]`. Simplify using the standard rewrite rules. Establish `hmax : max ((((r + 1 : ℕ) : ℝ) - ((t - 1 : ℕ) : ℝ)) / 2) (((t - 1 : ℕ) : ℝ) / 2) < s`.

Rewrite using `[hs, hcast]`. Use `push_cast`. Conclude with `max_lt (by linarith) (by linarith)`. Take `⟨B, hB⟩` from `bdd_right hmax hGd`. Establish `hq` using `quot_eq hrad hmax.le hid`.

Establish `h0` using `(pole_at hPR hc.isOpen hc.ne hrad hHd).2 ⟨B, (hB.and (ev_Ioc hrad.1)).mono fun x hx => by rw [hq x hx.2]; exact hx.1⟩ k hk`. Rewrite using `[((hfj (r + 1) (t - 1) hn' M m ψ hψ b₀ g (Ω 1) (integrable_th hθ m hΩ)).2 k), h0, mul_zero]`. Establish `P2 : ∀ k, 2 ≤ k → RankLT ψ (cf d E (s : ℂ) ε k) r`. Introduce `k hk`. Take `⟨⟨M⟩, ⟨m⟩⟩` from `hMaps D n r t hn`.

Use `rank_of_FJ hPB hTh hPc M m hψ hχ hres hr0 hθ (hcf k).1 (hcf k).2 ?_` and prove the remaining obligations. Introduce `b₀ hb Ω hΩ g`. Rewrite using `[((hfj r t hn M m ψ hψ b₀ g (Ω 1) (integrable_th hθ m hΩ)).2 k), (hR M m b₀ hb.2 Ω hΩ g).1 k hk, mul_zero]`. Use `⟨P1, P2, ?_⟩` and prove the remaining obligations. Introduce `mu hmu M m b₀ hb β hβ nb lam 𝓖 hcd Ω hΩ g`.

Take `⟨hcr, hlw⟩` from `rsec_real hRS M m hψ hb hχ hθ hΩ hH hφ hlaw (by omega) g`. Establish `hT` using `(hR M m b₀ hb Ω hΩ g).2`. Establish `hsm : s ∈ Set.Icc ((t : ℝ) / 2) (t / 2 + 1)`. Rewrite using `[hs]`. Conclude with `⟨le_rfl, by linarith⟩`.

Establish `hfs : Rsec M m ψ b₀ (fam H φ (s : ℂ) (s : ℂ)) g Ω = Rsec M m ψ b₀ φ g Ω` using `by rw [fam_self]`. Prove the components needed by the constructor for the conclusion. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `hcr.comp_continuous (f := fun x : G D t => (s, x)) (continuous_const.prodMk continuous_id) (fun x => ⟨hsm, Set.mem_univ _⟩)`. Establish `h2 : Continuous (Rsec M m ψ b₀ (fam H φ (s : ℂ) (s : ℂ)) g Ω)` using `h1`.

Rewrite `h2` using `[hfs]`. Then use the resulting hypothesis. Establish `h1` using `hlw s hsm`. Rewrite `h1` using `[hfs]`. Rewrite using `[hs']`. Conclude with `h1`.

Establish `hpf` using `(hPc D n r t hn M m ψ hψ _ (hcf 1).1 (hcf 1).2).2 (P1 1 le_rfl) b₀ hb β hβ nb lam 𝓖 hcd`. Establish `hE : ∫ y, fc ψ lam 𝓖 nb (cf d E (s : ℂ) ε 1) β (M.sh y * g) * conj (Ω 1 y) ∂m.μ = FJ M m ψ b₀ (cf d E (s : ℂ) ε 1) g (Ω 1)`. Simplify using `only [FJ, hpf]`. Rewrite using `[hE, (hfj r t hn M m ψ hψ b₀ g (Ω 1) (integrable_th hθ m hΩ)).2 1, ← hfs]`. Substitute `hs` using the available equality.

Conclude with `hmu.lim (fun x : ℝ => Rsec M m ψ b₀ (fam H φ (((t : ℝ) / 2 : ℝ) : ℂ) (x : ℂ)) g Ω) hcr hlw _ hT`.
-/
theorem polar : MapsExist → HtExist → HeckeEta → RightId → PoleReal → FJEis → PcBound → RSec → EisHol → ThTotal → CfFJ →
    PcFc → SphBound → Polar := by
  intro hMaps hHt hEta hId hPR hFJ hPB hRS hEH hTh hCf hPc hS
  intro D n r t hn hrt ψ hψ χ hχ hres hr0 θ hθ H hH φ hφ hlaw U d E σ hc ε hrad
  obtain ⟨s, hs, hs'⟩ : ∃ s : ℝ, s = (t : ℝ) / 2 ∧ (t : ℂ) / 2 = (s : ℂ) := ⟨_, rfl, by push_cast; rfl⟩
  rw [hs'] at hlaw hc hrad ⊢
  have ht : 2 ≤ t := by omega
  have htR : (r : ℝ) + 2 < 2 * t := by exact_mod_cast hrt
  obtain ⟨hcf, -, hfj⟩ := hCf D n H φ _ U d E σ hc ε hrad

  have hR : ∀ (M : Maps D hn) (m : Meas D r t) (b₀ : HermE D r), b₀.1.det ≠ 0 → ∀ Ω, IsTh ψ χ θ b₀ m.μ Ω → ∀ g,
      (∀ k : ℕ, 2 ≤ k → ∮ z in C((s : ℂ), ε), (z - s) ^ (k - 1) * (FJ M m ψ b₀ (E z) g (Ω 1) / d.eval z) = 0) ∧
      Tendsto (fun x : ℝ => ((x - s : ℝ) : ℂ) * eisS (Rsec M m ψ b₀ (fam H φ (s : ℂ) (x : ℂ)) g Ω) 1) (𝓝[>] s)
        (𝓝 ((2 * Real.pi * Complex.I)⁻¹ *
          ∮ z in C((s : ℂ), ε), (z - s) ^ (1 - 1) * (FJ M m ψ b₀ (E z) g (Ω 1) / d.eval z))) := by
    intro M m b₀ hb Ω hΩ g
    obtain ⟨hHd, -, hid⟩ := fj_eq hFJ hRS hEH hId hCf M m hψ hb hχ hχ hθ hΩ hH hφ hlaw hc hrad g
    have hmax : max (((r : ℝ) - t) / 2) ((t : ℝ) / 2) ≤ s := by
      rw [hs]
      exact max_le (by linarith) le_rfl
    have hq := quot_eq hrad hmax hid
    obtain ⟨hcr, hlw⟩ := rsec_real hRS M m hψ hb hχ hθ hΩ hH hφ hlaw (by omega) g
    obtain ⟨B, hB⟩ := sph_bound hHt hS (by omega) (fun x => Rsec M m ψ b₀ (fam H φ (s : ℂ) (x : ℂ)) g Ω) hcr hlw
    have hpole := (pole_at hPR hc.isOpen hc.ne hrad hHd).1 ⟨B, (ev_Ioc hrad.1).mono fun x hx => by
      rw [hq x hx]
      have h1 := min_le_right ε 1
      have h2 := hx.2
      have h3 := hB x ⟨by rw [← hs]; exact hx.1, by rw [← hs]; linarith⟩
      rwa [← hs] at h3⟩
    exact ⟨hpole.1, hpole.2.congr' ((ev_Ioc hrad.1).mono fun x hx => by simp only; rw [hq x hx])⟩
  have P1 : ∀ k, 1 ≤ k → RankLT ψ (cf d E (s : ℂ) ε k) (r + 1) := by
    intro k hk
    obtain ⟨χ', hχ', hres'⟩ := hEta D (r + 1)
    have hn' : (r + 1) + (t - 1) = n := by omega
    obtain ⟨⟨M⟩, ⟨m⟩⟩ := hMaps D n (r + 1) (t - 1) hn'
    refine rank_of_FJ hPB hTh hPc M m hψ hχ' hres' (by omega) hθ (hcf k).1 (hcf k).2 ?_
    intro b₀ hb Ω hΩ g
    obtain ⟨hHd, hGd, hid⟩ := fj_eq hFJ hRS hEH hId hCf M m hψ hb.2 hχ hχ' hθ hΩ hH hφ hlaw hc hrad g
    have hcast : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      simp
    have hmax : max ((((r + 1 : ℕ) : ℝ) - ((t - 1 : ℕ) : ℝ)) / 2) (((t - 1 : ℕ) : ℝ) / 2) < s := by
      rw [hs, hcast]
      push_cast
      exact max_lt (by linarith) (by linarith)
    obtain ⟨B, hB⟩ := bdd_right hmax hGd
    have hq := quot_eq hrad hmax.le hid
    have h0 := (pole_at hPR hc.isOpen hc.ne hrad hHd).2
      ⟨B, (hB.and (ev_Ioc hrad.1)).mono fun x hx => by rw [hq x hx.2]; exact hx.1⟩ k hk
    rw [((hfj (r + 1) (t - 1) hn' M m ψ hψ b₀ g (Ω 1) (integrable_th hθ m hΩ)).2 k), h0, mul_zero]
  have P2 : ∀ k, 2 ≤ k → RankLT ψ (cf d E (s : ℂ) ε k) r := by
    intro k hk
    obtain ⟨⟨M⟩, ⟨m⟩⟩ := hMaps D n r t hn
    refine rank_of_FJ hPB hTh hPc M m hψ hχ hres hr0 hθ (hcf k).1 (hcf k).2 ?_
    intro b₀ hb Ω hΩ g
    rw [((hfj r t hn M m ψ hψ b₀ g (Ω 1) (integrable_th hθ m hΩ)).2 k), (hR M m b₀ hb.2 Ω hΩ g).1 k hk, mul_zero]
  refine ⟨P1, P2, ?_⟩
  intro mu hmu M m b₀ hb β hβ nb lam 𝓖 hcd Ω hΩ g
  obtain ⟨hcr, hlw⟩ := rsec_real hRS M m hψ hb hχ hθ hΩ hH hφ hlaw (by omega) g
  have hT := (hR M m b₀ hb Ω hΩ g).2
  have hsm : s ∈ Set.Icc ((t : ℝ) / 2) (t / 2 + 1) := by
    rw [hs]
    exact ⟨le_rfl, by linarith⟩
  have hfs : Rsec M m ψ b₀ (fam H φ (s : ℂ) (s : ℂ)) g Ω = Rsec M m ψ b₀ φ g Ω := by rw [fam_self]
  constructor
  · refine ⟨?_, ?_⟩
    · have h1 := hcr.comp_continuous (f := fun x : G D t => (s, x)) (continuous_const.prodMk continuous_id)
        (fun x => ⟨hsm, Set.mem_univ _⟩)
      have h2 : Continuous (Rsec M m ψ b₀ (fam H φ (s : ℂ) (s : ℂ)) g Ω) := h1
      rwa [hfs] at h2
    · have h1 := hlw s hsm
      rw [hfs] at h1
      rw [hs']
      exact h1
  · have hpf := (hPc D n r t hn M m ψ hψ _ (hcf 1).1 (hcf 1).2).2 (P1 1 le_rfl) b₀ hb β hβ nb lam 𝓖 hcd
    have hE : ∫ y, fc ψ lam 𝓖 nb (cf d E (s : ℂ) ε 1) β (M.sh y * g) * conj (Ω 1 y) ∂m.μ =
        FJ M m ψ b₀ (cf d E (s : ℂ) ε 1) g (Ω 1) := by
      simp only [FJ, hpf]
    rw [hE, (hfj r t hn M m ψ hψ b₀ g (Ω 1) (integrable_th hθ m hΩ)).2 1, ← hfs]
    subst hs
    exact hmu.lim (fun x : ℝ => Rsec M m ψ b₀ (fam H φ (((t : ℝ) / 2 : ℝ) : ℂ) (x : ℂ)) g Ω) hcr hlw _ hT

end GlobalTheory.CompanionTheory.RswPolar

end
