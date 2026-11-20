import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClosedDiscExtensionOfPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFlatRadiusIdealFacts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisActionExtendsToAinfDiscRings
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyDiscPeriodAinfBasisDataOfIsPer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscToDiscInjectiveOfAdicBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitWittTiltAndNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralElementsUnitFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralWittLatticeBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitSaturatedBasisEtaleLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfClosedMembershipLimitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusMatrixMulEqEPowOfPeriodStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBoundedSemistablePeriodsNullFamilyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodsGaloisFixingFlatStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodFrobeniusRationalOverKisinRingStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableSeedModuleLAdicClosedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodsRationalInColumnsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodSpanFrobeniusStableStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodPowDvdByBasisAinfStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableDiscPeriodBasisIsUnitStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.WHeight

open GlobalTheory.BSP.HeightEx in

/- English proof (translation)
Introduce `l _ K bk τ hτ d ρ hρ s`. Take `⟨-, -, ⟨hρ0, hρ1, -⟩, -⟩` from `GlobalTheory.BSP.flat_disc l K bk`. Take `⟨ι, TB, k, v, Zf, -, hvZ, hsum⟩` from `GlobalTheory.T.exists_bounded_semistable_periods_null_family l K bk τ hτ d ρ hρ s`. Establish `hinj : Function.Injective bk.iA` using `(GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk _ bk.ev ι TB _ hρ0 hρ1).1`. Establish `hev` using `injective_of_topBasis TB`.

Establish `hτ0 : τ ≠ 0` using `(GlobalTheory.T.breuilKisin_period_isUnit_wittTilt_and_ne_zero l K bk τ hτ).2.2.1`. Establish `hl0 : (l : Ainf l) ≠ 0` using `WittVector.p_nonzero l (OCb l)`. Take `⟨j₀, hj₀⟩ : ∃ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j` from `GlobalTheory.BSP.exists_discMap_of_pow_dvd l _ _ bk.ev X (bk.ev X) _ _ 1 hρ0 (by rw [pow_one]) (by rw [pow_one])`. Take `⟨σ, hσ⟩` from `exists_cols bk hinj v TB.b _ (mul_ne_zero (pow_ne_zero k hl0) (pow_ne_zero _ hτ0)) hsum`. Use `set Y1 : Matrix (Fin d) (Fin d) (Ainf l) := Matrix.of fun a b => v (σ b).1 a (σ b).2 with hY1`.

Set `Z1 : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)` to `Matrix.of fun a b => Zf (σ b).1 a (σ b).2`. Establish `hZ1 : ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W * Z1.map j = Y1.map bk.iA` using `fun j hj => Matrix.ext fun a b => congrFun (congrFun (hvZ j hj (σ b).1) a) (σ b).2`. Use `clear_value Y1 Z1`. Establish `hdet : (Y1.map (inclW l)).det ≠ 0` using `fun h0 => hσ (GlobalTheory.BSP.HeightEx.inclW_injective (by`. Rewrite using `[RingHom.map_det, map_zero]`.

Conclude with `h0))`. Take `⟨δ, A1, hδ, hA1⟩` from `GlobalTheory.T.semistablePeriod_frobenius_rational_over_kisinRing l K bk τ hτ d ρ hρ s Y1 Z1 hσ hZ1`. Establish `hgal : ∀ g : ↥(GK K), bk.FixFlat g → τ ^ s.N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * Y1.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ s.N • Y1` using `fun g hg => by`. Take `⟨G, hG⟩` from `(GlobalTheory.BSP.galois_discMap l K bk).2 _ hρ0 (g : GQ l)`. Take `⟨hfix, hW⟩` from `GlobalTheory.T.semistable_periods_galois_fixing_flat l K bk τ hτ d ρ hρ s g hg G hG`.

Establish `e1 : (Z1.map j₀).map G = Z1.map j₀` using `Matrix.ext fun a b => hfix j₀ hj₀ _`. Establish `e2 : s.W.map G * Z1.map j₀ = (Y1.map (Per.σA (g : GQ l))).map bk.iA`. Rewrite using `[← e1, ← Matrix.map_mul, hZ1 j₀ hj₀]`. Conclude with `Matrix.ext fun a b => hG.ext _`. Establish `e3` using `congrArg (· * Z1.map j₀) hW`.

Simplify using `only [Matrix.smul_mul, Matrix.mul_assoc] at e3`. Rewrite `e3` using `[e2, hZ1 j₀ hj₀, hG.ext]`. Use `Matrix.ext fun a b => hinj ?_` and prove the remaining obligations. Establish `e4` using `congrFun (congrFun e3 a) b`. Simplify using `only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow, map_sum, RingHom.comp_apply] at e4 ⊢`.

Conclude with `e4`. Take `⟨m, P, Y', hP, hPd, hY', hlat, hsat⟩` from `GlobalTheory.T.exists_integralWittLattice_basis l K bk d _ hdet`. Establish `hY'u` using `GlobalTheory.T.isUnit_saturated_basis_etale_lattice l K bk τ hτ d s.N ρ hρ Y1 δ A1 hdet hδ hA1 hgal m P Y' hP hPd hY' hlat hsat`. Take `⟨Y, hYu, hY⟩` from `GlobalTheory.T.ainf_closed_membership_limit l K bk d (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) ⟨0, fun j _ => by simp only [Pi.zero_apply, map_zero]; exact Matrix. …`. Simplify using `only [Pi.add_apply, map_add]`.

Conclude with `(Matrix.mulVec_add s.W (fun a => j (x a)) fun a => j (x' a)).trans (by rw [hx j hj, hx' j hj]; rfl)⟩)`. Use the proof step `(fun c y ⟨x, hx⟩ => ⟨fun a => toDisc l X bk.ρ₀ c * x a, fun j hj => by`. Simplify using `only [map_mul, hj.ext]`. Conclude with `(Matrix.mulVec_smul s.W (bk.iA (bk.ev c)) fun a => j (x a)).trans (by rw [hx j hj]; rfl)⟩)`. Use the proof step `(fun y ⟨x, hx⟩ => by`.

Take `⟨t, ht⟩` from `(isUnit_l_disc l (X : bk.S) bk.ρ₀).exists_left_inv`. Use `⟨fun a => t * x a, fun j hj => ?_⟩` and prove the remaining obligations. Establish `ht'` using `congrArg j ht`. Rewrite `ht'` using `[map_mul, map_natCast, map_one]`. Simplify using `only [map_mul]`.

Use `(Matrix.mulVec_smul s.W (j t) fun a => j (x a)).trans ?_` and prove the remaining obligations. Rewrite using `[hx j hj]`. Use function extensionality and compare the values at `a`. Rewrite using `[Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, ← mul_assoc, ht', one_mul])`. Use the proof step `(GlobalTheory.T.semistableSeed_module_lAdic_closed l K bk τ hτ d ρ hρ s) Y1 Y' hdet hY'u`.

Use the proof step `(fun c => ⟨Z1 *ᵥ fun a => toDisc l X bk.ρ₀ (c a), fun j hj => by`. Simplify using `only [RingHom.map_mulVec]`. Establish `e : (j ∘ fun a => toDisc l X bk.ρ₀ (c a)) = bk.iA ∘ fun a => bk.ev (c a)` using `funext fun a => hj.ext _`. Rewrite using `[e, ← hZ1 j hj, ← Matrix.mulVec_mulVec]⟩)`. Use the proof step `(fun y hy => by`.

Take `⟨δ, c, hδ, h⟩` from `GlobalTheory.T.semistable_periods_rational_in_columns l K bk τ hτ d ρ hρ s Y1 Z1 hdet hZ1 y hy`. Conclude with `mem_lattice bk hev Y1 m P Y' hY' hlat y δ c hδ h)`. Take `⟨k', S', hS'⟩` from `GlobalTheory.T.semistablePeriod_pow_dvd_by_basis_ainf l K bk τ hτ d ρ hρ s Y hYu hY`. Establish `hcol : ∀ b : Fin d, ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (Y a b)` using `fun b => (hY fun a => Y a b).2 ⟨Pi.single b 1, by`. Use function extensionality and compare the values at `a`.

Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply, apply_ite]⟩`. Establish `hφ` using `fun b => (hY _).1 (GlobalTheory.T.semistablePeriod_span_frobenius_stable l K bk τ hτ d ρ hρ s _ (hcol b))`. Use `choose x hx using hcol`. Use `choose c hc using hφ`. Establish `hZ : ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W * (Matrix.of fun a b => x b a).map j = Y.map bk.iA` using `fun j hj => Matrix.ext fun a b => congrFun (hx b j hj) a`.

Establish `hA : Y.map WittVector.frobenius = Y * (Matrix.of fun a b => c b a).map bk.ev` using `Matrix.ext fun a b => congrFun (hc b) a`. Take `⟨b, A', hA'⟩` from `GlobalTheory.T.exists_frobenius_matrix_mul_eq_E_pow_of_period l K bk τ hτ d Y S' _ k' _ hYu hS' hA`. Conclude with `⟨Y, _, b, _, A', hYu, GlobalTheory.T.semistable_disc_period_basis_isUnit l K bk τ hτ d ρ hρ s Y _ k' S' hS' hZ, hZ, hA', hA⟩`.
-/
theorem exists_height : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ), ∃ (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (b : ℕ) (A A' : Matrix (Fin d) (Fin d) (bk.S)), IsUnit (Y.map (inclW l)) ∧ IsUnit Z ∧ (∀ i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev i → s.W * Z.map i = Y.map bk.iA) ∧ A * A' = bk.E ^ b • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ Y.map WittVector.frobenius = Y * A.map bk.ev := by
  intro l _ K bk τ hτ d ρ hρ s
  obtain ⟨-, -, ⟨hρ0, hρ1, -⟩, -⟩ := GlobalTheory.BSP.flat_disc l K bk
  obtain ⟨ι, TB, k, v, Zf, -, hvZ, hsum⟩ := GlobalTheory.T.exists_bounded_semistable_periods_null_family l K bk τ hτ d ρ hρ s
  have hinj : Function.Injective bk.iA := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk _ bk.ev ι TB _ hρ0 hρ1).1
  have hev := injective_of_topBasis TB
  have hτ0 : τ ≠ 0 := (GlobalTheory.T.breuilKisin_period_isUnit_wittTilt_and_ne_zero l K bk τ hτ).2.2.1
  have hl0 : (l : Ainf l) ≠ 0 := WittVector.p_nonzero l (OCb l)
  obtain ⟨j₀, hj₀⟩ : ∃ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j :=
    GlobalTheory.BSP.exists_discMap_of_pow_dvd l _ _ bk.ev X (bk.ev X) _ _ 1 hρ0 (by rw [pow_one]) (by rw [pow_one])
  obtain ⟨σ, hσ⟩ := exists_cols bk hinj v TB.b _ (mul_ne_zero (pow_ne_zero k hl0) (pow_ne_zero _ hτ0)) hsum
  set Y1 : Matrix (Fin d) (Fin d) (Ainf l) := Matrix.of fun a b => v (σ b).1 a (σ b).2 with hY1
  let Z1 : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀) := Matrix.of fun a b => Zf (σ b).1 a (σ b).2
  have hZ1 : ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W * Z1.map j = Y1.map bk.iA :=
    fun j hj => Matrix.ext fun a b => congrFun (congrFun (hvZ j hj (σ b).1) a) (σ b).2
  clear_value Y1 Z1
  have hdet : (Y1.map (inclW l)).det ≠ 0 := fun h0 => hσ (GlobalTheory.BSP.HeightEx.inclW_injective (by
    rw [RingHom.map_det, map_zero]; exact h0))
  obtain ⟨δ, A1, hδ, hA1⟩ := GlobalTheory.T.semistablePeriod_frobenius_rational_over_kisinRing l K bk τ hτ d ρ hρ s Y1 Z1 hσ hZ1
  have hgal : ∀ g : ↥(GK K), bk.FixFlat g → τ ^ s.N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) *
      Y1.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ s.N • Y1 := fun g hg => by
    obtain ⟨G, hG⟩ := (GlobalTheory.BSP.galois_discMap l K bk).2 _ hρ0 (g : GQ l)
    obtain ⟨hfix, hW⟩ := GlobalTheory.T.semistable_periods_galois_fixing_flat l K bk τ hτ d ρ hρ s g hg G hG
    have e1 : (Z1.map j₀).map G = Z1.map j₀ := Matrix.ext fun a b => hfix j₀ hj₀ _
    have e2 : s.W.map G * Z1.map j₀ = (Y1.map (Per.σA (g : GQ l))).map bk.iA := by
      rw [← e1, ← Matrix.map_mul, hZ1 j₀ hj₀]
      exact Matrix.ext fun a b => hG.ext _
    have e3 := congrArg (· * Z1.map j₀) hW
    simp only [Matrix.smul_mul, Matrix.mul_assoc] at e3
    rw [e2, hZ1 j₀ hj₀, hG.ext] at e3
    refine Matrix.ext fun a b => hinj ?_
    have e4 := congrFun (congrFun e3 a) b
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow, map_sum,
      RingHom.comp_apply] at e4 ⊢
    exact e4
  obtain ⟨m, P, Y', hP, hPd, hY', hlat, hsat⟩ := GlobalTheory.T.exists_integralWittLattice_basis l K bk d _ hdet
  have hY'u := GlobalTheory.T.isUnit_saturated_basis_etale_lattice l K bk τ hτ d s.N ρ hρ Y1 δ A1 hdet hδ hA1 hgal m P Y' hP hPd hY' hlat hsat
  obtain ⟨Y, hYu, hY⟩ := GlobalTheory.T.ainf_closed_membership_limit l K bk d (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀,
      ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a))
    ⟨0, fun j _ => by simp only [Pi.zero_apply, map_zero]; exact Matrix.mulVec_zero _⟩
    (fun y z ⟨x, hx⟩ ⟨x', hx'⟩ => ⟨x + x', fun j hj => by
      simp only [Pi.add_apply, map_add]
      exact (Matrix.mulVec_add s.W (fun a => j (x a)) fun a => j (x' a)).trans (by rw [hx j hj, hx' j hj]; rfl)⟩)
    (fun c y ⟨x, hx⟩ => ⟨fun a => toDisc l X bk.ρ₀ c * x a, fun j hj => by
      simp only [map_mul, hj.ext]
      exact (Matrix.mulVec_smul s.W (bk.iA (bk.ev c)) fun a => j (x a)).trans (by rw [hx j hj]; rfl)⟩)
    (fun y ⟨x, hx⟩ => by
      obtain ⟨t, ht⟩ := (isUnit_l_disc l (X : bk.S) bk.ρ₀).exists_left_inv
      refine ⟨fun a => t * x a, fun j hj => ?_⟩
      have ht' := congrArg j ht
      rw [map_mul, map_natCast, map_one] at ht'
      simp only [map_mul]
      refine (Matrix.mulVec_smul s.W (j t) fun a => j (x a)).trans ?_
      rw [hx j hj]
      funext a
      rw [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, ← mul_assoc, ht', one_mul])
    (GlobalTheory.T.semistableSeed_module_lAdic_closed l K bk τ hτ d ρ hρ s) Y1 Y' hdet hY'u
    (fun c => ⟨Z1 *ᵥ fun a => toDisc l X bk.ρ₀ (c a), fun j hj => by
      simp only [RingHom.map_mulVec]
      have e : (j ∘ fun a => toDisc l X bk.ρ₀ (c a)) = bk.iA ∘ fun a => bk.ev (c a) := funext fun a => hj.ext _
      rw [e, ← hZ1 j hj, ← Matrix.mulVec_mulVec]⟩)
    (fun y hy => by
      obtain ⟨δ, c, hδ, h⟩ := GlobalTheory.T.semistable_periods_rational_in_columns l K bk τ hτ d ρ hρ s Y1 Z1 hdet hZ1 y hy
      exact mem_lattice bk hev Y1 m P Y' hY' hlat y δ c hδ h)
  obtain ⟨k', S', hS'⟩ := GlobalTheory.T.semistablePeriod_pow_dvd_by_basis_ainf l K bk τ hτ d ρ hρ s Y hYu hY
  have hcol : ∀ b : Fin d, ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j →
      s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (Y a b) := fun b =>
    (hY fun a => Y a b).2 ⟨Pi.single b 1, by
      funext a
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, apply_ite]⟩
  have hφ := fun b => (hY _).1 (GlobalTheory.T.semistablePeriod_span_frobenius_stable l K bk τ hτ d ρ hρ s _ (hcol b))
  choose x hx using hcol
  choose c hc using hφ
  have hZ : ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j →
      s.W * (Matrix.of fun a b => x b a).map j = Y.map bk.iA :=
    fun j hj => Matrix.ext fun a b => congrFun (hx b j hj) a
  have hA : Y.map WittVector.frobenius = Y * (Matrix.of fun a b => c b a).map bk.ev :=
    Matrix.ext fun a b => congrFun (hc b) a
  obtain ⟨b, A', hA'⟩ := GlobalTheory.T.exists_frobenius_matrix_mul_eq_E_pow_of_period l K bk τ hτ d Y S' _ k' _ hYu hS' hA
  exact ⟨Y, _, b, _, A', hYu, GlobalTheory.T.semistable_disc_period_basis_isUnit l K bk τ hτ d ρ hρ s Y _ k' S' hS' hZ, hZ, hA', hA⟩

end GlobalTheory.BKLim.WHeight
