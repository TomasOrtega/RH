import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatiosEqOfSameOrbit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DehomogenizedEvalEqRatio
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

/- English proof (translation)
Establish `hE` using `Real.exp_pos (φ / 2)`. Establish `key : F / G / h = ρ / Real.exp (φ / 2)`. Establish `hF' : F = a * ρ * (G / Pb) * Pa`. Rewrite using `[e]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[hh, hF']`. Clear the denominators using the available nonvanishing facts. Rewrite using `[key, Real.log_div hρ.ne' hE.ne', Real.log_exp]`.
-/
theorem log_eq_of_frame {a ρ F G Pa Pb φ h : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hF : 0 < F) (hG : 0 < G)
    (hPa : 0 < Pa) (hPb : 0 < Pb) (hh : h = Pa / Pb * a * Real.exp (φ / 2))
    (e : a * ρ * (G / Pb) = F / Pa) : Real.log ρ - φ / 2 = Real.log (F / G / h) := by
  have hE := Real.exp_pos (φ / 2)
  have key : F / G / h = ρ / Real.exp (φ / 2) := by
    have hF' : F = a * ρ * (G / Pb) * Pa := by
      rw [e]
      field_simp
    rw [hh, hF']
    field_simp
  rw [key, Real.log_div hρ.ne' hE.ne', Real.log_exp]

/- English proof (translation)
Introduce `m n M A X _ i _ r hr f g hfg hrat y z hz hf0 hg0`. Take `⟨α, β, hf, hg, -, -, hdeg⟩` from `hfg`. Take `⟨u, hu, hcl⟩` from `hrat`. Take `⟨w, hw⟩ : ∃ w, w = PtsOver.map i rfl _ y` from `⟨_, rfl⟩`. Establish `hz' : IsUnder w z` using `hw ▸ hz`.

Establish `hwb` using `mem_pick (M.φ σ₀).isLB w`. Take `⟨b, hb⟩ : ∃ b, b = pick (M.φ σ₀).isLB w` from `⟨_, rfl⟩`. Rewrite `hwb` using `[← hb]`. Take `⟨c, hc⟩ : ∃ c : ∀ k, Bk n k, c = fun k => ptChart (w.1 (IsLocalRing.closedPoint ℂ)) k` from `⟨_, rfl⟩`. Establish `hwc : w ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c)` using `CxPts.mem_ptsIn.2 (Set.mem_iInter.2 fun k => hc ▸ mem_ptChart _ k)`.

Establish `hwbc : w ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U b ⊓ mchart c)` using `mem_ptsIn_inf.2 ⟨hwb, hwc⟩`. Establish `pre : ∀ V : (MP ℤ m n).Opens, w ∈ ptsIn (mpStr ℤ m n) σ₀ V → y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ V)`. Introduce `V hV`. Substitute `hw` using the available equality. Conclude with `CxPts.mem_ptsIn.2 (CxPts.mem_ptsIn.1 hV)`.

Establish `hyc` using `pre _ hwc`. Establish `hybc` using `pre _ hwbc`. Establish `hyb` using `pre _ hwb`. Establish `hgc : genericPoint X ∈ i ⁻¹ᵁ mchart c` using `gen_mem (CxPts.mem_ptsIn.1 hyc)`. Establish `hgb : genericPoint X ∈ i ⁻¹ᵁ (M.B.U b ⊓ mchart c)` using `gen_mem (CxPts.mem_ptsIn.1 hybc)`.

Establish `e` using `hcl b c hgc hgb`. Establish `hne : ∀ a : Fin (m + 1) → ℕ, ∏ k, z ⟨k, c k⟩ ^ a k ≠ 0` using `fun a => Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ ((hz' k (c k)).1.1 (CxPts.ptsIn_mono (mchart_le c k) hwc))`. Establish `val : ∀ (s : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog s a → ratVal (fnAt i c hgc s) y = eval z (map (Int.castRingHom ℂ) s) / ∏ k, z ⟨k, c k⟩ ^ a k`. Introduce `s a hs`. Use `(ratVal_fnOf hyc hgc _).trans ((CxPts.ev_app i rfl _ _ y).trans ?_)` and prove the remaining obligations.

Rewrite using `[← hw]`. Conclude with `ev_dehomog_of_isUnder m n c s a hs w z hz' hwc`. Establish `unit : ∀ (s : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog s a → eval z (map (Int.castRingHom ℂ) s) ≠ 0 → UnitAt (under y) (fnAt i c hgc s)`. Introduce `s a hs h0`. Use `(unitAt_fnOf_iff (CxPts.mem_ptsIn.1 hyc) hgc _).2 (CxPts.mem_ptsIn.1 ((mem_ptsIn_basicOpen hyc _).2 ?_))` and prove the remaining obligations.

Rewrite using `[← ratVal_fnOf hyc hgc]`. Express the relevant statement in the definitionally equal form `ratVal (fnAt i c hgc s) y ≠ 0`. Rewrite using `[val s a hs]`. Conclude with `div_ne_zero h0 (hne a)`. Establish `hF` using `unit f α hf hf0`.

Establish `hG` using `unit g β hg hg0`. Establish `hU : UnitAt (under y) (fnOf _ hgb (i.app _ (u b c).val))`. Take `⟨v, hv⟩` from `(u b c).isUnit.map (i.app (M.B.U b ⊓ mchart c)).hom`. Establish `hv' : (v : Γ(X, i ⁻¹ᵁ (M.B.U b ⊓ mchart c))) = i.app _ (u b c).val` using `hv`. Rewrite using `[← hv']`.

Conclude with `unitAt_fnOf (CxPts.mem_ptsIn.1 hybc) hgb v`. Establish `hR : UnitAt (under y) (r fun _ => b : X.functionField)`. Establish `e' : (r fun _ => b : X.functionField) = fnAt i c hgc f * (fnOf _ hgb (i.app _ (u b c).val) * fnAt i c hgc g)⁻¹`. Rewrite using `[← e]`. Establish `h1` using `hU.ne_zero`.

Establish `h2` using `hG.ne_zero`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e']`. Conclude with `hF.mul (hU.mul hG).inv`. Establish `hxb : under y ∈ (M.restr i).B.U (fun _ => b)`.

Use `Set.mem_iInter.2 fun _ => ?_` and prove the remaining obligations. Substitute `hw` using the available equality. Conclude with `CxPts.mem_ptsIn.1 hwb`. Establish `hyb' : y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ ((M.restr i).B.U (fun _ => b))` using `CxPts.mem_ptsIn.2 hxb`. Establish `ho : y ∈ offSupp (i ≫ mpStr ℤ m n) σ₀ ((M.restr i).div hr)` using `mem_offSupp.2 fun hs => ((presents_divOfRatSec (M.restr i).isLB hr).isEqn (fun _ => b) _ hxb).mem_supp_iff.1 hs hR`.

Use `⟨ho, ?_⟩` and prove the remaining obligations. Establish `hφ : ((M.restr i).φ σ₀).φ (fun _ => b) y = (M.φ σ₀).φ b w`. Rewrite using `[hw]`. Conclude with `GlobalTheory.Weight.pull_φ (M.φ σ₀) i rfl _ y`. Establish `hvU : ratVal (fnOf _ hgb (i.app _ (u b c).val)) y = CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U b ⊓ mchart c) (u b c : Γ(MP ℤ m n, M.B.U b ⊓ mchart c)) w`.

Use `(ratVal_fnOf hybc hgb _).trans ((CxPts.ev_app i rfl _ _ y).trans ?_)` and prove the remaining obligations. Rewrite using `[← hw]`. Establish `ev'` using `congrArg (ratVal · y) e`. Simplify using `only at ev'`. Rewrite `ev'` using `[ratVal_mul (hU.mul hR).regAt hG.regAt, ratVal_mul hU.regAt hR.regAt, hvU, val g β hg, val f α hf]`.

Establish `hP : ∀ a : Fin (m + 1) → ℕ, 0 < ∏ k, ‖z ⟨k, c k⟩‖ ^ a k` using `fun a => by`. Use `norm_pos_iff.2 (hne a)` as an intermediate fact. Simplify `this` using `only [norm_prod, norm_pow]`. Establish `hh` using `hu.2.2 b c w z hz' hwbc`. Establish `hzp : ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k = (∏ k, ‖z ⟨k, c k⟩‖ ^ α k) / ∏ k, ‖z ⟨k, c k⟩‖ ^ β k`.

Rewrite using `[← Finset.prod_div_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `h0 : ‖z ⟨k, c k⟩‖ ≠ 0` using `norm_ne_zero_iff.2 ((hz' k (c k)).1.1 (CxPts.ptsIn_mono (mchart_le c k) hwc))`. Rewrite using `[← hdeg k, zpow_sub₀ h0, zpow_natCast, zpow_natCast]`. Rewrite `hh` using `[hzp]`.

Rewrite using `[logNorm_eq _ hr ho hyb', hφ, logNormRat]`. Establish `evn` using `congrArg norm ev'`. Simplify using `only [norm_mul, norm_div, norm_prod, norm_pow] at evn`. Conclude with `log_eq_of_frame (norm_pos_iff.2 (ev_ne_zero hwbc (u b c).isUnit)) (norm_pos_iff.2 (ratVal_ne_zero hR)) (norm_pos_iff.2 hf0) (norm_pos_iff.2 hg0) (hP α) (hP β) hh evn`.
-/
theorem value_of_ne_zero : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : GlobalTheory.HermLB (mpStr ℤ m n)) (A : HermLine (Bk n)) (X : Scheme.{0}) [IsIntegral X]
    (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (r : (M.restr i).B.ι → X.functionFieldˣ) (hr : IsRatSec (M.restr i).B r)
    (f g : Pol n), IsRatSectionOn (ptIdeal (i (genericPoint X))) A f g → RatOf M A r f g →
    ∀ (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ), GlobalTheory.CompanionTheory.MixZ.ArchEq.Over i y z →
      eval z (map (Int.castRingHom ℂ) f) ≠ 0 → eval z (map (Int.castRingHom ℂ) g) ≠ 0 →
      y ∈ offSupp (i ≫ mpStr ℤ m n) σ₀ ((M.restr i).div hr) ∧
      GlobalTheory.Cartier.logNorm ((M.restr i).φ σ₀) r y = logNormRat A f g z := by
  intro m n M A X _ i _ r hr f g hfg hrat y z hz hf0 hg0
  obtain ⟨α, β, hf, hg, -, -, hdeg⟩ := hfg
  obtain ⟨u, hu, hcl⟩ := hrat
  obtain ⟨w, hw⟩ : ∃ w, w = PtsOver.map i rfl _ y := ⟨_, rfl⟩
  have hz' : IsUnder w z := hw ▸ hz
  have hwb := mem_pick (M.φ σ₀).isLB w
  obtain ⟨b, hb⟩ : ∃ b, b = pick (M.φ σ₀).isLB w := ⟨_, rfl⟩
  rw [← hb] at hwb
  obtain ⟨c, hc⟩ : ∃ c : ∀ k, Bk n k, c = fun k => ptChart (w.1 (IsLocalRing.closedPoint ℂ)) k := ⟨_, rfl⟩
  have hwc : w ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) :=
    CxPts.mem_ptsIn.2 (Set.mem_iInter.2 fun k => hc ▸ mem_ptChart _ k)
  have hwbc : w ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U b ⊓ mchart c) := mem_ptsIn_inf.2 ⟨hwb, hwc⟩
  have pre : ∀ V : (MP ℤ m n).Opens, w ∈ ptsIn (mpStr ℤ m n) σ₀ V → y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ V) := by
    intro V hV
    subst hw
    exact CxPts.mem_ptsIn.2 (CxPts.mem_ptsIn.1 hV)
  have hyc := pre _ hwc
  have hybc := pre _ hwbc
  have hyb := pre _ hwb
  have hgc : genericPoint X ∈ i ⁻¹ᵁ mchart c := gen_mem (CxPts.mem_ptsIn.1 hyc)
  have hgb : genericPoint X ∈ i ⁻¹ᵁ (M.B.U b ⊓ mchart c) := gen_mem (CxPts.mem_ptsIn.1 hybc)
  have e := hcl b c hgc hgb
  have hne : ∀ a : Fin (m + 1) → ℕ, ∏ k, z ⟨k, c k⟩ ^ a k ≠ 0 := fun a =>
    Finset.prod_ne_zero_iff.2 fun k _ =>
      pow_ne_zero _ ((hz' k (c k)).1.1 (CxPts.ptsIn_mono (mchart_le c k) hwc))
  have val : ∀ (s : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog s a →
      ratVal (fnAt i c hgc s) y = eval z (map (Int.castRingHom ℂ) s) / ∏ k, z ⟨k, c k⟩ ^ a k := by
    intro s a hs
    refine (ratVal_fnOf hyc hgc _).trans ((CxPts.ev_app i rfl _ _ y).trans ?_)
    rw [← hw]
    exact ev_dehomog_of_isUnder m n c s a hs w z hz' hwc
  have unit : ∀ (s : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog s a →
      eval z (map (Int.castRingHom ℂ) s) ≠ 0 → UnitAt (under y) (fnAt i c hgc s) := by
    intro s a hs h0
    refine (unitAt_fnOf_iff (CxPts.mem_ptsIn.1 hyc) hgc _).2 (CxPts.mem_ptsIn.1 ((mem_ptsIn_basicOpen hyc _).2 ?_))
    rw [← ratVal_fnOf hyc hgc]
    change ratVal (fnAt i c hgc s) y ≠ 0
    rw [val s a hs]
    exact div_ne_zero h0 (hne a)
  have hF := unit f α hf hf0
  have hG := unit g β hg hg0
  have hU : UnitAt (under y) (fnOf _ hgb (i.app _ (u b c).val)) := by
    obtain ⟨v, hv⟩ := (u b c).isUnit.map (i.app (M.B.U b ⊓ mchart c)).hom
    have hv' : (v : Γ(X, i ⁻¹ᵁ (M.B.U b ⊓ mchart c))) = i.app _ (u b c).val := hv
    rw [← hv']
    exact unitAt_fnOf (CxPts.mem_ptsIn.1 hybc) hgb v
  have hR : UnitAt (under y) (r fun _ => b : X.functionField) := by
    have e' : (r fun _ => b : X.functionField) =
        fnAt i c hgc f * (fnOf _ hgb (i.app _ (u b c).val) * fnAt i c hgc g)⁻¹ := by
      rw [← e]
      have h1 := hU.ne_zero
      have h2 := hG.ne_zero
      field_simp
    rw [e']
    exact hF.mul (hU.mul hG).inv
  have hxb : under y ∈ (M.restr i).B.U (fun _ => b) := by
    refine Set.mem_iInter.2 fun _ => ?_
    subst hw
    exact CxPts.mem_ptsIn.1 hwb
  have hyb' : y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ ((M.restr i).B.U (fun _ => b)) := CxPts.mem_ptsIn.2 hxb
  have ho : y ∈ offSupp (i ≫ mpStr ℤ m n) σ₀ ((M.restr i).div hr) :=
    mem_offSupp.2 fun hs =>
      ((presents_divOfRatSec (M.restr i).isLB hr).isEqn (fun _ => b) _ hxb).mem_supp_iff.1 hs hR
  refine ⟨ho, ?_⟩
  have hφ : ((M.restr i).φ σ₀).φ (fun _ => b) y = (M.φ σ₀).φ b w := by
    rw [hw]
    exact GlobalTheory.Weight.pull_φ (M.φ σ₀) i rfl _ y
  have hvU : ratVal (fnOf _ hgb (i.app _ (u b c).val)) y =
      CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U b ⊓ mchart c) (u b c : Γ(MP ℤ m n, M.B.U b ⊓ mchart c)) w := by
    refine (ratVal_fnOf hybc hgb _).trans ((CxPts.ev_app i rfl _ _ y).trans ?_)
    rw [← hw]
  have ev' := congrArg (ratVal · y) e
  simp only at ev'
  rw [ratVal_mul (hU.mul hR).regAt hG.regAt, ratVal_mul hU.regAt hR.regAt, hvU, val g β hg, val f α hf] at ev'
  have hP : ∀ a : Fin (m + 1) → ℕ, 0 < ∏ k, ‖z ⟨k, c k⟩‖ ^ a k := fun a => by
    have := norm_pos_iff.2 (hne a)
    simpa only [norm_prod, norm_pow] using this
  have hh := hu.2.2 b c w z hz' hwbc
  have hzp : ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k =
      (∏ k, ‖z ⟨k, c k⟩‖ ^ α k) / ∏ k, ‖z ⟨k, c k⟩‖ ^ β k := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    have h0 : ‖z ⟨k, c k⟩‖ ≠ 0 := norm_ne_zero_iff.2 ((hz' k (c k)).1.1 (CxPts.ptsIn_mono (mchart_le c k) hwc))
    rw [← hdeg k, zpow_sub₀ h0, zpow_natCast, zpow_natCast]
  rw [hzp] at hh
  rw [logNorm_eq _ hr ho hyb', hφ, logNormRat]
  have evn := congrArg norm ev'
  simp only [norm_mul, norm_div, norm_prod, norm_pow] at evn
  exact log_eq_of_frame (norm_pos_iff.2 (ev_ne_zero hwbc (u b c).isUnit)) (norm_pos_iff.2 (ratVal_ne_zero hR))
    (norm_pos_iff.2 hf0) (norm_pos_iff.2 hg0) (hP α) (hP β) hh evn

end GlobalTheory.CompanionTheory.MixZ.ArchEq
