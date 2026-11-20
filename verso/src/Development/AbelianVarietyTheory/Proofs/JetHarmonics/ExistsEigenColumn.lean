import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ColValMonomial
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ConstBFMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CanonicalLiftUnpacking
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ClosedPointWeilPower
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPosZsmulMemRange
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsValEqOfNonneg
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StalkMapInjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPowMulEqOne

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open GlobalTheory GlobalTheory.FamGerm
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS FB ev Dof)
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DepthBound

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (y : Pt1 E H V F)

/- English proof (translation)
Set `_` to `H.starRing`. Establish `hG` using `hL.globalFns`. Take `⟨f, hf1, -, -, hf4, -⟩` from `y.tors F q hq`. Take `⟨p0, hp0y, -, hp0a⟩` from `CanonicalLiftUnpacking.exists_zero_qk (D := y.P.D.toPre) (F := F) y.P.D.tau_bimult q`. Establish `hf0 : f p0 = 1`.

Use `hf4 p0 p0 p0 ⟨p0, by rw [hp0y, add_zero], hp0a, qk_equiv_refl y.P.D.tau_bimult p0⟩` as an intermediate fact. Conclude with `mul_eq_left.1 this.symm`. Take `⟨w, hw⟩ : ∃ w : LB.Gen (LB.LinComb y.P.D.toPre.P.L (DegPre.lineφ y.P.D.toPre F p0.g.b) (DegPre.lineε q)), w.IsGen` from `ClosedPointWeilPower.gen_local_linComb y.P.D.toPre.P.L y.P.D.toPre.P.isLB _ _`. Take `⟨ζ, hζ, hfin⟩` from `finOrdExists_of_laws hL V y.P.D F q hq p0 w hw`. Take `⟨Φ, hΦ⟩` from `phiFun_of_globalFns hG V _ y.P.D F q hq p0 w hw`.

Take `⟨w₂, hw₂, hc⟩` from `ThetaMul.phi_mul_core hG p0 p0 p0 (by rw [hp0y, add_zero]) hp0a w w hw hw`. Take `⟨e, he⟩` from `ThetaFinOrd.exists_scalar hG p0 w₂ w hw₂ hw (Φ * Φ : Module.End F (Fam y.P.D.toPre F q)) Φ (fun s => hc s _ _ ((hΦ _ _).2 rfl) ((hΦ _ _).2 rfl)) (fun s => (hΦ _ _).2 rfl)`. Take `⟨M, hM, hU⟩` from `(ThetaFinOrd.finOrd_iff p0 w ζ Φ hΦ).1 hfin`. Establish `hsc : ∀ t, Φ t = e • t` using `fun t => by`. Take `⟨M, rfl⟩ : ∃ M', M = M' + 1` from `⟨M - 1, by omega⟩`.

Establish `h1` using `LinearMap.congr_fun hU t`. Rewrite `h1` using `[pow_succ', Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply]`. Establish `h2` using `LinearMap.congr_fun he (((ζ • Φ : Module.End F (Fam y.P.D.toPre F q)) ^ M) t)`. Rewrite `h2` using `[Module.End.mul_apply, LinearMap.smul_apply]`. Rewrite using `[← h1, map_smul, h2, smul_comm]`.

Establish `hT : y.Transl q c s ((ζ * e) • s)`. Use `⟨p0, 1, w, ζ, Φ s, (hf1 _ _).2 hf0.symm, ?_, hw, hζ, hfin, (hΦ _ _).2 rfl, ?_⟩` and prove the remaining obligations. Use `y.P.oA.hom c` as an intermediate fact. Conclude with `MonObj.one_comp _`. Rewrite using `[DVR.isSmul_iff, hsc, smul_smul]`.

Distinguish the cases in `hs : s = 0`. Use `⟨1, y.v.map_one, ?_⟩` and prove the remaining obligations. Rewrite `hT`, the goal using `[hs, smul_zero]`. Conclude with `hT`. Use `⟨ζ * e, ?_, hT⟩` and prove the remaining obligations.

Establish `h1 : (ζ • Φ : Module.End F (Fam y.P.D.toPre F q)) = (ζ * e) • 1` using `LinearMap.ext fun t => by`. Rewrite using `[LinearMap.smul_apply, hsc, smul_smul]`. Both sides reduce to the same expression. Establish `h2` using `LinearMap.congr_fun hU s`. Rewrite `h2` using `[h1, smul_pow, one_pow, LinearMap.smul_apply, Module.End.one_apply]`.

Establish `h3 : (ζ * e) ^ M = 1`. Establish `: ((ζ * e) ^ M - 1) • s = 0` using `by rw [sub_smul, h2, one_smul, sub_self]`. Conclude with `sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right hs)`. Establish `h4` using `congrArg y.v h3`. Rewrite `h4` using `[y.v.map_pow, y.v.map_one]`.

Proceed by induction on `hx : y.v (ζ * e) using WithTop.recTopCoe with`. Consider the case `top`. Take `⟨M, rfl⟩ : ∃ M', M = M' + 1` from `⟨M - 1, by omega⟩`. Rewrite `h4` using `[hx, succ_nsmul, add_top]`. Conclude with `h4`.

Consider the case `coe x`. Rewrite `h4` using `[hx, ← WithTop.coe_nsmul, WithTop.coe_eq_zero, smul_eq_zero]`. Rewrite using `[h4.resolve_left (by omega)]; rfl`.
-/
theorem exists_transl_smul (hL : Laws) (q : ℕ) (hq : 1 ≤ q) (c : 𝓞 E) (s : Fam y.P.D.toPre F q) :
    ∃ u : F, y.v u = 0 ∧ y.Transl q c s (u • s) := by
  let _ := H.starRing
  have hG := hL.globalFns
  obtain ⟨f, hf1, -, -, hf4, -⟩ := y.tors F q hq
  obtain ⟨p0, hp0y, -, hp0a⟩ := CanonicalLiftUnpacking.exists_zero_qk (D := y.P.D.toPre) (F := F) y.P.D.tau_bimult q
  have hf0 : f p0 = 1 := by
    have := hf4 p0 p0 p0 ⟨p0, by rw [hp0y, add_zero], hp0a, qk_equiv_refl y.P.D.tau_bimult p0⟩
    exact mul_eq_left.1 this.symm
  obtain ⟨w, hw⟩ : ∃ w : LB.Gen (LB.LinComb y.P.D.toPre.P.L (DegPre.lineφ y.P.D.toPre F p0.g.b)
      (DegPre.lineε q)), w.IsGen := ClosedPointWeilPower.gen_local_linComb y.P.D.toPre.P.L y.P.D.toPre.P.isLB _ _
  obtain ⟨ζ, hζ, hfin⟩ := finOrdExists_of_laws hL V y.P.D F q hq p0 w hw
  obtain ⟨Φ, hΦ⟩ := phiFun_of_globalFns hG V _ y.P.D F q hq p0 w hw
  obtain ⟨w₂, hw₂, hc⟩ := ThetaMul.phi_mul_core hG p0 p0 p0 (by rw [hp0y, add_zero]) hp0a w w hw hw
  obtain ⟨e, he⟩ := ThetaFinOrd.exists_scalar hG p0 w₂ w hw₂ hw (Φ * Φ : Module.End F (Fam y.P.D.toPre F q)) Φ
    (fun s => hc s _ _ ((hΦ _ _).2 rfl) ((hΦ _ _).2 rfl)) (fun s => (hΦ _ _).2 rfl)
  obtain ⟨M, hM, hU⟩ := (ThetaFinOrd.finOrd_iff p0 w ζ Φ hΦ).1 hfin
  have hsc : ∀ t, Φ t = e • t := fun t => by
    obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
    have h1 := LinearMap.congr_fun hU t
    rw [pow_succ', Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply] at h1
    have h2 := LinearMap.congr_fun he (((ζ • Φ : Module.End F (Fam y.P.D.toPre F q)) ^ M) t)
    rw [Module.End.mul_apply, LinearMap.smul_apply] at h2
    rw [← h1, map_smul, h2, smul_comm]
  have hT : y.Transl q c s ((ζ * e) • s) := by
    refine ⟨p0, 1, w, ζ, Φ s, (hf1 _ _).2 hf0.symm, ?_, hw, hζ, hfin, (hΦ _ _).2 rfl, ?_⟩
    · have := y.P.oA.hom c
      exact MonObj.one_comp _
    · rw [DVR.isSmul_iff, hsc, smul_smul]
  by_cases hs : s = 0
  · refine ⟨1, y.v.map_one, ?_⟩
    rw [hs, smul_zero] at hT ⊢
    exact hT
  · refine ⟨ζ * e, ?_, hT⟩
    have h1 : (ζ • Φ : Module.End F (Fam y.P.D.toPre F q)) = (ζ * e) • 1 := LinearMap.ext fun t => by
      rw [LinearMap.smul_apply, hsc, smul_smul]; rfl
    have h2 := LinearMap.congr_fun hU s
    rw [h1, smul_pow, one_pow, LinearMap.smul_apply, Module.End.one_apply] at h2
    have h3 : (ζ * e) ^ M = 1 := by
      have : ((ζ * e) ^ M - 1) • s = 0 := by rw [sub_smul, h2, one_smul, sub_self]
      exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right hs)
    have h4 := congrArg y.v h3
    rw [y.v.map_pow, y.v.map_one] at h4
    induction hx : y.v (ζ * e) using WithTop.recTopCoe with
    | top =>
      obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      rw [hx, succ_nsmul, add_top] at h4
      exact h4
    | coe x =>
      rw [hx, ← WithTop.coe_nsmul, WithTop.coe_eq_zero, smul_eq_zero] at h4
      rw [h4.resolve_left (by omega)]; rfl

variable [CharZero F] [Algebra V F] [IsScalarTower V (FractionRing V) F]

omit [IsAlgClosed F] [CharZero F] in
/- English proof (translation)
The claim follows from `(IsScalarTower.algebraMap_eq V (FractionRing V) F).symm`.
-/
theorem fO_comp_eq : (algebraMap (TWO.Ov y.v) F).comp (TWO.fO y.v y.hϖ y.hv) = algebraMap V F :=
  (IsScalarTower.algebraMap_eq V (FractionRing V) F).symm

/- English proof (translation)
Set `_` to `H.starRing`. Establish `hk1 : 1 ≤ k` using `by omega`. Establish `hkN : 1 ≤ k * N` using `Nat.mul_pos hk1 hN`. Take `⟨G, hGm⟩` from `hG E H V F y (k * N) hkN`. Take `⟨π, -, hπ⟩` from `PullLin.exists_pull_linearMap hL V y.P.D F (𝓞 E) y.P.oD H.w0 y.P.w0 a N k hN hk1 haa`.

Take `⟨gm, h0, h1, h2⟩` from `hJ E H V F y r bs Cc M₀ hred k n hn hM`. Take `⟨s, f, h3, h4, -, h6⟩` from `h2 g hg`. Take `⟨w, κ, hw, hpull⟩` from `hP E H V F y a N k hN (by omega) haa h hh`. Take `⟨τ, hτ⟩` from `ExactTerm.exists_val_eq_of_nonneg y.hv h0`. Take `⟨u, hu, hT⟩` from `exists_transl_smul y hL (k * N) hkN (star a) (π (τ • s))`.

Establish `hnu : NuGe y.P.D y.Q F y.v k (τ • s) 0`. Use `NuGe.smul y.Q (s' := τ • s) hτ.ge (fun _ _ => rfl) h3` as an intermediate fact. Rewrite `this` using `[neg_add_cancel]`. Then use the resulting hypothesis. Establish `hκ : y.v (algebraMap V F κ) = 0`. Rewrite using `[← fO_comp_eq y]`.

Conclude with `TWO.v_unit y.v (Units.map (TWO.fO y.v y.hϖ y.hv : V →* TWO.Ov y.v) κ)`. Use `⟨τ • s, π (τ • s), _, u * τ * algebraMap V F κ, f, gm, ⟨hnu, (hπ _ _).2 rfl, hT, (hGm _ _).2 ?_⟩, ?_, h1, h6⟩` and prove the remaining obligations. Rewrite using `[map_smul, map_smul, map_smul, ← (hGm _ _).1 (hpull s _ f ((hπ _ _).2 rfl) h4), hw.trans hω.symm, MvPowerSeries.smul_eq_C_mul, MvPowerSeries.smul_eq_C_mul]`. Simplify using `only [map_mul, _root_.mul_assoc]`. Rewrite using `[y.v.map_mul, y.v.map_mul, hu, hτ, hκ, zero_add, add_zero]`.
-/
theorem exists_jet_column (hL : Laws) (hG : FamGerm.GermExSt) (hJ : JetsSt) (hP : PullGermSt) (r : ℕ)
    (bs : Module.Basis (Fin r) ℤ y.P.D.toPre.X) (Cc M₀ : ℝ) (hred : y.Red r bs Cc M₀) (a : 𝓞 E) (N k n : ℕ)
    (hN : 1 ≤ N) (haa : letI := H.starRing; a * star a = (N : 𝓞 E)) (hn : 4 * n + 4 ≤ k) (hM : (n : ℝ) * M₀ < k)
    (h : PS F 2 y.d) (hh : letI := H.starRing; y.B.IsCanonGauge F h) (ω : PS V 1 y.d)
    (hω : letI := H.starRing; FB.toK F ω =
      FB.expS F (ev (n := 1) ![y.B.actK F a] (y.B.hL F h H.w0) - (N : F) • y.B.hL F h H.w0))
    (g : PS F 1 y.d) (hg : ∀ mo, 0 ≤ y.v (MvPowerSeries.coeff mo g)) :
    letI := H.starRing
    ∃ (s : Fam y.P.D.toPre F k) (s' t : Fam y.P.D.toPre F (k * N)) (c : F) (f : PS F 1 y.d) (r₀ : ℚ),
      (NuGe y.P.D y.Q F y.v k s 0 ∧ PullAl y.P.D F y.P.oD a k N s s' ∧ y.Transl (k * N) (star a) s' t ∧
        y.Germ (k * N) t (MvPowerSeries.C c * (ev (n := 1) ![y.B.actK F a] f * FB.toK F ω ^ k))) ∧
      y.v c = (r₀ : ℚ) ∧ (r₀ : ℝ) ≤ (n : ℝ) ^ 2 * Cc / k ∧
      ∀ mo : Fin 1 × Fin y.d →₀ ℕ, mo.degree ≤ n → MvPowerSeries.coeff mo f = MvPowerSeries.coeff mo g := by
  let _ := H.starRing
  have hk1 : 1 ≤ k := by omega
  have hkN : 1 ≤ k * N := Nat.mul_pos hk1 hN
  obtain ⟨G, hGm⟩ := hG E H V F y (k * N) hkN
  obtain ⟨π, -, hπ⟩ := PullLin.exists_pull_linearMap hL V y.P.D F (𝓞 E) y.P.oD H.w0 y.P.w0 a N k hN hk1 haa
  obtain ⟨gm, h0, h1, h2⟩ := hJ E H V F y r bs Cc M₀ hred k n hn hM
  obtain ⟨s, f, h3, h4, -, h6⟩ := h2 g hg
  obtain ⟨w, κ, hw, hpull⟩ := hP E H V F y a N k hN (by omega) haa h hh
  obtain ⟨τ, hτ⟩ := ExactTerm.exists_val_eq_of_nonneg y.hv h0
  obtain ⟨u, hu, hT⟩ := exists_transl_smul y hL (k * N) hkN (star a) (π (τ • s))
  have hnu : NuGe y.P.D y.Q F y.v k (τ • s) 0 := by
    have := NuGe.smul y.Q (s' := τ • s) hτ.ge (fun _ _ => rfl) h3
    rwa [neg_add_cancel] at this
  have hκ : y.v (algebraMap V F κ) = 0 := by
    rw [← fO_comp_eq y]
    exact TWO.v_unit y.v (Units.map (TWO.fO y.v y.hϖ y.hv : V →* TWO.Ov y.v) κ)
  refine ⟨τ • s, π (τ • s), _, u * τ * algebraMap V F κ, f, gm, ⟨hnu, (hπ _ _).2 rfl, hT, (hGm _ _).2 ?_⟩, ?_, h1, h6⟩
  · rw [map_smul, map_smul, map_smul, ← (hGm _ _).1 (hpull s _ f ((hπ _ _).2 rfl) h4), hw.trans hω.symm,
      MvPowerSeries.smul_eq_C_mul, MvPowerSeries.smul_eq_C_mul]
    simp only [map_mul, _root_.mul_assoc]
  · rw [y.v.map_mul, y.v.map_mul, hu, hτ, hκ, zero_add, add_zero]

/- English proof (translation)
Set `_` to `H.starRing`. Establish `hk1 : 1 ≤ k` using `by omega`. Establish `hN : 1 ≤ p` using `hp.pos`. Establish `hkN : 1 ≤ k * p` using `Nat.mul_pos hk1 hN`. Establish `haa' : star a * a = (p : 𝓞 E)` using `by rw [mul_comm, haa]`.

Establish `hQa` using `QuadraticAlgebraValuation.qAl_of hL V y.ϖ y.hϖ y.P.D y.Q y.hQ (𝓞 E) y.P.oD a p haa haa'`. Take `⟨G, hGm⟩` from `hG E H V F y (k * p) hkN`. Take `⟨π, -, hπ⟩` from `PullLin.exists_pull_linearMap hL V y.P.D F (𝓞 E) y.P.oD H.w0 y.P.w0 a p k hN hk1 haa`. Take `⟨pt, x, hpt, hx, hE'⟩` from `hE E H V F y a p k hp hk haa Λ e yy α hα he hc Dw I hpk hcop`. Take `⟨w, hw⟩ : ∃ w : LB.Gen (LB.LinComb y.P.D.toPre.P.L (DegPre.lineφ y.P.D.toPre F pt.g.b) (DegPre.lineε (k * p))), w.IsGen` from `ClosedPointWeilPower.gen_local_linComb y.P.D.toPre.P.L y.P.D.toPre.P.isLB _ _`.

Take `⟨ζ, hζ, hfin⟩` from `finOrdExists_of_laws hL V y.P.D F _ hkN pt w hw`. Take `⟨Φ, hΦ⟩` from `phiFun_of_globalFns hL.globalFns V _ y.P.D F _ hkN pt w hw`. Take `⟨χ₀, hχ1, hχ2⟩` from `exists_coset_minimiser y.P.D.toPre.X (QForm.bHom y.hϖ y.P.D y.hQ) y.Q (fun _ _ => QForm.bOf_comm y.P.D _ _) (QForm.two_Q_eq y.hϖ y.P.D y.hQ) (fun _ hx => QForm.Q_pos y.hϖ y.P.D y.hQ hx) r bs Cc hred.2.2.1 (DistribSMul.toAddMonoidHom _ (star a)) p hN (fun x x' => by`. Simplify using `only [QForm.bHom_apply, QForm.bOf, DistribSMul.toAddMonoidHom_apply, ← smul_add, hQa]`. Use the proof step `ring) pt.y`.

Simplify using `only [DistribSMul.toAddMonoidHom_apply] at hχ1 hχ2`. Take `⟨s, hs, hex⟩` from `ExactTerm.main hL hTW hVR hUU V y.ϖ y.hϖ y.P.D y.Q y.hQ F y.v y.hv (𝓞 E) y.P.oD H.w0 y.P.w0 a p k hN hk haa pt w hw ζ hζ hfin χ₀`. Establish `hsm : Fam.IsSmul y.P.D.toPre F ζ (Φ (π s)) (ζ • Φ (π s))` using `(DVR.isSmul_iff _ _ _).2 rfl`. Take `⟨hnu, hsupp, c, hc0, hcv⟩` from `hex (π s) (Φ (π s)) _ ((hπ _ _).2 rfl) ((hΦ _ _).2 rfl) hsm`. Use `set t := ζ • Φ (π s) with ht`.

Use `set r₀ : ℚ := (y.Q (star a • χ₀ + pt.y) : ℚ) / (k * p) with hr₀`. Establish `hkp : (0 : ℚ) < k * p` using `by exact_mod_cast hkN`. Establish `hother : ∀ β, β ≠ star a • χ₀ + pt.y → VGe y.P.D F y.v (k * p) β (t.s β) (r₀ + 1 / (k * p))`. Introduce `β hβ`. Distinguish the cases in `hz : ∃ z, β = pt.y + star a • χ₀ + k • star a • z`.

Take `⟨z, rfl⟩` from `hz`. Use `(hnu _).mono ?_` and prove the remaining obligations. Establish `hz0 : star a • z ≠ 0` using `fun h0 => hβ (by rw [h0, smul_zero, add_zero, add_comm])`. Establish `h1` using `QForm.Q_pos y.hϖ y.P.D y.hQ hz0`. Establish `h2` using `hχ2 k z`.

Establish `h3 : (1 : ℤ) ≤ (k : ℤ) * (k - 1) * y.Q (star a • z)`. Establish `: (4 : ℤ) ≤ k` using `by exact_mod_cast hk`. Establish `h5 : (1 : ℤ) ≤ (k : ℤ) * (k - 1)` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `h4 : (y.Q (star a • χ₀ + pt.y) : ℚ) + 1 ≤ y.Q (pt.y + star a • χ₀ + k • star a • z)`.

Rewrite using `[add_comm (star a • χ₀)]`. Conclude with `(by linarith : y.Q (pt.y + star a • χ₀) + 1 ≤ y.Q (pt.y + star a • χ₀ + k • star a • z))` after adjusting the coercions. Rewrite using `[hr₀, zero_add, ← add_div, Nat.cast_mul]`. Conclude with `div_le_div_of_nonneg_right h4 hkp.le`. Conclude with `vge_of_zero (hsupp β fun z e => hz ⟨z, e⟩) _`.

Establish `hall : ∀ β, VGe y.P.D F y.v (k * p) β (t.s β) r₀` using `fun β => by`. Distinguish the cases in `hβ : β = star a • χ₀ + pt.y`. Substitute `hβ` using the available equality. Use `(hnu _).mono (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[hr₀, zero_add, Nat.cast_mul]`.

Conclude with `(hother β hβ).mono (le_add_of_nonneg_right (by positivity))`. Take `⟨hV1, hV2⟩` from `hV E H V F y (k * p) hkN t (G t) ((hGm _ _).2 rfl)`. Establish `hV1'` using `hV1 r₀ hall`. Establish `hV2'` using `hV2 _ c r₀ _ hc0 hcv (lt_add_of_pos_right _ (by positivity)) hother`. Establish `hcne : c ≠ 0` using `fun h0 => by`.

Rewrite `hcv` using `[h0, y.v.map_zero]`. Conclude with `WithTop.top_ne_coe hcv`. Establish `hci : y.v c⁻¹ = ((-r₀ : ℚ) : WithTop ℚ)`. Rewrite using `[y.v.map_inv, hcv]`. Both sides reduce to the same expression.

Set `f₀ : PS (TWO.Ov y.v) 1 y.d` to `fun mo => ⟨c⁻¹ * MvPowerSeries.coeff mo (G t), by`. Rewrite using `[TWO.mem_Ov, y.v.map_mul, hci]`. Use `le_trans (le_of_eq ?_) (add_le_add le_rfl (hV1' mo))` and prove the remaining obligations. Rewrite using `[← WithTop.coe_add, neg_add_cancel]`. Use the proof step `rfl⟩`.

Establish `hf₀ : FB.toK F f₀ = MvPowerSeries.C c⁻¹ * G t`. Use extensionality with `mo`. Rewrite using `[MvPowerSeries.coeff_C_mul]`. Both sides reduce to the same expression. Take `⟨ω', hω'⟩` from `(MvPowerSeries.isUnit_iff_constantCoeff.2 (hω1 ▸ isUnit_one) : IsUnit ω).exists_left_inv`.

Establish `hω'1 : MvPowerSeries.constantCoeff ω' = 1`. Use `congrArg MvPowerSeries.constantCoeff hω'` as an intermediate fact. Rewrite `this` using `[map_mul, hω1, _root_.mul_one, map_one]`. Then use the resulting hypothesis. Establish `hmap : FB.toK F (MvPowerSeries.map (TWO.fO y.v y.hϖ y.hv) ω') = FB.toK F ω'`. Use extensionality with `mo`.

Simplify using `only [MvPowerSeries.coeff_map, ← fO_comp_eq y, RingHom.comp_apply]`. Establish `hsp : FB.toK F (f₀ * MvPowerSeries.map (TWO.fO y.v y.hϖ y.hv) ω' ^ k) = MvPowerSeries.C c⁻¹ * G t * FB.toK F ω' ^ k`. Rewrite using `[← hf₀, ← hmap]`. Conclude with `(map_mul _ _ _).trans (congrArg _ (map_pow _ _ _))`. Establish `hωω : FB.toK F ω' * FB.toK F ω = 1`.

Rewrite using `[FB.toK, FB.toK, ← map_mul, hω', map_one]`. Establish `hf : FB.toK F (f₀ * MvPowerSeries.map (TWO.fO y.v y.hϖ y.hv) ω' ^ k) * FB.toK F ω ^ k = MvPowerSeries.C c⁻¹ * G t`. Rewrite using `[hsp, _root_.mul_assoc, ← mul_pow, hωω, one_pow, _root_.mul_one]`. Use `⟨s, π s, t, c, f₀ * MvPowerSeries.map (TWO.fO y.v y.hϖ y.hv) ω' ^ k, r₀, ⟨hs, (hπ _ _).2 rfl, ⟨pt, x, w, ζ, _, hpt, hx, hw, hζ, hfin, (hΦ _ _).2 rfl, hsm⟩, (hGm _ _).2 ?_⟩, hcv, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hf, ← _root_.mul_assoc, ← map_mul, mul_inv_cancel₀ hcne, map_one, _root_.one_mul]`.

Establish `hkR : (0 : ℝ) < k` using `by exact_mod_cast hk1`. Establish `hpR : (0 : ℝ) < p` using `by exact_mod_cast hN`. Rewrite using `[hr₀, add_comm (star a • χ₀)]`. Use `push_cast`. Rewrite using `[div_le_iff₀ (by positivity)]`.

Use `hχ1.trans (le_of_eq ?_)` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Rewrite using `[hsp]`. Simplify using `only [FB.toK, map_mul, map_pow, MvPowerSeries.constantCoeff_C, MvPowerSeries.constantCoeff_map, hω'1, map_one, one_pow, _root_.mul_one]`. Rewrite using `[y.v.map_mul, hci, hV2', ← WithTop.coe_add, neg_add_cancel]`.

Both sides reduce to the same expression. Establish `hct : (c⁻¹ * ζ) • Φ (π s) = c⁻¹ • t` using `by rw [ht, smul_smul]`. Use `hE' w hw s (π s) (Φ (π s)) (c⁻¹ * ζ) ((hπ _ _).2 rfl) ((hΦ _ _).2 rfl) (fun χ => ?_) h ω hh hω _ ?_` and prove the remaining obligations. Rewrite using `[hct]`. Use `(hall χ).smul (s' := (c⁻¹ • t).s χ) hci.ge (fun _ => rfl)` as an intermediate fact.

Rewrite `this` using `[add_neg_cancel]`. Then use the resulting hypothesis. Rewrite using `[hct, hf, hGm, G.map_smul c⁻¹ t, MvPowerSeries.smul_eq_C_mul]`.
-/
theorem exists_eigen_column (hL : Laws) (hTW : TwistBCSpanStatement) (hVR : TWM.VRatioGtStatement) (hUU : UUStatement)
    (hG : FamGerm.GermExSt) (hV : GermValSt) (hE : EigGermSt) (Dw : Datum H)
    (I : letI := H.starRing; TateIso Dw F (TFK (R := V) F ⟶ y.P.A.A) (fun a g => g ≫ y.P.oA.act a)
      (fun n g g' c => WeilIs y.P.A.A y.P.A.L n g g' (unitOn c))) (r : ℕ)
    (bs : Module.Basis (Fin r) ℤ y.P.D.toPre.X) (Cc M₀ : ℝ) (hred : y.Red r bs Cc M₀) (a : 𝓞 E) (p k : ℕ)
    (hp : p.Prime) (hk : 4 ≤ k) (haa : letI := H.starRing; a * star a = (p : 𝓞 E))
    (hcop : letI := H.starRing; ∃ u u' : 𝓞 E, u * a + u' * star a = 1) (hpk : Nat.Coprime p k)
    (Λ : Type) (e : Λ → Fin y.d → TWO.Ov y.v) (yy α : Λ → TWO.Ov y.v)
    (hα : ∀ l, α l ∈ Ideal.span {(p : TWO.Ov y.v)})
    (he : letI := H.starRing; ∀ l, (dAct F y.B a).mulVec (fun i => (e l i : F)) = (α l : F) • fun i => (e l i : F))
    (hc : y.CharAt a p e yy)
    (h : PS F 2 y.d) (hh : letI := H.starRing; y.B.IsCanonGauge F h) (ω : PS V 1 y.d)
    (hω1 : MvPowerSeries.constantCoeff ω = 1)
    (hω : letI := H.starRing; FB.toK F ω =
      FB.expS F (ev (n := 1) ![y.B.actK F a] (y.B.hL F h H.w0) - (p : F) • y.B.hL F h H.w0)) :
    letI := H.starRing
    ∃ (s : Fam y.P.D.toPre F k) (s' t : Fam y.P.D.toPre F (k * p)) (c : F) (f : PS (TWO.Ov y.v) 1 y.d) (r₀ : ℚ),
      (NuGe y.P.D y.Q F y.v k s 0 ∧ PullAl y.P.D F y.P.oD a k p s s' ∧ y.Transl (k * p) (star a) s' t ∧
        y.Germ (k * p) t (MvPowerSeries.C c * (FB.toK F f * FB.toK F ω ^ k))) ∧
      y.v c = (r₀ : ℚ) ∧ (r₀ : ℝ) ≤ r * Cc / (4 * k) ∧ y.v (MvPowerSeries.constantCoeff (FB.toK F f)) = 0 ∧
      ∀ l mo, y.v (p : F) ≤ y.v (MvPowerSeries.coeff mo (Dof (y.B.FK F) (fun i => (e l i : F)) (FB.toK F f) -
        MvPowerSeries.C (yy l : F) * FB.toK F f)) := by
  let _ := H.starRing
  have hk1 : 1 ≤ k := by omega
  have hN : 1 ≤ p := hp.pos
  have hkN : 1 ≤ k * p := Nat.mul_pos hk1 hN
  have haa' : star a * a = (p : 𝓞 E) := by rw [mul_comm, haa]
  have hQa := QuadraticAlgebraValuation.qAl_of hL V y.ϖ y.hϖ y.P.D y.Q y.hQ (𝓞 E) y.P.oD a p haa haa'
  obtain ⟨G, hGm⟩ := hG E H V F y (k * p) hkN
  obtain ⟨π, -, hπ⟩ := PullLin.exists_pull_linearMap hL V y.P.D F (𝓞 E) y.P.oD H.w0 y.P.w0 a p k hN hk1 haa
  obtain ⟨pt, x, hpt, hx, hE'⟩ := hE E H V F y a p k hp hk haa Λ e yy α hα he hc Dw I hpk hcop
  obtain ⟨w, hw⟩ : ∃ w : LB.Gen (LB.LinComb y.P.D.toPre.P.L (DegPre.lineφ y.P.D.toPre F pt.g.b)
      (DegPre.lineε (k * p))), w.IsGen := ClosedPointWeilPower.gen_local_linComb y.P.D.toPre.P.L y.P.D.toPre.P.isLB _ _
  obtain ⟨ζ, hζ, hfin⟩ := finOrdExists_of_laws hL V y.P.D F _ hkN pt w hw
  obtain ⟨Φ, hΦ⟩ := phiFun_of_globalFns hL.globalFns V _ y.P.D F _ hkN pt w hw
  obtain ⟨χ₀, hχ1, hχ2⟩ := exists_coset_minimiser y.P.D.toPre.X (QForm.bHom y.hϖ y.P.D y.hQ) y.Q
    (fun _ _ => QForm.bOf_comm y.P.D _ _) (QForm.two_Q_eq y.hϖ y.P.D y.hQ)
    (fun _ hx => QForm.Q_pos y.hϖ y.P.D y.hQ hx) r bs Cc hred.2.2.1 (DistribSMul.toAddMonoidHom _ (star a)) p hN
    (fun x x' => by
      simp only [QForm.bHom_apply, QForm.bOf, DistribSMul.toAddMonoidHom_apply, ← smul_add, hQa]
      ring) pt.y
  simp only [DistribSMul.toAddMonoidHom_apply] at hχ1 hχ2
  obtain ⟨s, hs, hex⟩ := ExactTerm.main hL hTW hVR hUU V y.ϖ y.hϖ y.P.D y.Q y.hQ F y.v y.hv (𝓞 E) y.P.oD H.w0 y.P.w0
    a p k hN hk haa pt w hw ζ hζ hfin χ₀
  have hsm : Fam.IsSmul y.P.D.toPre F ζ (Φ (π s)) (ζ • Φ (π s)) := (DVR.isSmul_iff _ _ _).2 rfl
  obtain ⟨hnu, hsupp, c, hc0, hcv⟩ := hex (π s) (Φ (π s)) _ ((hπ _ _).2 rfl) ((hΦ _ _).2 rfl) hsm
  set t := ζ • Φ (π s) with ht
  set r₀ : ℚ := (y.Q (star a • χ₀ + pt.y) : ℚ) / (k * p) with hr₀
  have hkp : (0 : ℚ) < k * p := by exact_mod_cast hkN
  have hother : ∀ β, β ≠ star a • χ₀ + pt.y → VGe y.P.D F y.v (k * p) β (t.s β) (r₀ + 1 / (k * p)) := by
    intro β hβ
    by_cases hz : ∃ z, β = pt.y + star a • χ₀ + k • star a • z
    · obtain ⟨z, rfl⟩ := hz
      refine (hnu _).mono ?_
      have hz0 : star a • z ≠ 0 := fun h0 => hβ (by rw [h0, smul_zero, add_zero, add_comm])
      have h1 := QForm.Q_pos y.hϖ y.P.D y.hQ hz0
      have h2 := hχ2 k z
      have h3 : (1 : ℤ) ≤ (k : ℤ) * (k - 1) * y.Q (star a • z) := by
        have : (4 : ℤ) ≤ k := by exact_mod_cast hk
        have h5 : (1 : ℤ) ≤ (k : ℤ) * (k - 1) := by nlinarith
        nlinarith
      have h4 : (y.Q (star a • χ₀ + pt.y) : ℚ) + 1 ≤ y.Q (pt.y + star a • χ₀ + k • star a • z) := by
        rw [add_comm (star a • χ₀)]
        exact_mod_cast (by linarith : y.Q (pt.y + star a • χ₀) + 1 ≤ y.Q (pt.y + star a • χ₀ + k • star a • z))
      rw [hr₀, zero_add, ← add_div, Nat.cast_mul]
      exact div_le_div_of_nonneg_right h4 hkp.le
    · exact vge_of_zero (hsupp β fun z e => hz ⟨z, e⟩) _
  have hall : ∀ β, VGe y.P.D F y.v (k * p) β (t.s β) r₀ := fun β => by
    by_cases hβ : β = star a • χ₀ + pt.y
    · subst hβ
      refine (hnu _).mono (le_of_eq ?_)
      rw [hr₀, zero_add, Nat.cast_mul]
    · exact (hother β hβ).mono (le_add_of_nonneg_right (by positivity))
  obtain ⟨hV1, hV2⟩ := hV E H V F y (k * p) hkN t (G t) ((hGm _ _).2 rfl)
  have hV1' := hV1 r₀ hall
  have hV2' := hV2 _ c r₀ _ hc0 hcv (lt_add_of_pos_right _ (by positivity)) hother
  have hcne : c ≠ 0 := fun h0 => by
    rw [h0, y.v.map_zero] at hcv
    exact WithTop.top_ne_coe hcv
  have hci : y.v c⁻¹ = ((-r₀ : ℚ) : WithTop ℚ) := by
    rw [y.v.map_inv, hcv]; rfl
  let f₀ : PS (TWO.Ov y.v) 1 y.d := fun mo => ⟨c⁻¹ * MvPowerSeries.coeff mo (G t), by
    rw [TWO.mem_Ov, y.v.map_mul, hci]
    refine le_trans (le_of_eq ?_) (add_le_add le_rfl (hV1' mo))
    rw [← WithTop.coe_add, neg_add_cancel]; rfl⟩
  have hf₀ : FB.toK F f₀ = MvPowerSeries.C c⁻¹ * G t := by
    ext mo
    rw [MvPowerSeries.coeff_C_mul]; rfl
  obtain ⟨ω', hω'⟩ := (MvPowerSeries.isUnit_iff_constantCoeff.2 (hω1 ▸ isUnit_one) : IsUnit ω).exists_left_inv
  have hω'1 : MvPowerSeries.constantCoeff ω' = 1 := by
    have := congrArg MvPowerSeries.constantCoeff hω'
    rwa [map_mul, hω1, _root_.mul_one, map_one] at this
  have hmap : FB.toK F (MvPowerSeries.map (TWO.fO y.v y.hϖ y.hv) ω') = FB.toK F ω' := by
    ext mo
    simp only [MvPowerSeries.coeff_map, ← fO_comp_eq y, RingHom.comp_apply]
  have hsp : FB.toK F (f₀ * MvPowerSeries.map (TWO.fO y.v y.hϖ y.hv) ω' ^ k) =
      MvPowerSeries.C c⁻¹ * G t * FB.toK F ω' ^ k := by
    rw [← hf₀, ← hmap]
    exact (map_mul _ _ _).trans (congrArg _ (map_pow _ _ _))
  have hωω : FB.toK F ω' * FB.toK F ω = 1 := by
    rw [FB.toK, FB.toK, ← map_mul, hω', map_one]
  have hf : FB.toK F (f₀ * MvPowerSeries.map (TWO.fO y.v y.hϖ y.hv) ω' ^ k) * FB.toK F ω ^ k =
      MvPowerSeries.C c⁻¹ * G t := by
    rw [hsp, _root_.mul_assoc, ← mul_pow, hωω, one_pow, _root_.mul_one]
  refine ⟨s, π s, t, c, f₀ * MvPowerSeries.map (TWO.fO y.v y.hϖ y.hv) ω' ^ k, r₀, ⟨hs, (hπ _ _).2 rfl,
    ⟨pt, x, w, ζ, _, hpt, hx, hw, hζ, hfin, (hΦ _ _).2 rfl, hsm⟩, (hGm _ _).2 ?_⟩, hcv, ?_, ?_, ?_⟩
  · rw [hf, ← _root_.mul_assoc, ← map_mul, mul_inv_cancel₀ hcne, map_one, _root_.one_mul]
  · have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
    have hpR : (0 : ℝ) < p := by exact_mod_cast hN
    rw [hr₀, add_comm (star a • χ₀)]
    push_cast
    rw [div_le_iff₀ (by positivity)]
    refine hχ1.trans (le_of_eq ?_)
    field_simp
  · rw [hsp]
    simp only [FB.toK, map_mul, map_pow, MvPowerSeries.constantCoeff_C, MvPowerSeries.constantCoeff_map, hω'1, map_one,
      one_pow, _root_.mul_one]
    rw [y.v.map_mul, hci, hV2', ← WithTop.coe_add, neg_add_cancel]; rfl
  · have hct : (c⁻¹ * ζ) • Φ (π s) = c⁻¹ • t := by rw [ht, smul_smul]
    refine hE' w hw s (π s) (Φ (π s)) (c⁻¹ * ζ) ((hπ _ _).2 rfl) ((hΦ _ _).2 rfl) (fun χ => ?_) h ω hh hω _ ?_
    · rw [hct]
      have := (hall χ).smul (s' := (c⁻¹ • t).s χ) hci.ge (fun _ => rfl)
      rwa [add_neg_cancel] at this
    · rw [hct, hf, hGm, G.map_smul c⁻¹ t, MvPowerSeries.smul_eq_C_mul]

end GlobalTheory.DepthBound
