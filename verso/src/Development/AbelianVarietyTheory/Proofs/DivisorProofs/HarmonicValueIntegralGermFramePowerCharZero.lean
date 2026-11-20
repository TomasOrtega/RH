import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralChartFormalBiextensionGaugeBound
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeExists
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeNabValBaseChange
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicValueCopiesGaugeIndependent
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FFVMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.FramePower

/- English proof (translation)
Establish `gC : GP (comp1 (B.actK R w0) (pt R (n` using `1) d 0)) := gp_comp1 _ _ (GlobalTheory.GaugeBaseChange.gp_actK B w0) (gp_pt 0)`. Establish `cL : MvPowerSeries.constantCoeff (B.hL R h w0) = 0` using `gt_const_ev _ (pair_points_zero_constant (gp_pt 0) gC) h hc`. Establish `eL : MvPowerSeries.map (algebraMap R K) (B.hL R h w0) = B.hL K (FB.toK K h) w0`. Unfold `FB.hL`. Rewrite using `[GlobalTheory.GaugeBaseChange.map_ev_two _ _ _ (gp_pt _) gC, GlobalTheory.QuadDeriv.baseChange_comp1 _ _ _ (gp_pt _), GlobalTheory.QuadDeriv.baseChange_pt]`.

Use `GlobalTheory.GaugeBaseChange.baseChange_actK B (Algebra.ofId R K) w0` as an intermediate fact. Conclude with `congrArg (fun t => ev (n := 1) ![pt K d 0, comp1 t (pt K d 0)] (FB.toK K h)) this`. Use `set S : PS R n d := ∑ b : Fin n, ev (n := n) ![pt R d b] (B.hL R h w0) with hS`. Establish `gp : ∀ b : Fin n, ∀ j : Fin 1, GP ((![pt R d b] : Fin 1 → Pt R n d) j)`. Introduce `b j`.

Use `fin_cases j`. Conclude with `gp_pt b`. Establish `cS : MvPowerSeries.constantCoeff S = 0`. Rewrite using `[hS, map_sum]`. Conclude with `Finset.sum_eq_zero fun b _ => gt_const_ev _ (gp b) _ cL`.

Establish `eS : MvPowerSeries.map (algebraMap R K) S = ∑ b : Fin n, ev (n` using `n) ![pt K d b] (B.hL K (FB.toK K h) w0) := by`. Rewrite using `[hS, map_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.QuadDeriv.map_ev _ _ (gp b), eL]`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Use `fin_cases j`. Conclude with `GlobalTheory.QuadDeriv.baseChange_pt _ _`. Establish `cm : ∀ m : ℕ, MvPowerSeries.constantCoeff ((m : R) • S) = 0` using `fun m => by`. Rewrite using `[MvPowerSeries.smul_eq_C_mul, map_mul, cS, mul_zero]`.

Establish `em : ∀ m : ℕ, FB.expS K ((m : K) • ∑ b : Fin n, ev (n` using `n) ![pt K d b] (B.hL K (FB.toK K h) w0)) = FB.toK K (FB.expS R ((m : R) • S)) := fun m => by`. Rewrite using `[FB.toK.eq_1 K (FB.expS R _), GlobalTheory.GaugeBaseChange.map_expS _ _ (cm m), MvPowerSeries.smul_eq_C_mul, MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.map_C, map_natCast (algebraMap R K), eS]`. Use `⟨g * FB.expS R ((k : R) • S - (k' : R) • S), fun cp u P => ?_⟩` and prove the remaining obligations. Unfold `nabValN`. Rewrite using `[em, em, FB.toK, FB.toK, FB.toK, FB.toK, ← map_mul, ← map_mul, _root_.mul_assoc, ← gt_expS_add _ _ (by rw [map_sub, cm, cm, sub_zero]) (cm k'), sub_add_cancel]`.
-/
theorem exists_nabValN_eq_of_map {R K O : Type} [CommRing R] [Algebra ℚ R] [CommRing K] [Algebra ℚ K] [Algebra R K]
    [CommRing O] [StarRing O] {d : ℕ} (B : FB R d O) (h : PS R 2 d) (hc : MvPowerSeries.constantCoeff h = 0)
    (w0 : O) (k k' : ℕ) {n : ℕ} (g : PS R n d) :
    ∃ g' : PS R n d, ∀ {Ix : Type} [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → K) (P : MvPolynomial Ix K),
      nabValN B K (FB.toK K h) w0 k (FB.toK K g) cp u P = nabValN B K (FB.toK K h) w0 k' (FB.toK K g') cp u P := by
  have gC : GP (comp1 (B.actK R w0) (pt R (n := 1) d 0)) :=
    gp_comp1 _ _ (GlobalTheory.GaugeBaseChange.gp_actK B w0) (gp_pt 0)
  have cL : MvPowerSeries.constantCoeff (B.hL R h w0) = 0 := gt_const_ev _ (pair_points_zero_constant (gp_pt 0) gC) h hc
  have eL : MvPowerSeries.map (algebraMap R K) (B.hL R h w0) = B.hL K (FB.toK K h) w0 := by
    unfold FB.hL
    rw [GlobalTheory.GaugeBaseChange.map_ev_two _ _ _ (gp_pt _) gC, GlobalTheory.QuadDeriv.baseChange_comp1 _ _ _ (gp_pt _),
      GlobalTheory.QuadDeriv.baseChange_pt]
    have := GlobalTheory.GaugeBaseChange.baseChange_actK B (Algebra.ofId R K) w0
    exact congrArg (fun t => ev (n := 1) ![pt K d 0, comp1 t (pt K d 0)] (FB.toK K h)) this
  set S : PS R n d := ∑ b : Fin n, ev (n := n) ![pt R d b] (B.hL R h w0) with hS
  have gp : ∀ b : Fin n, ∀ j : Fin 1, GP ((![pt R d b] : Fin 1 → Pt R n d) j) := by
    intro b j; fin_cases j; exact gp_pt b
  have cS : MvPowerSeries.constantCoeff S = 0 := by
    rw [hS, map_sum]
    exact Finset.sum_eq_zero fun b _ => gt_const_ev _ (gp b) _ cL
  have eS : MvPowerSeries.map (algebraMap R K) S =
      ∑ b : Fin n, ev (n := n) ![pt K d b] (B.hL K (FB.toK K h) w0) := by
    rw [hS, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [GlobalTheory.QuadDeriv.map_ev _ _ (gp b), eL]
    congr 1
    funext j; fin_cases j
    exact GlobalTheory.QuadDeriv.baseChange_pt _ _
  have cm : ∀ m : ℕ, MvPowerSeries.constantCoeff ((m : R) • S) = 0 := fun m => by
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, cS, mul_zero]
  have em : ∀ m : ℕ, FB.expS K ((m : K) • ∑ b : Fin n, ev (n := n) ![pt K d b] (B.hL K (FB.toK K h) w0)) =
      FB.toK K (FB.expS R ((m : R) • S)) := fun m => by
    rw [FB.toK.eq_1 K (FB.expS R _), GlobalTheory.GaugeBaseChange.map_expS _ _ (cm m), MvPowerSeries.smul_eq_C_mul, MvPowerSeries.smul_eq_C_mul,
      map_mul, MvPowerSeries.map_C, map_natCast (algebraMap R K), eS]
  refine ⟨g * FB.expS R ((k : R) • S - (k' : R) • S), fun cp u P => ?_⟩
  unfold nabValN
  rw [em, em, FB.toK, FB.toK, FB.toK, FB.toK, ← map_mul, ← map_mul, _root_.mul_assoc,
    ← gt_expS_add _ _ (by rw [map_sub, cm, cm, sub_zero]) (cm k'), sub_add_cancel]

end GlobalTheory.FramePower

open GlobalTheory.FramePower in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c`. Use `letI := H.starRing`. Establish `hstar : ∀ a : 𝓞 E, star a = H.bar a` using `fun _ => rfl`. Introduce `T io y C hchar`. Use `letI := io.toAlgebra`.

Introduce `a n k k' P hP f hf`. Take `⟨B, hBT, hB⟩` from `GlobalTheory.PlaceInt.integralBiext_gauge_eig_bound E H Dw l Xo c hstar T io y C`. Take `⟨hg, -, heig, -⟩` from `hB B hBT`. Take `⟨hF, hA, -⟩` from `C.gen.1`. Take `⟨e1, e2, -⟩` from `hBT`.

Establish `eF : B.FK T.Fr = C.ch.B.FK T.Fr`. Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `MvPowerSeries.map _ (B.G.F i) = MvPowerSeries.map _ (C.ch.B.G.F i)`. Rewrite using `[GlobalTheory.ChartBiext.toK_self, hF, e1]`. Establish `eA : ∀ a, B.actK T.Fr a = C.ch.B.actK T.Fr a`.

Introduce `a`. Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `MvPowerSeries.map _ (B.A.act a i) = MvPowerSeries.map _ (C.ch.B.A.act a i)`. Rewrite using `[GlobalTheory.ChartBiext.toK_self, hA, e2]`. Use `letI : Algebra ℚ T.V := (IsLocalization.lift (M := nonZeroDivisors ℤ) (S := ℚ) (g := Int.castRingHom T.V) (by`.

Introduce and unpack `⟨z, hz⟩`. Establish `h0 : z ≠ 0` using `nonZeroDivisors.ne_zero hz`. Rewrite using `[← residue_ne_zero_iff_isUnit]`. Simplify using `using h0)).toAlgebra`. Take `⟨h0, hh0⟩` from `GlobalTheory.canonGauge_exists T.V (chD C.ch) (𝓞 E) T.V B`.

Establish `hh1 : B.IsCanonGauge T.Fr (FB.toK T.Fr h0)` using `GlobalTheory.GaugeBaseChange.isCanonGauge_map B (Algebra.ofId T.V T.Fr) hh0`. Use `choose g hg' using hf`. Establish `ef : f = FB.toK T.Fr (g : PS T.V n (chD C.ch))`. Use extensionality with `m`. Conclude with `(hg' m).symm.trans (MvPowerSeries.coeff_map (algebraMap T.V T.Fr) m (g : PS T.V n (chD C.ch))).symm`.

Take `⟨g', hgg⟩` from `exists_nabValN_eq_of_map (K := T.Fr) B h0 (GlobalTheory.GaugeBaseChange.const_of_axis hh0.ax0) H.w0 k k' (g : PS T.V n (chD C.ch))`. Establish `key` using `GlobalTheory.nabValN_harmonic_gauge_independent T.V (chD C.ch) (𝓞 E) T.Fr B (gaugeOf C) (FB.toK T.Fr h0) hg hh1 (E →+* ℂ) Dw.mult ComplexEmbedding.conjugate (InPsi H) (fun τ => io.comp (embK c τ)) (fun τ => by ext x; simp) (ReciprocityTheory.ChartRestriction.G.PullbackSections.CV …`. Rewrite using `[RingHom.comp_apply, RingHom.comp_apply, hstar]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[embK_coe, embK_coe, ComplexEmbedding.conjugate_coe_eq, H.bar_eq, IsCMField.complexEmbedding_complexConj])`. Use the proof step `(fun σ τ hne => by`. Establish `hex : ∃ a : 𝓞 E, σ (a : E) ≠ τ (a : E)`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`.

Conclude with `hne (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => by simpa using hc a))`. Take `⟨a, ha⟩` from `hex`. Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `h0 : embK c σ a - embK c τ a ≠ 0`. Rewrite using `[sub_ne_zero]`.

Introduce `h1`. Apply `ha` to reduce the goal to its premises. Rewrite using `[← embK_coe c, ← embK_coe c, h1]`. Rewrite using `[RingHom.comp_apply, RingHom.comp_apply, ← map_sub]`. Conclude with `(Ne.isUnit h0).map _)`.

Use the proof step `C.ch.uvec heig n (MvPolynomial.map io P) (ReciprocityTheory.ChartRestriction.G.PullbackSections.harmK_map io hP.1.1) H.w0`. Use `⟨FB.toK T.Fr g', fun m => ⟨_, (MvPowerSeries.coeff_map _ _ _).symm⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← GlobalTheory.ChartBiext.nabValN_congr B C.ch.B eF eA, ← GlobalTheory.ChartBiext.nabValN_congr B C.ch.B eF eA]`. Use `(key k f).trans (Eq.trans ?_ (key k' _).symm)` and prove the remaining obligations. Rewrite using `[ef]`.

Conclude with `hgg _ _ _`.
-/
theorem GlobalTheory.FramePower.exists_nabValN_eq_of_harmonic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), CharZero (IsLocalRing.ResidueField T.V) → letI := io.toAlgebra; ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n k k' : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ f : PS T.Fr n (chD C.ch), IsIntPS T f → ∃ f' : PS T.Fr n (chD C.ch), IsIntPS T f' ∧ nabValN C.ch.B T.Fr C.ch.h H.w0 k f (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map io P) = nabValN C.ch.B T.Fr C.ch.h H.w0 k' f' (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map io P) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  have hstar : ∀ a : 𝓞 E, star a = H.bar a := fun _ => rfl
  intro T io y C hchar
  letI := io.toAlgebra
  intro a n k k' P hP f hf
  obtain ⟨B, hBT, hB⟩ := GlobalTheory.PlaceInt.integralBiext_gauge_eig_bound E H Dw l Xo c hstar T io y C
  obtain ⟨hg, -, heig, -⟩ := hB B hBT
  obtain ⟨hF, hA, -⟩ := C.gen.1
  obtain ⟨e1, e2, -⟩ := hBT
  have eF : B.FK T.Fr = C.ch.B.FK T.Fr := by
    funext i
    change MvPowerSeries.map _ (B.G.F i) = MvPowerSeries.map _ (C.ch.B.G.F i)
    rw [GlobalTheory.ChartBiext.toK_self, hF, e1]
  have eA : ∀ a, B.actK T.Fr a = C.ch.B.actK T.Fr a := by
    intro a
    funext i
    change MvPowerSeries.map _ (B.A.act a i) = MvPowerSeries.map _ (C.ch.B.A.act a i)
    rw [GlobalTheory.ChartBiext.toK_self, hA, e2]
  letI : Algebra ℚ T.V := (IsLocalization.lift (M := nonZeroDivisors ℤ) (S := ℚ) (g := Int.castRingHom T.V) (by
    rintro ⟨z, hz⟩
    have h0 : z ≠ 0 := nonZeroDivisors.ne_zero hz
    rw [← residue_ne_zero_iff_isUnit]
    simpa using h0)).toAlgebra
  obtain ⟨h0, hh0⟩ := GlobalTheory.canonGauge_exists T.V (chD C.ch) (𝓞 E) T.V B
  have hh1 : B.IsCanonGauge T.Fr (FB.toK T.Fr h0) :=
    GlobalTheory.GaugeBaseChange.isCanonGauge_map B (Algebra.ofId T.V T.Fr) hh0
  choose g hg' using hf
  have ef : f = FB.toK T.Fr (g : PS T.V n (chD C.ch)) := by
    ext m
    exact (hg' m).symm.trans (MvPowerSeries.coeff_map (algebraMap T.V T.Fr) m (g : PS T.V n (chD C.ch))).symm
  obtain ⟨g', hgg⟩ := exists_nabValN_eq_of_map (K := T.Fr) B h0 (GlobalTheory.GaugeBaseChange.const_of_axis hh0.ax0)
    H.w0 k k' (g : PS T.V n (chD C.ch))
  have key := GlobalTheory.nabValN_harmonic_gauge_independent T.V (chD C.ch) (𝓞 E) T.Fr B (gaugeOf C) (FB.toK T.Fr h0) hg hh1
    (E →+* ℂ) Dw.mult ComplexEmbedding.conjugate (InPsi H) (fun τ => io.comp (embK c τ)) (fun τ => by ext x; simp)
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.inPsi_or H)
    (fun τ a => by
      rw [RingHom.comp_apply, RingHom.comp_apply, hstar]
      congr 1
      apply Subtype.ext
      rw [embK_coe, embK_coe, ComplexEmbedding.conjugate_coe_eq, H.bar_eq, IsCMField.complexEmbedding_complexConj])
    (fun σ τ hne => by
      have hex : ∃ a : 𝓞 E, σ (a : E) ≠ τ (a : E) := by
        by_contra hc
        push Not at hc
        exact hne (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => by simpa using hc a))
      obtain ⟨a, ha⟩ := hex
      refine ⟨a, ?_⟩
      have h0 : embK c σ a - embK c τ a ≠ 0 := by
        rw [sub_ne_zero]
        intro h1
        apply ha
        rw [← embK_coe c, ← embK_coe c, h1]
      rw [RingHom.comp_apply, RingHom.comp_apply, ← map_sub]
      exact (Ne.isUnit h0).map _)
    C.ch.uvec heig n (MvPolynomial.map io P) (ReciprocityTheory.ChartRestriction.G.PullbackSections.harmK_map io hP.1.1) H.w0
  refine ⟨FB.toK T.Fr g', fun m => ⟨_, (MvPowerSeries.coeff_map _ _ _).symm⟩, ?_⟩
  rw [← GlobalTheory.ChartBiext.nabValN_congr B C.ch.B eF eA, ← GlobalTheory.ChartBiext.nabValN_congr B C.ch.B eF eA]
  refine (key k f).trans (Eq.trans ?_ (key k' _).symm)
  rw [ef]
  exact hgg _ _ _
