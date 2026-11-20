import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeyAtIffExistsKeyAtVia
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombSnd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivativesSeparateLieBasisCoeffsCartesianStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameMatrixHasSum
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieCombIffProd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcLieCoord

open MonoidalCategory CartesianMonoidalCategory MonObj Filter GlobalTheory.ArcLie

/- English proof (translation)
Rewrite `hc` using `[GlobalTheory.PowLie.isLieComb_iff_prod]`. Substitute `hc` using the available equality. Rewrite using `[GlobalTheory.PowLie.isTangent_iff]`. Establish `e0 : ∀ a : R, GlobalTheory.PowLie.zeroPt R ≫ GlobalTheory.PowLie.sc a = GlobalTheory.PowLie.zeroPt R` using `fun a => by`. Use `Over.OverMorphism.ext ?_` and prove the remaining obligations.

Simplify using `only [Over.comp_left, GlobalTheory.PowLie.zeroPt, GlobalTheory.PowLie.sc, Over.homMk_left]`. Rewrite using `[GlobalTheory.TanMod.spMap_comp']`. Use `congr 1`. Use `RingHom.ext fun r => ?_` and prove the remaining obligations. Simplify using `[epsScaleR]`.

Establish `e1` using `map_prod (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom (G := G) (GlobalTheory.PowLie.zeroPt R)) (fun k => GlobalTheory.PowLie.sc (c k) ≫ v k) Finset.univ`. Use `e1.trans ?_` and prove the remaining obligations. Use `(Finset.prod_congr rfl fun k _ => ?_).trans (Finset.prod_const_one)` and prove the remaining obligations. Use `show GlobalTheory.PowLie.zeroPt R ≫ GlobalTheory.PowLie.sc (c k) ≫ v k = 1`. Rewrite using `[← Category.assoc, e0, (GlobalTheory.PowLie.isTangent_iff _).1 (hv k)]`.

Both sides reduce to the same expression.
-/
theorem comb_tan {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ}
    (v : Fin n → (epsR R ⟶ G)) (hv : ∀ k, IsTangent (v k)) (c : Fin n → R) (w : epsR R ⟶ G) (hc : IsLieComb c v w) :
    IsTangent w := by
  rw [GlobalTheory.PowLie.isLieComb_iff_prod] at hc
  subst hc
  rw [GlobalTheory.PowLie.isTangent_iff]
  have e0 : ∀ a : R, GlobalTheory.PowLie.zeroPt R ≫ GlobalTheory.PowLie.sc a = GlobalTheory.PowLie.zeroPt R := fun a => by
    refine Over.OverMorphism.ext ?_
    simp only [Over.comp_left, GlobalTheory.PowLie.zeroPt, GlobalTheory.PowLie.sc, Over.homMk_left]
    rw [GlobalTheory.TanMod.spMap_comp']
    congr 1
    refine RingHom.ext fun r => ?_
    simp [epsScaleR]
  have e1 := map_prod (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom (G := G) (GlobalTheory.PowLie.zeroPt R)) (fun k => GlobalTheory.PowLie.sc (c k) ≫ v k)
    Finset.univ
  refine e1.trans ?_
  refine (Finset.prod_congr rfl fun k _ => ?_).trans (Finset.prod_const_one)
  show GlobalTheory.PowLie.zeroPt R ≫ GlobalTheory.PowLie.sc (c k) ≫ v k = 1
  rw [← Category.assoc, e0, (GlobalTheory.PowLie.isTangent_iff _).1 (hv k)]
  rfl

/- English proof (translation)
Take `⟨d, hd⟩` from `IsLocalization.exist_integer_multiples (M := nonZeroDivisors (PowerSeries ℂ)) (S := ℂ⸨X⸩) Finset.univ a`. Use `choose b hb using fun k => hd k (Finset.mem_univ k)`. Establish `hinj : Function.Injective (HahnSeries.ofPowerSeries ℤ ℂ)` using `HahnSeries.ofPowerSeries_injective`. Establish `hb' : ∀ k, HahnSeries.ofPowerSeries ℤ ℂ (b k) = HahnSeries.ofPowerSeries ℤ ℂ (d : PowerSeries ℂ) * a k` using `fun k => by`. Rewrite using `[← LaurentSeries.coe_algebraMap, hb k, Algebra.smul_def, LaurentSeries.coe_algebraMap]`.

Establish `h0` using `GlobalTheory.T.derivatives_separate_lieBasis_coeffs_cartesian h v hv hA hV b fun f => hinj (by`. Rewrite using `[map_sum, map_zero]`. Establish `e` using `congrArg (fun t => HahnSeries.ofPowerSeries ℤ ℂ (d : PowerSeries ℂ) * t) (ha f)`. Simplify using `only [mul_zero, Finset.mul_sum] at e`. Rewrite using `[← e]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hb', _root_.mul_assoc])`. Use function extensionality and compare the values at `k`. Establish `hd0 : HahnSeries.ofPowerSeries ℤ ℂ (d : PowerSeries ℂ) ≠ 0` using `fun e => nonZeroDivisors.coe_ne_zero d (hinj (e.trans (map_zero _).symm))`. Use `hb' k` as an intermediate fact.

Rewrite `this` using `[h0, Pi.zero_apply, map_zero]`. Conclude with `(mul_eq_zero.1 this.symm).resolve_left hd0`.
-/
theorem sep_laurent {X : Scheme.{0}} {x : Sp (PowerSeries ℂ) ⟶ X} {G : Over X} {G' : Over (Sp (PowerSeries ℂ))} [GrpObj G]
    [GrpObj G'] [IsCommMonObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G x φ) {n : ℕ}
    (v : Fin n → (epsR (PowerSeries ℂ) ⟶ G')) (hv : IsLieBasis v) {V : G.left.Opens} (hA : IsAffineOpen V)
    (hV : ⊤ ≤ ((η[G']).left ≫ φ) ⁻¹ᵁ V) (a : Fin n → ℂ⸨X⸩)
    (ha : ∀ f : Γ(G.left, V), ∑ k, a k * HahnSeries.ofPowerSeries ℤ ℂ (valR ((v k).left ≫ φ) V f).snd = 0) : a = 0 := by
  classical
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (M := nonZeroDivisors (PowerSeries ℂ)) (S := ℂ⸨X⸩)
    Finset.univ a
  choose b hb using fun k => hd k (Finset.mem_univ k)
  have hinj : Function.Injective (HahnSeries.ofPowerSeries ℤ ℂ) := HahnSeries.ofPowerSeries_injective
  have hb' : ∀ k, HahnSeries.ofPowerSeries ℤ ℂ (b k) = HahnSeries.ofPowerSeries ℤ ℂ (d : PowerSeries ℂ) * a k := fun k => by
    rw [← LaurentSeries.coe_algebraMap, hb k, Algebra.smul_def, LaurentSeries.coe_algebraMap]
  have h0 := GlobalTheory.T.derivatives_separate_lieBasis_coeffs_cartesian h v hv hA hV b fun f => hinj (by
    rw [map_sum, map_zero]
    have e := congrArg (fun t => HahnSeries.ofPowerSeries ℤ ℂ (d : PowerSeries ℂ) * t) (ha f)
    simp only [mul_zero, Finset.mul_sum] at e
    rw [← e]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, hb', _root_.mul_assoc])
  funext k
  have hd0 : HahnSeries.ofPowerSeries ℤ ℂ (d : PowerSeries ℂ) ≠ 0 := fun e =>
    nonZeroDivisors.coe_ne_zero d (hinj (e.trans (map_zero _).symm))
  have := hb' k
  rw [h0, Pi.zero_apply, map_zero] at this
  exact (mul_eq_zero.1 this.symm).resolve_left hd0

/- English proof (translation)
Rewrite using `[valR, dif_pos h]`. Both sides reduce to the same expression.
-/
theorem valR_eq_ev' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : valR x U f = ev x U h f := by
  rw [valR, dif_pos h]; rfl

section Point

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

/- English proof (translation)
Take `⟨-, -, hg', -, -, -, -, hv⟩` from `hK`. Establish `e1 : (x.v i).left ≫ φ = spMap (dualMap (ev z M.U hz)) ≫ M.v₀ j`. Rewrite using `[hv i]`. Use `congr 2`. Conclude with `Fin.ext hij`.

Rewrite `hV`, the goal using `[← e1]`. Establish `hU : ⊤ ≤ (x.v i).left ⁻¹ᵁ (φ ⁻¹ᵁ V)` using `hV`. Establish `hd'` using `hd (φ ⁻¹ᵁ V) hU ((φ.app V).hom f)`. Establish `e2 : (fun t => valAt' (e t) V f) = fun t => valAt' (u.ex t).left (φ ⁻¹ᵁ V) ((φ.app V).hom f)`. Use function extensionality and compare the values at `fun t => by rw [he, GlobalTheory.HolHom.valAt'_eq_valR, GlobalTheory.HolHom.valAt'_eq_valR, GlobalTheory.HolHom.valR_comp]`.

Rewrite using `[e2, ← hd', GlobalTheory.HolHom.valR_comp, GlobalTheory.HolHom.valR_eq _ _ hU]`. Both sides reduce to the same expression.
-/
theorem point_snd {Y : Model Xo c β} (M : GChart Y) {z : Sp ℂ ⟶ Y.X} {hz : ⊤ ≤ z ⁻¹ᵁ M.U} {x : KeyIn ℂ}
    {φ : x.P.A.left ⟶ Y.t.G.left} (hK : GlobalTheory.ArcNormal.KeyAtVia M z hz x φ) {g : ℕ} (u : HolUnif x.P.A x.P.L g)
    (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y.t.G.left)) (he : ∀ t, e t = (u.ex t).left ≫ φ) (i : Fin x.P.g) (j : Fin M.n)
    (hij : (i : ℕ) = j) (wv : Fin g → ℂ) (hd : u.IsDiff wv (x.v i)) (V : Y.t.G.left.Opens)
    (hV : ⊤ ≤ (spMap (dualMap (ev z M.U hz)) ≫ M.v₀ j) ⁻¹ᵁ V) (f : Γ(Y.t.G.left, V)) :
    (valR (spMap (dualMap (ev z M.U hz)) ≫ M.v₀ j) V f).snd = fderiv ℂ (fun t => valAt' (e t) V f) 0 wv := by
  obtain ⟨-, -, hg', -, -, -, -, hv⟩ := hK
  have e1 : (x.v i).left ≫ φ = spMap (dualMap (ev z M.U hz)) ≫ M.v₀ j := by
    rw [hv i]
    congr 2
    exact Fin.ext hij
  rw [← e1] at hV ⊢
  have hU : ⊤ ≤ (x.v i).left ⁻¹ᵁ (φ ⁻¹ᵁ V) := hV
  have hd' := hd (φ ⁻¹ᵁ V) hU ((φ.app V).hom f)
  have e2 : (fun t => valAt' (e t) V f) = fun t => valAt' (u.ex t).left (φ ⁻¹ᵁ V) ((φ.app V).hom f) :=
    funext fun t => by rw [he, GlobalTheory.HolHom.valAt'_eq_valR, GlobalTheory.HolHom.valAt'_eq_valR, GlobalTheory.HolHom.valR_comp]
  rw [e2, ← hd', GlobalTheory.HolHom.valR_comp, GlobalTheory.HolHom.valR_eq _ _ hU]
  rfl

end Point

open AlgebraicGeometry CategoryTheory Limits in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c σ _ _ V Y a χ W g ty Fu Ha M hM e v z hn v' A _ _ _ hχ _ hez hvb hdet hv' hA`. Set `Ω : Type` to `{q : ℂ × (Sp ℂ ⟶ Xo.XF c) × ((Fin g → ℂ) → (Sp ℂ ⟶ Y.oF.t.G.left)) × (Fin g → Fin g → ℂ) // q.2.1 ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw q.1) ∧ q.2.1 ≫ pullback.snd _ _ = spMap σ ∧ (∀ t, q.2.2.1 t ≫ Y.m0.toSABMap.φ = (Fu.ex Ha.i (Ha.Pw q.1) t).left ∧ q.2.2.1 t ≫ Y.oF.t.G.hom ≫ pul …`. Set `pw : Ω → ℂ` to `fun ω => ω.1.1`. Set `ψ : Ω → (Γ(Y.X, M.U) →+* ℂ)` to `fun ω => ev (ω.1.2.1 ≫ Y.j) M.U ω.2.2.2.2.1`. Establish `hcart` using `W.m.cart`.

Establish `tanv : ∀ k, IsTangent (v k)` using `hvb.1`. It suffices to establish `hs : ∀ i k, Cv pw (HahnSeries.ofPowerSeries ℤ ℂ (A i k)) (fun ω => ω.1.2.2.2 i k) by`. Take `⟨T, hT⟩` from `high_iff.1 (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun k => hs i k)`. Use `⟨T, fun w hw yF h1 h2 hz x φ hK hg u Wv hF hD i => ?_⟩` and prove the remaining obligations. Use `choose xF hxF using hF`.

Establish `hu : IsUnit (Matrix.of z).det` using `isUnit_iff_ne_zero.2 hdet`. Set `Gw : Fin g → Fin g → ℂ` to `fun i' => Matrix.vecMul (Wv (Fin.cast hg.symm i')) (Matrix.of z)⁻¹`. Establish `hGw : ∀ i' j, Wv (Fin.cast hg.symm i') j = ∑ k, Gw i' k * z k j` using `fun i' j => by`. Establish `e0 : Matrix.vecMul (Gw i') (Matrix.of z) = Wv (Fin.cast hg.symm i')`. Simplify using `only [Gw]`.

Rewrite using `[Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]`. Rewrite using `[← e0]`. Simplify using `[Matrix.vecMul, dotProduct]`. Establish `hω : ∀ (hz' : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (i' : Fin g) (Vo : Y.t.G.left.Opens) (f : Γ(Y.t.G.left, Vo)), ⊤ ≤ (spMap (dualMap (ev (yF ≫ Y.j) M.U hz')) ≫ M.v₀ (Fin.cast hn.symm i')) ⁻¹ᵁ Vo → (valR (spMap (dualMap (ev (yF ≫ Y.j) M.U hz')) ≫ M.v₀ (Fin.cast hn.symm i')) Vo f).snd = ∑ k, Gw …`. Introduce `hz' i' Vo f hV`.

Rewrite using `[point_snd M hK u (fun t => xF t ≫ Y.m.φ) (fun t => (hxF t).2.2.symm) (Fin.cast hg.symm i') (Fin.cast hn.symm i')`. Use `rfl _ (hD _) Vo hV f]`. Establish `e3 : Wv (Fin.cast hg.symm i') = ∑ k, Gw i' k • z k` using `funext fun j => by`. Rewrite using `[hGw i' j, Finset.sum_apply]`. Simplify using the standard rewrite rules.

Rewrite using `[e3, map_sum]`. Simplify using `[smul_eq_mul]`. Establish `hT'` using `hT ⟨(w, yF, xF, Gw), h1, h2, fun t => ⟨(hxF t).1, (hxF t).2.1⟩, hz, hω⟩ hw i`. Establish `hS : ∀ k, SumsAt (A i k) w (Gw i k)` using `fun k => GlobalTheory.Conv.sumsAt_iff.2 (hT' k)`. Use `⟨fun k => HasSum.summable (hS k), fun j => ?_⟩` and prove the remaining obligations.

Rewrite using `[hGw i j]`. Conclude with `Finset.sum_congr rfl fun k _ => by rw [HasSum.tsum_eq (hS k)]`. Introduce `i`. Take `⟨Vo, hVo, hpV, -⟩` from `exists_isAffineOpen_mem_and_subset (X := Y.t.G.left) (U := ⊤) (x := (show Sp (PowerSeries ℂ) ⟶ Y.t.G.left from (η[W.t.G]).left ≫ W.m.φ) (IsLocalRing.closedPoint (PowerSeries ℂ)))`. Discharge the goal by the elementary cases of `trivial`.

Establish `hVη : ⊤ ≤ ((η[W.t.G]).left ≫ W.m.φ) ⁻¹ᵁ Vo` using `(Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of (PowerSeries ℂ)) _ hpV).ge`. Establish `hvV : ∀ k, ⊤ ≤ ((v k).left ≫ W.m.φ) ⁻¹ᵁ Vo` using `fun k => tan_le hcart _ (tanv k) Vo hVη`. Establish `hv'V : ⊤ ≤ ((v' i).left ≫ W.m.φ) ⁻¹ᵁ Vo` using `tan_le hcart _ (comb_tan v tanv _ _ (hA i)) Vo hVη`. Set `φL : Γ(Y.X, M.U) →+* ℂ⸨X⸩` to `(HahnSeries.ofPowerSeries ℤ ℂ).comp (ev χ M.U hM)`. Establish `eχ : spMap (dualMap φL) ≫ M.v₀ (Fin.cast hn.symm i) = spMap (dualMap (HahnSeries.ofPowerSeries ℤ ℂ)) ≫ (v' i).left ≫ W.m.φ`.

Rewrite using `[hv' i, dualMap_comp, ← spMap_comp', Category.assoc]`. Establish `hc : ∀ r, Cv pw (φL r) (fun ω => ψ ω r)`. Introduce `r`. Take `⟨T', hT'⟩` from `Ha.point M.U r hM`. Use `high_iff.2 ⟨T', fun ω hω => ?_⟩` and prove the remaining obligations.

Take `⟨-, hs⟩` from `hT' _ hω ω.1.2.1 ω.2.1 ω.2.2.1`. Establish `h3` using `GlobalTheory.Conv.sumsAt_iff.1 hs`. Establish `e4 : valR χ M.U r = ev χ M.U hM r` using `valR_eq_ev' χ M.U hM r`. Establish `e5 : valAt' (ω.1.2.1 ≫ Y.j) M.U r = ψ ω r` using `valR_eq_ev' (ω.1.2.1 ≫ Y.j) M.U ω.2.2.2.2.1 r`. Rewrite `h3` using `[e4, e5]`.

Conclude with `h3`. Establish `hch` using `fun f => cv_chart (M.v₀ (Fin.cast hn.symm i)) Vo f φL ψ hc (by rw [eχ]; exact le_preimage_comp _ hv'V)`. Use `cv_coeff (F := Γ(Y.t.G.left, Vo)) (m := g) (A := fun f k => HahnSeries.ofPowerSeries ℤ ℂ (valR ((v k).left ≫ W.m.φ) Vo f).snd) (B := fun f => HahnSeries.ofPowerSeries ℤ ℂ (valR ((v' i).left ≫ W.m.φ) Vo f).snd) (Aw := fun f k ω => fderiv ℂ (fun t => valAt' (ω.1.2.2.1 t ≫ Y.m.φ) Vo …` and prove the remaining obligations. Rewrite using `[comb_snd hcart v tanv (A i) (v' i) (hA i) Vo hVη f, map_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => map_mul _ _ _`.

Take `⟨T', hT'⟩` from `Ha.diff (z k) (e k) (v k) Vo f (hez k).2.1 (hez k).2.2 (fun n ρ κ vn h1 h2 h3 h4 h5 => (hez k).1 n ρ κ vn h1 h2 h3 h4 (thick_base _ n (v k) ρ vn h1 h5) h5) (hvV k)`. Conclude with `high_iff.2 ⟨T', fun ω hω => GlobalTheory.Conv.sumsAt_iff.1 (hT' _ hω _ ω.2.2.2.1)⟩`. Establish `h1` using `(hch f).2`. Rewrite `h1` using `[eχ, GlobalTheory.HolHom.valR_spMap _ _ _ hv'V]`. Simplify `h1` using `[dualMap]`.

Use `filter_upwards [(hch f).1] with ω hω`. Conclude with `ω.2.2.2.2.2 ω.2.2.2.2.1 i Vo f hω`.
-/
theorem lie_coords_hasSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (M : GChart Y) (hM : ⊤ ≤ χ ⁻¹ᵁ M.U) (e : Fin g → Out.GtPt a.D₀ (epsR ℂ)) (v : Fin g → (epsR (PowerSeries ℂ) ⟶ W.t.G)) (z : Fin g → Fin g → ℂ) (hn : M.n = g) (v' : Fin g → (epsR (PowerSeries ℂ) ⟶ W.t.G)) (A : Matrix (Fin g) (Fin g) (PowerSeries ℂ)), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → (∀ k, GlobalTheory.ArcQ.LieImg W (e k) (v k) ∧ GlobalTheory.ArcQ.AnVec Ha (e k) (z k)) → IsLieBasis v → (Matrix.of z).det ≠ 0 → (∀ i, (v' i).left ≫ W.m.φ = spMap (dualMap (ev χ M.U hM)) ≫ M.v₀ (Fin.cast hn.symm i)) → (∀ i, IsLieComb (A i) v (v' i)) → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∀ (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (Wv : Fin x.P.g → Fin g → ℂ), GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u → (∀ i, u.IsDiff (Wv i) (x.v i)) → ∀ i, (∀ k, Summable (fun m : ℕ => PowerSeries.coeff m (A i k) * eTwoPi w ^ m)) ∧ ∀ j, Wv (Fin.cast hg.symm i) j = ∑ k, (∑' m : ℕ, PowerSeries.coeff m (A i k) * eTwoPi w ^ m) * z k j := by
  intro E _ _ _ H Dw l Xo c σ _ _ V Y a χ W g ty Fu Ha M hM e v z hn v' A _ _ _ hχ _ hez hvb hdet hv' hA
  let Ω : Type := {q : ℂ × (Sp ℂ ⟶ Xo.XF c) × ((Fin g → ℂ) → (Sp ℂ ⟶ Y.oF.t.G.left)) × (Fin g → Fin g → ℂ) //
    q.2.1 ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw q.1) ∧ q.2.1 ≫ pullback.snd _ _ = spMap σ ∧
    (∀ t, q.2.2.1 t ≫ Y.m0.toSABMap.φ = (Fu.ex Ha.i (Ha.Pw q.1) t).left ∧
      q.2.2.1 t ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap σ) ∧
    ⊤ ≤ (q.2.1 ≫ Y.j) ⁻¹ᵁ M.U ∧ ∀ (hz : ⊤ ≤ (q.2.1 ≫ Y.j) ⁻¹ᵁ M.U) (i : Fin g) (Vo : Y.t.G.left.Opens)
      (f : Γ(Y.t.G.left, Vo)), ⊤ ≤ (spMap (dualMap (ev (q.2.1 ≫ Y.j) M.U hz)) ≫ M.v₀ (Fin.cast hn.symm i)) ⁻¹ᵁ Vo →
      (valR (spMap (dualMap (ev (q.2.1 ≫ Y.j) M.U hz)) ≫ M.v₀ (Fin.cast hn.symm i)) Vo f).snd =
        ∑ k, q.2.2.2 i k * fderiv ℂ (fun t => valAt' (q.2.2.1 t ≫ Y.m.φ) Vo f) 0 (z k)}
  let pw : Ω → ℂ := fun ω => ω.1.1
  let ψ : Ω → (Γ(Y.X, M.U) →+* ℂ) := fun ω => ev (ω.1.2.1 ≫ Y.j) M.U ω.2.2.2.2.1
  have hcart := W.m.cart
  have tanv : ∀ k, IsTangent (v k) := hvb.1
  suffices hs : ∀ i k, Cv pw (HahnSeries.ofPowerSeries ℤ ℂ (A i k)) (fun ω => ω.1.2.2.2 i k) by
    obtain ⟨T, hT⟩ := high_iff.1 (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun k => hs i k)
    refine ⟨T, fun w hw yF h1 h2 hz x φ hK hg u Wv hF hD i => ?_⟩
    choose xF hxF using hF
    have hu : IsUnit (Matrix.of z).det := isUnit_iff_ne_zero.2 hdet
    let Gw : Fin g → Fin g → ℂ := fun i' => Matrix.vecMul (Wv (Fin.cast hg.symm i')) (Matrix.of z)⁻¹
    have hGw : ∀ i' j, Wv (Fin.cast hg.symm i') j = ∑ k, Gw i' k * z k j := fun i' j => by
      have e0 : Matrix.vecMul (Gw i') (Matrix.of z) = Wv (Fin.cast hg.symm i') := by
        simp only [Gw]
        rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
      rw [← e0]
      simp [Matrix.vecMul, dotProduct]
    have hω : ∀ (hz' : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (i' : Fin g) (Vo : Y.t.G.left.Opens) (f : Γ(Y.t.G.left, Vo)),
        ⊤ ≤ (spMap (dualMap (ev (yF ≫ Y.j) M.U hz')) ≫ M.v₀ (Fin.cast hn.symm i')) ⁻¹ᵁ Vo →
        (valR (spMap (dualMap (ev (yF ≫ Y.j) M.U hz')) ≫ M.v₀ (Fin.cast hn.symm i')) Vo f).snd =
          ∑ k, Gw i' k * fderiv ℂ (fun t => valAt' (xF t ≫ Y.m.φ) Vo f) 0 (z k) := by
      intro hz' i' Vo f hV
      rw [point_snd M hK u (fun t => xF t ≫ Y.m.φ) (fun t => (hxF t).2.2.symm) (Fin.cast hg.symm i') (Fin.cast hn.symm i')
        rfl _ (hD _) Vo hV f]
      have e3 : Wv (Fin.cast hg.symm i') = ∑ k, Gw i' k • z k := funext fun j => by
        rw [hGw i' j, Finset.sum_apply]
        simp
      rw [e3, map_sum]
      simp [smul_eq_mul]
    have hT' := hT ⟨(w, yF, xF, Gw), h1, h2, fun t => ⟨(hxF t).1, (hxF t).2.1⟩, hz, hω⟩ hw i
    have hS : ∀ k, SumsAt (A i k) w (Gw i k) := fun k => GlobalTheory.Conv.sumsAt_iff.2 (hT' k)
    refine ⟨fun k => HasSum.summable (hS k), fun j => ?_⟩
    rw [hGw i j]
    exact Finset.sum_congr rfl fun k _ => by rw [HasSum.tsum_eq (hS k)]
  intro i
  obtain ⟨Vo, hVo, hpV, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y.t.G.left) (U := ⊤)
    (x := (show Sp (PowerSeries ℂ) ⟶ Y.t.G.left from (η[W.t.G]).left ≫ W.m.φ) (IsLocalRing.closedPoint (PowerSeries ℂ)))
    trivial
  have hVη : ⊤ ≤ ((η[W.t.G]).left ≫ W.m.φ) ⁻¹ᵁ Vo :=
    (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of (PowerSeries ℂ)) _ hpV).ge
  have hvV : ∀ k, ⊤ ≤ ((v k).left ≫ W.m.φ) ⁻¹ᵁ Vo := fun k => tan_le hcart _ (tanv k) Vo hVη
  have hv'V : ⊤ ≤ ((v' i).left ≫ W.m.φ) ⁻¹ᵁ Vo := tan_le hcart _ (comb_tan v tanv _ _ (hA i)) Vo hVη
  let φL : Γ(Y.X, M.U) →+* ℂ⸨X⸩ := (HahnSeries.ofPowerSeries ℤ ℂ).comp (ev χ M.U hM)
  have eχ : spMap (dualMap φL) ≫ M.v₀ (Fin.cast hn.symm i) =
      spMap (dualMap (HahnSeries.ofPowerSeries ℤ ℂ)) ≫ (v' i).left ≫ W.m.φ := by
    rw [hv' i, dualMap_comp, ← spMap_comp', Category.assoc]
  have hc : ∀ r, Cv pw (φL r) (fun ω => ψ ω r) := by
    intro r
    obtain ⟨T', hT'⟩ := Ha.point M.U r hM
    refine high_iff.2 ⟨T', fun ω hω => ?_⟩
    obtain ⟨-, hs⟩ := hT' _ hω ω.1.2.1 ω.2.1 ω.2.2.1
    have h3 := GlobalTheory.Conv.sumsAt_iff.1 hs
    have e4 : valR χ M.U r = ev χ M.U hM r := valR_eq_ev' χ M.U hM r
    have e5 : valAt' (ω.1.2.1 ≫ Y.j) M.U r = ψ ω r := valR_eq_ev' (ω.1.2.1 ≫ Y.j) M.U ω.2.2.2.2.1 r
    rw [e4, e5] at h3
    exact h3
  have hch := fun f => cv_chart (M.v₀ (Fin.cast hn.symm i)) Vo f φL ψ hc (by rw [eχ]; exact le_preimage_comp _ hv'V)
  refine cv_coeff (F := Γ(Y.t.G.left, Vo)) (m := g)
    (A := fun f k => HahnSeries.ofPowerSeries ℤ ℂ (valR ((v k).left ≫ W.m.φ) Vo f).snd)
    (B := fun f => HahnSeries.ofPowerSeries ℤ ℂ (valR ((v' i).left ≫ W.m.φ) Vo f).snd)
    (Aw := fun f k ω => fderiv ℂ (fun t => valAt' (ω.1.2.2.1 t ≫ Y.m.φ) Vo f) 0 (z k))
    (Bw := fun f ω => (valR (spMap (dualMap (ψ ω)) ≫ M.v₀ (Fin.cast hn.symm i)) Vo f).snd)
    (Gw := fun k ω => ω.1.2.2.2 i k)
    (fun f => ?_) (sep_laurent hcart v hvb hVo hVη) (fun f k => ?_) (fun f => ?_) (fun f => ?_)
  · rw [comb_snd hcart v tanv (A i) (v' i) (hA i) Vo hVη f, map_sum]
    exact Finset.sum_congr rfl fun k _ => map_mul _ _ _
  · obtain ⟨T', hT'⟩ := Ha.diff (z k) (e k) (v k) Vo f (hez k).2.1 (hez k).2.2
      (fun n ρ κ vn h1 h2 h3 h4 h5 => (hez k).1 n ρ κ vn h1 h2 h3 h4 (thick_base _ n (v k) ρ vn h1 h5) h5) (hvV k)
    exact high_iff.2 ⟨T', fun ω hω => GlobalTheory.Conv.sumsAt_iff.1 (hT' _ hω _ ω.2.2.2.1)⟩
  · have h1 := (hch f).2
    rw [eχ, GlobalTheory.HolHom.valR_spMap _ _ _ hv'V] at h1
    simpa [dualMap] using h1
  · filter_upwards [(hch f).1] with ω hω
    exact ω.2.2.2.2.2 ω.2.2.2.2.1 i Vo f hω

end GlobalTheory.ArcLieCoord
