import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ChartCoverFOfSecBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeComposeInvertBaseChangeTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.FrameEval

namespace GlobalTheory.FlagTan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Local

variable {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]

/- English proof (translation)
The claim follows from `GlobalTheory.T.exists_framedPoint_baseChange_algebraMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c S T φ y`.
-/
theorem exists_frMap (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) : ∃ z, FrMap φ y z :=
  GlobalTheory.T.exists_framedPoint_baseChange_algebraMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c S T φ y

/- English proof (translation)
The claim follows from `(frMap_unique_refl_iff E H Dw l Xo c S T φ y).1 z z' h h'`.
-/
theorem frMap_unique {φ : S →ₐ[c.F] T} {y : FrPt Xo c S} {z z' : FrPt Xo c T} (h : FrMap φ y z) (h' : FrMap φ y z') :
    z = z' := (frMap_unique_refl_iff E H Dw l Xo c S T φ y).1 z z' h h'

/- English proof (translation)
The claim follows from `(frMap_unique_refl_iff E H Dw l Xo c S S (AlgHom.id c.F S) y).2.1`.
-/
theorem frMap_id (y : FrPt Xo c S) : FrMap (AlgHom.id c.F S) y y :=
  (frMap_unique_refl_iff E H Dw l Xo c S S (AlgHom.id c.F S) y).2.1

/- English proof (translation)
Take `rfl : ψ.comp φ = χ` from `AlgHom.ext e`. Conclude with `frMap_trans (Xo := Xo) (c := c) _ _ _ φ ψ y z w h h'`.
-/
theorem frMap_comp {U : Type} [CommRing U] [Algebra c.F U] {φ : S →ₐ[c.F] T} {ψ : T →ₐ[c.F] U} {χ : S →ₐ[c.F] U}
    {y : FrPt Xo c S} {z : FrPt Xo c T} {w : FrPt Xo c U} (h : FrMap φ y z) (h' : FrMap ψ z w)
    (e : ∀ a, ψ (φ a) = χ a) : FrMap χ y w := by
  obtain rfl : ψ.comp φ = χ := AlgHom.ext e
  exact frMap_trans (Xo := Xo) (c := c) _ _ _ φ ψ y z w h h'

/- English proof (translation)
Take `⟨w', hw⟩` from `exists_frMap ψ z`. Rewrite using `[frMap_unique h' (frMap_comp h hw e)]` and apply the resulting hypothesis.
-/
theorem frMap_of_comp {U : Type} [CommRing U] [Algebra c.F U] {φ : S →ₐ[c.F] T} {ψ : T →ₐ[c.F] U}
    {χ : S →ₐ[c.F] U} {y : FrPt Xo c S} {z : FrPt Xo c T} {w : FrPt Xo c U} (h : FrMap φ y z) (h' : FrMap χ y w)
    (e : ∀ a, ψ (φ a) = χ a) : FrMap ψ z w := by
  obtain ⟨w', hw⟩ := exists_frMap ψ z
  rwa [frMap_unique h' (frMap_comp h hw e)]

/- English proof (translation)
The claim follows from `(frChg_calculus E H Dw l Xo c S).2.2.1 T φ g a y y' z z' h hz`.
-/
theorem frMap_iff_frChg {φ : S →ₐ[c.F] T} {g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S} {a : S}
    {y y' : FrPt Xo c S} {z z' : FrPt Xo c T} (h : FrChg g a y y') (hz : FrMap φ y z) :
    FrMap φ y' z' ↔ FrChg (fun τ => (g τ).map φ) (φ a) z z' :=
  (frChg_calculus E H Dw l Xo c S).2.2.1 T φ g a y y' z z' h hz

/- English proof (translation)
Establish `hS : Out.SecBaseChangeSt` using `GlobalTheory.lawsFieldsSeparately.2.1`. Take `⟨xF, h1, h2⟩` from `ChartCover.exists_lift w`. Take `⟨p, j, y₀, hj, hp⟩` from `GlobalTheory.T.exists_openChart_framedPoint_testRing hS E H Dw l Xo c (xF (IsLocalRing.closedPoint S))`. Take `⟨A, π, X, s, u, hu⟩` from `GlobalTheory.T.exists_universalFrame_testRing hS E H Dw l Xo c p y₀`. Establish `key : ∀ z : FrPt Xo c S, z.x = w.x → ∃ a : A.R →ₐ[c.F] S, FrMap a u z` using `fun z hz => by`.

Take `⟨g, hg, hT⟩` from `ChartCover.near hS hj hu z xF (h1.trans hz.symm) h2 _ hp`. Take `⟨z', a, h, ha⟩` from `hT S (AlgHom.id _ _) (IsLocalRing.notMem_maximalIdeal.1 hg)`. Conclude with `⟨a, frMap_unique h (frMap_id z) ▸ ha⟩`. Take `⟨a, ha⟩` from `key w rfl`. Take `⟨a', ha'⟩` from `key w' hw`.

Conclude with `⟨p, A, j, y₀, π, X, s, u, a, a', hj, hu, ha, ha'⟩`.
-/
theorem exists_chart [IsLocalRing S] (w w' : FrPt Xo c S) (hw : w'.x = w.x) :
    ∃ (p A : TRing c.F) (j : Sp p.R ⟶ Xo.XF c) (y₀ : FrPt Xo c p.R) (π : p.R →ₐ[c.F] A.R)
      (X : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A.R) (s : (A.R)ˣ) (u : FrPt Xo c A.R)
      (a a' : A.R →ₐ[c.F] S), OpenChart j y₀ ∧ UnivFrame y₀ π X s u ∧ FrMap a u w ∧ FrMap a' u w' := by
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨xF, h1, h2⟩ := ChartCover.exists_lift w
  obtain ⟨p, j, y₀, hj, hp⟩ := GlobalTheory.T.exists_openChart_framedPoint_testRing hS E H Dw l Xo c (xF (IsLocalRing.closedPoint S))
  obtain ⟨A, π, X, s, u, hu⟩ := GlobalTheory.T.exists_universalFrame_testRing hS E H Dw l Xo c p y₀
  have key : ∀ z : FrPt Xo c S, z.x = w.x → ∃ a : A.R →ₐ[c.F] S, FrMap a u z := fun z hz => by
    obtain ⟨g, hg, hT⟩ := ChartCover.near hS hj hu z xF (h1.trans hz.symm) h2 _ hp
    obtain ⟨z', a, h, ha⟩ := hT S (AlgHom.id _ _) (IsLocalRing.notMem_maximalIdeal.1 hg)
    exact ⟨a, frMap_unique h (frMap_id z) ▸ ha⟩
  obtain ⟨a, ha⟩ := key w rfl
  obtain ⟨a', ha'⟩ := key w' hw
  exact ⟨p, A, j, y₀, π, X, s, u, a, a', hj, hu, ha, ha'⟩

/- English proof (translation)
Take `⟨-, A, -, -, -, -, -, u, a, -, -, -, ha, -⟩` from `exists_chart w w rfl`. Conclude with `⟨A, a, u, ha⟩`.
-/
theorem fromTest_of_isLocalRing [IsLocalRing S] (w : FrPt Xo c S) :
    FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w := by
  obtain ⟨-, A, -, -, -, -, -, u, a, -, -, -, ha, -⟩ := exists_chart w w rfl
  exact ⟨A, a, u, ha⟩

/- English proof (translation)
Establish `hT : FromTest (K` using `c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w := ⟨p, φ, u, h⟩`. Unfold `evR evalAt`. Rewrite using `[dif_pos hT]`. Conclude with `evalWD_fr (frChartF_of (chartCoverF_of_secBaseChange GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c)) f hf S _ _ _ _ _ _ w hT.choose_spec.choose_spec.choose_spec h`.
-/
theorem evR_eq {f : Rul Xo c}
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f) {p : TRing c.F}
    {φ : p.R →ₐ[c.F] S} {u : FrPt Xo c p.R} {w : FrPt Xo c S} (h : FrMap φ u w) : evR Xo c f w = φ (f p u) := by
  have hT : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w := ⟨p, φ, u, h⟩
  unfold evR evalAt
  rw [dif_pos hT]
  exact evalWD_fr (frChartF_of (chartCoverF_of_secBaseChange GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c)) f hf S
    _ _ _ _ _ _ w hT.choose_spec.choose_spec.choose_spec h

/- English proof (translation)
Take `⟨p, a, u, hu⟩` from `fromTest_of_isLocalRing y`. Rewrite using `[evR_eq hf hu, evR_eq hf (frMap_comp (χ := φ.comp a) hu h fun _ => rfl)]`. Both sides reduce to the same expression.
-/
theorem evR_frMap [IsLocalRing S] {f : Rul Xo c}
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f) {φ : S →ₐ[c.F] T}
    {y : FrPt Xo c S} {z : FrPt Xo c T} (h : FrMap φ y z) : evR Xo c f z = φ (evR Xo c f y) := by
  obtain ⟨p, a, u, hu⟩ := fromTest_of_isLocalRing y
  rw [evR_eq hf hu, evR_eq hf (frMap_comp (χ := φ.comp a) hu h fun _ => rfl)]
  rfl

/- English proof (translation)
Take `⟨p, A, j, y₀, π, X, s, u, a, a', hj, hu, ha, ha'⟩` from `exists_chart y y' h.1`. Take `⟨B, uB, uB', tB, q, q', hq, hq', hB, hU⟩` from `univFrame_borelPairs GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c p A j y₀ π X s u hj hu`. Take `⟨b, e1, e2, e3⟩` from `hU S a a' y y' t ha ha' h`. Establish `k : FrMap b uB y` using `frMap_of_comp hq ha fun x => DFunLike.congr_fun e1 x`. Establish `k' : FrMap b uB' y'` using `frMap_of_comp hq' ha' fun x => DFunLike.congr_fun e2 x`.

Establish `ht : t = fun i => Units.map (b : B.R →* S) (tB i)` using `funext fun i => Units.ext (e3 i).symm`. Rewrite using `[evR_eq hf.1 k, evR_eq hf.1 k', hf.2 B tB uB uB' hB, map_mul, ht]`. Use `congr 1`. Simplify using `only [← map_zpow, ← map_prod]`. Both sides reduce to the same expression.
-/
theorem evR_frBor [IsLocalRing S] {e : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ secZ Xo c e) {t : Ix Dw → Sˣ}
    {y y' : FrPt Xo c S} (h : FrBor t y y') :
    evR Xo c f y' = ((∏ i, t i ^ e i : Sˣ) : S) * evR Xo c f y := by
  obtain ⟨p, A, j, y₀, π, X, s, u, a, a', hj, hu, ha, ha'⟩ := exists_chart y y' h.1
  obtain ⟨B, uB, uB', tB, q, q', hq, hq', hB, hU⟩ :=
    univFrame_borelPairs GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c p A j y₀ π X s u hj hu
  obtain ⟨b, e1, e2, e3⟩ := hU S a a' y y' t ha ha' h
  have k : FrMap b uB y := frMap_of_comp hq ha fun x => DFunLike.congr_fun e1 x
  have k' : FrMap b uB' y' := frMap_of_comp hq' ha' fun x => DFunLike.congr_fun e2 x
  have ht : t = fun i => Units.map (b : B.R →* S) (tB i) := funext fun i => Units.ext (e3 i).symm
  rw [evR_eq hf.1 k, evR_eq hf.1 k', hf.2 B tB uB uB' hB, map_mul, ht]
  congr 1
  simp only [← map_zpow, ← map_prod]
  rfl

/- English proof (translation)
Establish `hS : Out.SecBaseChangeSt` using `GlobalTheory.lawsFieldsSeparately.2.1`. Choose the witnesses or unpack the hypotheses as in `⟨xF, h1, h2⟩ : ∃ xF : Sp S ⟶ Xo.XF c, xF ≫ pullback.fst _ _ = x ∧ xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := by`. Use `⟨pullback.lift x (spMap (algebraMap c.F S)) ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩` and prove the remaining obligations. Rewrite using `[hx, sOf, ← Spec.map_comp]`. Both sides reduce to the same expression.

Take `⟨p, j, y₀, hj, hp⟩` from `GlobalTheory.T.exists_openChart_framedPoint_testRing hS E H Dw l Xo c (xF (IsLocalRing.closedPoint S))`. Take `⟨g, hg, hT⟩` from `openChart_factor_near_prime E H Dw l Xo c _ j y₀ hj S xF h2 _ hp`. Take `⟨ψ, hψ⟩` from `hT S (AlgHom.id _ _) (IsLocalRing.notMem_maximalIdeal.1 hg)`. Take `⟨z, hz⟩` from `exists_frMap ψ y₀`. Use `⟨z, ?_⟩` and prove the remaining obligations.

Establish `hid : spMap (AlgHom.id c.F S).toRingHom = 𝟙 _` using `Spec.map_id _`. Rewrite using `[hz.1, ← hj.2.1, ← Category.assoc, ← hψ, hid, Category.id_comp, h1]`.
-/
theorem exists_frPt [IsLocalRing S] (x : Sp S ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c S) : ∃ z : FrPt Xo c S, z.x = x := by
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨xF, h1, h2⟩ : ∃ xF : Sp S ⟶ Xo.XF c, xF ≫ pullback.fst _ _ = x ∧
      xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := by
    refine ⟨pullback.lift x (spMap (algebraMap c.F S)) ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    rw [hx, sOf, ← Spec.map_comp]; rfl
  obtain ⟨p, j, y₀, hj, hp⟩ := GlobalTheory.T.exists_openChart_framedPoint_testRing hS E H Dw l Xo c (xF (IsLocalRing.closedPoint S))
  obtain ⟨g, hg, hT⟩ := openChart_factor_near_prime E H Dw l Xo c _ j y₀ hj S xF h2 _ hp
  obtain ⟨ψ, hψ⟩ := hT S (AlgHom.id _ _) (IsLocalRing.notMem_maximalIdeal.1 hg)
  obtain ⟨z, hz⟩ := exists_frMap ψ y₀
  refine ⟨z, ?_⟩
  have hid : spMap (AlgHom.id c.F S).toRingHom = 𝟙 _ := Spec.map_id _
  rw [hz.1, ← hj.2.1, ← Category.assoc, ← hψ, hid, Category.id_comp, h1]

end Local

section Coef

variable (Xo c) (K₀ : Type) [CommRing K₀] [Algebra c.F K₀]

abbrev RulK : Type := K₀ ⊗[c.F] Rul Xo c

def secK (e : Ix Dw → ℤ) : Submodule K₀ (RulK Xo c K₀) := (secZ Xo c e).baseChange K₀

variable {Xo c K₀} {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]

def val (φ : K₀ →ₐ[c.F] S) (y : FrPt Xo c S) : RulK Xo c K₀ →ₗ[c.F] S :=
  TensorProduct.lift ((LinearMap.mul c.F S).compl₁₂ φ.toLinearMap
    (evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y))

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem val_tmul (φ : K₀ →ₐ[c.F] S) (y : FrPt Xo c S) (a : K₀) (f : Rul Xo c) :
    val φ y (a ⊗ₜ f) = φ a * evR Xo c f y := rfl

/- English proof (translation)
Proceed by induction on `s using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add s s' h h' => rw [smul_add, map_add, map_add, h, h', mul_add]`. Consider the case `tmul b f => rw [TensorProduct.smul_tmul', val_tmul, val_tmul, smul_eq_mul, map_mul, mul_assoc]`.
-/
theorem val_smul (φ : K₀ →ₐ[c.F] S) (y : FrPt Xo c S) (a : K₀) (s : RulK Xo c K₀) :
    val φ y (a • s) = φ a * val φ y s := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | add s s' h h' => rw [smul_add, map_add, map_add, h, h', mul_add]
  | tmul b f => rw [TensorProduct.smul_tmul', val_tmul, val_tmul, smul_eq_mul, map_mul, mul_assoc]

/- English proof (translation)
The claim follows from `Submodule.tmul_mem_baseChange_of_mem a hf`.
-/
theorem tmul_mem_secK {e : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ secZ Xo c e) (a : K₀) : a ⊗ₜ f ∈ secK Xo c K₀ e :=
  Submodule.tmul_mem_baseChange_of_mem a hf

/- English proof (translation)
Take `⟨z, rfl⟩ : ∃ z, (secZ Xo c e).subtype.baseChange K₀ z = s` from `hs`. Proceed by induction on `z with`. Consider the case `zero => simpa using h0`. Consider the case `add s s' h h' => rw [map_add]`. Conclude with `h2 _ _ h h'`.

Consider the case `tmul a f => exact h1 a f.1 f.2`.
-/
theorem secK_induction {e : Ix Dw → ℤ} {P : RulK Xo c K₀ → Prop} (h0 : P 0)
    (h1 : ∀ a f, f ∈ secZ Xo c e → P (a ⊗ₜ f)) (h2 : ∀ s s', P s → P s' → P (s + s')) {s : RulK Xo c K₀}
    (hs : s ∈ secK Xo c K₀ e) : P s := by
  obtain ⟨z, rfl⟩ : ∃ z, (secZ Xo c e).subtype.baseChange K₀ z = s := hs
  induction z with
  | zero => simpa using h0
  | add s s' h h' => rw [map_add]; exact h2 _ _ h h'
  | tmul a f => exact h1 a f.1 f.2

/- English proof (translation)
Use `secK_induction (P := fun s => val χ z s = ψ (val φ y s)) (by simp) (fun a f hf => ?_) (fun s s' k k' => ?_) hs` and prove the remaining obligations. Simplify using `only [val_tmul, map_mul, hχ, evR_frMap hf.1 h]`. Simplify using `only [map_add, k, k']`.
-/
theorem val_frMap [IsLocalRing S] {e : Ix Dw → ℤ} {s : RulK Xo c K₀} (hs : s ∈ secK Xo c K₀ e)
    {φ : K₀ →ₐ[c.F] S} {ψ : S →ₐ[c.F] T} {χ : K₀ →ₐ[c.F] T} (hχ : ∀ a, ψ (φ a) = χ a) {y : FrPt Xo c S}
    {z : FrPt Xo c T} (h : FrMap ψ y z) : val χ z s = ψ (val φ y s) := by
  refine secK_induction (P := fun s => val χ z s = ψ (val φ y s)) (by simp) (fun a f hf => ?_)
    (fun s s' k k' => ?_) hs
  · simp only [val_tmul, map_mul, hχ, evR_frMap hf.1 h]
  · simp only [map_add, k, k']

/- English proof (translation)
Use `secK_induction (P := fun s => val φ y' s = ((∏ i, t i ^ e i : Sˣ) : S) * val φ y s) (by simp) (fun a f hf => ?_) (fun s s' k k' => ?_) hs` and prove the remaining obligations. Simplify using `only [val_tmul, evR_frBor hf h]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [map_add, k, k', mul_add]`.
-/
theorem val_frBor [IsLocalRing S] {e : Ix Dw → ℤ} {s : RulK Xo c K₀} (hs : s ∈ secK Xo c K₀ e)
    (φ : K₀ →ₐ[c.F] S) {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S} (h : FrBor t y y') :
    val φ y' s = ((∏ i, t i ^ e i : Sˣ) : S) * val φ y s := by
  refine secK_induction (P := fun s => val φ y' s = ((∏ i, t i ^ e i : Sˣ) : S) * val φ y s) (by simp)
    (fun a f hf => ?_) (fun s s' k k' => ?_) hs
  · simp only [val_tmul, evR_frBor hf h]; ring
  · simp only [map_add, k, k', mul_add]

end Coef

section Thick

open TrivSqZeroExt hiding map lift

variable {K : Type} [Field K]

instance isLocalRing_trivSqZeroExt {M : Type} [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M] :
    IsLocalRing (TrivSqZeroExt K M) :=
  haveI : Nontrivial (TrivSqZeroExt K M) := inl_injective.nontrivial
  .of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [isUnit_iff_isUnit_fst, fst_sub, fst_one]
    exact IsLocalRing.isUnit_or_isUnit_one_sub_self _

variable (Dw) in

abbrev FIx : Type := Option (Σ σ : E →+* ℂ, Fin (Dw.mult σ) × Fin (Dw.mult σ))

section

variable (K) {M : Type} [AddCommGroup M]

def unip (N : FIx Dw → M) (σ : E →+* ℂ) : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) (TrivSqZeroExt K M) :=
  Matrix.of fun i j => inl ((1 : Matrix _ _ K) i j) + inr (N (some ⟨σ, i, j⟩))

def unip₀ (N : FIx Dw → M) : TrivSqZeroExt K M := inl 1 + inr (N none)

variable {K} [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M]

/- English proof (translation)
Establish `e : (fstHom K K M).toRingHom.mapMatrix (unip K N σ) = 1`. Use extensionality with `i j`. Simplify using `[unip]`. Rewrite using `[isUnit_iff_isUnit_fst]`. Use `show IsUnit ((fstHom K K M).toRingHom _)`.

Rewrite using `[RingHom.map_det, e, Matrix.det_one]`. Conclude with `isUnit_one`.
-/
theorem isUnit_det_unip (N : FIx Dw → M) (σ : E →+* ℂ) : IsUnit (unip K N σ).det := by
  have e : (fstHom K K M).toRingHom.mapMatrix (unip K N σ) = 1 := by
    ext i j; simp [unip]
  rw [isUnit_iff_isUnit_fst]
  show IsUnit ((fstHom K K M).toRingHom _)
  rw [RingHom.map_det, e, Matrix.det_one]
  exact isUnit_one

/- English proof (translation)
Simplify using `[isUnit_iff_isUnit_fst, unip₀]`.
-/
theorem isUnit_unip₀ (N : FIx Dw → M) : IsUnit (unip₀ K N) := by
  simp [isUnit_iff_isUnit_fst, unip₀]

end

variable [Algebra c.F K]

variable (c K) in

abbrev red : DualNumber K →ₐ[c.F] K := fstHom c.F K K

variable (c K) in

abbrev cst : K →ₐ[c.F] DualNumber K := inlAlgHom c.F K K

variable (c) in

def dir {ι : Type} [Fintype ι] (m : ι → K) : TrivSqZeroExt K (ι → K) →ₐ[c.F] DualNumber K :=
  (TrivSqZeroExt.map (Fintype.linearCombination K m)).restrictScalars c.F

/- English proof (translation)
The claim follows from `fst_map _ z`.
-/
@[simp] theorem fst_dir {ι : Type} [Fintype ι] (m : ι → K) (z : TrivSqZeroExt K (ι → K)) :
    (dir c m z).fst = z.fst := fst_map _ z

/- English proof (translation)
The claim follows from `(snd_map _ z).trans (Fintype.linearCombination_apply _ _ _)`.
-/
@[simp] theorem snd_dir {ι : Type} [Fintype ι] (m : ι → K) (z : TrivSqZeroExt K (ι → K)) :
    (dir c m z).snd = ∑ k, z.snd k * m k := (snd_map _ z).trans (Fintype.linearCombination_apply _ _ _)

/- English proof (translation)
Take `⟨z, rfl⟩` from `exists_frPt X hX`. Take `⟨z₀, h₀⟩` from `exists_frMap (fstHom c.F K (ι → K)) z`. Take `⟨g, a, hg, hc⟩` from `(frChg_exists_unique E H Dw l Xo c K z₀ y).1 (hy.symm.trans h₀.1.symm)`. Take `⟨W, hW, -⟩` from `existsUnique_frChg E H Dw l Xo c _ z (fun τ => (g τ).map (inlAlgHom c.F K (ι → K))) (Units.map (inlAlgHom c.F K (ι → K)).toRingHom.toMonoidHom a) fun τ => by`. Use `(hg τ).map (inlAlgHom c.F K (ι → K)).toRingHom` as an intermediate fact.

Rewrite `this` using `[RingHom.map_det]`. Then use the resulting hypothesis. Use `⟨W, hW.1, (frMap_iff_frChg hW h₀).2 ?_⟩` and prove the remaining obligations. Use `hc using 2 with τ` and compare the differences between its conclusion and the goal. Use extensionality with `i j`. Simplify using the standard rewrite rules.

Both sides reduce to the same expression.
-/
theorem exists_lift {ι : Type} (y : FrPt Xo c K) (X : Sp (TrivSqZeroExt K (ι → K)) ⟶ Xo.X)
    (hX : X ≫ Xo.s = sOf c _) (hy : spMap (fstHom c.F K (ι → K)).toRingHom ≫ X = y.x) :
    ∃ W : FrPt Xo c (TrivSqZeroExt K (ι → K)), W.x = X ∧ FrMap (fstHom c.F K (ι → K)) W y := by
  obtain ⟨z, rfl⟩ := exists_frPt X hX
  obtain ⟨z₀, h₀⟩ := exists_frMap (fstHom c.F K (ι → K)) z
  obtain ⟨g, a, hg, hc⟩ := (frChg_exists_unique E H Dw l Xo c K z₀ y).1 (hy.symm.trans h₀.1.symm)
  obtain ⟨W, hW, -⟩ := existsUnique_frChg E H Dw l Xo c _ z (fun τ => (g τ).map (inlAlgHom c.F K (ι → K)))
    (Units.map (inlAlgHom c.F K (ι → K)).toRingHom.toMonoidHom a) fun τ => by
      have := (hg τ).map (inlAlgHom c.F K (ι → K)).toRingHom
      rwa [RingHom.map_det] at this
  refine ⟨W, hW.1, (frMap_iff_frChg hW h₀).2 ?_⟩
  convert hc using 2 with τ
  · ext i j; simp
  · rfl

end Thick

end GlobalTheory.FlagTan
