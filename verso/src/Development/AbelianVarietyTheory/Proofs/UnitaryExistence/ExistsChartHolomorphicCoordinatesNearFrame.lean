import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToFibPtAndCompFibre
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsOpenChartFramedPointTestRingStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.HolChart

/- English proof (translation)
Introduce `U f`. Establish `hs : {b ∈ B | ⊤ ≤ a' b ⁻¹ᵁ U} = {b ∈ B | ⊤ ≤ a b ⁻¹ᵁ U}`. Use extensionality with `b`. Conclude with `and_congr_right fun hb => by rw [he b hb]`. Rewrite using `[hs]`.

Conclude with `⟨(h U f).1, (h U f).2.congr fun b hb => by rw [he b hb.1]⟩`.
-/
theorem isHolTo_congr {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {B : Set V} {X : Scheme.{0}}
    {a a' : V → (Sp ℂ ⟶ X)} (h : IsHolTo B a) (he : ∀ b ∈ B, a' b = a b) : IsHolTo B a' := by
  intro U f
  have hs : {b ∈ B | ⊤ ≤ a' b ⁻¹ᵁ U} = {b ∈ B | ⊤ ≤ a b ⁻¹ᵁ U} := by
    ext b
    exact and_congr_right fun hb => by rw [he b hb]
  rw [hs]
  exact ⟨(h U f).1, (h U f).2.congr fun b hb => by rw [he b hb.1]⟩

/- English proof (translation)
Establish `h : ⊤ ≤ (spMap ψ) ⁻¹ᵁ ⊤` using `le_top`. Rewrite using `[valAt', dif_pos h, valAt]`. Establish `e : (spMap ψ).appLE ⊤ ⊤ h = (spMap ψ).appTop` using `(spMap ψ).appLE_eq_app`. Establish `n` using `Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ)`. Establish `n'` using `congrArg (fun φ => φ.hom t) n`.

Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n'`. Rewrite using `[e]`. Use `erw [← n']`. Conclude with `(Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv_hom_id_apply _`.
-/
theorem valAt'_spMap {R : Type} [CommRing R] (ψ : R →+* ℂ) (t : R) :
    valAt' (spMap ψ) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom t) = ψ t := by
  have h : ⊤ ≤ (spMap ψ) ⁻¹ᵁ ⊤ := le_top
  rw [valAt', dif_pos h, valAt]
  have e : (spMap ψ).appLE ⊤ ⊤ h = (spMap ψ).appTop := (spMap ψ).appLE_eq_app
  have n := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ)
  have n' := congrArg (fun φ => φ.hom t) n
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n'
  rw [e]
  erw [← n']
  exact (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv_hom_id_apply _

/- English proof (translation)
Set `U : X.Opens` to `j ''ᵁ ⊤`. Establish `hU : ∀ x : X, x ∈ U ↔ x ∈ Set.range j` using `fun x => by`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, -, rfl⟩`. Conclude with `⟨y, rfl⟩`.

Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨y, trivial, rfl⟩`. Establish `hl : ∀ x : Sp ℂ ⟶ X, ⊤ ≤ x ⁻¹ᵁ U → ∃ ψ : R →+* ℂ, x = spMap ψ ≫ j` using `fun x hx => by`. Establish `hr : Set.range x ⊆ Set.range j`. Introduce and unpack `_ ⟨q, rfl⟩`.

Conclude with `(hU _).1 (hx (Set.mem_univ q))`. Use `⟨(Spec.preimage (IsOpenImmersion.lift j x hr)).hom, ?_⟩` and prove the remaining obligations. Rewrite using `[spMap, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]`. Establish `h₀ : ⊤ ≤ a b₀ ⁻¹ᵁ U` using `(top_le_preimage_iff_mem _ _).2 ((hU _).2 hj)`. Set `ψ : V → (R →+* ℂ)` to `fun b => if hb : ⊤ ≤ a b ⁻¹ᵁ U then (hl _ hb).choose else (hl _ h₀).choose`.

Establish `hψ : ∀ b, ⊤ ≤ a b ⁻¹ᵁ U → a b = spMap (ψ b) ≫ j` using `fun b hb => by`. Simplify using `only [ψ, dif_pos hb]`. Conclude with `(hl _ hb).choose_spec`. Use `⟨{b ∈ B | ⊤ ≤ a b ⁻¹ᵁ U}, ψ, (h U 0).1, ⟨hb₀, h₀⟩, fun b hb => hb.1, fun b hb => hψ b hb.2, fun t => ?_⟩` and prove the remaining obligations. Use `(h U ((j.appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom t))).2.congr fun b hb => ?_` and prove the remaining obligations.

Establish `hle : (⊤ : (Sp R).Opens) ≤ j ⁻¹ᵁ U` using `fun y _ => (hU _).2 ⟨y, rfl⟩`. Establish `hid : (j.appIso ⊤).inv ≫ j.appLE U ⊤ hle = 𝟙 _`. Rewrite using `[Scheme.Hom.appIso_inv_appLE]`. Conclude with `(Sp R).presheaf.map_id _`. Rewrite using `[hψ b hb.2, ← valAt'_appLE (spMap (ψ b)) j U ⊤ hle _ le_top, ← CommRingCat.comp_apply, hid]`.

Conclude with `(valAt'_spMap (ψ b) t).symm`.
-/
theorem exists_coordinates {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {B : Set V} {X : Scheme.{0}}
    {a : V → (Sp ℂ ⟶ X)} (h : IsHolTo B a) {R : Type} [CommRing R] (j : Sp R ⟶ X) [IsOpenImmersion j]
    {b₀ : V} (hb₀ : b₀ ∈ B) (hj : a b₀ (default : PrimeSpectrum ℂ) ∈ Set.range j) :
    ∃ (B' : Set V) (ψ : V → (R →+* ℂ)), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ (∀ b ∈ B', a b = spMap (ψ b) ≫ j) ∧
      ∀ t : R, DifferentiableOn ℂ (fun b => ψ b t) B' := by
  classical
  let U : X.Opens := j ''ᵁ ⊤
  have hU : ∀ x : X, x ∈ U ↔ x ∈ Set.range j := fun x => by
    constructor
    · rintro ⟨y, -, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, trivial, rfl⟩
  have hl : ∀ x : Sp ℂ ⟶ X, ⊤ ≤ x ⁻¹ᵁ U → ∃ ψ : R →+* ℂ, x = spMap ψ ≫ j := fun x hx => by
    have hr : Set.range x ⊆ Set.range j := by
      rintro _ ⟨q, rfl⟩
      exact (hU _).1 (hx (Set.mem_univ q))
    refine ⟨(Spec.preimage (IsOpenImmersion.lift j x hr)).hom, ?_⟩
    rw [spMap, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]
  have h₀ : ⊤ ≤ a b₀ ⁻¹ᵁ U := (top_le_preimage_iff_mem _ _).2 ((hU _).2 hj)
  let ψ : V → (R →+* ℂ) := fun b => if hb : ⊤ ≤ a b ⁻¹ᵁ U then (hl _ hb).choose else (hl _ h₀).choose
  have hψ : ∀ b, ⊤ ≤ a b ⁻¹ᵁ U → a b = spMap (ψ b) ≫ j := fun b hb => by
    simp only [ψ, dif_pos hb]
    exact (hl _ hb).choose_spec
  refine ⟨{b ∈ B | ⊤ ≤ a b ⁻¹ᵁ U}, ψ, (h U 0).1, ⟨hb₀, h₀⟩, fun b hb => hb.1, fun b hb => hψ b hb.2, fun t => ?_⟩
  refine (h U ((j.appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom t))).2.congr fun b hb => ?_
  have hle : (⊤ : (Sp R).Opens) ≤ j ⁻¹ᵁ U := fun y _ => (hU _).2 ⟨y, rfl⟩
  have hid : (j.appIso ⊤).inv ≫ j.appLE U ⊤ hle = 𝟙 _ := by
    rw [Scheme.Hom.appIso_inv_appLE]
    exact (Sp R).presheaf.map_id _
  rw [hψ b hb.2, ← valAt'_appLE (spMap (ψ b)) j U ⊤ hle _ le_top, ← CommRingCat.comp_apply, hid]
  exact (valAt'_spMap (ψ b) t).symm

/- English proof (translation)
Introduce `hS E _ _ _ H Dw l Xo c σ g e F r M k T b₀ hb₀`. Use `set D : Set (Fin T.m → ℂ) := T.co ⁻¹' (M.X k).dom with hD`. Establish `hDo : IsOpen D` using `(FourierCoefficientDomain.isOpen_dom (M.X k)).preimage T.co.continuous`. Establish `hu : IsHolTo D (fun b => F.u k (T.Pf (T.co b)))` using `(F.hol k T.m D _ hDo T.holPer).1`. Establish `hw : ∀ b ∈ D, F.u k (T.Pf (T.co b)) ≫ Xo.s = spMap σ ≫ spMap (IntermediateField.inclusion c.le).toRingHom` using `fun b hb => by`.

Rewrite using `[F.over_σ k _ (T.isPer _ hb), spMap, spMap, spMap, ← Spec.map_comp]`. Both sides reduce to the same expression. Set `a : (Fin T.m → ℂ) → (Sp ℂ ⟶ Xo.XF c)` to `fun b => if hb : b ∈ D then pullback.lift _ _ (hw b hb) else pullback.lift _ _ (hw b₀ hb₀)`. Establish `ha₁ : ∀ b ∈ D, a b ≫ pullback.fst _ _ = F.u k (T.Pf (T.co b))` using `fun b hb => by`. Simplify using `only [a, dif_pos hb, pullback.lift_fst]`.

Establish `ha₂ : ∀ b ∈ D, a b ≫ pullback.snd _ _ = spMap σ` using `fun b hb => by`. Simplify using `only [a, dif_pos hb, pullback.lift_snd]`. Establish `ha : IsHolTo D a` using `GlobalTheory.HolFibre.isHolTo_of_isPullback (IsPullback.of_hasPullback _ _) (isHolTo_congr hu ha₁) (isHolTo_congr (GlobalTheory.HolFibre.isHolTo_const hDo (spMap σ)) ha₂)`. Take `⟨p, j, y₀, ⟨hj, hj₁, hj₂⟩, hz⟩` from `GlobalTheory.T.exists_openChart_framedPoint_testRing hS E H Dw l Xo c (a b₀ (default : PrimeSpectrum ℂ))`. Take `⟨B, ψ, hBo, hb, hBD, hψ, hol⟩` from `exists_coordinates ha j hb₀ hz`.

Establish `hc : ∀ b ∈ B, ∀ x, ψ b (algebraMap c.F p.R x) = σ x` using `fun b hb x => by`. Establish `h₂` using `ha₂ b (hBD hb)`. Rewrite `h₂` using `[hψ b hb, Category.assoc, hj₂, spMap, spMap, spMap, ← Spec.map_comp]`. Conclude with `congrArg (fun φ => φ.hom x) (Spec.map_injective h₂)`. Set `mk : ∀ b ∈ B, p.R →ₐ[c.F] CAt σ` to `fun b hb => { toRingHom := (ψ b : p.R →+* CAt σ), commutes' := hc b hb }`.

Use `⟨p, y₀, B, fun b => if h : b ∈ B then mk b h else mk b₀ hb, hBo, hb, hBD, fun b h => ?_, fun t => ?_⟩` and prove the remaining obligations. Simplify using `only [dif_pos h]`. Rewrite using `[← ha₁ b (hBD h), hψ b h, Category.assoc, hj₁]`. Both sides reduce to the same expression. Use `(hol t).congr fun b h => ?_` and prove the remaining obligations.

Simplify using `only [dif_pos h]`. Both sides reduce to the same expression.
-/
theorem exists_chart_holomorphic :
    Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b₀ ∈ T.co ⁻¹' (M.X k).dom, ∃ (p : TRing c.F) (y₀ : FrPt Xo c p.R) (B : Set (Fin T.m → ℂ)) (ψ : (Fin T.m → ℂ) → (p.R →ₐ[c.F] CAt σ)), IsOpen B ∧ b₀ ∈ B ∧ B ⊆ T.co ⁻¹' (M.X k).dom ∧ (∀ b ∈ B, F.u k (T.Pf (T.co b)) = spMap (ψ b).toRingHom ≫ y₀.x) ∧ ∀ t : p.R, DifferentiableOn ℂ (fun b => toC (ψ b t)) B := by
  intro hS E _ _ _ H Dw l Xo c σ g e F r M k T b₀ hb₀
  classical
  set D : Set (Fin T.m → ℂ) := T.co ⁻¹' (M.X k).dom with hD
  have hDo : IsOpen D := (FourierCoefficientDomain.isOpen_dom (M.X k)).preimage T.co.continuous
  have hu : IsHolTo D (fun b => F.u k (T.Pf (T.co b))) := (F.hol k T.m D _ hDo T.holPer).1
  have hw : ∀ b ∈ D, F.u k (T.Pf (T.co b)) ≫ Xo.s =
      spMap σ ≫ spMap (IntermediateField.inclusion c.le).toRingHom := fun b hb => by
    rw [F.over_σ k _ (T.isPer _ hb), spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  let a : (Fin T.m → ℂ) → (Sp ℂ ⟶ Xo.XF c) := fun b =>
    if hb : b ∈ D then pullback.lift _ _ (hw b hb) else pullback.lift _ _ (hw b₀ hb₀)
  have ha₁ : ∀ b ∈ D, a b ≫ pullback.fst _ _ = F.u k (T.Pf (T.co b)) := fun b hb => by
    simp only [a, dif_pos hb, pullback.lift_fst]
  have ha₂ : ∀ b ∈ D, a b ≫ pullback.snd _ _ = spMap σ := fun b hb => by
    simp only [a, dif_pos hb, pullback.lift_snd]
  have ha : IsHolTo D a := GlobalTheory.HolFibre.isHolTo_of_isPullback (IsPullback.of_hasPullback _ _)
    (isHolTo_congr hu ha₁) (isHolTo_congr (GlobalTheory.HolFibre.isHolTo_const hDo (spMap σ)) ha₂)
  obtain ⟨p, j, y₀, ⟨hj, hj₁, hj₂⟩, hz⟩ := GlobalTheory.T.exists_openChart_framedPoint_testRing hS E H Dw l Xo c (a b₀ (default : PrimeSpectrum ℂ))
  obtain ⟨B, ψ, hBo, hb, hBD, hψ, hol⟩ := exists_coordinates ha j hb₀ hz
  have hc : ∀ b ∈ B, ∀ x, ψ b (algebraMap c.F p.R x) = σ x := fun b hb x => by
    have h₂ := ha₂ b (hBD hb)
    rw [hψ b hb, Category.assoc, hj₂, spMap, spMap, spMap, ← Spec.map_comp] at h₂
    exact congrArg (fun φ => φ.hom x) (Spec.map_injective h₂)
  let mk : ∀ b ∈ B, p.R →ₐ[c.F] CAt σ := fun b hb =>
    { toRingHom := (ψ b : p.R →+* CAt σ), commutes' := hc b hb }
  refine ⟨p, y₀, B, fun b => if h : b ∈ B then mk b h else mk b₀ hb, hBo, hb, hBD, fun b h => ?_, fun t => ?_⟩
  · simp only [dif_pos h]
    rw [← ha₁ b (hBD h), hψ b h, Category.assoc, hj₁]
    rfl
  · refine (hol t).congr fun b h => ?_
    simp only [dif_pos h]
    rfl

end GlobalTheory.HolChart
