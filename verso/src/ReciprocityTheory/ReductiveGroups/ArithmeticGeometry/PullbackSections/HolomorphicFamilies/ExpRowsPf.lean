import Formalism.LocalToGlobal.ProjectiveLattices.OpenRowsFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartX

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows

open AlgebraicGeometry CategoryTheory Opposite NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped MonObj

section Der

variable {g : ℕ} {Y : Scheme.{0}}

instance isLocalHom_fst : IsLocalHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom :=
  ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ha⟩

instance isLocalHom_epsMul (cc : ℂ) : IsLocalHom (epsMul cc) :=
  ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (by
    have := TrivSqZeroExt.isUnit_iff_isUnit_fst.mp ha
    simpa [epsMul] using this)⟩

instance isLocalHom_fst' : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)) :=
  isLocalHom_fst

instance isLocalHom_epsMul' (cc : ℂ) : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom (epsMul cc))) :=
  isLocalHom_epsMul cc

/- English proof (translation)
Introduce `x _`. Establish `hs : (x : PrimeSpectrum (DualNumber ℂ)) ⤳ IsLocalRing.closedPoint (DualNumber ℂ)` using `by first`. Consider the case `exact IsLocalRing.specializes_closedPoint _`. Consider the case `exact (PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal (x : PrimeSpectrum (DualNumber ℂ)).2.ne_top)`. Conclude with `hs.mem_open W.isOpen hW`.
-/
theorem dual_top_le (W : (Spec (CommRingCat.of (DualNumber ℂ))).Opens)
    (hW : IsLocalRing.closedPoint (DualNumber ℂ) ∈ W) : ⊤ ≤ W := by
  intro x _
  have hs : (x : PrimeSpectrum (DualNumber ℂ)) ⤳ IsLocalRing.closedPoint (DualNumber ℂ) := by
    first
    | exact IsLocalRing.specializes_closedPoint _
    | exact (PrimeSpectrum.le_iff_specializes _ _).1
        (IsLocalRing.le_maximalIdeal (x : PrimeSpectrum (DualNumber ℂ)).2.ne_top)
  exact hs.mem_open W.isOpen hW

/- English proof (translation)
Establish `he : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0` using `hv.1`. Establish `hh : ∀ {a b : Sp ℂ ⟶ Y} (_ : a = b) (h1 : ⊤ ≤ a ⁻¹ᵁ U) (h2 : ⊤ ≤ b ⁻¹ᵁ U), a.appLE U ⊤ h1 = b.appLE U ⊤ h2`. Introduce `a b hab h1 h2`. Substitute `hab` using the available equality. Both sides reduce to the same expression.

Establish `h0 : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v) ⁻¹ᵁ U`. Rewrite using `[he]`. Conclude with `hU`. Establish `key` using `specMap_comp_appLE (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) v U h0 h`. Rewrite using `[← hh he h0 hU]`.

Establish `key2` using `congrArg (fun φ => φ.hom f) key`. Use `first`. Consider the case `exact key2.symm`. Consider the case `simpa using key2.symm`.
-/
theorem fst_appLE {e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Y}
    (hv : IsDerivAt0 e w v) (U : Y.Opens) (hU : ⊤ ≤ (e 0) ⁻¹ᵁ U) (h : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(Y, U)) :
    TrivSqZeroExt.fst ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom (v.appLE U ⊤ h f)) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((e 0).appLE U ⊤ hU f) := by
  have he : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 := hv.1
  have hh : ∀ {a b : Sp ℂ ⟶ Y} (_ : a = b) (h1 : ⊤ ≤ a ⁻¹ᵁ U) (h2 : ⊤ ≤ b ⁻¹ᵁ U),
      a.appLE U ⊤ h1 = b.appLE U ⊤ h2 := by
    intro a b hab h1 h2
    subst hab
    rfl
  have h0 : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v) ⁻¹ᵁ U := by
    rw [he]
    exact hU
  have key := specMap_comp_appLE (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) v U h0 h
  rw [← hh he h0 hU]
  have key2 := congrArg (fun φ => φ.hom f) key
  first
  | exact key2.symm
  | simpa using key2.symm

/- English proof (translation)
Introduce `x _`. Rewrite using `[← hv.1]`. Establish `hx` using `h (show (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).base x ∈ (⊤ : (Sp (DualNumber ℂ)).Opens) from trivial)`. Use `first`. Consider the case `exact hx`.

Consider the case `(simp only [Scheme.Hom.mem_preimage, Scheme.comp_base_apply] at hx ⊢; exact hx)`.
-/
theorem tangent_open_preimage_zero {e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Y}
    (hv : IsDerivAt0 e w v) (U : Y.Opens) (h : ⊤ ≤ v ⁻¹ᵁ U) : ⊤ ≤ (e 0) ⁻¹ᵁ U := by
  intro x _
  rw [← hv.1]
  have hx := h (show (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).base x ∈ (⊤ : (Sp (DualNumber ℂ)).Opens) from trivial)
  first
  | exact hx
  | (simp only [Scheme.Hom.mem_preimage, Scheme.comp_base_apply] at hx ⊢; exact hx)

/- English proof (translation)
Apply `hom_ext_of_local` to reduce the goal to its premises. Establish `hc : (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).base (IsLocalRing.closedPoint ℂ) = IsLocalRing.closedPoint (DualNumber ℂ)` using `IsLocalRing.comap_closedPoint _`. Establish `e1` using `congrArg (fun φ => φ.base (IsLocalRing.closedPoint ℂ)) (hv.1.trans hv'.1.symm)`. Establish `e2 : v ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) (IsLocalRing.closedPoint ℂ)) = v' ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) (IsLocalRing.closedPoint ℂ))` using `e1`. Rewrite `e2` using `[hc]`.

Conclude with `e2`. Introduce `U h₁ h₂`. Rewrite using `[← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom]`. Use extensionality with `f`. Establish `hU` using `tangent_open_preimage_zero hv U h₁`.

Conclude with `(fst_appLE hv U hU h₁ f).trans (fst_appLE hv' U hU h₂ f).symm`. Conclude with `(hv.2 U h₁ f).trans (hv'.2 U h₂ f).symm`.
-/
theorem isDerivAt0_unique {e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)} {w : Fin g → ℂ} {v v' : Sp (DualNumber ℂ) ⟶ Y}
    (hv : IsDerivAt0 e w v) (hv' : IsDerivAt0 e w v') : v = v' := by
  apply hom_ext_of_local
  · have hc : (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).base (IsLocalRing.closedPoint ℂ) =
        IsLocalRing.closedPoint (DualNumber ℂ) :=
      IsLocalRing.comap_closedPoint _
    have e1 := congrArg (fun φ => φ.base (IsLocalRing.closedPoint ℂ)) (hv.1.trans hv'.1.symm)
    have e2 : v ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) (IsLocalRing.closedPoint ℂ)) =
        v' ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) (IsLocalRing.closedPoint ℂ)) := e1
    rw [hc] at e2
    exact e2
  · intro U h₁ h₂
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom]
    ext f
    have hU := tangent_open_preimage_zero hv U h₁
    · exact (fst_appLE hv U hU h₁ f).trans (fst_appLE hv' U hU h₂ f).symm
    · exact (hv.2 U h₁ f).trans (hv'.2 U h₂ f).symm

/- English proof (translation)
Use `⟨by rw [← Category.assoc, hv.1], fun U h f => ?_⟩` and prove the remaining obligations. Establish `h' : ⊤ ≤ v ⁻¹ᵁ (φ ⁻¹ᵁ U)` using `h`. Establish `key` using `hv.2 (φ ⁻¹ᵁ U) h' (φ.app U f)`. Simplify using `only [← valAt'_comp]`. Rewrite using `[← key]`.

Establish `hc : (v ≫ φ).appLE U ⊤ h = φ.app U ≫ v.appLE (φ ⁻¹ᵁ U) ⊤ h'` using `by first`. Consider the case `exact Scheme.comp_appLE v φ U ⊤ h`. Consider the case `exact Scheme.Hom.comp_appLE v φ U ⊤ h`. Consider the case `simp [Scheme.Hom.appLE]`. Rewrite using `[hc]`.

Both sides reduce to the same expression.
-/
theorem isDerivAt0_comp_hom {Y' : Scheme.{0}} {e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)} {w : Fin g → ℂ}
    {v : Sp (DualNumber ℂ) ⟶ Y} (hv : IsDerivAt0 e w v) (φ : Y ⟶ Y') :
    IsDerivAt0 (fun z => e z ≫ φ) w (v ≫ φ) := by
  refine ⟨by rw [← Category.assoc, hv.1], fun U h f => ?_⟩
  have h' : ⊤ ≤ v ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
  have key := hv.2 (φ ⁻¹ᵁ U) h' (φ.app U f)
  simp only [← valAt'_comp]
  rw [← key]
  have hc : (v ≫ φ).appLE U ⊤ h = φ.app U ≫ v.appLE (φ ⁻¹ᵁ U) ⊤ h' := by
    first
    | exact Scheme.comp_appLE v φ U ⊤ h
    | exact Scheme.Hom.comp_appLE v φ U ⊤ h
    | simp [Scheme.Hom.appLE]
  rw [hc]
  rfl

/- English proof (translation)
Establish `hcomp : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (epsMul cc) = (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom` using `RingHom.ext fun x => by simp [epsMul]`. Use `⟨?_, fun U h f => ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, ← hv.1]`. Use `congr 1`. Use `show Spec.map _ ≫ Spec.map _ = Spec.map _`.

Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]`. Establish `hp : IsLocalRing.closedPoint (DualNumber ℂ) ∈ v ⁻¹ᵁ U`. Establish `hx` using `h (show IsLocalRing.closedPoint (DualNumber ℂ) ∈ (⊤ : (Sp (DualNumber ℂ)).Opens) from trivial)`. Establish `hc : (spMap (epsMul cc)).base (IsLocalRing.closedPoint (DualNumber ℂ)) = IsLocalRing.closedPoint (DualNumber ℂ)` using `IsLocalRing.comap_closedPoint (epsMul cc)`. Use `first`.

Consider the case `(rw [← hc]; exact hx)`. Consider the case `(simp only [Scheme.Hom.mem_preimage, Scheme.comp_base_apply] at hx ⊢; rwa [hc] at hx)`. Establish `hq : ⊤ ≤ v ⁻¹ᵁ U` using `dual_top_le _ hp`. Establish `key` using `congrArg (fun φ => φ.hom f) (specMap_comp_appLE (CommRingCat.ofHom (epsMul cc)) v U h hq)`. Establish `hd` using `hv.2 U hq f`.

Simplify using `only at key`. Rewrite using `[map_smul, ← hd]`. Use `show TrivSqZeroExt.snd (((spMap (epsMul cc) ≫ v).appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom).hom f) = _`. Rewrite using `[key]`. Use `first`.

Consider the case `simp [epsMul]`. Consider the case `rfl`.
-/
theorem isDerivAt0_smul {e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Y}
    (hv : IsDerivAt0 e w v) (cc : ℂ) : IsDerivAt0 e (cc • w) (spMap (epsMul cc) ≫ v) := by
  have hcomp : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (epsMul cc) =
      (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom :=
    RingHom.ext fun x => by simp [epsMul]
  refine ⟨?_, fun U h f => ?_⟩
  · rw [← Category.assoc, ← hv.1]
    congr 1
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  · have hp : IsLocalRing.closedPoint (DualNumber ℂ) ∈ v ⁻¹ᵁ U := by
      have hx := h (show IsLocalRing.closedPoint (DualNumber ℂ) ∈ (⊤ : (Sp (DualNumber ℂ)).Opens) from trivial)
      have hc : (spMap (epsMul cc)).base (IsLocalRing.closedPoint (DualNumber ℂ)) =
          IsLocalRing.closedPoint (DualNumber ℂ) :=
        IsLocalRing.comap_closedPoint (epsMul cc)
      first
      | (rw [← hc]; exact hx)
      | (simp only [Scheme.Hom.mem_preimage, Scheme.comp_base_apply] at hx ⊢; rwa [hc] at hx)
    have hq : ⊤ ≤ v ⁻¹ᵁ U := dual_top_le _ hp
    have key := congrArg (fun φ => φ.hom f) (specMap_comp_appLE (CommRingCat.ofHom (epsMul cc)) v U h hq)
    have hd := hv.2 U hq f
    simp only at key
    rw [map_smul, ← hd]
    show TrivSqZeroExt.snd (((spMap (epsMul cc) ≫ v).appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom).hom f) = _
    rw [key]
    first
    | simp [epsMul]
    | rfl

/- English proof (translation)
Use `⟨by show _ = e (D 0); rw [map_zero]; exact hv.1, fun U h f => ?_⟩` and prove the remaining obligations. Rewrite using `[hv.2 U h f]`. Establish `h0 : (0 : Fin g → ℂ) ∈ {z | ⊤ ≤ e z ⁻¹ᵁ U}` using `tangent_open_preimage_zero hv U h`. Establish `hd : DifferentiableAt ℂ (fun z => valAt' (e z) U f) (D 0)`. Rewrite using `[map_zero]`.

Conclude with `((hol U f).2 0 h0).differentiableAt ((hol U f).1.mem_nhds h0)`. Establish `hc` using `fderiv_comp (0 : Fin g → ℂ) hd D.differentiableAt`. Use `show _ = fderiv ℂ ((fun z => valAt' (e z) U f) ∘ D) 0 w`. Rewrite using `[hc, ContinuousLinearMap.fderiv, map_zero]`. Both sides reduce to the same expression.
-/
theorem isDerivAt0_comp_lin {e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)} (hol : IsHolFam e) (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ))
    {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Y} (hv : IsDerivAt0 e (D w) v) :
    IsDerivAt0 (fun z => e (D z)) w v := by
  refine ⟨by show _ = e (D 0); rw [map_zero]; exact hv.1, fun U h f => ?_⟩
  rw [hv.2 U h f]
  have h0 : (0 : Fin g → ℂ) ∈ {z | ⊤ ≤ e z ⁻¹ᵁ U} := tangent_open_preimage_zero hv U h
  have hd : DifferentiableAt ℂ (fun z => valAt' (e z) U f) (D 0) := by
    rw [map_zero]
    exact ((hol U f).2 0 h0).differentiableAt ((hol U f).1.mem_nhds h0)
  have hc := fderiv_comp (0 : Fin g → ℂ) hd D.differentiableAt
  show _ = fderiv ℂ ((fun z => valAt' (e z) U f) ∘ D) 0 w
  rw [hc, ContinuousLinearMap.fderiv, map_zero]
  rfl

end Der

section Tan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

def tyD (ty : Fin g → (E →+* ℂ)) (a : NumberField.RingOfIntegers E) : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z k => ty k (a : E) * z k
      map_add' := fun z z' => by funext k; simp [mul_add]
      map_smul' := fun t z => by funext k; simp; ring }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tyD_apply (a : NumberField.RingOfIntegers E) (z : Fin g → ℂ) : tyD ty a z = fun k => ty k (a : E) * z k := rfl

/- English proof (translation)
Take `⟨v0, hv0, -⟩` from `(F.ex_diff i P hP).1 w`. Rewrite using `[isDerivAt0_unique hv hv0, Over.w v0]`. Use `first`. Consider the case `rfl`. Consider the case `simp [epsPt]`.
-/
theorem derivAt_over (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left}
    (hv : IsDerivAt0 (fun z => (F.ex i P z).left) w v) :
    v ≫ Xo.univ.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ F.u i P := by
  obtain ⟨v0, hv0, -⟩ := (F.ex_diff i P hP).1 w
  rw [isDerivAt0_unique hv hv0, Over.w v0]
  first
  | rfl
  | simp [epsPt]

end Tan

end ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows
