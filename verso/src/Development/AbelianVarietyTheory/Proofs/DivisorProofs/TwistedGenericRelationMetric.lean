import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.GalCarry.LgCarry

section Loc

variable {X : Scheme.{0}} [IsIntegral X]

/- English proof (translation)
Take `⟨a, ha, rfl⟩` from `hf`. Take `⟨b, hb, rfl⟩` from `hg`. Conclude with `⟨a * b, ha.mul hb, map_mul _ _ _⟩`.
-/
private theorem unitAt_mul {x : X} {f g : X.functionField} (hf : UnitAt x f) (hg : UnitAt x g) : UnitAt x (f * g) := by
  obtain ⟨a, ha, rfl⟩ := hf
  obtain ⟨b, hb, rfl⟩ := hg
  exact ⟨a * b, ha.mul hb, map_mul _ _ _⟩

/- English proof (translation)
Take `⟨a, ha, rfl⟩` from `hf`. Use `⟨((ha.unit⁻¹ : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x), Units.isUnit _, ?_⟩` and prove the remaining obligations. Rewrite using `[map_units_inv, IsUnit.unit_spec]`.
-/
private theorem unitAt_inv {x : X} {f : X.functionField} (hf : UnitAt x f) : UnitAt x f⁻¹ := by
  obtain ⟨a, ha, rfl⟩ := hf
  refine ⟨((ha.unit⁻¹ : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x), Units.isUnit _, ?_⟩
  rw [map_units_inv, IsUnit.unit_spec]

/- English proof (translation)
Take `⟨a, rfl⟩` from `hf`. Take `⟨b, rfl⟩` from `hg`. Rewrite using `[← map_mul, GlobalTheory.TrueGeo.Base.valAt_stalk, GlobalTheory.TrueGeo.Base.valAt_stalk, GlobalTheory.TrueGeo.Base.valAt_stalk, map_mul]`.
-/
private theorem valAt_mul {K : Type} [Field K] (y : Sp K ⟶ X) {f g : X.functionField} (hf : RegAt (GlobalTheory.TrueGeo.below y) f)
    (hg : RegAt (GlobalTheory.TrueGeo.below y) g) : GlobalTheory.TrueGeo.valAt y (f * g) = GlobalTheory.TrueGeo.valAt y f * GlobalTheory.TrueGeo.valAt y g := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  rw [← map_mul, GlobalTheory.TrueGeo.Base.valAt_stalk, GlobalTheory.TrueGeo.Base.valAt_stalk, GlobalTheory.TrueGeo.Base.valAt_stalk, map_mul]

/- English proof (translation)
Take `⟨a, ha, rfl⟩` from `hf`. Rewrite using `[GlobalTheory.TrueGeo.Base.valAt_stalk]`. Conclude with `(ha.map _).ne_zero`.
-/
private theorem valAt_ne_zero {K : Type} [Field K] (y : Sp K ⟶ X) {f : X.functionField} (hf : UnitAt (GlobalTheory.TrueGeo.below y) f) :
    GlobalTheory.TrueGeo.valAt y f ≠ 0 := by
  obtain ⟨a, ha, rfl⟩ := hf
  rw [GlobalTheory.TrueGeo.Base.valAt_stalk]
  exact (ha.map _).ne_zero

/- English proof (translation)
Proceed by induction on `(Finset.univ : Finset ι) using Finset.induction_on with`. Consider the case `empty => simpa using CartierDiv.isEqn_zero x`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha]`. Conclude with `((h a).zsmul _).add ih`.
-/
private theorem isEqn_sum {ι : Type} [Fintype ι] (D : ι → CartierDiv X) (n : ι → ℤ) (t : ι → X.functionFieldˣ) {x : X}
    (h : ∀ i, (D i).IsEqn x (t i)) : (∑ i, n i • D i).IsEqn x (∏ i, t i ^ n i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simpa using CartierDiv.isEqn_zero x
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha]; exact ((h a).zsmul _).add ih

/- English proof (translation)
Rewrite using `[Units.val_mul, Units.val_inv_eq_inv_val, ← div_eq_mul_inv]`. Conclude with `(hg.iff_unitAt).1 hg'`.
-/
private theorem unitAt_of_isEqn {D : CartierDiv X} {x : X} {g g' : X.functionFieldˣ} (hg : D.IsEqn x g) (hg' : D.IsEqn x g') :
    UnitAt x ((g' * g⁻¹ : X.functionFieldˣ) : X.functionField) := by
  rw [Units.val_mul, Units.val_inv_eq_inv_val, ← div_eq_mul_inv]
  exact (hg.iff_unitAt).1 hg'

/- English proof (translation)
Take `⟨a, -, rfl⟩` from `hf`. Conclude with `⟨a, rfl⟩`.
-/
private theorem regAt_of_unitAt {x : X} {f : X.functionField} (hf : UnitAt x f) : RegAt x f := by
  obtain ⟨a, -, rfl⟩ := hf
  exact ⟨a, rfl⟩

/- English proof (translation)
Rewrite using `[valAt_mul y (regAt_of_unitAt hf) (regAt_of_unitAt hg), map_mul, Real.log_mul (ω.pos (valAt_ne_zero y hf)).ne' (ω.pos (valAt_ne_zero y hg)).ne']`.
-/
private theorem log_valAt_mul {K : Type} [Field K] (ω : AbsoluteValue K ℝ) (y : Sp K ⟶ X) {f g : X.functionField}
    (hf : UnitAt (GlobalTheory.TrueGeo.below y) f) (hg : UnitAt (GlobalTheory.TrueGeo.below y) g) :
    Real.log (ω (GlobalTheory.TrueGeo.valAt y (f * g))) =
      Real.log (ω (GlobalTheory.TrueGeo.valAt y f)) + Real.log (ω (GlobalTheory.TrueGeo.valAt y g)) := by
  rw [valAt_mul y (regAt_of_unitAt hf) (regAt_of_unitAt hg), map_mul,
    Real.log_mul (ω.pos (valAt_ne_zero y hf)).ne' (ω.pos (valAt_ne_zero y hg)).ne']

end Loc

/- English proof (translation)
Use `haveI := v.isMaximal`. Use `letI := Ideal.Quotient.field v.asIdeal`. Use `haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot`. Conclude with `CharP.char_is_prime (𝓞 F ⧸ v.asIdeal) _`.
-/
private theorem prime_resP {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : (resP v).Prime := by
  haveI := v.isMaximal
  letI := Ideal.Quotient.field v.asIdeal
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  exact CharP.char_is_prime (𝓞 F ⧸ v.asIdeal) _

/- English proof (translation)
Establish `h : Units.map (ψ : K' →* K) P' * U * Q⁻¹ = Units.map (ψ : K' →* K) (P' * Q'⁻¹) * (Units.map (ψ : K' →* K) Q' * U * Q⁻¹)`. Rewrite using `[map_mul, map_inv]`. Use `group`. Rewrite using `[h, Units.val_mul]`. Both sides reduce to the same expression.
-/
private theorem units_split {K K' : Type} [Field K] [Field K'] (ψ : K' →+* K) (Q U : Kˣ) (P' Q' : K'ˣ) :
    ((Units.map (ψ : K' →* K) P' * U * Q⁻¹ : Kˣ) : K) =
      ψ ((P' * Q'⁻¹ : K'ˣ) : K') * ((Units.map (ψ : K' →* K) Q' * U * Q⁻¹ : Kˣ) : K) := by
  have h : Units.map (ψ : K' →* K) P' * U * Q⁻¹ =
      Units.map (ψ : K' →* K) (P' * Q'⁻¹) * (Units.map (ψ : K' →* K) Q' * U * Q⁻¹) := by
    rw [map_mul, map_inv]; group
  rw [h, Units.val_mul]
  rfl

/- English proof (translation)
Substitute `hy hP` using the available equality. Establish `uC : UnitAt (GlobalTheory.TrueGeo.below y) (ψ ((P' * Q'⁻¹ : Y'.Fnˣ) : Y'.Fn))` using `unitAt_map h uA`. Establish `hs` using `units_split ψ Q U P' Q'`. Establish `hv` using `valAt_map h y (regAt_of_unitAt uA)`. Generalize the expression as in `((Units.map (ψ : Y'.Fn →* Y.Fn) Q' * U * Q⁻¹ : Y.Fnˣ) : Y.Fn) = d at hs ⊢`.

Establish `hne : ψ ((P' * Q'⁻¹ : Y'.Fnˣ) : Y'.Fn) ≠ 0` using `(map_ne_zero ψ).2 (Units.ne_zero _)`. Establish `uD : UnitAt (GlobalTheory.TrueGeo.below y) d`. Establish `e1` using `unitAt_mul (unitAt_inv uC) uB`. Rewrite `e1` using `[hs, inv_mul_cancel_left₀ hne]`. Then use the resulting hypothesis. Rewrite using `[hs, log_valAt_mul ω y uC uD, hv]`.
-/
private theorem log_split {F : Type} [Field F] {Y Y' : Var F} {f : Y.X ⟶ Y'.X} {ψ : Y'.Fn →+* Y.Fn}
    (h : genericPt Y ≫ f = spMap ψ ≫ genericPt Y') {K : Type} [Field K] (ω : AbsoluteValue K ℝ) (y : Sp K ⟶ Y.X)
    (y' : Sp K ⟶ Y'.X) (hy : y' = y ≫ f) (P Q U : Y.Fnˣ) (P' Q' : Y'.Fnˣ)
    (hP : P = Units.map (ψ : Y'.Fn →* Y.Fn) P' * U)
    (uA : UnitAt (GlobalTheory.TrueGeo.below y') ((P' * Q'⁻¹ : Y'.Fnˣ) : Y'.Fn))
    (uB : UnitAt (GlobalTheory.TrueGeo.below y) ((P * Q⁻¹ : Y.Fnˣ) : Y.Fn)) :
    Real.log (ω (GlobalTheory.TrueGeo.valAt y ((P * Q⁻¹ : Y.Fnˣ) : Y.Fn))) =
      Real.log (ω (GlobalTheory.TrueGeo.valAt y' ((P' * Q'⁻¹ : Y'.Fnˣ) : Y'.Fn))) +
      Real.log (ω (GlobalTheory.TrueGeo.valAt y ((Units.map (ψ : Y'.Fn →* Y.Fn) Q' * U * Q⁻¹ : Y.Fnˣ) : Y.Fn))) := by
  subst hy hP
  have uC : UnitAt (GlobalTheory.TrueGeo.below y) (ψ ((P' * Q'⁻¹ : Y'.Fnˣ) : Y'.Fn)) := unitAt_map h uA
  have hs := units_split ψ Q U P' Q'
  have hv := valAt_map h y (regAt_of_unitAt uA)
  generalize ((Units.map (ψ : Y'.Fn →* Y.Fn) Q' * U * Q⁻¹ : Y.Fnˣ) : Y.Fn) = d at hs ⊢
  have hne : ψ ((P' * Q'⁻¹ : Y'.Fnˣ) : Y'.Fn) ≠ 0 := (map_ne_zero ψ).2 (Units.ne_zero _)
  have uD : UnitAt (GlobalTheory.TrueGeo.below y) d := by
    have e1 := unitAt_mul (unitAt_inv uC) uB
    rwa [hs, inv_mul_cancel_left₀ hne] at e1
  rw [hs, log_valAt_mul ω y uC uD, hv]

section Carry

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} (T : Tw Z)

/- English proof (translation)
Rewrite using `[map_prod, ← Finset.prod_mul_distrib]`. Use `(Fintype.prod_equiv T.letter _ _ fun z => ?_).symm` and prove the remaining obligations. Rewrite using `[T.expo_sym hw]`. Take `⟨τ, i⟩` from `z`. Rewrite using `[map_zpow, ← mul_zpow]`.

Conclude with `congrArg (· ^ _) (h5 τ i).symm`.
-/
private theorem prod_relab {G G' : Type} [CommGroup G] [CommGroup G'] (m : G' →* G) (t t₀ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → G)
    (t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → G') (h5 : ∀ τ i, t (T.emb τ) (T.ix i) = m (t' τ i) * t₀ τ i)
    {w : Sym E →₀ ℤ} (hw : ∀ a ∈ w.support, a.2.2.isLeft = true) :
    (∏ x : Pad.Letter Dw, t x.1 x.2 ^ expo Dw (w.mapDomain T.sym) x) =
      m (∏ x : Pad.Letter Dw, t' x.1 x.2 ^ expo Dw w x) * ∏ x : Pad.Letter Dw, t₀ x.1 x.2 ^ expo Dw w x := by
  rw [map_prod, ← Finset.prod_mul_distrib]
  refine (Fintype.prod_equiv T.letter _ _ fun z => ?_).symm
  rw [T.expo_sym hw]
  obtain ⟨τ, i⟩ := z
  rw [map_zpow, ← mul_zpow]
  exact congrArg (· ^ _) (h5 τ i).symm

/- English proof (translation)
Substitute `hx` using the available equality. Rewrite using `[Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by push_cast; ring)]`. Use `Finsupp.sum_congr fun b hb => ?_` and prove the remaining obligations. Take `⟨bb, R, ⟨τ, k⟩ | k⟩` from `b`. Conclude with `congrArg _ (hLn p (bb p) _ _ _ ht hu τ k)`.

Conclude with `absurd (hw _ hb) (by simp)`.
-/
private theorem sum_lnStep (hLn : T.LnPush) (p : ℕ) [Fact p.Prime] {w : Sym E →₀ ℤ} (hw : ∀ a ∈ w.support, a.2.2.isLeft = true)
    (x x' : Sp ℂ_[p] ⟶ Z.X) (hx : x ≫ T.ρ.hom = x')
    (u u' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber ℂ_[p]) ⟶ Z.t.G.left)) (ht : ∀ τ i, IsTanAtG Z.t x (u τ i))
    (hu : ∀ τ i, u' τ i = u (T.emb τ) (T.ix i) ≫ T.mu.cm.F) :
    ((w.mapDomain T.sym).sum fun a n => (n : ℝ) * lnStep Z.t x u p (a.1 p) a.2.2) =
      w.sum fun a n => (n : ℝ) * lnStep Z.t x' u' p (a.1 p) a.2.2 := by
  subst hx
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by push_cast; ring)]
  refine Finsupp.sum_congr fun b hb => ?_
  obtain ⟨bb, R, ⟨τ, k⟩ | k⟩ := b
  · exact congrArg _ (hLn p (bb p) _ _ _ ht hu τ k)
  · exact absurd (hw _ hb) (by simp)

/- English proof (translation)
Introduce `b hb`. Take `⟨a', ha', rfl⟩` from `Finset.mem_image.1 (Finsupp.mapDomain_support hb)`. Take `⟨_, _, ⟨τ, k⟩ | k⟩` from `a'`. Both sides reduce to the same expression. Conclude with `absurd (hw _ ha') (by simp)`.
-/
private theorem isLeft_mapDomain {w : Sym E →₀ ℤ} (hw : ∀ a ∈ w.support, a.2.2.isLeft = true) :
    ∀ b ∈ (w.mapDomain T.sym).support, b.2.2.isLeft = true := by
  classical
  intro b hb
  obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hb)
  obtain ⟨_, _, ⟨τ, k⟩ | k⟩ := a'
  · rfl
  · exact absurd (hw _ ha') (by simp)

variable {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F}

/- English proof (translation)
Rewrite using `[h1, h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem add_mul_carry {A B D S S' : ℝ} (r : ℝ) (h1 : A = B + D) (h2 : S = S') : A + r * S = B + r * S' + D := by
  rw [h1, h2]; ring

/- English proof (translation)
Establish `ey : spMap (Scheme.stalkClosedPointTo y.1).hom ≫ stalkPt C.Y (GlobalTheory.TrueGeo.below y.1) = y.1` using `Scheme.Spec_stalkClosedPointTo_fromSpecStalk y.1`. Establish `ey' : spMap (Scheme.stalkClosedPointTo y'.1).hom ≫ stalkPt C'.Y (GlobalTheory.TrueGeo.below y'.1) = y'.1` using `Scheme.Spec_stalkClosedPointTo_fromSpecStalk y'.1`. Establish `hsc : (Scheme.stalkClosedPointTo y.1).hom.comp a = (Scheme.stalkClosedPointTo y'.1).hom`. Establish `k : spMap ((Scheme.stalkClosedPointTo y.1).hom.comp a) ≫ C'.Y.X.fromSpecStalk (GlobalTheory.TrueGeo.below y'.1) = spMap (Scheme.stalkClosedPointTo y'.1).hom ≫ C'.Y.X.fromSpecStalk (GlobalTheory.TrueGeo.below y'.1)`. Establish `k0` using `h1`.

Unfold `stalkPt at k0 ey ey'`. Rewrite using `[spMap_comp, Category.assoc, ← k0, ← Category.assoc, ey, ey', hy]`. Conclude with `congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 k))`. Establish `key2 : ∀ (ψy : C.Y.X.presheaf.stalk (GlobalTheory.TrueGeo.below y.1) →+* ℂ_[resP v]) (ψy' : C'.Y.X.presheaf.stalk (GlobalTheory.TrueGeo.below y'.1) →+* ℂ_[resP v]), ψy.comp a = ψy' → ((w.mapDomain T.sym).sum fun a n => (n : ℝ) * lnStep Z.t (spMap ψy ≫ stalkPt C.Y (GlobalTheory.Tr …`. Introduce `ψy ψy' hψa`.

Use `sum_lnStep T hLn (resP v) hw _ _ ?_ _ _ (fun τ i => GlobalTheory.LieMet.isTan_map ψy rfl (f.tan τ i)) fun τ i => ?_` and prove the remaining obligations. Simplify using `only [Category.assoc]`. Rewrite using `[← T.g_ι, ← reassoc_of% hφπ, reassoc_of% h1, ← Category.assoc (spMap ψy), ← spMap_comp, hψa]`. Rewrite using `[Category.assoc, ← h6]`. Establish `hd : spMap (dualMap ψy') = spMap (dualMap ψy) ≫ spMap (dualMap a)`.

Rewrite using `[← spMap_comp, ← dualMap_comp, hψa]`. Rewrite using `[hd]`. Conclude with `Category.assoc _ _ _`. Establish `k2` using `key2 ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom) ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y'.1).hom) (by rw [RingHom.comp_assoc, hsc])`. Establish `k1` using `log_split hgen ε.w y.1 y'.1 hy _ (GlobalTheory.TrueGeo.eqn (divOf C (expo Dw (w.mapDomain T.sym))) (GlobalTheory.TrueGeo.below y.1)) (prodPow t₀ (expo Dw w)) _ (GlobalTheory.TrueGeo.eqn (divOf C' (expo Dw w)) (GlobalTheory.TrueGeo.below y'.1)) (prod_relab T (Units.map (ψ : C'.Y.F …`.

Use `delta lgFr`. Conclude with `add_mul_carry _ k1 k2`.
-/
private theorem lgFr_carry (C C' : FlagCpt Z e) (φ : C.Y.X ≅ C'.Y.X) (ψ : C'.Y.Fn →+* C.Y.Fn)
    (t₀ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ) (w : Sym E →₀ ℤ) (hLn : T.LnPush)
    (hw : ∀ a ∈ w.support, a.2.2.isLeft = true) (v : HeightOneSpectrum (𝓞 F)) [Fact (resP v).Prime]
    (ε : GlobalTheory.TrueGeo.Ext v) (y : GlobalTheory.TrueGeo.AlgPt C.Y) (y' : GlobalTheory.TrueGeo.AlgPt C'.Y) (hy : y'.1 = y.1 ≫ φ.hom)
    (hφπ : φ.hom ≫ C'.π = C.π ≫ T.g.hom) (hgen : genericPt C.Y ≫ φ.hom = spMap ψ ≫ genericPt C'.Y)
    {χ : c.F →+* C.Y.X.presheaf.stalk (GlobalTheory.TrueGeo.below y.1)}
    (f : EigFrame Z χ (stalkPt C.Y (GlobalTheory.TrueGeo.below y.1) ≫ C.π ≫ genι Z))
    (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ)
    {χ' : c.F →+* C'.Y.X.presheaf.stalk (GlobalTheory.TrueGeo.below y'.1)}
    (f' : EigFrame Z χ' (stalkPt C'.Y (GlobalTheory.TrueGeo.below y'.1) ≫ C'.π ≫ genι Z))
    (t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C'.Y.Fnˣ)
    (a : C'.Y.X.presheaf.stalk (GlobalTheory.TrueGeo.below y'.1) →+* C.Y.X.presheaf.stalk (GlobalTheory.TrueGeo.below y.1))
    (h1 : stalkPt C.Y (GlobalTheory.TrueGeo.below y.1) ≫ φ.hom = spMap a ≫ stalkPt C'.Y (GlobalTheory.TrueGeo.below y'.1))
    (h5 : ∀ τ i, t (T.emb τ) (T.ix i) = Units.map (ψ : C'.Y.Fn →* C.Y.Fn) (t' τ i) * t₀ τ i)
    (h6 : ∀ τ i, spMap (dualMap a) ≫ f'.v τ i = f.v (T.emb τ) (T.ix i) ≫ T.mu.cm.F)
    (ht : ∀ τ i, (C.gr τ i).IsEqn (GlobalTheory.TrueGeo.below y.1) (t τ i))
    (ht' : ∀ τ i, (C'.gr τ i).IsEqn (GlobalTheory.TrueGeo.below y'.1) (t' τ i)) :
    lgFr C (w.mapDomain T.sym) v ε y f t = lgFr C' w v ε y' f' t' + Real.log (ε.w (GlobalTheory.TrueGeo.valAt y.1 ((Units.map (ψ : C'.Y.Fn →* C.Y.Fn) (GlobalTheory.TrueGeo.eqn (divOf C' (expo Dw w)) (GlobalTheory.TrueGeo.below y'.1)) * prodPow t₀ (expo Dw w) * (GlobalTheory.TrueGeo.eqn (divOf C (expo Dw (w.mapDomain T.sym))) (GlobalTheory.TrueGeo.below y.1))⁻¹ : C.Y.Fnˣ) : C.Y.Fn))) := by
  have ey : spMap (Scheme.stalkClosedPointTo y.1).hom ≫ stalkPt C.Y (GlobalTheory.TrueGeo.below y.1) = y.1 :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk y.1
  have ey' : spMap (Scheme.stalkClosedPointTo y'.1).hom ≫ stalkPt C'.Y (GlobalTheory.TrueGeo.below y'.1) = y'.1 :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk y'.1
  have hsc : (Scheme.stalkClosedPointTo y.1).hom.comp a = (Scheme.stalkClosedPointTo y'.1).hom := by
    have k : spMap ((Scheme.stalkClosedPointTo y.1).hom.comp a) ≫ C'.Y.X.fromSpecStalk (GlobalTheory.TrueGeo.below y'.1) =
        spMap (Scheme.stalkClosedPointTo y'.1).hom ≫ C'.Y.X.fromSpecStalk (GlobalTheory.TrueGeo.below y'.1) := by
      have k0 := h1
      unfold stalkPt at k0 ey ey'
      rw [spMap_comp, Category.assoc, ← k0, ← Category.assoc, ey, ey', hy]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 k))
  have key2 : ∀ (ψy : C.Y.X.presheaf.stalk (GlobalTheory.TrueGeo.below y.1) →+* ℂ_[resP v])
      (ψy' : C'.Y.X.presheaf.stalk (GlobalTheory.TrueGeo.below y'.1) →+* ℂ_[resP v]), ψy.comp a = ψy' →
      ((w.mapDomain T.sym).sum fun a n => (n : ℝ) * lnStep Z.t
        (spMap ψy ≫ stalkPt C.Y (GlobalTheory.TrueGeo.below y.1) ≫ C.π ≫ genι Z)
        (fun τ i => spMap (dualMap ψy) ≫ f.v τ i) (resP v) (a.1 (resP v)) a.2.2) =
      w.sum fun a n => (n : ℝ) * lnStep Z.t (spMap ψy' ≫ stalkPt C'.Y (GlobalTheory.TrueGeo.below y'.1) ≫ C'.π ≫ genι Z)
        (fun τ i => spMap (dualMap ψy') ≫ f'.v τ i) (resP v) (a.1 (resP v)) a.2.2 := by
    intro ψy ψy' hψa
    refine sum_lnStep T hLn (resP v) hw _ _ ?_ _ _ (fun τ i => GlobalTheory.LieMet.isTan_map ψy rfl (f.tan τ i)) fun τ i => ?_
    · simp only [Category.assoc]
      rw [← T.g_ι, ← reassoc_of% hφπ, reassoc_of% h1, ← Category.assoc (spMap ψy), ← spMap_comp, hψa]
    · rw [Category.assoc, ← h6]
      have hd : spMap (dualMap ψy') = spMap (dualMap ψy) ≫ spMap (dualMap a) := by
        rw [← spMap_comp, ← dualMap_comp, hψa]
      rw [hd]
      exact Category.assoc _ _ _
  have k2 := key2 ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom)
    ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y'.1).hom) (by rw [RingHom.comp_assoc, hsc])
  have k1 := log_split hgen ε.w y.1 y'.1 hy _
    (GlobalTheory.TrueGeo.eqn (divOf C (expo Dw (w.mapDomain T.sym))) (GlobalTheory.TrueGeo.below y.1)) (prodPow t₀ (expo Dw w)) _
    (GlobalTheory.TrueGeo.eqn (divOf C' (expo Dw w)) (GlobalTheory.TrueGeo.below y'.1))
    (prod_relab T (Units.map (ψ : C'.Y.Fn →* C.Y.Fn)) t t₀ t' h5 hw)
    (unitAt_of_isEqn (GlobalTheory.TrueGeo.Base.isEqn_eqn _ _)
      (isEqn_sum (fun x : Pad.Letter Dw => C'.gr x.1 x.2) (expo Dw w) (fun x => t' x.1 x.2) fun x => ht' x.1 x.2))
    (unitAt_of_isEqn (GlobalTheory.TrueGeo.Base.isEqn_eqn _ _)
      (isEqn_sum (fun x : Pad.Letter Dw => C.gr x.1 x.2) (expo Dw (w.mapDomain T.sym)) (fun x => t x.1 x.2)
        fun x => ht x.1 x.2))
  delta lgFr
  exact add_mul_carry _ k1 k2

/- English proof (translation)
Use `delta lgOf lgFr`. Conclude with `dif_pos hp.out`.
-/
private theorem lgOf_eq_lgFr (C : FlagCpt Z e) (w : Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) [hp : Fact (resP v).Prime]
    (ε : GlobalTheory.TrueGeo.Ext v) (y : GlobalTheory.TrueGeo.AlgPt C.Y) :
    lgOf C w v ε y = lgFr C w v ε y (C.gr_spec (GlobalTheory.TrueGeo.below y.1)).choose_spec.choose
      (C.gr_spec (GlobalTheory.TrueGeo.below y.1)).choose_spec.choose_spec.choose := by
  delta lgOf lgFr
  exact dif_pos hp.out

end Carry

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Z T F _ _ e C C' φ ψ t₀ w hLn hInd hTri hLoc hw v ε y y' hy`. Use `haveI : Fact (resP v).Prime := ⟨prime_resP v⟩`. Take `⟨hφπ, hgen, hloc⟩` from `hLoc`. Establish `hy0 : GlobalTheory.TrueGeo.below y'.1 = φ.hom (GlobalTheory.TrueGeo.below y.1)`. Rewrite using `[GlobalTheory.TrueGeo.below, hy]`.

Conclude with `Scheme.Hom.comp_apply _ _ _`. Establish `hT'` using `(C'.gr_spec (GlobalTheory.TrueGeo.below y'.1)).choose_spec.choose_spec.choose_spec`. Take `⟨a, χ, f, t, h1, -, -, h4, h5, h6⟩` from `hloc _ _ _ _ _ hy0 hT'.1`. Establish `e1` using `hInd (w.mapDomain T.sym) v ε y χ f t (isLeft_mapDomain T hw) h4`. Establish `e2` using `lgOf_eq_lgFr C' w v ε y'`.

Establish `e3` using `lgFr_carry T C C' φ ψ t₀ w hLn hw v ε y y' hy hφπ hgen f t _ _ a h1 h5 h6 (hTri _ χ f t h4) hT'.2`. Conclude with `e1.trans (e3.trans (congrArg (· + _) e2.symm))`.
-/
theorem _root_.GlobalTheory.T.twisted_generic_relation_metric : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (T : Tw Z) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (C C' : FlagCpt Z e) (φ : C.Y.X ≅ C'.Y.X) (ψ : C'.Y.Fn →+* C.Y.Fn) (t₀ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ) (w : Sym E →₀ ℤ), T.LnPush → LgIndep C → TriEqn C → T.LocRel C C' φ ψ t₀ → (∀ a ∈ w.support, a.2.2.isLeft = true) → ∀ (v : HeightOneSpectrum (𝓞 F)) (ε : GlobalTheory.TrueGeo.Ext v) (y : GlobalTheory.TrueGeo.AlgPt C.Y) (y' : GlobalTheory.TrueGeo.AlgPt C'.Y), y'.1 = y.1 ≫ φ.hom → lgOf C (w.mapDomain T.sym) v ε y = lgOf C' w v ε y' + Real.log (ε.w (GlobalTheory.TrueGeo.valAt y.1 ((Units.map (ψ : C'.Y.Fn →* C.Y.Fn) (GlobalTheory.TrueGeo.eqn (divOf C' (expo Dw w)) (GlobalTheory.TrueGeo.below y'.1)) * prodPow t₀ (expo Dw w) * (GlobalTheory.TrueGeo.eqn (divOf C (expo Dw (w.mapDomain T.sym))) (GlobalTheory.TrueGeo.below y.1))⁻¹ : C.Y.Fnˣ) : C.Y.Fn))) := by
  intro E _ _ _ H Dw l Xo c O _ β Z T F _ _ e C C' φ ψ t₀ w hLn hInd hTri hLoc hw v ε y y' hy
  haveI : Fact (resP v).Prime := ⟨prime_resP v⟩
  obtain ⟨hφπ, hgen, hloc⟩ := hLoc
  have hy0 : GlobalTheory.TrueGeo.below y'.1 = φ.hom (GlobalTheory.TrueGeo.below y.1) := by
    rw [GlobalTheory.TrueGeo.below, hy]; exact Scheme.Hom.comp_apply _ _ _
  have hT' := (C'.gr_spec (GlobalTheory.TrueGeo.below y'.1)).choose_spec.choose_spec.choose_spec
  obtain ⟨a, χ, f, t, h1, -, -, h4, h5, h6⟩ := hloc _ _ _ _ _ hy0 hT'.1
  have e1 := hInd (w.mapDomain T.sym) v ε y χ f t (isLeft_mapDomain T hw) h4
  have e2 := lgOf_eq_lgFr C' w v ε y'
  have e3 := lgFr_carry T C C' φ ψ t₀ w hLn hw v ε y y' hy hφπ hgen f t _ _ a h1 h5 h6 (hTri _ χ f t h4) hT'.2
  exact e1.trans (e3.trans (congrArg (· + _) e2.symm))

end GlobalTheory.ShFam.GalCarry.LgCarry
