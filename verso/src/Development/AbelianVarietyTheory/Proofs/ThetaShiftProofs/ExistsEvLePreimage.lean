import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSumsAtHalfCurveFraction

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.SpecCoord

/- English proof (translation)
Introduce `q _`. Set `p : PrimeSpectrum (Γ.R w)` to `spMap (Γ.ev w).toRingHom (default : PrimeSpectrum ℂ)`. Establish `hp : p ∈ (show Set (PrimeSpectrum (Γ.R w)) from (x ⁻¹ᵁ U).carrier)` using `h (x := (default : PrimeSpectrum ℂ)) trivial`. Establish `hle : (show PrimeSpectrum (Γ.R w) from q) ≤ p`. Introduce `s hs`.

Assume the negation of the conclusion as `hn`. Use `(show PrimeSpectrum (Γ.R w) from q).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hs (Γ.unit w s fun h0 => hn ?_))` and prove the remaining obligations. Use `show (Γ.ev w).toRingHom s ∈ (default : PrimeSpectrum ℂ).asIdeal`. Rewrite using `[show (Γ.ev w).toRingHom s = 0 from h0]`. Conclude with `zero_mem _`.

Conclude with `((PrimeSpectrum.le_iff_specializes _ _).1 hle).mem_open (x ⁻¹ᵁ U).isOpen hp`.
-/
theorem germ_le_preimage (Γ : Germs) (w : ℂ) {Z : Scheme.{0}} (x : Sp (Γ.R w) ⟶ Z) (U : Z.Opens)
    (h : ⊤ ≤ (spMap (Γ.ev w).toRingHom ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  intro q _
  let p : PrimeSpectrum (Γ.R w) := spMap (Γ.ev w).toRingHom (default : PrimeSpectrum ℂ)
  have hp : p ∈ (show Set (PrimeSpectrum (Γ.R w)) from (x ⁻¹ᵁ U).carrier) :=
    h (x := (default : PrimeSpectrum ℂ)) trivial
  have hle : (show PrimeSpectrum (Γ.R w) from q) ≤ p := by
    intro s hs
    by_contra hn
    refine (show PrimeSpectrum (Γ.R w) from q).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ hs (Γ.unit w s fun h0 => hn ?_))
    show (Γ.ev w).toRingHom s ∈ (default : PrimeSpectrum ℂ).asIdeal
    rw [show (Γ.ev w).toRingHom s = 0 from h0]
    exact zero_mem _
  exact ((PrimeSpectrum.le_iff_specializes _ _).1 hle).mem_open (x ⁻¹ᵁ U).isOpen hp

/- English proof (translation)
Introduce `p _` and use `h (x := g p) trivial`.
-/
theorem comp_le_preimage {X Y Z : Scheme.{0}} (g : X ⟶ Y) (x : Y ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    ⊤ ≤ (g ≫ x) ⁻¹ᵁ U := fun p _ => h (x := g p) trivial

/- English proof (translation)
Establish `hfac : spMap (Conv.halfRing T).val.toRingHom ≫ yT = spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) ≫ (spMap (Conv.halfIncl T : Conv.halfRing T →+* Conv.convLaurent) ≫ yT)`. Rewrite using `[← Category.assoc, ← spMap_comp]`. Both sides reduce to the same expression. Establish `hU' : ⊤ ≤ (spMap (Conv.halfIncl T : Conv.halfRing T →+* Conv.convLaurent) ≫ yT) ⁻¹ᵁ U`. Introduce `p _`.

Rewrite `hU` using `[hfac]`. Take `rfl : p = spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) (default : PrimeSpectrum ℂ⸨X⸩)` from `Subsingleton.elim (α := PrimeSpectrum Conv.convLaurent) _ _`. Conclude with `hU (x := (default : PrimeSpectrum ℂ⸨X⸩)) trivial`. Take `⟨T', h, hT'⟩` from `Conv.exists_le_preimage_inclusion yT hU'`. Use `⟨T', h, fun w hw' hw => ?_⟩` and prove the remaining obligations.

Establish `e : (Conv.ev T w hw).toRingHom = (Conv.ev T' w hw').toRingHom.comp (Subalgebra.inclusion (Conv.halfRing_mono h) : Conv.halfRing T →+* Conv.halfRing T')` using `RingHom.ext fun r => Conv.ev_congr hw hw' rfl`. Rewrite using `[e, spMap_comp, Category.assoc]`. Conclude with `comp_le_preimage _ _ _ hT'`.
-/
theorem exists_ev_le_preimage {Z : Scheme.{0}} {T : ℝ} (yT : Sp (Conv.halfRing T) ⟶ Z) (U : Z.Opens)
    (hU : ⊤ ≤ (spMap (Conv.halfRing T).val.toRingHom ≫ yT) ⁻¹ᵁ U) :
    ∃ T' ≥ T, ∀ w : ℂ, T' < w.im → ∀ hw : T < w.im, ⊤ ≤ (spMap (Conv.ev T w hw).toRingHom ≫ yT) ⁻¹ᵁ U := by
  have hfac : spMap (Conv.halfRing T).val.toRingHom ≫ yT =
      spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) ≫
        (spMap (Conv.halfIncl T : Conv.halfRing T →+* Conv.convLaurent) ≫ yT) := by
    rw [← Category.assoc, ← spMap_comp]
    rfl
  have hU' : ⊤ ≤ (spMap (Conv.halfIncl T : Conv.halfRing T →+* Conv.convLaurent) ≫ yT) ⁻¹ᵁ U := by
    intro p _
    rw [hfac] at hU
    obtain rfl : p = spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) (default : PrimeSpectrum ℂ⸨X⸩) :=
      Subsingleton.elim (α := PrimeSpectrum Conv.convLaurent) _ _
    exact hU (x := (default : PrimeSpectrum ℂ⸨X⸩)) trivial
  obtain ⟨T', h, hT'⟩ := Conv.exists_le_preimage_inclusion yT hU'
  refine ⟨T', h, fun w hw' hw => ?_⟩
  have e : (Conv.ev T w hw).toRingHom = (Conv.ev T' w hw').toRingHom.comp
      (Subalgebra.inclusion (Conv.halfRing_mono h) : Conv.halfRing T →+* Conv.halfRing T') :=
    RingHom.ext fun r => Conv.ev_congr hw hw' rfl
  rw [e, spMap_comp, Category.assoc]
  exact comp_le_preimage _ _ _ hT'

/- English proof (translation)
Introduce `E _ _ _ H _ D l B _ bb S _ s o A y Φ Γ Ψ N _ C`. Take `⟨T₁, hT₁, hU⟩` from `exists_ev_le_preimage Ψ.yT C.U (by rw [Ψ.yT_gen]; exact C.mem)`. Use `⟨max T₁ C.T, le_max_of_le_left hT₁, le_max_right _ _, fun w hw => ?_⟩` and prove the remaining obligations. Establish `hw1 : T₁ < w.im` using `(le_max_left _ _).trans_lt hw`. Establish `hwC : C.T < w.im` using `(le_max_right _ _).trans_lt hw`.

Establish `hwT : Ψ.T < w.im` using `lt_of_le_of_lt hT₁ hw1`. Establish `hy : ⊤ ≤ Ψ.yw w ⁻¹ᵁ C.U`. Rewrite using `[Ψ.yw_eq w hwT]`. Conclude with `hU w hw1 hwT`. Establish `hg : ⊤ ≤ (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hwT)).toRingHom ≫ Ψ.yT) ⁻¹ᵁ C.U`.

Apply `germ_le_preimage` to reduce the goal to its premises. Establish `e : (Γ.ev w).toRingHom.comp (Subalgebra.inclusion (Γ.le Ψ.T w hwT)).toRingHom = (Conv.ev Ψ.T w hwT).toRingHom` using `RingHom.ext fun r => Γ.ev_eq Ψ.T w hwT r`. Rewrite using `[← Category.assoc, ← spMap_comp, e, ← Ψ.yw_eq w hwT]`. Conclude with `hy`. Use `⟨hy, fun _ => hg, fun i v x' j hx' hj => ?_⟩` and prove the remaining obligations.

Establish `hxU : ⊤ ≤ (Ψ.xt w hwT v).left ⁻¹ᵁ (o.t.G.hom ⁻¹ᵁ C.U)`. Rewrite using `[← Scheme.Hom.comp_preimage, Over.w]`. Conclude with `hg`. Establish `hxj : ⊤ ≤ (Ψ.xt w hwT v).left ⁻¹ᵁ o.t.PP.L.U j`. Apply `germ_le_preimage` to reduce the goal to its premises.

Rewrite using `[← Ψ.pi_eq w hwT v]`. Conclude with `hj`. Take `⟨z, hz⟩ : ∃ z : Sp (Γ.R w) ⟶ (o.t.G.hom ⁻¹ᵁ C.U).toScheme, z ≫ (o.t.G.hom ⁻¹ᵁ C.U).ι = (Ψ.xt w hwT v).left` from `⟨IsOpenImmersion.lift (o.t.G.hom ⁻¹ᵁ C.U).ι (Ψ.xt w hwT v).left (by`. Introduce and unpack `_ ⟨p, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`.

Conclude with `hxU (x := p) trivial), IsOpenImmersion.lift_fac _ _ _⟩`. Establish `hzj : ⊤ ≤ z ⁻¹ᵁ (Out.powOver o.t.G o.t.PP.L C.U N).U (fun _ => j)`. Introduce `p _`. Rewrite `hxj` using `[← hz]`. Conclude with `Set.mem_iInter.2 fun _ => hxj (x := p) trivial`.

Establish `ex : x' = spMap (Γ.ev w).toRingHom ≫ z`. Rewrite using `[← cancel_mono (o.t.G.hom ⁻¹ᵁ C.U).ι, hx', Category.assoc, hz, Ψ.pi_eq w hwT v]`. Establish `hgen : (spMap (Γ.R w).val.toRingHom ≫ z) ≫ (o.t.G.hom ⁻¹ᵁ C.U).ι = (Φ.x v).left`. Rewrite using `[Category.assoc, hz, Ψ.xt_gen]`. Establish `hv` using `C.val i v _ j hgen (by rw [← Ψ.xt_gen w hwT v]; exact comp_le_preimage _ _ _ hxj)`.

Rewrite `hv` using `[HolHom.valR_spMap _ _ _ hzj, ← Ψ.τt_gen w hwT v j hxj]`. Establish `hr : valR z ((Out.powOver o.t.G o.t.PP.L C.U N).U (fun _ => j)) ((C.b i).f (fun _ => j)) = Subalgebra.inclusion (Γ.le C.T w hwC) (C.cf i v) * Ψ.τt w v j ^ N` using `Subtype.ext hv`. Rewrite using `[ex, HolHom.valR_spMap _ _ _ hzj, hr, map_mul, map_pow]`. Conclude with `congrArg (· * _) (Γ.ev_eq C.T w hwC (C.cf i v))`.
-/
theorem spec_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ), ∀ (N : ℕ) [NeZero N] (C : Coords Φ N), ∃ T' ≥ Ψ.T, ∃ hT : C.T ≤ T', ∀ w (hw : T' < w.im), ⊤ ≤ Ψ.yw w ⁻¹ᵁ C.U ∧ (∀ hw', ⊤ ≤ (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw')).toRingHom ≫ Ψ.yT) ⁻¹ᵁ C.U) ∧ ∀ i v (x' : Sp ℂ ⟶ (o.t.G.hom ⁻¹ᵁ C.U).toScheme) (j : o.t.PP.L.ι), x' ≫ (o.t.G.hom ⁻¹ᵁ C.U).ι = (Ψ.pi w v).left → ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ o.t.PP.L.U j → valR x' ((Out.powOver o.t.G o.t.PP.L C.U N).U (fun _ => j)) ((C.b i).f (fun _ => j)) = Conv.ev C.T w (lt_of_le_of_lt hT hw) (C.cf i v) * Ψ.fr w j v ^ N := by
  intro E _ _ _ H _ D l B _ bb S _ s o A y Φ Γ Ψ N _ C
  obtain ⟨T₁, hT₁, hU⟩ := exists_ev_le_preimage Ψ.yT C.U (by rw [Ψ.yT_gen]; exact C.mem)
  refine ⟨max T₁ C.T, le_max_of_le_left hT₁, le_max_right _ _, fun w hw => ?_⟩
  have hw1 : T₁ < w.im := (le_max_left _ _).trans_lt hw
  have hwC : C.T < w.im := (le_max_right _ _).trans_lt hw
  have hwT : Ψ.T < w.im := lt_of_le_of_lt hT₁ hw1
  have hy : ⊤ ≤ Ψ.yw w ⁻¹ᵁ C.U := by
    rw [Ψ.yw_eq w hwT]
    exact hU w hw1 hwT
  have hg : ⊤ ≤ (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hwT)).toRingHom ≫ Ψ.yT) ⁻¹ᵁ C.U := by
    apply germ_le_preimage
    have e : (Γ.ev w).toRingHom.comp (Subalgebra.inclusion (Γ.le Ψ.T w hwT)).toRingHom =
        (Conv.ev Ψ.T w hwT).toRingHom := RingHom.ext fun r => Γ.ev_eq Ψ.T w hwT r
    rw [← Category.assoc, ← spMap_comp, e, ← Ψ.yw_eq w hwT]
    exact hy
  refine ⟨hy, fun _ => hg, fun i v x' j hx' hj => ?_⟩
  have hxU : ⊤ ≤ (Ψ.xt w hwT v).left ⁻¹ᵁ (o.t.G.hom ⁻¹ᵁ C.U) := by
    rw [← Scheme.Hom.comp_preimage, Over.w]
    exact hg
  have hxj : ⊤ ≤ (Ψ.xt w hwT v).left ⁻¹ᵁ o.t.PP.L.U j := by
    apply germ_le_preimage
    rw [← Ψ.pi_eq w hwT v]
    exact hj
  obtain ⟨z, hz⟩ : ∃ z : Sp (Γ.R w) ⟶ (o.t.G.hom ⁻¹ᵁ C.U).toScheme,
      z ≫ (o.t.G.hom ⁻¹ᵁ C.U).ι = (Ψ.xt w hwT v).left :=
    ⟨IsOpenImmersion.lift (o.t.G.hom ⁻¹ᵁ C.U).ι (Ψ.xt w hwT v).left (by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hxU (x := p) trivial), IsOpenImmersion.lift_fac _ _ _⟩
  have hzj : ⊤ ≤ z ⁻¹ᵁ (Out.powOver o.t.G o.t.PP.L C.U N).U (fun _ => j) := by
    intro p _
    rw [← hz] at hxj
    exact Set.mem_iInter.2 fun _ => hxj (x := p) trivial
  have ex : x' = spMap (Γ.ev w).toRingHom ≫ z := by
    rw [← cancel_mono (o.t.G.hom ⁻¹ᵁ C.U).ι, hx', Category.assoc, hz, Ψ.pi_eq w hwT v]
  have hgen : (spMap (Γ.R w).val.toRingHom ≫ z) ≫ (o.t.G.hom ⁻¹ᵁ C.U).ι = (Φ.x v).left := by
    rw [Category.assoc, hz, Ψ.xt_gen]
  have hv := C.val i v _ j hgen (by rw [← Ψ.xt_gen w hwT v]; exact comp_le_preimage _ _ _ hxj)
  rw [HolHom.valR_spMap _ _ _ hzj, ← Ψ.τt_gen w hwT v j hxj] at hv
  have hr : valR z ((Out.powOver o.t.G o.t.PP.L C.U N).U (fun _ => j)) ((C.b i).f (fun _ => j)) =
      Subalgebra.inclusion (Γ.le C.T w hwC) (C.cf i v) * Ψ.τt w v j ^ N := Subtype.ext hv
  rw [ex, HolHom.valR_spMap _ _ _ hzj, hr, map_mul, map_pow]
  exact congrArg (· * _) (Γ.ev_eq C.T w hwC (C.cf i v))

end GlobalTheory.SpecCoord
