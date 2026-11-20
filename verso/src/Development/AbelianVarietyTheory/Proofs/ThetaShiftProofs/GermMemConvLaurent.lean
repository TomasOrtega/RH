import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumLocallyUniformlyOnTerm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSumsAtHalfCurveFraction

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcSectionValue

section General

variable {A B K : Type} [CommRing A] [CommRing B] [CommRing K] {Z : Scheme.{0}}

/- English proof (translation)
Take `⟨f, rfl⟩` from `Spec.map_surjective f`. Take `⟨g, rfl⟩` from `Spec.map_surjective g`. Rewrite `h` using `[spMap, ← Spec.map_comp, ← Spec.map_comp]`. Establish `h'` using `Spec.map_injective h`. Use `congr 1`.

Use extensionality with `a`. Conclude with `hρ (congrArg (fun q => q.hom a) h')`.
-/
theorem spMap_cancel {ρ : A →+* B} (hρ : Function.Injective ρ) {f g : Sp A ⟶ Sp K}
    (h : spMap ρ ≫ f = spMap ρ ≫ g) : f = g := by
  obtain ⟨f, rfl⟩ := Spec.map_surjective f
  obtain ⟨g, rfl⟩ := Spec.map_surjective g
  rw [spMap, ← Spec.map_comp, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  congr 1
  ext a
  exact hρ (congrArg (fun q => q.hom a) h')

/- English proof (translation)
Use `(HolHom.valR_appLE q p ⊤ U le_top _ h).trans ?_` and prove the remaining obligations. Rewrite using `[hq]`. Conclude with `Conv.valR_spMap_top f a`.
-/
theorem valR_const (p : Z ⟶ Sp K) (f : K →+* A) (q : Sp A ⟶ Z) (hq : q ≫ p = spMap f) (U : Z.Opens)
    (h : ⊤ ≤ q ⁻¹ᵁ U) (a : K) : valR q U (constFn p U a) = f a := by
  refine (HolHom.valR_appLE q p ⊤ U le_top _ h).trans ?_
  rw [hq]
  exact Conv.valR_spMap_top f a

/- English proof (translation)
Establish `: x (IsLocalRing.closedPoint A) ∈ ⨆ j, L.U j` using `hL.cover ▸ trivial`. Take `⟨j, hj⟩` from `TopologicalSpace.Opens.mem_iSup.1 this`. Conclude with `⟨j, ((IsLocalRing.closedPoint_mem_iff (x ⁻¹ᵁ L.U j)).1 hj).ge⟩`.
-/
theorem exists_chart_local [IsLocalRing A] (x : Sp A ⟶ Z) {L : LB Z} (hL : L.IsLB) : ∃ j, ⊤ ≤ x ⁻¹ᵁ L.U j := by
  have : x (IsLocalRing.closedPoint A) ∈ ⨆ j, L.U j := hL.cover ▸ trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 this
  exact ⟨j, ((IsLocalRing.closedPoint_mem_iff (x ⁻¹ᵁ L.U j)).1 hj).ge⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => ⟨fun _ hz => Set.mem_iInter.1 (h hz).1 PUnit.unit, fun _ hz => (h hz).2⟩, fun h _ hz => ⟨Set.mem_iInter.2 fun _ => h.1 hz, h.2 hz⟩⟩`.
-/
theorem le_div_iff {Z' : Scheme.{0}} (x : Sp A ⟶ Z') (φ : Z' ⟶ Z) (L : LB Z) (M : LB Z') (j : L.ι) (k : M.ι) :
    ⊤ ≤ x ⁻¹ᵁ (LB.div (L.pull φ) M).U (fun _ => j, k) ↔ ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U j ∧ ⊤ ≤ x ⁻¹ᵁ M.U k :=
  ⟨fun h => ⟨fun _ hz => Set.mem_iInter.1 (h hz).1 PUnit.unit, fun _ hz => (h hz).2⟩,
    fun h _ hz => ⟨Set.mem_iInter.2 fun _ => h.1 hz, h.2 hz⟩⟩

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `⟨w, k₁, hw, HEq.rfl, rfl, fun _ _ => rfl⟩`.
-/
theorem exists_rigIso_of_eq {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (m : CubeMap G' G) {L₁ L₂ : RigLB G'} (h : L₁ = L₂) (L : RigLB G)
    (w : LB.Iso L₁.L (L.L.pull m.F)) (hw : IsRigIso m L₁ L w) (k₁ : L₁.L.ι) :
    ∃ (w' : LB.Iso L₂.L (L.L.pull m.F)) (k₂ : L₂.L.ι), IsRigIso m L₂ L w' ∧ HEq k₁ k₂ ∧ L₁.L.U k₁ = L₂.L.U k₂ ∧
      ∀ (x : Sp A ⟶ G'.left) (j : L.L.ι),
        valR x _ (w.s (fun _ => j, k₁)).val = valR x _ (w'.s (fun _ => j, k₂)).val := by
  subst h
  exact ⟨w, k₁, hw, HEq.rfl, rfl, fun _ _ => rfl⟩

end General

section Germ

variable (Γ : Germs) (w : ℂ)

/- English proof (translation)
The claim follows from `IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by by_cases h : Γ.ev w a = 0 · exact Or.inr (Γ.unit w _ (by simp [h])) · exact Or.inl (Γ.unit w _ h)`.
-/
theorem isLocalRing_germ : IsLocalRing (Γ.R w) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    by_cases h : Γ.ev w a = 0
    · exact Or.inr (Γ.unit w _ (by simp [h]))
    · exact Or.inl (Γ.unit w _ h)

/- English proof (translation)
Take `⟨T, hw, a, s, hs, h⟩` from `Γ.frac w f`. Establish `hs' : (s : ℂ⸨X⸩) ≠ 0` using `fun e => hs (by rw [show s = 0 from Subtype.ext e, map_zero])`. Establish `: (f : ℂ⸨X⸩) = a / s` using `by rw [← h]; field_simp`. Rewrite using `[this]`. Conclude with `div_mem (Conv.halfRing_le_convLaurent T a.2) (Conv.halfRing_le_convLaurent T s.2)`.
-/
theorem germ_mem_convLaurent (f : Γ.R w) : (f : ℂ⸨X⸩) ∈ Conv.convLaurent := by
  obtain ⟨T, hw, a, s, hs, h⟩ := Γ.frac w f
  have hs' : (s : ℂ⸨X⸩) ≠ 0 := fun e => hs (by rw [show s = 0 from Subtype.ext e, map_zero])
  have : (f : ℂ⸨X⸩) = a / s := by rw [← h]; field_simp
  rw [this]
  exact div_mem (Conv.halfRing_le_convLaurent T a.2) (Conv.halfRing_le_convLaurent T s.2)

/- English proof (translation)
Use `haveI := isLocalRing_germ Γ w`. Use `haveI : IsLocalHom (Γ.ev w).toRingHom := ⟨fun a ha => Γ.unit w a ha.ne_zero⟩`. Use `((IsLocalRing.closedPoint_mem_iff (x ⁻¹ᵁ U)).1 ?_).ge` and prove the remaining obligations. Use `h (x := IsLocalRing.closedPoint ℂ) trivial` as an intermediate fact. Rewrite using `[← IsLocalRing.comap_closedPoint (Γ.ev w).toRingHom]`.

Conclude with `this`.
-/
theorem le_of_ev {Z : Scheme.{0}} (x : Sp (Γ.R w) ⟶ Z) {U : Z.Opens}
    (h : ⊤ ≤ (spMap (Γ.ev w).toRingHom ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  haveI := isLocalRing_germ Γ w
  haveI : IsLocalHom (Γ.ev w).toRingHom := ⟨fun a ha => Γ.unit w a ha.ne_zero⟩
  refine ((IsLocalRing.closedPoint_mem_iff (x ⁻¹ᵁ U)).1 ?_).ge
  have := h (x := IsLocalRing.closedPoint ℂ) trivial
  rw [← IsLocalRing.comap_closedPoint (Γ.ev w).toRingHom]
  exact this

end Germ

/- English proof (translation)
Establish `hfac : spMap (Conv.halfRing T).val.toRingHom ≫ yT = spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) ≫ (spMap (Conv.halfIncl T : Conv.halfRing T →+* Conv.convLaurent) ≫ yT)`. Rewrite using `[← Category.assoc, ← spMap_comp]`. Both sides reduce to the same expression. Use `Conv.exists_le_preimage_inclusion yT fun p _ => ?_` and prove the remaining obligations. Rewrite `hU` using `[hfac]`.

Take `rfl : p = spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) (default : PrimeSpectrum ℂ⸨X⸩)` from `Subsingleton.elim (α := PrimeSpectrum Conv.convLaurent) _ _`. Conclude with `hU (x := (default : PrimeSpectrum ℂ⸨X⸩)) trivial`.
-/
theorem exists_le_halfPlane {Z : Scheme.{0}} {T : ℝ} (yT : Sp (Conv.halfRing T) ⟶ Z) {U : Z.Opens}
    (hU : ⊤ ≤ (spMap (Conv.halfRing T).val.toRingHom ≫ yT) ⁻¹ᵁ U) :
    ∃ (T' : ℝ) (h : T ≤ T'), ⊤ ≤ (spMap (Subalgebra.inclusion (Conv.halfRing_mono h) :
      Conv.halfRing T →+* Conv.halfRing T') ≫ yT) ⁻¹ᵁ U := by
  have hfac : spMap (Conv.halfRing T).val.toRingHom ≫ yT =
      spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) ≫
        (spMap (Conv.halfIncl T : Conv.halfRing T →+* Conv.convLaurent) ≫ yT) := by
    rw [← Category.assoc, ← spMap_comp]
    rfl
  refine Conv.exists_le_preimage_inclusion yT fun p _ => ?_
  rw [hfac] at hU
  obtain rfl : p = spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) (default : PrimeSpectrum ℂ⸨X⸩) :=
    Subsingleton.elim (α := PrimeSpectrum Conv.convLaurent) _ _
  exact hU (x := (default : PrimeSpectrum ℂ⸨X⸩)) trivial

/- English proof (translation)
Take `⟨z, hz⟩` from `Function.ne_iff.1 h`. Use `⟨(0, z), fun e => hz ?_⟩` and prove the remaining obligations. Establish `hl : A.level 1 0 0 = {0}`. Use extensionality with `m`. Rewrite using `[AnArc.mem_level, Finset.mem_singleton]`.

Establish `h2` using `A.two_mul_exponent 1 0 m`. Use `⟨fun h0 => by_contra fun hm => ?_, fun h0 => by simp [h0, AnArc.exponent]⟩` and prove the remaining obligations. Use `A.be_pos m hm` as an intermediate fact. Simplify using `[h0] at h2`. Use linear arithmetic over natural numbers and integers.

Use `A.coeff_FSum 1 0 θ (0, z) 0` as an intermediate fact. Rewrite `this` using `[e, hl]`. Simplify `this.symm` using `[AnArc.term]`.
-/
theorem exists_fsum_ne_zero {O : Type} [CommRing O] [StarRing O] (A : AnArc O) {θ : (Fin A.gB → ℂ) → ℂ} (h : θ ≠ 0) :
    ∃ v, A.FSum 1 0 θ v ≠ 0 := by
  obtain ⟨z, hz⟩ := Function.ne_iff.1 h
  refine ⟨(0, z), fun e => hz ?_⟩
  have hl : A.level 1 0 0 = {0} := by
    ext m
    rw [AnArc.mem_level, Finset.mem_singleton]
    have h2 := A.two_mul_exponent 1 0 m
    refine ⟨fun h0 => by_contra fun hm => ?_, fun h0 => by simp [h0, AnArc.exponent]⟩
    have := A.be_pos m hm
    simp [h0] at h2
    omega
  have := A.coeff_FSum 1 0 θ (0, z) 0
  rw [e, hl] at this
  simpa [AnArc.term] using this.symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

/- English proof (translation)
Establish `hb : spMap (Conv.halfRing Ψ.T).val.toRingHom ≫ spMap ((algebraMap ℂ (Conv.halfRing Ψ.T)).comp bF) = yF ≫ pullback.snd _ _`. Rewrite using `[hover, ← spMap_comp]`. Both sides reduce to the same expression. Establish `hs : Ψ.yT ≫ Xo.s = spMap ((algebraMap ℂ (Conv.halfRing Ψ.T)).comp bF) ≫ spMap (IntermediateField.inclusion c.le).toRingHom`. Use `spMap_cancel (ρ := (Conv.halfRing Ψ.T).val.toRingHom) Subtype.val_injective ?_` and prove the remaining obligations.

Rewrite using `[← Category.assoc, Ψ.yT_gen, ← Category.assoc, hb, Category.assoc, Category.assoc, pullback.condition]`. Set `yT : Sp (Conv.halfRing Ψ.T) ⟶ Xo.XF c` to `pullback.lift _ _ hs`. Establish `h1 : yT ≫ pullback.fst _ _ = Ψ.yT` using `pullback.lift_fst _ _ _`. Establish `h2 : yT ≫ pullback.snd _ _ = spMap ((algebraMap ℂ (Conv.halfRing Ψ.T)).comp bF)` using `pullback.lift_snd _ _ _`. Establish `hg : spMap (Conv.halfRing Ψ.T).val.toRingHom ≫ yT = yF`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, h1, Ψ.yT_gen]`. Rewrite using `[Category.assoc, h2, hb]`. Take `⟨T₁, hT, hU₁⟩` from `exists_le_halfPlane yT (hg ▸ hU)`. Use `⟨T₁, fun w hw₁ => ⟨hT.trans_lt hw₁, fun v => ?_⟩⟩` and prove the remaining obligations.

Use `set hw := hT.trans_lt hw₁`. Establish `hP` using `Y.m0.cart.1`. Establish `hc : (Ψ.xt w hw v).left ≫ Xo.univ.t.G.hom = (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ yT) ≫ pullback.fst _ _`. Rewrite using `[Category.assoc, h1]`. Conclude with `Over.w (Ψ.xt w hw v)`.

Establish `e1` using `hP.lift_fst _ _ hc`. Establish `e2` using `hP.lift_snd _ _ hc`. Use `⟨hP.lift _ _ hc, e1, ?_, ?_, fun x hx1 hx2 => ?_⟩` and prove the remaining obligations. Apply `hP.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, e1, Ψ.xt_gen]`.

Conclude with `(hx v).symm`. Rewrite using `[Category.assoc, e2, ← Category.assoc, ← spMap_comp]`. Conclude with `hg.trans (Over.w (ΦF.x v)).symm`. Rewrite using `[e2]`. Establish `: spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom = spMap (Subalgebra.inclusion (Γ.le T₁ w hw₁)).toRingHom ≫ spMap (Subalgebra.inclusion (Conv.halfRing_mono hT) : Conv.halfRing Ψ.T →+* Conv.halfRing T₁)`.

Rewrite using `[← spMap_comp]`. Both sides reduce to the same expression. Rewrite using `[this, Category.assoc]`. Conclude with `FormalValue.top_le_comp hU₁ _`. Establish `e3 : x ≫ Y.m0.toSABMap.φ = (spMap (Γ.ev w).toRingHom ≫ hP.lift _ _ hc) ≫ Y.m0.toSABMap.φ`.

Rewrite using `[hx1, Ψ.pi_eq w hw v, Category.assoc]`. Conclude with `congrArg _ e1.symm`. Use `hP.hom_ext e3 (pullback.hom_ext ?_ ?_)` and prove the remaining obligations. Rewrite using `[Category.assoc, ← hP.w, ← Category.assoc, Category.assoc _ _ (pullback.fst _ _), ← hP.w, ← Category.assoc]`. Conclude with `congrArg (· ≫ Xo.univ.t.G.hom) e3`.

Rewrite using `[Category.assoc, hx2, Category.assoc, Category.assoc, reassoc_of% e2, h2, ← spMap_comp, ← spMap_comp]`. Use `congr 1`. Use extensionality with `a`. Conclude with `((Γ.ev w).commutes (bF a)).symm`.
-/
theorem exists_germ_lift (Y : Model Xo c β) (bF : c.F →+* ℂ) {A : AnArc (𝓞 E)} {yF : Sp ℂ⸨X⸩ ⟶ Xo.XF c}
    (hover : yF ≫ pullback.snd _ _ = spMap ((algebraMap ℂ ℂ⸨X⸩).comp bF))
    (ΦF : GenPts A Y.oF.t yF) {Φ : GenPts A Xo.univ.t (yF ≫ pullback.fst _ _)}
    (hx : ∀ v, (ΦF.x v).left ≫ Y.m0.toSABMap.φ = (Φ.x v).left) {Γ : Germs} (Ψ : SpecPts Φ Γ)
    (U : (Xo.XF c).Opens) (hU : ⊤ ≤ yF ⁻¹ᵁ U) :
    ∃ T₁ : ℝ, ∀ w : ℂ, T₁ < w.im → ∃ hw : Ψ.T < w.im, ∀ v, ∃ xg : Sp (Γ.R w) ⟶ Y.oF.t.G.left,
      xg ≫ Y.m0.toSABMap.φ = (Ψ.xt w hw v).left ∧ spMap (Γ.R w).val.toRingHom ≫ xg = (ΦF.x v).left ∧
      ⊤ ≤ (xg ≫ Y.oF.t.G.hom) ⁻¹ᵁ U ∧
      ∀ x : Sp ℂ ⟶ Y.oF.t.G.left, x ≫ Y.m0.toSABMap.φ = (Ψ.pi w v).left →
        x ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap bF → x = spMap (Γ.ev w).toRingHom ≫ xg := by
  have hb : spMap (Conv.halfRing Ψ.T).val.toRingHom ≫ spMap ((algebraMap ℂ (Conv.halfRing Ψ.T)).comp bF) =
      yF ≫ pullback.snd _ _ := by
    rw [hover, ← spMap_comp]; rfl
  have hs : Ψ.yT ≫ Xo.s = spMap ((algebraMap ℂ (Conv.halfRing Ψ.T)).comp bF) ≫
      spMap (IntermediateField.inclusion c.le).toRingHom := by
    refine spMap_cancel (ρ := (Conv.halfRing Ψ.T).val.toRingHom) Subtype.val_injective ?_
    rw [← Category.assoc, Ψ.yT_gen, ← Category.assoc, hb, Category.assoc, Category.assoc, pullback.condition]
  let yT : Sp (Conv.halfRing Ψ.T) ⟶ Xo.XF c := pullback.lift _ _ hs
  have h1 : yT ≫ pullback.fst _ _ = Ψ.yT := pullback.lift_fst _ _ _
  have h2 : yT ≫ pullback.snd _ _ = spMap ((algebraMap ℂ (Conv.halfRing Ψ.T)).comp bF) := pullback.lift_snd _ _ _
  have hg : spMap (Conv.halfRing Ψ.T).val.toRingHom ≫ yT = yF := by
    apply pullback.hom_ext
    · rw [Category.assoc, h1, Ψ.yT_gen]
    · rw [Category.assoc, h2, hb]
  obtain ⟨T₁, hT, hU₁⟩ := exists_le_halfPlane yT (hg ▸ hU)
  refine ⟨T₁, fun w hw₁ => ⟨hT.trans_lt hw₁, fun v => ?_⟩⟩
  set hw := hT.trans_lt hw₁
  have hP := Y.m0.cart.1
  have hc : (Ψ.xt w hw v).left ≫ Xo.univ.t.G.hom =
      (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ yT) ≫ pullback.fst _ _ := by
    rw [Category.assoc, h1]
    exact Over.w (Ψ.xt w hw v)
  have e1 := hP.lift_fst _ _ hc
  have e2 := hP.lift_snd _ _ hc
  refine ⟨hP.lift _ _ hc, e1, ?_, ?_, fun x hx1 hx2 => ?_⟩
  · apply hP.hom_ext
    · rw [Category.assoc, e1, Ψ.xt_gen]
      exact (hx v).symm
    · rw [Category.assoc, e2, ← Category.assoc, ← spMap_comp]
      exact hg.trans (Over.w (ΦF.x v)).symm
  · rw [e2]
    have : spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom =
        spMap (Subalgebra.inclusion (Γ.le T₁ w hw₁)).toRingHom ≫ spMap (Subalgebra.inclusion (Conv.halfRing_mono hT) :
          Conv.halfRing Ψ.T →+* Conv.halfRing T₁) := by
      rw [← spMap_comp]; rfl
    rw [this, Category.assoc]
    exact FormalValue.top_le_comp hU₁ _
  · have e3 : x ≫ Y.m0.toSABMap.φ = (spMap (Γ.ev w).toRingHom ≫ hP.lift _ _ hc) ≫ Y.m0.toSABMap.φ := by
      rw [hx1, Ψ.pi_eq w hw v, Category.assoc]
      exact congrArg _ e1.symm
    refine hP.hom_ext e3 (pullback.hom_ext ?_ ?_)
    · rw [Category.assoc, ← hP.w, ← Category.assoc, Category.assoc _ _ (pullback.fst _ _), ← hP.w, ← Category.assoc]
      exact congrArg (· ≫ Xo.univ.t.G.hom) e3
    · rw [Category.assoc, hx2, Category.assoc, Category.assoc, reassoc_of% e2, h2, ← spMap_comp, ← spMap_comp]
      congr 1
      ext a
      exact ((Γ.ev w).commutes (bF a)).symm

end GlobalTheory.ArcSectionValue
