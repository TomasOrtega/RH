import Formalism.SharpRestriction.LevelLetterCocycles.FinalLevelsOf

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}

/- English proof (translation)
Establish `h : ∀ y, ιV PD (LL` using `LL) (V := T.V) y = ((PD.ι.toLinearMap.restrictScalars Qp).lTensor T.V) y := fun y => by`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x b => simp [ιV]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.

Establish `hi : Function.Injective (PD.ι.toLinearMap.restrictScalars Qp)` using `PD.ι_inj`. Introduce `a b hab`. Rewrite `hab` using `[h, h]`. Conclude with `Module.Flat.lTensor_preserves_injective_linearMap _ hi hab`.
-/
theorem Pf_MapLoc_ιV_inj (T : LocLat G Qp LL O) : Function.Injective (ιV PD (LL := LL) (V := T.V)) := by
  have h : ∀ y, ιV PD (LL := LL) (V := T.V) y =
      ((PD.ι.toLinearMap.restrictScalars Qp).lTensor T.V) y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [ιV]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hi : Function.Injective (PD.ι.toLinearMap.restrictScalars Qp) := PD.ι_inj
  intro a b hab
  rw [h, h] at hab
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hi hab

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x b => simp [ιV]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem Pf_MapLoc_ιV_map {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (y : T₁.V ⊗[Qp] B) :
    AlgebraTensorModule.map F.f (LinearMap.id : BdR →ₗ[Qp] BdR) (ιV PD (LL := LL) (V := T₁.V) y) =
      ιV PD (LL := LL) (V := T₂.V) (AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp [ιV]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Apply `Pf_MapLoc_ιV_inj (PD := PD) T₂` to reduce the goal to its premises. Rewrite using `[← levN_eq, W.levN_map F crys₁ crys₂ i ζ x hx k, levN_eq, Pf_MapLoc_ιV_map]`.
-/
theorem Pf_MapLoc_levB_map {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (crys₁ : IsCrys PD T₁.ρ) (crys₂ : IsCrys PD T₂.ρ)
    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (i : ZMod n) (ζ : LL) (x : ↥(W.N T₁)) (hx : W.map F (x : W.DD T₁) ∈ W.N T₂) (k : ℤ) :
    Lb.levB T₂ i ζ ⟨W.map F (x : W.DD T₁), hx⟩ k =
      AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B) (Lb.levB T₁ i ζ x k) := by
  apply Pf_MapLoc_ιV_inj (PD := PD) T₂
  rw [← levN_eq, W.levN_map F crys₁ crys₂ i ζ x hx k, levN_eq, Pf_MapLoc_ιV_map]

/- English proof (translation)
Take `⟨y, rfl⟩` from `(TensorProduct.piScalarRight LL LL D₁ (Rs LL PD.p s)).surjective f`. Establish `h1 : (fun ζ => g (TensorProduct.piScalarRight LL LL D₁ (Rs LL PD.p s) y ζ)) = TensorProduct.piScalarRight LL LL D₂ (Rs LL PD.p s) (g.rTensor _ y)`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => funext ζ`. Simplify using the standard rewrite rules.

Consider the case `tmul x a => funext ζ`. Simplify using the standard rewrite rules. Consider the case `add y y' hy hy'`. Use function extensionality and compare the values at `ζ`. Establish `e1` using `congrFun hy ζ`.

Establish `e2` using `congrFun hy' ζ`. Simplify using `only [map_add, Pi.add_apply] at e1 e2 ⊢`. Rewrite using `[e1, e2]`. Simplify using `only [toKsD, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.symm_apply_apply]`. Rewrite using `[h1, LinearEquiv.symm_apply_apply]`.

Use `clear h1`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x a => simp [LinearMap.baseChange_tmul]`. Consider the case `add y y' hy hy' => simp only [map_add, hy, hy']`.
-/
theorem Pf_MapLoc_toKsD_map (s : ℕ) {D₁ D₂ : Type} [AddCommGroup D₁] [Module LL D₁]
    [AddCommGroup D₂] [Module LL D₂] (g : D₁ →ₗ[LL] D₂) (f : Rs LL PD.p s → D₁) :
    g.baseChange (KsW W s) (toKsD W s D₁ f) = toKsD W s D₂ (fun ζ => g (f ζ)) := by
  classical
  obtain ⟨y, rfl⟩ := (TensorProduct.piScalarRight LL LL D₁ (Rs LL PD.p s)).surjective f
  have h1 : (fun ζ => g (TensorProduct.piScalarRight LL LL D₁ (Rs LL PD.p s) y ζ)) =
      TensorProduct.piScalarRight LL LL D₂ (Rs LL PD.p s) (g.rTensor _ y) := by
    induction y using TensorProduct.induction_on with
    | zero => funext ζ; simp
    | tmul x a => funext ζ; simp
    | add y y' hy hy' =>
      funext ζ
      have e1 := congrFun hy ζ
      have e2 := congrFun hy' ζ
      simp only [map_add, Pi.add_apply] at e1 e2 ⊢
      rw [e1, e2]
  simp only [toKsD, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.symm_apply_apply]
  rw [h1, LinearEquiv.symm_apply_apply]
  clear h1
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x a => simp [LinearMap.baseChange_tmul]
  | add y y' hy hy' => simp only [map_add, hy, hy']

/- English proof (translation)
Establish `hc : ∀ k, (dmapOf h).baseChange (KsW W s) (coefN Lb s T₁ c x k) = coefN Lb s T₂ c y k`. Introduce `k`. Simplify using `only [coefN]`. Rewrite using `[Pf_MapLoc_toKsD_map]`. Use `congr 1`.

Use function extensionality and compare the values at `ζ`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `(hxy ζ.1 k).symm`. Apply `(HahnModule.of (KsW W s)).symm.injective` to reduce the goal to its premises. Use extensionality with `k`.

Simplify using `[ambF, ambMap, expN, HahnSeries.ofSuppBddBelow, hc]`.
-/
theorem Pf_MapLoc_ambF_expN (s : ℕ) {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L} {c : ZMod n}
    (h : MemD W F c) (x : ↥(W.N T₁)) (y : ↥(W.N T₂))
    (hxy : ∀ (ζ : LL) (k : ℤ), Lb.levB T₂ c ζ y k =
      AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B) (Lb.levB T₁ c ζ x k)) :
    ambF h s (expN Lb s T₁ c x) = expN Lb s T₂ c y := by
  have hc : ∀ k, (dmapOf h).baseChange (KsW W s) (coefN Lb s T₁ c x k) = coefN Lb s T₂ c y k := by
    intro k
    simp only [coefN]
    rw [Pf_MapLoc_toKsD_map]
    congr 1
    funext ζ
    apply Subtype.ext
    exact (hxy ζ.1 k).symm
  apply (HahnModule.of (KsW W s)).symm.injective
  ext k
  simp [ambF, ambMap, expN, HahnSeries.ofSuppBddBelow, hc]

section ThetaShiftProofs

variable {T₁ T₂ : LocLat G Qp LL O} {C₁ : Coord W (baseIdOf hR) T₁} {C₂ : Coord W (baseIdOf hR) T₂}
  {F : LatHom T₁.L T₂.L} {c : ZMod n} {ell : ℕ} {H : ℕ → ℕ} {κ₁ κ₂ : PowerSeries O} {r₁ r₂ : ℕ}
  {lam₁ : Fin r₁ → Dc W T₁ c} {lam₂ : Fin r₂ → Dc W T₂ c}

/- English proof (translation)
Introduce `s _ w hw hw'`. Use `funext fun ⟨s', hs'⟩ => Subtype.ext ?_` and prove the remaining obligations. Use `show ambF Mh.memD s' (locF Lb C₁ κ₁ s' (κ₁ • w) _) = locF Lb C₂ κ₂ s' (κ₂ • hC.f w) _`. Establish `hm₁ : C₂.t c (κ₁ • hC.f w) ∈ W.N T₂`. Establish `h0` using `(latHomOf hC).map_N c (κ₁ • w) (Hy₁.kap w hw)`.

Rewrite `h0` using `[show (latHomOf hC).f (κ₁ • w) = κ₁ • hC.f w from hC.f.map_smul κ₁ w]`. Conclude with `(mem_N C₂ c _).1 h0`. Establish `hm₂ : C₂.t c (κ₂ • hC.f w) ∈ W.N T₂` using `(mem_N C₂ c _).1 (Hy₂.kap _ hw')`. Establish `hA : ambF Mh.memD s' (expN Lb s' T₁ c ⟨C₁.t c (κ₁ • w), Hy₁.kap w hw⟩) = expN Lb s' T₂ c ⟨C₂.t c (κ₁ • hC.f w), hm₁⟩`. Apply `Pf_MapLoc_ambF_expN` to reduce the goal to its premises.

Introduce `ζ k`. Establish `hx : W.map F (C₁.t c (κ₁ • w)) ∈ W.N T₂`. Rewrite using `[← hC.coord_hom_map_trace, map_smul]`. Conclude with `hm₁`. Establish `he : (⟨C₂.t c (κ₁ • hC.f w), hm₁⟩ : ↥(W.N T₂)) = ⟨W.map F (C₁.t c (κ₁ • w)), hx⟩` using `Subtype.ext (by show C₂.t c (κ₁ • hC.f w) = W.map F (C₁.t c (κ₁ • w))`.

Rewrite using `[← hC.coord_hom_map_trace, map_smul])`. Rewrite using `[he]`. Conclude with `Pf_MapLoc_levB_map F hC.crys hC.crys' levN_eq c ζ ⟨C₁.t c (κ₁ • w), Hy₁.kap w hw⟩ hx k`. Establish `hs₁ : (baseIdOf hR).d κ₂ • C₂.t c (κ₁ • hC.f w) ∈ W.N T₂` using `(W.N T₂).smul_mem _ hm₁`. Establish `hs₂ : (baseIdOf hR).d κ₁ • C₂.t c (κ₂ • hC.f w) ∈ W.N T₂` using `(W.N T₂).smul_mem _ hm₂`.

Establish `hE : HahnSeries.ofPowerSeries ℤ (KsW W s') (rhoL hR c s' κ₂) • expN Lb s' T₂ c ⟨C₂.t c (κ₁ • hC.f w), hm₁⟩ = HahnSeries.ofPowerSeries ℤ (KsW W s') (rhoL hR c s' κ₁) • expN Lb s' T₂ c ⟨C₂.t c (κ₂ • hC.f w), hm₂⟩`. Rewrite using `[← Hy₂.expSemi s' κ₂ ⟨_, hm₁⟩ hs₁, ← Hy₂.expSemi s' κ₁ ⟨_, hm₂⟩ hs₂]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(baseIdOf hR).d κ₂ • C₂.t c (κ₁ • hC.f w) = (baseIdOf hR).d κ₁ • C₂.t c (κ₂ • hC.f w)`.

Rewrite using `[← C₂.t_smul, ← C₂.t_smul, smul_smul, smul_smul, mul_comm]`. Unfold `locF`. Rewrite using `[Mh.smul s', hA]`. Use `set ρ₁ := HahnSeries.ofPowerSeries ℤ (KsW W s') (rhoL hR c s' κ₁)`. Use `set ρ₂ := HahnSeries.ofPowerSeries ℤ (KsW W s') (rhoL hR c s' κ₂)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_smul, mul_assoc, Ring.inverse_mul_cancel ρ₂ (kap₂_unit s' hs'), mul_one]`. Use `_ = (Ring.inverse ρ₁ * Ring.inverse ρ₂) • (ρ₁ • expN Lb s' T₂ c ⟨C₂.t c (κ₂ • hC.f w), hm₂⟩) := by`. Rewrite using `[hE]`. Use `_ = Ring.inverse ρ₂ • expN Lb s' T₂ c ⟨C₂.t c (κ₂ • hC.f w), hm₂⟩ := by`.

Rewrite using `[smul_smul, mul_comm (Ring.inverse ρ₁), mul_assoc, Ring.inverse_mul_cancel ρ₁ (kap₁_unit s' hs'), mul_one]`.
-/
theorem locComm_holds (hC : CoordHom C₁ C₂ F)
    (Hy₁ : LvHyp Lb hR uZ ιZ C₁ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₁ lam₁)
    (Hy₂ : LvHyp Lb hR uZ ιZ C₂ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₂ lam₂)
    (Mh : MapHyp hR uZ ιZ F c) (j M g η : ℕ) (kind : ℕ → Kind) (b : ℕ → ℕ)
    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (kap₁_unit : ∀ s < ell, IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s κ₁)))
    (kap₂_unit : ∀ s < ell, IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s κ₂))) :
    ∀ s < ell, ∀ (w : C₁.V)
    (hw : w ∈ (latOf C₁).W c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell))
    (hw' : (latHomOf hC).f w ∈ (latOf C₂).W c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell)),
    prEOf Mh (hΔ₁ := Hy₁.delta) (hΔ₂ := Hy₂.delta) ell
        ((lvData Hy₁ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).loc s ⟨w, hw⟩) =
      (lvData Hy₂ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).loc s ⟨(latHomOf hC).f w, hw'⟩ := by
  intro s _ w hw hw'
  refine funext fun ⟨s', hs'⟩ => Subtype.ext ?_
  show ambF Mh.memD s' (locF Lb C₁ κ₁ s' (κ₁ • w) _) = locF Lb C₂ κ₂ s' (κ₂ • hC.f w) _
  have hm₁ : C₂.t c (κ₁ • hC.f w) ∈ W.N T₂ := by
    have h0 := (latHomOf hC).map_N c (κ₁ • w) (Hy₁.kap w hw)
    rw [show (latHomOf hC).f (κ₁ • w) = κ₁ • hC.f w from hC.f.map_smul κ₁ w] at h0
    exact (mem_N C₂ c _).1 h0
  have hm₂ : C₂.t c (κ₂ • hC.f w) ∈ W.N T₂ := (mem_N C₂ c _).1 (Hy₂.kap _ hw')
  have hA : ambF Mh.memD s' (expN Lb s' T₁ c ⟨C₁.t c (κ₁ • w), Hy₁.kap w hw⟩) =
      expN Lb s' T₂ c ⟨C₂.t c (κ₁ • hC.f w), hm₁⟩ := by
    apply Pf_MapLoc_ambF_expN
    intro ζ k
    have hx : W.map F (C₁.t c (κ₁ • w)) ∈ W.N T₂ := by
      rw [← hC.coord_hom_map_trace, map_smul]
      exact hm₁
    have he : (⟨C₂.t c (κ₁ • hC.f w), hm₁⟩ : ↥(W.N T₂)) = ⟨W.map F (C₁.t c (κ₁ • w)), hx⟩ :=
      Subtype.ext (by
        show C₂.t c (κ₁ • hC.f w) = W.map F (C₁.t c (κ₁ • w))
        rw [← hC.coord_hom_map_trace, map_smul])
    rw [he]
    exact Pf_MapLoc_levB_map F hC.crys hC.crys' levN_eq c ζ ⟨C₁.t c (κ₁ • w), Hy₁.kap w hw⟩ hx k
  have hs₁ : (baseIdOf hR).d κ₂ • C₂.t c (κ₁ • hC.f w) ∈ W.N T₂ := (W.N T₂).smul_mem _ hm₁
  have hs₂ : (baseIdOf hR).d κ₁ • C₂.t c (κ₂ • hC.f w) ∈ W.N T₂ := (W.N T₂).smul_mem _ hm₂
  have hE : HahnSeries.ofPowerSeries ℤ (KsW W s') (rhoL hR c s' κ₂) •
        expN Lb s' T₂ c ⟨C₂.t c (κ₁ • hC.f w), hm₁⟩ =
      HahnSeries.ofPowerSeries ℤ (KsW W s') (rhoL hR c s' κ₁) •
        expN Lb s' T₂ c ⟨C₂.t c (κ₂ • hC.f w), hm₂⟩ := by
    rw [← Hy₂.expSemi s' κ₂ ⟨_, hm₁⟩ hs₁, ← Hy₂.expSemi s' κ₁ ⟨_, hm₂⟩ hs₂]
    congr 1
    apply Subtype.ext
    change (baseIdOf hR).d κ₂ • C₂.t c (κ₁ • hC.f w) = (baseIdOf hR).d κ₁ • C₂.t c (κ₂ • hC.f w)
    rw [← C₂.t_smul, ← C₂.t_smul, smul_smul, smul_smul, mul_comm]
  unfold locF
  rw [Mh.smul s', hA]
  set ρ₁ := HahnSeries.ofPowerSeries ℤ (KsW W s') (rhoL hR c s' κ₁)
  set ρ₂ := HahnSeries.ofPowerSeries ℤ (KsW W s') (rhoL hR c s' κ₂)
  calc Ring.inverse ρ₁ • expN Lb s' T₂ c ⟨C₂.t c (κ₁ • hC.f w), hm₁⟩
      = (Ring.inverse ρ₁ * Ring.inverse ρ₂) • (ρ₂ • expN Lb s' T₂ c ⟨C₂.t c (κ₁ • hC.f w), hm₁⟩) := by
        rw [smul_smul, mul_assoc, Ring.inverse_mul_cancel ρ₂ (kap₂_unit s' hs'), mul_one]
    _ = (Ring.inverse ρ₁ * Ring.inverse ρ₂) • (ρ₁ • expN Lb s' T₂ c ⟨C₂.t c (κ₂ • hC.f w), hm₂⟩) := by
        rw [hE]
    _ = Ring.inverse ρ₂ • expN Lb s' T₂ c ⟨C₂.t c (κ₂ • hC.f w), hm₂⟩ := by
        rw [smul_smul, mul_comm (Ring.inverse ρ₁), mul_assoc, Ring.inverse_mul_cancel ρ₁ (kap₁_unit s' hs'),
          mul_one]

end ThetaShiftProofs

end Formalism.MainNotions.N.Ln03.Pf
