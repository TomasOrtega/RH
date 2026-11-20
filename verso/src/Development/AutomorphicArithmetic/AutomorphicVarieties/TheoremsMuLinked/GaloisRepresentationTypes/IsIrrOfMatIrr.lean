import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.LinkedRig
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.AdDown
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ExistsNrep3
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.OrthogonalPairingFromIntertwiner
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.MatrixIrreducibility.IrrOfMatIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.LkMarks
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.NormEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolCOfSolDescent
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SolDescent
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.CsdOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoBkMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.CplFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IntegralityOfNormCoefficients
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ContinuousHom
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOfKernel
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.StationaryPhaseModel

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th

namespace UpperTheory.V.Th.End3

open UpperTheory.V.U3 UpperTheory.V.Base

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
attribute [local instance 10000] IsDiscreteValuationRing.toIsLocalRing

/- English proof (translation)
The claim follows from `DivisionSemiring.to_moduleIsTorsionFree`.
-/
private theorem tf (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] : Module.IsTorsionFree L Ω :=
  DivisionSemiring.to_moduleIsTorsionFree

attribute [local instance] tf

/- English proof (translation)
Assemble the required witnesses or components as `⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩`.
-/
theorem algClo (L Ω : Type) [Field L] [CharZero L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra L Ω] :
    IsAlgClosure L Ω :=
  ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩

/- English proof (translation)
The claim follows from `(Continuous.units_map _ (show Continuous (fun x : ℤ_[l] => algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l])) from (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ F Ω l)`.
-/
theorem cyc_cont (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    Continuous (cycBar F Ω l) :=
  (Continuous.units_map _ (show Continuous (fun x : ℤ_[l] => algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l])) from
    (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ F Ω l)

/- English proof (translation)
Establish `h1 : cycZ F Ω l c = -1` using `UpperTheory.V.IsConjOm.cyc (E := F) (σ := c.toRingEquiv) h`. Establish `h2 : cycZ F Ω l c' = -1` using `UpperTheory.V.IsConjOm.cyc (E := F) (σ := c'.toRingEquiv) h'`. Simplify using `only [cycBar, MonoidHom.comp_apply, h1, h2]`.
-/
private theorem cyc_conj {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    {c c' : G F Ω} (h : Af.IsConjEl c) (h' : Af.IsConjEl c') : cycBar F Ω l c = cycBar F Ω l c' := by
  have h1 : cycZ F Ω l c = -1 := UpperTheory.V.IsConjOm.cyc (E := F) (σ := c.toRingEquiv) h
  have h2 : cycZ F Ω l c' = -1 := UpperTheory.V.IsConjOm.cyc (E := F) (σ := c'.toRingEquiv) h'
  simp only [cycBar, MonoidHom.comp_apply, h1, h2]

/- English proof (translation)
Take `⟨j, hj⟩` from `hσ`. Use `haveI : IsAlgClosure K Ω := algClo K Ω`. Use `haveI : IsAlgClosure L Ω := algClo L Ω`. Use `haveI : IsAlgClosure (maximalRealSubfield K) Ω := algClo (maximalRealSubfield K) Ω`. Set `c : G (maximalRealSubfield K) Ω` to `AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun x => by`.

Apply `j.injective` to reduce the goal to its premises. Use `(hj _).trans ?_` and prove the remaining obligations. Conclude with `(mem_maximalRealSubfield_iff x.1).1 x.2 (j.comp (algebraMap K Ω))`. Establish `hc : Af.IsConjEl c` using `⟨j, hj⟩`. Establish `hpc : Af.IsPairing c r (cycBar K Ω l ^ (1 - (n : ℤ))) P` using `fun s s' hs => hPr s s' (AlgEquiv.ext fun x => DFunLike.congr_fun hs x)`.

Establish `halg : Af.IsAlgChar ι (cycBar (maximalRealSubfield K) Ω l ^ (1 - (n : ℤ)))`. Use `(Af.algOfCyc hP (maximalRealSubfield K) Ω l ι).1 _ ((cyc_cont _ Ω l).zpow _) fun w _ => ?_` and prove the remaining obligations. Take `⟨A, hA⟩` from `exists_isPlaceOver Ω w`. Use `⟨A, hA, 1 - (n : ℤ), 1, one_pos, fun s _ => ?_⟩` and prove the remaining obligations. Rewrite using `[pow_one, MonoidHom.zpow_apply, zpow_neg, mul_inv_cancel]`.

Use `Af.csdOf hP ℚ L Ω inferInstance l ι n hn _ σ P ⟨j, hj⟩ ?_ fun s s' hs => hPr (galEmb K L Ω s) (galEmb K L Ω s') hs` and prove the remaining obligations. Use `(Z.Bc.solC_of_solDescent (Af.solDescent hP) (maximalRealSubfield K) K L Ω hsol ⟨inferInstance, Or.inr ⟨?_, inferInstance⟩⟩ inferInstance inferInstance l ι n hn r (cycBar (maximalRealSubfield K) Ω l ^ (1 - (n : ℤ))) hr hirr halg (fun a b ha hb => ?_) ⟨c, P, hc, ?_⟩).1 haut` and prove the remaining obligations. Conclude with `Algebra.IsQuadraticExtension.finrank_eq_two _ _`. Rewrite using `[MonoidHom.zpow_apply, MonoidHom.zpow_apply, cyc_conj l ha hb]`. Conclude with `hpc`.
-/
theorem upCsd (hP : Af.HypothesesH) (K L Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field L] [NumberField L] [IsCMField L]
    [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K L]
    [hsol : Group.IsSolvable (L ≃ₐ[K] L)] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (hn : 1 ≤ n)
    (r : G K Ω →* GL (Fin n) (Qbar l)) (σ : G ℚ Ω) (hσ : Sd.IsCC σ) (hr : Continuous r) (P : GL (Fin n) (Qbar l))
    (hPr : Sd.IsPair σ r (cycBar K Ω l ^ (1 - (n : ℤ))) P) (hirr : Af.IsIrr (r.comp (galEmb K L Ω)))
    (haut : Af.IsAut ι r) : Af.IsAutCsd ι (r.comp (galEmb K L Ω)) := by
  obtain ⟨j, hj⟩ := hσ
  haveI : IsAlgClosure K Ω := algClo K Ω
  haveI : IsAlgClosure L Ω := algClo L Ω
  haveI : IsAlgClosure (maximalRealSubfield K) Ω := algClo (maximalRealSubfield K) Ω
  let c : G (maximalRealSubfield K) Ω := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun x => by
    apply j.injective
    refine (hj _).trans ?_
    exact (mem_maximalRealSubfield_iff x.1).1 x.2 (j.comp (algebraMap K Ω))
  have hc : Af.IsConjEl c := ⟨j, hj⟩
  have hpc : Af.IsPairing c r (cycBar K Ω l ^ (1 - (n : ℤ))) P := fun s s' hs =>
    hPr s s' (AlgEquiv.ext fun x => DFunLike.congr_fun hs x)
  have halg : Af.IsAlgChar ι (cycBar (maximalRealSubfield K) Ω l ^ (1 - (n : ℤ))) := by
    refine (Af.algOfCyc hP (maximalRealSubfield K) Ω l ι).1 _ ((cyc_cont _ Ω l).zpow _) fun w _ => ?_
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    refine ⟨A, hA, 1 - (n : ℤ), 1, one_pos, fun s _ => ?_⟩
    rw [pow_one, MonoidHom.zpow_apply, zpow_neg, mul_inv_cancel]
  refine Af.csdOf hP ℚ L Ω inferInstance l ι n hn _ σ P ⟨j, hj⟩ ?_
    fun s s' hs => hPr (galEmb K L Ω s) (galEmb K L Ω s') hs
  refine (Z.Bc.solC_of_solDescent (Af.solDescent hP) (maximalRealSubfield K) K L Ω hsol
    ⟨inferInstance, Or.inr ⟨?_, inferInstance⟩⟩ inferInstance inferInstance
    l ι n hn r (cycBar (maximalRealSubfield K) Ω l ^ (1 - (n : ℤ))) hr hirr halg (fun a b ha hb => ?_) ⟨c, P, hc, ?_⟩).1 haut
  · exact Algebra.IsQuadraticExtension.finrank_eq_two _ _
  · rw [MonoidHom.zpow_apply, MonoidHom.zpow_apply, cyc_conj l ha hb]
  · exact hpc

/- English proof (translation)
Take `⟨sat, inf, hc, hreg, hatt⟩` from `h`. Conclude with `⟨sat, inf, hc, hreg, (Af.Bc.irrBasic.1 _ Unit _ n _).2.1 hi, hatt.2.mono fun w ⟨B, hB, h⟩ => ⟨B, hB, h.of_iso e⟩⟩`.
-/
theorem isAut_iso {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ}
    {n : ℕ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} (h : Af.IsAut ι r) (e : Af.RepIso r r') (hi : Af.IsIrr r') :
    Af.IsAut ι r' := by
  obtain ⟨sat, inf, hc, hreg, hatt⟩ := h
  exact ⟨sat, inf, hc, hreg, (Af.Bc.irrBasic.1 _ Unit _ n _).2.1 hi,
    hatt.2.mono fun w ⟨B, hB, h⟩ => ⟨B, hB, h.of_iso e⟩⟩

/- English proof (translation)
Introduce `A hA`. Take `⟨g, hg, h1, α, h2, h3⟩` from `h A hA`. Take `⟨a, ha⟩` from `e`. Use `⟨g, hg, h1, α, h2, ?_⟩` and prove the remaining obligations. Rewrite using `[← h3]`.

Use `show (r' g).val.charpoly = (r g).val.charpoly`. Rewrite using `[ha, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]`.
-/
theorem freeAt_iso {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} (h : FreeAt l r) (e : Af.RepIso r r') : FreeAt l r' := by
  intro A hA
  obtain ⟨g, hg, h1, α, h2, h3⟩ := h A hA
  obtain ⟨a, ha⟩ := e
  refine ⟨g, hg, h1, α, h2, ?_⟩
  rw [← h3]
  show (r' g).val.charpoly = (r g).val.charpoly
  rw [ha, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

/- English proof (translation)
Introduce `c hz hbk`. Take `⟨hcc, hcoc⟩` from `(mem_Z1_iff_cocycle _ _).1 hz`. Establish `hcont : Continuous (fun g => f (c g))` using `hc.comp hcc`. Establish `hz' : (fun g => f (c g)) ∈ Z1 ρ'` using `(mem_Z1_iff_cocycle _ _).2 ⟨hcont, fun g g' => by rw [hcoc, map_add, hf]⟩`. Take `⟨m, hm⟩` from `(mem_coboundaries1 _ _).1 (h _ hz' (X.Kato.bkMap l F Ω _ _ _ _ ρ ρ' (f.toLinearMap.restrictScalars ℚ_[l]) hf c hcont hbk))`.

Take `⟨m', rfl⟩` from `f.surjective m`. Use `(mem_coboundaries1 _ _).2 ⟨m', fun g => f.injective ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, hf]`. Conclude with `hm g`.
-/
theorem h1fZero_equiv {l : ℕ} [Fact l.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {C V V' : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] C V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V]
    [AddCommGroup V'] [Module C V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] C V']
    [TopologicalSpace V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul C V']
    (ρ : Representation C (G F Ω) V) (ρ' : Representation C (G F Ω) V') (f : V ≃ₗ[C] V') (hc : Continuous f)
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) (h : Af.BlochKatoSelmerVanishes l ρ') : Af.BlochKatoSelmerVanishes l ρ := by
  intro c hz hbk
  obtain ⟨hcc, hcoc⟩ := (mem_Z1_iff_cocycle _ _).1 hz
  have hcont : Continuous (fun g => f (c g)) := hc.comp hcc
  have hz' : (fun g => f (c g)) ∈ Z1 ρ' := (mem_Z1_iff_cocycle _ _).2 ⟨hcont, fun g g' => by rw [hcoc, map_add, hf]⟩
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 (h _ hz'
    (X.Kato.bkMap l F Ω _ _ _ _ ρ ρ' (f.toLinearMap.restrictScalars ℚ_[l]) hf c hcont hbk))
  obtain ⟨m', rfl⟩ := f.surjective m
  refine (mem_coboundaries1 _ _).2 ⟨m', fun g => f.injective ?_⟩
  rw [map_sub, hf]
  exact hm g

/- English proof (translation)
Set `f : Matrix (Fin m) (Fin m) (PadicAlgCl l) ≃ₗ[PadicAlgCl l] Matrix (Fin m) (Fin m) (PadicAlgCl l)` to `LinearMap.GeneralLinearGroup.toLinearEquiv ((GG.ad m (PadicAlgCl l)).toHomUnits (GG.ofGL h))`. Establish `hf : ∀ X, f X = GG.ad m (PadicAlgCl l) (GG.ofGL h) X` using `fun X => rfl`. Use `h1fZero_equiv _ _ f ?_ (fun g X => ?_) H` and prove the remaining obligations. Establish `: (f : _ → _) = fun X => h.val * X * (h⁻¹).val` using `funext fun X => by`. Rewrite using `[hf, GG.ad_apply, GG.adFun, if_pos (by rfl)]`.

Both sides reduce to the same expression. Rewrite using `[this]`. Use `fun_prop`. Rewrite using `[hf, hf] show _ = GG.ad m _ (GG.ofGL h * r g * (GG.ofGL h)⁻¹) _`. Rewrite using `[GG.ad_apply, GG.ad_apply, GG.ad_apply, ← GG.adFun_mul, inv_mul_cancel_right, GG.adFun_mul]`.

Both sides reduce to the same expression.
-/
theorem h1fZero_conjBy {l : ℕ} [Fact l.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {m : ℕ}
    (r : G F Ω →* GG m (PadicAlgCl l)) (h : GL (Fin m) (PadicAlgCl l)) (H : Af.BlochKatoSelmerVanishes l (adRep (conjBy h r))) :
    Af.BlochKatoSelmerVanishes l (adRep r) := by
  let f : Matrix (Fin m) (Fin m) (PadicAlgCl l) ≃ₗ[PadicAlgCl l] Matrix (Fin m) (Fin m) (PadicAlgCl l) :=
    LinearMap.GeneralLinearGroup.toLinearEquiv ((GG.ad m (PadicAlgCl l)).toHomUnits (GG.ofGL h))
  have hf : ∀ X, f X = GG.ad m (PadicAlgCl l) (GG.ofGL h) X := fun X => rfl
  refine h1fZero_equiv _ _ f ?_ (fun g X => ?_) H
  · have : (f : _ → _) = fun X => h.val * X * (h⁻¹).val := funext fun X => by
      rw [hf, GG.ad_apply, GG.adFun, if_pos (by rfl)]
      rfl
    rw [this]
    fun_prop
  · rw [hf, hf]
    show _ = GG.ad m _ (GG.ofGL h * r g * (GG.ofGL h)⁻¹) _
    rw [GG.ad_apply, GG.ad_apply, GG.ad_apply, ← GG.adFun_mul, inv_mul_cancel_right, GG.adFun_mul]
    rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `e`. Use extensionality with `a b`. Use `Ideal.Quotient.eq.2 (e a b)` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations.

Apply the tactic sequence `by_cases hab : a = b <;> simp [Matrix.one_apply, hab]`. Introduce `e a b`. Use `Ideal.Quotient.eq.1 ?_` and prove the remaining obligations. Use `(congrArg (fun x : GL (Fin 3) (C ⧸ I) => x.val a b) e).trans ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases hab : a = b <;> simp [Matrix.one_apply, hab]`.
-/
private theorem congOne_iff {C : Type} [CommRing C] (I : Ideal C) (h : GL (Fin 3) C) :
    CongOne I h ↔ Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) h = 1 := by
  constructor
  · intro e
    ext a b
    have := Ideal.Quotient.eq.2 (e a b)
    refine this.trans ?_
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  · intro e a b
    refine Ideal.Quotient.eq.1 ?_
    refine (congrArg (fun x : GL (Fin 3) (C ⧸ I) => x.val a b) e).trans ?_
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]

/- English proof (translation)
Establish `e : GG.map f (GG.ofGL h) = GG.ofGL (Matrix.GeneralLinearGroup.map f h)` using `rfl`. Use `MonoidHom.ext fun g => ?_` and prove the remaining obligations. Simplify using `only [conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, e]`.
-/
theorem map_conjBy {G R S : Type} [Group G] [CommRing R] [CommRing S] {m : ℕ} (f : R →+* S) (h : GL (Fin m) R)
    (r : G →* GG m R) :
    (GG.map f).comp (conjBy h r) = conjBy (Matrix.GeneralLinearGroup.map f h) ((GG.map f).comp r) := by
  have e : GG.map f (GG.ofGL h) = GG.ofGL (Matrix.GeneralLinearGroup.map f h) := rfl
  refine MonoidHom.ext fun g => ?_
  simp only [conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, e]

/- English proof (translation)
Simplify using `[conjBy]`.
-/
theorem conjBy_left {G R : Type} [Group G] [CommRing R] {m : ℕ} (h : GL (Fin m) R) (r : G →* GG m R) (g : G) :
    (conjBy h r g).left = h * (r g).left * sgnAct m R (r g).right h⁻¹ := by
  simp [conjBy]

/- English proof (translation)
Simplify using `[conjBy]`.
-/
theorem conjBy_right {G R : Type} [Group G] [CommRing R] {m : ℕ} (h : GL (Fin m) R) (r : G →* GG m R) (g : G) :
    (conjBy h r g).right = (r g).right := by
  simp [conjBy]

/- English proof (translation)
Use `MonoidHom.ext fun g => ?_` and prove the remaining obligations. Use `show GG.ofGL _ * (GG.ofGL h * r g * (GG.ofGL h)⁻¹) * (GG.ofGL _)⁻¹ = GG.ofGL _ * r g * (GG.ofGL _)⁻¹`. Simplify using `only [map_inv, map_mul, _root_.mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]`.
-/
private theorem conjBy_conjBy {C D : Type} [CommRing C] [Group D] (h h' : GL (Fin 3) C) (r : D →* GG 3 C) :
    conjBy (h * h')⁻¹ (conjBy h r) = conjBy h'⁻¹ r := by
  refine MonoidHom.ext fun g => ?_
  show GG.ofGL _ * (GG.ofGL h * r g * (GG.ofGL h)⁻¹) * (GG.ofGL _)⁻¹ = GG.ofGL _ * r g * (GG.ofGL _)⁻¹
  simp only [map_inv, map_mul, _root_.mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]

/- English proof (translation)
Use `⟨⟨fun g => (conjBy_right h r g).trans (hr.red.mult g), fun g a b => ?_⟩, fun n => ?_, hN, fun B' h1 s h2 h3 h4 => ?_, ?_⟩` and prove the remaining obligations. Establish `e` using `DFunLike.congr_fun (map_conjBy (Ideal.Quotient.mk (maximalIdeal A)) h r) g`. Rewrite `e` using `[(congOne_iff _ _).1 hh]`. Establish `e2 : (conjBy h r g).mat.map (Ideal.Quotient.mk (maximalIdeal A)) = (r g).mat.map (Ideal.Quotient.mk (maximalIdeal A))`. Use `(congrArg GG.mat e).trans ?_` and prove the remaining obligations.

Rewrite using `[GG.mat, conjBy_left, inv_one, map_one, one_mul, mul_one]`. Both sides reduce to the same expression. Use `Ideal.Quotient.eq.1 ((congrFun (congrFun e2 a) b).trans ?_)` and prove the remaining obligations. Conclude with `Ideal.Quotient.eq.2 (hr.red.red g a b)`. Use `((hr.cont n).prodMk hη).comp fun p : Matrix (Fin 3) (Fin 3) (A ⧸ maximalIdeal A ^ n) × ℤˣ => h.val.map (Ideal.Quotient.mk (maximalIdeal A ^ n)) * p.1 * (sgnAct 3 A p.2 h⁻¹).val.map (Ideal.Quotient.mk (maximalIdeal A ^ n))` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`. Rewrite using `[GG.mat, conjBy_left, hr.red.mult g, Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul]`. Both sides reduce to the same expression. Use `show GG.ofGL h * r s * (GG.ofGL h)⁻¹ = 1`.

Rewrite using `[hr.away B' h1 s h2 h3 h4, mul_one, mul_inv_cancel]`. Take `⟨h', h1, h2, h3⟩` from `hr.ord`. Establish `e : (conjBy h r).comp (Dec (F` using `ℚ) B).subtype = conjBy h (r.comp (Dec (F := ℚ) B).subtype) := rfl`. Use `⟨h * h', (congOne_iff _ _).2 ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, (congOne_iff _ _).1 hh, (congOne_iff _ _).1 h1, mul_one]`.

Rewrite using `[e, conjBy_conjBy]`. Conclude with `h2`. Rewrite using `[e, conjBy_conjBy]`. Conclude with `h3`.
-/
theorem ordPt_conj {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} {O : Type} [CommRing O] [IsLocalRing O]
    {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ g₂ : G ℚ Ω} {B : ValuationSubring Ω} {A : Type} [CommRing A] [IsLocalRing A]
    [Algebra O A] {r : G ℚ Ω →* GG 3 A} (hr : Pr.OrdPt l η Ψ σ g₁ B r) (hη : IsLocallyConstant η) (h : GL (Fin 3) A)
    (hh : CongOne (maximalIdeal A) h) (hN : Normalised σ g₂ (conjBy h r)) : Pr.OrdPt l η Ψ σ g₂ B (conjBy h r) := by
  refine ⟨⟨fun g => (conjBy_right h r g).trans (hr.red.mult g), fun g a b => ?_⟩, fun n => ?_, hN,
    fun B' h1 s h2 h3 h4 => ?_, ?_⟩
  · have e := DFunLike.congr_fun (map_conjBy (Ideal.Quotient.mk (maximalIdeal A)) h r) g
    rw [(congOne_iff _ _).1 hh] at e
    have e2 : (conjBy h r g).mat.map (Ideal.Quotient.mk (maximalIdeal A)) = (r g).mat.map (Ideal.Quotient.mk (maximalIdeal A)) := by
      refine (congrArg GG.mat e).trans ?_
      rw [GG.mat, conjBy_left, inv_one, map_one, one_mul, mul_one]
      rfl
    refine Ideal.Quotient.eq.1 ((congrFun (congrFun e2 a) b).trans ?_)
    exact Ideal.Quotient.eq.2 (hr.red.red g a b)
  · have := ((hr.cont n).prodMk hη).comp fun p : Matrix (Fin 3) (Fin 3) (A ⧸ maximalIdeal A ^ n) × ℤˣ =>
      h.val.map (Ideal.Quotient.mk (maximalIdeal A ^ n)) * p.1 *
        (sgnAct 3 A p.2 h⁻¹).val.map (Ideal.Quotient.mk (maximalIdeal A ^ n))
    convert this using 1
    funext g
    rw [GG.mat, conjBy_left, hr.red.mult g, Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul]
    rfl
  · show GG.ofGL h * r s * (GG.ofGL h)⁻¹ = 1
    rw [hr.away B' h1 s h2 h3 h4, mul_one, mul_inv_cancel]
  · obtain ⟨h', h1, h2, h3⟩ := hr.ord
    have e : (conjBy h r).comp (Dec (F := ℚ) B).subtype = conjBy h (r.comp (Dec (F := ℚ) B).subtype) := rfl
    refine ⟨h * h', (congOne_iff _ _).2 ?_, ?_, ?_⟩
    · rw [map_mul, (congOne_iff _ _).1 hh, (congOne_iff _ _).1 h1, mul_one]
    · rw [e, conjBy_conjBy]; exact h2
    · rw [e, conjBy_conjBy]; exact h3

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use `show (tor A t : Matrix (Fin 3) (Fin 3) A).map f = _`. Rewrite using `[tor_val, tor_val, Matrix.diagonal_map (map_zero f)]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Rewrite using `[← map_zpow]`. Both sides reduce to the same expression.
-/
private theorem map_tor {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (t : Aˣ) :
    Matrix.GeneralLinearGroup.map f (tor A t) = tor B (Units.map f.toMonoidHom t) := by
  apply Units.ext
  show (tor A t : Matrix (Fin 3) (Fin 3) A).map f = _
  rw [tor_val, tor_val, Matrix.diagonal_map (map_zero f)]
  congr 1
  funext i
  rw [← map_zpow]
  rfl

/- English proof (translation)
Take `⟨h, hh, hN⟩` from `exists_normalised η ((Units.map ((residue A).comp (algebraMap O A)).toMonoidHom).comp Ψ) σ g₂ r (by simpa [map_ofNat] using h2.map (algebraMap O A)) ⟨hM.csq, hM.ηc, by simp [hM.Ψc], hM.ηg, by simpa using hM.Ψg.map ((residue A).comp (algebraMap O A))⟩ (by`. Use `MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) (hr.red.mult g)` and prove the remaining obligations. Rewrite using `[unitaryThreeReflection_left, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_tor]`. Use extensionality with `a b`. Conclude with `Ideal.Quotient.eq.2 (hr.red.red g a b))`.

Conclude with `⟨h, hh, ordPt_conj hr hη h hh hN⟩`.
-/
theorem ordPt_renorm {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} {O : Type} [CommRing O] [IsLocalRing O]
    {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ g₂ : G ℚ Ω} {B : ValuationSubring Ω} {A : Type} [CommRing A] [IsLocalRing A]
    [Algebra O A] [IsAdicComplete (maximalIdeal A) A] {r : G ℚ Ω →* GG 3 A} (hr : Pr.OrdPt l η Ψ σ g₁ B r)
    (hη : IsLocallyConstant η) (h2 : IsUnit (2 : O)) (hM : Marks η Ψ σ g₂) :
    ∃ h : GL (Fin 3) A, CongOne (maximalIdeal A) h ∧ Pr.OrdPt l η Ψ σ g₂ B (conjBy h r) := by
  obtain ⟨h, hh, hN⟩ := exists_normalised η ((Units.map ((residue A).comp (algebraMap O A)).toMonoidHom).comp Ψ) σ g₂ r
    (by simpa [map_ofNat] using h2.map (algebraMap O A))
    ⟨hM.csq, hM.ηc, by simp [hM.Ψc], hM.ηg, by simpa using hM.Ψg.map ((residue A).comp (algebraMap O A))⟩ (by
      refine MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) (hr.red.mult g)
      rw [unitaryThreeReflection_left, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_tor]
      ext a b
      exact Ideal.Quotient.eq.2 (hr.red.red g a b))
  exact ⟨h, hh, ordPt_conj hr hη h hh hN⟩

/- English proof (translation)
Establish `hinj : Function.Injective (fun i => (a i : K) ^ d)`. Introduce `i j hij`. Assume the negation of the conclusion as `hne`. Apply `ha i j hne d hd` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Simplify using `using hij`. Establish `hroot : ∀ i, (M ^ d).charpoly.IsRoot ((a i : K) ^ d)`. Introduce `i`. Rewrite using `[← Matrix.mem_spectrum_iff_isRoot_charpoly]`. Apply `spectrum.pow_mem_pow` to reduce the goal to its premises.

Rewrite using `[Matrix.mem_spectrum_iff_isRoot_charpoly, hM, Polynomial.IsRoot, Polynomial.eval_prod]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (by simp)`. Establish `hdvd : (∏ i, (X - C ((a i : K) ^ d))) ∣ (M ^ d).charpoly`. Apply `Finset.prod_dvd_of_coprime` to reduce the goal to its premises. Introduce `i _ j _ hij`.

Conclude with `Polynomial.pairwise_coprime_X_sub_C hinj hij`. Introduce `i _`. Conclude with `Polynomial.dvd_iff_isRoot.2 (hroot i)`. Establish `hmon : (∏ i, (X - C ((a i : K) ^ d))).Monic` using `Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)`. Apply `Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon (Matrix.charpoly_monic _) hdvd` to reduce the goal to its premises.

Rewrite using `[Matrix.charpoly_natDegree_eq_dim, Polynomial.natDegree_finset_prod_X_sub_C_eq_card, Finset.card_univ]`.
-/
private theorem charpoly_pow {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (a : Fin n → Kˣ)
    (hM : M.charpoly = ∏ i, (X - C (a i : K))) (ha : Pr.FreeRatios a) (d : ℕ) (hd : 0 < d) :
    (M ^ d).charpoly = ∏ i, (X - C ((a i : K) ^ d)) := by
  have hinj : Function.Injective (fun i => (a i : K) ^ d) := by
    intro i j hij
    by_contra hne
    apply ha i j hne d hd
    apply Units.ext
    simpa using hij
  have hroot : ∀ i, (M ^ d).charpoly.IsRoot ((a i : K) ^ d) := by
    intro i
    rw [← Matrix.mem_spectrum_iff_isRoot_charpoly]
    apply spectrum.pow_mem_pow
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, hM, Polynomial.IsRoot, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hdvd : (∏ i, (X - C ((a i : K) ^ d))) ∣ (M ^ d).charpoly := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      exact Polynomial.pairwise_coprime_X_sub_C hinj hij
    · intro i _
      exact Polynomial.dvd_iff_isRoot.2 (hroot i)
  have hmon : (∏ i, (X - C ((a i : K) ^ d))).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon (Matrix.charpoly_monic _) hdvd
  rw [Matrix.charpoly_natDegree_eq_dim, Polynomial.natDegree_finset_prod_X_sub_C_eq_card, Finset.card_univ]

/- English proof (translation)
Introduce `A hA`. Take `⟨g, hg, h1, α, h2, h3⟩` from `h A hA`. Take `⟨d, hd, -, hm⟩` from `(galOf F L Ω).exists_pow_mem_of_index_ne_zero (by rw [(galEmbTop F L Ω).2.2]; exact Module.finrank_pos.ne') g`. Rewrite `hm` using `[← range_galEmb]`. Take `⟨t, ht⟩` from `hm`.

Use `⟨t, ?_, ?_, fun i => α i ^ d, fun i j hij m hm => ?_, ?_⟩` and prove the remaining obligations. Use `pow_mem hg d` as an intermediate fact. Rewrite `this` using `[← ht]`. Conclude with `this`. Use `show cycZ F Ω l (galEmb F L Ω t) = 1`.

Rewrite using `[ht, map_pow, h1, one_pow]`. Rewrite using `[← pow_mul, ← pow_mul]`. Conclude with `h2 i j hij _ (Nat.mul_pos hd hm)`. Use `show (r (galEmb F L Ω t)).val.charpoly = _`. Rewrite using `[ht, map_pow, Units.val_pow_eq_pow_val]`.

Simplify using `only [Units.val_pow_eq_pow_val]`. Conclude with `charpoly_pow _ α h3 h2 d hd`.
-/
theorem freeAt_res {F L Ω : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω] [Algebra F L] [Algebra F Ω]
    [Algebra L Ω] [IsScalarTower F L Ω] [IsAlgClosure F Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {r : G F Ω →* GL (Fin n) (Qbar l)} (h : FreeAt l r) : FreeAt l (r.comp (galEmb F L Ω)) := by
  intro A hA
  obtain ⟨g, hg, h1, α, h2, h3⟩ := h A hA
  obtain ⟨d, hd, -, hm⟩ := (galOf F L Ω).exists_pow_mem_of_index_ne_zero
    (by rw [(galEmbTop F L Ω).2.2]; exact Module.finrank_pos.ne') g
  rw [← range_galEmb] at hm
  obtain ⟨t, ht⟩ := hm
  refine ⟨t, ?_, ?_, fun i => α i ^ d, fun i j hij m hm => ?_, ?_⟩
  · have := pow_mem hg d
    rw [← ht] at this
    exact this
  · show cycZ F Ω l (galEmb F L Ω t) = 1
    rw [ht, map_pow, h1, one_pow]
  · rw [← pow_mul, ← pow_mul]
    exact h2 i j hij _ (Nat.mul_pos hd hm)
  · show (r (galEmb F L Ω t)).val.charpoly = _
    rw [ht, map_pow, Units.val_pow_eq_pow_val]
    simp only [Units.val_pow_eq_pow_val]
    exact charpoly_pow _ α h3 h2 d hd

/- English proof (translation)
Set `c' : Coef l` to `⟨A.restrictScalars ℤ_[l], ‹IsDiscreteValuationRing A›, (Module.Finite.trans (R := ℤ_[l]) c.O A :)⟩`. Use `haveI := (abelian₂.dvr_finite l c.O).1`. Use `⟨AlgebraTools.Conn.cplFinite (A := c.O) _ (maximalIdeal.isMaximal A).ne_top, Db.locHom c A, fun Γ _ f hf => ((UpperTheory.integrality_of_norm_coefficients l).2 c' Γ f).1 hf⟩` and prove the remaining obligations.
-/
theorem sub_facts {l : ℕ} [Fact l.Prime] (c : Coef l) (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A]
    [Module.Finite c.O A] : IsAdicComplete (maximalIdeal A) A ∧ IsLocalHom (algebraMap c.O A) ∧
      ∀ (Γ : Type) [TopologicalSpace Γ] (f : Γ → A), Alg.AdicCont (maximalIdeal A) f →
        Continuous fun g => (f g : PadicAlgCl l) := by
  let c' : Coef l := ⟨A.restrictScalars ℤ_[l], ‹IsDiscreteValuationRing A›,
    (Module.Finite.trans (R := ℤ_[l]) c.O A :)⟩
  haveI := (abelian₂.dvr_finite l c.O).1
  refine ⟨AlgebraTools.Conn.cplFinite (A := c.O) _ (maximalIdeal.isMaximal A).ne_top, Db.locHom c A, fun Γ _ f hf => ((UpperTheory.integrality_of_norm_coefficients l).2 c' Γ f).1 hf⟩

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.StationaryPhaseModel.matIrr_conj H h e`.
-/
theorem matIrr_conj {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {U : Subgroup Γ} {a a' : Γ → Matrix (Fin n) (Fin n) k}
    (H : MatIrr U a) (h : GL (Fin n) k) (e : ∀ g ∈ U, a' g = h.val * a g * (h⁻¹).val) : MatIrr U a' :=
  _root_.UpperTheory.Reformulated.B.StationaryPhaseModel.matIrr_conj H h e

/- English proof (translation)
Establish `hl : x.left = 1` using `Units.ext h1`. Simplify using `only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left, hl, h2, h3, inv_one, mul_one, one_mul, sgnAct_neg_one, map_one]`.
-/
private theorem left_conj {R : Type} [CommRing R] {m : ℕ} (x y : GG m R) (h1 : x.mat = 1) (h2 : x.right = -1)
    (h3 : y.right = 1) : (x * y * x⁻¹).left = theta y.left := by
  have hl : x.left = 1 := Units.ext h1
  simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left,
    hl, h2, h3, inv_one, mul_one, one_mul, sgnAct_neg_one, map_one]

/- English proof (translation)
Rewrite using `[theta_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (Jmat R m) (Jmat R m), Jmat_mul_Jmat, Matrix.mul_one, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one, Matrix.one_mul]`.
-/
private theorem pairing_theta {R : Type} [CommRing R] {m : ℕ} (a : GL (Fin m) R) :
    (a : Matrix (Fin m) (Fin m) R).transpose * Jmat R m * (theta a : GL (Fin m) R) = Jmat R m := by
  rw [theta_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (Jmat R m) (Jmat R m), Jmat_mul_Jmat,
    Matrix.mul_one, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one,
    Matrix.one_mul]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.ContinuousHomomorphism.cont_hom f h`.
-/
private theorem cont_hom {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ] [Monoid M] [TopologicalSpace M]
    (f : Γ →* Mˣ) (h : Continuous fun g => (f g : M)) : Continuous f :=
  _root_.UpperTheory.Reformulated.B.ContinuousHomomorphism.cont_hom f h

/- English proof (translation)
The claim follows from `Db.irr_of_matIrr n.succ_pos ⊤ _ h (MonoidHom.id Γ) (fun g _ => ⟨g, rfl⟩) r fun _ => rfl`.
-/
private theorem isIrr_of_matIrr {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin (n + 1)) k)
    (h : MatIrr ⊤ fun g => (r g).val) : Af.IsIrr r :=
  Db.irr_of_matIrr n.succ_pos ⊤ _ h (MonoidHom.id Γ) (fun g _ => ⟨g, rfl⟩) r fun _ => rfl

/- English proof (translation)
Introduce `W hW` and use `h W fun g hg v hv => by have := hW g hg v hv beta_reduce at this rwa [Af.tw_val, Matrix.smul_mulVec, W.smul_mem_iff (χ g).ne_zero] at this`.
-/
private theorem matIrr_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (h : MatIrr ⊤ fun g => (r g).val) : MatIrr ⊤ fun g => (Af.tw r χ g).val := fun W hW =>
  h W fun g hg v hv => by
    have := hW g hg v hv
    beta_reduce at this
    rwa [Af.tw_val, Matrix.smul_mulVec, W.smul_mem_iff (χ g).ne_zero] at this

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker η h`.
-/
private theorem lc_of_ker {Γ C : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group C] (η : Γ →* C)
    (h : IsOpen (η.ker : Set Γ)) : IsLocallyConstant η :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker η h

section Abs

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {K L : Type} [Field K] [NumberField K]
  [IsCMField K] [Algebra K Ω] [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω]
  {σ : G ℚ Ω} {R : G ℚ Ω →* GG 3 (PadicAlgCl l)} {ρ : G K Ω →* GL (Fin 3) (Qbar l)}

omit [IsAlgClosure ℚ Ω] [IsCMField K] in
/- English proof (translation)
Rewrite using `[hρ s', hs, map_mul, map_mul, map_inv, left_conj _ _ hatc hc (hK s), ← hρ]`. Conclude with `pairing_theta _`.
-/
private theorem pair_of (hρ : ∀ s, ρ s = (R (galEmb ℚ K Ω s)).left) (hK : ∀ s, (R (galEmb ℚ K Ω s)).right = 1)
    (hc : (R σ).right = -1) (hatc : (R σ).mat = 1) (s s' : G K Ω) (hs : galEmb ℚ K Ω s' = σ * galEmb ℚ K Ω s * σ⁻¹) :
    (ρ s).val.transpose * Jmat _ 3 * (ρ s').val = Jmat _ 3 := by
  rw [hρ s', hs, map_mul, map_mul, map_inv, left_conj _ _ hatc hc (hK s), ← hρ]
  exact pairing_theta _

/- English proof (translation)
Take `⟨_, hsol⟩` from `Db.galKL K L hab`. Use `haveI : Group.IsSolvable (L ≃ₐ[K] L) := hsol`. Take `⟨h', hiso⟩` from `hiso`. Establish `et : Af.tw (ρ.comp (galEmb K L Ω)) (cycBar L Ω l)⁻¹ = (Af.tw ρ (cycBar K Ω l)⁻¹).comp (galEmb K L Ω)` using `MonoidHom.ext fun s => Units.ext <| by`. Rewrite using `[Af.tw_val, MonoidHom.comp_apply, MonoidHom.comp_apply, Af.tw_val]`.

Both sides reduce to the same expression. Establish `hiT` using `isIrr_of_matIrr _ (matIrr_tw _ (cycBar L Ω l)⁻¹ hiL)`. Rewrite `hiT`, the goal using `[et]`. Use `upCsd hH K L Ω l ι 3 (by norm_num) (Af.tw ρ (cycBar K Ω l)⁻¹) σ hσ (Af.Bc.irrBasic.2 _ _ _ _ _ hρc (cyc_cont K Ω l).inv) (Jgl _ 3) (fun s s' hs => ?_) hiT (isAut_iso ((Af.autBridge hH K Ω l ι 3 _).2.2 haut) ⟨h', fun s => Units.ext ?_⟩ ((Af.Bc.irrBasic.1 _ _ _ 3 _).1 _ hiT))` and prove the remaining obligations. Establish `h1 : cycBar K Ω l s' = cycBar K Ω l s` using `by show cycBar ℚ Ω l (galEmb ℚ K Ω s') = cycBar ℚ Ω l (galEmb ℚ K Ω s)`.

Rewrite using `[hs, map_mul, map_mul, map_inv, mul_inv_cancel_comm]`. Establish `h3 : (cycBar K Ω l ^ (1 - ((3 : ℕ) : ℤ))) s = (cycBar K Ω l s)⁻¹ * (cycBar K Ω l s)⁻¹`. Rewrite using `[MonoidHom.zpow_apply, show (1 - ((3 : ℕ) : ℤ)) = -1 + -1 by norm_num, _root_.zpow_add, _root_.zpow_neg_one]`. Rewrite using `[Af.tw_val, Af.tw_val, MonoidHom.inv_apply, MonoidHom.inv_apply, h1, Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Units.val_mul, h3]`. Conclude with `congrArg _ (pair_of hρ hK hc hatc s s' hs)`.

Rewrite using `[Af.tw_val, hiso, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, Af.tw_val, Matrix.mul_smul, Matrix.smul_mul]`.
-/
private theorem aut_up (hH : Af.HypothesesH) (hab : IsAbelianGalois ℚ L) (ι : Qbar l ≃+* ℂ) (hσ : Sd.IsCC σ)
    (hρ : ∀ s, ρ s = (R (galEmb ℚ K Ω s)).left) (hK : ∀ s, (R (galEmb ℚ K Ω s)).right = 1)
    (hc : (R σ).right = -1) (hatc : (R σ).mat = 1) (hρc : Continuous ρ)
    (hiL : MatIrr ⊤ fun g => (ρ.comp (galEmb K L Ω) g).val) {ρ₀ : G K Ω →* GL (Fin 3) (Qbar l)} (hiso : Af.RepIso ρ₀ ρ)
    (haut : Af.IsAutCsd ι (Af.tw ρ₀ (cycBar K Ω l)⁻¹)) :
    Af.IsAutCsd ι (Af.tw (ρ.comp (galEmb K L Ω)) (cycBar L Ω l)⁻¹) := by
  obtain ⟨_, hsol⟩ := Db.galKL K L hab
  haveI : Group.IsSolvable (L ≃ₐ[K] L) := hsol
  obtain ⟨h', hiso⟩ := hiso
  have et : Af.tw (ρ.comp (galEmb K L Ω)) (cycBar L Ω l)⁻¹ = (Af.tw ρ (cycBar K Ω l)⁻¹).comp (galEmb K L Ω) :=
    MonoidHom.ext fun s => Units.ext <| by
      rw [Af.tw_val, MonoidHom.comp_apply, MonoidHom.comp_apply, Af.tw_val]
      rfl
  have hiT := isIrr_of_matIrr _ (matIrr_tw _ (cycBar L Ω l)⁻¹ hiL)
  rw [et] at hiT ⊢
  refine upCsd hH K L Ω l ι 3 (by norm_num) (Af.tw ρ (cycBar K Ω l)⁻¹) σ hσ
    (Af.Bc.irrBasic.2 _ _ _ _ _ hρc (cyc_cont K Ω l).inv) (Jgl _ 3) (fun s s' hs => ?_) hiT
    (isAut_iso ((Af.autBridge hH K Ω l ι 3 _).2.2 haut) ⟨h', fun s => Units.ext ?_⟩
      ((Af.Bc.irrBasic.1 _ _ _ 3 _).1 _ hiT))
  · have h1 : cycBar K Ω l s' = cycBar K Ω l s := by
      show cycBar ℚ Ω l (galEmb ℚ K Ω s') = cycBar ℚ Ω l (galEmb ℚ K Ω s)
      rw [hs, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    have h3 : (cycBar K Ω l ^ (1 - ((3 : ℕ) : ℤ))) s = (cycBar K Ω l s)⁻¹ * (cycBar K Ω l s)⁻¹ := by
      rw [MonoidHom.zpow_apply, show (1 - ((3 : ℕ) : ℤ)) = -1 + -1 by norm_num, _root_.zpow_add, _root_.zpow_neg_one]
    rw [Af.tw_val, Af.tw_val, MonoidHom.inv_apply, MonoidHom.inv_apply, h1, Matrix.transpose_smul,
      Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Units.val_mul, h3]
    exact congrArg _ (pair_of hρ hK hc hatc s s' hs)
  · rw [Af.tw_val, hiso, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, Af.tw_val, Matrix.mul_smul,
      Matrix.smul_mul]

/- English proof (translation)
Take `⟨s, V, τ, t1, t2, t3⟩` from `h`. Use `adDown Ω l K L hK2 (galOf_le ℚ K Ω L) s V 3 ρ 1 _ hρc ⟨σ, Jgl _ 3, hσ, fun s s' hs => ?_, fun s X => ?_, fun X => ?_⟩ τ ka (fun g t ht => ?_) (fun g g' t hg _ => ?_) t3` and prove the remaining obligations. Rewrite using `[MonoidHom.one_apply, Units.val_one, one_smul]`. Conclude with `pair_of hρ hK hc hatc s s' hs`. Use `show (R (galEmb ℚ K Ω s)).adFun X = _`.

Rewrite using `[GG.adFun, if_pos (hK s), hρ]`. Both sides reduce to the same expression. Establish `hl1 : (R σ).left = 1` using `Units.ext hatc show (R σ).adFun X = _`. Rewrite using `[GG.adFun, hc, if_neg (by decide), hatc, hl1, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]`. Both sides reduce to the same expression.

Take `rfl : galEmb K L Ω g = t` from `AlgEquiv.ext fun x => DFunLike.congr_fun ht x`. Conclude with `t1 g`. Rewrite using `[MonoidHom.one_apply, mul_one]`. Conclude with `t2 g g' hg`.
-/
private theorem ad_down [IsAlgClosure L Ω] (hK2 : Module.finrank ℚ K = 2) (hσ : Sd.IsCC σ)
    (hρ : ∀ s, ρ s = (R (galEmb ℚ K Ω s)).left) (hK : ∀ s, (R (galEmb ℚ K Ω s)).right = 1)
    (hc : (R σ).right = -1) (hatc : (R σ).mat = 1) (hρc : Continuous ρ) {ka : G L Ω →* (Qbar l)ˣ}
    (h : RigOver (ρ.comp (galEmb K L Ω)) ka) : Af.BlochKatoSelmerVanishes l (adRep R) := by
  obtain ⟨s, V, τ, t1, t2, t3⟩ := h
  refine adDown Ω l K L hK2 (galOf_le ℚ K Ω L) s V 3 ρ 1 _ hρc
    ⟨σ, Jgl _ 3, hσ, fun s s' hs => ?_, fun s X => ?_, fun X => ?_⟩ τ ka (fun g t ht => ?_) (fun g g' t hg _ => ?_) t3
  · rw [MonoidHom.one_apply, Units.val_one, one_smul]
    exact pair_of hρ hK hc hatc s s' hs
  · show (R (galEmb ℚ K Ω s)).adFun X = _
    rw [GG.adFun, if_pos (hK s), hρ]
    rfl
  · have hl1 : (R σ).left = 1 := Units.ext hatc
    show (R σ).adFun X = _
    rw [GG.adFun, hc, if_neg (by decide), hatc, hl1, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
    rfl
  · obtain rfl : galEmb K L Ω g = t := AlgEquiv.ext fun x => DFunLike.congr_fun ht x
    exact t1 g
  · rw [MonoidHom.one_apply, mul_one]
    exact t2 g g' hg

end Abs

end UpperTheory.V.Th.End3

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
attribute [local instance 10000] IsDiscreteValuationRing.toIsLocalRing

set_option maxHeartbeats 400000 in
open UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Th.End3 in
/- English proof (translation)
Introduce `hH hAd Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H hΨ hF A _ _ r hr hirr K _ _ _ _ hK2 hker ρ hρ haut hfree`. Take `⟨L, _, _, _, _, g₂, Φ, C₀, ⟨k⟩, hok, hbig, hseed⟩` from `hF`. Use `haveI := algClo K Ω`. Use `haveI := algClo L Ω`. Take `⟨hcpl, hloc, hcont⟩` from `sub_facts c A`.

Establish `hl : l ∣ M` using `(dvd_mul_right l N).trans H.dvd`. Establish `hσ : σ * σ = 1` using `Db.cc_sq H.cc`. Establish `hM` using `Pr.marks_of_link k hok hl hσ hΨ`. Establish `h2 : IsUnit (2 : c.O)`. Rewrite using `[← residue_ne_zero_iff_isUnit, map_ofNat]`.

Introduce `h0`. Conclude with `hok.l_odd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 ((CharP.cast_eq_zero_iff (ResidueField c.O) l 2).1 (by exact_mod_cast h0)))`. Take `⟨h, -, hr'⟩` from `ordPt_renorm hr (lc_of_ker η (hker ▸ (galEmbTop ℚ K Ω).2.1)) h2 hM`. Set `h' : GL (Fin 3) (Qbar l)` to `Matrix.GeneralLinearGroup.map (A.val : A →+* PadicAlgCl l) h`. Establish `eR : UnitaryThreeInertia.push A.val (conjBy h r) = conjBy h' (UnitaryThreeInertia.push A.val r)` using `map_conjBy _ h r`.

Use `h1fZero_conjBy _ h' ?_` and prove the remaining obligations. Rewrite using `[← eR]`. Establish `hmat : ∀ g ∈ η.ker, (UnitaryThreeInertia.push A.val (conjBy h r) g).left = h' * (UnitaryThreeInertia.push A.val r g).left * h'⁻¹` using `fun g hg => by`. Rewrite using `[eR, conjBy_left, show (UnitaryThreeInertia.push A.val r g).right = 1 from (hr.red.mult g).trans hg, sgnAct_one]`. Establish `hmem : ∀ s : G K Ω, galEmb ℚ K Ω s ∈ η.ker` using `fun s => hker ▸ galEmb_mem ℚ K Ω s`.

Set `ρ' : G K Ω →* GL (Fin 3) (Qbar l)` to `(MulAut.conj h').toMonoidHom.comp ρ`. Establish `hiso : ∀ s, ρ' s = h' * ρ s * h'⁻¹` using `fun _ => rfl`. Establish `hρ' : ∀ s, ρ' s = (UnitaryThreeInertia.push A.val (conjBy h r) (galEmb ℚ K Ω s)).left` using `fun s => by`. Rewrite using `[hmat _ (hmem s), hiso, show ρ s = _ from Units.ext (hρ s)]`. Establish `hLη : galOf ℚ L Ω ≤ η.ker` using `Db.galL_le k`.

Establish `hirr' : MatIrr (galOf ℚ L Ω) (mats (UnitaryThreeInertia.push A.val (conjBy h r)))` using `matIrr_conj (hirr _ (galEmbTop ℚ L Ω).2.1 hLη) h' fun g hg => congrArg Units.val (hmat g (hLη hg))`. Generalize the expression as in `conjBy h r = r' at hr' hρ' hirr'`. Establish `hright : ∀ g, (UnitaryThreeInertia.push A.val r' g).right = η g` using `hr'.red.mult`. Establish `hatc : (UnitaryThreeInertia.push A.val r' σ).mat = 1`. Rewrite using `[MonoidHom.comp_apply, GG.map_mat, hr'.norm.atc, Matrix.map_one _ (map_zero _) (map_one _)]`.

Establish `hc : (UnitaryThreeInertia.push A.val r' σ).right = -1` using `(hright σ).trans hM.ηc`. Establish `hK : ∀ s, (UnitaryThreeInertia.push A.val r' (galEmb ℚ K Ω s)).right = 1` using `fun s => (hright _).trans (hmem s)`. Establish `hρc : Continuous ρ'`. Use `cont_hom _ (continuous_matrix fun a b => ?_)` and prove the remaining obligations. Simplify using `only [hρ']`.

Conclude with `(hcont _ (fun g => (r' g).mat a b) fun n => (hr'.cont n).comp fun X => X a b).comp (galEmbTop ℚ K Ω).1.continuous`. Take `⟨_, _⟩` from `Db.algKL K L Ω (hLη.trans hker.le)`. Establish `hiL : MatIrr ⊤ fun g => (ρ'.comp (galEmb K L Ω) g).val` using `fun W hW => hirr' W fun g hg => by`. Rewrite `hg` using `[← range_galEmb]`. Take `⟨s, rfl⟩` from `hg`.

Use `hW s trivial` as an intermediate fact. Use `beta_reduce at this`. Rewrite `this` using `[MonoidHom.comp_apply, hρ']`. Then use the resulting hypothesis. Establish `hautL` using `aut_up hH k.ab ι H.cc hρ' hK hc hatc hρc hiL ⟨h', hiso⟩ haut`. Take `⟨ν, n1, n2, n3⟩` from `Pr.exists_nrep3 k hok hl hσ r' hr'`.

Establish `key` using `(linkedRig hH hAd Ω l ι c N e ψ η σ g₂ B M H L Φ C₀ k hok hbig hseed).1`. Establish `n4 : ∀ s, (ρ'.comp (galEmb K L Ω) s).val = (ν.r (k.p0 s)).map A.val` using `fun s => by`. Rewrite using `[n2, MonoidHom.comp_apply, hρ']`. Both sides reduce to the same expression. Establish `n5 : ∀ v i, ∀ g ∈ Φ.Iv v, (ν.ψ v i g).val = algebraMap c.O A (Chr.Psi l e (Chr.dirG ℚ Ω ψ) (k.j v g) ^ Fr.w 3 i).val` using `fun v i g hg => by`.

Rewrite using `[n3 v i g hg, Fr.w, if_pos rfl]`. Both sides reduce to the same expression. Conclude with `ad_down hK2 H.cc hρ' hK hc hatc hρc (key A ν n1 n5 _ n4 (isIrr_of_matIrr _ hiL) hautL (freeAt_res (freeAt_iso hfree ⟨h', hiso⟩)))`.
-/
theorem UpperTheory.V.Th.rigEnd3 :
    Af.HypothesesH → AdL → RigEnd3 := by
  intro hH hAd Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H hΨ hF A _ _ r hr hirr K _ _ _ _ hK2 hker ρ hρ haut hfree
  obtain ⟨L, _, _, _, _, g₂, Φ, C₀, ⟨k⟩, hok, hbig, hseed⟩ := hF
  haveI := algClo K Ω
  haveI := algClo L Ω
  obtain ⟨hcpl, hloc, hcont⟩ := sub_facts c A
  have hl : l ∣ M := (dvd_mul_right l N).trans H.dvd
  have hσ : σ * σ = 1 := Db.cc_sq H.cc
  have hM := Pr.marks_of_link k hok hl hσ hΨ
  have h2 : IsUnit (2 : c.O) := by
    rw [← residue_ne_zero_iff_isUnit, map_ofNat]
    intro h0
    exact hok.l_odd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1
      ((CharP.cast_eq_zero_iff (ResidueField c.O) l 2).1 (by exact_mod_cast h0)))
  obtain ⟨h, -, hr'⟩ := ordPt_renorm hr (lc_of_ker η (hker ▸ (galEmbTop ℚ K Ω).2.1)) h2 hM
  let h' : GL (Fin 3) (Qbar l) := Matrix.GeneralLinearGroup.map (A.val : A →+* PadicAlgCl l) h
  have eR : UnitaryThreeInertia.push A.val (conjBy h r) = conjBy h' (UnitaryThreeInertia.push A.val r) := map_conjBy _ h r
  refine h1fZero_conjBy _ h' ?_
  rw [← eR]
  have hmat : ∀ g ∈ η.ker, (UnitaryThreeInertia.push A.val (conjBy h r) g).left = h' * (UnitaryThreeInertia.push A.val r g).left * h'⁻¹ := fun g hg => by
    rw [eR, conjBy_left, show (UnitaryThreeInertia.push A.val r g).right = 1 from (hr.red.mult g).trans hg, sgnAct_one]
  have hmem : ∀ s : G K Ω, galEmb ℚ K Ω s ∈ η.ker := fun s => hker ▸ galEmb_mem ℚ K Ω s
  let ρ' : G K Ω →* GL (Fin 3) (Qbar l) := (MulAut.conj h').toMonoidHom.comp ρ
  have hiso : ∀ s, ρ' s = h' * ρ s * h'⁻¹ := fun _ => rfl
  have hρ' : ∀ s, ρ' s = (UnitaryThreeInertia.push A.val (conjBy h r) (galEmb ℚ K Ω s)).left := fun s => by
    rw [hmat _ (hmem s), hiso, show ρ s = _ from Units.ext (hρ s)]
  have hLη : galOf ℚ L Ω ≤ η.ker := Db.galL_le k
  have hirr' : MatIrr (galOf ℚ L Ω) (mats (UnitaryThreeInertia.push A.val (conjBy h r))) :=
    matIrr_conj (hirr _ (galEmbTop ℚ L Ω).2.1 hLη) h' fun g hg => congrArg Units.val (hmat g (hLη hg))
  generalize conjBy h r = r' at hr' hρ' hirr'
  have hright : ∀ g, (UnitaryThreeInertia.push A.val r' g).right = η g := hr'.red.mult
  have hatc : (UnitaryThreeInertia.push A.val r' σ).mat = 1 := by
    rw [MonoidHom.comp_apply, GG.map_mat, hr'.norm.atc, Matrix.map_one _ (map_zero _) (map_one _)]
  have hc : (UnitaryThreeInertia.push A.val r' σ).right = -1 := (hright σ).trans hM.ηc
  have hK : ∀ s, (UnitaryThreeInertia.push A.val r' (galEmb ℚ K Ω s)).right = 1 := fun s => (hright _).trans (hmem s)
  have hρc : Continuous ρ' := by
    refine cont_hom _ (continuous_matrix fun a b => ?_)
    simp only [hρ']
    exact (hcont _ (fun g => (r' g).mat a b) fun n => (hr'.cont n).comp fun X => X a b).comp (galEmbTop ℚ K Ω).1.continuous
  obtain ⟨_, _⟩ := Db.algKL K L Ω (hLη.trans hker.le)
  have hiL : MatIrr ⊤ fun g => (ρ'.comp (galEmb K L Ω) g).val := fun W hW => hirr' W fun g hg => by
    rw [← range_galEmb] at hg
    obtain ⟨s, rfl⟩ := hg
    have := hW s trivial
    beta_reduce at this
    rwa [MonoidHom.comp_apply, hρ'] at this
  have hautL := aut_up hH k.ab ι H.cc hρ' hK hc hatc hρc hiL ⟨h', hiso⟩ haut
  obtain ⟨ν, n1, n2, n3⟩ := Pr.exists_nrep3 k hok hl hσ r' hr'
  have key := (linkedRig hH hAd Ω l ι c N e ψ η σ g₂ B M H L Φ C₀ k hok hbig hseed).1
  have n4 : ∀ s, (ρ'.comp (galEmb K L Ω) s).val = (ν.r (k.p0 s)).map A.val := fun s => by
    rw [n2, MonoidHom.comp_apply, hρ']
    rfl
  have n5 : ∀ v i, ∀ g ∈ Φ.Iv v, (ν.ψ v i g).val =
      algebraMap c.O A (Chr.Psi l e (Chr.dirG ℚ Ω ψ) (k.j v g) ^ Fr.w 3 i).val := fun v i g hg => by
    rw [n3 v i g hg, Fr.w, if_pos rfl]
    rfl
  exact ad_down hK2 H.cc hρ' hK hc hatc hρc
    (key A ν n1 n5 _ n4 (isIrr_of_matIrr _ hiL) hautL (freeAt_res (freeAt_iso hfree ⟨h', hiso⟩)))
