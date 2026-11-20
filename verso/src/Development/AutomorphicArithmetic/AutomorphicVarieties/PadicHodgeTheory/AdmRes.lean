import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrField
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OpenField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictCrystallineDeRhamFiniteExt
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc.AdmRes

variable {l : ℕ} [Fact l.Prime]

section Transport

variable {G G' A A' V : Type} [Group G] [Group G'] [CommRing A] [Algebra ℚ_[l] A] [CommRing A'] [Algebra ℚ_[l] A']
  [AddCommGroup V] [Module A V] [Module A' V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [IsScalarTower ℚ_[l] A' V]
  {φ : G →* GQ l} {ρ : Representation A G V} {φ' : G' →* GQ l} {ρ' : Representation A' G' V}

/- English proof (translation)
Establish `hr : φ.range = φ'.range`. Use extensionality with `σ`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, rfl⟩`. Conclude with `⟨e g, h1 g⟩`.

Introduce and unpack `⟨g, rfl⟩`. Take `⟨g, rfl⟩` from `he g`. Conclude with `⟨g, (h1 g).symm⟩`. Establish `hρ : ∀ g, resCoef ℚ_[l] ρ' (e g) = resCoef ℚ_[l] ρ g` using `fun g => LinearMap.ext fun x => h2 g x`. Establish `hc : Dcr φ (resCoef ℚ_[l] ρ) = Dcr φ' (resCoef ℚ_[l] ρ')`.

Unfold `Dcr`. Rewrite using `[he.iInf_comp (fun g => LinearMap.ker (actC φ' (resCoef ℚ_[l] ρ') g - LinearMap.id)) |>.symm]`. Use `iInf_congr fun g => ?_` and prove the remaining obligations. Unfold `actC`. Rewrite using `[hρ, h1]`.

Establish `hd : Ddr φ (resCoef ℚ_[l] ρ) = Ddr φ' (resCoef ℚ_[l] ρ')`. Unfold `Ddr`. Rewrite using `[he.iInf_comp (fun g => LinearMap.ker (actD φ' (resCoef ℚ_[l] ρ') g - LinearMap.id)) |>.symm]`. Use `iInf_congr fun g => ?_` and prove the remaining obligations. Unfold `actD`.

Rewrite using `[hρ, h1]`. Unfold `IsCr IsDr`. Rewrite using `[hr, hc, hd]`. Conclude with `⟨Iff.rfl, Iff.rfl⟩`.
-/
private theorem transport (e : G → G') (he : Function.Surjective e) (h1 : ∀ g, φ' (e g) = φ g)
    (h2 : ∀ g x, ρ' (e g) x = ρ g x) : (IsCr φ ρ ↔ IsCr φ' ρ') ∧ (IsDr φ ρ ↔ IsDr φ' ρ') := by
  have hr : φ.range = φ'.range := by
    ext σ
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨e g, h1 g⟩
    · rintro ⟨g, rfl⟩
      obtain ⟨g, rfl⟩ := he g
      exact ⟨g, (h1 g).symm⟩
  have hρ : ∀ g, resCoef ℚ_[l] ρ' (e g) = resCoef ℚ_[l] ρ g := fun g => LinearMap.ext fun x => h2 g x
  have hc : Dcr φ (resCoef ℚ_[l] ρ) = Dcr φ' (resCoef ℚ_[l] ρ') := by
    unfold Dcr
    rw [he.iInf_comp (fun g => LinearMap.ker (actC φ' (resCoef ℚ_[l] ρ') g - LinearMap.id)) |>.symm]
    refine iInf_congr fun g => ?_
    unfold actC
    rw [hρ, h1]
  have hd : Ddr φ (resCoef ℚ_[l] ρ) = Ddr φ' (resCoef ℚ_[l] ρ') := by
    unfold Ddr
    rw [he.iInf_comp (fun g => LinearMap.ker (actD φ' (resCoef ℚ_[l] ρ') g - LinearMap.id)) |>.symm]
    refine iInf_congr fun g => ?_
    unfold actD
    rw [hρ, h1]
  unfold IsCr IsDr
  rw [hr, hc, hd]
  exact ⟨Iff.rfl, Iff.rfl⟩

end Transport

/- English proof (translation)
Use `LL.2` as an intermediate fact. Establish `: FiniteDimensional ↥LL.1 V` using `Module.Finite.of_restrictScalars_finite ℚ_[l] ↥LL.1 V`. Take `⟨T⟩` from `tiedP l`. Establish `hres` using `GlobalTheory.Per.TiedRestrict.restrict_crys_deRham l (PP l) (AIP l) T K K' LL h V ρ`. Rewrite using `[(isCrIff K ρ).1, (isCrIff K ρ).2, (isCrIff K' _).1, (isCrIff K' _).2, (isCrField K ρ).1, (isCrField K ρ).2.1, (isCrField K' _).1, (isCrField K' _).2.1]`.

Conclude with `⟨fun hc => (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (PP l) (AIP l) T K LL V ρ hc).1, hres.1, hres.2⟩`.
-/
private theorem field_case (K K' LL : FinExt l) (h : K.1 ≤ K'.1) {V : Type} [AddCommGroup V] [Module ↥LL.1 V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V]
    [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul ↥LL.1 V]
    (ρ : Representation ↥LL.1 ↥(GK K) V) :
    (IsCr (GK K).subtype ρ → IsDr (GK K).subtype ρ) ∧
      (IsCr (GK K).subtype ρ → IsCr (GK K').subtype (ρ.comp (incl h) : Representation ↥LL.1 ↥(GK K') V)) ∧
      (IsDr (GK K).subtype ρ ↔ IsDr (GK K').subtype (ρ.comp (incl h) : Representation ↥LL.1 ↥(GK K') V)) := by
  have := LL.2
  have : FiniteDimensional ↥LL.1 V := Module.Finite.of_restrictScalars_finite ℚ_[l] ↥LL.1 V
  obtain ⟨T⟩ := tiedP l
  have hres := GlobalTheory.Per.TiedRestrict.restrict_crys_deRham l (PP l) (AIP l) T K K' LL h V ρ
  rw [(isCrIff K ρ).1, (isCrIff K ρ).2, (isCrIff K' _).1, (isCrIff K' _).2, (isCrField K ρ).1, (isCrField K ρ).2.1,
    (isCrField K' _).1, (isCrField K' _).2.1]
  exact ⟨fun hc => (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (PP l) (AIP l) T K LL V ρ hc).1, hres.1, hres.2⟩

/- English proof (translation)
Set `β : ↥(botExt l).1 ≃ₐ[ℚ_[l]] ℚ_[l]` to `IntermediateField.botEquiv ℚ_[l] (Om l)`. Use `letI : Module ↥(botExt l).1 V := Module.compHom V (β : ↥(botExt l).1 →+* ℚ_[l])`. Establish `hs : ∀ (c : ↥(botExt l).1) (x : V), c • x = β c • x` using `fun _ _ => rfl`. Use `haveI : IsScalarTower ℚ_[l] ↥(botExt l).1 V := ⟨fun a c x => by`. Rewrite using `[hs, hs, Algebra.smul_def, map_mul, β.commutes, mul_smul]`.

Use the proof step `rfl⟩`. Use `haveI : ContinuousConstSMul ↥(botExt l).1 V := ⟨fun c => continuous_const_smul (β c)⟩`. Set `ρ' : Representation ↥(botExt l).1 ↥(GK K) V` to `{ toFun := fun g => { toFun := ρ g map_add' := map_add _ map_smul' := fun c x => by`. Rewrite using `[RingHom.id_apply, hs, hs]`. Conclude with `LinearMap.map_smul_of_tower _ _ _ }`.

Use the proof step `map_one' := by ext x; simp`. Use the proof step `map_mul' := fun g g' => by ext x; simp }`. Establish `t1` using `transport (φ := (GK K).subtype) (ρ := ρ) (φ' := (GK K).subtype) (ρ' := ρ') id Function.surjective_id (fun _ => rfl) (fun _ _ => rfl)`. Establish `t2` using `transport (φ := (GK K').subtype) (ρ := (ρ.comp (incl h) : Representation A ↥(GK K') V)) (φ' := (GK K').subtype) (ρ' := (ρ'.comp (incl h) : Representation ↥(botExt l).1 ↥(GK K') V)) id Function.surjective_id (fun _ => rfl) (fun _ _ => rfl)`. Rewrite using `[t1.1, t1.2, t2.1, t2.2]`.

Conclude with `field_case K K' (botExt l) h ρ'`.
-/
private theorem gal_case (K K' : FinExt l) (h : K.1 ≤ K'.1) {A V : Type} [CommRing A] [Algebra ℚ_[l] A]
    [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V]
    [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V]
    (ρ : Representation A ↥(GK K) V) :
    (IsCr (GK K).subtype ρ → IsDr (GK K).subtype ρ) ∧
      (IsCr (GK K).subtype ρ → IsCr (GK K').subtype (ρ.comp (incl h) : Representation A ↥(GK K') V)) ∧
      (IsDr (GK K).subtype ρ ↔ IsDr (GK K').subtype (ρ.comp (incl h) : Representation A ↥(GK K') V)) := by
  let β : ↥(botExt l).1 ≃ₐ[ℚ_[l]] ℚ_[l] := IntermediateField.botEquiv ℚ_[l] (Om l)
  letI : Module ↥(botExt l).1 V := Module.compHom V (β : ↥(botExt l).1 →+* ℚ_[l])
  have hs : ∀ (c : ↥(botExt l).1) (x : V), c • x = β c • x := fun _ _ => rfl
  haveI : IsScalarTower ℚ_[l] ↥(botExt l).1 V := ⟨fun a c x => by
    rw [hs, hs, Algebra.smul_def, map_mul, β.commutes, mul_smul]; rfl⟩
  haveI : ContinuousConstSMul ↥(botExt l).1 V := ⟨fun c => continuous_const_smul (β c)⟩
  let ρ' : Representation ↥(botExt l).1 ↥(GK K) V :=
    { toFun := fun g =>
        { toFun := ρ g
          map_add' := map_add _
          map_smul' := fun c x => by
            rw [RingHom.id_apply, hs, hs]
            exact LinearMap.map_smul_of_tower _ _ _ }
      map_one' := by ext x; simp
      map_mul' := fun g g' => by ext x; simp }
  have t1 := transport (φ := (GK K).subtype) (ρ := ρ) (φ' := (GK K).subtype) (ρ' := ρ') id
    Function.surjective_id (fun _ => rfl) (fun _ _ => rfl)
  have t2 := transport (φ := (GK K').subtype) (ρ := (ρ.comp (incl h) : Representation A ↥(GK K') V))
    (φ' := (GK K').subtype) (ρ' := (ρ'.comp (incl h) : Representation ↥(botExt l).1 ↥(GK K') V)) id
    Function.surjective_id (fun _ => rfl) (fun _ _ => rfl)
  rw [t1.1, t1.2, t2.1, t2.2]
  exact field_case K K' (botExt l) h ρ'

end UpperTheory.V.Loc.AdmRes

open UpperTheory.V.Loc.AdmRes in
/- English proof (translation)
Introduce `l _ G _ _ _ φ hφ A _ _ V _ _ _ _ _ _ _ _ _ ρ _`. Take `⟨K, e, -, -, he, hK, -, -⟩` from `openField φ hφ`. Establish `he' : ∀ g, ((e g : ↥(GK K)) : GQ l) = φ g` using `fun g => DFunLike.congr_fun he g`. Set `ρK : Representation A ↥(GK K) V` to `ρ.comp e.symm.toMonoidHom`. Establish `t1` using `transport (φ := φ) (ρ := ρ) (φ' := (GK K).subtype) (ρ' := ρK) e e.surjective he' (fun g x => by simp [ρK])`.

Use `⟨?_, fun H hH => ?_⟩` and prove the remaining obligations. Rewrite using `[t1.1, t1.2]`. Conclude with `(gal_case K K le_rfl ρK).1`. Establish `hφH : IsOpenEmbedding (φ.comp H.subtype)` using `hφ.comp hH.isOpenEmbedding_subtypeVal`. Take `⟨K', e', -, -, hf, hK', -, -⟩` from `openField (φ.comp H.subtype) hφH`.

Establish `hf' : ∀ g, ((e' g : ↥(GK K')) : GQ l) = φ g` using `fun g => DFunLike.congr_fun hf g`. Establish `hle : GK K' ≤ GK K`. Rewrite using `[← hK, ← hK']`. Introduce and unpack `_ ⟨g, rfl⟩`. Conclude with `⟨g, rfl⟩`.

Establish `h : K.1 ≤ K'.1`. Establish `: IsGalois ℚ_[l] (Om l)` using `inferInstance`. Rewrite using `[← InfiniteGalois.fixedField_fixingSubgroup K.1, ← InfiniteGalois.fixedField_fixingSubgroup K'.1]`. Conclude with `IntermediateField.fixedField_le hle`. Establish `t2` using `transport (φ := φ.comp H.subtype) (ρ := (ρ.comp H.subtype : Representation A H V)) (φ' := (GK K').subtype) (ρ' := (ρK.comp (incl h) : Representation A ↥(GK K') V)) e' e'.surjective hf' (fun g x => by`.

Establish `: incl h (e' g) = e g` using `Subtype.ext ((hf' g).trans (he' g).symm)`. Simplify using `[ρK, this])`. Unfold `CrOn`. Rewrite using `[t1.1, t1.2, t2.1, t2.2]`. Conclude with `(gal_case K K' h ρK).2`.
-/
theorem UpperTheory.V.Loc.isCrys_isDR_restrict_openSubgroup :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] (ρ : Representation A G V), ContAction ρ → (IsCr φ ρ → IsDr φ ρ) ∧ ∀ H : Subgroup G, IsOpen (H : Set G) → (IsCr φ ρ → CrOn φ ρ H) ∧ (IsDr φ ρ ↔ IsDr (φ.comp H.subtype) (ρ.comp H.subtype : Representation A H V)) := by
  intro l _ G _ _ _ φ hφ A _ _ V _ _ _ _ _ _ _ _ _ ρ _
  obtain ⟨K, e, -, -, he, hK, -, -⟩ := openField φ hφ
  have he' : ∀ g, ((e g : ↥(GK K)) : GQ l) = φ g := fun g => DFunLike.congr_fun he g
  let ρK : Representation A ↥(GK K) V := ρ.comp e.symm.toMonoidHom
  have t1 := transport (φ := φ) (ρ := ρ) (φ' := (GK K).subtype) (ρ' := ρK) e e.surjective he'
    (fun g x => by simp [ρK])
  refine ⟨?_, fun H hH => ?_⟩
  · rw [t1.1, t1.2]
    exact (gal_case K K le_rfl ρK).1
  have hφH : IsOpenEmbedding (φ.comp H.subtype) := hφ.comp hH.isOpenEmbedding_subtypeVal
  obtain ⟨K', e', -, -, hf, hK', -, -⟩ := openField (φ.comp H.subtype) hφH
  have hf' : ∀ g, ((e' g : ↥(GK K')) : GQ l) = φ g := fun g => DFunLike.congr_fun hf g
  have hle : GK K' ≤ GK K := by
    rw [← hK, ← hK']
    rintro _ ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have h : K.1 ≤ K'.1 := by
    have : IsGalois ℚ_[l] (Om l) := inferInstance
    rw [← InfiniteGalois.fixedField_fixingSubgroup K.1, ← InfiniteGalois.fixedField_fixingSubgroup K'.1]
    exact IntermediateField.fixedField_le hle
  have t2 := transport (φ := φ.comp H.subtype) (ρ := (ρ.comp H.subtype : Representation A H V))
    (φ' := (GK K').subtype) (ρ' := (ρK.comp (incl h) : Representation A ↥(GK K') V)) e' e'.surjective hf'
    (fun g x => by
      have : incl h (e' g) = e g := Subtype.ext ((hf' g).trans (he' g).symm)
      simp [ρK, this])
  unfold CrOn
  rw [t1.1, t1.2, t2.1, t2.2]
  exact (gal_case K K' h ρK).2
