import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

/- English proof (translation)
Rewrite using `[HasRingHomProperty.Spec_iff (P := @Flat)]`. Express the relevant statement in the definitionally equal form `φ.Flat`. Use `algebraize [φ]`. Express the relevant statement in the definitionally equal form `Module.Flat V O`. Rewrite using `[IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]`.

Introduce and unpack `t ⟨⟨a, ha⟩, ht⟩`. Establish `h1 : φ a * t = 0` using `ht`. Break down `mul_eq_zero.1 h1 with h | h` into its components or cases. Conclude with `absurd (hφ (h.trans (map_zero φ).symm)) (nonZeroDivisors.ne_zero ha)`. Conclude with `h`.
-/
theorem flat_injective_dvr {V O : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing O] [IsDomain O]
    (φ : V →+* O) (hφ : Function.Injective φ) : Flat (Spec.map (CommRingCat.ofHom φ)) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  change φ.Flat
  algebraize [φ]
  change Module.Flat V O
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
  rintro t ⟨⟨a, ha⟩, ht⟩
  have h1 : φ a * t = 0 := ht
  rcases mul_eq_zero.1 h1 with h | h
  · exact absurd (hφ (h.trans (map_zero φ).symm)) (nonZeroDivisors.ne_zero ha)
  · exact h

/- English proof (translation)
Use `set K := FractionRing O`. Use `set φ' := Spec.map (CommRingCat.ofHom φ)`. Use `set ι' : Spec (.of K) ⟶ Spec (.of O) := Spec.map (CommRingCat.ofHom (algebraMap O K))`. Use `set f : V →+* K := (algebraMap O K).comp φ`. Establish `hf : Function.Injective f` using `(IsFractionRing.injective O K).comp hφ`.

Establish `hfe : spMap f = ι' ≫ φ'`. Simplify using `only [spMap, ι', φ', f, ← Spec.map_comp]`. Both sides reduce to the same expression. Use `haveI hWi := hg K f hf`. Use `set Wk := pullback (Xw.ι ≫ s) (spMap f)`.

Set `m : Wk ⟶ pullback s φ'` to `pullback.lift (pullback.fst _ _ ≫ Xw.ι) (pullback.snd _ _ ≫ ι') (by`. Simplify using `only [Category.assoc]`. Rewrite using `[← hfe]`. Conclude with `pullback.condition)`. Use `haveI : Flat φ' := flat_injective_dvr φ hφ`.

Establish `gfst : GeneralizingMap (pullback.fst s φ')`. Conclude with `Flat.generalizingMap _`. Establish `gsnd : GeneralizingMap (pullback.snd s φ')`. Conclude with `Flat.generalizingMap _`. Use `haveI : IrreducibleSpace X := inferInstance`.

Use `set η := genericPoint X`. Take `⟨w₀⟩` from `(inferInstance : Nonempty Wk)`. Establish `hη : η ∈ Xw`. Conclude with `((genericPoint_spec X).mem_open_set_iff Xw.isOpen).2 ⟨_, trivial, (pullback.fst (Xw.ι ≫ s) (spMap f) w₀).2⟩`. Establish `key : ∀ x : ↥(pullback s φ'), x ∈ closure (Set.range m)`.

Introduce `x`. Take `⟨x₁, hx₁, hx₁s⟩` from `gsnd (b := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O)) (a := x) ((PrimeSpectrum.le_iff_specializes _ _).1 bot_le)`. Take `⟨x₂, hx₂, hx₂f⟩` from `gfst (genericPoint_specializes (pullback.fst s φ' x₁))`. Establish `hs₂ : pullback.snd s φ' x₂ = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O)`. Use `(hx₂.map (pullback.snd s φ').continuous)` as an intermediate fact.

Rewrite `this` using `[hx₁s]`. Conclude with `PrimeSpectrum.ext (le_bot_iff.1 ((PrimeSpectrum.le_iff_specializes _ _).2 this))`. Establish `hι : ι' (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O)`. Use `bot_map (X := Spec (.of O)) (IsFractionRing.injective O K) (𝟙 _)` as an intermediate fact. Conclude with `this`.

Take `⟨z, hz₁, hz₂⟩` from `Scheme.Pullback.exists_preimage_pullback (f := pullback.snd s φ') (g := ι') x₂ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) (by rw [hs₂, hι])`. Take `⟨y, hy₁, hy₂⟩` from `Scheme.Pullback.exists_preimage_pullback (f := Xw.ι) (g := pullback.fst (pullback.snd s φ') ι' ≫ pullback.fst s φ') ⟨η, hη⟩ z (by rw [Scheme.Hom.comp_apply, hz₁, hx₂f]; rfl)`. Set `h : pullback Xw.ι (pullback.fst (pullback.snd s φ') ι' ≫ pullback.fst s φ') ⟶ Wk` to `pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd _ _) (by`. Simplify using `only [Category.assoc]`. Rewrite using `[pullback.condition_assoc, Category.assoc, pullback.condition, pullback.condition_assoc, hfe])`.

Establish `hm : h ≫ m = pullback.snd _ _ ≫ pullback.fst (pullback.snd s φ') ι'`. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [Category.assoc, m, h, pullback.lift_fst, pullback.lift_fst_assoc]`. Rewrite using `[pullback.condition]`. Simplify using `only [Category.assoc, m, h, pullback.lift_snd, pullback.lift_snd_assoc]`.

Rewrite using `[pullback.condition]`. Establish `hx₂m : x₂ ∈ Set.range m` using `⟨h y, by`. Rewrite using `[← Scheme.Hom.comp_apply, hm, Scheme.Hom.comp_apply, hy₂, hz₁]⟩`. Conclude with `closure_mono (Set.singleton_subset_iff.2 hx₂m) (hx₂.trans hx₁).mem_closure`. Establish `hirr : IsIrreducible (Set.range m)`.

Rewrite using `[← Set.image_univ]`. Conclude with `(IrreducibleSpace.isIrreducible_univ Wk).image _ m.continuous.continuousOn`. Establish `: IrreducibleSpace ↑(pullback s φ')`. Establish `hcl` using `hirr.closure`. Rewrite `hcl` using `[Set.eq_univ_of_forall key]`.

Conclude with `(irreducibleSpace_def _).2 hcl`. Use `infer_instance`.
-/
theorem connected_pullback_of_geomIrr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (O : Type)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (φ : V →+* O) (hφ : Function.Injective φ)
    (_hloc : IsLocalHom φ) (X : Scheme.{0}) (s : X ⟶ Spec (.of V)) (Xw : X.Opens) (hX : IsIntegral X) (hs : Flat s)
    (hg : GeomIrr s Xw) : ConnectedSpace ↑(pullback s (Spec.map (CommRingCat.ofHom φ))) := by
  set K := FractionRing O
  set φ' := Spec.map (CommRingCat.ofHom φ)
  set ι' : Spec (.of K) ⟶ Spec (.of O) := Spec.map (CommRingCat.ofHom (algebraMap O K))
  set f : V →+* K := (algebraMap O K).comp φ
  have hf : Function.Injective f := (IsFractionRing.injective O K).comp hφ
  have hfe : spMap f = ι' ≫ φ' := by
    simp only [spMap, ι', φ', f, ← Spec.map_comp]
    rfl
  haveI hWi := hg K f hf
  set Wk := pullback (Xw.ι ≫ s) (spMap f)

  let m : Wk ⟶ pullback s φ' := pullback.lift (pullback.fst _ _ ≫ Xw.ι) (pullback.snd _ _ ≫ ι') (by
    simp only [Category.assoc]
    rw [← hfe]
    exact pullback.condition)
  haveI : Flat φ' := flat_injective_dvr φ hφ
  have gfst : GeneralizingMap (pullback.fst s φ') := by
    exact Flat.generalizingMap _
  have gsnd : GeneralizingMap (pullback.snd s φ') := by
    exact Flat.generalizingMap _

  haveI : IrreducibleSpace X := inferInstance
  set η := genericPoint X
  obtain ⟨w₀⟩ := (inferInstance : Nonempty Wk)
  have hη : η ∈ Xw := by
    exact ((genericPoint_spec X).mem_open_set_iff Xw.isOpen).2
      ⟨_, trivial, (pullback.fst (Xw.ι ≫ s) (spMap f) w₀).2⟩
  have key : ∀ x : ↥(pullback s φ'), x ∈ closure (Set.range m) := by
    intro x
    obtain ⟨x₁, hx₁, hx₁s⟩ := gsnd (b := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O)) (a := x)
      ((PrimeSpectrum.le_iff_specializes _ _).1 bot_le)
    obtain ⟨x₂, hx₂, hx₂f⟩ := gfst (genericPoint_specializes (pullback.fst s φ' x₁))
    have hs₂ : pullback.snd s φ' x₂ = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O) := by
      have := (hx₂.map (pullback.snd s φ').continuous)
      rw [hx₁s] at this
      exact PrimeSpectrum.ext (le_bot_iff.1 ((PrimeSpectrum.le_iff_specializes _ _).2 this))

    have hι : ι' (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O) := by
      have := bot_map (X := Spec (.of O)) (IsFractionRing.injective O K) (𝟙 _)
      exact this
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd s φ') (g := ι') x₂
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) (by rw [hs₂, hι])
    obtain ⟨y, hy₁, hy₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := Xw.ι)
      (g := pullback.fst (pullback.snd s φ') ι' ≫ pullback.fst s φ') ⟨η, hη⟩ z
      (by rw [Scheme.Hom.comp_apply, hz₁, hx₂f]; rfl)
    let h : pullback Xw.ι (pullback.fst (pullback.snd s φ') ι' ≫ pullback.fst s φ') ⟶ Wk :=
      pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd _ _) (by
        simp only [Category.assoc]
        rw [pullback.condition_assoc, Category.assoc, pullback.condition, pullback.condition_assoc, hfe])
    have hm : h ≫ m = pullback.snd _ _ ≫ pullback.fst (pullback.snd s φ') ι' := by
      apply pullback.hom_ext
      · simp only [Category.assoc, m, h, pullback.lift_fst, pullback.lift_fst_assoc]
        rw [pullback.condition]
      · simp only [Category.assoc, m, h, pullback.lift_snd, pullback.lift_snd_assoc]
        rw [pullback.condition]
    have hx₂m : x₂ ∈ Set.range m := ⟨h y, by
      rw [← Scheme.Hom.comp_apply, hm, Scheme.Hom.comp_apply, hy₂, hz₁]⟩
    exact closure_mono (Set.singleton_subset_iff.2 hx₂m) (hx₂.trans hx₁).mem_closure
  have hirr : IsIrreducible (Set.range m) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ Wk).image _ m.continuous.continuousOn
  have : IrreducibleSpace ↑(pullback s φ') := by
    have hcl := hirr.closure
    rw [Set.eq_univ_of_forall key] at hcl
    exact (irreducibleSpace_def _).2 hcl
  infer_instance

end GlobalTheory.FlatModel
