import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IqBasic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionGroupEquivLocalGaloisGroup

open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc Topology NumberField IsDedekindDomain

/- English proof (translation)
Rewrite using `[placeJ, ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff, PadicAlgCl.valuation_def, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]`.
-/
private theorem de_mem {Ω : Type} [Field Ω] {v : ℕ} [Fact v.Prime] (j : Ω →+* Om v) (x : Ω) :
    x ∈ placeJ j ↔ ‖j x‖ ≤ 1 := by
  rw [placeJ, ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff, PadicAlgCl.valuation_def,
    ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F`. Establish `hnorm : ∀ y, ‖j y‖ < 1 ↔ A.valuation y < 1` using `GlobalTheory.DecLocal.norm_lt_one_iff A j hj`. Establish `hle : ∀ y, A.valuation y ≤ 1 ↔ ‖j y‖ ≤ 1` using `fun y => by`. Rewrite using `[ValuationSubring.valuation_le_one_iff, hj]`. Rewrite using `[(iqBasic v).2.2.1 σ]`.

Express the relevant statement in the definitionally equal form `_ ↔ (g : G F Ω) ∈ ValuationSubring.decompositionSubgroup F A ∧ ∀ x, A.valuation x ≤ 1 → A.valuation ((g : G F Ω) x - x) < 1`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨g.2, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[← hnorm, map_sub, ← hi]`.

Conclude with `h (j x) ((hle x).mp hx)`. Introduce and unpack `⟨-, h⟩ y hy`. Take `⟨x, hx⟩` from `(GlobalTheory.PlaceBridge.denseRange_embedding j).exists_dist_lt y one_pos`. Rewrite `hx` using `[dist_eq_norm]`. Establish `hjx : ‖j x‖ ≤ 1`.

Establish `hm` using `IsUltrametricDist.norm_add_le_max y (-(y - j x))`. Rewrite `hm` using `[norm_neg, ← sub_eq_add_neg, sub_sub_cancel]`. Conclude with `hm.trans (max_le hy hx.le)`. Establish `h3 : ‖σ (j x) - j x‖ < 1`. Rewrite using `[hi, ← map_sub, hnorm]`.

Conclude with `h x ((hle x).mpr hjx)`. Establish `hdecomp : σ y - y = (σ (y - j x) - (y - j x)) + (σ (j x) - j x)`. Rewrite using `[map_sub]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : ‖σ (y - j x)‖ < 1`.

Rewrite using `[GlobalTheory.PlaceBridge.norm_algEquiv]`. Conclude with `hx`. Establish `h5 : ‖σ (y - j x) - (y - j x)‖ < 1`. Establish `hm` using `IsUltrametricDist.norm_add_le_max (σ (y - j x)) (-(y - j x))`. Rewrite `hm` using `[norm_neg, ← sub_eq_add_neg]`.

Conclude with `lt_of_le_of_lt hm (max_lt h1 hx)`. Rewrite using `[hdecomp]`. Conclude with `lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h5 h3)`.
-/
private theorem de_ine {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {v : ℕ} [Fact v.Prime] {A : ValuationSubring Ω} {j : Ω →+* Om v} (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1)
    (g : ↥(Dec (F := F) A)) (σ : GQ v) (hi : ∀ y, σ (j y) = j ((g : G F Ω) y)) :
    σ ∈ Iq v ↔ (g : G F Ω) ∈ Ine (F := F) A := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have hnorm : ∀ y, ‖j y‖ < 1 ↔ A.valuation y < 1 := GlobalTheory.DecLocal.norm_lt_one_iff A j hj
  have hle : ∀ y, A.valuation y ≤ 1 ↔ ‖j y‖ ≤ 1 := fun y => by
    rw [ValuationSubring.valuation_le_one_iff, hj]
  rw [(iqBasic v).2.2.1 σ]
  change _ ↔ (g : G F Ω) ∈ ValuationSubring.decompositionSubgroup F A ∧
    ∀ x, A.valuation x ≤ 1 → A.valuation ((g : G F Ω) x - x) < 1
  constructor
  · intro h
    refine ⟨g.2, fun x hx => ?_⟩
    rw [← hnorm, map_sub, ← hi]
    exact h (j x) ((hle x).mp hx)
  · rintro ⟨-, h⟩ y hy
    obtain ⟨x, hx⟩ := (GlobalTheory.PlaceBridge.denseRange_embedding j).exists_dist_lt y one_pos
    rw [dist_eq_norm] at hx
    have hjx : ‖j x‖ ≤ 1 := by
      have hm := IsUltrametricDist.norm_add_le_max y (-(y - j x))
      rw [norm_neg, ← sub_eq_add_neg, sub_sub_cancel] at hm
      exact hm.trans (max_le hy hx.le)
    have h3 : ‖σ (j x) - j x‖ < 1 := by
      rw [hi, ← map_sub, hnorm]
      exact h x ((hle x).mpr hjx)
    have hdecomp : σ y - y = (σ (y - j x) - (y - j x)) + (σ (j x) - j x) := by
      rw [map_sub]
      ring
    have h1 : ‖σ (y - j x)‖ < 1 := by
      rw [GlobalTheory.PlaceBridge.norm_algEquiv]
      exact hx
    have h5 : ‖σ (y - j x) - (y - j x)‖ < 1 := by
      have hm := IsUltrametricDist.norm_add_le_max (σ (y - j x)) (-(y - j x))
      rw [norm_neg, ← sub_eq_add_neg] at hm
      exact lt_of_le_of_lt hm (max_lt h1 hx)
    rw [hdecomp]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h5 h3)

/- English proof (translation)
Establish `hjinj : Function.Injective j` using `j.injective`. Simplify using `only [UpperTheory.V.Loc.cyc, ReciprocityTheory.Gal.cycZ, MonoidHom.comp_apply]`. Apply `Units.ext` to reduce the goal to its premises. Apply `(PadicInt.ext_of_toZModPow).mp` to reduce the goal to its premises. Introduce `n`.

Use `haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)`. Establish `h1` using `cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G F Ω) Ω g) ζ hζ.pow_eq_one`. Establish `h2` using `cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (GQ v) (Om v) σ) (j ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])`. Rewrite `h1` using `[show (MulSemiringAction.toRingAut (G F Ω) Ω g) ζ = g ζ from rfl]`.

Rewrite `h2` using `[show (MulSemiringAction.toRingAut (GQ v) (Om v) σ) (j ζ) = σ (j ζ) from rfl]`. Rewrite `h2` using `[hi, h1, ← map_pow]`. Establish `h4` using `hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (hjinj h2)`. Conclude with `(ZMod.val_injective _ h4).symm`.
-/
private theorem de_cyc {F Ω : Type} [Field F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosed Ω]
    {v : ℕ} [Fact v.Prime] {j : Ω →+* Om v} (l : ℕ) [Fact l.Prime]
    (g : G F Ω) (σ : GQ v) (hi : ∀ y, σ (j y) = j (g y)) :
    UpperTheory.V.Loc.cyc v l σ = cycZ F Ω l g := by
  have hjinj : Function.Injective j := j.injective
  simp only [UpperTheory.V.Loc.cyc, ReciprocityTheory.Gal.cycZ, MonoidHom.comp_apply]
  apply Units.ext
  apply (PadicInt.ext_of_toZModPow).mp
  intro n
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have h1 := cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G F Ω) Ω g) ζ hζ.pow_eq_one
  have h2 := cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (GQ v) (Om v) σ) (j ζ)
    (by rw [← map_pow, hζ.pow_eq_one, map_one])
  rw [show (MulSemiringAction.toRingAut (G F Ω) Ω g) ζ = g ζ from rfl] at h1
  rw [show (MulSemiringAction.toRingAut (GQ v) (Om v) σ) (j ζ) = σ (j ζ) from rfl] at h2
  rw [hi, h1, ← map_pow] at h2
  have h4 := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (hjinj h2)
  exact (ZMod.val_injective _ h4).symm

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ _ v _`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `A w hA hw`. Take `⟨j, hj⟩` from `GlobalTheory.PlaceBridge.exists_embedding (l := v) F Ω w A hw hA`.

Use `⟨j, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Rewrite using `[de_mem, hj]`. Introduce `j`. Establish `hj : ∀ x, x ∈ placeJ j ↔ ‖j x‖ ≤ 1` using `de_mem j`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hlt : (placeJ j).valuation ((v : ℕ) : Ω) < 1`. Rewrite using `[← GlobalTheory.DecLocal.norm_lt_one_iff _ j hj, map_natCast]`. Conclude with `GlobalTheory.PlaceBridge.norm_l_lt_one`. Take `⟨w, hw, hpo⟩` from `GlobalTheory.DecLocal.exists_place_below (p := v) (F := F) (placeJ j) hlt`.

Conclude with `⟨w, hpo, hw⟩`. Set `K : FinExt v` to `⟨IntermediateField.adjoin ℚ_[v] (Set.range fun x => j (algebraMap F Ω x)), GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap F Ω))⟩ haveI : FiniteDimensional ℚ_[v] (K : IntermediateField ℚ_[v] (Om v)) := K.2`. Establish `hK : (K : IntermediateField ℚ_[v] (Om v)) = IntermediateField.adjoin ℚ_[v] (Set.range fun x => j (algebraMap F Ω x))` using `rfl`. Take `⟨e, hec, hesc, he⟩` from `GlobalTheory.PlaceBridge.exists_mulEquiv (E := F) hj K hK`. Set `φ : ↥(Dec (F` to `F) (placeJ j)) →* GQ v := (GK K).subtype.comp e.toMonoidHom`.

Establish `hφ : ∀ g, φ g = (e g : GQ v)` using `fun g => rfl`. Establish `hrange : ∀ σ : GQ v, σ ∈ φ.range ↔ σ ∈ GK K`. Introduce `σ`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, rfl⟩`.

Conclude with `(e g).2`. Introduce `h`. Conclude with `⟨e.symm ⟨σ, h⟩, by rw [hφ, MulEquiv.apply_symm_apply]⟩`. Establish `hopen : IsOpen ((GK K : Subgroup (GQ v)) : Set (GQ v))` using `IntermediateField.fixingSubgroup_isOpen (K : IntermediateField ℚ_[v] (Om v))`. Use `⟨φ, ?_, fun g y => he g y, fun σ => by rw [hrange, GlobalTheory.PlaceBridge.mem_GK_iff (E := F) K hK], fun g => de_ine hj g (φ g) (he g), fun l _ g => de_cyc l (g : G F Ω) (φ g) (he g), fun w hw => ?_⟩` and prove the remaining obligations.

Set `h : ↥(Dec (F` to `F) (placeJ j)) ≃ₜ ↥(GK K) := { e.toEquiv with continuous_toFun := hec, continuous_invFun := hesc }`. Conclude with `hopen.isOpenEmbedding_subtypeVal.comp h.isOpenEmbedding`. Establish `hr : φ.range = GK K`. Use extensionality with `σ`. Conclude with `hrange σ`.

Rewrite using `[hr, ← GlobalTheory.DecLocal.finrank_closure_eq_locDeg v F Ω (placeJ j) j hj w hw, IntermediateField.finrank_eq_fixingSubgroup_index]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Loc.decEmb :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω] {v : ℕ} [Fact v.Prime], (∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 F)), IsPlaceOver A w → ((v : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ j : Ω →+* Om v, placeJ j = A) ∧ ∀ j : Ω →+* Om v, (∃ w : HeightOneSpectrum (𝓞 F), IsPlaceOver (placeJ j) w ∧ ((v : ℕ) : 𝓞 F) ∈ w.asIdeal) ∧ ∃ φ : ↥(Dec (F := F) (placeJ j)) →* GQ v, IsOpenEmbedding φ ∧ (∀ g y, φ g (j y) = j ((g : G F Ω) y)) ∧ (∀ σ : GQ v, σ ∈ φ.range ↔ ∀ x : F, σ (j (algebraMap F Ω x)) = j (algebraMap F Ω x)) ∧ (∀ g, φ g ∈ Iq v ↔ (g : G F Ω) ∈ Ine (F := F) (placeJ j)) ∧ (∀ (l : ℕ) [Fact l.Prime] g, UpperTheory.V.Loc.cyc v l (φ g) = cycZ F Ω l (g : G F Ω)) ∧ ∀ w : HeightOneSpectrum (𝓞 F), IsPlaceOver (placeJ j) w → φ.range.index = locDeg w := by
  intro F Ω _ _ _ _ _ _ v _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  refine ⟨?_, ?_⟩
  · intro A w hA hw
    obtain ⟨j, hj⟩ := GlobalTheory.PlaceBridge.exists_embedding (l := v) F Ω w A hw hA
    refine ⟨j, ?_⟩
    ext x
    rw [de_mem, hj]
  · intro j
    have hj : ∀ x, x ∈ placeJ j ↔ ‖j x‖ ≤ 1 := de_mem j
    refine ⟨?_, ?_⟩
    · have hlt : (placeJ j).valuation ((v : ℕ) : Ω) < 1 := by
        rw [← GlobalTheory.DecLocal.norm_lt_one_iff _ j hj, map_natCast]
        exact GlobalTheory.PlaceBridge.norm_l_lt_one
      obtain ⟨w, hw, hpo⟩ := GlobalTheory.DecLocal.exists_place_below (p := v) (F := F) (placeJ j) hlt
      exact ⟨w, hpo, hw⟩
    · let K : FinExt v := ⟨IntermediateField.adjoin ℚ_[v] (Set.range fun x => j (algebraMap F Ω x)),
        GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap F Ω))⟩
      haveI : FiniteDimensional ℚ_[v] (K : IntermediateField ℚ_[v] (Om v)) := K.2
      have hK : (K : IntermediateField ℚ_[v] (Om v)) =
          IntermediateField.adjoin ℚ_[v] (Set.range fun x => j (algebraMap F Ω x)) := rfl
      obtain ⟨e, hec, hesc, he⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := F) hj K hK
      let φ : ↥(Dec (F := F) (placeJ j)) →* GQ v := (GK K).subtype.comp e.toMonoidHom
      have hφ : ∀ g, φ g = (e g : GQ v) := fun g => rfl
      have hrange : ∀ σ : GQ v, σ ∈ φ.range ↔ σ ∈ GK K := by
        intro σ
        constructor
        · rintro ⟨g, rfl⟩
          exact (e g).2
        · intro h
          exact ⟨e.symm ⟨σ, h⟩, by rw [hφ, MulEquiv.apply_symm_apply]⟩
      have hopen : IsOpen ((GK K : Subgroup (GQ v)) : Set (GQ v)) :=
        IntermediateField.fixingSubgroup_isOpen (K : IntermediateField ℚ_[v] (Om v))
      refine ⟨φ, ?_, fun g y => he g y, fun σ => by rw [hrange, GlobalTheory.PlaceBridge.mem_GK_iff (E := F) K hK],
        fun g => de_ine hj g (φ g) (he g), fun l _ g => de_cyc l (g : G F Ω) (φ g) (he g), fun w hw => ?_⟩
      · let h : ↥(Dec (F := F) (placeJ j)) ≃ₜ ↥(GK K) :=
          { e.toEquiv with continuous_toFun := hec, continuous_invFun := hesc }
        exact hopen.isOpenEmbedding_subtypeVal.comp h.isOpenEmbedding
      · have hr : φ.range = GK K := by
          ext σ
          exact hrange σ
        rw [hr, ← GlobalTheory.DecLocal.finrank_closure_eq_locDeg v F Ω (placeJ j) j hj w hw,
          IntermediateField.finrank_eq_fixingSubgroup_index]
        rfl
