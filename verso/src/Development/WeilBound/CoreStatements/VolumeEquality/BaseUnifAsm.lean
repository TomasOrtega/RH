import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifGood
import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifEx2
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RingOfIntegersHomInjective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Limits NumberField MeasureTheory Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l}

/- English proof (translation)
The claim follows from `congrArg CommRingCat.Hom.hom (Spec.map_injective h)`.
-/
theorem spMap_injective {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

/- English proof (translation)
Use `haveI : FiniteDimensional ℚ c.F := c.fin`. Use `haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }`. Use `haveI : ∀ κ, Finite (U κ).ι := fun κ => (U κ).fin`. Set `C : Type` to `Σ κ : c.F →+* ℂ, (U κ).ι`. Take `⟨np, ⟨e⟩⟩` from `Finite.exists_equiv_fin C`.

Set `a : Fin np → C` to `e.symm`. Establish `hκ : ∀ κ κ' : c.F →+* ℂ, κ.comp (algebraMap (𝓞 c.F) c.F) = κ'.comp (algebraMap (𝓞 c.F) c.F) → κ = κ'` using `fun κ κ' h => IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) h`. Establish `hq : ∀ b : C, ((U b.1).F b.2).q = q` using `fun b => (U b.1).q_eq b.2`. Establish `hdisj : ∀ b b' : C, ∀ t ∈ ballDom q, ∀ t' ∈ ballDom q, (U b.1).pt b.2 t = (U b'.1).pt b'.2 t' → b = b'`. Introduce and unpack `⟨κ, k⟩ ⟨κ', k'⟩ t ht t' ht' h`.

Establish `h₁` using `(U κ).comp_s_eq_spMap_of_isOver k t ht`. Establish `h₂` using `(U κ').comp_s_eq_spMap_of_isOver k' t' ht'`. Simplify using `only at h`. Rewrite `h₁` using `[h, h₂]`. Take `rfl` from `hκ _ _ (spMap_injective h₁)`.

Rewrite using `[(U κ').disj k k' t ht t' ht' h]`. Establish `hemb : ∀ p : Sp ℂ ⟶ Y.X, ∃ κ : c.F →+* ℂ, p ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F))` using `fun p => by`. Take `⟨κ, hκρ⟩` from `FamEx.exists_ringHom_extend (Spec.preimage (p ≫ Y.s)).hom`. Use `⟨κ, ?_⟩` and prove the remaining obligations. Rewrite using `[hκρ]`.

Unfold `spMap`. Rewrite using `[CommRingCat.ofHom_hom, Spec.map_preimage]`. Use `⟨{ np := np g := g Di := fun k => (U (a k).1).Di (a k).2 sig := fun k => (U _).sig _ κ := fun k => (a k).1 F := fun k => (U (a k).1).F (a k).2 q_eq := fun k k' => (hq _).trans (hq _).symm form_eq := fun k => (U _).form_eq _ σ_eq := fun k => (U _).σ_eq _ Γ := fun k => (U (a k).1). …` and prove the remaining obligations. Rewrite using `[hq, hq]`. Conclude with `fun t ht t' ht' h => e.symm.injective (hdisj _ _ t ht t' ht' h)`.

Use `fibre := fun k => by rw [hq]; exact (U _).fibre _`. Use `onto := fun p hp => ?_`. Use `lat := fun k => by rw [hq]; exact (U _).lat _`. Use `vec := fun S Ω _ K _ J _ y 𝔐 k V z hV hs => (U _).vec S Ω K J y 𝔐 _ V z hV (by rw [← hq (a k)]; exact hs) }, ?_⟩`. Take `⟨κ, hκ⟩` from `hemb p`.

Take `⟨k, t, ht, h⟩` from `(U κ).onto p hp hκ`. Take `⟨i, hi⟩` from `e.symm.surjective ⟨κ, k⟩`. Use `⟨i, t, by rw [hq]; exact ht, ?_⟩` and prove the remaining obligations. Use `show (U (e.symm i).1).pt (e.symm i).2 t = p`. Rewrite using `[hi]`.

Conclude with `h`. Introduce `m T y hT hTc hy hyi b hb b' hb' k k' t ht t' ht' h h' choose κ hκy using fun b => hemb (y b)`. Establish `hd : ∀ r : 𝓞 c.F, DifferentiableOn ℂ (fun b => κ b (r : c.F)) T` using `fun r => by`. Establish `h3` using `(PullbackSections.isHolTo_comp hy Y.s ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 c.F))).inv r)).2`. Establish `hset : T ⊆ {b ∈ T | ⊤ ≤ (y b ≫ Y.s) ⁻¹ᵁ ⊤}` using `fun b hb => ⟨hb, le_top⟩`.

Use `(h3.mono hset).congr fun b _ => ?_` and prove the remaining obligations. Use `show κ b (r : c.F) = valAt' (y b ≫ Y.s) ⊤ _`. Rewrite using `[hκy b]`. Conclude with `(PullbackSections.valAt'_spMap ((κ b).comp (algebraMap (𝓞 c.F) c.F)) r).symm`. Establish `hc : ∀ b₁ ∈ T, y b₁ ≫ Y.s = spMap ((κ b).comp (algebraMap (𝓞 c.F) c.F))` using `fun b₁ hb₁ => by`.

Rewrite using `[hκy, FamEx.embedding_const_preconnected hTc κ hd hb₁ hb]`. Establish `key : ∀ d d' : C, y b = (U d.1).pt d.2 t → y b' = (U d'.1).pt d'.2 t' → t ∈ ballDom q → t' ∈ ballDom q → d = d'`. Introduce and unpack `⟨κ₁, k₁⟩ ⟨κ₂, k₂⟩ h₁ h₂ ht ht'`. Simplify using `only at h₁ h₂`. Establish `e₁` using `(U κ₁).comp_s_eq_spMap_of_isOver k₁ t ht`.

Establish `e₂` using `(U κ₂).comp_s_eq_spMap_of_isOver k₂ t' ht'`. Rewrite `e₁` using `[← h₁, hc b hb]`. Rewrite `e₂` using `[← h₂, hc b' hb']`. Take `rfl` from `hκ _ _ (spMap_injective e₁)`. Take `rfl` from `hκ _ _ (spMap_injective e₂)`.

Rewrite using `[(U (κ b)).locc m T y hT hTc hy hyi hc b hb b' hb' k₁ k₂ t ht t' ht' h₁ h₂]`. Conclude with `e.symm.injective (key (a k) (a k') h h' (by rw [← hq (a k)]; exact ht) (by rw [← hq (a k')]; exact ht'))`.
-/
theorem baseUnif_of_kUnif (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (sm : CMType H → CMType H ⊕ CMType H) (j j' n g : ℕ)
    (q : CMType H × Fin j × Fin j' ≃ Fin n) (U : ∀ κ, KUnif Y sm j j' n g q κ) :
    ∃ B : BaseUnif Y sm j j' n, B.Locc := by
  classical
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  haveI : ∀ κ, Finite (U κ).ι := fun κ => (U κ).fin
  let C : Type := Σ κ : c.F →+* ℂ, (U κ).ι
  obtain ⟨np, ⟨e⟩⟩ := Finite.exists_equiv_fin C
  let a : Fin np → C := e.symm
  have hκ : ∀ κ κ' : c.F →+* ℂ, κ.comp (algebraMap (𝓞 c.F) c.F) = κ'.comp (algebraMap (𝓞 c.F) c.F) → κ = κ' :=
    fun κ κ' h => IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) h
  have hq : ∀ b : C, ((U b.1).F b.2).q = q := fun b => (U b.1).q_eq b.2
  have hdisj : ∀ b b' : C, ∀ t ∈ ballDom q, ∀ t' ∈ ballDom q, (U b.1).pt b.2 t = (U b'.1).pt b'.2 t' → b = b' := by
    rintro ⟨κ, k⟩ ⟨κ', k'⟩ t ht t' ht' h
    have h₁ := (U κ).comp_s_eq_spMap_of_isOver k t ht
    have h₂ := (U κ').comp_s_eq_spMap_of_isOver k' t' ht'
    dsimp only at h
    rw [h, h₂] at h₁
    obtain rfl := hκ _ _ (spMap_injective h₁)
    rw [(U κ').disj k k' t ht t' ht' h]
  have hemb : ∀ p : Sp ℂ ⟶ Y.X, ∃ κ : c.F →+* ℂ, p ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F)) := fun p => by
    obtain ⟨κ, hκρ⟩ := FamEx.exists_ringHom_extend (Spec.preimage (p ≫ Y.s)).hom
    refine ⟨κ, ?_⟩
    rw [hκρ]
    unfold spMap
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  refine ⟨{
    np := np
    g := g
    Di := fun k => (U (a k).1).Di (a k).2
    sig := fun k => (U _).sig _
    κ := fun k => (a k).1
    F := fun k => (U (a k).1).F (a k).2
    q_eq := fun k k' => (hq _).trans (hq _).symm
    form_eq := fun k => (U _).form_eq _
    σ_eq := fun k => (U _).σ_eq _
    Γ := fun k => (U (a k).1).Γ (a k).2
    mem_Γ := fun k => (U _).mem_Γ _
    arith := fun k => (U _).arith _
    pt := fun k => (U (a k).1).pt (a k).2
    hol := fun k => by rw [hq]; exact (U _).hol _
    comp_s_eq_spMap_of_isOver := fun k => by rw [hq]; exact (U _).comp_s_eq_spMap_of_isOver _
    interior := fun k => by rw [hq]; exact (U _).interior _
    disj := fun k k' => by
      rw [hq, hq]
      exact fun t ht t' ht' h => e.symm.injective (hdisj _ _ t ht t' ht' h)
    fibre := fun k => by rw [hq]; exact (U _).fibre _
    onto := fun p hp => ?_
    lat := fun k => by rw [hq]; exact (U _).lat _
    vec := fun S Ω _ K _ J _ y 𝔐 k V z hV hs => (U _).vec S Ω K J y 𝔐 _ V z hV (by rw [← hq (a k)]; exact hs) }, ?_⟩
  · obtain ⟨κ, hκ⟩ := hemb p
    obtain ⟨k, t, ht, h⟩ := (U κ).onto p hp hκ
    obtain ⟨i, hi⟩ := e.symm.surjective ⟨κ, k⟩
    refine ⟨i, t, by rw [hq]; exact ht, ?_⟩
    show (U (e.symm i).1).pt (e.symm i).2 t = p
    rw [hi]
    exact h
  · intro m T y hT hTc hy hyi b hb b' hb' k k' t ht t' ht' h h'
    choose κ hκy using fun b => hemb (y b)
    have hd : ∀ r : 𝓞 c.F, DifferentiableOn ℂ (fun b => κ b (r : c.F)) T := fun r => by
      have h3 := (PullbackSections.isHolTo_comp hy Y.s ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 c.F))).inv r)).2
      have hset : T ⊆ {b ∈ T | ⊤ ≤ (y b ≫ Y.s) ⁻¹ᵁ ⊤} := fun b hb => ⟨hb, le_top⟩
      refine (h3.mono hset).congr fun b _ => ?_
      show κ b (r : c.F) = valAt' (y b ≫ Y.s) ⊤ _
      rw [hκy b]
      exact (PullbackSections.valAt'_spMap ((κ b).comp (algebraMap (𝓞 c.F) c.F)) r).symm
    have hc : ∀ b₁ ∈ T, y b₁ ≫ Y.s = spMap ((κ b).comp (algebraMap (𝓞 c.F) c.F)) := fun b₁ hb₁ => by
      rw [hκy, FamEx.embedding_const_preconnected hTc κ hd hb₁ hb]
    have key : ∀ d d' : C, y b = (U d.1).pt d.2 t → y b' = (U d'.1).pt d'.2 t' → t ∈ ballDom q → t' ∈ ballDom q → d = d' := by
      rintro ⟨κ₁, k₁⟩ ⟨κ₂, k₂⟩ h₁ h₂ ht ht'
      dsimp only at h₁ h₂
      have e₁ := (U κ₁).comp_s_eq_spMap_of_isOver k₁ t ht
      have e₂ := (U κ₂).comp_s_eq_spMap_of_isOver k₂ t' ht'
      rw [← h₁, hc b hb] at e₁
      rw [← h₂, hc b' hb'] at e₂
      obtain rfl := hκ _ _ (spMap_injective e₁)
      obtain rfl := hκ _ _ (spMap_injective e₂)
      rw [(U (κ b)).locc m T y hT hTc hy hyi hc b hb b' hb' k₁ k₂ t ht t' ht' h₁ h₂]
    exact e.symm.injective (key (a k) (a k') h h' (by rw [← hq (a k)]; exact ht) (by rw [← hq (a k')]; exact ht'))

/- English proof (translation)
Introduce `hG E _ _ _ H D l Xo c Y sm j j' n h1 hs hn`. Establish `hN : N1c` using `hG.1.2.2.1`. Take `⟨g, ty, hty⟩` from `GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q`. Establish `q : CMType H × Fin j × Fin j' ≃ Fin n` using `Fintype.equivFinOfCardEq (by simp [hn, mul_assoc])`. Set `ρ : c.F` to `(IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ`.

Establish `hρ : (ρ : ℂ) = H.rt0` using `rfl`. Establish `good : ∀ κ : c.F →+* ℂ, κ ρ = H.rt0 → Nonempty (KUnif Y sm j j' n g q κ)` using `fun κ hκ => by`. Take `⟨FU⟩` from `hN E H D l Xo (κ.comp (IntermediateField.inclusion c.le).toRingHom) g ty h1 hκ hty`. Conclude with `kUnif_good hV Y sm j j' n g q κ ty hty hs ρ hρ hκ FU`. Establish `all : ∀ κ : c.F →+* ℂ, Nonempty (KUnif Y sm j j' n g q κ)` using `fun κ => by`.

Establish `e : ρ ^ 2 = -(H.d : c.F)` using `Subtype.ext (by show (ρ : ℂ) ^ 2 = -(H.d : ℂ); exact H.sqrt_neg_disc_sq)`. Establish `e2 : (κ ρ) ^ 2 = H.rt0 ^ 2`. Rewrite using `[← map_pow, e, H.sqrt_neg_disc_sq]`. Simplify using the standard rewrite rules. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 e2 with h | h` into its components or cases.

Conclude with `good κ h`. Establish `h'` using `hC E H D l Xo c Y sm j j' n g q _ (good ((starRingEnd ℂ).comp κ) (by show starRingEnd ℂ (κ ρ) = _`. Rewrite using `[h, map_neg, FamEx.rt0_conj_neg_ne_zero, neg_neg]))`. Establish `e3 : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp κ) = κ` using `RingHom.ext fun x => by simp`. Rewrite `h'` using `[e3]`. Then use the resulting hypothesis.

Conclude with `baseUnif_of_kUnif Y sm j j' n g q fun κ => (all κ).some`.
-/
theorem baseUnifEx2_of (hV : VecOfPeriods) (hC : KUnifConj) : BaseUnifEx2 := by
  intro hG E _ _ _ H D l Xo c Y sm j j' n h1 hs hn
  have hN : N1c := hG.1.2.2.1
  obtain ⟨g, ty, hty⟩ := GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q
  have q : CMType H × Fin j × Fin j' ≃ Fin n := Fintype.equivFinOfCardEq (by simp [hn, mul_assoc])
  let ρ : c.F := (IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ
  have hρ : (ρ : ℂ) = H.rt0 := rfl
  have good : ∀ κ : c.F →+* ℂ, κ ρ = H.rt0 → Nonempty (KUnif Y sm j j' n g q κ) := fun κ hκ => by
    obtain ⟨FU⟩ := hN E H D l Xo (κ.comp (IntermediateField.inclusion c.le).toRingHom) g ty h1 hκ hty
    exact kUnif_good hV Y sm j j' n g q κ ty hty hs ρ hρ hκ FU
  have all : ∀ κ : c.F →+* ℂ, Nonempty (KUnif Y sm j j' n g q κ) := fun κ => by
    have e : ρ ^ 2 = -(H.d : c.F) := Subtype.ext (by show (ρ : ℂ) ^ 2 = -(H.d : ℂ); exact H.sqrt_neg_disc_sq)
    have e2 : (κ ρ) ^ 2 = H.rt0 ^ 2 := by
      rw [← map_pow, e, H.sqrt_neg_disc_sq]
      simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 e2 with h | h
    · exact good κ h
    · have h' := hC E H D l Xo c Y sm j j' n g q _ (good ((starRingEnd ℂ).comp κ) (by
        show starRingEnd ℂ (κ ρ) = _
        rw [h, map_neg, FamEx.rt0_conj_neg_ne_zero, neg_neg]))
      have e3 : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp κ) = κ := RingHom.ext fun x => by simp
      rwa [e3] at h'
  exact baseUnif_of_kUnif Y sm j j' n g q fun κ => (all κ).some

end SheetDecomposition
