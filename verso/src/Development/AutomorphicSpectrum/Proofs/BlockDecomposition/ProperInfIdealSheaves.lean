import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.Union

/- English proof (translation)
Establish `hle : T₁ * T₂ ≤ T₁ ⊓ T₂` using `fun U => Ideal.mul_le_inf`. Establish `h` using `Scheme.IdealSheafData.support_antitone hle`. Introduce `x hx`. Establish `hx' : x ∈ (T₁ * T₂).support` using `h hx`. Rewrite `hx'` using `[Scheme.IdealSheafData.support_mul]`.

Conclude with `hx'`.
-/
theorem support_inf_subset {X : Scheme.{0}} (T₁ T₂ : X.IdealSheafData) :
    ((T₁ ⊓ T₂).support : Set X) ⊆ (T₁.support : Set X) ∪ T₂.support := by
  have hle : T₁ * T₂ ≤ T₁ ⊓ T₂ := fun U => Ideal.mul_le_inf
  have h := Scheme.IdealSheafData.support_antitone hle
  intro x hx
  have hx' : x ∈ (T₁ * T₂).support := h hx
  rw [Scheme.IdealSheafData.support_mul] at hx'
  exact hx'

/- English proof (translation)
Rewrite using `[universallyClosed_iff]`. Introduce `X' Y' i₁ i₂ f' H`. Establish `key : ∀ {W : Scheme.{0}} (p : W ⟶ Z), UniversallyClosed (p ≫ h) → IsClosedMap (pullback.fst i₁ p ≫ f')`. Introduce `W p hp`. Establish `H' : IsPullback (pullback.fst i₁ p ≫ f') (pullback.snd i₁ p) i₂ (p ≫ h)` using `(IsPullback.of_hasPullback i₁ p).paste_horiz H`.

Conclude with `(universallyClosed_iff _).mp hp _ _ _ H'`. Establish `lift : ∀ {W : Scheme.{0}} (p : W ⟶ Z) (x : X'), i₁ x ∈ Set.range p → ∃ z : ↑(pullback i₁ p), pullback.fst i₁ p z = x`. Introduce and unpack `W p x ⟨w, hw⟩`. Take `⟨z, hz, -⟩` from `Scheme.Pullback.exists_preimage_pullback x w hw.symm`. Conclude with `⟨z, hz⟩`.

Use `show IsClosedMap f'`. Introduce `C hC`. Establish `hEq : f' '' C = (pullback.fst i₁ p₁ ≫ f') '' (pullback.fst i₁ p₁ ⁻¹' C) ∪ (pullback.fst i₁ p₂ ≫ f') '' (pullback.fst i₁ p₂ ⁻¹' C)`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, hx, rfl⟩`. Break down `hc (i₁ x) with hr | hr` into its components or cases. Take `⟨z, hz⟩` from `lift p₁ x hr`. Conclude with `Or.inl ⟨z, by simpa [hz] using hx, by simp [hz]⟩`. Take `⟨z, hz⟩` from `lift p₂ x hr`.

Conclude with `Or.inr ⟨z, by simpa [hz] using hx, by simp [hz]⟩`. Introduce and unpack `(⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)`. Conclude with `⟨_, hz, by simp⟩`. Conclude with `⟨_, hz, by simp⟩`. Rewrite using `[hEq]`.

Conclude with `(key p₁ h₁ _ (hC.preimage (pullback.fst i₁ p₁).continuous)).union (key p₂ h₂ _ (hC.preimage (pullback.fst i₁ p₂).continuous))`.
-/
theorem universallyClosed_of_cover {Z₁ Z₂ Z S : Scheme.{0}} (p₁ : Z₁ ⟶ Z) (p₂ : Z₂ ⟶ Z)
    (h : Z ⟶ S) (h₁ : UniversallyClosed (p₁ ≫ h)) (h₂ : UniversallyClosed (p₂ ≫ h))
    (hc : ∀ z : Z, z ∈ Set.range p₁ ∨ z ∈ Set.range p₂) : UniversallyClosed h := by
  rw [universallyClosed_iff]
  intro X' Y' i₁ i₂ f' H
  have key : ∀ {W : Scheme.{0}} (p : W ⟶ Z), UniversallyClosed (p ≫ h) →
      IsClosedMap (pullback.fst i₁ p ≫ f') := by
    intro W p hp
    have H' : IsPullback (pullback.fst i₁ p ≫ f') (pullback.snd i₁ p) i₂ (p ≫ h) :=
      (IsPullback.of_hasPullback i₁ p).paste_horiz H
    exact (universallyClosed_iff _).mp hp _ _ _ H'
  have lift : ∀ {W : Scheme.{0}} (p : W ⟶ Z) (x : X'), i₁ x ∈ Set.range p →
      ∃ z : ↑(pullback i₁ p), pullback.fst i₁ p z = x := by
    rintro W p x ⟨w, hw⟩
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x w hw.symm
    exact ⟨z, hz⟩
  show IsClosedMap f'
  intro C hC
  have hEq : f' '' C = (pullback.fst i₁ p₁ ≫ f') '' (pullback.fst i₁ p₁ ⁻¹' C) ∪
      (pullback.fst i₁ p₂ ≫ f') '' (pullback.fst i₁ p₂ ⁻¹' C) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hc (i₁ x) with hr | hr
      · obtain ⟨z, hz⟩ := lift p₁ x hr
        exact Or.inl ⟨z, by simpa [hz] using hx, by simp [hz]⟩
      · obtain ⟨z, hz⟩ := lift p₂ x hr
        exact Or.inr ⟨z, by simpa [hz] using hx, by simp [hz]⟩
    · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
      · exact ⟨_, hz, by simp⟩
      · exact ⟨_, hz, by simp⟩
  rw [hEq]
  exact (key p₁ h₁ _ (hC.preimage (pullback.fst i₁ p₁).continuous)).union
    (key p₂ h₂ _ (hC.preimage (pullback.fst i₁ p₂).continuous))

/- English proof (translation)
Introduce `X S f _ _ T₁ T₂ hT₁ hT₂`. Set `K : X.IdealSheafData` to `T₁ ⊓ T₂`. Set `p₁ : T₁.subscheme ⟶ K.subscheme` to `IsClosedImmersion.lift K.subschemeι T₁.subschemeι (by simpa [K] using (inf_le_left : T₁ ⊓ T₂ ≤ T₁))`. Set `p₂ : T₂.subscheme ⟶ K.subscheme` to `IsClosedImmersion.lift K.subschemeι T₂.subschemeι (by simpa [K] using (inf_le_right : T₁ ⊓ T₂ ≤ T₂))`. Establish `e₁ : p₁ ≫ K.subschemeι = T₁.subschemeι` using `IsClosedImmersion.lift_fac _ _ _`.

Establish `e₂ : p₂ ≫ K.subschemeι = T₂.subschemeι` using `IsClosedImmersion.lift_fac _ _ _`. Establish `u₁ : UniversallyClosed (p₁ ≫ K.subschemeι ≫ f)`. Rewrite using `[← Category.assoc, e₁]`. Use `infer_instance`. Establish `u₂ : UniversallyClosed (p₂ ≫ K.subschemeι ≫ f)`.

Rewrite using `[← Category.assoc, e₂]`. Use `infer_instance`. Establish `cover : ∀ {T : X.IdealSheafData} (p : T.subscheme ⟶ K.subscheme), p ≫ K.subschemeι = T.subschemeι → ∀ z : K.subscheme, K.subschemeι z ∈ (T.support : Set X) → z ∈ Set.range p`. Introduce `T p e z hz`. Take `⟨w, hw⟩` from `T.range_subschemeι.ge hz`.

Use `⟨w, K.subschemeι.isEmbedding.injective ?_⟩` and prove the remaining obligations. Rewrite using `[← hw, ← e]`. Both sides reduce to the same expression. Establish `hc : ∀ z : K.subscheme, z ∈ Set.range p₁ ∨ z ∈ Set.range p₂`. Introduce `z`.

Establish `hz : K.subschemeι z ∈ (K.support : Set X)` using `K.range_subschemeι.le ⟨z, rfl⟩`. Break down `support_inf_subset T₁ T₂ hz with h | h` into its components or cases. Conclude with `Or.inl (cover p₁ e₁ z h)`. Conclude with `Or.inr (cover p₂ e₂ z h)`. Establish `: UniversallyClosed (K.subschemeι ≫ f)` using `universallyClosed_of_cover p₁ p₂ _ u₁ u₂ hc`.

Conclude with `⟨⟩`.
-/
theorem isProper_inf : ∀ {X S : Scheme.{0}} (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f]
    (T₁ T₂ : X.IdealSheafData), IsProper (T₁.subschemeι ≫ f) → IsProper (T₂.subschemeι ≫ f) →
    IsProper ((T₁ ⊓ T₂).subschemeι ≫ f) := by
  intro X S f _ _ T₁ T₂ hT₁ hT₂
  let K : X.IdealSheafData := T₁ ⊓ T₂
  let p₁ : T₁.subscheme ⟶ K.subscheme := IsClosedImmersion.lift K.subschemeι T₁.subschemeι
    (by simpa [K] using (inf_le_left : T₁ ⊓ T₂ ≤ T₁))
  let p₂ : T₂.subscheme ⟶ K.subscheme := IsClosedImmersion.lift K.subschemeι T₂.subschemeι
    (by simpa [K] using (inf_le_right : T₁ ⊓ T₂ ≤ T₂))
  have e₁ : p₁ ≫ K.subschemeι = T₁.subschemeι := IsClosedImmersion.lift_fac _ _ _
  have e₂ : p₂ ≫ K.subschemeι = T₂.subschemeι := IsClosedImmersion.lift_fac _ _ _
  have u₁ : UniversallyClosed (p₁ ≫ K.subschemeι ≫ f) := by
    rw [← Category.assoc, e₁]; infer_instance
  have u₂ : UniversallyClosed (p₂ ≫ K.subschemeι ≫ f) := by
    rw [← Category.assoc, e₂]; infer_instance
  have cover : ∀ {T : X.IdealSheafData} (p : T.subscheme ⟶ K.subscheme),
      p ≫ K.subschemeι = T.subschemeι → ∀ z : K.subscheme, K.subschemeι z ∈ (T.support : Set X) →
      z ∈ Set.range p := by
    intro T p e z hz
    obtain ⟨w, hw⟩ := T.range_subschemeι.ge hz
    refine ⟨w, K.subschemeι.isEmbedding.injective ?_⟩
    rw [← hw, ← e]
    rfl
  have hc : ∀ z : K.subscheme, z ∈ Set.range p₁ ∨ z ∈ Set.range p₂ := by
    intro z
    have hz : K.subschemeι z ∈ (K.support : Set X) := K.range_subschemeι.le ⟨z, rfl⟩
    rcases support_inf_subset T₁ T₂ hz with h | h
    · exact Or.inl (cover p₁ e₁ z h)
    · exact Or.inr (cover p₂ e₂ z h)
  have : UniversallyClosed (K.subschemeι ≫ f) :=
    universallyClosed_of_cover p₁ p₂ _ u₁ u₂ hc
  exact ⟨⟩

end GlobalTheory.CompanionTheory.GE.Union
