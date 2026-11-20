import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.CuspRep

/- English proof (translation)
Introduce `E _ _ _ a r _ _ μ 𝓕 hμ h𝓕 f hf y g`. Use `haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm`. Use `haveI : Countable (ratN E a r) := by`. Establish `: ((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)) = Set.range (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r))` using `AddMonoidHom.coe_range _`. Express the relevant statement in the definitionally equal form `Countable (((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)))`.

Rewrite using `[this]`. Conclude with `(Set.countable_range _).to_subtype`. Use `set h : (BlockIx a r → Ad E) → ℂ := fun x => f (unip x * g) with hh`. Establish `hinv : ∀ (γ : ratN E a r) (x : BlockIx a r → Ad E), h (γ +ᵥ x) = h x`. Introduce and unpack `⟨_, e, rfl⟩ x`.

Express the relevant statement in the definitionally equal form `f (unip ((fun p => algebraMap E (Ad E) (e p)) + x) * g) = f (unip x * g)`. Rewrite using `[unip_add, unip_algebraMap, mul_assoc, hf]`. Establish `hL : ∀ x, f (unip x * (unip y * g)) = h (x + y)` using `fun x => by`. Simplify using `only [hh, unip_add, mul_assoc]`. Repeatedly rewrite using `[hL]`.

Establish `hmp : MeasurePreserving (fun x : BlockIx a r → Ad E => x + y) μ μ` using `measurePreserving_add_right μ y`. Establish `hemb : MeasurableEmbedding (fun x : BlockIx a r → Ad E => x + y)` using `(MeasurableEquiv.addRight y).measurableEmbedding`. Set `S : Set (BlockIx a r → Ad E)` to `(fun x => x - y) ⁻¹' 𝓕`. Establish `hpre : (fun x : BlockIx a r → Ad E => x + y) ⁻¹' S = 𝓕`. Use extensionality with `x`.

Simplify using `[S]`. Establish `hS : IsAddFundamentalDomain (ratN E a r) S μ`. Use `h𝓕.preimage_of_equiv (e := id) ?_ Function.bijective_id ?_` and prove the remaining obligations. Conclude with `(measurePreserving_sub_right μ y).quasiMeasurePreserving`. Introduce `γ x`.

Express the relevant statement in the definitionally equal form `(γ : BlockIx a r → Ad E) + x - y = (γ : BlockIx a r → Ad E) + (x - y)`. Normalize the expressions using the abelian group laws. Combine the equalities or inequalities in the displayed calculation.
-/
theorem constTerm_unip_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → ∀ f : GA E a → ℂ, (∀ γ g, f (ratGL E a γ * g) = f g) → ∀ (y : BlockIx a r → Ad E) (g : GA E a), ∫ x in 𝓕, f (unip x * (unip y * g)) ∂μ = ∫ x in 𝓕, f (unip x * g) ∂μ := by
  intro E _ _ _ a r _ _ μ 𝓕 hμ h𝓕 f hf y g
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable (ratN E a r) := by
    have : ((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)) = Set.range
        (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)) := AddMonoidHom.coe_range _
    change Countable (((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)))
    rw [this]; exact (Set.countable_range _).to_subtype
  set h : (BlockIx a r → Ad E) → ℂ := fun x => f (unip x * g) with hh
  have hinv : ∀ (γ : ratN E a r) (x : BlockIx a r → Ad E), h (γ +ᵥ x) = h x := by
    rintro ⟨_, e, rfl⟩ x
    change f (unip ((fun p => algebraMap E (Ad E) (e p)) + x) * g) = f (unip x * g)
    rw [unip_add, unip_algebraMap, mul_assoc, hf]
  have hL : ∀ x, f (unip x * (unip y * g)) = h (x + y) := fun x => by
    simp only [hh, unip_add, mul_assoc]
  simp_rw [hL]

  have hmp : MeasurePreserving (fun x : BlockIx a r → Ad E => x + y) μ μ := measurePreserving_add_right μ y
  have hemb : MeasurableEmbedding (fun x : BlockIx a r → Ad E => x + y) :=
    (MeasurableEquiv.addRight y).measurableEmbedding
  let S : Set (BlockIx a r → Ad E) := (fun x => x - y) ⁻¹' 𝓕
  have hpre : (fun x : BlockIx a r → Ad E => x + y) ⁻¹' S = 𝓕 := by
    ext x; simp [S]
  have hS : IsAddFundamentalDomain (ratN E a r) S μ := by
    refine h𝓕.preimage_of_equiv (e := id) ?_ Function.bijective_id ?_
    · exact (measurePreserving_sub_right μ y).quasiMeasurePreserving
    · intro γ x
      change (γ : BlockIx a r → Ad E) + x - y = (γ : BlockIx a r → Ad E) + (x - y)
      abel
  calc ∫ x in 𝓕, h (x + y) ∂μ = ∫ x in (fun x : BlockIx a r → Ad E => x + y) ⁻¹' S, h (x + y) ∂μ := by rw [hpre]
    _ = ∫ x in S, h x ∂μ := hmp.setIntegral_preimage_emb hemb h S
    _ = ∫ x in 𝓕, h x ∂μ := hS.setIntegral_eq h𝓕 hinv

end GlobalTheory.CuspRep
