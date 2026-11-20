import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.StarVirtualCharacterEqApplyInvStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldOfRepresentationStatement

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Use `haveI : Invertible (Nat.card H : ℂ) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')`. Establish `key` using `Representation.card_inv_mul_sum_char_mul_char_eq_finrank κ ρ`. Establish `hsum : (∑ g : H, κ.character g⁻¹ * ρ.character g) = ∑ g : H, ρ.character g * κ.character g⁻¹` using `Finset.sum_congr rfl fun g _ => mul_comm _ _`. Establish `hc : (Nat.card H : ℂ)⁻¹ ≠ 0` using `inv_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')`. Rewrite using `[hsum]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hpos : Module.finrank ℂ (Representation.IntertwiningMap κ ρ) ≠ 0`. Introduce `h0`. Rewrite `key` using `[h0, Nat.cast_zero]`.

Conclude with `h ((mul_eq_zero.mp key).resolve_left hc)`. Use `haveI := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hpos)`. Take `⟨φ, hφ⟩` from `exists_ne (0 : Representation.IntertwiningMap κ ρ)`. Use `⟨φ.toLinearMap, ?_, fun g x => Representation.IntertwiningMap.isIntertwining κ ρ φ g x⟩` and prove the remaining obligations. Introduce `h0`.

Conclude with `hφ (Representation.IntertwiningMap.ext (by simpa using h0))`. Introduce and unpack `⟨f, hf0, hf⟩`. Set `φ` to `f.intertwiningMap_of_isIntertwiningMap κ ρ hf`. Establish `hφ : φ ≠ 0`. Introduce `h0`.

Apply `hf0` to reduce the goal to its premises. Use extensionality with `x`. Use `congrArg (fun ψ : Representation.IntertwiningMap κ ρ => ψ x) h0` as an intermediate fact. Simplify `this` using `[φ]`. Establish `hpos : Module.finrank ℂ (Representation.IntertwiningMap κ ρ) ≠ 0`.

Rewrite using `[← (Representation.invariantsEquivIntertwiningMap κ ρ).finrank_eq]`. Apply `Nat.pos_iff_ne_zero.mp` to reduce the goal to its premises. Rewrite using `[Module.finrank_pos_iff_exists_ne_zero]`. Use `⟨(Representation.invariantsEquivIntertwiningMap κ ρ).symm φ, ?_⟩` and prove the remaining obligations. Simplify using `using hφ`.

Introduce `hs`. Rewrite `key` using `[hs, mul_zero]`. Conclude with `hpos (by exact_mod_cast key.symm)`.
-/
private theorem sum_ne_iff {H V W : Type} [Group H] [Fintype H] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ H V) (κ : Representation ℂ H W) :
    (∑ g : H, κ.character g⁻¹ * ρ.character g ≠ 0) ↔
      ∃ f : W →ₗ[ℂ] V, f ≠ 0 ∧ ∀ g x, f (κ g x) = ρ g (f x) := by
  classical
  haveI : Invertible (Nat.card H : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have key := Representation.card_inv_mul_sum_char_mul_char_eq_finrank κ ρ
  have hsum : (∑ g : H, κ.character g⁻¹ * ρ.character g) =
      ∑ g : H, ρ.character g * κ.character g⁻¹ :=
    Finset.sum_congr rfl fun g _ => mul_comm _ _
  have hc : (Nat.card H : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [hsum]
  constructor
  · intro h
    have hpos : Module.finrank ℂ (Representation.IntertwiningMap κ ρ) ≠ 0 := by
      intro h0
      rw [h0, Nat.cast_zero] at key
      exact h ((mul_eq_zero.mp key).resolve_left hc)
    haveI := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hpos)
    obtain ⟨φ, hφ⟩ := exists_ne (0 : Representation.IntertwiningMap κ ρ)
    refine ⟨φ.toLinearMap, ?_, fun g x => Representation.IntertwiningMap.isIntertwining κ ρ φ g x⟩
    intro h0
    exact hφ (Representation.IntertwiningMap.ext (by simpa using h0))
  · rintro ⟨f, hf0, hf⟩
    let φ := f.intertwiningMap_of_isIntertwiningMap κ ρ hf
    have hφ : φ ≠ 0 := by
      intro h0
      apply hf0
      ext x
      have := congrArg (fun ψ : Representation.IntertwiningMap κ ρ => ψ x) h0
      simpa [φ] using this
    have hpos : Module.finrank ℂ (Representation.IntertwiningMap κ ρ) ≠ 0 := by
      rw [← (Representation.invariantsEquivIntertwiningMap κ ρ).finrank_eq]
      apply Nat.pos_iff_ne_zero.mp
      rw [Module.finrank_pos_iff_exists_ne_zero]
      refine ⟨(Representation.invariantsEquivIntertwiningMap κ ρ).symm φ, ?_⟩
      simpa using hφ
    intro hs
    rw [hs, mul_zero] at key
    exact hpos (by exact_mod_cast key.symm)

/- English proof (translation)
Introduce `H V W _ _ _ _ _ _ _ _ ρ κ`. Use `haveI := Fintype.ofFinite H`. Establish `hstar : ∀ g : H, star (LinearMap.trace ℂ W (κ g)) = κ.character g⁻¹`. Introduce `g`. Establish `hmem : (fun g => algebraMap ℂ ℂ (κ.character g)) ∈ GlobalTheory.BI.Virt ℂ ℂ H` using `AddSubgroup.subset_closure (GlobalTheory.T.isCharacterOverSubfield_of_representation ℂ ℂ H W κ).1`.

Use `GlobalTheory.T.star_virtualCharacter_eq_apply_inv H _ hmem g` as an intermediate fact. Express the relevant statement in the definitionally equal form `star (κ.character g) = _`. Simplify using `using this`. Establish `hM : Meets ρ (fun g => LinearMap.trace ℂ W (κ g)) ↔ ∑ g : H, κ.character g⁻¹ * ρ.character g ≠ 0`. Unfold `Meets`.

Rewrite using `[finsum_eq_sum_of_fintype]`. Simplify using `only [hstar]`. Both sides reduce to the same expression. Establish `hswap : (∑ g : H, κ.character g⁻¹ * ρ.character g) = ∑ g : H, ρ.character g⁻¹ * κ.character g` using `Fintype.sum_equiv (Equiv.inv H) _ _ fun g => by simp [mul_comm]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hM, hswap]`. Conclude with `sum_ne_iff κ ρ`. Rewrite using `[hM]`. Conclude with `sum_ne_iff ρ κ`.
-/
theorem UpperTheory.Gal.InertialTypesAlt.meetsIff :
    MeetsIff := by
  intro H V W _ _ _ _ _ _ _ _ ρ κ
  classical
  haveI := Fintype.ofFinite H
  have hstar : ∀ g : H, star (LinearMap.trace ℂ W (κ g)) = κ.character g⁻¹ := by
    intro g
    have hmem : (fun g => algebraMap ℂ ℂ (κ.character g)) ∈ GlobalTheory.BI.Virt ℂ ℂ H :=
      AddSubgroup.subset_closure (GlobalTheory.T.isCharacterOverSubfield_of_representation ℂ ℂ H W κ).1
    have := GlobalTheory.T.star_virtualCharacter_eq_apply_inv H _ hmem g
    change star (κ.character g) = _
    simpa using this
  have hM : Meets ρ (fun g => LinearMap.trace ℂ W (κ g)) ↔
      ∑ g : H, κ.character g⁻¹ * ρ.character g ≠ 0 := by
    unfold Meets
    rw [finsum_eq_sum_of_fintype]
    simp only [hstar]
    rfl
  have hswap : (∑ g : H, κ.character g⁻¹ * ρ.character g) =
      ∑ g : H, ρ.character g⁻¹ * κ.character g :=
    Fintype.sum_equiv (Equiv.inv H) _ _ fun g => by simp [mul_comm]
  refine ⟨?_, ?_⟩
  · rw [hM, hswap]
    exact sum_ne_iff κ ρ
  · rw [hM]
    exact sum_ne_iff ρ κ
