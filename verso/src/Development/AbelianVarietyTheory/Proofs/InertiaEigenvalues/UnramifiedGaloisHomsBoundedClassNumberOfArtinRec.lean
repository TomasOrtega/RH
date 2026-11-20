import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import ReciprocityTheory.GaloisValuations.Global
import Formalism.WachLatticeTwists.CoprimeLiftBounds.Statement
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import ReciprocityTheory.NeutralLocalFields.HilbertClassField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HilbertClassFieldOfGlobalArtinReciprocityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthAddMonoidHomFiniteGroupFractionQuotientLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HilbertSubgroupLeKerOfKillsInertiaStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisAddHomVanishesComplexConjugationStatement
open Formalism.NG Formalism.RepresentationBoundsCohomology.BR NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.UnramifiedClassBound
open Neutral.HilbertClassField

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ Av hAv l _ O _ _ _ _ _ hl M _ _ hM ρ hρ S hS hU`. Take `⟨eM⟩` from `hM`. Take `⟨art, hsurj, hker, -⟩` from `GlobalTheory.T.hilbertClassField_of_globalArtinReciprocity hA E Ω`. Set `ψ : (Additive (ClassGroup (𝓞 E)) →+ M) →ₗ[O] coZ1s ρ` to `{ toFun := fun f => ⟨fun g => f (Additive.ofMul (art g)), fun g h => by show f (Additive.ofMul (art (g * h))) = f (Additive.ofMul (art g)) + ρ g (f (Additive.ofMul (art h)))`. Rewrite using `[hρ, map_mul, ofMul_mul, map_add]⟩`.

Use the proof step `map_add' := fun f f' => rfl`. Use the proof step `map_smul' := fun r f => rfl }`. Set `Φ` to `(Submodule.mkQ ((coB1 ρ).comap (coZ1s ρ).subtype)) ∘ₗ ψ`. Establish `hle : S ≤ LinearMap.range Φ`. Introduce `x hx`.

Take `⟨z, rfl, hlc⟩` from `hS x hx`. Establish `hz : ∀ g h : G E Ω, (z : G E Ω → M) (g * h) = (z : G E Ω → M) g + (z : G E Ω → M) h`. Introduce `g h`. Use `z.2 g h` as an intermediate fact. Rewrite `this` using `[hρ]`.

Conclude with `this`. Establish `hI : ∀ v, ∀ σ ∈ Ine (F` using `E) (Av v), (z : G E Ω → M) σ = 0 := by`. Introduce `v σ hσ`. Establish `h1` using `hU v hx`. Rewrite `h1` using `[unrH1, LinearMap.mem_ker, Formalism.NG.resH1, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]`.

Take `⟨w, hw⟩` from `h1`. Use `congrFun hw ⟨σ, hσ⟩` as an intermediate fact. Simplify using `only [coD0, resRep, LinearMap.coe_mk, AddHom.coe_mk] at this`. Conclude with `(show (z : G E Ω → M) σ = _ from this.symm).trans (by simp [hρ])`. Establish `hkill` using `GlobalTheory.T.hilbertSubgroup_le_ker_of_kills_inertia E Ω Av hAv M z hz hlc hI (fun c hc => GlobalTheory.T.galoisAddHom_vanishes_complexConjugation E Ω l O hl M z hz c hc)`.

Set `zH : G E Ω →* Multiplicative M` to `{ toFun := fun g => Multiplicative.ofAdd ((z : G E Ω → M) g) map_one' := by`. Use `hz 1 1` as an intermediate fact. Simplify using `only [mul_one] at this`. Establish `h0 : (z : G E Ω → M) 1 = 0`. Use `congrArg (fun t => t - (z : G E Ω → M) 1) this` as an intermediate fact.

Simplify using `using this.symm`. Simplify using `[h0]`. Use the proof step `map_mul' := fun g h => by simp [hz g h] }`. Establish `hk : art.ker ≤ zH.ker`. Introduce `σ hσ`.

Rewrite `hσ` using `[hker]`. Simplify using `[zH, MonoidHom.mem_ker, hkill σ hσ]`. Set `Lf` to `(MonoidHom.liftOfSurjective art hsurj) ⟨zH, hk⟩`. Set `f : Additive (ClassGroup (𝓞 E)) →+ M` to `{ toFun := fun a => Multiplicative.toAdd (Lf (Additive.toMul a)) map_zero' := by simp map_add' := fun a b => by simp }`. Use `⟨f, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Submodule.mkQ _ (ψ f) = Submodule.mkQ _ z`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Use `show Multiplicative.toAdd (Lf (art g)) = (z : G E Ω → M) g`.

Rewrite using `[MonoidHom.liftOfRightInverse_comp_apply]`. Both sides reduce to the same expression. Combine the equalities or inequalities in the displayed calculation. Use `GlobalTheory.T.length_addMonoidHom_finite_group_fractionQuotient_le l O M eM (Additive (ClassGroup (𝓞 E)))` as an intermediate fact. Rewrite using `[show Nat.card (Additive (ClassGroup (𝓞 E))) = classNumber E from by` and apply the resulting hypothesis.

Rewrite using `[NumberField.classNumber, ← Nat.card_eq_fintype_card]`. Use the proof step `rfl] at this`.
-/
theorem vhE_of_globalArtinReciprocity (hA : GlobalTheory.Published.GlobalArtinReciprocity) : ReciprocityTheory.ChartRestriction.T2.VhE := by
  intro E Ω _ _ _ _ _ Av hAv l _ O _ _ _ _ _ hl M _ _ hM ρ hρ S hS hU
  obtain ⟨eM⟩ := hM
  obtain ⟨art, hsurj, hker, -⟩ := GlobalTheory.T.hilbertClassField_of_globalArtinReciprocity hA E Ω

  let ψ : (Additive (ClassGroup (𝓞 E)) →+ M) →ₗ[O] coZ1s ρ :=
    { toFun := fun f => ⟨fun g => f (Additive.ofMul (art g)), fun g h => by
        show f (Additive.ofMul (art (g * h))) = f (Additive.ofMul (art g)) + ρ g (f (Additive.ofMul (art h)))
        rw [hρ, map_mul, ofMul_mul, map_add]⟩
      map_add' := fun f f' => rfl
      map_smul' := fun r f => rfl }
  let Φ := (Submodule.mkQ ((coB1 ρ).comap (coZ1s ρ).subtype)) ∘ₗ ψ
  have hle : S ≤ LinearMap.range Φ := by
    intro x hx
    obtain ⟨z, rfl, hlc⟩ := hS x hx
    have hz : ∀ g h : G E Ω, (z : G E Ω → M) (g * h) = (z : G E Ω → M) g + (z : G E Ω → M) h := by
      intro g h
      have := z.2 g h
      rw [hρ] at this
      exact this
    have hI : ∀ v, ∀ σ ∈ Ine (F := E) (Av v), (z : G E Ω → M) σ = 0 := by
      intro v σ hσ
      have h1 := hU v hx
      rw [unrH1, LinearMap.mem_ker, Formalism.NG.resH1, Submodule.mkQ_apply, Submodule.mapQ_apply,
        Submodule.Quotient.mk_eq_zero] at h1
      obtain ⟨w, hw⟩ := h1
      have := congrFun hw ⟨σ, hσ⟩
      simp only [coD0, resRep, LinearMap.coe_mk, AddHom.coe_mk] at this
      exact (show (z : G E Ω → M) σ = _ from this.symm).trans (by simp [hρ])
    have hkill := GlobalTheory.T.hilbertSubgroup_le_ker_of_kills_inertia E Ω Av hAv M z hz hlc hI (fun c hc => GlobalTheory.T.galoisAddHom_vanishes_complexConjugation E Ω l O hl M z hz c hc)
    let zH : G E Ω →* Multiplicative M :=
      { toFun := fun g => Multiplicative.ofAdd ((z : G E Ω → M) g)
        map_one' := by
          have := hz 1 1
          simp only [mul_one] at this
          have h0 : (z : G E Ω → M) 1 = 0 := by
            have := congrArg (fun t => t - (z : G E Ω → M) 1) this
            simpa using this.symm
          simp [h0]
        map_mul' := fun g h => by simp [hz g h] }
    have hk : art.ker ≤ zH.ker := by
      intro σ hσ
      rw [hker] at hσ
      simp [zH, MonoidHom.mem_ker, hkill σ hσ]
    let Lf := (MonoidHom.liftOfSurjective art hsurj) ⟨zH, hk⟩
    let f : Additive (ClassGroup (𝓞 E)) →+ M :=
      { toFun := fun a => Multiplicative.toAdd (Lf (Additive.toMul a))
        map_zero' := by simp
        map_add' := fun a b => by simp }
    refine ⟨f, ?_⟩
    change Submodule.mkQ _ (ψ f) = Submodule.mkQ _ z
    congr 1
    apply Subtype.ext
    funext g
    show Multiplicative.toAdd (Lf (art g)) = (z : G E Ω → M) g
    rw [MonoidHom.liftOfRightInverse_comp_apply]
    rfl
  calc Module.length O S ≤ Module.length O (LinearMap.range Φ) :=
        Module.length_le_of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
    _ ≤ Module.length O (Additive (ClassGroup (𝓞 E)) →+ M) :=
        Module.length_le_of_surjective Φ.rangeRestrict Φ.surjective_rangeRestrict
    _ ≤ _ := by
        have := GlobalTheory.T.length_addMonoidHom_finite_group_fractionQuotient_le l O M eM (Additive (ClassGroup (𝓞 E)))
        rwa [show Nat.card (Additive (ClassGroup (𝓞 E))) = classNumber E from by
          rw [NumberField.classNumber, ← Nat.card_eq_fintype_card]; rfl] at this
end GlobalTheory.UnramifiedClassBound
