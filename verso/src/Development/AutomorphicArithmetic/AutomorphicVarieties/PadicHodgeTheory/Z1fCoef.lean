import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaSpec
open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc Topology NumberField IsDedekindDomain

/- English proof (translation)
Introduce `l _ H _ _ φ A A' V V' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ρ ρ' f hfc hf c hc`. Take `⟨⟨hc, hcc⟩, x, hx⟩` from `hc`. Use `⟨⟨hfc.comp hc, fun g h => ?_⟩, LinearMap.rTensor (Bcr l) f x, fun g => ?_⟩` and prove the remaining obligations. Simplify using `only [hcc g h, map_add, hf]`. Establish `key : ∀ y : TensorProduct ℚ_[l] V (Bcr l), LinearMap.rTensor (Bcr l) f (actC φ ρ g y) = actC φ ρ' g (LinearMap.rTensor (Bcr l) f y)`.

Introduce `y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [actC, hf]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.

Rewrite using `[← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]`.
-/
theorem UpperTheory.V.Loc.z1fCoef :
    ∀ {l : ℕ} [Fact l.Prime] {H : Type} [Group H] [TopologicalSpace H] (φ : H →* GQ l) {A A' V V' : Type} [CommRing A] [Algebra ℚ_[l] A] [CommRing A'] [Algebra ℚ_[l] A'] [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] [AddCommGroup V'] [Module A' V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A' V'] [TopologicalSpace V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul A' V'] (ρ : Representation A H V) (ρ' : Representation A' H V') (f : V →ₗ[ℚ_[l]] V'), Continuous f → (∀ g x, f (ρ g x) = ρ' g (f x)) → ∀ c ∈ finiteCocycles φ ρ, (fun g => f (c g)) ∈ finiteCocycles φ ρ' := by
  intro l _ H _ _ φ A A' V V' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ρ ρ' f hfc hf c hc
  obtain ⟨⟨hc, hcc⟩, x, hx⟩ := hc
  refine ⟨⟨hfc.comp hc, fun g h => ?_⟩, LinearMap.rTensor (Bcr l) f x, fun g => ?_⟩
  · simp only [hcc g h, map_add, hf]
  · have key : ∀ y : TensorProduct ℚ_[l] V (Bcr l), LinearMap.rTensor (Bcr l) f (actC φ ρ g y) =
        actC φ ρ' g (LinearMap.rTensor (Bcr l) f y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [actC, hf]
      | add a b ha hb => simp only [map_add, ha, hb]
    rw [← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]
