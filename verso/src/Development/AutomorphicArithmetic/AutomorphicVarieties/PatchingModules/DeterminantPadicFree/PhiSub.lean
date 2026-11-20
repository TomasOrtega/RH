import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Introduce `l G _ _ _ H hH hG`. Unfold `PhiCond at *`. Introduce `K hK`. Establish `hK' : IsOpen ((K.map H.subtype : Subgroup G) : Set G)`. Rewrite using `[Subgroup.coe_map]`.

Conclude with `hH.isOpenMap_subtype_val _ hK`. Use `haveI := hG (K.map H.subtype) hK'`. Set `e` to `Subgroup.equivMapOfInjective K H.subtype H.subtype_injective`. Establish `he : ∀ y : K.map H.subtype, (((e.symm y : K) : H) : G) = (y : G)` using `fun y => congrArg Subtype.val (e.apply_symm_apply y)`. Establish `hc : Continuous fun y : K.map H.subtype => (e.symm y : K)`.

Apply `continuous_induced_rng.2` to reduce the goal to its premises. Apply `continuous_induced_rng.2` to reduce the goal to its premises. Conclude with `continuous_subtype_val.congr fun y => (he y).symm`. Use `Finite.of_injective (β := {ψ : K.map H.subtype →* Multiplicative (ZMod l) // IsOpen (ψ.ker : Set (K.map H.subtype))}) (fun φ => ⟨φ.1.comp e.symm.toMonoidHom, by show IsOpen ((fun y => (e.symm y : K)) ⁻¹' (φ.1.ker : Set K))` and prove the remaining obligations. Conclude with `φ.2.preimage hc⟩) ?_`.

Introduce `φ ψ h`. Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `k`. Establish `h'` using `congrArg (fun χ : {ψ : K.map H.subtype →* Multiplicative (ZMod l) // IsOpen (ψ.ker : Set (K.map H.subtype))} => χ.1 (e k)) h`. Simplify using `using h'`.
-/
theorem UpperTheory.V.Pa.Det.phiSub :
    ∀ (l : ℕ) {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G), IsOpen (H : Set G) → PhiCond G l → PhiCond H l := by
  intro l G _ _ _ H hH hG
  unfold PhiCond at *
  intro K hK
  have hK' : IsOpen ((K.map H.subtype : Subgroup G) : Set G) := by
    rw [Subgroup.coe_map]
    exact hH.isOpenMap_subtype_val _ hK
  haveI := hG (K.map H.subtype) hK'
  let e := Subgroup.equivMapOfInjective K H.subtype H.subtype_injective
  have he : ∀ y : K.map H.subtype, (((e.symm y : K) : H) : G) = (y : G) := fun y =>
    congrArg Subtype.val (e.apply_symm_apply y)
  have hc : Continuous fun y : K.map H.subtype => (e.symm y : K) := by
    apply continuous_induced_rng.2
    apply continuous_induced_rng.2
    exact continuous_subtype_val.congr fun y => (he y).symm
  refine Finite.of_injective
    (β := {ψ : K.map H.subtype →* Multiplicative (ZMod l) // IsOpen (ψ.ker : Set (K.map H.subtype))})
    (fun φ => ⟨φ.1.comp e.symm.toMonoidHom, by
      show IsOpen ((fun y => (e.symm y : K)) ⁻¹' (φ.1.ker : Set K))
      exact φ.2.preimage hc⟩) ?_
  intro φ ψ h
  apply Subtype.ext
  ext k
  have h' := congrArg (fun χ : {ψ : K.map H.subtype →* Multiplicative (ZMod l) //
    IsOpen (ψ.ker : Set (K.map H.subtype))} => χ.1 (e k)) h
  simpa using h'
