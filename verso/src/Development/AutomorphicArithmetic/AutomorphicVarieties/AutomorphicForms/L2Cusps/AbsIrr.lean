import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt

/- English proof (translation)
Introduce `G G₁ H L _ _ _ _ _ _ _ _ π ρ J r hr hρ X hXJ hX`. Take `⟨⟨hXc, hXinv⟩, hXne, hXmin⟩` from `hX`. Establish `hVc : IsClosed ((Submodule.comap J.toLinearMap X : Submodule ℂ H) : Set H)` using `hXc.preimage J.continuous`. Use `haveI hVcomp : CompleteSpace (Submodule.comap J.toLinearMap X) := hVc.completeSpace_coe`. Establish `hinv : π.IsInvariant (Submodule.comap J.toLinearMap X)`.

Introduce `g₁ v hv`. Take `⟨g, rfl⟩` from `hr g₁`. Use `show J (π (r g) v) ∈ X`. Rewrite using `[← hρ]`. Conclude with `hXinv g _ hv`.

Use `⟨hVcomp, hinv, ?_, ?_⟩` and prove the remaining obligations. Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hXne`. Take `⟨h, rfl⟩` from `hXJ hx`. Use `nontrivial_of_ne (⟨h, hx⟩ : Submodule.comap J.toLinearMap X) 0 ?_` and prove the remaining obligations. Introduce `e`.

Apply `hx0` to reduce the goal to its premises. Establish `e' : h = 0` using `congrArg Subtype.val e`. Rewrite using `[e', map_zero]`. Introduce `U' hU'c hU'inv`. Set `V` to `Submodule.comap J.toLinearMap X`.

Set `U : Submodule ℂ L` to `(U'.map V.subtype).map J.toLinearMap`. Establish `hUX : U ≤ X`. Introduce and unpack `_ ⟨_, ⟨u, _, rfl⟩, rfl⟩`. Conclude with `u.2`. Establish `hU'H : IsClosed ((U'.map V.subtype : Submodule ℂ H) : Set H)`.

Rewrite using `[Submodule.map_coe]`. Conclude with `hVc.isClosedEmbedding_subtypeVal.isClosedMap _ hU'c`. Establish `hUc : IsClosed (U : Set L)`. Rewrite using `[Submodule.map_coe]`. Conclude with `J.isometry.isClosedEmbedding.isClosedMap _ hU'H`.

Establish `hUinv : ∀ g, ∀ v ∈ U, ρ g v ∈ U`. Introduce and unpack `g _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩`. Use `⟨_, ⟨⟨π (r g) u, hinv _ _ u.2⟩, hU'inv (r g) u hu, rfl⟩, ?_⟩` and prove the remaining obligations. Conclude with `(hρ g u).symm`. Break down `hXmin U hUX ⟨hUc, hUinv⟩ with h | h` into its components or cases.

Use `left`. Rewrite using `[eq_bot_iff]`. Introduce `u hu`. Establish `hJu : J u ∈ U` using `⟨u, ⟨u, hu, rfl⟩, rfl⟩`. Rewrite `hJu` using `[h, Submodule.mem_bot]`.

Rewrite using `[Submodule.mem_bot]`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `hn : ‖(u : H)‖ = 0` using `by rw [← J.norm_map, hJu, norm_zero]`. Simplify using `using hn`. Use `right`.

Rewrite using `[eq_top_iff]`. Introduce `u _`. Establish `hJu : J u ∈ U`. Rewrite using `[h]`. Conclude with `u.2`.

Take `⟨_, ⟨u', hu', rfl⟩, he⟩` from `hJu`. Establish `: u' = u` using `Subtype.ext (J.injective he)`. Rewrite using `[← this]`. Conclude with `hu'`.
-/
theorem UpperTheory.V.KernelIndexFullLattice.absIrr_holds :
    UpperTheory.V.KernelIndexFullLattice.AbsIrr := by
  intro G G₁ H L _ _ _ _ _ _ _ _ π ρ J r hr hρ X hXJ hX
  obtain ⟨⟨hXc, hXinv⟩, hXne, hXmin⟩ := hX
  have hVc : IsClosed ((Submodule.comap J.toLinearMap X : Submodule ℂ H) : Set H) :=
    hXc.preimage J.continuous
  haveI hVcomp : CompleteSpace (Submodule.comap J.toLinearMap X) := hVc.completeSpace_coe
  have hinv : π.IsInvariant (Submodule.comap J.toLinearMap X) := by
    intro g₁ v hv
    obtain ⟨g, rfl⟩ := hr g₁
    show J (π (r g) v) ∈ X
    rw [← hρ]
    exact hXinv g _ hv
  refine ⟨hVcomp, hinv, ?_, ?_⟩
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hXne
    obtain ⟨h, rfl⟩ := hXJ hx
    refine nontrivial_of_ne (⟨h, hx⟩ : Submodule.comap J.toLinearMap X) 0 ?_
    intro e
    apply hx0
    have e' : h = 0 := congrArg Subtype.val e
    rw [e', map_zero]
  · intro U' hU'c hU'inv
    let V := Submodule.comap J.toLinearMap X
    let U : Submodule ℂ L := (U'.map V.subtype).map J.toLinearMap
    have hUX : U ≤ X := by
      rintro _ ⟨_, ⟨u, _, rfl⟩, rfl⟩
      exact u.2
    have hU'H : IsClosed ((U'.map V.subtype : Submodule ℂ H) : Set H) := by
      rw [Submodule.map_coe]
      exact hVc.isClosedEmbedding_subtypeVal.isClosedMap _ hU'c
    have hUc : IsClosed (U : Set L) := by
      rw [Submodule.map_coe]
      exact J.isometry.isClosedEmbedding.isClosedMap _ hU'H
    have hUinv : ∀ g, ∀ v ∈ U, ρ g v ∈ U := by
      rintro g _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨_, ⟨⟨π (r g) u, hinv _ _ u.2⟩, hU'inv (r g) u hu, rfl⟩, ?_⟩
      exact (hρ g u).symm
    rcases hXmin U hUX ⟨hUc, hUinv⟩ with h | h
    · left
      rw [eq_bot_iff]
      intro u hu
      have hJu : J u ∈ U := ⟨u, ⟨u, hu, rfl⟩, rfl⟩
      rw [h, Submodule.mem_bot] at hJu
      rw [Submodule.mem_bot]
      apply Subtype.ext
      have hn : ‖(u : H)‖ = 0 := by rw [← J.norm_map, hJu, norm_zero]
      simpa using hn
    · right
      rw [eq_top_iff]
      intro u _
      have hJu : J u ∈ U := by
        rw [h]
        exact u.2
      obtain ⟨_, ⟨u', hu', rfl⟩, he⟩ := hJu
      have : u' = u := Subtype.ext (J.injective he)
      rw [← this]
      exact hu'
