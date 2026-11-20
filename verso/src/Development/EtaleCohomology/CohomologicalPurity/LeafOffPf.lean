import Development.EtaleCohomology.CohomologicalPurity.LeafClCut

open CategoryTheory AlgebraicGeometry

namespace LateralTheory.CohomologicalPurity.Cl

/- English proof (translation)
Introduce `d P F`. Apply `le_antisymm F.h` to reduce the goal to its premises. Introduce `y hy`. Express the relevant statement in the definitionally equal form `y ∉ PrimeSpectrum.zeroLocus (F.I : Set F.B)`. Introduce `hz`.

Establish `hk : RingHom.ker (Ideal.Quotient.mk F.I) = F.I` using `Ideal.mk_ker`. Establish `hr : y ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk F.I))`. Rewrite using `[range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, hk]`. Conclude with `hz`. Take `⟨y0, rfl⟩` from `hr`.

Establish `hw` using `congrArg (fun g => g.base y0) F.cart.w`. Simplify using `only [Scheme.Hom.comp_base] at hw`. Establish `hU : F.w.base ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk F.I))).base y0) ∈ (P.U : Set P.X)` using `hy`. Rewrite `hU` using `[P.hU]`. Conclude with `hU ⟨F.z.base y0, hw.symm⟩`.
-/
theorem LeafOff_of : LeafOff := by
  intro d P F
  apply le_antisymm F.h
  intro y hy
  change y ∉ PrimeSpectrum.zeroLocus (F.I : Set F.B)
  intro hz
  have hk : RingHom.ker (Ideal.Quotient.mk F.I) = F.I := Ideal.mk_ker
  have hr : y ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk F.I)) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, hk]; exact hz
  obtain ⟨y0, rfl⟩ := hr
  have hw := congrArg (fun g => g.base y0) F.cart.w
  simp only [Scheme.Hom.comp_base] at hw
  have hU : F.w.base ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk F.I))).base y0) ∈ (P.U : Set P.X) := hy
  rw [P.hU] at hU
  exact hU ⟨F.z.base y0, hw.symm⟩

end LateralTheory.CohomologicalPurity.Cl
