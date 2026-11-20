import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle

open CategoryTheory UpperTheory.V.KH

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Supply the required witnesses or components.
-/
theorem UpperTheory.V.KH.imageRep :
    ∀ (G : Type) [Group G] (C B M : Rep ℤ G) (d : C ⟶ B) (e : B ⟶ M), Function.Exact d.hom e.hom →
      ∃ (K : Rep ℤ G) (p : C ⟶ K) (i : K ⟶ B), Function.Surjective p.hom ∧ Function.Injective i.hom ∧
        (∀ x, i.hom (p.hom x) = d.hom x) ∧ Function.Exact i.hom e.hom := by
  intro G _ C B M d e h
  have hs : Function.Surjective (Abelian.factorThruImage d).hom :=
    (Rep.epi_iff_surjective _).1 inferInstance
  have hi : Function.Injective (Abelian.image.ι d).hom :=
    (Rep.mono_iff_injective _).1 inferInstance
  have hc : ∀ x, (Abelian.image.ι d).hom ((Abelian.factorThruImage d).hom x) = d.hom x := by
    intro x
    have := congrArg (fun f : C ⟶ B => f.hom x) (Abelian.image.fac d)
    simpa using this
  refine ⟨Abelian.image d, Abelian.factorThruImage d, Abelian.image.ι d, hs, hi, hc, ?_⟩
  intro y
  rw [h y]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, hc x⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := hs z
    exact ⟨x, (hc x).symm⟩
