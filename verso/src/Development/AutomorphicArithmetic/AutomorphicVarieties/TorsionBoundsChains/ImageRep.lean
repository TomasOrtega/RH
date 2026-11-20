import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle

open CategoryTheory UpperTheory.V.KH

/- English proof (translation)
Introduce `G _ C B M d e h`. Establish `hs : Function.Surjective (Abelian.factorThruImage d).hom` using `(Rep.epi_iff_surjective _).1 inferInstance`. Establish `hi : Function.Injective (Abelian.image.ι d).hom` using `(Rep.mono_iff_injective _).1 inferInstance`. Establish `hc : ∀ x, (Abelian.image.ι d).hom ((Abelian.factorThruImage d).hom x) = d.hom x`. Introduce `x`.

Use `congrArg (fun f : C ⟶ B => f.hom x) (Abelian.image.fac d)` as an intermediate fact. Simplify using `using this`. Use `⟨Abelian.image d, Abelian.factorThruImage d, Abelian.image.ι d, hs, hi, hc, ?_⟩` and prove the remaining obligations. Introduce `y`. Rewrite using `[h y]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩`. Conclude with `⟨_, hc x⟩`. Introduce and unpack `⟨z, rfl⟩`. Take `⟨x, rfl⟩` from `hs z`.

Conclude with `⟨x, (hc x).symm⟩`.
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
