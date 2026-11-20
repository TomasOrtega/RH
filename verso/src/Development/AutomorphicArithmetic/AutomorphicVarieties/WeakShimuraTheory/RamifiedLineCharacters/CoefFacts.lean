import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MemRamLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Introduce `l _ c k _ a ha`. Use `haveI := c.dvr`. Use `haveI := c.fin`. Take `⟨_, hfin, hl, -⟩` from `UpperTheory.V.abelian₂.dvr_finite l c.O`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Establish `hk : (l : k) = 0`. Rewrite using `[← map_natCast a l]`. Conclude with `ha _ hl`. Conclude with `(CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).2 hk`. Set `f : ResidueField c.O →+* k` to `Ideal.Quotient.lift (maximalIdeal c.O) a ha`.

Use `(Set.finite_range f).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `⟨IsLocalRing.residue c.O x, Ideal.Quotient.lift_mk _ _ _⟩`.
-/
theorem UpperTheory.V.Ws.Gys.coefFacts :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → CharP k l ∧ (Set.range a).Finite := by
  intro l _ c k _ a ha
  haveI := c.dvr
  haveI := c.fin
  obtain ⟨_, hfin, hl, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  refine ⟨?_, ?_⟩
  · have hk : (l : k) = 0 := by
      rw [← map_natCast a l]
      exact ha _ hl
    exact (CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).2 hk
  · let f : ResidueField c.O →+* k := Ideal.Quotient.lift (maximalIdeal c.O) a ha
    refine (Set.finite_range f).subset ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨IsLocalRing.residue c.O x, Ideal.Quotient.lift_mk _ _ _⟩
