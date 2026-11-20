import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

/- English proof (translation)
Introduce `A R _ _ _ _ ι hι q Q hQ hcomap hmin`. Use `letI : Algebra A R := ι.toAlgebra`. Use `haveI : Module.Flat A R := hι`. Use `haveI : Algebra.HasGoingDown A R := Algebra.HasGoingDown.of_flat`. Use `haveI : q.IsPrime := hcomap ▸ Ideal.comap_isPrime ι Q`.

Use `haveI : Q.LiesOver q := ⟨hcomap.symm⟩`. Rewrite using `[Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q Q]`. It suffices to establish `h0 : (Q.map (Ideal.Quotient.mk (q.map (algebraMap A R)))).height = 0 by`. Rewrite using `[h0, add_zero]`. Establish `hJQ : q.map (algebraMap A R) ≤ Q` using `hmin.1.2`.

Establish `hker : RingHom.ker (Ideal.Quotient.mk (q.map (algebraMap A R))) ≤ Q`. Rewrite using `[Ideal.mk_ker]`. Conclude with `hJQ`. Use `haveI : (Q.map (Ideal.Quotient.mk (q.map (algebraMap A R)))).IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker`. Rewrite using `[Ideal.height_eq_zero_iff]`.

Use `⟨⟨inferInstance, bot_le⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `K ⟨hK, -⟩ hKQ`. Establish `hle : K.comap (Ideal.Quotient.mk (q.map (algebraMap A R))) ≤ Q`. Introduce `x hx`. Take `⟨y, hy, hxy⟩` from `(Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp (hKQ hx)`.

Establish `hd : y - x ∈ q.map (algebraMap A R)` using `Ideal.Quotient.eq.mp hxy`. Establish `hx' : x = y - (y - x)` using `by ring`. Rewrite using `[hx']`. Conclude with `Q.sub_mem hy (hJQ hd)`. Establish `hc : Q ≤ K.comap (Ideal.Quotient.mk (q.map (algebraMap A R)))`.

Use `hmin.2 ⟨Ideal.comap_isPrime _ K, ?_⟩ hle` and prove the remaining obligations. Introduce `x hx`. Establish `hx2 : x ∈ q.map (algebraMap A R)` using `hx`. Rewrite using `[Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx2]`. Conclude with `K.zero_mem`.

Conclude with `Ideal.map_le_iff_le_comap.mpr hc`.
-/
theorem UpperTheory.V.J.flatHt :
    ∀ (A R : Type) [CommRing A] [CommRing R] [IsNoetherianRing A] [IsNoetherianRing R] (ι : A →+* R), ι.Flat → ∀ (q : Ideal A) (Q : Ideal R),
        Q.IsPrime → Q.comap ι = q → Q ∈ (q.map ι).minimalPrimes → Q.height = q.height := by
  intro A R _ _ _ _ ι hι q Q hQ hcomap hmin
  letI : Algebra A R := ι.toAlgebra
  haveI : Module.Flat A R := hι
  haveI : Algebra.HasGoingDown A R := Algebra.HasGoingDown.of_flat
  haveI : q.IsPrime := hcomap ▸ Ideal.comap_isPrime ι Q
  haveI : Q.LiesOver q := ⟨hcomap.symm⟩
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q Q]
  suffices h0 : (Q.map (Ideal.Quotient.mk (q.map (algebraMap A R)))).height = 0 by
    rw [h0, add_zero]
  have hJQ : q.map (algebraMap A R) ≤ Q := hmin.1.2
  have hker : RingHom.ker (Ideal.Quotient.mk (q.map (algebraMap A R))) ≤ Q := by
    rw [Ideal.mk_ker]
    exact hJQ
  haveI : (Q.map (Ideal.Quotient.mk (q.map (algebraMap A R)))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  rw [Ideal.height_eq_zero_iff]
  refine ⟨⟨inferInstance, bot_le⟩, ?_⟩
  rintro K ⟨hK, -⟩ hKQ
  have hle : K.comap (Ideal.Quotient.mk (q.map (algebraMap A R))) ≤ Q := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp (hKQ hx)
    have hd : y - x ∈ q.map (algebraMap A R) := Ideal.Quotient.eq.mp hxy
    have hx' : x = y - (y - x) := by ring
    rw [hx']
    exact Q.sub_mem hy (hJQ hd)
  have hc : Q ≤ K.comap (Ideal.Quotient.mk (q.map (algebraMap A R))) := by
    refine hmin.2 ⟨Ideal.comap_isPrime _ K, ?_⟩ hle
    intro x hx
    have hx2 : x ∈ q.map (algebraMap A R) := hx
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx2]
    exact K.zero_mem
  exact Ideal.map_le_iff_le_comap.mpr hc
