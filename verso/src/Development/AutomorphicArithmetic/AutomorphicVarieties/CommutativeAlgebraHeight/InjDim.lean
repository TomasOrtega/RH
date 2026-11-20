import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

/- English proof (translation)
Introduce `A B _ _ _ _ _ d hA hB`. Assume the negation of the conclusion as `hni`. Choose the witnesses or unpack the hypotheses as in `⟨r, hr, hr0⟩ : ∃ r : A, algebraMap A B r = 0 ∧ r ≠ 0 := by`. Rewrite `hni` using `[injective_iff_map_eq_zero]`. Use `push_neg at hni`.

Conclude with `hni`. Establish `hrz : r ∈ nonZeroDivisors A` using `mem_nonZeroDivisors_of_ne_zero hr0`. Set `g : (A ⧸ Ideal.span {r}) →+* B` to `Ideal.Quotient.lift (Ideal.span {r}) (algebraMap A B) (by`. Introduce `a ha`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp ha`.

Rewrite using `[map_mul, hr, mul_zero])`. Use `letI : Algebra (A ⧸ Ideal.span {r}) B := g.toAlgebra`. Use `haveI : Algebra.IsIntegral (A ⧸ Ideal.span {r}) B := by`. Use `⟨fun b => ?_⟩` and prove the remaining obligations. Take `⟨p, hp, hpb⟩` from `Algebra.IsIntegral.isIntegral (R := A) b`.

Use `⟨p.map (Ideal.Quotient.mk _), hp.map _, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map, RingHom.algebraMap_toAlgebra, Ideal.Quotient.lift_comp_mk]`. Conclude with `hpb`. Establish `h1 : ringKrullDim B ≤ ringKrullDim (A ⧸ Ideal.span {r})` using `Order.krullDim_le_of_strictMono (fun P => (⟨Ideal.comap (algebraMap (A ⧸ Ideal.span {r}) B) P.asIdeal, inferInstance⟩ : PrimeSpectrum _)) (fun P Q h => Ideal.IsIntegral.comap_lt_comap h)`. Establish `h2` using `ringKrullDim_quotient_succ_le_of_nonZeroDivisor hrz`.

Rewrite `h2` using `[hA]`. Rewrite `h1` using `[hB]`. Establish `h3 : ((d : WithBot ℕ∞) + 1) ≤ d` using `le_trans (add_le_add_left h1 1) h2`. Normalize the coercions in `at h3`. Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.V.CA.inj_dim :
    ∀ (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] (d : ℕ), ringKrullDim A = d → ringKrullDim B = d → Function.Injective (algebraMap A B) := by
  intro A B _ _ _ _ _ d hA hB
  by_contra hni
  obtain ⟨r, hr, hr0⟩ : ∃ r : A, algebraMap A B r = 0 ∧ r ≠ 0 := by
    rw [injective_iff_map_eq_zero] at hni
    push_neg at hni
    exact hni
  have hrz : r ∈ nonZeroDivisors A := mem_nonZeroDivisors_of_ne_zero hr0
  let g : (A ⧸ Ideal.span {r}) →+* B := Ideal.Quotient.lift (Ideal.span {r}) (algebraMap A B) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hr, mul_zero])
  letI : Algebra (A ⧸ Ideal.span {r}) B := g.toAlgebra
  haveI : Algebra.IsIntegral (A ⧸ Ideal.span {r}) B := by
    refine ⟨fun b => ?_⟩
    obtain ⟨p, hp, hpb⟩ := Algebra.IsIntegral.isIntegral (R := A) b
    refine ⟨p.map (Ideal.Quotient.mk _), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, RingHom.algebraMap_toAlgebra, Ideal.Quotient.lift_comp_mk]
    exact hpb
  have h1 : ringKrullDim B ≤ ringKrullDim (A ⧸ Ideal.span {r}) :=
    Order.krullDim_le_of_strictMono
      (fun P => (⟨Ideal.comap (algebraMap (A ⧸ Ideal.span {r}) B) P.asIdeal, inferInstance⟩ :
        PrimeSpectrum _))
      (fun P Q h => Ideal.IsIntegral.comap_lt_comap h)
  have h2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hrz
  rw [hA] at h2
  rw [hB] at h1
  have h3 : ((d : WithBot ℕ∞) + 1) ≤ d := le_trans (add_le_add_left h1 1) h2
  norm_cast at h3
  omega
