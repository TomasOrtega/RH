import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

/- English proof (translation)
Establish `hZX : (Z * X) i j = 0`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hik : lamW i < lamW k`. Rewrite using `[hX k j (fun e => h (e ▸ hik)), mul_zero]`.

Rewrite using `[hZ i k hik, zero_mul]`. Rewrite using `[add_mul, one_mul, Matrix.add_apply, hZX, add_zero]`.
-/
private theorem ent_eq {R : Type} [CommRing R] {X Z : M4 R} (hX : IsBlock X) (hZ : Z ∈ hAB R) (i j : Fin 4)
    (h : ¬ lamW i < lamW j) : ((1 + Z) * X) i j = X i j := by
  have hZX : (Z * X) i j = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hik : lamW i < lamW k
    · rw [hX k j (fun e => h (e ▸ hik)), mul_zero]
    · rw [hZ i k hik, zero_mul]
  rw [add_mul, one_mul, Matrix.add_apply, hZX, add_zero]

/- English proof (translation)
Introduce `R _ X Z hX hZ`. Establish `hZa : Z ∈ hAB R` using `hZ.1`. Establish `hZs : adj Z = -Z` using `hZ.2`. Establish `hZZ : Z * Z = 0` using `hAB_mul_hAB hZa hZa`. Establish `hlow : ∀ i j, lamW j < lamW i → ((1 + Z) * X) i j = 0`.

Introduce `i j hij`. Rewrite using `[ent_eq hX hZa i j (fun h => lt_asymm h hij)]`. Conclude with `hX i j hij.ne'`. Use `⟨?_, hlow, ?_, ?_⟩` and prove the remaining obligations. Introduce `ν Y hY`.

Establish `g` using `grp R`. Establish `h1 : (1 + -Z) * (1 + Z) = 1`. Rewrite using `[add_mul, one_mul, neg_mul, mul_add, mul_one, hZZ, add_zero]`. Normalize the expressions using the abelian group laws. Use `show adj ((1 + Z) * Y) * ((1 + Z) * Y) = ν • 1`.

Rewrite using `[g.1, g.2.2.1, g.2.2.2.2.1, hZs, mul_assoc, ← mul_assoc (1 + -Z), h1, one_mul]`. Conclude with `hY`. Use extensionality with `a b`. Apply the tactic sequence `exact ent_eq hX hZa _ _ (by fin_cases a <;> fin_cases b <;> decide)`. Establish `hT : ((1 + Z) * X).BlockTriangular lamW` using `fun _ _ h => hlow _ _ h`.

Establish `hTX : X.BlockTriangular lamW` using `fun _ _ h => hX _ _ h.ne'`. Rewrite using `[hT.charpoly, hTX.charpoly]`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `congr 1`. Use extensionality with `i j`.

Simplify using `only [Matrix.toSquareBlock_def, Matrix.of_apply]`. Conclude with `ent_eq hX hZa _ _ (by rw [i.2, j.2]; exact lt_irrefl a)`.
-/
theorem UpperTheory.V.Ws.Bl.twistPt :
    ∀ (R : Type) [CommRing R] (X Z : M4 R), IsBlock X → Z ∈ uM R → (∀ ν Y, IsGSp ν Y → IsGSp ν ((1 + Z) * Y)) ∧ (∀ i j, lamW j < lamW i → ((1 + Z) * X) i j = 0) ∧
          ((1 + Z) * X).submatrix ixB ixB = X.submatrix ixB ixB ∧ ((1 + Z) * X).charpoly = X.charpoly := by
  intro R _ X Z hX hZ
  have hZa : Z ∈ hAB R := hZ.1
  have hZs : adj Z = -Z := hZ.2
  have hZZ : Z * Z = 0 := hAB_mul_hAB hZa hZa
  have hlow : ∀ i j, lamW j < lamW i → ((1 + Z) * X) i j = 0 := by
    intro i j hij
    rw [ent_eq hX hZa i j (fun h => lt_asymm h hij)]
    exact hX i j hij.ne'
  refine ⟨?_, hlow, ?_, ?_⟩
  · intro ν Y hY
    have g := grp R
    have h1 : (1 + -Z) * (1 + Z) = 1 := by
      rw [add_mul, one_mul, neg_mul, mul_add, mul_one, hZZ, add_zero]
      abel
    show adj ((1 + Z) * Y) * ((1 + Z) * Y) = ν • 1
    rw [g.1, g.2.2.1, g.2.2.2.2.1, hZs, mul_assoc, ← mul_assoc (1 + -Z), h1, one_mul]
    exact hY
  · ext a b
    exact ent_eq hX hZa _ _ (by fin_cases a <;> fin_cases b <;> decide)
  · have hT : ((1 + Z) * X).BlockTriangular lamW := fun _ _ h => hlow _ _ h
    have hTX : X.BlockTriangular lamW := fun _ _ h => hX _ _ h.ne'
    rw [hT.charpoly, hTX.charpoly]
    refine Finset.prod_congr rfl fun a _ => ?_
    congr 1
    ext i j
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply]
    exact ent_eq hX hZa _ _ (by rw [i.2, j.2]; exact lt_irrefl a)
