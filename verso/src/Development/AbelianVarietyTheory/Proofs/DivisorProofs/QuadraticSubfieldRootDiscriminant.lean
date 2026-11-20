import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EigenvectorLieDegree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.AdelicDegreeTameRamification
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke Polynomial

namespace GlobalTheory

/- English proof (translation)
Establish `hirr : Irreducible (X ^ 2 - C (a : ℚ))` using `X_pow_sub_C_irreducible_of_prime Nat.prime_two (Formalism.HF.P.quad_not_sq_rat a hsf h1)`. Establish `hmon : (X ^ 2 - C (a : ℚ)).Monic` using `monic_X_pow_sub_C _ two_ne_zero`. Establish `hev : aeval x (X ^ 2 - C (a : ℚ)) = 0` using `by simp [hx]`. Establish `hmin : minpoly ℚ x = X ^ 2 - C (a : ℚ)` using `(minpoly.eq_of_irreducible_of_monic hirr hev hmon).symm`. Use `IntermediateField.adjoin.finrank (K := ℚ) (x := x) (.of_finite ℚ x)` as an intermediate fact.

Rewrite `this` using `[hmin, natDegree_X_pow_sub_C, hadj, IntermediateField.finrank_top']`. Conclude with `this`.
-/
theorem finrank_eq_two_of_adjoin_sqrt_eq_top (K : Type) [Field K] [NumberField K] (a : ℤ) (x : K)
    (hx : x ^ 2 = (a : K)) (hadj : IntermediateField.adjoin ℚ {x} = ⊤) (hsf : Squarefree a) (h1 : a ≠ 1) :
    Module.finrank ℚ K = 2 := by
  have hirr : Irreducible (X ^ 2 - C (a : ℚ)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (Formalism.HF.P.quad_not_sq_rat a hsf h1)
  have hmon : (X ^ 2 - C (a : ℚ)).Monic := monic_X_pow_sub_C _ two_ne_zero
  have hev : aeval x (X ^ 2 - C (a : ℚ)) = 0 := by simp [hx]
  have hmin : minpoly ℚ x = X ^ 2 - C (a : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirr hev hmon).symm
  have := IntermediateField.adjoin.finrank (K := ℚ) (x := x) (.of_finite ℚ x)
  rw [hmin, natDegree_X_pow_sub_C, hadj, IntermediateField.finrank_top'] at this
  exact this

/- English proof (translation)
Apply `IntermediateField.lift_injective` to reduce the goal to its premises. Conclude with `(IntermediateField.lift_adjoin_simple ℚ _ (IntermediateField.AdjoinSimple.gen ℚ y)).trans (IntermediateField.lift_top ℚ (IntermediateField.adjoin ℚ {y})).symm`.
-/
theorem adjoin_gen_eq_top_rat {E : Type} [Field E] [NumberField E] (y : E) :
    IntermediateField.adjoin ℚ {IntermediateField.AdjoinSimple.gen ℚ y} = ⊤ := by
  apply IntermediateField.lift_injective
  exact (IntermediateField.lift_adjoin_simple ℚ _ (IntermediateField.AdjoinSimple.gen ℚ y)).trans
    (IntermediateField.lift_top ℚ (IntermediateField.adjoin ℚ {y})).symm

/- English proof (translation)
Introduce `E _ _ _ H`. Establish `hd16` using `H.d_mod`. Establish `hb2 : ((H.rt : 𝓞 E) : E) ^ 2 = -(H.d : E)`. Use `congrArg (algebraMap (𝓞 E) E) H.rt_sq` as an intermediate fact. Simplify using `using this`.

Take `⟨x, hxdef, hadj⟩ : ∃ x : AdelicDegreeTameRamification.quadField H, (x : E) = (H.rt : E) ∧ IntermediateField.adjoin ℚ {x} = ⊤` from `⟨IntermediateField.AdjoinSimple.gen ℚ _, rfl, adjoin_gen_eq_top_rat _⟩`. Establish `hx : x ^ 2 = ((-(H.d : ℤ) : ℤ) : AdelicDegreeTameRamification.quadField H)`. Apply `Subtype.ext` to reduce the goal to its premises. Use `push_cast`. Rewrite using `[hxdef, hb2]`.

Establish `hint : IsIntegral ℤ x`. Apply `IsIntegral.of_pow (n := 2) (by norm_num)` to reduce the goal to its premises. Rewrite using `[hx, ← eq_intCast (algebraMap ℤ (AdelicDegreeTameRamification.quadField H))]`. Conclude with `isIntegral_algebraMap`. Establish `hsf : Squarefree (-(H.d : ℤ))`.

Rewrite using `[← Int.squarefree_natAbs, Int.natAbs_neg, Int.natAbs_natCast]`. Conclude with `H.d_prime.squarefree`. Take `⟨x', hx'⟩ : ∃ x' : 𝓞 (AdelicDegreeTameRamification.quadField H), (x' : AdelicDegreeTameRamification.quadField H) = x` from `⟨⟨x, hint⟩, rfl⟩`. Establish `hdiff` using `Formalism.MainNotions.UnusedSlot33.HK.different_quad (AdelicDegreeTameRamification.quadField H) (-(H.d : ℤ)) x hx hadj hsf (by omega) (by omega) x' hx'`. Establish `h2` using `finrank_eq_two_of_adjoin_sqrt_eq_top (AdelicDegreeTameRamification.quadField H) (-(H.d : ℤ)) x hx hadj hsf (by omega)`.

Establish `hD` using `Formalism.HF.P.quadDiscr_ne_one (AdelicDegreeTameRamification.quadField H) (-(H.d : ℤ)) x hx hadj hsf (by omega) (by omega)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[rootDiscr_def, h2, hD, Real.sqrt_eq_rpow]`. Simplify using the standard rewrite rules. Rewrite using `[hdiff, Ideal.map_span, Set.image_singleton]`.

Use `congr 2`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Use `show ((x' : AdelicDegreeTameRamification.quadField H) : E) = _`. Rewrite using `[hx', hxdef]`.
-/
theorem rootDiscr_and_different_quadField :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E),
      rootDiscr (AdelicDegreeTameRamification.quadField H) = √(H.d : ℝ) ∧
      (differentIdeal ℤ (𝓞 (AdelicDegreeTameRamification.quadField H))).map (algebraMap (𝓞 (AdelicDegreeTameRamification.quadField H)) (𝓞 E)) =
        Ideal.span {H.rt} := by
  intro E _ _ _ H
  have hd16 := H.d_mod
  have hb2 : ((H.rt : 𝓞 E) : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  obtain ⟨x, hxdef, hadj⟩ : ∃ x : AdelicDegreeTameRamification.quadField H, (x : E) = (H.rt : E) ∧
      IntermediateField.adjoin ℚ {x} = ⊤ :=
    ⟨IntermediateField.AdjoinSimple.gen ℚ _, rfl, adjoin_gen_eq_top_rat _⟩
  have hx : x ^ 2 = ((-(H.d : ℤ) : ℤ) : AdelicDegreeTameRamification.quadField H) := by
    apply Subtype.ext
    push_cast
    rw [hxdef, hb2]
  have hint : IsIntegral ℤ x := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [hx, ← eq_intCast (algebraMap ℤ (AdelicDegreeTameRamification.quadField H))]
    exact isIntegral_algebraMap
  have hsf : Squarefree (-(H.d : ℤ)) := by
    rw [← Int.squarefree_natAbs, Int.natAbs_neg, Int.natAbs_natCast]
    exact H.d_prime.squarefree
  obtain ⟨x', hx'⟩ : ∃ x' : 𝓞 (AdelicDegreeTameRamification.quadField H), (x' : AdelicDegreeTameRamification.quadField H) = x := ⟨⟨x, hint⟩, rfl⟩
  have hdiff := Formalism.MainNotions.UnusedSlot33.HK.different_quad (AdelicDegreeTameRamification.quadField H) (-(H.d : ℤ)) x hx hadj hsf
    (by omega) (by omega) x' hx'
  have h2 := finrank_eq_two_of_adjoin_sqrt_eq_top (AdelicDegreeTameRamification.quadField H) (-(H.d : ℤ)) x hx hadj hsf (by omega)
  have hD := Formalism.HF.P.quadDiscr_ne_one (AdelicDegreeTameRamification.quadField H) (-(H.d : ℤ)) x hx hadj hsf (by omega) (by omega)
  refine ⟨?_, ?_⟩
  · rw [rootDiscr_def, h2, hD, Real.sqrt_eq_rpow]
    simp
  · rw [hdiff, Ideal.map_span, Set.image_singleton]
    congr 2
    apply RingOfIntegers.coe_injective
    show ((x' : AdelicDegreeTameRamification.quadField H) : E) = _
    rw [hx', hxdef]

end GlobalTheory
