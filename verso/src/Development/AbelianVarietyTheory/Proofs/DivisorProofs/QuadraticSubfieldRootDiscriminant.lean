import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EigenvectorLieDegree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.AdelicDegreeTameRamification
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke Polynomial

namespace GlobalTheory

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
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
Reduce the claim to the hypotheses of an applicable result. A detailed English derivation is pending.
-/
theorem adjoin_gen_eq_top_rat {E : Type} [Field E] [NumberField E] (y : E) :
    IntermediateField.adjoin ℚ {IntermediateField.AdjoinSimple.gen ℚ y} = ⊤ := by
  apply IntermediateField.lift_injective
  exact (IntermediateField.lift_adjoin_simple ℚ _ (IntermediateField.AdjoinSimple.gen ℚ y)).trans
    (IntermediateField.lift_top ℚ (IntermediateField.adjoin ℚ {y})).symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
