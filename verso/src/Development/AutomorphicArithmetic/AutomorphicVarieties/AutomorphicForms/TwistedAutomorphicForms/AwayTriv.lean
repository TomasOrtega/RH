import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.EqOneOfMemLev
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits

open NumberField IsDedekindDomain Neutral.B1

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.Af.Tw.awayTriv :
    UpperTheory.V.Af.Tw.AwayTriv := by
  intro F B _ _ _ _ _ _ N S hN hinf hS b hbS hbin
  classical
  have k1 : (b : AdeleRing (𝓞 F) F).1 * ((b⁻¹ : Ideles F) : AdeleRing (𝓞 F) F).1 = 1 :=
    congrArg Prod.fst (Units.mul_inv b)
  have k2 : ((b⁻¹ : Ideles F) : AdeleRing (𝓞 F) F).1 * (b : AdeleRing (𝓞 F) F).1 = 1 :=
    congrArg Prod.fst (Units.inv_mul b)
  have k3 : (b : AdeleRing (𝓞 F) F).2 * ((b⁻¹ : Ideles F) : AdeleRing (𝓞 F) F).2 = 1 :=
    congrArg Prod.snd (Units.mul_inv b)
  have k4 : ((b⁻¹ : Ideles F) : AdeleRing (𝓞 F) F).2 * (b : AdeleRing (𝓞 F) F).2 = 1 :=
    congrArg Prod.snd (Units.inv_mul b)
  let binf : Ideles F := ⟨((b : AdeleRing (𝓞 F) F).1, 1), (((b⁻¹ : Ideles F) : AdeleRing (𝓞 F) F).1, 1),
    Prod.ext k1 (mul_one 1), Prod.ext k2 (mul_one 1)⟩
  let bfin : Ideles F := ⟨(1, (b : AdeleRing (𝓞 F) F).2), (1, ((b⁻¹ : Ideles F) : AdeleRing (𝓞 F) F).2),
    Prod.ext (mul_one 1) k3, Prod.ext (mul_one 1) k4⟩
  have hb : b = binf * bfin := by
    apply Units.ext
    exact Prod.ext (mul_one _).symm (one_mul _).symm
  have hfin2 : (↑bfin : AdeleRing (𝓞 F) F).2 = (↑b : AdeleRing (𝓞 F) F).2 := rfl
  have h1 : N binf = 1 := hinf binf rfl
  have h2 : N bfin = 1 := by
    refine GlobalTheory.FrobDense.eq_one_of_local N hN bfin rfl ?_
    intro v
    by_cases hv : v ∈ S
    · have hone : Units.map (GlobalTheory.Mem.LocTriv.ev v) bfin = 1 := by
        apply Units.ext
        rw [Units.coe_map, Units.val_one]
        change (↑bfin : AdeleRing (𝓞 F) F).2 v = 1
        rw [hfin2]
        exact hbin v hv
      rw [hone, map_one, map_one]
    · apply hS v hv
      change Valued.v ((↑bfin : AdeleRing (𝓞 F) F).2 v) = 1
      rw [hfin2]
      exact hbS v hv
  rw [hb, map_mul, h1, h2, one_mul]
