import Formalism.PadicSubsetSums.CentralIdempotents.PrimitiveRootFifteenSubOneUnit

namespace Formalism.IrreducibleCountingLemmas.Z

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem circle_pow_surjective {n : ℤ} (hn : n ≠ 0) :
    Function.Surjective (fun a : Circle => a ^ n) := by
  intro z
  obtain ⟨θ, rfl⟩ := Circle.exp_surjective z
  refine ⟨Circle.exp (θ / n), ?_⟩
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  show Circle.exp (θ / n) ^ n = Circle.exp θ
  rw [← Circle.exp_zsmul, zsmul_eq_mul, mul_div_cancel₀ _ hn']

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem circle_character_extends : CircleCharExtends := by
  intro A _ H χ
  have : DivisibleBy (Additive Circle) ℤ :=
    divisibleByOfSMulRightSurj (Additive Circle) ℤ fun {n} hn a => by
      obtain ⟨b, hb⟩ := circle_pow_surjective hn a.toMul
      exact ⟨Additive.ofMul b, congrArg Additive.ofMul hb⟩
  obtain ⟨ψ, hψ⟩ := (Module.Baer.of_divisible (Additive Circle)).extension_property_addMonoidHom
    (MonoidHom.toAdditive H.subtype) (fun a b hab => by
      have : (a.toMul : A) = (b.toMul : A) := congrArg Additive.toMul hab
      exact congrArg Additive.ofMul (Subtype.ext this))
    (MonoidHom.toAdditive χ)
  refine ⟨MonoidHom.toAdditive.symm ψ, fun h => ?_⟩
  have := DFunLike.congr_fun hψ (Additive.ofMul h)
  exact congrArg Additive.toMul this

end Formalism.IrreducibleCountingLemmas.Z
