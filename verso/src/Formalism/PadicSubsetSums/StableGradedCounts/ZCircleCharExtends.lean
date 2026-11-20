import Formalism.PadicSubsetSums.CentralIdempotents.PrimitiveRootFifteenSubOneUnit

namespace Formalism.IrreducibleCountingLemmas.Z

/- English proof (translation)
Introduce `z`. Take `⟨θ, rfl⟩` from `Circle.exp_surjective z`. Use `⟨Circle.exp (θ / n), ?_⟩` and prove the remaining obligations. Establish `hn' : (n : ℝ) ≠ 0` using `by exact_mod_cast hn`. Use `show Circle.exp (θ / n) ^ n = Circle.exp θ`.

Rewrite using `[← Circle.exp_zsmul, zsmul_eq_mul, mul_div_cancel₀ _ hn']`.
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
Introduce `A _ H χ`. Establish `: DivisibleBy (Additive Circle) ℤ` using `divisibleByOfSMulRightSurj (Additive Circle) ℤ fun {n} hn a => by`. Take `⟨b, hb⟩` from `circle_pow_surjective hn a.toMul`. Conclude with `⟨Additive.ofMul b, congrArg Additive.ofMul hb⟩`. Take `⟨ψ, hψ⟩` from `(Module.Baer.of_divisible (Additive Circle)).extension_property_addMonoidHom (MonoidHom.toAdditive H.subtype) (fun a b hab => by`.

Establish `: (a.toMul : A) = (b.toMul : A)` using `congrArg Additive.toMul hab`. Conclude with `congrArg Additive.ofMul (Subtype.ext this))`. Use the proof step `(MonoidHom.toAdditive χ)`. Use `⟨MonoidHom.toAdditive.symm ψ, fun h => ?_⟩` and prove the remaining obligations. Use `DFunLike.congr_fun hψ (Additive.ofMul h)` as an intermediate fact.

Conclude with `congrArg Additive.toMul this`.
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
