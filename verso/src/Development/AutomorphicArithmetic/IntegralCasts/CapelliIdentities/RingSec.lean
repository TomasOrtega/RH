import Mathlib

/- English proof (translation)
Introduce `Ω C _ _ _ _ φ hφ`. Use `letI : Algebra Ω C := φ.toAlgebra`. Use `haveI : Algebra.FiniteType Ω C := hφ`. Take `⟨m, hm⟩` from `Ideal.exists_maximal C`. Use `letI : Field (C ⧸ m) := Ideal.Quotient.field m`.

Use `haveI : Module.Finite Ω (C ⧸ m) := finite_of_finite_type_of_isJacobsonRing Ω (C ⧸ m)`. Set `f : (C ⧸ m) →ₐ[Ω] Ω` to `IsAlgClosed.lift`. Use `⟨(f.comp (Ideal.Quotient.mkₐ Ω m)).toRingHom, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Conclude with `(f.comp (Ideal.Quotient.mkₐ Ω m)).commutes x`.
-/
theorem UpperTheory.Reformulated.B.Qh66.ring_sec :
    ∀ (Ω C : Type) [inst : Field Ω] [IsAlgClosed Ω]
    [inst_2 : CommRing C] [Nontrivial C] (φ : Ω →+* C), φ.FiniteType → ∃ (ρ : C →+* Ω), ρ.comp φ = RingHom.id Ω := by
  intro Ω C _ _ _ _ φ hφ
  letI : Algebra Ω C := φ.toAlgebra
  haveI : Algebra.FiniteType Ω C := hφ
  obtain ⟨m, hm⟩ := Ideal.exists_maximal C
  letI : Field (C ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite Ω (C ⧸ m) := finite_of_finite_type_of_isJacobsonRing Ω (C ⧸ m)
  let f : (C ⧸ m) →ₐ[Ω] Ω := IsAlgClosed.lift
  refine ⟨(f.comp (Ideal.Quotient.mkₐ Ω m)).toRingHom, ?_⟩
  ext x
  exact (f.comp (Ideal.Quotient.mkₐ Ω m)).commutes x
