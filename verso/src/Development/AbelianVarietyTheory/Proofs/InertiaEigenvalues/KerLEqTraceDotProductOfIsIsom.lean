import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

/- English proof (translation)
Introduce `F E _ _ _ _ _ A ψ x r j hj y' y`. Establish `h2 : Module.finrank F E = 2` using `Unram.finrank_eq`. Use `haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ h2`. Use `haveI : Module.Finite E A.L := Module.Finite.equiv j.symm`. Use `haveI : Module.Free E A.L := Module.Free.of_equiv j.symm`.

Establish `hb : IsBaseChange A.K (IsScalarTower.toAlgHom F E A.L).toLinearMap` using `A.push.symm.out`. Use `haveI : Module.Free A.K A.L := Module.Free.of_equiv hb.equiv`. Use `haveI : Module.Finite A.K A.L := Module.Finite.equiv hb.equiv`. Rewrite using `[hj y' y]`. Unfold `Et.kerL Et.psiK`.

Use `congr 1`. Rewrite using `[← Algebra.smul_def, smul_mul_assoc, Algebra.trace_trace (R := F) (S := E), ← smul_eq_mul, ← LinearMap.map_smul, Algebra.trace_trace]`.
-/
theorem Et.kerL_eq_of_isIsom : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ y' y : A.L, A.kerL ψ x y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y)) := by
  intro F E _ _ _ _ _ A ψ x r j hj y' y
  have h2 : Module.finrank F E = 2 := Unram.finrank_eq
  haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ h2
  haveI : Module.Finite E A.L := Module.Finite.equiv j.symm
  haveI : Module.Free E A.L := Module.Free.of_equiv j.symm
  have hb : IsBaseChange A.K (IsScalarTower.toAlgHom F E A.L).toLinearMap := A.push.symm.out
  haveI : Module.Free A.K A.L := Module.Free.of_equiv hb.equiv
  haveI : Module.Finite A.K A.L := Module.Finite.equiv hb.equiv
  rw [hj y' y]
  unfold Et.kerL Et.psiK
  congr 1
  rw [← Algebra.smul_def, smul_mul_assoc, Algebra.trace_trace (R := F) (S := E), ← smul_eq_mul,
    ← LinearMap.map_smul, Algebra.trace_trace]
end GlobalTheory.JR
