import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2

/- English proof (translation)
Establish `h` using `span_evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ`. Establish `h2 : ValC (Gr emb σ n) lam ≤ Submodule.span ℂ (Set.range fun i => evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (bVV K lam i))`. Rewrite using `[← h, Submodule.span_le]`. Introduce and unpack `_ ⟨F, rfl⟩`. Rewrite using `[← (bVV K lam).sum_repr F, map_sum]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smulₛₗ]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Use `haveI := FiniteDimensional.span_of_finite ℂ (Set.finite_range fun i => evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (bVV K lam i))`. Conclude with `Submodule.finiteDimensional_of_le h2`.
-/
theorem valC_finiteDimensional {E K ι : Type} [Field E] [Field K] [CharZero K] [Fintype ι] {n : ℕ}
    (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n) :
    FiniteDimensional ℂ (ValC (Gr emb σ n) lam) := by
  classical
  have h := span_evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ
  have h2 : ValC (Gr emb σ n) lam ≤
      Submodule.span ℂ (Set.range fun i => evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (bVV K lam i)) := by
    rw [← h, Submodule.span_le]
    rintro _ ⟨F, rfl⟩
    rw [← (bVV K lam).sum_repr F, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI := FiniteDimensional.span_of_finite ℂ
    (Set.finite_range fun i => evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (bVV K lam i))
  exact Submodule.finiteDimensional_of_le h2

/- English proof (translation)
Use `haveI := hS.fin_orb`. Use `haveI := valC_finiteDimensional emb σ lam`. Set `f : S.Fi emb σ lam →ₗ[ℂ] (S.Cl → ValC (Gr emb σ n) lam)` to `{ toFun := fun φ c => ⟨φ.1 c, (φ.2 c).1⟩ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Use `Module.Finite.of_injective f fun a b hab => ?_` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `c`. Conclude with `congrArg Subtype.val (congrFun hab c)`.
-/
theorem GStep.fi_finiteDimensional {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K]
    [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)
    (_hF : FOk emb σ) (hS : S.Ok) : FiniteDimensional ℂ (S.Fi emb σ lam) := by
  haveI := hS.fin_orb
  haveI := valC_finiteDimensional emb σ lam
  let f : S.Fi emb σ lam →ₗ[ℂ] (S.Cl → ValC (Gr emb σ n) lam) :=
    { toFun := fun φ c => ⟨φ.1 c, (φ.2 c).1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective f fun a b hab => ?_
  apply Subtype.ext
  funext c
  exact congrArg Subtype.val (congrFun hab c)

end GlobalTheory.Mem.Col2
