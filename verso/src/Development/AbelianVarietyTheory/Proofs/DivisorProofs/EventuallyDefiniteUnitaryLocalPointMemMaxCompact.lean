import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.GoodInt

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem eventually_int (x : E) :
    ∀ᶠ w : Pl E in cofinite, algebraMap E (w.adicCompletion E) x ∈ w.adicCompletionIntegers E := by
  filter_upwards [(HeightOneSpectrum.Support.finite (𝓞 E) x).compl_mem_cofinite] with w hw
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h2 : Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
  rw [h2]
  exact not_lt.mp hw

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem mem_GLint {L : Type} [Field L] {n : ℕ} (O : Subring L) (g : GL (Fin n) L)
    (h1 : ∀ i j, g.1 i j ∈ O) (h2 : ∀ i j, g⁻¹.1 i j ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. A detailed English derivation is pending.
-/
theorem eventually_mem_KGL {n : ℕ} (g : GL (Fin n) E) : ∀ᶠ w : Pl E in cofinite,
    GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) g ∈ GlobalTheory.LFun.KGL w n := by
  have h : ∀ g : GL (Fin n) E, ∀ᶠ w : Pl E in cofinite, ∀ i j,
      algebraMap E (w.adicCompletion E) (g.val i j) ∈ w.adicCompletionIntegers E := fun g => by
    simp only [Filter.eventually_all]; exact fun i j => eventually_int _
  filter_upwards [h g, h g⁻¹] with w a b
  exact mem_GLint _ _ a (by rw [← map_inv]; exact b)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem locPt_mem_KL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ γ : UE E n,
    γ.1.val.charpoly.Separable → ∀ᶠ w in cofinite, locPt w γ ∈ KL n w := by
  intro E _ _ _ _ n γ _
  filter_upwards [eventually_mem_KGL (E := E) γ.1] with w hw
  unfold locPt toSub
  split_ifs with h
  · exact hw
  · exact one_mem _

end GlobalTheory.BCT.GoodInt
