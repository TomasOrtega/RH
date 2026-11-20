import Mathlib
import Formalism.PeriodIntegrals.EmbTraceSum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EmbeddingTraceSum.Imports

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem sumEqTrace_holds : PI.EmbTraceSum := by
  intro E _ _ K φ₀ S _ emb hinj hext hcard y
  let _ : Algebra K ℂ := (φ₀.comp (algebraMap K E)).toAlgebra
  have hcomm : ∀ (s : S) (a : K), emb s (algebraMap K E a) = algebraMap K ℂ a := fun s a => hext s a
  let f : S → (E →ₐ[K] ℂ) := fun s => { emb s with commutes' := hcomm s }
  have hf : Function.Injective f := by
    intro s t hst
    apply hinj
    ext x
    exact AlgHom.congr_fun hst x
  have : FiniteDimensional K E := FiniteDimensional.right ℚ K E
  have hcard' : Fintype.card S = Fintype.card (E →ₐ[K] ℂ) := by
    rw [hcard, AlgHom.card]
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hcard'⟩
  have htr := trace_eq_sum_embeddings (K := K) (L := E) (E := ℂ) (x := y)
  calc ∑ s, emb s y = ∑ s, f s y := rfl
    _ = ∑ σ : E →ₐ[K] ℂ, σ y := Fintype.sum_bijective f hbij _ _ (fun _ => rfl)
    _ = algebraMap K ℂ (Algebra.trace K E y) := htr.symm
    _ = φ₀ ((Algebra.trace K E y : K) : E) := rfl
