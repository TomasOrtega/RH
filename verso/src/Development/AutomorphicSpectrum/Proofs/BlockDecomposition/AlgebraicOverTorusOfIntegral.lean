import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace GlobalTheory.CompanionTheory.GeoTorus

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem isAlgebraic_unit_inv {K R : Type} [Field K] [CommRing R] [IsDomain R] [Algebra K R]
    (A : Subalgebra K R) (u : Rˣ) (hu : (u : R) ∈ A) : IsAlgebraic A ((u⁻¹ : Rˣ) : R) := by
  refine ⟨Polynomial.C (⟨u, hu⟩ : A) * Polynomial.X - 1, ?_, ?_⟩
  · intro h
    have h1 := congrArg (fun p => Polynomial.coeff p 0) h
    simp at h1
  · simp [Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_mul]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts.
-/
theorem isAlgebraic_unit_zpow {K R : Type} [Field K] [CommRing R] [IsDomain R] [Algebra K R]
    (A : Subalgebra K R) (u : Rˣ) (hu : (u : R) ∈ A) (m : ℤ) : IsAlgebraic A ((u ^ m : Rˣ) : R) := by
  obtain ⟨n, rfl | rfl⟩ := m.eq_nat_or_neg
  · have h : IsAlgebraic A (u : R) := isAlgebraic_algebraMap (⟨u, hu⟩ : A)
    simpa using h.pow n
  · simpa using (isAlgebraic_unit_inv A u hu).pow n

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Treat this case separately. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isAlgebraic_tpow {K R : Type} [Field K] [CommRing R] [IsDomain R] [Algebra K R] {d : ℕ}
    (t : Fin d → Rˣ) (m : Fin d → ℤ) :
    IsAlgebraic (Algebra.adjoin K (Set.range fun k => (t k : R))) (tpow t m) := by
  set A := Algebra.adjoin K (Set.range fun k => (t k : R))
  have hmem : ∀ k, (t k : R) ∈ A := fun k => Algebra.subset_adjoin ⟨k, rfl⟩
  have key : ∀ s : Finset (Fin d), IsAlgebraic A (((∏ k ∈ s, t k ^ m k : Rˣ)) : R) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (isAlgebraic_one : IsAlgebraic A (1 : R))
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Units.val_mul]
      exact (isAlgebraic_unit_zpow A (t a) (hmem a) (m a)).mul ih
  exact key Finset.univ

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isAlgebraic_of_integral_torusS : ∀ {K R : Type} [Field K] [CommRing R] [IsDomain R] [Algebra K R] {d : ℕ} (t : Fin d → Rˣ), (∀ r : R, IsIntegral (torusS K t Finset.univ) r) → Algebra.IsAlgebraic (Algebra.adjoin K (Set.range fun k => (t k : R))) R := by
  intro K R _ _ _ _ d t hint
  set A := Algebra.adjoin K (Set.range fun k => (t k : R)) with hA
  let S : Subalgebra A R := Subalgebra.algebraicClosure A R
  have hle : ∀ b : torusS K t Finset.univ, (b : R) ∈ S := by
    rintro ⟨b, hb⟩
    have : torusS K t Finset.univ ≤ S.restrictScalars K := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨m, -, rfl⟩
      exact (Subalgebra.mem_algebraicClosure A R).2 (isAlgebraic_tpow t m)
    exact this hb
  let φ : torusS K t Finset.univ →+* S :=
    { toFun := fun b => ⟨b, hle b⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  refine ⟨fun r => ?_⟩
  obtain ⟨p, hm, hp⟩ := hint r
  have hS : IsIntegral S r := by
    refine ⟨p.map φ, hm.map φ, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hp
  exact hS.isAlgebraic.restrictScalars A

end GlobalTheory.CompanionTheory.GeoTorus
