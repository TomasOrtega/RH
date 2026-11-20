import Development.EtaleCohomology.DivisorCycles.OpenCoset

open Matrix
namespace LateralTheory.DivDb.UnipotentPartTrivial
open LateralTheory.DivDb

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.
-/
theorem pow_vanish {C : Type} [Field C] {N : ℕ} (E : Mat C N) (h : E * E = 0) (k : ℕ) (hk : 2 ≤ k) :
    E ^ k = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add, sq, h, zero_mul]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem series_eq {C : Type} [Field C] {N : ℕ} (E : Mat C N) (h : E * E = 0) (p : Fin N × Fin N) :
    PowerSeries.mk (fun k => ((k.factorial : C)⁻¹ • E ^ k) p.1 p.2)
      = ((Polynomial.C ((1 : Mat C N) p.1 p.2) + Polynomial.X * Polynomial.C (E p.1 p.2) : Polynomial C) :
          PowerSeries C) := by
  ext k
  rw [PowerSeries.coeff_mk, Polynomial.coeff_coe]
  rcases k with _ | _ | k
  · simp
  · simp
  · rw [pow_vanish E h _ (by omega)]
    simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Rewrite the indicated hypotheses using the stated equalities. Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem Unip_of (h : ExpVan) : Unip := by
  intro C _ _ N S E hE hEE f hf
  have h0 := h C N S E hE f hf
  let g : Fin N × Fin N → Polynomial C := fun p =>
    Polynomial.C ((1 : Mat C N) p.1 p.2) + Polynomial.X * Polynomial.C (E p.1 p.2)
  have h1 : MvPolynomial.aeval g f = 0 := by
    apply Polynomial.coe_injective
    rw [Polynomial.coe_zero]
    have hc := congrArg (fun φ => φ f)
      (MvPolynomial.comp_aeval (R := C) g (Polynomial.coeToPowerSeries.algHom C))
    simp only [AlgHom.comp_apply] at hc
    simp only [Polynomial.coeToPowerSeries.algHom_apply, PowerSeries.map_id, Algebra.algebraMap_self] at hc
    simp only [id] at hc
    have hs : (fun p : Fin N × Fin N => PowerSeries.mk (fun k => ((k.factorial : C)⁻¹ • E ^ k) p.1 p.2))
        = fun i => ((g i : Polynomial C) : PowerSeries C) := funext (series_eq E hEE)
    rw [hs] at h0
    exact hc.trans h0
  have h2 := congrArg (fun q => Polynomial.aeval (1 : C) q) h1
  simp only [map_zero] at h2
  have hc := congrArg (fun φ => φ f) (MvPolynomial.comp_aeval (R := C) g (Polynomial.aeval (1 : C)))
  simp only [AlgHom.comp_apply] at hc
  rw [hc] at h2
  have h3 : (fun p : Fin N × Fin N => Polynomial.aeval (1 : C) (g p)) = fun p => (1 + E) p.1 p.2 := by
    funext p; simp [g]
  rw [h3] at h2
  unfold ev
  exact h2

end LateralTheory.DivDb.UnipotentPartTrivial
