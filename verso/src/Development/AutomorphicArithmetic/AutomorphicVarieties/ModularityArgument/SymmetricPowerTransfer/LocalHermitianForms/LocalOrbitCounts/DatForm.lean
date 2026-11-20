import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatLam

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
private theorem two_ne {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ : K} (L : IsLoc O Δ) : (2 : K) ≠ 0 := by
  have h := (L.two).map (algebraMap O K)
  rw [map_ofNat] at h
  exact h.ne_zero

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Both sides reduce to the same expression. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Apply the first step, then apply the next step to every resulting obligation. Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Z.Sym.Loc.datForm : UpperTheory.V.Z.Sym.Loc.DatForm := by
  intro O K _ _ _ _ _ Δ τ hL c lam hn z hz m hD
  have h2 : (2 : K) ≠ 0 := two_ne hL
  have h1 := datLam K Δ τ c hD.reg hD.c_ne lam hn z hz
  have hs1 : sigL (1 : EL Δ τ) = 1 := by
    simp [sigL]
    rfl
  have hdd := h1.m_sig
  rw [hs1, one_mul] at hdd
  have hsm := hD.m_sig
  rw [mul_assoc, ← hdd, mul_one] at hsm
  have hst := hD.m_star
  rw [hsm] at hst
  have him : m.im = 0 := by
    have e := congrArg QuadraticAlgebra.im hst
    simp only [QuadraticAlgebra.im_star] at e
    have e2 : (2 : K) • m.im = 0 := by
      rw [two_smul]
      linear_combination -e
    exact (smul_eq_zero.mp e2).resolve_left h2
  have hre : m.re.im = 0 := by
    have e := congrArg (fun x : EL Δ τ => x.re.im) hsm
    simp only [sigL, QuadraticAlgebra.im_star] at e
    have e2 : (2 : K) * m.re.im = 0 := by
      linear_combination -e
    exact (mul_eq_zero.mp e2).resolve_left h2
  have ht : m.re.re ≠ 0 := by
    intro h0
    apply hD.m_unit.ne_zero
    ext <;> simp [h0, hre, him]
  refine ⟨Units.mk0 m.re.re ht, ?_⟩
  ext <;> simp [hre, him]
