import Mathlib
import Formalism.PeriodIntegrals.PinHostLoc

noncomputable section

open IsDedekindDomain NumberField ValuativeRel WithZero

namespace PI.PinHostLoc.UnitaryGroupMassFormula

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem resChar_eq {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    {n : ℕ} (hn : n.Prime) (hp : ((n : ℕ) : 𝓞 F) ∈ p.asIdeal) :
    Formalism.MainNotions.S.Loc.resChar p = n := by
  have : Nontrivial (𝓞 F ⧸ p.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr p.isPrime.ne_top
  have h0 : ((n : ℕ) : 𝓞 F ⧸ p.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk p.asIdeal) n]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hp
  show ringChar (𝓞 F ⧸ p.asIdeal) = n
  exact CharP.ringChar_of_prime_eq_zero (R := 𝓞 F ⧸ p.asIdeal) hn h0

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem le_exp_neg_one_of_lt_one {a : ℤᵐ⁰} (h : a < 1) : a ≤ exp (-1) := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact zero_le
  · rw [← WithZero.exp_log ha] at h ⊢
    have h' : WithZero.exp (WithZero.log a) < WithZero.exp (0 : ℤ) := by
      rwa [WithZero.exp_zero]
    rw [WithZero.exp_lt_exp] at h'
    rw [WithZero.exp_le_exp]
    omega

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : Formalism.MainNotions.S.Loc.LocAt F E sig p)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem vF (x y : F) :
    valuation A.Fp (A.ιF x) ≤ valuation A.Fp (A.ιF y) ↔ p.valuation F x ≤ p.valuation F y := ((ValuativeRel.valuation A.Fp).vle_iff_le).symm.trans (A.val x y)

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem vF_eq (x y : F) :
    valuation A.Fp (A.ιF x) = valuation A.Fp (A.ιF y) ↔ p.valuation F x = p.valuation F y := by
  rw [le_antisymm_iff, le_antisymm_iff, vF A, vF A]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_val (a : A.Fp) (ha : a ≠ 0) :
    ∃ x : F, valuation A.Fp (A.ιF x) = valuation A.Fp a := by
  have := A.lf
  have hv : ValuativeRel.valuation A.Fp a ≠ 0 := (ValuativeRel.valuation A.Fp).ne_zero_iff.mpr ha
  obtain ⟨x, hx⟩ := A.dense.mem_nhds ((ValuativeRel.valuation A.Fp).locally_const hv)
  exact ⟨x, hx⟩

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem natVal (n : ℕ) : p.valuation F ((n : ℕ) : F) = p.intValuation ((n : ℕ) : 𝓞 F) := by
  have h := p.valuation_of_algebraMap (K := F) ((n : ℕ) : 𝓞 F)
  exact_mod_cast h

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem vF_lt (x y : F) :
    valuation A.Fp (A.ιF x) < valuation A.Fp (A.ιF y) ↔ p.valuation F x < p.valuation F y := by
  rw [← not_le, ← not_le, vF A]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Put the expressions in a common number system so they can be compared. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem irr {g : ℕ} (hg0 : g ≠ 0) (hin : ((g : ℕ) : 𝓞 F) ∈ p.asIdeal)
    (hnot : ((g : ℕ) : 𝓞 F) ∉ p.asIdeal ^ 2) : Irreducible ((g : ℕ) : 𝒪[A.Fp]) := by
  have hne : ((g : ℕ) : 𝓞 F) ≠ 0 := fun h => hg0 (by
    have h' := congrArg (algebraMap (𝓞 F) F) h
    rw [map_natCast, map_zero] at h'
    exact_mod_cast h')
  have hge : WithZero.exp (-1) ≤ p.valuation F ((g : ℕ) : F) := by
    rw [natVal]
    have h2 : ¬ p.intValuation ((g : ℕ) : 𝓞 F) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := fun h =>
      hnot ((p.intValuation_le_pow_iff_mem _ 2).mp h)
    have hz : p.intValuation ((g : ℕ) : 𝓞 F) ≠ 0 := p.intValuation_ne_zero _ hne
    rw [← WithZero.exp_log hz] at h2 ⊢
    rw [WithZero.exp_le_exp] at h2 ⊢
    omega
  have hlt : ValuativeRel.valuation A.Fp (A.ιF ((g : ℕ) : F)) < 1 := by
    have h := (vF_lt A ((g : ℕ) : F) 1).mpr (by
      rw [map_one, natVal]
      exact (p.intValuation_lt_one_iff_mem _).mpr hin)
    simp only [map_one] at h
    exact h
  have hcoe : (((g : ℕ) : 𝒪[A.Fp]) : A.Fp) = A.ιF ((g : ℕ) : F) := by simp
  have hgne : A.ιF ((g : ℕ) : F) ≠ 0 := (map_ne_zero A.ιF).mpr (Nat.cast_ne_zero.mpr hg0)
  refine ⟨?_, ?_⟩
  · rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one, hcoe]
    exact hlt
  · intro a b hab
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨ha, hb⟩ := hcon
    rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one] at ha hb
    have hab' : (a : A.Fp) * (b : A.Fp) = A.ιF ((g : ℕ) : F) := by
      rw [← hcoe, hab]
      norm_cast
    have hab0 : (a : A.Fp) * (b : A.Fp) ≠ 0 := by
      rw [hab']
      exact hgne
    have ha0 : (a : A.Fp) ≠ 0 := left_ne_zero_of_mul hab0
    have hva : ValuativeRel.valuation A.Fp (a : A.Fp) ≠ 0 :=
      (ValuativeRel.valuation A.Fp).ne_zero_iff.mpr ha0
    obtain ⟨x, hx⟩ := exists_val A (a : A.Fp) ha0
    have hxlt : p.valuation F x < 1 := by
      have h := (vF_lt A x 1).mp (by
        simp only [map_one]
        rw [hx]
        exact ha)
      simp only [map_one] at h
      exact h
    have hle : ValuativeRel.valuation A.Fp (a : A.Fp) ≤
        ValuativeRel.valuation A.Fp (A.ιF ((g : ℕ) : F)) := by
      rw [← hx, vF A]
      exact (le_exp_neg_one_of_lt_one hxlt).trans hge
    rw [← hab', map_mul] at hle
    have h1 := mul_le_mul' (le_refl (ValuativeRel.valuation A.Fp (a : A.Fp))⁻¹) hle
    rw [← mul_assoc, inv_mul_cancel₀ hva, one_mul] at h1
    exact absurd hb (not_lt.mpr h1)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem unit {n : ℕ} (hn : ((n : ℕ) : 𝓞 F) ∉ p.asIdeal) :
    ∃ u : 𝒪[A.Fp], IsUnit u ∧ (u : A.Fp) = A.ιF ((n : ℕ) : F) := by
  have hw : p.valuation F ((n : ℕ) : F) = 1 := by
    rw [natVal]
    exact HeightOneSpectrum.intValuation_eq_one_iff.mpr hn
  have hv : ValuativeRel.valuation A.Fp (A.ιF ((n : ℕ) : F)) = 1 := by
    have h := (vF_eq A ((n : ℕ) : F) 1).mpr (by rw [hw, map_one])
    simp only [map_one] at h
    exact h
  have hmem : A.ιF ((n : ℕ) : F) ∈ 𝒪[A.Fp] := by
    rw [Valuation.mem_integer_iff, hv]
  refine ⟨⟨A.ιF ((n : ℕ) : F), hmem⟩, ?_, rfl⟩
  by_contra hu
  rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one] at hu
  exact absurd hv (ne_of_lt hu)

end

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem target : PI.PinHostLoc.Target := by
  unfold PI.PinHostLoc.Target
  intro F E _ _ _ _ _ sig p A g hg hne i hin hnot
  have hres : Formalism.MainNotions.S.Loc.resChar p = g i := resChar_eq p (hg i) hin
  refine ⟨?_, ?_⟩
  · rw [hres]
    exact irr A (hg i).ne_zero hin hnot
  · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · have h1 : ((g 1 : ℕ) : 𝓞 F) ∉ p.asIdeal := fun h1 =>
        hne ((resChar_eq p (hg 1) h1).symm.trans hres).symm
      obtain ⟨u, hu, hu'⟩ := unit A h1
      refine ⟨u, hu, ?_⟩
      rw [hu', mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (hg 0).ne_zero)]
    · have h0 : ((g 0 : ℕ) : 𝓞 F) ∉ p.asIdeal := fun h0 =>
        hne ((resChar_eq p (hg 0) h0).symm.trans hres)
      obtain ⟨u, hu, hu'⟩ := unit A h0
      refine ⟨u, hu, ?_⟩
      rw [hu', mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr (hg 1).ne_zero)]

end PI.PinHostLoc.UnitaryGroupMassFormula
