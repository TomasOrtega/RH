import Formalism.SharpRestriction.LevelLetterCocycles.TeichOnto

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Module IsLocalRing Formalism.MainNotions.N.Ln03

/- English proof (translation)
Substitute using the available equality. Both sides reduce to the same expression.
-/
theorem zpEquiv_apply_symm {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (x : ℤ_[q]) :
    zpEquiv h (zpEquiv h.symm x) = x := by
  subst h
  rfl

/- English proof (translation)
Substitute using the available equality. Both sides reduce to the same expression.
-/
theorem zpEquiv_valuation {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (x : ℤ_[q]) :
    (zpEquiv h.symm x).valuation = x.valuation := by
  subst h
  rfl

section Loc

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Chain the equalities or inequalities of the calculation.

A detailed English derivation is pending.
-/
theorem norm_chiQ_le (P : LocPrime l) (g : GQ l) : ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l])‖ ≤ 1 := by
  obtain ⟨a, ha, -⟩ := P.χQ_cyc g 0 1 (by simp)
  have h1 : ‖((a : ℕ) : ℚ_[l])‖ ≤ 1 := by
    rw [← PadicInt.coe_natCast]
    exact PadicInt.norm_le_one _
  have ha' : ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - (a : ℚ_[l])‖ ≤ 1 := by simpa using ha
  calc ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l])‖
      = ‖(((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - (a : ℚ_[l])) + (a : ℚ_[l])‖ := by rw [sub_add_cancel]
    _ ≤ max ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - (a : ℚ_[l])‖ ‖(a : ℚ_[l])‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := max_le ha' h1

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem norm_chiQ (P : LocPrime l) (g : GQ l) : ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l])‖ = 1 := by
  have h1 := norm_chiQ_le P g
  have h2 := norm_chiQ_le P g⁻¹
  have hm : ((P.χQ g⁻¹ : ℚ_[l]ˣ) : ℚ_[l]) * ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hn : ‖((P.χQ g⁻¹ : ℚ_[l]ˣ) : ℚ_[l])‖ * ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l])‖ = 1 := by
    rw [← norm_mul, hm, norm_one]
  refine le_antisymm h1 ?_
  nlinarith [norm_nonneg ((P.χQ g⁻¹ : ℚ_[l]ˣ) : ℚ_[l]), norm_nonneg ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l])]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem v_algebraMap_zp (P : LocPrime l) (LL : FinExt l) (y : ℤ_[l]) (hy : y ≠ 0) :
    P.v LL (algebraMap ℤ_[l] ↥LL.1 y) = ((y.valuation : ℕ) : WithTop ℚ) := by
  have hint : ∀ z : ℤ_[l], 0 ≤ P.v LL (algebraMap ℤ_[l] ↥LL.1 z) := fun z =>
    (P.v_O LL _).2 (Subalgebra.algebraMap_mem (OL LL) z)
  have spec := PadicInt.unitCoeff_spec hy
  set w := PadicInt.unitCoeff hy
  have hw : P.v LL (algebraMap ℤ_[l] ↥LL.1 (w : ℤ_[l])) = 0 := by
    have h1 := hint (w : ℤ_[l])
    have h2 := hint ((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l])
    have hsum : P.v LL (algebraMap ℤ_[l] ↥LL.1 (w : ℤ_[l])) +
        P.v LL (algebraMap ℤ_[l] ↥LL.1 ((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l])) = 0 := by
      rw [← AddValuation.map_mul, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one,
        AddValuation.map_one]
    exact le_antisymm ((le_add_of_nonneg_right h2).trans hsum.le) h1
  conv_lhs => rw [spec]
  rw [map_mul, map_pow, map_natCast, AddValuation.map_mul, AddValuation.map_pow, hw, P.v_l, zero_add,
    nsmul_one]

end Loc

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem uTieRec_holds (D : D7) (HW : HWOf D.loc) : UTieRec D HW := by
  intro l _ K LL h _
  obtain ⟨g0, hg0⟩ := ((HW l).W K 1 LL h.2.2).resΓ_onto ((HW l).W K 1 LL h.2.2).gam
  have hres := ((HW l).W K 1 LL h.2.2).χΓ_res g0
  rw [hg0] at hres
  have hn : ‖((((D.loc l).PD K).χ g0 : ℚ_[l]ˣ) : ℚ_[l])‖ = 1 := by
    rw [(D.loc l).PD_χ]
    exact norm_chiQ (D.loc l) _
  set u : ℤ_[l]ˣ := PadicInt.mkUnits hn with hu
  have hu' : ((u : ℤ_[l]) : ℚ_[l]) = ((((D.loc l).PD K).χ g0 : ℚ_[l]ˣ) : ℚ_[l]) := PadicInt.mkUnits_eq hn
  have hχ : ((((HW l).W K 1 LL h.2.2).χΓ ((HW l).W K 1 LL h.2.2).gam : ↥(OL LL)) : ↥LL.1) =
      algebraMap ℤ_[l] ↥LL.1 (u : ℤ_[l]) := by
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1, PadicInt.algebraMap_apply, hu']
    exact hres
  refine ⟨Units.map (zpEquiv ((D.loc l).PD_p K).symm).toRingHom.toMonoidHom u, ?_, ?_⟩
  · show (zpEquiv ((D.loc l).PD_p K).symm (u : ℤ_[l]) - 1).valuation = 1
    rw [← map_one (zpEquiv ((D.loc l).PD_p K).symm), ← map_sub, zpEquiv_valuation ((D.loc l).PD_p K)]
    have hg := ((HW l).W K 1 LL h.2.2).gam_gen
    rw [(HW l).W_s K 1 LL h.2.2] at hg
    change (D.loc l).v LL ((((HW l).W K 1 LL h.2.2).χΓ ((HW l).W K 1 LL h.2.2).gam : ↥(OL LL)) - 1) =
      ((1 : ℕ) : WithTop ℚ) at hg
    rw [hχ, ← map_one (algebraMap ℤ_[l] ↥LL.1), ← map_sub] at hg
    have hne : (u : ℤ_[l]) - 1 ≠ 0 := by
      intro h0
      rw [h0, map_zero, AddValuation.map_zero] at hg
      exact WithTop.top_ne_coe hg
    rw [v_algebraMap_zp (D.loc l) LL _ hne] at hg
    exact_mod_cast hg
  · apply Subtype.ext
    show ((algebraMap ℤ_[l] ↥(OL LL) (zpEquiv ((D.loc l).PD_p K)
      (zpEquiv ((D.loc l).PD_p K).symm (u : ℤ_[l])))) : ↥LL.1) = _
    rw [zpEquiv_apply_symm, hχ]
    rfl

end Formalism.MainNotions.N.Ln03.Pf
