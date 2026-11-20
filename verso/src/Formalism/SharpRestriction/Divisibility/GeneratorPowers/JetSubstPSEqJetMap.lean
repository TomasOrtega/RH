import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ESecToUnit
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF

open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet

variable {S : Type} [CommRing S] {κ κ' κ'' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
  [Fintype κ''] [DecidableEq κ'']

/- English proof (translation)
Unfold `psJet`. Rewrite using `[psTrunc_eq]`. Conclude with `mk_trunc_coe m P`.
-/
theorem psJet_coe (m : ℕ) (P : MvPolynomial κ S) : psJet m (P : MvPowerSeries κ S) = Ideal.Quotient.mk _ P := by
  unfold psJet
  rw [psTrunc_eq]
  exact mk_trunc_coe m P

/- English proof (translation)
Unfold `jetSubstPS`. Rewrite using `[jetMap_mk, MvPolynomial.aeval_X, Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB.cc_psTrunc', hP i, map_zero, sub_zero]`. Both sides reduce to the same expression.
-/
theorem jetSubstPS_X (m : ℕ) (P : κ → MvPowerSeries κ' S) (hP : ∀ i, MvPowerSeries.constantCoeff (P i) = 0)
    (i : κ) : jetSubstPS (m := m) P (Ideal.Quotient.mk _ (X i)) = psJet m (P i) := by
  unfold jetSubstPS
  rw [jetMap_mk, MvPolynomial.aeval_X, Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB.cc_psTrunc', hP i, map_zero, sub_zero]
  rfl

/- English proof (translation)
Unfold `jetSubstPS`. Use `congr 1`. Use function extensionality and compare the values at `i`. Establish `h0 : MvPolynomial.constantCoeff (psTrunc m (Q i)) = 0`. Establish `hmem : (0 : κ' →₀ ℕ) ∈ degLE (ι` using `κ') m := by`.

Simplify using `only [degLE, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]`. Use `⟨⟨fun _ => 0, ?_⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `j`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite using `[← hQ i]`. Express the relevant statement in the definitionally equal form `MvPolynomial.coeff 0 (psTrunc m (Q i)) = _`. Unfold `psTrunc`. Rewrite using `[MvPolynomial.coeff_sum]`. Simplify using `only [MvPolynomial.coeff_monomial]`.

Rewrite using `[Finset.sum_ite_eq']`. Rewrite using `[if_pos hmem]`. Both sides reduce to the same expression. Rewrite using `[h0, map_zero, sub_zero]`.
-/
theorem jetSubstPS_eq_jetMap (m : ℕ) (Q : κ → MvPowerSeries κ' S) (hQ : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0) :
    jetSubstPS (m := m) Q = jetMap (fun i => psTrunc m (Q i)) (fun i => psTrunc_mem_orig m (Q i) (hQ i)) := by
  unfold jetSubstPS
  congr 1
  funext i
  have h0 : MvPolynomial.constantCoeff (psTrunc m (Q i)) = 0 := by
    have hmem : (0 : κ' →₀ ℕ) ∈ degLE (ι := κ') m := by
      simp only [degLE, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      refine ⟨⟨fun _ => 0, ?_⟩, ?_⟩
      · ext j
        simp
      · simp
    rw [← hQ i]
    change MvPolynomial.coeff 0 (psTrunc m (Q i)) = _
    unfold psTrunc
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    rw [if_pos hmem]
    rfl
  rw [h0, map_zero, sub_zero]

/- English proof (translation)
Rewrite using `[jetSubstPS_eq_jetMap m Q hQ, psJet_subst m Q hQ f]`.
-/
theorem jetSubstPS_psJet (m : ℕ) (Q : κ → MvPowerSeries κ' S) (hQ : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0)
    (f : MvPowerSeries κ S) : jetSubstPS (m := m) Q (psJet m f) = psJet m (MvPowerSeries.subst Q f) := by
  rw [jetSubstPS_eq_jetMap m Q hQ, psJet_subst m Q hQ f]

/- English proof (translation)
Conclude with `MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero hQ) hQ hf`.
-/
theorem const_substPS (Q : κ' → MvPowerSeries κ'' S) (hQ : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0)
    (f : MvPowerSeries κ' S) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst Q f) = 0 := by
  exact MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero hQ) hQ hf

/- English proof (translation)
Apply `Ideal.Quotient.algHom_ext` to reduce the goal to its premises. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `i`. Simplify using `only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]`. Rewrite using `[jetSubstPS_X m P hP i, jetSubstPS_psJet m Q hQ, jetSubstPS_X m _ (fun i => const_substPS Q hQ (P i) (hP i)) i]`.
-/
theorem jetSubstPS_comp (m : ℕ) (P : κ → MvPowerSeries κ' S) (Q : κ' → MvPowerSeries κ'' S)
    (hP : ∀ i, MvPowerSeries.constantCoeff (P i) = 0) (hQ : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0) :
    (jetSubstPS (m := m) Q).comp (jetSubstPS (m := m) P) =
      jetSubstPS (m := m) (fun i => MvPowerSeries.subst Q (P i)) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [jetSubstPS_X m P hP i, jetSubstPS_psJet m Q hQ,
    jetSubstPS_X m _ (fun i => const_substPS Q hQ (P i) (hP i)) i]

/- English proof (translation)
Establish `hσ' : ∀ i, MvPowerSeries.constantCoeff ((σ i : MvPowerSeries κ' S)) = 0` using `fun i => by show MvPowerSeries.coeff (0 : κ' →₀ ℕ) ((σ i : MvPowerSeries κ' S)) = 0`. Rewrite using `[MvPolynomial.coeff_coe]`. Conclude with `hσ i`. Apply `Ideal.Quotient.algHom_ext` to reduce the goal to its premises. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises.

Introduce `i`. Simplify using `only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]`. Rewrite using `[jetSubstPS_X m _ hσ' i, psJet_coe]`. Unfold `jetSubstP`. Rewrite using `[jetMap_mk, MvPolynomial.aeval_X, hσ i, map_zero, sub_zero]`.
-/
theorem jetSubstP_eq_jetSubstPS (m : ℕ) (σ : κ → MvPolynomial κ' S) (hσ : ∀ i, MvPolynomial.constantCoeff (σ i) = 0) :
    jetSubstP m σ = jetSubstPS (m := m) (fun i => (σ i : MvPowerSeries κ' S)) := by
  have hσ' : ∀ i, MvPowerSeries.constantCoeff ((σ i : MvPowerSeries κ' S)) = 0 := fun i => by
    show MvPowerSeries.coeff (0 : κ' →₀ ℕ) ((σ i : MvPowerSeries κ' S)) = 0
    rw [MvPolynomial.coeff_coe]
    exact hσ i
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [jetSubstPS_X m _ hσ' i, psJet_coe]
  unfold jetSubstP
  rw [jetMap_mk, MvPolynomial.aeval_X, hσ i, map_zero, sub_zero]

/- English proof (translation)
Apply `Ideal.Quotient.algHom_ext` to reduce the goal to its premises. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `p`. Simplify using `only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]`. Rewrite using `[jetSubstPS_X m _ (fun p => MvPowerSeries.constantCoeff_X _) p, ← MvPolynomial.coe_X, psJet_coe]`.

Unfold `jetCopy`. Rewrite using `[jetMap_mk, MvPolynomial.aeval_X]`.
-/
theorem jetCopy_eq_PS {d n : ℕ} (m : ℕ) (i : Fin n) :
    jetCopy (S := S) d m i =
      jetSubstPS (m := m) (fun p : Fin 1 × Fin d => (MvPowerSeries.X (i, p.2) : MvPowerSeries (Fin n × Fin d) S)) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro p
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [jetSubstPS_X m _ (fun p => MvPowerSeries.constantCoeff_X _) p, ← MvPolynomial.coe_X, psJet_coe]
  unfold jetCopy
  rw [jetMap_mk, MvPolynomial.aeval_X]

/- English proof (translation)
Rewrite using `[psJet_subst m Q hQ, psJet_subst m Q hQ, psJet_coe]`. Both sides reduce to the same expression.
-/
theorem psJet_subst_trunc (m : ℕ) (Q : κ → MvPowerSeries κ' S) (hQ : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0)
    (f : MvPowerSeries κ S) :
    psJet m (MvPowerSeries.subst Q ((psTrunc m f : MvPolynomial κ S) : MvPowerSeries κ S)) =
      psJet m (MvPowerSeries.subst Q f) := by
  rw [psJet_subst m Q hQ, psJet_subst m Q hQ, psJet_coe]
  rfl

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF
