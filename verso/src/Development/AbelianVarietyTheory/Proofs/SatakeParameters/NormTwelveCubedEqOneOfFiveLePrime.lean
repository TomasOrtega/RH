import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.CmIntegralityOfTorsionPoints
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HasCMByStable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelAtPrimeEqSumTorsionTranslates

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

namespace GlobalTheory.GoodModelFive

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem norm_nat_twelve (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) {N k : ℕ} (hN : N ∣ 12 ^ k) : ‖(N : ℂ_[p])‖ = 1 := by
  refine Formalism.L2.Th1.E.ScaledModelNorms.norm_nat p fun h => ?_
  have hp : p.Prime := Fact.out
  have h12 : p ∣ 12 := hp.dvd_of_dvd_pow (h.trans hN)
  have hle : p ≤ 12 := Nat.le_of_dvd (by norm_num) h12
  interval_cases p <;> first | omega | exact absurd hp (by norm_num)

/- English proof (translation)
Simplify to obtain the desired conclusion from the available facts.
-/
theorem norm_twelve_cubed_eq_one_of_five_le_prime (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) : ‖(1728 : ℂ_[p])‖ = 1 := by
  simpa using norm_nat_twelve p h5 (N := 1728) (k := 3) (by norm_num)

/- English proof (translation)
Simplify to obtain the desired conclusion from the available facts.
-/
theorem norm_27 (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) : ‖(27 : ℂ_[p])‖ = 1 := by
  simpa using norm_nat_twelve p h5 (N := 27) (k := 3) (by norm_num)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem lamOf_eq_map (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    TaylorLogMetric.lamOf D cc δ = (TaylorLogMetric.lamOf D cc 1).map (AddMonoidHom.mulLeft δ) := by
  unfold TaylorLogMetric.lamOf
  rw [AddMonoidHom.map_closure]
  congr 1
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_image, AddMonoidHom.coe_mulLeft, one_mul]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨_, ⟨c, hc, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨c, hc, rfl⟩

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem omega1_ne_zero (L : PeriodPair) : L.ω₁ ≠ 0 := by
  have := L.indep.ne_zero 0
  simpa using this

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem intCurve_of_disc_one (hIn : GlobalTheory.ThLoc.Inputs) (d : ℕ) (L : PeriodPair) (hsq : Squarefree d) (hd4 : d % 4 = 3)
    (hcm : Formalism.L2.Th1.CM.HasCMBy d L) (hΔ : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1) (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p)
    (ι : ℂ ≃+* ℂ_[p]) : IntCurve (curveL p L ι) := by
  set a : ℂ := L.g₂ with ha
  set b : ℂ := L.g₃ with hb
  have hj : 1728 * a ^ 3 = Formalism.L2.Th1.CM.jInv L := by
    unfold Formalism.L2.Th1.CM.jInv
    rw [← ha, ← hb, hΔ, div_one]
  have hJ : ‖ι (Formalism.L2.Th1.CM.jInv L)‖ ≤ 1 :=
    GlobalTheory.NormSum.KernelAt.norm_le_one_of_isIntegral (by convert map_isIntegral_int ι (hIn.jInt d L hsq hd4 hcm); exact Subsingleton.elim _ _)
  have ha3 : ‖ι a‖ ^ 3 ≤ 1 := by
    have h := congrArg ι hj
    rw [map_mul, map_pow, map_ofNat] at h
    rw [← h, norm_mul, norm_twelve_cubed_eq_one_of_five_le_prime p h5, one_mul, norm_pow] at hJ
    exact hJ
  have ha1 : ‖ι a‖ ≤ 1 := (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 ha3
  have hb2 : ‖ι b‖ ^ 2 ≤ 1 := by
    have h : 27 * ι b ^ 2 = ι a ^ 3 - 1 := by
      have h := congrArg ι hΔ
      rw [map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one] at h
      linear_combination -h
    have h' := congrArg norm h
    rw [norm_mul, norm_27 p h5, one_mul, norm_pow] at h'
    rw [h', sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (by simp))
    rw [norm_pow]; exact ha3
  have hb1 : ‖ι b‖ ≤ 1 := (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 hb2
  unfold curveL
  refine Formalism.L2.Th1.E.ScaledModelNorms.intCurve_short p h5 _ _ ha1 hb1 ?_
  have h := congrArg ι hΔ
  rw [map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one] at h
  rw [h, norm_one]

end GlobalTheory.GoodModelFive

namespace GlobalTheory.GoodModelFive

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. It suffices to derive a contradiction.

Establish an intermediate fact. Replace the chosen expression with an arbitrary variable. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem goodModel_five : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc →
    TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0),
    CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p (cmL a₀ b₀ D.host.d ha hd lam hlam) ι) := by
  intro hIn D cc δ _hcc hδ a₀ b₀ c₀ ha hd lam hlam hok hlat p _ h5 ι
  set L := cmL a₀ b₀ D.host.d ha hd lam hlam with hL
  obtain ⟨h4, _hodd, h8, hprime⟩ := hok
  have hmem : ∀ z, z ∈ TaylorLogMetric.lamOf D cc δ ↔ z ∈ L.lattice := fun z => by
    rw [← hlat]; rfl

  have hδ0 : δ ≠ 0 := by
    rintro rfl
    have h1 : L.ω₁ ∈ TaylorLogMetric.lamOf D cc 0 := (hmem _).2 (L.mem_lattice.2 ⟨1, 0, by simp⟩)
    have hle : TaylorLogMetric.lamOf D cc 0 ≤ ⊥ := by
      unfold TaylorLogMetric.lamOf
      rw [AddSubgroup.closure_le]
      rintro w ⟨c, -, rfl⟩
      simp
    exact omega1_ne_zero L (by simpa using hle h1)

  set L' := Formalism.L2.Th1.F.scalePair L δ⁻¹ (inv_ne_zero hδ0) with hL'
  have hH := Formalism.L2.Th1.F.homogeneity L δ⁻¹ (inv_ne_zero hδ0)
  have hmem' : ∀ z, z ∈ TaylorLogMetric.lamOf D cc 1 ↔ z ∈ L'.lattice := fun z => by
    rw [hH.1, inv_inv, ← hmem, lamOf_eq_map D cc δ]
    exact (AddSubgroup.mem_map_iff_mem (f := AddMonoidHom.mulLeft δ) (mul_right_injective₀ hδ0)).symm
  have hdict := GlobalTheory.LatticeInvariants.invariants_dictionary L' (TaylorLogMetric.lamOf D cc 1) hmem'
  have e2 : TaylorLogMetric.g2 (TaylorLogMetric.lamOf D cc 1) = δ ^ 4 * L.g₂ := by
    rw [hdict.1, hH.2.2.2.2.2.2.2.2.2.1, inv_pow, inv_inv]
  have e3 : TaylorLogMetric.g3 (TaylorLogMetric.lamOf D cc 1) = δ ^ 6 * L.g₃ := by
    rw [hdict.2.1, hH.2.2.2.2.2.2.2.2.2.2, inv_pow, inv_inv]

  have hΔ : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1 := by
    have h : δ ^ 12 = δ ^ 12 * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
      conv_lhs => rw [hδ]
      unfold TaylorLogMetric.discr
      rw [e2, e3]
      ring
    have h12 : δ ^ 12 ≠ 0 := pow_ne_zero _ hδ0
    exact (mul_left_cancel₀ h12 (h.symm.trans (mul_one _).symm))

  have hbodd : Odd b₀ := by
    rcases Int.even_or_odd b₀ with ⟨k, hk⟩ | h
    · exfalso
      have e : (D.host.d : ℤ) = 4 * ((a₀ : ℤ) * c₀ - k * k) := by rw [hk] at h4; linear_combination -h4
      generalize (a₀ : ℤ) * c₀ - k * k = m at e
      omega
    · exact h
  have hcm : Formalism.L2.Th1.CM.HasCMBy D.host.d L :=
    Formalism.L2.Th1.F.hasCMByScale D.host.d _ lam hlam
      (Formalism.L2.Th1.F.cmPairHasCMBy a₀ b₀ c₀ D.host.d ha hd h4 hbodd)
  exact intCurve_of_disc_one hIn D.host.d L hprime.prime.squarefree (by omega) hcm hΔ p h5 ι

end GlobalTheory.GoodModelFive
