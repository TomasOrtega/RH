import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemRange

noncomputable section

open GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta CategoryTheory

namespace GlobalTheory.DlogSpan

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Introduce a local definition for the expression. Simplify using the standard rewrite rules.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify using the standard rewrite rules. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem ker_finite_free {O : Type} [CommRing O] [IsDomain O] [ValuationRing O] {h : ℕ}
    (b : (Fin h → O) →ₗ[O] (Fin h → O)) :
    Module.Finite O (LinearMap.ker b) ∧ Module.Free O (LinearMap.ker b) := by
  have flat : ∀ S : Submodule O (Fin h → O), Module.Flat O S := fun S => by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro x ⟨a, ha⟩
    have h1 : (a : O) • (x : Fin h → O) = 0 := congrArg Subtype.val ha
    rw [Submodule.mem_bot]
    apply Subtype.ext
    exact (smul_eq_zero.1 h1).resolve_left (nonZeroDivisors.ne_zero a.2)
  haveI := flat (LinearMap.range b)
  haveI : Module.Free O (LinearMap.range b) := Module.free_of_flat_of_isLocalRing
  obtain ⟨s, hs⟩ := Module.projective_lifting_property b.rangeRestrict LinearMap.id
    b.surjective_rangeRestrict
  have hs' : ∀ y, b (s y) = y := fun y => congrArg Subtype.val (LinearMap.congr_fun hs y)
  let π : (Fin h → O) →ₗ[O] LinearMap.ker b :=
    (LinearMap.id - s ∘ₗ b.rangeRestrict).codRestrict _ fun x => by
      simp [LinearMap.mem_ker, hs']
  have hπ : Function.Surjective π := fun x => ⟨x, by
    apply Subtype.ext
    have h0 : b.rangeRestrict x = 0 := Subtype.ext x.2
    simp [π, h0]⟩
  haveI hfin : Module.Finite O (LinearMap.ker b) := Module.Finite.of_surjective π hπ
  haveI := flat (LinearMap.ker b)
  exact ⟨hfin, Module.free_of_flat_of_isLocalRing⟩

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem sub_one_dvd {O : Type} [CommRing O] [IsDomain O] {ζ : O} {k : ℕ}
    (hζ : IsPrimitiveRoot ζ k) (hk : 1 < k) : ζ - 1 ∣ (k : O) := by
  have h0 := hζ.geom_sum_eq_zero hk
  have h1 : (k : O) = -∑ i ∈ Finset.range k, (ζ ^ i - 1) := by
    rw [Finset.sum_sub_distrib, h0]; simp
  rw [h1, dvd_neg]
  exact Finset.dvd_sum fun i _ => sub_one_dvd_pow_sub_one ζ i

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]

def pDivGroupOmegaBidualEquiv (G : PDivGroup p O) : G.omega ≃ₗ[O] G.dual.dual.omega :=
  LinearEquiv.ofLinear (omegaMap _ _ G.bidual.inv) (omegaMap _ _ G.bidual.hom)
    (by rw [← omegaMap_comp, Iso.inv_hom_id, omegaMap_id])
    (by rw [← omegaMap_comp, Iso.hom_inv_id, omegaMap_id])

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem pDivGroupOmegaBidual_dlog_eq_dual_hodgeTate (G : PDivGroup p O) (χ : G.dual.Tate) :
    pDivGroupOmegaBidualEquiv G (dlog G χ) = hodgeTate G.dual χ := by
  rw [hodgeTate_apply, ← dualHom_bidual_inv, dlog_tateMap]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem finite_free_and_sq_smul_mem_span : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (ε : PreTilt O p) (hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), v.Integers O → GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε → ∀ G : PDivGroup p O, Module.Finite O G.omega ∧ Module.Free O G.omega ∧ ∀ w : G.omega, (p : O) ^ 2 • w ∈ Submodule.span O (Set.range (dlog (G := G))) := by
  intro p hp C _ _ _ v O _ _ _ _ _ ε hε hv hS G
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  obtain ⟨u₁, u₂, hS⟩ := hS
  obtain ⟨D, e, fil, lie, hR⟩ := hS G.dual ℤ_[p] (padicAction _)
  let Ψ : G.omega ≃ₗ[O] D.Fil := pDivGroupOmegaBidualEquiv G ≪≫ₗ fil
  obtain ⟨hfin, hfree⟩ := ker_finite_free D.bb
  haveI : Module.Finite O D.Fil := hfin
  haveI : Module.Free O D.Fil := hfree
  refine ⟨Module.Finite.equiv Ψ.symm, Module.Free.of_equiv Ψ.symm, fun w => ?_⟩
  have hζ : IsPrimitiveRoot (root ε).untilt p := by
    have h := hε 1
    rw [pow_one] at h
    exact h
  obtain ⟨-, -, -, hb, -⟩ := HodgeTateBound.bound p C v O hv ε hζ ℤ_[p] _ D
  have hθ : WittVector.fontaineTheta O p (nu ε) = (root ε).untilt - 1 := by
    rw [nu, map_sub, WittVector.fontaineTheta_teichmuller, map_one]
  have hal : ∀ χ : G.dual.Tate, D.al (toO e χ) = (Ψ ((u₁ : O) • dlog G χ) : Fin _ → O) := by
    intro χ
    rw [hR.al_eq, ← hodgeTate_eq_omegaMap, ← pDivGroupOmegaBidual_dlog_eq_dual_hodgeTate, map_smul]
    rfl
  have key : ∀ y, ∃ s ∈ Submodule.span O (Set.range (dlog G)),
      D.al y = (Ψ s : Fin _ → O) := by
    intro y
    refine ⟨∑ i, y i • (u₁ : O) • dlog G (e.symm (Pi.single i 1)), ?_, ?_⟩
    · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
    · have hy : y = ∑ i, y i • toO e (e.symm (Pi.single i 1)) := by
        ext j
        simp [toO, Finset.sum_apply, Pi.single_apply, apply_ite]
      conv_lhs => rw [hy]
      rw [map_sum, map_sum, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hal, map_smul Ψ (y i), Submodule.coe_smul]
  obtain ⟨y, hy⟩ := hb (Ψ w) (Ψ w).2
  obtain ⟨s, hs, hys⟩ := key y
  have h1 : WittVector.fontaineTheta O p (nu ε) • w = s := by
    apply Ψ.injective
    apply Subtype.ext
    rw [map_smul, Submodule.coe_smul, ← hy, hys]
  obtain ⟨c, hc⟩ := sub_one_dvd hζ hp.out.one_lt
  have h2 : (p : O) ^ 2 • w = ((p : O) * c) • s := by
    rw [← h1, hθ, smul_smul, pow_two]
    congr 1
    rw [mul_assoc, mul_comm c, ← hc]
  rw [h2]
  exact Submodule.smul_mem _ _ hs

end GlobalTheory.DlogSpan
