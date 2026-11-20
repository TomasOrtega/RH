import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfRetract
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCyclotomicCharacterLocalGaloisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH2LeCardLocalStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotPowMaximalIdealDiscreteFiniteStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH2EqSameActionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCardH2CompEquivStatement
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory.QuotientH2Count

def zmodScalarRep (n : ℕ) {O Γ M : Type} [CommRing O] [Group Γ] [AddCommGroup M] [Module O M]
    [Module (ZMod n) M] (χ : Γ →* Oˣ) : Representation (ZMod n) Γ M where
  toFun g := (DistribMulAction.toAddMonoidHom M ((χ g : Oˣ) : O)).toZModLinearMap n
  map_one' := LinearMap.ext fun x => by
    show ((χ 1 : Oˣ) : O) • x = x
    rw [map_one, Units.val_one, one_smul]
  map_mul' g h := LinearMap.ext fun x => by
    show ((χ (g * h) : Oˣ) : O) • x = ((χ g : Oˣ) : O) • (((χ h : Oˣ) : O) • x)
    rw [map_mul, Units.val_mul, mul_smul]

/- English proof (translation)
Take `⟨rho, hrho⟩ : ∃ rho : Representation (ZMod (p ^ r)) (GK p K) M, ∀ (g : GK p K) (x : M), rho g x = ((ε (i.symm g) : Oˣ) : O) • x` from `⟨zmodScalarRep (p ^ r) (carry i ε), fun _ _ => rfl⟩`. Establish `hcont : ReciprocityTheory.Gal.ContAction rho`. Establish `e : (fun q : GK p K × M => rho q.1 q.2) = (fun q : G × M => ((ε q.1 : Oˣ) : O) • q.2) ∘ fun q => (i.symm q.1, q.2)`. Use function extensionality and compare the values at `q`. Conclude with `hrho q.1 q.2`.

Unfold `ReciprocityTheory.Gal.ContAction`. Rewrite using `[e]`. Conclude with `hc.comp ((i.symm.continuous.comp continuous_fst).prodMk continuous_snd)`. Take `⟨hF, hC⟩` from `GlobalTheory.T.card_H2_le_card_local hTD p K hK r M rho hr hcont`. Establish `htr` using `GlobalTheory.T.natCard_H2_comp_equiv i rho`.

Establish `hsc` using `GlobalTheory.T.card_H2_eq_same_action (rho.comp i.toMulEquiv.toMonoidHom) (twist ε M) (fun g x => by show rho (i g) x = ((ε g : Oˣ) : O) • x`. Rewrite using `[hrho, i.symm_apply_apply])`. Establish `hcard : Nat.card (H2 (twist ε M)) = Nat.card (H2 rho)`. Rewrite using `[← hsc, htr]`. Use `⟨?_, hcard ▸ hC⟩` and prove the remaining obligations.

Apply `Nat.finite_of_card_ne_zero` to reduce the goal to its premises. Rewrite using `[hcard]`. Conclude with `Nat.card_pos.ne'`.
-/
theorem h2_twist_card_of_zmod {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
    (hTD : Formalism.GaloisCohomology.LocalTateDualityK) (hK : FiniteDimensional ℚ_[p] K) (i : G ≃ₜ* GK p K)
    (ε : G →* Oˣ) (M : Type) [AddCommGroup M] [Module O M] [TopologicalSpace M]
    [DiscreteTopology M] [Finite M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M]
    (r : ℕ) [Module (ZMod (p ^ r)) M] (hr : 0 < r)
    (hc : Continuous fun q : G × M => ((ε q.1 : Oˣ) : O) • q.2) :
    Finite (H2 (twist ε M)) ∧ Nat.card (H2 (twist ε M)) ≤ Nat.card M := by
  obtain ⟨rho, hrho⟩ : ∃ rho : Representation (ZMod (p ^ r)) (GK p K) M,
      ∀ (g : GK p K) (x : M), rho g x = ((ε (i.symm g) : Oˣ) : O) • x :=
    ⟨zmodScalarRep (p ^ r) (carry i ε), fun _ _ => rfl⟩
  have hcont : ReciprocityTheory.Gal.ContAction rho := by
    have e : (fun q : GK p K × M => rho q.1 q.2) =
        (fun q : G × M => ((ε q.1 : Oˣ) : O) • q.2) ∘ fun q => (i.symm q.1, q.2) := by
      funext q; exact hrho q.1 q.2
    unfold ReciprocityTheory.Gal.ContAction
    rw [e]
    exact hc.comp ((i.symm.continuous.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨hF, hC⟩ := GlobalTheory.T.card_H2_le_card_local hTD p K hK r M rho hr hcont
  have htr := GlobalTheory.T.natCard_H2_comp_equiv i rho
  have hsc := GlobalTheory.T.card_H2_eq_same_action (rho.comp i.toMulEquiv.toMonoidHom) (twist ε M) (fun g x => by
      show rho (i g) x = ((ε g : Oˣ) : O) • x
      rw [hrho, i.symm_apply_apply])
  have hcard : Nat.card (H2 (twist ε M)) = Nat.card (H2 rho) := by
    rw [← hsc, htr]
  refine ⟨?_, hcard ▸ hC⟩
  apply Nat.finite_of_card_ne_zero
  rw [hcard]
  exact Nat.card_pos.ne'

/- English proof (translation)
Introduce `p _ K O _ _ _ _ _ G _ _ hTD hK hO i ε hε k`. Take `⟨hdisc, hfin⟩` from `GlobalTheory.T.quotient_maximalIdeal_pow_discrete_and_finite hO k`. Use `haveI := hdisc`. Use `haveI := hfin`. Establish `hkill : ∀ x : O ⧸ IsLocalRing.maximalIdeal O ^ k, (p ^ (k + 1)) • x = 0`.

Introduce `x`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite using `[← map_nsmul, Ideal.Quotient.eq_zero_iff_mem, nsmul_eq_mul]`. Use `push_cast`. Rewrite using `[pow_succ, mul_assoc]`.

Conclude with `Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hO.p_mem k)`. Establish `hce` using `GlobalTheory.T.continuous_cyclotomic_character_localGalois hO i hε`. Establish `hc : Continuous fun q : G × (O ⧸ IsLocalRing.maximalIdeal O ^ k) => ((ε q.1 : Oˣ) : O) • q.2`. Establish `hq : Continuous (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ k))` using `continuous_quot_mk`. Establish `e : (fun q : G × (O ⧸ IsLocalRing.maximalIdeal O ^ k) => ((ε q.1 : Oˣ) : O) • q.2) = fun q => Ideal.Quotient.mk _ ((ε q.1 : Oˣ) : O) * q.2`.

Use function extensionality and compare the values at `q`. Conclude with `Algebra.smul_def _ _`. Rewrite using `[e]`. Conclude with `((hq.comp hce).comp continuous_fst).mul continuous_snd`. Use `letI : Module (ZMod (p ^ (k + 1))) (O ⧸ IsLocalRing.maximalIdeal O ^ k) := AddCommGroup.zmodModule hkill`.

Conclude with `h2_twist_card_of_zmod hTD hK i ε _ (k + 1) (Nat.succ_pos k) hc`.
-/
theorem h2_quot_card : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] {G : Type} [Group G] [TopologicalSpace G], Formalism.GaloisCohomology.LocalTateDualityK → FiniteDimensional ℚ_[p] K → PadicCoeff p O → ∀ (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) → ∀ k : ℕ, Finite (H2 (twist ε (O ⧸ IsLocalRing.maximalIdeal O ^ k))) ∧ Nat.card (H2 (twist ε (O ⧸ IsLocalRing.maximalIdeal O ^ k))) ≤ Nat.card (O ⧸ IsLocalRing.maximalIdeal O ^ k) := by
  intro p _ K O _ _ _ _ _ G _ _ hTD hK hO i ε hε k
  obtain ⟨hdisc, hfin⟩ := GlobalTheory.T.quotient_maximalIdeal_pow_discrete_and_finite hO k
  haveI := hdisc
  haveI := hfin
  have hkill : ∀ x : O ⧸ IsLocalRing.maximalIdeal O ^ k, (p ^ (k + 1)) • x = 0 := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_nsmul, Ideal.Quotient.eq_zero_iff_mem, nsmul_eq_mul]
    push_cast
    rw [pow_succ, mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hO.p_mem k)
  have hce := GlobalTheory.T.continuous_cyclotomic_character_localGalois hO i hε
  have hc : Continuous fun q : G × (O ⧸ IsLocalRing.maximalIdeal O ^ k) =>
      ((ε q.1 : Oˣ) : O) • q.2 := by
    have hq : Continuous (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ k)) := continuous_quot_mk
    have e : (fun q : G × (O ⧸ IsLocalRing.maximalIdeal O ^ k) => ((ε q.1 : Oˣ) : O) • q.2) =
        fun q => Ideal.Quotient.mk _ ((ε q.1 : Oˣ) : O) * q.2 := by
      funext q; exact Algebra.smul_def _ _
    rw [e]
    exact ((hq.comp hce).comp continuous_fst).mul continuous_snd
  letI : Module (ZMod (p ^ (k + 1))) (O ⧸ IsLocalRing.maximalIdeal O ^ k) :=
    AddCommGroup.zmodModule hkill
  exact h2_twist_card_of_zmod hTD hK i ε _ (k + 1) (Nat.succ_pos k) hc

end GlobalTheory.QuotientH2Count
