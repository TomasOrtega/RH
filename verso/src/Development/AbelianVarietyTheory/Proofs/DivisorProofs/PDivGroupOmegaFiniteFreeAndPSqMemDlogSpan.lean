import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemRange

noncomputable section

open GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta CategoryTheory

namespace GlobalTheory.DlogSpan

/- English proof (translation)
Establish `flat : ∀ S : Submodule O (Fin h → O), Module.Flat O S` using `fun S => by`. Rewrite using `[Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]`. Introduce and unpack `x ⟨a, ha⟩`. Establish `h1 : (a : O) • (x : Fin h → O) = 0` using `congrArg Subtype.val ha`. Rewrite using `[Submodule.mem_bot]`.

Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `(smul_eq_zero.1 h1).resolve_left (nonZeroDivisors.ne_zero a.2)`. Use `haveI := flat (LinearMap.range b)`. Use `haveI : Module.Free O (LinearMap.range b) := Module.free_of_flat_of_isLocalRing`. Take `⟨s, hs⟩` from `Module.projective_lifting_property b.rangeRestrict LinearMap.id b.surjective_rangeRestrict`.

Establish `hs' : ∀ y, b (s y) = y` using `fun y => congrArg Subtype.val (LinearMap.congr_fun hs y)`. Set `π : (Fin h → O) →ₗ[O] LinearMap.ker b` to `(LinearMap.id - s ∘ₗ b.rangeRestrict).codRestrict _ fun x => by`. Simplify using `[LinearMap.mem_ker, hs']`. Establish `hπ : Function.Surjective π` using `fun x => ⟨x, by`. Apply `Subtype.ext` to reduce the goal to its premises.

Establish `h0 : b.rangeRestrict x = 0` using `Subtype.ext x.2`. Simplify using `[π, h0]⟩`. Use `haveI hfin : Module.Finite O (LinearMap.ker b) := Module.Finite.of_surjective π hπ`. Use `haveI := flat (LinearMap.ker b)`. Conclude with `⟨hfin, Module.free_of_flat_of_isLocalRing⟩`.
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
Establish `h0` using `hζ.geom_sum_eq_zero hk`. Establish `h1 : (k : O) = -∑ i ∈ Finset.range k, (ζ ^ i - 1)`. Rewrite using `[Finset.sum_sub_distrib, h0]`. Simplify using the standard rewrite rules. Rewrite using `[h1, dvd_neg]`.

Conclude with `Finset.dvd_sum fun i _ => sub_one_dvd_pow_sub_one ζ i`.
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
Rewrite using `[hodgeTate_apply, ← dualHom_bidual_inv, dlog_tateMap]`. Both sides reduce to the same expression.
-/
theorem pDivGroupOmegaBidual_dlog_eq_dual_hodgeTate (G : PDivGroup p O) (χ : G.dual.Tate) :
    pDivGroupOmegaBidualEquiv G (dlog G χ) = hodgeTate G.dual χ := by
  rw [hodgeTate_apply, ← dualHom_bidual_inv, dlog_tateMap]
  rfl

/- English proof (translation)
Introduce `p hp C _ _ _ v O _ _ _ _ _ ε hε hv hS G`. Use `haveI : ValuationRing O := ValuationRing.of_integers v hv`. Take `⟨u₁, u₂, hS⟩` from `hS`. Take `⟨D, e, fil, lie, hR⟩` from `hS G.dual ℤ_[p] (padicAction _)`. Set `Ψ : G.omega ≃ₗ[O] D.Fil` to `pDivGroupOmegaBidualEquiv G ≪≫ₗ fil`.

Take `⟨hfin, hfree⟩` from `ker_finite_free D.bb`. Use `haveI : Module.Finite O D.Fil := hfin`. Use `haveI : Module.Free O D.Fil := hfree`. Use `⟨Module.Finite.equiv Ψ.symm, Module.Free.of_equiv Ψ.symm, fun w => ?_⟩` and prove the remaining obligations. Establish `hζ : IsPrimitiveRoot (root ε).untilt p`.

Establish `h` using `hε 1`. Rewrite `h` using `[pow_one]`. Conclude with `h`. Take `⟨-, -, -, hb, -⟩` from `HodgeTateBound.bound p C v O hv ε hζ ℤ_[p] _ D`. Establish `hθ : WittVector.fontaineTheta O p (nu ε) = (root ε).untilt - 1`.

Rewrite using `[nu, map_sub, WittVector.fontaineTheta_teichmuller, map_one]`. Establish `hal : ∀ χ : G.dual.Tate, D.al (toO e χ) = (Ψ ((u₁ : O) • dlog G χ) : Fin _ → O)`. Introduce `χ`. Rewrite using `[hR.al_eq, ← hodgeTate_eq_omegaMap, ← pDivGroupOmegaBidual_dlog_eq_dual_hodgeTate, map_smul]`. Both sides reduce to the same expression.

Establish `key : ∀ y, ∃ s ∈ Submodule.span O (Set.range (dlog G)), D.al y = (Ψ s : Fin _ → O)`. Introduce `y`. Use `⟨∑ i, y i • (u₁ : O) • dlog G (e.symm (Pi.single i 1)), ?_, ?_⟩` and prove the remaining obligations. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))`. Establish `hy : y = ∑ i, y i • toO e (e.symm (Pi.single i 1))`.

Use extensionality with `j`. Simplify using `[toO, Finset.sum_apply, Pi.single_apply, apply_ite]`. Use `conv_lhs => rw [hy]`. Rewrite using `[map_sum, map_sum, Submodule.coe_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, hal, map_smul Ψ (y i), Submodule.coe_smul]`. Take `⟨y, hy⟩` from `hb (Ψ w) (Ψ w).2`. Take `⟨s, hs, hys⟩` from `key y`. Establish `h1 : WittVector.fontaineTheta O p (nu ε) • w = s`. Apply `Ψ.injective` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[map_smul, Submodule.coe_smul, ← hy, hys]`. Take `⟨c, hc⟩` from `sub_one_dvd hζ hp.out.one_lt`. Establish `h2 : (p : O) ^ 2 • w = ((p : O) * c) • s`. Rewrite using `[← h1, hθ, smul_smul, pow_two]`.

Use `congr 1`. Rewrite using `[mul_assoc, mul_comm c, ← hc]`. Rewrite using `[h2]`. Conclude with `Submodule.smul_mem _ _ hs`.
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
