import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsUniformDenominator
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XTestptExists
import GroundTheory.ArithmeticGeometry.ToricVarieties.KrullDomain
open GlobalTheory.CompanionTheory.Ar.Num

namespace PositivityTheory.Xgn.A_ha_lattice

/- English proof (translation)
Establish `hloc : IsLocalRing S` using `IsLocalization.AtPrime.isLocalRing S q`. Establish `hN : IsNoetherianRing S` using `IsLocalization.isNoetherianRing q.primeCompl S inferInstance`. Establish `hI : IsIntegrallyClosed S` using `isIntegrallyClosed_of_isLocalization S q.primeCompl q.primeCompl_le_nonZeroDivisors`. Establish `hd : ringKrullDim S = 1`. Rewrite using `[IsLocalization.AtPrime.ringKrullDim_eq_height q S, h1]`.

Both sides reduce to the same expression. Establish `hf : ¬ IsField S` using `fun h => by`. Rewrite `hd` using `[ringKrullDim_eq_zero_of_isField h]`. Conclude with `absurd hd (by decide)`. Establish `hk : Ring.KrullDimLE 1 S` using `Ring.krullDimLE_iff.2 (by rw [hd]; rfl)`.

Establish `key : IsDiscreteValuationRing S ↔ IsIntegrallyClosed S ∧ ∃! P : Ideal S, P ≠ ⊥ ∧ P.IsPrime` using `(IsDiscreteValuationRing.TFAE S hf).out 0 3`. Use `key.2 ⟨hI, IsLocalRing.maximalIdeal S, ⟨IsLocalRing.isField_iff_maximalIdeal_eq.not.1 hf, inferInstance⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `P ⟨hP0, hP⟩`. Conclude with `IsLocalRing.eq_maximalIdeal (Ring.krullDimLE_one_iff_of_noZeroDivisors.1 hk P hP0 hP)`.
-/
theorem dvr_of_height_one {A S : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (q : Ideal A) [q.IsPrime] (h1 : q.height = 1) [CommRing S] [IsDomain S] [Algebra A S]
    [IsLocalization.AtPrime S q] : IsDiscreteValuationRing S := by
  have hloc : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S q
  have hN : IsNoetherianRing S := IsLocalization.isNoetherianRing q.primeCompl S inferInstance
  have hI : IsIntegrallyClosed S :=
    isIntegrallyClosed_of_isLocalization S q.primeCompl q.primeCompl_le_nonZeroDivisors
  have hd : ringKrullDim S = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q S, h1]; rfl
  have hf : ¬ IsField S := fun h => by
    rw [ringKrullDim_eq_zero_of_isField h] at hd
    exact absurd hd (by decide)
  have hk : Ring.KrullDimLE 1 S := Ring.krullDimLE_iff.2 (by rw [hd]; rfl)
  have key : IsDiscreteValuationRing S ↔ IsIntegrallyClosed S ∧ ∃! P : Ideal S, P ≠ ⊥ ∧ P.IsPrime :=
    (IsDiscreteValuationRing.TFAE S hf).out 0 3
  refine key.2 ⟨hI, IsLocalRing.maximalIdeal S,
    ⟨IsLocalRing.isField_iff_maximalIdeal_eq.not.1 hf, inferInstance⟩, ?_⟩
  rintro P ⟨hP0, hP⟩
  exact IsLocalRing.eq_maximalIdeal (Ring.krullDimLE_one_iff_of_noZeroDivisors.1 hk P hP0 hP)

/- English proof (translation)
Establish `hIC : IsIntegrallyClosed R` using `(isIntegrallyClosed_iff_isIntegrallyClosedIn Ω).2 hI`. Take `⟨y, hy⟩` from `GroundTheory.Arith.Toric.mem_range_of_forall_height_one (A := R) (K := Ω) a (fun q hq h1 => by`. Distinguish the cases in `hpq : (p : R) ∈ q`. Set `S : Subalgebra R Ω` to `Localization.subalgebra.ofField Ω q.primeCompl q.primeCompl_le_nonZeroDivisors`. Establish `hS : IsDiscreteValuationRing S` using `dvr_of_height_one q h1`.

Set `A : Subalgebra o Ω` to `S.restrictScalars o`. Establish `hA : IsDiscreteValuationRing A` using `hS`. Establish `hAF : IsFractionRing A Ω` using `(inferInstance : IsFractionRing S Ω)`. Establish `hu : ¬ IsUnit (p : A)`. Introduce `hu`.

Establish `hu' : IsUnit (algebraMap R S (p : R))`. Rewrite using `[map_natCast]`. Conclude with `hu`. Conclude with `((IsLocalization.AtPrime.isUnit_to_map_iff S q _).1 hu') hpq`. Take `⟨C, _, _, _, _, RC, hT, hRC⟩` from `PositivityTheory.Xgn.t_testpt_exists A p hp hp0 hA hAF hu`.

Establish `hT' : IsTestPt p R RC` using `⟨hT.1, hT.2.1, hT.2.2.1, fun b hb => hT.2.2.2 b (S.algebraMap_mem ⟨b, hb⟩)⟩`. Take `⟨b, s, hs, hab⟩` from `hRC a (h C RC hT')`. Use `⟨b, s, hs, ?_⟩` and prove the remaining obligations. Establish `hs0 : algebraMap R Ω s ≠ 0`. Introduce `h0`.

Establish `: s = 0` using `Subtype.ext h0`. Conclude with `hs (this ▸ q.zero_mem)`. Rewrite using `[hab, mul_assoc, inv_mul_cancel₀ hs0, mul_one]`. Use `⟨⟨_, hm⟩, (p : R) ^ m, fun h' => hpq (hq.mem_of_pow_mem m h'), ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow, map_natCast, mul_comm]`.

Use the proof step `rfl)`. Rewrite using `[← hy]`. Conclude with `y.2`.
-/
theorem mem_of_testPt {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (p : ℕ)
    (hp : p.Prime) (hp0 : (p : Ω) ≠ 0) (hN : IsNoetherianRing R) (hF : IsFractionRing R Ω)
    (hI : IsIntegrallyClosedIn R Ω) (a : Ω) (m : ℕ) (hm : (p : Ω) ^ m * a ∈ R)
    (h : ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C),
      IsTestPt p R RC → algebraMap Ω C a ∈ RC) : a ∈ R := by
  have hIC : IsIntegrallyClosed R := (isIntegrallyClosed_iff_isIntegrallyClosedIn Ω).2 hI
  obtain ⟨y, hy⟩ := GroundTheory.Arith.Toric.mem_range_of_forall_height_one (A := R) (K := Ω) a
    (fun q hq h1 => by
      by_cases hpq : (p : R) ∈ q
      · let S : Subalgebra R Ω :=
          Localization.subalgebra.ofField Ω q.primeCompl q.primeCompl_le_nonZeroDivisors
        have hS : IsDiscreteValuationRing S := dvr_of_height_one q h1
        let A : Subalgebra o Ω := S.restrictScalars o
        have hA : IsDiscreteValuationRing A := hS
        have hAF : IsFractionRing A Ω := (inferInstance : IsFractionRing S Ω)
        have hu : ¬ IsUnit (p : A) := by
          intro hu
          have hu' : IsUnit (algebraMap R S (p : R)) := by
            rw [map_natCast]; exact hu
          exact ((IsLocalization.AtPrime.isUnit_to_map_iff S q _).1 hu') hpq
        obtain ⟨C, _, _, _, _, RC, hT, hRC⟩ := PositivityTheory.Xgn.t_testpt_exists A p hp hp0 hA hAF hu
        have hT' : IsTestPt p R RC :=
          ⟨hT.1, hT.2.1, hT.2.2.1, fun b hb => hT.2.2.2 b (S.algebraMap_mem ⟨b, hb⟩)⟩
        obtain ⟨b, s, hs, hab⟩ := hRC a (h C RC hT')
        refine ⟨b, s, hs, ?_⟩
        have hs0 : algebraMap R Ω s ≠ 0 := by
          intro h0
          have : s = 0 := Subtype.ext h0
          exact hs (this ▸ q.zero_mem)
        rw [hab, mul_assoc, inv_mul_cancel₀ hs0, mul_one]
      · refine ⟨⟨_, hm⟩, (p : R) ^ m, fun h' => hpq (hq.mem_of_pow_mem m h'), ?_⟩
        rw [map_pow, map_natCast, mul_comm]
        rfl)
  rw [← hy]
  exact y.2

/- English proof (translation)
Use `⟨Fintype.linearCombination C fun i => algebraMap Ω C (ψ (Pi.single i 1)), fun e => ?_⟩` and prove the remaining obligations. Use `conv_rhs => rw [pi_eq_sum_univ' e]`. Simplify using `[Fintype.linearCombination_apply, bcMap, map_sum]`.
-/
theorem exists_ext {Ω C : Type} [Field Ω] [Field C] [Algebra Ω C] {ι : Type} [Fintype ι]
    (ψ : Module.Dual Ω (ι → Ω)) :
    ∃ Φ : Module.Dual C (ι → C), ∀ e, Φ (bcMap Ω C ι e) = algebraMap Ω C (ψ e) := by
  classical
  refine ⟨Fintype.linearCombination C fun i => algebraMap Ω C (ψ (Pi.single i 1)), fun e => ?_⟩
  conv_rhs => rw [pi_eq_sum_univ' e]
  simp [Fintype.linearCombination_apply, bcMap, map_sum]

end PositivityTheory.Xgn.A_ha_lattice

/- English proof (translation)
Introduce `o Ω _ _ _ R p hp hp0 hN hF hI ι _ N L hL v hv h`. Take `⟨m, hm⟩` from `hv`. Use `Reflexive.locFree_reflexive R N L hL v fun ψ hψ => ?_` and prove the remaining obligations. Use `PositivityTheory.Xgn.A_ha_lattice.mem_of_testPt R p hp hp0 hN hF hI (ψ v) m ?_ ?_` and prove the remaining obligations. Use `hψ _ hm` as an intermediate fact.

Rewrite `this` using `[map_smul, smul_eq_mul]`. Then use the resulting hypothesis. Introduce `C _ _ _ _ RC hT`. Take `⟨Φ, hΦ⟩` from `PositivityTheory.Xgn.A_ha_lattice.exists_ext (C := C) ψ`. Establish `key : ∀ x ∈ spanOver RC (bcMap Ω C ι '' L), Φ x ∈ RC`. Introduce `x hx`.

Proceed by induction on `hx using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨c, hc, _, ⟨e, he, rfl⟩, rfl⟩` from `hx`. Rewrite using `[map_smul, smul_eq_mul, hΦ]`. Conclude with `RC.mul_mem hc (hT.2.2.2 _ (hψ e he))`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `RC.add_mem hx hy`. Consider the case `neg x _ hx => rw [map_neg]`. Conclude with `RC.neg_mem hx`.

Rewrite using `[← hΦ]`. Conclude with `key _ (h C RC hT)`.
-/
theorem PositivityTheory.Xgn.t_ha_lattice : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (p : ℕ), p.Prime → (p : Ω) ≠ 0 → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ {ι : Type} [Fintype ι] (N : ℕ) (L : AddSubgroup (ι → Ω)), LocFree R N L → ∀ v : ι → Ω, (∃ m : ℕ, (p : Ω) ^ m • v ∈ L) → (∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), IsTestPt p R RC → bcMap Ω C ι v ∈ spanOver RC (bcMap Ω C ι '' L)) → v ∈ L := by
  intro o Ω _ _ _ R p hp hp0 hN hF hI ι _ N L hL v hv h
  obtain ⟨m, hm⟩ := hv
  refine Reflexive.locFree_reflexive R N L hL v fun ψ hψ => ?_
  refine PositivityTheory.Xgn.A_ha_lattice.mem_of_testPt R p hp hp0 hN hF hI (ψ v) m ?_ ?_
  · have := hψ _ hm
    rwa [map_smul, smul_eq_mul] at this
  · intro C _ _ _ _ RC hT
    obtain ⟨Φ, hΦ⟩ := PositivityTheory.Xgn.A_ha_lattice.exists_ext (C := C) ψ
    have key : ∀ x ∈ spanOver RC (bcMap Ω C ι '' L), Φ x ∈ RC := by
      intro x hx
      induction hx using AddSubgroup.closure_induction with
      | mem x hx =>
        obtain ⟨c, hc, _, ⟨e, he, rfl⟩, rfl⟩ := hx
        rw [map_smul, smul_eq_mul, hΦ]
        exact RC.mul_mem hc (hT.2.2.2 _ (hψ e he))
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact RC.add_mem hx hy
      | neg x _ hx => rw [map_neg]; exact RC.neg_mem hx
    rw [← hΦ]
    exact key _ (h C RC hT)
