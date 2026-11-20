import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
open IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.IwaPlace

variable {D : D7}

open GlobalTheory.SelfDualAt in

/- English proof (translation)
Use `Ideal.mem_inf.2 ⟨?_, Ideal.mem_iInf.2 fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.mem_ker] show infPart D (cP (· = v) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0`. Conclude with `TensorProduct.zero_tmul _ _`. Rewrite using `[RingHom.mem_ker] show GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w.1 (finPart D (algebraMap (AF D.host.F) (AE D) (cP (· = v)))) = 0`. Rewrite using `[Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, GlobalTheory.LatVac.finPart_tmul]`.

Establish `h : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w.1 (sndA D.host.F (cP (· = v)) ⊗ₜ[D.host.F] (1 : D.host.E)) = evalV D.host.F w.1 (indP (· = v)) ⊗ₜ[D.host.F] (1 : D.host.E)`. Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]`. Both sides reduce to the same expression. Rewrite using `[h, evalV_indP, if_neg w.2]`. Conclude with `TensorProduct.zero_tmul _ _`.
-/
theorem idAt₂ (v : Pl D) : algebraMap (AF D.host.F) (AE D) (cP (· = v)) ∈ idAt D (· = v) := by
  refine Ideal.mem_inf.2 ⟨?_, Ideal.mem_iInf.2 fun w => ?_⟩
  · rw [RingHom.mem_ker]
    show infPart D (cP (· = v) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    exact TensorProduct.zero_tmul _ _
  · rw [RingHom.mem_ker]
    show GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w.1 (finPart D (algebraMap (AF D.host.F) (AE D) (cP (· = v)))) = 0
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, GlobalTheory.LatVac.finPart_tmul]
    have h : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w.1 (sndA D.host.F (cP (· = v)) ⊗ₜ[D.host.F] (1 : D.host.E)) =
        evalV D.host.F w.1 (indP (· = v)) ⊗ₜ[D.host.F] (1 : D.host.E) := by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply]
      rfl
    rw [h, evalV_indP, if_neg w.2]
    exact TensorProduct.zero_tmul _ _

open GlobalTheory.SelfDualAt in

/- English proof (translation)
Establish `h1` using `algebraMap_placeIdempotent_mul (· = v) ε hεI.1`. Establish `h2` using `(hε _).1 (idAt₂ v)`. Rewrite using `[← h2, mul_comm]`. Conclude with `h1.symm`.
-/
theorem eq_alg_cP {v : Pl D} {ε : AE D} (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) :
    ε = algebraMap (AF D.host.F) (AE D) (cP (· = v)) := by
  have h1 := algebraMap_placeIdempotent_mul (· = v) ε hεI.1
  have h2 := (hε _).1 (idAt₂ v)
  rw [← h2, mul_comm]
  exact h1.symm

open GlobalTheory.SelfDualAt in

/- English proof (translation)
Take `⟨α, rfl, h1, h0⟩` from `h`. Unfold `cP`. Use `congr 1`. Use `FiniteAdeleRing.ext (R := 𝓞 D.host.F) D.host.F fun w => ?_` and prove the remaining obligations. Use `show evalV D.host.F w α = evalV D.host.F w (indP (· = v))`.

Rewrite using `[evalV_indP]`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[if_pos rfl, h1]`. Rewrite using `[if_neg hw, h0 w hw]`.
-/
theorem placeIdem_eq_cP {v : Pl D} {εF : AF D.host.F} (h : IsPlaceIdem D v εF) : εF = cP (· = v) := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  unfold cP
  congr 1
  refine FiniteAdeleRing.ext (R := 𝓞 D.host.F) D.host.F fun w => ?_
  show evalV D.host.F w α = evalV D.host.F w (indP (· = v))
  rw [evalV_indP]
  by_cases hw : w = v
  · subst hw; rw [if_pos rfl, h1]
  · rw [if_neg hw, h0 w hw]

/- English proof (translation)
Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Establish `e1 : Valued.v (algebraMap D.host.F (Fv D.host.F v) 2⁻¹) = v.valuation D.host.F 2⁻¹` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _`. Establish `e2 : v.valuation D.host.F (2 : D.host.F) = 1`. Use `HeightOneSpectrum.valuation_of_algebraMap (K := D.host.F) v (2 : 𝓞 D.host.F)` as an intermediate fact. Simplify using `only [map_ofNat] at this`.

Rewrite using `[this]`. Conclude with `HeightOneSpectrum.intValuation_eq_one_iff.2 h2`. Rewrite using `[e1, map_inv₀, e2, inv_one]`.
-/
theorem half_mem_int (v : Pl D) (h2 : (2 : 𝓞 D.host.F) ∉ v.asIdeal) :
    algebraMap D.host.F (Fv D.host.F v) (2⁻¹) ∈ v.adicCompletionIntegers D.host.F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have e1 : Valued.v (algebraMap D.host.F (Fv D.host.F v) 2⁻¹) = v.valuation D.host.F 2⁻¹ :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  have e2 : v.valuation D.host.F (2 : D.host.F) = 1 := by
    have := HeightOneSpectrum.valuation_of_algebraMap (K := D.host.F) v (2 : 𝓞 D.host.F)
    simp only [map_ofNat] at this
    rw [this]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 h2
  rw [e1, map_inv₀, e2, inv_one]

open GlobalTheory.SelfDualAt in

/- English proof (translation)
Introduce `D v ε _ _ hεI hε ht`. Establish `hεη` using `eq_alg_cP hεI hε`. Break down `ht.2 with h2 | ⟨e, εF, hsp, hpl, hsum⟩` into its components or cases. Use `⟨algebraMap (AF D.host.F) (AE D) (cP (· = v) * algebraMap D.host.F (AF D.host.F) 2⁻¹), ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul]`.

Conclude with `Ideal.mul_mem_right _ _ (idAt₂ v)`. Rewrite using `[Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, GlobalTheory.LatVac.finPart_tmul]`. Use `AddSubgroup.subset_closure ⟨sndA D.host.F (cP (· = v) * algebraMap D.host.F (AF D.host.F) 2⁻¹), fun w => ?_, 1, by simp⟩` and prove the remaining obligations. Rewrite using `[map_mul, AlgHom.commutes, map_mul]`. Use `show evalV D.host.F w (indP (· = v)) * _ ∈ _`.

Rewrite using `[evalV_indP]`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[if_pos rfl, one_mul, AlgHom.commutes]`. Conclude with `half_mem_int w h2`.

Rewrite using `[if_neg hw, zero_mul]`. Conclude with `zero_mem _`. Rewrite using `[cA_alg, ← map_add, hεη]`. Use `congr 1`. Rewrite using `[← two_mul, mul_left_comm, ← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one, mul_one]`.

Establish `hs : e + cA D e = ε` using `by rw [hsum, placeIdem_eq_cP hpl, hεη]`. Use `⟨e, ⟨?_, ?_⟩, hs⟩` and prove the remaining obligations. Establish `: e * ε = e` using `by rw [← hs, mul_add, hsp.1, hsp.2.1, add_zero]`. Rewrite using `[← this]`. Conclude with `Ideal.mul_mem_left _ _ hεI.1`.

Conclude with `GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hsp.1])`.
-/
theorem exists_trace_one_at_tame : ∀ (D : D7) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε)
    (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a), Tame D v →
    ∃ w ∈ intAt D (· = v), w + cA D w = ε := by
  intro D v ε _ _ hεI hε ht
  have hεη := eq_alg_cP hεI hε
  rcases ht.2 with h2 | ⟨e, εF, hsp, hpl, hsum⟩
  · refine ⟨algebraMap (AF D.host.F) (AE D) (cP (· = v) * algebraMap D.host.F (AF D.host.F) 2⁻¹), ⟨?_, ?_⟩, ?_⟩
    · rw [map_mul]
      exact Ideal.mul_mem_right _ _ (idAt₂ v)
    · rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, GlobalTheory.LatVac.finPart_tmul]
      refine AddSubgroup.subset_closure ⟨sndA D.host.F (cP (· = v) * algebraMap D.host.F (AF D.host.F) 2⁻¹), fun w => ?_, 1, by simp⟩
      rw [map_mul, AlgHom.commutes, map_mul]
      show evalV D.host.F w (indP (· = v)) * _ ∈ _
      rw [evalV_indP]
      by_cases hw : w = v
      · subst hw
        rw [if_pos rfl, one_mul, AlgHom.commutes]
        exact half_mem_int w h2
      · rw [if_neg hw, zero_mul]
        exact zero_mem _
    · rw [cA_alg, ← map_add, hεη]
      congr 1
      rw [← two_mul, mul_left_comm, ← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul,
        mul_inv_cancel₀ two_ne_zero, map_one, mul_one]
  · have hs : e + cA D e = ε := by rw [hsum, placeIdem_eq_cP hpl, hεη]
    refine ⟨e, ⟨?_, ?_⟩, hs⟩
    · have : e * ε = e := by rw [← hs, mul_add, hsp.1, hsp.2.1, add_zero]
      rw [← this]
      exact Ideal.mul_mem_left _ _ hεI.1
    · exact GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hsp.1])

end GlobalTheory.IwaPlace

end
