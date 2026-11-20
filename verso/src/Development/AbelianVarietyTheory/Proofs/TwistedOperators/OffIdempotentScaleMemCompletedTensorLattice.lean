import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ShiftedTensorLatticePartMemLiftGroupPoints
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjPEqCP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatePlacesProductIdealProperOddCoprime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.OffIdemLat

open GlobalTheory.IdemSupport GlobalTheory.OffIdemDen

variable {D : D7}

abbrev conjProd (SS : Finset (Formalism.L2.DIV.Pl D.host.E)) : Ideal (𝓞 D.host.E) := ∏ PP ∈ SS, conjI PP.asIdeal

/- English proof (translation)
Take `⟨PP, hPP, hle⟩` from `(Ideal.IsPrime.prod_le Q.isPrime).1 h`. Establish `: PP = cP Q` using `eq_of_le fun x hx => by`. Rewrite using `[mem_cP]`. Conclude with `hle (Ideal.subset_span ⟨x, hx, rfl⟩)`. Conclude with `this ▸ hPP`.
-/
theorem cP_mem_of_le {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} {Q : HeightOneSpectrum (𝓞 D.host.E)}
    (h : conjProd SS ≤ Q.asIdeal) : cP Q ∈ SS := by
  obtain ⟨PP, hPP, hle⟩ := (Ideal.IsPrime.prod_le Q.isPrime).1 h
  have : PP = cP Q := eq_of_le fun x hx => by
    rw [mem_cP]
    exact hle (Ideal.subset_span ⟨x, hx, rfl⟩)
  exact this ▸ hPP

/- English proof (translation)
Rewrite using `[← Ideal.zero_eq_bot]`. Use `Finset.prod_ne_zero_iff.2 fun PP _ => ?_` and prove the remaining obligations. Rewrite using `[Ne, Ideal.zero_eq_bot, GlobalTheory.LiftIdeal.conjI_eq_map, Ideal.map_eq_bot_iff_of_injective (f := (GlobalTheory.LiftIdeal.conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E)) (GlobalTheory.LiftIdeal.conjO D).injective]`. Conclude with `PP.ne_bot`.
-/
theorem conjProd_ne_bot (SS : Finset (Formalism.L2.DIV.Pl D.host.E)) : conjProd SS ≠ ⊥ := by
  rw [← Ideal.zero_eq_bot]
  refine Finset.prod_ne_zero_iff.2 fun PP _ => ?_
  rw [Ne, Ideal.zero_eq_bot, GlobalTheory.LiftIdeal.conjI_eq_map,
    Ideal.map_eq_bot_iff_of_injective (f := (GlobalTheory.LiftIdeal.conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E))
      (GlobalTheory.LiftIdeal.conjO D).injective]
  exact PP.ne_bot

end GlobalTheory.OffIdemLat

namespace GlobalTheory.OffIdemLat
open GlobalTheory.IdemSupport GlobalTheory.OffIdemDen
variable {D : D7}

/- English proof (translation)
Take `⟨Φ, hΦ⟩` from `exists_comp D`. Take `⟨⟨es, hes, rfl⟩, horth⟩` from `he`. Establish `hd : ∀ P ∈ SS, IsDelta Φ P (es P)` using `fun P hP => delta_of_isIdemAt hΦ (hes P hP)`. Establish `hdc : ∀ P ∈ SS, IsDelta Φ (cP P) (cA D (es P))` using `fun P hP => delta_conj hΦ (hd P hP)`. Establish `hE : ∀ Q, Φ (∑ P ∈ SS, es P) Q = ∑ P ∈ SS, Φ (es P) Q` using `fun Q => map_sum (evQ Φ Q) _ _`.

Establish `hC : ∀ Q, Φ (cA D (∑ P ∈ SS, es P)) Q = ∑ P ∈ SS, Φ (cA D (es P)) Q` using `fun Q => by`. Rewrite using `[map_sum]`. Conclude with `map_sum (evQ Φ Q) _ _`. Establish `hO : ∀ Q, Φ (1 - ∑ P ∈ SS, es P - cA D (∑ P ∈ SS, es P)) Q = 1 - Φ (∑ P ∈ SS, es P) Q - Φ (cA D (∑ P ∈ SS, es P)) Q` using `fun Q => by`. Express the relevant statement in the definitionally equal form `evQ Φ Q _ = _`.

Rewrite using `[map_sub, map_sub, map_one]`. Both sides reduce to the same expression. Establish `hprod : ∀ Q, Φ (∑ P ∈ SS, es P) Q * Φ (cA D (∑ P ∈ SS, es P)) Q = 0` using `fun Q => by`. Rewrite using `[← ev_mul, horth, ev_zero]`. Rewrite using `[hΦ.int]`.

Introduce `Q`. Rewrite using `[ev_mul, hΦ.inc]`. Distinguish the cases in `hQ : Q ∈ SS ∨ cP Q ∈ SS`. Establish `h0 : Φ (1 - ∑ P ∈ SS, es P - cA D (∑ P ∈ SS, es P)) Q = 0`. Rewrite using `[hO]`.

Break down `hQ with hQ | hQ` into its components or cases. Establish `h1 : Φ (∑ P ∈ SS, es P) Q = 1`. Rewrite using `[hE, Finset.sum_eq_single Q (fun P hP hne => (hd P hP).2.2 Q (Ne.symm hne)) (fun h => absurd hQ h), (hd Q hQ).2.1]`. Establish `h2` using `hprod Q`. Rewrite `h2` using `[h1, one_mul]`.

Rewrite using `[h1, h2, sub_self, sub_zero]`. Establish `h1 : Φ (cA D (∑ P ∈ SS, es P)) Q = 1`. Rewrite using `[hC, Finset.sum_eq_single (cP Q) (fun P hP hne => (hdc P hP).2.2 Q (fun h => hne (by`. Rewrite using `[h, cP_cP])))`. Use the proof step `(fun h => absurd hQ h)]`.

Use `(hdc (cP Q) hQ).2.1` as an intermediate fact. Rewrite `this` using `[cP_cP]`. Then use the resulting hypothesis. Establish `h2` using `hprod Q`. Rewrite `h2` using `[h1, mul_one]`. Rewrite using `[h1, h2, sub_zero, sub_self]`.

Rewrite using `[h0, zero_mul]`. Conclude with `(Q.adicCompletionIntegers D.host.E).zero_mem`. Use `push_neg at hQ`. Use `mul_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[hO, hE, hC]`.

Conclude with `sub_mem (sub_mem (Q.adicCompletionIntegers D.host.E).one_mem (sum_mem fun P hP => delta_mem (hd P hP) Q)) (sum_mem fun P hP => delta_mem (hdc P hP) Q)`. Establish `hnle : ¬ conjProd SS ≤ Q.asIdeal` using `fun h => hQ.2 (cP_mem_of_le h)`. Take `⟨j, hj, hjQ⟩` from `Set.not_subset.1 hnle`. Take `⟨o, ho⟩` from `hx j hj`. Establish `hj0 : j ≠ 0` using `fun h => hjQ (h ▸ zero_mem _)`.

Establish `hj0' : ((j : 𝓞 D.host.E) : D.host.E) ≠ 0` using `fun h => hj0 (RingOfIntegers.ext (h.trans rfl))`. Establish `hxe : x = (o : D.host.E) * ((j : D.host.E))⁻¹`. Rewrite using `[ho, mul_assoc, mul_inv_cancel₀ hj0', mul_one]`. Establish `hinv` using `(inv_mem_iff Q hj0).2 hjQ`. Establish `ho' : algebraMap D.host.E (Q.adicCompletion D.host.E) (o : D.host.E) ∈ Q.adicCompletionIntegers D.host.E` using `HeightOneSpectrum.coe_mem_adicCompletionIntegers Q o`.

Express the relevant statement in the definitionally equal form `algebraMap D.host.E (Q.adicCompletion D.host.E) x ∈ Q.adicCompletionIntegers D.host.E`. Rewrite using `[hxe, map_mul]`. Conclude with `mul_mem ho' hinv`.
-/
theorem finPart_mul_mem (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)) (he : IsIdemSum e SS) (x : D.host.E)
    (hx : ∀ j ∈ conjProd SS, ∃ o : 𝓞 D.host.E, (o : D.host.E) = x * (j : D.host.E)) :
    finPart D ((1 - e - cA D e) * incA D x) ∈ intAE D := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨⟨es, hes, rfl⟩, horth⟩ := he
  have hd : ∀ P ∈ SS, IsDelta Φ P (es P) := fun P hP => delta_of_isIdemAt hΦ (hes P hP)
  have hdc : ∀ P ∈ SS, IsDelta Φ (cP P) (cA D (es P)) := fun P hP => delta_conj hΦ (hd P hP)
  have hE : ∀ Q, Φ (∑ P ∈ SS, es P) Q = ∑ P ∈ SS, Φ (es P) Q := fun Q => map_sum (evQ Φ Q) _ _
  have hC : ∀ Q, Φ (cA D (∑ P ∈ SS, es P)) Q = ∑ P ∈ SS, Φ (cA D (es P)) Q := fun Q => by
    rw [map_sum]; exact map_sum (evQ Φ Q) _ _
  have hO : ∀ Q, Φ (1 - ∑ P ∈ SS, es P - cA D (∑ P ∈ SS, es P)) Q =
      1 - Φ (∑ P ∈ SS, es P) Q - Φ (cA D (∑ P ∈ SS, es P)) Q := fun Q => by
    change evQ Φ Q _ = _
    rw [map_sub, map_sub, map_one]; rfl
  have hprod : ∀ Q, Φ (∑ P ∈ SS, es P) Q * Φ (cA D (∑ P ∈ SS, es P)) Q = 0 := fun Q => by
    rw [← ev_mul, horth, ev_zero]
  rw [hΦ.int]
  intro Q
  rw [ev_mul, hΦ.inc]
  by_cases hQ : Q ∈ SS ∨ cP Q ∈ SS
  · have h0 : Φ (1 - ∑ P ∈ SS, es P - cA D (∑ P ∈ SS, es P)) Q = 0 := by
      rw [hO]
      rcases hQ with hQ | hQ
      · have h1 : Φ (∑ P ∈ SS, es P) Q = 1 := by
          rw [hE, Finset.sum_eq_single Q (fun P hP hne => (hd P hP).2.2 Q (Ne.symm hne))
            (fun h => absurd hQ h), (hd Q hQ).2.1]
        have h2 := hprod Q
        rw [h1, one_mul] at h2
        rw [h1, h2, sub_self, sub_zero]
      · have h1 : Φ (cA D (∑ P ∈ SS, es P)) Q = 1 := by
          rw [hC, Finset.sum_eq_single (cP Q) (fun P hP hne => (hdc P hP).2.2 Q (fun h => hne (by
              rw [h, cP_cP])))
            (fun h => absurd hQ h)]
          have := (hdc (cP Q) hQ).2.1
          rwa [cP_cP] at this
        have h2 := hprod Q
        rw [h1, mul_one] at h2
        rw [h1, h2, sub_zero, sub_self]
    rw [h0, zero_mul]
    exact (Q.adicCompletionIntegers D.host.E).zero_mem
  · push_neg at hQ
    refine mul_mem ?_ ?_
    · rw [hO, hE, hC]
      exact sub_mem (sub_mem (Q.adicCompletionIntegers D.host.E).one_mem
        (sum_mem fun P hP => delta_mem (hd P hP) Q)) (sum_mem fun P hP => delta_mem (hdc P hP) Q)
    · have hnle : ¬ conjProd SS ≤ Q.asIdeal := fun h => hQ.2 (cP_mem_of_le h)
      obtain ⟨j, hj, hjQ⟩ := Set.not_subset.1 hnle
      obtain ⟨o, ho⟩ := hx j hj
      have hj0 : j ≠ 0 := fun h => hjQ (h ▸ zero_mem _)
      have hj0' : ((j : 𝓞 D.host.E) : D.host.E) ≠ 0 := fun h => hj0 (RingOfIntegers.ext (h.trans rfl))
      have hxe : x = (o : D.host.E) * ((j : D.host.E))⁻¹ := by
        rw [ho, mul_assoc, mul_inv_cancel₀ hj0', mul_one]
      have hinv := (inv_mem_iff Q hj0).2 hjQ
      have ho' : algebraMap D.host.E (Q.adicCompletion D.host.E) (o : D.host.E) ∈
          Q.adicCompletionIntegers D.host.E := HeightOneSpectrum.coe_mem_adicCompletionIntegers Q o
      change algebraMap D.host.E (Q.adicCompletion D.host.E) x ∈ Q.adicCompletionIntegers D.host.E
      rw [hxe, map_mul]
      exact mul_mem ho' hinv

end GlobalTheory.OffIdemLat

namespace GlobalTheory.OffIdemLat
open GlobalTheory.IdemSupport
variable {D : D7}

/- English proof (translation)
Use `GlobalTheory.Ker.SignVac.hatA_induction (p := fun u => (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((j : 𝓞 D.host.E) : D.host.E) : AE D) • u ∈ hatA S T (tens (stdL D.host.E S.rank) N)) ?_ ?_ ?_ ?_ hu` and prove the remaining obligations. Introduce `α hα y hy`. Rewrite using `[GlobalTheory.LatVac.tmul_smul_finTens, one_mul, ← Matrix.transpose_smul]`. Conclude with `GlobalTheory.Ker.SignVac.finTens_mem hα (GlobalTheory.LiftLevel.smul_mem_tens _ (fun v hv => hMN (Submodule.smul_mem_smul hj hv)) hy)`. Rewrite using `[smul_zero]`.

Conclude with `zero_mem _`. Introduce `x y hx hy`. Rewrite using `[smul_add]`. Conclude with `add_mem hx hy`. Introduce `x hx`.

Rewrite using `[smul_neg]`. Conclude with `neg_mem hx`.
-/
theorem fin_smul_mem {S T : HSp D} {J : Ideal (𝓞 D.host.E)} {M N : Lt D.host.E T.rank} (hMN : J • M ≤ N)
    {j : 𝓞 D.host.E} (hj : j ∈ J) {u : WO S T} (hu : u ∈ hatA S T (tens (stdL D.host.E S.rank) M)) :
    (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((j : 𝓞 D.host.E) : D.host.E) : AE D) • u ∈
      hatA S T (tens (stdL D.host.E S.rank) N) := by
  refine GlobalTheory.Ker.SignVac.hatA_induction (p := fun u => (pairA D.host.F 0 1 ⊗ₜ[D.host.F]
      ((j : 𝓞 D.host.E) : D.host.E) : AE D) • u ∈ hatA S T (tens (stdL D.host.E S.rank) N)) ?_ ?_ ?_ ?_ hu
  · intro α hα y hy
    rw [GlobalTheory.LatVac.tmul_smul_finTens, one_mul, ← Matrix.transpose_smul]
    exact GlobalTheory.Ker.SignVac.finTens_mem hα
      (GlobalTheory.LiftLevel.smul_mem_tens _ (fun v hv => hMN (Submodule.smul_mem_smul hj hv)) hy)
  · rw [smul_zero]; exact zero_mem _
  · intro x y hx hy; rw [smul_add]; exact add_mem hx hy
  · intro x hx; rw [smul_neg]; exact neg_mem hx

/- English proof (translation)
Introduce `D S T e SS he M N hMN u hu`. Establish `hA : ∀ o : 𝓞 D.host.E, ∀ y ∈ tens (stdL D.host.E S.rank) N, (o : D.host.E) • y ∈ tens (stdL D.host.E S.rank) N` using `fun o y hy => GlobalTheory.LiftLevel.smul_mem_tens o (fun v hv => Submodule.smul_mem _ o hv) hy`. Establish `hJ : ((conjProd SS : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.2 (conjProd_ne_bot SS)`. Establish `h1 : (1 : D.host.E) ∈ ((conjProd SS : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * ((conjProd SS : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹`. Rewrite using `[mul_inv_cancel₀ hJ]`.

Conclude with `FractionalIdeal.one_mem_one _`. Establish `key : ((1 - e - cA D e) * incA D 1) • u ∈ hatA S T (tens (stdL D.host.E S.rank) N)`. Use `FractionalIdeal.mul_induction_on (C := fun z => ((1 - e - cA D e) * incA D z) • u ∈ hatA S T (tens (stdL D.host.E S.rank) N)) h1 ?_ ?_` and prove the remaining obligations. Introduce `i hi x hx`. Take `⟨i', hi', rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).1 hi`.

Establish `hxJ : ∀ j ∈ conjProd SS, ∃ o : 𝓞 D.host.E, (o : D.host.E) = x * (j : D.host.E)`. Introduce `j hj`. Take `⟨o, ho⟩` from `(FractionalIdeal.mem_one_iff _).1 ((FractionalIdeal.mem_inv_iff hJ).1 hx (algebraMap (𝓞 D.host.E) D.host.E j) ((FractionalIdeal.mem_coeIdeal _).2 ⟨j, hj, rfl⟩))`. Conclude with `⟨o, ho⟩`. Establish `hint` using `finPart_mul_mem e SS he x hxJ`.

Establish `e1 : ((1 - e - cA D e) * incA D (algebraMap (𝓞 D.host.E) D.host.E i' * x)) • u = ((1 - e - cA D e) * incA D x) • (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((i' : 𝓞 D.host.E) : D.host.E) : AE D) • u`. Establish `e2 : (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((i' : 𝓞 D.host.E) : D.host.E) : AE D) = incA D ((i' : 𝓞 D.host.E) : D.host.E) * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E))`. Express the relevant statement in the definitionally equal form `_ = ((1 : AF D.host.F) ⊗ₜ[D.host.F] ((i' : 𝓞 D.host.E) : D.host.E)) * _`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]`. Rewrite using `[e2, mul_smul (incA D ((i' : 𝓞 D.host.E) : D.host.E)), GlobalTheory.Ker.SignVac.one_smul_hatA hu, smul_smul, mul_assoc, ← map_mul, mul_comm x]`.

Rewrite using `[e1]`. Conclude with `GlobalTheory.LiftLevel.smul_mem_hatA_of_int hA hint (fin_smul_mem hMN hi' hu)`. Introduce `x y hx hy`. Rewrite using `[map_add, mul_add, add_smul]`. Conclude with `add_mem hx hy`.

Rewrite `key` using `[map_one, mul_one]`. Rewrite using `[GlobalTheory.LiftLevel.partAt_eq_smul]`. Conclude with `key`.
-/
theorem partAt_off_mem : ∀ (D : D7) (S T : HSp D) (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (M N : Lt D.host.E T.rank), (∏ PP ∈ SS, conjI PP.asIdeal) • M ≤ N → ∀ u ∈ hatA S T (tens (stdL D.host.E S.rank) M), GlobalTheory.LiftLevel.partAt (1 - e - cA D e) u ∈ hatA S T (tens (stdL D.host.E S.rank) N) := by
  intro D S T e SS he M N hMN u hu
  have hA : ∀ o : 𝓞 D.host.E, ∀ y ∈ tens (stdL D.host.E S.rank) N,
      (o : D.host.E) • y ∈ tens (stdL D.host.E S.rank) N :=
    fun o y hy => GlobalTheory.LiftLevel.smul_mem_tens o (fun v hv => Submodule.smul_mem _ o hv) hy
  have hJ : ((conjProd SS : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (conjProd_ne_bot SS)
  have h1 : (1 : D.host.E) ∈ ((conjProd SS : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) *
      ((conjProd SS : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹ := by
    rw [mul_inv_cancel₀ hJ]
    exact FractionalIdeal.one_mem_one _
  have key : ((1 - e - cA D e) * incA D 1) • u ∈ hatA S T (tens (stdL D.host.E S.rank) N) := by
    refine FractionalIdeal.mul_induction_on (C := fun z => ((1 - e - cA D e) * incA D z) • u ∈
      hatA S T (tens (stdL D.host.E S.rank) N)) h1 ?_ ?_
    · intro i hi x hx
      obtain ⟨i', hi', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hi
      have hxJ : ∀ j ∈ conjProd SS, ∃ o : 𝓞 D.host.E, (o : D.host.E) = x * (j : D.host.E) := by
        intro j hj
        obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 ((FractionalIdeal.mem_inv_iff hJ).1 hx
          (algebraMap (𝓞 D.host.E) D.host.E j) ((FractionalIdeal.mem_coeIdeal _).2 ⟨j, hj, rfl⟩))
        exact ⟨o, ho⟩
      have hint := finPart_mul_mem e SS he x hxJ
      have e1 : ((1 - e - cA D e) * incA D (algebraMap (𝓞 D.host.E) D.host.E i' * x)) • u =
          ((1 - e - cA D e) * incA D x) •
            (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((i' : 𝓞 D.host.E) : D.host.E) : AE D) • u := by
        have e2 : (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((i' : 𝓞 D.host.E) : D.host.E) : AE D) =
            incA D ((i' : 𝓞 D.host.E) : D.host.E) * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E)) := by
          change _ = ((1 : AF D.host.F) ⊗ₜ[D.host.F] ((i' : 𝓞 D.host.E) : D.host.E)) * _
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
        rw [e2, mul_smul (incA D ((i' : 𝓞 D.host.E) : D.host.E)), GlobalTheory.Ker.SignVac.one_smul_hatA hu, smul_smul,
          mul_assoc, ← map_mul, mul_comm x]
      rw [e1]
      exact GlobalTheory.LiftLevel.smul_mem_hatA_of_int hA hint (fin_smul_mem hMN hi' hu)
    · intro x y hx hy
      rw [map_add, mul_add, add_smul]
      exact add_mem hx hy
  rw [map_one, mul_one] at key
  rw [GlobalTheory.LiftLevel.partAt_eq_smul]
  exact key

end GlobalTheory.OffIdemLat
