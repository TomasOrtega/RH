import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousIntegralInvMulOfLocallyIntegrable
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

open IsDedekindDomain

namespace GlobalTheory.AdeleDenom

variable (E : Type) [Field E] [NumberField E]

def intAfter (c : Af E) : Set (Af E) := {y | ∀ v, (c * y) v ∈ v.adicCompletionIntegers E}

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isOpen_intAfter (c : Af E) : IsOpen (intAfter E c) :=
  (GlobalTheory.AdLat.OpenLat.isOpen_integral E).preimage (continuous_const.mul continuous_id)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem nat_mul_integral (k : ℕ) {x : Af E} (hx : ∀ v, x v ∈ v.adicCompletionIntegers E) (v) :
    ((k : Af E) * x) v ∈ v.adicCompletionIntegers E := by
  have hk : ((k : Af E)) v ∈ v.adicCompletionIntegers E := by
    rw [show ((k : Af E)) v = (k : v.adicCompletion E) from rfl]
    exact natCast_mem _ k
  exact mul_mem hk (hx v)

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_nat_mul_integral (a : Af E) :
    ∃ N : ℕ, 0 < N ∧ ∀ v, ((N : Af E) * a) v ∈ v.adicCompletionIntegers E := by
  obtain ⟨N, hN, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele E (intAfter E a)
    ((isOpen_intAfter E a).mem_nhds (by intro v; simp only [mul_zero]; exact zero_mem _))
  refine ⟨N, hN, fun v => ?_⟩
  have h1 := h 1 (fun v => one_mem _) v
  rw [nsmul_eq_mul, mul_one, mul_comm] at h1
  exact h1

/- English proof (translation)
Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_intAfter_of_dvd {d m : ℕ} (h : d ∣ m) {y : Af E} (hy : y ∈ intAfter E (d : Af E)) :
    y ∈ intAfter E (m : Af E) := by
  obtain ⟨k, rfl⟩ := h
  intro v
  have e : (((d * k : ℕ)) : Af E) * y = (k : Af E) * ((d : Af E) * y) := by
    rw [Nat.cast_mul]; ring
  rw [e]
  exact nat_mul_integral E k hy v

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem intAfter_mono {n m : ℕ} (h : n ≤ m) :
    intAfter E ((n.factorial : ℕ) : Af E) ⊆ intAfter E ((m.factorial : ℕ) : Af E) :=
  fun _ hy => mem_intAfter_of_dvd E (Nat.factorial_dvd_factorial h) hy

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_common_denom : ∀ (E : Type) [Field E] [NumberField E] (Kf : Set (Af E)), IsCompact Kf →
    ∃ n : ℕ, 0 < n ∧ ∀ ξ : E, algebraMap E (Af E) ξ ∈ Kf → IsIntegral ℤ ((n : E) * ξ) := by
  intro E _ _ Kf hK
  have hcov : Kf ⊆ ⋃ n : ℕ, intAfter E ((n.factorial : ℕ) : Af E) := by
    intro y _
    obtain ⟨N, hN, h⟩ := exists_nat_mul_integral E y
    exact Set.mem_iUnion.mpr ⟨N, mem_intAfter_of_dvd E (Nat.dvd_factorial hN le_rfl) h⟩
  obtain ⟨n, hn⟩ := hK.elim_directed_cover _ (fun n => isOpen_intAfter E _) hcov
    (Monotone.directed_le fun a b h => intAfter_mono E h)
  refine ⟨n.factorial, Nat.factorial_pos n, fun ξ hξ => ?_⟩
  have h := hn hξ
  have hr : ((n.factorial : ℕ) : E) * ξ ∈ (algebraMap (𝓞 E) E).range := by
    refine HeightOneSpectrum.mem_integers_of_valuation_le_one E _ fun v => ?_
    have := h v
    rw [← map_natCast (algebraMap E (Af E)), ← map_mul] at this
    rwa [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
  obtain ⟨a, ha⟩ := hr
  rw [← ha]
  exact ((RingOfIntegers.isIntegral a).map (IsScalarTower.toAlgHom ℤ (𝓞 E) E))

end GlobalTheory.AdeleDenom
