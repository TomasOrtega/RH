import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RelIndexSquaresLeTwoMulOfSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HigherUnitsLeSquaresHigherUnitsStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGlobalUniformizerResidueRepresentativesStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RelIndexHigherUnitsSuccLeCardStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IndexSquaresLeTwoMulUnitsSquaresStatement

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

/- English proof (translation)
Introduce and unpack `x ⟨hx, hx'⟩`. Use `⟨hx, hx'.trans ?_⟩` and prove the remaining obligations. Rewrite using `[WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem sqIdx_hiUnits_anti {K : Type} [Field K] (w : Valuation K ℤᵐ⁰) {m n : ℕ} (h : m ≤ n) :
    hiUnits w n ≤ hiUnits w m := by
  rintro x ⟨hx, hx'⟩
  refine ⟨hx, hx'.trans ?_⟩
  rw [WithZero.exp_le_exp]
  omega

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Take `⟨h1, h2⟩` from `GlobalTheory.T.relIndex_higherUnits_succ_le_card K w π R (n + k) hπ hR`. Use `Subgroup.relIndex_mul_relIndex (hiUnits w (n + k + 1)) (hiUnits w (n + k)) (hiUnits w n) (sqIdx_hiUnits_anti w (by omega)) (sqIdx_hiUnits_anti w (by omega))` as an intermediate fact.

Rewrite using `[← add_assoc, ← this]`. Use `⟨mul_ne_zero h1 ih.1, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ']`. Conclude with `Nat.mul_le_mul h2 ih.2`.
-/
theorem sqIdx_relIndex_hiUnits_add {K : Type} [Field K] (w : Valuation K ℤᵐ⁰) (π : K)
    (R : Finset K) (hπ : w π = WithZero.exp (-1))
    (hR : ∀ x : K, w x ≤ 1 → ∃ r ∈ R, w (x - r) < 1) (n k : ℕ) :
    (hiUnits w (n + k)).relIndex (hiUnits w n) ≠ 0 ∧
      (hiUnits w (n + k)).relIndex (hiUnits w n) ≤ R.card ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨h1, h2⟩ := GlobalTheory.T.relIndex_higherUnits_succ_le_card K w π R (n + k) hπ hR
    have := Subgroup.relIndex_mul_relIndex (hiUnits w (n + k + 1)) (hiUnits w (n + k))
      (hiUnits w n) (sqIdx_hiUnits_anti w (by omega)) (sqIdx_hiUnits_anti w (by omega))
    rw [← add_assoc, ← this]
    refine ⟨mul_ne_zero h1 ih.1, ?_⟩
    rw [pow_succ']
    exact Nat.mul_le_mul h2 ih.2

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[mem_sqSub, Subgroup.mem_comap]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, hr⟩`. Establish `hx : φ (x : F) ≠ 0` using `by simp`.

Establish `hr0 : r ≠ 0`. Introduce and unpack `rfl`. Conclude with `hx (by simpa using hr)`. Use `⟨Units.mk0 r hr0, Subgroup.mem_top _, ?_⟩` and prove the remaining obligations. Use `ext`.

Simplify using `[hr, sq]`. Introduce and unpack `⟨r, -, hr⟩`. Use `⟨(r : L), ?_⟩` and prove the remaining obligations. Use `congrArg (fun u : Lˣ => (u : L)) hr` as an intermediate fact. Simplify `this.symm` using `[sq]`.
-/
theorem sqIdx_sqSub_eq_comap {F L : Type} [Field F] [Field L] (φ : F →+* L) :
    sqSub φ = (sqs (⊤ : Subgroup Lˣ)).comap (Units.map (φ : F →* L)) := by
  ext x
  rw [mem_sqSub, Subgroup.mem_comap]
  constructor
  · rintro ⟨r, hr⟩
    have hx : φ (x : F) ≠ 0 := by simp
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact hx (by simpa using hr)
    refine ⟨Units.mk0 r hr0, Subgroup.mem_top _, ?_⟩
    ext
    simp [hr, sq]
  · rintro ⟨r, -, hr⟩
    refine ⟨(r : L), ?_⟩
    have := congrArg (fun u : Lˣ => (u : L)) hr
    simpa [sq] using this.symm

/- English proof (translation)
Introduce `F _ _ v e he`. Take `⟨⟨π, -, hπ⟩, hval, -, R, hcard, -, hR⟩` from `GlobalTheory.T.exists_global_uniformizer_residue_representatives F v`. Establish `h2 : Valued.v (2 : v.adicCompletion F) = WithZero.exp (-(e : ℤ))`. Rewrite using `[← he, ← hval, map_ofNat (algebraMap F (v.adicCompletion F))]`. Establish `hsq` using `GlobalTheory.T.higherUnits_le_squares_higherUnits F v e h2`.

Use `set w : Valuation (v.adicCompletion F) ℤᵐ⁰ := Valued.v with hw`. Establish `hA` using `sqIdx_relIndex_hiUnits_add w _ R hπ hR (e + 1) e`. Establish `hB` using `sqIdx_relIndex_hiUnits_add w _ R hπ hR 0 (e + 1)`. Rewrite `hA` using `[show e + 1 + e = 2 * e + 1 by ring]`. Rewrite `hB` using `[zero_add]`.

Establish `hC0 : (sqs (hiUnits w (e + 1))).relIndex (hiUnits w (e + 1)) ≠ 0` using `fun h => hA.1 (Subgroup.relIndex_eq_zero_of_le_left hsq h)`. Establish `hC : (sqs (hiUnits w (e + 1))).relIndex (hiUnits w (e + 1)) ≤ R.card ^ e` using `(Subgroup.relIndex_le_of_le_left hsq hA.1).trans hA.2`. Establish `hD` using `GlobalTheory.T.relIndex_squares_le_two_mul_of_subgroup (v.adicCompletion F)ˣ (hiUnits w 0) (hiUnits w (e + 1)) (-1) (sqIdx_hiUnits_anti w (by omega)) hB.1 (fun a ha => by`. Establish `h : (a : v.adicCompletion F) ^ 2 = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, ha, Units.val_one]`.

Break down `sq_eq_one_iff.mp h with h | h` into its components or cases. Use `left`. Conclude with `Units.ext h`. Use the proof step `right; exact Units.ext (by simpa using h)) hC0`. Establish `hE` using `GlobalTheory.T.index_squares_le_two_mul_units_squares (v.adicCompletion F) w _ hπ hD.1`.

Rewrite using `[sqIdx_sqSub_eq_comap, Subgroup.index_comap]`. Rewrite `hE` using `[← Subgroup.relIndex_top_right]`. Use `⟨fun h => hE.1 (Subgroup.relIndex_eq_zero_of_le_right le_top h), ?_⟩` and prove the remaining obligations. Use `(Subgroup.relIndex_le_of_le_right le_top hE.1).trans (hE.2.trans ?_)` and prove the remaining obligations. Establish `hp : R.card ^ e ≤ Ideal.absNorm v.asIdeal ^ e` using `Nat.pow_le_pow_left hcard e`.

Use `hD.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem index_sqSub_adicCompletion_le : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (e : ℕ), v.valuation F 2 = WithZero.exp (-(e : ℤ)) → (sqSub (algebraMap F (v.adicCompletion F))).index ≠ 0 ∧ (sqSub (algebraMap F (v.adicCompletion F))).index ≤ 4 * Ideal.absNorm v.asIdeal ^ e := by
  intro F _ _ v e he
  obtain ⟨⟨π, -, hπ⟩, hval, -, R, hcard, -, hR⟩ := GlobalTheory.T.exists_global_uniformizer_residue_representatives F v
  have h2 : Valued.v (2 : v.adicCompletion F) = WithZero.exp (-(e : ℤ)) := by
    rw [← he, ← hval, map_ofNat (algebraMap F (v.adicCompletion F))]
  have hsq := GlobalTheory.T.higherUnits_le_squares_higherUnits F v e h2
  set w : Valuation (v.adicCompletion F) ℤᵐ⁰ := Valued.v with hw
  have hA := sqIdx_relIndex_hiUnits_add w _ R hπ hR (e + 1) e
  have hB := sqIdx_relIndex_hiUnits_add w _ R hπ hR 0 (e + 1)
  rw [show e + 1 + e = 2 * e + 1 by ring] at hA
  rw [zero_add] at hB
  have hC0 : (sqs (hiUnits w (e + 1))).relIndex (hiUnits w (e + 1)) ≠ 0 :=
    fun h => hA.1 (Subgroup.relIndex_eq_zero_of_le_left hsq h)
  have hC : (sqs (hiUnits w (e + 1))).relIndex (hiUnits w (e + 1)) ≤ R.card ^ e :=
    (Subgroup.relIndex_le_of_le_left hsq hA.1).trans hA.2
  have hD := GlobalTheory.T.relIndex_squares_le_two_mul_of_subgroup (v.adicCompletion F)ˣ (hiUnits w 0) (hiUnits w (e + 1)) (-1)
    (sqIdx_hiUnits_anti w (by omega)) hB.1 (fun a ha => by
      have h : (a : v.adicCompletion F) ^ 2 = 1 := by
        rw [← Units.val_pow_eq_pow_val, ha, Units.val_one]
      rcases sq_eq_one_iff.mp h with h | h
      · left; exact Units.ext h
      · right; exact Units.ext (by simpa using h)) hC0
  have hE := GlobalTheory.T.index_squares_le_two_mul_units_squares (v.adicCompletion F) w _ hπ hD.1
  rw [sqIdx_sqSub_eq_comap, Subgroup.index_comap]
  rw [← Subgroup.relIndex_top_right] at hE
  refine ⟨fun h => hE.1 (Subgroup.relIndex_eq_zero_of_le_right le_top h), ?_⟩
  refine (Subgroup.relIndex_le_of_le_right le_top hE.1).trans (hE.2.trans ?_)
  have hp : R.card ^ e ≤ Ideal.absNorm v.asIdeal ^ e := Nat.pow_le_pow_left hcard e
  have := hD.2
  omega

end GlobalTheory.QNorm
