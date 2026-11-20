import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module Matrix

/- English proof (translation)
Introduce `A hA e a T ha hT`. Establish `hmem : ∀ i, (a i : E) ∈ A` using `fun i => hA ⟨a i, rfl⟩`. Set `b : Fin (finrank ℚ E) → A` to `fun i => ⟨a i, hmem i⟩`. Establish `hb : ∀ i, b i = ∑ j, T i j • e j`. Introduce `i`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[b, hT i]`. Establish `hdet : T.det ≠ 0`. Introduce `h0`. Establish `h0' : ((Int.castRingHom ℚ).mapMatrix T).det = 0`.

Rewrite using `[← RingHom.map_det, h0, map_zero]`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_vecMul_eq_zero_iff.mpr h0'`. Establish `hsum : ∑ i, v i • (a i : E) = 0`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[hT i, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Int.cast_smul_eq_zsmul ℚ, smul_smul]`. Use `_ = ∑ j, (∑ i, v i * (T i j : ℚ)) • (e j : E) := by`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_smul]`. Use `_ = 0 := by`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Use `congrFun hv j` as an intermediate fact.

Simplify using `only [vecMul, dotProduct, RingHom.mapMatrix_apply, map_apply, eq_intCast, Pi.zero_apply] at this`. Rewrite using `[this, zero_smul]`. Conclude with `hv0 (funext fun i => Fintype.linearIndependent_iff.mp ha v hsum i)`. Establish `hliE : LinearIndependent ℤ (fun i => (a i : E))` using `ha.restrict_scalars' ℤ`. Establish `hli : LinearIndependent ℤ b` using `LinearIndependent.of_comp (A.subtype.toIntLinearMap) hliE`.

Establish `: Module.Free ℤ A` using `Module.Free.of_basis e`. Establish `: Module.Finite ℤ A` using `Module.Finite.of_basis e`. Use `set N := Submodule.span ℤ (Set.range b) with hN`. Set `bN` to `Basis.span hli`. Establish `hbN : ((↑) ∘ bN : Fin (finrank ℚ E) → A) = b` using `funext fun i => congrArg Subtype.val (Basis.span_apply hli i)`.

Establish `hcard` using `Submodule.natAbs_det_basis_change e N bN`. Rewrite `hcard` using `[hbN]`. Establish `hdetb : e.det b = T.det`. Rewrite using `[Basis.det_apply, ← Matrix.det_transpose]`. Use `congr 1`.

Use extensionality with `i j`. Rewrite using `[Matrix.transpose_apply, Basis.toMatrix_apply, hb i, map_sum]`. Simplify using `[Finsupp.single_apply]`. Rewrite `hcard` using `[hdetb]`. Establish `hle : N.toAddSubgroup ≤ (intSubgroup E).addSubgroupOf A`.

Establish `: N ≤ ((intSubgroup E).addSubgroupOf A).toIntSubmodule`. Rewrite using `[hN, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Use `show b i ∈ (intSubgroup E).addSubgroupOf A`. Rewrite using `[AddSubgroup.mem_addSubgroupOf]`.

Conclude with `⟨a i, rfl⟩`. Conclude with `this`. Establish `hidx : N.toAddSubgroup.index = T.det.natAbs` using `hcard.symm`. Establish `hdvd` using `AddSubgroup.index_dvd_of_le hle`. Rewrite `hdvd` using `[hidx]`.

Establish `hle' : (intSubgroup E).relIndex A ≤ T.det.natAbs` using `Nat.le_of_dvd (Int.natAbs_pos.mpr hdet) hdvd`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem IndexLeDet.proof (E : Type*) [Field E] [NumberField E] : IndexLeDet.Statement E := by
  classical
  intro A hA e a T ha hT
  have hmem : ∀ i, (a i : E) ∈ A := fun i => hA ⟨a i, rfl⟩
  let b : Fin (finrank ℚ E) → A := fun i => ⟨a i, hmem i⟩
  have hb : ∀ i, b i = ∑ j, T i j • e j := by
    intro i
    apply Subtype.ext
    simp [b, hT i]

  have hdet : T.det ≠ 0 := by
    intro h0
    have h0' : ((Int.castRingHom ℚ).mapMatrix T).det = 0 := by
      rw [← RingHom.map_det, h0, map_zero]
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0'
    have hsum : ∑ i, v i • (a i : E) = 0 := by
      calc ∑ i, v i • (a i : E)
          = ∑ i, ∑ j, (v i * (T i j : ℚ)) • (e j : E) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hT i, Finset.smul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul]
        _ = ∑ j, (∑ i, v i * (T i j : ℚ)) • (e j : E) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_smul]
        _ = 0 := by
            refine Finset.sum_eq_zero fun j _ => ?_
            have := congrFun hv j
            simp only [vecMul, dotProduct, RingHom.mapMatrix_apply, map_apply, eq_intCast,
              Pi.zero_apply] at this
            rw [this, zero_smul]
    exact hv0 (funext fun i => Fintype.linearIndependent_iff.mp ha v hsum i)

  have hliE : LinearIndependent ℤ (fun i => (a i : E)) := ha.restrict_scalars' ℤ
  have hli : LinearIndependent ℤ b :=
    LinearIndependent.of_comp (A.subtype.toIntLinearMap) hliE
  have : Module.Free ℤ A := Module.Free.of_basis e
  have : Module.Finite ℤ A := Module.Finite.of_basis e
  set N := Submodule.span ℤ (Set.range b) with hN
  let bN := Basis.span hli
  have hbN : ((↑) ∘ bN : Fin (finrank ℚ E) → A) = b := funext fun i => congrArg Subtype.val (Basis.span_apply hli i)
  have hcard := Submodule.natAbs_det_basis_change e N bN
  rw [hbN] at hcard
  have hdetb : e.det b = T.det := by
    rw [Basis.det_apply, ← Matrix.det_transpose]
    congr 1
    ext i j
    rw [Matrix.transpose_apply, Basis.toMatrix_apply, hb i, map_sum]
    simp [Finsupp.single_apply]
  rw [hdetb] at hcard

  have hle : N.toAddSubgroup ≤ (intSubgroup E).addSubgroupOf A := by
    have : N ≤ ((intSubgroup E).addSubgroupOf A).toIntSubmodule := by
      rw [hN, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      show b i ∈ (intSubgroup E).addSubgroupOf A
      rw [AddSubgroup.mem_addSubgroupOf]
      exact ⟨a i, rfl⟩
    exact this
  have hidx : N.toAddSubgroup.index = T.det.natAbs := hcard.symm
  have hdvd := AddSubgroup.index_dvd_of_le hle
  rw [hidx] at hdvd
  have hle' : (intSubgroup E).relIndex A ≤ T.det.natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hdet) hdvd
  calc ((intSubgroup E).relIndex A : ℝ) ≤ (T.det.natAbs : ℝ) := by exact_mod_cast hle'
    _ = |(T.det : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]

end GroundTheory.Heights₂.Heights.FiniteCovolume
