import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

/- English proof (translation)
Use `⟨fun i j hij => ?_, fun i => ?_, fun a h => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero (fun k _ => ?_)` and prove the remaining obligations. Break down `lt_or_ge k i with hk | hk` into its components or cases. Rewrite using `[hX0 i k hk, zero_mul]`.

Rewrite using `[hY0 k j (lt_of_lt_of_le hij hk), mul_zero]`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single i]`. Simplify using `[hX1, hY1]`. Introduce `k _ hk`. Break down `lt_or_gt_of_ne hk with hk | hk` into its components or cases.

Rewrite using `[hX0 i k hk, zero_mul]`. Rewrite using `[hY0 k i hk, mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`. Use `set b : Fin n := ⟨a.val + 1, h⟩ with hb`.

Establish `hab : a ≠ b`. Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact. Simplify using `[hb] at this`. Rewrite using `[Matrix.mul_apply, Fintype.sum_eq_add a b hab]`.

Rewrite using `[hX1, hY1, one_mul, mul_one, add_comm]`. Introduce and unpack `k ⟨hka, hkb⟩`. Break down `lt_or_ge k a with hk | hk` into its components or cases. Rewrite using `[hX0 a k hk, zero_mul]`. Establish `hk' : a.val < k.val` using `lt_of_le_of_ne hk (fun e => hka (Fin.ext e.symm))`.

Establish `hk'' : b.val < k.val`. Establish `: k.val ≠ a.val + 1` using `fun e => hkb (Fin.ext (by simp [hb, e]))`. Simplify using `[hb]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hY0 k b hk'', mul_zero]`.
-/
theorem unitriangular_mul_superdiagonal_add {E : Type} [Field E] {n : ℕ} (X Y : Matrix (Fin n) (Fin n) E)
    (hX0 : ∀ i j, j < i → X i j = 0) (hX1 : ∀ i, X i i = 1)
    (hY0 : ∀ i j, j < i → Y i j = 0) (hY1 : ∀ i, Y i i = 1) :
    (∀ i j, j < i → (X * Y) i j = 0) ∧ (∀ i, (X * Y) i i = 1) ∧
    (∀ (a : Fin n) (h : a.val + 1 < n), (X * Y) a ⟨a.val + 1, h⟩ = X a ⟨a.val + 1, h⟩ + Y a ⟨a.val + 1, h⟩) := by
  refine ⟨fun i j hij => ?_, fun i => ?_, fun a h => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rcases lt_or_ge k i with hk | hk
    · rw [hX0 i k hk, zero_mul]
    · rw [hY0 k j (lt_of_lt_of_le hij hk), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · simp [hX1, hY1]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hk | hk
      · rw [hX0 i k hk, zero_mul]
      · rw [hY0 k i hk, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  · set b : Fin n := ⟨a.val + 1, h⟩ with hb
    have hab : a ≠ b := by
      intro e; have := congrArg Fin.val e; simp [hb] at this
    rw [Matrix.mul_apply, Fintype.sum_eq_add a b hab]
    · rw [hX1, hY1, one_mul, mul_one, add_comm]
    · rintro k ⟨hka, hkb⟩
      rcases lt_or_ge k a with hk | hk
      · rw [hX0 a k hk, zero_mul]
      · have hk' : a.val < k.val := lt_of_le_of_ne hk (fun e => hka (Fin.ext e.symm))
        have hk'' : b.val < k.val := by
          have : k.val ≠ a.val + 1 := fun e => hkb (Fin.ext (by simp [hb, e]))
          simp [hb]; omega
        rw [hY0 k b hk'', mul_zero]

/- English proof (translation)
Introduce `E _ n B C hB0 hB1 hC0 hC1`. Take `⟨hD0, hD1⟩` from `Formalism.L2.SG.TermLoc.inv_unitri C hC0 hC1`. Take `⟨hP0, hP1, hP2⟩` from `unitriangular_mul_superdiagonal_add B C⁻¹ hB0 hB1 hD0 hD1`. Take `⟨-, -, hQ2⟩` from `unitriangular_mul_superdiagonal_add C C⁻¹ hC0 hC1 hD0 hD1`. Establish `hdet : IsUnit C.det`.

Rewrite using `[Matrix.det_of_upperTriangular (fun i j hij => hC0 i j hij)]`. Simplify using `[hC1]`. Establish `hCC : C * C⁻¹ = 1` using `Matrix.mul_nonsing_inv C hdet`. Use `⟨hP0, hP1, ?_⟩` and prove the remaining obligations. Unfold `Formalism.L2.SG.PairVal.sgUp`.

Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Use `split_ifs with h`. Establish `hq` using `hQ2 a h`. Rewrite `hq` using `[hCC, Matrix.one_apply_ne]`.

Rewrite using `[hP2 a h]`. Take the linear combination `-hq`. Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact. Simplify using `at this`.

Simplify using the standard rewrite rules.
-/
theorem unitri_mul_inv_sgUp : ∀ {E : Type} [Field E] {n : ℕ} (B C : Matrix (Fin n) (Fin n) E), (∀ i j, j < i → B i j = 0) → (∀ i, B i i = 1) → (∀ i j, j < i → C i j = 0) → (∀ i, C i i = 1) → (∀ i j, j < i → (B * C⁻¹) i j = 0) ∧ (∀ i, (B * C⁻¹) i i = 1) ∧ Formalism.L2.SG.PairVal.sgUp (B * C⁻¹) = Formalism.L2.SG.PairVal.sgUp B - Formalism.L2.SG.PairVal.sgUp C := by
  intro E _ n B C hB0 hB1 hC0 hC1
  obtain ⟨hD0, hD1⟩ := Formalism.L2.SG.TermLoc.inv_unitri C hC0 hC1
  obtain ⟨hP0, hP1, hP2⟩ := unitriangular_mul_superdiagonal_add B C⁻¹ hB0 hB1 hD0 hD1
  obtain ⟨-, -, hQ2⟩ := unitriangular_mul_superdiagonal_add C C⁻¹ hC0 hC1 hD0 hD1
  have hdet : IsUnit C.det := by
    rw [Matrix.det_of_upperTriangular (fun i j hij => hC0 i j hij)]; simp [hC1]
  have hCC : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C hdet
  refine ⟨hP0, hP1, ?_⟩
  unfold Formalism.L2.SG.PairVal.sgUp
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  split_ifs with h
  · have hq := hQ2 a h
    rw [hCC, Matrix.one_apply_ne] at hq
    · rw [hP2 a h]; linear_combination -hq
    · intro e; have := congrArg Fin.val e; simp at this
  · simp

end GlobalTheory
