import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharNegEqOne

open Filter Topology

namespace GlobalTheory.LinSchur

open Classical in

/- English proof (translation)
Establish `hK : IsCompact (tsupport f)` using `hf.2`. Take `⟨F0, -, hcov⟩` from `hK.elim_nhds_subcover (fun x => {Y | Y - x ∈ L}) (fun x _ => (hL.preimage (continuous_id.sub continuous_const)).mem_nhds (by simp))`. Use `⟨(F0.image (QuotientAddGroup.mk (s := L))).image Quotient.out, ?_⟩` and prove the remaining obligations. Establish `hmk : ∀ y ∈ (F0.image (QuotientAddGroup.mk (s` using `L))).image Quotient.out, ∀ Y : X, Y - y ∈ L ↔ (QuotientAddGroup.mk Y : X ⧸ L) = QuotientAddGroup.mk y := by`. Introduce `y _ Y`.

Rewrite using `[QuotientAddGroup.eq, ← neg_mem_iff]`. Simplify using `[sub_eq_add_neg, add_comm]`. Use function extensionality and compare the values at `Y`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.LinSchur.cind]`. Distinguish the cases in `hex : ∃ y ∈ (F0.image (QuotientAddGroup.mk (s := L))).image Quotient.out, Y - y ∈ L`.

Take `⟨y, hy, hYy⟩` from `hex`. Rewrite using `[Finset.sum_eq_single y]`. Rewrite using `[if_pos hYy, mul_one]`. Use `hper y (Y - y) hYy` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`.

Conclude with `this`. Introduce `y' hy' hne`. Rewrite using `[if_neg, mul_zero]`. Introduce `hY'`. Apply `hne` to reduce the goal to its premises.

Take `⟨q', -, rfl⟩` from `Finset.mem_image.mp hy'`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.mp hy`. Establish `e1` using `(hmk _ hy' Y).mp hY'`. Establish `e2` using `(hmk _ hy Y).mp hYy`. Simplify using `only [QuotientAddGroup.out_eq'] at e1 e2`.

Rewrite using `[← e1, ← e2]`. Introduce `h`. Conclude with `absurd hy h`. Use `push_neg at hex`. Rewrite using `[Finset.sum_eq_zero (fun y hy => by rw [if_neg (hex y hy), mul_zero])]`.

Apply `image_eq_zero_of_notMem_tsupport` to reduce the goal to its premises. Introduce `hY`. Use `hcov hY` as an intermediate fact. Simplify using `only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at this`. Take `⟨y0, hy0, hYy0⟩` from `this`.

Establish `hmem : (QuotientAddGroup.mk y0 : X ⧸ L).out ∈ (F0.image (QuotientAddGroup.mk (s` using `L))).image Quotient.out := Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr ⟨y0, hy0, rfl⟩, rfl⟩`. Apply `hex _ hmem` to reduce the goal to its premises. Rewrite using `[hmk _ hmem, QuotientAddGroup.out_eq']`. Rewrite using `[← QuotientAddGroup.eq_iff_sub_mem.mpr hYy0]`.
-/
theorem exists_finset_eq_sum_cind {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (L : AddSubgroup X) (hL : IsOpen (L : Set X)) (f : X → ℂ) (hf : f ∈ GlobalTheory.WeilM.SB X)
    (hper : ∀ Y, ∀ C ∈ L, f (Y + C) = f Y) :
    ∃ F : Finset X, f = ∑ y ∈ F, f y • GlobalTheory.LinSchur.cind L y := by
  have hK : IsCompact (tsupport f) := hf.2
  obtain ⟨F0, -, hcov⟩ := hK.elim_nhds_subcover (fun x => {Y | Y - x ∈ L}) (fun x _ =>
    (hL.preimage (continuous_id.sub continuous_const)).mem_nhds (by simp))
  refine ⟨(F0.image (QuotientAddGroup.mk (s := L))).image Quotient.out, ?_⟩
  have hmk : ∀ y ∈ (F0.image (QuotientAddGroup.mk (s := L))).image Quotient.out, ∀ Y : X,
      Y - y ∈ L ↔ (QuotientAddGroup.mk Y : X ⧸ L) = QuotientAddGroup.mk y := by
    intro y _ Y
    rw [QuotientAddGroup.eq, ← neg_mem_iff]
    simp [sub_eq_add_neg, add_comm]
  funext Y
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.LinSchur.cind]
  by_cases hex : ∃ y ∈ (F0.image (QuotientAddGroup.mk (s := L))).image Quotient.out, Y - y ∈ L
  · obtain ⟨y, hy, hYy⟩ := hex
    rw [Finset.sum_eq_single y]
    · rw [if_pos hYy, mul_one]
      have := hper y (Y - y) hYy
      rw [add_sub_cancel] at this
      exact this
    · intro y' hy' hne
      rw [if_neg, mul_zero]
      intro hY'
      apply hne
      obtain ⟨q', -, rfl⟩ := Finset.mem_image.mp hy'
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hy
      have e1 := (hmk _ hy' Y).mp hY'
      have e2 := (hmk _ hy Y).mp hYy
      simp only [QuotientAddGroup.out_eq'] at e1 e2
      rw [← e1, ← e2]
    · intro h; exact absurd hy h
  · push_neg at hex
    rw [Finset.sum_eq_zero (fun y hy => by rw [if_neg (hex y hy), mul_zero])]
    apply image_eq_zero_of_notMem_tsupport
    intro hY
    have := hcov hY
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at this
    obtain ⟨y0, hy0, hYy0⟩ := this
    have hmem : (QuotientAddGroup.mk y0 : X ⧸ L).out ∈
        (F0.image (QuotientAddGroup.mk (s := L))).image Quotient.out :=
      Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr ⟨y0, hy0, rfl⟩, rfl⟩
    apply hex _ hmem
    rw [hmk _ hmem, QuotientAddGroup.out_eq']
    rw [← QuotientAddGroup.eq_iff_sub_mem.mpr hYy0]

end GlobalTheory.LinSchur

/- English proof (translation)
Introduce `L hL f hf hp` and use `GlobalTheory.LinSchur.exists_finset_eq_sum_cind L hL f hf hp`.
-/
example : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] (L : AddSubgroup X), IsOpen (L : Set X) → ∀ f ∈ GlobalTheory.WeilM.SB X, (∀ Y, ∀ C ∈ L, f (Y + C) = f Y) → ∃ F : Finset X, f = ∑ y ∈ F, f y • GlobalTheory.LinSchur.cind L y :=
  fun L hL f hf hp => GlobalTheory.LinSchur.exists_finset_eq_sum_cind L hL f hf hp
