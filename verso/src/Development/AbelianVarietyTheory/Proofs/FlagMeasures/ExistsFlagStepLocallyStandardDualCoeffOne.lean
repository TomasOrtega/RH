import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NormAdditiveCharacterTypePrimeEqOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalIsotropicFlagMovesStepIntoPrevStatement

open Formalism.MainNotions.S

namespace GlobalTheory

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M V _ _ H r Fr n hn L a`. Establish `hiso : ∀ b c : Fin r, H.h (Fr.e b) (Fr.e c) = 0` using `fun b c => Fr.h_iso b.castSucc c.castSucc (Or.inl (Fin.castSucc_lt_last b).ne)`. Establish `hes : ∀ b c : Fin r, H.h (Fr.e b) (Fr.es c) = if b = c then 1 else 0` using `fun b c => Fr.h_es b c`. Establish `hlam : Fr.e a ∈ Fr.LamStd L`. Use `Submodule.subset_span ⟨fun b => ?_, fun b => ?_, ⟨0, ?_, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[hes] split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`. Rewrite using `[hiso]`. Conclude with `zero_mem _`.

Simplify using `only [Formalism.MainNotions.S.LocNG.FrameD.prF, hes, hiso, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const_zero, sub_self, ZeroMemClass.coe_zero]`. Rewrite using `[map_zero]`. Conclude with `L.zero_mem`. Establish `hperp : ∀ w ∈ Fr.Fj a.val, H.h w (Fr.es a) = 0`. Introduce `w hw`.

Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨b, hb, rfl⟩` from `hx`. Rewrite using `[hes, if_neg (Fin.ne_of_val_ne (Nat.ne_of_lt hb))]`. Consider the case `zero => exact H.h_zero_left _`.

Consider the case `add x y _ _ hx hy => rw [H.h_add_left, hx, hy, add_zero]`. Consider the case `smul c x _ hx => rw [H.h_smul_left, hx, mul_zero]`. Establish `hmem : Fr.e a ∈ Fr.Fj (a.val + 1)` using `Submodule.subset_span ⟨a, Nat.lt_succ_self _, rfl⟩`. Establish `hle : a.val + 1 ≤ r` using `a.isLt`. Establish `hdiff : n (Fr.e a) - Fr.e a ∈ Fr.Fj a.val`.

Use `(T.unipotentRadical_isotropicFlag_moves_step_into_prev Fr n hn (a.val + 1) hle (Fr.e a) hmem).1` as an intermediate fact. Simplify using `using this`. Establish `hmono : Fr.Fj a.val ≤ Fr.Fj (a.val + 1)` using `Submodule.span_mono (Set.image_mono fun b (hb : b.val < a.val) => Nat.lt_succ_of_lt hb)`. Use `⟨n (Fr.e a), Submodule.mem_map.mpr ⟨Fr.e a, hlam, rfl⟩, ?_, ?_⟩` and prove the remaining obligations. Use `(Fr.Fj (a.val + 1)).add_mem (hmono hdiff) hmem` as an intermediate fact.

Simplify using `using this`. Establish `hsplit : n (Fr.e a) = (n (Fr.e a) - Fr.e a) + Fr.e a` using `by abel`. Rewrite using `[hsplit, H.h_add_left, hperp _ hdiff, hes, if_pos rfl, zero_add]`.
-/
theorem locStd_exists_flag_coef_one : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : Formalism.MainNotions.S.Loc.HermSp M V} {r : ℕ} (Fr : Formalism.MainNotions.S.LocNG.FrameD H r) (n : V ≃ₗ[E] V), n ∈ Fr.N → ∀ (L : Submodule M.L.O (H.Wb Fr.f)) (a : Fin r), ∃ v ∈ Formalism.MainNotions.S.LocNG.img n (Fr.LamStd L), v ∈ Fr.Fj (a.val + 1) ∧ H.h v (Fr.es a) = 1 := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r Fr n hn L a

  have hiso : ∀ b c : Fin r, H.h (Fr.e b) (Fr.e c) = 0 := fun b c =>
    Fr.h_iso b.castSucc c.castSucc (Or.inl (Fin.castSucc_lt_last b).ne)
  have hes : ∀ b c : Fin r, H.h (Fr.e b) (Fr.es c) = if b = c then 1 else 0 := fun b c =>
    Fr.h_es b c

  have hlam : Fr.e a ∈ Fr.LamStd L := by
    refine Submodule.subset_span ⟨fun b => ?_, fun b => ?_, ⟨0, ?_, ?_⟩⟩
    · rw [hes]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · rw [hiso]
      exact zero_mem _
    · simp only [Formalism.MainNotions.S.LocNG.FrameD.prF, hes, hiso, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const_zero, sub_self,
        ZeroMemClass.coe_zero]
    · rw [map_zero]
      exact L.zero_mem

  have hperp : ∀ w ∈ Fr.Fj a.val, H.h w (Fr.es a) = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, rfl⟩ := hx
      rw [hes, if_neg (Fin.ne_of_val_ne (Nat.ne_of_lt hb))]
    | zero => exact H.h_zero_left _
    | add x y _ _ hx hy => rw [H.h_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [H.h_smul_left, hx, mul_zero]

  have hmem : Fr.e a ∈ Fr.Fj (a.val + 1) :=
    Submodule.subset_span ⟨a, Nat.lt_succ_self _, rfl⟩
  have hle : a.val + 1 ≤ r := a.isLt
  have hdiff : n (Fr.e a) - Fr.e a ∈ Fr.Fj a.val := by
    have := (T.unipotentRadical_isotropicFlag_moves_step_into_prev Fr n hn (a.val + 1) hle (Fr.e a) hmem).1
    simpa using this
  have hmono : Fr.Fj a.val ≤ Fr.Fj (a.val + 1) :=
    Submodule.span_mono (Set.image_mono fun b (hb : b.val < a.val) => Nat.lt_succ_of_lt hb)
  refine ⟨n (Fr.e a), Submodule.mem_map.mpr ⟨Fr.e a, hlam, rfl⟩, ?_, ?_⟩
  · have := (Fr.Fj (a.val + 1)).add_mem (hmono hdiff) hmem
    simpa using this
  · have hsplit : n (Fr.e a) = (n (Fr.e a) - Fr.e a) + Fr.e a := by abel
    rw [hsplit, H.h_add_left, hperp _ hdiff, hes, if_pos rfl, zero_add]

end GlobalTheory
