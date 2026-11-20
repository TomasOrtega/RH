import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarmonicHighestWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFockJointHarmonicsHighestWeightOfShape
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointShapeUniqueAndDegWEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionHomogeneousEigenvector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinFirst
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint

noncomputable section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR MvPolynomial GlobalTheory.JointHarm

namespace GlobalTheory.HoweR.MultOne

variable {P Q R S : ℕ}

/- English proof (translation)
Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem g hg`. Take `⟨X, f, rfl⟩` from `hg`. Use `Submodule.subset_span ⟨X, fockAct2 P Q R S Y f, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, map_smul, GlobalTheory.FockAlg.MinFirst.fockAct1_fockAct2_commute]`.

Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul c a _ ha => rw [map_smul]`. Conclude with `Submodule.smul_mem _ _ ha`.
-/
theorem coinv_stable2 (x : ℂ) (Y : Mat R S) {v : Pol P Q R S} (hv : v ∈ coinv P Q R S x) :
    fockAct2 P Q R S Y v ∈ coinv P Q R S x := by
  induction hv using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨X, f, rfl⟩ := hg
    refine Submodule.subset_span ⟨X, fockAct2 P Q R S Y f, ?_⟩
    rw [map_sub, map_smul, GlobalTheory.FockAlg.MinFirst.fockAct1_fockAct2_commute]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

/- English proof (translation)
Distinguish the cases in `h0 : f = 0`. Substitute `h0` using the available equality. Introduce `Z _`. Simplify using `[minusPart]`. Take `⟨d, hd, hdf⟩` from `isSide_two.homog_of_hw Prod.swap_bijective ⟨h0, hw⟩ ((mem_harm2 f).1 h2)`.

Establish `hdeg` using `(GlobalTheory.JointShapeUniq.jointShape_unique_deg P Q R S _ _ _ _ hJ hJ).2`. Introduce `Z hZ`. Rewrite using `[fockAct2_eq, (parts_omAct (odd_kron2 hZ) f).2]`. Distinguish the cases in `hd2 : d < 2`. Conclude with `dnOp_low _ d hd2 f hdf`.

Assume the negation of the conclusion as `hne`. Establish `h1` using `isSide_one.degW_le Function.bijective_id (dnOp_homog _ d f hdf) (GlobalTheory.FockScalarType.isHW_of_mem hne (GlobalTheory.FockScalarType.dnOp_mem_charSub hZ hdf hc))`. Rewrite `h1` using `[hdeg, ← hd]`. Establish `e : ((d - 2 : ℕ) : ℚ) = (d : ℚ) - 2` using `by push_cast [Nat.cast_sub (by omega : 2 ≤ d)]; ring`. Rewrite `h1` using `[e]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem fockHarmonicsSecondMember_of_jointShape_highestWeight {x : ℚ} {μ' : Ix R S → ℚ} (hJ : JointShape P Q R S (fun _ => x) μ') {f : Pol P Q R S}
    (h2 : f ∈ harm2 P Q R S) (hc : f ∈ GlobalTheory.FockScalarType.charSub P Q R S x)
    (hw : f ∈ hwSub (fockAct2 P Q R S) μ') : f ∈ harm1 P Q R S := by
  by_cases h0 : f = 0
  · subst h0; intro Z _; simp [minusPart]
  obtain ⟨d, hd, hdf⟩ := isSide_two.homog_of_hw Prod.swap_bijective ⟨h0, hw⟩ ((mem_harm2 f).1 h2)
  have hdeg := (GlobalTheory.JointShapeUniq.jointShape_unique_deg P Q R S _ _ _ _ hJ hJ).2
  intro Z hZ
  rw [fockAct2_eq, (parts_omAct (odd_kron2 hZ) f).2]
  by_cases hd2 : d < 2
  · exact dnOp_low _ d hd2 f hdf
  by_contra hne
  have h1 := isSide_one.degW_le Function.bijective_id (dnOp_homog _ d f hdf)
    (GlobalTheory.FockScalarType.isHW_of_mem hne (GlobalTheory.FockScalarType.dnOp_mem_charSub hZ hdf hc))
  rw [hdeg, ← hd] at h1
  have e : ((d - 2 : ℕ) : ℚ) = (d : ℚ) - 2 := by push_cast [Nat.cast_sub (by omega : 2 ≤ d)]; ring
  rw [e] at h1
  linarith

end GlobalTheory.HoweR.MultOne

namespace GlobalTheory.HoweR

open GlobalTheory.HoweR.MultOne in

/- English proof (translation)
Introduce `P Q R S x μ' hJ`. Use `set L := hwSub (fockAct1 P Q R S) (fun _ => x) ⊓ hwSub (fockAct2 P Q R S) μ' ⊓ Submodule.span ℂ (jointHarm P Q R S) with hL`. Take `⟨v, -, hv⟩` from `finrank_eq_one_iff'.1 (GlobalTheory.JointHarm.finrank_joint_highest_of_shape P Q R S _ _ hJ)`. Use `⟨v.1, fun g hg => ?_⟩` and prove the remaining obligations. Use `set C := coinv P Q R S (x : ℂ) with hC`.

Set `pr` to `C.mkQ`. Establish `hker : ∀ w, pr w = 0 ↔ w ∈ C` using `fun w => by rw [← LinearMap.mem_ker, Submodule.ker_mkQ]`. Establish `hpr1 : ∀ X f, pr (fockAct1 P Q R S X f) = ((x : ℂ) * X.trace) • pr f`. Introduce `X f`. Rewrite using `[← map_smul, ← sub_eq_zero, ← map_sub]`.

Conclude with `(hker _).2 (Submodule.subset_span ⟨X, f, rfl⟩)`. Establish `hpr2 : ∀ Y w w', pr w = pr w' → pr (fockAct2 P Q R S Y w) = pr (fockAct2 P Q R S Y w')`. Introduce `Y w w' h`. Rewrite `h` using `[← sub_eq_zero, ← map_sub]`. Rewrite using `[← sub_eq_zero, ← map_sub, ← map_sub]`.

Conclude with `(hker _).2 (coinv_stable2 _ Y ((hker _).1 h))`. Establish `hPC : ∀ Z : Mat P Q, IsPC Z → ∀ f, pr (fockAct1 P Q R S Z f) = 0`. Introduce `Z hZ f`. Rewrite using `[hpr1, GlobalTheory.HarmLift.trace_PC hZ, mul_zero, zero_smul]`. Take `⟨h, hh, hprh⟩` from `GlobalTheory.HarmLift.lemA P Q R S _ pr hPC g`.

Take `⟨H0, hfin, hH0, hharm, hs1, hs2⟩` from `GlobalTheory.HarmLift.lemB P Q R S h hh`. Take `⟨ι, hιIP, hιinj⟩` from `GlobalTheory.FischerParts.exists_fockIP (Ln P Q R S)`. Set `A : Set (Module.End ℂ (Pol P Q R S))` to `{a | (∃ X, IsKC X ∧ a = fockAct1 P Q R S X) ∨ ∃ Y, IsKC Y ∧ a = fockAct2 P Q R S Y}`. Establish `hadj` using `GlobalTheory.FockAdj.fock_adjoints P Q R S _ ι hιIP`. Take `⟨c, hc, hcpr, hceig⟩` from `GlobalTheory.HarmLift.lemC (Pol P Q R S) (Pol P Q R S ⧸ C) _ ι hιinj pr H0 hfin A (by`.

Introduce and unpack `a (⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩) w hw`. Use `exacts [hs1 X hX w hw, hs2 Y hY w hw])`. Use the proof step `(by`. Introduce and unpack `a (⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩) w _ hw`. Rewrite using `[hpr1, hw, smul_zero]`.

Rewrite using `[hpr2 Y w 0 (by rw [hw, map_zero]), map_zero, map_zero])`. Use the proof step `(by`. Introduce and unpack `a (⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩)`. Conclude with `⟨_, Or.inl ⟨_, GlobalTheory.HarmLift.isKC_adjZ hX, rfl⟩, hadj.2.1 X⟩`. Conclude with `⟨_, Or.inr ⟨_, GlobalTheory.HarmLift.isKC_adjZ hY, rfl⟩, hadj.2.2 Y⟩)`.

Use `h hH0`. Rewrite `hcpr` using `[hprh]`. Establish `hcc : c ∈ GlobalTheory.FockScalarType.charSub P Q R S x` using `fun X hX => hceig _ (Or.inl ⟨X, hX, rfl⟩) _ (by rw [hpr1])`. Establish `hcw : c ∈ hwSub (fockAct2 P Q R S) μ'`. Establish `hg2` using `hg`.

Simplify using `only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hg2 ⊢`. Use `⟨fun a => ?_, fun a b hab => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `have hs : sameBlock a a := by rcases a with a | a <;> simp [sameBlock]`. Use `hceig _ (Or.inr ⟨_, GlobalTheory.HarmLift.isKC_Eab hs, rfl⟩) _ ?_` and prove the remaining obligations. Rewrite using `[hpr2 (Eab a a) c g hcpr, hg2.1 a, map_smul, hcpr]`.

Apply the tactic sequence `have hs : sameBlock a b := by revert hab; rcases a with a | a <;> rcases b with b | b <;> simp [posC, sameBlock]`. Rewrite using `[hceig _ (Or.inr ⟨_, GlobalTheory.HarmLift.isKC_Eab hs, rfl⟩) 0 (by rw [hpr2 (Eab a b) c g hcpr, hg2.2 a b hab, map_zero, zero_smul]), zero_smul]`. Establish `hcJ : c ∈ jointHarm P Q R S` using `⟨hharm c hc, fockHarmonicsSecondMember_of_jointShape_highestWeight hJ (hharm c hc) hcc hcw⟩`. Establish `hcL : c ∈ L`. Distinguish the cases in `h0 : c = 0`.

Rewrite using `[h0]`. Conclude with `L.zero_mem`. Conclude with `⟨⟨(GlobalTheory.FockScalarType.isHW_of_mem h0 hcc).2, hcw⟩, Submodule.subset_span hcJ⟩`. Take `⟨t, ht⟩` from `hv ⟨c, hcL⟩`. Establish `hct : c = t • v.1`.

Use `congrArg Subtype.val ht` as an intermediate fact. Simplify using `using this.symm`. Establish `hgc : g - c ∈ C` using `(hker _).1 (by rw [map_sub, hcpr, sub_self])`. Rewrite using `[← sub_add_cancel g c, add_comm]`. Conclude with `Submodule.add_mem_sup (hct ▸ Submodule.smul_mem _ t (Submodule.mem_span_singleton_self _)) hgc`.
-/
theorem hw_le_span_sup_coinv : ∀ (P Q R S : ℕ) (x : ℚ) (μ' : Ix R S → ℚ), JointShape P Q R S (fun _ => x) μ' →
    ∃ f₀ : Formalism.BasicNotions.TH.Pol P Q R S, hwSub (fockAct2 P Q R S) μ' ≤ Submodule.span ℂ {f₀} ⊔ coinv P Q R S (x : ℂ) := by
  intro P Q R S x μ' hJ
  set L := hwSub (fockAct1 P Q R S) (fun _ => x) ⊓ hwSub (fockAct2 P Q R S) μ' ⊓
    Submodule.span ℂ (jointHarm P Q R S) with hL
  obtain ⟨v, -, hv⟩ := finrank_eq_one_iff'.1 (GlobalTheory.JointHarm.finrank_joint_highest_of_shape P Q R S _ _ hJ)
  refine ⟨v.1, fun g hg => ?_⟩
  set C := coinv P Q R S (x : ℂ) with hC
  let pr := C.mkQ
  have hker : ∀ w, pr w = 0 ↔ w ∈ C := fun w => by rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
  have hpr1 : ∀ X f, pr (fockAct1 P Q R S X f) = ((x : ℂ) * X.trace) • pr f := by
    intro X f
    rw [← map_smul, ← sub_eq_zero, ← map_sub]
    exact (hker _).2 (Submodule.subset_span ⟨X, f, rfl⟩)
  have hpr2 : ∀ Y w w', pr w = pr w' → pr (fockAct2 P Q R S Y w) = pr (fockAct2 P Q R S Y w') := by
    intro Y w w' h
    rw [← sub_eq_zero, ← map_sub] at h
    rw [← sub_eq_zero, ← map_sub, ← map_sub]
    exact (hker _).2 (coinv_stable2 _ Y ((hker _).1 h))
  have hPC : ∀ Z : Mat P Q, IsPC Z → ∀ f, pr (fockAct1 P Q R S Z f) = 0 := by
    intro Z hZ f; rw [hpr1, GlobalTheory.HarmLift.trace_PC hZ, mul_zero, zero_smul]
  obtain ⟨h, hh, hprh⟩ := GlobalTheory.HarmLift.lemA P Q R S _ pr hPC g
  obtain ⟨H0, hfin, hH0, hharm, hs1, hs2⟩ := GlobalTheory.HarmLift.lemB P Q R S h hh
  obtain ⟨ι, hιIP, hιinj⟩ := GlobalTheory.FischerParts.exists_fockIP (Ln P Q R S)
  let A : Set (Module.End ℂ (Pol P Q R S)) :=
    {a | (∃ X, IsKC X ∧ a = fockAct1 P Q R S X) ∨ ∃ Y, IsKC Y ∧ a = fockAct2 P Q R S Y}
  have hadj := GlobalTheory.FockAdj.fock_adjoints P Q R S _ ι hιIP
  obtain ⟨c, hc, hcpr, hceig⟩ := GlobalTheory.HarmLift.lemC (Pol P Q R S) (Pol P Q R S ⧸ C) _ ι hιinj pr H0 hfin A
    (by
      rintro a (⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩) w hw
      exacts [hs1 X hX w hw, hs2 Y hY w hw])
    (by
      rintro a (⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩) w _ hw
      · rw [hpr1, hw, smul_zero]
      · rw [hpr2 Y w 0 (by rw [hw, map_zero]), map_zero, map_zero])
    (by
      rintro a (⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩)
      · exact ⟨_, Or.inl ⟨_, GlobalTheory.HarmLift.isKC_adjZ hX, rfl⟩, hadj.2.1 X⟩
      · exact ⟨_, Or.inr ⟨_, GlobalTheory.HarmLift.isKC_adjZ hY, rfl⟩, hadj.2.2 Y⟩)
    h hH0
  rw [hprh] at hcpr
  have hcc : c ∈ GlobalTheory.FockScalarType.charSub P Q R S x := fun X hX =>
    hceig _ (Or.inl ⟨X, hX, rfl⟩) _ (by rw [hpr1])
  have hcw : c ∈ hwSub (fockAct2 P Q R S) μ' := by
    have hg2 := hg
    simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hg2 ⊢
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · have hs : sameBlock a a := by rcases a with a | a <;> simp [sameBlock]
      refine hceig _ (Or.inr ⟨_, GlobalTheory.HarmLift.isKC_Eab hs, rfl⟩) _ ?_
      rw [hpr2 (Eab a a) c g hcpr, hg2.1 a, map_smul, hcpr]
    · have hs : sameBlock a b := by
        revert hab; rcases a with a | a <;> rcases b with b | b <;> simp [posC, sameBlock]
      rw [hceig _ (Or.inr ⟨_, GlobalTheory.HarmLift.isKC_Eab hs, rfl⟩) 0
        (by rw [hpr2 (Eab a b) c g hcpr, hg2.2 a b hab, map_zero, zero_smul]), zero_smul]
  have hcJ : c ∈ jointHarm P Q R S := ⟨hharm c hc, fockHarmonicsSecondMember_of_jointShape_highestWeight hJ (hharm c hc) hcc hcw⟩
  have hcL : c ∈ L := by
    by_cases h0 : c = 0
    · rw [h0]; exact L.zero_mem
    exact ⟨⟨(GlobalTheory.FockScalarType.isHW_of_mem h0 hcc).2, hcw⟩, Submodule.subset_span hcJ⟩
  obtain ⟨t, ht⟩ := hv ⟨c, hcL⟩
  have hct : c = t • v.1 := by
    have := congrArg Subtype.val ht
    simpa using this.symm
  have hgc : g - c ∈ C := (hker _).1 (by rw [map_sub, hcpr, sub_self])
  rw [← sub_add_cancel g c, add_comm]
  exact Submodule.add_mem_sup (hct ▸ Submodule.smul_mem _ t (Submodule.mem_span_singleton_self _)) hgc

end GlobalTheory.HoweR
