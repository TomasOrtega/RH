import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open Formalism.HermitianLatticeCounting.P

noncomputable section

namespace GlobalTheory.DegCnt.ReflectionLatticeMembership

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ} (N : NF H r)

def Sg : Submodule K V := N.F.X ⊔ N.F'.X ⊔ N.Ist

/- English proof (translation)
Assume the hypotheses and unpack their components. Simplify to obtain the desired conclusion from the available facts.
-/
theorem line_le {A : Submodule (𝓞 K) K} {v : V} {S : Submodule K V} (hv : v ∈ S) :
    line A v ≤ rs (𝓞 K) S := by
  rintro _ ⟨a, -, rfl⟩
  simpa using S.smul_mem a hv

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

A detailed English derivation is pending.
-/
theorem normalForm_baseLattice_le_dualSpan_sup_line : N.P0 ≤ rs (𝓞 K) (Sg N) ⊔ line 1 N.F.z := by
  unfold NF.P0
  refine sup_le (sup_le (sup_le ?_ ?_) le_sup_right) ?_
  · refine iSup_le fun a => le_sup_of_le_left (line_le ?_)
    exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨a, a.isLt, rfl⟩))
  · refine iSup_le fun a => iSup_le fun _ => le_sup_of_le_left (line_le ?_)
    exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span ⟨a, a.isLt, rfl⟩))
  · refine iSup_le fun a => iSup_le fun h => le_sup_of_le_left (line_le ?_)
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨a, h, rfl⟩)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem Sg_le_Pi [FiniteDimensional K V] : Sg N ≤ N.Pi := by
  rw [NFGeom.Pi_eq]
  exact sup_le (sup_le (le_sup_of_le_left (le_sup_left.trans le_sup_left))
    (le_sup_of_le_left (le_sup_right.trans le_sup_left))) le_sup_right

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem z_mem_Pi [FiniteDimensional K V] : N.F.z ∈ N.Pi := by
  rw [NFGeom.Pi_eq]
  exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span (by simp)))

/- English proof (translation)
Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Substitute using the available equality. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem eq_zero [FiniteDimensional K V] {q : V} (hS : q ∈ Sg N) (hW : q ∈ N.Wn) : q = 0 := by
  rw [NFGeom.Wn_eq N] at hW
  obtain ⟨w, hw, m, hm, rfl⟩ := Submodule.mem_sup.1 hW
  obtain ⟨κ, rfl⟩ := Submodule.mem_span_singleton.1 hm
  have hwP : w ∈ N.Pi := by
    have e : w = (w + κ • N.F.z) - κ • N.F.z := by abel
    rw [e]
    exact Submodule.sub_mem _ (Sg_le_Pi N hS) (Submodule.smul_mem _ _ (z_mem_Pi N))
  have hw0 : w = 0 := NFGeom.Wt_inf_Pi N hw hwP
  subst hw0
  rw [zero_add] at hS ⊢
  have h1 : H.B N.F.z (κ • N.F.z) = 0 := (mem_perp_iff H (Sg N) _).1 (NFGeom.z_mem_Wn N) _ hS
  have h2 : H.B (κ • N.F.z) N.F.z = 0 := B_swap0 H h1
  have h3 : H.B N.F.z N.F.z = -N.F.T := N.F.zz
  rw [map_smul, LinearMap.smul_apply, h3, smul_eq_mul, mul_neg, neg_eq_zero] at h2
  rcases mul_eq_zero.1 h2 with h | h
  · simp [h]
  · exact absurd h N.F.hT

end GlobalTheory.DegCnt.ReflectionLatticeMembership

namespace GlobalTheory.DegCnt

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Substitute using the available equality.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem NF.ref_mem_of_mem_Wn : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : GlobalTheory.DegCnt.NF H r) (L : Submodule (𝓞 K) V), N.F.z ∈ L → ∀ v ∈ N.Ref L, v ∈ N.Wn → v ∈ L := by
  intro K V _ _ _ _ _ _ _ _ H _ r N L hz v hv hvW
  obtain ⟨p, hp, l, hl, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨q, hq, m, hm, rfl⟩ := Submodule.mem_sup.1 (ReflectionLatticeMembership.normalForm_baseLattice_le_dualSpan_sup_line N hp)
  obtain ⟨γ, hγ, rfl⟩ := hm
  obtain ⟨x, rfl⟩ := Submodule.mem_one.1 hγ
  have hm' : ((LinearMap.toSpanSingleton K V N.F.z).restrictScalars (𝓞 K)) (algebraMap (𝓞 K) K x) = x • N.F.z := by
    simp [algebraMap_smul]
  rw [hm'] at hvW ⊢
  have hmW : x • N.F.z ∈ N.Wn := by
    rw [← algebraMap_smul K x N.F.z]
    exact N.Wn.smul_mem _ (NFGeom.z_mem_Wn N)
  have hlW : l ∈ N.Wn := hl.2
  have hq0 : q = 0 := ReflectionLatticeMembership.eq_zero N hq (by
    have h := N.Wn.sub_mem (N.Wn.sub_mem hvW hlW) hmW
    convert h using 1
    abel)
  subst hq0
  rw [zero_add]
  exact L.add_mem (L.smul_mem x hz) hl.1

end GlobalTheory.DegCnt
