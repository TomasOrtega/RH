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
Introduce and unpack `_ ⟨a, -, rfl⟩`. Simplify using `using S.smul_mem a hv`.
-/
theorem line_le {A : Submodule (𝓞 K) K} {v : V} {S : Submodule K V} (hv : v ∈ S) :
    line A v ≤ rs (𝓞 K) S := by
  rintro _ ⟨a, -, rfl⟩
  simpa using S.smul_mem a hv

/- English proof (translation)
Unfold `NF.P0`. Use `sup_le (sup_le (sup_le ?_ ?_) le_sup_right) ?_` and prove the remaining obligations. Use `iSup_le fun a => le_sup_of_le_left (line_le ?_)` and prove the remaining obligations. Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨a, a.isLt, rfl⟩))`. Use `iSup_le fun a => iSup_le fun _ => le_sup_of_le_left (line_le ?_)` and prove the remaining obligations.

Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span ⟨a, a.isLt, rfl⟩))`. Use `iSup_le fun a => iSup_le fun h => le_sup_of_le_left (line_le ?_)` and prove the remaining obligations. Conclude with `Submodule.mem_sup_right (Submodule.subset_span ⟨a, h, rfl⟩)`.
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
Rewrite using `[NFGeom.Pi_eq]`. Conclude with `sup_le (sup_le (le_sup_of_le_left (le_sup_left.trans le_sup_left)) (le_sup_of_le_left (le_sup_right.trans le_sup_left))) le_sup_right`.
-/
theorem Sg_le_Pi [FiniteDimensional K V] : Sg N ≤ N.Pi := by
  rw [NFGeom.Pi_eq]
  exact sup_le (sup_le (le_sup_of_le_left (le_sup_left.trans le_sup_left))
    (le_sup_of_le_left (le_sup_right.trans le_sup_left))) le_sup_right

/- English proof (translation)
Rewrite using `[NFGeom.Pi_eq]`. Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span (by simp)))`.
-/
theorem z_mem_Pi [FiniteDimensional K V] : N.F.z ∈ N.Pi := by
  rw [NFGeom.Pi_eq]
  exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span (by simp)))

/- English proof (translation)
Rewrite `hW` using `[NFGeom.Wn_eq N]`. Take `⟨w, hw, m, hm, rfl⟩` from `Submodule.mem_sup.1 hW`. Take `⟨κ, rfl⟩` from `Submodule.mem_span_singleton.1 hm`. Establish `hwP : w ∈ N.Pi`. Establish `e : w = (w + κ • N.F.z) - κ • N.F.z` using `by abel`.

Rewrite using `[e]`. Conclude with `Submodule.sub_mem _ (Sg_le_Pi N hS) (Submodule.smul_mem _ _ (z_mem_Pi N))`. Establish `hw0 : w = 0` using `NFGeom.Wt_inf_Pi N hw hwP`. Substitute `hw0` using the available equality. Rewrite `hS`, the goal using `[zero_add]`.

Establish `h1 : H.B N.F.z (κ • N.F.z) = 0` using `(mem_perp_iff H (Sg N) _).1 (NFGeom.z_mem_Wn N) _ hS`. Establish `h2 : H.B (κ • N.F.z) N.F.z = 0` using `B_swap0 H h1`. Establish `h3 : H.B N.F.z N.F.z = -N.F.T` using `N.F.zz`. Rewrite `h2` using `[map_smul, LinearMap.smul_apply, h3, smul_eq_mul, mul_neg, neg_eq_zero]`. Break down `mul_eq_zero.1 h2 with h | h` into its components or cases.

Simplify using `[h]`. Conclude with `absurd h N.F.hT`.
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
Introduce `K V _ _ _ _ _ _ _ _ H _ r N L hz v hv hvW`. Take `⟨p, hp, l, hl, rfl⟩` from `Submodule.mem_sup.1 hv`. Take `⟨q, hq, m, hm, rfl⟩` from `Submodule.mem_sup.1 (ReflectionLatticeMembership.normalForm_baseLattice_le_dualSpan_sup_line N hp)`. Take `⟨γ, hγ, rfl⟩` from `hm`. Take `⟨x, rfl⟩` from `Submodule.mem_one.1 hγ`.

Establish `hm' : ((LinearMap.toSpanSingleton K V N.F.z).restrictScalars (𝓞 K)) (algebraMap (𝓞 K) K x) = x • N.F.z`. Simplify using `[algebraMap_smul]`. Rewrite `hvW`, the goal using `[hm']`. Establish `hmW : x • N.F.z ∈ N.Wn`. Rewrite using `[← algebraMap_smul K x N.F.z]`.

Conclude with `N.Wn.smul_mem _ (NFGeom.z_mem_Wn N)`. Establish `hlW : l ∈ N.Wn` using `hl.2`. Establish `hq0 : q = 0` using `ReflectionLatticeMembership.eq_zero N hq (by`. Establish `h` using `N.Wn.sub_mem (N.Wn.sub_mem hvW hlW) hmW`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use the proof step `abel)`. Substitute `hq0` using the available equality. Rewrite using `[zero_add]`. Conclude with `L.add_mem (L.smul_mem x hz) hl.1`.
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
