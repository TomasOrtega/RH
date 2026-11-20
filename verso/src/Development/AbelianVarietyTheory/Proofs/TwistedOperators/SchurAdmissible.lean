import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation

namespace GlobalTheory.SchurAdmissibility

/- English proof (translation)
Distinguish the cases in `hN : ∀ v : N, v = 0`. Conclude with `⟨0, LinearMap.ext fun v => by rw [hN (φ v)]; simp⟩`. Use `push Not at hN`. Take `⟨v, hv⟩` from `hN`. Set `S : Subgroup G` to `{ carrier := {g : G | π g v = v} mul_mem' := by`.

Introduce `a b ha hb`. Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`. Rewrite using `[map_mul, Module.End.mul_apply, hb, ha]`. Use the proof step `one_mem' := by simp`. Use the proof step `inv_mem' := by`.

Introduce `a ha`. Simplify using `only [Set.mem_setOf_eq] at ha ⊢`. Use `conv_lhs => rw [← ha]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }`. Establish `hSo : IsOpen (S : Set G)` using `hadm.1 v`.

Establish `hSc : IsClosed (S : Set G)` using `S.isClosed_of_isOpen hSo`. Establish `hLo : IsOpen ((K ⊓ S : Subgroup G) : Set G)`. Rewrite using `[Subgroup.coe_inf]`. Conclude with `hKo.inter hSo`. Establish `hLc : IsCompact ((K ⊓ S : Subgroup G) : Set G)`.

Rewrite using `[Subgroup.coe_inf]`. Conclude with `hKc.inter_right hSc`. Use `haveI hfd := hadm.2 (K ⊓ S) hLo hLc`. Establish `hmem : ∀ w : N, w ∈ GlobalTheory.PRep.fixed π (K ⊓ S) ↔ ∀ h : (K ⊓ S : Subgroup G), π (h : G) w = w`. Introduce `w`.

Express the relevant statement in the definitionally equal form `(∀ h : (K ⊓ S : Subgroup G), π (h : G) w = _) ↔ _`. Simplify using the standard rewrite rules. Establish `hvm : v ∈ GlobalTheory.PRep.fixed π (K ⊓ S)` using `(hmem v).2 fun h => h.2.2`. Use `haveI : Nontrivial (GlobalTheory.PRep.fixed π (K ⊓ S)) := ⟨⟨⟨v, hvm⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩`. Establish `hres : ∀ w ∈ GlobalTheory.PRep.fixed π (K ⊓ S), φ w ∈ GlobalTheory.PRep.fixed π (K ⊓ S)`.

Introduce `w hw`. Rewrite `hw`, the goal using `[hmem]`. Introduce `h`. Rewrite using `[← hφ, hw h]`. Take `⟨c, hc⟩` from `Module.End.exists_eigenvalue (φ.restrict hres)`.

Take `⟨w, hw⟩` from `hc.exists_hasEigenvector`. Establish `hw0 : (w : N) ≠ 0` using `fun h => hw.2 (Subtype.ext h)`. Establish `hw1 : φ w = c • (w : N)` using `congrArg Subtype.val hw.apply_eq_smul`. Set `U : Subrepresentation π` to `{ toSubmodule := Module.End.eigenspace φ c apply_mem_toSubmodule := by`. Introduce `g x hx`.

Rewrite `hx`, the goal using `[Module.End.mem_eigenspace_iff]`. Rewrite using `[hφ, hx, map_smul] }`. Use `⟨c, ?_⟩` and prove the remaining obligations. Break down `hirr.eq_bot_or_eq_top U with h | h` into its components or cases. It suffices to derive a contradiction.

Establish `h1 : (w : N) ∈ U.toSubmodule` using `Module.End.mem_eigenspace_iff.2 hw1`. Rewrite `h1` using `[h]`. Conclude with `hw0 h1`. Use extensionality with `x`. Establish `h1 : x ∈ U.toSubmodule`.

Rewrite using `[h]`. Discharge the goal by the elementary cases of `trivial`. Conclude with `Module.End.mem_eigenspace_iff.1 h1`.
-/
theorem schur_admissible (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (N : Type) [AddCommGroup N] [Module ℂ N] (π : Representation ℂ G N)
    (hirr : Representation.IsIrreducible π) (hadm : GlobalTheory.PRep.IsAdmissible π)
    (φ : N →ₗ[ℂ] N) (hφ : ∀ (g : G) (x : N), φ (π g x) = π g (φ x)) :
    ∃ c : ℂ, φ = c • LinearMap.id := by
  by_cases hN : ∀ v : N, v = 0
  · exact ⟨0, LinearMap.ext fun v => by rw [hN (φ v)]; simp⟩
  push Not at hN
  obtain ⟨v, hv⟩ := hN
  let S : Subgroup G :=
    { carrier := {g : G | π g v = v}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hSo : IsOpen (S : Set G) := hadm.1 v
  have hSc : IsClosed (S : Set G) := S.isClosed_of_isOpen hSo
  have hLo : IsOpen ((K ⊓ S : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]; exact hKo.inter hSo
  have hLc : IsCompact ((K ⊓ S : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]; exact hKc.inter_right hSc
  haveI hfd := hadm.2 (K ⊓ S) hLo hLc
  have hmem : ∀ w : N, w ∈ GlobalTheory.PRep.fixed π (K ⊓ S) ↔
      ∀ h : (K ⊓ S : Subgroup G), π (h : G) w = w := by
    intro w
    change (∀ h : (K ⊓ S : Subgroup G), π (h : G) w = _) ↔ _
    simp
  have hvm : v ∈ GlobalTheory.PRep.fixed π (K ⊓ S) := (hmem v).2 fun h => h.2.2
  haveI : Nontrivial (GlobalTheory.PRep.fixed π (K ⊓ S)) :=
    ⟨⟨⟨v, hvm⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  have hres : ∀ w ∈ GlobalTheory.PRep.fixed π (K ⊓ S), φ w ∈ GlobalTheory.PRep.fixed π (K ⊓ S) := by
    intro w hw
    rw [hmem] at hw ⊢
    intro h
    rw [← hφ, hw h]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (φ.restrict hres)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  have hw0 : (w : N) ≠ 0 := fun h => hw.2 (Subtype.ext h)
  have hw1 : φ w = c • (w : N) := congrArg Subtype.val hw.apply_eq_smul
  let U : Subrepresentation π :=
    { toSubmodule := Module.End.eigenspace φ c
      apply_mem_toSubmodule := by
        intro g x hx
        rw [Module.End.mem_eigenspace_iff] at hx ⊢
        rw [hφ, hx, map_smul] }
  refine ⟨c, ?_⟩
  rcases hirr.eq_bot_or_eq_top U with h | h
  · exfalso
    have h1 : (w : N) ∈ U.toSubmodule := Module.End.mem_eigenspace_iff.2 hw1
    rw [h] at h1
    exact hw0 h1
  · ext x
    have h1 : x ∈ U.toSubmodule := by
      rw [h]; trivial
    exact Module.End.mem_eigenspace_iff.1 h1

end GlobalTheory.SchurAdmissibility
