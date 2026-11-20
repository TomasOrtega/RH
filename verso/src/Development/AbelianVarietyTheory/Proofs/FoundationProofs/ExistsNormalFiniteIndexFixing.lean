import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

/- English proof (translation)
Use `set T : Set L := ⋃ s ∈ S, MulAction.orbit G s with hT`. Establish `hTfin : T.Finite` using `Set.Finite.biUnion S.finite_toSet (fun s hs => hS s hs)`. Establish `hTstab : ∀ g : G, ∀ x ∈ T, g • x ∈ T`. Introduce `g x hx`. Simplify using `only [hT, Set.mem_iUnion] at hx ⊢`.

Take `⟨s, hs, hx⟩` from `hx`. Conclude with `⟨s, hs, MulAction.mem_orbit_of_mem_orbit g hx⟩`. Use `set F : Finset L := hTfin.toFinset`. Establish `hF : ∀ x, x ∈ F ↔ x ∈ T` using `fun x => hTfin.mem_toFinset`. Set `U : Subgroup G` to `⨅ x ∈ F, MulAction.stabilizer G x`.

Establish `hU : ∀ g : G, g ∈ U ↔ ∀ x ∈ T, g • x = x`. Introduce `g`. Simplify using `only [U, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff, hF]`. Establish `hST : ∀ s ∈ S, s ∈ T`. Introduce `s hs`.

Simplify using `only [hT, Set.mem_iUnion]`. Conclude with `⟨s, hs, MulAction.mem_orbit_self s⟩`. Establish `hFix : ∀ x ∈ T, x ∈ Fix L U`. Introduce `x hx`. Express the relevant statement in the definitionally equal form `∀ m : U, m • x = x`.

Introduce and unpack `⟨g, hg⟩`. Conclude with `(hU g).1 hg x hx`. Use `⟨U, ?_, ?_, fun s hs => hFix s (hST s hs), ?_⟩` and prove the remaining obligations. Use `⟨fun n hn g => ?_⟩` and prove the remaining obligations. Rewrite `hn`, the goal using `[hU]`.

Introduce `x hx`. Use `hn (g⁻¹ • x) (hTstab g⁻¹ x hx)` as an intermediate fact. Rewrite using `[mul_smul, mul_smul, this, smul_inv_smul]`. Use `Subgroup.finiteIndex_iInf' _ (fun x hx => ?_)` and prove the remaining obligations. Use `⟨?_⟩` and prove the remaining obligations.

Rewrite using `[MulAction.index_stabilizer]`. Establish `hx'` using `(hF x).1 hx`. Simplify using `only [hT, Set.mem_iUnion] at hx'`. Take `⟨s, hs, hxs⟩` from `hx'`. Rewrite using `[MulAction.orbit_eq_iff.mpr hxs]`.

Conclude with `(Set.ncard_pos (hS s hs)).mpr ⟨s, MulAction.mem_orbit_self s⟩ |>.ne'`. Introduce `h hh`. Rewrite `hh` using `[hU]`. Use `push_neg at hh`. Take `⟨x, hx, hne⟩` from `hh`.

Conclude with `⟨x, hFix x hx, hne⟩`.
-/
theorem exists_normal_finiteIndex_fixing (L : Type) [Field L] (G : Type) [Group G]
    [MulSemiringAction G L] (S : Finset L) (hS : ∀ s ∈ S, (MulAction.orbit G s).Finite) :
    ∃ U : Subgroup G, U.Normal ∧ U.FiniteIndex ∧ (∀ s ∈ S, s ∈ Fix L U) ∧
      ∀ h : G, h ∉ U → ∃ x ∈ Fix L U, h • x ≠ x := by
  classical
  set T : Set L := ⋃ s ∈ S, MulAction.orbit G s with hT
  have hTfin : T.Finite := Set.Finite.biUnion S.finite_toSet (fun s hs => hS s hs)
  have hTstab : ∀ g : G, ∀ x ∈ T, g • x ∈ T := by
    intro g x hx
    simp only [hT, Set.mem_iUnion] at hx ⊢
    obtain ⟨s, hs, hx⟩ := hx
    exact ⟨s, hs, MulAction.mem_orbit_of_mem_orbit g hx⟩
  set F : Finset L := hTfin.toFinset
  have hF : ∀ x, x ∈ F ↔ x ∈ T := fun x => hTfin.mem_toFinset
  let U : Subgroup G := ⨅ x ∈ F, MulAction.stabilizer G x
  have hU : ∀ g : G, g ∈ U ↔ ∀ x ∈ T, g • x = x := by
    intro g
    simp only [U, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff, hF]
  have hST : ∀ s ∈ S, s ∈ T := by
    intro s hs
    simp only [hT, Set.mem_iUnion]
    exact ⟨s, hs, MulAction.mem_orbit_self s⟩
  have hFix : ∀ x ∈ T, x ∈ Fix L U := by
    intro x hx
    change ∀ m : U, m • x = x
    rintro ⟨g, hg⟩
    exact (hU g).1 hg x hx
  refine ⟨U, ?_, ?_, fun s hs => hFix s (hST s hs), ?_⟩
  · refine ⟨fun n hn g => ?_⟩
    rw [hU] at hn ⊢
    intro x hx
    have := hn (g⁻¹ • x) (hTstab g⁻¹ x hx)
    rw [mul_smul, mul_smul, this, smul_inv_smul]
  · refine Subgroup.finiteIndex_iInf' _ (fun x hx => ?_)
    refine ⟨?_⟩
    rw [MulAction.index_stabilizer]
    have hx' := (hF x).1 hx
    simp only [hT, Set.mem_iUnion] at hx'
    obtain ⟨s, hs, hxs⟩ := hx'
    rw [MulAction.orbit_eq_iff.mpr hxs]
    exact (Set.ncard_pos (hS s hs)).mpr ⟨s, MulAction.mem_orbit_self s⟩ |>.ne'
  · intro h hh
    rw [hU] at hh
    push_neg at hh
    obtain ⟨x, hx, hne⟩ := hh
    exact ⟨x, hFix x hx, hne⟩

end GlobalTheory.AlmostEt
