import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff

namespace GlobalTheory.SeqCx

/- English proof (translation)
Establish `hlin : ∀ d : List V →₀ ℤ, Finsupp.mapDomain (fun l => (l, ([] : List W))) d = Finsupp.lmapDomain ℤ ℤ (fun l => (l, ([] : List W))) d` using `fun d => rfl`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[chains2, Finsupp.mem_supported]`. Rewrite `hc` using `[chains, Finsupp.mem_supported]`. Introduce `z hz`.

Establish `hz'` using `Finsupp.mapDomain_support hz`. Rewrite `hz'` using `[Finset.mem_image]`. Take `⟨l, hl, rfl⟩` from `hz'`. Use `hc (Finset.mem_coe.mpr hl)` as an intermediate fact. Conclude with `⟨this.1, this.2, rfl⟩`.

Establish `key : (hbd V W).comp (Finsupp.lmapDomain ℤ ℤ (fun l => (l, ([] : List W)))) = (Finsupp.lmapDomain ℤ ℤ (fun l => (l, ([] : List W)))).comp (bd V)`. Apply `Finsupp.lhom_ext'` to reduce the goal to its premises. Introduce `l`. Apply `LinearMap.ext_ring` to reduce the goal to its premises. Simplify using `[hbd, Finsupp.mapDomain_single]`.

Use `LinearMap.congr_fun key c` as an intermediate fact. Simplify using `only [LinearMap.comp_apply] at this`. Rewrite using `[hlin, this, hb, map_zero]`. Establish `key : (vbd V W).comp (Finsupp.lmapDomain ℤ ℤ (fun l => (l, ([] : List W)))) = 0`. Apply `Finsupp.lhom_ext'` to reduce the goal to its premises.

Introduce `l`. Apply `LinearMap.ext_ring` to reduce the goal to its premises. Simplify using `[vbd, bd, Finsupp.mapDomain_single]`. Use `LinearMap.congr_fun key c` as an intermediate fact. Simplify `this` using `[LinearMap.comp_apply]`.
-/
theorem cycle_pair_empty (V W : Type) (D : Set (List V × List W)) (p : ℕ) (c : List V →₀ ℤ)
    (hc : c ∈ chains {l | (l, ([] : List W)) ∈ D} p) (hb : bd V c = 0) :
    Finsupp.mapDomain (fun l => (l, ([] : List W))) c ∈ chains2 D p 0 ∧
      hbd V W (Finsupp.mapDomain (fun l => (l, ([] : List W))) c) = 0 ∧
      vbd V W (Finsupp.mapDomain (fun l => (l, ([] : List W))) c) = 0 := by
  have hlin : ∀ d : List V →₀ ℤ, Finsupp.mapDomain (fun l => (l, ([] : List W))) d
      = Finsupp.lmapDomain ℤ ℤ (fun l => (l, ([] : List W))) d := fun d => rfl
  classical
  refine ⟨?_, ?_, ?_⟩
  · rw [chains2, Finsupp.mem_supported]
    rw [chains, Finsupp.mem_supported] at hc
    intro z hz
    have hz' := Finsupp.mapDomain_support hz
    rw [Finset.mem_image] at hz'
    obtain ⟨l, hl, rfl⟩ := hz'
    have := hc (Finset.mem_coe.mpr hl)
    exact ⟨this.1, this.2, rfl⟩
  · have key : (hbd V W).comp (Finsupp.lmapDomain ℤ ℤ (fun l => (l, ([] : List W))))
        = (Finsupp.lmapDomain ℤ ℤ (fun l => (l, ([] : List W)))).comp (bd V) := by
      apply Finsupp.lhom_ext'
      intro l
      apply LinearMap.ext_ring
      simp [hbd, Finsupp.mapDomain_single]
    have := LinearMap.congr_fun key c
    simp only [LinearMap.comp_apply] at this
    rw [hlin, this, hb, map_zero]
  · have key : (vbd V W).comp (Finsupp.lmapDomain ℤ ℤ (fun l => (l, ([] : List W)))) = 0 := by
      apply Finsupp.lhom_ext'
      intro l
      apply LinearMap.ext_ring
      simp [vbd, bd, Finsupp.mapDomain_single]
    have := LinearMap.congr_fun key c
    simpa [LinearMap.comp_apply] using this

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.SeqCx.cycle_pair_empty`.
-/
theorem _root_.GlobalTheory.T.pair_nil_hbd_vbd_eq_zero_of_cycle : ∀ (V W : Type) (D : Set (List V × List W)) (p : ℕ) (c : List V →₀ ℤ), c ∈ chains {l | (l, ([] : List W)) ∈ D} p → bd V c = 0 → Finsupp.mapDomain (fun l => (l, ([] : List W))) c ∈ chains2 D p 0 ∧ hbd V W (Finsupp.mapDomain (fun l => (l, ([] : List W))) c) = 0 ∧ vbd V W (Finsupp.mapDomain (fun l => (l, ([] : List W))) c) = 0 := by
  first
  | exact @GlobalTheory.SeqCx.cycle_pair_empty
end
