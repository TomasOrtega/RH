import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.ProperGenMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

/- English proof (translation)
Introduce `m b z hz a' ha'`. Use function extensionality and compare the values at `s0`. Set `L : GF M n →ₗ[ℂ_[l]] ℂ_[l]` to `{ toFun := fun g => ∑ a ∈ Finset.range (n + 1), ∑ s, z a s * g a ((b a).coord s) map_add' := by`. Introduce `f g`. Simplify using `only [Pi.add_apply, mul_add, Finset.sum_add_distrib]`.

Use the proof step `map_smul' := by`. Introduce `c f`. Simplify using `only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Use `ring }`.

Establish `hL : Sp P M n ≤ LinearMap.ker L`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, rfl⟩`. Conclude with `hz v`. Take `⟨N, hN, hmem⟩` from `h a' (b a' s0)`.

Establish `h0 : L (tgt hC (b a' s0) N) = 0` using `hL hmem`. Establish `hGe : ∀ s, Gx hC (b a' s0) ((b a').coord s) (oneH M.q) = (b a').coord s (b a' s0)`. Introduce `s`. Unfold `Gx`. Rewrite using `[dif_pos (Nat.zero_add a')]`.

Simplify using `only [LinearMap.comp_apply, LinearMap.flip_apply, cupL_apply]`. Rewrite using `[(hC _ _ M.q).2.2.2.1]`. Establish `hGn : ∀ a, a ≠ a' → ∀ s, Gx hC (b a' s0) ((b a).coord s) (oneH M.q) = 0`. Introduce `a ha s`. Unfold `Gx`.

Rewrite using `[dif_neg (by omega)]`. Both sides reduce to the same expression. Establish `hv : L (tgt hC (b a' s0) N) = z a' s0 * qC l N` using `by show ∑ a ∈ Finset.range (n + 1), ∑ s, z a s * (qC l N * kC K (Gx hC (b a' s0) ((b a).coord s) (oneH M.q))) = _`. Rewrite using `[Finset.sum_eq_single a']`. Simplify using `only [hGe, Module.Basis.coord_apply, Module.Basis.repr_self]`.

Rewrite using `[Finset.sum_eq_single s0]`. Simplify using the standard rewrite rules. Introduce `s _ hs`. Simplify using `[Ne.symm hs]`. Simplify using the standard rewrite rules.

Introduce `a _ ha`. Use `Finset.sum_eq_zero fun s _ => ?_` and prove the remaining obligations. Rewrite using `[hGn a ha]`. Simplify using the standard rewrite rules. Introduce `ha`.

Conclude with `absurd (Finset.mem_range.2 (by omega)) ha`. Rewrite `h0` using `[hv]`. Establish `hq : qC l N ≠ 0` using `(map_ne_zero (qC l)).2 hN`. Simplify `h0` using `[hq]`.
-/
theorem surj_of_core (hC : CupLaws) (P : HTPre l K) (M : Model l K) (n : ℕ)
    (h : ∀ a' (x : Hdg M.q a' n), ∃ N : ℚ_[l], N ≠ 0 ∧ tgt hC x N ∈ Sp P M n) : Surj P M n := by
  intro m b z hz a' ha'
  funext s0
  let L : GF M n →ₗ[ℂ_[l]] ℂ_[l] :=
    { toFun := fun g => ∑ a ∈ Finset.range (n + 1), ∑ s, z a s * g a ((b a).coord s)
      map_add' := by
        intro f g
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c f
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => ?_
        ring }
  have hL : Sp P M n ≤ LinearMap.ker L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, rfl⟩
    exact hz v
  obtain ⟨N, hN, hmem⟩ := h a' (b a' s0)
  have h0 : L (tgt hC (b a' s0) N) = 0 := hL hmem
  have hGe : ∀ s, Gx hC (b a' s0) ((b a').coord s) (oneH M.q) = (b a').coord s (b a' s0) := by
    intro s
    unfold Gx
    rw [dif_pos (Nat.zero_add a')]
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, cupL_apply]
    rw [(hC _ _ M.q).2.2.2.1]
  have hGn : ∀ a, a ≠ a' → ∀ s, Gx hC (b a' s0) ((b a).coord s) (oneH M.q) = 0 := by
    intro a ha s
    unfold Gx
    rw [dif_neg (by omega)]
    rfl
  have hv : L (tgt hC (b a' s0) N) = z a' s0 * qC l N := by
    show ∑ a ∈ Finset.range (n + 1), ∑ s, z a s * (qC l N * kC K (Gx hC (b a' s0) ((b a).coord s) (oneH M.q))) = _
    rw [Finset.sum_eq_single a']
    · simp only [hGe, Module.Basis.coord_apply, Module.Basis.repr_self]
      rw [Finset.sum_eq_single s0]
      · simp
      · intro s _ hs
        simp [Ne.symm hs]
      · simp
    · intro a _ ha
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [hGn a ha]
      simp
    · intro ha
      exact absurd (Finset.mem_range.2 (by omega)) ha
  rw [hv] at h0
  have hq : qC l N ≠ 0 := (map_ne_zero (qC l)).2 hN
  simpa [hq] using h0

end CrystallineSemistableComparison.Onto

end
