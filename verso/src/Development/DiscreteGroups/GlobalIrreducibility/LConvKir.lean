import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.LConvKirStep

noncomputable section
open GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.PRep

namespace DiscreteGroups.sglob.LConv

open DiscreteGroups.sglob.LConvKir in
/- English proof (translation)
Introduce `k _ _ _ _ ψ hψc hψ m V _ _ ρ hsm v₀`. Establish `key : ∀ j, j ≤ m → ∃ v : V, ∀ l : Module.Dual ℂ V, IsFunctional ψ ρ l → l v = l v₀ ∧ (l v₀ = 0 → ∀ g, InH j g → l (ρ g v) = 0)`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`.

Introduce `_`. Conclude with `⟨v₀, fun l _ => ⟨rfl, fun h0 g hg => by rw [InH_zero g hg, map_one, Module.End.one_apply]; exact h0⟩⟩`. Consider the case `succ j ih`. Introduce `hj`. Take `⟨v, hv⟩` from `ih (by omega)`.

Take `⟨v', hv'⟩` from `step ψ hψc hψ ρ hsm j (by omega) v`. Conclude with `⟨v', fun l hl => ⟨(hv' l hl).1.trans (hv l hl).1, fun h0 g hg => (hv' l hl).2 ((hv l hl).2 h0) g hg⟩⟩`. Take `⟨v, hv⟩` from `key m le_rfl`. Conclude with `⟨v, fun l hl => ⟨(hv l hl).1, fun h0 g => (hv l hl).2 h0 _ (InH_corner g)⟩⟩`.
-/
theorem kirBump : KirBump := by
  intro k _ _ _ _ ψ hψc hψ m V _ _ ρ hsm v₀
  have key : ∀ j, j ≤ m → ∃ v : V, ∀ l : Module.Dual ℂ V, IsFunctional ψ ρ l →
      l v = l v₀ ∧ (l v₀ = 0 → ∀ g, InH j g → l (ρ g v) = 0) := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨v₀, fun l _ => ⟨rfl, fun h0 g hg => by rw [InH_zero g hg, map_one, Module.End.one_apply]; exact h0⟩⟩
    | succ j ih =>
      intro hj
      obtain ⟨v, hv⟩ := ih (by omega)
      obtain ⟨v', hv'⟩ := step ψ hψc hψ ρ hsm j (by omega) v
      exact ⟨v', fun l hl => ⟨(hv' l hl).1.trans (hv l hl).1,
        fun h0 g hg => (hv' l hl).2 ((hv l hl).2 h0) g hg⟩⟩
  obtain ⟨v, hv⟩ := key m le_rfl
  exact ⟨v, fun l hl => ⟨(hv l hl).1, fun h0 g => (hv l hl).2 h0 _ (InH_corner g)⟩⟩

end DiscreteGroups.sglob.LConv
