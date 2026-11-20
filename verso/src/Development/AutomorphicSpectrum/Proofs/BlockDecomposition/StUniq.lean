import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeStair

/- English proof (translation)
Introduce `hcol R _ C _ F T hT j z`. Take `⟨hι, hdv, hinj, hex0, hex⟩` from `hcol R C F T hT`. Establish `key : ∀ (s k : ℕ) (x : Cn (T.K s) k), T.St z s k x → T.BZ s k x → z ∈ (cx F).B j`. Introduce `s`. Proceed by induction on `s with`.

Consider the case `zero`. Introduce `k x hS hB`. Take `⟨h, rfl⟩` from `hS`. Substitute `h` using the available equality. Consider the cases of `j with`.

Consider the case `zero`. Establish `h0 : T.ιC 0 z = 0` using `hB`. Establish `hz : z = 0` using `hinj 0 (by rw [h0, map_zero])`. Rewrite using `[hz]`. Conclude with `Submodule.zero_mem _`.

Consider the case `succ k`. Take `⟨b, hb, hdb⟩` from `hB`. Take `⟨z', rfl⟩` from `(hex0 k b).1 hb`. Use `(⟨z', ?_⟩ : z ∈ LinearMap.range (d F k))` and prove the remaining obligations. Apply `hinj (k + 1)` to reduce the goal to its premises.

Rewrite using `[← hι]`. Conclude with `hdb`. Consider the case `succ s ih`. Introduce `k x hS hB`. Take `⟨a, rfl, hS'⟩` from `hS`.

Consider the cases of `k with`. Consider the case `zero`. Conclude with `ih 1 _ hS' ⟨a, hB, by simp⟩`. Consider the case `succ k`. Take `⟨b, hb, hdb⟩` from `hB`.

Take `⟨b', rfl⟩` from `(hex s k b).1 hb`. Use `ih (k + 2) _ hS' ⟨(-1 : ℤ) ^ (k + 1) • (a - d _ k b'), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zsmul, map_sub, ← hdv, hdb, sub_self, smul_zero]`. Rewrite using `[map_zsmul, map_sub, d_d, sub_zero]`. Introduce `s k x hS hB`.

Conclude with `key s k x hS hB`.
-/
theorem stUniq : CrystallineSemistableComparison.E.StCol → CrystallineSemistableComparison.E.StUniq := by
  intro hcol R _ C _ F T hT j z
  obtain ⟨hι, hdv, hinj, hex0, hex⟩ := hcol R C F T hT
  have key : ∀ (s k : ℕ) (x : Cn (T.K s) k), T.St z s k x → T.BZ s k x → z ∈ (cx F).B j := by
    intro s
    induction s with
    | zero =>
      intro k x hS hB
      obtain ⟨h, rfl⟩ := hS
      subst h
      cases j with
      | zero =>
        have h0 : T.ιC 0 z = 0 := hB
        have hz : z = 0 := hinj 0 (by rw [h0, map_zero])
        rw [hz]
        exact Submodule.zero_mem _
      | succ k =>
        obtain ⟨b, hb, hdb⟩ := hB
        obtain ⟨z', rfl⟩ := (hex0 k b).1 hb
        refine (⟨z', ?_⟩ : z ∈ LinearMap.range (d F k))
        apply hinj (k + 1)
        rw [← hι]
        exact hdb
    | succ s ih =>
      intro k x hS hB
      obtain ⟨a, rfl, hS'⟩ := hS
      cases k with
      | zero =>
        exact ih 1 _ hS' ⟨a, hB, by simp⟩
      | succ k =>
        obtain ⟨b, hb, hdb⟩ := hB
        obtain ⟨b', rfl⟩ := (hex s k b).1 hb
        refine ih (k + 2) _ hS' ⟨(-1 : ℤ) ^ (k + 1) • (a - d _ k b'), ?_, ?_⟩
        · rw [map_zsmul, map_sub, ← hdv, hdb, sub_self, smul_zero]
        · rw [map_zsmul, map_sub, d_d, sub_zero]
  intro s k x hS hB
  exact key s k x hS hB

end GlobalTheory.CompanionTheory.EdgeStair
