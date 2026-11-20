import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

/- English proof (translation)
Introduce `C _ v O _ _ V _ _ _ _ h N g hv hsp hN`. Use `hv.hom_inj.isDomain` as an intermediate fact. Use `ValuationRing.of_integers v hv` as an intermediate fact. Use `hv.isFractionRing` as an intermediate fact. Use `set A : Submodule O V := Submodule.span O (Set.range g) with hA`.

Establish `: Module.Finite O A` using `Module.Finite.iff_fg.2 (Submodule.fg_span (Set.finite_range g))`. Establish `: Module.Flat O A`. Rewrite using `[Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]`. Introduce and unpack `⟨x, hxA⟩ hx`. Rewrite using `[Submodule.mem_bot]`.

Take `⟨a, ha⟩` from `(Submodule.mem_torsion_iff _).1 hx`. Establish `h' : ((a : O) • x : V) = 0` using `congrArg Subtype.val ha`. Rewrite `h'` using `[← algebraMap_smul C (a : O) x]`. Conclude with `Subtype.ext ((smul_eq_zero.1 h').resolve_left (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2))`. Establish `: Module.Free O A` using `Module.free_of_flat_of_isLocalRing`.

Set `b` to `Module.Free.chooseBasis O A`. Set `w : Module.Free.ChooseBasisIndex O A → V` to `fun i => (b i : V)`. Establish `hR : LinearIndependent O w` using `b.linearIndependent.map' A.subtype (Submodule.ker_subtype _)`. Establish `hC : LinearIndependent C w` using `(LinearIndependent.iff_fractionRing O C).1 hR`. Establish `hspR : Submodule.span O (Set.range w) = A`.

Establish `: Set.range w = A.subtype '' Set.range b`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]`. Establish `hspC : Submodule.span C (Set.range w) = ⊤`.

Rewrite using `[← Submodule.span_span_of_tower O, hspR, hA, Submodule.span_span_of_tower, hsp]`. Set `bC` to `Module.Basis.mk hC (by rw [hspC])`. Establish `hcard : Fintype.card (Module.Free.ChooseBasisIndex O A) = N`. Rewrite using `[← hN, Module.finrank_eq_card_basis bC]`. Use `⟨bC.reindex (Fintype.equivFinOfCardEq hcard), ?_⟩` and prove the remaining obligations.

Rewrite using `[Module.Basis.range_reindex, Module.Basis.coe_mk, hspR]`.
-/
theorem exists_basis_span_eq_span_of_valuation : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (h N : ℕ) (g : Fin h → V), v.Integers O → Submodule.span C (Set.range g) = ⊤ → Module.finrank C V = N → ∃ b : Module.Basis (Fin N) C V, Submodule.span O (Set.range g) = Submodule.span O (Set.range b) := by
  intro C _ v O _ _ V _ _ _ _ h N g hv hsp hN
  classical
  have := hv.hom_inj.isDomain
  have := ValuationRing.of_integers v hv
  have := hv.isFractionRing
  set A : Submodule O V := Submodule.span O (Set.range g) with hA
  have : Module.Finite O A := Module.Finite.iff_fg.2 (Submodule.fg_span (Set.finite_range g))
  have : Module.Flat O A := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro ⟨x, hxA⟩ hx
    rw [Submodule.mem_bot]
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff _).1 hx
    have h' : ((a : O) • x : V) = 0 := congrArg Subtype.val ha
    rw [← algebraMap_smul C (a : O) x] at h'
    exact Subtype.ext ((smul_eq_zero.1 h').resolve_left
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2))
  have : Module.Free O A := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis O A
  let w : Module.Free.ChooseBasisIndex O A → V := fun i => (b i : V)
  have hR : LinearIndependent O w := b.linearIndependent.map' A.subtype (Submodule.ker_subtype _)
  have hC : LinearIndependent C w := (LinearIndependent.iff_fractionRing O C).1 hR
  have hspR : Submodule.span O (Set.range w) = A := by
    have : Set.range w = A.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hspC : Submodule.span C (Set.range w) = ⊤ := by
    rw [← Submodule.span_span_of_tower O, hspR, hA, Submodule.span_span_of_tower, hsp]
  let bC := Module.Basis.mk hC (by rw [hspC])
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex O A) = N := by
    rw [← hN, Module.finrank_eq_card_basis bC]
  refine ⟨bC.reindex (Fintype.equivFinOfCardEq hcard), ?_⟩
  rw [Module.Basis.range_reindex, Module.Basis.coe_mk, hspR]

end GlobalTheory
