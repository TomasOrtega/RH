import Mathlib

namespace Formalism.L2.G

open Module

/- English proof (translation)
Take `⟨b, hbM, hspan, hli⟩` from `exists_linearIndependent Kf (M : Set W)`. Rewrite using `[← hspan, rank_span_set hli]`. Establish `hinj : Function.Injective fun r : O => r • (1 : Kf)`. Simplify `IsFractionRing.injective O Kf` using `[Algebra.smul_def]`. Establish `hliO : LinearIndependent O (fun x : b => (x : W))` using `hli.restrict_scalars hinj`.

Set `w : b → M` to `fun x => ⟨x, hbM x.2⟩`. Establish `hliw : LinearIndependent O w` using `LinearIndependent.of_comp M.subtype hliO`. Establish `h1` using `hliw.cardinal_le_rank`. Establish `h2 : Module.rank O M < Cardinal.aleph0` using `Module.rank_lt_aleph0 O M`. Rewrite using `[Module.finrank, Cardinal.cast_toNat_of_lt_aleph0 h2]`.

Conclude with `h1`.
-/
theorem finrank_span_le {O Kf W : Type} [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] [IsFractionRing O Kf]
    [AddCommGroup W] [Module Kf W] [Module O W] [IsScalarTower O Kf W] (M : Submodule O W) [Module.Finite O M] :
    Module.rank Kf (Submodule.span Kf (M : Set W)) ≤ (Module.finrank O M : Cardinal) := by
  obtain ⟨b, hbM, hspan, hli⟩ := exists_linearIndependent Kf (M : Set W)
  rw [← hspan, rank_span_set hli]

  have hinj : Function.Injective fun r : O => r • (1 : Kf) := by
    simpa [Algebra.smul_def] using IsFractionRing.injective O Kf
  have hliO : LinearIndependent O (fun x : b => (x : W)) := hli.restrict_scalars hinj
  let w : b → M := fun x => ⟨x, hbM x.2⟩
  have hliw : LinearIndependent O w := LinearIndependent.of_comp M.subtype hliO
  have h1 := hliw.cardinal_le_rank
  have h2 : Module.rank O M < Cardinal.aleph0 := Module.rank_lt_aleph0 O M
  rw [Module.finrank, Cardinal.cast_toNat_of_lt_aleph0 h2]
  exact h1

/- English proof (translation)
Assume the negation of the conclusion as `hF'`. Establish `hli2 : LinearIndependent Kf (fun o : Option ι => Option.casesOn' o F c)` using `linearIndependent_option'.mpr ⟨hli, hF'⟩`. Set `S` to `Submodule.span Kf (M : Set W)`. Establish `hmem : ∀ o : Option ι, Option.casesOn' o F c ∈ S`. Introduce `o`.

Consider the cases of `o with`. Consider the case `none => exact Submodule.subset_span hF`. Consider the case `some i => exact hc i`. Set `w : Option ι → S` to `fun o => ⟨_, hmem o⟩`. Establish `hliw : LinearIndependent Kf w` using `LinearIndependent.of_comp S.subtype hli2`.

Establish `h1` using `hliw.cardinal_le_rank.trans (finrank_span_le (Kf := Kf) M)`. Rewrite `h1` using `[Cardinal.mk_fintype, Fintype.card_option]`. Normalize the coercions in `at h1`. Use linear arithmetic over natural numbers and integers.
-/
theorem mem_span_of_card {O Kf W ι : Type} [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] [IsFractionRing O Kf]
    [AddCommGroup W] [Module Kf W] [Module O W] [IsScalarTower O Kf W] (M : Submodule O W) [Module.Finite O M]
    [Fintype ι] (c : ι → W) (hli : LinearIndependent Kf c) (hc : ∀ i, c i ∈ Submodule.span Kf (M : Set W))
    (hcard : Fintype.card ι = Module.finrank O M) (F : W) (hF : F ∈ M) : F ∈ Submodule.span Kf (Set.range c) := by
  by_contra hF'
  have hli2 : LinearIndependent Kf (fun o : Option ι => Option.casesOn' o F c) :=
    linearIndependent_option'.mpr ⟨hli, hF'⟩
  let S := Submodule.span Kf (M : Set W)
  have hmem : ∀ o : Option ι, Option.casesOn' o F c ∈ S := by
    intro o
    cases o with
    | none => exact Submodule.subset_span hF
    | some i => exact hc i
  let w : Option ι → S := fun o => ⟨_, hmem o⟩
  have hliw : LinearIndependent Kf w := LinearIndependent.of_comp S.subtype hli2

  have h1 := hliw.cardinal_le_rank.trans (finrank_span_le (Kf := Kf) M)
  rw [Cardinal.mk_fintype, Fintype.card_option] at h1
  norm_cast at h1
  omega

end Formalism.L2.G
