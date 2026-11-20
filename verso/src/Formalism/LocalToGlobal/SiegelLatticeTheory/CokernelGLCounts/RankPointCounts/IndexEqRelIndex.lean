import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CardCells

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.CountAb

variable {G 𝒳 : Type} [Group G] [MulAction G 𝒳]
variable (W : 𝒳) (S N' K : Subgroup G) (π : G →* G) (g : G)

/- English proof (translation)
Set `e : ↥(K ⊓ S) →* ↥(Ak S K)` to `{ toFun := fun x => ⟨⟨x.1, x.2.1⟩, by simp only [Ak, Subgroup.mem_subgroupOf]; exact x.2.2⟩ map_one' := rfl map_mul' := fun _ _ => rfl }`. Establish `he : Function.Surjective e` using `fun a => ⟨⟨a.1.1, a.1.2, by have h := a.2; simp only [Ak, Subgroup.mem_subgroupOf] at h; exact h⟩, rfl⟩`. Rewrite using `[← Subgroup.index_comap_of_surjective _ he]`. Unfold `Subgroup.relIndex`. Use `congr 1`.

Use extensionality with `x`. Simplify using `only [Subgroup.mem_comap, Subgroup.mem_map, Subgroup.mem_subgroupOf]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, hkx⟩`. Use `⟨k.1, ?_, ?_⟩` and prove the remaining obligations.

Simplify `hk` using `[Hk, Subgroup.mem_subgroupOf]`. Establish `h2` using `congrArg (fun y : ↥(Ak S K) => ((y : ↥K) : G)) hkx`. Simplify `h2` using `[πk, e]`. Introduce and unpack `⟨y, hy, hyx⟩`. Use `⟨⟨y, hy.1⟩, ?_, ?_⟩` and prove the remaining obligations.

Simplify `hy` using `[Hk, Subgroup.mem_subgroupOf]`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Simplify `hyx` using `[πk, e]`.
-/
theorem index_eq_relIndex (hD : Data W S N' K π) :
    ((Hk W K g).map (πk W S N' K π hD)).index = ((Hs W K g).map π).relIndex (K ⊓ S) := by
  let e : ↥(K ⊓ S) →* ↥(Ak S K) :=
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, by simp only [Ak, Subgroup.mem_subgroupOf]; exact x.2.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have he : Function.Surjective e := fun a =>
    ⟨⟨a.1.1, a.1.2, by have h := a.2; simp only [Ak, Subgroup.mem_subgroupOf] at h; exact h⟩, rfl⟩
  rw [← Subgroup.index_comap_of_surjective _ he]
  unfold Subgroup.relIndex
  congr 1
  ext x
  simp only [Subgroup.mem_comap, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨k, hk, hkx⟩
    refine ⟨k.1, ?_, ?_⟩
    · simpa [Hk, Subgroup.mem_subgroupOf] using hk
    · have h2 := congrArg (fun y : ↥(Ak S K) => ((y : ↥K) : G)) hkx
      simpa [πk, e] using h2
  · rintro ⟨y, hy, hyx⟩
    refine ⟨⟨y, hy.1⟩, ?_, ?_⟩
    · simpa [Hk, Subgroup.mem_subgroupOf] using hy
    · apply Subtype.ext
      apply Subtype.ext
      simpa [πk, e] using hyx

/- English proof (translation)
The claim follows from `(card_cells W S N' K π g hD).trans (index_eq_relIndex W S N' K π g hD)`.
-/
theorem card_cells' (hD : Data W S N' K π) :
    Nat.card (Quotient (cellRel W N' K g)) = ((Hs W K g).map π).relIndex (K ⊓ S) := (card_cells W S N' K π g hD).trans (index_eq_relIndex W S N' K π g hD)

end Formalism.L2.SG.Pf.CountAb
