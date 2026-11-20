import Development.EtaleCohomology.EtaleSheaves.LeafGeoCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Set Order TopologicalSpace Topology

namespace LateralTheory.E.LeafBdryPf

def univIC (Y : Type*) [TopologicalSpace Y] [IrreducibleSpace Y] : IrreducibleCloseds Y where
  carrier := univ
  isIrreducible' := IrreducibleSpace.isIrreducible_univ Y
  isClosed' := isClosed_univ

/- English proof (translation)
Proceed by induction on `a using WithBot.recBotCoe with`. Consider the case `bot => exact absurd rfl ha`. Consider the case `coe a`. Proceed by induction on `b using WithBot.recBotCoe with`. Consider the case `bot => exact absurd h (by simp)`.

Consider the case `coe b`. Establish `hb' : b < ⊤`. Rewrite `hb` using `[← WithBot.coe_top]`. Conclude with `WithBot.coe_lt_coe.mp hb`. Establish `h' : a + 1 ≤ b` using `by exact_mod_cast h`.

Establish `ha' : a ≠ ⊤` using `(lt_of_le_of_lt (le_self_add.trans h') hb').ne`. Conclude with `WithBot.coe_lt_coe.mpr ((ENat.add_one_le_iff ha').mp h')`.
-/
lemma withBot_lt_of_add_one_le {a b : WithBot ℕ∞} (h : a + 1 ≤ b) (hb : b < ⊤) (ha : a ≠ ⊥) : a < b := by
  induction a using WithBot.recBotCoe with
  | bot => exact absurd rfl ha
  | coe a =>
    induction b using WithBot.recBotCoe with
    | bot => exact absurd h (by simp)
    | coe b =>
      have hb' : b < ⊤ := by
        rw [← WithBot.coe_top] at hb
        exact WithBot.coe_lt_coe.mp hb
      have h' : a + 1 ≤ b := by exact_mod_cast h
      have ha' : a ≠ ⊤ := (lt_of_le_of_lt (le_self_add.trans h') hb').ne
      exact WithBot.coe_lt_coe.mpr ((ENat.add_one_le_iff ha').mp h')

/- English proof (translation)
Establish `hY : Nonempty (IrreducibleCloseds Y)` using `⟨univIC Y⟩`. Distinguish the cases in `hZ : Nonempty (IrreducibleCloseds Z)`. Establish `hlt : ∀ c : IrreducibleCloseds Z, IrreducibleCloseds.map f hf.continuous c < univIC Y`. Introduce `c`. Use `lt_of_le_of_ne (fun x _ => trivial) ?_` and prove the remaining obligations.

Introduce `heq`. Take `⟨y, hy⟩` from `hne`. Establish `h1 : (IrreducibleCloseds.map f hf.continuous c : Set Y) ⊆ range f`. Rewrite using `[IrreducibleCloseds.coe_map]`. Conclude with `closure_minimal (image_subset_range _ _) hf.isClosed_range`.

Apply `hy` to reduce the goal to its premises. Apply `h1` to reduce the goal to its premises. Rewrite using `[heq]`. Discharge the goal by the elementary cases of `trivial`. Set `g : WithTop (IrreducibleCloseds Z) → IrreducibleCloseds Y` to `fun o => WithTop.recTopCoe (univIC Y) (IrreducibleCloseds.map f hf.continuous) o`.

Establish `hg : StrictMono g`. Introduce `a b hab`. Proceed by induction on `a using WithTop.recTopCoe with`. Consider the case `top => exact absurd hab (by simp)`. Consider the case `coe a`.

Proceed by induction on `b using WithTop.recTopCoe with`. Consider the case `top => exact hlt a`. Consider the case `coe b`. Conclude with `IrreducibleCloseds.map_strictMono_of_isInducing hf.isInducing (WithTop.coe_lt_coe.mp hab)`. Establish `h` using `krullDim_le_of_strictMono g hg`.

Rewrite `h` using `[krullDim_WithTop]`. Conclude with `withBot_lt_of_add_one_le h hfin (bot_lt_krullDim).ne'`. Rewrite `hZ` using `[not_nonempty_iff]`. Establish `: topologicalKrullDim Z = ⊥` using `krullDim_eq_bot`. Rewrite using `[this]`.

Conclude with `bot_lt_krullDim`.
-/
theorem dim_lt_of_closedEmbedding {Z Y : Type*} [TopologicalSpace Z] [TopologicalSpace Y] [IrreducibleSpace Y]
    (f : Z → Y) (hf : IsClosedEmbedding f) (hfin : topologicalKrullDim Y < ⊤) (hne : (range f)ᶜ.Nonempty) :
    topologicalKrullDim Z < topologicalKrullDim Y := by
  have hY : Nonempty (IrreducibleCloseds Y) := ⟨univIC Y⟩
  by_cases hZ : Nonempty (IrreducibleCloseds Z)
  · have hlt : ∀ c : IrreducibleCloseds Z, IrreducibleCloseds.map f hf.continuous c < univIC Y := by
      intro c
      refine lt_of_le_of_ne (fun x _ => trivial) ?_
      intro heq
      obtain ⟨y, hy⟩ := hne
      have h1 : (IrreducibleCloseds.map f hf.continuous c : Set Y) ⊆ range f := by
        rw [IrreducibleCloseds.coe_map]
        exact closure_minimal (image_subset_range _ _) hf.isClosed_range
      apply hy
      apply h1
      rw [heq]
      trivial
    let g : WithTop (IrreducibleCloseds Z) → IrreducibleCloseds Y :=
      fun o => WithTop.recTopCoe (univIC Y) (IrreducibleCloseds.map f hf.continuous) o
    have hg : StrictMono g := by
      intro a b hab
      induction a using WithTop.recTopCoe with
      | top => exact absurd hab (by simp)
      | coe a =>
        induction b using WithTop.recTopCoe with
        | top => exact hlt a
        | coe b =>
          exact IrreducibleCloseds.map_strictMono_of_isInducing hf.isInducing (WithTop.coe_lt_coe.mp hab)
    have h := krullDim_le_of_strictMono g hg
    rw [krullDim_WithTop] at h
    exact withBot_lt_of_add_one_le h hfin (bot_lt_krullDim).ne'
  · rw [not_nonempty_iff] at hZ
    have : topologicalKrullDim Z = ⊥ := krullDim_eq_bot
    rw [this]
    exact bot_lt_krullDim

/- English proof (translation)
Introduce `Y B W p ι hι hirr hfin hne`. Establish `: IsClosedImmersion (pullback.fst p ι)` using `inferInstance`. Use `dim_lt_of_closedEmbedding _ (pullback.fst p ι).isClosedEmbedding hfin ?_` and prove the remaining obligations. Rewrite using `[Scheme.Pullback.range_fst, ← preimage_compl]`. Conclude with `hne`.
-/
theorem LeafBdry_of : LateralTheory.E.LeafGeoCut.LeafBdry := by
  intro Y B W p ι hι hirr hfin hne
  have : IsClosedImmersion (pullback.fst p ι) := inferInstance
  refine dim_lt_of_closedEmbedding _ (pullback.fst p ι).isClosedEmbedding hfin ?_
  rw [Scheme.Pullback.range_fst, ← preimage_compl]
  exact hne

end LateralTheory.E.LeafBdryPf

end
