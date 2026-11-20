import Development.EtaleCohomology.EtaleSheaves.LeafGeoCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Set Order TopologicalSpace Topology

namespace LateralTheory.E.LeafBdryPf

def univIC (Y : Type*) [TopologicalSpace Y] [IrreducibleSpace Y] : IrreducibleCloseds Y where
  carrier := univ
  isIrreducible' := IrreducibleSpace.isIrreducible_univ Y
  isClosed' := isClosed_univ

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Proceed by induction. Treat this case separately.

Treat this case separately. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

A detailed English derivation is pending.
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
Establish an intermediate fact. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Check the elementary cases of the proposition. Introduce a local definition for the expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Proceed by induction.

Treat this case separately. Treat this case separately. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem LeafBdry_of : LateralTheory.E.LeafGeoCut.LeafBdry := by
  intro Y B W p ι hι hirr hfin hne
  have : IsClosedImmersion (pullback.fst p ι) := inferInstance
  refine dim_lt_of_closedEmbedding _ (pullback.fst p ι).isClosedEmbedding hfin ?_
  rw [Scheme.Pullback.range_fst, ← preimage_compl]
  exact hne

end LateralTheory.E.LeafBdryPf

end
