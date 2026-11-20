import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import GroundTheory.AutomorphicForms.GeometricLemma
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.SizeCells

/- English proof (translation)
Introduce `α _ _ N m _ _ β' _ _ m' _ _ e e' b`. Take `⟨f⟩` from `b.nonempty_rows`. Take `⟨g⟩` from `b.nonempty_cols`. Set `A : (Σ i, Σ j, Fin (b.1 i j)) ≃ Fin N` to `(Equiv.sigmaCongrRight f).trans e`. Set `B : (Σ j, Σ i, Fin (b.1 i j)) ≃ Fin N` to `(Equiv.sigmaCongrRight g).trans e'`.

Set `S : (Σ i, Σ j, Fin (b.1 i j)) ≃ (Σ j, Σ i, Fin (b.1 i j))` to `{ toFun := fun p => ⟨p.2.1, p.1, p.2.2⟩ invFun := fun p => ⟨p.2.1, p.1, p.2.2⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl }`. Set `w : Equiv.Perm (Fin N)` to `(B.symm.trans S.symm).trans A`. Establish `hA : ∀ p, blk e (A p) = p.1`. Introduce `p`. Simplify using `[A, blk]`.

Establish `hB : ∀ p, blk e' (B p) = p.1`. Introduce `p`. Simplify using `[B, blk]`. Establish `hw : ∀ p, w.symm (A p) = B (S p)`. Introduce `p`.

Simplify using `[w]`. Use `⟨w, fun i j => ?_⟩` and prove the remaining obligations. Establish `himg : (Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j) = Finset.univ.image (fun t : Fin (b.1 i j) => A ⟨i, j, t⟩)`. Use extensionality with `x`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Take `⟨⟨i', j', t⟩, rfl⟩` from `A.surjective x`. Rewrite `h1` using `[hA]`. Rewrite `h2` using `[hw, hB]`.

Simplify using `only [S, Equiv.coe_fn_mk] at h1 h2`. Substitute `h1` using the available equality. Substitute `h2` using the available equality. Conclude with `⟨t, rfl⟩`. Introduce and unpack `⟨t, rfl⟩`.

Use `⟨hA _, ?_⟩` and prove the remaining obligations. Rewrite using `[hw, hB]`. Both sides reduce to the same expression. Rewrite using `[himg, Finset.card_image_of_injective _ (fun s t h => by simpa using A.injective h)]`. Simplify using the standard rewrite rules.
-/
theorem exists_perm_cell_sizes : ∀ {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ Fin N) (e' : (Σ j, m' j) ≃ Fin N) (b : SizeMatrix m m'), ∃ w : Equiv.Perm (Fin N), ∀ i j, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = b.1 i j := by
  intro α _ _ N m _ _ β' _ _ m' _ _ e e' b
  obtain ⟨f⟩ := b.nonempty_rows
  obtain ⟨g⟩ := b.nonempty_cols
  let A : (Σ i, Σ j, Fin (b.1 i j)) ≃ Fin N := (Equiv.sigmaCongrRight f).trans e
  let B : (Σ j, Σ i, Fin (b.1 i j)) ≃ Fin N := (Equiv.sigmaCongrRight g).trans e'
  let S : (Σ i, Σ j, Fin (b.1 i j)) ≃ (Σ j, Σ i, Fin (b.1 i j)) :=
    { toFun := fun p => ⟨p.2.1, p.1, p.2.2⟩
      invFun := fun p => ⟨p.2.1, p.1, p.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let w : Equiv.Perm (Fin N) := (B.symm.trans S.symm).trans A
  have hA : ∀ p, blk e (A p) = p.1 := by
    intro p
    simp [A, blk]
  have hB : ∀ p, blk e' (B p) = p.1 := by
    intro p
    simp [B, blk]
  have hw : ∀ p, w.symm (A p) = B (S p) := by
    intro p
    simp [w]
  refine ⟨w, fun i j => ?_⟩
  have himg : (Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j) =
      Finset.univ.image (fun t : Fin (b.1 i j) => A ⟨i, j, t⟩) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨⟨i', j', t⟩, rfl⟩ := A.surjective x
      rw [hA] at h1
      rw [hw, hB] at h2
      dsimp only [S, Equiv.coe_fn_mk] at h1 h2
      subst h1
      subst h2
      exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      refine ⟨hA _, ?_⟩
      rw [hw, hB]
      rfl
  rw [himg, Finset.card_image_of_injective _ (fun s t h => by simpa using A.injective h)]
  simp

end GlobalTheory.CompanionTheory.SizeCells
