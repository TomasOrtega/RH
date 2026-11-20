import Mathlib
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
open NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV

namespace GlobalTheory

/- English proof (translation)
Introduce `L _ _ _ s φ n r h g hφ hg`. Establish `key : ∀ a b, (g : Matrix (Fin n) (Fin n) (kP s.w)) a b = 0 ↔ Valued.v ((h : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b) < 1`. Introduce `a b`. Take `⟨hab, e⟩` from `hg a b`. Rewrite using `[e, hφ]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_blockTri]`. Prove the components needed by the constructor for the conclusion. Introduce `H a b ha hb`. Rewrite using `[← key]`.

Apply `H` to reduce the goal to its premises. Simplify using `[blk2, hb, Nat.not_lt.mpr ha]`. Introduce `H i j hij`. Rewrite using `[key]`. Unfold `blk2 at hij`.

Distinguish the cases in `hj : j.val < r`. Distinguish the cases in `hi : i.val < r`. Simplify using `[hj, hi] at hij`. Conclude with `H i j (Nat.not_lt.mp hi) hj`. Apply the tactic sequence `by_cases hi : i.val < r <;> simp [hj, hi] at hij`.

Introduce `hT`. Set `M : Matrix {x : Fin n // r ≤ x.val} {x : Fin n // r ≤ x.val} (s.v.adicCompletionIntegers (maximalRealSubfield L))` to `fun a b => ⟨(h : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a.1 b.1, (hg a.1 b.1).1⟩`. Establish `hdet : NG.detDD s r h = (s.v.adicCompletionIntegers (maximalRealSubfield L)).subtype M.det`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression.

Use `⟨hdet ▸ (M.det).2, ?_⟩` and prove the remaining obligations. Establish `e1 : (⟨NG.detDD s r h, hdet ▸ (M.det).2⟩ : s.v.adicCompletionIntegers (maximalRealSubfield L)) = M.det` using `Subtype.ext hdet`. Rewrite using `[e1, RingHom.map_det, diag_block_det_val 1 hT]`. Set `e : {a : Fin n // blk2 r a = 1} ≃ {x : Fin n // r ≤ x.val}` to `Equiv.subtypeEquivRight (fun a => by`. Unfold `blk2`.

Use `split_ifs with h'`. Conclude with `⟨fun h0 => absurd h0 (by decide), fun h0 => absurd h' (Nat.not_lt.mpr h0)⟩`. Conclude with `⟨fun _ => Nat.not_lt.mp h', fun _ => rfl⟩)`. Rewrite using `[← Matrix.det_submatrix_equiv_self e]`. Use `congr 1`.

Use extensionality with `a b`. Simplify using `only [Matrix.submatrix_apply, Matrix.map_apply, M]`. Conclude with `(hg (e a).1 (e b).1).2`.
-/
theorem reduction_blockTri_detDD : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L) (φ : s.v.adicCompletionIntegers (maximalRealSubfield L) →+* kP s.w) (n r : ℕ) (h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) (g : GL (Fin n) (kP s.w)), (∀ x, φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield L)) < 1) → (∀ a b, ∃ hab : (h : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield L), (g : Matrix (Fin n) (Fin n) (kP s.w)) a b = φ ⟨_, hab⟩) → (g ∈ blockTri (blk2 r) ↔ ∀ a b : Fin n, r ≤ a.val → b.val < r → Valued.v ((h : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b) < 1) ∧ (g ∈ blockTri (blk2 r) → ∃ hd : NG.detDD s r h ∈ s.v.adicCompletionIntegers (maximalRealSubfield L), ((dBlk (blk2 r) 1 g : (kP s.w)ˣ) : kP s.w) = φ ⟨_, hd⟩) := by
  intro L _ _ _ s φ n r h g hφ hg
  have key : ∀ a b, (g : Matrix (Fin n) (Fin n) (kP s.w)) a b = 0 ↔
      Valued.v ((h : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b) < 1 := by
    intro a b
    obtain ⟨hab, e⟩ := hg a b
    rw [e, hφ]
  refine ⟨?_, ?_⟩
  · rw [mem_blockTri]
    constructor
    · intro H a b ha hb
      rw [← key]
      apply H
      simp [blk2, hb, Nat.not_lt.mpr ha]
    · intro H i j hij
      rw [key]
      unfold blk2 at hij
      by_cases hj : j.val < r
      · by_cases hi : i.val < r
        · simp [hj, hi] at hij
        · exact H i j (Nat.not_lt.mp hi) hj
      · by_cases hi : i.val < r <;> simp [hj, hi] at hij
  · intro hT
    let M : Matrix {x : Fin n // r ≤ x.val} {x : Fin n // r ≤ x.val} (s.v.adicCompletionIntegers (maximalRealSubfield L)) :=
      fun a b => ⟨(h : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a.1 b.1, (hg a.1 b.1).1⟩
    have hdet : NG.detDD s r h = (s.v.adicCompletionIntegers (maximalRealSubfield L)).subtype M.det := by
      rw [RingHom.map_det]
      rfl
    refine ⟨hdet ▸ (M.det).2, ?_⟩
    have e1 : (⟨NG.detDD s r h, hdet ▸ (M.det).2⟩ : s.v.adicCompletionIntegers (maximalRealSubfield L)) = M.det :=
      Subtype.ext hdet
    rw [e1, RingHom.map_det, diag_block_det_val 1 hT]
    let e : {a : Fin n // blk2 r a = 1} ≃ {x : Fin n // r ≤ x.val} :=
      Equiv.subtypeEquivRight (fun a => by
        unfold blk2
        split_ifs with h'
        · exact ⟨fun h0 => absurd h0 (by decide), fun h0 => absurd h' (Nat.not_lt.mpr h0)⟩
        · exact ⟨fun _ => Nat.not_lt.mp h', fun _ => rfl⟩)
    rw [← Matrix.det_submatrix_equiv_self e]
    congr 1
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.map_apply, M]
    exact (hg (e a).1 (e b).1).2

end GlobalTheory
