import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerCrystallineCocycles
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles

namespace GlobalTheory.Proof.AbsoluteIrreducibilitySpan

open Formalism.MainNotions.N in

/- English proof (translation)
Use `set K := AlgebraicClosure k`. Establish `htop : Submodule.span K ((fun v : Fin a → k => (algebraMap k K) ∘ v) '' ((⊤ : Submodule k (Fin a → k)) : Set (Fin a → k))) = ⊤`. Rewrite using `[eq_top_iff, ← (Pi.basisFun K (Fin a)).span_eq]`. Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨j, rfl⟩`.

Use `⟨Pi.single j 1, trivial, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Distinguish the cases in `hx : x = j`. Substitute `hx` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[hx]`. Unfold `AbsIrrSub`. Rewrite using `[htop]`. Establish `: Nonempty (Fin a)` using `⟨⟨0, ha⟩⟩`. Use `⟨top_ne_bot, fun _ _ _ => trivial, fun W' _ hW => ?_⟩` and prove the remaining obligations.

Establish `key : ∀ X : Matrix (Fin a) (Fin a) k, ∀ v ∈ W', (X.map (algebraMap k K)).mulVec v ∈ W'`. Introduce `X`. Establish `hX : X ∈ Submodule.span k (Set.range M)` using `h ▸ Submodule.mem_top`. Proceed by induction on `hX using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨g, rfl⟩` from `hx`. Introduce `v hv`. Establish `h1 : (M g).map (algebraMap k K) = algebraMap k K (c g) • ((mapRep (algebraMap k K) ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)`. Use extensionality with `p q`. Simplify using `[hM, mapRep]`.

Rewrite using `[h1, Matrix.smul_mulVec]`. Conclude with `W'.smul_mem _ (hW g v hv)`. Consider the case `zero => intro v hv`. Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy`.

Introduce `v hv`. Rewrite using `[Matrix.map_add _ (map_add _), Matrix.add_mulVec]`. Conclude with `W'.add_mem (hx v hv) (hy v hv)`. Consider the case `smul r x _ hx`. Introduce `v hv`.

Establish `h1 : (r • x).map (algebraMap k K) = algebraMap k K r • x.map (algebraMap k K)`. Use extensionality with `p q`. Simplify using the standard rewrite rules. Rewrite using `[h1, Matrix.smul_mulVec]`. Conclude with `W'.smul_mem _ (hx v hv)`.

Distinguish the cases in `hb : W' = ⊥`. Conclude with `Or.inl hb`. Use `right`. Take `⟨v, hv, hv0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hb`. Take `⟨b, hb'⟩` from `Function.ne_iff.mp hv0`.

Rewrite using `[eq_top_iff, ← (Pi.basisFun K (Fin a)).span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Establish `h2` using `W'.smul_mem (v b)⁻¹ (key (Matrix.single j b 1) v hv)`. Establish `hb2 : v b ≠ 0` using `hb'`. Establish `h3 : (v b)⁻¹ • ((Matrix.single j b (1 : k)).map (algebraMap k K)).mulVec v = Pi.basisFun K (Fin a) j`.

Rewrite using `[Matrix.map_single, map_one, Matrix.single_mulVec]`. Use extensionality with `x`. Distinguish the cases in `hx : x = j`. Substitute `hx` using the available equality. Simplify using `[hb2]`.

Simplify using `[hx]`. Rewrite `h2` using `[h3]`. Conclude with `h2`.
-/
theorem absIrr_of_span {Γ k : Type} [Group Γ] [Field k] {a : ℕ} (ha : 0 < a) (ρ : Γ →* GL (Fin a) k)
    (M : Γ → Matrix (Fin a) (Fin a) k) (c : Γ → k)
    (hM : ∀ g, M g = c g • (ρ g : Matrix (Fin a) (Fin a) k))
    (h : Submodule.span k (Set.range M) = ⊤) : AbsIrrSub ρ ⊤ := by
  classical
  set K := AlgebraicClosure k
  have htop : Submodule.span K ((fun v : Fin a → k => (algebraMap k K) ∘ v) ''
      ((⊤ : Submodule k (Fin a → k)) : Set (Fin a → k))) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun K (Fin a)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    refine ⟨Pi.single j 1, trivial, ?_⟩
    ext x
    by_cases hx : x = j
    · subst hx; simp
    · simp [hx]
  unfold AbsIrrSub
  rw [htop]
  have : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  refine ⟨top_ne_bot, fun _ _ _ => trivial, fun W' _ hW => ?_⟩
  have key : ∀ X : Matrix (Fin a) (Fin a) k, ∀ v ∈ W', (X.map (algebraMap k K)).mulVec v ∈ W' := by
    intro X
    have hX : X ∈ Submodule.span k (Set.range M) := h ▸ Submodule.mem_top
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      intro v hv
      have h1 : (M g).map (algebraMap k K) = algebraMap k K (c g) •
          ((mapRep (algebraMap k K) ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) := by
        ext p q
        simp [hM, mapRep]
      rw [h1, Matrix.smul_mulVec]
      exact W'.smul_mem _ (hW g v hv)
    | zero => intro v hv; simp
    | add x y _ _ hx hy =>
      intro v hv
      rw [Matrix.map_add _ (map_add _), Matrix.add_mulVec]
      exact W'.add_mem (hx v hv) (hy v hv)
    | smul r x _ hx =>
      intro v hv
      have h1 : (r • x).map (algebraMap k K) = algebraMap k K r • x.map (algebraMap k K) := by
        ext p q
        simp
      rw [h1, Matrix.smul_mulVec]
      exact W'.smul_mem _ (hx v hv)
  by_cases hb : W' = ⊥
  · exact Or.inl hb
  right
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  obtain ⟨b, hb'⟩ := Function.ne_iff.mp hv0
  rw [eq_top_iff, ← (Pi.basisFun K (Fin a)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have h2 := W'.smul_mem (v b)⁻¹ (key (Matrix.single j b 1) v hv)
  have hb2 : v b ≠ 0 := hb'
  have h3 : (v b)⁻¹ • ((Matrix.single j b (1 : k)).map (algebraMap k K)).mulVec v = Pi.basisFun K (Fin a) j := by
    rw [Matrix.map_single, map_one, Matrix.single_mulVec]
    ext x
    by_cases hx : x = j
    · subst hx; simp [hb2]
    · simp [hx]
  rw [h3] at h2
  exact h2

end GlobalTheory.Proof.AbsoluteIrreducibilitySpan
