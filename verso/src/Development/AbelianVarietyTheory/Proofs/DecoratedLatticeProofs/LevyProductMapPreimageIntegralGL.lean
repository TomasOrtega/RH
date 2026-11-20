import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdRFJCoe
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

namespace GlobalTheory.HaarR

/- English proof (translation)
Take `⟨h1, h2⟩` from `(GlobalTheory.SplitFlip.mem_KO_iff g).1 hg`. Establish `key : ∀ x : GL n k, (∀ i j, x.val i j ∈ 𝒪[k]) → ∀ i j, (embX c x).val i j ∈ 𝒪[k]`. Introduce `x hx i j`. Rewrite using `[GlobalTheory.RootEx.Radical.embX_val]`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j`.

Simplify using `using hx i j`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using `only [fromBlocks_apply₂₂, Matrix.one_apply] split_ifs`. Conclude with `one_mem _`.

Conclude with `zero_mem _`. Use `(GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨key g h1, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_inv]`. Conclude with `key _ h2`.
-/
theorem rootExchangeEmbedGL_mem_integralGL {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] (c : ℕ) {g : GL n k} (hg : g ∈ KO k n) :
    embX c g ∈ KO k (n ⊕ Fin c) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SplitFlip.mem_KO_iff g).1 hg
  have key : ∀ x : GL n k, (∀ i j, x.val i j ∈ 𝒪[k]) → ∀ i j, (embX c x).val i j ∈ 𝒪[k] := by
    intro x hx i j
    rw [GlobalTheory.RootEx.Radical.embX_val]
    rcases i with i | i <;> rcases j with j | j
    · simpa using hx i j
    · simp
    · simp
    · simp only [fromBlocks_apply₂₂, Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
  refine (GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨key g h1, ?_⟩
  rw [← map_inv]
  exact key _ h2

/- English proof (translation)
Introduce `k _ _ _ _ n _ _ c p`. Use extensionality with `⟨g, u⟩`. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq, prodR_coe, Set.mem_prod, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Take `⟨h1, h2⟩` from `(GlobalTheory.SplitFlip.mem_KO_iff _).1 h`. Establish `hg : g ∈ KO k n`. Use `(GlobalTheory.SplitFlip.mem_KO_iff g).2 ⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Establish `e` using `GlobalTheory.RootEx.Radical.toBlocks₁₁_embX_mul (c := c) g u.2`. Use `h1 (Sum.inl i) (Sum.inl j)` as an intermediate fact.

Rewrite using `[← e]`. Conclude with `this`. Establish `hu' : embX c g * ((u : GL (n ⊕ Fin c) k))⁻¹ * (embX c g)⁻¹ ∈ N k n c p` using `GlobalTheory.RootEx.Radical.conj_mem g (inv_mem u.2)`. Establish `e` using `GlobalTheory.RootEx.Radical.toBlocks₁₁_embX_mul (c := c) g⁻¹ hu'`. Establish `hinv : (embX c g * (u : GL (n ⊕ Fin c) k))⁻¹ = embX c g⁻¹ * (embX c g * ((u : GL (n ⊕ Fin c) k))⁻¹ * (embX c g)⁻¹)`.

Rewrite using `[map_inv]`. Use `group`. Use `h2 (Sum.inl i) (Sum.inl j)` as an intermediate fact. Rewrite `this` using `[hinv]`. Rewrite using `[← e]`.

Conclude with `this`. Use `⟨hg, ?_⟩` and prove the remaining obligations. Use `mul_mem (inv_mem (rootExchangeEmbedGL_mem_integralGL c hg)) h` as an intermediate fact. Rewrite `this` using `[inv_mul_cancel_left]`. Then use the resulting hypothesis. Introduce and unpack `⟨hg, hu⟩`.

Conclude with `mul_mem (rootExchangeEmbedGL_mem_integralGL c hg) hu`.
-/
theorem prodR_preimage_KO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), prodR (k := k) (n := n) (c := c) p ⁻¹' {x | (x : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} = (KO k n : Set (GL n k)) ×ˢ {u : N k n c p | (u : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} := by
  intro k _ _ _ _ n _ _ c p
  ext ⟨g, u⟩
  simp only [Set.mem_preimage, Set.mem_setOf_eq, prodR_coe, Set.mem_prod, SetLike.mem_coe]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := (GlobalTheory.SplitFlip.mem_KO_iff _).1 h
    have hg : g ∈ KO k n := by
      refine (GlobalTheory.SplitFlip.mem_KO_iff g).2 ⟨fun i j => ?_, fun i j => ?_⟩
      · have e := GlobalTheory.RootEx.Radical.toBlocks₁₁_embX_mul (c := c) g u.2
        have := h1 (Sum.inl i) (Sum.inl j)
        rw [← e]; exact this
      · have hu' : embX c g * ((u : GL (n ⊕ Fin c) k))⁻¹ * (embX c g)⁻¹ ∈ N k n c p :=
          GlobalTheory.RootEx.Radical.conj_mem g (inv_mem u.2)
        have e := GlobalTheory.RootEx.Radical.toBlocks₁₁_embX_mul (c := c) g⁻¹ hu'
        have hinv : (embX c g * (u : GL (n ⊕ Fin c) k))⁻¹
            = embX c g⁻¹ * (embX c g * ((u : GL (n ⊕ Fin c) k))⁻¹ * (embX c g)⁻¹) := by
          rw [map_inv]; group
        have := h2 (Sum.inl i) (Sum.inl j)
        rw [hinv] at this
        rw [← e]
        exact this
    refine ⟨hg, ?_⟩
    have := mul_mem (inv_mem (rootExchangeEmbedGL_mem_integralGL c hg)) h
    rwa [inv_mul_cancel_left] at this
  · rintro ⟨hg, hu⟩
    exact mul_mem (rootExchangeEmbedGL_mem_integralGL c hg) hu

end GlobalTheory.HaarR
