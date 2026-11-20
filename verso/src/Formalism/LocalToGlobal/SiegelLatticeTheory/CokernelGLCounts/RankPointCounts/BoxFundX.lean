import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CovolOneEqOne

noncomputable section

open MeasureTheory

namespace Formalism.L2.SG.NGCut.SplitEmbedding

/- English proof (translation)
Set `w : P → (ι → P → ℂ) → (ι → ℂ)` to `fun p γ => τ p γ + fun v => x v p + BX p (γ v) (x v)`. Set `c : P → (ι → P → ℂ) → (ι → ℂ)` to `fun p γ => ((hFd p (w p γ)).exists.choose : ι → ℂ) + τ p γ`. Establish `hloc : ∀ p (γ γ' : ι → P → ℂ), (∀ q, h q < h p → ∀ v, γ v q = γ' v q) → c p γ = c p γ'`. Introduce `p γ γ' hg`. Establish `h1 : τ p γ = τ p γ'` using `hτ p γ γ' hg`.

Establish `h2 : w p γ = w p γ'` using `by show (τ p γ + fun v => x v p + BX p (γ v) (x v)) = τ p γ' + fun v => x v p + BX p (γ' v) (x v)`. Rewrite using `[h1]`. Use `congr 1`. Use function extensionality and compare the values at `v`. Rewrite using `[hBd p (γ v) (γ' v) (x v) (x v) (fun q hq => ⟨hg q hq v, rfl⟩)]`.

Establish `hch : ∀ u u' : ι → ℂ, u = u' → ((hFd p u).exists.choose : ι → ℂ) = ((hFd p u').exists.choose : ι → ℂ)`. Introduce and unpack `u _ rfl`. Both sides reduce to the same expression. Use `show ((hFd p (w p γ)).exists.choose : ι → ℂ) + τ p γ = ((hFd p (w p γ')).exists.choose : ι → ℂ) + τ p γ'`. Rewrite using `[h1, hch _ _ h2]`.

Establish `key : ∀ p (γ : ι → P → ℂ), ((fun v => γ v p) - τ p γ ∈ A p ∧ (fun v => lawX BX γ x v p) ∈ F p) ↔ (fun v => γ v p) = c p γ`. Introduce `p γ`. Take `⟨a, ha, huniq⟩` from `hFd p (w p γ)`. Establish `hc : c p γ = (a : ι → ℂ) + τ p γ` using `by show ((hFd p (w p γ)).exists.choose : ι → ℂ) + τ p γ = (a : ι → ℂ) + τ p γ`. Rewrite using `[huniq _ (hFd p (w p γ)).exists.choose_spec]`.

Establish `hlaw : (fun v => lawX BX γ x v p) = ((fun v => γ v p) - τ p γ) + w p γ`. Use function extensionality and compare the values at `v`. Simplify using `only [lawX, w, Pi.add_apply, Pi.sub_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc, hlaw]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hA, hF⟩`. Establish `e` using `congrArg Subtype.val (huniq ⟨_, hA⟩ hF)`. Simplify using `only at e`. Rewrite using `[← e]`.

Normalize the expressions using the abelian group laws. Introduce `hg`. Rewrite using `[hg, add_sub_cancel_right]`. Conclude with `⟨a.2, ha⟩`. Set `Φ : (ι → P → ℂ) → (ι → P → ℂ)` to `fun γ v p => c p γ v`.

Establish `hit : ∀ k (γ γ' : ι → P → ℂ), ∀ p, h p < k → ∀ v, (Φ^[k] γ) v p = (Φ^[k] γ') v p`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro γ γ' p hp`. Conclude with `absurd hp (Nat.not_lt_zero _)`.

Consider the case `succ k ih`. Introduce `γ γ' p hp v`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply']`. Use `show c p (Φ^[k] γ) v = c p (Φ^[k] γ') v`. Rewrite using `[hloc p _ _ (fun q hq v => ih γ γ' q (by omega) v)]`.

Establish `hN : ∀ p, h p < Finset.univ.sup h + 1` using `fun p => Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ p))`. Establish `hcond : ∀ γ : ι → P → ℂ, ((∀ p, (fun v => γ v p) - τ p γ ∈ A p) ∧ lawX BX γ x ∈ {y : ι → P → ℂ | ∀ p, (fun v => y v p) ∈ F p}) ↔ Φ γ = γ`. Introduce `γ`. Rewrite using `[Set.mem_setOf_eq, ← forall_and, forall_congr' (fun p => key p γ)]`. Prove the components needed by the constructor for the conclusion.

Introduce `H`. Use function extensionality and compare the values at `v p`. Conclude with `(congrFun (H p) v).symm`. Introduce `H p`. Use function extensionality and compare the values at `v`.

Conclude with `(congrFun (congrFun H v) p).symm`. Use `⟨Φ^[Finset.univ.sup h + 1] 0, (hcond _).2 ?_, fun γ hγ => ?_⟩` and prove the remaining obligations. Rewrite using `[← Function.iterate_succ_apply' Φ _ 0, Function.iterate_succ_apply]`. Use function extensionality and compare the values at `v p`. Conclude with `hit _ (Φ 0) 0 p (hN p) v`.

Establish `e1 : Φ^[Finset.univ.sup h + 1] γ = γ` using `Function.iterate_fixed ((hcond γ).1 hγ) _`. Use function extensionality and compare the values at `v p`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem box_fundX {ι P : Type} [Fintype P] [DecidableEq P] (h : P → ℕ) (BX : P → (P → ℂ) → (P → ℂ) → ℂ)
    (hBd : ∀ p (x x' y y' : P → ℂ), (∀ q, h q < h p → x q = x' q ∧ y q = y' q) → BX p x y = BX p x' y')
    (τ : P → (ι → P → ℂ) → (ι → ℂ))
    (hτ : ∀ p (x x' : ι → P → ℂ), (∀ q, h q < h p → ∀ v, x v q = x' v q) → τ p x = τ p x')
    (A : P → AddSubgroup (ι → ℂ)) (F : P → Set (ι → ℂ)) (hFd : ∀ p (v : ι → ℂ), ∃! a : A p, (a : ι → ℂ) + v ∈ F p)
    (x : ι → P → ℂ) :
    ∃! γ : ι → P → ℂ, (∀ p, (fun v => γ v p) - τ p γ ∈ A p) ∧
      lawX BX γ x ∈ {y : ι → P → ℂ | ∀ p, (fun v => y v p) ∈ F p} := by
  classical
  let w : P → (ι → P → ℂ) → (ι → ℂ) := fun p γ => τ p γ + fun v => x v p + BX p (γ v) (x v)
  let c : P → (ι → P → ℂ) → (ι → ℂ) := fun p γ =>
    ((hFd p (w p γ)).exists.choose : ι → ℂ) + τ p γ
  have hloc : ∀ p (γ γ' : ι → P → ℂ), (∀ q, h q < h p → ∀ v, γ v q = γ' v q) → c p γ = c p γ' := by
    intro p γ γ' hg
    have h1 : τ p γ = τ p γ' := hτ p γ γ' hg
    have h2 : w p γ = w p γ' := by
      show (τ p γ + fun v => x v p + BX p (γ v) (x v)) = τ p γ' + fun v => x v p + BX p (γ' v) (x v)
      rw [h1]
      congr 1
      funext v
      rw [hBd p (γ v) (γ' v) (x v) (x v) (fun q hq => ⟨hg q hq v, rfl⟩)]
    have hch : ∀ u u' : ι → ℂ, u = u' →
        ((hFd p u).exists.choose : ι → ℂ) = ((hFd p u').exists.choose : ι → ℂ) := by
      rintro u _ rfl
      rfl
    show ((hFd p (w p γ)).exists.choose : ι → ℂ) + τ p γ = ((hFd p (w p γ')).exists.choose : ι → ℂ) + τ p γ'
    rw [h1, hch _ _ h2]
  have key : ∀ p (γ : ι → P → ℂ), ((fun v => γ v p) - τ p γ ∈ A p ∧ (fun v => lawX BX γ x v p) ∈ F p) ↔
      (fun v => γ v p) = c p γ := by
    intro p γ
    obtain ⟨a, ha, huniq⟩ := hFd p (w p γ)
    have hc : c p γ = (a : ι → ℂ) + τ p γ := by
      show ((hFd p (w p γ)).exists.choose : ι → ℂ) + τ p γ = (a : ι → ℂ) + τ p γ
      rw [huniq _ (hFd p (w p γ)).exists.choose_spec]
    have hlaw : (fun v => lawX BX γ x v p) = ((fun v => γ v p) - τ p γ) + w p γ := by
      funext v
      simp only [lawX, w, Pi.add_apply, Pi.sub_apply]
      ring
    rw [hc, hlaw]
    constructor
    · rintro ⟨hA, hF⟩
      have e := congrArg Subtype.val (huniq ⟨_, hA⟩ hF)
      simp only at e
      rw [← e]
      abel
    · intro hg
      rw [hg, add_sub_cancel_right]
      exact ⟨a.2, ha⟩
  let Φ : (ι → P → ℂ) → (ι → P → ℂ) := fun γ v p => c p γ v
  have hit : ∀ k (γ γ' : ι → P → ℂ), ∀ p, h p < k → ∀ v, (Φ^[k] γ) v p = (Φ^[k] γ') v p := by
    intro k
    induction k with
    | zero => intro γ γ' p hp; exact absurd hp (Nat.not_lt_zero _)
    | succ k ih =>
      intro γ γ' p hp v
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      show c p (Φ^[k] γ) v = c p (Φ^[k] γ') v
      rw [hloc p _ _ (fun q hq v => ih γ γ' q (by omega) v)]
  have hN : ∀ p, h p < Finset.univ.sup h + 1 := fun p =>
    Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ p))
  have hcond : ∀ γ : ι → P → ℂ, ((∀ p, (fun v => γ v p) - τ p γ ∈ A p) ∧
      lawX BX γ x ∈ {y : ι → P → ℂ | ∀ p, (fun v => y v p) ∈ F p}) ↔ Φ γ = γ := by
    intro γ
    rw [Set.mem_setOf_eq, ← forall_and, forall_congr' (fun p => key p γ)]
    constructor
    · intro H
      funext v p
      exact (congrFun (H p) v).symm
    · intro H p
      funext v
      exact (congrFun (congrFun H v) p).symm
  refine ⟨Φ^[Finset.univ.sup h + 1] 0, (hcond _).2 ?_, fun γ hγ => ?_⟩
  · rw [← Function.iterate_succ_apply' Φ _ 0, Function.iterate_succ_apply]
    funext v p
    exact hit _ (Φ 0) 0 p (hN p) v
  · have e1 : Φ^[Finset.univ.sup h + 1] γ = γ := Function.iterate_fixed ((hcond γ).1 hγ) _
    funext v p
    calc γ v p = (Φ^[Finset.univ.sup h + 1] γ) v p := by rw [e1]
      _ = _ := hit _ γ 0 p (hN p) v

end Formalism.L2.SG.NGCut.SplitEmbedding
