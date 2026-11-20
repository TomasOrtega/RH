import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `X _ _ q hneg hcube hpos N`. Establish `h0 : q 0 = 0`. Use `hcube 0 0 0` as an intermediate fact. Simplify using `only [add_zero] at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hnn : ∀ a, 0 ≤ q a`. Introduce `a`. Distinguish the cases in `ha : a = 0`. Simplify using `[ha, h0]`. Combine the linear relations using `[hpos a ha]`.

Set `B : X → X → ℤ` to `fun a b => q (a + b) - q a - q b`. Establish `Bsymm : ∀ a b, B a b = B b a`. Introduce `a b`. Simplify using `only [B, add_comm a b]`. Expand and normalize the polynomial expressions, which then agree.

Establish `Badd : ∀ a a' b, B (a + a') b = B a b + B a' b`. Introduce `a a' b`. Simplify using `only [B]`. Combine the linear relations using `[hcube a a' b]`. Set `L : X → (X →+ ℤ)` to `fun b => AddMonoidHom.mk' (fun a => B a b) (fun a a' => Badd a a' b)`.

Establish `L_apply : ∀ a b, L b a = B a b` using `fun _ _ => rfl`. Establish `Bdiag : ∀ a, B a a = 2 * q a`. Introduce `a`. Establish `h` using `hcube a (-a) a`. Simplify using `only [add_neg_cancel, neg_add_cancel, zero_add, hneg, h0] at h`.

Use `show q (a + a) - q a - q a = 2 * q a`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `Bbound : ∀ a s, |B a s| ≤ q a + q s`. Introduce `a s`. Establish `h1 : B a s = q (a + s) - q a - q s` using `rfl`.

Establish `h2 : B (-a) s = q (-a + s) - q (-a) - q s` using `rfl`. Establish `h3 : B (-a) s = - B a s`. Rewrite using `[← L_apply, ← L_apply, map_neg]`. Rewrite `h2` using `[hneg]`. Use `hnn (a + s)` as an intermediate fact.

Use `hnn (-a + s)` as an intermediate fact. Apply the tactic sequence `rw [abs_le]; constructor <;> linarith`. Take `⟨S, hS⟩` from `Module.Finite.fg_top (R := ℤ) (M := X)`. Establish `hzero : ∀ c, (∀ i ∈ S, B c i = 0) → c = 0`. Introduce `c hc`.

Establish `hle : Submodule.span ℤ (S : Set X) ≤ (L c).ker.toIntSubmodule`. Rewrite using `[Submodule.span_le]`. Introduce `x hx`. Express the relevant statement in the definitionally equal form `(L c) x = 0`. Rewrite using `[L_apply, Bsymm]`.

Conclude with `hc x hx`. Establish `hc' : c ∈ (L c).ker.toIntSubmodule` using `hle (hS ▸ Submodule.mem_top)`. Express the relevant statement in the definitionally equal form `(L c) c = 0 at hc'`. Rewrite `hc'` using `[L_apply, Bdiag]`. Assume the negation of the conclusion as `hne`.

Use `hpos c hne` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Set `φ : X → (S → ℤ)` to `fun a i => B a i`. Establish `φinj : Function.Injective φ`. Introduce `a a' h`.

Establish `: a - a' = 0`. Apply `hzero` to reduce the goal to its premises. Introduce `i hi`. Establish `hi'` using `congrFun h ⟨i, hi⟩`. Simplify using `only [φ] at hi'`.

Rewrite using `[← L_apply, map_sub, L_apply, L_apply, hi', sub_self]`. Conclude with `sub_eq_zero.mp this`. Establish `hfin : (Set.pi Set.univ (fun i : S => Set.Icc (-(N + q i)) (N + q i))).Finite` using `Set.Finite.pi (fun i => Set.finite_Icc _ _)`. Use `(hfin.preimage φinj.injOn).subset ?_` and prove the remaining obligations. Introduce `a ha`.

Simplify using `only [Set.mem_setOf_eq] at ha`. Simplify using `only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]`. Introduce `i`. Use `Bbound a i` as an intermediate fact. Rewrite `this` using `[abs_le]`.

Simplify using `only [φ]`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem posquad_finite : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (q : X → ℤ), (∀ a, q (-a) = q a) → (∀ a a' b, q (a + a' + b) + q a + q a' + q b = q (a + a') + q (a + b) + q (a' + b)) → (∀ a, a ≠ 0 → 1 ≤ q a) → ∀ N : ℤ, {a | q a ≤ N}.Finite := by
  intro X _ _ q hneg hcube hpos N
  have h0 : q 0 = 0 := by
    have := hcube 0 0 0
    simp only [add_zero] at this
    linarith
  have hnn : ∀ a, 0 ≤ q a := by
    intro a
    by_cases ha : a = 0
    · simp [ha, h0]
    · linarith [hpos a ha]
  let B : X → X → ℤ := fun a b => q (a + b) - q a - q b
  have Bsymm : ∀ a b, B a b = B b a := by
    intro a b; simp only [B, add_comm a b]; ring
  have Badd : ∀ a a' b, B (a + a') b = B a b + B a' b := by
    intro a a' b
    simp only [B]
    linarith [hcube a a' b]
  let L : X → (X →+ ℤ) := fun b => AddMonoidHom.mk' (fun a => B a b) (fun a a' => Badd a a' b)
  have L_apply : ∀ a b, L b a = B a b := fun _ _ => rfl
  have Bdiag : ∀ a, B a a = 2 * q a := by
    intro a
    have h := hcube a (-a) a
    simp only [add_neg_cancel, neg_add_cancel, zero_add, hneg, h0] at h
    show q (a + a) - q a - q a = 2 * q a
    linarith
  have Bbound : ∀ a s, |B a s| ≤ q a + q s := by
    intro a s
    have h1 : B a s = q (a + s) - q a - q s := rfl
    have h2 : B (-a) s = q (-a + s) - q (-a) - q s := rfl
    have h3 : B (-a) s = - B a s := by
      rw [← L_apply, ← L_apply, map_neg]
    rw [hneg] at h2
    have := hnn (a + s)
    have := hnn (-a + s)
    rw [abs_le]; constructor <;> linarith
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ) (M := X)
  have hzero : ∀ c, (∀ i ∈ S, B c i = 0) → c = 0 := by
    intro c hc
    have hle : Submodule.span ℤ (S : Set X) ≤ (L c).ker.toIntSubmodule := by
      rw [Submodule.span_le]
      intro x hx
      change (L c) x = 0
      rw [L_apply, Bsymm]; exact hc x hx
    have hc' : c ∈ (L c).ker.toIntSubmodule := hle (hS ▸ Submodule.mem_top)
    change (L c) c = 0 at hc'
    rw [L_apply, Bdiag] at hc'
    by_contra hne
    have := hpos c hne
    omega
  let φ : X → (S → ℤ) := fun a i => B a i
  have φinj : Function.Injective φ := by
    intro a a' h
    have : a - a' = 0 := by
      apply hzero
      intro i hi
      have hi' := congrFun h ⟨i, hi⟩
      simp only [φ] at hi'
      rw [← L_apply, map_sub, L_apply, L_apply, hi', sub_self]
    exact sub_eq_zero.mp this
  have hfin : (Set.pi Set.univ (fun i : S => Set.Icc (-(N + q i)) (N + q i))).Finite :=
    Set.Finite.pi (fun i => Set.finite_Icc _ _)
  refine (hfin.preimage φinj.injOn).subset ?_
  intro a ha
  simp only [Set.mem_setOf_eq] at ha
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  intro i
  have := Bbound a i
  rw [abs_le] at this
  simp only [φ]
  constructor <;> linarith

end GlobalTheory
