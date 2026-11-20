import Formalism.WachLatticeTwists.HerrComplexInjectivity.StatInvWach
import Formalism.WachLatticeTwists.WachProductBases.WachConsequencesFurther

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JN

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.N2

/- English proof (translation)
Introduce `O A A₀ _ _ _ _ _ S B Δ _ _ _ IB ι pr D _ _ _ _ W ρ M h M₀ D' _ _ _ _ j φ' γ' hs hΔ hGQ hP5 hM hinj hsm hrange hφ hγ hρ hP9`. Take `⟨-, -, hw, ⟨r, hr, hQ⟩, ε₀, hε₀, hjX⟩` from `hΔ`. Use `choose w hwu hw using hw`. Establish `hX : S.X = S.π` using `by simp [HidaSetting.X, hs]`. Take `⟨r', hr'⟩` from `hr.exists_left_inv`.

Establish `hjQ : IB.j B.Q = r' * S.Q` using `by rw [hQ, ← mul_assoc, hr', one_mul]`. Establish `hQinj : ∀ y : D, IB.j B.Q • y = 0 → y = 0`. Introduce `y hy`. Apply `W.Q_bij.1` to reduce the goal to its premises. Use `show S.Q • y = S.Q • (0 : D)`.

Rewrite using `[hQ, mul_smul, hy, smul_zero, smul_zero]`. Establish `hinvQ : ∀ d : Δ, d • IB.j B.Q = IB.j B.Q` using `(IB.j_range _).2 ⟨_, rfl⟩`. Set `p : A → Prop` to `fun a => ∀ y : D, a • y = 0 → y = 0`. Establish `pmul : ∀ a b, p a → p b → p (a * b)` using `fun a b ha hb y hy => hb y (ha _ (by rwa [smul_smul]))`. Establish `punit : ∀ a, IsUnit a → p a`.

Introduce `a ha y hy`. Take `⟨a', ha'⟩` from `ha.exists_left_inv`. Rewrite using `[← one_smul A y, ← ha', mul_smul, hy, smul_zero]`. Establish `pπ : p S.π` using `fun y hy => W.X_bij.1 (show S.X • y = S.X • (0 : D) by rw [hX, hy, smul_zero])`. Establish `pX : p (IB.j B.X)`.

Rewrite using `[hjX]`. Use `pmul _ _ (punit _ (hε₀.map IB.j)) (Finset.prod_induction _ p pmul (punit 1 isUnit_one) fun d _ => ?_)` and prove the remaining obligations. Rewrite using `[hw d]`. Conclude with `pmul _ _ (punit _ (hwu d)) pπ`. Set `N : Submodule A₀ D'` to `{ carrier := {x | ∀ i, j x i ∈ W.N i} add_mem' := by`.

Introduce `a b ha hb i`. Rewrite using `[map_add]`. Conclude with `(W.N i).add_mem (ha i) (hb i)`. Use the proof step `zero_mem' := by`. Introduce `i`.

Rewrite using `[map_zero]`. Conclude with `(W.N i).zero_mem`. Use the proof step `smul_mem' := by`. Introduce `a x hx i`. Rewrite using `[hsm]`.

Conclude with `(W.N i).smul_mem _ (hx i) }`. Establish `hQbij : Function.Bijective (fun x : D' => B.Q • x)`. Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`. Establish `hxy' : B.Q • x = B.Q • y` using `hxy`.

Apply `hinj` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Establish `h1 : j (B.Q • x) i = j (B.Q • y) i` using `by rw [hxy']`. Rewrite `h1` using `[hsm, hsm]`. Conclude with `sub_eq_zero.1 (hQinj _ (by rw [smul_sub, h1, sub_self]))`.

Introduce `x choose y hy using fun i => W.Q_bij.2 (r • j x i)`. Establish `hy' : ∀ i, IB.j B.Q • y i = j x i`. Introduce `i`. Establish `h1 : S.Q • y i = r • j x i` using `hy i`. Rewrite using `[hjQ, mul_smul, h1, smul_smul, hr', one_smul]`.

Establish `hxinv : ∀ i d, ρ i d (j x i) = j x i` using `(hrange _).2 ⟨x, rfl⟩`. Establish `hyinv : ∀ i d, ρ i d (y i) = y i`. Introduce `i d`. Apply `sub_eq_zero.1` to reduce the goal to its premises. Apply `hQinj` to reduce the goal to its premises.

Establish `h2 : IB.j B.Q • ρ i d (y i) = ρ i d (IB.j B.Q • y i)` using `by rw [hρ, hinvQ]`. Rewrite using `[smul_sub, h2, hy' i, hxinv, sub_self]`. Take `⟨x', hx'⟩` from `(hrange y).1 hyinv`. Use `⟨x', hinj (funext fun i => ?_)⟩` and prove the remaining obligations. Use `show j (B.Q • x') i = j x i`.

Rewrite using `[hsm, hx', hy']`. Establish `hγN : ∀ x ∈ N, ∃ x' ∈ N, γ' x - x = B.X • x'`. Introduce `x hx`. Take `⟨y, hyN, hyinv, hy⟩` from `hP9 (j x) hx ((hrange _).2 ⟨x, rfl⟩)`. Take `⟨x', hx'⟩` from `(hrange y).1 hyinv`.

Use `⟨x', fun i => by rw [hx']; exact hyN i, hinj (funext fun i => ?_)⟩` and prove the remaining obligations. Rewrite using `[map_sub, Pi.sub_apply, hγ, hsm, hx', hy]`. Establish `hγs : ∀ (a : A₀) (x : D'), γ' (a • x) = B.γ a • γ' x`. Introduce `a x`. Apply `hinj` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Rewrite using `[hγ, hsm, W.γ_smul, hsm, IB.j_γ, hγ]`. Establish `hφs : ∀ (a : A₀) (x : D'), φ' (a • x) = B.φ a • φ' x`. Introduce `a x`. Apply `hinj` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Rewrite using `[hφ, hsm, W.φ_smul, hsm, IB.j_φ, hφ]`. Establish `hcomm : ∀ x, φ' (γ' x) = γ' (φ' x)`. Introduce `x`. Apply `hinj` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Rewrite using `[hφ, hγ, hγ, hφ, W.comm]`. Establish `hXinj : ∀ x : D', B.X • x = 0 → x = 0`. Introduce `x hx`. Apply `hinj` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Rewrite using `[map_zero]`. Conclude with `pX _ (by rw [← hsm, hx, map_zero]; rfl)`. Establish `hφN : ∀ x ∈ N, B.Q ^ M₀ • φ' x ∈ N`. Introduce `x hx i`.

Rewrite using `[hsm, map_pow, hφ, hjQ, mul_pow, mul_smul]`. Use `(W.N i).smul_mem _ ?_` and prove the remaining obligations. Establish `e : S.Q ^ M₀ = S.Q ^ (M₀ - M i) * S.Q ^ M i`. Rewrite using `[← pow_add, Nat.sub_add_cancel (hM i)]`. Rewrite using `[e, mul_smul]`.

Conclude with `(W.N i).smul_mem _ (hP5.1 i _ (hx (pr i)))`. Establish `hγQN` using `gammaStableOfGammaQUnit_holds O A₀ B M₀ D' N γ' hGQ hQbij hγs hγN`. Conclude with `⟨⟨N, φ', γ', hφs, hγs, hcomm, hXinj, hQbij, hφN, hγN, hγQN⟩, ⟨j, hinj, hsm, hrange, fun x => Iff.rfl⟩, rfl, rfl, rfl⟩`.
-/
theorem wach_invariants_holds : StatInvWach := by
  intro O A A₀ _ _ _ _ _ S B Δ _ _ _ IB ι pr D _ _ _ _ W ρ M h M₀ D' _ _ _ _ j φ' γ' hs hΔ hGQ hP5 hM
    hinj hsm hrange hφ hγ hρ hP9
  obtain ⟨-, -, hw, ⟨r, hr, hQ⟩, ε₀, hε₀, hjX⟩ := hΔ
  choose w hwu hw using hw
  have hX : S.X = S.π := by simp [HidaSetting.X, hs]
  obtain ⟨r', hr'⟩ := hr.exists_left_inv
  have hjQ : IB.j B.Q = r' * S.Q := by rw [hQ, ← mul_assoc, hr', one_mul]
  have hQinj : ∀ y : D, IB.j B.Q • y = 0 → y = 0 := by
    intro y hy
    apply W.Q_bij.1
    show S.Q • y = S.Q • (0 : D)
    rw [hQ, mul_smul, hy, smul_zero, smul_zero]
  have hinvQ : ∀ d : Δ, d • IB.j B.Q = IB.j B.Q := (IB.j_range _).2 ⟨_, rfl⟩
  let p : A → Prop := fun a => ∀ y : D, a • y = 0 → y = 0
  have pmul : ∀ a b, p a → p b → p (a * b) :=
    fun a b ha hb y hy => hb y (ha _ (by rwa [smul_smul]))
  have punit : ∀ a, IsUnit a → p a := by
    intro a ha y hy
    obtain ⟨a', ha'⟩ := ha.exists_left_inv
    rw [← one_smul A y, ← ha', mul_smul, hy, smul_zero]
  have pπ : p S.π := fun y hy =>
    W.X_bij.1 (show S.X • y = S.X • (0 : D) by rw [hX, hy, smul_zero])
  have pX : p (IB.j B.X) := by
    rw [hjX]
    refine pmul _ _ (punit _ (hε₀.map IB.j))
      (Finset.prod_induction _ p pmul (punit 1 isUnit_one) fun d _ => ?_)
    rw [hw d]
    exact pmul _ _ (punit _ (hwu d)) pπ
  let N : Submodule A₀ D' :=
    { carrier := {x | ∀ i, j x i ∈ W.N i}
      add_mem' := by
        intro a b ha hb i
        rw [map_add]
        exact (W.N i).add_mem (ha i) (hb i)
      zero_mem' := by
        intro i
        rw [map_zero]
        exact (W.N i).zero_mem
      smul_mem' := by
        intro a x hx i
        rw [hsm]
        exact (W.N i).smul_mem _ (hx i) }
  have hQbij : Function.Bijective (fun x : D' => B.Q • x) := by
    constructor
    · intro x y hxy
      have hxy' : B.Q • x = B.Q • y := hxy
      apply hinj
      funext i
      have h1 : j (B.Q • x) i = j (B.Q • y) i := by rw [hxy']
      rw [hsm, hsm] at h1
      exact sub_eq_zero.1 (hQinj _ (by rw [smul_sub, h1, sub_self]))
    · intro x
      choose y hy using fun i => W.Q_bij.2 (r • j x i)
      have hy' : ∀ i, IB.j B.Q • y i = j x i := by
        intro i
        have h1 : S.Q • y i = r • j x i := hy i
        rw [hjQ, mul_smul, h1, smul_smul, hr', one_smul]
      have hxinv : ∀ i d, ρ i d (j x i) = j x i := (hrange _).2 ⟨x, rfl⟩
      have hyinv : ∀ i d, ρ i d (y i) = y i := by
        intro i d
        apply sub_eq_zero.1
        apply hQinj
        have h2 : IB.j B.Q • ρ i d (y i) = ρ i d (IB.j B.Q • y i) := by rw [hρ, hinvQ]
        rw [smul_sub, h2, hy' i, hxinv, sub_self]
      obtain ⟨x', hx'⟩ := (hrange y).1 hyinv
      refine ⟨x', hinj (funext fun i => ?_)⟩
      show j (B.Q • x') i = j x i
      rw [hsm, hx', hy']
  have hγN : ∀ x ∈ N, ∃ x' ∈ N, γ' x - x = B.X • x' := by
    intro x hx
    obtain ⟨y, hyN, hyinv, hy⟩ := hP9 (j x) hx ((hrange _).2 ⟨x, rfl⟩)
    obtain ⟨x', hx'⟩ := (hrange y).1 hyinv
    refine ⟨x', fun i => by rw [hx']; exact hyN i, hinj (funext fun i => ?_)⟩
    rw [map_sub, Pi.sub_apply, hγ, hsm, hx', hy]
  have hγs : ∀ (a : A₀) (x : D'), γ' (a • x) = B.γ a • γ' x := by
    intro a x
    apply hinj
    funext i
    rw [hγ, hsm, W.γ_smul, hsm, IB.j_γ, hγ]
  have hφs : ∀ (a : A₀) (x : D'), φ' (a • x) = B.φ a • φ' x := by
    intro a x
    apply hinj
    funext i
    rw [hφ, hsm, W.φ_smul, hsm, IB.j_φ, hφ]
  have hcomm : ∀ x, φ' (γ' x) = γ' (φ' x) := by
    intro x
    apply hinj
    funext i
    rw [hφ, hγ, hγ, hφ, W.comm]
  have hXinj : ∀ x : D', B.X • x = 0 → x = 0 := by
    intro x hx
    apply hinj
    funext i
    rw [map_zero]
    exact pX _ (by rw [← hsm, hx, map_zero]; rfl)
  have hφN : ∀ x ∈ N, B.Q ^ M₀ • φ' x ∈ N := by
    intro x hx i
    rw [hsm, map_pow, hφ, hjQ, mul_pow, mul_smul]
    refine (W.N i).smul_mem _ ?_
    have e : S.Q ^ M₀ = S.Q ^ (M₀ - M i) * S.Q ^ M i := by
      rw [← pow_add, Nat.sub_add_cancel (hM i)]
    rw [e, mul_smul]
    exact (W.N i).smul_mem _ (hP5.1 i _ (hx (pr i)))
  have hγQN := gammaStableOfGammaQUnit_holds O A₀ B M₀ D' N γ' hGQ hQbij hγs hγN
  exact ⟨⟨N, φ', γ', hφs, hγs, hcomm, hXinj, hQbij, hφN, hγN, hγQN⟩,
    ⟨j, hinj, hsm, hrange, fun x => Iff.rfl⟩, rfl, rfl, rfl⟩

end Formalism.RepresentationBoundsCohomology.JN
