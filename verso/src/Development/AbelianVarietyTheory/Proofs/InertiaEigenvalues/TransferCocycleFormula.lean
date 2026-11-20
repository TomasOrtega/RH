import Mathlib

namespace GlobalTheory

open QuotientGroup

/- English proof (translation)
Introduce `R G X _ _ _ _ ρ H _ tr`. Establish `mem : ∀ (g : G) (q : G ⧸ H), (g • q).out⁻¹ * g * q.out ∈ H`. Introduce `g q`. Establish `h1 : (((g • q).out : G) : G ⧸ H) = ((g * q.out : G) : G ⧸ H)`. Rewrite using `[QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']`.

Rewrite using `[mul_assoc]`. Conclude with `QuotientGroup.eq.mp h1`. Establish `reidx : ∀ (g : G) (F : G ⧸ H → X), ∑ q, F (g • q) = ∑ q, F q` using `fun g F => Equiv.sum_comp (MulAction.toPerm g) F`. Establish `rmul : ∀ (s t : G) (y : X), ρ s (ρ t y) = ρ (s * t) y`. Introduce `s t y`.

Rewrite using `[map_mul, Module.End.mul_apply]`. Use `⟨mem, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `f hf a b`. Establish `key : ∀ q : G ⧸ H, ρ ((a * b) • q).out (f (((a * b) • q).out⁻¹ * (a * b) * q.out)) = ρ (a • (b • q)).out (f ((a • (b • q)).out⁻¹ * a * (b • q).out)) + ρ a (ρ (b • q).out (f ((b • q).out⁻¹ * b * q.out)))`. Introduce `q`.

Rewrite using `[mul_smul]`. Establish `e : (a • b • q).out⁻¹ * (a * b) * q.out = ((a • b • q).out⁻¹ * a * (b • q).out) * ((b • q).out⁻¹ * b * q.out)` using `by group`. Rewrite using `[e, hf _ (mem a (b • q)) _ (mem b q), map_add, rmul, rmul]`. Use `congr 3`. Use `group`.

Use `show ∑ q : G ⧸ H, ρ ((a * b) • q).out (f (((a * b) • q).out⁻¹ * (a * b) * q.out)) = ∑ q : G ⧸ H, ρ (a • q).out (f ((a • q).out⁻¹ * a * q.out)) + ρ a (∑ q : G ⧸ H, ρ (b • q).out (f ((b • q).out⁻¹ * b * q.out)))`. Rewrite using `[Finset.sum_congr rfl (fun q _ => key q), Finset.sum_add_distrib, map_sum, reidx b (fun q => ρ (a • q).out (f ((a • q).out⁻¹ * a * q.out)))]`. Introduce `f x hf g`. Establish `key : ∀ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out)) = ρ g (ρ q.out x) - ρ (g • q).out x`. Introduce `q`.

Rewrite using `[hf _ (mem g q), map_sub, rmul, rmul]`. Use `congr 2`. Use `group`. Use `show ∑ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out)) = _`. Rewrite using `[Finset.sum_congr rfl (fun q _ => key q), Finset.sum_sub_distrib, map_sum, reidx g (fun q => ρ q.out x)]`.

Introduce `f hf g`. Establish `f1 : f 1 = 0`. Use `hf 1 1` as an intermediate fact. Simplify using `only [mul_one, map_one, Module.End.one_apply] at this`. Conclude with `left_eq_add.mp this`.

Establish `finv : ∀ s : G, ρ s (f s⁻¹) = - f s`. Introduce `s`. Use `hf s s⁻¹` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel, f1]`. Conclude with `(neg_eq_of_add_eq_zero_right this.symm).symm`.

Establish `key : ∀ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out)) = (f g + ρ g (f q.out)) - f (g • q).out`. Introduce `q`. Rewrite using `[mul_assoc, hf, map_add, finv, rmul, mul_inv_cancel, map_one, Module.End.one_apply, hf]`. Normalize the expressions using the abelian group laws. Use `show ∑ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out)) = _`.

Rewrite using `[Finset.sum_congr rfl (fun q _ => key q), Finset.sum_sub_distrib, Finset.sum_add_distrib, map_sum, reidx g (fun q => f q.out), Finset.sum_const, Finset.card_univ, Subgroup.index_eq_card, Nat.card_eq_fintype_card]`. Normalize the expressions using the abelian group laws.
-/
theorem transfer_cocycle_formula : ∀ (R G X : Type) [CommRing R] [Group G] [AddCommGroup X] [Module R X] (ρ : Representation R G X) (H : Subgroup G) [Fintype (G ⧸ H)], let tr : (G → X) → G → X := fun f g => ∑ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out)); (∀ (g : G) (q : G ⧸ H), (g • q).out⁻¹ * g * q.out ∈ H) ∧ (∀ f : G → X, (∀ a ∈ H, ∀ b ∈ H, f (a * b) = f a + ρ a (f b)) → ∀ a b, tr f (a * b) = tr f a + ρ a (tr f b)) ∧ (∀ (f : G → X) (x : X), (∀ h ∈ H, f h = ρ h x - x) → ∀ g, tr f g = ρ g (∑ q : G ⧸ H, ρ q.out x) - ∑ q : G ⧸ H, ρ q.out x) ∧ (∀ f : G → X, (∀ a b, f (a * b) = f a + ρ a (f b)) → ∀ g, tr f g = H.index • f g + (ρ g (∑ q : G ⧸ H, f q.out) - ∑ q : G ⧸ H, f q.out)) := by
  intro R G X _ _ _ _ ρ H _ tr
  have mem : ∀ (g : G) (q : G ⧸ H), (g • q).out⁻¹ * g * q.out ∈ H := by
    intro g q
    have h1 : (((g • q).out : G) : G ⧸ H) = ((g * q.out : G) : G ⧸ H) := by
      rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
    rw [mul_assoc]
    exact QuotientGroup.eq.mp h1
  have reidx : ∀ (g : G) (F : G ⧸ H → X), ∑ q, F (g • q) = ∑ q, F q := fun g F =>
    Equiv.sum_comp (MulAction.toPerm g) F
  have rmul : ∀ (s t : G) (y : X), ρ s (ρ t y) = ρ (s * t) y := by
    intro s t y
    rw [map_mul, Module.End.mul_apply]
  refine ⟨mem, ?_, ?_, ?_⟩
  · intro f hf a b
    have key : ∀ q : G ⧸ H, ρ ((a * b) • q).out (f (((a * b) • q).out⁻¹ * (a * b) * q.out))
        = ρ (a • (b • q)).out (f ((a • (b • q)).out⁻¹ * a * (b • q).out))
          + ρ a (ρ (b • q).out (f ((b • q).out⁻¹ * b * q.out))) := by
      intro q
      rw [mul_smul]
      have e : (a • b • q).out⁻¹ * (a * b) * q.out
          = ((a • b • q).out⁻¹ * a * (b • q).out) * ((b • q).out⁻¹ * b * q.out) := by group
      rw [e, hf _ (mem a (b • q)) _ (mem b q), map_add, rmul, rmul]
      congr 3
      group
    show ∑ q : G ⧸ H, ρ ((a * b) • q).out (f (((a * b) • q).out⁻¹ * (a * b) * q.out))
      = ∑ q : G ⧸ H, ρ (a • q).out (f ((a • q).out⁻¹ * a * q.out))
        + ρ a (∑ q : G ⧸ H, ρ (b • q).out (f ((b • q).out⁻¹ * b * q.out)))
    rw [Finset.sum_congr rfl (fun q _ => key q), Finset.sum_add_distrib, map_sum,
      reidx b (fun q => ρ (a • q).out (f ((a • q).out⁻¹ * a * q.out)))]
  · intro f x hf g
    have key : ∀ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out))
        = ρ g (ρ q.out x) - ρ (g • q).out x := by
      intro q
      rw [hf _ (mem g q), map_sub, rmul, rmul]
      congr 2
      group
    show ∑ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out)) = _
    rw [Finset.sum_congr rfl (fun q _ => key q), Finset.sum_sub_distrib, map_sum,
      reidx g (fun q => ρ q.out x)]
  · intro f hf g
    have f1 : f 1 = 0 := by
      have := hf 1 1
      simp only [mul_one, map_one, Module.End.one_apply] at this
      exact left_eq_add.mp this
    have finv : ∀ s : G, ρ s (f s⁻¹) = - f s := by
      intro s
      have := hf s s⁻¹
      rw [mul_inv_cancel, f1] at this
      exact (neg_eq_of_add_eq_zero_right this.symm).symm
    have key : ∀ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out))
        = (f g + ρ g (f q.out)) - f (g • q).out := by
      intro q
      rw [mul_assoc, hf, map_add, finv, rmul, mul_inv_cancel, map_one, Module.End.one_apply, hf]
      abel
    show ∑ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out)) = _
    rw [Finset.sum_congr rfl (fun q _ => key q), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      map_sum, reidx g (fun q => f q.out), Finset.sum_const, Finset.card_univ,
      Subgroup.index_eq_card, Nat.card_eq_fintype_card]
    abel

end GlobalTheory
