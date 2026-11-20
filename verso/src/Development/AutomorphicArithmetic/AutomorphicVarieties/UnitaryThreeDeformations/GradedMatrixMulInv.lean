import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section
variable {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜]

/- English proof (translation)
Introduce `a b`. Simplify using `only [Matrix.mul_apply]`. Use `Submodule.sum_mem _ fun c _ => ?_` and prove the remaining obligations. Establish `h` using `SetLike.GradedMul.mul_mem (hX a c) (hY c b)`. Establish `e : wt a c + wt c b = wt a b` using `by simp only [wt]; ring`.

Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
private theorem gr_mul {X Y : Matrix (Fin 3) (Fin 3) R} (hX : GrMat 𝒜 X) (hY : GrMat 𝒜 Y) :
    GrMat 𝒜 (X * Y) := by
  intro a b
  simp only [Matrix.mul_apply]
  refine Submodule.sum_mem _ fun c _ => ?_
  have h := SetLike.GradedMul.mul_mem (hX a c) (hY c b)
  have e : wt a c + wt c b = wt a b := by simp only [wt]; ring
  rwa [e] at h

/- English proof (translation)
Introduce `a b`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Rewrite using `[Matrix.one_apply_eq]`. Establish `e : wt a a = 0` using `by simp [wt]`.

Rewrite using `[e]`. Conclude with `SetLike.GradedOne.one_mem`. Rewrite using `[Matrix.one_apply_ne h]`. Conclude with `zero_mem _`.
-/
private theorem gr_one : GrMat 𝒜 (1 : Matrix (Fin 3) (Fin 3) R) := by
  intro a b
  by_cases h : a = b
  · subst h
    rw [Matrix.one_apply_eq]
    have e : wt a a = 0 := by simp [wt]
    rw [e]
    exact SetLike.GradedOne.one_mem
  · rw [Matrix.one_apply_ne h]
    exact zero_mem _

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero]`. Conclude with `gr_one 𝒜`. Consider the case `succ n ih => rw [pow_succ, Units.val_mul]`. Conclude with `gr_mul 𝒜 ih hg`.
-/
private theorem gr_pow {g : GL (Fin 3) R} (hg : GrMat 𝒜 (g : Matrix (Fin 3) (Fin 3) R)) (n : ℕ) :
    GrMat 𝒜 ((g ^ n : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  induction n with
  | zero => rw [pow_zero]; exact gr_one 𝒜
  | succ n ih => rw [pow_succ, Units.val_mul]; exact gr_mul 𝒜 ih hg

/- English proof (translation)
Establish `hn` using `orderOf_pos g`. Establish `e : g⁻¹ = g ^ (orderOf g - 1)`. Use `symm`. Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises. Rewrite using `[← pow_succ, Nat.sub_add_cancel hn, pow_orderOf_eq_one]`.

Rewrite using `[e]`. Conclude with `gr_pow 𝒜 hg _`.
-/
private theorem gr_inv [Finite R] {g : GL (Fin 3) R} (hg : GrMat 𝒜 (g : Matrix (Fin 3) (Fin 3) R)) :
    GrMat 𝒜 ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  have hn := orderOf_pos g
  have e : g⁻¹ = g ^ (orderOf g - 1) := by
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel hn, pow_orderOf_eq_one]
  rw [e]
  exact gr_pow 𝒜 hg _

/- English proof (translation)
Rewrite using `[theta_val]`. Establish `hi` using `gr_inv 𝒜 hg`. Establish `key : ∀ (M : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3), (Jmat R 3 * Mᵀ * Jmat R 3) a b = M b.rev a.rev`. Introduce `M a b`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Jmat, Fin.sum_univ_three, Fin.rev]`.

Introduce `a b`. Rewrite using `[key]`. Apply the tactic sequence `have e : wt b.rev a.rev = wt a b := by fin_cases a <;> fin_cases b <;> rfl`. Rewrite using `[← e]`. Conclude with `hi _ _`.
-/
private theorem gr_theta [Finite R] {g : GL (Fin 3) R} (hg : GrMat 𝒜 (g : Matrix (Fin 3) (Fin 3) R)) :
    GrMat 𝒜 ((theta g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  rw [theta_val]
  have hi := gr_inv 𝒜 hg
  have key : ∀ (M : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3),
      (Jmat R 3 * Mᵀ * Jmat R 3) a b = M b.rev a.rev := by
    intro M a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Jmat, Fin.sum_univ_three, Fin.rev]
  intro a b
  rw [key]
  have e : wt b.rev a.rev = wt a b := by fin_cases a <;> fin_cases b <;> rfl
  rw [← e]
  exact hi _ _

/- English proof (translation)
Break down `Int.units_eq_one_or s with rfl | rfl` into its components or cases. Rewrite using `[sgnAct_one]`. Conclude with `hg`. Rewrite using `[sgnAct_neg_one]`. Conclude with `gr_theta 𝒜 hg`.
-/
private theorem gr_act [Finite R] (s : ℤˣ) {g : GL (Fin 3) R} (hg : GrMat 𝒜 (g : Matrix (Fin 3) (Fin 3) R)) :
    GrMat 𝒜 ((sgnAct 3 R s g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · rw [sgnAct_one]; exact hg
  · rw [sgnAct_neg_one]; exact gr_theta 𝒜 hg

end

/- English proof (translation)
Introduce `O R _ _ _ _ 𝒜 _ x y hx hy`. Unfold `GG.mat at *`. Prove the components needed by the constructor for the conclusion. Rewrite using `[SemidirectProduct.mul_left, Units.val_mul]`. Conclude with `gr_mul 𝒜 hx (gr_act 𝒜 _ hy)`.

Rewrite using `[SemidirectProduct.inv_left]`. Conclude with `gr_act 𝒜 _ (gr_inv 𝒜 hx)`.
-/
theorem UpperTheory.graded_matrix_mul_inv :
    ∀ {O R : Type} [CommRing O] [CommRing R] [Algebra O R] [Finite R] (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] (x y : GG 3 R), GrMat 𝒜 x.mat → GrMat 𝒜 y.mat → GrMat 𝒜 (x * y).mat ∧ GrMat 𝒜 (x⁻¹).mat := by
  intro O R _ _ _ _ 𝒜 _ x y hx hy
  unfold GG.mat at *
  constructor
  · rw [SemidirectProduct.mul_left, Units.val_mul]
    exact gr_mul 𝒜 hx (gr_act 𝒜 _ hy)
  · rw [SemidirectProduct.inv_left]
    exact gr_act 𝒜 _ (gr_inv 𝒜 hx)
