import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

/- English proof (translation)
Establish `hk : 0 < orderOf x` using `orderOf_pos x`. Establish `e : x⁻¹ = x ^ (orderOf x - 1)`. Apply `inv_eq_of_mul_eq_one_right` to reduce the goal to its premises. Rewrite using `[← pow_succ', Nat.sub_add_cancel hk, pow_orderOf_eq_one]`. Rewrite using `[e]`.

Conclude with `S.pow_mem hx _`.
-/
private theorem ltgs_inv_mem {M : Type} [Group M] [Finite M] (S : Submonoid M) {x : M} (hx : x ∈ S) : x⁻¹ ∈ S := by
  have hk : 0 < orderOf x := orderOf_pos x
  have e : x⁻¹ = x ^ (orderOf x - 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', Nat.sub_add_cancel hk, pow_orderOf_eq_one]
  rw [e]
  exact S.pow_mem hx _

/- English proof (translation)
Introduce `O R _ _ _ _ ℬ _`. Establish `hwt : ∀ a c b : Fin 3, wt a c + wt c b = wt a b`. Introduce `a c b`. Simplify using `only [wt]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hwrev : ∀ a b : Fin 3, wt b.rev a.rev = wt a b`. Apply the tactic sequence `intro a b; fin_cases a <;> fin_cases b <;> rfl`. Establish `hone : GrMat ℬ (1 : Matrix (Fin 3) (Fin 3) R)`. Introduce `a b`. Distinguish the cases in `h : a = b`.

Substitute `h` using the available equality. Rewrite using `[Matrix.one_apply_eq]`. Establish `h0 : wt a a = 0` using `by simp [wt]`. Rewrite using `[h0]`. Conclude with `SetLike.GradedOne.one_mem`.

Rewrite using `[Matrix.one_apply_ne h]`. Conclude with `Submodule.zero_mem _`. Establish `hmul : ∀ X Y : Matrix (Fin 3) (Fin 3) R, GrMat ℬ X → GrMat ℬ Y → GrMat ℬ (X * Y)`. Introduce `X Y hX hY a b`. Rewrite using `[Matrix.mul_apply]`.

Use `Submodule.sum_mem _ fun c _ => ?_` and prove the remaining obligations. Rewrite using `[← hwt a c b]`. Conclude with `SetLike.GradedMul.mul_mem (hX a c) (hY c b)`. Set `T : Submonoid (GL (Fin 3) R)` to `{ carrier := {g | GrMat ℬ (g : Matrix (Fin 3) (Fin 3) R)} mul_mem' := fun {g h} hg hh => by show GrMat ℬ ((g * h : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)`. Rewrite using `[Units.val_mul]`.

Conclude with `hmul _ _ hg hh`. Use the proof step `one_mem' := by show GrMat ℬ ((1 : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)`. Rewrite using `[Units.val_one]`. Conclude with `hone }`. Establish `hinv : ∀ g : GL (Fin 3) R, GrMat ℬ (g : Matrix (Fin 3) (Fin 3) R) → GrMat ℬ ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)` using `fun g hg => ltgs_inv_mem T (x := g) hg`.

Establish `hJ : ∀ (M : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3), (Jmat R 3 * M * Jmat R 3) a b = M a.rev b.rev`. Introduce `M a b`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat] <;> rfl`. Establish `htheta : ∀ g : GL (Fin 3) R, GrMat ℬ (g : Matrix (Fin 3) (Fin 3) R) → GrMat ℬ ((theta g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)`. Introduce `g hg a b`.

Rewrite using `[theta_val, hJ, Matrix.transpose_apply, ← hwrev a b]`. Conclude with `hinv g hg b.rev a.rev`. Establish `hact : ∀ (s : ℤˣ) (g : GL (Fin 3) R), GrMat ℬ (g : Matrix (Fin 3) (Fin 3) R) → GrMat ℬ ((sgnAct 3 R s g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)`. Introduce `s g hg`. Break down `Int.units_eq_one_or s with rfl | rfl` into its components or cases.

Rewrite using `[sgnAct_one]`. Conclude with `hg`. Rewrite using `[sgnAct_neg_one]`. Conclude with `htheta g hg`. Use `haveI : Finite (GG 3 R) := Finite.of_injective (fun x : GG 3 R => (x.left, x.right)) (fun x y h => SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))`.

Set `S0 : Submonoid (GG 3 R)` to `{ carrier := {x | GrMat ℬ x.mat} mul_mem' := fun {x y} hx hy => by show GrMat ℬ ((x * y).left : Matrix (Fin 3) (Fin 3) R)`. Rewrite using `[SemidirectProduct.mul_left, Units.val_mul]`. Conclude with `hmul _ _ hx (hact _ _ hy)`. Use the proof step `one_mem' := by show GrMat ℬ ((1 : GG 3 R).left : Matrix (Fin 3) (Fin 3) R)`. Rewrite using `[SemidirectProduct.one_left, Units.val_one]`.

Conclude with `hone }`. Conclude with `⟨{ S0 with inv_mem' := fun {x} hx => ltgs_inv_mem S0 hx }, fun x => Iff.rfl⟩`.
-/
theorem UpperTheory.V.UnitaryThreeInertia.lt_grSub :
    ∀ {O R : Type} [CommRing O] [CommRing R] [Algebra O R] [Finite R] (ℬ : ℤ → Submodule O R) [SetLike.GradedMonoid ℬ],
      ∃ S : Subgroup (GG 3 R), ∀ x, x ∈ S ↔ GrMat ℬ x.mat := by
  intro O R _ _ _ _ ℬ _
  classical
  have hwt : ∀ a c b : Fin 3, wt a c + wt c b = wt a b := by
    intro a c b; simp only [wt]; ring
  have hwrev : ∀ a b : Fin 3, wt b.rev a.rev = wt a b := by
    intro a b; fin_cases a <;> fin_cases b <;> rfl
  have hone : GrMat ℬ (1 : Matrix (Fin 3) (Fin 3) R) := by
    intro a b
    by_cases h : a = b
    · subst h
      rw [Matrix.one_apply_eq]
      have h0 : wt a a = 0 := by simp [wt]
      rw [h0]
      exact SetLike.GradedOne.one_mem
    · rw [Matrix.one_apply_ne h]
      exact Submodule.zero_mem _
  have hmul : ∀ X Y : Matrix (Fin 3) (Fin 3) R, GrMat ℬ X → GrMat ℬ Y → GrMat ℬ (X * Y) := by
    intro X Y hX hY a b
    rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ fun c _ => ?_
    rw [← hwt a c b]
    exact SetLike.GradedMul.mul_mem (hX a c) (hY c b)
  let T : Submonoid (GL (Fin 3) R) :=
    { carrier := {g | GrMat ℬ (g : Matrix (Fin 3) (Fin 3) R)}
      mul_mem' := fun {g h} hg hh => by
        show GrMat ℬ ((g * h : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)
        rw [Units.val_mul]
        exact hmul _ _ hg hh
      one_mem' := by
        show GrMat ℬ ((1 : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)
        rw [Units.val_one]
        exact hone }
  have hinv : ∀ g : GL (Fin 3) R, GrMat ℬ (g : Matrix (Fin 3) (Fin 3) R) →
      GrMat ℬ ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) :=
    fun g hg => ltgs_inv_mem T (x := g) hg
  have hJ : ∀ (M : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3),
      (Jmat R 3 * M * Jmat R 3) a b = M a.rev b.rev := by
    intro M a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat] <;> rfl
  have htheta : ∀ g : GL (Fin 3) R, GrMat ℬ (g : Matrix (Fin 3) (Fin 3) R) →
      GrMat ℬ ((theta g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
    intro g hg a b
    rw [theta_val, hJ, Matrix.transpose_apply, ← hwrev a b]
    exact hinv g hg b.rev a.rev
  have hact : ∀ (s : ℤˣ) (g : GL (Fin 3) R), GrMat ℬ (g : Matrix (Fin 3) (Fin 3) R) →
      GrMat ℬ ((sgnAct 3 R s g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
    intro s g hg
    rcases Int.units_eq_one_or s with rfl | rfl
    · rw [sgnAct_one]; exact hg
    · rw [sgnAct_neg_one]; exact htheta g hg
  haveI : Finite (GG 3 R) := Finite.of_injective (fun x : GG 3 R => (x.left, x.right))
    (fun x y h => SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  let S0 : Submonoid (GG 3 R) :=
    { carrier := {x | GrMat ℬ x.mat}
      mul_mem' := fun {x y} hx hy => by
        show GrMat ℬ ((x * y).left : Matrix (Fin 3) (Fin 3) R)
        rw [SemidirectProduct.mul_left, Units.val_mul]
        exact hmul _ _ hx (hact _ _ hy)
      one_mem' := by
        show GrMat ℬ ((1 : GG 3 R).left : Matrix (Fin 3) (Fin 3) R)
        rw [SemidirectProduct.one_left, Units.val_one]
        exact hone }
  exact ⟨{ S0 with inv_mem' := fun {x} hx => ltgs_inv_mem S0 hx }, fun x => Iff.rfl⟩
