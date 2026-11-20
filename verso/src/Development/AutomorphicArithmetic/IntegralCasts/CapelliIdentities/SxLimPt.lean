import Mathlib

/- English proof (translation)
Introduce `Λ A R S _ _ _ _ _ I _ e y hex huniq`. Use `choose f hf using hex`. Establish `hc : ∀ {m n : ℕ} (hle : m + 1 ≤ n + 1), (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right hle)).comp (f n) = f m`. Introduce `m n hle`. Use `huniq m _ _ fun s => ?_` and prove the remaining obligations.

Rewrite using `[AlgHom.comp_apply, hf, hf]`. Both sides reduce to the same expression. Set `g : (n : ℕ) → A →ₐ[Λ] R ⧸ I ^ n` to `fun n => (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right (Nat.le_succ n))).comp (f n)`. Establish `hg : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right hle)).comp (g n) = g m`. Introduce `m n hle`.

Use `AlgHom.ext fun a => ?_` and prove the remaining obligations. Simplify using `only [g, ← hc (Nat.succ_le_succ hle), AlgHom.comp_apply]`. Take `⟨r, hr⟩` from `Ideal.Quotient.mk_surjective (f n a)`. Rewrite using `[← hr]`. Both sides reduce to the same expression.

Use `⟨IsAdicComplete.liftAlgHom I g hg, fun s => ?_⟩` and prove the remaining obligations. Establish `key : (fun s => IsAdicComplete.liftAlgHom I g hg (e s)) = y`. Apply `IsHausdorff.funext' I` to reduce the goal to its premises. Introduce `n t`. Establish `h1` using `IsAdicComplete.mk_liftAlgHom I g hg n (e t)`.

Use `h1.trans ?_` and prove the remaining obligations. Simplify using `only [g, AlgHom.comp_apply, hf]`. Both sides reduce to the same expression. Conclude with `congrFun key s`.
-/
theorem UpperTheory.Reformulated.B.Qg4.sxLimPt :
    ∀ {Λ A R S : Type} [inst : CommRing Λ] [inst_1 : CommRing A] [inst_2 : Algebra Λ A]
    [inst_3 : CommRing R] [inst_4 : Algebra Λ R] (I : Ideal R) [IsAdicComplete I R] (e : S → A) (y : S → R),
    (∀ (N : ℕ),
        ∃ (f : A →ₐ[Λ] R ⧸ I ^ (N + (1 : ℕ))),
          ∀ (s : S),
            (f : A → R ⧸ I ^ (N + (1 : ℕ))) (e s) =
              (Ideal.Quotient.mk (I ^ (N + (1 : ℕ))) : R → R ⧸ I ^ (N + (1 : ℕ))) (y s)) →
      (∀ (N : ℕ) (f f' : A →ₐ[Λ] R ⧸ I ^ (N + (1 : ℕ))),
          (∀ (s : S), (f : A → R ⧸ I ^ (N + (1 : ℕ))) (e s) = (f' : A → R ⧸ I ^ (N + (1 : ℕ))) (e s)) → f = f') →
        ∃ (f : A →ₐ[Λ] R), ∀ (s : S), (f : A → R) (e s) = y s := by
  intro Λ A R S _ _ _ _ _ I _ e y hex huniq
  choose f hf using hex
  have hc : ∀ {m n : ℕ} (hle : m + 1 ≤ n + 1),
      (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right hle)).comp (f n) = f m := by
    intro m n hle
    refine huniq m _ _ fun s => ?_
    rw [AlgHom.comp_apply, hf, hf]
    rfl
  let g : (n : ℕ) → A →ₐ[Λ] R ⧸ I ^ n := fun n =>
    (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right (Nat.le_succ n))).comp (f n)
  have hg : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right hle)).comp (g n) = g m := by
    intro m n hle
    refine AlgHom.ext fun a => ?_
    simp only [g, ← hc (Nat.succ_le_succ hle), AlgHom.comp_apply]
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (f n a)
    rw [← hr]
    rfl
  refine ⟨IsAdicComplete.liftAlgHom I g hg, fun s => ?_⟩
  have key : (fun s => IsAdicComplete.liftAlgHom I g hg (e s)) = y := by
    apply IsHausdorff.funext' I
    intro n t
    have h1 := IsAdicComplete.mk_liftAlgHom I g hg n (e t)
    refine h1.trans ?_
    simp only [g, AlgHom.comp_apply, hf]
    rfl
  exact congrFun key s
