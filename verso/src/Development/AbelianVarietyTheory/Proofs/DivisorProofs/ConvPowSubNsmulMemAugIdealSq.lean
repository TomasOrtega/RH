import Mathlib

open TensorProduct Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `A B _ _ _ ε Δ α hL hR h0 hS`. Establish `hεu : ∀ a : A, ε (algebraMap A B a) = a` using `fun a => by simp`. Establish `hL' : ∀ b, Algebra.TensorProduct.lift ((Algebra.ofId A B).comp ε) (AlgHom.id A B) (fun _ _ => Commute.all _ _) (Δ b) = b` using `fun b => by`. Simplify `DFunLike.congr_fun hL b` using `only [AlgHom.comp_apply, AlgHom.id_apply]`. Establish `hR' : ∀ b, Algebra.TensorProduct.lift (AlgHom.id A B) ((Algebra.ofId A B).comp ε) (fun _ _ => Commute.all _ _) (Δ b) = b` using `fun b => by`.

Simplify `DFunLike.congr_fun hR b` using `only [AlgHom.comp_apply, AlgHom.id_apply]`. Establish `hε : ∀ n b, ε (α n b) = ε b`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro b`.

Rewrite using `[h0]`. Simplify using `[hεu]`. Consider the case `succ n ih`. Introduce `b`. Establish `key : ∀ t : B ⊗[A] B, ε (Algebra.TensorProduct.lift (α n) (AlgHom.id A B) (fun _ _ => Commute.all _ _) t) = ε (Algebra.TensorProduct.lift ((Algebra.ofId A B).comp ε) (AlgHom.id A B) (fun _ _ => Commute.all _ _) t)`.

Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul b c => simp [Algebra.TensorProduct.lift_tmul, ih, hεu]`. Consider the case `add s t hs ht => simp only [map_add, hs, ht]`.

Rewrite using `[hS n, AlgHom.comp_apply, key, hL' b]`. Establish `hright : ∀ (ψ : B →ₐ[A] B) (t : B ⊗[A] B), Algebra.TensorProduct.lift ψ ((Algebra.ofId A B).comp ε) (fun _ _ => Commute.all _ _) t = ψ (Algebra.TensorProduct.lift (AlgHom.id A B) ((Algebra.ofId A B).comp ε) (fun _ _ => Commute.all _ _) t)`. Introduce `ψ t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul b c => simp [Algebra.TensorProduct.lift_tmul]`. Consider the case `add s t hs ht => simp only [map_add, hs, ht]`. Establish `gen : ∀ (φ : B →ₐ[A] B), (∀ b, ε (φ b) = ε b) → ∀ t : B ⊗[A] B, Algebra.TensorProduct.lift φ (AlgHom.id A B) (fun _ _ => Commute.all _ _) t - Algebra.TensorProduct.lift ((Algebra.ofId A B).comp ε) (AlgHom.id A B) (fun _ _ => Commute.all _ _) t - Algebra.TensorProduct.lift φ ((Alg …`. Introduce `φ hφ t`. Proceed by induction on `t using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul b c`. Simplify using `only [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, AlgHom.id_apply, Algebra.ofId_apply]`. Establish `e : φ b * c - algebraMap A B (ε b) * c - φ b * algebraMap A B (ε c) + algebraMap A B (ε b) * algebraMap A B (ε c) = (φ b - algebraMap A B (ε b)) * (c - algebraMap A B (ε c))` using `by ring`. Rewrite using `[e, sq]`.

Conclude with `Ideal.mul_mem_mul (by rw [RingHom.mem_ker]; simp [hφ, hεu]) (by rw [RingHom.mem_ker]; simp [hεu])`. Consider the case `add s t hs ht`. Establish `e` using `add_mem hs ht`. Simplify using `only [map_add]`. Use `e using 1` and compare the differences between its conclusion and the goal.

Normalize the expressions using the abelian group laws. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `x hx`.

Rewrite using `[h0]`. Simplify using `[RingHom.mem_ker.mp hx]`. Consider the case `succ n ih`. Introduce `x hx`. Establish `E` using `gen (α n) (hε n) (Δ x)`.

Rewrite `E` using `[hL' x, hright (α n) (Δ x), hright ((Algebra.ofId A B).comp ε) (Δ x), hR' x]`. Establish `hx0 : ε x = 0` using `by simpa using hx`. Establish `h4 : ((Algebra.ofId A B).comp ε) x = 0` using `by simp [hx0]`. Rewrite `E` using `[h4, add_zero]`. Rewrite using `[hS n, AlgHom.comp_apply]`.

Use `add_mem E (ih x hx) using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem convPow_sub_nsmul_mem_augIdeal_sq : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (ε : B →ₐ[A] A) (Δ : B →ₐ[A] B ⊗[A] B) (α : ℕ → (B →ₐ[A] B)), (Algebra.TensorProduct.lift ((Algebra.ofId A B).comp ε) (AlgHom.id A B) (fun _ _ => Commute.all _ _)).comp Δ = AlgHom.id A B → (Algebra.TensorProduct.lift (AlgHom.id A B) ((Algebra.ofId A B).comp ε) (fun _ _ => Commute.all _ _)).comp Δ = AlgHom.id A B → α 0 = (Algebra.ofId A B).comp ε → (∀ n, α (n+1) = (Algebra.TensorProduct.lift (α n) (AlgHom.id A B) (fun _ _ => Commute.all _ _)).comp Δ) → ∀ n, ∀ x ∈ RingHom.ker ε, α n x - (n : B) * x ∈ (RingHom.ker ε) ^ 2 := by
  intro A B _ _ _ ε Δ α hL hR h0 hS
  have hεu : ∀ a : A, ε (algebraMap A B a) = a := fun a => by simp
  have hL' : ∀ b, Algebra.TensorProduct.lift ((Algebra.ofId A B).comp ε) (AlgHom.id A B)
      (fun _ _ => Commute.all _ _) (Δ b) = b := fun b => by
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using DFunLike.congr_fun hL b
  have hR' : ∀ b, Algebra.TensorProduct.lift (AlgHom.id A B) ((Algebra.ofId A B).comp ε)
      (fun _ _ => Commute.all _ _) (Δ b) = b := fun b => by
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using DFunLike.congr_fun hR b

  have hε : ∀ n b, ε (α n b) = ε b := by
    intro n
    induction n with
    | zero => intro b; rw [h0]; simp [hεu]
    | succ n ih =>
      intro b
      have key : ∀ t : B ⊗[A] B,
          ε (Algebra.TensorProduct.lift (α n) (AlgHom.id A B) (fun _ _ => Commute.all _ _) t) =
          ε (Algebra.TensorProduct.lift ((Algebra.ofId A B).comp ε) (AlgHom.id A B)
            (fun _ _ => Commute.all _ _) t) := by
        intro t
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul b c => simp [Algebra.TensorProduct.lift_tmul, ih, hεu]
        | add s t hs ht => simp only [map_add, hs, ht]
      rw [hS n, AlgHom.comp_apply, key, hL' b]

  have hright : ∀ (ψ : B →ₐ[A] B) (t : B ⊗[A] B),
      Algebra.TensorProduct.lift ψ ((Algebra.ofId A B).comp ε) (fun _ _ => Commute.all _ _) t =
      ψ (Algebra.TensorProduct.lift (AlgHom.id A B) ((Algebra.ofId A B).comp ε)
        (fun _ _ => Commute.all _ _) t) := by
    intro ψ t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b c => simp [Algebra.TensorProduct.lift_tmul]
    | add s t hs ht => simp only [map_add, hs, ht]

  have gen : ∀ (φ : B →ₐ[A] B), (∀ b, ε (φ b) = ε b) → ∀ t : B ⊗[A] B,
      Algebra.TensorProduct.lift φ (AlgHom.id A B) (fun _ _ => Commute.all _ _) t
        - Algebra.TensorProduct.lift ((Algebra.ofId A B).comp ε) (AlgHom.id A B)
            (fun _ _ => Commute.all _ _) t
        - Algebra.TensorProduct.lift φ ((Algebra.ofId A B).comp ε) (fun _ _ => Commute.all _ _) t
        + Algebra.TensorProduct.lift ((Algebra.ofId A B).comp ε) ((Algebra.ofId A B).comp ε)
            (fun _ _ => Commute.all _ _) t ∈ RingHom.ker ε ^ 2 := by
    intro φ hφ t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b c =>
      simp only [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, AlgHom.id_apply,
        Algebra.ofId_apply]
      have e : φ b * c - algebraMap A B (ε b) * c - φ b * algebraMap A B (ε c)
          + algebraMap A B (ε b) * algebraMap A B (ε c)
          = (φ b - algebraMap A B (ε b)) * (c - algebraMap A B (ε c)) := by ring
      rw [e, sq]
      exact Ideal.mul_mem_mul (by rw [RingHom.mem_ker]; simp [hφ, hεu])
        (by rw [RingHom.mem_ker]; simp [hεu])
    | add s t hs ht =>
      have e := add_mem hs ht
      simp only [map_add]
      convert e using 1
      abel
  intro n
  induction n with
  | zero =>
    intro x hx
    rw [h0]
    simp [RingHom.mem_ker.mp hx]
  | succ n ih =>
    intro x hx
    have E := gen (α n) (hε n) (Δ x)
    rw [hL' x, hright (α n) (Δ x), hright ((Algebra.ofId A B).comp ε) (Δ x), hR' x] at E
    have hx0 : ε x = 0 := by simpa using hx
    have h4 : ((Algebra.ofId A B).comp ε) x = 0 := by simp [hx0]
    rw [h4, add_zero] at E
    rw [hS n, AlgHom.comp_apply]
    convert add_mem E (ih x hx) using 1
    push_cast
    ring

end GlobalTheory
