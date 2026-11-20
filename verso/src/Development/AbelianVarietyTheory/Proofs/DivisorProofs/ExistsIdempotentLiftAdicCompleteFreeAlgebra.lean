import Mathlib

open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.IdemNewton

variable {A : Type} [CommRing A] {Λ : Type} [Ring Λ] [Algebra A Λ]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hz i`. Use `Submodule.smul_induction_on hz (fun r hr y _ => ?_) (fun y w hy hw => ?_)` and prove the remaining obligations. Rewrite using `[map_smul, Finsupp.smul_apply, smul_eq_mul]`. Conclude with `J.mul_mem_right _ hr`.

Rewrite using `[map_add, Finsupp.add_apply]`. Conclude with `add_mem hy hw`. Introduce `h`. Rewrite using `[← b.sum_repr z]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top`.
-/
theorem mem_smul_top_iff_repr {ι : Type} [Fintype ι] (b : Module.Basis ι A Λ) (J : Ideal A) (z : Λ) :
    z ∈ J • (⊤ : Submodule A Λ) ↔ ∀ i, b.repr z i ∈ J := by
  constructor
  · intro hz i
    refine Submodule.smul_induction_on hz (fun r hr y _ => ?_) (fun y w hy hw => ?_)
    · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact J.mul_mem_right _ hr
    · rw [map_add, Finsupp.add_apply]
      exact add_mem hy hw
  · intro h
    rw [← b.sum_repr z]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

/- English proof (translation)
Use `Submodule.smul_induction_on hz (fun r hr w _ => ?_) (fun u w hu hw => ?_)` and prove the remaining obligations. Rewrite using `[smul_mul_assoc]`. Conclude with `Submodule.smul_mem_smul hr Submodule.mem_top`. Rewrite using `[add_mul]`. Conclude with `add_mem hu hw`.
-/
theorem mul_mem_right {J : Ideal A} {z : Λ} (y : Λ) (hz : z ∈ J • (⊤ : Submodule A Λ)) :
    z * y ∈ J • (⊤ : Submodule A Λ) := by
  refine Submodule.smul_induction_on hz (fun r hr w _ => ?_) (fun u w hu hw => ?_)
  · rw [smul_mul_assoc]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · rw [add_mul]
    exact add_mem hu hw

/- English proof (translation)
Use `Submodule.smul_induction_on hz (fun r hr w _ => ?_) (fun u w hu hw => ?_)` and prove the remaining obligations. Rewrite using `[mul_smul_comm]`. Conclude with `Submodule.smul_mem_smul hr Submodule.mem_top`. Rewrite using `[mul_add]`. Conclude with `add_mem hu hw`.
-/
theorem mul_mem_left {J : Ideal A} {z : Λ} (y : Λ) (hz : z ∈ J • (⊤ : Submodule A Λ)) :
    y * z ∈ J • (⊤ : Submodule A Λ) := by
  refine Submodule.smul_induction_on hz (fun r hr w _ => ?_) (fun u w hu hw => ?_)
  · rw [mul_smul_comm]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · rw [mul_add]
    exact add_mem hu hw

/- English proof (translation)
Use `Submodule.smul_induction_on hz (fun r hr w _ => ?_) (fun u w hu hw => ?_)` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, Submodule.mul_smul]`. Conclude with `Submodule.smul_mem_smul hr (mul_mem_left w hy)`. Rewrite using `[add_mul]`. Conclude with `add_mem hu hw`.
-/
theorem mul_mem {J K : Ideal A} {z y : Λ} (hz : z ∈ J • (⊤ : Submodule A Λ))
    (hy : y ∈ K • (⊤ : Submodule A Λ)) : z * y ∈ (J * K) • (⊤ : Submodule A Λ) := by
  refine Submodule.smul_induction_on hz (fun r hr w _ => ?_) (fun u w hu hw => ?_)
  · rw [smul_mul_assoc, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hr (mul_mem_left w hy)
  · rw [add_mul]
    exact add_mem hu hw

/- English proof (translation)
Introduce `A _ I _ Λ _ _ _ _ x hx`. Set `b` to `Module.Free.chooseBasis A Λ`. Establish `mono : ∀ {k m : ℕ}, k ≤ m → ∀ {z : Λ}, z ∈ (I ^ m) • (⊤ : Submodule A Λ) → z ∈ (I ^ k) • (⊤ : Submodule A Λ)` using `fun hkm _ hz => Submodule.smul_mono_left (Ideal.pow_le_pow_right hkm) hz`. Set `f : ℕ → Λ` to `fun k => Nat.rec x (fun _ y => 3 * (y * y) - 2 * (y * y * y)) k`. Establish `f0 : f 0 = x` using `rfl`.

Establish `fs : ∀ k, f (k + 1) = 3 * (f k * f k) - 2 * (f k * f k * f k)` using `fun k => rfl`. Establish `h1 : ∀ k, (f k * f k - f k) ∈ (I ^ (k + 1)) • (⊤ : Submodule A Λ)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simpa [f0] using hx`.

Consider the case `succ k ih`. Establish `e : f (k + 1) * f (k + 1) - f (k + 1) = ((f k * f k - f k) * (f k * f k - f k)) * (4 * (f k * f k) - 4 * f k - 3)`. Rewrite using `[fs]`. Use `noncomm_ring`. Rewrite using `[e]`.

Use `mul_mem_right _ ?_` and prove the remaining obligations. Use `mul_mem ih ih` as an intermediate fact. Rewrite `this` using `[← pow_add]`. Conclude with `mono (by omega) this`. Establish `h2 : ∀ k, (f (k + 1) - f k) ∈ (I ^ (k + 1)) • (⊤ : Submodule A Λ)`.

Introduce `k`. Establish `e : f (k + 1) - f k = (f k * f k - f k) * (1 - 2 * f k)`. Rewrite using `[fs]`. Use `noncomm_ring`. Rewrite using `[e]`.

Conclude with `mul_mem_right _ (h1 k)`. Establish `h3 : ∀ k m, k ≤ m → (f m - f k) ∈ (I ^ (k + 1)) • (⊤ : Submodule A Λ)`. Introduce `k m hkm`. Proceed by induction on `m, hkm using Nat.le_induction with`. Consider the case `base => simp`.

Consider the case `succ m hkm ih`. Establish `e : f (m + 1) - f k = (f (m + 1) - f m) + (f m - f k)` using `by abel`. Rewrite using `[e]`. Conclude with `add_mem (mono (by omega) (h2 m)) ih`. Establish `h4 : ∀ i, ∃ L : A, ∀ k, b.repr (f k) i - L ∈ I ^ k`.

Introduce `i`. Take `⟨L, hL⟩` from `IsPrecomplete.prec' (I := I) (fun k => b.repr (f k) i) (fun {k m} hkm => by`. Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_mem_iff, neg_sub]`. Use `(mem_smul_top_iff_repr b _ _).1 (mono (Nat.le_succ k) (h3 k m hkm)) i` as an intermediate fact. Rewrite using `[map_sub, Finsupp.sub_apply] at this)` and apply the resulting hypothesis.

Use `⟨L, fun k => ?_⟩` and prove the remaining obligations. Use `hL k` as an intermediate fact. Rewrite `this` using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`. Then use the resulting hypothesis. Use `choose L hL using h4`. Set `e : Λ` to `b.equivFun.symm L`.

Establish `he : ∀ i, b.repr e i = L i` using `fun i => by`. Use `congrFun (b.equivFun.apply_symm_apply L) i` as an intermediate fact. Rewrite `this` using `[Module.Basis.equivFun_apply]`. Then use the resulting hypothesis. Establish `hL' : ∀ k, (f k - e) ∈ (I ^ k) • (⊤ : Submodule A Λ)` using `fun k => (mem_smul_top_iff_repr b _ _).2 fun i => by`. Rewrite using `[map_sub, Finsupp.sub_apply, he]`.

Conclude with `hL i k`. Use `⟨e, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `e * e = e`. Rewrite using `[← sub_eq_zero]`. Use `b.ext_elem fun i => ?_` and prove the remaining obligations.

Rewrite using `[map_zero, Finsupp.zero_apply]`. Use `IsHausdorff.haus' (I := I) _ fun k => ?_` and prove the remaining obligations. Rewrite using `[SModEq.zero, smul_eq_mul, Ideal.mul_top]`. Use `(mem_smul_top_iff_repr b _ _).1 ?_ i` and prove the remaining obligations. Establish `e1 : e * e - e = (f k * f k - f k) - ((f k - e) * (f k - 1) + e * (f k - e))` using `by noncomm_ring`.

Rewrite using `[e1]`. Conclude with `sub_mem (mono (Nat.le_succ k) (h1 k)) (add_mem (mul_mem_right _ (hL' k)) (mul_mem_left _ (hL' k)))`. Establish `e1 : e - x = (f 1 - f 0) - (f 1 - e)` using `by rw [f0]; abel`. Rewrite using `[e1]`. Establish `a` using `h2 0`.

Establish `c` using `hL' 1`. Rewrite `a` using `[zero_add, pow_one]`. Rewrite `c` using `[pow_one]`. Conclude with `sub_mem a c`.
-/
theorem exists_idem : ∀ (A : Type) [CommRing A] (I : Ideal A) [IsAdicComplete I A] (Λ : Type) [Ring Λ]
    [Algebra A Λ] [Module.Free A Λ] [Module.Finite A Λ] (x : Λ),
    x * x - x ∈ I • (⊤ : Submodule A Λ) →
      ∃ e : Λ, IsIdempotentElem e ∧ e - x ∈ I • (⊤ : Submodule A Λ) := by
  intro A _ I _ Λ _ _ _ _ x hx
  let b := Module.Free.chooseBasis A Λ
  have mono : ∀ {k m : ℕ}, k ≤ m → ∀ {z : Λ}, z ∈ (I ^ m) • (⊤ : Submodule A Λ) →
      z ∈ (I ^ k) • (⊤ : Submodule A Λ) := fun hkm _ hz =>
    Submodule.smul_mono_left (Ideal.pow_le_pow_right hkm) hz
  let f : ℕ → Λ := fun k => Nat.rec x (fun _ y => 3 * (y * y) - 2 * (y * y * y)) k
  have f0 : f 0 = x := rfl
  have fs : ∀ k, f (k + 1) = 3 * (f k * f k) - 2 * (f k * f k * f k) := fun k => rfl
  have h1 : ∀ k, (f k * f k - f k) ∈ (I ^ (k + 1)) • (⊤ : Submodule A Λ) := by
    intro k
    induction k with
    | zero => simpa [f0] using hx
    | succ k ih =>
      have e : f (k + 1) * f (k + 1) - f (k + 1) =
          ((f k * f k - f k) * (f k * f k - f k)) * (4 * (f k * f k) - 4 * f k - 3) := by
        rw [fs]; noncomm_ring
      rw [e]
      refine mul_mem_right _ ?_
      have := mul_mem ih ih
      rw [← pow_add] at this
      exact mono (by omega) this
  have h2 : ∀ k, (f (k + 1) - f k) ∈ (I ^ (k + 1)) • (⊤ : Submodule A Λ) := by
    intro k
    have e : f (k + 1) - f k = (f k * f k - f k) * (1 - 2 * f k) := by
      rw [fs]; noncomm_ring
    rw [e]
    exact mul_mem_right _ (h1 k)
  have h3 : ∀ k m, k ≤ m → (f m - f k) ∈ (I ^ (k + 1)) • (⊤ : Submodule A Λ) := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base => simp
    | succ m hkm ih =>
      have e : f (m + 1) - f k = (f (m + 1) - f m) + (f m - f k) := by abel
      rw [e]
      exact add_mem (mono (by omega) (h2 m)) ih
  have h4 : ∀ i, ∃ L : A, ∀ k, b.repr (f k) i - L ∈ I ^ k := by
    intro i
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) (fun k => b.repr (f k) i) (fun {k m} hkm => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_mem_iff, neg_sub]
      have := (mem_smul_top_iff_repr b _ _).1 (mono (Nat.le_succ k) (h3 k m hkm)) i
      rwa [map_sub, Finsupp.sub_apply] at this)
    refine ⟨L, fun k => ?_⟩
    have := hL k
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  choose L hL using h4
  let e : Λ := b.equivFun.symm L
  have he : ∀ i, b.repr e i = L i := fun i => by
    have := congrFun (b.equivFun.apply_symm_apply L) i
    rwa [Module.Basis.equivFun_apply] at this
  have hL' : ∀ k, (f k - e) ∈ (I ^ k) • (⊤ : Submodule A Λ) := fun k =>
    (mem_smul_top_iff_repr b _ _).2 fun i => by
      rw [map_sub, Finsupp.sub_apply, he]
      exact hL i k
  refine ⟨e, ?_, ?_⟩
  · change e * e = e
    rw [← sub_eq_zero]
    refine b.ext_elem fun i => ?_
    rw [map_zero, Finsupp.zero_apply]
    refine IsHausdorff.haus' (I := I) _ fun k => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    refine (mem_smul_top_iff_repr b _ _).1 ?_ i
    have e1 : e * e - e = (f k * f k - f k) - ((f k - e) * (f k - 1) + e * (f k - e)) := by
      noncomm_ring
    rw [e1]
    exact sub_mem (mono (Nat.le_succ k) (h1 k))
      (add_mem (mul_mem_right _ (hL' k)) (mul_mem_left _ (hL' k)))
  · have e1 : e - x = (f 1 - f 0) - (f 1 - e) := by rw [f0]; abel
    rw [e1]
    have a := h2 0
    have c := hL' 1
    rw [zero_add, pow_one] at a
    rw [pow_one] at c
    exact sub_mem a c

end GlobalTheory.IdemNewton
