import ReciprocityTheory.GroupCohomology.CupConnRightStatement

namespace ReciprocityTheory.Coh

universe u

namespace Cx

variable {R : Type u} [CommRing R] {A B C : Cx R}

/- English proof (translation)
Rewrite using `[← φ.comm, hx, map_zero]`.
-/
theorem Hom.d_f_eq_zero (φ : Hom A B) {n : ℕ} {x : A.X n} (hx : A.d n x = 0) :
    B.d n (φ.f n x) = 0 := by
  rw [← φ.comm, hx, map_zero]

/- English proof (translation)
Rewrite using `[map_add, hx, hy, add_zero]`.
-/
theorem d_add_eq_zero {n : ℕ} {x y : A.X n} (hx : A.d n x = 0) (hy : A.d n y = 0) :
    A.d n (x + y) = 0 := by
  rw [map_add, hx, hy, add_zero]

/- English proof (translation)
Rewrite using `[map_sub, hx, hy, sub_zero]`.
-/
theorem d_sub_eq_zero {n : ℕ} {x y : A.X n} (hx : A.d n x = 0) (hy : A.d n y = 0) :
    A.d n (x - y) = 0 := by
  rw [map_sub, hx, hy, sub_zero]

/- English proof (translation)
Rewrite using `[map_neg, hx, neg_zero]`.
-/
theorem d_neg_eq_zero {n : ℕ} {x : A.X n} (hx : A.d n x = 0) : A.d n (-x) = 0 := by
  rw [map_neg, hx, neg_zero]

/- English proof (translation)
Rewrite using `[map_smul, hx, smul_zero]`. Use the proof step `@[elab_as_elim]`.
-/
theorem d_smul_eq_zero {n : ℕ} (r : R) {x : A.X n} (hx : A.d n x = 0) : A.d n (r • x) = 0 := by
  rw [map_smul, hx, smul_zero]

@[elab_as_elim]
/- English proof (translation)
Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ c`. Conclude with `h z.1 z.2`.
-/
theorem H_ind {n : ℕ} {P : A.H n → Prop} (h : ∀ x hx, P (A.cls n x hx)) (c : A.H n) : P c := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact h z.1 z.2

/- English proof (translation)
Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ c`. Conclude with `⟨z.1, z.2, rfl⟩`.
-/
theorem exists_cls {n : ℕ} (c : A.H n) : ∃ x hx, c = A.cls n x hx := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact ⟨z.1, z.2, rfl⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem cls_zero (n : ℕ) (h : A.d n 0 = 0) : A.cls n 0 h = 0 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem cls_add {n : ℕ} (x y : A.X n) (hx : A.d n x = 0) (hy : A.d n y = 0) :
    A.cls n x hx + A.cls n y hy = A.cls n (x + y) (d_add_eq_zero hx hy) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem cls_sub {n : ℕ} (x y : A.X n) (hx : A.d n x = 0) (hy : A.d n y = 0) :
    A.cls n x hx - A.cls n y hy = A.cls n (x - y) (d_sub_eq_zero hx hy) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem cls_neg {n : ℕ} (x : A.X n) (hx : A.d n x = 0) :
    -A.cls n x hx = A.cls n (-x) (d_neg_eq_zero hx) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem cls_smul {n : ℕ} (r : R) (x : A.X n) (hx : A.d n x = 0) :
    r • A.cls n x hx = A.cls n (r • x) (d_smul_eq_zero r hx) := rfl

/- English proof (translation)
Unfold `cls`. Rewrite using `[Submodule.Quotient.eq]`. Conclude with `Iff.rfl`.
-/
theorem cls_eq_iff {n : ℕ} {x y : A.X n} (hx : A.d n x = 0) (hy : A.d n y = 0) :
    A.cls n x hx = A.cls n y hy ↔ x - y ∈ A.B n := by
  unfold cls
  rw [Submodule.Quotient.eq]
  exact Iff.rfl

/- English proof (translation)
Unfold `cls`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Conclude with `Iff.rfl`.
-/
@[simp] theorem cls_eq_zero_iff {n : ℕ} {x : A.X n} (hx : A.d n x = 0) :
    A.cls n x hx = 0 ↔ x ∈ A.B n := by
  unfold cls
  rw [Submodule.Quotient.mk_eq_zero]
  exact Iff.rfl

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem cls_congr {n : ℕ} {x y : A.X n} (hx : A.d n x = 0) (hy : A.d n y = 0) (h : x = y) :
    A.cls n x hx = A.cls n y hy := by
  subst h
  rfl

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero`. Express the relevant statement in the definitionally equal form `x ∈ (⊥ : Submodule R (A.X 0)) at h`. Rewrite using `[(Submodule.mem_bot R).1 h, map_zero]`. Consider the case `succ n`.

Express the relevant statement in the definitionally equal form `x ∈ LinearMap.range (A.d n) at h`. Take `⟨y, rfl⟩` from `LinearMap.mem_range.1 h`. Conclude with `A.dd n y`.
-/
theorem d_eq_zero_of_mem_B {n : ℕ} {x : A.X n} (h : x ∈ A.B n) : A.d n x = 0 := by
  cases n with
  | zero =>
    change x ∈ (⊥ : Submodule R (A.X 0)) at h
    rw [(Submodule.mem_bot R).1 h, map_zero]
  | succ n =>
    change x ∈ LinearMap.range (A.d n) at h
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 h
    exact A.dd n y

/- English proof (translation)
Express the relevant statement in the definitionally equal form `x ∈ LinearMap.range (A.d n) ↔ _`. Conclude with `LinearMap.mem_range`.
-/
theorem mem_B_succ {n : ℕ} {x : A.X (n + 1)} : x ∈ A.B (n + 1) ↔ ∃ y, A.d n y = x := by
  change x ∈ LinearMap.range (A.d n) ↔ _
  exact LinearMap.mem_range

/- English proof (translation)
Express the relevant statement in the definitionally equal form `x ∈ (⊥ : Submodule R (A.X 0)) ↔ _`. Conclude with `Submodule.mem_bot R`.
-/
theorem mem_B_zero {x : A.X 0} : x ∈ A.B 0 ↔ x = 0 := by
  change x ∈ (⊥ : Submodule R (A.X 0)) ↔ _
  exact Submodule.mem_bot R

/- English proof (translation)
Rewrite using `[cls_eq_zero_iff, mem_B_succ]`. Conclude with `⟨y, rfl⟩`.
-/
@[simp] theorem cls_d {n : ℕ} (y : A.X n) (h : A.d (n + 1) (A.d n y) = 0) :
    A.cls (n + 1) (A.d n y) h = 0 := by
  rw [cls_eq_zero_iff, mem_B_succ]
  exact ⟨y, rfl⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem Hom.Z_apply (φ : Hom A B) {n : ℕ} (x : A.Z n) : (φ.Z n x : B.X n) = φ.f n x := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem Hom.H_cls (φ : Hom A B) {n : ℕ} (x : A.X n) (hx : A.d n x = 0) :
    φ.H n (A.cls n x hx) = B.cls n (φ.f n x) (φ.d_f_eq_zero hx) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem Hom.id_f (n : ℕ) (x : A.X n) : (Hom.id A).f n x = x := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem Hom.comp_f (ψ : Hom B C) (φ : Hom A B) (n : ℕ) (x : A.X n) :
    (ψ.comp φ).f n x = ψ.f n (φ.f n x) := rfl

/- English proof (translation)
Use `LinearMap.ext fun c => ?_` and prove the remaining obligations. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ c`. Both sides reduce to the same expression.
-/
@[simp] theorem Hom.id_H (n : ℕ) : (Hom.id A).H n = LinearMap.id := by
  refine LinearMap.ext fun c => ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  rfl

/- English proof (translation)
Use `LinearMap.ext fun c => ?_` and prove the remaining obligations. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ c`. Both sides reduce to the same expression.
-/
theorem Hom.comp_H (ψ : Hom B C) (φ : Hom A B) (n : ℕ) : (ψ.comp φ).H n = (ψ.H n).comp (φ.H n) := by
  refine LinearMap.ext fun c => ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  rfl

/- English proof (translation)
Rewrite using `[Hom.comp_H]`. Both sides reduce to the same expression.
-/
theorem Hom.comp_H_apply (ψ : Hom B C) (φ : Hom A B) (n : ℕ) (c : A.H n) :
    (ψ.comp φ).H n c = ψ.H n (φ.H n c) := by
  rw [Hom.comp_H]
  rfl

/- English proof (translation)
Use `LinearMap.ext fun c => ?_` and prove the remaining obligations. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ c`. Conclude with `h z.1 z.2`.
-/
theorem H_hom_ext {M : Type*} [AddCommGroup M] [Module R M] {n : ℕ} {f g : A.H n →ₗ[R] M}
    (h : ∀ x hx, f (A.cls n x hx) = g (A.cls n x hx)) : f = g := by
  refine LinearMap.ext fun c => ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact h z.1 z.2

end Cx

open Cx in
/- English proof (translation)
Introduce `R _ A B C φ ψ n`. Conclude with `⟨Hom.id_H n, Hom.comp_H ψ φ n, exists_cls, fun x hx => cls_eq_zero_iff hx, fun x hx => ⟨_, Hom.H_cls φ x hx⟩⟩`.
-/
theorem basic_holds : BasicStatement.{u} := by
  intro R _ A B C φ ψ n
  exact ⟨Hom.id_H n, Hom.comp_H ψ φ n, exists_cls, fun x hx => cls_eq_zero_iff hx,
    fun x hx => ⟨_, Hom.H_cls φ x hx⟩⟩

end ReciprocityTheory.Coh
