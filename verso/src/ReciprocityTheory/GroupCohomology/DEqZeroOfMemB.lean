import ReciprocityTheory.GroupCohomology.CupConnRightStatement

namespace ReciprocityTheory.Coh

universe u

namespace Cx

variable {R : Type u} [CommRing R] {A B C : Cx R}

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem Hom.d_f_eq_zero (φ : Hom A B) {n : ℕ} {x : A.X n} (hx : A.d n x = 0) :
    B.d n (φ.f n x) = 0 := by
  rw [← φ.comm, hx, map_zero]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem d_add_eq_zero {n : ℕ} {x y : A.X n} (hx : A.d n x = 0) (hy : A.d n y = 0) :
    A.d n (x + y) = 0 := by
  rw [map_add, hx, hy, add_zero]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem d_sub_eq_zero {n : ℕ} {x y : A.X n} (hx : A.d n x = 0) (hy : A.d n y = 0) :
    A.d n (x - y) = 0 := by
  rw [map_sub, hx, hy, sub_zero]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem d_neg_eq_zero {n : ℕ} {x : A.X n} (hx : A.d n x = 0) : A.d n (-x) = 0 := by
  rw [map_neg, hx, neg_zero]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem d_smul_eq_zero {n : ℕ} (r : R) {x : A.X n} (hx : A.d n x = 0) : A.d n (r • x) = 0 := by
  rw [map_smul, hx, smul_zero]

@[elab_as_elim]
/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem H_ind {n : ℕ} {P : A.H n → Prop} (h : ∀ x hx, P (A.cls n x hx)) (c : A.H n) : P c := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact h z.1 z.2

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
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
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem cls_eq_iff {n : ℕ} {x y : A.X n} (hx : A.d n x = 0) (hy : A.d n y = 0) :
    A.cls n x hx = A.cls n y hy ↔ x - y ∈ A.B n := by
  unfold cls
  rw [Submodule.Quotient.eq]
  exact Iff.rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Unfold both sides to obtain the same proposition, which implies itself.
-/
@[simp] theorem cls_eq_zero_iff {n : ℕ} {x : A.X n} (hx : A.d n x = 0) :
    A.cls n x hx = 0 ↔ x ∈ A.B n := by
  unfold cls
  rw [Submodule.Quotient.mk_eq_zero]
  exact Iff.rfl

/- English proof (translation)
Substitute using the available equality. Both sides reduce to the same expression.
-/
theorem cls_congr {n : ℕ} {x y : A.X n} (hx : A.d n x = 0) (hy : A.d n y = 0) (h : x = y) :
    A.cls n x hx = A.cls n y hy := by
  subst h
  rfl

/- English proof (translation)
Split into cases according to the possible forms of the given data. Treat this case separately. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Treat this case separately.

Express the relevant assertion in an equivalent form by its definition. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
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
Express the relevant assertion in an equivalent form by its definition. A detailed English derivation is pending.
-/
theorem mem_B_succ {n : ℕ} {x : A.X (n + 1)} : x ∈ A.B (n + 1) ↔ ∃ y, A.d n y = x := by
  change x ∈ LinearMap.range (A.d n) ↔ _
  exact LinearMap.mem_range

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. A detailed English derivation is pending.
-/
theorem mem_B_zero {x : A.X 0} : x ∈ A.B 0 ↔ x = 0 := by
  change x ∈ (⊥ : Submodule R (A.X 0)) ↔ _
  exact Submodule.mem_bot R

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
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
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Both sides reduce to the same expression.
-/
@[simp] theorem Hom.id_H (n : ℕ) : (Hom.id A).H n = LinearMap.id := by
  refine LinearMap.ext fun c => ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  rfl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Both sides reduce to the same expression.
-/
theorem Hom.comp_H (ψ : Hom B C) (φ : Hom A B) (n : ℕ) : (ψ.comp φ).H n = (ψ.H n).comp (φ.H n) := by
  refine LinearMap.ext fun c => ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem Hom.comp_H_apply (ψ : Hom B C) (φ : Hom A B) (n : ℕ) (c : A.H n) :
    (ψ.comp φ).H n c = ψ.H n (φ.H n c) := by
  rw [Hom.comp_H]
  rfl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem H_hom_ext {M : Type*} [AddCommGroup M] [Module R M] {n : ℕ} {f g : A.H n →ₗ[R] M}
    (h : ∀ x hx, f (A.cls n x hx) = g (A.cls n x hx)) : f = g := by
  refine LinearMap.ext fun c => ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact h z.1 z.2

end Cx

open Cx in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem basic_holds : BasicStatement.{u} := by
  intro R _ A B C φ ψ n
  exact ⟨Hom.id_H n, Hom.comp_H ψ φ n, exists_cls, fun x hx => cls_eq_zero_iff hx,
    fun x hx => ⟨_, Hom.H_cls φ x hx⟩⟩

end ReciprocityTheory.Coh
