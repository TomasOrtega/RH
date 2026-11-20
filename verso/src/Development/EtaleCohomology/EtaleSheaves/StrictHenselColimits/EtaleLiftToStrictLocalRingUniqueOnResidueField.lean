import Development.EtaleCohomology.EtaleSheaves.StrictHenselColimits

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut TensorProduct

namespace LateralTheory.E.ColimPf.RigidPf

/- English proof (translation)
Introduce `A B O Ω _ ψ g hg hloc u v huv hψ`. Set `: Algebra A B` to `g.hom.toAlgebra`. Set `: Algebra A O` to `(g ≫ u).hom.toAlgebra`. Establish `: Algebra.Etale A B` using `hg`. Set `u' : B →ₐ[A] O` to `{ u.hom with commutes' := fun _ => rfl }`.

Establish `hv : ∀ a, v.hom (g.hom a) = (g ≫ u).hom a` using `fun a => by rw [huv]; rfl`. Set `v' : B →ₐ[A] O` to `{ v.hom with commutes' := hv }`. Take `⟨e, he, hsp⟩ : ∃ e, IsIdempotentElem e ∧ KaehlerDifferential.ideal A B = B ⊗[A] B ∙ e` from `(Ideal.isIdempotentElem_iff_of_fg _ (KaehlerDifferential.ideal_fg A B)).mp <| (Ideal.cotangent_subsingleton_iff _).mp <| inferInstanceAs <| Subsingleton Ω[B⁄A]`. Set `w : B ⊗[A] B →ₐ[A] O` to `Algebra.TensorProduct.productMap u' v'`. Establish `hψu : ∀ b, ψ (v.hom b) = ψ (u.hom b)` using `fun b => (DFunLike.congr_fun hψ b).symm`.

Establish `hpt : ∀ t : B ⊗[A] B, ψ (w t) = ψ (u.hom (Algebra.TensorProduct.lmul' A t))`. Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y`.

Simplify using `only [w, Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.lmul'_apply_tmul, map_mul]`. Express the relevant statement in the definitionally equal form `ψ (u.hom x) * ψ (v.hom y) = ψ (u.hom x) * ψ (u.hom y)`. Rewrite using `[hψu]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Establish `he0 : e ∈ KaehlerDifferential.ideal A B` using `by rw [hsp]; exact Submodule.mem_span_singleton_self e`.

Establish `hwe : ψ (w e) = 0`. Rewrite using `[hpt]`. Establish `: Algebra.TensorProduct.lmul' A e = 0` using `he0`. Rewrite using `[this, map_zero, map_zero]`. Establish `hwe0 : w e = 0`.

Establish `hu : IsUnit (1 - w e)` using `hloc _ (by rw [map_sub, map_one, hwe, sub_zero]; exact one_ne_zero)`. Establish `hid : w e * (1 - w e) = 0`. Use `(he.map w).eq` as an intermediate fact. Rewrite using `[mul_sub, mul_one, this, sub_self]`. Simplify using `using (hu.mul_left_eq_zero).1 hid`.

Use extensionality with `b`. Establish `hb : b ⊗ₜ[A] (1 : B) - 1 ⊗ₜ b ∈ KaehlerDifferential.ideal A B`. Rewrite using `[KaehlerDifferential.ideal, RingHom.mem_ker, map_sub]`. Simplify using the standard rewrite rules. Rewrite `hb` using `[hsp]`.

Take `⟨r, hr⟩` from `Submodule.mem_span_singleton.1 hb`. Use `congrArg w hr` as an intermediate fact. Rewrite `this` using `[smul_eq_mul, map_mul, hwe0, mul_zero, map_sub]`. Simplify using `only [w, Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one, one_mul] at this`. Conclude with `sub_eq_zero.1 this.symm`.
-/
theorem etale_lift_to_strict_local_ring_unique_on_residue_field : LateralTheory.E.ColimPf.Rigid := by
  intro A B O Ω _ ψ g hg hloc u v huv hψ
  let : Algebra A B := g.hom.toAlgebra
  let : Algebra A O := (g ≫ u).hom.toAlgebra
  have : Algebra.Etale A B := hg
  let u' : B →ₐ[A] O := { u.hom with commutes' := fun _ => rfl }
  have hv : ∀ a, v.hom (g.hom a) = (g ≫ u).hom a := fun a => by rw [huv]; rfl
  let v' : B →ₐ[A] O := { v.hom with commutes' := hv }
  obtain ⟨e, he, hsp⟩ : ∃ e, IsIdempotentElem e ∧ KaehlerDifferential.ideal A B = B ⊗[A] B ∙ e :=
    (Ideal.isIdempotentElem_iff_of_fg _ (KaehlerDifferential.ideal_fg A B)).mp <|
      (Ideal.cotangent_subsingleton_iff _).mp <| inferInstanceAs <| Subsingleton Ω[B⁄A]
  let w : B ⊗[A] B →ₐ[A] O := Algebra.TensorProduct.productMap u' v'
  have hψu : ∀ b, ψ (v.hom b) = ψ (u.hom b) := fun b => (DFunLike.congr_fun hψ b).symm
  have hpt : ∀ t : B ⊗[A] B, ψ (w t) = ψ (u.hom (Algebra.TensorProduct.lmul' A t)) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [w, Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.lmul'_apply_tmul, map_mul]
      change ψ (u.hom x) * ψ (v.hom y) = ψ (u.hom x) * ψ (u.hom y)
      rw [hψu]
    | add x y hx hy => simp only [map_add, hx, hy]
  have he0 : e ∈ KaehlerDifferential.ideal A B := by rw [hsp]; exact Submodule.mem_span_singleton_self e
  have hwe : ψ (w e) = 0 := by
    rw [hpt]
    have : Algebra.TensorProduct.lmul' A e = 0 := he0
    rw [this, map_zero, map_zero]
  have hwe0 : w e = 0 := by
    have hu : IsUnit (1 - w e) := hloc _ (by rw [map_sub, map_one, hwe, sub_zero]; exact one_ne_zero)
    have hid : w e * (1 - w e) = 0 := by
      have := (he.map w).eq
      rw [mul_sub, mul_one, this, sub_self]
    simpa using (hu.mul_left_eq_zero).1 hid
  ext b
  have hb : b ⊗ₜ[A] (1 : B) - 1 ⊗ₜ b ∈ KaehlerDifferential.ideal A B := by
    rw [KaehlerDifferential.ideal, RingHom.mem_ker, map_sub]
    simp
  rw [hsp] at hb
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hb
  have := congrArg w hr
  rw [smul_eq_mul, map_mul, hwe0, mul_zero, map_sub] at this
  simp only [w, Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one, one_mul] at this
  exact sub_eq_zero.1 this.symm

end LateralTheory.E.ColimPf.RigidPf
