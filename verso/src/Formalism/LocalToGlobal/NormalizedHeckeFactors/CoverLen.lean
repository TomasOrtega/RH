import Mathlib

namespace Formalism.L2.NCov

open Module

section

variable {R R' M M' : Type*} [CommRing R] [CommRing R'] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R' M']

/- English proof (translation)
Use `letI := RingHomInvPair.of_ringEquiv φ`. Use `letI := RingHomInvPair.symm (φ : R →+* R') (φ.symm : R' →+* R)`. Set `e : M ≃ₛₗ[(φ : R →+* R')] M'` to `LinearEquiv.ofBijective f hf`. Rewrite using `[Module.length_eq_height, Module.length_eq_height, ← Order.height_orderIso (Submodule.orderIsoMapComap e) ⊤, OrderIso.map_top]`.
-/
theorem length_eq_of_bijective (φ : R ≃+* R') (f : M →ₛₗ[(φ : R →+* R')] M') (hf : Function.Bijective f) :
    Module.length R' M' = Module.length R M := by
  letI := RingHomInvPair.of_ringEquiv φ
  letI := RingHomInvPair.symm (φ : R →+* R') (φ.symm : R' →+* R)
  let e : M ≃ₛₗ[(φ : R →+* R')] M' := LinearEquiv.ofBijective f hf
  rw [Module.length_eq_height, Module.length_eq_height,
    ← Order.height_orderIso (Submodule.orderIsoMapComap e) ⊤, OrderIso.map_top]

/- English proof (translation)
Set `g : (M ⧸ q) →ₛₗ[(φ : R →+* R')] (M' ⧸ q')` to `q.mapQ q' f (fun x hx => (h x).2 hx)`. Use `length_eq_of_bijective φ g ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `y hy`. Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective q y`.

Establish `hy' : (Submodule.Quotient.mk (f a) : M' ⧸ q') = 0` using `hy`. Rewrite `hy'` using `[Submodule.Quotient.mk_eq_zero]`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Conclude with `(h a).1 hy'`. Introduce `y`.

Take `⟨b, rfl⟩` from `Submodule.Quotient.mk_surjective q' y`. Take `⟨a, rfl⟩` from `hf.2 b`. Conclude with `⟨Submodule.Quotient.mk a, rfl⟩`.
-/
private theorem length_quotient_eq_of_bijective_semilinear (φ : R ≃+* R') (f : M →ₛₗ[(φ : R →+* R')] M')
    (hf : Function.Bijective f) (q : Submodule R M) (q' : Submodule R' M')
    (h : ∀ x, f x ∈ q' ↔ x ∈ q) :
    Module.length R' (M' ⧸ q') = Module.length R (M ⧸ q) := by
  let g : (M ⧸ q) →ₛₗ[(φ : R →+* R')] (M' ⧸ q') := q.mapQ q' f (fun x hx => (h x).2 hx)
  refine length_eq_of_bijective φ g ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective q y
    have hy' : (Submodule.Quotient.mk (f a) : M' ⧸ q') = 0 := hy
    rw [Submodule.Quotient.mk_eq_zero] at hy'
    rw [Submodule.Quotient.mk_eq_zero]
    exact (h a).1 hy'
  · intro y
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective q' y
    obtain ⟨a, rfl⟩ := hf.2 b
    exact ⟨Submodule.Quotient.mk a, rfl⟩

/- English proof (translation)
The claim follows from `RingHomInvPair.of_ringEquiv φ Module.length R' (↥(p.map f) ⧸ (q.map f).comap (p.map f).subtype) = Module.length R (↥p ⧸ q.comap p.subtype) := by letI := RingHomInvPair.of_ringEquiv φ let g : ↥p →ₛₗ[(φ : R →+* R')] ↥(p.map f) := { toFun := fun x => ⟨f x, Submodule.mem_map_of_mem x …`.
-/
theorem length_quot_map (φ : R ≃+* R') (f : M →ₛₗ[(φ : R →+* R')] M') (hf : Function.Injective f)
    (p q : Submodule R M) :
    haveI := RingHomInvPair.of_ringEquiv φ
    Module.length R' (↥(p.map f) ⧸ (q.map f).comap (p.map f).subtype) =
      Module.length R (↥p ⧸ q.comap p.subtype) := by
  letI := RingHomInvPair.of_ringEquiv φ
  let g : ↥p →ₛₗ[(φ : R →+* R')] ↥(p.map f) :=
    { toFun := fun x => ⟨f x, Submodule.mem_map_of_mem x.2⟩
      map_add' := fun x y => Subtype.ext (map_add f (x : M) (y : M))
      map_smul' := fun r x => Subtype.ext (f.map_smulₛₗ r (x : M)) }
  refine length_quotient_eq_of_bijective_semilinear φ g ⟨?_, ?_⟩ _ _ ?_
  · intro x y hxy
    exact Subtype.ext (hf (congrArg Subtype.val hxy))
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    exact ⟨⟨x, hx⟩, rfl⟩
  · intro x
    show f x ∈ q.map f ↔ (x : M) ∈ q
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hx
      rw [← hf hyx]
      exact hy
    · intro hx
      exact Submodule.mem_map_of_mem hx

/- English proof (translation)
Set `F : R →ₛₗ[(φ : R →+* R')] R'` to `{ toFun := φ map_add' := map_add φ map_smul' := fun r x => by simp only [smul_eq_mul, map_mul, RingEquiv.coe_toRingHom] }`. Use `length_quotient_eq_of_bijective_semilinear φ F φ.bijective _ _ ?_` and prove the remaining obligations. Introduce `x`. Use `show φ x ∈ Ideal.span {(n : R')} ↔ x ∈ Ideal.span {(n : R)}`. Rewrite using `[Ideal.mem_span_singleton, Ideal.mem_span_singleton]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc⟩`. Conclude with `⟨φ.symm c, by apply φ.injective; simp [hc]⟩`. Introduce and unpack `⟨c, rfl⟩`. Conclude with `⟨φ c, by simp⟩`.
-/
theorem length_quot_natCast (φ : R ≃+* R') (n : ℕ) :
    Module.length R' (R' ⧸ Ideal.span {(n : R')}) = Module.length R (R ⧸ Ideal.span {(n : R)}) := by
  let F : R →ₛₗ[(φ : R →+* R')] R' :=
    { toFun := φ
      map_add' := map_add φ
      map_smul' := fun r x => by simp only [smul_eq_mul, map_mul, RingEquiv.coe_toRingHom] }
  refine length_quotient_eq_of_bijective_semilinear φ F φ.bijective _ _ ?_
  intro x
  show φ x ∈ Ideal.span {(n : R')} ↔ x ∈ Ideal.span {(n : R)}
  rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨φ.symm c, by apply φ.injective; simp [hc]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨φ c, by simp⟩

end

end Formalism.L2.NCov
