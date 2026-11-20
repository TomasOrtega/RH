import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace GenericFibreModelTransport

open MvPolynomial

/- English proof (translation)
Establish `hring : (Algebra.adjoin k₂ (h '' s)).toSubring = (Algebra.adjoin k₁ s).toSubring.map h`. Rewrite using `[Algebra.adjoin_eq_ring_closure, Algebra.adjoin_eq_ring_closure, RingHom.map_closure, Set.image_union]`. Use `congr 2`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨c, rfl⟩`. Conclude with `⟨algebraMap k₁ A₁ (i.symm c), ⟨_, rfl⟩, by simpa using (congr($hc (i.symm c))).symm⟩`. Introduce and unpack `⟨_, ⟨c, rfl⟩, rfl⟩`. Conclude with `⟨i c, by simpa using congr($hc c)⟩`. Establish `hmem : ∀ y, y ∈ Algebra.adjoin k₂ (h '' s) ↔ ∃ x ∈ Algebra.adjoin k₁ s, h x = y` using `fun y => by`.

Rewrite using `[← Subalgebra.mem_toSubring, hring, Subring.mem_map]`. Both sides reduce to the same expression. Set `g : Algebra.adjoin k₁ s →+* Algebra.adjoin k₂ (h '' s)` to `(h.comp (Algebra.adjoin k₁ s).val.toRingHom).codRestrict (Algebra.adjoin k₂ (h '' s)) (fun x => (hmem _).2 ⟨x, x.2, rfl⟩)`. Establish `hg : Function.Bijective g`. Use `⟨fun x y hxy => Subtype.ext (h.injective (congr_arg Subtype.val hxy)), fun y => ?_⟩` and prove the remaining obligations.

Take `⟨x, hx, e⟩` from `(hmem y).1 y.2`. Conclude with `⟨⟨x, hx⟩, Subtype.ext e⟩`. Set `j` to `RingEquiv.ofBijective g hg`. Use `⟨Algebra.finrank_eq_of_equiv_equiv i j (RingHom.ext fun c => Subtype.ext congr($hc c)), (transcendental_ringHom_iff_of_comp_eq j h h.injective (RingHom.ext fun x => rfl)).symm⟩` and prove the remaining obligations.
-/
theorem adjoin_transport {k₁ A₁ k₂ A₂ : Type*} [Field k₁] [Field A₁] [Algebra k₁ A₁] [Field k₂] [Field A₂]
    [Algebra k₂ A₂] (i : k₁ ≃+* k₂) (h : A₁ →+* A₂)
    (hc : (algebraMap k₂ A₂).comp i.toRingHom = h.comp (algebraMap k₁ A₁)) (s : Set A₁) (a : A₁) :
    Module.finrank k₁ (Algebra.adjoin k₁ s) = Module.finrank k₂ (Algebra.adjoin k₂ (h '' s)) ∧
      (Transcendental (Algebra.adjoin k₁ s) a ↔ Transcendental (Algebra.adjoin k₂ (h '' s)) (h a)) := by
  have hring : (Algebra.adjoin k₂ (h '' s)).toSubring = (Algebra.adjoin k₁ s).toSubring.map h := by
    rw [Algebra.adjoin_eq_ring_closure, Algebra.adjoin_eq_ring_closure, RingHom.map_closure, Set.image_union]
    congr 2
    ext y
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨algebraMap k₁ A₁ (i.symm c), ⟨_, rfl⟩, by simpa using (congr($hc (i.symm c))).symm⟩
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      exact ⟨i c, by simpa using congr($hc c)⟩
  have hmem : ∀ y, y ∈ Algebra.adjoin k₂ (h '' s) ↔ ∃ x ∈ Algebra.adjoin k₁ s, h x = y := fun y => by
    rw [← Subalgebra.mem_toSubring, hring, Subring.mem_map]; rfl
  let g : Algebra.adjoin k₁ s →+* Algebra.adjoin k₂ (h '' s) :=
    (h.comp (Algebra.adjoin k₁ s).val.toRingHom).codRestrict (Algebra.adjoin k₂ (h '' s))
      (fun x => (hmem _).2 ⟨x, x.2, rfl⟩)
  have hg : Function.Bijective g := by
    refine ⟨fun x y hxy => Subtype.ext (h.injective (congr_arg Subtype.val hxy)), fun y => ?_⟩
    obtain ⟨x, hx, e⟩ := (hmem y).1 y.2
    exact ⟨⟨x, hx⟩, Subtype.ext e⟩
  let j := RingEquiv.ofBijective g hg
  refine ⟨Algebra.finrank_eq_of_equiv_equiv i j (RingHom.ext fun c => Subtype.ext congr($hc c)),
    (transcendental_ringHom_iff_of_comp_eq j h h.injective (RingHom.ext fun x => rfl)).symm⟩

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => rw [eval₂_C, eq_intCast]`. Conclude with `intCast_mem _ a`. Consider the case `add p q hp hq => rw [eval₂_add]`. Conclude with `add_mem hp hq`.

Consider the case `mul_X p n hp => rw [eval₂_mul, eval₂_X]`. Conclude with `mul_mem hp (Subfield.subset_closure ⟨n, rfl⟩)`.
-/
theorem eval₂_mem_closure {σ F : Type*} [Field F] (c : ℤ →+* F) (y : σ → F) (f : MvPolynomial σ ℤ) :
    eval₂ c y f ∈ Subfield.closure (Set.range y) := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [eval₂_C, eq_intCast]; exact intCast_mem _ a
  | add p q hp hq => rw [eval₂_add]; exact add_mem hp hq
  | mul_X p n hp => rw [eval₂_mul, eval₂_X]; exact mul_mem hp (Subfield.subset_closure ⟨n, rfl⟩)

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Rewrite `ha` using `[Ideal.Quotient.lift_mk]`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, ← h]`.

Conclude with `ha`.
-/
theorem quotient_lift_injective {A F : Type*} [CommRing A] [Field F] (φ : A →+* F) (P : Ideal A)
    (h : RingHom.ker φ = P) (hP : ∀ a ∈ P, φ a = 0) : Function.Injective (Ideal.Quotient.lift P φ hP) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.Quotient.lift_mk] at ha
  rw [Ideal.Quotient.eq_zero_iff_mem, ← h]
  exact ha

/- English proof (translation)
Set `g : k →+* ι.fieldRange` to `(α.comp k.subtype).codRestrict ι.fieldRange (fun c => hr ▸ Subfield.mem_map.2 ⟨c, c.2, rfl⟩)`. Establish `hg : Function.Bijective g`. Use `⟨fun x y hxy => Subtype.ext (α.injective (congr_arg Subtype.val hxy)), fun y => ?_⟩` and prove the remaining obligations. Establish `hy : (y : A) ∈ k.map α` using `hr ▸ y.2`. Take `⟨x, hx, e⟩` from `Subfield.mem_map.1 hy`.

Conclude with `⟨⟨x, hx⟩, Subtype.ext e⟩`. Conclude with `⟨(RingEquiv.ofBijective g hg).trans ι.rangeRestrictFieldEquiv.symm, fun c => RingHom.rangeRestrictFieldEquiv_apply_symm_apply ι (g c)⟩`.
-/
theorem subfield_equiv {L A Φ : Type*} [Field L] [Field A] [Field Φ] (k : Subfield L) (α : L →+* A)
    (ι : Φ →+* A) (hr : ι.fieldRange = k.map α) : ∃ e : k ≃+* Φ, ∀ c, ι (e c) = α c := by
  let g : k →+* ι.fieldRange :=
    (α.comp k.subtype).codRestrict ι.fieldRange (fun c => hr ▸ Subfield.mem_map.2 ⟨c, c.2, rfl⟩)
  have hg : Function.Bijective g := by
    refine ⟨fun x y hxy => Subtype.ext (α.injective (congr_arg Subtype.val hxy)), fun y => ?_⟩
    have hy : (y : A) ∈ k.map α := hr ▸ y.2
    obtain ⟨x, hx, e⟩ := Subfield.mem_map.1 hy
    exact ⟨⟨x, hx⟩, Subtype.ext e⟩
  exact ⟨(RingEquiv.ofBijective g hg).trans ι.rangeRestrictFieldEquiv.symm, fun c =>
    RingHom.rangeRestrictFieldEquiv_apply_symm_apply ι (g c)⟩

end GenericFibreModelTransport

end GroundTheory.Heights₂.Heights
