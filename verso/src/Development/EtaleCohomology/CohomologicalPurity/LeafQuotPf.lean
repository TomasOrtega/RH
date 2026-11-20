import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut

open CategoryTheory Limits

namespace LateralTheory.CohomologicalPurity.TubeCut

/- English proof (translation)
Introduce `A B _ _ φ I h`. Take `⟨J, _, _, D, s, t, ⟨hc⟩, hj⟩` from `h`. Establish `hst : ∀ j (a : A), (t.app j).hom ((s.app j).hom a) = φ a` using `fun j a => congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of B => f.hom a) (hj j).2`. Establish `sn : ∀ {j k : J} (f : j ⟶ k), (D.map f).hom.comp (s.app j).hom = (s.app k).hom`. Introduce `j k f`.

Use `s.naturality f` as an intermediate fact. Simplify using `only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at this`. Rewrite using `[this]`. Both sides reduce to the same expression. Establish `tn : ∀ {j k : J} (f : j ⟶ k) (y : D.obj j), (t.app k).hom ((D.map f).hom y) = (t.app j).hom y`.

Introduce `j k f y`. Use `t.naturality f` as an intermediate fact. Simplify using `only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this`. Conclude with `congrArg (fun g : D.obj j ⟶ CommRingCat.of B => g.hom y) this`. Establish `mv : ∀ {j k : J} (f : j ⟶ k) (y : D.obj j), y ∈ I.map (s.app j).hom → (D.map f).hom y ∈ I.map (s.app k).hom`.

Introduce `j k f y hy`. Use `Ideal.mem_map_of_mem (D.map f).hom hy` as an intermediate fact. Rewrite `this` using `[Ideal.map_map, sn f]`. Then use the resulting hypothesis. Establish `rep : ∀ b : B, ∃ j, ∃ y : D.obj j, (t.app j).hom y = b` using `fun b => Concrete.isColimit_exists_rep D hc b`. Establish `mem : ∀ x ∈ I.map φ, ∃ j, ∃ y : D.obj j, y ∈ I.map (s.app j).hom ∧ (t.app j).hom y = x`.

Introduce `x hx`. Take `⟨j0⟩` from `IsFiltered.nonempty (C := J)`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x h`. Take `⟨a, ha, rfl⟩` from `h`.

Conclude with `⟨j0, (s.app j0).hom a, Ideal.mem_map_of_mem _ ha, hst j0 a⟩`. Consider the case `zero => exact ⟨j0, 0, zero_mem _, map_zero _⟩`. Consider the case `add x x' _ _ h h'`. Take `⟨j, y, hy, rfl⟩` from `h`. Take `⟨k, y', hy', rfl⟩` from `h'`.

Use `⟨IsFiltered.max j k, (D.map (IsFiltered.leftToMax j k)).hom y + (D.map (IsFiltered.rightToMax j k)).hom y', add_mem (mv _ _ hy) (mv _ _ hy'), ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, tn, tn]`. Consider the case `smul b x _ h`. Take `⟨j, y, hy, rfl⟩` from `h`. Take `⟨k, c, rfl⟩` from `rep b`.

Use `⟨IsFiltered.max k j, (D.map (IsFiltered.leftToMax k j)).hom c * (D.map (IsFiltered.rightToMax k j)).hom y, Ideal.mul_mem_left _ _ (mv _ _ hy), ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, tn, tn]`. Both sides reduce to the same expression. Prove the components needed by the constructor for the conclusion. Introduce `u v huv`.

Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective u`. Take `⟨a', rfl⟩` from `Ideal.Quotient.mk_surjective v`. Rewrite `huv` using `[Ideal.quotientMap_mk, Ideal.quotientMap_mk, Ideal.Quotient.eq]`. Rewrite using `[Ideal.Quotient.eq]`. Rewrite `huv` using `[← map_sub]`.

Take `⟨j, y, hy, hy'⟩` from `mem _ huv`. Rewrite `hy'` using `[← hst j]`. Take `⟨k, f, g, hfg⟩` from `Concrete.isColimit_exists_of_rep_eq D hc y ((s.app j).hom (a - a')) hy'`. Establish `h1 : (s.app k).hom (a - a') ∈ I.map (s.app k).hom`. Establish `e : (D.map g).hom ((s.app j).hom (a - a')) = (D.map f).hom y` using `hfg.symm`.

Establish `e2 : ((D.map g).hom.comp (s.app j).hom) (a - a') = (s.app k).hom (a - a')` using `congrArg (fun r : A →+* D.obj k => r (a - a')) (sn g)`. Rewrite using `[← e2]`. Use `mv f y hy` as an intermediate fact. Rewrite `this` using `[← e]`. Conclude with `this`.

Establish `h2` using `(hj k).1.2.1 (a₁ := Ideal.Quotient.mk I (a - a')) (a₂ := 0) (by`. Rewrite using `[Ideal.quotientMap_mk, map_zero, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `h1)`. Conclude with `(Ideal.Quotient.eq_zero_iff_mem).1 h2`. Introduce `w`.

Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective w`. Take `⟨j, y, rfl⟩` from `rep b`. Take `⟨u, hu⟩` from `(hj j).1.2.2 (Ideal.Quotient.mk _ y)`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective u`. Use `⟨Ideal.Quotient.mk I a, ?_⟩` and prove the remaining obligations.

Rewrite `hu` using `[Ideal.quotientMap_mk, Ideal.Quotient.eq]`. Rewrite using `[Ideal.quotientMap_mk, Ideal.Quotient.eq]`. Establish `hc' : (t.app j).hom.comp (s.app j).hom = φ` using `congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of B => f.hom) (hj j).2`. Use `Ideal.mem_map_of_mem (t.app j).hom hu` as an intermediate fact. Rewrite `this` using `[Ideal.map_map, hc', map_sub, hst]`.

Conclude with `this`.
-/
theorem LeafQuot_of : LeafQuot := by
  intro A B _ _ φ I h
  obtain ⟨J, _, _, D, s, t, ⟨hc⟩, hj⟩ := h
  have hst : ∀ j (a : A), (t.app j).hom ((s.app j).hom a) = φ a := fun j a =>
    congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of B => f.hom a) (hj j).2
  have sn : ∀ {j k : J} (f : j ⟶ k), (D.map f).hom.comp (s.app j).hom = (s.app k).hom := by
    intro j k f
    have := s.naturality f
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at this
    rw [this]; rfl
  have tn : ∀ {j k : J} (f : j ⟶ k) (y : D.obj j), (t.app k).hom ((D.map f).hom y) = (t.app j).hom y := by
    intro j k f y
    have := t.naturality f
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
    exact congrArg (fun g : D.obj j ⟶ CommRingCat.of B => g.hom y) this
  have mv : ∀ {j k : J} (f : j ⟶ k) (y : D.obj j), y ∈ I.map (s.app j).hom →
      (D.map f).hom y ∈ I.map (s.app k).hom := by
    intro j k f y hy
    have := Ideal.mem_map_of_mem (D.map f).hom hy
    rwa [Ideal.map_map, sn f] at this
  have rep : ∀ b : B, ∃ j, ∃ y : D.obj j, (t.app j).hom y = b := fun b =>
    Concrete.isColimit_exists_rep D hc b
  have mem : ∀ x ∈ I.map φ, ∃ j, ∃ y : D.obj j, y ∈ I.map (s.app j).hom ∧ (t.app j).hom y = x := by
    intro x hx
    obtain ⟨j0⟩ := IsFiltered.nonempty (C := J)
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨a, ha, rfl⟩ := h
      exact ⟨j0, (s.app j0).hom a, Ideal.mem_map_of_mem _ ha, hst j0 a⟩
    | zero => exact ⟨j0, 0, zero_mem _, map_zero _⟩
    | add x x' _ _ h h' =>
      obtain ⟨j, y, hy, rfl⟩ := h
      obtain ⟨k, y', hy', rfl⟩ := h'
      refine ⟨IsFiltered.max j k, (D.map (IsFiltered.leftToMax j k)).hom y + (D.map (IsFiltered.rightToMax j k)).hom y',
        add_mem (mv _ _ hy) (mv _ _ hy'), ?_⟩
      rw [map_add, tn, tn]
    | smul b x _ h =>
      obtain ⟨j, y, hy, rfl⟩ := h
      obtain ⟨k, c, rfl⟩ := rep b
      refine ⟨IsFiltered.max k j, (D.map (IsFiltered.leftToMax k j)).hom c * (D.map (IsFiltered.rightToMax k j)).hom y,
        Ideal.mul_mem_left _ _ (mv _ _ hy), ?_⟩
      rw [map_mul, tn, tn]; rfl
  constructor
  · intro u v huv
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective v
    rw [Ideal.quotientMap_mk, Ideal.quotientMap_mk, Ideal.Quotient.eq] at huv
    rw [Ideal.Quotient.eq]
    rw [← map_sub] at huv
    obtain ⟨j, y, hy, hy'⟩ := mem _ huv
    rw [← hst j] at hy'
    obtain ⟨k, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq D hc y ((s.app j).hom (a - a')) hy'
    have h1 : (s.app k).hom (a - a') ∈ I.map (s.app k).hom := by
      have e : (D.map g).hom ((s.app j).hom (a - a')) = (D.map f).hom y := hfg.symm
      have e2 : ((D.map g).hom.comp (s.app j).hom) (a - a') = (s.app k).hom (a - a') :=
        congrArg (fun r : A →+* D.obj k => r (a - a')) (sn g)
      rw [← e2]
      have := mv f y hy
      rw [← e] at this
      exact this
    have h2 := (hj k).1.2.1 (a₁ := Ideal.Quotient.mk I (a - a')) (a₂ := 0) (by
      rw [Ideal.quotientMap_mk, map_zero, Ideal.Quotient.eq_zero_iff_mem]; exact h1)
    exact (Ideal.Quotient.eq_zero_iff_mem).1 h2
  · intro w
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨j, y, rfl⟩ := rep b
    obtain ⟨u, hu⟩ := (hj j).1.2.2 (Ideal.Quotient.mk _ y)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
    refine ⟨Ideal.Quotient.mk I a, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hu
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
    have hc' : (t.app j).hom.comp (s.app j).hom = φ :=
      congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of B => f.hom) (hj j).2
    have := Ideal.mem_map_of_mem (t.app j).hom hu
    rw [Ideal.map_map, hc', map_sub, hst] at this
    exact this

end LateralTheory.CohomologicalPurity.TubeCut
