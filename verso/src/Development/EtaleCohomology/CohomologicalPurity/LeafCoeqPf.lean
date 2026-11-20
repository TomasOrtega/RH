import Development.EtaleCohomology.CohomologicalPurity.LeafHensCutDef

noncomputable section
open scoped TensorProduct

namespace LateralTheory.CohomologicalPurity.Hz

/- English proof (translation)
Set `` to `φ.toAlgebra`. Set `` to `φ'.toAlgebra`. Establish `: Algebra.Etale A S` using `hφ.etale`. Set `u' : S →ₐ[A] S'` to `{ u with commutes' := fun a => RingHom.congr_fun hu a }`. Set `v' : S →ₐ[A] S'` to `{ v with commutes' := fun a => RingHom.congr_fun hv a }`.

Take `⟨t, ht1, ht2⟩` from `(Algebra.FormallyUnramified.iff_exists_tensorProduct (R := A) (S := S)).1 inferInstance`. Use `⟨Algebra.TensorProduct.productMap u' v' t, fun s => ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (Algebra.TensorProduct.productMap u' v') (ht1 s)`. Simplify `h` using `[map_mul, map_sub, Algebra.TensorProduct.productMap_apply_tmul, u', v']`. Establish `hmem : ∀ x ∈ I.map φ, u x ∈ I.map φ' ∧ v x ∈ I.map φ'` using `fun x hx => by`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `Ideal.mem_map_of_mem u hx` as an intermediate fact. Rewrite `this` using `[Ideal.map_map, hu]`. Then use the resulting hypothesis. Use `Ideal.mem_map_of_mem v hx` as an intermediate fact. Rewrite `this` using `[Ideal.map_map, hv]`. Then use the resulting hypothesis.

Set `q` to `Ideal.Quotient.mkₐ A (I.map φ')`. Establish `hqv : q.comp v' = q.comp u'`. Use extensionality with `s`. Take `⟨a, ha⟩` from `hφ.surj s`. Establish `e1 : v s - u s = v (s - φ a) - u (s - φ a)`.

Establish `h1 : v (φ a) = u (φ a)` using `(RingHom.congr_fun hv a).trans (RingHom.congr_fun hu a).symm`. Rewrite using `[map_sub, map_sub, h1]`. Expand and normalize the polynomial expressions, which then agree. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ (v s) = Ideal.Quotient.mk _ (u s)`. Rewrite using `[Ideal.Quotient.eq, e1]`.

Conclude with `Ideal.sub_mem _ (hmem _ ha).2 (hmem _ ha).1`. Establish `hprod : q.comp (Algebra.TensorProduct.productMap u' v') = q.comp (u'.comp (Algebra.TensorProduct.lmul' A))`. Apply `Algebra.TensorProduct.ext'` to reduce the goal to its premises. Introduce `a b`. Establish `hb` using `AlgHom.congr_fun hqv b`.

Simplify using `only [AlgHom.comp_apply, Algebra.TensorProduct.productMap_apply_tmul, map_mul, Algebra.TensorProduct.lmul'_apply_tmul] at hb ⊢`. Rewrite using `[hb]`. Establish `h` using `AlgHom.congr_fun hprod t`. Simplify using `only [AlgHom.comp_apply] at h`. Rewrite `h` using `[ht2, map_one]`.

Rewrite using `[← Ideal.Quotient.eq]`. Simplify `h` using `[q]`.
-/
theorem coeq_elem {A S S' : Type} [CommRing A] [CommRing S] [CommRing S'] (φ : A →+* S) (φ' : A →+* S')
    (I : Ideal A) (u v : S →+* S') (hφ : Good φ I) (hu : u.comp φ = φ') (hv : v.comp φ = φ') :
    ∃ e : S', (∀ s, (v s - u s) * e = 0) ∧ e - 1 ∈ I.map φ' := by
  let := φ.toAlgebra
  let := φ'.toAlgebra
  have : Algebra.Etale A S := hφ.etale
  let u' : S →ₐ[A] S' := { u with commutes' := fun a => RingHom.congr_fun hu a }
  let v' : S →ₐ[A] S' := { v with commutes' := fun a => RingHom.congr_fun hv a }
  obtain ⟨t, ht1, ht2⟩ :=
    (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := A) (S := S)).1 inferInstance
  refine ⟨Algebra.TensorProduct.productMap u' v' t, fun s => ?_, ?_⟩
  · have h := congrArg (Algebra.TensorProduct.productMap u' v') (ht1 s)
    simpa [map_mul, map_sub, Algebra.TensorProduct.productMap_apply_tmul, u', v'] using h
  · have hmem : ∀ x ∈ I.map φ, u x ∈ I.map φ' ∧ v x ∈ I.map φ' := fun x hx => by
      refine ⟨?_, ?_⟩
      · have := Ideal.mem_map_of_mem u hx
        rwa [Ideal.map_map, hu] at this
      · have := Ideal.mem_map_of_mem v hx
        rwa [Ideal.map_map, hv] at this
    let q := Ideal.Quotient.mkₐ A (I.map φ')
    have hqv : q.comp v' = q.comp u' := by
      ext s
      obtain ⟨a, ha⟩ := hφ.surj s
      have e1 : v s - u s = v (s - φ a) - u (s - φ a) := by
        have h1 : v (φ a) = u (φ a) := (RingHom.congr_fun hv a).trans (RingHom.congr_fun hu a).symm
        rw [map_sub, map_sub, h1]; ring
      change Ideal.Quotient.mk _ (v s) = Ideal.Quotient.mk _ (u s)
      rw [Ideal.Quotient.eq, e1]
      exact Ideal.sub_mem _ (hmem _ ha).2 (hmem _ ha).1
    have hprod : q.comp (Algebra.TensorProduct.productMap u' v') = q.comp (u'.comp (Algebra.TensorProduct.lmul' A)) := by
      apply Algebra.TensorProduct.ext'
      intro a b
      have hb := AlgHom.congr_fun hqv b
      simp only [AlgHom.comp_apply, Algebra.TensorProduct.productMap_apply_tmul, map_mul,
        Algebra.TensorProduct.lmul'_apply_tmul] at hb ⊢
      rw [hb]
    have h := AlgHom.congr_fun hprod t
    simp only [AlgHom.comp_apply] at h
    rw [ht2, map_one] at h
    rw [← Ideal.Quotient.eq]
    simpa [q] using h

/- English proof (translation)
Introduce `A S S' _ _ _ φ φ' I u v hφ hφ' hu hv`. Take `⟨e, he1, he2⟩` from `coeq_elem φ φ' I u v hφ hu hv`. Take `⟨T, _, ψ, hg, hunit⟩` from `hInv S' (I.map φ') (e - 1) he2`. Rewrite `hunit` using `[add_sub_cancel]`. Use `⟨T, inferInstance, ψ, RingHom.ext fun s => ?_, hComp.2 A S' T φ' ψ I hφ' hg⟩` and prove the remaining obligations.

Establish `h` using `congrArg ψ (he1 s)`. Rewrite `h` using `[map_mul, map_zero, hunit.mul_left_eq_zero, map_sub, sub_eq_zero]`. Conclude with `h.symm`.
-/
theorem LeafCoeq_of (hInv : LeafInv) (hComp : LeafComp) : LeafCoeq := by
  intro A S S' _ _ _ φ φ' I u v hφ hφ' hu hv
  obtain ⟨e, he1, he2⟩ := coeq_elem φ φ' I u v hφ hu hv
  obtain ⟨T, _, ψ, hg, hunit⟩ := hInv S' (I.map φ') (e - 1) he2
  rw [add_sub_cancel] at hunit
  refine ⟨T, inferInstance, ψ, RingHom.ext fun s => ?_, hComp.2 A S' T φ' ψ I hφ' hg⟩
  have h := congrArg ψ (he1 s)
  rw [map_mul, map_zero, hunit.mul_left_eq_zero, map_sub, sub_eq_zero] at h
  exact h.symm

end LateralTheory.CohomologicalPurity.Hz
