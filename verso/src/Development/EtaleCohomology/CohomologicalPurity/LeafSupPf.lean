import Development.EtaleCohomology.CohomologicalPurity.LeafHensCutDef

noncomputable section
open TensorProduct

namespace LateralTheory.CohomologicalPurity.Hz

section Sup
variable {A S S' : Type} [CommRing A] [CommRing S] [CommRing S'] [Algebra A S] [Algebra A S'] (I : Ideal A)

/- English proof (translation)
Rewrite `*` using `[RingHom.etale_algebraMap]`. Conclude with `Algebra.Etale.comp A S (S ⊗[A] S')`.
-/
theorem sup_etale (h : (algebraMap A S).Etale) (h' : (algebraMap A S').Etale) :
    (algebraMap A (S ⊗[A] S')).Etale := by
  rw [RingHom.etale_algebraMap] at *
  exact Algebra.Etale.comp A S (S ⊗[A] S')

/- English proof (translation)
Take `⟨r, hr⟩` from `hr`. Take `⟨r', hr'⟩` from `hr'`. Establish `c1 : ∀ a, r (algebraMap A S a) = algebraMap A (A ⧸ I) a` using `fun a => by`. Rewrite using `[Ideal.Quotient.algebraMap_eq]`. Conclude with `RingHom.congr_fun hr a`.

Establish `c2 : ∀ a, r' (algebraMap A S' a) = algebraMap A (A ⧸ I) a` using `fun a => by`. Rewrite using `[Ideal.Quotient.algebraMap_eq]`. Conclude with `RingHom.congr_fun hr' a`. Set `f : S →ₐ[A] A ⧸ I` to `{ r with commutes' := c1 }`. Set `g : S' →ₐ[A] A ⧸ I` to `{ r' with commutes' := c2 }`.

Use `⟨(Algebra.TensorProduct.productMap f g).toRingHom, ?_⟩` and prove the remaining obligations. Use extensionality with `a`. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes, Ideal.Quotient.algebraMap_eq]`.
-/
theorem sup_retr (hr : ∃ r : S →+* A ⧸ I, r.comp (algebraMap A S) = Ideal.Quotient.mk I)
    (hr' : ∃ r : S' →+* A ⧸ I, r.comp (algebraMap A S') = Ideal.Quotient.mk I) :
    ∃ r : S ⊗[A] S' →+* A ⧸ I, r.comp (algebraMap A (S ⊗[A] S')) = Ideal.Quotient.mk I := by
  obtain ⟨r, hr⟩ := hr
  obtain ⟨r', hr'⟩ := hr'
  have c1 : ∀ a, r (algebraMap A S a) = algebraMap A (A ⧸ I) a := fun a => by
    rw [Ideal.Quotient.algebraMap_eq]; exact RingHom.congr_fun hr a
  have c2 : ∀ a, r' (algebraMap A S' a) = algebraMap A (A ⧸ I) a := fun a => by
    rw [Ideal.Quotient.algebraMap_eq]; exact RingHom.congr_fun hr' a
  let f : S →ₐ[A] A ⧸ I := { r with commutes' := c1 }
  let g : S' →ₐ[A] A ⧸ I := { r' with commutes' := c2 }
  refine ⟨(Algebra.TensorProduct.productMap f g).toRingHom, ?_⟩
  ext a
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
    Ideal.Quotient.algebraMap_eq]

/- English proof (translation)
Establish `e : (f : S →+* B).comp (algebraMap A S) = algebraMap A B` using `f.comp_algebraMap`. Establish `h2` using `Ideal.mem_map_of_mem (f : S →+* B) h`. Rewrite `h2` using `[Ideal.map_map, e, map_sub]`. Simplify using `using h2`.
-/
theorem mem_map_of_algHom {B : Type} [CommRing B] [Algebra A B] (f : S →ₐ[A] B) {s : S} {a : A}
    (h : s - algebraMap A S a ∈ I.map (algebraMap A S)) : f s - algebraMap A B a ∈ I.map (algebraMap A B) := by
  have e : (f : S →+* B).comp (algebraMap A S) = algebraMap A B := f.comp_algebraMap
  have h2 := Ideal.mem_map_of_mem (f : S →+* B) h
  rw [Ideal.map_map, e, map_sub] at h2
  simpa using h2

/- English proof (translation)
Use `set J := I.map (algebraMap A (S ⊗[A] S'))`. Set `R : Subring ((S ⊗[A] S') ⧸ J)` to `((Ideal.Quotient.mk J).comp (algebraMap A (S ⊗[A] S'))).range`. Establish `key : ∀ {B : Type} [CommRing B] [Algebra A B] (_ : ∀ s : B, ∃ a : A, s - algebraMap A B a ∈ I.map (algebraMap A B)) (f : B →ₐ[A] S ⊗[A] S') (s : B), Ideal.Quotient.mk J (f s) ∈ R`. Introduce `B _ _ hB f s`. Take `⟨a, ha⟩` from `hB s`.

Use `⟨a, ?_⟩` and prove the remaining obligations. Use `show Ideal.Quotient.mk J (algebraMap A _ a) = Ideal.Quotient.mk J (f s)`. Conclude with `(Ideal.Quotient.eq.2 (mem_map_of_algHom I f ha)).symm`. It suffices to establish `Ideal.Quotient.mk J t ∈ R by`. Take `⟨a, ha⟩` from `this`.

Conclude with `⟨a, Ideal.Quotient.eq.1 ha.symm⟩`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero]`. Conclude with `R.zero_mem`. Consider the case `tmul s s'`.

Establish `e : s ⊗ₜ[A] s' = Algebra.TensorProduct.includeLeft (S` using `A) s * Algebra.TensorProduct.includeRight s' := by`. Simplify using the standard rewrite rules. Rewrite using `[e, map_mul]`. Conclude with `R.mul_mem (key hs _ s) (key hs' _ s')`. Consider the case `add x y hx hy => rw [map_add]`.

Conclude with `R.add_mem hx hy`.
-/
theorem sup_surj (hs : ∀ s : S, ∃ a : A, s - algebraMap A S a ∈ I.map (algebraMap A S))
    (hs' : ∀ s : S', ∃ a : A, s - algebraMap A S' a ∈ I.map (algebraMap A S')) (t : S ⊗[A] S') :
    ∃ a : A, t - algebraMap A (S ⊗[A] S') a ∈ I.map (algebraMap A (S ⊗[A] S')) := by
  set J := I.map (algebraMap A (S ⊗[A] S'))
  let R : Subring ((S ⊗[A] S') ⧸ J) := ((Ideal.Quotient.mk J).comp (algebraMap A (S ⊗[A] S'))).range
  have key : ∀ {B : Type} [CommRing B] [Algebra A B]
      (_ : ∀ s : B, ∃ a : A, s - algebraMap A B a ∈ I.map (algebraMap A B)) (f : B →ₐ[A] S ⊗[A] S') (s : B),
      Ideal.Quotient.mk J (f s) ∈ R := by
    intro B _ _ hB f s
    obtain ⟨a, ha⟩ := hB s
    refine ⟨a, ?_⟩
    show Ideal.Quotient.mk J (algebraMap A _ a) = Ideal.Quotient.mk J (f s)
    exact (Ideal.Quotient.eq.2 (mem_map_of_algHom I f ha)).symm
  suffices Ideal.Quotient.mk J t ∈ R by
    obtain ⟨a, ha⟩ := this
    exact ⟨a, Ideal.Quotient.eq.1 ha.symm⟩
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact R.zero_mem
  | tmul s s' =>
    have e : s ⊗ₜ[A] s' = Algebra.TensorProduct.includeLeft (S := A) s * Algebra.TensorProduct.includeRight s' := by
      simp
    rw [e, map_mul]
    exact R.mul_mem (key hs _ s) (key hs' _ s')
  | add x y hx hy => rw [map_add]; exact R.add_mem hx hy

/- English proof (translation)
Introduce `B _ J hB ψ hIJ`. Set `_ : Algebra A B` to `ψ.toAlgebra`. Take `⟨χ, hχ, -⟩` from `hu B J hB ψ hIJ`. Take `⟨χ', hχ', -⟩` from `hu' B J hB ψ hIJ`. Set `f : S →ₐ[A] B` to `{ χ with commutes' := fun a => RingHom.congr_fun hχ a }`.

Set `g : S' →ₐ[A] B` to `{ χ' with commutes' := fun a => RingHom.congr_fun hχ' a }`. Use `⟨(Algebra.TensorProduct.productMap f g).toRingHom, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `a`. Conclude with `(Algebra.TensorProduct.productMap f g).commutes a`. Introduce `χ₁ h₁`.

Establish `hl : χ₁.comp (Algebra.TensorProduct.includeLeft (R` using `A) (S := A) (A := S) (B := S') : S →ₐ[A] S ⊗[A] S').toRingHom = χ := by`. Use `(hu B J hB ψ hIJ).unique ?_ hχ` and prove the remaining obligations. Rewrite using `[RingHom.comp_assoc, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap, h₁]`. Establish `hr : χ₁.comp (Algebra.TensorProduct.includeRight (R` using `A) (A := S) (B := S') : S' →ₐ[A] S ⊗[A] S').toRingHom = χ' := by`. Use `(hu' B J hB ψ hIJ).unique ?_ hχ'` and prove the remaining obligations.

Rewrite using `[RingHom.comp_assoc, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap, h₁]`. Use `RingHom.ext fun t => ?_` and prove the remaining obligations. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul s s'`.

Establish `e : s ⊗ₜ[A] s' = Algebra.TensorProduct.includeLeft (S` using `A) s * Algebra.TensorProduct.includeRight s' := by`. Simplify using the standard rewrite rules. Rewrite using `[e, map_mul, map_mul]`. Establish `a1` using `RingHom.congr_fun hl s`. Establish `a2` using `RingHom.congr_fun hr s'`.

Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at a1 a2`. Rewrite using `[a1, a2]`. Simplify using `[f, g]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem sup_univ (hu : Univ (algebraMap A S) I) (hu' : Univ (algebraMap A S') I) :
    Univ (algebraMap A (S ⊗[A] S')) I := by
  intro B _ J hB ψ hIJ
  let _ : Algebra A B := ψ.toAlgebra
  obtain ⟨χ, hχ, -⟩ := hu B J hB ψ hIJ
  obtain ⟨χ', hχ', -⟩ := hu' B J hB ψ hIJ
  let f : S →ₐ[A] B := { χ with commutes' := fun a => RingHom.congr_fun hχ a }
  let g : S' →ₐ[A] B := { χ' with commutes' := fun a => RingHom.congr_fun hχ' a }
  refine ⟨(Algebra.TensorProduct.productMap f g).toRingHom, ?_, ?_⟩
  · ext a
    exact (Algebra.TensorProduct.productMap f g).commutes a
  · intro χ₁ h₁
    have hl : χ₁.comp (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := S) (B := S') : S →ₐ[A] S ⊗[A] S').toRingHom = χ := by
      refine (hu B J hB ψ hIJ).unique ?_ hχ
      rw [RingHom.comp_assoc, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap, h₁]
    have hr : χ₁.comp (Algebra.TensorProduct.includeRight (R := A) (A := S) (B := S') : S' →ₐ[A] S ⊗[A] S').toRingHom = χ' := by
      refine (hu' B J hB ψ hIJ).unique ?_ hχ'
      rw [RingHom.comp_assoc, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap, h₁]
    refine RingHom.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s s' =>
      have e : s ⊗ₜ[A] s' = Algebra.TensorProduct.includeLeft (S := A) s * Algebra.TensorProduct.includeRight s' := by
        simp
      rw [e, map_mul, map_mul]
      have a1 := RingHom.congr_fun hl s
      have a2 := RingHom.congr_fun hr s'
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at a1 a2
      rw [a1, a2]
      simp [f, g]
    | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
Assemble the required witnesses or components as `⟨sup_etale h.etale h'.etale, sup_retr I h.retr h'.retr, sup_surj I h.surj h'.surj, sup_univ I h.univ h'.univ⟩`.
-/
theorem sup_good (h : Good (algebraMap A S) I) (h' : Good (algebraMap A S') I) :
    Good (algebraMap A (S ⊗[A] S')) I :=
  ⟨sup_etale h.etale h'.etale, sup_retr I h.retr h'.retr, sup_surj I h.surj h'.surj, sup_univ I h.univ h'.univ⟩

end Sup

/- English proof (translation)
Introduce `A S S' _ _ _ φ φ' I h h'`. Set `_ : Algebra A S` to `φ.toAlgebra`. Set `_ : Algebra A S'` to `φ'.toAlgebra`. Use `⟨S ⊗[A] S', inferInstance, (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := S) (B := S') : S →ₐ[A] S ⊗[A] S').toRingHom, (Algebra.TensorProduct.includeRight (R := A) (A := S) (B := S') : S' →ₐ[A] S ⊗[A] S').toRingHom, ?_, ?_⟩` and prove the remaining obligations. Conclude with `RingHom.ext fun a => ((Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := S) (B := S')).commutes a).trans ((Algebra.TensorProduct.includeRight (R := A) (A := S) (B := S')).commutes a).symm`.

Establish `e : (Algebra.TensorProduct.includeLeft (R` using `A) (S := A) (A := S) (B := S') : S →ₐ[A] S ⊗[A] S').toRingHom.comp φ = algebraMap A (S ⊗[A] S') := RingHom.ext fun a => (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := S) (B := S')).commutes a`. Rewrite using `[e]`. Conclude with `sup_good I h h'`.
-/
theorem LeafSup_of : LeafSup := by
  intro A S S' _ _ _ φ φ' I h h'
  let _ : Algebra A S := φ.toAlgebra
  let _ : Algebra A S' := φ'.toAlgebra
  refine ⟨S ⊗[A] S', inferInstance, (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := S) (B := S') : S →ₐ[A] S ⊗[A] S').toRingHom,
    (Algebra.TensorProduct.includeRight (R := A) (A := S) (B := S') : S' →ₐ[A] S ⊗[A] S').toRingHom, ?_, ?_⟩
  · exact RingHom.ext fun a => ((Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := S) (B := S')).commutes a).trans
      ((Algebra.TensorProduct.includeRight (R := A) (A := S) (B := S')).commutes a).symm
  · have e : (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := S) (B := S') : S →ₐ[A] S ⊗[A] S').toRingHom.comp φ =
        algebraMap A (S ⊗[A] S') :=
      RingHom.ext fun a => (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := S) (B := S')).commutes a
    rw [e]
    exact sup_good I h h'

end LateralTheory.CohomologicalPurity.Hz
