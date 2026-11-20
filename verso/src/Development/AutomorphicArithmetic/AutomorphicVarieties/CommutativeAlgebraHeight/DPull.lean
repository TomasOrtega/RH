import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MapSurj

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section
variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) {E' : Type} [Ring E']
  [Algebra A E'] (f : E' →ₐ[A] E)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem pull_D (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] E') :
    (D.pull f).D S y = D.D S (Algebra.TensorProduct.map (AlgHom.id S S) f y) := rfl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem map_gen {ι : Type} [Fintype ι] (x : ι → E') :
    Algebra.TensorProduct.map (AlgHom.id (MvPolynomial ι A) (MvPolynomial ι A)) f (Det.gen (A := A) x) =
      Det.gen (A := A) (fun a => f (x a)) := by
  simp [Det.gen, map_sum]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Simplify using the standard rewrite rules. Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.
-/
private theorem pull_chiS (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] E') :
    (D.pull f).chiS S y = D.chiS S (Algebra.TensorProduct.map (AlgHom.id S S) f y) := by
  unfold Det.chiS
  rw [pull_D]
  congr 1
  rw [map_sub]
  congr 1
  · simp
  · induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add a b ha hb => simp only [map_add, ha, hb]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.
-/
private theorem map_coeff {ι : Type} (α : ι →₀ ℕ) (y : MvPolynomial ι A ⊗[A] E') :
    f (TensorProduct.lid A E' ((MvPolynomial.lcoeff A α).rTensor E' y)) =
      TensorProduct.lid A E ((MvPolynomial.lcoeff A α).rTensor E
        (Algebra.TensorProduct.map (AlgHom.id (MvPolynomial ι A) (MvPolynomial ι A)) f y)) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add a b ha hb => simp only [map_add, ha, hb]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
private theorem map_chElt {k : ℕ} (x : Fin k → E') (α : Fin k →₀ ℕ) :
    f ((D.pull f).chElt x α) = D.chElt (fun a => f (x a)) α := by
  unfold Det.chElt
  rw [map_coeff, pull_chiS, ← Polynomial.aeval_algHom_apply, map_gen]

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
private theorem map_surj (hf : Function.Surjective f) (S : Type) [CommRing S] [Algebra A S] :
    Function.Surjective (Algebra.TensorProduct.map (AlgHom.id S S) f) :=
  by apply _root_.UpperTheory.Reformulated.B.Qk2.map_surj <;> assumption

end

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Proceed by induction.

Treat this case separately. Extract witnesses or component facts from the available result. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. Treat this case separately. Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Replace the relevant objects with their definitions.

Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Treat this case separately. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Treat this case separately.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Treat this case separately. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem UpperTheory.V.CA.d_pull :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) {E' : Type} [Ring E'] [Algebra A E'] (f : E' →ₐ[A] E), (∀ x, (D.pull f).chi x = D.chi (f x)) ∧ (∀ x, f x ∈ D.ker → x ∈ (D.pull f).ker) ∧ (∀ x ∈ (D.pull f).CH, f x ∈ D.CH) ∧ (Function.Surjective f → (∀ x, x ∈ (D.pull f).ker → f x ∈ D.ker) ∧ ∀ y ∈ D.CH, ∃ x ∈ (D.pull f).CH, f x = y) := by
  intro n A E _ _ _ D E' _ _ f
  refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_, fun hf => ⟨fun x hx => ?_, fun y hy => ?_⟩⟩
  · unfold Det.chi
    rw [pull_D]
    simp
  · rw [Det.mem_ker] at hx ⊢
    intro S _ _ y u v
    rw [pull_D, pull_D, map_add, map_mul, map_mul, Algebra.TensorProduct.map_tmul, map_one]
    exact hx S _ _ _
  · unfold Det.CH at hx
    induction hx using TwoSidedIdeal.span_induction with
    | mem x h =>
      obtain ⟨k, z, α, rfl⟩ := h
      exact TwoSidedIdeal.subset_span ⟨k, _, α, map_chElt D f z α⟩
    | zero => rw [map_zero]; exact D.CH.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact D.CH.add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact D.CH.neg_mem hx
    | left_absorb a x _ hx => rw [map_mul]; exact D.CH.mul_mem_left _ _ hx
    | right_absorb b x _ hx => rw [map_mul]; exact D.CH.mul_mem_right _ _ hx
  · rw [Det.mem_ker] at hx ⊢
    intro S _ _ y u v
    obtain ⟨y, rfl⟩ := map_surj f hf S y
    obtain ⟨u, rfl⟩ := map_surj f hf S u
    obtain ⟨v, rfl⟩ := map_surj f hf S v
    have := hx S y u v
    rwa [pull_D, pull_D, map_add, map_mul, map_mul, Algebra.TensorProduct.map_tmul, map_one] at this
  · unfold Det.CH at hy
    induction hy using TwoSidedIdeal.span_induction with
    | mem y h =>
      obtain ⟨k, z, α, rfl⟩ := h
      choose w hw using fun a => hf (z a)
      refine ⟨(D.pull f).chElt w α, TwoSidedIdeal.subset_span ⟨k, w, α, rfl⟩, ?_⟩
      rw [map_chElt]
      simp only [hw]
    | zero => exact ⟨0, (D.pull f).CH.zero_mem, map_zero f⟩
    | add x y _ _ hx hy =>
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      exact ⟨x' + y', (D.pull f).CH.add_mem hx' hy', map_add f _ _⟩
    | neg x _ hx =>
      obtain ⟨x', hx', rfl⟩ := hx
      exact ⟨-x', (D.pull f).CH.neg_mem hx', map_neg f _⟩
    | left_absorb a x _ hx =>
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨a, rfl⟩ := hf a
      exact ⟨a * x', (D.pull f).CH.mul_mem_left _ _ hx', map_mul f _ _⟩
    | right_absorb a x _ hx =>
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨a, rfl⟩ := hf a
      exact ⟨x' * a, (D.pull f).CH.mul_mem_right _ _ hx', map_mul f _ _⟩
