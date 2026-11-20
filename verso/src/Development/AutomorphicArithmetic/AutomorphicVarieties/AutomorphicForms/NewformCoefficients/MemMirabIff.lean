import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt

open UpperTheory.V.Sd in
/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules.
-/
private theorem mem_mirab_iff {R : Type} [CommRing R] (g : GL (Fin 2) R) : g ∈ mirab R ↔ g 1 0 = 0 ∧ g 1 1 = 1 := by
  change Matrix.vecMul ![0, 1] (g : Matrix (Fin 2) (Fin 2) R) = ![0, 1] ↔ _
  simp [funext_iff, Fin.forall_fin_two, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

open NumberField GlobalTheory.CuspRep UpperTheory.V.Af UpperTheory.V.Sd in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Af.Nf.memK :
    UpperTheory.V.Af.Nf.MemK := by
  intro M g
  constructor
  · rintro ⟨k, hk, rfl⟩
    have e0 : Ideal.Quotient.mk (Ideal.span {(M : ↥(Ohat ℚ))}) (k 1 0) = 0 := ((mem_mirab_iff _).1 hk).1
    have e1 : Ideal.Quotient.mk (Ideal.span {(M : ↥(Ohat ℚ))}) (k 1 1) = Ideal.Quotient.mk _ 1 := ((mem_mirab_iff _).1 hk).2
    refine ⟨fun a b => (k a b).2, fun a b => ?_, ?_, ?_⟩
    · rw [← map_inv]; exact ((k⁻¹ : GL (Fin 2) ↥(Ohat ℚ)) a b).2
    · obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 e0)
      exact ⟨y, y.2, congrArg Subtype.val hy⟩
    · obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 e1)
      exact ⟨y, y.2, congrArg Subtype.val hy⟩
  · rintro ⟨ha, hb, ⟨y, hy, e⟩, ⟨z, hz, e'⟩⟩
    have inj : Function.Injective (RingHom.mapMatrix (m := Fin 2) (Ohat ℚ).subtype) := fun x y h =>
      Matrix.ext fun a b => Subtype.ext (congrFun (congrFun h a) b)
    let k : GL (Fin 2) ↥(Ohat ℚ) :=
      ⟨Matrix.of fun a b => ⟨g a b, ha a b⟩, Matrix.of fun a b => ⟨(g⁻¹ : GL (Fin 2) (Af ℚ)) a b, hb a b⟩,
        inj (by rw [map_mul, map_one]; exact g.mul_inv), inj (by rw [map_mul, map_one]; exact g.inv_mul)⟩
    have e0 : Ideal.Quotient.mk (Ideal.span {(M : ↥(Ohat ℚ))}) (k 1 0) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 ⟨⟨y, hy⟩, Subtype.ext e⟩)
    have e1 : Ideal.Quotient.mk (Ideal.span {(M : ↥(Ohat ℚ))}) (k 1 1) = Ideal.Quotient.mk _ 1 :=
      Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 ⟨⟨z, hz⟩, Subtype.ext e'⟩)
    exact ⟨k, (mem_mirab_iff _).2 ⟨e0, e1⟩, Units.ext rfl⟩
