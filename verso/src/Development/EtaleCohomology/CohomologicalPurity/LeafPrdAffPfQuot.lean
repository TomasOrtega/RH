import Development.EtaleCohomology.CohomologicalPurity.LeafPrdAffPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

/- English proof (translation)
Establish `hJ : Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R) = MvPolynomial.X '' Set.univ` using `Set.image_univ.symm`. Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `r hr`. Rewrite `hr` using `[RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, hJ, MvPolynomial.mem_ideal_span_X_image]`.

Assume the negation of the conclusion as `h`. Take `⟨i, -, hi⟩` from `hr 0 (by rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C, if_pos rfl]; exact h)`. Conclude with `hi rfl`. Introduce `y`. Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective y`.

Use `⟨MvPolynomial.constantCoeff p, ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, Ideal.Quotient.eq, hJ, MvPolynomial.mem_ideal_span_X_image]`. Introduce `m hm`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Establish `: m = 0` using `Finsupp.ext fun i => hcon i (Set.mem_univ i)`. Substitute `this` using the available equality. Rewrite `hm` using `[MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, MvPolynomial.coeff_C, if_pos rfl, ← MvPolynomial.constantCoeff_eq, sub_self]`. Conclude with `hm rfl`.
-/
theorem quotC_bij (d : ℕ) (R : Type) [CommRing R] :
    Function.Bijective ((Ideal.Quotient.mk (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R)))).comp
      MvPolynomial.C) := by
  have hJ : Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R) = MvPolynomial.X '' Set.univ := Set.image_univ.symm
  constructor
  · rw [injective_iff_map_eq_zero]
    intro r hr
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, hJ, MvPolynomial.mem_ideal_span_X_image] at hr
    by_contra h
    obtain ⟨i, -, hi⟩ := hr 0 (by rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C, if_pos rfl]; exact h)
    exact hi rfl
  · intro y
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨MvPolynomial.constantCoeff p, ?_⟩
    rw [RingHom.comp_apply, Ideal.Quotient.eq, hJ, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra hcon
    push_neg at hcon
    have : m = 0 := Finsupp.ext fun i => hcon i (Set.mem_univ i)
    subst this
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, MvPolynomial.coeff_C, if_pos rfl,
      ← MvPolynomial.constantCoeff_eq, sub_self] at hm
    exact hm rfl

/- English proof (translation)
Introduce `hQ d R B C _ _ _ ψ η hψ I K hη hK hI`. Substitute `hK` using the available equality. Establish `hJI : (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R))).map ψ = I`. Rewrite using `[Ideal.map_span, ← Set.range_comp]`. Conclude with `hI`.

Substitute `hJI` using the available equality. Establish `b2` using `hψ.2`. Establish `b3` using `hQ B C η _ hη`. Establish `e : (Ideal.Quotient.mk _).comp (η.comp (ψ.comp MvPolynomial.C)) = ((Ideal.quotientMap _ η Ideal.le_comap_map).comp (Ideal.quotientMap _ ψ Ideal.le_comap_map)).comp ((Ideal.Quotient.mk (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R)))).comp MvPolynomial.C)`. Use extensionality with `r`.

Simplify using `[Ideal.quotientMap_mk]`. Rewrite using `[e]`. Conclude with `(b3.comp b2).comp (quotC_bij d R)`.
-/
theorem leafAffQuot_pf : LeafAffQuot := by
  intro hQ d R B C _ _ _ ψ η hψ I K hη hK hI
  subst hK
  have hJI : (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R))).map ψ = I := by
    rw [Ideal.map_span, ← Set.range_comp]; exact hI
  subst hJI
  have b2 := hψ.2
  have b3 := hQ B C η _ hη
  have e : (Ideal.Quotient.mk _).comp (η.comp (ψ.comp MvPolynomial.C)) =
      ((Ideal.quotientMap _ η Ideal.le_comap_map).comp (Ideal.quotientMap _ ψ Ideal.le_comap_map)).comp
        ((Ideal.Quotient.mk (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R)))).comp
          MvPolynomial.C) := by
    ext r; simp [Ideal.quotientMap_mk]
  rw [e]
  exact (b3.comp b2).comp (quotC_bij d R)

/- English proof (translation)
The claim follows from `LeafPrdAff_of hT hA h1 leafAffQuot_pf h3 hQ hI`.
-/
theorem LeafPrdAff_of' (hT : LeafThom) (hA : LeafActNat) (h1 : LeafHensH) (h3 : LeafExcAff)
    (hQ : LeafQuot) (hI : LeafIndExc) : LeafPrdAff :=
  LeafPrdAff_of hT hA h1 leafAffQuot_pf h3 hQ hI

end LateralTheory.CohomologicalPurity.TubeCut
