import Development.EtaleCohomology.EtaleSheaves.AlgResPropsPf

open CategoryTheory LateralTheory.E.t_E3Cut

namespace LateralTheory.E.EtAlgPf

/- English proof (translation)
Set `P` to `Q.comap (algebraMap A B)`. Establish `: Q.LiesOver P` using `⟨rfl⟩`. Use `letI := Localization.AtPrime.algebraOfLiesOver P Q`. Establish `: Algebra.IsUnramifiedAt A Q` using `inferInstance`. Establish `: Module.Finite P.ResidueField Q.ResidueField` using `inferInstance`.

Establish `: IsScalarTower A P.ResidueField Q.ResidueField` using `inferInstance`. Use `set x := algebraMap B Q.ResidueField c`. Establish `hx : IsIntegral P.ResidueField x` using `Algebra.IsIntegral.isIntegral x`. Set `p` to `minpoly P.ResidueField x`. Establish `hp0 : p ≠ 0` using `minpoly.ne_zero hx`.

Set `M` to `nonZeroDivisors (A ⧸ P)`. Set `q` to `IsLocalization.integerNormalization M p`. Take `⟨b, hb⟩` from `IsLocalization.integerNormalization_spec M p`. Establish `hq0 : q ≠ 0`. Introduce `h`.

Conclude with `hp0 ((IsLocalization.integerNormalization_eq_zero_iff le_rfl p).1 h)`. Establish `hqm : q.map (algebraMap (A ⧸ P) P.ResidueField) = Polynomial.C (algebraMap (A ⧸ P) P.ResidueField b) * p`. Rewrite using `[hb.2, ← Polynomial.smul_eq_C_mul, algebraMap_smul]`. Take `⟨r, hr⟩` from `Polynomial.map_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective q`. Choose the witnesses or unpack the hypotheses as in `⟨n, hn⟩ : ∃ n, q.coeff n ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hq0 (Polynomial.ext h)`. Use `⟨r, ⟨n, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `hm`.

Apply `hn` to reduce the goal to its premises. Rewrite using `[← hr, Polynomial.coeff_map, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hm`. Rewrite using `[← Ideal.algebraMap_residueField_eq_zero, Polynomial.hom_eval₂, ← IsScalarTower.algebraMap_eq]`. Establish `e1 : algebraMap A Q.ResidueField = (algebraMap P.ResidueField Q.ResidueField).comp ((algebraMap (A ⧸ P) P.ResidueField).comp (Ideal.Quotient.mk P))`.

Use extensionality with `a`. Rewrite using `[RingHom.comp_apply, RingHom.comp_apply, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply A (A ⧸ P) P.ResidueField, ← IsScalarTower.algebraMap_apply A P.ResidueField Q.ResidueField]`. Rewrite using `[e1, ← Polynomial.eval₂_map, ← Polynomial.map_map, hr, hqm, ← Polynomial.aeval_def, map_mul, minpoly.aeval, mul_zero]`.
-/
theorem key (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B] (Q : Ideal B) [Q.IsPrime]
    (c : B) : ∃ p : Polynomial A, (∃ n, algebraMap A B (p.coeff n) ∉ Q) ∧ p.eval₂ (algebraMap A B) c ∈ Q := by
  let P := Q.comap (algebraMap A B)
  have : Q.LiesOver P := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver P Q
  have : Algebra.IsUnramifiedAt A Q := inferInstance
  have : Module.Finite P.ResidueField Q.ResidueField := inferInstance
  have : IsScalarTower A P.ResidueField Q.ResidueField := inferInstance
  set x := algebraMap B Q.ResidueField c
  have hx : IsIntegral P.ResidueField x := Algebra.IsIntegral.isIntegral x
  let p := minpoly P.ResidueField x
  have hp0 : p ≠ 0 := minpoly.ne_zero hx
  let M := nonZeroDivisors (A ⧸ P)
  let q := IsLocalization.integerNormalization M p
  obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_spec M p
  have hq0 : q ≠ 0 := by
    intro h; exact hp0 ((IsLocalization.integerNormalization_eq_zero_iff le_rfl p).1 h)
  have hqm : q.map (algebraMap (A ⧸ P) P.ResidueField) = Polynomial.C (algebraMap (A ⧸ P) P.ResidueField b) * p := by
    rw [hb.2, ← Polynomial.smul_eq_C_mul, algebraMap_smul]
  obtain ⟨r, hr⟩ := Polynomial.map_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective q
  obtain ⟨n, hn⟩ : ∃ n, q.coeff n ≠ 0 := by
    by_contra h; push_neg at h; exact hq0 (Polynomial.ext h)
  refine ⟨r, ⟨n, ?_⟩, ?_⟩
  · intro hm; apply hn
    rw [← hr, Polynomial.coeff_map, Ideal.Quotient.eq_zero_iff_mem]; exact hm
  · rw [← Ideal.algebraMap_residueField_eq_zero, Polynomial.hom_eval₂, ← IsScalarTower.algebraMap_eq]
    have e1 : algebraMap A Q.ResidueField = (algebraMap P.ResidueField Q.ResidueField).comp
        ((algebraMap (A ⧸ P) P.ResidueField).comp (Ideal.Quotient.mk P)) := by
      ext a
      rw [RingHom.comp_apply, RingHom.comp_apply, ← Ideal.Quotient.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply A (A ⧸ P) P.ResidueField,
        ← IsScalarTower.algebraMap_apply A P.ResidueField Q.ResidueField]
    rw [e1, ← Polynomial.eval₂_map, ← Polynomial.map_map, hr, hqm, ← Polynomial.aeval_def, map_mul,
      minpoly.aeval, mul_zero]

/- English proof (translation)
Introduce `A B f hf`. Set `_` to `f.hom.toAlgebra`. Establish `: Algebra.Etale A B` using `hf`. Introduce `Q hQ c`. Conclude with `key A B Q c`.
-/
theorem EtAlg_of : LateralTheory.E.AlgResPropsPf.EtAlg := by
  intro A B f hf
  let _ := f.hom.toAlgebra
  have : Algebra.Etale A B := hf
  intro Q hQ c
  exact key A B Q c

end LateralTheory.E.EtAlgPf
