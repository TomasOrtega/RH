import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalDivisorChartGeneric
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelDivisorChartGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace NormalDivisorChartGeneric

/- English proof (translation)
Set `: Algebra R S` to `f.toAlgebra`. Establish `: Algebra.IsIntegral R S` using `⟨hint⟩`. Use `iSup_le fun l => ?_` and prove the remaining obligations. Establish `hker : (⊥ : Ideal S).comap (algebraMap R S) ≤ (RelSeries.head l).asIdeal`. Introduce `r hr`.

Establish `: f r = 0` using `hr`. Rewrite using `[show r = 0 from hinj (by rw [this, map_zero])]`. Conclude with `Ideal.zero_mem _`. Take `⟨P, -, hP, hPo⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral _ ⊥ hker`. Establish `: P.LiesOver (RelSeries.head l).asIdeal` using `⟨hPo.symm⟩`.

Take `⟨L, hlen, -, -⟩` from `Ideal.exists_ltSeries_of_hasGoingUp l P`. Conclude with `le_iSup_of_le L (by rw [hlen])`.
-/
theorem ringKrullDim_le_of_injective_isIntegral {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hinj : Function.Injective f) (hint : f.IsIntegral) : ringKrullDim R ≤ ringKrullDim S := by
  let : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hint⟩
  refine iSup_le fun l => ?_
  have hker : (⊥ : Ideal S).comap (algebraMap R S) ≤ (RelSeries.head l).asIdeal := by
    intro r hr
    have : f r = 0 := hr
    rw [show r = 0 from hinj (by rw [this, map_zero])]
    exact Ideal.zero_mem _
  obtain ⟨P, -, hP, hPo⟩ := Ideal.exists_ideal_over_prime_of_isIntegral _ ⊥ hker
  have : P.LiesOver (RelSeries.head l).asIdeal := ⟨hPo.symm⟩
  obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  exact le_iSup_of_le L (by rw [hlen])

/- English proof (translation)
Use `set f := (Ideal.Quotient.mk B).comp (rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m)).toRingHom with hf`. Set `: Algebra (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ B)` to `f.toAlgebra`. Establish `hX : ∀ s, IsIntegral (MvPolynomial (Fin n) ℂ) (Ideal.Quotient.mk B (X s))`. Introduce and unpack `(i | i)`. Establish `h : Ideal.Quotient.mk B (X (Sum.inl i)) = algebraMap (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ B) (X i)` using `by show _ = f (X i)`.

Simplify using `[hf]`. Rewrite using `[h]`. Conclude with `isIntegral_algebraMap`. Take `⟨P, hPm, hP⟩` from `M.integral i`. Use `⟨P, hPm, ?_⟩` and prove the remaining obligations.

Establish `h` using `Ideal.Quotient.eq_zero_iff_mem.mpr (hB hP)`. Rewrite `h` using `[Polynomial.hom_eval₂]`. Conclude with `h`. Introduce `z`. Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective z`.

Use `show IsIntegral (MvPolynomial (Fin n) ℂ) (Ideal.Quotient.mk B p)`. Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a`. Establish `h : Ideal.Quotient.mk B (C a) = algebraMap (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ B) (C a)` using `by show _ = f (C a)`. Simplify using `[hf]`.

Rewrite using `[h]`. Conclude with `isIntegral_algebraMap`. Consider the case `add p q hp hq`. Rewrite using `[map_add]`. Conclude with `hp.add hq`.

Consider the case `mul_X p s hp`. Rewrite using `[map_mul]`. Conclude with `hp.mul (hX s)`.
-/
theorem isIntegral_mk_comp_rename {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J) {B : Ideal (MvPolynomial (Fin n ⊕ Fin M.m) ℂ)} (hB : M.ideal ≤ B) :
    ((Ideal.Quotient.mk B).comp (rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m)).toRingHom).IsIntegral := by
  set f := (Ideal.Quotient.mk B).comp (rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m)).toRingHom with hf
  let : Algebra (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ B) := f.toAlgebra
  have hX : ∀ s, IsIntegral (MvPolynomial (Fin n) ℂ) (Ideal.Quotient.mk B (X s)) := by
    rintro (i | i)
    · have h : Ideal.Quotient.mk B (X (Sum.inl i)) =
          algebraMap (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ B) (X i) := by
        show _ = f (X i)
        simp [hf]
      rw [h]
      exact isIntegral_algebraMap
    · obtain ⟨P, hPm, hP⟩ := M.integral i
      refine ⟨P, hPm, ?_⟩
      have h := Ideal.Quotient.eq_zero_iff_mem.mpr (hB hP)
      rw [Polynomial.hom_eval₂] at h
      exact h
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  show IsIntegral (MvPolynomial (Fin n) ℂ) (Ideal.Quotient.mk B p)
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : Ideal.Quotient.mk B (C a) =
        algebraMap (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ B) (C a) := by
      show _ = f (C a)
      simp [hf]
    rw [h]
    exact isIntegral_algebraMap
  | add p q hp hq =>
    rw [map_add]
    exact hp.add hq
  | mul_X p s hp =>
    rw [map_mul]
    exact hp.mul (hX s)

/- English proof (translation)
Introduce `n d J u M hJ hdim hu`. Take `⟨B, hleB, hdimB, hB⟩` from `hUp n d J u M hJ hdim hu`. Use `⟨B.comap (rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m)).toRingHom, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `sup_le ?_ ((Ideal.span_le).2 (Set.singleton_subset_iff.2 ?_))` and prove the remaining obligations. Conclude with `M.comap_eq.symm.le.trans (Ideal.comap_mono (le_sup_left.trans hleB))`.

Conclude with `hleB (Ideal.mem_sup_right (Ideal.subset_span rfl))`. Use `lt_of_le_of_lt ?_ hdimB` and prove the remaining obligations. Conclude with `ringKrullDim_le_of_injective_isIntegral _ Ideal.quotientMap_injective ((isIntegral_quotientMap_iff _).2 (isIntegral_mk_comp_rename M (le_sup_left.trans hleB)))`. Introduce `q _ hqu hqI w hw hwq`. Use `hB w hw (hwq ▸ hqu) fun hwB => hqI fun f hf => ?_` and prove the remaining obligations.

Establish `h` using `hwB _ hf`. Rewrite `h` using `[AlgHom.toRingHom_eq_coe, RingHom.coe_coe, eval_rename]`. Rewrite using `[← hwq]`. Conclude with `h`.
-/
theorem proof (hUp : NormalModelDivisorChartGeneric.Statement) : NormalDivisorChartGeneric.Statement := by
  intro n d J u M hJ hdim hu
  obtain ⟨B, hleB, hdimB, hB⟩ := hUp n d J u M hJ hdim hu
  refine ⟨B.comap (rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m)).toRingHom, ?_, ?_, ?_⟩
  · refine sup_le ?_ ((Ideal.span_le).2 (Set.singleton_subset_iff.2 ?_))
    · exact M.comap_eq.symm.le.trans (Ideal.comap_mono (le_sup_left.trans hleB))
    · exact hleB (Ideal.mem_sup_right (Ideal.subset_span rfl))
  · refine lt_of_le_of_lt ?_ hdimB
    exact ringKrullDim_le_of_injective_isIntegral _ Ideal.quotientMap_injective
      ((isIntegral_quotientMap_iff _).2 (isIntegral_mk_comp_rename M (le_sup_left.trans hleB)))
  · intro q _ hqu hqI w hw hwq
    refine hB w hw (hwq ▸ hqu) fun hwB => hqI fun f hf => ?_
    have h := hwB _ hf
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, eval_rename] at h
    rw [← hwq]
    exact h

end NormalDivisorChartGeneric

end

end GroundTheory.Heights₂.Heights
