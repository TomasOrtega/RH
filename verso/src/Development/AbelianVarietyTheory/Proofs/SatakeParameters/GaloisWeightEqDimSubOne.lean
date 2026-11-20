import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GaloisRepOfPolarizedPair
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiTempered
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TemperedProductOfSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.EssSquareIntegrableSegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GenericUnlinkedGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmGaloisRepresentationCrystalline
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CsdWeight

/- English proof (translation)
Proceed by induction on `m using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons x m ih => simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_map_const_sub (c : ℂ) (m : Multiset ℂ) :
    (m.map fun z => c - z).sum = (Multiset.card m : ℂ) * c - m.sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x m ih => simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, ih]; push_cast; ring

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ _ l _ ι a ha π χ r wt HT hinf hc H`. Take `⟨φ0⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Use `set τ0 : E →+* Qbar l := ι.symm.toRingHom.comp φ0 with hτ0`. Use `set c : E →+* E := (IsCMField.complexConj E).toRingEquiv.toRingHom with hcdef`. Use `set φ : E →+* ℂ := ι.toRingHom.comp τ0 with hφ`.

Establish `hconj : ι.toRingHom.comp (τ0.comp c) = ComplexEmbedding.conjugate φ`. Use extensionality with `x`. Conclude with `IsCMField.complexEmbedding_complexConj E φ x`. Take `⟨m, hm⟩` from `hinf φ`. Take `⟨m', hm'⟩` from `hinf (ComplexEmbedding.conjugate φ)`.

Establish `hmm` using `GlobalTheory.CsdTwistGal.infChar_conj_of_isCsd E a π hc φ m m' hm hm'`. Establish `i1 : (CG.mk π).infChar φ = m` using `CG.HasInfChar.infChar_eq (π := CG.mk π) hm`. Establish `i2 : (CG.mk π).infChar (ComplexEmbedding.conjugate φ) = m'` using `CG.HasInfChar.infChar_eq (π := CG.mk π) hm'`. Establish `hcard : Multiset.card m = a` using `i1 ▸ CG.card_infChar _ φ`. Establish `e1` using `congrArg Multiset.sum (H.weights τ0)`.

Establish `e2` using `congrArg Multiset.sum (H.weights (τ0.comp c))`. Rewrite `e2` using `[H.weights_conj τ0, hconj, i2, hmm]`. Rewrite `e1` using `[i1]`. Rewrite `e1` using `[sum_map_const_sub, hcard]`. Rewrite `e2` using `[sum_map_const_sub, Multiset.card_map, hcard]`.

Establish `e3 : (((HT τ0).map (wt - ·)).map fun n : ℤ => (n : ℂ)).sum = (Multiset.card (HT τ0) : ℂ) * wt - ((HT τ0).map fun n : ℤ => (n : ℂ)).sum`. Rewrite using `[Multiset.map_map]`. Establish `: ((HT τ0).map ((fun n : ℤ => (n : ℂ)) ∘ (wt - ·))) = ((HT τ0).map fun n : ℤ => (n : ℂ)).map fun z => (wt : ℂ) - z`. Rewrite using `[Multiset.map_map]`. Use `Multiset.map_congr rfl fun n _ => ?_` and prove the remaining obligations.

Simplify using the standard rewrite rules. Rewrite using `[this, sum_map_const_sub, Multiset.card_map]`. Establish `hcHT : Multiset.card (HT τ0) = a`. Use `congrArg Multiset.card (H.weights τ0)` as an intermediate fact. Rewrite `this` using `[Multiset.card_map, Multiset.card_map, i1, hcard]`. Then use the resulting hypothesis.

Rewrite `e2` using `[e3, hcHT, e1, Multiset.sum_map_neg']`. Establish `ha0 : (a : ℂ) ≠ 0` using `by exact_mod_cast (show a ≠ 0 by omega)`. Establish `h4 : (a : ℂ) * ((wt : ℂ) - ((a : ℂ) - 1)) = 0` using `by linear_combination e2`. Establish `h5 : (wt : ℂ) = ((a : ℤ) - 1 : ℤ)`. Use `push_cast`.

Use `(mul_eq_zero.1 h4).resolve_left ha0` as an intermediate fact. Take the linear combination `this`. Conclude with `h5` after adjusting the coercions.
-/
theorem weight_eq : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E))
    (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
    (∀ τ : E →+* ℂ, ∃ m, π.HasInfChar τ m) → π.IsCsd → IsGalRepOf π χ ι r wt HT → wt = (a : ℤ) - 1 := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha π χ r wt HT hinf hc H
  obtain ⟨φ0⟩ : Nonempty (E →+* ℂ) := inferInstance
  set τ0 : E →+* Qbar l := ι.symm.toRingHom.comp φ0 with hτ0
  set c : E →+* E := (IsCMField.complexConj E).toRingEquiv.toRingHom with hcdef
  set φ : E →+* ℂ := ι.toRingHom.comp τ0 with hφ
  have hconj : ι.toRingHom.comp (τ0.comp c) = ComplexEmbedding.conjugate φ := by
    ext x
    exact IsCMField.complexEmbedding_complexConj E φ x
  obtain ⟨m, hm⟩ := hinf φ
  obtain ⟨m', hm'⟩ := hinf (ComplexEmbedding.conjugate φ)
  have hmm := GlobalTheory.CsdTwistGal.infChar_conj_of_isCsd E a π hc φ m m' hm hm'
  have i1 : (CG.mk π).infChar φ = m := CG.HasInfChar.infChar_eq (π := CG.mk π) hm
  have i2 : (CG.mk π).infChar (ComplexEmbedding.conjugate φ) = m' := CG.HasInfChar.infChar_eq (π := CG.mk π) hm'
  have hcard : Multiset.card m = a := i1 ▸ CG.card_infChar _ φ
  have e1 := congrArg Multiset.sum (H.weights τ0)
  have e2 := congrArg Multiset.sum (H.weights (τ0.comp c))
  rw [H.weights_conj τ0, hconj, i2, hmm] at e2
  rw [i1] at e1
  rw [sum_map_const_sub, hcard] at e1
  rw [sum_map_const_sub, Multiset.card_map, hcard] at e2
  have e3 : (((HT τ0).map (wt - ·)).map fun n : ℤ => (n : ℂ)).sum =
      (Multiset.card (HT τ0) : ℂ) * wt - ((HT τ0).map fun n : ℤ => (n : ℂ)).sum := by
    rw [Multiset.map_map]
    have : ((HT τ0).map ((fun n : ℤ => (n : ℂ)) ∘ (wt - ·))) = ((HT τ0).map fun n : ℤ => (n : ℂ)).map
        fun z => (wt : ℂ) - z := by
      rw [Multiset.map_map]; refine Multiset.map_congr rfl fun n _ => ?_; simp
    rw [this, sum_map_const_sub, Multiset.card_map]
  have hcHT : Multiset.card (HT τ0) = a := by
    have := congrArg Multiset.card (H.weights τ0)
    rwa [Multiset.card_map, Multiset.card_map, i1, hcard] at this
  rw [e3, hcHT, e1, Multiset.sum_map_neg'] at e2
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have h4 : (a : ℂ) * ((wt : ℂ) - ((a : ℂ) - 1)) = 0 := by linear_combination e2
  have h5 : (wt : ℂ) = ((a : ℤ) - 1 : ℤ) := by
    push_cast
    have := (mul_eq_zero.1 h4).resolve_left ha0
    linear_combination this
  exact_mod_cast h5

end GlobalTheory.CsdWeight
