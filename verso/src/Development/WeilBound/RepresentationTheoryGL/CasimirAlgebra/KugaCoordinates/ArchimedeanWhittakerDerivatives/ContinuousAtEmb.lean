import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.ArchimedeanWhittakerDerivatives.ContinuousInfGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieCoordinateMatrixEquivariant

noncomputable section

namespace PositivityTheory.Rg.Cz

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric GlobalTheory.WigAlg

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [NumberField E] [IsTotallyComplex E] in
/- English proof (translation)
Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.
-/
theorem atEmb_add (τ : E →+* ℂ) (z w : ℂ) : atEmb τ (z + w) = atEmb τ z + atEmb τ w := by
  rw [atEmb_eq τ (z + w), atEmb_eq τ z, atEmb_eq τ w, Complex.add_re, Complex.add_im, add_smul, add_smul]
  abel

omit [NumberField E] [IsTotallyComplex E] in
/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities.
-/
theorem atEmb_real_mul (τ : E →+* ℂ) (t : ℝ) (z : ℂ) : atEmb τ (t * z) = t • atEmb τ z := by
  rw [atEmb_eq τ (t * z), atEmb_eq τ z, Complex.re_ofReal_mul, Complex.im_ofReal_mul, smul_add, smul_smul, smul_smul]

omit [NumberField E] [IsTotallyComplex E] in
/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem continuous_atEmb (τ : E →+* ℂ) : Continuous (atEmb τ) := by
  have e : atEmb τ = fun z : ℂ => z.re • atEmb τ 1 + z.im • atEmb τ Complex.I := funext fun z => atEmb_eq τ z
  rw [e]
  exact (Complex.continuous_re.smul continuous_const).add (Complex.continuous_im.smul continuous_const)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem continuous_sInf' : Continuous (sInf E) :=
  ((continuous_infEq E).prodMk continuous_const : Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))

/- English proof (translation)
Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions.

Rewrite the indicated hypotheses using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem psi_nontriv {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (τ : E →+* ℂ) : ∃ z : ℂ, ψ (sInf E (atEmb τ z)) ≠ 1 := by
  classical
  haveI : Nontrivial (Af E) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 E)
    let v : IsDedekindDomain.HeightOneSpectrum (𝓞 E) :=
      ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)⟩
    refine ⟨0, 1, fun h => ?_⟩
    have h2 : (0 : v.adicCompletion E) = 1 := congrArg (fun x : Af E => x v) h
    exact zero_ne_one h2
  by_contra hc
  push Not at hc
  have hpi : ∀ x, pInf E (sInf E x) = x := fun x => (infEq E).symm_apply_apply x
  have hpf : ∀ x, pFin E (sInf E x) = 0 := fun x => rfl
  have key : ∀ c : E, ψ (sInf E (atEmb τ 1) * algebraMap E (Ad E) c) = 1 := fun c => by
    have e : sInf E (atEmb τ 1) * algebraMap E (Ad E) c =
        sInf E (atEmb τ (coord τ (pInf E (algebraMap E (Ad E) c)) * 1)) :=
      ad_ext (by rw [map_mul, hpi, hpi, ← mul_embeddingScalar_eq_coord_mul, mul_comm]) (by rw [map_mul, hpf, hpf, zero_mul])
    rw [e]
    exact hc _
  obtain ⟨d, hd⟩ := hψ.ann _ key
  have hd0 : d = 0 := by
    have h1 := congrArg (pFin E) hd
    rw [hpf] at h1
    have h2 : pFin E (algebraMap E (Ad E) d) = algebraMap E (Af E) d := rfl
    rw [h2] at h1
    exact (algebraMap E (Af E)).injective (h1.symm.trans (map_zero _).symm)
  rw [hd0, map_zero] at hd
  have h3 := congrArg (fun x => pInf E x (InfinitePlace.mk τ)) hd
  simp only [hpi, map_zero, Pi.zero_apply] at h3
  unfold atEmb at h3
  rw [Pi.single_eq_same] at h3
  split_ifs at h3 <;> simp at h3

end PositivityTheory.Rg.Cz
