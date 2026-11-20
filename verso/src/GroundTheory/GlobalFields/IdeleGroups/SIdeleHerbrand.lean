import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.SIdeleHerbrand.Places
import GroundTheory.GlobalFields.SemilocalAlgebras.Finite

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum GroundTheory.GroupCoh

open scoped NumberField.LiesOver

open SemiLocal (PlacesOver)

noncomputable section

namespace IdeleGroup

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

open SemiLocal in

/- English proof (translation)
Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_nonempty_iff]`. Use `sum_finrank_eq L v` as an intermediate fact. Rewrite `this` using `[Finset.univ_eq_empty, Finset.sum_empty]`. Conclude with `(Module.finrank_pos (R := K) (M := L)).ne this`.
-/
theorem nonempty_placesOver_of_finite (v : HeightOneSpectrum (𝓞 K)) :
    Nonempty (PlacesOver L v) := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := sum_finrank_eq L v
  rw [Finset.univ_eq_empty, Finset.sum_empty] at this
  exact (Module.finrank_pos (R := K) (M := L)).ne this

variable [IsGalois K L] [Fintype Gal(L/K)]

/- English proof (translation)
Establish `h : ∀ v : ↥Sᶜ, Subsingleton (CycTateZero (Representation.ofMulDistribMulAction Gal(L/K) ((w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ)) σ)` using `fun v ↦ by`. Take `⟨w⟩` from `nonempty_placesOver_of_finite (L := L) v.1`. Conclude with `subsingleton_cycTateZero_integerUnitsAbove v.1 σ hσ w (hS v.1 v.2 w)`. Conclude with `(cycTateZeroMulPiEquiv (fun v : ↥Sᶜ ↦ (w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ) σ).toEquiv.subsingleton`.
-/
theorem subsingleton_cycTateZero_integerUnitsOutside (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v ∉ S, ∀ w : PlacesOver L v, w.1.asIdeal.ramificationIdx (𝓞 K) = 1)
    (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Subsingleton (CycTateZero (Representation.ofMulDistribMulAction Gal(L/K)
      ((v : ↥Sᶜ) → (w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ)) σ) := by
  have h : ∀ v : ↥Sᶜ, Subsingleton (CycTateZero (Representation.ofMulDistribMulAction Gal(L/K)
      ((w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ)) σ) := fun v ↦ by
    obtain ⟨w⟩ := nonempty_placesOver_of_finite (L := L) v.1
    exact subsingleton_cycTateZero_integerUnitsAbove v.1 σ hσ w (hS v.1 v.2 w)
  exact (cycTateZeroMulPiEquiv
    (fun v : ↥Sᶜ ↦ (w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ) σ).toEquiv.subsingleton

/- English proof (translation)
Establish `h : ∀ v : ↥Sᶜ, Subsingleton (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K) ((w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ)) σ)` using `fun v ↦ by`. Take `⟨w⟩` from `nonempty_placesOver_of_finite (L := L) v.1`. Conclude with `subsingleton_cycTateNegOne_integerUnitsAbove v.1 σ hσ w (hS v.1 v.2 w)`. Conclude with `(cycTateNegOneMulPiEquiv (fun v : ↥Sᶜ ↦ (w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ) σ).toEquiv.subsingleton`.
-/
theorem subsingleton_cycTateNegOne_integerUnitsOutside (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v ∉ S, ∀ w : PlacesOver L v, w.1.asIdeal.ramificationIdx (𝓞 K) = 1)
    (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Subsingleton (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K)
      ((v : ↥Sᶜ) → (w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ)) σ) := by
  have h : ∀ v : ↥Sᶜ, Subsingleton (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K)
      ((w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ)) σ) := fun v ↦ by
    obtain ⟨w⟩ := nonempty_placesOver_of_finite (L := L) v.1
    exact subsingleton_cycTateNegOne_integerUnitsAbove v.1 σ hσ w (hS v.1 v.2 w)
  exact (cycTateNegOneMulPiEquiv
    (fun v : ↥Sᶜ ↦ (w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ) σ).toEquiv.subsingleton

/- English proof (translation)
Establish `h0` using `subsingleton_cycTateZero_integerUnitsOutside S hS σ hσ`. Establish `h1` using `subsingleton_cycTateNegOne_integerUnitsOutside S hS σ hσ`. Rewrite using `[cycHerbrand_eq, Nat.card_eq_one_iff_unique.2 ⟨h0, ⟨0⟩⟩, Nat.card_eq_one_iff_unique.2 ⟨h1, ⟨0⟩⟩]`. Evaluate the numerical expressions.
-/
theorem cycHerbrand_integerUnitsOutside (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v ∉ S, ∀ w : PlacesOver L v, w.1.asIdeal.ramificationIdx (𝓞 K) = 1)
    (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cycHerbrand (Representation.ofMulDistribMulAction Gal(L/K)
      ((v : ↥Sᶜ) → (w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ)) σ = 1 := by
  have h0 := subsingleton_cycTateZero_integerUnitsOutside S hS σ hσ
  have h1 := subsingleton_cycTateNegOne_integerUnitsOutside S hS σ hσ
  rw [cycHerbrand_eq, Nat.card_eq_one_iff_unique.2 ⟨h0, ⟨0⟩⟩,
    Nat.card_eq_one_iff_unique.2 ⟨h1, ⟨0⟩⟩]
  norm_num

open AdicLiesOver in

/- English proof (translation)
Set `_ : Fintype S` to `hSf.fintype`. Establish `key : cycHerbrand (Representation.ofMulDistribMulAction Gal(L/K) (sIdeles (placesAbove L S))) σ = (∏ v : InfinitePlace K, (Module.finrank v.Completion (wInf v).1.Completion : ℚ)) * ∏ v ∈ hSf.toFinset, (Module.finrank (v.adicCompletion K) ((wFin v).1.adicCompletion L) : ℚ)`. Establish `hcompat : ∀ (g : Gal(L/K)) (x : Additive (sIdeles (placesAbove L S))), (sIdelesEquivProduct S hSf).toAdditive (Representation.ofMulDistribMulAction Gal(L/K) (sIdeles (placesAbove L S)) g x) = Representation.ofMulDistribMulAction Gal(L/K) (SIdelesProduct L S) g ((sIdelesEquivProdu …` using `fun g x ↦ by`. Apply `Additive.toMul.injective` to reduce the goal to its premises. Conclude with `sIdelesEquivProduct_smul S hSf g x.toMul`.

Rewrite using `[cycHerbrand_congr (sIdelesEquivProduct S hSf).toAdditive hcompat σ]`. Rewrite using `[cycHerbrand_mulProd, cycHerbrand_mulProd, cycHerbrand_integerUnitsOutside S hS σ hσ, mul_one, cycHerbrand_mulPi, cycHerbrand_mulPi, Finset.prod_subtype hSf.toFinset (fun v ↦ hSf.mem_toFinset)]`. Use `congr 1`. Conclude with `Finset.prod_congr rfl fun v _ ↦ cycHerbrand_infiniteUnitsAbove v σ hσ (wInf v)`. Conclude with `Finset.prod_congr rfl fun v _ ↦ cycHerbrand_finiteUnitsAbove v.1 σ hσ (wFin v.1)`.

Use `⟨hasHerbrandQuotient_of_cycHerbrand_ne_zero ?_, key⟩` and prove the remaining obligations. Rewrite using `[key]`. Use `mul_ne_zero (Finset.prod_ne_zero_iff.2 fun v _ ↦ ?_) (Finset.prod_ne_zero_iff.2 fun v _ ↦ ?_)` and prove the remaining obligations. Conclude with `Nat.cast_ne_zero.2 Module.finrank_pos.ne'`. Conclude with `Nat.cast_ne_zero.2 Module.finrank_pos.ne'`.
-/
theorem cycHerbrand_sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) (hSf : S.Finite)
    (hS : ∀ v ∉ S, ∀ w : PlacesOver L v, w.1.asIdeal.ramificationIdx (𝓞 K) = 1)
    (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    (wInf : ∀ v : InfinitePlace K, v.placesOver L) (wFin : ∀ v : HeightOneSpectrum (𝓞 K), PlacesOver L v) :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction Gal(L/K) (sIdeles (placesAbove L S))) σ)
        (cycNorm (Representation.ofMulDistribMulAction Gal(L/K) (sIdeles (placesAbove L S)))) ∧
      cycHerbrand (Representation.ofMulDistribMulAction Gal(L/K) (sIdeles (placesAbove L S))) σ =
        (∏ v : InfinitePlace K, (Module.finrank v.Completion (wInf v).1.Completion : ℚ)) *
          ∏ v ∈ hSf.toFinset,
            (Module.finrank (v.adicCompletion K) ((wFin v).1.adicCompletion L) : ℚ) := by
  let _ : Fintype S := hSf.fintype
  have key : cycHerbrand (Representation.ofMulDistribMulAction Gal(L/K)
      (sIdeles (placesAbove L S))) σ =
        (∏ v : InfinitePlace K, (Module.finrank v.Completion (wInf v).1.Completion : ℚ)) *
          ∏ v ∈ hSf.toFinset,
            (Module.finrank (v.adicCompletion K) ((wFin v).1.adicCompletion L) : ℚ) := by
    have hcompat : ∀ (g : Gal(L/K)) (x : Additive (sIdeles (placesAbove L S))),
        (sIdelesEquivProduct S hSf).toAdditive
            (Representation.ofMulDistribMulAction Gal(L/K) (sIdeles (placesAbove L S)) g x) =
          Representation.ofMulDistribMulAction Gal(L/K) (SIdelesProduct L S) g
            ((sIdelesEquivProduct S hSf).toAdditive x) := fun g x ↦ by
      apply Additive.toMul.injective
      exact sIdelesEquivProduct_smul S hSf g x.toMul
    rw [cycHerbrand_congr (sIdelesEquivProduct S hSf).toAdditive hcompat σ]
    rw [cycHerbrand_mulProd, cycHerbrand_mulProd, cycHerbrand_integerUnitsOutside S hS σ hσ,
      mul_one, cycHerbrand_mulPi, cycHerbrand_mulPi,
      Finset.prod_subtype hSf.toFinset (fun v ↦ hSf.mem_toFinset)]
    congr 1
    · exact Finset.prod_congr rfl fun v _ ↦ cycHerbrand_infiniteUnitsAbove v σ hσ (wInf v)
    · exact Finset.prod_congr rfl fun v _ ↦ cycHerbrand_finiteUnitsAbove v.1 σ hσ (wFin v.1)
  refine ⟨hasHerbrandQuotient_of_cycHerbrand_ne_zero ?_, key⟩
  rw [key]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun v _ ↦ ?_)
    (Finset.prod_ne_zero_iff.2 fun v _ ↦ ?_)
  · exact Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  · exact Nat.cast_ne_zero.2 Module.finrank_pos.ne'

end IdeleGroup

end

end GroundTheory.Global
