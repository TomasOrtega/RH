import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

namespace GlobalTheory.CMTypeCard

/- English proof (translation)
Use `⟨fun i j hij => ?_, fun w => ?_⟩` and prove the remaining obligations. Take `⟨k, -, hk⟩` from `h (φ j)`. Establish `h1 : j = k` using `hk j (Or.inl rfl)`. Establish `h2 : i = k` using `hk i (by`. Break down `InfinitePlace.mk_eq_iff.1 hij with e | e` into its components or cases.

Conclude with `Or.inl e.symm`. Conclude with `Or.inr e.symm)`. Rewrite using `[h1, h2]`. Take `⟨i, hi, -⟩` from `h w.embedding`. Use `⟨i, ?_⟩` and prove the remaining obligations.

Break down `hi with e | e` into its components or cases. Simplify using `only [← e, InfinitePlace.mk_embedding]`. Use `congrArg InfinitePlace.mk e` as an intermediate fact. Rewrite `this` using `[InfinitePlace.mk_embedding, InfinitePlace.mk_conjugate_eq]`. Conclude with `this.symm`.
-/
theorem bijective_mk_of_isCMType {E : Type} [Field E] [NumberField E] {I : Type} {φ : I → E →+* ℂ}
    (h : IsCMType φ) : Function.Bijective (fun i => InfinitePlace.mk (φ i)) := by
  refine ⟨fun i j hij => ?_, fun w => ?_⟩
  · obtain ⟨k, -, hk⟩ := h (φ j)
    have h1 : j = k := hk j (Or.inl rfl)
    have h2 : i = k := hk i (by
      rcases InfinitePlace.mk_eq_iff.1 hij with e | e
      · exact Or.inl e.symm
      · exact Or.inr e.symm)
    rw [h1, h2]
  · obtain ⟨i, hi, -⟩ := h w.embedding
    refine ⟨i, ?_⟩
    rcases hi with e | e
    · simp only [← e, InfinitePlace.mk_embedding]
    · have := congrArg InfinitePlace.mk e
      rw [InfinitePlace.mk_embedding, InfinitePlace.mk_conjugate_eq] at this
      exact this.symm

/- English proof (translation)
Introduce `K E _ _ _ _ _ _ I _ φ hφ h2`. Establish `hc : Fintype.card I = Fintype.card (InfinitePlace E)` using `Fintype.card_of_bijective (bijective_mk_of_isCMType hφ)`. Establish `hE : Module.finrank ℚ E = 2 * Fintype.card (InfinitePlace E)`. Establish `h1` using `InfinitePlace.card_add_two_mul_card_eq_rank E`. Establish `hr : NumberField.InfinitePlace.nrRealPlaces E = 0` using `IsTotallyComplex.nrRealPlaces_eq_zero E`.

Establish `h3` using `InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)`. Use linear arithmetic over natural numbers and integers. Establish `hKE : Module.finrank ℚ E = Module.finrank ℚ K * Module.finrank K E` using `(Module.finrank_mul_finrank ℚ K E).symm`. Rewrite `hKE` using `[h2]`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_eq_finrank_of_isCMType : ∀ {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [IsCMField E]
    [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hφ : IsCMType φ) (h2 : Module.finrank ℚ K = 2),
    Fintype.card I = Module.finrank K E := by
  intro K E _ _ _ _ _ _ I _ φ hφ h2
  have hc : Fintype.card I = Fintype.card (InfinitePlace E) :=
    Fintype.card_of_bijective (bijective_mk_of_isCMType hφ)
  have hE : Module.finrank ℚ E = 2 * Fintype.card (InfinitePlace E) := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank E
    have hr : NumberField.InfinitePlace.nrRealPlaces E = 0 := IsTotallyComplex.nrRealPlaces_eq_zero E
    have h3 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)
    omega
  have hKE : Module.finrank ℚ E = Module.finrank ℚ K * Module.finrank K E :=
    (Module.finrank_mul_finrank ℚ K E).symm
  rw [h2] at hKE
  omega

end GlobalTheory.CMTypeCard
