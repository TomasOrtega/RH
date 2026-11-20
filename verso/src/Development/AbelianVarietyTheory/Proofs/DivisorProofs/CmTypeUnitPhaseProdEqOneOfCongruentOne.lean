import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitRealOfCongrOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdArgRealUnitEqOneStatement
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ σ h emb q hq hq2 ht u hu`. Establish `hr` using `GlobalTheory.T.unit_real_of_sub_one_mem_span_prime E q hq ht u hu`. Establish `hs` using `GlobalTheory.T.prod_arg_real_unit_eq_one' E q hq hq2 u hu hr`. Take `⟨hF, hE, h2, -⟩` from `h`. Set `f : InfinitePlace F → InfinitePlace E` to `fun w => InfinitePlace.mk (emb w).1`.

Establish `hcomap : ∀ w, (f w).comap (algebraMap F E) = w`. Introduce `w`. Simplify using `only [f]`. Rewrite using `[InfinitePlace.comap_mk, (emb w).2, InfinitePlace.mk_embedding]`. Establish `hinj : Function.Injective f` using `fun a b hab => by`.

Rewrite using `[← hcomap a, ← hcomap b, hab]`. Establish `hcard : Fintype.card (InfinitePlace F) = Fintype.card (InfinitePlace E)`. Establish `a1` using `InfinitePlace.card_add_two_mul_card_eq_rank F`. Establish `a2` using `InfinitePlace.card_add_two_mul_card_eq_rank E`. Establish `b1` using `InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := F)`.

Establish `b2` using `InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)`. Establish `c1` using `IsTotallyReal.nrComplexPlaces_eq_zero F`. Establish `c2` using `IsTotallyComplex.nrRealPlaces_eq_zero E`. Establish `d` using `Module.finrank_mul_finrank ℚ F E`. Rewrite `d` using `[h2]`.

Use linear arithmetic over natural numbers and integers. Establish `hbij : Function.Bijective f` using `(Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩`. Establish `hfac : ∀ w, (emb w).1 ((u : 𝓞 E) : E) = (f w).embedding ((u : 𝓞 E) : E)`. Introduce `w`. Break down `InfinitePlace.embedding_mk_eq (emb w).1 with h' | h'` into its components or cases.

Simplify using `only [f]`. Rewrite using `[h']`. Simplify using `only [f]`. Rewrite using `[h', ComplexEmbedding.conjugate_coe_eq, hr]`. Rewrite using `[← hs]`.

Rewrite using `[← Fintype.prod_bijective f hbij (fun w => ((emb w).1 ((u : 𝓞 E) : E) / ((‖(emb w).1 ((u : 𝓞 E) : E)‖ : ℝ) : ℂ))) (fun v => (v.embedding ((u : 𝓞 E) : E) / ((‖v.embedding ((u : 𝓞 E) : E)‖ : ℝ) : ℂ))) (fun w => by rw [hfac w])]`.
-/
theorem weil_unit_phase_prod : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsCMField E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (q : ℕ), q.Prime → 2 < q → ¬ q ∣ Nat.card (Units.torsion E) → ∀ u : (𝓞 E)ˣ, (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)} → ∏ w : InfinitePlace F, ((emb w).1 ((u : 𝓞 E) : E) / ((‖(emb w).1 ((u : 𝓞 E) : E)‖ : ℝ) : ℂ)) = 1 := by
  intro F E _ _ _ _ _ _ σ h emb q hq hq2 ht u hu
  have hr := GlobalTheory.T.unit_real_of_sub_one_mem_span_prime E q hq ht u hu
  have hs := GlobalTheory.T.prod_arg_real_unit_eq_one' E q hq hq2 u hu hr
  obtain ⟨hF, hE, h2, -⟩ := h
  let f : InfinitePlace F → InfinitePlace E := fun w => InfinitePlace.mk (emb w).1
  have hcomap : ∀ w, (f w).comap (algebraMap F E) = w := by
    intro w
    simp only [f]
    rw [InfinitePlace.comap_mk, (emb w).2, InfinitePlace.mk_embedding]
  have hinj : Function.Injective f := fun a b hab => by
    rw [← hcomap a, ← hcomap b, hab]
  have hcard : Fintype.card (InfinitePlace F) = Fintype.card (InfinitePlace E) := by
    have a1 := InfinitePlace.card_add_two_mul_card_eq_rank F
    have a2 := InfinitePlace.card_add_two_mul_card_eq_rank E
    have b1 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := F)
    have b2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)
    have c1 := IsTotallyReal.nrComplexPlaces_eq_zero F
    have c2 := IsTotallyComplex.nrRealPlaces_eq_zero E
    have d := Module.finrank_mul_finrank ℚ F E
    rw [h2] at d
    omega
  have hbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩
  have hfac : ∀ w, (emb w).1 ((u : 𝓞 E) : E) = (f w).embedding ((u : 𝓞 E) : E) := by
    intro w
    rcases InfinitePlace.embedding_mk_eq (emb w).1 with h' | h'
    · simp only [f]; rw [h']
    · simp only [f]; rw [h', ComplexEmbedding.conjugate_coe_eq, hr]
  rw [← hs]
  rw [← Fintype.prod_bijective f hbij (fun w => ((emb w).1 ((u : 𝓞 E) : E) / ((‖(emb w).1 ((u : 𝓞 E) : E)‖ : ℝ) : ℂ))) (fun v => (v.embedding ((u : 𝓞 E) : E) / ((‖v.embedding ((u : 𝓞 E) : E)‖ : ℝ) : ℂ))) (fun w => by rw [hfac w])]

end GlobalTheory
