import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SubMemDifferentIdeal
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealPlaces

variable (D : D7)

/- English proof (translation)
Introduce `τ τ' h`. Conclude with `D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))`.
-/
theorem embS_injective : Function.Injective (embS D) := by
  intro τ τ' h
  exact D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨g, rfl⟩` from `(factEmb D.R D.host).1.2 φ`. Establish `hg` using `((factEmb D.R D.host).2 g).1 h`. Use `⟨D.eTau.symm ⟨g, hg⟩, ?_⟩` and prove the remaining obligations.

Unfold `embS`. Rewrite using `[Equiv.apply_symm_apply]`. Introduce and unpack `⟨τ, rfl⟩`. Conclude with `((factEmb D.R D.host).2 _).2 (D.eTau τ).2`.
-/
theorem mem_cm_iff (φ : D.host.E →+* ℂ) :
    φ ∈ D.host.cmType ↔ ∃ τ, embS D τ = φ := by
  constructor
  · intro h
    obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 φ
    have hg := ((factEmb D.R D.host).2 g).1 h
    refine ⟨D.eTau.symm ⟨g, hg⟩, ?_⟩
    unfold embS
    rw [Equiv.apply_symm_apply]
  · rintro ⟨τ, rfl⟩
    exact ((factEmb D.R D.host).2 _).2 (D.eTau τ).2

/- English proof (translation)
Rewrite using `[← mem_cm_iff, ← mem_cm_iff]`. Conclude with `D.host.der.cmType.1 φ`.
-/
theorem range_iff (φ : D.host.E →+* ℂ) :
    (∃ τ, embS D τ = φ) ↔ ¬ ∃ τ, embS D τ = ComplexEmbedding.conjugate φ := by
  rw [← mem_cm_iff, ← mem_cm_iff]
  exact D.host.der.cmType.1 φ

/- English proof (translation)
Introduce `h` and use `(range_iff D _).1 ⟨τ, rfl⟩ ⟨τ', h⟩`.
-/
theorem ne_conj (τ τ' : D.what₂.Tau) : embS D τ' ≠ ComplexEmbedding.conjugate (embS D τ) :=
  fun h => (range_iff D _).1 ⟨τ, rfl⟩ ⟨τ', h⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `(τ | τ) (τ' | τ') h`. Conclude with `congrArg _ (embS_injective D h)`. Conclude with `absurd h (ne_conj D _ _)`. Conclude with `absurd h.symm (ne_conj D _ _)`.

Conclude with `congrArg _ (embS_injective D (star_injective h))`. Introduce `φ`. Distinguish the cases in `h : ∃ τ, embS D τ = φ`. Take `⟨τ, hτ⟩` from `h`. Conclude with `⟨Sum.inl τ, hτ⟩`.

Take `⟨τ, hτ⟩` from `not_not.1 (fun h' => h ((range_iff D φ).2 h'))`. Use `⟨Sum.inr τ, ?_⟩` and prove the remaining obligations. Use `show star (embS D τ) = φ`. Rewrite using `[hτ]`. Conclude with `star_star φ`.
-/
theorem sum_bijective : Function.Bijective
    (Sum.elim (embS D) (fun τ => ComplexEmbedding.conjugate (embS D τ))) := by
  constructor
  · rintro (τ | τ) (τ' | τ') h
    · exact congrArg _ (embS_injective D h)
    · exact absurd h (ne_conj D _ _)
    · exact absurd h.symm (ne_conj D _ _)
    · exact congrArg _ (embS_injective D (star_injective h))
  · intro φ
    by_cases h : ∃ τ, embS D τ = φ
    · obtain ⟨τ, hτ⟩ := h
      exact ⟨Sum.inl τ, hτ⟩
    · obtain ⟨τ, hτ⟩ := not_not.1 (fun h' => h ((range_iff D φ).2 h'))
      refine ⟨Sum.inr τ, ?_⟩
      show star (embS D τ) = φ
      rw [hτ]
      exact star_star φ

/- English proof (translation)
Establish `hex : ∃ τ, InfinitePlace.mk (embS D τ) = w`. Take `⟨τ | τ, h⟩` from `(sum_bijective D).2 w.embedding`. Conclude with `⟨τ, by rw [show embS D τ = w.embedding from h, InfinitePlace.mk_embedding]⟩`. Use `⟨τ, ?_⟩` and prove the remaining obligations. Rewrite using `[← InfinitePlace.mk_conjugate_eq, show ComplexEmbedding.conjugate (embS D τ) = w.embedding from h, InfinitePlace.mk_embedding]`.

Take `⟨τ, hτ⟩` from `hex`. Use `⟨τ, hτ, fun τ' h' => ?_⟩` and prove the remaining obligations. Break down `InfinitePlace.mk_eq_iff.1 (h'.trans hτ.symm) with h | h` into its components or cases. Conclude with `embS_injective D h`. Conclude with `absurd h.symm (ne_conj D _ _)`.
-/
theorem existsUnique_place (w : InfinitePlace D.host.E) :
    ∃! τ, InfinitePlace.mk (embS D τ) = w := by
  have hex : ∃ τ, InfinitePlace.mk (embS D τ) = w := by
    obtain ⟨τ | τ, h⟩ := (sum_bijective D).2 w.embedding
    · exact ⟨τ, by rw [show embS D τ = w.embedding from h, InfinitePlace.mk_embedding]⟩
    · refine ⟨τ, ?_⟩
      rw [← InfinitePlace.mk_conjugate_eq,
        show ComplexEmbedding.conjugate (embS D τ) = w.embedding from h, InfinitePlace.mk_embedding]
  obtain ⟨τ, hτ⟩ := hex
  refine ⟨τ, hτ, fun τ' h' => ?_⟩
  rcases InfinitePlace.mk_eq_iff.1 (h'.trans hτ.symm) with h | h
  · exact embS_injective D h
  · exact absurd h.symm (ne_conj D _ _)

/- English proof (translation)
Establish `hb : Function.Bijective (fun τ => InfinitePlace.mk (embS D τ))` using `(Function.bijective_iff_existsUnique _).2 (existsUnique_place D)`. Establish `h` using `InfinitePlace.prod_eq_abs_norm a`. Rewrite `h` using `[Rat.cast_abs]`. Rewrite using `[← h, ← hb.prod_comp]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Establish `hc : (InfinitePlace.mk (embS D τ)).IsComplex`. Rewrite using `[InfinitePlace.isComplex_mk_iff]`. Conclude with `fun hr => ne_conj D τ τ (ComplexEmbedding.isReal_iff.1 hr).symm`. Rewrite using `[hc.mult_eq_two, InfinitePlace.apply]`.
-/
theorem prod_norm (a : D.host.E) :
    ∏ τ, ‖embS D τ a‖ ^ 2 = |((Algebra.norm ℚ a : ℚ) : ℝ)| := by
  have hb : Function.Bijective (fun τ => InfinitePlace.mk (embS D τ)) :=
    (Function.bijective_iff_existsUnique _).2 (existsUnique_place D)
  have h := InfinitePlace.prod_eq_abs_norm a
  rw [Rat.cast_abs] at h
  rw [← h, ← hb.prod_comp]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hc : (InfinitePlace.mk (embS D τ)).IsComplex := by
    rw [InfinitePlace.isComplex_mk_iff]
    exact fun hr => ne_conj D τ τ (ComplexEmbedding.isReal_iff.1 hr).symm
  rw [hc.mult_eq_two, InfinitePlace.apply]

/- English proof (translation)
Unfold `placeProd`. Rewrite using `[← (sum_bijective D).prod_comp, Fintype.prod_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, hc]`. Conclude with `Real.sqrt_mul_self (Finset.prod_nonneg fun τ _ => h0 _)`.
-/
theorem placeProd_eq (X : (D.host.E →+* ℂ) → ℝ) (h0 : ∀ φ, 0 ≤ X φ)
    (hc : ∀ φ, X (ComplexEmbedding.conjugate φ) = X φ) : placeProd X = ∏ τ, X (embS D τ) := by
  unfold placeProd
  rw [← (sum_bijective D).prod_comp, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, hc]
  exact Real.sqrt_mul_self (Finset.prod_nonneg fun τ _ => h0 _)

/- English proof (translation)
Rewrite using `[D.host.finrank_cmField, Ranks.f, Ranks.n]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finrank_E : finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.finrank_cmField, Ranks.f, Ranks.n]
  ring

/- English proof (translation)
Establish `h` using `finrank_mul_finrank ℚ D.host.F D.host.E`. Rewrite `h` using `[finrank_E, D.sp.cm.deg2]`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_F : finrank ℚ D.host.F = D.R.f := by
  have h := finrank_mul_finrank ℚ D.host.F D.host.E
  rw [finrank_E, D.sp.cm.deg2] at h
  omega

/- English proof (translation)
Unfold `Host.rdE`. Use `Real.one_le_rpow ?_ (by positivity)` and prove the remaining obligations. Use `Int.one_le_abs (discr_ne_zero D.host.E)` as an intermediate fact. Conclude with `this` after adjusting the coercions.
-/
theorem one_le_rdE : 1 ≤ D.host.rdE := by
  unfold Host.rdE
  refine Real.one_le_rpow ?_ (by positivity)
  have := Int.one_le_abs (discr_ne_zero D.host.E)
  exact_mod_cast this

/- English proof (translation)
Take `⟨h1, h2⟩` from `GlobalTheory.cm_discr_sq D.host.F D.host.E D.sp.cm`. Establish `hpos : finrank ℚ D.host.E ≠ 0` using `Module.finrank_pos.ne'`. Unfold `ddS Host.rdE`. Rewrite using `[FractionalIdeal.coeIdeal_absNorm, h2, ← finrank_E, one_div, Real.rpow_inv_natCast_pow (abs_nonneg _) hpos]`. Establish `h3 : |(discr D.host.E : ℝ)| = (discr D.host.F : ℝ) ^ 2` using `by exact_mod_cast h1`.

Rewrite using `[h3]`. Use `push_cast`. Rewrite using `[Nat.cast_natAbs, Int.cast_abs, sq_abs]`.
-/
theorem absNorm_ddS :
    ((FractionalIdeal.absNorm (ddS D) : ℚ) : ℝ) = D.host.rdE ^ (2 * D.R.f) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.cm_discr_sq D.host.F D.host.E D.sp.cm
  have hpos : finrank ℚ D.host.E ≠ 0 := Module.finrank_pos.ne'
  unfold ddS Host.rdE
  rw [FractionalIdeal.coeIdeal_absNorm, h2, ← finrank_E, one_div,
    Real.rpow_inv_natCast_pow (abs_nonneg _) hpos]
  have h3 : |(discr D.host.E : ℝ)| = (discr D.host.F : ℝ) ^ 2 := by exact_mod_cast h1
  rw [h3]
  push_cast
  rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]

end GlobalTheory.RealPlaces

/- English proof (translation)
Introduce `D`. Use `⟨D.what₂.card_Tau, GlobalTheory.RealPlaces.finrank_E D, GlobalTheory.RealPlaces.finrank_F D, D.R.rS_two.symm, GlobalTheory.RealPlaces.one_le_rdE D, fun τ a => D.sp.cm.cmUnram.2.1 _ a, GlobalTheory.RealPlaces.prod_norm D, GlobalTheory.RealPlaces.placeProd_eq D, GlobalTheory.RealPl …` and prove the remaining obligations.
-/
theorem GlobalTheory.real_places_facts : ∀ D : D7, Fintype.card D.what₂.Tau = D.R.f ∧ finrank ℚ D.host.E = 2 * D.R.f ∧ finrank ℚ D.host.F = D.R.f ∧ D.R.m = 2 * D.R.rS + 2 ∧ 1 ≤ D.host.rdE ∧ (∀ τ (a : D.host.E), embS D τ (star a) = starRingEnd ℂ (embS D τ a)) ∧ (∀ a : D.host.E, ∏ τ, ‖embS D τ a‖ ^ 2 = |((Algebra.norm ℚ a : ℚ) : ℝ)|) ∧ (∀ X : (D.host.E →+* ℂ) → ℝ, (∀ φ, 0 ≤ X φ) → (∀ φ, X (NumberField.ComplexEmbedding.conjugate φ) = X φ) → placeProd X = ∏ τ, X (embS D τ)) ∧ ((FractionalIdeal.absNorm (ddS D) : ℚ) : ℝ) = D.host.rdE ^ (2 * D.R.f) ∧ (∀ w : InfinitePlace D.host.E, ∃! τ, InfinitePlace.mk (embS D τ) = w) := by
  intro D
  refine ⟨D.what₂.card_Tau, GlobalTheory.RealPlaces.finrank_E D, GlobalTheory.RealPlaces.finrank_F D, D.R.rS_two.symm,
    GlobalTheory.RealPlaces.one_le_rdE D, fun τ a => D.sp.cm.cmUnram.2.1 _ a, GlobalTheory.RealPlaces.prod_norm D,
    GlobalTheory.RealPlaces.placeProd_eq D, GlobalTheory.RealPlaces.absNorm_ddS D,
    GlobalTheory.RealPlaces.existsUnique_place D⟩
