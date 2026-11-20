import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.ExistsDenOfIsCompactAdele
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IntAdCpctOpen

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.IndefR.Eqv.G5

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply the tactic sequence `have hnn : ∀ w : InfinitePlace F, 0 ≤ w (r : F) := fun w => by first | positivity | exact w.nonneg _ | exact InfinitePlace.nonneg w _`. Establish `hN : (1 : ℝ) ≤ ((|Algebra.norm ℚ (r : F)| : ℚ) : ℝ)`. Rewrite using `[← Algebra.coe_norm_int]`.

Establish `hz : Algebra.norm ℤ r ≠ 0` using `Algebra.norm_ne_zero_iff.mpr hr`. Use `Int.one_le_abs hz` as an intermediate fact. Conclude with `this` after adjusting the coercions. Rewrite `hN` using `[← InfinitePlace.prod_eq_abs_norm]`. Take `⟨w0⟩` from `(inferInstance : Nonempty (InfinitePlace F))`.

Rewrite `hN` using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w0)]`. Establish `h1 : w0 (r : F) ^ w0.mult < 1` using `pow_lt_one₀ (hnn w0) (h w0) InfinitePlace.mult_pos.ne'`. Establish `h2 : ∏ w ∈ Finset.univ.erase w0, w (r : F) ^ w.mult ≤ 1` using `Finset.prod_le_one (fun w _ => pow_nonneg (hnn w) _) (fun w _ => pow_le_one₀ (hnn w) (h w).le)`. Establish `h3 : 0 ≤ w0 (r : F) ^ w0.mult` using `pow_nonneg (hnn w0) _`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem adl_exists_place_ge_one (r : 𝓞 F) (hr : r ≠ 0) :
    ∃ w : InfinitePlace F, 1 ≤ w (r : F) := by
  classical
  by_contra h
  push_neg at h
  have hnn : ∀ w : InfinitePlace F, 0 ≤ w (r : F) := fun w => by
    first | positivity | exact w.nonneg _ | exact InfinitePlace.nonneg w _
  have hN : (1 : ℝ) ≤ ((|Algebra.norm ℚ (r : F)| : ℚ) : ℝ) := by
    rw [← Algebra.coe_norm_int]
    have hz : Algebra.norm ℤ r ≠ 0 := Algebra.norm_ne_zero_iff.mpr hr
    have := Int.one_le_abs hz
    exact_mod_cast this
  rw [← InfinitePlace.prod_eq_abs_norm] at hN
  obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace F))
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w0)] at hN
  have h1 : w0 (r : F) ^ w0.mult < 1 := pow_lt_one₀ (hnn w0) (h w0) InfinitePlace.mult_pos.ne'
  have h2 : ∏ w ∈ Finset.univ.erase w0, w (r : F) ^ w.mult ≤ 1 :=
    Finset.prod_le_one (fun w _ => pow_nonneg (hnn w) _) (fun w _ => pow_le_one₀ (hnn w) (h w).le)
  have h3 : 0 ≤ w0 (r : F) ^ w0.mult := pow_nonneg (hnn w0) _
  nlinarith

open scoped AdeleRing

variable (F) in

def adlNbhd : Set (AdeleRing (𝓞 F) F) :=
  {x | (∀ w, ‖x.1 w‖ < 1) ∧ ∀ v, x.2 v ∈ v.adicCompletionIntegers F}

/- English proof (translation)
Establish `h1 : IsOpen {y : InfiniteAdeleRing F | ∀ w, ‖y w‖ < 1}`. Establish `e : {y : InfiniteAdeleRing F | ∀ w, ‖y w‖ < 1} = Set.pi Set.univ (fun _ => Metric.ball 0 1)`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce `h w _`.

Simplify `h w` using `[mem_ball_zero_iff]`. Introduce `h w`. Simplify `h w (Set.mem_univ w)` using `[mem_ball_zero_iff]`. Rewrite using `[e]`. Conclude with `isOpen_set_pi Set.finite_univ (fun w _ => Metric.isOpen_ball)`.

Establish `h2 : IsOpen {y : FiniteAdeleRing (𝓞 F) F | ∀ v, y v ∈ v.adicCompletionIntegers F}`. Apply `RestrictedProduct.isOpen_forall_mem` to reduce the goal to its premises. Introduce `v`. Use `first`. Consider the case `exact IsDedekindDomain.HeightOneSpectrum.isOpen_adicCompletionIntegers F v`.

Consider the case `exact v.isOpen_adicCompletionIntegers F`. Consider the case `exact Valued.isOpen_integer _`. Consider the case `exact Valued.integer_isOpen _`. Conclude with `h1.prod h2`.
-/
theorem adl_isOpen_nbhd : IsOpen (adlNbhd F) := by
  have h1 : IsOpen {y : InfiniteAdeleRing F | ∀ w, ‖y w‖ < 1} := by
    have e : {y : InfiniteAdeleRing F | ∀ w, ‖y w‖ < 1} = Set.pi Set.univ (fun _ => Metric.ball 0 1) := by
      ext y
      constructor
      · intro h w _
        simpa [mem_ball_zero_iff] using h w
      · intro h w
        simpa [mem_ball_zero_iff] using h w (Set.mem_univ w)
    rw [e]
    exact isOpen_set_pi Set.finite_univ (fun w _ => Metric.isOpen_ball)
  have h2 : IsOpen {y : FiniteAdeleRing (𝓞 F) F | ∀ v, y v ∈ v.adicCompletionIntegers F} := by
    apply RestrictedProduct.isOpen_forall_mem
    intro v
    first
      | exact IsDedekindDomain.HeightOneSpectrum.isOpen_adicCompletionIntegers F v
      | exact v.isOpen_adicCompletionIntegers F
      | exact Valued.isOpen_integer _
      | exact Valued.integer_isOpen _
  exact h1.prod h2

/- English proof (translation)
Use `⟨fun w => ?_, fun v => ?_⟩` and prove the remaining obligations. Establish `h0 : (0 : AdeleRing (𝓞 F) F).1 w = 0` using `rfl`. Rewrite using `[h0, norm_zero]`. Conclude with `one_pos`. Apply the tactic sequence `first | exact zero_mem _ | simp`.
-/
theorem adl_zero_mem_nbhd : (0 : AdeleRing (𝓞 F) F) ∈ adlNbhd F := by
  refine ⟨fun w => ?_, fun v => ?_⟩
  · have h0 : (0 : AdeleRing (𝓞 F) F).1 w = 0 := rfl
    rw [h0, norm_zero]
    exact one_pos
  · first | exact zero_mem _ | simp

/- English proof (translation)
Simplify using `[InfiniteAdeleRing.algebraMap_apply]`. Apply the tactic sequence `first | rfl | simp [WithAbs.equiv, WithAbs.toAbs]`.
-/
theorem adl_norm_algebraMap (x : F) (w : InfinitePlace F) :
    ‖(algebraMap F (InfiniteAdeleRing F) x) w‖ = w x := by
  simp [InfiniteAdeleRing.algebraMap_apply]
  first | rfl | simp [WithAbs.equiv, WithAbs.toAbs]

/- English proof (translation)
Take `⟨hinf, hfin⟩` from `ha`. Choose the witnesses or unpack the hypotheses as in `⟨r, hr⟩ : ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = a := by`. Apply `IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one` to reduce the goal to its premises. Introduce `v`. Establish `hv` using `hfin v`.

Rewrite `hv` using `[IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]`. Establish `e : (algebraMap F (AdeleRing (𝓞 F) F) a).2 v = (a : v.adicCompletion F)` using `rfl`. Rewrite `hv` using `[e, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Conclude with `hv`. Assume the negation of the conclusion as `ha0`.

Establish `hr0 : r ≠ 0`. Introduce and unpack `rfl`. Apply `ha0` to reduce the goal to its premises. Rewrite using `[← hr, map_zero]`. Take `⟨w, hw⟩` from `adl_exists_place_ge_one r hr0`.

Establish `h1` using `hinf w`. Establish `e1 : (algebraMap F (AdeleRing (𝓞 F) F) a).1 w = (algebraMap F (InfiniteAdeleRing F) a) w` using `rfl`. Rewrite `h1` using `[e1, adl_norm_algebraMap, ← hr]`. Establish `h2 : w (r : F) < 1` using `h1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem adl_eq_zero_of_mem_nbhd (a : F) (ha : algebraMap F (AdeleRing (𝓞 F) F) a ∈ adlNbhd F) : a = 0 := by
  obtain ⟨hinf, hfin⟩ := ha
  obtain ⟨r, hr⟩ : ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = a := by
    apply IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro v
    have hv := hfin v
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at hv
    have e : (algebraMap F (AdeleRing (𝓞 F) F) a).2 v = (a : v.adicCompletion F) := rfl
    rw [e, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
    exact hv
  by_contra ha0
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply ha0
    rw [← hr, map_zero]
  obtain ⟨w, hw⟩ := adl_exists_place_ge_one r hr0
  have h1 := hinf w
  have e1 : (algebraMap F (AdeleRing (𝓞 F) F) a).1 w = (algebraMap F (InfiniteAdeleRing F) a) w := rfl
  rw [e1, adl_norm_algebraMap, ← hr] at h1
  have h2 : w (r : F) < 1 := h1
  linarith

/- English proof (translation)
Set `b` to `mixedEmbedding.latticeBasis F`. Set `R : ℝ` to `∑ i, ‖b i‖`. Establish `hcoord : ∀ (x : InfiniteAdeleRing F) (w : InfinitePlace F), ‖x w‖ ≤ ‖InfiniteAdeleRing.ringEquiv_mixedSpace F x‖`. Introduce `x w`. Rewrite using `[InfiniteAdeleRing.ringEquiv_mixedSpace_apply]`.

Distinguish the cases in `hw : w.IsReal`. Use `le_trans ?_ (norm_fst_le _)` and prove the remaining obligations. Use `le_trans ?_ (norm_le_pi_norm _ ⟨w, hw⟩)` and prove the remaining obligations. Conclude with `((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) (x w)).ge`. Use `le_trans ?_ (norm_snd_le _)` and prove the remaining obligations.

Use `le_trans ?_ (norm_le_pi_norm _ ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp hw⟩)` and prove the remaining obligations. Conclude with `((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) (x w)).ge`. Establish `hK : ∀ w : InfinitePlace F, IsCompact {z : w.Completion | ‖z‖ ≤ R}`. Introduce `w`. Establish `he : {z : w.Completion | ‖z‖ ≤ R} = (InfinitePlace.Completion.extensionEmbedding w) ⁻¹' Metric.closedBall 0 R`.

Use extensionality with `z`. Simplify using `only [Set.mem_setOf_eq, Set.mem_preimage, mem_closedBall_zero_iff, (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _)]`. Rewrite using `[he]`. Conclude with `(InfinitePlace.Completion.isometry_extensionEmbedding w).isClosedEmbedding.isCompact_preimage (isCompact_closedBall 0 R)`. Use `⟨Set.pi Set.univ fun w => {z : w.Completion | ‖z‖ ≤ R}, isCompact_univ_pi hK, ?_⟩` and prove the remaining obligations.

Introduce `y`. Take `⟨r, hr⟩` from `RingHom.mem_range.mp ((mixedEmbedding.mem_span_latticeBasis (K := F)).mp (ZSpan.floor b (InfiniteAdeleRing.ringEquiv_mixedSpace F y)).2)`. Use `⟨r, fun w _ => ?_⟩` and prove the remaining obligations. Use `show ‖(y - algebraMap F _ (r : F)) w‖ ≤ R`. Use `(hcoord _ w).trans ?_` and prove the remaining obligations.

Rewrite using `[map_sub, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]`. Establish `h2 : mixedEmbedding F (r : F) = (ZSpan.floor b (InfiniteAdeleRing.ringEquiv_mixedSpace F y) : mixedEmbedding.mixedSpace F)` using `hr`. Rewrite using `[h2, ← ZSpan.fract_apply]`. Conclude with `ZSpan.norm_fract_le b _`.
-/
theorem adl_inf_cocompact : ∃ C : Set (InfiniteAdeleRing F), IsCompact C ∧
    ∀ y, ∃ r : 𝓞 F, y - algebraMap F _ (r : F) ∈ C := by
  classical
  let b := mixedEmbedding.latticeBasis F
  let R : ℝ := ∑ i, ‖b i‖

  have hcoord : ∀ (x : InfiniteAdeleRing F) (w : InfinitePlace F),
      ‖x w‖ ≤ ‖InfiniteAdeleRing.ringEquiv_mixedSpace F x‖ := by
    intro x w
    rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    by_cases hw : w.IsReal
    · refine le_trans ?_ (norm_fst_le _)
      refine le_trans ?_ (norm_le_pi_norm _ ⟨w, hw⟩)
      exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
        (map_zero _) (x w)).ge
    · refine le_trans ?_ (norm_snd_le _)
      refine le_trans ?_ (norm_le_pi_norm _ ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp hw⟩)
      exact ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
        (map_zero _) (x w)).ge
  have hK : ∀ w : InfinitePlace F, IsCompact {z : w.Completion | ‖z‖ ≤ R} := by
    intro w
    have he : {z : w.Completion | ‖z‖ ≤ R} =
        (InfinitePlace.Completion.extensionEmbedding w) ⁻¹' Metric.closedBall 0 R := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_preimage, mem_closedBall_zero_iff,
        (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _)]
    rw [he]
    exact (InfinitePlace.Completion.isometry_extensionEmbedding w).isClosedEmbedding.isCompact_preimage
      (isCompact_closedBall 0 R)
  refine ⟨Set.pi Set.univ fun w => {z : w.Completion | ‖z‖ ≤ R}, isCompact_univ_pi hK, ?_⟩
  intro y
  obtain ⟨r, hr⟩ := RingHom.mem_range.mp ((mixedEmbedding.mem_span_latticeBasis (K := F)).mp
    (ZSpan.floor b (InfiniteAdeleRing.ringEquiv_mixedSpace F y)).2)
  refine ⟨r, fun w _ => ?_⟩
  show ‖(y - algebraMap F _ (r : F)) w‖ ≤ R
  refine (hcoord _ w).trans ?_
  rw [map_sub, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  have h2 : mixedEmbedding F (r : F) =
      (ZSpan.floor b (InfiniteAdeleRing.ringEquiv_mixedSpace F y) : mixedEmbedding.mixedSpace F) := hr
  rw [h2, ← ZSpan.fract_apply]
  exact ZSpan.norm_fract_le b _

/- English proof (translation)
Take `⟨C, hC, hCy⟩` from `adl_inf_cocompact (F := F)`. Use `⟨C ×ˢ {x : FiniteAdeleRing (𝓞 F) F | ∀ v, x v ∈ v.adicCompletionIntegers F}, hC.prod (finiteAdeleIntegers_compactOpen F).2, fun x => ?_⟩` and prove the remaining obligations. Take `⟨u, hu⟩` from `Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_sub_mem_intAd x.2`. Take `⟨r, hr⟩` from `hCy (x.1 - algebraMap F _ u)`. Use `⟨u + r, ?_, ?_⟩` and prove the remaining obligations.

Use `show x.1 - algebraMap F (InfiniteAdeleRing F) (u + r) ∈ C`. Rewrite using `[map_add, ← sub_sub]`. Conclude with `hr`. Establish `: x.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) (u + r) = (x.2 - algebraMap F _ u) - algebraMap F _ (r : F)` using `by rw [map_add, sub_sub] show ∀ v, (x.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) (u + r)) v ∈ _`. Rewrite using `[this]`.

Conclude with `sub_mem hu (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.algebraMap_mem_intAd r)`.
-/
theorem adl_cocompact : ∃ K : Set (AdeleRing (𝓞 F) F), IsCompact K ∧
    ∀ x, ∃ a : F, x - algebraMap F _ a ∈ K := by
  obtain ⟨C, hC, hCy⟩ := adl_inf_cocompact (F := F)
  refine ⟨C ×ˢ {x : FiniteAdeleRing (𝓞 F) F | ∀ v, x v ∈ v.adicCompletionIntegers F},
    hC.prod (finiteAdeleIntegers_compactOpen F).2, fun x => ?_⟩
  obtain ⟨u, hu⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_sub_mem_intAd x.2
  obtain ⟨r, hr⟩ := hCy (x.1 - algebraMap F _ u)
  refine ⟨u + r, ?_, ?_⟩
  · show x.1 - algebraMap F (InfiniteAdeleRing F) (u + r) ∈ C
    rw [map_add, ← sub_sub]
    exact hr
  · have : x.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) (u + r) =
        (x.2 - algebraMap F _ u) - algebraMap F _ (r : F) := by rw [map_add, sub_sub]
    show ∀ v, (x.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) (u + r)) v ∈ _
    rw [this]
    exact sub_mem hu (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.algebraMap_mem_intAd r)

end Formalism.IndefR.Eqv.G5
