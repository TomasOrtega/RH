import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform
import GroundTheory.AutomorphicForms.ReductionIdele
import GroundTheory.AutomorphicForms.GL2.GJGlobalLattice

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Ff

open scoped nonZeroDivisors
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F]

private noncomputable def lw (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (N : ℕ) (ξ : Fin 4 → F) : ℝ :=
  if ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 F)⁰ F) then ((1 + ‖embPi F ξ‖) ^ N)⁻¹ else 0

/- English proof (translation)
Unfold `lw`. Use `split_ifs`. Check the signs of the components of the expression. Conclude with `le_rfl`.
-/
private theorem lw_nonneg (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (N : ℕ) (ξ : Fin 4 → F) : 0 ≤ lw J N ξ := by
  unfold lw
  split_ifs
  · positivity
  · exact le_rfl

/- English proof (translation)
Unfold `wt`. Use `split_ifs`. Check the signs of the components of the expression. Conclude with `le_rfl`.
-/
private theorem wt_nonneg (K : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)) (N : ℕ) (v : V4 F) : 0 ≤ wt K N v := by
  unfold wt
  split_ifs
  · positivity
  · exact le_rfl

/- English proof (translation)
Establish `hrank : Module.finrank ℤ (idealLatticePi (K` using `F) (fun _ : Fin 4 => J)) < N := by`. Rewrite using `[ZLattice.rank ℝ (idealLatticePi (K := F) (fun _ : Fin 4 => J))]`. Conclude with `hN`. Establish `hs` using `ZLattice.summable_norm_pow_inv (idealLatticePi (K := F) (fun _ : Fin 4 => J)) N hrank`. Use `Summable.of_norm_bounded_eventually hs ?_` and prove the remaining obligations.

Use `filter_upwards [(Set.finite_singleton (0 : idealLatticePi (K := F) (fun _ : Fin 4 => J))).compl_mem_cofinite] with z hz`. Establish `hpos : 0 < ‖z‖` using `norm_pos_iff.mpr hz`. Establish `hz' : ‖z‖ = ‖(z : Fin 4 → mixedEmbedding.mixedSpace F)‖` using `rfl`. Rewrite using `[Real.norm_of_nonneg (inv_nonneg.2 (by positivity)), inv_pow, ← hz']`. Use `gcongr`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem summable_lat (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) {N : ℕ}
    (hN : Module.finrank ℝ (Fin 4 → mixedEmbedding.mixedSpace F) < N) :
    Summable fun z : idealLatticePi (K := F) (fun _ : Fin 4 => J) =>
      ((1 + ‖(z : Fin 4 → mixedEmbedding.mixedSpace F)‖) ^ N)⁻¹ := by
  have hrank : Module.finrank ℤ (idealLatticePi (K := F) (fun _ : Fin 4 => J)) < N := by
    rw [ZLattice.rank ℝ (idealLatticePi (K := F) (fun _ : Fin 4 => J))]; exact hN
  have hs := ZLattice.summable_norm_pow_inv (idealLatticePi (K := F) (fun _ : Fin 4 => J)) N hrank
  refine Summable.of_norm_bounded_eventually hs ?_
  filter_upwards [(Set.finite_singleton (0 : idealLatticePi (K := F) (fun _ : Fin 4 => J))).compl_mem_cofinite] with z hz
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hz' : ‖z‖ = ‖(z : Fin 4 → mixedEmbedding.mixedSpace F)‖ := rfl
  rw [Real.norm_of_nonneg (inv_nonneg.2 (by positivity)), inv_pow, ← hz']
  gcongr
  linarith

/- English proof (translation)
Rewrite using `[mem_idealLatticePi]`. Introduce `i`. Conclude with `(mixedEmbedding.mem_idealLattice F J).2 ⟨_, h i, rfl⟩`.
-/
private theorem mem_lat (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (ξ : Fin 4 → F)
    (h : ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 F)⁰ F)) :
    embPi F ξ ∈ idealLatticePi (K := F) (fun _ : Fin 4 => J) := by
  rw [mem_idealLatticePi]
  intro i
  exact (mixedEmbedding.mem_idealLattice F J).2 ⟨_, h i, rfl⟩

/- English proof (translation)
Introduce `_ _ h` and use `funext fun i => (mixedEmbedding F).injective (congrFun h i)`.
-/
private theorem embPi_injective : Function.Injective (embPi F : (Fin 4 → F) → _) := fun _ _ h =>
  funext fun i => (mixedEmbedding F).injective (congrFun h i)

/- English proof (translation)
Establish `hsT : Summable fun ξ : {ξ : Fin 4 → F | ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 F)⁰ F)} => ((1 + ‖embPi F (ξ : Fin 4 → F)‖) ^ N)⁻¹`. Establish `hinj : Function.Injective fun ξ : {ξ : Fin 4 → F | ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 F)⁰ F)} => (⟨embPi F ξ.1, mem_lat J ξ.1 ξ.2⟩ : idealLatticePi (K` using `F) (fun _ : Fin 4 => J)) := fun x y h => Subtype.ext (embPi_injective (congrArg Subtype.val h))`. Establish `h` using `(summable_lat J hN).comp_injective hinj`. Use `h.congr fun ξ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`.

Establish `heq : lw (F` using `F) J N = Set.indicator {ξ : Fin 4 → F | ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 F)⁰ F)} (fun ξ => ((1 + ‖embPi F ξ‖) ^ N)⁻¹) := by`. Use function extensionality and compare the values at `ξ`. Unfold `lw`. Distinguish the cases in `h : ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 F)⁰ F)`. Rewrite using `[if_pos h, Set.indicator_of_mem (show ξ ∈ {ξ : Fin 4 → F | ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 F)⁰ F)} from h)]`.

Rewrite using `[if_neg h, Set.indicator_of_notMem (show ξ ∉ {ξ : Fin 4 → F | ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 F)⁰ F)} from h)]`. Rewrite using `[heq, ← summable_subtype_iff_indicator]`. Conclude with `hsT`.
-/
private theorem summable_lw (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) {N : ℕ}
    (hN : Module.finrank ℝ (Fin 4 → mixedEmbedding.mixedSpace F) < N) : Summable (lw J N) := by
  have hsT : Summable fun ξ : {ξ : Fin 4 → F | ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 F)⁰ F)} =>
      ((1 + ‖embPi F (ξ : Fin 4 → F)‖) ^ N)⁻¹ := by
    have hinj : Function.Injective fun ξ : {ξ : Fin 4 → F | ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 F)⁰ F)} =>
        (⟨embPi F ξ.1, mem_lat J ξ.1 ξ.2⟩ : idealLatticePi (K := F) (fun _ : Fin 4 => J)) := fun x y h =>
      Subtype.ext (embPi_injective (congrArg Subtype.val h))
    have h := (summable_lat J hN).comp_injective hinj
    refine h.congr fun ξ => ?_
    simp only [Function.comp_apply]
  have heq : lw (F := F) J N = Set.indicator {ξ : Fin 4 → F | ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 F)⁰ F)}
      (fun ξ => ((1 + ‖embPi F ξ‖) ^ N)⁻¹) := by
    funext ξ
    unfold lw
    by_cases h : ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 F)⁰ F)
    · rw [if_pos h, Set.indicator_of_mem (show ξ ∈ {ξ : Fin 4 → F | ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 F)⁰ F)} from h)]
    · rw [if_neg h, Set.indicator_of_notMem (show ξ ∉ {ξ : Fin 4 → F | ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 F)⁰ F)} from h)]
  rw [heq, ← summable_subtype_iff_indicator]
  exact hsT

/- English proof (translation)
Establish `hc : Continuous fun u : IdeleGroup F => ∑ w : InfinitePlace F, ‖(((u⁻¹ : IdeleGroup F) : A F)).1 w‖` using `continuous_finset_sum _ fun w _ => continuous_norm.comp ((continuous_apply w).comp (continuous_fst.comp Units.continuous_coe_inv))`. Take `⟨M, hM⟩` from `hS.exists_bound_of_continuousOn hc.continuousOn`. Use `set b := max M 1`. Establish `hb1 : 1 ≤ b` using `le_max_right _ _`. Use `set n : ℝ := (Fintype.card (InfinitePlace F) : ℝ)`.

Establish `hn : 0 ≤ n` using `Nat.cast_nonneg _`. Use `⟨n * b + 1, by nlinarith, fun s hs hs1 u hu η => ?_⟩` and prove the remaining obligations. Use `set y := (((posIdele s hs * u : IdeleGroup F) : A F) * rt η).1`. Establish `hub : ∀ w, ‖(((u⁻¹ : IdeleGroup F) : A F)).1 w‖ ≤ b` using `fun w => by`. Use `le_trans ?_ ((le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hM u hu).trans (le_max_left _ _)))` and prove the remaining obligations.

Conclude with `Finset.single_le_sum (f := fun w : InfinitePlace F => ‖(((u⁻¹ : IdeleGroup F) : A F)).1 w‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ w)`. Establish `hw : ∀ w, ‖(rt η : A F).1 w‖ ≤ b * ‖homeomorphMixedSpace F y‖` using `fun w => by`. Establish `e1 : y w = ((posIdele s hs : IdeleGroup F) : A F).1 w * (((u : IdeleGroup F) : A F) * rt η).1 w`. Simplify using `only [y, Units.val_mul, mul_assoc]`. Both sides reduce to the same expression.

Establish `e2 : (rt η : A F).1 w = (((u⁻¹ : IdeleGroup F) : A F)).1 w * (((u : IdeleGroup F) : A F) * rt η).1 w`. Establish `: (rt η : A F) = ((u⁻¹ : IdeleGroup F) : A F) * (((u : IdeleGroup F) : A F) * rt η)`. Rewrite using `[← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]`. Conclude with `congrArg (fun z : A F => z.1 w) this`. Establish `e3 : ‖(((u : IdeleGroup F) : A F) * rt η).1 w‖ ≤ ‖y w‖`.

Rewrite using `[e1, norm_mul, norm_posIdele_infinite]`. Use polynomial arithmetic with `[norm_nonneg ((((u : IdeleGroup F) : A F) * rt η).1 w)]`. Rewrite using `[e2, norm_mul]`. Conclude with `mul_le_mul (hub w) (e3.trans (GJGlobal.norm_apply_le_norm_homeomorphMixedSpace y w)) (norm_nonneg _) (by linarith)`. Establish `h1 : ‖mixedEmbedding F η‖ ≤ ∑ w : InfinitePlace F, ‖(rt η : A F).1 w‖`.

Use `GJGlobal.norm_homeomorphMixedSpace_le_sum (algebraMap F (InfiniteAdeleRing F) η)` as an intermediate fact. Rewrite `this` using `[homeomorphMixedSpace_algebraMap]`. Conclude with `this`. Establish `h2 : ∑ w : InfinitePlace F, ‖(rt η : A F).1 w‖ ≤ n * (b * ‖homeomorphMixedSpace F y‖)`. Use `(Finset.sum_le_sum fun w _ => hw w).trans_eq ?_` and prove the remaining obligations.

Simplify using `[n, Finset.card_univ]`. Use polynomial arithmetic with `[norm_nonneg (homeomorphMixedSpace F y)]`.
-/
private theorem mixed_le {S : Set (IdeleGroup F)} (hS : IsCompact S) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (s : ℝ) (hs : 0 < s), 1 ≤ s → ∀ u ∈ S, ∀ η : F,
      ‖mixedEmbedding F η‖ ≤ B * ‖homeomorphMixedSpace F
        ((((posIdele s hs * u : IdeleGroup F) : A F) * rt η).1)‖ := by
  have hc : Continuous fun u : IdeleGroup F => ∑ w : InfinitePlace F, ‖(((u⁻¹ : IdeleGroup F) : A F)).1 w‖ :=
    continuous_finset_sum _ fun w _ => continuous_norm.comp
      ((continuous_apply w).comp (continuous_fst.comp Units.continuous_coe_inv))
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hc.continuousOn
  set b := max M 1
  have hb1 : 1 ≤ b := le_max_right _ _
  set n : ℝ := (Fintype.card (InfinitePlace F) : ℝ)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  refine ⟨n * b + 1, by nlinarith, fun s hs hs1 u hu η => ?_⟩
  set y := (((posIdele s hs * u : IdeleGroup F) : A F) * rt η).1
  have hub : ∀ w, ‖(((u⁻¹ : IdeleGroup F) : A F)).1 w‖ ≤ b := fun w => by
    refine le_trans ?_ ((le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hM u hu).trans (le_max_left _ _)))
    exact Finset.single_le_sum (f := fun w : InfinitePlace F => ‖(((u⁻¹ : IdeleGroup F) : A F)).1 w‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
  have hw : ∀ w, ‖(rt η : A F).1 w‖ ≤ b * ‖homeomorphMixedSpace F y‖ := fun w => by
    have e1 : y w = ((posIdele s hs : IdeleGroup F) : A F).1 w * (((u : IdeleGroup F) : A F) * rt η).1 w := by
      simp only [y, Units.val_mul, mul_assoc]
      rfl
    have e2 : (rt η : A F).1 w = (((u⁻¹ : IdeleGroup F) : A F)).1 w * (((u : IdeleGroup F) : A F) * rt η).1 w := by
      have : (rt η : A F) = ((u⁻¹ : IdeleGroup F) : A F) * (((u : IdeleGroup F) : A F) * rt η) := by
        rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
      exact congrArg (fun z : A F => z.1 w) this
    have e3 : ‖(((u : IdeleGroup F) : A F) * rt η).1 w‖ ≤ ‖y w‖ := by
      rw [e1, norm_mul, norm_posIdele_infinite]
      nlinarith [norm_nonneg ((((u : IdeleGroup F) : A F) * rt η).1 w)]
    rw [e2, norm_mul]
    exact mul_le_mul (hub w) (e3.trans (GJGlobal.norm_apply_le_norm_homeomorphMixedSpace y w)) (norm_nonneg _)
      (by linarith)
  have h1 : ‖mixedEmbedding F η‖ ≤ ∑ w : InfinitePlace F, ‖(rt η : A F).1 w‖ := by
    have := GJGlobal.norm_homeomorphMixedSpace_le_sum (algebraMap F (InfiniteAdeleRing F) η)
    rw [homeomorphMixedSpace_algebraMap] at this
    exact this
  have h2 : ∑ w : InfinitePlace F, ‖(rt η : A F).1 w‖ ≤ n * (b * ‖homeomorphMixedSpace F y‖) := by
    refine (Finset.sum_le_sum fun w _ => hw w).trans_eq ?_
    simp [n, Finset.card_univ]
  nlinarith [norm_nonneg (homeomorphMixedSpace F y)]

/- English proof (translation)
Use `set Kf : Set (FiniteAdeleRing (𝓞 F) F) := ⋃ i : Fin 4, (fun k : Fin 4 → FiniteAdeleRing (𝓞 F) F => k i) '' K`. Establish `hKf : IsCompact Kf` using `isCompact_iUnion fun i => hK.image (continuous_apply i)`. Use `set Q : Set (FiniteAdeleRing (𝓞 F) F) := (fun p : IdeleGroup F × FiniteAdeleRing (𝓞 F) F => (((p.1⁻¹ : IdeleGroup F) : A F)).2 * p.2) '' (S ×ˢ Kf)`. Establish `hi : Continuous fun u : IdeleGroup F => (((u⁻¹ : IdeleGroup F) : A F)).2` using `continuous_snd.comp Units.continuous_coe_inv`. Establish `hQ : IsCompact Q` using `(hS.prod hKf).image ((hi.comp continuous_fst).mul continuous_snd)`.

Take `⟨d, hd0, hd⟩` from `exists_mul_mem_integralFiniteAdeles_of_isCompact hQ`. Use `set dK := algebraMap (𝓞 F) F d`. Establish `hdK : dK ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hd0`. Use `⟨Units.mk0 (FractionalIdeal.spanSingleton (𝓞 F)⁰ dK⁻¹) ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr (inv_ne_zero hdK)), fun s hs u hu η hη i => ?_⟩` and prove the remaining obligations. Establish `hp : (((posIdele s hs : IdeleGroup F) : A F)).2 = 1`.

Apply `RestrictedProduct.ext` to reduce the goal to its premises. Introduce `v`. Conclude with `posIdele_finite s hs v`. Establish `hmem : algebraMap F (FiniteAdeleRing (𝓞 F) F) (η i) ∈ Q`. Use `⟨(u, finPartPi (sc (posIdele s hs * u) η) i), ⟨hu, Set.mem_iUnion.2 ⟨i, _, hη, rfl⟩⟩, ?_⟩` and prove the remaining obligations.

Establish `e1 : finPartPi (sc (posIdele s hs * u) η) i = (((u : IdeleGroup F) : A F)).2 * algebraMap F (FiniteAdeleRing (𝓞 F) F) (η i)`. Express the relevant statement in the definitionally equal form `((((posIdele s hs * u : IdeleGroup F) : A F)) * rt (η i)).2 = _`. Rewrite using `[Units.val_mul, mul_assoc]`. Express the relevant statement in the definitionally equal form `(((posIdele s hs : IdeleGroup F) : A F)).2 * _ = _`. Rewrite using `[hp, one_mul]`.

Both sides reduce to the same expression. Establish `e2 : (((u⁻¹ : IdeleGroup F) : A F)).2 * (((u : IdeleGroup F) : A F)).2 = 1` using `congrArg Prod.snd (Units.inv_mul u)`. Express the relevant statement in the definitionally equal form `(((u⁻¹ : IdeleGroup F) : A F)).2 * finPartPi (sc (posIdele s hs * u) η) i = _`. Rewrite using `[e1, ← mul_assoc, e2, one_mul]`. Establish `h1` using `hd _ hmem`.

Rewrite `h1` using `[← map_mul]`. Establish `h2 : dK * η i ∈ ((1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F)`. Rewrite using `[← algebraMap_mem_idealFiniteAdeles_iff, ← SetLike.mem_coe, idealFiniteAdeles_one]`. Conclude with `h1`. Rewrite `h2` using `[Units.val_one]`.

Take `⟨r, hr⟩` from `(FractionalIdeal.mem_one_iff _).mp h2`. Use `(FractionalIdeal.mem_spanSingleton _).mpr ⟨r, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, hr, mul_comm dK, mul_assoc, mul_inv_cancel₀ hdK, mul_one]`.
-/
private theorem fin_mem {K : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)} (hK : IsCompact K)
    {S : Set (IdeleGroup F)} (hS : IsCompact S) :
    ∃ J : (FractionalIdeal (𝓞 F)⁰ F)ˣ, ∀ (s : ℝ) (hs : 0 < s), ∀ u ∈ S, ∀ η : Fin 4 → F,
      finPartPi (sc (posIdele s hs * u) η) ∈ K → ∀ i, η i ∈ (J : FractionalIdeal (𝓞 F)⁰ F) := by
  set Kf : Set (FiniteAdeleRing (𝓞 F) F) := ⋃ i : Fin 4, (fun k : Fin 4 → FiniteAdeleRing (𝓞 F) F => k i) '' K
  have hKf : IsCompact Kf := isCompact_iUnion fun i => hK.image (continuous_apply i)
  set Q : Set (FiniteAdeleRing (𝓞 F) F) :=
    (fun p : IdeleGroup F × FiniteAdeleRing (𝓞 F) F => (((p.1⁻¹ : IdeleGroup F) : A F)).2 * p.2) '' (S ×ˢ Kf)
  have hi : Continuous fun u : IdeleGroup F => (((u⁻¹ : IdeleGroup F) : A F)).2 :=
    continuous_snd.comp Units.continuous_coe_inv
  have hQ : IsCompact Q := (hS.prod hKf).image ((hi.comp continuous_fst).mul continuous_snd)
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hQ
  set dK := algebraMap (𝓞 F) F d
  have hdK : dK ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hd0
  refine ⟨Units.mk0 (FractionalIdeal.spanSingleton (𝓞 F)⁰ dK⁻¹)
    ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr (inv_ne_zero hdK)), fun s hs u hu η hη i => ?_⟩
  have hp : (((posIdele s hs : IdeleGroup F) : A F)).2 = 1 := by
    apply RestrictedProduct.ext
    intro v
    exact posIdele_finite s hs v
  have hmem : algebraMap F (FiniteAdeleRing (𝓞 F) F) (η i) ∈ Q := by
    refine ⟨(u, finPartPi (sc (posIdele s hs * u) η) i),
      ⟨hu, Set.mem_iUnion.2 ⟨i, _, hη, rfl⟩⟩, ?_⟩
    have e1 : finPartPi (sc (posIdele s hs * u) η) i =
        (((u : IdeleGroup F) : A F)).2 * algebraMap F (FiniteAdeleRing (𝓞 F) F) (η i) := by
      change ((((posIdele s hs * u : IdeleGroup F) : A F)) * rt (η i)).2 = _
      rw [Units.val_mul, mul_assoc]
      change (((posIdele s hs : IdeleGroup F) : A F)).2 * _ = _
      rw [hp, one_mul]
      rfl
    have e2 : (((u⁻¹ : IdeleGroup F) : A F)).2 * (((u : IdeleGroup F) : A F)).2 = 1 :=
      congrArg Prod.snd (Units.inv_mul u)
    change (((u⁻¹ : IdeleGroup F) : A F)).2 * finPartPi (sc (posIdele s hs * u) η) i = _
    rw [e1, ← mul_assoc, e2, one_mul]
  have h1 := hd _ hmem
  rw [← map_mul] at h1
  have h2 : dK * η i ∈ ((1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [← algebraMap_mem_idealFiniteAdeles_iff, ← SetLike.mem_coe, idealFiniteAdeles_one]
    exact h1
  rw [Units.val_one] at h2
  obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp h2
  refine (FractionalIdeal.mem_spanSingleton _).mpr ⟨r, ?_⟩
  rw [Algebra.smul_def, hr, mul_comm dK, mul_assoc, mul_inv_cancel₀ hdK, mul_one]

/- English proof (translation)
Establish `hB0 : 0 < B` using `one_pos.trans_le hB`. Distinguish the cases in `h : finPartPi (sc a η) ∈ K`. Unfold `wt lw`. Rewrite using `[if_pos h, if_pos (hfin η h)]`. Establish `h1 : ‖embPi F η‖ ≤ B * ‖infPartPi (sc a η)‖` using `(pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (hinf (η i)).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm (infPartPi (sc a η)) i) hB0.le)`.

Establish `h2 : 1 + ‖embPi F η‖ ≤ B * (1 + ‖infPartPi (sc a η)‖)` using `by linarith`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]`. Use `_ ≤ B ^ N * ((1 + ‖embPi F η‖) ^ N)⁻¹ := by gcongr`. Unfold `wt`.

Rewrite using `[if_neg h]`. Conclude with `mul_nonneg (by positivity) (lw_nonneg _ _ _)`.
-/
private theorem wt_le {K : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)} {J : (FractionalIdeal (𝓞 F)⁰ F)ˣ}
    {B : ℝ} (hB : 1 ≤ B) {a : (A F)ˣ}
    (hfin : ∀ η : Fin 4 → F, finPartPi (sc a η) ∈ K → ∀ i, η i ∈ (J : FractionalIdeal (𝓞 F)⁰ F))
    (hinf : ∀ η : F, ‖mixedEmbedding F η‖ ≤ B * ‖homeomorphMixedSpace F (((a : A F) * rt η).1)‖)
    (N : ℕ) (η : Fin 4 → F) : wt K N (sc a η) ≤ B ^ N * lw J N η := by
  have hB0 : 0 < B := one_pos.trans_le hB
  by_cases h : finPartPi (sc a η) ∈ K
  · unfold wt lw
    rw [if_pos h, if_pos (hfin η h)]
    have h1 : ‖embPi F η‖ ≤ B * ‖infPartPi (sc a η)‖ :=
      (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (hinf (η i)).trans
        (mul_le_mul_of_nonneg_left (norm_le_pi_norm (infPartPi (sc a η)) i) hB0.le)
    have h2 : 1 + ‖embPi F η‖ ≤ B * (1 + ‖infPartPi (sc a η)‖) := by linarith
    calc ((1 + ‖infPartPi (sc a η)‖) ^ N)⁻¹ = B ^ N * ((B * (1 + ‖infPartPi (sc a η)‖)) ^ N)⁻¹ := by
          rw [mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
      _ ≤ B ^ N * ((1 + ‖embPi F η‖) ^ N)⁻¹ := by gcongr
  · unfold wt
    rw [if_neg h]
    exact mul_nonneg (by positivity) (lw_nonneg _ _ _)

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.R2.Ff

open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction in
/- English proof (translation)
Introduce `F _ _`. Use `⟨Module.finrank ℝ (Fin 4 → mixedEmbedding.mixedSpace F) + 1, fun K hK c hc => ?_⟩` and prove the remaining obligations. Use `set N := Module.finrank ℝ (Fin 4 → mixedEmbedding.mixedSpace F) + 1 with hNdef`. Take `⟨S, hS, hSm⟩` from `exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := F) hc c`. Take `⟨J, hJ⟩` from `fin_mem hK hS`.

Take `⟨B, hB1, hB⟩` from `mixed_le hS`. Establish `hsum : Summable (lw J N)` using `summable_lw J (Nat.lt_succ_self _)`. Establish `hB0 : 0 ≤ B ^ N` using `pow_nonneg (zero_le_one.trans hB1) _`. Use `⟨B ^ N * ∑' ξ, lw J N ξ, fun a ha => ?_⟩` and prove the remaining obligations. Use `set d := Module.finrank ℚ F`.

Establish `hd : d ≠ 0` using `Module.finrank_pos.ne'`. Establish `hx : 1 ≤ ab a / c` using `(one_le_div hc).2 ha`. Use `set s := (ab a / c) ^ (d : ℝ)⁻¹`. Establish `hs1 : 1 ≤ s` using `Real.one_le_rpow hx (by positivity)`. Establish `hs0 : 0 < s` using `one_pos.trans_le hs1`.

Establish `hsd : s ^ d = ab a / c` using `Real.rpow_inv_natCast_pow (zero_le_one.trans hx) hd`. Use `set p : IdeleGroup F := posIdele s hs0 with hp`. Establish `hm : (IdeleGroup.ideleModule F (p⁻¹ * a) : ℝ) = c`. Establish `h1 : (IdeleGroup.ideleModule F (p⁻¹ * a) : ℝ) = ((IdeleGroup.ideleModule F p : ℝ))⁻¹ * (IdeleGroup.ideleModule F a : ℝ)`. Simplify using `[map_mul, map_inv]`.

Establish `h2 : (0 : ℝ) < ab a` using `hc.trans_le ha`. Rewrite using `[h1, hp, ideleModule_posIdele, hsd]`. Express the relevant statement in the definitionally equal form `(ab a / c)⁻¹ * ab a = c`. Clear the denominators using the available nonvanishing facts. Take `⟨t, ht⟩` from `hSm _ hm.ge hm.le`.

Use `set u := IdeleGroup.diagonal F t * (p⁻¹ * a) with hu`. Establish `hau : IdeleGroup.diagonal F t * a = p * u`. Rewrite using `[hu, mul_left_comm, mul_inv_cancel_left]`. Set `e : (Fin 4 → F) ≃ (Fin 4 → F)` to `Equiv.piCongrRight fun _ => Units.mulLeft t`. Establish `hsc : ∀ ξ, sc a (e ξ) = sc (p * u) ξ` using `fun ξ => by`.

Use function extensionality and compare the values at `i`. Establish `h1 : ((IdeleGroup.diagonal F t : IdeleGroup F) : A F) = rt (t : F)` using `IdeleGroup.coe_diagonal _ _`. Establish `h2 : ((p * u : IdeleGroup F) : A F) = (a : A F) * rt (t : F)`. Rewrite using `[← hau, Units.val_mul, h1, mul_comm]`. Express the relevant statement in the definitionally equal form `(a : A F) * rt ((t : F) * ξ i) = ((p * u : IdeleGroup F) : A F) * rt (ξ i)`.

Rewrite using `[h2, show rt ((t : F) * ξ i) = rt (t : F) * rt (ξ i) from map_mul _ _ _, mul_assoc]`. Establish `hle : ∀ ξ, wt K N (sc a (e ξ)) ≤ B ^ N * lw J N ξ` using `fun ξ => by`. Rewrite using `[hsc]`. Conclude with `wt_le hB1 (hJ s hs0 u ht) (hB s hs0 hs1 u ht) N ξ`. Establish `hs' : Summable fun ξ => wt K N (sc a (e ξ))` using `Summable.of_nonneg_of_le (fun _ => wt_nonneg _ _ _) hle (hsum.mul_left _)`.

Use `⟨e.summable_iff.1 hs', ?_⟩` and prove the remaining obligations. Rewrite using `[← e.tsum_eq, ← tsum_mul_left]`. Conclude with `hs'.tsum_le_tsum hle (hsum.mul_left _)`.
-/
theorem UpperTheory.ConvolutionTheory.R2.Ff.wtSum :
    ∀ (F : Type) [Field F] [NumberField F], WtSum F := by
  intro F _ _
  refine ⟨Module.finrank ℝ (Fin 4 → mixedEmbedding.mixedSpace F) + 1, fun K hK c hc => ?_⟩
  set N := Module.finrank ℝ (Fin 4 → mixedEmbedding.mixedSpace F) + 1 with hNdef
  obtain ⟨S, hS, hSm⟩ := exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := F) hc c
  obtain ⟨J, hJ⟩ := fin_mem hK hS
  obtain ⟨B, hB1, hB⟩ := mixed_le hS
  have hsum : Summable (lw J N) := summable_lw J (Nat.lt_succ_self _)
  have hB0 : 0 ≤ B ^ N := pow_nonneg (zero_le_one.trans hB1) _
  refine ⟨B ^ N * ∑' ξ, lw J N ξ, fun a ha => ?_⟩
  set d := Module.finrank ℚ F
  have hd : d ≠ 0 := Module.finrank_pos.ne'
  have hx : 1 ≤ ab a / c := (one_le_div hc).2 ha
  set s := (ab a / c) ^ (d : ℝ)⁻¹
  have hs1 : 1 ≤ s := Real.one_le_rpow hx (by positivity)
  have hs0 : 0 < s := one_pos.trans_le hs1
  have hsd : s ^ d = ab a / c := Real.rpow_inv_natCast_pow (zero_le_one.trans hx) hd
  set p : IdeleGroup F := posIdele s hs0 with hp
  have hm : (IdeleGroup.ideleModule F (p⁻¹ * a) : ℝ) = c := by
    have h1 : (IdeleGroup.ideleModule F (p⁻¹ * a) : ℝ) =
        ((IdeleGroup.ideleModule F p : ℝ))⁻¹ * (IdeleGroup.ideleModule F a : ℝ) := by
      simp [map_mul, map_inv]
    have h2 : (0 : ℝ) < ab a := hc.trans_le ha
    rw [h1, hp, ideleModule_posIdele, hsd]
    change (ab a / c)⁻¹ * ab a = c
    field_simp
  obtain ⟨t, ht⟩ := hSm _ hm.ge hm.le
  set u := IdeleGroup.diagonal F t * (p⁻¹ * a) with hu
  have hau : IdeleGroup.diagonal F t * a = p * u := by
    rw [hu, mul_left_comm, mul_inv_cancel_left]
  let e : (Fin 4 → F) ≃ (Fin 4 → F) := Equiv.piCongrRight fun _ => Units.mulLeft t
  have hsc : ∀ ξ, sc a (e ξ) = sc (p * u) ξ := fun ξ => by
    funext i
    have h1 : ((IdeleGroup.diagonal F t : IdeleGroup F) : A F) = rt (t : F) := IdeleGroup.coe_diagonal _ _
    have h2 : ((p * u : IdeleGroup F) : A F) = (a : A F) * rt (t : F) := by
      rw [← hau, Units.val_mul, h1, mul_comm]
    change (a : A F) * rt ((t : F) * ξ i) = ((p * u : IdeleGroup F) : A F) * rt (ξ i)
    rw [h2, show rt ((t : F) * ξ i) = rt (t : F) * rt (ξ i) from map_mul _ _ _, mul_assoc]
  have hle : ∀ ξ, wt K N (sc a (e ξ)) ≤ B ^ N * lw J N ξ := fun ξ => by
    rw [hsc]
    exact wt_le hB1 (hJ s hs0 u ht) (hB s hs0 hs1 u ht) N ξ
  have hs' : Summable fun ξ => wt K N (sc a (e ξ)) :=
    Summable.of_nonneg_of_le (fun _ => wt_nonneg _ _ _) hle (hsum.mul_left _)
  refine ⟨e.summable_iff.1 hs', ?_⟩
  rw [← e.tsum_eq, ← tsum_mul_left]
  exact hs'.tsum_le_tsum hle (hsum.mul_left _)
