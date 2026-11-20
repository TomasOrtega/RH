import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitDom
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionNonzeroAdmissible
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaSumAdmissibility

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.WeilM Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory GlobalTheory.CompanionTheory.ThetaCoord
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ContDiff

namespace GlobalTheory.CompanionTheory.ThetaCoord.Cont

variable {F : Type} [Field F] [NumberField F] {κ : Type}

def ratA (ξ : κ → F) : κ → AF F := fun i => algebraMap F (AF F) (ξ i)

/- English proof (translation)
The claim follows from `continuous_pi fun i => continuous_snd.comp (continuous_apply i)`.
-/
theorem continuous_finOf : Continuous (finOf : (κ → AF F) → κ → FiniteAdeleRing (𝓞 F) F) :=
  continuous_pi fun i => continuous_snd.comp (continuous_apply i)

/- English proof (translation)
Use `first`. Consider the case `exact (InfiniteAdeleRing.homeomorph_mixedSpace F).continuous`. Consider the case `(rw [show (InfiniteAdeleRing.ringEquiv_mixedSpace F : InfiniteAdeleRing F → mixedEmbedding.mixedSpace F) = fun x => (fun v : {w : InfinitePlace F // w.IsReal} => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v.1), fun v : {w : InfinitePlace F // w.IsComplex} => Infin …`. Conclude with `Continuous.prodMk (continuous_pi fun v => (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)) (continuous_pi fun v => (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)))`.
-/
private theorem continuous_infiniteAdeleRing_ringEquiv_mixedSpace :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  first
  | exact (InfiniteAdeleRing.homeomorph_mixedSpace F).continuous
  | (rw [show (InfiniteAdeleRing.ringEquiv_mixedSpace F : InfiniteAdeleRing F → mixedEmbedding.mixedSpace F) =
        fun x => (fun v : {w : InfinitePlace F // w.IsReal} =>
          InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v.1),
          fun v : {w : InfinitePlace F // w.IsComplex} =>
          InfinitePlace.Completion.extensionEmbedding v.1 (x v.1)) from rfl]
     exact Continuous.prodMk
      (continuous_pi fun v => (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _))
      (continuous_pi fun v => (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)))

/- English proof (translation)
Conclude with `continuous_pi fun i => continuous_infiniteAdeleRing_ringEquiv_mixedSpace.comp (continuous_fst.comp (continuous_apply i))`.
-/
theorem continuous_infOf : Continuous (infOf : (κ → AF F) → κ → mixedEmbedding.mixedSpace F) := by
  exact continuous_pi fun i => continuous_infiniteAdeleRing_ringEquiv_mixedSpace.comp (continuous_fst.comp (continuous_apply i))

/- English proof (translation)
Use `⟨fun s => ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `Set.indicator_const_preimage V s (1 : ℂ)`. Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff] at h`. Apply the tactic sequence `rcases h with h | h | h | h <;> rw [h]`. Conclude with `isOpen_univ`.

Conclude with `hV.isOpen`. Conclude with `hV.isClosed.isOpen_compl`. Conclude with `isOpen_empty`. Conclude with `HasCompactSupport.intro' hc hV.isClosed fun x hx => by simp [hx]`.
-/
theorem indicator_mem_SB_of_isClopen {X : Type} [TopologicalSpace X] {V : Set X} (hV : IsClopen V) (hc : IsCompact V) :
    V.indicator (fun _ => (1 : ℂ)) ∈ SB X := by
  refine ⟨fun s => ?_, ?_⟩
  · have h := Set.indicator_const_preimage V s (1 : ℂ)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h | h <;> rw [h]
    · exact isOpen_univ
    · exact hV.isOpen
    · exact hV.isClosed.isOpen_compl
    · exact isOpen_empty
  · exact HasCompactSupport.intro' hc hV.isClosed fun x hx => by simp [hx]

/- English proof (translation)
Set `f : FiniteAdeleRing (𝓞 F) F → ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F` to `fun x v => x v`. Establish `hf : Continuous f` using `by first`. Consider the case `exact RestrictedProduct.continuous_coe`. Consider the case `fun_prop`. Establish `hi : Function.Injective f` using `by first`.

Consider the case `exact RestrictedProduct.coe_injective`. Consider the case `exact fun x y h => Subtype.ext h`. Use `⟨fun s _ hs => ?_⟩` and prove the remaining obligations. Establish `h1 : (f '' s).Subsingleton` using `(hs.image f hf.continuousOn).subsingleton`. Conclude with `fun x hx y hy => hi (h1 (Set.mem_image_of_mem f hx) (Set.mem_image_of_mem f hy))`.
-/
private theorem totallyDisconnectedSpace_finiteAdeleRing :
    TotallyDisconnectedSpace (FiniteAdeleRing (𝓞 F) F) := by
  let f : FiniteAdeleRing (𝓞 F) F → ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F := fun x v => x v
  have hf : Continuous f := by
    first
    | exact RestrictedProduct.continuous_coe
    | fun_prop
  have hi : Function.Injective f := by
    first
    | exact RestrictedProduct.coe_injective
    | exact fun x y h => Subtype.ext h
  refine ⟨fun s _ hs => ?_⟩
  have h1 : (f '' s).Subsingleton := (hs.image f hf.continuousOn).subsingleton
  exact fun x hx y hy => hi (h1 (Set.mem_image_of_mem f hx) (Set.mem_image_of_mem f hy))

open GroundTheory.Global in

/- English proof (translation)
Use `haveI := totallyDisconnectedSpace_finiteAdeleRing (F := F)`. Establish `hB : TopologicalSpace.IsTopologicalBasis {s : Set (κ → FiniteAdeleRing (𝓞 F) F) | IsClopen s}` using `loc_compact_Haus_tot_disc_of_zero_dim`. Establish `hx : ∀ x ∈ S, ∃ C : Set (κ → FiniteAdeleRing (𝓞 F) F), IsClopen C ∧ IsCompact C ∧ x ∈ C`. Introduce `x _`. Take `⟨K, hK, hKx⟩` from `exists_compact_mem_nhds x`.

Take `⟨C, hCc, hxC, hCK⟩` from `hB.mem_nhds_iff.1 hKx`. Conclude with `⟨C, hCc, hK.of_isClosed_subset hCc.isClosed hCK, hxC⟩`. Use `choose! C hCc hCk hxC using hx`. Take `⟨t, htS, ht, hcov⟩` from `hS.elim_finite_subcover_image (fun x hx => (hCc x hx).isOpen) (fun x hx => Set.mem_biUnion hx (hxC x hx))`. Use `⟨⋃ x ∈ t, C x, ⟨ht.isClosed_biUnion fun x hx => (hCc x (htS hx)).isClosed, isOpen_biUnion fun x hx => (hCc x (htS hx)).isOpen⟩, ht.isCompact_biUnion fun x hx => hCk x (htS hx), hcov⟩` and prove the remaining obligations.
-/
theorem exists_clopen_superset [Fintype κ] {S : Set (κ → FiniteAdeleRing (𝓞 F) F)} (hS : IsCompact S) :
    ∃ V, IsClopen V ∧ IsCompact V ∧ S ⊆ V := by
  classical
  haveI := totallyDisconnectedSpace_finiteAdeleRing (F := F)
  have hB : TopologicalSpace.IsTopologicalBasis {s : Set (κ → FiniteAdeleRing (𝓞 F) F) | IsClopen s} :=
    loc_compact_Haus_tot_disc_of_zero_dim
  have hx : ∀ x ∈ S, ∃ C : Set (κ → FiniteAdeleRing (𝓞 F) F), IsClopen C ∧ IsCompact C ∧ x ∈ C := by
    intro x _
    obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x
    obtain ⟨C, hCc, hxC, hCK⟩ := hB.mem_nhds_iff.1 hKx
    exact ⟨C, hCc, hK.of_isClosed_subset hCc.isClosed hCK, hxC⟩
  choose! C hCc hCk hxC using hx
  obtain ⟨t, htS, ht, hcov⟩ := hS.elim_finite_subcover_image (fun x hx => (hCc x hx).isOpen)
    (fun x hx => Set.mem_biUnion hx (hxC x hx))
  refine ⟨⋃ x ∈ t, C x, ⟨ht.isClosed_biUnion fun x hx => (hCc x (htS hx)).isClosed,
    isOpen_biUnion fun x hx => (hCc x (htS hx)).isOpen⟩, ht.isCompact_biUnion fun x hx => hCk x (htS hx), hcov⟩

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (InfiniteAdeleRing F) (ξ i) + (a i).1) = mixedEmbedding F (ξ i) + InfiniteAdeleRing.ringEquiv_mixedSpace F (a i).1`. Rewrite using `[map_add, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp F]`.
-/
theorem infOf_ratA_add [Fintype κ] (ξ : κ → F) (a : κ → AF F) :
    infOf (ratA ξ + a) = (fun i => mixedEmbedding F (ξ i) : κ → mixedEmbedding.mixedSpace F) + infOf a := by
  funext i
  show InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (InfiniteAdeleRing F) (ξ i) + (a i).1) =
    mixedEmbedding F (ξ i) + InfiniteAdeleRing.ringEquiv_mixedSpace F (a i).1
  rw [map_add, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp F]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finOf_ratA_add (ξ : κ → F) (a : κ → AF F) :
    finOf (ratA ξ + a) = (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) + finOf a := rfl

open scoped Classical in

/- English proof (translation)
Take `⟨hgl, hgc⟩` from `hg`. Take `⟨M, hM⟩` from `hgl.continuous.bounded_above_of_compact_support hgc`. Establish `hM0 : 0 ≤ M` using `(norm_nonneg _).trans (hM 0)`. Take `⟨R0, hR0⟩` from `(hK.image continuous_infOf).isBounded.exists_norm_le`. Establish `hD : IsCompact ((fun q : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) => q.1 - q.2) '' (tsupport g ×ˢ (finOf '' K)))` using `(hgc.isCompact.prod (hK.image continuous_finOf)).image continuous_sub`.

Take `⟨V, hVc, hVk, hDV⟩` from `exists_clopen_superset hD`. Take `⟨k, hk⟩` from `GlobalTheory.CompanionTheory.ThetaAdm.summable_weight F (indicator_mem_SB_of_isClopen hVc hVk)`. Establish `hC : ∀ z, (1 + ‖z‖) ^ k * ‖f z‖ ≤ 2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f` using `fun z => by`. Use `SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) le_rfl le_rfl f z` as an intermediate fact. Simplify `this` using `[norm_iteratedFDeriv_zero]`.

Take `⟨C, hCdef⟩ : ∃ C, C = 2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f` from `⟨_, rfl⟩`. Rewrite `hC` using `[← hCdef]`. Establish `hC0 : 0 ≤ C` using `(mul_nonneg (by positivity) (norm_nonneg _)).trans (hC 0)`. Take `⟨R, hR, hRdef⟩ : ∃ R : ℝ, 0 ≤ R ∧ R = max R0 0` from `⟨_, le_max_right _ _, rfl⟩`. Use `⟨fun ξ => (M * (C * (1 + R) ^ k)) * (‖V.indicator (fun _ => (1 : ℂ)) (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))‖ * ((1 + ‖(fun i => mixedEmbedding F (ξ i) : κ → mixedEmbedding.mixedSpace F)‖) ^ k)⁻¹), hk.mul_left _, ?_⟩` and prove the remaining obligations.

Introduce `ξ a ha`. Use `beta_reduce`. Establish `hpure : pureA F f g (ratA ξ + a) = f ((fun i => mixedEmbedding F (ξ i) : κ → mixedEmbedding.mixedSpace F) + infOf a) * g ((fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) + finOf a)` using `by show f (infOf (ratA ξ + a)) * g (finOf (ratA ξ + a)) = _`. Rewrite using `[infOf_ratA_add, finOf_ratA_add]`. Rewrite using `[hpure, norm_mul]`.

Generalize the expression as in `hp : (fun i => mixedEmbedding F (ξ i) : κ → mixedEmbedding.mixedSpace F) = p`. Generalize the expression as in `hy : (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) = y`. Establish `hRa : ‖infOf a‖ ≤ R` using `hRdef ▸ (hR0 _ ⟨a, ha, rfl⟩).trans (le_max_left _ _)`. Establish `hf1 : ‖f (p + infOf a)‖ ≤ C * (1 + R) ^ k * ((1 + ‖p‖) ^ k)⁻¹`. Establish `h0 : ‖p‖ ≤ ‖p + infOf a‖ + ‖infOf a‖`.

Simplify using `using norm_sub_le (p + infOf a) (infOf a)`. Establish `h1 : 1 + ‖p‖ ≤ (1 + ‖p + infOf a‖) * (1 + R)`. Use polynomial arithmetic with `[norm_nonneg (p + infOf a), norm_nonneg (infOf a)]`. Establish `hpos : 0 < 1 + ‖p‖` using `by positivity`. Establish `h2 : (1 + ‖p‖) ^ k ≤ (1 + ‖p + infOf a‖) ^ k * (1 + R) ^ k`.

Rewrite using `[← mul_pow]`. Conclude with `pow_le_pow_left₀ hpos.le h1 k`. Establish `h3` using `hC (p + infOf a)`. Rewrite using `[le_mul_inv_iff₀ (by positivity)]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hg1 : ‖g (y + finOf a)‖ ≤ M * ‖V.indicator (fun _ => (1 : ℂ)) y‖`. Distinguish the cases in `hyV : y ∈ V`. Rewrite using `[Set.indicator_of_mem hyV, norm_one, mul_one]`. Conclude with `hM _`. Establish `hz : g (y + finOf a) = 0`.

Assume the negation of the conclusion as `hne`. Apply `hyV` to reduce the goal to its premises. Apply `hDV` to reduce the goal to its premises. Conclude with `⟨(y + finOf a, finOf a), ⟨subset_tsupport g hne, ⟨a, ha, rfl⟩⟩, by simp⟩`. Rewrite using `[hz, norm_zero]`.

Conclude with `mul_nonneg hM0 (norm_nonneg _)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem pure_bound [Fintype κ] (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F))
    {K : Set (κ → AF F)} (hK : IsCompact K) :
    ∃ u : (κ → F) → ℝ, Summable u ∧ ∀ ξ, ∀ a ∈ K, ‖pureA F f g (ratA ξ + a)‖ ≤ u ξ := by
  obtain ⟨hgl, hgc⟩ := hg
  obtain ⟨M, hM⟩ := hgl.continuous.bounded_above_of_compact_support hgc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨R0, hR0⟩ := (hK.image continuous_infOf).isBounded.exists_norm_le
  have hD : IsCompact ((fun q : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) => q.1 - q.2) ''
      (tsupport g ×ˢ (finOf '' K))) :=
    (hgc.isCompact.prod (hK.image continuous_finOf)).image continuous_sub
  obtain ⟨V, hVc, hVk, hDV⟩ := exists_clopen_superset hD
  obtain ⟨k, hk⟩ := GlobalTheory.CompanionTheory.ThetaAdm.summable_weight F (indicator_mem_SB_of_isClopen hVc hVk)
  have hC : ∀ z, (1 + ‖z‖) ^ k * ‖f z‖ ≤
      2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f := fun z => by
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) le_rfl le_rfl f z
    simpa [norm_iteratedFDeriv_zero] using this
  obtain ⟨C, hCdef⟩ : ∃ C, C = 2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f := ⟨_, rfl⟩
  rw [← hCdef] at hC
  have hC0 : 0 ≤ C := (mul_nonneg (by positivity) (norm_nonneg _)).trans (hC 0)
  obtain ⟨R, hR, hRdef⟩ : ∃ R : ℝ, 0 ≤ R ∧ R = max R0 0 := ⟨_, le_max_right _ _, rfl⟩
  refine ⟨fun ξ => (M * (C * (1 + R) ^ k)) *
    (‖V.indicator (fun _ => (1 : ℂ)) (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))‖ *
      ((1 + ‖(fun i => mixedEmbedding F (ξ i) : κ → mixedEmbedding.mixedSpace F)‖) ^ k)⁻¹), hk.mul_left _, ?_⟩
  intro ξ a ha
  beta_reduce
  have hpure : pureA F f g (ratA ξ + a) =
      f ((fun i => mixedEmbedding F (ξ i) : κ → mixedEmbedding.mixedSpace F) + infOf a) *
        g ((fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) + finOf a) := by
    show f (infOf (ratA ξ + a)) * g (finOf (ratA ξ + a)) = _
    rw [infOf_ratA_add, finOf_ratA_add]
  rw [hpure, norm_mul]
  generalize hp : (fun i => mixedEmbedding F (ξ i) : κ → mixedEmbedding.mixedSpace F) = p
  generalize hy : (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) = y
  have hRa : ‖infOf a‖ ≤ R := hRdef ▸ (hR0 _ ⟨a, ha, rfl⟩).trans (le_max_left _ _)
  have hf1 : ‖f (p + infOf a)‖ ≤ C * (1 + R) ^ k * ((1 + ‖p‖) ^ k)⁻¹ := by
    have h0 : ‖p‖ ≤ ‖p + infOf a‖ + ‖infOf a‖ := by
      simpa using norm_sub_le (p + infOf a) (infOf a)
    have h1 : 1 + ‖p‖ ≤ (1 + ‖p + infOf a‖) * (1 + R) := by
      nlinarith [norm_nonneg (p + infOf a), norm_nonneg (infOf a)]
    have hpos : 0 < 1 + ‖p‖ := by positivity
    have h2 : (1 + ‖p‖) ^ k ≤ (1 + ‖p + infOf a‖) ^ k * (1 + R) ^ k := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ hpos.le h1 k
    have h3 := hC (p + infOf a)
    rw [le_mul_inv_iff₀ (by positivity)]
    calc ‖f (p + infOf a)‖ * (1 + ‖p‖) ^ k
        ≤ ‖f (p + infOf a)‖ * ((1 + ‖p + infOf a‖) ^ k * (1 + R) ^ k) :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = ((1 + ‖p + infOf a‖) ^ k * ‖f (p + infOf a)‖) * (1 + R) ^ k := by ring
      _ ≤ C * (1 + R) ^ k := mul_le_mul_of_nonneg_right h3 (by positivity)
  have hg1 : ‖g (y + finOf a)‖ ≤ M * ‖V.indicator (fun _ => (1 : ℂ)) y‖ := by
    by_cases hyV : y ∈ V
    · rw [Set.indicator_of_mem hyV, norm_one, mul_one]
      exact hM _
    · have hz : g (y + finOf a) = 0 := by
        by_contra hne
        apply hyV
        apply hDV
        exact ⟨(y + finOf a, finOf a), ⟨subset_tsupport g hne, ⟨a, ha, rfl⟩⟩, by simp⟩
      rw [hz, norm_zero]
      exact mul_nonneg hM0 (norm_nonneg _)
  calc ‖f (p + infOf a)‖ * ‖g (y + finOf a)‖
      ≤ (C * (1 + R) ^ k * ((1 + ‖p‖) ^ k)⁻¹) * (M * ‖V.indicator (fun _ => (1 : ℂ)) y‖) :=
        mul_le_mul hf1 hg1 (norm_nonneg _) (by positivity)
    _ = M * (C * (1 + R) ^ k) * (‖V.indicator (fun _ => (1 : ℂ)) y‖ * ((1 + ‖p‖) ^ k)⁻¹) := by ring

open scoped Classical in

/- English proof (translation)
Use `Submodule.span_induction (p := fun Φ _ => Continuous Φ ∧ ∀ K : Set (κ → AF F), IsCompact K → ∃ u : (κ → F) → ℝ, Summable u ∧ ∀ ξ, ∀ a ∈ K, ‖Φ (ratA ξ + a)‖ ≤ u ξ) ?_ ?_ ?_ ?_ hΦ` and prove the remaining obligations. Introduce and unpack `x ⟨f, g, hg, rfl⟩`. Use `⟨?_, fun K hK => pure_bound f hg hK⟩` and prove the remaining obligations. Use `show Continuous fun x => f (infOf x) * g (finOf x)`. Conclude with `(f.continuous.comp continuous_infOf).mul (hg.1.continuous.comp continuous_finOf)`.

Use `⟨continuous_const, fun K _ => ⟨0, summable_zero, fun ξ a _ => by simp⟩⟩` and prove the remaining obligations. Introduce and unpack `x y _ _ ⟨hxc, hxb⟩ ⟨hyc, hyb⟩`. Use `⟨hxc.add hyc, fun K hK => ?_⟩` and prove the remaining obligations. Take `⟨u, hu, hub⟩` from `hxb K hK`. Take `⟨v, hv, hvb⟩` from `hyb K hK`.

Conclude with `⟨u + v, hu.add hv, fun ξ a ha => (norm_add_le _ _).trans (add_le_add (hub ξ a ha) (hvb ξ a ha))⟩`. Introduce and unpack `c x _ ⟨hxc, hxb⟩`. Use `⟨hxc.const_smul c, fun K hK => ?_⟩` and prove the remaining obligations. Take `⟨u, hu, hub⟩` from `hxb K hK`. Use `⟨fun ξ => ‖c‖ * u ξ, hu.mul_left _, fun ξ a ha => ?_⟩` and prove the remaining obligations.

Rewrite using `[Pi.smul_apply, norm_smul]`. Conclude with `mul_le_mul_of_nonneg_left (hub ξ a ha) (norm_nonneg _)`.
-/
theorem schA_bound [Fintype κ] {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    Continuous Φ ∧ ∀ K : Set (κ → AF F), IsCompact K →
      ∃ u : (κ → F) → ℝ, Summable u ∧ ∀ ξ, ∀ a ∈ K, ‖Φ (ratA ξ + a)‖ ≤ u ξ := by
  refine Submodule.span_induction (p := fun Φ _ => Continuous Φ ∧ ∀ K : Set (κ → AF F), IsCompact K →
      ∃ u : (κ → F) → ℝ, Summable u ∧ ∀ ξ, ∀ a ∈ K, ‖Φ (ratA ξ + a)‖ ≤ u ξ) ?_ ?_ ?_ ?_ hΦ
  · rintro x ⟨f, g, hg, rfl⟩
    refine ⟨?_, fun K hK => pure_bound f hg hK⟩
    show Continuous fun x => f (infOf x) * g (finOf x)
    exact (f.continuous.comp continuous_infOf).mul (hg.1.continuous.comp continuous_finOf)
  · refine ⟨continuous_const, fun K _ => ⟨0, summable_zero, fun ξ a _ => by simp⟩⟩
  · rintro x y _ _ ⟨hxc, hxb⟩ ⟨hyc, hyb⟩
    refine ⟨hxc.add hyc, fun K hK => ?_⟩
    obtain ⟨u, hu, hub⟩ := hxb K hK
    obtain ⟨v, hv, hvb⟩ := hyb K hK
    exact ⟨u + v, hu.add hv, fun ξ a ha => (norm_add_le _ _).trans (add_le_add (hub ξ a ha) (hvb ξ a ha))⟩
  · rintro c x _ ⟨hxc, hxb⟩
    refine ⟨hxc.const_smul c, fun K hK => ?_⟩
    obtain ⟨u, hu, hub⟩ := hxb K hK
    refine ⟨fun ξ => ‖c‖ * u ξ, hu.mul_left _, fun ξ a ha => ?_⟩
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hub ξ a ha) (norm_nonneg _)

end GlobalTheory.CompanionTheory.ThetaCoord.Cont

end
