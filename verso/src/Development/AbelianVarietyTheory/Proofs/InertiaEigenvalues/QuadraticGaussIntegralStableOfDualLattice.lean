import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStableGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticStarStructure
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.WeilQuad

/- English proof (translation)
Introduce `F E _ _ _ _ hU A ψ x μ hψ hμ t M D hMo hMc hDo hDc hN hD`. Take `⟨⟨bas⟩, hinj, hNL, hTr, -⟩` from `Et.quadratic_structure F E A`. Use `haveI : Module.Finite A.K A.L := Module.Finite.of_basis bas`. Use `haveI : Module.Finite F A.L := Module.Finite.trans A.K A.L`. Use `haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L`.

Use `haveI : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L`. Establish `hpsi : ∀ u v : A.K, A.psiK ψ (u + v) = A.psiK ψ u * A.psiK ψ v`. Introduce `u v`. Simplify using `only [Et.psiK, map_add, AddChar.map_add_eq_mul]`. Establish `hNadd : ∀ y m : A.L, A.NL (y + m) = A.NL y + Algebra.trace A.K A.L (star y * m) + A.NL m`.

Introduce `y m`. Apply `hinj` to reduce the goal to its premises. Simplify using `only [map_add, hNL, hTr, star_add, star_mul, star_star]`. Expand and normalize the polynomial expressions, which then agree. Use `set g : A.L → ℂ := fun y => A.psiK ψ (t * x * A.NL y) with hg`.

Establish `hgadd : ∀ y m : A.L, g (y + m) = g y * A.kerL ψ (t * x) y m * A.psiK ψ (t * x * A.NL m)`. Introduce `y m`. Simplify using `only [hg, Et.kerL, ← hpsi, hNadd]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `hkadd : ∀ y y' m : A.L, A.kerL ψ (t * x) (y + y') m = A.kerL ψ (t * x) y m * A.kerL ψ (t * x) y' m`. Introduce `y y' m`. Simplify using `only [Et.kerL, ← hpsi, star_add, add_mul, map_add, mul_add]`. Establish `hmemD : ∀ y, y ∈ D ↔ ∀ m ∈ M, A.kerL ψ (t * x) y m = 1` using `fun y => Set.ext_iff.1 hD y`. Establish `hMD : M ≤ D`.

Introduce `m hm`. Rewrite using `[hmemD]`. Introduce `m' hm'`. Establish `h` using `hgadd m m'`. Establish `h1 : g (m + m') = 1` using `hN _ (M.add_mem hm hm')`.

Establish `h2 : g m = 1` using `hN _ hm`. Rewrite `h` using `[h1, h2, hN _ hm']`. Simplify using `using h.symm`. Establish `hgc : Continuous g`. Rewrite using `[continuous_iff_continuousAt]`.

Introduce `y`. Establish `c1 : Continuous (fun m : A.L => Algebra.trace A.K A.L (star y * m))` using `IsModuleTopology.continuous_of_linearMap (((Algebra.trace A.K A.L).comp (LinearMap.mulLeft A.K (star y))).restrictScalars F)`. Establish `c2 : Continuous (fun m : A.L => Algebra.trace F A.K (t * x * Algebra.trace A.K A.L (star y * m)))` using `(IsModuleTopology.continuous_of_linearMap (Algebra.trace F A.K)).comp (continuous_const.mul c1)`. Establish `hU0 : {m : A.L | m ∈ M ∧ ‖Algebra.trace F A.K (t * x * Algebra.trace A.K A.L (star y * m))‖ ≤ 1} ∈ 𝓝 (0 : A.L)`. Use `Filter.inter_mem (hMo.mem_nhds M.zero_mem) ?_` and prove the remaining obligations.

Establish `h0 : Metric.closedBall (0 : F) 1 ∈ 𝓝 (Algebra.trace F A.K (t * x * Algebra.trace A.K A.L (star y * (0 : A.L))))`. Simplify using `only [mul_zero, map_zero]`. Conclude with `Metric.closedBall_mem_nhds 0 one_pos`. Conclude with `Filter.mem_of_superset ((c2.continuousAt (x := (0 : A.L))).preimage_mem_nhds h0) (fun m hm => (show ‖Algebra.trace F A.K (t * x * Algebra.trace A.K A.L (star y * m))‖ ≤ 1 by`. Simplify `hm))` using `[Metric.mem_closedBall, dist_zero_right]`.

Establish `hU1` using `(continuous_sub_right y).continuousAt.preimage_mem_nhds (by rw [sub_self]; exact hU0)`. Use `ContinuousAt.congr (f := fun _ => g y) continuousAt_const ?_` and prove the remaining obligations. Use `filter_upwards [hU1] with z hz`. Use `show g y = g z`. Take `⟨hzM, hz1⟩` from `hz`.

Use `hgadd y (z - y)` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Rewrite using `[this, hN _ hzM, Et.kerL, Et.psiK, hψ.1 _ hz1]`. Simplify using the standard rewrite rules. Use `⟨D, hDo, hDc, fun Λ hΛo hΛc hDΛ => ?_⟩` and prove the remaining obligations.

Establish `hmeas : ∀ S : Set A.L, IsOpen S → MeasurableSet S` using `fun S hS => hS.measurableSet`. Establish `hint : IntegrableOn g (Λ : Set A.L) μ` using `hgc.continuousOn.integrableOn_compact' hΛc (hmeas _ hΛo)`. Establish `hsplit : (Λ : Set A.L) = (D : Set A.L) ∪ ((Λ : Set A.L) \ (D : Set A.L))` using `(Set.union_diff_cancel (show (D : Set A.L) ⊆ Λ from hDΛ)).symm`. Use `haveI : DiscreteTopology (A.L ⧸ D) := QuotientAddGroup.discreteTopology hDo`. Establish `hmk : Continuous (QuotientAddGroup.mk : A.L → A.L ⧸ D)` using `continuous_quot_mk`.

Use `set S : A.L ⧸ D → Set A.L := fun q => ((Λ : Set A.L) \ (D : Set A.L)) ∩ QuotientAddGroup.mk ⁻¹' {q} with hS`. Establish `hSo : ∀ q, MeasurableSet (S q)` using `fun q => ((hmeas _ hΛo).diff (hmeas _ hDo)).inter (hmeas _ ((isOpen_discrete {q}).preimage hmk))`. Establish `hzero : ∀ q, ∫ y in S q, g y ∂μ = 0`. Introduce `q`. Distinguish the cases in `hne : (S q).Nonempty`.

Use `swap`. Rewrite using `[Set.not_nonempty_iff_eq_empty.1 hne, Measure.restrict_empty, integral_zero_measure]`. Take `⟨y₀, ⟨hy₀Λ, hy₀D⟩, hy₀q⟩` from `hne`. Establish `hy₀ : ¬ ∀ m ∈ M, A.kerL ψ (t * x) y₀ m = 1` using `fun h => hy₀D ((hmemD y₀).2 h)`. Use `push_neg at hy₀`.

Take `⟨m₀, hm₀, hc⟩` from `hy₀`. Establish `hm₀D : m₀ ∈ D` using `hMD hm₀`. Establish `hshift : ∀ y ∈ S q, g (m₀ + y) = A.kerL ψ (t * x) y₀ m₀ * g y`. Introduce `y hy`. Take `⟨-, hyq⟩` from `hy`.

Establish `hrel : -y₀ + y ∈ D`. Rewrite using `[← QuotientAddGroup.eq]`. Conclude with `(hy₀q.trans hyq.symm)`. Establish `h1 : A.kerL ψ (t * x) y m₀ = A.kerL ψ (t * x) y₀ m₀`. Use `hkadd y₀ (-y₀ + y) m₀` as an intermediate fact.

Rewrite `this` using `[add_neg_cancel_left, (hmemD _).1 hrel m₀ hm₀, mul_one]`. Conclude with `this`. Rewrite using `[add_comm, hgadd, h1, hN _ hm₀]`. Expand and normalize the polynomial expressions, which then agree. Establish `hpre : (fun y => m₀ + y) ⁻¹' (S q) = S q`.

Use extensionality with `y`. Simplify using `only [hS, Set.mem_preimage, Set.mem_inter_iff, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]`. Establish `e1 : m₀ + y ∈ Λ ↔ y ∈ Λ` using `⟨fun h => by simpa using Λ.sub_mem h (hDΛ hm₀D), fun h => Λ.add_mem (hDΛ hm₀D) h⟩`. Establish `e2 : m₀ + y ∈ D ↔ y ∈ D` using `⟨fun h => by simpa using D.sub_mem h hm₀D, fun h => D.add_mem hm₀D h⟩`. Establish `e3 : (QuotientAddGroup.mk (m₀ + y) : A.L ⧸ D) = QuotientAddGroup.mk y`.

Rewrite using `[QuotientAddGroup.eq]`. Simplify using `using D.neg_mem hm₀D`. Rewrite using `[e1, e2, e3]`. Establish `htr` using `(measurePreserving_add_left μ m₀).setIntegral_preimage_emb (measurableEmbedding_addLeft m₀) g (S q)`. Rewrite `htr` using `[hpre]`.

Establish `h2 : ∫ y in S q, g (m₀ + y) ∂μ = A.kerL ψ (t * x) y₀ m₀ * ∫ y in S q, g y ∂μ`. Rewrite using `[← integral_const_mul]`. Conclude with `setIntegral_congr_fun (hSo q) (fun y hy => hshift y hy)`. Rewrite `htr` using `[h2]`. Establish `h3 : (A.kerL ψ (t * x) y₀ m₀ - 1) * ∫ y in S q, g y ∂μ = 0` using `by rw [sub_mul, htr]; ring`.

Conclude with `(mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hc)`. Establish `hfin : (QuotientAddGroup.mk '' (Λ : Set A.L) : Set (A.L ⧸ D)).Finite` using `(hΛc.image hmk).finite_of_discrete`. Establish `hunion : ((Λ : Set A.L) \ (D : Set A.L)) = ⋃ q ∈ hfin.toFinset, S q`. Use extensionality with `y`. Simplify using `only [hS, Set.mem_iUnion, Set.Finite.mem_toFinset, Set.mem_image, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, exists_prop]`.

Prove the components needed by the constructor for the conclusion. Introduce `hy`. Conclude with `⟨_, ⟨y, hy.1, rfl⟩, hy, rfl⟩`. Introduce and unpack `⟨_, _, hy, _⟩`. Conclude with `hy`.

Establish `hrest : ∫ y in (Λ : Set A.L) \ (D : Set A.L), g y ∂μ = 0`. Rewrite using `[hunion, integral_biUnion_finset]`. Conclude with `Finset.sum_eq_zero (fun q _ => hzero q)`. Conclude with `fun q _ => hSo q`. Introduce `q₁ _ q₂ _ hq`.

Use `Set.disjoint_left.2 ?_` and prove the remaining obligations. Introduce and unpack `y ⟨-, h1⟩ ⟨-, h2⟩`. Conclude with `hq ((Set.mem_singleton_iff.1 h1).symm.trans (Set.mem_singleton_iff.1 h2))`. Conclude with `fun q _ => hint.mono_set (fun y hy => hy.1.1)`. Use `show ∫ y in (Λ : Set A.L), g y ∂μ = ∫ y in (D : Set A.L), g y ∂μ`.

Rewrite using `[hsplit, setIntegral_union Set.disjoint_sdiff_right ((hmeas _ hΛo).diff (hmeas _ hDo)) (hint.mono_set hDΛ) (hint.mono_set Set.diff_subset), hrest, add_zero]`.
-/
theorem gaussInt_stable_of_dual : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L), IsStdChar ψ → μ.IsAddHaarMeasure → ∀ (t : A.K) (M D : AddSubgroup A.L), IsOpen (M : Set A.L) → IsCompact (M : Set A.L) → IsOpen (D : Set A.L) → IsCompact (D : Set A.L) → (∀ m ∈ M, A.psiK ψ (t * x * A.NL m) = 1) → (D : Set A.L) = {y : A.L | ∀ m ∈ M, A.kerL ψ (t * x) y m = 1} → IsStableGauss A ψ x μ t (gaussInt A ψ x μ t (D : Set A.L)) := by
  intro F E _ _ _ _ hU A ψ x μ hψ hμ t M D hMo hMc hDo hDc hN hD
  obtain ⟨⟨bas⟩, hinj, hNL, hTr, -⟩ := Et.quadratic_structure F E A
  haveI : Module.Finite A.K A.L := Module.Finite.of_basis bas
  haveI : Module.Finite F A.L := Module.Finite.trans A.K A.L
  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  haveI : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  have hpsi : ∀ u v : A.K, A.psiK ψ (u + v) = A.psiK ψ u * A.psiK ψ v := by
    intro u v
    simp only [Et.psiK, map_add, AddChar.map_add_eq_mul]
  have hNadd : ∀ y m : A.L, A.NL (y + m) = A.NL y + Algebra.trace A.K A.L (star y * m) + A.NL m := by
    intro y m
    apply hinj
    simp only [map_add, hNL, hTr, star_add, star_mul, star_star]
    ring
  set g : A.L → ℂ := fun y => A.psiK ψ (t * x * A.NL y) with hg
  have hgadd : ∀ y m : A.L, g (y + m) = g y * A.kerL ψ (t * x) y m * A.psiK ψ (t * x * A.NL m) := by
    intro y m
    simp only [hg, Et.kerL, ← hpsi, hNadd]
    congr 1
    ring
  have hkadd : ∀ y y' m : A.L, A.kerL ψ (t * x) (y + y') m = A.kerL ψ (t * x) y m * A.kerL ψ (t * x) y' m := by
    intro y y' m
    simp only [Et.kerL, ← hpsi, star_add, add_mul, map_add, mul_add]
  have hmemD : ∀ y, y ∈ D ↔ ∀ m ∈ M, A.kerL ψ (t * x) y m = 1 := fun y => Set.ext_iff.1 hD y
  have hMD : M ≤ D := by
    intro m hm
    rw [hmemD]
    intro m' hm'
    have h := hgadd m m'
    have h1 : g (m + m') = 1 := hN _ (M.add_mem hm hm')
    have h2 : g m = 1 := hN _ hm
    rw [h1, h2, hN _ hm'] at h
    simpa using h.symm

  have hgc : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro y
    have c1 : Continuous (fun m : A.L => Algebra.trace A.K A.L (star y * m)) :=
      IsModuleTopology.continuous_of_linearMap
        (((Algebra.trace A.K A.L).comp (LinearMap.mulLeft A.K (star y))).restrictScalars F)
    have c2 : Continuous (fun m : A.L => Algebra.trace F A.K (t * x * Algebra.trace A.K A.L (star y * m))) :=
      (IsModuleTopology.continuous_of_linearMap (Algebra.trace F A.K)).comp (continuous_const.mul c1)
    have hU0 : {m : A.L | m ∈ M ∧ ‖Algebra.trace F A.K (t * x * Algebra.trace A.K A.L (star y * m))‖ ≤ 1} ∈ 𝓝 (0 : A.L) := by
      refine Filter.inter_mem (hMo.mem_nhds M.zero_mem) ?_
      have h0 : Metric.closedBall (0 : F) 1 ∈ 𝓝 (Algebra.trace F A.K (t * x * Algebra.trace A.K A.L (star y * (0 : A.L)))) := by
        simp only [mul_zero, map_zero]
        exact Metric.closedBall_mem_nhds 0 one_pos
      exact Filter.mem_of_superset ((c2.continuousAt (x := (0 : A.L))).preimage_mem_nhds h0)
        (fun m hm => (show ‖Algebra.trace F A.K (t * x * Algebra.trace A.K A.L (star y * m))‖ ≤ 1 by
          simpa [Metric.mem_closedBall, dist_zero_right] using hm))
    have hU1 := (continuous_sub_right y).continuousAt.preimage_mem_nhds (by rw [sub_self]; exact hU0)
    refine ContinuousAt.congr (f := fun _ => g y) continuousAt_const ?_
    filter_upwards [hU1] with z hz
    show g y = g z
    obtain ⟨hzM, hz1⟩ := hz
    have := hgadd y (z - y)
    rw [add_sub_cancel] at this
    rw [this, hN _ hzM, Et.kerL, Et.psiK, hψ.1 _ hz1]
    simp

  refine ⟨D, hDo, hDc, fun Λ hΛo hΛc hDΛ => ?_⟩
  have hmeas : ∀ S : Set A.L, IsOpen S → MeasurableSet S := fun S hS => hS.measurableSet
  have hint : IntegrableOn g (Λ : Set A.L) μ := hgc.continuousOn.integrableOn_compact' hΛc (hmeas _ hΛo)
  have hsplit : (Λ : Set A.L) = (D : Set A.L) ∪ ((Λ : Set A.L) \ (D : Set A.L)) :=
    (Set.union_diff_cancel (show (D : Set A.L) ⊆ Λ from hDΛ)).symm

  haveI : DiscreteTopology (A.L ⧸ D) := QuotientAddGroup.discreteTopology hDo
  have hmk : Continuous (QuotientAddGroup.mk : A.L → A.L ⧸ D) := continuous_quot_mk
  set S : A.L ⧸ D → Set A.L := fun q => ((Λ : Set A.L) \ (D : Set A.L)) ∩ QuotientAddGroup.mk ⁻¹' {q} with hS
  have hSo : ∀ q, MeasurableSet (S q) := fun q =>
    ((hmeas _ hΛo).diff (hmeas _ hDo)).inter (hmeas _ ((isOpen_discrete {q}).preimage hmk))
  have hzero : ∀ q, ∫ y in S q, g y ∂μ = 0 := by
    intro q
    by_cases hne : (S q).Nonempty
    swap
    · rw [Set.not_nonempty_iff_eq_empty.1 hne, Measure.restrict_empty, integral_zero_measure]
    obtain ⟨y₀, ⟨hy₀Λ, hy₀D⟩, hy₀q⟩ := hne
    have hy₀ : ¬ ∀ m ∈ M, A.kerL ψ (t * x) y₀ m = 1 := fun h => hy₀D ((hmemD y₀).2 h)
    push_neg at hy₀
    obtain ⟨m₀, hm₀, hc⟩ := hy₀
    have hm₀D : m₀ ∈ D := hMD hm₀
    have hshift : ∀ y ∈ S q, g (m₀ + y) = A.kerL ψ (t * x) y₀ m₀ * g y := by
      intro y hy
      obtain ⟨-, hyq⟩ := hy
      have hrel : -y₀ + y ∈ D := by
        rw [← QuotientAddGroup.eq]
        exact (hy₀q.trans hyq.symm)
      have h1 : A.kerL ψ (t * x) y m₀ = A.kerL ψ (t * x) y₀ m₀ := by
        have := hkadd y₀ (-y₀ + y) m₀
        rw [add_neg_cancel_left, (hmemD _).1 hrel m₀ hm₀, mul_one] at this
        exact this
      rw [add_comm, hgadd, h1, hN _ hm₀]
      ring
    have hpre : (fun y => m₀ + y) ⁻¹' (S q) = S q := by
      ext y
      simp only [hS, Set.mem_preimage, Set.mem_inter_iff, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]
      have e1 : m₀ + y ∈ Λ ↔ y ∈ Λ := ⟨fun h => by simpa using Λ.sub_mem h (hDΛ hm₀D), fun h => Λ.add_mem (hDΛ hm₀D) h⟩
      have e2 : m₀ + y ∈ D ↔ y ∈ D := ⟨fun h => by simpa using D.sub_mem h hm₀D, fun h => D.add_mem hm₀D h⟩
      have e3 : (QuotientAddGroup.mk (m₀ + y) : A.L ⧸ D) = QuotientAddGroup.mk y := by
        rw [QuotientAddGroup.eq]
        simpa using D.neg_mem hm₀D
      rw [e1, e2, e3]
    have htr := (measurePreserving_add_left μ m₀).setIntegral_preimage_emb (measurableEmbedding_addLeft m₀) g (S q)
    rw [hpre] at htr
    have h2 : ∫ y in S q, g (m₀ + y) ∂μ = A.kerL ψ (t * x) y₀ m₀ * ∫ y in S q, g y ∂μ := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun (hSo q) (fun y hy => hshift y hy)
    rw [h2] at htr
    have h3 : (A.kerL ψ (t * x) y₀ m₀ - 1) * ∫ y in S q, g y ∂μ = 0 := by rw [sub_mul, htr]; ring
    exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hc)
  have hfin : (QuotientAddGroup.mk '' (Λ : Set A.L) : Set (A.L ⧸ D)).Finite :=
    (hΛc.image hmk).finite_of_discrete
  have hunion : ((Λ : Set A.L) \ (D : Set A.L)) = ⋃ q ∈ hfin.toFinset, S q := by
    ext y
    simp only [hS, Set.mem_iUnion, Set.Finite.mem_toFinset, Set.mem_image, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, exists_prop]
    constructor
    · intro hy
      exact ⟨_, ⟨y, hy.1, rfl⟩, hy, rfl⟩
    · rintro ⟨_, _, hy, _⟩
      exact hy
  have hrest : ∫ y in (Λ : Set A.L) \ (D : Set A.L), g y ∂μ = 0 := by
    rw [hunion, integral_biUnion_finset]
    · exact Finset.sum_eq_zero (fun q _ => hzero q)
    · exact fun q _ => hSo q
    · intro q₁ _ q₂ _ hq
      refine Set.disjoint_left.2 ?_
      rintro y ⟨-, h1⟩ ⟨-, h2⟩
      exact hq ((Set.mem_singleton_iff.1 h1).symm.trans (Set.mem_singleton_iff.1 h2))
    · exact fun q _ => hint.mono_set (fun y hy => hy.1.1)
  show ∫ y in (Λ : Set A.L), g y ∂μ = ∫ y in (D : Set A.L), g y ∂μ
  rw [hsplit, setIntegral_union Set.disjoint_sdiff_right ((hmeas _ hΛo).diff (hmeas _ hDo))
    (hint.mono_set hDΛ) (hint.mono_set Set.diff_subset), hrest, add_zero]

end GlobalTheory.JR.WeilQuad
