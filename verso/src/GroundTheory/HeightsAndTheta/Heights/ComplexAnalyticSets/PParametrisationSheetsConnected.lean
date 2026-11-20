import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParametrisationSheetsConnected
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSheetPieceProductAnalytic
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSheetPieceReachesCentre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter MeasureTheory

/- English proof (translation)
Set `φ : (σ → ℂ) → ((σ → ℂ) →ₗ[ℝ] ℂ)` to `fun u => { toFun := fun v => ∑ i, v i * u i map_add' := fun a b => by simp [add_mul, Finset.sum_add_distrib] map_smul' := fun c a => by simp [Finset.mul_sum, mul_assoc] }`. Establish `hφ : ∀ u v, φ u v = ∑ i, v i * u i` using `fun _ _ => rfl`. Establish `hker : ∀ u ∈ T, volume (LinearMap.ker (φ u) : Set (σ → ℂ)) = 0`. Introduce `u hu`. Use `Measure.addHaar_submodule volume _ fun htop => ?_` and prove the remaining obligations.

Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, u i ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `h0 (by rwa [show u = 0 from funext h] at hu)`. Establish `hm : Pi.single i 1 ∈ LinearMap.ker (φ u)` using `htop ▸ Submodule.mem_top`.

Rewrite `hm` using `[LinearMap.mem_ker, hφ]`. Simplify using `[Pi.single_apply] at hm`. Conclude with `hi hm`. Establish `hnull : volume (⋃ u ∈ T, (LinearMap.ker (φ u) : Set (σ → ℂ))) = 0` using `(measure_biUnion_null_iff hT).2 hker`. Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v, v ∉ ⋃ u ∈ T, (LinearMap.ker (φ u) : Set (σ → ℂ)) := by`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `hu : (Set.univ : Set (σ → ℂ)) ⊆ ⋃ u ∈ T, (LinearMap.ker (φ u) : Set (σ → ℂ))` using `fun x _ => h x`. Establish `hpos` using `isOpen_univ.measure_pos (volume : Measure (σ → ℂ)) Set.univ_nonempty`. Conclude with `hpos.ne' (measure_mono_null hu hnull)`.

Use `⟨∑ i, v i • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i, fun u hu => ?_⟩` and prove the remaining obligations. Establish `hvu : φ u v ≠ 0` using `fun h => hv (Set.mem_biUnion hu (LinearMap.mem_ker.2 h))`. Rewrite `hvu` using `[hφ]`. Simplify `hvu` using `[ContinuousLinearMap.sum_apply]`.
-/
theorem exists_clm_ne_zero_of_countable {σ : Type} [Fintype σ] {T : Set (σ → ℂ)} (hT : T.Countable)
    (h0 : (0 : σ → ℂ) ∉ T) : ∃ ℓ : (σ → ℂ) →L[ℂ] ℂ, ∀ u ∈ T, ℓ u ≠ 0 := by
  classical
  let φ : (σ → ℂ) → ((σ → ℂ) →ₗ[ℝ] ℂ) := fun u =>
    { toFun := fun v => ∑ i, v i * u i
      map_add' := fun a b => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c a => by simp [Finset.mul_sum, mul_assoc] }
  have hφ : ∀ u v, φ u v = ∑ i, v i * u i := fun _ _ => rfl
  have hker : ∀ u ∈ T, volume (LinearMap.ker (φ u) : Set (σ → ℂ)) = 0 := by
    intro u hu
    refine Measure.addHaar_submodule volume _ fun htop => ?_
    obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
      by_contra h
      push Not at h
      exact h0 (by rwa [show u = 0 from funext h] at hu)
    have hm : Pi.single i 1 ∈ LinearMap.ker (φ u) := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hφ] at hm
    simp [Pi.single_apply] at hm
    exact hi hm
  have hnull : volume (⋃ u ∈ T, (LinearMap.ker (φ u) : Set (σ → ℂ))) = 0 :=
    (measure_biUnion_null_iff hT).2 hker
  obtain ⟨v, hv⟩ : ∃ v, v ∉ ⋃ u ∈ T, (LinearMap.ker (φ u) : Set (σ → ℂ)) := by
    by_contra h
    push Not at h
    have hu : (Set.univ : Set (σ → ℂ)) ⊆ ⋃ u ∈ T, (LinearMap.ker (φ u) : Set (σ → ℂ)) := fun x _ => h x
    have hpos := isOpen_univ.measure_pos (volume : Measure (σ → ℂ)) Set.univ_nonempty
    exact hpos.ne' (measure_mono_null hu hnull)
  refine ⟨∑ i, v i • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i, fun u hu => ?_⟩
  have hvu : φ u v ≠ 0 := fun h => hv (Set.mem_biUnion hu (LinearMap.mem_ker.2 h))
  rw [hφ] at hvu
  simpa [ContinuousLinearMap.sum_apply] using hvu

/- English proof (translation)
Introduce `σ _ X w B d A D δ N hP hirr`. Take `⟨hB, hwXB, hD, -, hmaps, -, -, -, -, hcard, -, hdense⟩` from `id hP`. Use `set S := {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} with hS`. Assume the negation of the conclusion as `hnc`. Rewrite `hnc` using `[IsPreconnected]`.

Use `push Not at hnc`. Take `⟨u, v, hu, hv, hSuv, hSu, hSv, hdisj⟩` from `hnc`. Establish `hdisj' : S ∩ (v ∩ u) = ∅` using `by rwa [Set.inter_comm v u]`. Establish `hSvu : S ⊆ v ∪ u` using `by rwa [Set.union_comm]`. Establish `hwu` using `h₂ σ X w B d A D δ N u v hP hu hv hSuv hdisj hSu`.

Establish `hwv` using `h₂ σ X w B d A D δ N v u hP hv hu hSvu hdisj' hSv`. Take `⟨p, hpS, hpw⟩` from `mem_closure_iff_seq_limit.1 hwu`. Take `⟨q, hqS, hqw⟩` from `mem_closure_iff_seq_limit.1 hwv`. Establish `hfin : ∀ (U' : Set (σ → ℂ)), ∀ x ∈ S, {x' | x' ∈ X ∩ B ∧ x' ∈ U' ∧ A x' = A x}.Finite` using `fun U' x hx => (Set.finite_of_encard_eq_coe (hcard (A x) (hmaps hx.1) hx.2)).subset fun x' hx' => ⟨hx'.1, hx'.2.2⟩`. Use `set T : Set (σ → ℂ) := (⋃ n, (fun x' => p n - x') '' {x' | x' ∈ X ∩ B ∧ x' ∈ v ∧ A x' = A (p n)}) ∪ ⋃ n, (fun x' => q n - x') '' {x' | x' ∈ X ∩ B ∧ x' ∈ u ∧ A x' = A (q n)} with hT`.

Establish `hTc : T.Countable` using `(Set.countable_iUnion fun n => ((hfin v (p n) (hpS n).1).image _).countable).union (Set.countable_iUnion fun n => ((hfin u (q n) (hqS n).1).image _).countable)`. Establish `hT0 : (0 : σ → ℂ) ∉ T`. Establish `key : ∀ (r : σ → ℂ) (U₁ U₂ : Set (σ → ℂ)), r ∈ S ∩ U₁ → S ∩ (U₁ ∩ U₂) = ∅ → ∀ x' ∈ {x' | x' ∈ X ∩ B ∧ x' ∈ U₂ ∧ A x' = A r}, r - x' ≠ 0`. Introduce `r U₁ U₂ hr hd x' hx' h0`. Establish `hrx : r = x'` using `sub_eq_zero.1 h0`.

Establish `hx'S : x' ∈ S` using `⟨hx'.1, by rw [hx'.2.2]; exact hr.1.2⟩`. Conclude with `(Set.eq_empty_iff_forall_notMem.1 hd x') ⟨hx'S, hrx ▸ hr.2, hx'.2.1⟩`. Apply the tactic sequence `rintro (h | h) <;> obtain ⟨n, x', hx', hx0⟩ := Set.mem_iUnion.1 h`. Conclude with `key (p n) u v (hpS n) hdisj x' hx' hx0`. Conclude with `key (q n) v u (hqS n) hdisj' x' hx' hx0`.

Take `⟨ℓ, hℓ⟩` from `exists_clm_ne_zero_of_countable hTc hT0`. Take `⟨f, hfan, hfeq⟩` from `h₁ σ X w B d A D δ N u v ℓ hP hu hv hSuv hdisj`. Take `⟨g, hgan, hgeq⟩` from `h₁ σ X w B d A D δ N v u ℓ hP hv hu hSvu hdisj'`. Establish `hzero : ∀ (U' : Set (σ → ℂ)) (F : (σ → ℂ) → ℂ), (∀ z, A z ∈ D → δ (A z) ≠ 0 → F z = ∏ᶠ x ∈ {x | x ∈ X ∩ B ∧ x ∈ U' ∧ A x = A z}, (ℓ z - ℓ x)) → ∀ x ∈ S, x ∈ U' → F x = 0`. Introduce `U' F hF x hx hxU`.

Rewrite using `[hF x (hmaps hx.1) hx.2, finprod_mem_eq_finite_toFinset_prod _ (hfin U' x hx)]`. Conclude with `Finset.prod_eq_zero ((hfin U' x hx).mem_toFinset.2 ⟨hx.1, hxU, rfl⟩) (sub_self _)`. Establish `hne : ∀ (U' : Set (σ → ℂ)) (F : (σ → ℂ) → ℂ) (r : σ → ℂ), (∀ z, A z ∈ D → δ (A z) ≠ 0 → F z = ∏ᶠ x ∈ {x | x ∈ X ∩ B ∧ x ∈ U' ∧ A x = A z}, (ℓ z - ℓ x)) → r ∈ S → (∀ x' ∈ {x' | x' ∈ X ∩ B ∧ x' ∈ U' ∧ A x' = A r}, r - x' ∈ T) → F r ≠ 0`. Introduce `U' F r hF hr hrT`. Rewrite using `[hF r (hmaps hr.1) hr.2, finprod_mem_eq_finite_toFinset_prod _ (hfin U' r hr)]`.

Use `Finset.prod_ne_zero_iff.2 fun x' hx' => ?_` and prove the remaining obligations. Rewrite using `[← map_sub]`. Conclude with `hℓ _ (hrT x' ((hfin U' r hr).mem_toFinset.1 hx'))`. Establish `hfq : ∀ n, f (q n) ≠ 0` using `fun n => hne u f (q n) hfeq (hqS n).1 fun x' hx' => Or.inr (Set.mem_iUnion.2 ⟨n, x', hx', rfl⟩)`. Establish `hgp : ∀ n, g (p n) ≠ 0` using `fun n => hne v g (p n) hgeq (hpS n).1 fun x' hx' => Or.inl (Set.mem_iUnion.2 ⟨n, x', hx', rfl⟩)`.

Establish `hprod : ∀ z ∈ X ∩ B, f z * g z = 0`. Introduce `z hz`. Establish `hc : ContinuousAt (fun z => f z * g z) z` using `(hfan z (hmaps hz)).continuousAt.mul (hgan z (hmaps hz)).continuousAt`. Use `mem_closure_iff_nhdsWithin_neBot.1 (hdense hz)` as an intermediate fact. Establish `h2 : (fun z => f z * g z) =ᶠ[𝓝[S] z] fun _ => 0` using `eventually_nhdsWithin_of_forall fun x hx => by`.

Break down `hSuv hx with hxu | hxv` into its components or cases. Simplify using `[hzero u f hfeq x hx hxu]`. Simplify using `[hzero v g hgeq x hx hxv]`. Conclude with `tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds) (tendsto_const_nhds.congr' h2.symm)`. Establish `hw : A w ∈ D` using `hmaps hwXB`.

Establish `hev : ∀ᶠ z in 𝓝 w, z ∈ X → f z * g z = 0` using `by filter_upwards [hB.mem_nhds hwXB.2] with z hzB hzX using hprod z ⟨hzX, hzB⟩`. Break down `hirr.2 f g (hfan w hw) (hgan w hw) hev with hf0 | hg0` into its components or cases. Take `⟨n, hn⟩` from `(hqw.eventually hf0).exists`. Conclude with `hfq n (hn (hqS n).1.1.1)`. Take `⟨n, hn⟩` from `(hpw.eventually hg0).exists`.

Conclude with `hgp n (hn (hpS n).1.1.1)`.
-/
theorem ParametrisationSheetsConnected.proof (h₁ : SheetPieceProductAnalytic.Statement)
    (h₂ : SheetPieceReachesCentre.Statement) : ParametrisationSheetsConnected.Statement := by
  classical
  intro σ _ X w B d A D δ N hP hirr
  obtain ⟨hB, hwXB, hD, -, hmaps, -, -, -, -, hcard, -, hdense⟩ := id hP
  set S := {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} with hS
  by_contra hnc
  rw [IsPreconnected] at hnc
  push Not at hnc
  obtain ⟨u, v, hu, hv, hSuv, hSu, hSv, hdisj⟩ := hnc
  have hdisj' : S ∩ (v ∩ u) = ∅ := by rwa [Set.inter_comm v u]
  have hSvu : S ⊆ v ∪ u := by rwa [Set.union_comm]
  have hwu := h₂ σ X w B d A D δ N u v hP hu hv hSuv hdisj hSu
  have hwv := h₂ σ X w B d A D δ N v u hP hv hu hSvu hdisj' hSv
  obtain ⟨p, hpS, hpw⟩ := mem_closure_iff_seq_limit.1 hwu
  obtain ⟨q, hqS, hqw⟩ := mem_closure_iff_seq_limit.1 hwv

  have hfin : ∀ (U' : Set (σ → ℂ)), ∀ x ∈ S, {x' | x' ∈ X ∩ B ∧ x' ∈ U' ∧ A x' = A x}.Finite :=
    fun U' x hx => (Set.finite_of_encard_eq_coe (hcard (A x) (hmaps hx.1) hx.2)).subset
      fun x' hx' => ⟨hx'.1, hx'.2.2⟩
  set T : Set (σ → ℂ) :=
    (⋃ n, (fun x' => p n - x') '' {x' | x' ∈ X ∩ B ∧ x' ∈ v ∧ A x' = A (p n)}) ∪
      ⋃ n, (fun x' => q n - x') '' {x' | x' ∈ X ∩ B ∧ x' ∈ u ∧ A x' = A (q n)} with hT
  have hTc : T.Countable :=
    (Set.countable_iUnion fun n => ((hfin v (p n) (hpS n).1).image _).countable).union
      (Set.countable_iUnion fun n => ((hfin u (q n) (hqS n).1).image _).countable)
  have hT0 : (0 : σ → ℂ) ∉ T := by
    have key : ∀ (r : σ → ℂ) (U₁ U₂ : Set (σ → ℂ)), r ∈ S ∩ U₁ → S ∩ (U₁ ∩ U₂) = ∅ →
        ∀ x' ∈ {x' | x' ∈ X ∩ B ∧ x' ∈ U₂ ∧ A x' = A r}, r - x' ≠ 0 := by
      intro r U₁ U₂ hr hd x' hx' h0
      have hrx : r = x' := sub_eq_zero.1 h0
      have hx'S : x' ∈ S := ⟨hx'.1, by rw [hx'.2.2]; exact hr.1.2⟩
      exact (Set.eq_empty_iff_forall_notMem.1 hd x') ⟨hx'S, hrx ▸ hr.2, hx'.2.1⟩
    rintro (h | h) <;> obtain ⟨n, x', hx', hx0⟩ := Set.mem_iUnion.1 h
    · exact key (p n) u v (hpS n) hdisj x' hx' hx0
    · exact key (q n) v u (hqS n) hdisj' x' hx' hx0
  obtain ⟨ℓ, hℓ⟩ := exists_clm_ne_zero_of_countable hTc hT0
  obtain ⟨f, hfan, hfeq⟩ := h₁ σ X w B d A D δ N u v ℓ hP hu hv hSuv hdisj
  obtain ⟨g, hgan, hgeq⟩ := h₁ σ X w B d A D δ N v u ℓ hP hv hu hSvu hdisj'

  have hzero : ∀ (U' : Set (σ → ℂ)) (F : (σ → ℂ) → ℂ),
      (∀ z, A z ∈ D → δ (A z) ≠ 0 →
        F z = ∏ᶠ x ∈ {x | x ∈ X ∩ B ∧ x ∈ U' ∧ A x = A z}, (ℓ z - ℓ x)) →
      ∀ x ∈ S, x ∈ U' → F x = 0 := by
    intro U' F hF x hx hxU
    rw [hF x (hmaps hx.1) hx.2, finprod_mem_eq_finite_toFinset_prod _ (hfin U' x hx)]
    exact Finset.prod_eq_zero ((hfin U' x hx).mem_toFinset.2 ⟨hx.1, hxU, rfl⟩) (sub_self _)

  have hne : ∀ (U' : Set (σ → ℂ)) (F : (σ → ℂ) → ℂ) (r : σ → ℂ),
      (∀ z, A z ∈ D → δ (A z) ≠ 0 →
        F z = ∏ᶠ x ∈ {x | x ∈ X ∩ B ∧ x ∈ U' ∧ A x = A z}, (ℓ z - ℓ x)) → r ∈ S →
      (∀ x' ∈ {x' | x' ∈ X ∩ B ∧ x' ∈ U' ∧ A x' = A r}, r - x' ∈ T) → F r ≠ 0 := by
    intro U' F r hF hr hrT
    rw [hF r (hmaps hr.1) hr.2, finprod_mem_eq_finite_toFinset_prod _ (hfin U' r hr)]
    refine Finset.prod_ne_zero_iff.2 fun x' hx' => ?_
    rw [← map_sub]
    exact hℓ _ (hrT x' ((hfin U' r hr).mem_toFinset.1 hx'))
  have hfq : ∀ n, f (q n) ≠ 0 := fun n => hne u f (q n) hfeq (hqS n).1
    fun x' hx' => Or.inr (Set.mem_iUnion.2 ⟨n, x', hx', rfl⟩)
  have hgp : ∀ n, g (p n) ≠ 0 := fun n => hne v g (p n) hgeq (hpS n).1
    fun x' hx' => Or.inl (Set.mem_iUnion.2 ⟨n, x', hx', rfl⟩)

  have hprod : ∀ z ∈ X ∩ B, f z * g z = 0 := by
    intro z hz
    have hc : ContinuousAt (fun z => f z * g z) z :=
      (hfan z (hmaps hz)).continuousAt.mul (hgan z (hmaps hz)).continuousAt
    have := mem_closure_iff_nhdsWithin_neBot.1 (hdense hz)
    have h2 : (fun z => f z * g z) =ᶠ[𝓝[S] z] fun _ => 0 :=
      eventually_nhdsWithin_of_forall fun x hx => by
        rcases hSuv hx with hxu | hxv
        · simp [hzero u f hfeq x hx hxu]
        · simp [hzero v g hgeq x hx hxv]
    exact tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' h2.symm)
  have hw : A w ∈ D := hmaps hwXB
  have hev : ∀ᶠ z in 𝓝 w, z ∈ X → f z * g z = 0 := by
    filter_upwards [hB.mem_nhds hwXB.2] with z hzB hzX using hprod z ⟨hzX, hzB⟩
  rcases hirr.2 f g (hfan w hw) (hgan w hw) hev with hf0 | hg0
  · obtain ⟨n, hn⟩ := (hqw.eventually hf0).exists
    exact hfq n (hn (hqS n).1.1.1)
  · obtain ⟨n, hn⟩ := (hpw.eventually hg0).exists
    exact hgp n (hn (hpS n).1.1.1)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
