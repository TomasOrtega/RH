import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.AnalyticGerm
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAnalyticGermComponents
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermFiniteProjection
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteGermProjectionOpenAt

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter

namespace GlobalTheory.CompanionTheory.AnalyticGermSlice

/- English proof (translation)
Take `⟨N, k, f, hN, hwN, hf, hXN⟩` from `hX`. Use `⟨N, k + m, Fin.append f g, hN, hwN, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Proceed by induction on `i using Fin.addCases with`. Consider the case `left j => rw [Fin.append_left]`.

Conclude with `hf j`. Consider the case `right j => rw [Fin.append_right]`. Conclude with `(hg j).mono (Set.subset_univ N)`. Use extensionality with `z`. Establish `hz` using `Set.ext_iff.1 hXN z`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨hzX, hg0⟩, hzN⟩`. Use `⟨hzN, (Fin.forall_fin_add _).2 ⟨fun j => ?_, fun j => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Fin.append_left]`. Conclude with `(hz.1 ⟨hzX, hzN⟩).2 j`.

Rewrite using `[Fin.append_right]`. Conclude with `hg0 j`. Introduce and unpack `⟨hzN, hall⟩`. Establish `h2` using `(Fin.forall_fin_add _).1 hall`. Use `⟨⟨(hz.2 ⟨hzN, fun j => ?_⟩).1, fun j => ?_⟩, hzN⟩` and prove the remaining obligations.

Use `h2.1 j` as an intermediate fact. Rewrite `this` using `[Fin.append_left]`. Then use the resulting hypothesis. Use `h2.2 j` as an intermediate fact. Rewrite `this` using `[Fin.append_right]`. Then use the resulting hypothesis.
-/
theorem isAnalyticNear_zeros_inter {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {w : σ → ℂ}
    (hX : IsAnalyticNear X w) {m : ℕ} (g : Fin m → (σ → ℂ) → ℂ)
    (hg : ∀ i, AnalyticOnNhd ℂ (g i) Set.univ) :
    IsAnalyticNear {z | z ∈ X ∧ ∀ i, g i z = 0} w := by
  obtain ⟨N, k, f, hN, hwN, hf, hXN⟩ := hX
  refine ⟨N, k + m, Fin.append f g, hN, hwN, ?_, ?_⟩
  · intro i
    induction i using Fin.addCases with
    | left j => rw [Fin.append_left]; exact hf j
    | right j => rw [Fin.append_right]; exact (hg j).mono (Set.subset_univ N)
  · ext z
    have hz := Set.ext_iff.1 hXN z
    constructor
    · rintro ⟨⟨hzX, hg0⟩, hzN⟩
      refine ⟨hzN, (Fin.forall_fin_add _).2 ⟨fun j => ?_, fun j => ?_⟩⟩
      · rw [Fin.append_left]; exact (hz.1 ⟨hzX, hzN⟩).2 j
      · rw [Fin.append_right]; exact hg0 j
    · rintro ⟨hzN, hall⟩
      have h2 := (Fin.forall_fin_add _).1 hall
      refine ⟨⟨(hz.2 ⟨hzN, fun j => ?_⟩).1, fun j => ?_⟩, hzN⟩
      · have := h2.1 j
        rwa [Fin.append_left] at this
      · have := h2.2 j
        rwa [Fin.append_right] at this

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Establish `hcon' : ∀ i, ¬ ∀ᶠ t in 𝓝 a, f i t = 0` using `fun i hi => hcon ⟨i, hi⟩`. Establish `hne : ∀ i, ∀ᶠ t in 𝓝[≠] a, f i t ≠ 0` using `fun i => ((hf i).eventually_eq_zero_or_eventually_ne_zero).resolve_left (hcon' i)`. Establish `hall : ∀ᶠ t in 𝓝[≠] a, ∀ i, f i t ≠ 0` using `Filter.eventually_all.2 hne`. Establish `hP' : ∀ᶠ t in 𝓝[≠] a, ∏ i, f i t = 0` using `nhdsWithin_le_nhds hP`.

Take `⟨t, ht1, ht2⟩` from `(hall.and hP').exists`. Conclude with `(Finset.prod_ne_zero_iff.2 fun i _ => ht1 i) ht2`.
-/
private theorem exists_eventually_eq_zero_of_prod_analyticAt {n : ℕ} (a : ℂ) (f : Fin n → ℂ → ℂ)
    (hf : ∀ i, AnalyticAt ℂ (f i) a) (hP : ∀ᶠ t in 𝓝 a, ∏ i, f i t = 0) :
    ∃ i, ∀ᶠ t in 𝓝 a, f i t = 0 := by
  by_contra hcon
  have hcon' : ∀ i, ¬ ∀ᶠ t in 𝓝 a, f i t = 0 := fun i hi => hcon ⟨i, hi⟩
  have hne : ∀ i, ∀ᶠ t in 𝓝[≠] a, f i t ≠ 0 := fun i =>
    ((hf i).eventually_eq_zero_or_eventually_ne_zero).resolve_left (hcon' i)
  have hall : ∀ᶠ t in 𝓝[≠] a, ∀ i, f i t ≠ 0 := Filter.eventually_all.2 hne
  have hP' : ∀ᶠ t in 𝓝[≠] a, ∏ i, f i t = 0 := nhdsWithin_le_nhds hP
  obtain ⟨t, ht1, ht2⟩ := (hall.and hP').exists
  exact (Finset.prod_ne_zero_iff.2 fun i _ => ht1 i) ht2

/- English proof (translation)
Introduce `hFG hGF hAC σ _ X w hX hirr hacc`. Take `⟨d, A, ⟨W0, hW0, hfib⟩, hdom⟩` from `hGF σ X w hX hirr`. Establish `hd : 0 < d`. Break down `Nat.eq_zero_or_pos d with h0 | h0` into its components or cases. Substitute `h0` using the available equality.

Take `⟨y, ⟨hyW, hyX⟩, hyw⟩` from `(accPt_iff_nhds.1 hacc) W0 hW0`. Conclude with `absurd (hfib y ⟨hyX, hyW⟩ (Subsingleton.elim _ _)) hyw`. Conclude with `h0`. Set `i0 : Fin d` to `⟨0, hd⟩`. Set `g : Fin d → (σ → ℂ) → ℂ` to `fun j z => if j = i0 then 0 else A z j - A w j`.

Establish `hgan : ∀ j, AnalyticOnNhd ℂ (g j) Set.univ`. Introduce `j`. Distinguish the cases in `hj : j = i0`. Simplify using `only [g, hj, if_true]`. Conclude with `analyticOnNhd_const`.

Simplify using `only [g, hj, if_false]`. Conclude with `(((ContinuousLinearMap.proj j).comp A).analyticOnNhd _).sub analyticOnNhd_const`. Set `S : Set (σ → ℂ)` to `{z | z ∈ X ∧ ∀ j, g j z = 0}`. Establish `hSan : IsAnalyticNear S w` using `isAnalyticNear_zeros_inter hX g hgan`. Apply the tactic sequence `have hwS : w ∈ S := ⟨hirr.1, fun j => by by_cases hj : j = i0 <;> simp [g, hj]⟩`.

Take `⟨n, Y, hYi, W1, hW1, hYeq⟩` from `hAC σ S w hSan hwS`. Set `A1 : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ)` to `(ContinuousLinearMap.pi fun _ : Fin 1 => ContinuousLinearMap.proj i0).comp A`. Establish `hA1 : ∀ z k, A1 z k = A z i0` using `fun z k => rfl`. Establish `hfibS : ∀ x ∈ S ∩ W0, A1 x = A1 w → x = w`. Introduce and unpack `x ⟨⟨hxX, hxg⟩, hxW⟩ hx`.

Use `hfib x ⟨hxX, hxW⟩ (funext fun j => ?_)` and prove the remaining obligations. Distinguish the cases in `hj : j = i0`. Substitute `hj` using the available equality. Use `congrFun hx 0` as an intermediate fact. Simplify `this` using `[hA1]`.

Use `hxg j` as an intermediate fact. Simplify using `only [g, hj, if_false, sub_eq_zero] at this`. Conclude with `this`. Establish `himg : ∀ V ∈ 𝓝 w, A1 '' (S ∩ V) ∈ 𝓝 (A1 w)`. Introduce `V hV`.

Establish `hbig` using `hFG σ X w d A hX ⟨W0, hW0, hfib⟩ hdom V hV`. Set `ψ : (Fin 1 → ℂ) → (Fin d → ℂ)` to `fun y j => if j = i0 then y 0 else A w j`. Establish `hψc : Continuous ψ`. Use `continuous_pi fun j => ?_` and prove the remaining obligations. Distinguish the cases in `hj : j = i0`.

Simplify using `only [ψ, hj, if_true]`. Conclude with `continuous_apply 0`. Simplify using `only [ψ, hj, if_false]`. Conclude with `continuous_const`. Establish `hψw : ψ (A1 w) = A w`.

Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = i0`. Substitute `hj` using the available equality. Simplify using `[ψ, hA1]`. Simplify using `[ψ, hj]`.

Establish `hpre : ψ ⁻¹' (A '' (X ∩ V)) ∈ 𝓝 (A1 w)`. Apply `hψc.continuousAt.preimage_mem_nhds` to reduce the goal to its premises. Rewrite using `[hψw]`. Conclude with `hbig`. Use `Filter.mem_of_superset hpre ?_` and prove the remaining obligations.

Introduce and unpack `y ⟨x, ⟨hxX, hxV⟩, hxy⟩`. Use `⟨x, ⟨⟨hxX, fun j => ?_⟩, hxV⟩, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hj : j = i0`. Simplify using `[g, hj]`. Use `congrFun hxy j` as an intermediate fact.

Simplify using `only [ψ, hj, if_false] at this`. Simplify using `[g, hj, this]`. Use function extensionality and compare the values at `k`. Use `congrFun hxy i0` as an intermediate fact. Simplify using `only [ψ, if_true] at this`.

Rewrite using `[hA1, this, Subsingleton.elim k 0]`. Establish `hdomi : ∃ i, ∀ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A1 w) → (∀ᶠ z in 𝓝 w, z ∈ Y i → h (A1 z) = 0) → ∀ᶠ y in 𝓝 (A1 w), h y = 0`. Assume the negation of the conclusion as `hcon`. Establish `hcon' : ∀ i, ∃ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A1 w) ∧ (∀ᶠ z in 𝓝 w, z ∈ Y i → h (A1 z) = 0) ∧ ¬ ∀ᶠ y in 𝓝 (A1 w), h y = 0`. Introduce `i`.

Assume the negation of the conclusion as `hi`. Conclude with `hcon ⟨i, fun h ha hz => by`. Assume the negation of the conclusion as `hy`. Conclude with `hi ⟨h, ha, hz, hy⟩⟩`. Use `choose h hha hhz hhnz using hcon'`.

Set `c : ℂ →L[ℂ] (Fin 1 → ℂ)` to `ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℂ ℂ`. Set `a : ℂ` to `A w i0`. Establish `hca : c a = A1 w`. Use function extensionality and compare the values at `k`. Both sides reduce to the same expression.

Establish `hback : ∀ φ : (Fin 1 → ℂ) → ℂ, (∀ᶠ t in 𝓝 a, φ (c t) = 0) → ∀ᶠ y in 𝓝 (A1 w), φ y = 0`. Introduce `φ hφ`. Establish `hev : Tendsto (fun y : Fin 1 → ℂ => y 0) (𝓝 (A1 w)) (𝓝 a)` using `(continuous_apply 0).tendsto' _ _ rfl`. Use `filter_upwards [hev.eventually hφ] with y hy`. Establish `hyc : c (y 0) = y`.

Use function extensionality and compare the values at `k`. Rewrite using `[Subsingleton.elim k 0]`. Both sides reduce to the same expression. Rewrite `hy` using `[hyc]`. Then use the resulting hypothesis. Establish `hfan : ∀ i, AnalyticAt ℂ (fun t => h i (c t)) a`.

Introduce `i`. Establish `h1 : AnalyticAt ℂ (h i) (c a)`. Rewrite using `[hca]`. Conclude with `hha i`. Conclude with `h1.comp (c.analyticAt a)`.

Establish `hPz : ∀ᶠ t in 𝓝 a, ∏ i, h i (c t) = 0`. Establish `hV : ∀ᶠ z in 𝓝 w, ∀ i, z ∈ Y i → h i (A1 z) = 0` using `Filter.eventually_all.2 hhz`. Establish `hV' : {z | ∀ i, z ∈ Y i → h i (A1 z) = 0} ∩ W1 ∈ 𝓝 w` using `Filter.inter_mem hV hW1`. Establish `hI` using `himg _ hV'`. Establish `hy : ∀ᶠ y in 𝓝 (A1 w), ∏ i, h i y = 0` using `by filter_upwards [hI] with y hy`.

Take `⟨x, ⟨hxS, hxV, hxW⟩, rfl⟩` from `hy`. Establish `hxU : x ∈ (⋃ i, Y i) ∩ W1`. Rewrite using `[← hYeq]`. Conclude with `⟨hxS, hxW⟩`. Take `⟨i, hi⟩` from `Set.mem_iUnion.1 hxU.1`.

Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (hxV i hi)`. Establish `hev : Tendsto c (𝓝 a) (𝓝 (A1 w))`. Rewrite using `[← hca]`. Conclude with `c.continuous.tendsto a`. Conclude with `hev.eventually hy`.

Take `⟨i, hi⟩` from `exists_eventually_eq_zero_of_prod_analyticAt a (fun i t => h i (c t)) hfan hPz`. Conclude with `hhnz i (hback (h i) hi)`. Take `⟨i, hi⟩` from `hdomi`. Use `⟨Y i, W1, A1, hW1, ?_, (hYi i).1, (hYi i).2, ⟨W1 ∩ W0, Filter.inter_mem hW1 hW0, ?_⟩, hi⟩` and prove the remaining obligations. Introduce and unpack `z ⟨hzY, hzW⟩`.

Establish `hzU : z ∈ (⋃ j, Y j) ∩ W1` using `⟨Set.mem_iUnion.2 ⟨i, hzY⟩, hzW⟩`. Rewrite `hzU` using `[← hYeq]`. Conclude with `hzU.1.1`. Introduce and unpack `x ⟨hxY, hxW1, hxW0⟩ hx`. Establish `hxU : x ∈ (⋃ j, Y j) ∩ W1` using `⟨Set.mem_iUnion.2 ⟨i, hxY⟩, hxW1⟩`.

Rewrite `hxU` using `[← hYeq]`. Conclude with `hfibS x ⟨hxU.1, hxW0⟩ hx`.
-/
theorem exists_irreducible_slice :
    FiniteGermProjectionOpenAt.Statement → GermFiniteProjection.Statement → AnalyticGermComponents.Statement → ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ), IsAnalyticNear X w → GermIrreducibleAt X w → AccPt w (𝓟 X) → ∃ (Y W : Set (σ → ℂ)) (A : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ)), W ∈ 𝓝 w ∧ Y ∩ W ⊆ X ∧ IsAnalyticNear Y w ∧ GermIrreducibleAt Y w ∧ (∃ W' ∈ 𝓝 w, ∀ x ∈ Y ∩ W', A x = A w → x = w) ∧ ∀ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ Y → h (A z) = 0) → ∀ᶠ y in 𝓝 (A w), h y = 0 := by
  intro hFG hGF hAC σ _ X w hX hirr hacc
  obtain ⟨d, A, ⟨W0, hW0, hfib⟩, hdom⟩ := hGF σ X w hX hirr
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0
      obtain ⟨y, ⟨hyW, hyX⟩, hyw⟩ := (accPt_iff_nhds.1 hacc) W0 hW0
      exact absurd (hfib y ⟨hyX, hyW⟩ (Subsingleton.elim _ _)) hyw
    · exact h0
  let i0 : Fin d := ⟨0, hd⟩
  let g : Fin d → (σ → ℂ) → ℂ := fun j z => if j = i0 then 0 else A z j - A w j
  have hgan : ∀ j, AnalyticOnNhd ℂ (g j) Set.univ := by
    intro j
    by_cases hj : j = i0
    · simp only [g, hj, if_true]
      exact analyticOnNhd_const
    · simp only [g, hj, if_false]
      exact (((ContinuousLinearMap.proj j).comp A).analyticOnNhd _).sub analyticOnNhd_const
  let S : Set (σ → ℂ) := {z | z ∈ X ∧ ∀ j, g j z = 0}
  have hSan : IsAnalyticNear S w := isAnalyticNear_zeros_inter hX g hgan
  have hwS : w ∈ S := ⟨hirr.1, fun j => by by_cases hj : j = i0 <;> simp [g, hj]⟩
  obtain ⟨n, Y, hYi, W1, hW1, hYeq⟩ := hAC σ S w hSan hwS
  let A1 : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ) :=
    (ContinuousLinearMap.pi fun _ : Fin 1 => ContinuousLinearMap.proj i0).comp A
  have hA1 : ∀ z k, A1 z k = A z i0 := fun z k => rfl
  have hfibS : ∀ x ∈ S ∩ W0, A1 x = A1 w → x = w := by
    rintro x ⟨⟨hxX, hxg⟩, hxW⟩ hx
    refine hfib x ⟨hxX, hxW⟩ (funext fun j => ?_)
    by_cases hj : j = i0
    · subst hj
      have := congrFun hx 0
      simpa [hA1] using this
    · have := hxg j
      simp only [g, hj, if_false, sub_eq_zero] at this
      exact this
  have himg : ∀ V ∈ 𝓝 w, A1 '' (S ∩ V) ∈ 𝓝 (A1 w) := by
    intro V hV
    have hbig := hFG σ X w d A hX ⟨W0, hW0, hfib⟩ hdom V hV
    let ψ : (Fin 1 → ℂ) → (Fin d → ℂ) := fun y j => if j = i0 then y 0 else A w j
    have hψc : Continuous ψ := by
      refine continuous_pi fun j => ?_
      by_cases hj : j = i0
      · simp only [ψ, hj, if_true]
        exact continuous_apply 0
      · simp only [ψ, hj, if_false]
        exact continuous_const
    have hψw : ψ (A1 w) = A w := by
      funext j
      by_cases hj : j = i0
      · subst hj
        simp [ψ, hA1]
      · simp [ψ, hj]
    have hpre : ψ ⁻¹' (A '' (X ∩ V)) ∈ 𝓝 (A1 w) := by
      apply hψc.continuousAt.preimage_mem_nhds
      rw [hψw]
      exact hbig
    refine Filter.mem_of_superset hpre ?_
    rintro y ⟨x, ⟨hxX, hxV⟩, hxy⟩
    refine ⟨x, ⟨⟨hxX, fun j => ?_⟩, hxV⟩, ?_⟩
    · by_cases hj : j = i0
      · simp [g, hj]
      · have := congrFun hxy j
        simp only [ψ, hj, if_false] at this
        simp [g, hj, this]
    · funext k
      have := congrFun hxy i0
      simp only [ψ, if_true] at this
      rw [hA1, this, Subsingleton.elim k 0]
  have hdomi : ∃ i, ∀ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A1 w) →
      (∀ᶠ z in 𝓝 w, z ∈ Y i → h (A1 z) = 0) → ∀ᶠ y in 𝓝 (A1 w), h y = 0 := by
    by_contra hcon
    have hcon' : ∀ i, ∃ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A1 w) ∧
        (∀ᶠ z in 𝓝 w, z ∈ Y i → h (A1 z) = 0) ∧ ¬ ∀ᶠ y in 𝓝 (A1 w), h y = 0 := by
      intro i
      by_contra hi
      exact hcon ⟨i, fun h ha hz => by
        by_contra hy
        exact hi ⟨h, ha, hz, hy⟩⟩
    choose h hha hhz hhnz using hcon'
    let c : ℂ →L[ℂ] (Fin 1 → ℂ) := ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℂ ℂ
    let a : ℂ := A w i0
    have hca : c a = A1 w := by
      funext k
      rfl
    have hback : ∀ φ : (Fin 1 → ℂ) → ℂ, (∀ᶠ t in 𝓝 a, φ (c t) = 0) → ∀ᶠ y in 𝓝 (A1 w), φ y = 0 := by
      intro φ hφ
      have hev : Tendsto (fun y : Fin 1 → ℂ => y 0) (𝓝 (A1 w)) (𝓝 a) :=
        (continuous_apply 0).tendsto' _ _ rfl
      filter_upwards [hev.eventually hφ] with y hy
      have hyc : c (y 0) = y := by
        funext k
        rw [Subsingleton.elim k 0]
        rfl
      rwa [hyc] at hy
    have hfan : ∀ i, AnalyticAt ℂ (fun t => h i (c t)) a := by
      intro i
      have h1 : AnalyticAt ℂ (h i) (c a) := by
        rw [hca]
        exact hha i
      exact h1.comp (c.analyticAt a)
    have hPz : ∀ᶠ t in 𝓝 a, ∏ i, h i (c t) = 0 := by
      have hV : ∀ᶠ z in 𝓝 w, ∀ i, z ∈ Y i → h i (A1 z) = 0 := Filter.eventually_all.2 hhz
      have hV' : {z | ∀ i, z ∈ Y i → h i (A1 z) = 0} ∩ W1 ∈ 𝓝 w := Filter.inter_mem hV hW1
      have hI := himg _ hV'
      have hy : ∀ᶠ y in 𝓝 (A1 w), ∏ i, h i y = 0 := by
        filter_upwards [hI] with y hy
        obtain ⟨x, ⟨hxS, hxV, hxW⟩, rfl⟩ := hy
        have hxU : x ∈ (⋃ i, Y i) ∩ W1 := by
          rw [← hYeq]
          exact ⟨hxS, hxW⟩
        obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hxU.1
        exact Finset.prod_eq_zero (Finset.mem_univ i) (hxV i hi)
      have hev : Tendsto c (𝓝 a) (𝓝 (A1 w)) := by
        rw [← hca]
        exact c.continuous.tendsto a
      exact hev.eventually hy
    obtain ⟨i, hi⟩ := exists_eventually_eq_zero_of_prod_analyticAt a (fun i t => h i (c t)) hfan hPz
    exact hhnz i (hback (h i) hi)
  obtain ⟨i, hi⟩ := hdomi
  refine ⟨Y i, W1, A1, hW1, ?_, (hYi i).1, (hYi i).2, ⟨W1 ∩ W0, Filter.inter_mem hW1 hW0, ?_⟩, hi⟩
  · rintro z ⟨hzY, hzW⟩
    have hzU : z ∈ (⋃ j, Y j) ∩ W1 := ⟨Set.mem_iUnion.2 ⟨i, hzY⟩, hzW⟩
    rw [← hYeq] at hzU
    exact hzU.1.1
  · rintro x ⟨hxY, hxW1, hxW0⟩ hx
    have hxU : x ∈ (⋃ j, Y j) ∩ W1 := ⟨Set.mem_iUnion.2 ⟨i, hxY⟩, hxW1⟩
    rw [← hYeq] at hxU
    exact hfibS x ⟨hxU.1, hxW0⟩ hx

end GlobalTheory.CompanionTheory.AnalyticGermSlice
