import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

/- English proof (translation)
Establish `hd : HasStrictDerivAt (fun x : K => x * x) 2 1`. Use `(hasStrictDerivAt_id (1 : K)).mul (hasStrictDerivAt_id (1 : K))` as an intermediate fact. Establish `h11 : (1 : K) * id 1 + id 1 * 1 = 2` using `by simp; norm_num`. Rewrite `this` using `[h11]`. Conclude with `this`.

Establish `hF` using `hd.hasStrictFDerivAt_equiv h2`. Set `e` to `hF.toOpenPartialHomeomorph`. Establish `he : ∀ x, e x = x * x` using `fun x => rfl`. Establish `h1 : (1 : K) ∈ e.source` using `hF.mem_toOpenPartialHomeomorph_source`. Establish `h1' : e 1 = 1` using `by rw [he, mul_one]`.

Use `⟨e.target, e.open_target, h1' ▸ e.map_source h1, e.symm, e.continuousOn_symm, ?_, ?_⟩` and prove the remaining obligations. Use `e.left_inv h1` as an intermediate fact. Rewrite `this` using `[h1']`. Then use the resulting hypothesis. Introduce `u hu`. Rewrite using `[← he]`.

Conclude with `e.right_inv hu`.
-/
theorem exists_local_sqrt_nontrivial (K : Type) [NontriviallyNormedField K] [CompleteSpace K]
    (h2 : (2 : K) ≠ 0) :
    ∃ U : Set K, IsOpen U ∧ (1 : K) ∈ U ∧ ∃ s : K → K, ContinuousOn s U ∧ s 1 = 1 ∧
      ∀ u ∈ U, s u * s u = u := by
  have hd : HasStrictDerivAt (fun x : K => x * x) 2 1 := by
    have := (hasStrictDerivAt_id (1 : K)).mul (hasStrictDerivAt_id (1 : K))
    have h11 : (1 : K) * id 1 + id 1 * 1 = 2 := by simp; norm_num
    rw [h11] at this
    exact this
  have hF := hd.hasStrictFDerivAt_equiv h2
  let e := hF.toOpenPartialHomeomorph
  have he : ∀ x, e x = x * x := fun x => rfl
  have h1 : (1 : K) ∈ e.source := hF.mem_toOpenPartialHomeomorph_source
  have h1' : e 1 = 1 := by rw [he, mul_one]
  refine ⟨e.target, e.open_target, h1' ▸ e.map_source h1, e.symm, e.continuousOn_symm, ?_, ?_⟩
  · have := e.left_inv h1
    rwa [h1'] at this
  · intro u hu
    rw [← he]; exact e.right_inv hu

/- English proof (translation)
Distinguish the cases in `h : ∃ x : K, 1 < ‖x‖`. Set `: NontriviallyNormedField K` to `{ (inferInstance : NormedField K) with non_trivial := h }`. Conclude with `exists_local_sqrt_nontrivial K h2`. Use `push Not at h`. Use `⟨Metric.ball 1 1, Metric.isOpen_ball, Metric.mem_ball_self one_pos, fun _ => 1, continuousOn_const, rfl, fun u hu => ?_⟩` and prove the remaining obligations.

Rewrite `hu` using `[mem_ball_iff_norm]`. Assume the negation of the conclusion as `hne`. Establish `h0 : u - 1 ≠ 0` using `fun h0 => hne (by rw [sub_eq_zero.1 h0, mul_one])`. Establish `h3` using `h (u - 1)⁻¹`. Rewrite `h3` using `[norm_inv, inv_le_one₀ (norm_pos_iff.2 h0)]`.

Conclude with `absurd hu (not_lt.2 h3)`.
-/
theorem exists_local_sqrt (K : Type) [NormedField K] [CompleteSpace K] (h2 : (2 : K) ≠ 0) :
    ∃ U : Set K, IsOpen U ∧ (1 : K) ∈ U ∧ ∃ s : K → K, ContinuousOn s U ∧ s 1 = 1 ∧
      ∀ u ∈ U, s u * s u = u := by
  by_cases h : ∃ x : K, 1 < ‖x‖
  · let : NontriviallyNormedField K := { (inferInstance : NormedField K) with non_trivial := h }
    exact exists_local_sqrt_nontrivial K h2
  · push Not at h
    refine ⟨Metric.ball 1 1, Metric.isOpen_ball, Metric.mem_ball_self one_pos, fun _ => 1,
      continuousOn_const, rfl, fun u hu => ?_⟩
    rw [mem_ball_iff_norm] at hu
    by_contra hne
    have h0 : u - 1 ≠ 0 := fun h0 => hne (by rw [sub_eq_zero.1 h0, mul_one])
    have h3 := h (u - 1)⁻¹
    rw [norm_inv, inv_le_one₀ (norm_pos_iff.2 h0)] at h3
    exact absurd hu (not_lt.2 h3)

/- English proof (translation)
Assemble the required witnesses or components as `⟨inferInstance, inferInstance, inferInstance, exists_local_sqrt K h2⟩`.
-/
theorem nice_field (K : Type) [NormedField K] [CompleteSpace K] (h2 : (2 : K) ≠ 0) : Nice K :=
  ⟨inferInstance, inferInstance, inferInstance, exists_local_sqrt K h2⟩

/- English proof (translation)
Use `⟨inferInstance, inferInstance, ⟨Units.isOpenEmbedding_val⟩, ?_⟩` and prove the remaining obligations. Use `choose U hU h1 s hs hs1 hss using fun i => exists_local_sqrt (K i) (h2 i)`. Use `⟨Set.univ.pi U, isOpen_set_pi Set.finite_univ fun i _ => hU i, fun i _ => h1 i, fun x i => s i (x i), ?_, funext fun i => hs1 i, fun u hu => funext fun i => hss i _ (hu i trivial)⟩` and prove the remaining obligations. Conclude with `continuousOn_pi.2 fun i => (hs i).comp (continuous_apply i).continuousOn fun x hx => hx i trivial`.
-/
theorem nice_pi {ι : Type} [Fintype ι] (K : ι → Type) [∀ i, NormedField (K i)]
    [∀ i, CompleteSpace (K i)] (h2 : ∀ i, (2 : K i) ≠ 0) : Nice (∀ i, K i) := by
  refine ⟨inferInstance, inferInstance, ⟨Units.isOpenEmbedding_val⟩, ?_⟩
  choose U hU h1 s hs hs1 hss using fun i => exists_local_sqrt (K i) (h2 i)
  refine ⟨Set.univ.pi U, isOpen_set_pi Set.finite_univ fun i _ => hU i, fun i _ => h1 i,
    fun x i => s i (x i), ?_, funext fun i => hs1 i, fun u hu => funext fun i => hss i _ (hu i trivial)⟩
  exact continuousOn_pi.2 fun i => (hs i).comp (continuous_apply i).continuousOn
    fun x hx => hx i trivial

/- English proof (translation)
Introduce `F _ _`. Use `⟨nice_pi (fun w : InfinitePlace F => w.Completion) fun w => ?_, fun v => nice_field _ ?_⟩` and prove the remaining obligations. Establish `: CharZero w.Completion` using `charZero_of_injective_algebraMap (algebraMap F _).injective`. Conclude with `two_ne_zero`. Establish `: CharZero (Fv F v)` using `charZero_of_injective_algebraMap (algebraMap F _).injective`.

Conclude with `two_ne_zero`.
-/
theorem nice_ainf_fv : ∀ (F : Type) [Field F] [NumberField F],
    Nice (Ainf F) ∧ ∀ v : HeightOneSpectrum (𝓞 F), Nice (Fv F v) := by
  intro F _ _
  refine ⟨nice_pi (fun w : InfinitePlace F => w.Completion) fun w => ?_, fun v => nice_field _ ?_⟩
  · have : CharZero w.Completion := charZero_of_injective_algebraMap (algebraMap F _).injective
    exact two_ne_zero
  · have : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F _).injective
    exact two_ne_zero

end GlobalTheory.GaugeEx
