import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StChartDualRational
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

namespace ChartDualRational

/- English proof (translation)
Use `choose N hN using h`. Conclude with `⟨∑ a, N a, fun a ↦ mono a _ _ (Finset.single_le_sum (by simp) (Finset.mem_univ a)) (hN a)⟩`.
-/
theorem exists_uniform {α : Type*} [Fintype α] (P : α → ℕ → Prop) (mono : ∀ a n m, n ≤ m → P a n → P a m)
    (h : ∀ a, ∃ n, P a n) : ∃ n, ∀ a, P a n := by
  choose N hN using h
  exact ⟨∑ a, N a, fun a ↦ mono a _ _ (Finset.single_le_sum (by simp) (Finset.mem_univ a)) (hN a)⟩

variable {Ω : Type*} [Field Ω] {R : Subalgebra ℤ Ω}

/- English proof (translation)
Rewrite using `[← pow_mul_pow_sub u hnm, mul_comm (u ^ n), mul_assoc]`. Conclude with `mul_mem (pow_mem hu _) h`.
-/
theorem pow_mul_mem_mono {u y : Ω} (hu : u ∈ R) {n m : ℕ} (hnm : n ≤ m) (h : u ^ n * y ∈ R) :
    u ^ m * y ∈ R := by
  rw [← pow_mul_pow_sub u hnm, mul_comm (u ^ n), mul_assoc]
  exact mul_mem (pow_mem hu _) h

/- English proof (translation)
Take `⟨N, hN⟩` from `exists_uniform _ (fun l _ _ h ↦ pow_mul_mem_mono (hf l) h) hy`. Set `f' : Fin k → R` to `fun l ↦ ⟨f l, hf l⟩`. Establish `htop : Ideal.span (Set.range f') = ⊤`. Rewrite using `[Ideal.eq_top_iff_one]`. Establish `h1 : ∑ l, (⟨c l, hc l⟩ : R) * f' l = 1` using `Subtype.ext (by simpa [f'] using hsum)`.

Rewrite using `[← h1]`. Conclude with `Ideal.sum_mem _ fun l _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)`. Establish `hN'` using `Ideal.span_pow_eq_top _ htop N`. Rewrite `hN'` using `[← Set.range_comp, Ideal.eq_top_iff_one]`. Take `⟨d, hd⟩` from `(Submodule.mem_span_range_iff_exists_fun R).1 hN'`.

Establish `hd' : ∑ l, (d l : Ω) * f l ^ N = 1` using `by simpa [f'] using congrArg Subtype.val hd`. Establish `: y = ∑ l, (d l : Ω) * (f l ^ N * y)`. Repeatedly rewrite using `[← mul_assoc, ← Finset.sum_mul, hd', one_mul]`. Rewrite using `[this]`. Conclude with `sum_mem fun l _ ↦ mul_mem (d l).2 (hN l)`.
-/
theorem mem_of_cover {k : ℕ} {f c : Fin k → Ω} (hf : ∀ l, f l ∈ R) (hc : ∀ l, c l ∈ R) (hsum : ∑ l, c l * f l = 1)
    {y : Ω} (hy : ∀ l, ∃ N : ℕ, f l ^ N * y ∈ R) : y ∈ R := by
  obtain ⟨N, hN⟩ := exists_uniform _ (fun l _ _ h ↦ pow_mul_mem_mono (hf l) h) hy
  let f' : Fin k → R := fun l ↦ ⟨f l, hf l⟩
  have htop : Ideal.span (Set.range f') = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h1 : ∑ l, (⟨c l, hc l⟩ : R) * f' l = 1 := Subtype.ext (by simpa [f'] using hsum)
    rw [← h1]
    exact Ideal.sum_mem _ fun l _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)
  have hN' := Ideal.span_pow_eq_top _ htop N
  rw [← Set.range_comp, Ideal.eq_top_iff_one] at hN'
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hN'
  have hd' : ∑ l, (d l : Ω) * f l ^ N = 1 := by simpa [f'] using congrArg Subtype.val hd
  have : y = ∑ l, (d l : Ω) * (f l ^ N * y) := by
    simp_rw [← mul_assoc, ← Finset.sum_mul, hd', one_mul]
  rw [this]
  exact sum_mem fun l _ ↦ mul_mem (d l).2 (hN l)

/- English proof (translation)
Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem y hy => exact IntermediateField.subset_adjoin _ _ hy`. Consider the case `algebraMap r => simp`. Consider the case `add y z _ _ hy hz => exact add_mem hy hz`. Consider the case `mul y z _ _ hy hz => exact mul_mem hy hz`.
-/
theorem mem_adjoin_of_mem_chartRing [CharZero Ω] {ι : Type*} (x : ι → Ω) (i : ι) {a : Ω} (ha : a ∈ chartRing ℤ x i) :
    a ∈ IntermediateField.adjoin ℚ (Set.range fun j ↦ x j / x i) := by
  induction ha using Algebra.adjoin_induction with
  | mem y hy => exact IntermediateField.subset_adjoin _ _ hy
  | algebraMap r => simp
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz => exact mul_mem hy hz

end ChartDualRational

open ChartDualRational in

/- English proof (translation)
Introduce `Ω _ _ ι κ _ _ E _ _ x B φ i₀ hx hsec hgen`. Take `⟨r, f, c, hf, hc, hsum, hfr⟩` from `B.frame i₀ hx`. Use `choose b hbli hbsp hbiff using hfr`. Choose the witnesses or unpack the hypotheses as in `⟨l₀, hl₀⟩ : ∃ l, f l ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push Not at h`. Simplify using `[h] at hsum`. Apply the tactic sequence `have hn1 : ∀ l p, ∃ m : ℕ, f l ^ m • b l p ∈ B.lat i₀ := fun l p ↦ (hbiff l (b l p)).2 ⟨Pi.single p 1, fun q ↦ ⟨0, by by_cases hq : q = p <;> simp [hq, one_mem, zero_mem]⟩, by simp [Pi.single_apply]⟩`. Use `choose n hn using fun l ↦ exists_uniform (fun p m ↦ f l ^ m • b l p ∈ B.lat i₀) (fun p m m' hmm' h ↦ by`. Rewrite using `[← pow_mul_pow_sub (f l) hmm', mul_comm, mul_smul]`.

Conclude with `B.stable i₀ _ (pow_mem (hf l) _) _ h) (hn1 l)`. Take `⟨bb, hbb⟩ : ∃ bb : Module.Basis (Fin 2) Ω E, ∀ q, bb q = b l₀ q` from `⟨Module.Basis.mk (hbli l₀) (hbsp l₀).ge, fun q ↦ by simp⟩`. Establish `hcoord : ∀ v ∈ B.lat i₀, ∀ q, ∃ t : ℕ, f l₀ ^ t * bb.coord q v ∈ chartRing ℤ x i₀`. Introduce `v hv q`. Take `⟨a, ha, rfl⟩` from `(hbiff l₀ v).1 ⟨0, by simpa using hv⟩`.

Take `⟨t, ht⟩` from `ha q`. Use `⟨t, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `have : bb.coord q (∑ p, a p • b l₀ p) = a q := by fin_cases q <;> simp [← hbb, Module.Basis.coord_apply, Module.Basis.repr_self]`. Rewrite using `[this]` and apply the resulting hypothesis. Take `⟨M, hM⟩` from `exists_uniform (fun (a : Fin r × Fin 2 × Fin 2) t ↦ f l₀ ^ t * bb.coord a.2.2 (f a.1 ^ n a.1 • b a.1 a.2.1) ∈ chartRing ℤ x i₀) (fun _ _ _ h h' ↦ pow_mul_mem_mono (hf l₀) h h') (fun a ↦ hcoord _ (hn a.1 a.2.1) _)`.

Establish `hdual : ∀ q, f l₀ ^ M • bb.coord q ∈ T.dualLat B i₀`. Introduce `q`. Simplify using `only [T.dualLat, Set.mem_ofPred_eq]`. Introduce `v hv`. Rewrite using `[LinearMap.smul_apply, smul_eq_mul]`.

Use `mem_of_cover hf hc hsum fun l ↦ ?_` and prove the remaining obligations. Take `⟨a, ha, rfl⟩` from `(hbiff l v).1 ⟨0, by simpa using hv⟩`. Take `⟨m, hm⟩` from `exists_uniform (fun p t ↦ f l ^ t * a p ∈ chartRing ℤ x i₀) (fun p _ _ h h' ↦ pow_mul_mem_mono (hf l) h h') ha`. Use `⟨m + n l, ?_⟩` and prove the remaining obligations. Establish `: f l ^ (m + n l) * (f l₀ ^ M * bb.coord q (∑ p, a p • b l p)) = ∑ p, (f l ^ m * a p) * (f l₀ ^ M * bb.coord q (f l ^ n l • b l p))`.

Simplify using `only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum, pow_add]`. Conclude with `Finset.sum_congr rfl fun p _ ↦ by ring`. Rewrite using `[this]`. Conclude with `sum_mem fun p _ ↦ mul_mem (hm p) (hM (l, p, q))`. Use `choose d hdR hd using fun q ↦ hgen i₀ hx _ (hdual q)`.

Use `⟨bb, fun k q ↦ φ k (bb q) / x i₀, fun k q ↦ by field_simp, fun k q ↦ ?_, ?_⟩` and prove the remaining obligations. Establish `hs : f l₀ ^ n l₀ • bb q ∈ B.lat i₀` using `by rw [hbb]; exact hn l₀ q`. Take `⟨a, ha, hae⟩` from `(mem_lineLat x 1 i₀ _).1 (hsec i₀ hx k _ hs)`. Rewrite `hae` using `[map_smul, smul_eq_mul, pow_one]`. Establish `: φ k (bb q) / x i₀ = a / f l₀ ^ n l₀`.

Rewrite using `[div_eq_div_iff hx (pow_ne_zero _ hl₀), hae]`. Expand and normalize the polynomial expressions, which then agree. Use `show φ k (bb q) / x i₀ ∈ _`. Rewrite using `[this]`. Conclude with `div_mem (mem_adjoin_of_mem_chartRing x i₀ ha) (pow_mem (mem_adjoin_of_mem_chartRing x i₀ (hf l₀)) _)`.

Assume the negation of the conclusion as `hmin push Not at hmin`. Establish `hm : ∀ k k', φ k (bb 0) / x i₀ * (φ k' (bb 1) / x i₀) - φ k (bb 1) / x i₀ * (φ k' (bb 0) / x i₀) = 0` using `fun k k' ↦ hmin k k'`. Establish `hrow : ∀ q p, ∑ k, d q k * (φ k (bb p) / x i₀) = f l₀ ^ M * if p = q then 1 else 0`. Introduce `q p`. Establish `h` using `LinearMap.congr_fun (hd q) (bb p)`.

Simplify using `only [LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, LinearMap.sum_apply, smul_eq_mul] at h`. Rewrite using `[h]`. Conclude with `Finset.sum_congr rfl fun k _ ↦ by ring`. Establish `hdet : (∑ k, d 0 k * (φ k (bb 0) / x i₀)) * (∑ k, d 1 k * (φ k (bb 1) / x i₀)) - (∑ k, d 0 k * (φ k (bb 1) / x i₀)) * (∑ k, d 1 k * (φ k (bb 0) / x i₀)) = 0`. Rewrite using `[Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]`.

Use `Finset.sum_eq_zero fun k _ ↦ ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_eq_zero fun k' _ ↦ ?_` and prove the remaining obligations. Take the linear combination `(d 0 k * d 1 k') * hm k k'`. Rewrite `hdet` using `[hrow 0 0, hrow 1 1, hrow 0 1, hrow 1 0]`.

Simplify using `[hl₀] at hdet`.
-/
theorem ChartDualRational.proof : ChartDualRational.Statement := by
  intro Ω _ _ ι κ _ _ E _ _ x B φ i₀ hx hsec hgen
  obtain ⟨r, f, c, hf, hc, hsum, hfr⟩ := B.frame i₀ hx
  choose b hbli hbsp hbiff using hfr
  obtain ⟨l₀, hl₀⟩ : ∃ l, f l ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at hsum
  have hn1 : ∀ l p, ∃ m : ℕ, f l ^ m • b l p ∈ B.lat i₀ := fun l p ↦
    (hbiff l (b l p)).2 ⟨Pi.single p 1, fun q ↦ ⟨0, by by_cases hq : q = p <;> simp [hq, one_mem, zero_mem]⟩,
      by simp [Pi.single_apply]⟩
  choose n hn using fun l ↦ exists_uniform (fun p m ↦ f l ^ m • b l p ∈ B.lat i₀)
    (fun p m m' hmm' h ↦ by
      rw [← pow_mul_pow_sub (f l) hmm', mul_comm, mul_smul]
      exact B.stable i₀ _ (pow_mem (hf l) _) _ h) (hn1 l)
  obtain ⟨bb, hbb⟩ : ∃ bb : Module.Basis (Fin 2) Ω E, ∀ q, bb q = b l₀ q :=
    ⟨Module.Basis.mk (hbli l₀) (hbsp l₀).ge, fun q ↦ by simp⟩
  have hcoord : ∀ v ∈ B.lat i₀, ∀ q, ∃ t : ℕ, f l₀ ^ t * bb.coord q v ∈ chartRing ℤ x i₀ := by
    intro v hv q
    obtain ⟨a, ha, rfl⟩ := (hbiff l₀ v).1 ⟨0, by simpa using hv⟩
    obtain ⟨t, ht⟩ := ha q
    refine ⟨t, ?_⟩
    have : bb.coord q (∑ p, a p • b l₀ p) = a q := by
      fin_cases q <;> simp [← hbb, Module.Basis.coord_apply, Module.Basis.repr_self]
    rwa [this]
  obtain ⟨M, hM⟩ := exists_uniform
    (fun (a : Fin r × Fin 2 × Fin 2) t ↦ f l₀ ^ t * bb.coord a.2.2 (f a.1 ^ n a.1 • b a.1 a.2.1) ∈ chartRing ℤ x i₀)
    (fun _ _ _ h h' ↦ pow_mul_mem_mono (hf l₀) h h') (fun a ↦ hcoord _ (hn a.1 a.2.1) _)
  have hdual : ∀ q, f l₀ ^ M • bb.coord q ∈ T.dualLat B i₀ := by
    intro q
    simp only [T.dualLat, Set.mem_ofPred_eq]
    intro v hv
    rw [LinearMap.smul_apply, smul_eq_mul]
    refine mem_of_cover hf hc hsum fun l ↦ ?_
    obtain ⟨a, ha, rfl⟩ := (hbiff l v).1 ⟨0, by simpa using hv⟩
    obtain ⟨m, hm⟩ := exists_uniform (fun p t ↦ f l ^ t * a p ∈ chartRing ℤ x i₀)
      (fun p _ _ h h' ↦ pow_mul_mem_mono (hf l) h h') ha
    refine ⟨m + n l, ?_⟩
    have : f l ^ (m + n l) * (f l₀ ^ M * bb.coord q (∑ p, a p • b l p)) =
        ∑ p, (f l ^ m * a p) * (f l₀ ^ M * bb.coord q (f l ^ n l • b l p)) := by
      simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum, pow_add]
      exact Finset.sum_congr rfl fun p _ ↦ by ring
    rw [this]
    exact sum_mem fun p _ ↦ mul_mem (hm p) (hM (l, p, q))
  choose d hdR hd using fun q ↦ hgen i₀ hx _ (hdual q)
  refine ⟨bb, fun k q ↦ φ k (bb q) / x i₀, fun k q ↦ by field_simp, fun k q ↦ ?_, ?_⟩
  · have hs : f l₀ ^ n l₀ • bb q ∈ B.lat i₀ := by rw [hbb]; exact hn l₀ q
    obtain ⟨a, ha, hae⟩ := (mem_lineLat x 1 i₀ _).1 (hsec i₀ hx k _ hs)
    rw [map_smul, smul_eq_mul, pow_one] at hae
    have : φ k (bb q) / x i₀ = a / f l₀ ^ n l₀ := by
      rw [div_eq_div_iff hx (pow_ne_zero _ hl₀), hae]
      ring
    show φ k (bb q) / x i₀ ∈ _
    rw [this]
    exact div_mem (mem_adjoin_of_mem_chartRing x i₀ ha) (pow_mem (mem_adjoin_of_mem_chartRing x i₀ (hf l₀)) _)
  · by_contra hmin
    push Not at hmin
    have hm : ∀ k k', φ k (bb 0) / x i₀ * (φ k' (bb 1) / x i₀) - φ k (bb 1) / x i₀ * (φ k' (bb 0) / x i₀) = 0 :=
      fun k k' ↦ hmin k k'
    have hrow : ∀ q p, ∑ k, d q k * (φ k (bb p) / x i₀) = f l₀ ^ M * if p = q then 1 else 0 := by
      intro q p
      have h := LinearMap.congr_fun (hd q) (bb p)
      simp only [LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
        LinearMap.sum_apply, smul_eq_mul] at h
      rw [h]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
    have hdet : (∑ k, d 0 k * (φ k (bb 0) / x i₀)) * (∑ k, d 1 k * (φ k (bb 1) / x i₀)) -
        (∑ k, d 0 k * (φ k (bb 1) / x i₀)) * (∑ k, d 1 k * (φ k (bb 0) / x i₀)) = 0 := by
      rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun k' _ ↦ ?_
      linear_combination (d 0 k * d 1 k') * hm k k'
    rw [hrow 0 0, hrow 1 1, hrow 0 1, hrow 1 0] at hdet
    simp [hl₀] at hdet

end GroundTheory.Heights₂.Heights.Inter
