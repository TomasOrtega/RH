import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlTwoInvariantHolomorphicMemAdjoinJInvariantStatement

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.KZ.LevelOneFrac

open Filter Topology Polynomial

/- English proof (translation)
The claim follows from `isOpen_lt continuous_const Complex.continuous_im`.
-/
theorem isOpen_Hs' : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨Complex.I, by simp [Hs]⟩, (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected⟩`.
-/
theorem isConnected_Hs' : IsConnected Hs :=
  ⟨⟨Complex.I, by simp [Hs]⟩, (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected⟩

/- English proof (translation)
Rewrite `h` using `[Filter.Eventually, mem_codiscreteWithin]`. Establish `h1` using `Filter.disjoint_principal_right.1 (h z hz)`. Establish `h2 : ∀ᶠ w in 𝓝[≠] z, w ∈ Hs` using `nhdsWithin_le_nhds (isOpen_Hs'.mem_nhds hz)`. Use `filter_upwards [h1, h2] with w hw1 hw2`. Assume the negation of the conclusion as `hP`.

Conclude with `hw1 ⟨hw2, hP⟩`.
-/
theorem eventually_nhdsNE {P : ℂ → Prop} (h : ∀ᶠ w in codiscreteWithin Hs, P w) {z : ℂ} (hz : z ∈ Hs) :
    ∀ᶠ w in 𝓝[≠] z, P w := by
  rw [Filter.Eventually, mem_codiscreteWithin] at h
  have h1 := Filter.disjoint_principal_right.1 (h z hz)
  have h2 : ∀ᶠ w in 𝓝[≠] z, w ∈ Hs := nhdsWithin_le_nhds (isOpen_Hs'.mem_nhds hz)
  filter_upwards [h1, h2] with w hw1 hw2
  by_contra hP
  exact hw1 ⟨hw2, hP⟩

/- English proof (translation)
Introduce `hneg`. Establish `hinf` using `tendsto_cobounded_of_meromorphicOrderAt_neg hneg`. Establish `hinv : Tendsto (fun w => (h w)⁻¹) (𝓝[≠] z) (𝓝 0)` using `tendsto_inv₀_cobounded.comp hinf`. Establish `hne : ∀ᶠ w in 𝓝[≠] z, h w ≠ 0`. Establish `: ({0}ᶜ : Set ℂ) ∈ Bornology.cobounded ℂ` using `Bornology.isBounded_def.1 Bornology.isBounded_singleton`.

Conclude with `hinf this`. Establish `hF : Tendsto (fun w => 1 + ∑ i ∈ Finset.range n, c i w * ((h w)⁻¹) ^ (n - i)) (𝓝[≠] z) (𝓝 (1 + ∑ i ∈ Finset.range n, c i z * (0 : ℂ) ^ (n - i)))` using `tendsto_const_nhds.add (tendsto_finsetSum _ fun i _ => ((hc i).tendsto.mono_left nhdsWithin_le_nhds).mul (hinv.pow _))`. Establish `hlim : (1 + ∑ i ∈ Finset.range n, c i z * (0 : ℂ) ^ (n - i)) = 1`. Rewrite using `[add_eq_left]`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations.

Establish `: n - i ≠ 0` using `by have := Finset.mem_range.1 hi; omega`. Rewrite using `[zero_pow this, mul_zero]`. Establish `hev : ∀ᶠ w in 𝓝[≠] z, (1 + ∑ i ∈ Finset.range n, c i w * ((h w)⁻¹) ^ (n - i)) = 0` using `by filter_upwards [hrel, hne] with w hw hw0`. Establish `hp : h w ^ n ≠ 0` using `pow_ne_zero _ hw0`. Establish `e : (1 + ∑ i ∈ Finset.range n, c i w * ((h w)⁻¹) ^ (n - i)) * h w ^ n = h w ^ n + ∑ i ∈ Finset.range n, c i w * h w ^ i`.

Rewrite using `[add_mul, one_mul, Finset.sum_mul]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hi' : i ≤ n` using `(Finset.mem_range.1 hi).le`. Establish `e2 : h w ^ n = h w ^ (n - i) * h w ^ i` using `by rw [← pow_add, Nat.sub_add_cancel hi']`.

Rewrite using `[e2, inv_pow, mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero _ hw0)]`. Rewrite `e` using `[hw]`. Conclude with `(mul_eq_zero.1 e).resolve_right hp`. Establish `h1` using `tendsto_nhds_unique hF (tendsto_const_nhds.congr' (hev.mono fun w hw => hw.symm))`. Rewrite `h1` using `[hlim]`.

Conclude with `one_ne_zero h1`.
-/
theorem not_order_neg {h : ℂ → ℂ} {z : ℂ} (n : ℕ) (c : ℕ → ℂ → ℂ) (hc : ∀ i, ContinuousAt (c i) z)
    (hrel : ∀ᶠ w in 𝓝[≠] z, h w ^ n + ∑ i ∈ Finset.range n, c i w * h w ^ i = 0) :
    ¬ meromorphicOrderAt h z < 0 := by
  intro hneg
  have hinf := tendsto_cobounded_of_meromorphicOrderAt_neg hneg
  have hinv : Tendsto (fun w => (h w)⁻¹) (𝓝[≠] z) (𝓝 0) := tendsto_inv₀_cobounded.comp hinf
  have hne : ∀ᶠ w in 𝓝[≠] z, h w ≠ 0 := by
    have : ({0}ᶜ : Set ℂ) ∈ Bornology.cobounded ℂ := Bornology.isBounded_def.1 Bornology.isBounded_singleton
    exact hinf this
  have hF : Tendsto (fun w => 1 + ∑ i ∈ Finset.range n, c i w * ((h w)⁻¹) ^ (n - i)) (𝓝[≠] z)
      (𝓝 (1 + ∑ i ∈ Finset.range n, c i z * (0 : ℂ) ^ (n - i))) :=
    tendsto_const_nhds.add (tendsto_finsetSum _ fun i _ =>
      ((hc i).tendsto.mono_left nhdsWithin_le_nhds).mul (hinv.pow _))
  have hlim : (1 + ∑ i ∈ Finset.range n, c i z * (0 : ℂ) ^ (n - i)) = 1 := by
    rw [add_eq_left]
    refine Finset.sum_eq_zero fun i hi => ?_
    have : n - i ≠ 0 := by have := Finset.mem_range.1 hi; omega
    rw [zero_pow this, mul_zero]
  have hev : ∀ᶠ w in 𝓝[≠] z, (1 + ∑ i ∈ Finset.range n, c i w * ((h w)⁻¹) ^ (n - i)) = 0 := by
    filter_upwards [hrel, hne] with w hw hw0
    have hp : h w ^ n ≠ 0 := pow_ne_zero _ hw0
    have e : (1 + ∑ i ∈ Finset.range n, c i w * ((h w)⁻¹) ^ (n - i)) * h w ^ n =
        h w ^ n + ∑ i ∈ Finset.range n, c i w * h w ^ i := by
      rw [add_mul, one_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ n := (Finset.mem_range.1 hi).le
      have e2 : h w ^ n = h w ^ (n - i) * h w ^ i := by rw [← pow_add, Nat.sub_add_cancel hi']
      rw [e2, inv_pow, mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero _ hw0)]
    rw [hw] at e
    exact (mul_eq_zero.1 e).resolve_right hp
  have h1 := tendsto_nhds_unique hF (tendsto_const_nhds.congr' (hev.mono fun w hw => hw.symm))
  rw [hlim] at h1
  exact one_ne_zero h1

/- English proof (translation)
Use `⟨toMeromorphicNFOn h Hs, ?_, toMeromorphicNFOn_eqOn_codiscrete hm⟩` and prove the remaining obligations. Introduce `z hz`. Establish `hNF : MeromorphicNFAt (toMeromorphicNFOn h Hs) z` using `meromorphicNFOn_toMeromorphicNFOn h Hs hz`. Break down `meromorphicNFAt_iff_analyticAt_or.1 hNF with ha | ⟨-, hneg, -⟩` into its components or cases. Conclude with `ha.differentiableAt.differentiableWithinAt`.

Rewrite `hneg` using `[meromorphicOrderAt_toMeromorphicNFOn hm hz]`. Conclude with `absurd hneg (not_order_neg n c (fun i => (hc i).continuousOn.continuousAt (isOpen_Hs'.mem_nhds hz)) (eventually_nhdsNE hrel hz))`.
-/
theorem exists_differentiableOn {h : ℂ → ℂ} (hm : MeromorphicOn h Hs) (n : ℕ) (c : ℕ → ℂ → ℂ)
    (hc : ∀ i, DifferentiableOn ℂ (c i) Hs)
    (hrel : ∀ᶠ w in codiscreteWithin Hs, h w ^ n + ∑ i ∈ Finset.range n, c i w * h w ^ i = 0) :
    ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ h =ᶠ[codiscreteWithin Hs] φ := by
  refine ⟨toMeromorphicNFOn h Hs, ?_, toMeromorphicNFOn_eqOn_codiscrete hm⟩
  intro z hz
  have hNF : MeromorphicNFAt (toMeromorphicNFOn h Hs) z := meromorphicNFOn_toMeromorphicNFOn h Hs hz
  rcases meromorphicNFAt_iff_analyticAt_or.1 hNF with ha | ⟨-, hneg, -⟩
  · exact ha.differentiableAt.differentiableWithinAt
  · rw [meromorphicOrderAt_toMeromorphicNFOn hm hz] at hneg
    exact absurd hneg (not_order_neg n c
      (fun i => (hc i).continuousOn.continuousAt (isOpen_Hs'.mem_nhds hz)) (eventually_nhdsNE hrel hz))

end GlobalTheory.KZ.LevelOneFrac

namespace GlobalTheory.KZ.LevelOneFrac

open Filter Topology Polynomial

/- English proof (translation)
Establish `hA : AnalyticOnNhd ℂ a Hs` using `ha.analyticOnNhd isOpen_Hs'`. Establish `hB : AnalyticOnNhd ℂ b Hs` using `hb.analyticOnNhd isOpen_Hs'`. Establish `hx : ∃ x ∈ Hs, b x ≠ 0`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Apply `hb0` to reduce the goal to its premises. Rewrite using `[← Filter.Germ.coe_zero]`. Use `Filter.Germ.coe_eq.2 ?_` and prove the remaining obligations. Use `filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz using h z hz`. Take `⟨x, hxH, hx0⟩` from `hx`.

Establish `hne : b ⁻¹' {0}ᶜ ∈ codiscreteWithin Hs` using `hB.preimage_zero_mem_codiscreteWithin hx0 hxH isConnected_Hs'`. Establish `h1 : ((b * b⁻¹ : ℂ → ℂ) : Mero) = 1`. Rewrite using `[← Filter.Germ.coe_one]`. Use `Filter.Germ.coe_eq.2 ?_` and prove the remaining obligations. Use `filter_upwards [hne] with z hz`.

Simplify using `only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply]`. Conclude with `mul_inv_cancel₀ hz`. Establish `hG : G = ((a / b : ℂ → ℂ) : Mero)`. Combine the equalities or inequalities in the displayed calculation. Establish `hM : MeromorphicOn (a / b) Hs` using `fun z hz => (hA z hz).meromorphicAt.div (hB z hz).meromorphicAt`.

Use `choose c hcd hce using hc`. Use `set n := p.natDegree`. Use `set g : ℂ → ℂ := a / b`. Establish `key : ((fun w => g w ^ n + ∑ i ∈ Finset.range n, c i w * g w ^ i : ℂ → ℂ) : Mero) = 0`. Establish `e1 : ((fun w => g w ^ n + ∑ i ∈ Finset.range n, c i w * g w ^ i : ℂ → ℂ) : Mero) = Filter.Germ.coeRingHom _ (g ^ n + ∑ i ∈ Finset.range n, c i * g ^ i)`.

Use `congr 1`. Use extensionality with `w`. Simplify using `[Finset.sum_apply]`. Rewrite using `[e1, map_add, map_pow, map_sum]`. Repeatedly rewrite using `[map_mul, map_pow]`.

Express the relevant statement in the definitionally equal form `(g : Mero) ^ n + ∑ i ∈ Finset.range n, (c i : Mero) * (g : Mero) ^ i = 0`. Rewrite using `[← hG]`. Repeatedly rewrite using `[← hce]`. Rewrite `he` using `[Polynomial.eval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_mul]`. Rewrite using `[add_comm]`.

Conclude with `he`. Establish `hrel : ∀ᶠ w in codiscreteWithin Hs, g w ^ n + ∑ i ∈ Finset.range n, c i w * g w ^ i = 0`. Use `Filter.Germ.coe_eq.1 (key.trans Filter.Germ.coe_zero.symm)` as an intermediate fact. Use `filter_upwards [this] with w hw using hw`. Take `⟨φ, hφ, hgφ⟩` from `exists_differentiableOn hM n c hcd hrel`.

Conclude with `⟨φ, hφ, hG.trans (Filter.Germ.coe_eq.2 hgφ)⟩`.
-/
theorem germ_differentiableOn (G : Mero) (a b : ℂ → ℂ) (ha : DifferentiableOn ℂ a Hs) (hb : DifferentiableOn ℂ b Hs)
    (hb0 : (b : Mero) ≠ 0) (hab : G * (b : Mero) = (a : Mero)) (p : Mero[X]) (hp : p.Monic)
    (hc : ∀ i, ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ p.coeff i = (φ : Mero)) (he : p.eval G = 0) :
    ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ G = (φ : Mero) := by
  have hA : AnalyticOnNhd ℂ a Hs := ha.analyticOnNhd isOpen_Hs'
  have hB : AnalyticOnNhd ℂ b Hs := hb.analyticOnNhd isOpen_Hs'
  have hx : ∃ x ∈ Hs, b x ≠ 0 := by
    by_contra h
    push Not at h
    apply hb0
    rw [← Filter.Germ.coe_zero]
    refine Filter.Germ.coe_eq.2 ?_
    filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz using h z hz
  obtain ⟨x, hxH, hx0⟩ := hx
  have hne : b ⁻¹' {0}ᶜ ∈ codiscreteWithin Hs :=
    hB.preimage_zero_mem_codiscreteWithin hx0 hxH isConnected_Hs'
  have h1 : ((b * b⁻¹ : ℂ → ℂ) : Mero) = 1 := by
    rw [← Filter.Germ.coe_one]
    refine Filter.Germ.coe_eq.2 ?_
    filter_upwards [hne] with z hz
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply]
    exact mul_inv_cancel₀ hz
  have hG : G = ((a / b : ℂ → ℂ) : Mero) := by
    calc G = G * ((b * b⁻¹ : ℂ → ℂ) : Mero) := by rw [h1, mul_one]
      _ = (G * (b : Mero)) * ((b⁻¹ : ℂ → ℂ) : Mero) := by rw [Filter.Germ.coe_mul, mul_assoc]
      _ = ((a / b : ℂ → ℂ) : Mero) := by rw [hab, ← Filter.Germ.coe_mul, div_eq_mul_inv]
  have hM : MeromorphicOn (a / b) Hs := fun z hz => (hA z hz).meromorphicAt.div (hB z hz).meromorphicAt
  choose c hcd hce using hc
  set n := p.natDegree
  set g : ℂ → ℂ := a / b
  have key : ((fun w => g w ^ n + ∑ i ∈ Finset.range n, c i w * g w ^ i : ℂ → ℂ) : Mero) = 0 := by
    have e1 : ((fun w => g w ^ n + ∑ i ∈ Finset.range n, c i w * g w ^ i : ℂ → ℂ) : Mero) =
        Filter.Germ.coeRingHom _ (g ^ n + ∑ i ∈ Finset.range n, c i * g ^ i) := by
      congr 1
      ext w
      simp [Finset.sum_apply]
    rw [e1, map_add, map_pow, map_sum]
    simp_rw [map_mul, map_pow]
    change (g : Mero) ^ n + ∑ i ∈ Finset.range n, (c i : Mero) * (g : Mero) ^ i = 0
    rw [← hG]
    simp_rw [← hce]
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_mul] at he
    rw [add_comm]
    exact he
  have hrel : ∀ᶠ w in codiscreteWithin Hs, g w ^ n + ∑ i ∈ Finset.range n, c i w * g w ^ i = 0 := by
    have := Filter.Germ.coe_eq.1 (key.trans Filter.Germ.coe_zero.symm)
    filter_upwards [this] with w hw using hw
  obtain ⟨φ, hφ, hgφ⟩ := exists_differentiableOn hM n c hcd hrel
  exact ⟨φ, hφ, hG.trans (Filter.Germ.coe_eq.2 hgφ)⟩

end GlobalTheory.KZ.LevelOneFrac

namespace GlobalTheory.KZ.LevelOneFrac

open Filter Topology Polynomial

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

/- English proof (translation)
Proceed by induction on `hr using Algebra.adjoin_induction with`. Consider the case `mem x hx => rw [Set.mem_singleton_iff.1 hx]`. Conclude with `hj`. Consider the case `algebraMap c => exact ⟨fun _ => ε c, differentiableOn_const _, X.an_c c⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨φ, h1, h2⟩` from `hx`. Take `⟨ψ, h3, h4⟩` from `hy`. Conclude with `⟨φ + ψ, h1.add h3, by rw [map_add, h2, h4, Filter.Germ.coe_add]⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨φ, h1, h2⟩` from `hx`.

Take `⟨ψ, h3, h4⟩` from `hy`. Conclude with `⟨φ * ψ, h1.mul h3, by rw [map_mul, h2, h4, Filter.Germ.coe_mul]⟩`.
-/
theorem holRep (X : Tower Ω ε) (hj : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) {r : X.K}
    (hr : r ∈ Algebra.adjoin Ω {X.jK}) : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an r = (φ : Mero) := by
  induction hr using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact hj
  | algebraMap c => exact ⟨fun _ => ε c, differentiableOn_const _, X.an_c c⟩
  | add x y _ _ hx hy =>
    obtain ⟨φ, h1, h2⟩ := hx
    obtain ⟨ψ, h3, h4⟩ := hy
    exact ⟨φ + ψ, h1.add h3, by rw [map_add, h2, h4, Filter.Germ.coe_add]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨φ, h1, h2⟩ := hx
    obtain ⟨ψ, h3, h4⟩ := hy
    exact ⟨φ * ψ, h1.mul h3, by rw [map_mul, h2, h4, Filter.Germ.coe_mul]⟩

/- English proof (translation)
Proceed by induction on `hr using Algebra.adjoin_induction with`. Consider the case `mem x hx => rw [Set.mem_singleton_iff.1 hx]`. Conclude with `X.j_inv γ`. Consider the case `algebraMap c => exact (X.sl (ofSL γ)).commutes c`. Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy]`.

Consider the case `mul x y _ _ hx hy => rw [map_mul, hx, hy]`.
-/
theorem sl_eq_of_mem (X : Tower Ω ε) {r : X.K} (hr : r ∈ Algebra.adjoin Ω {X.jK}) (γ : SL(2, ℤ)) :
    X.sl (ofSL γ) r = r := by
  induction hr using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact X.j_inv γ
  | algebraMap c => exact (X.sl (ofSL γ)).commutes c
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

/- English proof (translation)
Take `⟨r, hr, s, hs, rfl⟩` from `(IntermediateField.mem_adjoin_iff_div (x := c)).1 hc`. Distinguish the cases in `h : s = 0`. Use `⟨1, Subalgebra.one_mem _, one_ne_zero, ?_⟩` and prove the remaining obligations. Rewrite using `[h, div_zero, mul_zero]`. Conclude with `Subalgebra.zero_mem _`.

Use `⟨s, hs, h, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_div_cancel₀ r h]` and apply the resulting hypothesis.
-/
theorem exists_denom (X : Tower Ω ε) {c : X.K} (hc : c ∈ IntermediateField.adjoin Ω {X.jK}) :
    ∃ d ∈ Algebra.adjoin Ω {X.jK}, d ≠ 0 ∧ d * c ∈ Algebra.adjoin Ω {X.jK} := by
  obtain ⟨r, hr, s, hs, rfl⟩ := (IntermediateField.mem_adjoin_iff_div (x := c)).1 hc
  by_cases h : s = 0
  · refine ⟨1, Subalgebra.one_mem _, one_ne_zero, ?_⟩
    rw [h, div_zero, mul_zero]
    exact Subalgebra.zero_mem _
  · refine ⟨s, hs, h, ?_⟩
    rwa [mul_div_cancel₀ r h]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨1, Subalgebra.one_mem _, one_ne_zero, by simp⟩`. Consider the case `insert a s ha ih`. Take `⟨d, hd, hd0, hds⟩` from `ih (fun c hc => hs c (Finset.mem_insert_of_mem hc))`. Take `⟨e, he, he0, hea⟩` from `exists_denom X (hs a (Finset.mem_insert_self a s))`.

Use `⟨e * d, Subalgebra.mul_mem _ he hd, mul_ne_zero he0 hd0, fun c hc => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hc with rfl | hc` into its components or cases. Rewrite using `[mul_comm e d, mul_assoc]`. Conclude with `Subalgebra.mul_mem _ hd hea`. Rewrite using `[mul_assoc]`.

Conclude with `Subalgebra.mul_mem _ he (hds c hc)`.
-/
theorem exists_denom_finset (X : Tower Ω ε) (s : Finset X.K) (hs : ∀ c ∈ s, c ∈ IntermediateField.adjoin Ω {X.jK}) :
    ∃ d ∈ Algebra.adjoin Ω {X.jK}, d ≠ 0 ∧ ∀ c ∈ s, d * c ∈ Algebra.adjoin Ω {X.jK} := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, Subalgebra.one_mem _, one_ne_zero, by simp⟩
  | insert a s ha ih =>
    obtain ⟨d, hd, hd0, hds⟩ := ih (fun c hc => hs c (Finset.mem_insert_of_mem hc))
    obtain ⟨e, he, he0, hea⟩ := exists_denom X (hs a (Finset.mem_insert_self a s))
    refine ⟨e * d, Subalgebra.mul_mem _ he hd, mul_ne_zero he0 hd0, fun c hc => ?_⟩
    rcases Finset.mem_insert.1 hc with rfl | hc
    · rw [mul_comm e d, mul_assoc]
      exact Subalgebra.mul_mem _ hd hea
    · rw [mul_assoc]
      exact Subalgebra.mul_mem _ he (hds c hc)

/- English proof (translation)
Take `⟨p, hp0, hpf⟩` from `X.alg_j f`. Take `⟨d, hd, hd0, hds⟩` from `exists_denom_finset X (p.support.image (fun i => (p.coeff i : X.K))) (by`. Introduce `c hc`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 hc`. Conclude with `(p.coeff i).2)`.

Set `P : X.K[X]` to `C d * p.map (algebraMap (IntermediateField.adjoin Ω {X.jK}) X.K)`. Establish `hlift : P ∈ Polynomial.lifts (algebraMap (Algebra.adjoin Ω {X.jK}) X.K)`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Introduce `n`. Distinguish the cases in `hn : n ∈ p.support`.

Use `⟨⟨_, hds _ (Finset.mem_image_of_mem _ hn)⟩, ?_⟩` and prove the remaining obligations. Simplify using `[P, coeff_C_mul]`. Establish `h0 : p.coeff n = 0` using `Polynomial.notMem_support_iff.1 hn`. Use `⟨0, ?_⟩` and prove the remaining obligations. Simplify using `[P, coeff_C_mul, h0]`.

Take `⟨q, hq⟩` from `hlift`. Rewrite `hq` using `[Polynomial.coe_mapRingHom]`. Use `⟨q, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Rewrite `hq` using `[Polynomial.map_zero]`.

Establish `h2` using `hq.symm`. Simplify using `only [P, mul_eq_zero, Polynomial.C_eq_zero, Polynomial.map_eq_zero] at h2`. Break down `h2 with h2 | h2` into its components or cases. Conclude with `hd0 h2`. Conclude with `hp0 h2`.

Rewrite using `[aeval_def, eval₂_eq_eval_map, hq]`. Simplify using `only [P, eval_mul, eval_C, eval_map, ← aeval_def, hpf, mul_zero]`.
-/
theorem isAlgebraic_adjoin (X : Tower Ω ε) (f : X.K) : IsAlgebraic (Algebra.adjoin Ω {X.jK}) f := by
  classical
  obtain ⟨p, hp0, hpf⟩ := X.alg_j f
  obtain ⟨d, hd, hd0, hds⟩ := exists_denom_finset X (p.support.image (fun i => (p.coeff i : X.K)))
    (by
      intro c hc
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hc
      exact (p.coeff i).2)
  let P : X.K[X] := C d * p.map (algebraMap (IntermediateField.adjoin Ω {X.jK}) X.K)
  have hlift : P ∈ Polynomial.lifts (algebraMap (Algebra.adjoin Ω {X.jK}) X.K) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases hn : n ∈ p.support
    · refine ⟨⟨_, hds _ (Finset.mem_image_of_mem _ hn)⟩, ?_⟩
      simp [P, coeff_C_mul]
    · have h0 : p.coeff n = 0 := Polynomial.notMem_support_iff.1 hn
      refine ⟨0, ?_⟩
      simp [P, coeff_C_mul, h0]
  obtain ⟨q, hq⟩ := hlift
  rw [Polynomial.coe_mapRingHom] at hq
  refine ⟨q, ?_, ?_⟩
  · rintro rfl
    rw [Polynomial.map_zero] at hq
    have h2 := hq.symm
    simp only [P, mul_eq_zero, Polynomial.C_eq_zero, Polynomial.map_eq_zero] at h2
    rcases h2 with h2 | h2
    · exact hd0 h2
    · exact hp0 h2
  · rw [aeval_def, eval₂_eq_eval_map, hq]
    simp only [P, eval_mul, eval_C, eval_map, ← aeval_def, hpf, mul_zero]

/- English proof (translation)
Introduce `Ω _ _ _ ε X hj f hf`. Take `⟨y, hy0, hyi⟩` from `(isAlgebraic_adjoin X f).exists_integral_multiple`. Use `set g : X.K := (y : X.K) * f with hgdef`. Establish `hyf : y • f = g` using `rfl`. Rewrite `hyi` using `[hyf]`.

Establish `hginv : ∀ γ : SL(2, ℤ), X.sl (ofSL γ) g = g` using `fun γ => by`. Rewrite using `[hgdef, map_mul, sl_eq_of_mem X y.2 γ, hf γ]`. Take `⟨p, hpm, hpe⟩` from `hyi`. Take `⟨a, b, ha, hb, hb0, hab⟩` from `X.an_mero g`. Take `⟨φ, hφ, hgφ⟩` from `germ_differentiableOn (X.an g) a b ha hb hb0 hab (p.map (X.an.comp (algebraMap (Algebra.adjoin Ω {X.jK}) X.K))) (hpm.map _) (fun i => by rw [coeff_map]; exact holRep X hj (p.coeff i).2) (by rw [eval_map, ← Polynomial.hom_eval₂, hpe, map_zero])`.

Establish `hgR : g ∈ Algebra.adjoin Ω {X.jK}` using `GlobalTheory.T.slTwo_invariant_holomorphic_mem_adjoin_jInvariant ε X ε.injective hj g hginv ⟨φ, hφ, hgφ⟩`. Establish `hle` using `IntermediateField.algebra_adjoin_le_adjoin Ω ({X.jK} : Set X.K)`. Establish `hyL : (y : X.K) ∈ IntermediateField.adjoin Ω {X.jK}` using `hle y.2`. Establish `hgL : g ∈ IntermediateField.adjoin Ω {X.jK}` using `hle hgR`. Establish `hy0' : (y : X.K) ≠ 0` using `fun h => hy0 (Subtype.ext h)`.

Establish `hfe : f = g / y` using `by rw [hgdef, mul_div_cancel_left₀ _ hy0']`. Rewrite using `[hfe]`. Conclude with `div_mem hgL hyL`.
-/
theorem mem_adjoin_of_sl_inv : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε),
    (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ f : X.K,
    (∀ γ : SL(2, ℤ), X.sl (ofSL γ) f = f) → f ∈ IntermediateField.adjoin Ω {X.jK} := by
  intro Ω _ _ _ ε X hj f hf
  obtain ⟨y, hy0, hyi⟩ := (isAlgebraic_adjoin X f).exists_integral_multiple
  set g : X.K := (y : X.K) * f with hgdef
  have hyf : y • f = g := rfl
  rw [hyf] at hyi
  have hginv : ∀ γ : SL(2, ℤ), X.sl (ofSL γ) g = g := fun γ => by
    rw [hgdef, map_mul, sl_eq_of_mem X y.2 γ, hf γ]
  obtain ⟨p, hpm, hpe⟩ := hyi
  obtain ⟨a, b, ha, hb, hb0, hab⟩ := X.an_mero g
  obtain ⟨φ, hφ, hgφ⟩ := germ_differentiableOn (X.an g) a b ha hb hb0 hab
    (p.map (X.an.comp (algebraMap (Algebra.adjoin Ω {X.jK}) X.K))) (hpm.map _)
    (fun i => by rw [coeff_map]; exact holRep X hj (p.coeff i).2)
    (by rw [eval_map, ← Polynomial.hom_eval₂, hpe, map_zero])
  have hgR : g ∈ Algebra.adjoin Ω {X.jK} := GlobalTheory.T.slTwo_invariant_holomorphic_mem_adjoin_jInvariant ε X ε.injective hj g hginv ⟨φ, hφ, hgφ⟩
  have hle := IntermediateField.algebra_adjoin_le_adjoin Ω ({X.jK} : Set X.K)
  have hyL : (y : X.K) ∈ IntermediateField.adjoin Ω {X.jK} := hle y.2
  have hgL : g ∈ IntermediateField.adjoin Ω {X.jK} := hle hgR
  have hy0' : (y : X.K) ≠ 0 := fun h => hy0 (Subtype.ext h)
  have hfe : f = g / y := by rw [hgdef, mul_div_cancel_left₀ _ hy0']
  rw [hfe]
  exact div_mem hgL hyL

end GlobalTheory.KZ.LevelOneFrac
