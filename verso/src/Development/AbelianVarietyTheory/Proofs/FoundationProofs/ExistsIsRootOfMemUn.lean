import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTowerPlaceAtUpperHalfPlanePointStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHolomorphicRootUpperHalfPlaneStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
open Filter Topology

noncomputable section

namespace GlobalTheory.KZ.H3.UnRoot

/- English proof (translation)
The claim follows from `isOpen_lt continuous_const Complex.continuous_im`.
-/
lemma isOpen_Hs : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

/- English proof (translation)
The claim follows from `(convex_halfSpace_gt Complex.imLm.isLinear (0:ℝ)).isPreconnected`.
-/
lemma isPreconnected_Hs : IsPreconnected Hs :=
  (convex_halfSpace_gt Complex.imLm.isLinear (0:ℝ)).isPreconnected

/- English proof (translation)
Establish `h' : ∀ᶠ z in codiscreteWithin Hs, φ z = ψ z` using `Filter.Germ.coe_eq.mp h`. Rewrite `h'` using `[Filter.eventually_iff, mem_codiscreteWithin]`. Establish `hd` using `Filter.disjoint_principal_right.mp (h' τ hτ)`. Establish `hH : Hs ∈ 𝓝[≠] τ` using `mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hτ)`. Use `filter_upwards [hH, hd] with z hz1 hz2`.

Assume the negation of the conclusion as `hne`. Conclude with `hz2 ⟨hz1, hne⟩`.
-/
lemma eventually_of_germ_eq {φ ψ : ℂ → ℂ} (h : (φ : Mero) = (ψ : Mero)) {τ : ℂ} (hτ : τ ∈ Hs) :
    ∀ᶠ z in 𝓝[≠] τ, φ z = ψ z := by
  have h' : ∀ᶠ z in codiscreteWithin Hs, φ z = ψ z := Filter.Germ.coe_eq.mp h
  rw [Filter.eventually_iff, mem_codiscreteWithin] at h'
  have hd := Filter.disjoint_principal_right.mp (h' τ hτ)
  have hH : Hs ∈ 𝓝[≠] τ := mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hτ)
  filter_upwards [hH, hd] with z hz1 hz2
  by_contra hne
  exact hz2 ⟨hz1, hne⟩

/- English proof (translation)
Establish `hτ : F τ = G τ` using `tendsto_nhds_unique (hF.tendsto.mono_left nhdsWithin_le_nhds) ((hG.tendsto.mono_left nhdsWithin_le_nhds).congr' (h.mono fun z hz => hz.symm))`. Establish `h2` using `eventually_nhdsWithin_iff.mp h`. Use `filter_upwards [h2] with z hz`. Distinguish the cases in `hz' : z = τ`. Substitute `hz'` using the available equality.

Conclude with `hτ`. Conclude with `hz hz'`.
-/
lemma eq_nhds_of_punctured {F G : ℂ → ℂ} {τ : ℂ} (hF : ContinuousAt F τ) (hG : ContinuousAt G τ)
    (h : ∀ᶠ z in 𝓝[≠] τ, F z = G z) : F =ᶠ[𝓝 τ] G := by
  have hτ : F τ = G τ :=
    tendsto_nhds_unique (hF.tendsto.mono_left nhdsWithin_le_nhds)
      ((hG.tendsto.mono_left nhdsWithin_le_nhds).congr' (h.mono fun z hz => hz.symm))
  have h2 := eventually_nhdsWithin_iff.mp h
  filter_upwards [h2] with z hz
  by_cases hz' : z = τ
  · subst hz'; exact hτ
  · exact hz hz'

/- English proof (translation)
Introduce `htop`. Apply `h0` to reduce the goal to its premises. Establish `hA : AnalyticOnNhd ℂ a Hs` using `ha.analyticOnNhd isOpen_Hs`. Establish `hz` using `hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Hs hτ (analyticOrderAt_eq_top.mp htop)`. Establish `: ∀ᶠ z in codiscreteWithin Hs, a z = (0 : ℂ → ℂ) z` using `Filter.mem_of_superset (self_mem_codiscreteWithin Hs) fun z hz' => hz hz'`.

Rewrite using `[← Filter.Germ.coe_zero]`. Conclude with `Filter.Germ.coe_eq.mpr this`.
-/
lemma order_ne_top {a : ℂ → ℂ} (ha : DifferentiableOn ℂ a Hs) (h0 : (a : Mero) ≠ 0) {τ : ℂ} (hτ : τ ∈ Hs) :
    analyticOrderAt a τ ≠ ⊤ := by
  intro htop
  apply h0
  have hA : AnalyticOnNhd ℂ a Hs := ha.analyticOnNhd isOpen_Hs
  have hz := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Hs hτ
    (analyticOrderAt_eq_top.mp htop)
  have : ∀ᶠ z in codiscreteWithin Hs, a z = (0 : ℂ → ℂ) z :=
    Filter.mem_of_superset (self_mem_codiscreteWithin Hs) fun z hz' => hz hz'
  rw [← Filter.Germ.coe_zero]
  exact Filter.Germ.coe_eq.mpr this

/- English proof (translation)
The claim follows from `Filter.Germ.coe_eq.mpr (Filter.mem_of_superset (self_mem_codiscreteWithin Hs) fun z hz => h z hz)`.
-/
lemma germ_eq_of_eqOn {φ ψ : ℂ → ℂ} (h : ∀ z ∈ Hs, φ z = ψ z) : (φ : Mero) = (ψ : Mero) :=
  Filter.Germ.coe_eq.mpr (Filter.mem_of_superset (self_mem_codiscreteWithin Hs) fun z hz => h z hz)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

/- English proof (translation)
Introduce `h`. Apply `hb` to reduce the goal to its premises. Establish `e : X.an ((f⁻¹ : X.Kˣ) : X.K) * X.an (f : X.K) = 1`. Rewrite using `[← map_mul, Units.inv_mul, map_one]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma num_ne_zero (X : Tower Ω ε) (f : X.Kˣ) {a b : ℂ → ℂ} (hb : (b : Mero) ≠ 0)
    (hf : X.an (f : X.K) * (b : Mero) = (a : Mero)) : (a : Mero) ≠ 0 := by
  intro h
  apply hb
  have e : X.an ((f⁻¹ : X.Kˣ) : X.K) * X.an (f : X.K) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  calc (b : Mero) = X.an ((f⁻¹ : X.Kˣ) : X.K) * (X.an (f : X.K) * b) := by rw [← mul_assoc, e, one_mul]
    _ = 0 := by rw [hf, h, mul_zero]

end GlobalTheory.KZ.H3.UnRoot

namespace GlobalTheory.KZ.H3.UnRoot

/- English proof (translation)
Introduce `Ω _ _ ε X hj m hm f hf`. Take `⟨a0, b0, ha0, hb0, hb0ne, hf0⟩` from `X.an_mero (f : X.K)`. Establish `ha0ne : (a0 : Mero) ≠ 0` using `num_ne_zero X f hb0ne hf0`. Take `⟨m', rfl⟩ : ∃ m', m = m' + 1` from `⟨m - 1, by omega⟩`. Establish `hA : ∀ {c : ℂ → ℂ}, DifferentiableOn ℂ c Hs → ∀ τ ∈ Hs, AnalyticAt ℂ c τ` using `fun hc τ hτ => hc.analyticOnNhd isOpen_Hs τ hτ`.

Establish `hord : ∀ τ ∈ Hs, ∃ k : ℕ, analyticOrderAt (a0 * b0 ^ m') τ = (((m' + 1) * k : ℕ) : ℕ∞)`. Introduce `τ hτ`. Take `⟨W, hW, hWmem⟩` from `GlobalTheory.T.exists_tower_place_at_upperHalfPlane_point Ω ε X hj τ hτ`. Take `⟨g, hg⟩` from `hf W hW`. Use `set u : X.K := (f : X.K) / (g : X.K) ^ (m' + 1) with hu`.

Establish `hgm : (g : X.K) ^ (m' + 1) ≠ 0` using `pow_ne_zero _ g.ne_zero`. Establish `hune : u ≠ 0` using `div_ne_zero f.ne_zero hgm`. Establish `huW : u ∈ W` using `(W.valuation_le_one_iff u).mp hg.le`. Establish `huW' : u⁻¹ ∈ W` using `(W.valuation_le_one_iff u⁻¹).mp (by rw [map_inv₀, hg, inv_one])`. Take `⟨φ, hφ, hφa⟩` from `(hWmem u).mp huW`.

Take `⟨ψ, hψ, hψa⟩` from `(hWmem u⁻¹).mp huW'`. Establish `hφψ : ((φ * ψ : ℂ → ℂ) : Mero) = ((1 : ℂ → ℂ) : Mero)`. Rewrite using `[Filter.Germ.coe_mul, Filter.Germ.coe_one, ← hφ, ← hψ, ← map_mul, mul_inv_cancel₀ hune, map_one]`. Establish `hφτ : φ τ ≠ 0`. Establish `e : φ τ * ψ τ = 1` using `(eq_nhds_of_punctured (hφa.continuousAt.mul hψa.continuousAt) continuousAt_const (eventually_of_germ_eq hφψ hτ)).self_of_nhds`.

Introduce `h0`. Rewrite `e` using `[h0, zero_mul]`. Conclude with `zero_ne_one e`. Take `⟨a1, b1, ha1, hb1, hb1ne, hg1⟩` from `X.an_mero (g : X.K)`. Establish `ha1ne : (a1 : Mero) ≠ 0` using `num_ne_zero X g hb1ne hg1`.

Establish `hfu : X.an (f : X.K) = X.an u * X.an (g : X.K) ^ (m' + 1)`. Rewrite using `[← map_pow, ← map_mul, hu, div_mul_cancel₀ _ hgm]`. Establish `hgerm : ((a0 * b1 ^ (m' + 1) : ℂ → ℂ) : Mero) = ((φ * a1 ^ (m' + 1) * b0 : ℂ → ℂ) : Mero)`. Simplify using `only [Filter.Germ.coe_mul, Filter.Germ.coe_pow]`. Rewrite using `[← hf0, ← hg1, hfu, hφ]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hev` using `eq_nhds_of_punctured ((hA ha0 τ hτ).continuousAt.mul ((hA hb1 τ hτ).continuousAt.pow _)) ((hφa.continuousAt.mul ((hA ha1 τ hτ).continuousAt.pow _)).mul (hA hb0 τ hτ).continuousAt) (eventually_of_germ_eq hgerm hτ)`. Establish `hcong` using `analyticOrderAt_congr hev`. Rewrite `hcong` using `[analyticOrderAt_mul (hA ha0 τ hτ) ((hA hb1 τ hτ).pow _), analyticOrderAt_pow (hA hb1 τ hτ), analyticOrderAt_mul (hφa.mul ((hA ha1 τ hτ).pow _)) (hA hb0 τ hτ), analyticOrderAt_mul hφa ((hA ha1 τ hτ).pow _), analyticOrderAt_pow (hA ha1 τ hτ), hφa.analyticOrderAt_eq_zero.mpr hφτ]`. Take `⟨oA0, orbitMap_conj_smul_zero⟩` from `ENat.ne_top_iff_exists.mp (order_ne_top ha0 ha0ne hτ)`.

Take `⟨oB0, eB0⟩` from `ENat.ne_top_iff_exists.mp (order_ne_top hb0 hb0ne hτ)`. Take `⟨oA1, orbitMap_conj_smul_one⟩` from `ENat.ne_top_iff_exists.mp (order_ne_top ha1 ha1ne hτ)`. Take `⟨oB1, eB1⟩` from `ENat.ne_top_iff_exists.mp (order_ne_top hb1 hb1ne hτ)`. Rewrite `hcong` using `[← orbitMap_conj_smul_zero, ← eB0, ← orbitMap_conj_smul_one, ← eB1]`. Establish `heq : oA0 + (m' + 1) * oB1 = (m' + 1) * oA1 + oB0`.

Simplify using `only [nsmul_eq_mul, zero_add] at hcong`. Conclude with `hcong` after adjusting the coercions. Establish `hdvd : (m' + 1) ∣ oA0 + m' * oB0` using `Int.natCast_dvd_natCast.mp ⟨(oA1 : ℤ) + oB0 - oB1, by`. Use `congrArg (fun n : ℕ => (n : ℤ)) heq` as an intermediate fact. Move the coercions through the operations in `at this ⊢`.

Take the linear combination `this⟩`. Take `⟨k, hk⟩` from `hdvd`. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[analyticOrderAt_mul (hA ha0 τ hτ) ((hA hb0 τ hτ).pow _), analyticOrderAt_pow (hA hb0 τ hτ), ← orbitMap_conj_smul_zero, ← eB0, ← hk]`. Simplify using `only [nsmul_eq_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take `⟨r, hr, hrm⟩` from `GlobalTheory.T.exists_holomorphic_root_upperHalfPlane (a0 * b0 ^ m') (m' + 1) hm (ha0.mul (hb0.pow _)) hord`. Use `⟨r, b0, hr, hb0, hb0ne, ?_⟩` and prove the remaining obligations. Establish `e1 : ((r ^ (m' + 1) : ℂ → ℂ) : Mero) = ((a0 * b0 ^ m' : ℂ → ℂ) : Mero)` using `germ_eq_of_eqOn fun z hz => by simpa using hrm z hz`.

Simplify using `only [Filter.Germ.coe_pow, Filter.Germ.coe_mul] at e1 ⊢`. Rewrite using `[e1, ← hf0]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_isRoot_of_mem_Un : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), JHol X →
    ∀ (m : ℕ), 0 < m → ∀ f ∈ X.Un m, ∃ a b : ℂ → ℂ, IsRoot X m f a b := by
  intro Ω _ _ ε X hj m hm f hf
  obtain ⟨a0, b0, ha0, hb0, hb0ne, hf0⟩ := X.an_mero (f : X.K)
  have ha0ne : (a0 : Mero) ≠ 0 := num_ne_zero X f hb0ne hf0
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hA : ∀ {c : ℂ → ℂ}, DifferentiableOn ℂ c Hs → ∀ τ ∈ Hs, AnalyticAt ℂ c τ :=
    fun hc τ hτ => hc.analyticOnNhd isOpen_Hs τ hτ
  have hord : ∀ τ ∈ Hs, ∃ k : ℕ, analyticOrderAt (a0 * b0 ^ m') τ = (((m' + 1) * k : ℕ) : ℕ∞) := by
    intro τ hτ
    obtain ⟨W, hW, hWmem⟩ := GlobalTheory.T.exists_tower_place_at_upperHalfPlane_point Ω ε X hj τ hτ
    obtain ⟨g, hg⟩ := hf W hW
    set u : X.K := (f : X.K) / (g : X.K) ^ (m' + 1) with hu
    have hgm : (g : X.K) ^ (m' + 1) ≠ 0 := pow_ne_zero _ g.ne_zero
    have hune : u ≠ 0 := div_ne_zero f.ne_zero hgm
    have huW : u ∈ W := (W.valuation_le_one_iff u).mp hg.le
    have huW' : u⁻¹ ∈ W := (W.valuation_le_one_iff u⁻¹).mp (by rw [map_inv₀, hg, inv_one])
    obtain ⟨φ, hφ, hφa⟩ := (hWmem u).mp huW
    obtain ⟨ψ, hψ, hψa⟩ := (hWmem u⁻¹).mp huW'

    have hφψ : ((φ * ψ : ℂ → ℂ) : Mero) = ((1 : ℂ → ℂ) : Mero) := by
      rw [Filter.Germ.coe_mul, Filter.Germ.coe_one, ← hφ, ← hψ, ← map_mul, mul_inv_cancel₀ hune, map_one]
    have hφτ : φ τ ≠ 0 := by
      have e : φ τ * ψ τ = 1 := (eq_nhds_of_punctured (hφa.continuousAt.mul hψa.continuousAt) continuousAt_const
        (eventually_of_germ_eq hφψ hτ)).self_of_nhds
      intro h0
      rw [h0, zero_mul] at e
      exact zero_ne_one e

    obtain ⟨a1, b1, ha1, hb1, hb1ne, hg1⟩ := X.an_mero (g : X.K)
    have ha1ne : (a1 : Mero) ≠ 0 := num_ne_zero X g hb1ne hg1
    have hfu : X.an (f : X.K) = X.an u * X.an (g : X.K) ^ (m' + 1) := by
      rw [← map_pow, ← map_mul, hu, div_mul_cancel₀ _ hgm]
    have hgerm : ((a0 * b1 ^ (m' + 1) : ℂ → ℂ) : Mero) = ((φ * a1 ^ (m' + 1) * b0 : ℂ → ℂ) : Mero) := by
      simp only [Filter.Germ.coe_mul, Filter.Germ.coe_pow]
      rw [← hf0, ← hg1, hfu, hφ]
      ring
    have hev := eq_nhds_of_punctured
      ((hA ha0 τ hτ).continuousAt.mul ((hA hb1 τ hτ).continuousAt.pow _))
      ((hφa.continuousAt.mul ((hA ha1 τ hτ).continuousAt.pow _)).mul (hA hb0 τ hτ).continuousAt)
      (eventually_of_germ_eq hgerm hτ)
    have hcong := analyticOrderAt_congr hev
    rw [analyticOrderAt_mul (hA ha0 τ hτ) ((hA hb1 τ hτ).pow _), analyticOrderAt_pow (hA hb1 τ hτ),
      analyticOrderAt_mul (hφa.mul ((hA ha1 τ hτ).pow _)) (hA hb0 τ hτ),
      analyticOrderAt_mul hφa ((hA ha1 τ hτ).pow _), analyticOrderAt_pow (hA ha1 τ hτ),
      hφa.analyticOrderAt_eq_zero.mpr hφτ] at hcong
    obtain ⟨oA0, orbitMap_conj_smul_zero⟩ := ENat.ne_top_iff_exists.mp (order_ne_top ha0 ha0ne hτ)
    obtain ⟨oB0, eB0⟩ := ENat.ne_top_iff_exists.mp (order_ne_top hb0 hb0ne hτ)
    obtain ⟨oA1, orbitMap_conj_smul_one⟩ := ENat.ne_top_iff_exists.mp (order_ne_top ha1 ha1ne hτ)
    obtain ⟨oB1, eB1⟩ := ENat.ne_top_iff_exists.mp (order_ne_top hb1 hb1ne hτ)
    rw [← orbitMap_conj_smul_zero, ← eB0, ← orbitMap_conj_smul_one, ← eB1] at hcong
    have heq : oA0 + (m' + 1) * oB1 = (m' + 1) * oA1 + oB0 := by
      simp only [nsmul_eq_mul, zero_add] at hcong
      exact_mod_cast hcong
    have hdvd : (m' + 1) ∣ oA0 + m' * oB0 :=
      Int.natCast_dvd_natCast.mp ⟨(oA1 : ℤ) + oB0 - oB1, by
        have := congrArg (fun n : ℕ => (n : ℤ)) heq
        push_cast at this ⊢
        linear_combination this⟩
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨k, ?_⟩
    rw [analyticOrderAt_mul (hA ha0 τ hτ) ((hA hb0 τ hτ).pow _), analyticOrderAt_pow (hA hb0 τ hτ),
      ← orbitMap_conj_smul_zero, ← eB0, ← hk]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  obtain ⟨r, hr, hrm⟩ := GlobalTheory.T.exists_holomorphic_root_upperHalfPlane (a0 * b0 ^ m') (m' + 1) hm (ha0.mul (hb0.pow _)) hord
  refine ⟨r, b0, hr, hb0, hb0ne, ?_⟩
  have e1 : ((r ^ (m' + 1) : ℂ → ℂ) : Mero) = ((a0 * b0 ^ m' : ℂ → ℂ) : Mero) :=
    germ_eq_of_eqOn fun z hz => by simpa using hrm z hz
  simp only [Filter.Germ.coe_pow, Filter.Germ.coe_mul] at e1 ⊢
  rw [e1, ← hf0]
  ring

end GlobalTheory.KZ.H3.UnRoot
