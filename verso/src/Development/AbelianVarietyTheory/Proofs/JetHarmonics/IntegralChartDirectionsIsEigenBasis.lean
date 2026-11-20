import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SaturationChartsHolds

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap V K)` using `IsFractionRing.injective V K`. Establish `hext : ∀ (g : Fin (m τ) → K) (k : Fin d), ∑ ℓ : (Σ j, Fin (m j)), (if h : ℓ.1 = τ then g (h ▸ ℓ.2) else 0) * algebraMap V K (u ℓ k) = ∑ i, g i * algebraMap V K (u ⟨τ, i⟩ k)`. Introduce `g k`. Rewrite using `[Fintype.sum_sigma, Finset.sum_eq_single τ]`. Simplify using the standard rewrite rules.

Introduce `j _ hj`. Simplify using `[hj]`. Simplify using the standard rewrite rules. Use `⟨fun i a => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `k`.

Apply `hinj` to reduce the goal to its premises. Use `heig a ⟨τ, i⟩ k` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.smul_apply, smul_eq_mul, ht]`. Conclude with `this`. Take `⟨b, hb, -⟩` from `hbas fun k => algebraMap V K (v k)`.

Establish `hb0 : ∀ ℓ : (Σ j, Fin (m j)), ℓ.1 ≠ τ → b ℓ = 0`. Introduce `ℓ hℓ`. Take `⟨a, ha⟩` from `hsep _ _ hℓ`. Establish `h1 : ∀ k, ∑ ℓ', (b ℓ' * χ ℓ'.1 a) * algebraMap V K (u ℓ' k) = χ τ a * algebraMap V K (v k)`. Introduce `k`.

Establish `h2` using `congrArg (algebraMap V K) (congrFun (hv a) k)`. Simplify using `only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.smul_apply, smul_eq_mul, ht] at h2`. Rewrite using `[← h2]`. Simplify using `only [← hb, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun ℓ' _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, ← heig, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k' _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ∀ k, ∑ ℓ', (χ τ a * b ℓ') * algebraMap V K (u ℓ' k) = χ τ a * algebraMap V K (v k)`.

Introduce `k`. Rewrite using `[← hb, Finset.mul_sum]`. Simplify using `only [mul_assoc]`. Establish `h3` using `congrFun ((hbas fun k => χ τ a * algebraMap V K (v k)).unique h1 h2) ℓ`. Establish `h4 : b ℓ * (χ ℓ.1 a - χ τ a) = 0`.

Rewrite using `[mul_sub, h3]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `(mul_eq_zero.1 h4).resolve_right (sub_ne_zero.2 ha)`. Establish `hb1 : ∀ k, ∑ i, b ⟨τ, i⟩ * algebraMap V K (u ⟨τ, i⟩ k) = algebraMap V K (v k)`. Introduce `k`.

Rewrite using `[← hb k, Fintype.sum_sigma, Finset.sum_eq_single τ]`. Introduce `j _ hj`. Conclude with `Finset.sum_eq_zero fun i _ => by rw [hb0 ⟨j, i⟩ hj, zero_mul]`. Simplify using the standard rewrite rules. Take `⟨s, hs⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors V) fun i => b ⟨τ, i⟩`.

Use `choose g hg using hs`. Establish `hmem : (s : V) • v ∈ Submodule.span V (Set.range fun i : Fin (m τ) => u ⟨τ, i⟩)`. Rewrite using `[Submodule.mem_span_range_iff_exists_fun]`. Use `⟨g, funext fun k => hinj ?_⟩` and prove the remaining obligations. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, hg, ← hb1, Finset.mul_sum]`.

Simplify using `only [Algebra.smul_def, mul_assoc]`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun V).1 (hsat v s (nonZeroDivisors.ne_zero s.2) hmem)`. Use `⟨c, hc, fun c' hc' => ?_⟩` and prove the remaining obligations. Establish `hK : ∀ c : Fin (m τ) → V, ∑ i, c i • u ⟨τ, i⟩ = v → ∀ k, ∑ ℓ : (Σ j, Fin (m j)), (if h : ℓ.1 = τ then algebraMap V K (c (h ▸ ℓ.2)) else 0) * algebraMap V K (u ℓ k) = algebraMap V K (v k)`. Introduce `c hc k`.

Rewrite using `[hext (fun i => algebraMap V K (c i)) k, ← hc]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]`. Establish `h5` using `(hbas fun k => algebraMap V K (v k)).unique (hK c' hc') (hK c hc)`. Use function extensionality and compare the values at `i`. Apply `hinj` to reduce the goal to its premises.

Simplify using `using congrFun h5 ⟨τ, i⟩`.
-/
theorem eigBasis_of_generic {V K : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K]
    {A J : Type} [Fintype J] {m : J → ℕ} {d : ℕ} (M : A → Matrix (Fin d) (Fin d) V) (χ : J → A → K)
    (hsep : ∀ j j', j ≠ j' → ∃ a, χ j a ≠ χ j' a) (u : (Σ j, Fin (m j)) → Fin d → V)
    (heig : ∀ a ℓ i, ∑ k, algebraMap V K (M a i k) * algebraMap V K (u ℓ k) = χ ℓ.1 a * algebraMap V K (u ℓ i))
    (hbas : ∀ p : Fin d → K, ∃! b : (Σ j, Fin (m j)) → K, ∀ k, ∑ ℓ, b ℓ * algebraMap V K (u ℓ k) = p k)
    (τ : J) (t : A → V) (ht : ∀ a, algebraMap V K (t a) = χ τ a)
    (hsat : ∀ (v : Fin d → V) (a : V), a ≠ 0 →
      a • v ∈ Submodule.span V (Set.range fun i : Fin (m τ) => u ⟨τ, i⟩) →
      v ∈ Submodule.span V (Set.range fun i : Fin (m τ) => u ⟨τ, i⟩)) :
    (∀ i a, (M a).mulVec (u ⟨τ, i⟩) = t a • u ⟨τ, i⟩) ∧
      ∀ v : Fin d → V, (∀ a, (M a).mulVec v = t a • v) → ∃! c : Fin (m τ) → V, ∑ i, c i • u ⟨τ, i⟩ = v := by
  classical
  have hinj : Function.Injective (algebraMap V K) := IsFractionRing.injective V K
  have hext : ∀ (g : Fin (m τ) → K) (k : Fin d),
      ∑ ℓ : (Σ j, Fin (m j)), (if h : ℓ.1 = τ then g (h ▸ ℓ.2) else 0) * algebraMap V K (u ℓ k) =
        ∑ i, g i * algebraMap V K (u ⟨τ, i⟩ k) := by
    intro g k
    rw [Fintype.sum_sigma, Finset.sum_eq_single τ]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  refine ⟨fun i a => ?_, fun v hv => ?_⟩
  · funext k
    apply hinj
    have := heig a ⟨τ, i⟩ k
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.smul_apply, smul_eq_mul, ht]
    exact this
  obtain ⟨b, hb, -⟩ := hbas fun k => algebraMap V K (v k)
  have hb0 : ∀ ℓ : (Σ j, Fin (m j)), ℓ.1 ≠ τ → b ℓ = 0 := by
    intro ℓ hℓ
    obtain ⟨a, ha⟩ := hsep _ _ hℓ
    have h1 : ∀ k, ∑ ℓ', (b ℓ' * χ ℓ'.1 a) * algebraMap V K (u ℓ' k) = χ τ a * algebraMap V K (v k) := by
      intro k
      have h2 := congrArg (algebraMap V K) (congrFun (hv a) k)
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.smul_apply, smul_eq_mul, ht] at h2
      rw [← h2]
      simp only [← hb, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ℓ' _ => ?_
      rw [mul_assoc, ← heig, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k' _ => ?_
      ring
    have h2 : ∀ k, ∑ ℓ', (χ τ a * b ℓ') * algebraMap V K (u ℓ' k) = χ τ a * algebraMap V K (v k) := by
      intro k
      rw [← hb, Finset.mul_sum]
      simp only [mul_assoc]
    have h3 := congrFun ((hbas fun k => χ τ a * algebraMap V K (v k)).unique h1 h2) ℓ
    have h4 : b ℓ * (χ ℓ.1 a - χ τ a) = 0 := by
      rw [mul_sub, h3]; ring
    exact (mul_eq_zero.1 h4).resolve_right (sub_ne_zero.2 ha)
  have hb1 : ∀ k, ∑ i, b ⟨τ, i⟩ * algebraMap V K (u ⟨τ, i⟩ k) = algebraMap V K (v k) := by
    intro k
    rw [← hb k, Fintype.sum_sigma, Finset.sum_eq_single τ]
    · intro j _ hj
      exact Finset.sum_eq_zero fun i _ => by rw [hb0 ⟨j, i⟩ hj, zero_mul]
    · simp
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors V) fun i => b ⟨τ, i⟩
  choose g hg using hs
  have hmem : (s : V) • v ∈ Submodule.span V (Set.range fun i : Fin (m τ) => u ⟨τ, i⟩) := by
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨g, funext fun k => hinj ?_⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, hg, ← hb1, Finset.mul_sum]
    simp only [Algebra.smul_def, mul_assoc]
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun V).1 (hsat v s (nonZeroDivisors.ne_zero s.2) hmem)
  refine ⟨c, hc, fun c' hc' => ?_⟩
  have hK : ∀ c : Fin (m τ) → V, ∑ i, c i • u ⟨τ, i⟩ = v → ∀ k,
      ∑ ℓ : (Σ j, Fin (m j)), (if h : ℓ.1 = τ then algebraMap V K (c (h ▸ ℓ.2)) else 0) * algebraMap V K (u ℓ k) =
        algebraMap V K (v k) := by
    intro c hc k
    rw [hext (fun i => algebraMap V K (c i)) k, ← hc]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
  have h5 := (hbas fun k => algebraMap V K (v k)).unique (hK c' hc') (hK c hc)
  funext i
  apply hinj
  simpa using congrFun h5 ⟨τ, i⟩

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c`. Use `letI := H.starRing`. Introduce `T io y Ch τ τT hτ`. Use `letI := io.toAlgebra`. Establish `hu : ∀ ℓ i, Ch.ch.uvec ℓ i = algebraMap T.V T.Fr (Ch.uvecT ℓ i)` using `Ch.gen.1.2.2.2.2.2.2`.

Establish `hA : ∀ a j, Ch.ch.B.A.act a j = MvPowerSeries.map (algebraMap T.V T.Fr) (Ch.actT a j)` using `Ch.gen.1.2.1`. Use `eigBasis_of_generic (K := T.Fr) (m := Dw.mult) (fun a => linPart (Ch.actT a)) (fun τ a => io (embK c τ a)) ?_ Ch.uvecT ?_ ?_ τ τT hτ (SaturatedCharts.saturation_charts_holds Xo c T io y Ch τ).2` and prove the remaining obligations. Introduce `j j' h`. Take `⟨a, ha⟩` from `GlobalTheory.EigDir.embK_sep c j j' h`. Conclude with `⟨a, fun e => ha (io.injective e)⟩`.

Introduce `a ℓ i`. Establish `h` using `GlobalTheory.EigDir.linEig_holds E H Dw l Xo c T.Fr y.1 Ch.ch a ℓ i`. Simplify using `only [hu, ReciprocityTheory.ChartRestriction.G.TB.dLin, hA] at h`. Conclude with `h`. Introduce `p`.

Establish `h` using `Ch.ch.chart.basis p`. Simplify using `only [hu] at h`. Conclude with `h`.
-/
theorem isEigBasis_uvecT : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing;
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (τ : E →+* ℂ)
      (τT : 𝓞 E →+* T.V), (∀ a, algebraMap T.V T.Fr (τT a) = io (embK c τ a)) →
      IsEigBasis Ch.actT τT (fun i : Fin (Dw.mult τ) => Ch.uvecT ⟨τ, i⟩) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y Ch τ τT hτ
  letI := io.toAlgebra
  have hu : ∀ ℓ i, Ch.ch.uvec ℓ i = algebraMap T.V T.Fr (Ch.uvecT ℓ i) := Ch.gen.1.2.2.2.2.2.2
  have hA : ∀ a j, Ch.ch.B.A.act a j = MvPowerSeries.map (algebraMap T.V T.Fr) (Ch.actT a j) := Ch.gen.1.2.1
  refine eigBasis_of_generic (K := T.Fr) (m := Dw.mult) (fun a => linPart (Ch.actT a))
    (fun τ a => io (embK c τ a)) ?_ Ch.uvecT ?_ ?_ τ τT hτ (SaturatedCharts.saturation_charts_holds Xo c T io y Ch τ).2
  · intro j j' h
    obtain ⟨a, ha⟩ := GlobalTheory.EigDir.embK_sep c j j' h
    exact ⟨a, fun e => ha (io.injective e)⟩
  · intro a ℓ i
    have h := GlobalTheory.EigDir.linEig_holds E H Dw l Xo c T.Fr y.1 Ch.ch a ℓ i
    simp only [hu, ReciprocityTheory.ChartRestriction.G.TB.dLin, hA] at h
    exact h
  · intro p
    have h := Ch.ch.chart.basis p
    simp only [hu] at h
    exact h

end GlobalTheory.CharDepth
