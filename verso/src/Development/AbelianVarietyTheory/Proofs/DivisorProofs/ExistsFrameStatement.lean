import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistenceOfComparison
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonStatementHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHTFrameCpAndNonempty
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModuliPointIntegralFrameAfterFiniteExtension
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniformisedChartAfterValuationRingExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonExtension

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.DetHT

/- English proof (translation)
Take `⟨g, hg⟩ : ∃ g : 𝓞 c.F →+* K, z ≫ Y.s = spMap g` from `⟨(Spec.preimage (z ≫ Y.s)).hom, (Spec.map_preimage _).symm⟩`. Take `⟨x, hx⟩` from `h ⟨(default : PrimeSpectrum K), rfl⟩`. Establish `e : Y.j ≫ Y.s = (Y.jQ ≫ pullback.snd _ _) ≫ spMap (algebraMap (𝓞 c.F) c.F)`. Rewrite using `[ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j, Category.assoc, pullback.condition, Category.assoc]`. Choose the witnesses or unpack the hypotheses as in `⟨q, e1⟩ : ∃ q : PrimeSpectrum c.F, PrimeSpectrum.comap g default = PrimeSpectrum.comap (algebraMap (𝓞 c.F) c.F) q := by`.

Establish `e2 : (z ≫ Y.s) (default : PrimeSpectrum K) = (Y.j ≫ Y.s) x` using `congrArg Y.s hx.symm`. Rewrite `e2` using `[hg, e]`. Conclude with `⟨_, e2⟩`. Establish `hinj : Function.Injective g`. Use `(injective_iff_map_eq_zero g).2 fun v hv => ?_` and prove the remaining obligations.

Establish `h1 : v ∈ (PrimeSpectrum.comap g default).asIdeal`. Rewrite using `[PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, hv]`. Conclude with `zero_mem _`. Rewrite `h1` using `[e1, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]`. Rewrite `h1` using `[Ideal.eq_bot_of_prime q.asIdeal]`.

Conclude with `IsFractionRing.injective (𝓞 c.F) c.F (h1.trans (map_zero _).symm)`. Set `g' : c.F →+* K` to `IsFractionRing.lift hinj`. Establish `hg' : spMap g' ≫ spMap (algebraMap (𝓞 c.F) c.F) = spMap g`. Rewrite using `[← Spec.map_comp]`. Use `congr 1`.

Use extensionality with `v`. Conclude with `IsFractionRing.lift_algebraMap hinj v`. Set `z' : Sp K ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F))` to `pullback.lift z (spMap g') (hg.trans hg'.symm)`. Establish `hz' : z' ≫ pullback.fst _ _ = z` using `pullback.lift_fst _ _ _`. Establish `: IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F))` using `IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F)) (S := c.F)`.

Establish `h1 : IsPreimmersion (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)))` using `MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip this`. Use `Y.jQ_open` as an intermediate fact. Establish `hr : Set.range z' ⊆ Set.range Y.jQ`. Introduce and unpack `_ ⟨p, rfl⟩`. Take `rfl : p = (default : PrimeSpectrum K)` from `Subsingleton.elim (α := PrimeSpectrum K) _ _`.

Use `⟨x, (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).isEmbedding.injective ?_⟩` and prove the remaining obligations. Establish `e3 : (z' ≫ pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) (default : PrimeSpectrum K) = z (default : PrimeSpectrum K)`. Rewrite using `[hz']`. Conclude with `hx.trans e3.symm`. Use `⟨IsOpenImmersion.lift Y.jQ z' hr, ?_⟩` and prove the remaining obligations.

Rewrite using `[ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, hz']`.
-/
theorem exists_lift_int {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}
    (Y : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) {K : Type} [Field K] (z : Sp K ⟶ Y.X)
    (h : Set.range z ⊆ Set.range Y.j) : ∃ y : Sp K ⟶ Xo.XF c, y ≫ Y.j = z := by
  obtain ⟨g, hg⟩ : ∃ g : 𝓞 c.F →+* K, z ≫ Y.s = spMap g := ⟨(Spec.preimage (z ≫ Y.s)).hom, (Spec.map_preimage _).symm⟩
  obtain ⟨x, hx⟩ := h ⟨(default : PrimeSpectrum K), rfl⟩
  have e : Y.j ≫ Y.s = (Y.jQ ≫ pullback.snd _ _) ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j, Category.assoc, pullback.condition, Category.assoc]
  obtain ⟨q, e1⟩ : ∃ q : PrimeSpectrum c.F,
      PrimeSpectrum.comap g default = PrimeSpectrum.comap (algebraMap (𝓞 c.F) c.F) q := by
    have e2 : (z ≫ Y.s) (default : PrimeSpectrum K) = (Y.j ≫ Y.s) x := congrArg Y.s hx.symm
    rw [hg, e] at e2
    exact ⟨_, e2⟩
  have hinj : Function.Injective g := by
    refine (injective_iff_map_eq_zero g).2 fun v hv => ?_
    have h1 : v ∈ (PrimeSpectrum.comap g default).asIdeal := by
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, hv]; exact zero_mem _
    rw [e1, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at h1
    rw [Ideal.eq_bot_of_prime q.asIdeal] at h1
    exact IsFractionRing.injective (𝓞 c.F) c.F (h1.trans (map_zero _).symm)
  let g' : c.F →+* K := IsFractionRing.lift hinj
  have hg' : spMap g' ≫ spMap (algebraMap (𝓞 c.F) c.F) = spMap g := by
    rw [← Spec.map_comp]
    congr 1
    ext v
    exact IsFractionRing.lift_algebraMap hinj v
  let z' : Sp K ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)) := pullback.lift z (spMap g') (hg.trans hg'.symm)
  have hz' : z' ≫ pullback.fst _ _ = z := pullback.lift_fst _ _ _
  have : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F)) (S := c.F)
  have h1 : IsPreimmersion (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip this
  have := Y.jQ_open
  have hr : Set.range z' ⊆ Set.range Y.jQ := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = (default : PrimeSpectrum K) := Subsingleton.elim (α := PrimeSpectrum K) _ _
    refine ⟨x, (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).isEmbedding.injective ?_⟩
    have e3 : (z' ≫ pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) (default : PrimeSpectrum K) =
        z (default : PrimeSpectrum K) := by
      rw [hz']
    exact hx.trans e3.symm
  refine ⟨IsOpenImmersion.lift Y.jQ z' hr, ?_⟩
  rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, hz']

/- English proof (translation)
Establish `: IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F))` using `IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F)) (S := c.F)`. Establish `h1 : IsPreimmersion (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)))` using `MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip this`. Use `Y.jQ_open` as an intermediate fact. Rewrite using `[ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j]`. Use `infer_instance`.
-/
theorem mono_j_int {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}
    (Y : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) : Mono Y.j := by
  have : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F)) (S := c.F)
  have h1 : IsPreimmersion (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip this
  have := Y.jQ_open
  rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j]
  infer_instance

/- English proof (translation)
Establish `hπ0 : π ≠ 0`. Introduce and unpack `rfl`. Rewrite `hπ` using `[map_zero]`. Conclude with `WithZero.exp_ne_zero hπ.symm`. Establish `hw : ∀ a : K, a ≠ 0 → w a ≠ 0` using `fun a ha => (Valuation.ne_zero_iff w).2 ha`.

Establish `hu : ∀ a : K, a ≠ 0 → u a ≠ 0` using `fun a ha => (Valuation.ne_zero_iff u).2 ha`. Establish `hle : ∀ a : K, a ≠ 0 → ((w a).log ≤ 0 ↔ (u a).log ≤ 0)` using `fun a ha => by`. Rewrite using `[WithZero.log_le_iff_le_exp (hw a ha), WithZero.log_le_iff_le_exp (hu a ha), WithZero.exp_zero]`. Conclude with `h a`. Establish `hlu : (u π).log = -1` using `by rw [hπ, WithZero.log_exp]`.

Establish `hpos : 0 < -(w π).log`. Establish `h1` using `hle π⁻¹ (inv_ne_zero hπ0)`. Rewrite `h1` using `[map_inv₀, map_inv₀, WithZero.log_inv, WithZero.log_inv, hlu]`. Use linear arithmetic over natural numbers and integers. Use `⟨(-(w π).log).toNat, by omega, fun a => ?_⟩` and prove the remaining obligations.

Rewrite using `[Int.toNat_of_nonneg hpos.le]`. Distinguish the cases in `ha : a = 0`. Simplify using `[ha]`. Establish `hb : a * π ^ (u a).log ≠ 0` using `mul_ne_zero ha (zpow_ne_zero _ hπ0)`. Establish `h1` using `hle _ hb`.

Establish `h2` using `hle _ (inv_ne_zero hb)`. Rewrite `h2` using `[map_inv₀, map_inv₀, WithZero.log_inv, WithZero.log_inv]`. Establish `e1 : (u (a * π ^ (u a).log)).log = 0`. Rewrite using `[map_mul, map_zpow₀, WithZero.log_mul (hu a ha) (zpow_ne_zero _ (hu π hπ0)), WithZero.log_zpow, hlu]`. Simplify using the standard rewrite rules.

Establish `e2 : (w (a * π ^ (u a).log)).log = (w a).log + (u a).log * (w π).log`. Rewrite using `[map_mul, map_zpow₀, WithZero.log_mul (hw a ha) (zpow_ne_zero _ (hw π hπ0)), WithZero.log_zpow, smul_eq_mul]`. Rewrite `h1`, `h2` using `[e1, e2]`. Establish `h3` using `h1.2 le_rfl`. Establish `h4` using `h2.2 (by simp)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_eq_mul_of_le_one_iff {K : Type} [Field K] (w u : Valuation K (WithZero (Multiplicative ℤ)))
    (h : ∀ a, w a ≤ 1 ↔ u a ≤ 1) (π : K) (hπ : u π = WithZero.exp (-1 : ℤ)) :
    ∃ e : ℕ, 0 < e ∧ ∀ a, -(w a).log = (e : ℤ) * -(u a).log := by
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hw : ∀ a : K, a ≠ 0 → w a ≠ 0 := fun a ha => (Valuation.ne_zero_iff w).2 ha
  have hu : ∀ a : K, a ≠ 0 → u a ≠ 0 := fun a ha => (Valuation.ne_zero_iff u).2 ha
  have hle : ∀ a : K, a ≠ 0 → ((w a).log ≤ 0 ↔ (u a).log ≤ 0) := fun a ha => by
    rw [WithZero.log_le_iff_le_exp (hw a ha), WithZero.log_le_iff_le_exp (hu a ha), WithZero.exp_zero]
    exact h a
  have hlu : (u π).log = -1 := by rw [hπ, WithZero.log_exp]
  have hpos : 0 < -(w π).log := by
    have h1 := hle π⁻¹ (inv_ne_zero hπ0)
    rw [map_inv₀, map_inv₀, WithZero.log_inv, WithZero.log_inv, hlu] at h1
    omega
  refine ⟨(-(w π).log).toNat, by omega, fun a => ?_⟩
  rw [Int.toNat_of_nonneg hpos.le]
  by_cases ha : a = 0
  · simp [ha]
  have hb : a * π ^ (u a).log ≠ 0 := mul_ne_zero ha (zpow_ne_zero _ hπ0)
  have h1 := hle _ hb
  have h2 := hle _ (inv_ne_zero hb)
  rw [map_inv₀, map_inv₀, WithZero.log_inv, WithZero.log_inv] at h2
  have e1 : (u (a * π ^ (u a).log)).log = 0 := by
    rw [map_mul, map_zpow₀, WithZero.log_mul (hu a ha) (zpow_ne_zero _ (hu π hπ0)), WithZero.log_zpow, hlu]
    simp
  have e2 : (w (a * π ^ (u a).log)).log = (w a).log + (u a).log * (w π).log := by
    rw [map_mul, map_zpow₀, WithZero.log_mul (hw a ha) (zpow_ne_zero _ (hw π hπ0)), WithZero.log_zpow, smul_eq_mul]
  rw [e1, e2] at h1 h2
  have h3 := h1.2 le_rfl
  have h4 := h2.2 (by simp)
  linarith

/- English proof (translation)
Take `⟨r, hr⟩` from `GlobalTheory.CompHt.exists_log_eq (v := (Valued.v : Valuation ℂ_[p] ℝ≥0)) (PadicComplexInt.integers p) k kO hk`. Simplify using `only [coe_valued] at hr`. Establish `hp : p.Prime` using `Fact.out`. Establish `hp0 : (p : T.Fr) ≠ 0` using `fun h0 => by`. Use `congrArg k h0` as an intermediate fact.

Rewrite `this` using `[map_natCast, map_zero]`. Conclude with `hp.ne_zero (by exact_mod_cast this)`. Establish `hv0 : ∀ x : T.Fr, x ≠ 0 → valV T.V x ≠ 0` using `fun x hx => (Valuation.ne_zero_iff _).2 hx`. Establish `hiff : ∀ x : T.Fr, x ≠ 0 → (0 ≤ vV T.V x ↔ valV T.V x ≤ 1)` using `fun x hx => by`. Rewrite using `[vV, neg_nonneg, WithZero.log_le_iff_le_exp (hv0 x hx), WithZero.exp_zero]`.

Establish `hvp : 0 ≤ vV T.V (p : T.Fr)`. Rewrite using `[hiff _ hp0, ← map_natCast (algebraMap T.V T.Fr)]`. Conclude with `HeightOneSpectrum.valuation_le_one _ _`. Establish `hr0 : r < 0`. Establish `h1` using `hr _ hp0`.

Rewrite `h1` using `[map_natCast]`. Establish `h2 : ‖(p : ℂ_[p])‖ < 1`. Rewrite using `[← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap']`. Conclude with `Padic.norm_p_lt_one`. Establish `h3 : Real.log ‖(p : ℂ_[p])‖ < 0` using `Real.log_neg (norm_pos_iff.2 (by exact_mod_cast hp.ne_zero)) h2`.

Establish `h4 : (0 : ℝ) ≤ (vV T.V (p : T.Fr) : ℝ)` using `by exact_mod_cast hvp`. Assume the negation of the conclusion as `h5`. Use `mul_nonneg h4 (not_lt.1 h5)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨π, hπ⟩` from `la.valuation_exists_uniformizer K`.

Use `log_eq_mul_of_le_one_iff ((valV T.V).comap io) (la.valuation K) (fun a => ?_) π hπ` and prove the remaining obligations. Distinguish the cases in `ha : a = 0`. Simplify using `[ha]`. Establish `ha' : io a ≠ 0` using `(map_ne_zero io).2 ha`. Rewrite using `[← h a, Valuation.comap_apply, ← hiff _ ha', ← Real.log_nonpos_iff (norm_nonneg _), hr _ ha']`.

Prove the components needed by the constructor for the conclusion. Introduce `h1`. Conclude with `mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast h1) hr0.le`. Introduce `h1`. Establish `: (0 : ℝ) ≤ (vV T.V (io a) : ℝ)` using `by nlinarith`.

Conclude with `this` after adjusting the coercions.
-/
theorem exists_overLa {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (T : CDVR) (io : K →+* T.Fr)
    (p : ℕ) [Fact p.Prime] (k : T.Fr →+* ℂ_[p]) (kO : T.V →+* 𝓞_ℂ_[p])
    (hk : ∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a) = k (algebraMap T.V T.Fr a))
    (h : ∀ a : K, ‖k (io a)‖ ≤ 1 ↔ la.valuation K a ≤ 1) : ∃ e : ℕ, OverLa la T.V io e := by
  obtain ⟨r, hr⟩ := GlobalTheory.CompHt.exists_log_eq (v := (Valued.v : Valuation ℂ_[p] ℝ≥0)) (PadicComplexInt.integers p) k kO hk
  simp only [coe_valued] at hr
  have hp : p.Prime := Fact.out
  have hp0 : (p : T.Fr) ≠ 0 := fun h0 => by
    have := congrArg k h0
    rw [map_natCast, map_zero] at this
    exact hp.ne_zero (by exact_mod_cast this)
  have hv0 : ∀ x : T.Fr, x ≠ 0 → valV T.V x ≠ 0 := fun x hx => (Valuation.ne_zero_iff _).2 hx
  have hiff : ∀ x : T.Fr, x ≠ 0 → (0 ≤ vV T.V x ↔ valV T.V x ≤ 1) := fun x hx => by
    rw [vV, neg_nonneg, WithZero.log_le_iff_le_exp (hv0 x hx), WithZero.exp_zero]
  have hvp : 0 ≤ vV T.V (p : T.Fr) := by
    rw [hiff _ hp0, ← map_natCast (algebraMap T.V T.Fr)]
    exact HeightOneSpectrum.valuation_le_one _ _
  have hr0 : r < 0 := by
    have h1 := hr _ hp0
    rw [map_natCast] at h1
    have h2 : ‖(p : ℂ_[p])‖ < 1 := by
      rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap']
      exact Padic.norm_p_lt_one
    have h3 : Real.log ‖(p : ℂ_[p])‖ < 0 :=
      Real.log_neg (norm_pos_iff.2 (by exact_mod_cast hp.ne_zero)) h2
    have h4 : (0 : ℝ) ≤ (vV T.V (p : T.Fr) : ℝ) := by exact_mod_cast hvp
    by_contra h5
    have := mul_nonneg h4 (not_lt.1 h5)
    linarith
  obtain ⟨π, hπ⟩ := la.valuation_exists_uniformizer K
  refine log_eq_mul_of_le_one_iff ((valV T.V).comap io) (la.valuation K) (fun a => ?_) π hπ
  by_cases ha : a = 0
  · simp [ha]
  have ha' : io a ≠ 0 := (map_ne_zero io).2 ha
  rw [← h a, Valuation.comap_apply, ← hiff _ ha', ← Real.log_nonpos_iff (norm_nonneg _), hr _ ha']
  constructor
  · intro h1
    exact mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast h1) hr0.le
  · intro h1
    have : (0 : ℝ) ≤ (vV T.V (io a) : ℝ) := by nlinarith
    exact_mod_cast this

/- English proof (translation)
Use `letI := H.starRing`. Use `letI := io.toAlgebra`. Establish `hxeq` using `GlobalTheory.CompHt.IsHTFrame.x_eq hy`. Take `⟨-, kO₀, P, ψ₀, z, hP, -, hch⟩` from `hy`. Take `⟨hkO₀, G, t', m₁, m₂, π₀, φ₀, hπ₀, hact₀, hφ₀, hgen₀, hψ₀, -⟩` from `hP`.

Establish `tr : ∀ {S S' : Scheme.{0}} {s : SAB H S} {s' : SAB H S'} {f g : S' ⟶ S}, f = g → ∀ m : SABMap s' s f, ∃ m' : SABMap s' s g, m'.φ = m.φ`. Introduce `S S' s s' f g h m`. Substitute `h` using the available equality. Conclude with `⟨m, rfl⟩`. Establish `hkk : kO₀ = kO.comp i` using `RingHom.ext fun a => P.integers.hom_inj (by`.

Rewrite using `[hkO₀ a, RingHom.comp_apply, hkO (i a), hi, hk']`. Use the proof step `rfl)`. Establish `hkk' : k'.comp iF = k.toRingHom` using `RingHom.ext fun a => hk' a`. Establish `hii : (algebraMap T'.V T'.Fr).comp i = iF.comp (algebraMap T.V T.Fr)` using `RingHom.ext hi`. Establish `hOO : (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO = k'.comp (algebraMap T'.V T'.Fr)` using `RingHom.ext hkO`.

Establish `hx' : yyT ≫ pullback.fst _ _ = spMap iF ≫ y₀.1.x`. Rewrite using `[hr, Category.assoc]`. Use `congr 1`. Conclude with `pullback.lift_fst _ _ _`. Take `⟨G', ⟨a⟩⟩` from `exists_sab (spMap i) G`.

Take `⟨Yt', ⟨b⟩⟩` from `exists_sab yT Y.t`. Take `⟨t₂, ⟨q⟩⟩` from `exists_sab yyT Y.oF.t`. Take `⟨t₁, ⟨c₁⟩⟩` from `exists_sab (spMap (algebraMap T'.V T'.Fr)) G'`. Take `⟨n₁, hn₁⟩` from `sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν q`. Take `⟨e₂, he₂⟩` from `sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m q`.

Take `⟨e₂', he₂'⟩` from `tr (show yyT ≫ Y.jQ ≫ pullback.fst _ _ = spMap (algebraMap T'.V T'.Fr) ≫ yT from hT.symm) e₂`. Take `⟨n₂, hn₂⟩` from `sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ b e₂'`. Take `⟨e₁, he₁⟩` from `sabComp pullCubComp E H _ _ _ _ _ _ _ _ a c₁`. Take `⟨e₁', he₁'⟩` from `tr (show spMap (algebraMap T'.V T'.Fr) ≫ spMap i = spMap iF ≫ spMap (algebraMap T.V T.Fr) by`. Rewrite using `[spMap_spMap, spMap_spMap, hii]) e₁`.

Take `⟨d, hd⟩` from `sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m₂ e₁'`. Take `⟨m₁', hm₁'⟩` from `sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₁ d`. Take `⟨m₁'', hm₁''⟩` from `tr hx'.symm m₁'`. Take `⟨κ, nn, hκ, hnn⟩` from `GlobalTheory.sab_extensions_iso E H Dw l Xo T'.V T'.Fr _ G' Yt' t₁ t₂ m₁'' c₁ n₁ n₂`. Establish `w₁ : π₀ ≫ G.G.hom = (P.G.hom ≫ spMap kO) ≫ spMap i`.

Rewrite using `[hπ₀.1.w, Category.assoc, spMap_spMap, hkk]`. Set `π₁ : P.G.left ⟶ G'.G.left` to `a.cart.1.lift π₀ (P.G.hom ≫ spMap kO) w₁`. Establish `hπ₁a : π₁ ≫ a.φ = π₀` using `a.cart.1.lift_fst _ _ _`. Establish `hπ₁s : π₁ ≫ G'.G.hom = P.G.hom ≫ spMap kO` using `a.cart.1.lift_snd _ _ _`. Establish `hπ₁ : IsGrpPullback P.G G'.G (spMap kO) π₁` using `a.cart.cancel (hπ₀.congr (by rw [spMap_spMap, hkk]) hπ₁a.symm) hπ₁s`.

Establish `w₂ : φ₀ ≫ t'.G.hom = (P.A.A.hom ≫ spMap k') ≫ spMap iF`. Rewrite using `[hφ₀.1.w, Category.assoc, spMap_spMap, hkk']`. Set `ψ₁ : P.A.A.left ⟶ t₁.G.left` to `d.cart.1.lift φ₀ (P.A.A.hom ≫ spMap k') w₂`. Establish `hψ₁d : ψ₁ ≫ d.φ = φ₀` using `d.cart.1.lift_fst _ _ _`. Establish `hψ₁s : ψ₁ ≫ t₁.G.hom = P.A.A.hom ≫ spMap k'` using `d.cart.1.lift_snd _ _ _`.

Establish `hψ₁ : IsGrpPullback P.A.A t₁.G (spMap k') ψ₁` using `d.cart.cancel (hφ₀.congr (by rw [spMap_spMap, hkk']) hψ₁d.symm) hψ₁s`. Establish `key : ψ₁ ≫ c₁.φ = P.gen ≫ π₁`. Apply `a.cart.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, hπ₁a, ← he₁, ← he₁', hd, ← Category.assoc, hψ₁d, hgen₀]`. Rewrite using `[Category.assoc, Category.assoc, hπ₁s, c₁.cart.1.w, ← Category.assoc, hψ₁s, ← Category.assoc, P.gen_pull.1.w, Category.assoc, Category.assoc, spMap_spMap, spMap_spMap, hOO]`.

Use `⟨P, π₁ ≫ nn.φ ≫ b.φ, ψ₁ ≫ κ.φ ≫ q.φ, z, ?_⟩` and prove the remaining obligations. Establish `hψν : (ψ₁ ≫ κ.φ ≫ q.φ) ≫ ν.φ = ψ₀`. Rewrite using `[Category.assoc, Category.assoc, ← hn₁, hκ, hm₁'', hm₁', ← Category.assoc, hψ₁d, hψ₀]`. Use `⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, by rw [hψν]; exact hch⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, spMap_spMap, hOO, ← spMap_spMap, Category.assoc, hT, Category.assoc]`.

Conclude with `((hπ₁.comp nn.cart).comp b.cart).congr (by rw [Category.comp_id]) (by rw [Category.assoc])`. Introduce `a₀`. Establish `h1 : (P.oG.act a₀).left ≫ π₁ = π₁ ≫ (G'.act.act a₀).left`. Apply `a.cart.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, hπ₁a, hact₀, a.act, ← Category.assoc, hπ₁a]`.

Rewrite using `[Category.assoc, Category.assoc, hπ₁s, Over.w, hπ₁s, ← Category.assoc, Over.w]`. Simplify using `only [Category.assoc, reassoc_of% h1, reassoc_of% (nn.act a₀), b.act a₀]`. Conclude with `((hψ₁.comp κ.cart).comp q.cart).congr (by rw [Category.comp_id]) (by rw [Category.assoc])`. Establish `h2 : q.φ ≫ Y.m.φ = n₂.φ ≫ b.φ` using `by rw [← he₂, ← he₂', hn₂]`. Rewrite using `[Category.assoc, Category.assoc, h2, ← Category.assoc κ.φ, ← hnn]`.

Simplify using `only [Category.assoc]`. Rewrite using `[reassoc_of% key]`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[ptF, pullback.lift_fst, hxeq, Category.assoc, hx', ← Category.assoc, spMap_spMap, hkk']`. Rewrite using `[ptF, pullback.lift_snd]`.

Simplify using `only [Category.assoc]`. Rewrite using `[hr, Category.assoc, ← Category.assoc, spMap_spMap, hkk', ptF, pullback.lift_snd, spMap_spMap]`. Use `congr 1`. Conclude with `(RingHom.ext fun x => k.commutes x).symm`.
-/
theorem ptAt_of_isHTFrame {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Y : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (ν : SABMap Y.oF.t Xo.univ.t (pullback.fst _ _))
    (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]] (T T' : CDVR) (i : T.V →+* T'.V) (iF : T.Fr →+* T'.Fr)
    (hi : ∀ a, algebraMap T'.V T'.Fr (i a) = iF (algebraMap T.V T.Fr a))
    (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] ℂ_[p]) (y : FrPt Xo c ℂ_[p])
    (hy : IsHTFrameCp p y₀ k y) (k' : T'.Fr →+* ℂ_[p]) (kO : T'.V →+* 𝓞_ℂ_[p])
    (hkO : ∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a) = k' (algebraMap T'.V T'.Fr a)) (hk' : ∀ a, k' (iF a) = k a)
    (yT : Sp T'.V ⟶ Y.X) (yyT : Sp T'.Fr ⟶ Xo.XF c) (hT : spMap (algebraMap T'.V T'.Fr) ≫ yT = yyT ≫ Y.j)
    (hr : yyT = spMap iF ≫ (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y₀.1)) :
    letI := H.starRing; ∃ (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (z : FrPt Xo c ℂ_[p]),
      PtAt Y (spMap kO ≫ yT) (spMap k' ≫ yyT) P π ψ ∧ GlobalTheory.AllWt.ptF y = spMap k' ≫ yyT ∧
        IsHTChange P (ψ ≫ ν.φ) z y := by
  letI := H.starRing
  letI := io.toAlgebra
  have hxeq := GlobalTheory.CompHt.IsHTFrame.x_eq hy
  obtain ⟨-, kO₀, P, ψ₀, z, hP, -, hch⟩ := hy
  obtain ⟨hkO₀, G, t', m₁, m₂, π₀, φ₀, hπ₀, hact₀, hφ₀, hgen₀, hψ₀, -⟩ := hP
  have tr : ∀ {S S' : Scheme.{0}} {s : SAB H S} {s' : SAB H S'} {f g : S' ⟶ S}, f = g →
      ∀ m : SABMap s' s f, ∃ m' : SABMap s' s g, m'.φ = m.φ := by
    intro S S' s s' f g h m
    subst h
    exact ⟨m, rfl⟩

  have hkk : kO₀ = kO.comp i := RingHom.ext fun a => P.integers.hom_inj (by
    rw [hkO₀ a, RingHom.comp_apply, hkO (i a), hi, hk']; rfl)
  have hkk' : k'.comp iF = k.toRingHom := RingHom.ext fun a => hk' a
  have hii : (algebraMap T'.V T'.Fr).comp i = iF.comp (algebraMap T.V T.Fr) := RingHom.ext hi
  have hOO : (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO = k'.comp (algebraMap T'.V T'.Fr) := RingHom.ext hkO
  have hx' : yyT ≫ pullback.fst _ _ = spMap iF ≫ y₀.1.x := by
    rw [hr, Category.assoc]
    congr 1
    exact pullback.lift_fst _ _ _

  obtain ⟨G', ⟨a⟩⟩ := exists_sab (spMap i) G
  obtain ⟨Yt', ⟨b⟩⟩ := exists_sab yT Y.t
  obtain ⟨t₂, ⟨q⟩⟩ := exists_sab yyT Y.oF.t
  obtain ⟨t₁, ⟨c₁⟩⟩ := exists_sab (spMap (algebraMap T'.V T'.Fr)) G'
  obtain ⟨n₁, hn₁⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν q
  obtain ⟨e₂, he₂⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m q
  obtain ⟨e₂', he₂'⟩ := tr (show yyT ≫ Y.jQ ≫ pullback.fst _ _ = spMap (algebraMap T'.V T'.Fr) ≫ yT from hT.symm) e₂
  obtain ⟨n₂, hn₂⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ b e₂'
  obtain ⟨e₁, he₁⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ a c₁
  obtain ⟨e₁', he₁'⟩ := tr (show spMap (algebraMap T'.V T'.Fr) ≫ spMap i = spMap iF ≫ spMap (algebraMap T.V T.Fr) by
    rw [spMap_spMap, spMap_spMap, hii]) e₁
  obtain ⟨d, hd⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m₂ e₁'
  obtain ⟨m₁', hm₁'⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₁ d
  obtain ⟨m₁'', hm₁''⟩ := tr hx'.symm m₁'
  obtain ⟨κ, nn, hκ, hnn⟩ := GlobalTheory.sab_extensions_iso E H Dw l Xo T'.V T'.Fr _ G' Yt' t₁ t₂ m₁'' c₁ n₁ n₂

  have w₁ : π₀ ≫ G.G.hom = (P.G.hom ≫ spMap kO) ≫ spMap i := by
    rw [hπ₀.1.w, Category.assoc, spMap_spMap, hkk]
  let π₁ : P.G.left ⟶ G'.G.left := a.cart.1.lift π₀ (P.G.hom ≫ spMap kO) w₁
  have hπ₁a : π₁ ≫ a.φ = π₀ := a.cart.1.lift_fst _ _ _
  have hπ₁s : π₁ ≫ G'.G.hom = P.G.hom ≫ spMap kO := a.cart.1.lift_snd _ _ _
  have hπ₁ : IsGrpPullback P.G G'.G (spMap kO) π₁ :=
    a.cart.cancel (hπ₀.congr (by rw [spMap_spMap, hkk]) hπ₁a.symm) hπ₁s

  have w₂ : φ₀ ≫ t'.G.hom = (P.A.A.hom ≫ spMap k') ≫ spMap iF := by
    rw [hφ₀.1.w, Category.assoc, spMap_spMap, hkk']
  let ψ₁ : P.A.A.left ⟶ t₁.G.left := d.cart.1.lift φ₀ (P.A.A.hom ≫ spMap k') w₂
  have hψ₁d : ψ₁ ≫ d.φ = φ₀ := d.cart.1.lift_fst _ _ _
  have hψ₁s : ψ₁ ≫ t₁.G.hom = P.A.A.hom ≫ spMap k' := d.cart.1.lift_snd _ _ _
  have hψ₁ : IsGrpPullback P.A.A t₁.G (spMap k') ψ₁ :=
    d.cart.cancel (hφ₀.congr (by rw [spMap_spMap, hkk']) hψ₁d.symm) hψ₁s
  have key : ψ₁ ≫ c₁.φ = P.gen ≫ π₁ := by
    apply a.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, hπ₁a, ← he₁, ← he₁', hd, ← Category.assoc, hψ₁d, hgen₀]
    · rw [Category.assoc, Category.assoc, hπ₁s, c₁.cart.1.w, ← Category.assoc, hψ₁s, ← Category.assoc,
        P.gen_pull.1.w, Category.assoc, Category.assoc, spMap_spMap, spMap_spMap, hOO]
  refine ⟨P, π₁ ≫ nn.φ ≫ b.φ, ψ₁ ≫ κ.φ ≫ q.φ, z, ?_⟩
  have hψν : (ψ₁ ≫ κ.φ ≫ q.φ) ≫ ν.φ = ψ₀ := by
    rw [Category.assoc, Category.assoc, ← hn₁, hκ, hm₁'', hm₁', ← Category.assoc, hψ₁d, hψ₀]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, by rw [hψν]; exact hch⟩
  · rw [← Category.assoc, spMap_spMap, hOO, ← spMap_spMap, Category.assoc, hT, Category.assoc]
  · exact ((hπ₁.comp nn.cart).comp b.cart).congr (by rw [Category.comp_id]) (by rw [Category.assoc])
  · intro a₀
    have h1 : (P.oG.act a₀).left ≫ π₁ = π₁ ≫ (G'.act.act a₀).left := by
      apply a.cart.1.hom_ext
      · rw [Category.assoc, Category.assoc, hπ₁a, hact₀, a.act, ← Category.assoc, hπ₁a]
      · rw [Category.assoc, Category.assoc, hπ₁s, Over.w, hπ₁s, ← Category.assoc, Over.w]
    simp only [Category.assoc, reassoc_of% h1, reassoc_of% (nn.act a₀), b.act a₀]
  · exact ((hψ₁.comp κ.cart).comp q.cart).congr (by rw [Category.comp_id]) (by rw [Category.assoc])
  · have h2 : q.φ ≫ Y.m.φ = n₂.φ ≫ b.φ := by rw [← he₂, ← he₂', hn₂]
    rw [Category.assoc, Category.assoc, h2, ← Category.assoc κ.φ, ← hnn]
    simp only [Category.assoc]
    rw [reassoc_of% key]
  · apply pullback.hom_ext
    · rw [ptF, pullback.lift_fst, hxeq, Category.assoc, hx', ← Category.assoc, spMap_spMap, hkk']
    · rw [ptF, pullback.lift_snd]
      simp only [Category.assoc]
      rw [hr, Category.assoc, ← Category.assoc, spMap_spMap, hkk', ptF, pullback.lift_snd, spMap_spMap]
      congr 1
      exact (RingHom.ext fun x => k.commutes x).symm

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c hpq Y Zc la p _ inst hla P yb hyb hP`. Take `⟨hgen, T, kO, yT, hfin, hkO, hyT⟩` from `hyb`. Establish `hiO : Function.Injective (algebraMap 𝓞_ℂ_[p] ℂ_[p])` using `(PadicComplexInt.integers p).hom_inj`. Establish `hgX : Set.range (spMap (algebraMap T.V T.Fr) ≫ yT) ⊆ Set.range Y.j`. Introduce and unpack `_ ⟨s, rfl⟩`.

Take `rfl : s = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T.Fr)` from `Subsingleton.elim (α := PrimeSpectrum T.Fr) _ _`. Establish `h1` using `bot_map (IsFractionRing.injective T.V T.Fr) yT`. Establish `h2` using `bot_map (φ := (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO) (hiO.comp hkO) yT`. Rewrite `h2` using `[← sp_sp, hyT, hgen]`. Rewrite using `[h1, ← h2]`.

Conclude with `⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩`. Take `⟨yyT, hyyT⟩` from `exists_lift_int Y _ hgX`. Take `⟨io, hio⟩ : ∃ io : c.F →+* T.Fr, yyT ≫ pullback.snd _ _ = spMap io` from `⟨(Spec.preimage (yyT ≫ pullback.snd _ _)).hom, (Spec.map_preimage (yyT ≫ pullback.snd _ _)).symm⟩`. Set `x : Sp T.Fr ⟶ Xo.X` to `yyT ≫ pullback.fst _ _`. Establish `hx : (letI` using `io.toAlgebra; x ≫ Xo.s = sOf c T.Fr) := by`.

Use `letI := io.toAlgebra`. Use `show (yyT ≫ pullback.fst _ _) ≫ Xo.s = _`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc yyT, hio, sOf, spMap_spMap]`. Take `⟨T', i, rr, hrr, hv, hfin', y₀, hy₀⟩` from `GlobalTheory.AnyLevelFrame.intFrExt E H Dw l Xo c hpq T io hfin x hx`. Take `⟨φ, hφ, hloc⟩` from `GlobalTheory.GoodChartExt.exists_local_restrict T T' i rr hrr hv`.

Establish `hφi : Function.Injective φ`. Introduce `a b h`. Apply `i.injective.comp (IsFractionRing.injective T.V T.Fr)` to reduce the goal to its premises. Establish `ha` using `RingHom.congr_fun hφ a`. Establish `hb` using `RingHom.congr_fun hφ b`.

Simplify using `only [RingHom.comp_apply] at ha hb`. Simplify using `only [Function.comp_apply, ← ha, ← hb, h]`. Establish `hfinφ : φ.Finite` using `GlobalTheory.CompHS.finite_of_finRes hfin' φ hφi`. Take `⟨kO', hkO', hinj'⟩` from `exists_ext_of_integral (Valued.v : Valuation ℂ_[p] ℝ≥0) (PadicComplexInt.integers p) φ hφi hfinφ.to_isIntegral kO (hiO.comp hkO)`. Set `k : T'.Fr →+* ℂ_[p]` to `IsFractionRing.lift hinj'`.

Establish `hk : ∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO' a) = k (algebraMap T'.V T'.Fr a)` using `fun a => (IsFractionRing.lift_algebraMap hinj' a).symm`. Establish `hcomm : spMap (algebraMap T'.V T'.Fr) ≫ (spMap φ ≫ yT) = (spMap i ≫ yyT) ≫ Y.j`. Rewrite using `[sp_sp, hφ, ← sp_sp, Category.assoc, hyyT]`. Establish `hPk : GlobalTheory.AllWt.ptF P = spMap k ≫ spMap i ≫ yyT`. Use `mono_j_int Y` as an intermediate fact.

Rewrite using `[← cancel_mono Y.j, ← hgen, Category.assoc, ← hcomm, ← hyT, ← hkO', sp_sp, sp_sp, sp_sp]`. Use `congr 2`. Conclude with `RingHom.ext fun a => hk (φ a)`. Establish `halg : algebraMap c.F ℂ_[p] = k.comp (i.comp io)`. Establish `h1` using `ptF_snd P`.

Rewrite `h1` using `[hPk, Category.assoc, Category.assoc, hio, spMap_spMap, spMap_spMap]`. Conclude with `(congrArg CommRingCat.Hom.hom (Spec.map_injective h1)).symm`. Use `letI := (i.comp io).toAlgebra`. Use `letI := H.starRing`. Set `kA : T'.Fr →ₐ[c.F] ℂ_[p]` to `{ k with commutes' := fun a => (RingHom.congr_fun halg a).symm }`.

Take `⟨y, hy⟩` from `GlobalTheory.CompHt.exists_isHTFrame (p := p) (v := (Valued.v : Valuation ℂ_[p] ℝ≥0)) (O := 𝓞_ℂ_[p]) (fun _ => rfl) (PadicComplexInt.integers p) y₀ hfin' kA kO' hk`. Establish `hpt : spMap i ≫ yyT = GlobalTheory.AllWt.ptF y₀.1`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[GlobalTheory.AllWt.ptF, pullback.lift_fst, hy₀, Category.assoc]`. Rewrite using `[GlobalTheory.AllWt.ptF, pullback.lift_snd, Category.assoc, hio, spMap_spMap]`.

Take `⟨Q, π, ψ, z, h1, h2, h3⟩` from `ptAt_of_isHTFrame Y Y.m0.toSABMap p T' T' (RingHom.id _) (RingHom.id _) (fun _ => rfl) (i.comp io) y₀ kA y hy k kO' hk (fun _ => rfl) (spMap φ ≫ yT) (spMap i ≫ yyT) hcomm (by rw [show spMap (RingHom.id T'.Fr) = 𝟙 _ from Spec.map_id _, Category.id_comp, hpt])`. Rewrite `h1` using `[sp_sp, hkO', hyT, ← hPk]`. Take `⟨e, he⟩` from `exists_overLa la T' (i.comp io) p k kO' hk fun a => by`. Rewrite using `[← hla a, halg]`. Both sides reduce to the same expression.

Use `⟨y, ⟨T', i.comp io, e, y₀, he, ⟨hfin', fun s => ?_⟩, p, inferInstance, inst, kA, y, hy, rfl⟩, h2.trans hPk.symm, Q, π, ψ, z, h1, h3⟩` and prove the remaining obligations. Take `rfl : s = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T'.Fr)` from `Subsingleton.elim (α := PrimeSpectrum T'.Fr) _ _`. Establish `h4` using `hP (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ_[p])`. Rewrite `h4` using `[hPk, hpt, bot_map k.injective]`. Conclude with `h4`.
-/
theorem exFrameSt_holds : ExFrameSt := by
  intro E _ _ _ H Dw l Xo c hpq Y Zc la p _ inst hla P yb hyb hP
  obtain ⟨hgen, T, kO, yT, hfin, hkO, hyT⟩ := hyb
  have hiO : Function.Injective (algebraMap 𝓞_ℂ_[p] ℂ_[p]) := (PadicComplexInt.integers p).hom_inj
  have hgX : Set.range (spMap (algebraMap T.V T.Fr) ≫ yT) ⊆ Set.range Y.j := by
    rintro _ ⟨s, rfl⟩
    obtain rfl : s = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T.Fr) := Subsingleton.elim (α := PrimeSpectrum T.Fr) _ _
    have h1 := bot_map (IsFractionRing.injective T.V T.Fr) yT
    have h2 := bot_map (φ := (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO) (hiO.comp hkO) yT
    rw [← sp_sp, hyT, hgen] at h2
    rw [h1, ← h2]
    exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
  obtain ⟨yyT, hyyT⟩ := exists_lift_int Y _ hgX
  obtain ⟨io, hio⟩ : ∃ io : c.F →+* T.Fr, yyT ≫ pullback.snd _ _ = spMap io :=
    ⟨(Spec.preimage (yyT ≫ pullback.snd _ _)).hom, (Spec.map_preimage (yyT ≫ pullback.snd _ _)).symm⟩
  let x : Sp T.Fr ⟶ Xo.X := yyT ≫ pullback.fst _ _
  have hx : (letI := io.toAlgebra; x ≫ Xo.s = sOf c T.Fr) := by
    letI := io.toAlgebra
    show (yyT ≫ pullback.fst _ _) ≫ Xo.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc yyT, hio, sOf, spMap_spMap]
  obtain ⟨T', i, rr, hrr, hv, hfin', y₀, hy₀⟩ := GlobalTheory.AnyLevelFrame.intFrExt E H Dw l Xo c hpq T io hfin x hx
  obtain ⟨φ, hφ, hloc⟩ := GlobalTheory.GoodChartExt.exists_local_restrict T T' i rr hrr hv
  have hφi : Function.Injective φ := by
    intro a b h
    apply i.injective.comp (IsFractionRing.injective T.V T.Fr)
    have ha := RingHom.congr_fun hφ a
    have hb := RingHom.congr_fun hφ b
    simp only [RingHom.comp_apply] at ha hb
    simp only [Function.comp_apply, ← ha, ← hb, h]
  have hfinφ : φ.Finite := GlobalTheory.CompHS.finite_of_finRes hfin' φ hφi
  obtain ⟨kO', hkO', hinj'⟩ := exists_ext_of_integral (Valued.v : Valuation ℂ_[p] ℝ≥0) (PadicComplexInt.integers p)
    φ hφi hfinφ.to_isIntegral kO (hiO.comp hkO)
  let k : T'.Fr →+* ℂ_[p] := IsFractionRing.lift hinj'
  have hk : ∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO' a) = k (algebraMap T'.V T'.Fr a) := fun a =>
    (IsFractionRing.lift_algebraMap hinj' a).symm
  have hcomm : spMap (algebraMap T'.V T'.Fr) ≫ (spMap φ ≫ yT) = (spMap i ≫ yyT) ≫ Y.j := by
    rw [sp_sp, hφ, ← sp_sp, Category.assoc, hyyT]
  have hPk : GlobalTheory.AllWt.ptF P = spMap k ≫ spMap i ≫ yyT := by
    have := mono_j_int Y
    rw [← cancel_mono Y.j, ← hgen, Category.assoc, ← hcomm, ← hyT, ← hkO', sp_sp, sp_sp, sp_sp]
    congr 2
    exact RingHom.ext fun a => hk (φ a)
  have halg : algebraMap c.F ℂ_[p] = k.comp (i.comp io) := by
    have h1 := ptF_snd P
    rw [hPk, Category.assoc, Category.assoc, hio, spMap_spMap, spMap_spMap] at h1
    exact (congrArg CommRingCat.Hom.hom (Spec.map_injective h1)).symm
  letI := (i.comp io).toAlgebra
  letI := H.starRing
  let kA : T'.Fr →ₐ[c.F] ℂ_[p] := { k with commutes' := fun a => (RingHom.congr_fun halg a).symm }
  obtain ⟨y, hy⟩ := GlobalTheory.CompHt.exists_isHTFrame (p := p) (v := (Valued.v : Valuation ℂ_[p] ℝ≥0)) (O := 𝓞_ℂ_[p])
    (fun _ => rfl) (PadicComplexInt.integers p) y₀ hfin' kA kO' hk
  have hpt : spMap i ≫ yyT = GlobalTheory.AllWt.ptF y₀.1 := by
    apply pullback.hom_ext
    · rw [GlobalTheory.AllWt.ptF, pullback.lift_fst, hy₀, Category.assoc]
    · rw [GlobalTheory.AllWt.ptF, pullback.lift_snd, Category.assoc, hio, spMap_spMap]
  obtain ⟨Q, π, ψ, z, h1, h2, h3⟩ := ptAt_of_isHTFrame Y Y.m0.toSABMap p T' T' (RingHom.id _) (RingHom.id _)
    (fun _ => rfl) (i.comp io) y₀ kA y hy k kO' hk (fun _ => rfl) (spMap φ ≫ yT) (spMap i ≫ yyT) hcomm
    (by rw [show spMap (RingHom.id T'.Fr) = 𝟙 _ from Spec.map_id _, Category.id_comp, hpt])
  rw [sp_sp, hkO', hyT, ← hPk] at h1
  obtain ⟨e, he⟩ := exists_overLa la T' (i.comp io) p k kO' hk fun a => by
    rw [← hla a, halg]; rfl
  refine ⟨y, ⟨T', i.comp io, e, y₀, he, ⟨hfin', fun s => ?_⟩, p, inferInstance, inst, kA, y, hy, rfl⟩, h2.trans hPk.symm,
    Q, π, ψ, z, h1, h3⟩
  obtain rfl : s = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T'.Fr) := Subsingleton.elim (α := PrimeSpectrum T'.Fr) _ _
  have h4 := hP (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ_[p])
  rw [hPk, hpt, bot_map k.injective] at h4
  exact h4

end GlobalTheory.DetHT

end
