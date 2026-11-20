import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveVertPointLengthSteps
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftBirationalAmple
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple

noncomputable section

namespace CurveSectionQuotientLocal

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  (y : (Σ k, ι k) → Ω)

/- English proof (translation)
Use `show _ ∈ chartLat y _ 1`. Establish `h` using `chartLat_prod (y := y) Finset.univ (fun k => y ⟨k, c k⟩ ^ d k) (fun k => d k • (Pi.single k 1 : K → ℤ)) (fun k _ => chartLat_pow (chartLat_var (y := y) ⟨k, c k⟩) (d k))`. Use `h using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`. Rewrite using `[Finset.sum_apply, Finset.sum_eq_single j]`.

Simplify using the standard rewrite rules. Introduce `k _ hk`. Simplify using `[Ne.symm hk]`. Simplify using the standard rewrite rules.
-/
theorem chart_mem_curveSectionMod (c : ∀ k, ι k) (d : K → ℕ) :
    ∏ k, y ⟨k, c k⟩ ^ d k ∈ curveSectionMod y (fun k => (d k : ℤ)) := by
  classical
  show _ ∈ chartLat y _ 1
  have h := chartLat_prod (y := y) Finset.univ (fun k => y ⟨k, c k⟩ ^ d k)
    (fun k => d k • (Pi.single k 1 : K → ℤ))
    (fun k _ => chartLat_pow (chartLat_var (y := y) ⟨k, c k⟩) (d k))
  convert h using 2
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [Ne.symm hk]
  · simp

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Proceed by induction on `hz using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨p, rfl⟩` from `hx`. Conclude with `h p`. Consider the case `algebraMap r`.

Use `⟨(r : curveRing y), 1, (Ideal.ne_top_iff_one m).mp hm.ne_top, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Consider the case `add x z _ _ hx hz`. Take `⟨a₁, b₁, hb₁, e₁⟩` from `hx`. Take `⟨a₂, b₂, hb₂, e₂⟩` from `hz`.

Use `⟨b₂ * a₁ + b₁ * a₂, b₁ * b₂, fun hmem => (hm.mem_or_mem hmem).elim hb₁ hb₂, ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[← e₁, ← e₂]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul x z _ _ hx hz`.

Take `⟨a₁, b₁, hb₁, e₁⟩` from `hx`. Take `⟨a₂, b₂, hb₂, e₂⟩` from `hz`. Use `⟨a₁ * a₂, b₁ * b₂, fun hmem => (hm.mem_or_mem hmem).elim hb₁ hb₂, ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[← e₁, ← e₂]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_mul_mem_of_mem_chartRingZ (m : Ideal (curveRing y)) (hm : m.IsPrime) (c : ∀ k, ι k)
    (h : ∀ p : Σ k, ι k, ∃ a b : curveRing y, b ∉ m ∧ (b : Ω) * (y p / y ⟨p.1, c p.1⟩) = a)
    {z : Ω} (hz : z ∈ chartRingZ y c) :
    ∃ a b : curveRing y, b ∉ m ∧ (b : Ω) * z = a := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact h p
  | algebraMap r =>
    refine ⟨(r : curveRing y), 1, (Ideal.ne_top_iff_one m).mp hm.ne_top, ?_⟩
    simp
  | add x z _ _ hx hz =>
    obtain ⟨a₁, b₁, hb₁, e₁⟩ := hx
    obtain ⟨a₂, b₂, hb₂, e₂⟩ := hz
    refine ⟨b₂ * a₁ + b₁ * a₂, b₁ * b₂, fun hmem => (hm.mem_or_mem hmem).elim hb₁ hb₂, ?_⟩
    push_cast
    rw [← e₁, ← e₂]
    ring
  | mul x z _ _ hx hz =>
    obtain ⟨a₁, b₁, hb₁, e₁⟩ := hx
    obtain ⟨a₂, b₂, hb₂, e₂⟩ := hz
    refine ⟨a₁ * a₂, b₁ * b₂, fun hmem => (hm.mem_or_mem hmem).elim hb₁ hb₂, ?_⟩
    push_cast
    rw [← e₁, ← e₂]
    ring

end CurveSectionQuotientLocal

open CurveSectionQuotientLocal in

/- English proof (translation)
Introduce `K _ ι _ Ω _ y s d _hy _hs _hsP m c hm hc hrat a b hb hba`. Use `set x := aeval y s with hx_def`. Use `set e₀ : Ω := ∏ k, y ⟨k, c k⟩ ^ d k with he₀_def`. Establish `he₀ : e₀ ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)`. Set `e : curveSectionMod y (fun k => (d k : ℤ))` to `⟨e₀, chart_mem_curveSectionMod y c d⟩`.

Set `φ : curveRing y →ₗ[curveRing y] curveSectionQuot y (fun k => (d k : ℤ)) x` to `LinearMap.toSpanSingleton (curveRing y) _ (Submodule.Quotient.mk e)`. Establish `hφ : ∀ β : curveRing y, φ β = Submodule.Quotient.mk (β • e)` using `fun β => by`. Simplify using `[φ, Submodule.Quotient.mk_smul]`. Establish `hφ0 : ∀ β : curveRing y, φ β = 0 ↔ ∃ γ : curveRing y, (γ : Ω) * x = β * e₀`. Introduce `β`.

Rewrite using `[hφ, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_span_singleton]`. Both sides reduce to the same expression. Establish `hle : Ideal.span {a} ≤ LinearMap.ker φ`. Rewrite using `[Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, hφ0]`. Conclude with `⟨b, hba⟩`.

Set `ψ : (curveRing y ⧸ Ideal.span {a}) →ₗ[curveRing y] curveSectionQuot y (fun k => (d k : ℤ)) x` to `(Ideal.span {a}).liftQ φ hle`. Establish `hker : ∀ q, ψ q = 0 → b • q = 0`. Introduce `q hq`. Take `⟨β, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Take `⟨γ, hγ⟩` from `(hφ0 β).mp hq`.

Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul, Ideal.mem_span_singleton']`. Use `⟨γ, Subtype.ext ?_⟩` and prove the remaining obligations. Use `push_cast`. Apply `mul_right_cancel₀ he₀` to reduce the goal to its premises. Rewrite using `[mul_assoc, ← hba, mul_assoc, ← hγ]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsurj0 : ∀ n : curveSectionMod y (fun k => (d k : ℤ)), ∃ r : curveRing y, r ∉ m ∧ ∃ β : curveRing y, r • n = β • e`. Introduce `n`. Establish `hn : (n : Ω) ∈ chartLat y (fun k => (d k : ℤ)) 1` using `n.2`. Establish `hnc : (n : Ω) * e₀⁻¹ ∈ chartRingZ y c`.

Establish `h1` using `(mem_chartLat_one y).mp hn c hc`. Establish `h2 : ∏ k, y ⟨k, c k⟩ ^ (-((fun k => (d k : ℤ)) k)) = e₀⁻¹`. Rewrite using `[he₀_def, ← Finset.prod_inv_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[zpow_neg, zpow_natCast]`.

Rewrite `h1` using `[h2]`. Then use the resulting hypothesis. Take `⟨β, r, hr, hβ⟩` from `exists_mul_mem_of_mem_chartRingZ y m hm c hrat hnc`. Use `⟨r, hr, β, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show (r : Ω) * n = β * e₀`. Rewrite using `[← hβ]`.

Clear the denominators using the available nonvanishing facts. Set `S` to `m.primeCompl`. Set `Φ` to `IsLocalizedModule.map S (LocalizedModule.mkLinearMap S (curveRing y ⧸ Ideal.span {a})) (LocalizedModule.mkLinearMap S (curveSectionQuot y (fun k => (d k : ℤ)) x)) ψ`. Establish `hΦ : ∀ q (r : S), Φ (LocalizedModule.mk q r) = LocalizedModule.mk (ψ q) r` using `fun q r => IsLocalizedModule.map_LocalizedModules S _ q r`. Establish `hinj : Function.Injective Φ`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `z`. Use `LocalizedModule.induction_on (β := fun z => Φ z = 0 → z = 0) (fun q r hz => ?_) z` and prove the remaining obligations. Rewrite `hz` using `[hΦ, ← LocalizedModule.zero_mk r, LocalizedModule.mk_eq]`. Take `⟨u, hu⟩` from `hz`.

Simplify using `only [smul_zero, Submonoid.smul_def] at hu`. Rewrite `hu` using `[← map_smul, ← map_smul]`. Establish `hq` using `hker _ hu`. Rewrite using `[← LocalizedModule.zero_mk r, LocalizedModule.mk_eq]`. Use `⟨⟨b * u, S.mul_mem hb u.2⟩, ?_⟩` and prove the remaining obligations.

Simplify using `only [smul_zero, Submonoid.smul_def, mul_smul]`. Conclude with `hq`. Establish `hsurj : Function.Surjective Φ`. Introduce `z`. Use `LocalizedModule.induction_on (β := fun z => ∃ w, Φ w = z) (fun n r => ?_) z` and prove the remaining obligations.

Take `⟨n', rfl⟩` from `Submodule.Quotient.mk_surjective _ n`. Take `⟨r', hr', β, hβ⟩` from `hsurj0 n'`. Use `⟨LocalizedModule.mk (Submodule.Quotient.mk β) (⟨r', hr'⟩ * r), ?_⟩` and prove the remaining obligations. Rewrite using `[hΦ]`. Establish `hψ : ψ (Submodule.Quotient.mk β) = Submodule.Quotient.mk (β • e)`.

Rewrite using `[← hφ]`. Both sides reduce to the same expression. Rewrite using `[hψ, ← hβ, Submodule.Quotient.mk_smul]`. Conclude with `LocalizedModule.mk_cancel_common_left ⟨r', hr'⟩ r _`. Use `hm` as an intermediate fact.

Set `E` to `(LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).extendScalarsOfIsLocalization S (Localization.AtPrime m)`. Unfold `locLen`. Rewrite using `[dif_pos hm, dif_pos hm, E.length_eq]`.
-/
theorem CurveSectionQuotLocal.proof : CurveSectionQuotLocal.Statement := by
  intro K _ ι _ Ω _ y s d _hy _hs _hsP m c hm hc hrat a b hb hba
  set x := aeval y s with hx_def
  set e₀ : Ω := ∏ k, y ⟨k, c k⟩ ^ d k with he₀_def
  have he₀ : e₀ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)

  let e : curveSectionMod y (fun k => (d k : ℤ)) := ⟨e₀, chart_mem_curveSectionMod y c d⟩
  let φ : curveRing y →ₗ[curveRing y] curveSectionQuot y (fun k => (d k : ℤ)) x :=
    LinearMap.toSpanSingleton (curveRing y) _ (Submodule.Quotient.mk e)
  have hφ : ∀ β : curveRing y, φ β = Submodule.Quotient.mk (β • e) := fun β => by
    simp [φ, Submodule.Quotient.mk_smul]
  have hφ0 : ∀ β : curveRing y, φ β = 0 ↔ ∃ γ : curveRing y, (γ : Ω) * x = β * e₀ := by
    intro β
    rw [hφ, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_span_singleton]
    rfl
  have hle : Ideal.span {a} ≤ LinearMap.ker φ := by
    rw [Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, hφ0]
    exact ⟨b, hba⟩
  let ψ : (curveRing y ⧸ Ideal.span {a}) →ₗ[curveRing y] curveSectionQuot y (fun k => (d k : ℤ)) x :=
    (Ideal.span {a}).liftQ φ hle

  have hker : ∀ q, ψ q = 0 → b • q = 0 := by
    intro q hq
    obtain ⟨β, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨γ, hγ⟩ := (hφ0 β).mp hq
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul,
      Ideal.mem_span_singleton']
    refine ⟨γ, Subtype.ext ?_⟩
    push_cast
    apply mul_right_cancel₀ he₀
    rw [mul_assoc, ← hba, mul_assoc, ← hγ]
    ring

  have hsurj0 : ∀ n : curveSectionMod y (fun k => (d k : ℤ)),
      ∃ r : curveRing y, r ∉ m ∧ ∃ β : curveRing y, r • n = β • e := by
    intro n
    have hn : (n : Ω) ∈ chartLat y (fun k => (d k : ℤ)) 1 := n.2
    have hnc : (n : Ω) * e₀⁻¹ ∈ chartRingZ y c := by
      have h1 := (mem_chartLat_one y).mp hn c hc
      have h2 : ∏ k, y ⟨k, c k⟩ ^ (-((fun k => (d k : ℤ)) k)) = e₀⁻¹ := by
        rw [he₀_def, ← Finset.prod_inv_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [zpow_neg, zpow_natCast]
      rwa [h2] at h1
    obtain ⟨β, r, hr, hβ⟩ := exists_mul_mem_of_mem_chartRingZ y m hm c hrat hnc
    refine ⟨r, hr, β, Subtype.ext ?_⟩
    show (r : Ω) * n = β * e₀
    rw [← hβ]
    field_simp

  let S := m.primeCompl
  let Φ := IsLocalizedModule.map S (LocalizedModule.mkLinearMap S (curveRing y ⧸ Ideal.span {a}))
    (LocalizedModule.mkLinearMap S (curveSectionQuot y (fun k => (d k : ℤ)) x)) ψ
  have hΦ : ∀ q (r : S), Φ (LocalizedModule.mk q r) = LocalizedModule.mk (ψ q) r :=
    fun q r => IsLocalizedModule.map_LocalizedModules S _ q r
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro z
    refine LocalizedModule.induction_on (β := fun z => Φ z = 0 → z = 0) (fun q r hz => ?_) z
    rw [hΦ, ← LocalizedModule.zero_mk r, LocalizedModule.mk_eq] at hz
    obtain ⟨u, hu⟩ := hz
    simp only [smul_zero, Submonoid.smul_def] at hu
    rw [← map_smul, ← map_smul] at hu
    have hq := hker _ hu
    rw [← LocalizedModule.zero_mk r, LocalizedModule.mk_eq]
    refine ⟨⟨b * u, S.mul_mem hb u.2⟩, ?_⟩
    simp only [smul_zero, Submonoid.smul_def, mul_smul]
    exact hq
  have hsurj : Function.Surjective Φ := by
    intro z
    refine LocalizedModule.induction_on (β := fun z => ∃ w, Φ w = z) (fun n r => ?_) z
    obtain ⟨n', rfl⟩ := Submodule.Quotient.mk_surjective _ n
    obtain ⟨r', hr', β, hβ⟩ := hsurj0 n'
    refine ⟨LocalizedModule.mk (Submodule.Quotient.mk β) (⟨r', hr'⟩ * r), ?_⟩
    rw [hΦ]
    have hψ : ψ (Submodule.Quotient.mk β) = Submodule.Quotient.mk (β • e) := by
      rw [← hφ]
      rfl
    rw [hψ, ← hβ, Submodule.Quotient.mk_smul]
    exact LocalizedModule.mk_cancel_common_left ⟨r', hr'⟩ r _
  have := hm
  let E := (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).extendScalarsOfIsLocalization S
    (Localization.AtPrime m)
  unfold locLen
  rw [dif_pos hm, dif_pos hm, E.length_eq]

end

end GroundTheory.Heights₂.Heights.Targets
