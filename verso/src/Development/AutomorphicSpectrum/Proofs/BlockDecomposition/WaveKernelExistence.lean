import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ContDiff ComplexConjugate

namespace GlobalTheory.CompanionTheory.WaveKer

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Local

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

/- English proof (translation)
Use `filter_upwards [h.eventuallyEq_nhds] with y hy`. Simplify using `only [Rd, Pi.zero_apply]`. Rewrite using `[hy.fderiv_eq]`. Establish `: fderiv ℝ (0 : Mat n → V) y = 0`. Simplify using `using fderiv_const_apply (𝕜 := ℝ) (x := y) (0 : V)`.

Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem Rd_germ (X : Mat n) {f : Mat n → V} {x : Mat n} (h : f =ᶠ[𝓝 x] 0) :
    Rd X f =ᶠ[𝓝 x] 0 := by
  filter_upwards [h.eventuallyEq_nhds] with y hy
  simp only [Rd, Pi.zero_apply]
  rw [hy.fderiv_eq]
  have : fderiv ℝ (0 : Mat n → V) y = 0 := by
    simpa using fderiv_const_apply (𝕜 := ℝ) (x := y) (0 : V)
  rw [this]
  rfl

/- English proof (translation)
Use `filter_upwards [Rd_germ (Matrix.single a b 1) h, Rd_germ (Matrix.single a b Complex.I) h] with y h1 h2`. Simplify using `only [Eu, Pi.smul_apply, Pi.add_apply, h1, h2, Pi.zero_apply, smul_zero, add_zero]`.
-/
theorem Eu_germ (s : Bool) (a b : Fin n) {f : Mat n → V} {x : Mat n} (h : f =ᶠ[𝓝 x] 0) :
    Eu s a b f =ᶠ[𝓝 x] 0 := by
  filter_upwards [Rd_germ (Matrix.single a b 1) h, Rd_germ (Matrix.single a b Complex.I) h]
    with y h1 h2
  simp only [Eu, Pi.smul_apply, Pi.add_apply, h1, h2, Pi.zero_apply, smul_zero, add_zero]

/- English proof (translation)
Proceed by induction on `m generalizing a b with`. Consider the case `zero`. Distinguish the cases in `hab : a = b`. Simplify `h` using `[Epow, hab]`. Simplify using `[Epow, hab]`.

Consider the case `succ m ih`. Establish `: ∀ᶠ y in 𝓝 x, ∀ c, Eu s a c (Epow s m c b f) y = 0` using `eventually_all.2 fun c => Eu_germ s a c (ih c b)`. Use `filter_upwards [this] with y hy`. Simplify using `[Epow, Finset.sum_apply, hy]`.
-/
theorem Epow_germ (s : Bool) (m : ℕ) (a b : Fin n) {f : Mat n → V} {x : Mat n}
    (h : f =ᶠ[𝓝 x] 0) : Epow s m a b f =ᶠ[𝓝 x] 0 := by
  induction m generalizing a b with
  | zero =>
    by_cases hab : a = b
    · simpa [Epow, hab] using h
    · simp [Epow, hab]
  | succ m ih =>
    have : ∀ᶠ y in 𝓝 x, ∀ c, Eu s a c (Epow s m c b f) y = 0 :=
      eventually_all.2 fun c => Eu_germ s a c (ih c b)
    filter_upwards [this] with y hy
    simp [Epow, Finset.sum_apply, hy]

/- English proof (translation)
Establish `: ∀ᶠ y in 𝓝 x, ∀ a, Epow s m a a f y = 0` using `eventually_all.2 fun a => Epow_germ s m a a h`. Use `filter_upwards [this] with y hy`. Simplify using `[gel, Finset.sum_apply, hy]`.
-/
theorem gel_germ (s : Bool) (m : ℕ) {f : Mat n → V} {x : Mat n} (h : f =ᶠ[𝓝 x] 0) :
    gel s m f =ᶠ[𝓝 x] 0 := by
  have : ∀ᶠ y in 𝓝 x, ∀ a, Epow s m a a f y = 0 :=
    eventually_all.2 fun a => Epow_germ s m a a h
  filter_upwards [this] with y hy
  simp [gel, Finset.sum_apply, hy]

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => simpa [zOp] using h`. Consider the case `cons p w ih => exact gel_germ p.1 p.2 ih`.
-/
theorem zOp_germ (w : List (Bool × ℕ)) {f : Mat n → V} {x : Mat n} (h : f =ᶠ[𝓝 x] 0) :
    zOp w f =ᶠ[𝓝 x] 0 := by
  induction w with
  | nil => simpa [zOp] using h
  | cons p w ih => exact gel_germ p.1 p.2 ih

end Local

/- English proof (translation)
Simplify using `[GLs]`.
-/
theorem one_mem_GLs (n : ℕ) : (1 : Mat n) ∈ GLs n := by simp [GLs]

/- English proof (translation)
Simplify using `only [GLs, Set.mem_setOf_eq, det_mul] at *`. Conclude with `mul_ne_zero hx hy`.
-/
theorem mul_mem_GLs {n : ℕ} {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, det_mul] at *
  exact mul_ne_zero hx hy

/- English proof (translation)
Introduce `h`. Establish `h1` using `congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.1 k.2)`. Rewrite `h1` using `[det_mul, h, mul_zero, det_one]`. Conclude with `zero_ne_one h1`.
-/
theorem unitary_mem_GLs {n : ℕ} (k : Matrix.unitaryGroup (Fin n) ℂ) : k.1 ∈ GLs n := by
  intro h
  have h1 := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.1 k.2)
  rw [det_mul, h, mul_zero, det_one] at h1
  exact zero_ne_one h1

/- English proof (translation)
The claim follows from `((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero`.
-/
theorem val_mem_GLs {n : ℕ} (y : G n) : y.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

/- English proof (translation)
Establish `hc : Continuous fun g : Mat n => g.det` using `continuous_id.matrix_det`. Conclude with `isOpen_ne.preimage hc`.
-/
theorem isOpen_GLs (n : ℕ) : IsOpen (GLs n) := by
  have hc : Continuous fun g : Mat n => g.det := continuous_id.matrix_det
  exact isOpen_ne.preimage hc

/- English proof (translation)
Establish `h` using `(hL n).1 1 (one_mem_GLs n) 1 (one_mem_GLs n)`. Rewrite `h` using `[one_mul]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lg_one_nonneg (hL : LgFacts) (n : ℕ) : 0 ≤ lg (1 : Mat n) := by
  have h := (hL n).1 1 (one_mem_GLs n) 1 (one_mem_GLs n)
  rw [one_mul] at h
  linarith

/- English proof (translation)
Take `⟨hsub, -, hinv, hsm, -, -, -⟩` from `hL n`. Establish `hL0` using `lg_one_nonneg hL n`. Establish `hM0 : 0 ≤ max c₀ 0` using `le_max_right _ _`. Establish `hGo` using `isOpen_GLs n`. Use `set A : ℝ := (max c₀ 0 + lg (1 : Mat n) + 1) * (1 + T) with hA`.

Establish `hUo : IsOpen (GLs n ∩ lg ⁻¹' Set.Ioi A)` using `hsm.continuousOn.isOpen_inter_preimage hGo isOpen_Ioi`. Use `hU n μ E k (GLs n ∩ lg ⁻¹' Set.Ioi A) hUo Set.inter_subset_left ?_ hk.1.continuousOn ?_ ?_ y ⟨hy, hlt⟩` and prove the remaining obligations. Introduce `z hz k₂`. Use `⟨mul_mem_GLs hz.1 (unitary_mem_GLs k₂), ?_⟩` and prove the remaining obligations. Establish `h` using `hinv z hz.1 1 k₂`.

Simplify using `only [OneMemClass.coe_one, one_mul] at h`. Simplify `hz.2` using `[h]`. Introduce `z hz k₂`. Establish `h` using `hk.2.2.1 z hz 1 k₂`. Simplify using `using h`.

Introduce `f hf _ hoff`. Take `⟨u, hu, hu0⟩` from `hE n E f hf`. Establish `hact : act μ E k f 1 = act μ E k (u 0) 1`. Simplify using `only [act]`. Use `congr 1`.

Use function extensionality and compare the values at `z`. Rewrite using `[one_mul, hu0 _ (val_mem_GLs z)]`. Establish `hzero : ∀ x ∈ GLs n, lg x < lg (1 : Mat n) + 1 → ∀ t, |t| ≤ T → u t x = 0`. Introduce `x hx hlx t ht`. Use `hc E u hu t x hx fun z hz hlz => ?_` and prove the remaining obligations.

Rewrite using `[hu0 _ (mul_mem_GLs hx hz)]`. Use `hoff _ (mul_mem_GLs hx hz) ?_` and prove the remaining obligations. Introduce and unpack `⟨-, hbig⟩`. Establish `hbig' : A < lg (x * z)` using `hbig`. Establish `h0` using `hsub x hx z hz`.

Establish `h1 : c₀ * (1 + |t|) ≤ max c₀ 0 * (1 + |t|)` using `mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)`. Establish `h2 : max c₀ 0 * (1 + |t|) ≤ max c₀ 0 * (1 + T)` using `mul_le_mul_of_nonneg_left (by linarith) hM0`. Establish `h3 : lg (1 : Mat n) + 1 ≤ (lg (1 : Mat n) + 1) * (1 + T)` using `by nlinarith`. Establish `h4 : A = max c₀ 0 * (1 + T) + (lg (1 : Mat n) + 1) * (1 + T)` using `by rw [hA]; ring`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hF : (fun x' => ∫ t, (g t : ℂ) • u t x') =ᶠ[𝓝 (1 : Mat n)] 0`. Establish `hN : GLs n ∩ lg ⁻¹' Set.Iio (lg (1 : Mat n) + 1) ∈ 𝓝 (1 : Mat n)` using `(hsm.continuousOn.isOpen_inter_preimage hGo isOpen_Iio).mem_nhds ⟨one_mem_GLs n, Set.mem_preimage.2 (Set.mem_Iio.2 (lt_add_one _))⟩`. Use `filter_upwards [hN] with x hx`. Establish `h0 : ∀ t, (g t : ℂ) • u t x = 0`. Introduce `t`.

Distinguish the cases in `ht : |t| ≤ T`. Rewrite using `[hzero x hx.1 hx.2 t ht, smul_zero]`. Rewrite using `[hg.2.2 t (not_le.1 ht)]`. Simplify using the standard rewrite rules. Simplify using `[h0]`.

Rewrite using `[hact, hk.2.2.2 u hu 1 (one_mem_GLs n)]`. Conclude with `(zOp_germ w hF).self_of_nhds`.
-/
theorem ker_support (hL : LgFacts) (hE : WaveEx) (hU : KerUniq) {n : ℕ}
    [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (c₀ : ℝ)
    (hc : ∀ (E : KMod n) (u : ℝ → Mat n → E.V), IsWave E u → ∀ (t : ℝ), ∀ x ∈ GLs n,
      (∀ y ∈ GLs n, lg y ≤ c₀ * (1 + |t|) → u 0 (x * y) = 0) → u t x = 0)
    {w : List (Bool × ℕ)} {g : ℝ → ℝ} {T : ℝ} {k : Mat n → (E.V →L[ℂ] E.V)} (hT : 0 ≤ T)
    (hg : IsBump g T) (hk : IsKer μ E w g k) {y : Mat n} (hy : y ∈ GLs n)
    (hlt : (max c₀ 0 + lg (1 : Mat n) + 1) * (1 + T) < lg y) : k y = 0 := by
  obtain ⟨hsub, -, hinv, hsm, -, -, -⟩ := hL n
  have hL0 := lg_one_nonneg hL n
  have hM0 : 0 ≤ max c₀ 0 := le_max_right _ _
  have hGo := isOpen_GLs n
  set A : ℝ := (max c₀ 0 + lg (1 : Mat n) + 1) * (1 + T) with hA
  have hUo : IsOpen (GLs n ∩ lg ⁻¹' Set.Ioi A) :=
    hsm.continuousOn.isOpen_inter_preimage hGo isOpen_Ioi
  refine hU n μ E k (GLs n ∩ lg ⁻¹' Set.Ioi A) hUo Set.inter_subset_left ?_
    hk.1.continuousOn ?_ ?_ y ⟨hy, hlt⟩
  · intro z hz k₂
    refine ⟨mul_mem_GLs hz.1 (unitary_mem_GLs k₂), ?_⟩
    have h := hinv z hz.1 1 k₂
    simp only [OneMemClass.coe_one, one_mul] at h
    simpa [h] using hz.2
  · intro z hz k₂
    have h := hk.2.2.1 z hz 1 k₂
    simpa using h
  · intro f hf _ hoff
    obtain ⟨u, hu, hu0⟩ := hE n E f hf
    have hact : act μ E k f 1 = act μ E k (u 0) 1 := by
      simp only [act]
      congr 1
      funext z
      rw [one_mul, hu0 _ (val_mem_GLs z)]
    have hzero : ∀ x ∈ GLs n, lg x < lg (1 : Mat n) + 1 → ∀ t, |t| ≤ T → u t x = 0 := by
      intro x hx hlx t ht
      refine hc E u hu t x hx fun z hz hlz => ?_
      rw [hu0 _ (mul_mem_GLs hx hz)]
      refine hoff _ (mul_mem_GLs hx hz) ?_
      rintro ⟨-, hbig⟩
      have hbig' : A < lg (x * z) := hbig
      have h0 := hsub x hx z hz
      have h1 : c₀ * (1 + |t|) ≤ max c₀ 0 * (1 + |t|) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      have h2 : max c₀ 0 * (1 + |t|) ≤ max c₀ 0 * (1 + T) :=
        mul_le_mul_of_nonneg_left (by linarith) hM0
      have h3 : lg (1 : Mat n) + 1 ≤ (lg (1 : Mat n) + 1) * (1 + T) := by nlinarith
      have h4 : A = max c₀ 0 * (1 + T) + (lg (1 : Mat n) + 1) * (1 + T) := by rw [hA]; ring
      linarith
    have hF : (fun x' => ∫ t, (g t : ℂ) • u t x') =ᶠ[𝓝 (1 : Mat n)] 0 := by
      have hN : GLs n ∩ lg ⁻¹' Set.Iio (lg (1 : Mat n) + 1) ∈ 𝓝 (1 : Mat n) :=
        (hsm.continuousOn.isOpen_inter_preimage hGo isOpen_Iio).mem_nhds
          ⟨one_mem_GLs n, Set.mem_preimage.2 (Set.mem_Iio.2 (lt_add_one _))⟩
      filter_upwards [hN] with x hx
      have h0 : ∀ t, (g t : ℂ) • u t x = 0 := by
        intro t
        by_cases ht : |t| ≤ T
        · rw [hzero x hx.1 hx.2 t ht, smul_zero]
        · rw [hg.2.2 t (not_le.1 ht)]
          simp
      simp [h0]
    rw [hact, hk.2.2.2 u hu 1 (one_mem_GLs n)]
    exact (zOp_germ w hF).self_of_nhds

/- English proof (translation)
Introduce `hL _ hS hE hU hO n`. Take `⟨c₀, hc⟩` from `hS n`. Use `⟨max c₀ 0 + lg (1 : Mat n) + 1, ?_⟩` and prove the remaining obligations. Introduce `_ _ μ _ E`. Use `⟨fun w g T hg => hO n μ E w g T hg, ?_⟩` and prove the remaining obligations.

Introduce and unpack `k val T hT ⟨m, c, w, g, ks, hi, hsum, -⟩ y hy hlt`. Rewrite using `[hsum y hy]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[ker_support hL hE hU μ E c₀ hc hT (hi i).1 (hi i).2 hy hlt, smul_zero]`.
-/
theorem asmKerEx : AsmKerEx := by
  intro hL _ hS hE hU hO n
  obtain ⟨c₀, hc⟩ := hS n
  refine ⟨max c₀ 0 + lg (1 : Mat n) + 1, ?_⟩
  intro _ _ μ _ E
  refine ⟨fun w g T hg => hO n μ E w g T hg, ?_⟩
  rintro k val T hT ⟨m, c, w, g, ks, hi, hsum, -⟩ y hy hlt
  rw [hsum y hy]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [ker_support hL hE hU μ E c₀ hc hT (hi i).1 (hi i).2 hy hlt, smul_zero]

end GlobalTheory.CompanionTheory.WaveKer
