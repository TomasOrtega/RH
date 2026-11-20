import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChPrime

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.KerChart

open MvPolynomial ReciprocityTheory.AnForm.R

variable {σ : Type}

/- English proof (translation)
Proceed by induction on `G using MvPolynomial.induction_on with`. Consider the case `C a`. Use `⟨a.den, C a.num, by exact_mod_cast a.den_nz, ?_⟩` and prove the remaining obligations. Rewrite using `[map_C, ← C_mul]`. Use `congr 1`.

Simplify using `[Rat.den_mul_eq_num]`. Consider the case `add f g hf hg`. Take `⟨n₁, F, h₁, e₁⟩` from `hf`. Take `⟨n₂, F', h₂, e₂⟩` from `hg`. Use `⟨n₁ * n₂, C n₂ * F + C n₁ * F', mul_ne_zero h₁ h₂, ?_⟩` and prove the remaining obligations.

Simplify using `only [map_add, map_mul, map_C, e₁, e₂]`. Simplify using `only [eq_intCast, Int.cast_mul, C_mul]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul_X f i hf`. Take `⟨n, F, h, e⟩` from `hf`.

Conclude with `⟨n, F * X i, h, by rw [map_mul, map_X, e, mul_assoc]⟩`.
-/
theorem exists_int_clear (G : MvPolynomial σ ℚ) :
    ∃ (n : ℤ) (G₀ : MvPolynomial σ ℤ), n ≠ 0 ∧
      map (Int.castRingHom ℚ) G₀ = C (n : ℚ) * G := by
  induction G using MvPolynomial.induction_on with
  | C a =>
    refine ⟨a.den, C a.num, by exact_mod_cast a.den_nz, ?_⟩
    rw [map_C, ← C_mul]
    congr 1
    simp [Rat.den_mul_eq_num]
  | add f g hf hg =>
    obtain ⟨n₁, F, h₁, e₁⟩ := hf
    obtain ⟨n₂, F', h₂, e₂⟩ := hg
    refine ⟨n₁ * n₂, C n₂ * F + C n₁ * F', mul_ne_zero h₁ h₂, ?_⟩
    simp only [map_add, map_mul, map_C, e₁, e₂]
    simp only [eq_intCast, Int.cast_mul, C_mul]
    ring
  | mul_X f i hf =>
    obtain ⟨n, F, h, e⟩ := hf
    exact ⟨n, F * X i, h, by rw [map_mul, map_X, e, mul_assoc]⟩

/- English proof (translation)
Set `M : Submonoid (MvPolynomial σ ℤ)` to `Submonoid.closure (Set.range fun q => (X (s q) : MvPolynomial σ ℤ))`. Set `B` to `Localization M`. Establish `hs : ∀ q, (X (s q) : MvPolynomial σ ℤ) ∈ M` using `fun q => Submonoid.subset_closure ⟨q, rfl⟩`. Set `ψ : MvPolynomial σ ℤ →+* B` to `eval₂Hom (Int.castRingHom B) (fun q => IsLocalization.mk' B (X q : MvPolynomial σ ℤ) ⟨X (s q), hs q⟩)`. Take `⟨⟨H, m⟩, hHm⟩` from `IsLocalization.surj M (ψ G₀)`.

Use `⟨H, m, fun T _ f w hu hw => ?_⟩` and prove the remaining obligations. Establish `hM : ∀ y : M, IsUnit (f y)`. Introduce and unpack `⟨y, hy⟩`. Proceed by induction on `hy using Submonoid.closure_induction with`. Consider the case `mem x hx`.

Take `⟨q, rfl⟩` from `hx`. Conclude with `hu q`. Consider the case `one => simp`. Consider the case `mul a b _ _ ha hb => simpa using ha.mul hb`. Set `L : B →+* T` to `IsLocalization.lift hM`.

Establish `hL : ∀ r, L (algebraMap _ B r) = f r` using `IsLocalization.lift_eq hM`. Establish `hcomp : L.comp ψ = eval₂Hom (Int.castRingHom T) w`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using `[ψ]`.

Introduce `q`. Simplify using `only [RingHom.comp_apply, ψ, eval₂Hom_X']`. Conclude with `(IsLocalization.lift_mk'_spec _ _ _ _).2 (hw q)`. Use `⟨hM m, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg L hHm`.

Rewrite `h` using `[map_mul, hL, hL]`. Rewrite using `[← h, ← hcomp]`. Both sides reduce to the same expression.
-/
theorem exists_homog (s : σ → σ) (G₀ : MvPolynomial σ ℤ) :
    ∃ H m : MvPolynomial σ ℤ, ∀ (T : Type) [CommRing T] (f : MvPolynomial σ ℤ →+* T) (w : σ → T),
      (∀ q, IsUnit (f (X (s q)))) → (∀ q, f (X q) = f (X (s q)) * w q) →
      IsUnit (f m) ∧ eval₂Hom (Int.castRingHom T) w G₀ * f m = f H := by
  classical
  let M : Submonoid (MvPolynomial σ ℤ) :=
    Submonoid.closure (Set.range fun q => (X (s q) : MvPolynomial σ ℤ))
  let B := Localization M
  have hs : ∀ q, (X (s q) : MvPolynomial σ ℤ) ∈ M := fun q => Submonoid.subset_closure ⟨q, rfl⟩
  let ψ : MvPolynomial σ ℤ →+* B := eval₂Hom (Int.castRingHom B)
    (fun q => IsLocalization.mk' B (X q : MvPolynomial σ ℤ) ⟨X (s q), hs q⟩)
  obtain ⟨⟨H, m⟩, hHm⟩ := IsLocalization.surj M (ψ G₀)
  refine ⟨H, m, fun T _ f w hu hw => ?_⟩
  have hM : ∀ y : M, IsUnit (f y) := by
    rintro ⟨y, hy⟩
    induction hy using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨q, rfl⟩ := hx
      exact hu q
    | one => simp
    | mul a b _ _ ha hb => simpa using ha.mul hb
  let L : B →+* T := IsLocalization.lift hM
  have hL : ∀ r, L (algebraMap _ B r) = f r := IsLocalization.lift_eq hM
  have hcomp : L.comp ψ = eval₂Hom (Int.castRingHom T) w := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ψ]
    · intro q
      simp only [RingHom.comp_apply, ψ, eval₂Hom_X']
      exact (IsLocalization.lift_mk'_spec _ _ _ _).2 (hw q)
  refine ⟨hM m, ?_⟩
  have h := congrArg L hHm
  rw [map_mul, hL, hL] at h
  rw [← h, ← hcomp]
  rfl

/- English proof (translation)
Introduce `K _ ι _ Ω _ _ y p hy G hG`. Take `⟨n, G₀, hn, hG₀⟩` from `exists_int_clear G`. Take `⟨H, m, hHm⟩` from `exists_homog (fun q : Σ k, ι k => (⟨q.1, p q.1⟩ : Σ k, ι k)) G₀`. Establish `hz : aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) G₀ = (0 : Ω)`. Establish `h1 : aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) (map (algebraMap ℤ ℚ) G₀) = (0 : Ω)`.

Establish `: (algebraMap ℤ ℚ) = Int.castRingHom ℚ` using `rfl`. Rewrite using `[this, hG₀, map_mul, hG, mul_zero]`. Rewrite `h1` using `[aeval_map_algebraMap]`. Then use the resulting hypothesis. Establish `hH : H ∈ ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y`. Set `F` to `FractionRing (MvPolynomial K Ω)`.

Set `f : MvPolynomial (Σ k, ι k) ℤ →+* F` to `(algebraMap (MvPolynomial K Ω) F).comp (ReciprocityTheory.ChartRestriction.G.Geo.mConeMap y).toRingHom`. Set `w : (Σ k, ι k) → F` to `fun q => algebraMap (MvPolynomial K Ω) F (C (y q / y ⟨q.1, p q.1⟩))`. Establish `hfX : ∀ q, f (X q) = algebraMap (MvPolynomial K Ω) F (C (y q) * X q.1)`. Introduce `q`. Simplify using `[f, ReciprocityTheory.ChartRestriction.G.Geo.mConeMap]`.

Establish `hinj : Function.Injective (algebraMap (MvPolynomial K Ω) F)` using `IsFractionRing.injective _ _`. Establish `hu : ∀ q : Σ k, ι k, IsUnit (f (X ⟨q.1, p q.1⟩))`. Introduce `q`. Rewrite using `[hfX, isUnit_iff_ne_zero]`. Introduce `h0`.

Use `hinj (h0.trans (map_zero _).symm)` as an intermediate fact. Conclude with `mul_ne_zero (C_ne_zero.mpr (hy q.1)) (X_ne_zero _) this`. Establish `hw : ∀ q, f (X q) = f (X ⟨q.1, p q.1⟩) * w q`. Introduce `q`. Rewrite using `[hfX, hfX, ← map_mul]`.

Use `congr 1`. Establish `: y q = y ⟨q.1, p q.1⟩ * (y q / y ⟨q.1, p q.1⟩)`. Clear denominators, using `[hy q.1]` for the nonvanishing conditions. Use `show C (y q) * X q.1 = C (y ⟨q.1, p q.1⟩) * X q.1 * C (y q / y ⟨q.1, p q.1⟩)`. Rewrite using `[mul_right_comm, ← C_mul, ← this]`.

Take `⟨-, h⟩` from `hHm F f w hu hw`. Establish `hev : eval₂Hom (Int.castRingHom F) w G₀ = 0`. Establish `: eval₂Hom (Int.castRingHom F) w = ((algebraMap (MvPolynomial K Ω) F).comp C).comp (aeval (R` using `ℤ) (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩)).toRingHom := by`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`.

Simplify using the standard rewrite rules. Introduce `q`. Simplify using `[w]`. Rewrite using `[this]`. Simplify using `[hz]`.

Rewrite `h` using `[hev, zero_mul]`. Conclude with `hinj (h.symm.trans (map_zero _).symm)`. Use `set P := ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y) with hP`. Set `A` to `MvPolynomial (Σ k, ι k) ℂ ⧸ chartIdeal P p`. Set `f : MvPolynomial (Σ k, ι k) ℤ →+* A` to `(Ideal.Quotient.mk (chartIdeal P p)).comp (map (Int.castRingHom ℂ))`.

Set `w : (Σ k, ι k) → A` to `fun q => Ideal.Quotient.mk _ (X q)`. Establish `hone : ∀ k, f (X ⟨k, p k⟩) = 1`. Introduce `k`. Establish `: (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ chartIdeal P p` using `Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)`. Simplify `Ideal.Quotient.eq_zero_iff_mem.mpr this` using `[f, sub_eq_zero]`.

Take `⟨hm, h⟩` from `hHm A f w (fun q => by rw [hone]; exact isUnit_one) (fun q => by rw [hone, one_mul]; simp [f, w])`. Establish `hfH : f H = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (Ideal.subset_span ⟨H, hH, rfl⟩))`. Establish `hev : eval₂Hom (Int.castRingHom A) w = f`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`.

Simplify using `[f]`. Introduce `q`. Simplify using `[f, w]`. Rewrite `h` using `[hev, hfH]`. Establish `hG₀0 : f G₀ = 0` using `hm.mul_left_eq_zero.mp h`.

Establish `hmem : map (Int.castRingHom ℂ) G₀ ∈ chartIdeal P p` using `Ideal.Quotient.eq_zero_iff_mem.mp hG₀0`. Establish `hmap : map (Int.castRingHom ℂ) G₀ = C (n : ℂ) * map (algebraMap ℚ ℂ) G`. Establish `h1 : map (Int.castRingHom ℂ) G₀ = map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) G₀)`. Rewrite using `[map_map]`. Use `congr 1`.

Rewrite using `[h1, hG₀, map_mul, map_C]`. Simplify using the standard rewrite rules. Establish `hn' : (n : ℂ) ≠ 0` using `by exact_mod_cast hn`. Rewrite `hmem` using `[hmap]`. Use `(chartIdeal P p).mul_mem_left (C (n : ℂ)⁻¹) hmem` as an intermediate fact.

Rewrite `this` using `[← mul_assoc, ← C_mul, inv_mul_cancel₀ hn', C_1, one_mul]`. Then use the resulting hypothesis.
-/
theorem map_mem_chartIdeal_of_aeval_eq_zero :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
      (y : (Σ k, ι k) → Ω) (p : (k : K) → ι k), (∀ k, y ⟨k, p k⟩ ≠ 0) →
      ∀ G : MvPolynomial (Σ k, ι k) ℚ, aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) G = 0 →
        map (algebraMap ℚ ℂ) G ∈
          chartIdeal (ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y)) p := by
  intro K _ ι _ Ω _ _ y p hy G hG
  classical
  obtain ⟨n, G₀, hn, hG₀⟩ := exists_int_clear G
  obtain ⟨H, m, hHm⟩ := exists_homog (fun q : Σ k, ι k => (⟨q.1, p q.1⟩ : Σ k, ι k)) G₀
  have hz : aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) G₀ = (0 : Ω) := by
    have h1 : aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩)
        (map (algebraMap ℤ ℚ) G₀) = (0 : Ω) := by
      have : (algebraMap ℤ ℚ) = Int.castRingHom ℚ := rfl
      rw [this, hG₀, map_mul, hG, mul_zero]
    rwa [aeval_map_algebraMap] at h1

  have hH : H ∈ ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y := by
    let F := FractionRing (MvPolynomial K Ω)
    let f : MvPolynomial (Σ k, ι k) ℤ →+* F :=
      (algebraMap (MvPolynomial K Ω) F).comp (ReciprocityTheory.ChartRestriction.G.Geo.mConeMap y).toRingHom
    let w : (Σ k, ι k) → F := fun q => algebraMap (MvPolynomial K Ω) F (C (y q / y ⟨q.1, p q.1⟩))
    have hfX : ∀ q, f (X q) = algebraMap (MvPolynomial K Ω) F (C (y q) * X q.1) := by
      intro q
      simp [f, ReciprocityTheory.ChartRestriction.G.Geo.mConeMap]
    have hinj : Function.Injective (algebraMap (MvPolynomial K Ω) F) :=
      IsFractionRing.injective _ _
    have hu : ∀ q : Σ k, ι k, IsUnit (f (X ⟨q.1, p q.1⟩)) := by
      intro q
      rw [hfX, isUnit_iff_ne_zero]
      intro h0
      have := hinj (h0.trans (map_zero _).symm)
      exact mul_ne_zero (C_ne_zero.mpr (hy q.1)) (X_ne_zero _) this
    have hw : ∀ q, f (X q) = f (X ⟨q.1, p q.1⟩) * w q := by
      intro q
      rw [hfX, hfX, ← map_mul]
      congr 1
      have : y q = y ⟨q.1, p q.1⟩ * (y q / y ⟨q.1, p q.1⟩) := by
        field_simp [hy q.1]
      show C (y q) * X q.1 = C (y ⟨q.1, p q.1⟩) * X q.1 * C (y q / y ⟨q.1, p q.1⟩)
      rw [mul_right_comm, ← C_mul, ← this]
    obtain ⟨-, h⟩ := hHm F f w hu hw
    have hev : eval₂Hom (Int.castRingHom F) w G₀ = 0 := by
      have : eval₂Hom (Int.castRingHom F) w =
          ((algebraMap (MvPolynomial K Ω) F).comp C).comp
            (aeval (R := ℤ) (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩)).toRingHom := by
        apply MvPolynomial.ringHom_ext
        · intro r
          simp
        · intro q
          simp [w]
      rw [this]
      simp [hz]
    rw [hev, zero_mul] at h
    exact hinj (h.symm.trans (map_zero _).symm)

  set P := ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y) with hP
  let A := MvPolynomial (Σ k, ι k) ℂ ⧸ chartIdeal P p
  let f : MvPolynomial (Σ k, ι k) ℤ →+* A :=
    (Ideal.Quotient.mk (chartIdeal P p)).comp (map (Int.castRingHom ℂ))
  let w : (Σ k, ι k) → A := fun q => Ideal.Quotient.mk _ (X q)
  have hone : ∀ k, f (X ⟨k, p k⟩) = 1 := by
    intro k
    have : (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ chartIdeal P p :=
      Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
    simpa [f, sub_eq_zero] using Ideal.Quotient.eq_zero_iff_mem.mpr this
  obtain ⟨hm, h⟩ := hHm A f w (fun q => by rw [hone]; exact isUnit_one)
    (fun q => by rw [hone, one_mul]; simp [f, w])
  have hfH : f H = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (Ideal.subset_span ⟨H, hH, rfl⟩))
  have hev : eval₂Hom (Int.castRingHom A) w = f := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [f]
    · intro q
      simp [f, w]
  rw [hev, hfH] at h
  have hG₀0 : f G₀ = 0 := hm.mul_left_eq_zero.mp h
  have hmem : map (Int.castRingHom ℂ) G₀ ∈ chartIdeal P p :=
    Ideal.Quotient.eq_zero_iff_mem.mp hG₀0
  have hmap : map (Int.castRingHom ℂ) G₀ = C (n : ℂ) * map (algebraMap ℚ ℂ) G := by
    have h1 : map (Int.castRingHom ℂ) G₀ = map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) G₀) := by
      rw [map_map]
      congr 1
    rw [h1, hG₀, map_mul, map_C]
    simp
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [hmap] at hmem
  have := (chartIdeal P p).mul_mem_left (C (n : ℂ)⁻¹) hmem
  rwa [← mul_assoc, ← C_mul, inv_mul_cancel₀ hn', C_1, one_mul] at this

end GlobalTheory.CompanionTheory.Ar.Cmp.KerChart
