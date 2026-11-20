import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

/- English proof (translation)
Establish `e : ∀ z : HahnSeries ℚ Ω, HahnSeries.map z ((s : Ω →+* Ω) : Ω →ₙ+* Ω) = HahnSeries.map z (s : Ω →+* Ω)`. Introduce `z`. Use extensionality with `r`. Simplify using `[HahnSeries.map_coeff]`. Both sides reduce to the same expression.

Rewrite using `[← e, ← e, ← e]`. Conclude with `HahnSeries.map_mul _`.
-/
private theorem hahnSeries_map_mul {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : Ω ≃ₐ[ℚ] Ω) (x y : HahnSeries ℚ Ω) :
    HahnSeries.map (x * y) (s : Ω →+* Ω) = HahnSeries.map x (s : Ω →+* Ω) * HahnSeries.map y (s : Ω →+* Ω) := by
  have e : ∀ z : HahnSeries ℚ Ω, HahnSeries.map z ((s : Ω →+* Ω) : Ω →ₙ+* Ω) = HahnSeries.map z (s : Ω →+* Ω) := by
    intro z
    ext r
    simp [HahnSeries.map_coeff]
    rfl
  rw [← e, ← e, ← e]
  exact HahnSeries.map_mul _

/- English proof (translation)
Use extensionality with `r`. Use `show algebraMap ℚ Ω (q * r) * (HahnSeries.map x (s : Ω →+* Ω)).coeff r = (s : Ω →+* Ω) (algebraMap ℚ Ω (q * r) * x.coeff r)`. Rewrite using `[HahnSeries.map_coeff, map_mul (s : Ω →+* Ω), show (s : Ω →+* Ω) (algebraMap ℚ Ω (q * r)) = algebraMap ℚ Ω (q * r) from s.commutes _]`.
-/
private theorem theta_hahnSeries_map_comm {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : Ω ≃ₐ[ℚ] Ω) (q : ℚ) (x : HahnSeries ℚ Ω) :
    theta q (HahnSeries.map x (s : Ω →+* Ω)) = HahnSeries.map (theta q x) (s : Ω →+* Ω) := by
  ext r
  show algebraMap ℚ Ω (q * r) * (HahnSeries.map x (s : Ω →+* Ω)).coeff r = (s : Ω →+* Ω) (algebraMap ℚ Ω (q * r) * x.coeff r)
  rw [HahnSeries.map_coeff, map_mul (s : Ω →+* Ω),
    show (s : Ω →+* Ω) (algebraMap ℚ Ω (q * r)) = algebraMap ℚ Ω (q * r) from s.commutes _]

/- English proof (translation)
Use extensionality with `r`. Simplify using `[HahnSeries.map_coeff]`.
-/
private theorem hahnSeries_map_sub {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : Ω ≃ₐ[ℚ] Ω) (x y : HahnSeries ℚ Ω) :
    HahnSeries.map (x - y) (s : Ω →+* Ω) = HahnSeries.map x (s : Ω →+* Ω) - HahnSeries.map y (s : Ω →+* Ω) := by
  ext r
  simp [HahnSeries.map_coeff]

/- English proof (translation)
Take `⟨h1, r, hr0, hr⟩` from `hx`. Use `⟨fun t => ?_, r, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[HahnSeries.map_coeff]`. Conclude with `(hA _).1 (h1 t)`. Rewrite using `[HahnSeries.map_coeff]`.

Conclude with `(map_ne_zero _).2 hr0`. Rewrite using `[HahnSeries.map_coeff, ← map_inv₀]`. Conclude with `(hA _).1 hr`.
-/
private theorem prim_hahnSeries_map_of_prim_comap {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A A' : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω)
    (hA : ∀ x, x ∈ A' ↔ s x ∈ A) (x : HahnSeries ℚ Ω) (hx : Prim A' x) :
    Prim A (HahnSeries.map x (s : Ω →+* Ω)) := by
  obtain ⟨h1, r, hr0, hr⟩ := hx
  refine ⟨fun t => ?_, r, ?_, ?_⟩
  · rw [HahnSeries.map_coeff]
    exact (hA _).1 (h1 t)
  · rw [HahnSeries.map_coeff]
    exact (map_ne_zero _).2 hr0
  · rw [HahnSeries.map_coeff, ← map_inv₀]
    exact (hA _).1 hr

set_option maxHeartbeats 800000 in
/- English proof (translation)
Introduce `Ω _ _ _ _ ε X l _ A A' s hA n q f φ h`. Take `⟨hφ, a, b, κ, hκ, hfb, ha, hb, hc⟩` from `h`. Establish `hM : ∀ g : X.K, X.exp (X.gal s g) = HahnSeries.map (X.exp g) (s : Ω →+* Ω)`. Introduce `g`. Use extensionality with `r`.

Rewrite using `[HahnSeries.map_coeff, X.gal_exp]`. Both sides reduce to the same expression. Establish `hsm : ∀ (c : Ω) (y : HahnSeries ℚ Ω) (r : ℚ), (algebraMap Ω (HahnSeries ℚ Ω) c * y).coeff r = c * y.coeff r`. Introduce `c y r`. Rewrite using `[HahnSeries.algebraMap_apply']`.

Simplify using `[HahnSeries.C_mul_eq_smul]`. Establish `hsκ : s κ ≠ 0` using `(map_ne_zero _).2 hκ`. Establish `hc0 : algebraMap Ω X.K (s κ) ≠ 0` using `(map_ne_zero _).2 hsκ`. Establish `hexpa : X.exp ((algebraMap Ω X.K (s κ))⁻¹ * X.gal s (algebraMap Ω X.K κ * a)) = HahnSeries.map (X.exp a) (s : Ω →+* Ω)`. Rewrite using `[← map_inv₀, map_mul, AlgHom.commutes, hM, map_mul, AlgHom.commutes]`.

Use extensionality with `r`. Rewrite using `[hsm, HahnSeries.map_coeff, HahnSeries.map_coeff, hsm, map_mul, ← mul_assoc, show (s κ)⁻¹ * (s : Ω →+* Ω) κ = 1 from inv_mul_cancel₀ hsκ, one_mul]`. Use `⟨fun r => ?_, (algebraMap Ω X.K (s κ))⁻¹ * X.gal s (algebraMap Ω X.K κ * a), X.gal s b, s κ, hsκ, ?_, ?_, ?_, fun r => ?_⟩` and prove the remaining obligations. Rewrite using `[HahnSeries.map_coeff]`. Conclude with `(hA _).1 (hφ r)`.

Rewrite using `[← map_mul, hfb, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]`. Rewrite using `[hexpa]`. Conclude with `prim_hahnSeries_map_of_prim_comap A A' s hA _ ha`. Rewrite using `[hM]`. Conclude with `prim_hahnSeries_map_of_prim_comap A A' s hA _ hb`.

Rewrite using `[hexpa, hM, theta_hahnSeries_map_comm, theta_hahnSeries_map_comm, ← hahnSeries_map_mul, ← hahnSeries_map_mul, ← hahnSeries_map_mul, ← hahnSeries_map_mul, ← hahnSeries_map_sub, HahnSeries.map_coeff, HahnSeries.map_coeff]`. Take `⟨z, hz, e⟩` from `hc r`. Use `⟨s z, (hA z).1 hz, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_sub, e, map_mul]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.Kd.L.dlgal :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (A A' : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), (∀ x, x ∈ A' ↔ s x ∈ A) → ∀ (n : ℕ) (a : ℚ) (f : X.K) (φ : HahnSeries ℚ Ω), IsDl X A' l n a f φ → IsDl X A l n a (X.gal s f) (HahnSeries.map φ (s : Ω →+* Ω)) := by
  intro Ω _ _ _ _ ε X l _ A A' s hA n q f φ h
  obtain ⟨hφ, a, b, κ, hκ, hfb, ha, hb, hc⟩ := h
  have hM : ∀ g : X.K, X.exp (X.gal s g) = HahnSeries.map (X.exp g) (s : Ω →+* Ω) := by
    intro g
    ext r
    rw [HahnSeries.map_coeff, X.gal_exp]
    rfl
  have hsm : ∀ (c : Ω) (y : HahnSeries ℚ Ω) (r : ℚ),
      (algebraMap Ω (HahnSeries ℚ Ω) c * y).coeff r = c * y.coeff r := by
    intro c y r
    rw [HahnSeries.algebraMap_apply']
    simp [HahnSeries.C_mul_eq_smul]
  have hsκ : s κ ≠ 0 := (map_ne_zero _).2 hκ
  have hc0 : algebraMap Ω X.K (s κ) ≠ 0 := (map_ne_zero _).2 hsκ
  have hexpa : X.exp ((algebraMap Ω X.K (s κ))⁻¹ * X.gal s (algebraMap Ω X.K κ * a)) =
      HahnSeries.map (X.exp a) (s : Ω →+* Ω) := by
    rw [← map_inv₀, map_mul, AlgHom.commutes, hM, map_mul, AlgHom.commutes]
    ext r
    rw [hsm, HahnSeries.map_coeff, HahnSeries.map_coeff, hsm, map_mul, ← mul_assoc,
      show (s κ)⁻¹ * (s : Ω →+* Ω) κ = 1 from inv_mul_cancel₀ hsκ, one_mul]
  refine ⟨fun r => ?_, (algebraMap Ω X.K (s κ))⁻¹ * X.gal s (algebraMap Ω X.K κ * a), X.gal s b, s κ, hsκ,
    ?_, ?_, ?_, fun r => ?_⟩
  · rw [HahnSeries.map_coeff]
    exact (hA _).1 (hφ r)
  · rw [← map_mul, hfb, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  · rw [hexpa]
    exact prim_hahnSeries_map_of_prim_comap A A' s hA _ ha
  · rw [hM]
    exact prim_hahnSeries_map_of_prim_comap A A' s hA _ hb
  · rw [hexpa, hM, theta_hahnSeries_map_comm, theta_hahnSeries_map_comm, ← hahnSeries_map_mul, ← hahnSeries_map_mul, ← hahnSeries_map_mul, ← hahnSeries_map_mul, ← hahnSeries_map_sub,
      HahnSeries.map_coeff, HahnSeries.map_coeff]
    obtain ⟨z, hz, e⟩ := hc r
    refine ⟨s z, (hA z).1 hz, ?_⟩
    rw [← map_sub, e, map_mul]
    simp
