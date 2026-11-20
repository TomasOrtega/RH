import Mathlib

namespace GlobalTheory

open Matrix

/- English proof (translation)
Take `⟨n, hn⟩` from `h`. Establish `h0` using `congrFun (congrFun hn ⟨0, hd⟩) ⟨0, hd⟩`. Rewrite `h0` using `[smul_pow, one_pow]`. Simplify using `at h0`. Conclude with `h0.1`.
-/
theorem scalar_eq_zero_of_isNilpotent_smul_one {d : ℕ} (hd : 0 < d) {c : ℂ}
    (h : IsNilpotent (c • (1 : Matrix (Fin d) (Fin d) ℂ))) : c = 0 := by
  obtain ⟨n, hn⟩ := h
  have h0 := congrFun (congrFun hn ⟨0, hd⟩) ⟨0, hd⟩
  rw [smul_pow, one_pow] at h0
  simp at h0
  exact h0.1

/- English proof (translation)
Introduce `G _ _ H d ρ χ hd hnil hH hcont`. Establish `key : ∀ c : ℂ, IsNilpotent (c • (1 : Matrix (Fin d) (Fin d) ℂ)) → c = 0` using `fun c h => scalar_eq_zero_of_isNilpotent_smul_one hd h`. Establish `htr : ∀ s, χ s = trace (ρ s) / (d : ℂ)`. Introduce `s`. Establish `h1 : IsNilpotent (trace (ρ s - χ s • (1 : Matrix (Fin d) (Fin d) ℂ)))` using `Matrix.isNilpotent_trace_of_isNilpotent (hnil s)`.

Establish `h2` using `h1.eq_zero`. Rewrite `h2` using `[trace_sub, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul]`. Establish `hd' : (d : ℂ) ≠ 0` using `by exact_mod_cast hd.ne'`. Clear the denominators using the available nonvanishing facts. Take the linear combination `-h2`.

Establish `hχ1 : χ 1 = 1`. Establish `h` using `hnil 1`. Rewrite `h` using `[map_one]`. Establish `: (1 : Matrix (Fin d) (Fin d) ℂ) - χ 1 • 1 = (1 - χ 1) • 1`. Rewrite using `[sub_smul, one_smul]`.

Rewrite `h` using `[this]`. Use `key _ h` as an intermediate fact. Take the linear combination `-this`. Establish `hmul : ∀ s t, χ (s * t) = χ s * χ t`. Introduce `s t`.

Establish `hc : Commute (ρ s) (ρ t)` using `by show ρ s * ρ t = ρ t * ρ s`. Rewrite using `[← map_mul, ← map_mul, mul_comm]`. Use `set A := ρ s - χ s • (1 : Matrix (Fin d) (Fin d) ℂ)`. Use `set B := ρ t - χ t • (1 : Matrix (Fin d) (Fin d) ℂ)`. Establish `hAt : Commute A (ρ t)`.

Simplify using `only [A]`. Conclude with `(hc.sub_left ((Commute.one_left _).smul_left _))`. Establish `hAB : Commute (A * ρ t) (χ s • B)`. Simplify using `only [B]`. Use `Commute.smul_right ?_ _` and prove the remaining obligations.

Use `Commute.sub_right ?_ ((Commute.one_right _).smul_right _)` and prove the remaining obligations. Conclude with `Commute.mul_left hAt (Commute.refl _)`. Establish `hN1 : IsNilpotent (A * ρ t + χ s • B)`. Use `Commute.isNilpotent_add hAB ?_ ?_` and prove the remaining obligations. Conclude with `Commute.isNilpotent_mul_right hAt (hnil s)`.

Conclude with `(hnil t).smul _`. Establish `heq1 : A * ρ t + χ s • B = ρ (s * t) - (χ s * χ t) • 1`. Simplify using `only [A, B, map_mul, sub_mul, smul_mul_assoc, one_mul, smul_sub, mul_smul]`. Normalize the expressions using the abelian group laws. Rewrite `hN1` using `[heq1]`.

Establish `hN2` using `hnil (s * t)`. Establish `hcomm : Commute (ρ (s * t) - (χ s * χ t) • (1 : Matrix (Fin d) (Fin d) ℂ)) (ρ (s * t) - χ (s * t) • 1)`. Use `Commute.sub_left ?_ ((Commute.one_left _).smul_left _)` and prove the remaining obligations. Conclude with `Commute.sub_right (Commute.refl _) ((Commute.one_right _).smul_right _)`. Establish `hN3` using `Commute.isNilpotent_sub hcomm hN1 hN2`.

Establish `: (ρ (s * t) - (χ s * χ t) • (1 : Matrix (Fin d) (Fin d) ℂ)) - (ρ (s * t) - χ (s * t) • 1) = (χ (s * t) - χ s * χ t) • 1`. Rewrite using `[sub_smul]`. Normalize the expressions using the abelian group laws. Rewrite `hN3` using `[this]`. Use `key _ hN3` as an intermediate fact.

Take the linear combination `this`. Set `m : G →* ℂ` to `{ toFun := χ, map_one' := hχ1, map_mul' := hmul }`. Establish `hne : ∀ s, χ s ≠ 0`. Introduce `s h`. Use `hmul s s⁻¹` as an intermediate fact.

Rewrite `this` using `[mul_inv_cancel, hχ1, h, zero_mul]`. Conclude with `one_ne_zero this`. Set `lam : G →* ℂˣ` to `m.toHomUnits`. Use `⟨lam, fun s => rfl, ?_, ?_⟩` and prove the remaining obligations. Use `show Continuous χ`.

Establish `: χ = fun s => trace (ρ s) / (d : ℂ)` using `funext htr`. Rewrite using `[this]`. Use `Continuous.div_const ?_ _` and prove the remaining obligations. Simplify using `only [Matrix.trace, Matrix.diag]`. Conclude with `continuous_finset_sum _ (fun i _ => hcont i i)`.

Introduce `γ hγ`. Apply `Units.ext` to reduce the goal to its premises. Use `show χ γ = 1`. Establish `h` using `hnil γ`. Rewrite `h` using `[hH γ hγ]`.

Establish `: (1 : Matrix (Fin d) (Fin d) ℂ) - χ γ • 1 = (1 - χ γ) • 1`. Rewrite using `[sub_smul, one_smul]`. Rewrite `h` using `[this]`. Use `key _ h` as an intermediate fact. Take the linear combination `-this`.
-/
theorem scalar_part_character :
    ∀ (G : Type) [CommGroup G] [TopologicalSpace G] (H : Set G) (d : ℕ)
      (ρ : G →* Matrix (Fin d) (Fin d) ℂ) (χ : G → ℂ), 0 < d →
      (∀ s, IsNilpotent (ρ s - χ s • (1 : Matrix (Fin d) (Fin d) ℂ))) →
      (∀ γ ∈ H, ρ γ = 1) → (∀ i j, Continuous fun s => ρ s i j) →
      ∃ lam : G →* ℂˣ, (∀ s, ((lam s : ℂˣ) : ℂ) = χ s) ∧
        Continuous (fun s => ((lam s : ℂˣ) : ℂ)) ∧ ∀ γ ∈ H, lam γ = 1 := by
  intro G _ _ H d ρ χ hd hnil hH hcont

  have key : ∀ c : ℂ, IsNilpotent (c • (1 : Matrix (Fin d) (Fin d) ℂ)) → c = 0 :=
    fun c h => scalar_eq_zero_of_isNilpotent_smul_one hd h

  have htr : ∀ s, χ s = trace (ρ s) / (d : ℂ) := by
    intro s
    have h1 : IsNilpotent (trace (ρ s - χ s • (1 : Matrix (Fin d) (Fin d) ℂ))) :=
      Matrix.isNilpotent_trace_of_isNilpotent (hnil s)
    have h2 := h1.eq_zero
    rw [trace_sub, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul] at h2
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp
    linear_combination -h2
  have hχ1 : χ 1 = 1 := by
    have h := hnil 1
    rw [map_one] at h
    have : (1 : Matrix (Fin d) (Fin d) ℂ) - χ 1 • 1 = (1 - χ 1) • 1 := by
      rw [sub_smul, one_smul]
    rw [this] at h
    have := key _ h
    linear_combination -this
  have hmul : ∀ s t, χ (s * t) = χ s * χ t := by
    intro s t
    have hc : Commute (ρ s) (ρ t) := by
      show ρ s * ρ t = ρ t * ρ s
      rw [← map_mul, ← map_mul, mul_comm]
    set A := ρ s - χ s • (1 : Matrix (Fin d) (Fin d) ℂ)
    set B := ρ t - χ t • (1 : Matrix (Fin d) (Fin d) ℂ)
    have hAt : Commute A (ρ t) := by
      simp only [A]
      exact (hc.sub_left ((Commute.one_left _).smul_left _))
    have hAB : Commute (A * ρ t) (χ s • B) := by
      simp only [B]
      refine Commute.smul_right ?_ _
      refine Commute.sub_right ?_ ((Commute.one_right _).smul_right _)
      exact Commute.mul_left hAt (Commute.refl _)
    have hN1 : IsNilpotent (A * ρ t + χ s • B) := by
      refine Commute.isNilpotent_add hAB ?_ ?_
      · exact Commute.isNilpotent_mul_right hAt (hnil s)
      · exact (hnil t).smul _
    have heq1 : A * ρ t + χ s • B = ρ (s * t) - (χ s * χ t) • 1 := by
      simp only [A, B, map_mul, sub_mul, smul_mul_assoc, one_mul, smul_sub, mul_smul]
      abel
    rw [heq1] at hN1
    have hN2 := hnil (s * t)
    have hcomm : Commute (ρ (s * t) - (χ s * χ t) • (1 : Matrix (Fin d) (Fin d) ℂ))
        (ρ (s * t) - χ (s * t) • 1) := by
      refine Commute.sub_left ?_ ((Commute.one_left _).smul_left _)
      exact Commute.sub_right (Commute.refl _) ((Commute.one_right _).smul_right _)
    have hN3 := Commute.isNilpotent_sub hcomm hN1 hN2
    have : (ρ (s * t) - (χ s * χ t) • (1 : Matrix (Fin d) (Fin d) ℂ)) - (ρ (s * t) - χ (s * t) • 1)
        = (χ (s * t) - χ s * χ t) • 1 := by
      rw [sub_smul]; abel
    rw [this] at hN3
    have := key _ hN3
    linear_combination this
  let m : G →* ℂ := { toFun := χ, map_one' := hχ1, map_mul' := hmul }
  have hne : ∀ s, χ s ≠ 0 := by
    intro s h
    have := hmul s s⁻¹
    rw [mul_inv_cancel, hχ1, h, zero_mul] at this
    exact one_ne_zero this
  let lam : G →* ℂˣ := m.toHomUnits
  refine ⟨lam, fun s => rfl, ?_, ?_⟩
  · show Continuous χ
    have : χ = fun s => trace (ρ s) / (d : ℂ) := funext htr
    rw [this]
    refine Continuous.div_const ?_ _
    simp only [Matrix.trace, Matrix.diag]
    exact continuous_finset_sum _ (fun i _ => hcont i i)
  · intro γ hγ
    apply Units.ext
    show χ γ = 1
    have h := hnil γ
    rw [hH γ hγ] at h
    have : (1 : Matrix (Fin d) (Fin d) ℂ) - χ γ • 1 = (1 - χ γ) • 1 := by
      rw [sub_smul, one_smul]
    rw [this] at h
    have := key _ h
    linear_combination -this

end GlobalTheory
