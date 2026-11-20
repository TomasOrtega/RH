import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TranslationZeroModeLift

namespace ReciprocityTheory.ChartRestriction.G.I2

open Complex NumberField
open scoped InnerProductSpace

noncomputable section

namespace Col

variable {E : Type} [Field E] [NumberField E]

def ucL (X : PT E) (I : Submodule ℤ (Vsp X.dim)) : X.L →ₗ[ℤ] Vsp X.dim :=
  (AddMonoidHom.mk' (fun γ : X.L => uc (IR I) (γ : Vsp X.dim))
    (fun a b => by simp only [Submodule.coe_add]; exact uc_add _ _)).toIntLinearMap

/- English proof (translation)
Introduce `x hx`. Rewrite using `[LinearMap.mem_ker]`. Conclude with `uc_Ip hx`.
-/
theorem NIp_le_ker (X : PT E) (I : Submodule ℤ (Vsp X.dim)) : NIp X I ≤ LinearMap.ker (ucL X I) := by
  intro x hx
  rw [LinearMap.mem_ker]
  exact uc_Ip hx

def uQ (X : PT E) (I : Submodule ℤ (Vsp X.dim)) : Qc X I →ₗ[ℤ] Vsp X.dim :=
  (NIp X I).liftQ (ucL X I) (NIp_le_ker X I)

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem uQ_mk (γ : X.L) : uQ X I (Submodule.Quotient.mk γ) = uc (IR I) (γ : Vsp X.dim) := rfl

/- English proof (translation)
Establish `e : (Submodule.Quotient.mk (Quotient.out c) : Qc X I) = c` using `Quotient.out_eq c`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem uQ_out (c : Qc X I) : uQ X I c = uc (IR I) ((Quotient.out c : X.L) : Vsp X.dim) := by
  have e : (Submodule.Quotient.mk (Quotient.out c) : Qc X I) = c := Quotient.out_eq c
  calc uQ X I c = uQ X I (Submodule.Quotient.mk (Quotient.out c)) := by rw [e]
    _ = _ := uQ_mk _

/- English proof (translation)
Rewrite using `[uQ_out]`. Conclude with `uc_mem _ _`.
-/
theorem uQ_mem (c : Qc X I) : uQ X I c ∈ IR I := by
  rw [uQ_out]
  exact uc_mem _ _

/- English proof (translation)
Establish `hγ : ((Quotient.out c : X.L) : Vsp X.dim) ∈ Ip X I`. Rewrite using `[mem_Ip]`. Use `⟨(Quotient.out c).2, fun a ha => ?_⟩` and prove the remaining obligations. Rewrite using `[← inner_uc (IR I) _ a (Submodule.subset_span ha), ← uQ_out, h, inner_zero_left]`. Establish `e : (Submodule.Quotient.mk (Quotient.out c) : Qc X I) = c` using `Quotient.out_eq c`.

Rewrite using `[← e]`. Conclude with `(Submodule.Quotient.mk_eq_zero _).2 hγ`.
-/
theorem uQ_eq_zero {c : Qc X I} (h : uQ X I c = 0) : c = 0 := by
  have hγ : ((Quotient.out c : X.L) : Vsp X.dim) ∈ Ip X I := by
    rw [mem_Ip]
    refine ⟨(Quotient.out c).2, fun a ha => ?_⟩
    rw [← inner_uc (IR I) _ a (Submodule.subset_span ha), ← uQ_out, h, inner_zero_left]
  have e : (Submodule.Quotient.mk (Quotient.out c) : Qc X I) = c := Quotient.out_eq c
  rw [← e]
  exact (Submodule.Quotient.mk_eq_zero _).2 hγ

variable {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
include hI

/- English proof (translation)
Establish `hne : uQ X I c ≠ 0` using `fun h0 => h (uQ_eq_zero h0)`. Rewrite `hne`, the goal using `[uQ_out]`. Conclude with `hI.sep _ (Quotient.out c).2 _ (isU_uc _) hne`.
-/
theorem uQ_sep {c : Qc X I} (h : c ≠ 0) : b0 (E := E) P.q P.R0 ≤ ‖uQ X I c‖ ^ 2 := by
  have hne : uQ X I c ≠ 0 := fun h0 => h (uQ_eq_zero h0)
  rw [uQ_out] at hne ⊢
  exact hI.sep _ (Quotient.out c).2 _ (isU_uc _) hne

/- English proof (translation)
Establish `h1` using `uQ_sep hI (sub_ne_zero.2 h)`. Rewrite using `[dist_eq_norm, ← map_sub, ← Real.sqrt_sq (norm_nonneg (uQ X I (c - c')))]`. Conclude with `Real.sqrt_le_sqrt h1`.
-/
theorem uQ_dist {c c' : Qc X I} (h : c ≠ c') :
    Real.sqrt (b0 (E := E) P.q P.R0) ≤ dist (uQ X I c) (uQ X I c') := by
  have h1 := uQ_sep hI (sub_ne_zero.2 h)
  rw [dist_eq_norm, ← map_sub, ← Real.sqrt_sq (norm_nonneg (uQ X I (c - c')))]
  exact Real.sqrt_le_sqrt h1

/- English proof (translation)
Take `⟨ρ, -, hρ⟩` from `hI.rank`. Establish `hdK : dK (IR I) = 2 * (PT.f E * ρ)` using `by show Module.finrank ℝ (IR I) = 2 * (PT.f E * ρ)`. Rewrite using `[hρ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hb0 : 0 < b0 (E` using `E) P.q P.R0 := cutoff_pos P`.

Establish `haqb : 0 < a * P.q * b0 (E` using `E) P.q P.R0 := by`. Establish `: (0 : ℝ) ≤ dK (IR I)` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `haq : 0 < a * (P.q : ℝ)`. Assume the negation of the conclusion as `hneg`.

Rewrite `hneg` using `[not_lt]`. Use polynomial arithmetic with `[haqb, hb0, hneg]`. Take `⟨s, hs_def⟩ : ∃ s, s = Real.sqrt (a * P.q)` from `⟨_, rfl⟩`. Establish `hs : 0 < s` using `hs_def ▸ Real.sqrt_pos.2 haq`. Establish `hs2 : s ^ 2 = a * P.q` using `by rw [hs_def]; exact Real.sq_sqrt haq.le`.

Take `⟨δ, hδ_def⟩ : ∃ δ, δ = Real.sqrt (b0 (E` from `E) P.q P.R0) := ⟨_, rfl⟩`. Establish `hδ : 0 < δ` using `hδ_def ▸ Real.sqrt_pos.2 hb0`. Establish `hδ2 : δ ^ 2 = b0 (E` using `E) P.q P.R0 := by rw [hδ_def]; exact Real.sq_sqrt hb0.le`. Establish `h4s : 0 < 4 * s` using `by positivity`. Establish `hr0pos : 0 < 4 * s * δ` using `by positivity`.

Establish `hnorm : ∀ c : {c : Qc X I // c ∉ ({0} : Finset (Qc X I))}, δ ≤ ‖uQ X I c.1‖`. Introduce `c`. Establish `hc : c.1 ≠ 0` using `by simpa using c.2`. Rewrite using `[hδ_def, ← Real.sqrt_sq (norm_nonneg (uQ X I c.1))]`. Conclude with `Real.sqrt_le_sqrt (uQ_sep hI hc)`.

Establish `hinj : Function.Injective (fun c : {c : Qc X I // c ∉ ({0} : Finset (Qc X I))} => uQ X I c.1)`. Introduce `c c' hcc`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h0 : uQ X I (c.1 - c'.1) = 0` using `by rw [map_sub]; exact sub_eq_zero.2 hcc`. Conclude with `sub_eq_zero.1 (uQ_eq_zero h0)`.

Establish `key` using `hA {c : Qc X I // c ∉ ({0} : Finset (Qc X I))} (fun c => 4 * s * ‖uQ X I c.1‖) (PT.f E * ρ) (4 * s * δ) hr0pos (by`. Establish `e1 : (4 * s * δ) ^ 2 = 16 * (a * P.q * b0 (E` using `E) P.q P.R0) := by`. Rewrite using `[mul_pow, mul_pow, hs2, hδ2]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (dK (IR I) : ℝ) = 2 * ((PT.f E * ρ : ℕ) : ℝ)` using `by rw [hdK]; push_cast; ring`.

Rewrite using `[e1]`. Rewrite `hcond` using `[e2]`. Use the proof step `linarith)`. Use the proof step `(fun c => mul_le_mul_of_nonneg_left (hnorm c) h4s.le)`. Use the proof step `(by`.

Introduce `R hR S hS`. Establish `hcard : (S.image fun c => uQ X I c.1).card = S.card` using `Finset.card_image_of_injective _ hinj`. Establish `hpk` using `pack_K hP (IR I) (S.image fun c => uQ X I c.1) (by`. Introduce `u hu`. Take `⟨c, -, rfl⟩` from `Finset.mem_image.1 hu`.

Conclude with `uQ_mem c.1) δ (R / (4 * s)) hδ`. Use the proof step `(by`. Rewrite using `[le_div_iff₀ h4s]`. Combine the equalities or inequalities in the displayed calculation. Use the proof step `(by`.

Introduce `u hu`. Take `⟨c, hc, rfl⟩` from `Finset.mem_image.1 hu`. Rewrite using `[le_div_iff₀ h4s]`. Combine the equalities or inequalities in the displayed calculation. Use the proof step `(by`.

Introduce `u hu v hv huv`. Take `⟨c, -, rfl⟩` from `Finset.mem_image.1 hu`. Take `⟨c', -, rfl⟩` from `Finset.mem_image.1 hv`. Establish `hcc : c.1 ≠ c'.1` using `fun e => huv (by simp only [e])`. Rewrite using `[hδ_def]`.

Conclude with `uQ_dist hI hcc)`. Establish `e3 : 3 * (R / (4 * s)) / δ = 3 * R / (4 * s * δ)`. Clear the denominators using the available nonvanishing facts. Rewrite `hpk` using `[e3, hdK, hcard]`. Conclude with `hpk)`.

Establish `hfun : (fun c : {c : Qc X I // c ∉ ({0} : Finset (Qc X I))} => Real.exp (-(4 * s * ‖uQ X I c.1‖) ^ 2 / 16)) = fun c => Real.exp (-(a * P.q) * ‖uQ X I c.1‖ ^ 2)`. Use function extensionality and compare the values at `c`. Use `congr 1`. Rewrite using `[mul_pow, mul_pow, hs2]`. Expand and normalize the polynomial expressions, which then agree.

Establish `e9 : (9 : ℝ) ^ (PT.f E * ρ) = 3 ^ (dK (IR I))` using `by rw [hdK, pow_mul (3 : ℝ) 2 (PT.f E * ρ)]; norm_num`. Establish `er : -(4 * s * δ) ^ 2 / 16 = -(a * P.q * b0 (E` using `E) P.q P.R0) := by`. Rewrite using `[mul_pow, mul_pow, hs2, hδ2]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `key` using `[hfun, e9, er]`.

Conclude with `key`.
-/
theorem tailQ (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound) (a : ℝ) (ha : 0 < a)
    (hcond : (dK (IR I) : ℝ) + 1 ≤ a * P.q * b0 (E := E) P.q P.R0) :
    Summable (fun c : {c : Qc X I // c ∉ ({0} : Finset (Qc X I))} =>
        Real.exp (-(a * P.q) * ‖uQ X I c‖ ^ 2)) ∧
      ∑' c : {c : Qc X I // c ∉ ({0} : Finset (Qc X I))}, Real.exp (-(a * P.q) * ‖uQ X I c‖ ^ 2) ≤
        2 * 3 ^ (dK (IR I)) * Real.exp (-(a * P.q * b0 (E := E) P.q P.R0)) := by
  classical
  obtain ⟨ρ, -, hρ⟩ := hI.rank
  have hdK : dK (IR I) = 2 * (PT.f E * ρ) := by
    show Module.finrank ℝ (IR I) = 2 * (PT.f E * ρ)
    rw [hρ]; ring
  have hb0 : 0 < b0 (E := E) P.q P.R0 := cutoff_pos P
  have haqb : 0 < a * P.q * b0 (E := E) P.q P.R0 := by
    have : (0 : ℝ) ≤ dK (IR I) := Nat.cast_nonneg _
    linarith
  have haq : 0 < a * (P.q : ℝ) := by
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith [haqb, hb0, hneg]
  obtain ⟨s, hs_def⟩ : ∃ s, s = Real.sqrt (a * P.q) := ⟨_, rfl⟩
  have hs : 0 < s := hs_def ▸ Real.sqrt_pos.2 haq
  have hs2 : s ^ 2 = a * P.q := by rw [hs_def]; exact Real.sq_sqrt haq.le
  obtain ⟨δ, hδ_def⟩ : ∃ δ, δ = Real.sqrt (b0 (E := E) P.q P.R0) := ⟨_, rfl⟩
  have hδ : 0 < δ := hδ_def ▸ Real.sqrt_pos.2 hb0
  have hδ2 : δ ^ 2 = b0 (E := E) P.q P.R0 := by rw [hδ_def]; exact Real.sq_sqrt hb0.le
  have h4s : 0 < 4 * s := by positivity
  have hr0pos : 0 < 4 * s * δ := by positivity
  have hnorm : ∀ c : {c : Qc X I // c ∉ ({0} : Finset (Qc X I))}, δ ≤ ‖uQ X I c.1‖ := by
    intro c
    have hc : c.1 ≠ 0 := by simpa using c.2
    rw [hδ_def, ← Real.sqrt_sq (norm_nonneg (uQ X I c.1))]
    exact Real.sqrt_le_sqrt (uQ_sep hI hc)
  have hinj : Function.Injective
      (fun c : {c : Qc X I // c ∉ ({0} : Finset (Qc X I))} => uQ X I c.1) := by
    intro c c' hcc
    apply Subtype.ext
    have h0 : uQ X I (c.1 - c'.1) = 0 := by rw [map_sub]; exact sub_eq_zero.2 hcc
    exact sub_eq_zero.1 (uQ_eq_zero h0)
  have key := hA {c : Qc X I // c ∉ ({0} : Finset (Qc X I))} (fun c => 4 * s * ‖uQ X I c.1‖)
    (PT.f E * ρ) (4 * s * δ) hr0pos
    (by
      have e1 : (4 * s * δ) ^ 2 = 16 * (a * P.q * b0 (E := E) P.q P.R0) := by
        rw [mul_pow, mul_pow, hs2, hδ2]; ring
      have e2 : (dK (IR I) : ℝ) = 2 * ((PT.f E * ρ : ℕ) : ℝ) := by rw [hdK]; push_cast; ring
      rw [e1]; rw [e2] at hcond; linarith)
    (fun c => mul_le_mul_of_nonneg_left (hnorm c) h4s.le)
    (by
      intro R hR S hS
      have hcard : (S.image fun c => uQ X I c.1).card = S.card := Finset.card_image_of_injective _ hinj
      have hpk := pack_K hP (IR I) (S.image fun c => uQ X I c.1)
        (by
          intro u hu
          obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hu
          exact uQ_mem c.1) δ (R / (4 * s)) hδ
        (by
          rw [le_div_iff₀ h4s]
          calc δ * (4 * s) = 4 * s * δ := by ring
            _ ≤ R := hR)
        (by
          intro u hu
          obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hu
          rw [le_div_iff₀ h4s]
          calc ‖uQ X I c.1‖ * (4 * s) = 4 * s * ‖uQ X I c.1‖ := by ring
            _ ≤ R := hS c hc)
        (by
          intro u hu v hv huv
          obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hu
          obtain ⟨c', -, rfl⟩ := Finset.mem_image.1 hv
          have hcc : c.1 ≠ c'.1 := fun e => huv (by simp only [e])
          rw [hδ_def]
          exact uQ_dist hI hcc)
      have e3 : 3 * (R / (4 * s)) / δ = 3 * R / (4 * s * δ) := by
        field_simp
      rw [e3, hdK, hcard] at hpk
      exact hpk)
  have hfun : (fun c : {c : Qc X I // c ∉ ({0} : Finset (Qc X I))} =>
      Real.exp (-(4 * s * ‖uQ X I c.1‖) ^ 2 / 16)) =
      fun c => Real.exp (-(a * P.q) * ‖uQ X I c.1‖ ^ 2) := by
    funext c
    congr 1
    rw [mul_pow, mul_pow, hs2]; ring
  have e9 : (9 : ℝ) ^ (PT.f E * ρ) = 3 ^ (dK (IR I)) := by rw [hdK, pow_mul (3 : ℝ) 2 (PT.f E * ρ)]; norm_num
  have er : -(4 * s * δ) ^ 2 / 16 = -(a * P.q * b0 (E := E) P.q P.R0) := by
    rw [mul_pow, mul_pow, hs2, hδ2]; ring
  rw [hfun, e9, er] at key
  exact key

end Col

end

end ReciprocityTheory.ChartRestriction.G.I2
