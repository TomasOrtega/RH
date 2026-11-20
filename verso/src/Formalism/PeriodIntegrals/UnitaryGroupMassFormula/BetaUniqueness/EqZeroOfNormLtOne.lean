import Mathlib

noncomputable section

open NumberField

namespace PI.UnitaryGroupMassFormula.BetaLUniq.EigA

/- English proof (translation)
Establish `hPt : P ≠ ⊤` using `hP.ne_top`. Establish `hlt : P ^ 2 < P ^ 1` using `Ideal.pow_right_strictAnti P hP0 hPt (show 1 < 2 by norm_num)`. Rewrite `hlt` using `[pow_one]`. Take `⟨π, hπP, hπ2⟩` from `SetLike.exists_of_lt hlt`. Establish `hπ0 : π ≠ 0` using `by rintro rfl; exact hπ2 (Ideal.zero_mem _)`.

Establish `hdvd : P ∣ Ideal.span {π}` using `Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem P).mpr hπP)`. Take `⟨Q, hQ⟩` from `hdvd`. Establish `hQP : ¬ Q ≤ P`. Introduce `hle`. Apply `hπ2` to reduce the goal to its premises.

Establish `: Ideal.span {π} ≤ P ^ 2` using `by rw [hQ, pow_two]; exact Ideal.mul_mono_right hle`. Conclude with `this (Ideal.mem_span_singleton_self π)`. Take `⟨b, hbQ, hbP⟩` from `SetLike.not_le_iff_exists.mp hQP`. Use `⟨π, hπP, hπ0, b, hbP, fun p hp => ?_⟩` and prove the remaining obligations. Rewrite using `[hQ, mul_comm b]`.

Conclude with `Ideal.mul_mem_mul hp hbQ`.
-/
theorem exists_pi_b {R : Type*} [CommRing R] [IsDedekindDomain R] (P : Ideal R) [hP : P.IsPrime]
    (hP0 : P ≠ ⊥) : ∃ π ∈ P, π ≠ 0 ∧ ∃ b ∉ P, ∀ p ∈ P, b * p ∈ Ideal.span {π} := by
  have hPt : P ≠ ⊤ := hP.ne_top
  have hlt : P ^ 2 < P ^ 1 := Ideal.pow_right_strictAnti P hP0 hPt (show 1 < 2 by norm_num)
  rw [pow_one] at hlt
  obtain ⟨π, hπP, hπ2⟩ := SetLike.exists_of_lt hlt
  have hπ0 : π ≠ 0 := by rintro rfl; exact hπ2 (Ideal.zero_mem _)
  have hdvd : P ∣ Ideal.span {π} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem P).mpr hπP)
  obtain ⟨Q, hQ⟩ := hdvd
  have hQP : ¬ Q ≤ P := by
    intro hle
    apply hπ2
    have : Ideal.span {π} ≤ P ^ 2 := by rw [hQ, pow_two]; exact Ideal.mul_mono_right hle
    exact this (Ideal.mem_span_singleton_self π)
  obtain ⟨b, hbQ, hbP⟩ := SetLike.not_le_iff_exists.mp hQP
  refine ⟨π, hπP, hπ0, b, hbP, fun p hp => ?_⟩
  rw [hQ, mul_comm b]
  exact Ideal.mul_mem_mul hp hbQ

variable {E : Type} [Field E] [NumberField E]

def InO (x : E) : Prop := ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = x

/- English proof (translation)
Set `J : Ideal (𝓞 E)` to `Submodule.comap (LinearMap.toSpanSingleton (𝓞 E) E ν) (LinearMap.range (Algebra.linearMap (𝓞 E) E))`. Establish `hmem : ∀ s, s ∈ J ↔ InO (algebraMap (𝓞 E) E s * ν)`. Introduce `s`. Simplify using `only [J, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, LinearMap.mem_range, Algebra.linearMap_apply, Algebra.smul_def, InO]`. Establish `hJ : J = ⊤`.

Assume the negation of the conclusion as `hne`. Take `⟨M, hM, hJM⟩` from `Ideal.exists_le_maximal J hne`. Take `⟨s, hsM, hs⟩` from `h M hM`. Conclude with `hsM (hJM ((hmem s).mpr hs))`. Establish `h1` using `(hmem 1).mp (hJ ▸ Submodule.mem_top)`.

Rewrite `h1` using `[map_one, one_mul]`. Then use the resulting hypothesis.
-/
theorem mem_O_of_local (ν : E)
    (h : ∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ s : 𝓞 E, s ∉ P ∧ InO (algebraMap (𝓞 E) E s * ν)) :
    InO ν := by
  let J : Ideal (𝓞 E) := Submodule.comap (LinearMap.toSpanSingleton (𝓞 E) E ν)
    (LinearMap.range (Algebra.linearMap (𝓞 E) E))
  have hmem : ∀ s, s ∈ J ↔ InO (algebraMap (𝓞 E) E s * ν) := by
    intro s
    simp only [J, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, LinearMap.mem_range,
      Algebra.linearMap_apply, Algebra.smul_def, InO]
  have hJ : J = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hne
    obtain ⟨s, hsM, hs⟩ := h M hM
    exact hsM (hJM ((hmem s).mpr hs))
  have h1 := (hmem 1).mp (hJ ▸ Submodule.mem_top)
  rwa [map_one, one_mul] at h1

/- English proof (translation)
Establish `hint : IsIntegral (𝓞 E) x` using `isIntegral_of_smul_mem_submodule I hI hfg x (fun c hc => by simpa [smul_eq_mul] using hx c hc)`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hint`. Conclude with `⟨y, hy⟩`.
-/
theorem mem_O_of_stable (I : Submodule (𝓞 E) E) (hI : I ≠ ⊥) (hfg : I.FG) (x : E)
    (hx : ∀ c ∈ I, x * c ∈ I) : InO x := by
  have hint : IsIntegral (𝓞 E) x :=
    isIntegral_of_smul_mem_submodule I hI hfg x (fun c hc => by simpa [smul_eq_mul] using hx c hc)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact ⟨y, hy⟩

/- English proof (translation)
Take `⟨S, hS⟩` from `hfg`. Establish `hS' : ∀ c ∈ S, ∃ s : 𝓞 E, s ∉ P ∧ algebraMap (𝓞 E) E s * x * c ∈ I` using `fun c hc => hx c (hS ▸ Submodule.subset_span hc)`. Use `choose! f hfP hfI using hS'`. Use `⟨∏ c ∈ S, f c, ?_, ?_⟩` and prove the remaining obligations. Introduce `hmem`.

Take `⟨c, hc, hcP⟩` from `Ideal.IsPrime.prod_mem_iff.mp hmem`. Conclude with `hfP c hc hcP`. Introduce `c hc`. Rewrite `hc` using `[← hS]`. Proceed by induction on `hc using Submodule.span_induction with`.

Consider the case `mem c hc`. Take `⟨r, hr⟩` from `Finset.dvd_prod_of_mem f hc`. Establish `: algebraMap (𝓞 E) E (f c * r) * x * c = r • (algebraMap (𝓞 E) E (f c) * x * c)`. Rewrite using `[Algebra.smul_def, map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hr, this]`. Conclude with `I.smul_mem r (hfI c hc)`. Consider the case `zero => simpa using I.zero_mem`. Consider the case `add a b _ _ ha hb => rw [mul_add]`. Conclude with `I.add_mem ha hb`.

Consider the case `smul a c _ hc`. Establish `: algebraMap (𝓞 E) E (∏ c ∈ S, f c) * x * (a • c) = a • (algebraMap (𝓞 E) E (∏ c ∈ S, f c) * x * c)`. Rewrite using `[Algebra.smul_def, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `I.smul_mem a hc`.
-/
theorem exists_common (P : Ideal (𝓞 E)) [P.IsPrime] (I : Submodule (𝓞 E) E) (hfg : I.FG) (x : E)
    (hx : ∀ c ∈ I, ∃ s : 𝓞 E, s ∉ P ∧ algebraMap (𝓞 E) E s * x * c ∈ I) :
    ∃ s : 𝓞 E, s ∉ P ∧ ∀ c ∈ I, algebraMap (𝓞 E) E s * x * c ∈ I := by
  classical
  obtain ⟨S, hS⟩ := hfg
  have hS' : ∀ c ∈ S, ∃ s : 𝓞 E, s ∉ P ∧ algebraMap (𝓞 E) E s * x * c ∈ I :=
    fun c hc => hx c (hS ▸ Submodule.subset_span hc)
  choose! f hfP hfI using hS'
  refine ⟨∏ c ∈ S, f c, ?_, ?_⟩
  · intro hmem
    obtain ⟨c, hc, hcP⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hfP c hc hcP
  · intro c hc
    rw [← hS] at hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem f hc
      have : algebraMap (𝓞 E) E (f c * r) * x * c = r • (algebraMap (𝓞 E) E (f c) * x * c) := by
        rw [Algebra.smul_def, map_mul]; ring
      rw [hr, this]
      exact I.smul_mem r (hfI c hc)
    | zero => simpa using I.zero_mem
    | add a b _ _ ha hb => rw [mul_add]; exact I.add_mem ha hb
    | smul a c _ hc =>
      have : algebraMap (𝓞 E) E (∏ c ∈ S, f c) * x * (a • c) =
          a • (algebraMap (𝓞 E) E (∏ c ∈ S, f c) * x * c) := by
        rw [Algebra.smul_def, Algebra.smul_def]; ring
      rw [this]
      exact I.smul_mem a hc

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Use `set y : E := algebraMap (𝓞 E) E x with hy`. Establish `hne : Algebra.norm ℤ x ≠ 0`. Rewrite using `[Ne, Algebra.norm_eq_zero_iff]` and apply the resulting hypothesis. Establish `hQ : ((Algebra.norm ℤ x : ℤ) : ℚ) = Algebra.norm ℚ y` using `Algebra.coe_norm_int x`.

Establish `hC` using `Algebra.norm_eq_prod_embeddings ℚ ℂ y`. Rewrite `hC` using `[← hQ, map_intCast]`. Set `σ0 : E →ₐ[ℚ] ℂ` to `IsAlgClosed.lift`. Establish `hlt : ‖∏ σ : E →ₐ[ℚ] ℂ, σ y‖ < 1`. Rewrite using `[norm_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ σ0)]`.

Establish `h0 : ‖σ0 y‖ < 1` using `h σ0.toRingHom`. Establish `h1 : ∏ σ ∈ Finset.univ.erase σ0, ‖σ y‖ ≤ 1` using `Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun σ _ => (h σ.toRingHom).le)`. Combine the equalities or inequalities in the displayed calculation. Rewrite `hlt` using `[← hC]`. Establish `h1 : (1 : ℝ) ≤ ‖((Algebra.norm ℤ x : ℤ) : ℂ)‖`.

Rewrite using `[Complex.norm_intCast]`. Conclude with `Int.one_le_abs hne` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eq_zero_of_norm_lt_one (x : 𝓞 E) (h : ∀ φ : E →+* ℂ, ‖φ (algebraMap (𝓞 E) E x)‖ < 1) :
    x = 0 := by
  classical
  by_contra hx
  set y : E := algebraMap (𝓞 E) E x with hy
  have hne : Algebra.norm ℤ x ≠ 0 := by
    rwa [Ne, Algebra.norm_eq_zero_iff]
  have hQ : ((Algebra.norm ℤ x : ℤ) : ℚ) = Algebra.norm ℚ y := Algebra.coe_norm_int x
  have hC := Algebra.norm_eq_prod_embeddings ℚ ℂ y
  rw [← hQ, map_intCast] at hC
  let σ0 : E →ₐ[ℚ] ℂ := IsAlgClosed.lift
  have hlt : ‖∏ σ : E →ₐ[ℚ] ℂ, σ y‖ < 1 := by
    rw [norm_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ σ0)]
    have h0 : ‖σ0 y‖ < 1 := h σ0.toRingHom
    have h1 : ∏ σ ∈ Finset.univ.erase σ0, ‖σ y‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun σ _ => (h σ.toRingHom).le)
    calc ‖σ0 y‖ * ∏ σ ∈ Finset.univ.erase σ0, ‖σ y‖ ≤ ‖σ0 y‖ * 1 :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ < 1 := by rwa [mul_one]
  rw [← hC] at hlt
  have h1 : (1 : ℝ) ≤ ‖((Algebra.norm ℤ x : ℤ) : ℂ)‖ := by
    rw [Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hne
  linarith

/- English proof (translation)
Take `⟨o, ho⟩` from `hν`. Establish `hg0 : (g : E) ≠ 0` using `Nat.cast_ne_zero.mpr (by omega)`. Establish `hg' : (3 : ℝ) ≤ g` using `by exact_mod_cast hg`. Establish `ho0 : o = 0`. Apply `eq_zero_of_norm_lt_one` to reduce the goal to its premises.

Introduce `φ`. Rewrite using `[ho, map_div₀, map_sub, map_one, map_natCast, norm_div, Complex.norm_natCast, div_lt_one (by positivity)]`. Combine the equalities or inequalities in the displayed calculation. Rewrite `ho` using `[ho0, map_zero, eq_comm, div_eq_zero_iff]`. Break down `ho with h | h` into its components or cases.

Conclude with `sub_eq_zero.mp h`. Conclude with `absurd h hg0`.
-/
theorem eq_one_of_cong (μ : E) (g : ℕ) (hg : 3 ≤ g) (hμ : ∀ φ : E →+* ℂ, ‖φ μ‖ = 1)
    (hν : InO ((μ - 1) / (g : E))) : μ = 1 := by
  obtain ⟨o, ho⟩ := hν
  have hg0 : (g : E) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hg' : (3 : ℝ) ≤ g := by exact_mod_cast hg
  have ho0 : o = 0 := by
    apply eq_zero_of_norm_lt_one
    intro φ
    rw [ho, map_div₀, map_sub, map_one, map_natCast, norm_div, Complex.norm_natCast,
      div_lt_one (by positivity)]
    calc ‖φ μ - 1‖ ≤ ‖φ μ‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [hμ φ, norm_one]; norm_num
      _ < g := by linarith
  rw [ho0, map_zero, eq_comm, div_eq_zero_iff] at ho
  rcases ho with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hg0

end PI.UnitaryGroupMassFormula.BetaLUniq.EigA
