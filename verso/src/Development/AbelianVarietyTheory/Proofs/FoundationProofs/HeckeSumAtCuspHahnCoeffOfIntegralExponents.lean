import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed

noncomputable section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion

namespace GlobalTheory.HeckeInt

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

/- English proof (translation)
Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Establish `hn : x.den ≠ 0` using `x.den_nz`. Use `haveI : NeZero ((x.den : ℕ) : Ω) := ⟨by exact_mod_cast hn⟩`. Use `haveI : NeZero x.den := ⟨hn⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω x.den`.

Establish `hζ'` using `hζ.map_of_injective ε.injective`. Establish `hz : (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ^ x.den = 1`. Rewrite using `[← Complex.exp_nat_mul]`. Establish `hx : (x : ℂ) * (x.den : ℂ) = (x.num : ℂ)` using `by exact_mod_cast Rat.mul_den_eq_num x`. Establish `: (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = (x.num : ℂ) * (2 * Real.pi * Complex.I)`.

Take the linear combination `(2 * Real.pi * Complex.I) * hx`. Rewrite using `[this, Complex.exp_int_mul_two_pi_mul_I]`. Take `⟨i, -, hi⟩` from `hζ'.eq_pow_of_pow_eq_one hz`. Conclude with `⟨ζ ^ i, by rw [map_pow]; exact hi⟩`.
-/
theorem exists_pre_exp [IsAlgClosed Ω] (ε : Ω →+* ℂ) (x : ℚ) :
    ∃ ω : Ω, ε ω = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hn : x.den ≠ 0 := x.den_nz
  haveI : NeZero ((x.den : ℕ) : Ω) := ⟨by exact_mod_cast hn⟩
  haveI : NeZero x.den := ⟨hn⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω x.den
  have hζ' := hζ.map_of_injective ε.injective
  have hz : (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul]
    have hx : (x : ℂ) * (x.den : ℂ) = (x.num : ℂ) := by exact_mod_cast Rat.mul_den_eq_num x
    have : (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = (x.num : ℂ) * (2 * Real.pi * Complex.I) := by
      linear_combination (2 * Real.pi * Complex.I) * hx
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hz
  exact ⟨ζ ^ i, by rw [map_pow]; exact hi⟩

/- English proof (translation)
The claim follows from `Function.invFun_eq (exists_pre_exp ε x)`.
-/
theorem eps_eOm [IsAlgClosed Ω] (ε : Ω →+* ℂ) (x : ℚ) :
    ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) :=
  Function.invFun_eq (exists_pre_exp ε x)

/- English proof (translation)
Establish `hq' : (0 : ℚ) < (q : ℚ)` using `by exact_mod_cast hq`. Establish `h : (0 : ℚ) < 1 / (q : ℚ)` using `by positivity`. Unfold `sub scale`. Rewrite using `[dif_pos h]`. Establish `e : (OrderIso.mulLeft₀ (1 / (q : ℚ)) h).toOrderEmbedding ((q : ℚ) * s) = s`.

Simplify using `only [RelIso.coe_toRelEmbedding, OrderIso.coe_toOrderEmbedding, OrderIso.mulLeft₀_apply]`. Clear the denominators using the available nonvanishing facts. Establish `key` using `HahnSeries.embDomain_coeff (f := (OrderIso.mulLeft₀ (1 / (q : ℚ)) h).toOrderEmbedding) (x := cm (fun r => eOm ε (r * j / (q : ℚ))) φ) (a := (q : ℚ) * s)`. Rewrite `key` using `[e]`. Rewrite using `[key]`.

Simplify using `only [cm]`. Use `congr 2`. Clear the denominators using the available nonvanishing facts.
-/
theorem sub_coeff (ε : Ω →+* ℂ) (q : ℕ) (hq : 0 < q) (j : ℚ) (φ : HahnSeries ℚ Ω) (s : ℚ) :
    (sub ε 1 j (q : ℚ) φ).coeff s = eOm ε (s * j) * φ.coeff ((q : ℚ) * s) := by
  have hq' : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have h : (0 : ℚ) < 1 / (q : ℚ) := by positivity
  unfold sub scale
  rw [dif_pos h]
  have e : (OrderIso.mulLeft₀ (1 / (q : ℚ)) h).toOrderEmbedding ((q : ℚ) * s) = s := by
    simp only [RelIso.coe_toRelEmbedding, OrderIso.coe_toOrderEmbedding, OrderIso.mulLeft₀_apply]
    field_simp
  have key := HahnSeries.embDomain_coeff (f := (OrderIso.mulLeft₀ (1 / (q : ℚ)) h).toOrderEmbedding)
    (x := cm (fun r => eOm ε (r * j / (q : ℚ))) φ) (a := (q : ℚ) * s)
  rw [e] at key
  rw [key]
  simp only [cm]
  congr 2
  field_simp

/- English proof (translation)
Apply `ε.injective` to reduce the goal to its premises. Establish `hz : ∀ j : ℕ, ε (eOm ε (s * (j : ℚ))) = (Complex.exp (2 * Real.pi * Complex.I * (s : ℂ))) ^ j`. Introduce `j`. Rewrite using `[eps_eOm, ← Complex.exp_nat_mul]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_sum]`. Simplify using `only [hz]`. Use `split_ifs with hd`.

Establish `h1 : Complex.exp (2 * Real.pi * Complex.I * (s : ℂ)) = 1`. Establish `: (s : ℂ) = ((s.num : ℤ) : ℂ)`. Use `Rat.coe_int_num_of_den_eq_one hd` as an intermediate fact. Rewrite using `[← this]`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite using `[this, show 2 * (Real.pi : ℂ) * Complex.I * ((s.num : ℤ) : ℂ) = (s.num : ℂ) * (2 * Real.pi * Complex.I) by ring]`. Conclude with `Complex.exp_int_mul_two_pi_mul_I _`. Simplify using `[h1]`. Establish `hne : Complex.exp (2 * Real.pi * Complex.I * (s : ℂ)) ≠ 1`.

Introduce `h1`. Rewrite `h1` using `[Complex.exp_eq_one_iff]`. Take `⟨n, hn⟩` from `h1`. Establish `hsn : (s : ℂ) = (n : ℂ)`. Establish `h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0` using `by simp [Real.pi_ne_zero, Complex.I_ne_zero]`.

Apply `mul_left_cancel₀ h2` to reduce the goal to its premises. Take the linear combination `hn`. Establish `: s = (n : ℚ)` using `by exact_mod_cast hsn`. Conclude with `hd (by rw [this]; rfl)`. Establish `hpow : (Complex.exp (2 * Real.pi * Complex.I * (s : ℂ))) ^ q = 1`.

Rewrite using `[← Complex.exp_nat_mul]`. Establish `hx : ((q : ℚ) * s : ℚ) = ((((q : ℚ) * s).num : ℤ) : ℚ)` using `(Rat.coe_int_num_of_den_eq_one hs).symm`. Establish `hx' : (q : ℂ) * (s : ℂ) = ((((q : ℚ) * s).num : ℤ) : ℂ)` using `by exact_mod_cast hx`. Rewrite using `[show (q : ℂ) * (2 * Real.pi * Complex.I * (s : ℂ)) = ((((q : ℚ) * s).num : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by`. Rewrite using `[← hx']`.

Use the proof step `ring]`. Conclude with `Complex.exp_int_mul_two_pi_mul_I _`. Rewrite using `[geom_sum_eq hne, hpow, sub_self, zero_div, map_zero]`.
-/
theorem sum_eOm [IsAlgClosed Ω] (ε : Ω →+* ℂ) (q : ℕ) (hq : 0 < q) (s : ℚ) (hs : ((q : ℚ) * s).den = 1) :
    ∑ j ∈ Finset.range q, eOm ε (s * (j : ℚ)) = if s.den = 1 then (q : Ω) else 0 := by
  apply ε.injective
  have hz : ∀ j : ℕ, ε (eOm ε (s * (j : ℚ))) = (Complex.exp (2 * Real.pi * Complex.I * (s : ℂ))) ^ j := by
    intro j
    rw [eps_eOm, ← Complex.exp_nat_mul]
    congr 1
    push_cast; ring
  rw [map_sum]
  simp only [hz]
  split_ifs with hd
  · have h1 : Complex.exp (2 * Real.pi * Complex.I * (s : ℂ)) = 1 := by
      have : (s : ℂ) = ((s.num : ℤ) : ℂ) := by
        have := Rat.coe_int_num_of_den_eq_one hd
        rw [← this]; push_cast; rfl
      rw [this, show 2 * (Real.pi : ℂ) * Complex.I * ((s.num : ℤ) : ℂ) = (s.num : ℂ) * (2 * Real.pi * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    simp [h1]
  · have hne : Complex.exp (2 * Real.pi * Complex.I * (s : ℂ)) ≠ 1 := by
      intro h1
      rw [Complex.exp_eq_one_iff] at h1
      obtain ⟨n, hn⟩ := h1
      have hsn : (s : ℂ) = (n : ℂ) := by
        have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
        apply mul_left_cancel₀ h2
        linear_combination hn
      have : s = (n : ℚ) := by exact_mod_cast hsn
      exact hd (by rw [this]; rfl)
    have hpow : (Complex.exp (2 * Real.pi * Complex.I * (s : ℂ))) ^ q = 1 := by
      rw [← Complex.exp_nat_mul]
      have hx : ((q : ℚ) * s : ℚ) = ((((q : ℚ) * s).num : ℤ) : ℚ) := (Rat.coe_int_num_of_den_eq_one hs).symm
      have hx' : (q : ℂ) * (s : ℂ) = ((((q : ℚ) * s).num : ℤ) : ℂ) := by exact_mod_cast hx
      rw [show (q : ℂ) * (2 * Real.pi * Complex.I * (s : ℂ)) = ((((q : ℚ) * s).num : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by
        rw [← hx']; ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    rw [geom_sum_eq hne, hpow, sub_self, zero_div, map_zero]

/- English proof (translation)
Introduce `Ω _ _ _ ε q hq0 φ hφ s`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Unfold `hq`. Rewrite using `[HahnSeries.coeff_smul, HahnSeries.coeff_sum, smul_eq_mul]`. Simplify using `only [GlobalTheory.HeckeInt.sub_coeff ε q hq0]`.

Rewrite using `[← Finset.sum_mul]`. Distinguish the cases in `hc : φ.coeff ((q : ℚ) * s) = 0`. Simplify using `[hc]`. Rewrite using `[GlobalTheory.HeckeInt.sum_eOm ε q hq0 s (hφ _ hc)]`. Establish `hqne : (q : Ω) ≠ 0` using `by exact_mod_cast hq0.ne'`.

Use `split_ifs`. Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules.
-/
theorem hq_coeff_of_int : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (q : ℕ), 0 < q → ∀ φ : HahnSeries ℚ Ω,
    (∀ r : ℚ, φ.coeff r ≠ 0 → r.den = 1) → ∀ s : ℚ,
      (hq ε q φ).coeff s = if s.den = 1 then φ.coeff ((q : ℚ) * s) else 0 := by
  intro Ω _ _ _ ε q hq0 φ hφ s
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  unfold hq
  rw [HahnSeries.coeff_smul, HahnSeries.coeff_sum, smul_eq_mul]
  simp only [GlobalTheory.HeckeInt.sub_coeff ε q hq0]
  rw [← Finset.sum_mul]
  by_cases hc : φ.coeff ((q : ℚ) * s) = 0
  · simp [hc]
  · rw [GlobalTheory.HeckeInt.sum_eOm ε q hq0 s (hφ _ hc)]
    have hqne : (q : Ω) ≠ 0 := by exact_mod_cast hq0.ne'
    split_ifs
    · field_simp
    · simp

end GlobalTheory.HeckeInt
