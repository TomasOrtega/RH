import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeUnramifiedUniformizer
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LevelUnif

open GlobalTheory.LevelHecke

/- English proof (translation)
Break down `eq_or_ne x 0 with rfl | hx` into its components or cases. Conclude with `zero_le'`. Rewrite `h`, the goal using `[← WithZero.exp_log hx]`. Rewrite `h` using `[WithZero.exp_lt_exp]`. Rewrite using `[WithZero.exp_le_exp]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem le_exp_sub_one {x : WithZero (Multiplicative ℤ)} {n : ℤ} (h : x < WithZero.exp n) :
    x ≤ WithZero.exp (n - 1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le'
  rw [← WithZero.exp_log hx] at h ⊢
  rw [WithZero.exp_lt_exp] at h
  rw [WithZero.exp_le_exp]
  omega

/- English proof (translation)
Use `set v0 := A.eV.symm ⟨v, hv⟩ with hv0`. Establish `hU` using `GlobalTheory.LevelUnram.unram D u A v0`. Use `set P := RingHom.ker (A.res v0) with hP`. Use `haveI hPp : P.IsPrime := RingHom.ker_isPrime _`. Establish `hvP : ∀ x, x ∈ v.asIdeal → algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ P`.

Introduce `x hx`. Establish `h` using `(A.res_v v0 x).1 (by rw [hv0, Equiv.apply_symm_apply]; exact hx)`. Conclude with `h`. Establish `hTP : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ P` using `hU.1`. Establish `hT0 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ≠ 0`.

Conclude with `(D.mem u).A.T_prime.ne_zero` after adjusting the coercions. Establish `hPbot : P ≠ ⊥` using `fun h => hT0 (by rw [h] at hTP; exact (Ideal.mem_bot).1 hTP)`. Establish `hlt : P ^ 2 < P ^ 1` using `Ideal.pow_right_strictAnti P hPbot hPp.ne_top (by norm_num)`. Rewrite `hlt` using `[pow_one]`. Take `⟨a, haP, ha2⟩` from `SetLike.exists_of_lt hlt`.

Establish `hTE : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ P ^ 2`. Introduce `hT2`. Take `⟨s, b, hs, hsab⟩` from `hU.2 a haP`. Establish `h1 : s * a ∈ P ^ 2` using `by rw [hsab]; exact Ideal.mul_mem_right _ _ hT2`. Break down `Ideal.IsPrime.mul_mem_pow P h1 with h | h` into its components or cases.

Conclude with `hs h`. Conclude with `ha2 h`. Introduce `hv2`. Apply `hTE` to reduce the goal to its premises. Establish `hle : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) v.asIdeal ≤ P` using `Ideal.map_le_iff_le_comap.2 (fun x hx => hvP x hx)`.

Establish `h3` using `Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) hv2`. Rewrite `h3` using `[Ideal.map_pow]`. Establish `h4` using `Ideal.pow_right_mono hle 2 h3`. Simplify using `using h4`.
-/
theorem T_notMem_sq (D : D7) (u : D.what₂.Word) (A : Formalism.L2.Forms.AtTTied u)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) :
    (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal ^ 2 := by
  set v0 := A.eV.symm ⟨v, hv⟩ with hv0
  have hU := GlobalTheory.LevelUnram.unram D u A v0
  set P := RingHom.ker (A.res v0) with hP
  haveI hPp : P.IsPrime := RingHom.ker_isPrime _
  have hvP : ∀ x, x ∈ v.asIdeal → algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ P := by
    intro x hx
    have h := (A.res_v v0 x).1 (by rw [hv0, Equiv.apply_symm_apply]; exact hx)
    exact h
  have hTP : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ P := hU.1
  have hT0 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ≠ 0 := by
    exact_mod_cast (D.mem u).A.T_prime.ne_zero
  have hPbot : P ≠ ⊥ := fun h => hT0 (by rw [h] at hTP; exact (Ideal.mem_bot).1 hTP)
  have hlt : P ^ 2 < P ^ 1 := Ideal.pow_right_strictAnti P hPbot hPp.ne_top (by norm_num)
  rw [pow_one] at hlt
  obtain ⟨a, haP, ha2⟩ := SetLike.exists_of_lt hlt
  have hTE : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ P ^ 2 := by
    intro hT2
    obtain ⟨s, b, hs, hsab⟩ := hU.2 a haP
    have h1 : s * a ∈ P ^ 2 := by rw [hsab]; exact Ideal.mul_mem_right _ _ hT2
    rcases Ideal.IsPrime.mul_mem_pow P h1 with h | h
    · exact hs h
    · exact ha2 h
  intro hv2
  apply hTE
  have hle : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) v.asIdeal ≤ P :=
    Ideal.map_le_iff_le_comap.2 (fun x hx => hvP x hx)
  have h3 := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) hv2
  rw [Ideal.map_pow] at h3
  have h4 := Ideal.pow_right_mono hle 2 h3
  simpa using h4

/- English proof (translation)
Introduce `D u A v hv a ha`. Establish `hT2` using `T_notMem_sq D u A v hv`. Establish `hval : v.intValuation (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) = WithZero.exp (-1)`. Apply `le_antisymm` to reduce the goal to its premises. Establish `h` using `(v.intValuation_le_pow_iff_mem _ 1).2 (by simpa using hv)`.

Simplify using `using h`. Assume the negation of the conclusion as `h push_neg at h`. Establish `h2` using `le_exp_sub_one h`. Evaluate the numerical expressions using `at h2`. Conclude with `hT2 ((v.intValuation_le_pow_iff_mem _ 2).1 (by simpa using h2))`.

Establish `hTv : Valued.v ((((D.mem u).A.T : ℕ) : v.adicCompletion D.host.F)) = WithZero.exp (-1)`. Establish `h` using `v.valuedAdicCompletion_eq_valuation (K := D.host.F) (((D.mem u).A.T : ℕ) : 𝓞 D.host.F)`. Rewrite `h` using `[HeightOneSpectrum.valuation_of_algebraMap, hval]`. Simplify using `using h`. Establish `hc0 : ((((D.mem u).A.T : ℕ) : v.adicCompletion D.host.F)) ≠ 0`.

Introduce `h`. Rewrite `hTv` using `[h, map_zero]`. Conclude with `WithZero.zero_ne_coe hTv`. Establish `hale : Valued.v (a : v.adicCompletion D.host.F) ≤ WithZero.exp (-1)`. Establish `h` using `le_exp_sub_one (n := 0) (by simpa using ha)`.

Simplify using `using h`. Use `set c : v.adicCompletion D.host.F := (((D.mem u).A.T : ℕ) : v.adicCompletion D.host.F) with hc`. Establish `hb : (a : v.adicCompletion D.host.F) / c ∈ v.adicCompletionIntegers D.host.F`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, hTv]`. Rewrite using `[div_le_one₀ (by simp)]`.

Conclude with `hale`. Use `⟨⟨_, hb⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[← hc, mul_div_cancel₀ _ hc0]`.
-/
theorem dvd_of_val_lt_one : ∀ (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) (A : Formalism.L2.Forms.AtTTied u)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (_ : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal)
    (a : v.adicCompletionIntegers D.host.F) (_ : Valued.v (a : v.adicCompletion D.host.F) < 1),
    ∃ b : v.adicCompletionIntegers D.host.F, a = (((D.mem u).A.T : ℕ) : v.adicCompletionIntegers D.host.F) * b := by
  intro D u A v hv a ha
  have hT2 := T_notMem_sq D u A v hv
  have hval : v.intValuation (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) = WithZero.exp (-1) := by
    apply le_antisymm
    · have h := (v.intValuation_le_pow_iff_mem _ 1).2 (by simpa using hv)
      simpa using h
    · by_contra h
      push_neg at h
      have h2 := le_exp_sub_one h
      norm_num at h2
      exact hT2 ((v.intValuation_le_pow_iff_mem _ 2).1 (by simpa using h2))
  have hTv : Valued.v ((((D.mem u).A.T : ℕ) : v.adicCompletion D.host.F)) = WithZero.exp (-1) := by
    have h := v.valuedAdicCompletion_eq_valuation (K := D.host.F) (((D.mem u).A.T : ℕ) : 𝓞 D.host.F)
    rw [HeightOneSpectrum.valuation_of_algebraMap, hval] at h
    simpa using h
  have hc0 : ((((D.mem u).A.T : ℕ) : v.adicCompletion D.host.F)) ≠ 0 := by
    intro h; rw [h, map_zero] at hTv; exact WithZero.zero_ne_coe hTv
  have hale : Valued.v (a : v.adicCompletion D.host.F) ≤ WithZero.exp (-1) := by
    have h := le_exp_sub_one (n := 0) (by simpa using ha)
    simpa using h
  set c : v.adicCompletion D.host.F := (((D.mem u).A.T : ℕ) : v.adicCompletion D.host.F) with hc
  have hb : (a : v.adicCompletion D.host.F) / c ∈ v.adicCompletionIntegers D.host.F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, hTv]
    rw [div_le_one₀ (by simp)]
    exact hale
  refine ⟨⟨_, hb⟩, Subtype.ext ?_⟩
  push_cast
  rw [← hc, mul_div_cancel₀ _ hc0]

end GlobalTheory.LevelUnif

end
