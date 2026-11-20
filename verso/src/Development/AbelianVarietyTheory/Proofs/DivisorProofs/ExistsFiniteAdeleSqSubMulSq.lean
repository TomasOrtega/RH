import Mathlib
import GroundTheory.GlobalFields.LocalAtPlace
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Polynomial

namespace GlobalTheory.AdelicQuadSol

/- English proof (translation)
Use `haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v`. Establish `hm : (X ^ 2 - C r : (v.adicCompletionIntegers K)[X]).Monic` using `monic_X_pow_sub_C r two_ne_zero`. Establish `hd : eval b (derivative (X ^ 2 - C r : (v.adicCompletionIntegers K)[X])) = 2 * b`. Simplify using `[one_add_one_eq_two]`. Take `⟨s, hs, -⟩` from `HenselianRing.is_henselian (I := maximalIdeal (v.adicCompletionIntegers K)) (X ^ 2 - C r) hm b (by simpa using hb) (by rw [hd]; exact hu.map _)`.

Use `⟨s, ?_⟩` and prove the remaining obligations. Establish `h0 : s ^ 2 - r = 0` using `by simpa using hs`. Take the linear combination `h0`.
-/
theorem exists_sq_eq_of_approx {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (r b : v.adicCompletionIntegers K) (hb : b ^ 2 - r ∈ maximalIdeal (v.adicCompletionIntegers K))
    (hu : IsUnit (2 * b)) : ∃ s : v.adicCompletionIntegers K, s ^ 2 = r := by
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  have hm : (X ^ 2 - C r : (v.adicCompletionIntegers K)[X]).Monic := monic_X_pow_sub_C r two_ne_zero
  have hd : eval b (derivative (X ^ 2 - C r : (v.adicCompletionIntegers K)[X])) = 2 * b := by
    simp [one_add_one_eq_two]
  obtain ⟨s, hs, -⟩ := HenselianRing.is_henselian (I := maximalIdeal (v.adicCompletionIntegers K))
    (X ^ 2 - C r) hm b (by simpa using hb) (by rw [hd]; exact hu.map _)
  refine ⟨s, ?_⟩
  have h0 : s ^ 2 - r = 0 := by simpa using hs
  linear_combination h0

/- English proof (translation)
Introduce `K _ _ v δ a h2 hδ ha`. Use `set O := v.adicCompletionIntegers K`. Set `d : O` to `⟨algebraMap K (v.adicCompletion K) δ, by rw [mem_adicCompletionIntegers, hδ]⟩`. Set `α : O` to `⟨algebraMap K (v.adicCompletion K) a, by rw [mem_adicCompletionIntegers, ha]⟩`. Establish `hdu : IsUnit d` using `adicCompletionIntegers.isUnit_iff_valued_eq_one.2 hδ`.

Establish `hαu : IsUnit α` using `adicCompletionIntegers.isUnit_iff_valued_eq_one.2 ha`. Establish `h2u : IsUnit (2 : O)`. Apply `adicCompletionIntegers.isUnit_iff_valued_eq_one.2` to reduce the goal to its premises. Establish `e2 : ((2 : O) : v.adicCompletion K) = algebraMap K (v.adicCompletion K) 2`. Rewrite using `[map_ofNat]`.

Both sides reduce to the same expression. Rewrite using `[e2]`. Conclude with `h2`. Use `letI := Fintype.ofFinite (ResidueField O)`. Establish `h2k : (2 : ResidueField O) ≠ 0`.

Use `(h2u.map (residue O)).ne_zero` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis. Establish `hchar : ringChar (ResidueField O) ≠ 2`. Introduce `h`. Apply `h2k` to reduce the goal to its premises.

Use `ringChar.Nat.cast_ringChar (R := ResidueField O)` as an intermediate fact. Rewrite `this` using `[h]`. Conclude with `this` after adjusting the coercions. Establish `hodd` using `FiniteField.odd_card_of_char_ne_two hchar`. Establish `hdk : residue O d ≠ 0` using `(hdu.map (residue O)).ne_zero`.

Establish `hαk : residue O α ≠ 0` using `(hαu.map (residue O)).ne_zero`. Take `⟨s, t, hst⟩` from `FiniteField.exists_root_sum_quadratic (f := (X ^ 2 : (ResidueField O)[X])) (g := C (-residue O d) * X ^ 2 + C (-residue O α)) (by simp) (by compute_degree!) hodd`. Take `⟨x0, rfl⟩` from `residue_surjective s`. Take `⟨y0, rfl⟩` from `residue_surjective t`. Establish `he : x0 ^ 2 - d * y0 ^ 2 - α ∈ maximalIdeal O`.

Rewrite using `[← residue_eq_zero_iff]`. Simplify using `only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at hst`. Rewrite using `[map_sub, map_sub, map_mul, map_pow, map_pow]`. Take the linear combination `hst`. Distinguish the cases in `hx : residue O x0 = 0`.

Establish `hy : residue O y0 ≠ 0`. Introduce `hy`. Apply `hαk` to reduce the goal to its premises. Use `(residue_eq_zero_iff _).2 he` as an intermediate fact. Rewrite `this` using `[map_sub, map_sub, map_mul, map_pow, map_pow, hx, hy]`.

Take the linear combination `-this`. Take `⟨e, he'⟩` from `hdu`. Use `set di : O := ((e⁻¹ : Oˣ) : O)`. Establish `hdi : di * d = 1` using `by rw [← he']; exact e.inv_mul`. Take `⟨y, hy2⟩` from `exists_sq_eq_of_approx v (di * (x0 ^ 2 - α)) y0 (by`.

Establish `: y0 ^ 2 - di * (x0 ^ 2 - α) = -di * (x0 ^ 2 - d * y0 ^ 2 - α)`. Take the linear combination `(-(y0 ^ 2)) * hdi`. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_left _ _ he)`. Use the proof step `(h2u.mul (by`.

Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit]`. Conclude with `hy))`. Use `⟨(x0 : v.adicCompletion K), (y : v.adicCompletion K), x0.2, y.2, ?_⟩` and prove the remaining obligations. Establish `hO : x0 ^ 2 - d * y ^ 2 = α`. Rewrite using `[hy2]`.

Take the linear combination `(-(x0 ^ 2 - α)) * hdi`. Use `congrArg (fun z : O => (z : v.adicCompletion K)) hO` as an intermediate fact. Simplify `this` using `[d, α]`. Take `⟨x, hx2⟩` from `exists_sq_eq_of_approx v (α + d * y0 ^ 2) x0 (by`. Establish `: x0 ^ 2 - (α + d * y0 ^ 2) = x0 ^ 2 - d * y0 ^ 2 - α` using `by ring`.

Rewrite using `[this]`. Conclude with `he)`. Use the proof step `(h2u.mul (by rw [← IsLocalRing.residue_ne_zero_iff_isUnit]; exact hx))`. Use `⟨(x : v.adicCompletion K), (y0 : v.adicCompletion K), x.2, y0.2, ?_⟩` and prove the remaining obligations. Establish `hO : x ^ 2 - d * y0 ^ 2 = α` using `by rw [hx2]; ring`.

Use `congrArg (fun z : O => (z : v.adicCompletion K)) hO` as an intermediate fact. Simplify `this` using `[d, α]`.
-/
theorem local_integral : ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (δ a : K), Valued.v (algebraMap K (v.adicCompletion K) 2) = 1 → Valued.v (algebraMap K (v.adicCompletion K) δ) = 1 → Valued.v (algebraMap K (v.adicCompletion K) a) = 1 → ∃ x y : v.adicCompletion K, x ∈ v.adicCompletionIntegers K ∧ y ∈ v.adicCompletionIntegers K ∧ x ^ 2 - algebraMap K (v.adicCompletion K) δ * y ^ 2 = algebraMap K (v.adicCompletion K) a := by
  intro K _ _ v δ a h2 hδ ha
  set O := v.adicCompletionIntegers K
  let d : O := ⟨algebraMap K (v.adicCompletion K) δ, by rw [mem_adicCompletionIntegers, hδ]⟩
  let α : O := ⟨algebraMap K (v.adicCompletion K) a, by rw [mem_adicCompletionIntegers, ha]⟩
  have hdu : IsUnit d := adicCompletionIntegers.isUnit_iff_valued_eq_one.2 hδ
  have hαu : IsUnit α := adicCompletionIntegers.isUnit_iff_valued_eq_one.2 ha
  have h2u : IsUnit (2 : O) := by
    apply adicCompletionIntegers.isUnit_iff_valued_eq_one.2
    have e2 : ((2 : O) : v.adicCompletion K) = algebraMap K (v.adicCompletion K) 2 := by
      rw [map_ofNat]; rfl
    rw [e2]; exact h2
  letI := Fintype.ofFinite (ResidueField O)
  have h2k : (2 : ResidueField O) ≠ 0 := by
    have := (h2u.map (residue O)).ne_zero
    rwa [map_ofNat] at this
  have hchar : ringChar (ResidueField O) ≠ 2 := by
    intro h
    apply h2k
    have := ringChar.Nat.cast_ringChar (R := ResidueField O)
    rw [h] at this
    exact_mod_cast this
  have hodd := FiniteField.odd_card_of_char_ne_two hchar
  have hdk : residue O d ≠ 0 := (hdu.map (residue O)).ne_zero
  have hαk : residue O α ≠ 0 := (hαu.map (residue O)).ne_zero
  obtain ⟨s, t, hst⟩ := FiniteField.exists_root_sum_quadratic
    (f := (X ^ 2 : (ResidueField O)[X])) (g := C (-residue O d) * X ^ 2 + C (-residue O α))
    (by simp) (by compute_degree!) hodd
  obtain ⟨x0, rfl⟩ := residue_surjective s
  obtain ⟨y0, rfl⟩ := residue_surjective t
  have he : x0 ^ 2 - d * y0 ^ 2 - α ∈ maximalIdeal O := by
    rw [← residue_eq_zero_iff]
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at hst
    rw [map_sub, map_sub, map_mul, map_pow, map_pow]
    linear_combination hst
  by_cases hx : residue O x0 = 0
  · have hy : residue O y0 ≠ 0 := by
      intro hy
      apply hαk
      have := (residue_eq_zero_iff _).2 he
      rw [map_sub, map_sub, map_mul, map_pow, map_pow, hx, hy] at this
      linear_combination -this
    obtain ⟨e, he'⟩ := hdu
    set di : O := ((e⁻¹ : Oˣ) : O)
    have hdi : di * d = 1 := by rw [← he']; exact e.inv_mul
    obtain ⟨y, hy2⟩ := exists_sq_eq_of_approx v (di * (x0 ^ 2 - α)) y0
      (by
        have : y0 ^ 2 - di * (x0 ^ 2 - α) = -di * (x0 ^ 2 - d * y0 ^ 2 - α) := by
          linear_combination (-(y0 ^ 2)) * hdi
        rw [this]; exact Ideal.mul_mem_left _ _ he)
      (h2u.mul (by
        rw [← IsLocalRing.residue_ne_zero_iff_isUnit]; exact hy))
    refine ⟨(x0 : v.adicCompletion K), (y : v.adicCompletion K), x0.2, y.2, ?_⟩
    have hO : x0 ^ 2 - d * y ^ 2 = α := by
      rw [hy2]; linear_combination (-(x0 ^ 2 - α)) * hdi
    have := congrArg (fun z : O => (z : v.adicCompletion K)) hO
    simpa [d, α] using this
  · obtain ⟨x, hx2⟩ := exists_sq_eq_of_approx v (α + d * y0 ^ 2) x0
      (by
        have : x0 ^ 2 - (α + d * y0 ^ 2) = x0 ^ 2 - d * y0 ^ 2 - α := by ring
        rw [this]; exact he)
      (h2u.mul (by rw [← IsLocalRing.residue_ne_zero_iff_isUnit]; exact hx))
    refine ⟨(x : v.adicCompletion K), (y0 : v.adicCompletion K), x.2, y0.2, ?_⟩
    have hO : x ^ 2 - d * y0 ^ 2 = α := by rw [hx2]; ring
    have := congrArg (fun z : O => (z : v.adicCompletion K)) hO
    simpa [d, α] using this

/- English proof (translation)
Use `filter_upwards [(algebraMap K (FiniteAdeleRing (𝓞 K) K) c).2, (algebraMap K (FiniteAdeleRing (𝓞 K) K) c⁻¹).2] with v h1 h2`. Establish `h1' : Valued.v (algebraMap K (v.adicCompletion K) c) ≤ 1` using `(mem_adicCompletionIntegers (𝓞 K) K v).1 h1`. Establish `h2' : Valued.v (algebraMap K (v.adicCompletion K) c⁻¹) ≤ 1` using `(mem_adicCompletionIntegers (𝓞 K) K v).1 h2`. Rewrite `h2'` using `[map_inv₀, map_inv₀]`. Establish `h0 : Valued.v (algebraMap K (v.adicCompletion K) c) ≠ 0`.

Rewrite using `[Ne, map_eq_zero, map_eq_zero]`. Conclude with `hc`. Conclude with `le_antisymm h1' ((inv_le_one₀ (zero_lt_iff.2 h0)).1 h2')`.
-/
theorem eventually_valued_eq_one {K : Type} [Field K] [NumberField K] {c : K} (hc : c ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      Valued.v (algebraMap K (v.adicCompletion K) c) = 1 := by
  filter_upwards [(algebraMap K (FiniteAdeleRing (𝓞 K) K) c).2,
    (algebraMap K (FiniteAdeleRing (𝓞 K) K) c⁻¹).2] with v h1 h2
  have h1' : Valued.v (algebraMap K (v.adicCompletion K) c) ≤ 1 := (mem_adicCompletionIntegers (𝓞 K) K v).1 h1
  have h2' : Valued.v (algebraMap K (v.adicCompletion K) c⁻¹) ≤ 1 := (mem_adicCompletionIntegers (𝓞 K) K v).1 h2
  rw [map_inv₀, map_inv₀] at h2'
  have h0 : Valued.v (algebraMap K (v.adicCompletion K) c) ≠ 0 := by
    rw [Ne, map_eq_zero, map_eq_zero]; exact hc
  exact le_antisymm h1' ((inv_le_one₀ (zero_lt_iff.2 h0)).1 h2')

/- English proof (translation)
Introduce `K _ _ δ a hδ ha hloc`. Establish `h2 : (2 : K) ≠ 0` using `two_ne_zero`. Establish `hev : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, Valued.v (algebraMap K (v.adicCompletion K) 2) = 1 ∧ Valued.v (algebraMap K (v.adicCompletion K) δ) = 1 ∧ Valued.v (algebraMap K (v.adicCompletion K) a) = 1` using `(eventually_valued_eq_one h2).and ((eventually_valued_eq_one hδ).and (eventually_valued_eq_one ha))`. Set `sol : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K × v.adicCompletion K` to `fun v => if h : Valued.v (algebraMap K (v.adicCompletion K) 2) = 1 ∧ Valued.v (algebraMap K (v.adicCompletion K) δ) = 1 ∧ Valued.v (algebraMap K (v.adicCompletion K) a) = 1 then ((local_integral K v δ a h.1 h.2.1 h.2.2).choose, (local_integral K v δ a h.1 h.2.1 h.2.2).choose_spec …`. Establish `hsol : ∀ v, (sol v).1 ^ 2 - algebraMap K (v.adicCompletion K) δ * (sol v).2 ^ 2 = algebraMap K (v.adicCompletion K) a`.

Introduce `v`. Simplify using `only [sol]`. Use `split_ifs with h`. Conclude with `(local_integral K v δ a h.1 h.2.1 h.2.2).choose_spec.choose_spec.2.2`. Conclude with `(hloc v).choose_spec.choose_spec`.

Establish `hint : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, (sol v).1 ∈ v.adicCompletionIntegers K ∧ (sol v).2 ∈ v.adicCompletionIntegers K` using `by filter_upwards [hev] with v h`. Simplify using `only [sol, dif_pos h]`. Conclude with `⟨(local_integral K v δ a h.1 h.2.1 h.2.2).choose_spec.choose_spec.1, (local_integral K v δ a h.1 h.2.1 h.2.2).choose_spec.choose_spec.2.1⟩`. Use `⟨⟨fun v => (sol v).1, hint.mono fun _ h => h.1⟩, ⟨fun v => (sol v).2, hint.mono fun _ h => h.2⟩, ?_⟩` and prove the remaining obligations. Use `FiniteAdeleRing.ext K fun v => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(sol v).1 ^ 2 - algebraMap K (v.adicCompletion K) δ * (sol v).2 ^ 2 = algebraMap K (v.adicCompletion K) a`. Conclude with `hsol v`.
-/
theorem exists_finiteAdele_sq_sub_mul_sq : ∀ (K : Type) [Field K] [NumberField K] (δ a : K), δ ≠ 0 → a ≠ 0 → (∀ v : HeightOneSpectrum (𝓞 K), ∃ x y : v.adicCompletion K, x ^ 2 - algebraMap K (v.adicCompletion K) δ * y ^ 2 = algebraMap K (v.adicCompletion K) a) → ∃ x y : FiniteAdeleRing (𝓞 K) K, x ^ 2 - algebraMap K (FiniteAdeleRing (𝓞 K) K) δ * y ^ 2 = algebraMap K (FiniteAdeleRing (𝓞 K) K) a := by
  intro K _ _ δ a hδ ha hloc
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      Valued.v (algebraMap K (v.adicCompletion K) 2) = 1 ∧
      Valued.v (algebraMap K (v.adicCompletion K) δ) = 1 ∧
      Valued.v (algebraMap K (v.adicCompletion K) a) = 1 :=
    (eventually_valued_eq_one h2).and ((eventually_valued_eq_one hδ).and (eventually_valued_eq_one ha))
  classical
  let sol : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K × v.adicCompletion K := fun v =>
    if h : Valued.v (algebraMap K (v.adicCompletion K) 2) = 1 ∧
      Valued.v (algebraMap K (v.adicCompletion K) δ) = 1 ∧
      Valued.v (algebraMap K (v.adicCompletion K) a) = 1 then
      ((local_integral K v δ a h.1 h.2.1 h.2.2).choose, (local_integral K v δ a h.1 h.2.1 h.2.2).choose_spec.choose)
    else ((hloc v).choose, (hloc v).choose_spec.choose)
  have hsol : ∀ v, (sol v).1 ^ 2 - algebraMap K (v.adicCompletion K) δ * (sol v).2 ^ 2 =
      algebraMap K (v.adicCompletion K) a := by
    intro v
    simp only [sol]
    split_ifs with h
    · exact (local_integral K v δ a h.1 h.2.1 h.2.2).choose_spec.choose_spec.2.2
    · exact (hloc v).choose_spec.choose_spec
  have hint : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      (sol v).1 ∈ v.adicCompletionIntegers K ∧ (sol v).2 ∈ v.adicCompletionIntegers K := by
    filter_upwards [hev] with v h
    simp only [sol, dif_pos h]
    exact ⟨(local_integral K v δ a h.1 h.2.1 h.2.2).choose_spec.choose_spec.1,
      (local_integral K v δ a h.1 h.2.1 h.2.2).choose_spec.choose_spec.2.1⟩
  refine ⟨⟨fun v => (sol v).1, hint.mono fun _ h => h.1⟩, ⟨fun v => (sol v).2, hint.mono fun _ h => h.2⟩, ?_⟩
  refine FiniteAdeleRing.ext K fun v => ?_
  change (sol v).1 ^ 2 - algebraMap K (v.adicCompletion K) δ * (sol v).2 ^ 2 = algebraMap K (v.adicCompletion K) a
  exact hsol v

end GlobalTheory.AdelicQuadSol
