import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.LGDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.TraceOfKer
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.DSurjDef

noncomputable section

namespace PI.CntNotIntW

open NumberField IsDedekindDomain Formalism.MainNotions.S
open Classical ValuativeRel
open scoped TensorProduct

/- English proof (translation)
Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`. Conclude with `ringChar.Nat.cast_ringChar`.
-/
theorem resChar_memK {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)) :
    ((Loc.resChar p : ℕ) : 𝓞 K) ∈ p.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

/- English proof (translation)
Rewrite using `[Valuation.mem_integer_iff]`. Establish `h` using `(hval (a : K) 1).mpr (by rw [map_one]; exact p.valuation_le_one a)`. Rewrite `h` using `[Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation Fp)]`. Simplify `h` using `only [map_one]`.
-/
theorem int_memK {K : Type} [Field K] [NumberField K] {p : HeightOneSpectrum (𝓞 K)}
    {Fp : Type} [Field Fp] [ValuativeRel Fp] (ι : K →+* Fp)
    (hval : ∀ x y : K, (ι x ≤ᵥ ι y) ↔ p.valuation K x ≤ p.valuation K y) (a : 𝓞 K) :
    ι (a : K) ∈ 𝒪[Fp] := by
  rw [Valuation.mem_integer_iff]
  have h := (hval (a : K) 1).mpr (by rw [map_one]; exact p.valuation_le_one a)
  rw [Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation Fp)] at h
  simpa only [map_one] using h

/- English proof (translation)
Establish `hmem` using `resChar_memK p`. Establish `h1 : p.valuation K ((Loc.resChar p : ℕ) : K) < 1`. Establish `h` using `(p.valuation_lt_one_iff_mem (K := K) ((Loc.resChar p : ℕ) : 𝓞 K)).mpr hmem`. Simplify using `using h`. Establish `h2 : ¬ (ι 1 ≤ᵥ ι ((Loc.resChar p : ℕ) : K))`.

Rewrite using `[hval, map_one]`. Conclude with `not_le.mpr h1`. Rewrite `h2` using `[Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation Fp)]`. Simplify using `only [map_one, map_natCast] at h2`. Conclude with `not_le.mp h2`.
-/
theorem val_ell_lt {K : Type} [Field K] [NumberField K] {p : HeightOneSpectrum (𝓞 K)}
    {Fp : Type} [Field Fp] [ValuativeRel Fp] (ι : K →+* Fp)
    (hval : ∀ x y : K, (ι x ≤ᵥ ι y) ↔ p.valuation K x ≤ p.valuation K y) :
    valuation Fp ((Loc.resChar p : ℕ) : Fp) < 1 := by
  have hmem := resChar_memK p
  have h1 : p.valuation K ((Loc.resChar p : ℕ) : K) < 1 := by
    have h := (p.valuation_lt_one_iff_mem (K := K) ((Loc.resChar p : ℕ) : 𝓞 K)).mpr hmem
    simpa using h
  have h2 : ¬ (ι 1 ≤ᵥ ι ((Loc.resChar p : ℕ) : K)) := by
    rw [hval, map_one]
    exact not_le.mpr h1
  rw [Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation Fp)] at h2
  simp only [map_one, map_natCast] at h2
  exact not_le.mp h2

/- English proof (translation)
Establish `hg : Continuous fun y : ℤ_[ℓ] => algebraMap ℚ_[ℓ] Fp (y : ℚ_[ℓ])` using `hc.comp continuous_subtype_val`. Establish `hcl : IsClosed {y : ℤ_[ℓ] | algebraMap ℚ_[ℓ] Fp (y : ℚ_[ℓ]) ∈ 𝒪[Fp]}` using `Valuation.isClosed_integer.preimage hg`. Establish `hsub : Set.range (Nat.cast : ℕ → ℤ_[ℓ]) ⊆ {y : ℤ_[ℓ] | algebraMap ℚ_[ℓ] Fp (y : ℚ_[ℓ]) ∈ 𝒪[Fp]}`. Introduce and unpack `_ ⟨k, rfl⟩`. Simplify using `only [Set.mem_setOf_eq]`.

Use `push_cast`. Conclude with `natCast_mem _ k`. Conclude with `hcl.closure_subset_iff.mpr hsub (PadicInt.denseRange_natCast x)`.
-/
theorem zp_memK {ℓ : ℕ} [Fact ℓ.Prime] {Fp : Type} [Field Fp] [ValuativeRel Fp] [TopologicalSpace Fp]
    [IsNonarchimedeanLocalField Fp] [Algebra ℚ_[ℓ] Fp] (hc : Continuous (algebraMap ℚ_[ℓ] Fp))
    (x : ℤ_[ℓ]) : algebraMap ℚ_[ℓ] Fp (x : ℚ_[ℓ]) ∈ 𝒪[Fp] := by
  have hg : Continuous fun y : ℤ_[ℓ] => algebraMap ℚ_[ℓ] Fp (y : ℚ_[ℓ]) :=
    hc.comp continuous_subtype_val
  have hcl : IsClosed {y : ℤ_[ℓ] | algebraMap ℚ_[ℓ] Fp (y : ℚ_[ℓ]) ∈ 𝒪[Fp]} :=
    Valuation.isClosed_integer.preimage hg
  have hsub : Set.range (Nat.cast : ℕ → ℤ_[ℓ]) ⊆ {y : ℤ_[ℓ] | algebraMap ℚ_[ℓ] Fp (y : ℚ_[ℓ]) ∈ 𝒪[Fp]} := by
    rintro _ ⟨k, rfl⟩
    simp only [Set.mem_setOf_eq]
    push_cast
    exact natCast_mem _ k
  exact hcl.closure_subset_iff.mpr hsub (PadicInt.denseRange_natCast x)

/- English proof (translation)
Establish `hπ1 : ∀ y : K, piMap K ℓ Fp ι (1 ⊗ₜ y) = ι y` using `piMap_one_tmul K ℓ Fp ι`. Set `b` to `NumberField.integralBasis K`. Set `bd` to `(Algebra.traceForm ℚ K).dualBasis (traceForm_nondegenerate ℚ K) b`. Establish `hdb : ∀ i j, Algebra.trace ℚ K (bd i * b j) = if j = i then 1 else 0`. Introduce `i j`.

Use `(Algebra.traceForm ℚ K).apply_dualBasis_left (traceForm_nondegenerate ℚ K) b i j` as an intermediate fact. Rewrite `this` using `[Algebra.traceForm_apply]`. Then use the resulting hypothesis. Set `BA` to `Algebra.TensorProduct.basis ℚ_[ℓ] bd`. Establish `hBA : ∀ i, BA i = 1 ⊗ₜ bd i` using `fun i => Algebra.TensorProduct.basis_apply bd i`. Set `Bb` to `Algebra.TensorProduct.basis ℚ_[ℓ] b`.

Establish `hBb : ∀ i, Bb i = 1 ⊗ₜ b i` using `fun i => Algebra.TensorProduct.basis_apply b i`. Establish `: FiniteDimensional ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] K)` using `Module.Finite.of_basis BA`. Establish `htb : ∀ i j, Algebra.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] K) ((1 ⊗ₜ bd i) * (1 ⊗ₜ b j)) = if j = i then 1 else 0`. Introduce `i j`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, trace_one_tmul, hdb]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `hnd : ∀ γ : ℚ_[ℓ] ⊗[ℚ] K, (∀ j, Algebra.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] K) (γ * (1 ⊗ₜ b j)) = 0) → γ = 0`. Introduce `γ hγ`. Establish `hexp` using `BA.sum_repr γ`. Establish `hc0 : ∀ j, BA.repr γ j = 0`.

Introduce `j`. Establish `h` using `hγ j`. Rewrite `h` using `[← hexp, Finset.sum_mul, map_sum]`. Simplify `h` using `only [smul_mul_assoc, map_smul, hBA, htb, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite using `[← hexp]`.

Simplify using `[hc0]`. Set `φ : ℚ_[ℓ] ⊗[ℚ] K →ₗ[ℚ_[ℓ]] ℚ_[ℓ]` to `(Algebra.trace ℚ_[ℓ] Fp).comp ((LinearMap.mulLeft ℚ_[ℓ] z).comp (piMap K ℓ Fp ι).toLinearMap)`. Establish `hφ : ∀ x, φ x = Algebra.trace ℚ_[ℓ] Fp (z * piMap K ℓ Fp ι x)` using `fun x => rfl`. Set `β : ℚ_[ℓ] ⊗[ℚ] K` to `∑ i, φ (1 ⊗ₜ b i) • (1 ⊗ₜ bd i)`. Establish `hβ : ∀ x, Algebra.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] K) (β * x) = φ x`.

Establish `hL : (Algebra.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] K)).comp (LinearMap.mulLeft ℚ_[ℓ] β) = φ`. Apply `Bb.ext` to reduce the goal to its premises. Introduce `j`. Rewrite using `[hBb, LinearMap.comp_apply, LinearMap.mulLeft_apply]`. Simplify using `only [β, Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, htb, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.

Introduce `x`. Conclude with `congrArg (fun L => L x) hL`. Establish `hker : ∀ x, piMap K ℓ Fp ι x = 0 → β * x = 0`. Introduce `x hx`. Apply `hnd` to reduce the goal to its premises.

Introduce `j`. Rewrite using `[mul_assoc, hβ, hφ, map_mul (piMap K ℓ Fp ι), hx, zero_mul, mul_zero, map_zero]`. Establish `htr : ∀ x, Algebra.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] K) (β * x) = Algebra.trace ℚ_[ℓ] Fp (piMap K ℓ Fp ι β * piMap K ℓ Fp ι x)`. Introduce `x`. Rewrite using `[trace_of_ker (piMap K ℓ Fp ι) hsurj (β * x), map_mul]`.

Introduce `y hy`. Rewrite using `[mul_comm β x, mul_assoc, hker y hy, mul_zero]`. Establish `hπβ : piMap K ℓ Fp ι β = z`. Assume the negation of the conclusion as `hne`. Establish `hd0 : piMap K ℓ Fp ι β - z ≠ 0` using `sub_ne_zero.2 hne`.

Take `⟨x, hx⟩` from `hsurj (piMap K ℓ Fp ι β - z)⁻¹`. Establish `e1 : Algebra.trace ℚ_[ℓ] Fp ((piMap K ℓ Fp ι β - z) * piMap K ℓ Fp ι x) = 0`. Rewrite using `[sub_mul, map_sub, ← htr, hβ, hφ, sub_self]`. Rewrite `e1` using `[hx, mul_inv_cancel₀ hd0, ← map_one (algebraMap ℚ_[ℓ] Fp), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]`. Conclude with `(Nat.cast_ne_zero.2 Module.finrank_pos.ne') e1`.

Establish `hzi : ∀ i, ‖φ (1 ⊗ₜ b i)‖ ≤ 1`. Introduce `i`. Rewrite using `[hφ, hπ1, mul_comm]`. Apply `hz` to reduce the goal to its premises. Establish `hb : b i = algebraMap (𝓞 K) K (RingOfIntegers.basis K i)` using `NumberField.integralBasis_apply K i`.

Rewrite using `[hb]`. Conclude with `hint _`. Use `choose N hN using fun i => hS Fp (ι (bd i)) (ℓ : Fp) hℓ`. Set `w : Module.Free.ChooseBasisIndex ℤ (𝓞 K) → ℤ_[ℓ]` to `fun i => ⟨φ (1 ⊗ₜ b i), hzi i⟩`. Set `n : Module.Free.ChooseBasisIndex ℤ (𝓞 K) → ℕ` to `fun i => PadicInt.appr (w i) (k + N i)`.

Establish `hsp : ∀ i, ∃ e : ℤ_[ℓ], e * (ℓ : ℤ_[ℓ]) ^ (k + N i) = w i - n i` using `fun i => Ideal.mem_span_singleton'.1 (PadicInt.appr_spec (k + N i) (w i))`. Use `choose e he using hsp`. Set `t : K` to `∑ i, (n i : ℚ) • bd i`. Use `⟨t, ?_, -(∑ i, algebraMap ℚ_[ℓ] Fp (e i : ℚ_[ℓ]) * ((ℓ : Fp) ^ N i * ι (bd i))), ?_, ?_⟩` and prove the remaining obligations. Establish `htj : ∀ j, Algebra.trace ℚ K (t * b j) = (n j : ℚ)`.

Introduce `j`. Simplify using `only [t, Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, hdb, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Introduce `a`. Establish `ha : (a : K) = ∑ j, ((RingOfIntegers.basis K).repr a j) • b j`. Establish `h` using `congrArg (algebraMap (𝓞 K) K) ((RingOfIntegers.basis K).sum_repr a)`.

Rewrite `h` using `[map_sum]`. Simplify using `only [map_zsmul, ← NumberField.integralBasis_apply] at h`. Conclude with `h.symm`. Use `⟨∑ j, (RingOfIntegers.basis K).repr a j * (n j : ℤ), ?_⟩` and prove the remaining obligations. Rewrite using `[ha, Finset.mul_sum, map_sum]`.

Use `push_cast`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[mul_smul_comm, map_zsmul, htj, zsmul_eq_mul]`. Conclude with `Subring.neg_mem _ (Subring.sum_mem _ fun i _ => Subring.mul_mem _ (zp_memK hc (e i)) ((Valuation.mem_integer_iff _ _).2 (hN i).le))`. Establish `hz' : z = ∑ i, algebraMap ℚ_[ℓ] Fp (w i : ℚ_[ℓ]) * ι (bd i)`.

Rewrite using `[← hπβ]`. Simplify using `only [β, map_sum]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[map_smul, hπ1, Algebra.smul_def]`. Establish `hw : ∀ i, algebraMap ℚ_[ℓ] Fp (w i : ℚ_[ℓ]) = (n i : Fp) + (ℓ : Fp) ^ (k + N i) * algebraMap ℚ_[ℓ] Fp (e i : ℚ_[ℓ])`.

Introduce `i`. Establish `h` using `congrArg (fun x : ℤ_[ℓ] => algebraMap ℚ_[ℓ] Fp (x : ℚ_[ℓ])) (he i)`. Simplify using `only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast, PadicInt.coe_sub, map_mul, map_pow, map_natCast, map_sub] at h`. Take the linear combination `-h`. Establish `hιt : ι t = ∑ i, (n i : Fp) * ι (bd i)`.

Simplify using `only [t, map_sum]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Rat.smul_def, map_mul, map_ratCast, Rat.cast_natCast]`. Rewrite using `[hιt, hz']`. Simplify using `only [hw]`.

Rewrite using `[mul_neg, Finset.mul_sum, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem approx_core {K : Type} [Field K] [NumberField K] {ℓ : ℕ} [Fact ℓ.Prime] {Fp : Type} [Field Fp]
    [CharZero Fp] [ValuativeRel Fp] [TopologicalSpace Fp] [IsNonarchimedeanLocalField Fp] [Algebra ℚ_[ℓ] Fp]
    (hS : PowSmall) (hc : Continuous (algebraMap ℚ_[ℓ] Fp)) (hfin : FiniteDimensional ℚ_[ℓ] Fp) (ι : K →+* Fp)
    (hsurj : Function.Surjective (piMap K ℓ Fp ι)) (hint : ∀ a : 𝓞 K, ι (a : K) ∈ 𝒪[Fp])
    (hℓ : valuation Fp (ℓ : Fp) < 1) (z : Fp) (hz : ∀ c ∈ 𝒪[Fp], ‖Algebra.trace ℚ_[ℓ] Fp (c * z)‖ ≤ 1)
    (k : ℕ) : ∃ t : K, (∀ a : 𝓞 K, ∃ n : ℤ, Algebra.trace ℚ K (t * a) = n) ∧
      ∃ μ ∈ 𝒪[Fp], ι t = z + (ℓ : Fp) ^ k * μ := by
  have hπ1 : ∀ y : K, piMap K ℓ Fp ι (1 ⊗ₜ y) = ι y := piMap_one_tmul K ℓ Fp ι
  let b := NumberField.integralBasis K
  let bd := (Algebra.traceForm ℚ K).dualBasis (traceForm_nondegenerate ℚ K) b
  have hdb : ∀ i j, Algebra.trace ℚ K (bd i * b j) = if j = i then 1 else 0 := by
    intro i j
    have := (Algebra.traceForm ℚ K).apply_dualBasis_left (traceForm_nondegenerate ℚ K) b i j
    rwa [Algebra.traceForm_apply] at this
  let BA := Algebra.TensorProduct.basis ℚ_[ℓ] bd
  have hBA : ∀ i, BA i = 1 ⊗ₜ bd i := fun i => Algebra.TensorProduct.basis_apply bd i
  let Bb := Algebra.TensorProduct.basis ℚ_[ℓ] b
  have hBb : ∀ i, Bb i = 1 ⊗ₜ b i := fun i => Algebra.TensorProduct.basis_apply b i
  have : FiniteDimensional ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] K) := Module.Finite.of_basis BA
  have htb : ∀ i j, Algebra.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] K) ((1 ⊗ₜ bd i) * (1 ⊗ₜ b j)) =
      if j = i then 1 else 0 := by
    intro i j
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, trace_one_tmul, hdb]
    split_ifs <;> simp
  have hnd : ∀ γ : ℚ_[ℓ] ⊗[ℚ] K,
      (∀ j, Algebra.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] K) (γ * (1 ⊗ₜ b j)) = 0) → γ = 0 := by
    intro γ hγ
    have hexp := BA.sum_repr γ
    have hc0 : ∀ j, BA.repr γ j = 0 := by
      intro j
      have h := hγ j
      rw [← hexp, Finset.sum_mul, map_sum] at h
      simpa only [smul_mul_assoc, map_smul, hBA, htb, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true] using h
    rw [← hexp]
    simp [hc0]
  let φ : ℚ_[ℓ] ⊗[ℚ] K →ₗ[ℚ_[ℓ]] ℚ_[ℓ] :=
    (Algebra.trace ℚ_[ℓ] Fp).comp ((LinearMap.mulLeft ℚ_[ℓ] z).comp (piMap K ℓ Fp ι).toLinearMap)
  have hφ : ∀ x, φ x = Algebra.trace ℚ_[ℓ] Fp (z * piMap K ℓ Fp ι x) := fun x => rfl
  let β : ℚ_[ℓ] ⊗[ℚ] K := ∑ i, φ (1 ⊗ₜ b i) • (1 ⊗ₜ bd i)
  have hβ : ∀ x, Algebra.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] K) (β * x) = φ x := by
    have hL : (Algebra.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] K)).comp (LinearMap.mulLeft ℚ_[ℓ] β) = φ := by
      apply Bb.ext
      intro j
      rw [hBb, LinearMap.comp_apply, LinearMap.mulLeft_apply]
      simp only [β, Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, htb, smul_eq_mul, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    intro x
    exact congrArg (fun L => L x) hL
  have hker : ∀ x, piMap K ℓ Fp ι x = 0 → β * x = 0 := by
    intro x hx
    apply hnd
    intro j
    rw [mul_assoc, hβ, hφ, map_mul (piMap K ℓ Fp ι), hx, zero_mul, mul_zero, map_zero]
  have htr : ∀ x, Algebra.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] K) (β * x) =
      Algebra.trace ℚ_[ℓ] Fp (piMap K ℓ Fp ι β * piMap K ℓ Fp ι x) := by
    intro x
    rw [trace_of_ker (piMap K ℓ Fp ι) hsurj (β * x), map_mul]
    intro y hy
    rw [mul_comm β x, mul_assoc, hker y hy, mul_zero]
  have hπβ : piMap K ℓ Fp ι β = z := by
    by_contra hne
    have hd0 : piMap K ℓ Fp ι β - z ≠ 0 := sub_ne_zero.2 hne
    obtain ⟨x, hx⟩ := hsurj (piMap K ℓ Fp ι β - z)⁻¹
    have e1 : Algebra.trace ℚ_[ℓ] Fp ((piMap K ℓ Fp ι β - z) * piMap K ℓ Fp ι x) = 0 := by
      rw [sub_mul, map_sub, ← htr, hβ, hφ, sub_self]
    rw [hx, mul_inv_cancel₀ hd0, ← map_one (algebraMap ℚ_[ℓ] Fp), Algebra.trace_algebraMap, nsmul_eq_mul,
      mul_one] at e1
    exact (Nat.cast_ne_zero.2 Module.finrank_pos.ne') e1
  have hzi : ∀ i, ‖φ (1 ⊗ₜ b i)‖ ≤ 1 := by
    intro i
    rw [hφ, hπ1, mul_comm]
    apply hz
    have hb : b i = algebraMap (𝓞 K) K (RingOfIntegers.basis K i) := NumberField.integralBasis_apply K i
    rw [hb]
    exact hint _
  choose N hN using fun i => hS Fp (ι (bd i)) (ℓ : Fp) hℓ
  let w : Module.Free.ChooseBasisIndex ℤ (𝓞 K) → ℤ_[ℓ] := fun i => ⟨φ (1 ⊗ₜ b i), hzi i⟩
  let n : Module.Free.ChooseBasisIndex ℤ (𝓞 K) → ℕ := fun i => PadicInt.appr (w i) (k + N i)
  have hsp : ∀ i, ∃ e : ℤ_[ℓ], e * (ℓ : ℤ_[ℓ]) ^ (k + N i) = w i - n i :=
    fun i => Ideal.mem_span_singleton'.1 (PadicInt.appr_spec (k + N i) (w i))
  choose e he using hsp
  let t : K := ∑ i, (n i : ℚ) • bd i
  refine ⟨t, ?_, -(∑ i, algebraMap ℚ_[ℓ] Fp (e i : ℚ_[ℓ]) * ((ℓ : Fp) ^ N i * ι (bd i))), ?_, ?_⟩
  · have htj : ∀ j, Algebra.trace ℚ K (t * b j) = (n j : ℚ) := by
      intro j
      simp only [t, Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, hdb, smul_eq_mul, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    intro a
    have ha : (a : K) = ∑ j, ((RingOfIntegers.basis K).repr a j) • b j := by
      have h := congrArg (algebraMap (𝓞 K) K) ((RingOfIntegers.basis K).sum_repr a)
      rw [map_sum] at h
      simp only [map_zsmul, ← NumberField.integralBasis_apply] at h
      exact h.symm
    refine ⟨∑ j, (RingOfIntegers.basis K).repr a j * (n j : ℤ), ?_⟩
    rw [ha, Finset.mul_sum, map_sum]
    push_cast
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_smul_comm, map_zsmul, htj, zsmul_eq_mul]
  · exact Subring.neg_mem _ (Subring.sum_mem _ fun i _ =>
      Subring.mul_mem _ (zp_memK hc (e i)) ((Valuation.mem_integer_iff _ _).2 (hN i).le))
  · have hz' : z = ∑ i, algebraMap ℚ_[ℓ] Fp (w i : ℚ_[ℓ]) * ι (bd i) := by
      rw [← hπβ]
      simp only [β, map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_smul, hπ1, Algebra.smul_def]
    have hw : ∀ i, algebraMap ℚ_[ℓ] Fp (w i : ℚ_[ℓ]) =
        (n i : Fp) + (ℓ : Fp) ^ (k + N i) * algebraMap ℚ_[ℓ] Fp (e i : ℚ_[ℓ]) := by
      intro i
      have h := congrArg (fun x : ℤ_[ℓ] => algebraMap ℚ_[ℓ] Fp (x : ℚ_[ℓ])) (he i)
      simp only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast, PadicInt.coe_sub, map_mul, map_pow,
        map_natCast, map_sub] at h
      linear_combination -h
    have hιt : ι t = ∑ i, (n i : Fp) * ι (bd i) := by
      simp only [t, map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Rat.smul_def, map_mul, map_ratCast, Rat.cast_natCast]
    rw [hιt, hz']
    simp only [hw]
    rw [mul_neg, Finset.mul_sum, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring

/- English proof (translation)
Introduce `K _ _ p _ Fp _ _ _ _ _ hc hfin ι hd hval z hz k`. Use `haveI : CharZero Fp := charZero_of_injective_algebraMap (algebraMap ℚ_[Loc.resChar p] Fp).injective`. Conclude with `approx_core hS hc hfin ι (hP K (Loc.resChar p) Fp hc hfin ι hd) (int_memK ι hval) (val_ell_lt ι hval) z hz k`.
-/
theorem dualApprox_of (hS : PowSmall) (hP : PiSurj) : DualApprox := by
  intro K _ _ p _ Fp _ _ _ _ _ hc hfin ι hd hval z hz k
  haveI : CharZero Fp :=
    charZero_of_injective_algebraMap (algebraMap ℚ_[Loc.resChar p] Fp).injective
  exact approx_core hS hc hfin ι (hP K (Loc.resChar p) Fp hc hfin ι hd) (int_memK ι hval)
    (val_ell_lt ι hval) z hz k

end PI.CntNotIntW
