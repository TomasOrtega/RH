import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Formalism.LocalRingCardinality.DataSpaces

open ValuativeRel IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct

namespace GlobalTheory.ResidueCharacterDense

/- English proof (translation)
Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `z hz`. Rewrite using `[IsValuativeTopology.mem_nhds_iff]`. Use `⟨1, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨w, hw, rfl⟩`.

Conclude with `Valuation.map_add_lt _ hz (by simpa using hw)`.
-/
theorem isOpen_ball (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : IsOpen {z : K | valuation K z < 1} := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  rw [IsValuativeTopology.mem_nhds_iff]
  refine ⟨1, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact Valuation.map_add_lt _ hz (by simpa using hw)

/- English proof (translation)
Establish `: MulArchimedean (ValueGroupWithZero K)` using `ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance`. Rewrite using `[(IsValuativeTopology.hasBasis_nhds_zero K).tendsto_right_iff]`. Introduce `γ _`. Take `⟨n, hn⟩` from `exists_pow_lt₀ hz γ`. Use `filter_upwards [eventually_ge_atTop n] with m hm`.

Simplify using `only [Set.mem_setOf_eq, map_pow]`. Conclude with `lt_of_le_of_lt (pow_le_pow_right_of_le_one' hz.le hm) hn`.
-/
theorem tendsto_pow_zero (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (z : K) (hz : valuation K z < 1) :
    Tendsto (fun n : ℕ => z ^ n) atTop (𝓝 0) := by
  have : MulArchimedean (ValueGroupWithZero K) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  rw [(IsValuativeTopology.hasBasis_nhds_zero K).tendsto_right_iff]
  intro γ _
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hz γ
  filter_upwards [eventually_ge_atTop n] with m hm
  simp only [Set.mem_setOf_eq, map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' hz.le hm) hn

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Take `⟨f, hf, hx⟩` from `hx`. Rewrite `hx` using `[Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ]`. Establish `h1 : f.coeff f.natDegree = 1` using `hf`.

Rewrite `hx` using `[h1, map_one, one_mul]`. Establish `h2 : x ^ f.natDegree = - ∑ i ∈ Finset.range f.natDegree, algebraMap ℤ Ω (f.coeff i) * x ^ i`. Take the linear combination `hx`. Establish `h3 : ‖∑ i ∈ Finset.range f.natDegree, algebraMap ℤ Ω (f.coeff i) * x ^ i‖ ≤ ‖x‖ ^ f.natDegree / ‖x‖`. Apply `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)` to reduce the goal to its premises.

Introduce `i hi`. Rewrite using `[norm_mul, norm_pow, le_div_iff₀ (by linarith)]`. Establish `h4 : ‖algebraMap ℤ Ω (f.coeff i)‖ ≤ 1`. Simplify using `using IsUltrametricDist.norm_intCast_le_one Ω (f.coeff i)`. Establish `h5 : ‖x‖ ^ (i + 1) ≤ ‖x‖ ^ f.natDegree` using `pow_le_pow_right₀ h.le (Finset.mem_range.mp hi)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite `h3` using `[← norm_neg, ← h2, norm_pow, le_div_iff₀ (by linarith)]`. Establish `: 0 < ‖x‖ ^ f.natDegree` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem norm_le_one_of_isIntegral {Ω : Type} [NormedField Ω] [IsUltrametricDist Ω] {x : Ω}
    (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  by_contra h
  push Not at h
  obtain ⟨f, hf, hx⟩ := hx
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ] at hx
  have h1 : f.coeff f.natDegree = 1 := hf
  rw [h1, map_one, one_mul] at hx
  have h2 : x ^ f.natDegree = - ∑ i ∈ Finset.range f.natDegree, algebraMap ℤ Ω (f.coeff i) * x ^ i := by
    linear_combination hx
  have h3 : ‖∑ i ∈ Finset.range f.natDegree, algebraMap ℤ Ω (f.coeff i) * x ^ i‖ ≤ ‖x‖ ^ f.natDegree / ‖x‖ := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [norm_mul, norm_pow, le_div_iff₀ (by linarith)]
    have h4 : ‖algebraMap ℤ Ω (f.coeff i)‖ ≤ 1 := by
      simpa using IsUltrametricDist.norm_intCast_le_one Ω (f.coeff i)
    have h5 : ‖x‖ ^ (i + 1) ≤ ‖x‖ ^ f.natDegree :=
      pow_le_pow_right₀ h.le (Finset.mem_range.mp hi)
    calc _ ≤ 1 * ‖x‖ ^ i * ‖x‖ := by gcongr
      _ = ‖x‖ ^ (i + 1) := by ring
      _ ≤ _ := h5
  rw [← norm_neg, ← h2, norm_pow, le_div_iff₀ (by linarith)] at h3
  have : 0 < ‖x‖ ^ f.natDegree := by positivity
  nlinarith

/- English proof (translation)
Establish `hl : (l : ℚ) ≠ 0` using `by exact_mod_cast (Fact.out : l.Prime).ne_zero`. Establish `h1 : ‖(m : ℚ_[l])‖ ≤ (l : ℝ) ^ (-n : ℤ)`. Establish `: (m : ℚ_[l]) = (q : ℚ_[l]) * (l : ℚ_[l]) ^ n` using `by exact_mod_cast h.symm`. Rewrite using `[this, norm_mul, Padic.norm_p_pow]`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨c, hc⟩` from `(Padic.norm_int_le_pow_iff_dvd m n).mp h1`. Use `⟨c, ?_⟩` and prove the remaining obligations. Rewrite `h` using `[hc]`. Move the coercions through the operations in `at h`. Establish `: (l : ℚ) ^ n ≠ 0` using `pow_ne_zero _ hl`.

Apply `mul_right_cancel₀ this` to reduce the goal to its premises. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_int_of_norm_le {l : ℕ} [Fact l.Prime] (q : ℚ) (n : ℕ) (m : ℤ)
    (h : q * (l : ℚ) ^ n = m) (hq : ‖(q : ℚ_[l])‖ ≤ 1) : ∃ c : ℤ, q = c := by
  have hl : (l : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have h1 : ‖(m : ℚ_[l])‖ ≤ (l : ℝ) ^ (-n : ℤ) := by
    have : (m : ℚ_[l]) = (q : ℚ_[l]) * (l : ℚ_[l]) ^ n := by exact_mod_cast h.symm
    rw [this, norm_mul, Padic.norm_p_pow]
    calc _ ≤ 1 * (l : ℝ) ^ (-n : ℤ) := by gcongr
      _ = _ := one_mul _
  obtain ⟨c, hc⟩ := (Padic.norm_int_le_pow_iff_dvd m n).mp h1
  refine ⟨c, ?_⟩
  rw [hc] at h
  push_cast at h
  have : (l : ℚ) ^ n ≠ 0 := pow_ne_zero _ hl
  apply mul_right_cancel₀ this
  rw [h]; ring

/- English proof (translation)
Establish `: Module.Finite F E` using `Module.finite_of_finrank_pos (by omega)`. Establish `: Module.Finite K L` using `Module.finite_of_finrank_pos (by omega)`. Set `b` to `Module.finBasisOfFinrankEq F E hE`. Establish `key : ∀ y : E, g y = ∑ i, f (b.repr y i) • g (b i)`. Introduce `y`.

Use `conv_lhs => rw [← b.sum_repr y]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul, hc]`. Establish `hsp : ⊤ ≤ Submodule.span K (Set.range fun i => g (b i))`.

Rewrite using `[← hs, Submodule.span_le]`. Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[key y]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Set `c` to `basisOfTopLeSpanOfCardEqFinrank (fun i => g (b i)) hsp (by simp [hL])`.

Establish `hcb : ∀ i, c i = g (b i)` using `fun i => by simp [c]`. Establish `hr : ∀ y i, c.repr (g y) i = f (b.repr y i)`. Introduce `y i`. Rewrite using `[key y]`. Repeatedly rewrite using `[← hcb]`.

Conclude with `congrFun (c.repr_sum_self _) i`. Rewrite using `[Algebra.trace_eq_matrix_trace c, Algebra.trace_eq_matrix_trace b, Matrix.trace, Matrix.trace, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul]`. Rewrite using `[hcb, ← map_mul, hr]`.
-/
theorem trace_base_change {F E K L : Type} [Field F] [Field E] [Algebra F E] [Field K]
    [CommRing L] [Algebra K L] [Module.Free K L] (hE : Module.finrank F E = 2)
    (hL : Module.finrank K L = 2) (f : F →+* K) (g : E →+* L)
    (hc : ∀ a : F, g (algebraMap F E a) = algebraMap K L (f a))
    (hs : Submodule.span K (Set.range g) = ⊤) (x : E) :
    Algebra.trace K L (g x) = f (Algebra.trace F E x) := by
  have : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have : Module.Finite K L := Module.finite_of_finrank_pos (by omega)
  let b := Module.finBasisOfFinrankEq F E hE
  have key : ∀ y : E, g y = ∑ i, f (b.repr y i) • g (b i) := by
    intro y
    conv_lhs => rw [← b.sum_repr y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hc]
  have hsp : ⊤ ≤ Submodule.span K (Set.range fun i => g (b i)) := by
    rw [← hs, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    rw [key y]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let c := basisOfTopLeSpanOfCardEqFinrank (fun i => g (b i)) hsp (by simp [hL])
  have hcb : ∀ i, c i = g (b i) := fun i => by simp [c]
  have hr : ∀ y i, c.repr (g y) i = f (b.repr y i) := by
    intro y i
    rw [key y]
    simp_rw [← hcb]
    exact congrFun (c.repr_sum_self _) i
  rw [Algebra.trace_eq_matrix_trace c, Algebra.trace_eq_matrix_trace b, Matrix.trace, Matrix.trace,
    map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul]
  rw [hcb, ← map_mul, hr]

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `⟨inferInstance, hc, hf, fun _ _ => rfl⟩`.
-/
theorem transport (r l : ℕ) [Fact r.Prime] [Fact l.Prime] (h : r = l) (K : Type) [Field K]
    [TopologicalSpace K] [Algebra ℚ_[r] K] (hc : Continuous (algebraMap ℚ_[r] K))
    (hf : FiniteDimensional ℚ_[r] K) :
    ∃ _ : Algebra ℚ_[l] K, Continuous (algebraMap ℚ_[l] K) ∧ FiniteDimensional ℚ_[l] K ∧
      ∀ (z : K) (a : ℚ), ‖Algebra.trace ℚ_[r] K z - (a : ℚ_[r])‖ =
        ‖Algebra.trace ℚ_[l] K z - (a : ℚ_[l])‖ := by
  subst h
  exact ⟨inferInstance, hc, hf, fun _ _ => rfl⟩

/- English proof (translation)
Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ringChar.spec, ← Nat.prime_dvd_prime_iff_eq hp hl]`. Both sides reduce to the same expression.
-/
theorem resChar_eq_iff {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    (hp : (Formalism.MainNotions.S.Loc.resChar p).Prime) {l : ℕ} (hl : l.Prime) :
    Formalism.MainNotions.S.Loc.resChar p = l ↔ (l : 𝓞 F) ∈ p.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ringChar.spec,
    ← Nat.prime_dvd_prime_iff_eq hp hl]
  rfl

/- English proof (translation)
Set `` to `IsTopologicalAddGroup.rightUniformSpace K`. Use `isUniformAddGroup_of_addCommGroup (G := K)` as an intermediate fact. Use `infer_instance`.
-/
theorem t2Space_isNonarchimedeanLocalField_singleBlock (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : T2Space K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

def smallIdeal {F Ω : Type} [Field F] [NormedField Ω] [IsUltrametricDist Ω] (σ : F →+* Ω) :
    Ideal (𝓞 F) where
  carrier := {x | ‖σ x‖ < 1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add] at *
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at *
    have h1 : ‖σ c‖ ≤ 1 :=
      norm_le_one_of_isIntegral ((RingOfIntegers.isIntegral_coe c).map σ.toIntAlgHom)
    calc _ ≤ 1 * ‖σ x‖ := by gcongr
      _ < 1 := by simpa using hx

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_smallIdeal {F Ω : Type} [Field F] [NormedField Ω] [IsUltrametricDist Ω]
    (σ : F →+* Ω) (x : 𝓞 F) : x ∈ smallIdeal σ ↔ ‖σ x‖ < 1 := Iff.rfl

/- English proof (translation)
Rewrite using `[Ideal.ne_top_iff_one, mem_smallIdeal]`. Simplify using the standard rewrite rules. Use the proof step `mem_or_mem' := by`. Introduce `x y h`. Simplify using `only [mem_smallIdeal] at *`.

Assume the negation of the conclusion as `h'`. Use `push Not at h'`. Simplify using `only [map_mul, norm_mul] at h`. Use polynomial arithmetic with `[h'.1, h'.2]`.
-/
theorem smallIdeal_isPrime {F Ω : Type} [Field F] [NormedField Ω] [IsUltrametricDist Ω]
    (σ : F →+* Ω) : (smallIdeal σ).IsPrime where
  ne_top' := by
    rw [Ideal.ne_top_iff_one, mem_smallIdeal]
    simp
  mem_or_mem' := by
    intro x y h
    simp only [mem_smallIdeal] at *
    by_contra h'
    push Not at h'
    simp only [map_mul, norm_mul] at h
    nlinarith [h'.1, h'.2]

section Local

variable {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [NumberField F]
  (p : HeightOneSpectrum (𝓞 F)) {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [T2Space K] [CharZero K] [Algebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K] [ContinuousSMul ℚ_[l] K]
  (ι : F →+* K) (U : Set K)

omit [NumberField F] [CharZero K] in
/- English proof (translation)
Establish `h1 : Continuous τ` using `τ.toLinearMap.continuous_of_finiteDimensional`. Establish `h2 : Continuous τ'` using `τ'.toLinearMap.continuous_of_finiteDimensional`. Conclude with `DFunLike.coe_injective (hd.equalizer h1 h2 (funext h))`.
-/
theorem algHom_ext_dense (hd : DenseRange ι) (τ τ' : K →ₐ[ℚ_[l]] PadicAlgCl l)
    (h : ∀ x, τ (ι x) = τ' (ι x)) : τ = τ' := by
  have h1 : Continuous τ := τ.toLinearMap.continuous_of_finiteDimensional
  have h2 : Continuous τ' := τ'.toLinearMap.continuous_of_finiteDimensional
  exact DFunLike.coe_injective (hd.equalizer h1 h2 (funext h))

omit [CharZero K] in
/- English proof (translation)
Establish `h1 : Continuous τ` using `τ.toLinearMap.continuous_of_finiteDimensional`. Apply `p.isMaximal.eq_of_le (smallIdeal_isPrime _).ne_top` to reduce the goal to its premises. Introduce `x hx`. Rewrite using `[mem_smallIdeal]`. Establish `h2` using `hpow _ ((hU x).mpr ((p.valuation_lt_one_iff_mem x).mpr hx))`.

Establish `h3` using `(h1.tendsto 0).comp h2`. Rewrite `h3` using `[map_zero]`. Rewrite using `[← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]`. Use `h3.congr fun n => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem smallIdeal_comp (hU : ∀ x, ι x ∈ U ↔ p.valuation F x < 1)
    (hpow : ∀ z ∈ U, Tendsto (fun n : ℕ => z ^ n) atTop (𝓝 0))
    (τ : K →ₐ[ℚ_[l]] PadicAlgCl l) :
    p.asIdeal = smallIdeal ((τ : K →+* PadicAlgCl l).comp ι) := by
  have h1 : Continuous τ := τ.toLinearMap.continuous_of_finiteDimensional
  apply p.isMaximal.eq_of_le (smallIdeal_isPrime _).ne_top
  intro x hx
  rw [mem_smallIdeal]
  have h2 := hpow _ ((hU x).mpr ((p.valuation_lt_one_iff_mem x).mpr hx))
  have h3 := (h1.tendsto 0).comp h2
  rw [map_zero] at h3
  rw [← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
  refine h3.congr fun n => ?_
  simp

/- English proof (translation)
Establish `hle : ∀ x : F, ι x ∈ U → ‖σ x‖ ≤ 1`. Introduce `x hx`. Take `⟨n, d, hnd⟩` from `p.exists_primeCompl_mul_eq_of_integer x ((hU x).mp hx).le`. Establish `hd1 : 1 ≤ ‖σ (d : 𝓞 F)‖`. Establish `: (d : 𝓞 F) ∉ p.asIdeal` using `d.2`.

Conclude with `not_lt.mp fun h => this (hσ.ge ((mem_smallIdeal σ _).mpr h))`. Establish `hn : ‖σ n‖ ≤ 1` using `norm_le_one_of_isIntegral ((RingOfIntegers.isIntegral_coe n).map σ.toIntAlgHom)`. Establish `h3 : ‖σ x‖ * ‖σ (d : 𝓞 F)‖ = ‖σ n‖`. Rewrite using `[← norm_mul, ← map_mul]`. Conclude with `congrArg (fun t => ‖σ t‖) hnd`.

Use polynomial arithmetic with `[norm_nonneg (σ x)]`. Establish `h0 : (0 : K) ∈ U` using `by simpa using (hU 0).mpr (by simp)`. Set `b` to `Module.finBasis ℚ F`. Set `Φ : (Fin (Module.finrank ℚ F) → ℚ_[l]) →ₗ[ℚ_[l]] K` to `Fintype.linearCombination ℚ_[l] fun i => ι (b i)`. Set `Ψ : (Fin (Module.finrank ℚ F) → ℚ_[l]) →ₗ[ℚ_[l]] PadicAlgCl l` to `Fintype.linearCombination ℚ_[l] fun i => σ (b i)`.

Establish `hΦc : Continuous Φ` using `Φ.continuous_of_finiteDimensional`. Establish `hΨc : Continuous Ψ` using `Ψ.continuous_of_finiteDimensional`. Establish `hΦq : ∀ c : Fin (Module.finrank ℚ F) → ℚ, Φ (fun i => (c i : ℚ_[l])) = ι (∑ i, c i • b i)`. Introduce `c`. Simplify using `[Φ, Fintype.linearCombination_apply, Algebra.smul_def]`.

Establish `hΨq : ∀ c : Fin (Module.finrank ℚ F) → ℚ, Ψ (fun i => (c i : ℚ_[l])) = σ (∑ i, c i • b i)`. Introduce `c`. Simplify using `[Ψ, Fintype.linearCombination_apply, Algebra.smul_def]`. Establish `hden : DenseRange (Pi.map fun (_ : Fin (Module.finrank ℚ F)) => (Rat.cast : ℚ → ℚ_[l]))` using `DenseRange.piMap fun _ => Padic.denseRange_ratCast l`. Establish `hcl : ∀ c, Φ c ∈ U → ‖Ψ c‖ ≤ 1`.

Introduce `c hc`. Establish `h1` using `Dense.open_subset_closure_inter hden (hUo.preimage hΦc) hc`. Establish `h2 : IsClosed {c | ‖Ψ c‖ ≤ 1}` using `isClosed_le hΨc.norm continuous_const`. Use `h2.closure_subset_iff.mpr ?_ h1` and prove the remaining obligations. Introduce and unpack `_ ⟨hx, q, rfl⟩`.

Establish `e : (Pi.map (fun (_ : Fin (Module.finrank ℚ F)) => (Rat.cast : ℚ → ℚ_[l])) q) = fun i => (q i : ℚ_[l])` using `rfl`. Rewrite `hx` using `[e, Set.mem_preimage, hΦq]`. Rewrite using `[e, Set.mem_setOf_eq, hΨq]`. Conclude with `hle _ hx`. Establish `hker : ∀ c, Φ c = 0 → Ψ c = 0`.

Introduce `c hc`. Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < ‖Ψ c‖` using `norm_pos_iff.mpr hne`. Take `⟨a, ha⟩` from `NormedField.exists_lt_norm ℚ_[l] (‖Ψ c‖⁻¹)`. Establish `h1` using `hcl (a • c) (by rw [map_smul, hc, smul_zero]; exact h0)`.

Rewrite `h1` using `[map_smul, norm_smul]`. Rewrite `ha` using `[inv_lt_iff_one_lt_mul₀ hpos]`. Combine the linear equalities and inequalities to obtain the conclusion. Set `φ : ℚ_[l] ⊗[ℚ] F →ₐ[ℚ_[l]] K` to `Algebra.TensorProduct.lift (Algebra.ofId _ _) ι.toRatAlgHom fun _ _ => Commute.all _ _`. Set `ψ : ℚ_[l] ⊗[ℚ] F →ₐ[ℚ_[l]] PadicAlgCl l` to `Algebra.TensorProduct.lift (Algebra.ofId _ _) σ.toRatAlgHom fun _ _ => Commute.all _ _`.

Establish `hφ : ∀ x, φ (1 ⊗ₜ x) = ι x` using `fun x => by simp [φ]`. Establish `hψ : ∀ x, ψ (1 ⊗ₜ x) = σ x` using `fun x => by simp [ψ]`. Establish `hsurj : Function.Surjective φ`. Establish `h1 : IsClosed (LinearMap.range φ.toLinearMap : Set K)` using `Submodule.closed_of_finiteDimensional _`. Introduce `z`.

Establish `h2 : Set.range ι ⊆ (LinearMap.range φ.toLinearMap : Set K)`. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `⟨1 ⊗ₜ x, hφ x⟩`. Conclude with `h1.closure_subset_iff.mpr h2 (hd z)`. Establish `hk : RingHom.ker φ.toRingHom ≤ RingHom.ker ψ.toRingHom`.

Introduce `t ht`. Set `B` to `Algebra.TensorProduct.basis ℚ_[l] b`. Establish `e1 : φ t = Φ (B.repr t)` using `by conv_lhs => rw [← B.sum_repr t]`. Simplify using `[Φ, Fintype.linearCombination_apply, B, hφ]`. Establish `e2 : ψ t = Ψ (B.repr t)` using `by conv_lhs => rw [← B.sum_repr t]`.

Simplify using `[Ψ, Fintype.linearCombination_apply, B, hψ]`. Establish `ht' : φ t = 0` using `ht`. Express the relevant statement in the definitionally equal form `ψ t = 0`. Rewrite using `[e2]`. Conclude with `hker _ (e1 ▸ ht')`.

Use `⟨AlgHom.liftOfSurjective φ hsurj ψ hk, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← hφ, ← hψ]`. Simplify using the standard rewrite rules.
-/
theorem exists_extension (hd : DenseRange ι) (hUo : IsOpen U)
    (hU : ∀ x, ι x ∈ U ↔ p.valuation F x < 1) (σ : F →+* PadicAlgCl l)
    (hσ : p.asIdeal = smallIdeal σ) :
    ∃ τ : K →ₐ[ℚ_[l]] PadicAlgCl l, ∀ x, τ (ι x) = σ x := by
  have hle : ∀ x : F, ι x ∈ U → ‖σ x‖ ≤ 1 := by
    intro x hx
    obtain ⟨n, d, hnd⟩ := p.exists_primeCompl_mul_eq_of_integer x ((hU x).mp hx).le
    have hd1 : 1 ≤ ‖σ (d : 𝓞 F)‖ := by
      have : (d : 𝓞 F) ∉ p.asIdeal := d.2
      exact not_lt.mp fun h => this (hσ.ge ((mem_smallIdeal σ _).mpr h))
    have hn : ‖σ n‖ ≤ 1 :=
      norm_le_one_of_isIntegral ((RingOfIntegers.isIntegral_coe n).map σ.toIntAlgHom)
    have h3 : ‖σ x‖ * ‖σ (d : 𝓞 F)‖ = ‖σ n‖ := by
      rw [← norm_mul, ← map_mul]; exact congrArg (fun t => ‖σ t‖) hnd
    nlinarith [norm_nonneg (σ x)]
  have h0 : (0 : K) ∈ U := by simpa using (hU 0).mpr (by simp)
  let b := Module.finBasis ℚ F
  let Φ : (Fin (Module.finrank ℚ F) → ℚ_[l]) →ₗ[ℚ_[l]] K :=
    Fintype.linearCombination ℚ_[l] fun i => ι (b i)
  let Ψ : (Fin (Module.finrank ℚ F) → ℚ_[l]) →ₗ[ℚ_[l]] PadicAlgCl l :=
    Fintype.linearCombination ℚ_[l] fun i => σ (b i)
  have hΦc : Continuous Φ := Φ.continuous_of_finiteDimensional
  have hΨc : Continuous Ψ := Ψ.continuous_of_finiteDimensional
  have hΦq : ∀ c : Fin (Module.finrank ℚ F) → ℚ,
      Φ (fun i => (c i : ℚ_[l])) = ι (∑ i, c i • b i) := by
    intro c
    simp [Φ, Fintype.linearCombination_apply, Algebra.smul_def]
  have hΨq : ∀ c : Fin (Module.finrank ℚ F) → ℚ,
      Ψ (fun i => (c i : ℚ_[l])) = σ (∑ i, c i • b i) := by
    intro c
    simp [Ψ, Fintype.linearCombination_apply, Algebra.smul_def]
  have hden : DenseRange (Pi.map fun (_ : Fin (Module.finrank ℚ F)) => (Rat.cast : ℚ → ℚ_[l])) :=
    DenseRange.piMap fun _ => Padic.denseRange_ratCast l
  have hcl : ∀ c, Φ c ∈ U → ‖Ψ c‖ ≤ 1 := by
    intro c hc
    have h1 := Dense.open_subset_closure_inter hden (hUo.preimage hΦc) hc
    have h2 : IsClosed {c | ‖Ψ c‖ ≤ 1} := isClosed_le hΨc.norm continuous_const
    refine h2.closure_subset_iff.mpr ?_ h1
    rintro _ ⟨hx, q, rfl⟩
    have e : (Pi.map (fun (_ : Fin (Module.finrank ℚ F)) => (Rat.cast : ℚ → ℚ_[l])) q) =
      fun i => (q i : ℚ_[l]) := rfl
    rw [e, Set.mem_preimage, hΦq] at hx
    rw [e, Set.mem_setOf_eq, hΨq]
    exact hle _ hx
  have hker : ∀ c, Φ c = 0 → Ψ c = 0 := by
    intro c hc
    by_contra hne
    have hpos : 0 < ‖Ψ c‖ := norm_pos_iff.mpr hne
    obtain ⟨a, ha⟩ := NormedField.exists_lt_norm ℚ_[l] (‖Ψ c‖⁻¹)
    have h1 := hcl (a • c) (by rw [map_smul, hc, smul_zero]; exact h0)
    rw [map_smul, norm_smul] at h1
    rw [inv_lt_iff_one_lt_mul₀ hpos] at ha
    linarith
  let φ : ℚ_[l] ⊗[ℚ] F →ₐ[ℚ_[l]] K :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) ι.toRatAlgHom fun _ _ => Commute.all _ _
  let ψ : ℚ_[l] ⊗[ℚ] F →ₐ[ℚ_[l]] PadicAlgCl l :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) σ.toRatAlgHom fun _ _ => Commute.all _ _
  have hφ : ∀ x, φ (1 ⊗ₜ x) = ι x := fun x => by simp [φ]
  have hψ : ∀ x, ψ (1 ⊗ₜ x) = σ x := fun x => by simp [ψ]
  have hsurj : Function.Surjective φ := by
    have h1 : IsClosed (LinearMap.range φ.toLinearMap : Set K) :=
      Submodule.closed_of_finiteDimensional _
    intro z
    have h2 : Set.range ι ⊆ (LinearMap.range φ.toLinearMap : Set K) := by
      rintro _ ⟨x, rfl⟩
      exact ⟨1 ⊗ₜ x, hφ x⟩
    exact h1.closure_subset_iff.mpr h2 (hd z)
  have hk : RingHom.ker φ.toRingHom ≤ RingHom.ker ψ.toRingHom := by
    intro t ht
    let B := Algebra.TensorProduct.basis ℚ_[l] b
    have e1 : φ t = Φ (B.repr t) := by
      conv_lhs => rw [← B.sum_repr t]
      simp [Φ, Fintype.linearCombination_apply, B, hφ]
    have e2 : ψ t = Ψ (B.repr t) := by
      conv_lhs => rw [← B.sum_repr t]
      simp [Ψ, Fintype.linearCombination_apply, B, hψ]
    have ht' : φ t = 0 := ht
    change ψ t = 0
    rw [e2]
    exact hker _ (e1 ▸ ht')
  refine ⟨AlgHom.liftOfSurjective φ hsurj ψ hk, fun x => ?_⟩
  rw [← hφ, ← hψ]
  simp

end Local

/- English proof (translation)
Apply `(algebraMap ℚ_[l] (PadicAlgCl l)).injective` to reduce the goal to its premises. Rewrite using `[map_sum, map_ratCast]`. Establish `e : ((Algebra.trace ℚ F t : ℚ) : PadicAlgCl l) = algebraMap ℚ (PadicAlgCl l) (Algebra.trace ℚ F t)` using `by simp`. Rewrite using `[e, trace_eq_sum_embeddings]`. Repeatedly rewrite using `[trace_eq_sum_embeddings]`.

Rewrite using `[Finset.sum_sigma', Finset.univ_sigma_univ]`. Use `Fintype.sum_bijective (fun x : (Σ s, K s →ₐ[ℚ_[l]] PadicAlgCl l) => ((x.2 : K x.1 →+* PadicAlgCl l).comp (ι x.1)).toRatAlgHom) ⟨?_, ?_⟩ _ _ (fun x => rfl)` and prove the remaining obligations. Introduce and unpack `⟨s, τ⟩ ⟨s', τ'⟩ h`. Establish `h' : (τ : K s →+* PadicAlgCl l).comp (ι s) = (τ' : K s' →+* PadicAlgCl l).comp (ι s')` using `RingHom.ext fun x => DFunLike.congr_fun h x`. Establish `h1` using `smallIdeal_comp (P s) (ι s) (U s) (hU s) (hpow s) τ`.

Establish `h2` using `smallIdeal_comp (P s') (ι s') (U s') (hU s') (hpow s') τ'`. Rewrite `h1` using `[h', ← h2]`. Take `rfl : s = s'` from `hP (HeightOneSpectrum.ext h1)`. Rewrite using `[algHom_ext_dense (ι s) (hd s) τ τ' fun x => DFunLike.congr_fun h' x]`. Introduce `σ`.

Take `⟨s, hs⟩` from `hS (smallIdeal (σ : F →+* PadicAlgCl l)) (smallIdeal_isPrime _) (by`. Rewrite using `[mem_smallIdeal]`. Establish `: (σ : F →+* PadicAlgCl l) ((l : 𝓞 F) : F) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l])` using `by simp`. Rewrite using `[this, norm_algebraMap']`. Conclude with `Padic.norm_p_lt_one)`.

Take `⟨τ, hτ⟩` from `exists_extension (P s) (ι s) (U s) (hd s) (hUo s) (hU s) _ hs`. Conclude with `⟨⟨s, τ⟩, AlgHom.ext fun x => hτ x⟩`.
-/
theorem sum_local_trace {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [NumberField F]
    {S : Type} [Fintype S] (P : S → HeightOneSpectrum (𝓞 F)) (hP : Function.Injective P)
    (hS : ∀ I : Ideal (𝓞 F), I.IsPrime → (l : 𝓞 F) ∈ I → ∃ s, (P s).asIdeal = I)
    (K : S → Type) [∀ s, Field (K s)] [∀ s, TopologicalSpace (K s)]
    [∀ s, IsTopologicalRing (K s)] [∀ s, T2Space (K s)] [∀ s, CharZero (K s)]
    [∀ s, Algebra ℚ_[l] (K s)] [∀ s, FiniteDimensional ℚ_[l] (K s)]
    [∀ s, ContinuousSMul ℚ_[l] (K s)] (ι : ∀ s, F →+* K s) (U : ∀ s, Set (K s))
    (hd : ∀ s, DenseRange (ι s)) (hUo : ∀ s, IsOpen (U s))
    (hU : ∀ s x, ι s x ∈ U s ↔ (P s).valuation F x < 1)
    (hpow : ∀ s, ∀ z ∈ U s, Tendsto (fun n : ℕ => z ^ n) atTop (𝓝 0)) (t : F) :
    ∑ s, Algebra.trace ℚ_[l] (K s) (ι s t) = ((Algebra.trace ℚ F t : ℚ) : ℚ_[l]) := by
  classical
  apply (algebraMap ℚ_[l] (PadicAlgCl l)).injective
  rw [map_sum, map_ratCast]
  have e : ((Algebra.trace ℚ F t : ℚ) : PadicAlgCl l) =
      algebraMap ℚ (PadicAlgCl l) (Algebra.trace ℚ F t) := by simp
  rw [e, trace_eq_sum_embeddings]
  simp_rw [trace_eq_sum_embeddings]
  rw [Finset.sum_sigma', Finset.univ_sigma_univ]
  refine Fintype.sum_bijective
    (fun x : (Σ s, K s →ₐ[ℚ_[l]] PadicAlgCl l) =>
      ((x.2 : K x.1 →+* PadicAlgCl l).comp (ι x.1)).toRatAlgHom) ⟨?_, ?_⟩ _ _ (fun x => rfl)
  · rintro ⟨s, τ⟩ ⟨s', τ'⟩ h
    have h' : (τ : K s →+* PadicAlgCl l).comp (ι s) = (τ' : K s' →+* PadicAlgCl l).comp (ι s') :=
      RingHom.ext fun x => DFunLike.congr_fun h x
    have h1 := smallIdeal_comp (P s) (ι s) (U s) (hU s) (hpow s) τ
    have h2 := smallIdeal_comp (P s') (ι s') (U s') (hU s') (hpow s') τ'
    rw [h', ← h2] at h1
    obtain rfl : s = s' := hP (HeightOneSpectrum.ext h1)
    rw [algHom_ext_dense (ι s) (hd s) τ τ' fun x => DFunLike.congr_fun h' x]
  · intro σ
    obtain ⟨s, hs⟩ := hS (smallIdeal (σ : F →+* PadicAlgCl l)) (smallIdeal_isPrime _) (by
      rw [mem_smallIdeal]
      have : (σ : F →+* PadicAlgCl l) ((l : 𝓞 F) : F) =
          algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
      rw [this, norm_algebraMap']
      exact Padic.norm_p_lt_one)
    obtain ⟨τ, hτ⟩ := exists_extension (P s) (ι s) (U s) (hd s) (hUo s) (hU s) _ hs
    exact ⟨⟨s, τ⟩, AlgHom.ext fun x => hτ x⟩

open Formalism.MainNotions.S.Loc

/- English proof (translation)
Take `⟨a, h1, h2, h3⟩` from `A.psiE_def (A.ιE x)`. Use `⟨a, h1, ?_, h3⟩` and prove the remaining obligations. Use `A.free` as an intermediate fact. Use `A.qlFin` as an intermediate fact. Establish `: Module.Finite A.Fp A.Ep` using `Module.finite_of_finrank_pos (by rw [A.rank]; omega)`.

Use `letI := ((algebraMap A.Fp A.Ep).comp (algebraMap ℚ_[resChar p] A.Fp)).toAlgebra`. Establish `: IsScalarTower ℚ_[resChar p] A.Fp A.Ep` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Rewrite using `[← trace_base_change hE A.rank A.ιF A.ιE A.compat A.span x, Algebra.trace_trace]`. Conclude with `h2`.
-/
theorem psi_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (hE : Module.finrank F E = 2) {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
    (A : LocAt F E sig p) [Fact (resChar p).Prime] (x : E) :
    ∃ a : ℚ, (∃ n : ℕ, a.den = (resChar p) ^ n) ∧
      ‖Algebra.trace ℚ_[resChar p] A.Fp (A.ιF (Algebra.trace F E x)) - (a : ℚ_[resChar p])‖ ≤ 1 ∧
      A.psiE (A.ιE x) = Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)) := by
  obtain ⟨a, h1, h2, h3⟩ := A.psiE_def (A.ιE x)
  refine ⟨a, h1, ?_, h3⟩
  have := A.free
  have := A.qlFin
  have : Module.Finite A.Fp A.Ep := Module.finite_of_finrank_pos (by rw [A.rank]; omega)
  letI := ((algebraMap A.Fp A.Ep).comp (algebraMap ℚ_[resChar p] A.Fp)).toAlgebra
  have : IsScalarTower ℚ_[resChar p] A.Fp A.Ep := IsScalarTower.of_algebraMap_eq fun _ => rfl
  rw [← trace_base_change hE A.rank A.ιF A.ιE A.compat A.span x, Algebra.trace_trace]
  exact h2

/- English proof (translation)
Rewrite using `[← Complex.exp_int_mul_two_pi_mul_I c]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exp_int (c : ℤ) : Complex.exp (2 * Real.pi * Complex.I * ((c : ℚ) : ℂ)) = 1 := by
  rw [← Complex.exp_int_mul_two_pi_mul_I c]
  congr 1
  push_cast
  ring

/- English proof (translation)
Take `⟨j, rfl⟩` from `Nat.exists_eq_add_of_le hN`. Use `⟨a.num * l ^ j, ?_⟩` and prove the remaining obligations. Establish `: a * (l : ℚ) ^ n = a.num`. Rewrite using `[← Rat.mul_den_eq_num, h]`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite using `[pow_add, ← mul_assoc, this]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem exists_mul_pow_int (a : ℚ) (l n : ℕ) (h : a.den = l ^ n) (N : ℕ) (hN : n ≤ N) :
    ∃ m : ℤ, a * (l : ℚ) ^ N = m := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hN
  refine ⟨a.num * l ^ j, ?_⟩
  have : a * (l : ℚ) ^ n = a.num := by
    rw [← Rat.mul_den_eq_num, h]; push_cast; rfl
  rw [pow_add, ← mul_assoc, this]
  push_cast
  rfl

/- English proof (translation)
Use `A.ellPrime` as an intermediate fact. Use `A.qlFin` as an intermediate fact. Use `A.char0` as an intermediate fact. Establish `: Module.Finite F E` using `Module.finite_of_finrank_pos (by omega)`. Take `⟨a, ⟨n, hn⟩, h2, h3⟩` from `psi_eq hE A (y / (l : E) ^ k)`.

Establish `e1 : y / (l : E) ^ k = ((l : F) ^ k)⁻¹ • y`. Rewrite using `[Algebra.smul_def]`. Simplify using `[div_eq_inv_mul]`. Establish `e2 : A.ιF (Algebra.trace F E (y / (l : E) ^ k)) = ((l : ℚ_[resChar p]) ^ k)⁻¹ • A.ιF (Algebra.trace F E y)`. Rewrite using `[e1, map_smul, Algebra.smul_def, Algebra.smul_def]`.

Simplify using the standard rewrite rules. Establish `i1 : IsIntegral ℤ (Algebra.trace ℚ_[resChar p] A.Fp (A.ιF (Algebra.trace F E y)))` using `Algebra.isIntegral_trace ((Algebra.isIntegral_trace hy).map A.ιF.toIntAlgHom)`. Establish `n1 : ‖(l : ℚ_[resChar p])‖ = 1`. Rewrite using `[Padic.norm_natCast_eq_one_iff]`. Conclude with `(Nat.coprime_primes A.ellPrime.out hl).mpr hp`.

Establish `n2 : ‖Algebra.trace ℚ_[resChar p] A.Fp (A.ιF (Algebra.trace F E (y / (l : E) ^ k)))‖ ≤ 1`. Rewrite using `[e2, map_smul, norm_smul, norm_inv, norm_pow, n1]`. Simplify using `using norm_le_one_of_isIntegral i1`. Establish `n3 : ‖(a : ℚ_[resChar p])‖ ≤ 1`. Use `IsUltrametricDist.norm_add_le_max _ _ |>.trans (max_le n2 ((norm_neg _).trans_le h2))` as an intermediate fact.

Simplify using `using this`. Take `⟨m, hm⟩` from `exists_mul_pow_int a _ n hn n le_rfl`. Take `⟨c, rfl⟩` from `exists_int_of_norm_le a n m hm n3`. Rewrite using `[h3, exp_int]`.
-/
theorem psi_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (hE : Module.finrank F E = 2) {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
    (A : LocAt F E sig p) {l : ℕ} (hl : l.Prime) (hp : resChar p ≠ l) (y : E)
    (hy : IsIntegral ℤ y) (k : ℕ) : A.psiE (A.ιE (y / (l : E) ^ k)) = 1 := by
  have := A.ellPrime
  have := A.qlFin
  have := A.char0
  have : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  obtain ⟨a, ⟨n, hn⟩, h2, h3⟩ := psi_eq hE A (y / (l : E) ^ k)
  have e1 : y / (l : E) ^ k = ((l : F) ^ k)⁻¹ • y := by
    rw [Algebra.smul_def]; simp [div_eq_inv_mul]
  have e2 : A.ιF (Algebra.trace F E (y / (l : E) ^ k)) =
      ((l : ℚ_[resChar p]) ^ k)⁻¹ • A.ιF (Algebra.trace F E y) := by
    rw [e1, map_smul, Algebra.smul_def, Algebra.smul_def]; simp
  have i1 : IsIntegral ℤ (Algebra.trace ℚ_[resChar p] A.Fp (A.ιF (Algebra.trace F E y))) :=
    Algebra.isIntegral_trace ((Algebra.isIntegral_trace hy).map A.ιF.toIntAlgHom)
  have n1 : ‖(l : ℚ_[resChar p])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes A.ellPrime.out hl).mpr hp
  have n2 : ‖Algebra.trace ℚ_[resChar p] A.Fp (A.ιF (Algebra.trace F E (y / (l : E) ^ k)))‖ ≤ 1 := by
    rw [e2, map_smul, norm_smul, norm_inv, norm_pow, n1]
    simpa using norm_le_one_of_isIntegral i1
  have n3 : ‖(a : ℚ_[resChar p])‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max _ _ |>.trans (max_le n2 ((norm_neg _).trans_le h2))
    simpa using this
  obtain ⟨m, hm⟩ := exists_mul_pow_int a _ n hn n le_rfl
  obtain ⟨c, rfl⟩ := exists_int_of_norm_le a n m hm n3
  rw [h3, exp_int]

/- English proof (translation)
Establish `: Fact l.Prime` using `⟨hl⟩`. Establish `: Module.Finite F E` using `Module.finite_of_finrank_pos (by omega)`. Establish `hl0 : (l : 𝓞 F) ≠ 0` using `by exact_mod_cast hl.ne_zero`. Establish `hfin : {p : HeightOneSpectrum (𝓞 F) | resChar p = l}.Finite`. Use `(Ideal.finite_factors (I := Ideal.span {(l : 𝓞 F)}) (by simpa using hl0)).subset ?_` and prove the remaining obligations.

Introduce `p hp`. Rewrite using `[Set.mem_setOf_eq, Ideal.dvd_span_singleton]`. Conclude with `(resChar_eq_iff p (A p).ellPrime.out hl).mp hp`. Establish `hsupp : (Function.mulSupport fun p : HeightOneSpectrum (𝓞 F) => (A p).psiE ((A p).ιE (y / (l : E) ^ k))) ⊆ {p | resChar p = l}`. Introduce `p hp`.

Assume the negation of the conclusion as `h`. Conclude with `hp (psi_eq_one hE (A p) hl h y hy k)`. Use `⟨hfin.subset hsupp, ?_⟩` and prove the remaining obligations. Set `S : Type` to `{p : HeightOneSpectrum (𝓞 F) | resChar p = l}`. Use `letI : Fintype S := hfin.fintype`.

Rewrite using `[finprod_eq_prod_of_mulSupport_subset _ (s := hfin.toFinset) (by simpa using hsupp), Finset.prod_subtype (F := (inferInstance : Fintype S)) hfin.toFinset (p := fun p => p ∈ {p : HeightOneSpectrum (𝓞 F) | resChar p = l}) (by simp)]`. Use `set x := y / (l : E) ^ k with hx`. Establish `hres : ∀ s : S, resChar s.1 = l` using `fun s => s.2`. Establish `hF : ∀ p : HeightOneSpectrum (𝓞 F), Fact (resChar p).Prime` using `fun p => (A p).ellPrime`. Use `choose alg hc hf ht using fun s : S => transport (resChar s.1) l (hres s) (A s.1).Fp (A s.1).qlCont (A s.1).qlFin`.

Use `choose a ha hb hψ using fun s : S => psi_eq hE (A s.1) x`. Use `choose n hn using ha`. Rewrite `hb` using `[ht]`. Establish `hlf : ∀ s : S, IsNonarchimedeanLocalField (A s.1).Fp` using `fun s => (A s.1).lf`. Establish `: ∀ s : S, T2Space (A s.1).Fp` using `fun s => t2Space_isNonarchimedeanLocalField_singleBlock _`.

Establish `: ∀ s : S, CharZero (A s.1).Fp` using `fun s => (A s.1).char0`. Establish `: ∀ s : S, ContinuousSMul ℚ_[l] (A s.1).Fp` using `fun s => continuousSMul_of_algebraMap _ _ (hc s)`. Establish `hsum` using `sum_local_trace (l := l) (S := S) Subtype.val Subtype.val_injective (fun I hI hlI => ⟨⟨⟨I, hI, fun h => hl0 (by simpa [h] using hlI)⟩, (resChar_eq_iff _ (hF _).out hl).mpr hlI⟩, rfl⟩) (fun s => (A s.1).Fp) (fun s => (A s.1).ιF) (fun s => {z | valuation _ z < 1}) (fun s => (A s.1) …`. Establish `h` using `(A s.1).val 1 z`. Rewrite `h` using `[Valuation.Compatible.vle_iff_le (v := valuation _)]`.

Simplify using `only [map_one] at h`. Rewrite using `[Set.mem_setOf_eq, ← not_le, ← not_le, h])`. Use the proof step `(fun s z hz => tendsto_pow_zero _ z hz) (Algebra.trace F E x)`. Rewrite `hsum` using `[Algebra.trace_trace]`. Establish `hnorm : ‖((Algebra.trace ℚ E x - ∑ s, a s : ℚ) : ℚ_[l])‖ ≤ 1`.

Use `push_cast`. Rewrite using `[← hsum, ← Finset.sum_sub_distrib]`. Conclude with `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun s _ => hb s`. Set `N` to `k + ∑ s, n s`. Use `choose m hm using fun s : S => exists_mul_pow_int (a s) l (n s) (by rw [hn s, hres s]) N ((Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)).trans (Nat.le_add_left _ _))`.

Take `⟨r, hr⟩` from `IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_trace (L := ℚ) hy)`. Establish `hlq : (l : ℚ) ≠ 0` using `by exact_mod_cast hl.ne_zero`. Establish `e1 : Algebra.trace ℚ E x = ((l : ℚ) ^ k)⁻¹ * r`. Establish `: x = ((l : ℚ) ^ k)⁻¹ • y`. Rewrite using `[hx, Algebra.smul_def]`.

Simplify using `[div_eq_inv_mul]`. Rewrite using `[this, map_smul, ← hr]`. Simplify using the standard rewrite rules. Take `⟨c, hc⟩` from `exists_int_of_norm_le _ N (r * l ^ (∑ s, n s) - ∑ s, m s) (by`. Rewrite using `[sub_mul, Finset.sum_mul, e1]`.

Repeatedly rewrite using `[hm]`. Use `push_cast`. Simplify using `only [N, pow_add]`. Use the proof step `field_simp) hnorm`. Establish `e2 : Algebra.trace ℚ E x = ∑ s, a s + c` using `by linear_combination hc`.

Rewrite using `[e2, Rat.cast_add, mul_add, Complex.exp_add, exp_int, mul_one, Rat.cast_sum, Finset.mul_sum, Complex.exp_sum]`. Conclude with `Finset.prod_congr rfl fun s _ => hψ s`.
-/
theorem prod_psi {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (hE : Module.finrank F E = 2) {sig : E →ₐ[F] E}
    (A : (p : HeightOneSpectrum (𝓞 F)) → LocAt F E sig p) {l : ℕ} (hl : l.Prime) (y : E)
    (hy : IsIntegral ℤ y) (k : ℕ) :
    Set.Finite (Function.mulSupport fun p : HeightOneSpectrum (𝓞 F) =>
      (A p).psiE ((A p).ιE (y / (l : E) ^ k))) ∧
    ∏ᶠ p : HeightOneSpectrum (𝓞 F), (A p).psiE ((A p).ιE (y / (l : E) ^ k)) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ E (y / (l : E) ^ k) : ℚ) : ℂ)) := by
  classical
  have : Fact l.Prime := ⟨hl⟩
  have : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hl0 : (l : 𝓞 F) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hfin : {p : HeightOneSpectrum (𝓞 F) | resChar p = l}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {(l : 𝓞 F)}) (by simpa using hl0)).subset ?_
    intro p hp
    rw [Set.mem_setOf_eq, Ideal.dvd_span_singleton]
    exact (resChar_eq_iff p (A p).ellPrime.out hl).mp hp
  have hsupp : (Function.mulSupport fun p : HeightOneSpectrum (𝓞 F) =>
      (A p).psiE ((A p).ιE (y / (l : E) ^ k))) ⊆ {p | resChar p = l} := by
    intro p hp
    by_contra h
    exact hp (psi_eq_one hE (A p) hl h y hy k)
  refine ⟨hfin.subset hsupp, ?_⟩
  let S : Type := {p : HeightOneSpectrum (𝓞 F) | resChar p = l}
  letI : Fintype S := hfin.fintype
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := hfin.toFinset) (by simpa using hsupp),
    Finset.prod_subtype (F := (inferInstance : Fintype S)) hfin.toFinset
      (p := fun p => p ∈ {p : HeightOneSpectrum (𝓞 F) | resChar p = l}) (by simp)]
  set x := y / (l : E) ^ k with hx
  have hres : ∀ s : S, resChar s.1 = l := fun s => s.2
  have hF : ∀ p : HeightOneSpectrum (𝓞 F), Fact (resChar p).Prime := fun p => (A p).ellPrime
  choose alg hc hf ht using fun s : S =>
    transport (resChar s.1) l (hres s) (A s.1).Fp (A s.1).qlCont (A s.1).qlFin
  choose a ha hb hψ using fun s : S => psi_eq hE (A s.1) x
  choose n hn using ha
  simp_rw [ht] at hb
  have hlf : ∀ s : S, IsNonarchimedeanLocalField (A s.1).Fp := fun s => (A s.1).lf
  have : ∀ s : S, T2Space (A s.1).Fp := fun s => t2Space_isNonarchimedeanLocalField_singleBlock _
  have : ∀ s : S, CharZero (A s.1).Fp := fun s => (A s.1).char0
  have : ∀ s : S, ContinuousSMul ℚ_[l] (A s.1).Fp := fun s =>
    continuousSMul_of_algebraMap _ _ (hc s)
  have hsum := sum_local_trace (l := l) (S := S) Subtype.val Subtype.val_injective
    (fun I hI hlI => ⟨⟨⟨I, hI, fun h => hl0 (by simpa [h] using hlI)⟩,
      (resChar_eq_iff _ (hF _).out hl).mpr hlI⟩, rfl⟩)
    (fun s => (A s.1).Fp) (fun s => (A s.1).ιF) (fun s => {z | valuation _ z < 1})
    (fun s => (A s.1).dense) (fun s => isOpen_ball _)
    (fun s z => by
      have h := (A s.1).val 1 z
      rw [Valuation.Compatible.vle_iff_le (v := valuation _)] at h
      simp only [map_one] at h
      rw [Set.mem_setOf_eq, ← not_le, ← not_le, h])
    (fun s z hz => tendsto_pow_zero _ z hz) (Algebra.trace F E x)
  rw [Algebra.trace_trace] at hsum
  have hnorm : ‖((Algebra.trace ℚ E x - ∑ s, a s : ℚ) : ℚ_[l])‖ ≤ 1 := by
    push_cast
    rw [← hsum, ← Finset.sum_sub_distrib]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun s _ => hb s
  let N := k + ∑ s, n s
  choose m hm using fun s : S => exists_mul_pow_int (a s) l (n s) (by rw [hn s, hres s]) N
    ((Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)).trans
      (Nat.le_add_left _ _))
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (Algebra.isIntegral_trace (L := ℚ) hy)
  have hlq : (l : ℚ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have e1 : Algebra.trace ℚ E x = ((l : ℚ) ^ k)⁻¹ * r := by
    have : x = ((l : ℚ) ^ k)⁻¹ • y := by
      rw [hx, Algebra.smul_def]; simp [div_eq_inv_mul]
    rw [this, map_smul, ← hr]; simp
  obtain ⟨c, hc⟩ := exists_int_of_norm_le _ N (r * l ^ (∑ s, n s) - ∑ s, m s) (by
    rw [sub_mul, Finset.sum_mul, e1]
    simp_rw [hm]
    push_cast
    simp only [N, pow_add]
    field_simp) hnorm
  have e2 : Algebra.trace ℚ E x = ∑ s, a s + c := by linear_combination hc
  rw [e2, Rat.cast_add, mul_add, Complex.exp_add, exp_int, mul_one, Rat.cast_sum, Finset.mul_sum,
    Complex.exp_sum]
  exact Finset.prod_congr rfl fun s _ => hψ s

end GlobalTheory.ResidueCharacterDense
