import Mathlib
import Formalism.LocalRingCardinality.SpanPowerMembership.Adelic

noncomputable section

namespace Formalism.BasicNotions.Examples₂.LocF

open NumberField IsDedekindDomain HeightOneSpectrum WithZero

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

@[reducible] def vrel : ValuativeRel (v.adicCompletion F) :=
  .ofValuation (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)

/- English proof (translation)
The claim follows from `.ofValuation _`.
-/
theorem vcompat : letI := vrel v
    (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).Compatible := .ofValuation _

/- English proof (translation)
The claim follows from `Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot`.
-/
theorem finite_quot : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot

/- English proof (translation)
Use `finite_quot v` as an intermediate fact. Establish `h1 : IsDiscreteValuationRing (v.adicCompletionIntegers F)` using `inferInstance`. Establish `h2` using `adicInt_residue_finite (K := F) v`. Conclude with `Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mpr ⟨inferInstance, h1, h2⟩`.
-/
theorem proper : ProperSpace (v.adicCompletion F) := by
  have := finite_quot v
  have h1 : IsDiscreteValuationRing (v.adicCompletionIntegers F) := inferInstance
  have h2 := adicInt_residue_finite (K := F) v
  exact Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mpr
    ⟨inferInstance, h1, h2⟩

/- English proof (translation)
Set `_` to `vrel v`. Use `vcompat v` as an intermediate fact. Use `proper v` as an intermediate fact. Establish `h1 : IsValuativeTopology (v.adicCompletion F)` using `IsValuativeTopology.of_mem_nhds_iff_vle (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) (fun {s x} => Valued.mem_nhds)`. Establish `h2 : ValuativeRel.IsNontrivial (v.adicCompletion F)` using `(ValuativeRel.isNontrivial_iff_isNontrivial (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)).mpr inferInstance`.

Conclude with `{ }`.
-/
theorem isLocalField : letI := vrel v; IsNonarchimedeanLocalField (v.adicCompletion F) := by
  let _ := vrel v
  have := vcompat v
  have := proper v
  have h1 : IsValuativeTopology (v.adicCompletion F) :=
    IsValuativeTopology.of_mem_nhds_iff_vle (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)
      (fun {s x} => Valued.mem_nhds)
  have h2 : ValuativeRel.IsNontrivial (v.adicCompletion F) :=
    (ValuativeRel.isNontrivial_iff_isNontrivial
      (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)).mpr inferInstance
  exact { }

section Ql

variable (l : ℕ) [hl : Fact l.Prime] (hv : (l : 𝓞 F) ∈ v.asIdeal)

/- English proof (translation)
Introduce `hd`. Establish `hu` using `PadicInt.isUnit_den q h`. Rewrite `hu` using `[PadicInt.isUnit_iff]`. Establish `: ‖((q.den : ℤ) : ℤ_[l])‖ < 1` using `(PadicInt.norm_int_lt_one_iff_dvd _).mpr (Int.natCast_dvd_natCast.mpr hd)`. Rewrite `this` using `[Int.cast_natCast]`.

Conclude with `absurd hu this.ne`.
-/
theorem not_dvd_den (q : ℚ) (h : ‖(q : ℚ_[l])‖ ≤ 1) : ¬ l ∣ q.den := by
  intro hd
  have hu := PadicInt.isUnit_den q h
  rw [PadicInt.isUnit_iff] at hu
  have : ‖((q.den : ℤ) : ℤ_[l])‖ < 1 :=
    (PadicInt.norm_int_lt_one_iff_dvd _).mpr (Int.natCast_dvd_natCast.mpr hd)
  rw [Int.cast_natCast] at this
  exact absurd hu this.ne

/- English proof (translation)
Rewrite using `[map_natCast, map_natCast]`.
-/
theorem norm_nat (n : ℕ) : ‖(n : v.adicCompletion F)‖ =
    ‖FinitePlace.embedding v (algebraMap (𝓞 F) F (n : 𝓞 F))‖ := by
  rw [map_natCast, map_natCast]

/- English proof (translation)
Use `FinitePlace.norm_le_one (K := F) v (n : 𝓞 F)` as an intermediate fact. Rewrite `this` using `[map_intCast, map_intCast]`. Then use the resulting hypothesis.
-/
theorem norm_int_le (n : ℤ) : ‖(n : v.adicCompletion F)‖ ≤ 1 := by
  have := FinitePlace.norm_le_one (K := F) v (n : 𝓞 F)
  rwa [map_intCast, map_intCast] at this

include hv in
/- English proof (translation)
Rewrite using `[norm_nat]`. Conclude with `(FinitePlace.norm_lt_one_iff_mem F v _).mpr hv`.
-/
theorem norm_l_lt : ‖(l : v.adicCompletion F)‖ < 1 := by
  rw [norm_nat]; exact (FinitePlace.norm_lt_one_iff_mem F v _).mpr hv

include hv in
/- English proof (translation)
Rewrite using `[norm_nat]`. Use `(FinitePlace.norm_eq_one_iff_notMem F v _).mpr (fun hn => v.isPrime.ne_top ?_)` and prove the remaining obligations. Establish `hc : IsCoprime (l : 𝓞 F) (n : 𝓞 F)` using `Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hl.out).mpr h)`. Take `⟨a, b, hab⟩` from `hc`. Rewrite using `[Ideal.eq_top_iff_one, ← hab]`.

Conclude with `add_mem (Ideal.mul_mem_left _ _ hv) (Ideal.mul_mem_left _ _ hn)`.
-/
theorem norm_nat_eq_one (n : ℕ) (h : ¬ l ∣ n) : ‖(n : v.adicCompletion F)‖ = 1 := by
  rw [norm_nat]
  refine (FinitePlace.norm_eq_one_iff_notMem F v _).mpr (fun hn => v.isPrime.ne_top ?_)
  have hc : IsCoprime (l : 𝓞 F) (n : 𝓞 F) :=
    Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hl.out).mpr h)
  obtain ⟨a, b, hab⟩ := hc
  rw [Ideal.eq_top_iff_one, ← hab]
  exact add_mem (Ideal.mul_mem_left _ _ hv) (Ideal.mul_mem_left _ _ hn)

instance : CharZero (v.adicCompletion F) := algebraRat.charZero _

include hv in
/- English proof (translation)
Rewrite using `[Rat.cast_def, norm_div, norm_nat_eq_one v l hv _ (not_dvd_den l q h), div_one]`. Conclude with `norm_int_le v _`.
-/
theorem norm_rat_le (q : ℚ) (h : ‖(q : ℚ_[l])‖ ≤ 1) : ‖(q : v.adicCompletion F)‖ ≤ 1 := by
  rw [Rat.cast_def, norm_div, norm_nat_eq_one v l hv _ (not_dvd_den l q h), div_one]
  exact norm_int_le v _

def QL (_l : ℕ) : Type := ℚ
instance : Field (QL l) := inferInstanceAs (Field ℚ)

def iQ : QL l →+* ℚ_[l] := Rat.castHom ℚ_[l]
instance : PseudoMetricSpace (QL l) := PseudoMetricSpace.induced (iQ l) inferInstance

def fQ : QL l →+* v.adicCompletion F := Rat.castHom _

/- English proof (translation)
Assemble the required witnesses or components as `⟨rfl⟩`.
-/
theorem iQ_ind : IsUniformInducing (iQ l) := ⟨rfl⟩
/- English proof (translation)
The claim follows from `Padic.denseRange_ratCast l`.
-/
theorem iQ_dense : DenseRange (iQ l) := Padic.denseRange_ratCast l

include hv in
/- English proof (translation)
Rewrite using `[Metric.uniformContinuous_iff]`. Introduce `ε hε`. Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one hε (norm_l_lt v l hv)`. Establish `hl0 : (l : ℚ) ≠ 0` using `Nat.cast_ne_zero.mpr hl.out.ne_zero`. Establish `hlp : (0 : ℝ) < ‖(l : ℚ_[l])‖ ^ n` using `pow_pos (norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.out.ne_zero)) n`.

Use `⟨‖(l : ℚ_[l])‖ ^ n, hlp, fun {a b} hab => ?_⟩` and prove the remaining obligations. Set `q : ℚ` to `(show ℚ from a) - (show ℚ from b)`. Establish `h1 : ‖(q : ℚ_[l])‖ < ‖(l : ℚ_[l])‖ ^ n`. Establish `: dist a b = ‖iQ l a - iQ l b‖` using `dist_eq_norm (iQ l a) (iQ l b)`. Rewrite `hab` using `[this, ← map_sub]`.

Conclude with `hab`. Establish `h2 : ‖((q / (l : ℚ) ^ n : ℚ) : ℚ_[l])‖ ≤ 1`. Use `push_cast`. Rewrite using `[norm_div, norm_pow, div_le_one hlp]`. Conclude with `h1.le`.

Establish `h3` using `norm_rat_le v l hv _ h2`. Establish `hlv : (0 : ℝ) < ‖(l : v.adicCompletion F)‖ ^ n` using `pow_pos (norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.out.ne_zero)) n`. Move the coercions through the operations in `at h3`. Rewrite `h3` using `[norm_div, norm_pow, div_le_one hlv]`. Rewrite using `[dist_eq_norm, ← map_sub]`.

Conclude with `lt_of_le_of_lt h3 hn`.
-/
theorem fQ_uc : UniformContinuous (fQ v l) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (norm_l_lt v l hv)
  have hl0 : (l : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hl.out.ne_zero
  have hlp : (0 : ℝ) < ‖(l : ℚ_[l])‖ ^ n :=
    pow_pos (norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.out.ne_zero)) n
  refine ⟨‖(l : ℚ_[l])‖ ^ n, hlp, fun {a b} hab => ?_⟩
  let q : ℚ := (show ℚ from a) - (show ℚ from b)
  have h1 : ‖(q : ℚ_[l])‖ < ‖(l : ℚ_[l])‖ ^ n := by
    have : dist a b = ‖iQ l a - iQ l b‖ := dist_eq_norm (iQ l a) (iQ l b)
    rw [this, ← map_sub] at hab
    exact hab
  have h2 : ‖((q / (l : ℚ) ^ n : ℚ) : ℚ_[l])‖ ≤ 1 := by
    push_cast
    rw [norm_div, norm_pow, div_le_one hlp]
    exact h1.le
  have h3 := norm_rat_le v l hv _ h2
  have hlv : (0 : ℝ) < ‖(l : v.adicCompletion F)‖ ^ n :=
    pow_pos (norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.out.ne_zero)) n
  push_cast at h3
  rw [norm_div, norm_pow, div_le_one hlv] at h3
  rw [dist_eq_norm, ← map_sub]
  exact lt_of_le_of_lt h3 hn

def emb : ℚ_[l] →+* v.adicCompletion F :=
  IsDenseInducing.extendRingHom (iQ_ind l) (iQ_dense l) (fQ_uc v l hv)

/- English proof (translation)
The claim follows from `(uniformContinuous_uniformly_extend (iQ_ind l) (iQ_dense l) (fQ_uc v l hv)).continuous`.
-/
theorem emb_cont : Continuous (emb v l hv) :=
  (uniformContinuous_uniformly_extend (iQ_ind l) (iQ_dense l) (fQ_uc v l hv)).continuous

open scoped TensorProduct in
/- English proof (translation)
Set `_` to `(emb v l hv).toAlgebra`. Establish `: ContinuousSMul ℚ_[l] (v.adicCompletion F)` using `continuousSMul_of_algebraMap _ _ (emb_cont v l hv)`. Establish `: IsScalarTower ℚ ℚ_[l] (v.adicCompletion F)` using `IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)`. Set `Φ : ℚ_[l] ⊗[ℚ] F →ₗ[ℚ_[l]] v.adicCompletion F` to `(Algebra.TensorProduct.lift (Algebra.ofId ℚ_[l] (v.adicCompletion F)) (algebraMap F (v.adicCompletion F)).toRatAlgHom (fun _ _ => Commute.all _ _)).toLinearMap`. Establish `hd : DenseRange Φ`.

Apply `(v.denseRange_algebraMap F).mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, rfl⟩`. Use `⟨1 ⊗ₜ x, ?_⟩` and prove the remaining obligations. Conclude with `(Algebra.TensorProduct.lift_tmul _ _ (fun _ _ => Commute.all _ _) 1 x).trans (by rw [map_one, one_mul]; rfl)`. Conclude with `Module.Finite.of_surjective Φ (by`.

Rewrite using `[← Set.range_eq_univ, ← Φ.coe_range, ← Φ.range.closed_of_finiteDimensional.closure_eq]`. Conclude with `hd.closure_range)`.
-/
theorem emb_finite : letI := (emb v l hv).toAlgebra
    FiniteDimensional ℚ_[l] (v.adicCompletion F) := by
  let _ := (emb v l hv).toAlgebra
  have : ContinuousSMul ℚ_[l] (v.adicCompletion F) :=
    continuousSMul_of_algebraMap _ _ (emb_cont v l hv)
  have : IsScalarTower ℚ ℚ_[l] (v.adicCompletion F) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let Φ : ℚ_[l] ⊗[ℚ] F →ₗ[ℚ_[l]] v.adicCompletion F :=
    (Algebra.TensorProduct.lift (Algebra.ofId ℚ_[l] (v.adicCompletion F))
      (algebraMap F (v.adicCompletion F)).toRatAlgHom (fun _ _ => Commute.all _ _)).toLinearMap
  have hd : DenseRange Φ := by
    apply (v.denseRange_algebraMap F).mono
    rintro _ ⟨x, rfl⟩
    refine ⟨1 ⊗ₜ x, ?_⟩
    exact (Algebra.TensorProduct.lift_tmul _ _ (fun _ _ => Commute.all _ _) 1 x).trans (by rw [map_one, one_mul]; rfl)
  exact Module.Finite.of_surjective Φ (by
    rw [← Set.range_eq_univ, ← Φ.coe_range, ← Φ.range.closed_of_finiteDimensional.closure_eq]
    exact hd.closure_range)

/- English proof (translation)
Establish `hl1 : ‖(l : ℚ_[l])‖ < 1` using `Padic.norm_p_lt_one`. Establish `hl0 : (l : ℚ_[l]) ≠ 0` using `Nat.cast_ne_zero.mpr hl.out.ne_zero`. Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one (show 0 < (‖x‖ + 1)⁻¹ by positivity) hl1`. Establish `hz : ‖(l : ℚ_[l]) ^ n * x‖ ≤ 1`. Rewrite using `[norm_mul, norm_pow]`.

Establish `h1 : ‖(l : ℚ_[l])‖ ^ n * (‖x‖ + 1) ≤ 1`. Rewrite using `[← le_div_iff₀ (by positivity), one_div]; exact hn.le`. Use polynomial arithmetic with `[pow_nonneg (norm_nonneg (l : ℚ_[l])) n]`. Set `z : ℤ_[l]` to `⟨_, hz⟩`. Take `⟨e, he⟩` from `Ideal.mem_span_singleton.mp (PadicInt.appr_spec n z)`.

Use `⟨(z.appr n : ℚ) / (l : ℚ) ^ n, ?_, ?_⟩` and prove the remaining obligations. Establish `: ((z.appr n : ℚ) / (l : ℚ) ^ n).den ∣ l ^ n`. Establish `h` using `Rat.den_dvd (z.appr n : ℤ) ((l ^ n : ℕ) : ℤ)`. Rewrite `h` using `[Rat.divInt_eq_div]`. Move the coercions through the operations in `at h`.

Conclude with `h` after adjusting the coercions. Take `⟨k, -, hk⟩` from `(Nat.dvd_prime_pow hl.out).mp this`. Conclude with `⟨k, hk⟩`. Establish `h` using `congrArg (fun t : ℤ_[l] => (t : ℚ_[l])) he`. Establish `hzc : (z : ℚ_[l]) = (l : ℚ_[l]) ^ n * x` using `rfl`.

Simplify using `only [PadicInt.coe_sub, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast, hzc] at h`. Use `push_cast`. Establish `: x - (z.appr n : ℚ_[l]) / (l : ℚ_[l]) ^ n = (e : ℚ_[l])`. Clear the denominators using the available nonvanishing facts. Take the linear combination `h`.

Rewrite using `[this]`. Conclude with `e.2`.
-/
theorem exists_frac (x : ℚ_[l]) : ∃ a : ℚ, (∃ n : ℕ, a.den = l ^ n) ∧ ‖x - (a : ℚ_[l])‖ ≤ 1 := by
  have hl1 : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
  have hl0 : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr hl.out.ne_zero
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < (‖x‖ + 1)⁻¹ by positivity) hl1
  have hz : ‖(l : ℚ_[l]) ^ n * x‖ ≤ 1 := by
    rw [norm_mul, norm_pow]
    have h1 : ‖(l : ℚ_[l])‖ ^ n * (‖x‖ + 1) ≤ 1 := by
      rw [← le_div_iff₀ (by positivity), one_div]; exact hn.le
    nlinarith [pow_nonneg (norm_nonneg (l : ℚ_[l])) n]
  let z : ℤ_[l] := ⟨_, hz⟩
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec n z)
  refine ⟨(z.appr n : ℚ) / (l : ℚ) ^ n, ?_, ?_⟩
  · have : ((z.appr n : ℚ) / (l : ℚ) ^ n).den ∣ l ^ n := by
      have h := Rat.den_dvd (z.appr n : ℤ) ((l ^ n : ℕ) : ℤ)
      rw [Rat.divInt_eq_div] at h
      push_cast at h
      exact_mod_cast h
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hl.out).mp this
    exact ⟨k, hk⟩
  · have h := congrArg (fun t : ℤ_[l] => (t : ℚ_[l])) he
    have hzc : (z : ℚ_[l]) = (l : ℚ_[l]) ^ n * x := rfl
    simp only [PadicInt.coe_sub, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast, hzc] at h
    push_cast
    have : x - (z.appr n : ℚ_[l]) / (l : ℚ_[l]) ^ n = (e : ℚ_[l]) := by
      field_simp
      linear_combination h
    rw [this]
    exact e.2

/- English proof (translation)
Take `⟨k, -, hk⟩` from `(Nat.dvd_prime_pow hl.out).mp hd`. Establish `hnd` using `not_dvd_den l b h`. Establish `: k = 0`. Assume the negation of the conclusion as `hk0`. Conclude with `hnd (hk ▸ dvd_pow_self l hk0)`.

Rewrite `hk` using `[this, pow_zero]`. Conclude with `⟨b.num, (Rat.coe_int_num_of_den_eq_one hk).symm⟩`.
-/
theorem int_of_frac (b : ℚ) (n : ℕ) (hd : b.den ∣ l ^ n) (h : ‖(b : ℚ_[l])‖ ≤ 1) : ∃ z : ℤ, b = z := by
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hl.out).mp hd
  have hnd := not_dvd_den l b h
  have : k = 0 := by
    by_contra hk0
    exact hnd (hk ▸ dvd_pow_self l hk0)
  rw [this, pow_zero] at hk
  exact ⟨b.num, (Rat.coe_int_num_of_den_eq_one hk).symm⟩

def frac (x : ℚ_[l]) : ℚ := (exists_frac l x).choose

/- English proof (translation)
Establish `: (a : ℂ) = b + z`. Establish `h' : a = b + z` using `by linarith`. Rewrite using `[h']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, mul_add, Complex.exp_add, mul_comm _ (z : ℂ), Complex.exp_int_mul_two_pi_mul_I, mul_one]`.
-/
theorem exp_eq_of_int (a b : ℚ) (z : ℤ) (h : a - b = z) :
    Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)) = Complex.exp (2 * Real.pi * Complex.I * (b : ℂ)) := by
  have : (a : ℂ) = b + z := by
    have h' : a = b + z := by linarith
    rw [h']; push_cast; ring
  rw [this, mul_add, Complex.exp_add, mul_comm _ (z : ℂ), Complex.exp_int_mul_two_pi_mul_I, mul_one]

def psi0 : AddChar ℚ_[l] ℂ where
  toFun x := Complex.exp (2 * Real.pi * Complex.I * (frac l x : ℂ))
  map_zero_eq_one' := by
    obtain ⟨⟨n, hn⟩, h⟩ := (exists_frac l 0).choose_spec
    obtain ⟨z, hz⟩ := int_of_frac l (frac l 0) n (hn ▸ dvd_rfl) (by simpa [frac] using h)
    rw [exp_eq_of_int (frac l 0) 0 z (by simpa using hz)]
    simp
  map_add_eq_mul' x y := by
    obtain ⟨⟨n, hn⟩, h⟩ := (exists_frac l x).choose_spec
    obtain ⟨⟨m, hm⟩, h'⟩ := (exists_frac l y).choose_spec
    obtain ⟨⟨k, hk⟩, h''⟩ := (exists_frac l (x + y)).choose_spec
    have hd : (frac l (x + y) - (frac l x + frac l y)).den ∣ l ^ (k + (n + m)) := by
      refine (Rat.sub_den_dvd _ _).trans ?_
      rw [pow_add, pow_add]
      refine mul_dvd_mul (hk ▸ dvd_rfl) ((Rat.add_den_dvd _ _).trans ?_)
      exact mul_dvd_mul (hn ▸ dvd_rfl) (hm ▸ dvd_rfl)
    have hn1 : ‖((frac l (x + y) - (frac l x + frac l y) : ℚ) : ℚ_[l])‖ ≤ 1 := by
      have e : ((frac l (x + y) - (frac l x + frac l y) : ℚ) : ℚ_[l]) =
          ((x - frac l x) + (y - frac l y)) + -((x + y) - frac l (x + y)) := by push_cast; ring
      rw [e]
      refine (Padic.nonarchimedean _ _).trans (max_le ((Padic.nonarchimedean _ _).trans (max_le h h')) ?_)
      rw [norm_neg]; exact h''
    obtain ⟨z, hz⟩ := int_of_frac l _ _ hd hn1
    rw [exp_eq_of_int _ _ z hz, ← Complex.exp_add]
    congr 1
    push_cast; ring

/- English proof (translation)
Assemble the required witnesses or components as `⟨frac l x, (exists_frac l x).choose_spec.1, (exists_frac l x).choose_spec.2, rfl⟩`.
-/
theorem padicCharacter_spec (x : ℚ_[l]) : ∃ a : ℚ, (∃ n : ℕ, a.den = l ^ n) ∧ ‖x - (a : ℚ_[l])‖ ≤ 1 ∧
    psi0 l x = Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)) :=
  ⟨frac l x, (exists_frac l x).choose_spec.1, (exists_frac l x).choose_spec.2, rfl⟩

end Ql

end Formalism.BasicNotions.Examples₂.LocF
