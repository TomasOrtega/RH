import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.TrBase
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.ExistsEqEllMul

noncomputable section

open IsDedekindDomain NumberField TensorProduct ValuativeRel

namespace PI.ProdFormulaE.Tr

variable {F : Type} [Field F] [NumberField F] {ℓ : ℕ} [Fact ℓ.Prime] {ι : Type}

/- English proof (translation)
Conclude with `(Valuation.Compatible.vle_iff_le (v := valuation K) x y)`.
-/
lemma vle_iff' {K : Type*} [Field K] [ValuativeRel K] (x y : K) :
    x ≤ᵥ y ↔ valuation K x ≤ valuation K y := by
  exact (Valuation.Compatible.vle_iff_le (v := valuation K) x y)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Use `push_cast`. Conclude with `Valuation.map_add_le _ ih (by simp)`.
-/
lemma valuation_natCast_le_one' {K : Type*} [Field K] [ValuativeRel K] (n : ℕ) :
    valuation K (n : K) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact Valuation.map_add_le _ ih (by simp)

/- English proof (translation)
Establish `h` using `IsValuativeTopology.isClosed_closedBall (R := K) (v := valuation K) 1`. Use `first`. Consider the case `(convert h using 3 with x; simp)`. Consider the case `simpa [Valuation.restrict_le_one_iff] using h`. Consider the case `simpa using h`.
-/
private theorem isClosed_setOf_valuation_le_one {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : IsClosed {x : K | valuation K x ≤ 1} := by
  have h := IsValuativeTopology.isClosed_closedBall (R := K) (v := valuation K) 1
  first
  | (convert h using 3 with x; simp)
  | simpa [Valuation.restrict_le_one_iff] using h
  | simpa using h

/- English proof (translation)
Set `c' : ℤ_[ℓ]` to `⟨c, hc⟩`. Express the relevant statement in the definitionally equal form `valuation (D.K i) (algebraMap ℚ_[ℓ] (D.K i) (c' : ℚ_[ℓ])) ≤ 1`. Use `PadicInt.denseRange_natCast.induction_on c' (p := fun z : ℤ_[ℓ] => valuation (D.K i) (algebraMap ℚ_[ℓ] (D.K i) (z : ℚ_[ℓ])) ≤ 1) ?_ ?_` and prove the remaining obligations. Conclude with `isClosed_setOf_valuation_le_one.preimage ((D.cont i).comp continuous_subtype_val)`. Introduce `n`.

Simplify using `using valuation_natCast_le_one' (K := D.K i) n`.
-/
lemma LocFam.valuation_algebraMap_le_one (D : LocFam F ℓ ι) (i : ι) (c : ℚ_[ℓ]) (hc : ‖c‖ ≤ 1) :
    valuation (D.K i) (algebraMap ℚ_[ℓ] (D.K i) c) ≤ 1 := by
  let c' : ℤ_[ℓ] := ⟨c, hc⟩
  change valuation (D.K i) (algebraMap ℚ_[ℓ] (D.K i) (c' : ℚ_[ℓ])) ≤ 1
  refine PadicInt.denseRange_natCast.induction_on c'
    (p := fun z : ℤ_[ℓ] => valuation (D.K i) (algebraMap ℚ_[ℓ] (D.K i) (z : ℚ_[ℓ])) ≤ 1) ?_ ?_
  · exact isClosed_setOf_valuation_le_one.preimage ((D.cont i).comp continuous_subtype_val)
  · intro n
    simpa using valuation_natCast_le_one' (K := D.K i) n

/- English proof (translation)
Establish `h` using `(D.val i (x : F) 1).2 (by simpa using (D.P i).valuation_le_one x)`. Simplify `h` using `[vle_iff']`.
-/
lemma LocFam.valuation_ιF_le_one (D : LocFam F ℓ ι) (i : ι) (x : 𝓞 F) :
    valuation (D.K i) (D.ιF i (x : F)) ≤ 1 := by
  have h := (D.val i (x : F) 1).2 (by simpa using (D.P i).valuation_le_one x)
  simpa [vle_iff'] using h

/- English proof (translation)
Use `set b := integralBasis F with hb_def`. Use `set bZ := RingOfIntegers.basis F with hbZ`. Establish `hbb : ∀ k, b k = algebraMap (𝓞 F) F (bZ k)` using `fun k => by`. Rewrite using `[hb_def, hbZ, integralBasis_apply]`. Establish `hw : ∀ k i, D.Φ (1 ⊗ₜ b k) i = D.ιF i (b k)` using `fun k i => by`.

Rewrite using `[LocFam.Φ_tmul, map_one, one_mul]`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`.

Take `⟨k1, hk1⟩` from `hne`. Take `⟨k0, -, hk0⟩` from `Finset.exists_max_image Finset.univ (fun k => ‖g k‖) ⟨k1, Finset.mem_univ _⟩`. Establish `hg0 : g k0 ≠ 0`. Introduce `h`. Establish `h'` using `hk0 k1 (Finset.mem_univ _)`.

Rewrite `h'` using `[h, norm_zero]`. Conclude with `hk1 (norm_le_zero_iff.1 h')`. Use `set c : _ → ℚ_[ℓ] := fun k => g k / g k0 with hc_def`. Establish `hc1 : ∀ k, ‖c k‖ ≤ 1` using `fun k => by`. Simplify using `only [hc_def, norm_div]`.

Conclude with `div_le_one_of_le₀ (hk0 k (Finset.mem_univ _)) (norm_nonneg _)`. Establish `hck0 : c k0 = 1` using `div_self hg0`. Establish `hrel : ∀ i, ∑ k, algebraMap ℚ_[ℓ] (D.K i) (c k) * D.ιF i (b k) = 0`. Introduce `i`. Establish `h` using `congrFun hg i`.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, hw, Pi.zero_apply] at h`. Establish `h2` using `congrArg (fun y => algebraMap ℚ_[ℓ] (D.K i) (g k0)⁻¹ * y) h`. Simplify using `only [mul_zero, Finset.mul_sum, Algebra.smul_def] at h2`. Rewrite using `[← h2]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Simplify using `only [hc_def, div_eq_inv_mul, map_mul, mul_assoc]`. Use `choose m hm using fun k => hB (c k) (hc1 k)`. Use `set d : _ → ℚ_[ℓ] := fun k => (c k - m k) / ℓ with hd_def`. Establish `hd1 : ∀ k, ‖d k‖ ≤ 1` using `hm`. Establish `hℓ0 : (ℓ : ℚ_[ℓ]) ≠ 0` using `Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero`.

Establish `hcd : ∀ k, c k - m k = ℓ * d k` using `fun k => by`. Simplify using `only [hd_def]`. Clear the denominators using the available nonvanishing facts. Use `set X : 𝓞 F := ∑ k, m k • bZ k with hX_def`. Establish `hXF : ((X : 𝓞 F) : F) = ∑ k, (m k : F) * b k` using `by first`.

Consider the case `(rw [hX_def]; simp [hbb, zsmul_eq_mul])`. Consider the case `(push_cast [hX_def, hbb, zsmul_eq_mul]; rfl)`. Establish `hval : ∀ v : HeightOneSpectrum (𝓞 F), (ℓ : 𝓞 F) ∈ v.asIdeal → v.valuation F (X : F) ≤ v.valuation F (ℓ : F)`. Introduce `v hv`. Take `⟨i, rfl⟩` from `(hD.2 v).2 hv`.

Rewrite using `[← D.val i, vle_iff']`. Establish `hterm : ∀ k, D.ιF i ((m k : F) * b k) = algebraMap ℚ_[ℓ] (D.K i) (c k) * D.ιF i (b k) - (ℓ : D.K i) * (algebraMap ℚ_[ℓ] (D.K i) (d k) * D.ιF i (b k))`. Introduce `k`. Establish `e : (m k : ℚ_[ℓ]) = c k - ℓ * d k` using `by rw [← hcd]; ring`. Establish `e' : ((m k : ℤ) : D.K i) = algebraMap ℚ_[ℓ] (D.K i) (c k) - (ℓ : D.K i) * algebraMap ℚ_[ℓ] (D.K i) (d k)`.

Rewrite using `[← map_intCast (algebraMap ℚ_[ℓ] (D.K i)), e, map_sub, map_mul, map_natCast]`. Rewrite using `[map_mul, map_intCast, e']`. Expand and normalize the polynomial expressions, which then agree. Establish `hιX : D.ιF i (X : F) = -((ℓ : D.K i) * ∑ k, algebraMap ℚ_[ℓ] (D.K i) (d k) * D.ιF i (b k))`. Rewrite using `[hXF, map_sum, Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_sub_distrib, hrel i, Finset.mul_sum]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsum : valuation (D.K i) (∑ k, algebraMap ℚ_[ℓ] (D.K i) (d k) * D.ιF i (b k)) ≤ 1`. Use `Valuation.map_sum_le _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hbb]`. Conclude with `mul_le_one' (LocFam.valuation_algebraMap_le_one D i _ (hd1 k)) (LocFam.valuation_ιF_le_one D i (bZ k))`.

Rewrite using `[hιX, Valuation.map_neg, map_mul, map_natCast (D.ιF i) ℓ]`. Use `first`. Consider the case `exact mul_le_of_le_one_right' hsum`. Consider the case `exact mul_le_of_le_one_right₀ hsum`. Consider the case `(calc _ ≤ valuation (D.K i) (ℓ : D.K i) * 1 := by gcongr _ = _ := mul_one _)`.

Take `⟨Z, hZ⟩` from `hA X hval`. Establish `hrepr : ∀ k, bZ.repr X k = m k` using `fun k => by`. Rewrite using `[hX_def, bZ.repr_sum_self]`. Establish `hmk : m k0 = ℓ * bZ.repr Z k0`. Establish `h` using `congrArg (fun y => bZ.repr y k0) hZ`.

Simplify using `only [hrepr] at h`. Rewrite using `[h]`. Establish `e : ((ℓ : 𝓞 F) * Z) = (ℓ : ℤ) • Z` using `by rw [zsmul_eq_mul]; push_cast; rfl`. Rewrite using `[e, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul]`. Establish `e` using `hcd k0`.

Rewrite `e` using `[hck0, hmk]`. Move the coercions through the operations in `at e`. Establish `h1 : (1 : ℚ_[ℓ]) = ℓ * (((bZ.repr Z k0 : ℤ) : ℚ_[ℓ]) + d k0)` using `by linear_combination e`. Establish `hn` using `congrArg norm h1`. Rewrite `hn` using `[norm_one, norm_mul]`.

Establish `hlt : ‖(ℓ : ℚ_[ℓ])‖ < 1` using `Padic.norm_p_lt_one`. Establish `hle : ‖((bZ.repr Z k0 : ℤ) : ℚ_[ℓ]) + d k0‖ ≤ 1` using `(Padic.nonarchimedean _ _).trans (max_le (Padic.norm_int_le_one _) (hd1 k0))`. Use polynomial arithmetic with `[norm_nonneg (ℓ : ℚ_[ℓ]), norm_nonneg (((bZ.repr Z k0 : ℤ) : ℚ_[ℓ]) + d k0)]`.
-/
theorem LocFam.linearIndependent [Fintype ι] (D : LocFam F ℓ ι) (hD : D.Over)
    (hA : ∀ X : 𝓞 F, (∀ v : HeightOneSpectrum (𝓞 F), (ℓ : 𝓞 F) ∈ v.asIdeal →
      v.valuation F (X : F) ≤ v.valuation F (ℓ : F)) → ∃ Z : 𝓞 F, X = ℓ * Z)
    (hB : ∀ c : ℚ_[ℓ], ‖c‖ ≤ 1 → ∃ m : ℤ, ‖(c - m) / ℓ‖ ≤ 1) :
    LinearIndependent ℚ_[ℓ] (fun k => D.Φ (1 ⊗ₜ integralBasis F k)) := by
  classical
  set b := integralBasis F with hb_def
  set bZ := RingOfIntegers.basis F with hbZ
  have hbb : ∀ k, b k = algebraMap (𝓞 F) F (bZ k) := fun k => by
    rw [hb_def, hbZ, integralBasis_apply]
  have hw : ∀ k i, D.Φ (1 ⊗ₜ b k) i = D.ιF i (b k) := fun k i => by
    rw [LocFam.Φ_tmul, map_one, one_mul]
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  push_neg at hne
  obtain ⟨k1, hk1⟩ := hne
  obtain ⟨k0, -, hk0⟩ := Finset.exists_max_image Finset.univ (fun k => ‖g k‖) ⟨k1, Finset.mem_univ _⟩
  have hg0 : g k0 ≠ 0 := by
    intro h
    have h' := hk0 k1 (Finset.mem_univ _)
    rw [h, norm_zero] at h'
    exact hk1 (norm_le_zero_iff.1 h')
  set c : _ → ℚ_[ℓ] := fun k => g k / g k0 with hc_def
  have hc1 : ∀ k, ‖c k‖ ≤ 1 := fun k => by
    simp only [hc_def, norm_div]
    exact div_le_one_of_le₀ (hk0 k (Finset.mem_univ _)) (norm_nonneg _)
  have hck0 : c k0 = 1 := div_self hg0
  have hrel : ∀ i, ∑ k, algebraMap ℚ_[ℓ] (D.K i) (c k) * D.ιF i (b k) = 0 := by
    intro i
    have h := congrFun hg i
    simp only [Finset.sum_apply, Pi.smul_apply, hw, Pi.zero_apply] at h
    have h2 := congrArg (fun y => algebraMap ℚ_[ℓ] (D.K i) (g k0)⁻¹ * y) h
    simp only [mul_zero, Finset.mul_sum, Algebra.smul_def] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hc_def, div_eq_inv_mul, map_mul, mul_assoc]
  choose m hm using fun k => hB (c k) (hc1 k)
  set d : _ → ℚ_[ℓ] := fun k => (c k - m k) / ℓ with hd_def
  have hd1 : ∀ k, ‖d k‖ ≤ 1 := hm
  have hℓ0 : (ℓ : ℚ_[ℓ]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero
  have hcd : ∀ k, c k - m k = ℓ * d k := fun k => by
    simp only [hd_def]
    field_simp
  set X : 𝓞 F := ∑ k, m k • bZ k with hX_def
  have hXF : ((X : 𝓞 F) : F) = ∑ k, (m k : F) * b k := by
    first
    | (rw [hX_def]; simp [hbb, zsmul_eq_mul])
    | (push_cast [hX_def, hbb, zsmul_eq_mul]; rfl)
  have hval : ∀ v : HeightOneSpectrum (𝓞 F), (ℓ : 𝓞 F) ∈ v.asIdeal →
      v.valuation F (X : F) ≤ v.valuation F (ℓ : F) := by
    intro v hv
    obtain ⟨i, rfl⟩ := (hD.2 v).2 hv
    rw [← D.val i, vle_iff']
    have hterm : ∀ k, D.ιF i ((m k : F) * b k) = algebraMap ℚ_[ℓ] (D.K i) (c k) * D.ιF i (b k)
        - (ℓ : D.K i) * (algebraMap ℚ_[ℓ] (D.K i) (d k) * D.ιF i (b k)) := by
      intro k
      have e : (m k : ℚ_[ℓ]) = c k - ℓ * d k := by rw [← hcd]; ring
      have e' : ((m k : ℤ) : D.K i) = algebraMap ℚ_[ℓ] (D.K i) (c k)
          - (ℓ : D.K i) * algebraMap ℚ_[ℓ] (D.K i) (d k) := by
        rw [← map_intCast (algebraMap ℚ_[ℓ] (D.K i)), e, map_sub, map_mul, map_natCast]
      rw [map_mul, map_intCast, e']
      ring
    have hιX : D.ιF i (X : F) =
        -((ℓ : D.K i) * ∑ k, algebraMap ℚ_[ℓ] (D.K i) (d k) * D.ιF i (b k)) := by
      rw [hXF, map_sum, Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_sub_distrib, hrel i,
        Finset.mul_sum]
      ring
    have hsum : valuation (D.K i) (∑ k, algebraMap ℚ_[ℓ] (D.K i) (d k) * D.ιF i (b k)) ≤ 1 := by
      refine Valuation.map_sum_le _ fun k _ => ?_
      rw [map_mul, hbb]
      exact mul_le_one' (LocFam.valuation_algebraMap_le_one D i _ (hd1 k))
        (LocFam.valuation_ιF_le_one D i (bZ k))
    rw [hιX, Valuation.map_neg, map_mul, map_natCast (D.ιF i) ℓ]
    first
    | exact mul_le_of_le_one_right' hsum
    | exact mul_le_of_le_one_right₀ hsum
    | (calc _ ≤ valuation (D.K i) (ℓ : D.K i) * 1 := by gcongr
        _ = _ := mul_one _)
  obtain ⟨Z, hZ⟩ := hA X hval
  have hrepr : ∀ k, bZ.repr X k = m k := fun k => by
    rw [hX_def, bZ.repr_sum_self]
  have hmk : m k0 = ℓ * bZ.repr Z k0 := by
    have h := congrArg (fun y => bZ.repr y k0) hZ
    simp only [hrepr] at h
    rw [h]
    have e : ((ℓ : 𝓞 F) * Z) = (ℓ : ℤ) • Z := by rw [zsmul_eq_mul]; push_cast; rfl
    rw [e, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul]
  have e := hcd k0
  rw [hck0, hmk] at e
  push_cast at e
  have h1 : (1 : ℚ_[ℓ]) = ℓ * (((bZ.repr Z k0 : ℤ) : ℚ_[ℓ]) + d k0) := by linear_combination e
  have hn := congrArg norm h1
  rw [norm_one, norm_mul] at hn
  have hlt : ‖(ℓ : ℚ_[ℓ])‖ < 1 := Padic.norm_p_lt_one
  have hle : ‖((bZ.repr Z k0 : ℤ) : ℚ_[ℓ]) + d k0‖ ≤ 1 :=
    (Padic.nonarchimedean _ _).trans (max_le (Padic.norm_int_le_one _) (hd1 k0))
  nlinarith [norm_nonneg (ℓ : ℚ_[ℓ]), norm_nonneg (((bZ.repr Z k0 : ℤ) : ℚ_[ℓ]) + d k0)]

/- English proof (translation)
Use `set bb := Algebra.TensorProduct.basis ℚ_[ℓ] (integralBasis F) with hbb`. Establish `hb : ∀ k, bb k = 1 ⊗ₜ integralBasis F k` using `fun k => Algebra.TensorProduct.basis_apply _ _`. Use `(injective_iff_map_eq_zero D.Φ).2 fun x hx => ?_` and prove the remaining obligations. Rewrite `hx`, the goal using `[← bb.sum_repr x]`. Simplify using `only [map_sum, map_smul, hb] at hx`.

Establish `h0` using `(Fintype.linearIndependent_iff.1 hl) (fun k => bb.repr x k) hx`. Simplify using `[h0]`.
-/
theorem LocFam.injective_of_linearIndependent [Fintype ι] (D : LocFam F ℓ ι)
    (hl : LinearIndependent ℚ_[ℓ] (fun k => D.Φ (1 ⊗ₜ integralBasis F k))) :
    Function.Injective D.Φ := by
  classical
  set bb := Algebra.TensorProduct.basis ℚ_[ℓ] (integralBasis F) with hbb
  have hb : ∀ k, bb k = 1 ⊗ₜ integralBasis F k := fun k => Algebra.TensorProduct.basis_apply _ _
  refine (injective_iff_map_eq_zero D.Φ).2 fun x hx => ?_
  rw [← bb.sum_repr x] at hx ⊢
  simp only [map_sum, map_smul, hb] at hx
  have h0 := (Fintype.linearIndependent_iff.1 hl) (fun k => bb.repr x k) hx
  simp [h0]

/- English proof (translation)
Introduce `F _ _ ℓ _ ι _ D hD`. Conclude with `LocFam.injective_of_linearIndependent D (LocFam.linearIndependent D hD (exists_eq_ell_mul ℓ) (exists_int_approx ℓ))`.
-/
theorem toPi_injective : TrInj := by
  intro F _ _ ℓ _ ι _ D hD
  exact LocFam.injective_of_linearIndependent D
    (LocFam.linearIndependent D hD (exists_eq_ell_mul ℓ) (exists_int_approx ℓ))

end PI.ProdFormulaE.Tr
