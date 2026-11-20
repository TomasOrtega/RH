import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemDivSuppOfDivCycleNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsMonomialNotMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.InhDivCycleOfSuppEmpty
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsLineFibre
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsLinearQuotient
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

section Helpers

variable {F : Type} [Field F]

/- English proof (translation)
Use extensionality with `d`. Rewrite using `[coeff_C_mul, coeff_X]`. Distinguish the cases in `h : Finsupp.single 0 1 = d`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[if_neg h, mul_zero]`. Assume the negation of the conclusion as `hne`. Apply `h` to reduce the goal to its premises. Establish `hw` using `hg hne`. Use `Finsupp.ext fun i => ?_` and prove the remaining obligations.

Use `fin_cases i`. Simplify using `[Finsupp.weight_apply, Finsupp.sum_fintype] at hw ⊢`. Use linear arithmetic over natural numbers and integers.
-/
theorem linearForm_fin_one_eq {g : MvPolynomial (Fin 1) F} (hg : g.IsHomogeneous 1) :
    g = C (coeff (Finsupp.single 0 1) g) * X 0 := by
  ext d
  rw [coeff_C_mul, coeff_X]
  by_cases h : Finsupp.single 0 1 = d
  · subst h
    simp
  · rw [if_neg h, mul_zero]
    by_contra hne
    apply h
    have hw := hg hne
    refine Finsupp.ext fun i => ?_
    fin_cases i
    simp [Finsupp.weight_apply, Finsupp.sum_fintype] at hw ⊢
    omega

/- English proof (translation)
Introduce `d hd`. Establish `h` using `hf d (mem_support_iff.mpr hd)`. Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]`. Simplify using `only [Pi.one_apply, smul_eq_mul, mul_one]`. Rewrite using `[Fintype.sum_sigma]`.

Simplify using `[h, hK]`.
-/
theorem isHomogeneous_of_isMultiHomog_one {K₀ : Type} [Fintype K₀] {ι₀ : K₀ → Type}
    [∀ k, Fintype (ι₀ k)] (hK : Fintype.card K₀ = 1) {f : MRingOver F ι₀}
    (hf : IsMultiHomog f fun _ => 1) : f.IsHomogeneous 1 := by
  intro d hd
  have h := hf d (mem_support_iff.mpr hd)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Pi.one_apply, smul_eq_mul, mul_one]
  rw [Fintype.sum_sigma]
  simp [h, hK]

end Helpers

/- English proof (translation)
Introduce `F _ K₀ _ ι₀ _ k₀ Q J hk hQ ⟨S, hS, hQS⟩ hJ m`. Establish `hK : Fintype.card K₀ = 1` using `Fintype.card_eq_one_iff.mpr ⟨k₀, hk⟩`. Establish `hQp : Q.IsPrime` using `hQ.1.1`. Take `⟨i₀, hi₀⟩` from `hQ.1.2.2 k₀`. Use `set ℓ : MRingOver F ι₀ := X ⟨k₀, i₀⟩ with hℓdef`.

Take `⟨r, φ, hφs, hφk, hφX⟩` from `hLin F (Σ k, ι₀ k) (insert ℓ S) (by`. Introduce and unpack `f (rfl | hf)`. Conclude with `isHomogeneous_X F _`. Conclude with `isHomogeneous_of_isMultiHomog_one hK (hS f hf))`. Use `set W : Ideal (MRingOver F ι₀) := RingHom.ker φ with hWdef`.

Establish `hQW : Q ⊔ Ideal.span {ℓ} = W`. Rewrite using `[hφk, Ideal.span_insert, hQS, sup_comm]`. Establish `hWp : W.IsPrime` using `RingHom.ker_isPrime φ`. Establish `hWmin : W ∈ (Q ⊔ Ideal.span {ℓ}).minimalPrimes`. Rewrite using `[hQW, Ideal.minimalPrimes_eq_subsingleton_self]`.

Both sides reduce to the same expression. Establish `hdim` using `cyc_dim_quot_minimal_add_one hi₀ hWmin (fun h => by`. Rewrite `h` using `[hQ.2]`. Conclude with `ENat.natCast_ne_top _ (WithBot.coe_injective h))`. Establish `hdimW : ringKrullDim (MRingOver F ι₀ ⧸ W) = ((1 : ℕ) : WithBot ℕ∞)` using `cyc_withBot_eq_of_add_one (by rw [hdim, hQ.2, hK])`.

Rewrite `hdimW` using `[hWdef, ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerAlgEquivOfSurjective hφs).toRingEquiv, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]`. Establish `hr : r = 1`. Establish `: ((Nat.card (Fin r) : ℕ) : WithBot ℕ∞) = ((1 : ℕ) : WithBot ℕ∞)` using `hdimW`. Establish `h2 : Nat.card (Fin r) = 1` using `by exact_mod_cast this`. Simplify using `using h2`.

Substitute `hr` using the available equality. Establish `hex : ∃ s, (X s : MRingOver F ι₀) ∉ W`. Assume the negation of the conclusion as `hno`. Simplify using `only [not_exists, not_not] at hno`. Establish `hφ0 : φ = (Algebra.ofId F _).comp (aeval fun _ => (0 : F))`.

Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `s`. Establish `h0` using `hno s`. Rewrite `h0` using `[hWdef, RingHom.mem_ker]`. Simplify using `[h0]`.

Take `⟨f, hf⟩` from `hφs (X 0)`. Rewrite `hf` using `[hφ0]`. Use `congrArg (coeff (Finsupp.single 0 1)) hf` as an intermediate fact. Simplify using `[Algebra.ofId_apply, coeff_X, algebraMap_eq, coeff_C] at this`. Rewrite `this` using `[if_neg (Finsupp.single_ne_zero.mpr one_ne_zero).symm]`.

Conclude with `zero_ne_one this`. Take `⟨s₁, hs₁⟩` from `hex`. Establish `hWrel : IsRelevant W` using `fun k => by`. Take `rfl : k = s₁.1` from `(hk k).trans (hk s₁.1).symm`. Conclude with `⟨s₁.2, hs₁⟩`.

Establish `hdivℓ : divCycle Q ℓ = Finsupp.single W 1` using `inh_divCycle_prime Q ℓ W hQW hWrel`. Establish `hℓpow : ∀ n : ℕ, ℓ ^ n ∉ Q` using `fun n h => hi₀ (hQp.mem_of_pow_mem n h)`. Establish `hdivpow : ∀ n : ℕ, divCycle Q (ℓ ^ n) = Finsupp.single W n`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => simp [divCycle_one]`. Consider the case `succ n ih`. Rewrite using `[pow_succ, divCycle_mul hQp (hℓpow n) hi₀, ih, hdivℓ, ← Finsupp.single_add]`. Establish `hWpv : IsProjVarF W 0` using `isProjVarF_of_mem_divSupp (n := 0) hQ (isMultiHomog_X k₀ i₀) hi₀ ⟨hWmin, hWrel⟩`. Use `set j : ∀ k, ι₀ k := fun k => (hWrel k).choose with hjdef`.

Establish `hj : IsChart W j` using `fun k => (hWrel k).choose_spec`. Use `set p₁ : Σ k, ι₀ k := ⟨k₀, j k₀⟩ with hp₁`. Use `set a : (Σ k, ι₀ k) → F := fun s => coeff (Finsupp.single 0 1) (φ (X s)) with hadef`. Establish `hφXs : ∀ s, φ (X s) = C (a s) * X 0` using `fun s => linearForm_fin_one_eq (hφX s)`. Establish `ha1 : a p₁ ≠ 0`.

Introduce `h0`. Apply `hj k₀` to reduce the goal to its premises. Rewrite using `[hWdef, RingHom.mem_ker, hφXs, h0, C_0, zero_mul]`. Use `set c : (Σ k, ι₀ k) → F := fun s => a s / a p₁ with hcdef`. Establish `hev : aeval c = (aeval fun _ : Fin 1 => (a p₁)⁻¹).comp φ`.

Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `s`. Simplify using `[hφXs, hcdef, div_eq_mul_inv]`. Establish `hpt : ∀ L : Fin 0 → K₀ → ℤ, J W 0 L = 1`. Introduce `L`.

Rewrite using `[hJ.1 W L j hWpv hj]`. Unfold `ptDeg chartIdeal`. Rewrite using `[inh_finrank_quot _ c]`. Both sides reduce to the same expression. Apply `sup_le` to reduce the goal to its premises.

Introduce `f hf`. Rewrite using `[RingHom.mem_ker, ← coe_aeval_eq_eval, hev]`. Rewrite `hf` using `[hWdef, RingHom.mem_ker]`. Simplify using `[hf]`. Rewrite using `[Ideal.span_le]`.

Introduce and unpack `_ ⟨k, rfl⟩`. Take `rfl : k = k₀` from `hk k`. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker, map_sub, eval_X, map_one]`. Conclude with `sub_eq_zero.mpr (div_self ha1)`. Introduce `s`.

Establish `h1 : X s - C (c s) * X p₁ ∈ W`. Rewrite using `[hWdef, RingHom.mem_ker, map_sub, map_mul, algHom_C, hφXs, hφXs, ← mul_assoc, algebraMap_eq, ← C_mul, hcdef, div_mul_cancel₀ _ ha1, sub_self]`. Establish `h2 : C (c s) * (X p₁ - 1) ∈ Ideal.span (Set.range fun k => (X ⟨k, j k⟩ : MRingOver F ι₀) - 1)` using `Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k₀, rfl⟩)`. Establish `e : X s - C (c s) = (X s - C (c s) * X p₁) + C (c s) * (X p₁ - 1)` using `by ring`. Rewrite using `[e]`.

Conclude with `Ideal.add_mem _ (Ideal.mem_sup_left h1) (Ideal.mem_sup_right h2)`. Establish `e1 : (![m] : Fin 1 → K₀ → ℤ) = Fin.snoc (α` using `fun _ => K₀ → ℤ) Fin.elim0 m := by`. Use function extensionality and compare the values at `i`. Use `fin_cases i`. Both sides reduce to the same expression.

Establish `hmk : ∀ k, m k = m k₀` using `fun k => by rw [hk k]`. Establish `hhomℓ : ∀ n : ℕ, IsMultiHomog (ℓ ^ n) (fun _ => n)` using `fun n => by`. Use `isMultiHomog_pow (isMultiHomog_X (F := F) (ι := ι₀) k₀ i₀) n` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`.

Rewrite using `[hk k]`. Simplify using the standard rewrite rules. Establish `h1Q : (1 : MRingOver F ι₀) ∉ Q` using `fun h => hQp.ne_top ((Ideal.eq_top_iff_one _).mpr h)`. Rewrite using `[e1]`. Take `⟨n, hn | hn⟩` from `Int.eq_nat_or_neg (m k₀)`.

Rewrite using `[hJ.2 Q 0 Fin.elim0 m (ℓ ^ n) 1 hQ ⟨fun _ => n, 0, hhomℓ n, isMultiHomog_one, hℓpow n, h1Q, fun k => by simp [hmk k, hn]⟩, ratDiv, hdivpow, divCycle_one]`. Simplify using `[inh_cycEval_single, hpt, hn]`. Rewrite using `[hJ.2 Q 0 Fin.elim0 m 1 (ℓ ^ n) hQ ⟨0, fun _ => n, isMultiHomog_one, hhomℓ n, h1Q, hℓpow n, fun k => by simp [hmk k, hn]⟩, ratDiv, hdivpow, divCycle_one]`. Simplify using `only [Finsupp.mapRange_zero, Finsupp.mapRange_single, zero_sub]`. Rewrite using `[← Finsupp.single_neg, inh_cycEval_single, hpt, hn]`.

Simplify using the standard rewrite rules.
-/
theorem LineFibreBlocks.proof (hLin : LinearQuotient.Statement) : LineFibreBlocks.Statement := by
  intro F _ K₀ _ ι₀ _ k₀ Q J hk hQ ⟨S, hS, hQS⟩ hJ m
  classical
  have hK : Fintype.card K₀ = 1 := Fintype.card_eq_one_iff.mpr ⟨k₀, hk⟩
  have hQp : Q.IsPrime := hQ.1.1
  obtain ⟨i₀, hi₀⟩ := hQ.1.2.2 k₀
  set ℓ : MRingOver F ι₀ := X ⟨k₀, i₀⟩ with hℓdef
  obtain ⟨r, φ, hφs, hφk, hφX⟩ := hLin F (Σ k, ι₀ k) (insert ℓ S) (by
    rintro f (rfl | hf)
    · exact isHomogeneous_X F _
    · exact isHomogeneous_of_isMultiHomog_one hK (hS f hf))
  set W : Ideal (MRingOver F ι₀) := RingHom.ker φ with hWdef
  have hQW : Q ⊔ Ideal.span {ℓ} = W := by
    rw [hφk, Ideal.span_insert, hQS, sup_comm]
  have hWp : W.IsPrime := RingHom.ker_isPrime φ
  have hWmin : W ∈ (Q ⊔ Ideal.span {ℓ}).minimalPrimes := by
    rw [hQW, Ideal.minimalPrimes_eq_subsingleton_self]
    rfl

  have hdim := cyc_dim_quot_minimal_add_one hi₀ hWmin (fun h => by
    rw [hQ.2] at h
    exact ENat.natCast_ne_top _ (WithBot.coe_injective h))
  have hdimW : ringKrullDim (MRingOver F ι₀ ⧸ W) = ((1 : ℕ) : WithBot ℕ∞) :=
    cyc_withBot_eq_of_add_one (by rw [hdim, hQ.2, hK])
  rw [hWdef, ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerAlgEquivOfSurjective hφs).toRingEquiv,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add] at hdimW
  have hr : r = 1 := by
    have : ((Nat.card (Fin r) : ℕ) : WithBot ℕ∞) = ((1 : ℕ) : WithBot ℕ∞) := hdimW
    have h2 : Nat.card (Fin r) = 1 := by exact_mod_cast this
    simpa using h2
  subst hr

  have hex : ∃ s, (X s : MRingOver F ι₀) ∉ W := by
    by_contra hno
    simp only [not_exists, not_not] at hno
    have hφ0 : φ = (Algebra.ofId F _).comp (aeval fun _ => (0 : F)) := by
      apply MvPolynomial.algHom_ext
      intro s
      have h0 := hno s
      rw [hWdef, RingHom.mem_ker] at h0
      simp [h0]
    obtain ⟨f, hf⟩ := hφs (X 0)
    rw [hφ0] at hf
    have := congrArg (coeff (Finsupp.single 0 1)) hf
    simp [Algebra.ofId_apply, coeff_X, algebraMap_eq, coeff_C] at this
    rw [if_neg (Finsupp.single_ne_zero.mpr one_ne_zero).symm] at this
    exact zero_ne_one this
  obtain ⟨s₁, hs₁⟩ := hex
  have hWrel : IsRelevant W := fun k => by
    obtain rfl : k = s₁.1 := (hk k).trans (hk s₁.1).symm
    exact ⟨s₁.2, hs₁⟩

  have hdivℓ : divCycle Q ℓ = Finsupp.single W 1 := inh_divCycle_prime Q ℓ W hQW hWrel
  have hℓpow : ∀ n : ℕ, ℓ ^ n ∉ Q := fun n h => hi₀ (hQp.mem_of_pow_mem n h)
  have hdivpow : ∀ n : ℕ, divCycle Q (ℓ ^ n) = Finsupp.single W n := by
    intro n
    induction n with
    | zero => simp [divCycle_one]
    | succ n ih =>
      rw [pow_succ, divCycle_mul hQp (hℓpow n) hi₀, ih, hdivℓ, ← Finsupp.single_add]

  have hWpv : IsProjVarF W 0 :=
    isProjVarF_of_mem_divSupp (n := 0) hQ (isMultiHomog_X k₀ i₀) hi₀ ⟨hWmin, hWrel⟩
  set j : ∀ k, ι₀ k := fun k => (hWrel k).choose with hjdef
  have hj : IsChart W j := fun k => (hWrel k).choose_spec
  set p₁ : Σ k, ι₀ k := ⟨k₀, j k₀⟩ with hp₁
  set a : (Σ k, ι₀ k) → F := fun s => coeff (Finsupp.single 0 1) (φ (X s)) with hadef
  have hφXs : ∀ s, φ (X s) = C (a s) * X 0 := fun s => linearForm_fin_one_eq (hφX s)
  have ha1 : a p₁ ≠ 0 := by
    intro h0
    apply hj k₀
    rw [hWdef, RingHom.mem_ker, hφXs, h0, C_0, zero_mul]
  set c : (Σ k, ι₀ k) → F := fun s => a s / a p₁ with hcdef
  have hev : aeval c = (aeval fun _ : Fin 1 => (a p₁)⁻¹).comp φ := by
    apply MvPolynomial.algHom_ext
    intro s
    simp [hφXs, hcdef, div_eq_mul_inv]
  have hpt : ∀ L : Fin 0 → K₀ → ℤ, J W 0 L = 1 := by
    intro L
    rw [hJ.1 W L j hWpv hj]
    unfold ptDeg chartIdeal
    rw [inh_finrank_quot _ c]
    · rfl
    · apply sup_le
      · intro f hf
        rw [RingHom.mem_ker, ← coe_aeval_eq_eval, hev]
        rw [hWdef, RingHom.mem_ker] at hf
        simp [hf]
      · rw [Ideal.span_le]
        rintro _ ⟨k, rfl⟩
        obtain rfl : k = k₀ := hk k
        rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, eval_X, map_one]
        exact sub_eq_zero.mpr (div_self ha1)
    · intro s
      have h1 : X s - C (c s) * X p₁ ∈ W := by
        rw [hWdef, RingHom.mem_ker, map_sub, map_mul, algHom_C, hφXs, hφXs, ← mul_assoc,
          algebraMap_eq, ← C_mul, hcdef, div_mul_cancel₀ _ ha1, sub_self]
      have h2 : C (c s) * (X p₁ - 1) ∈
          Ideal.span (Set.range fun k => (X ⟨k, j k⟩ : MRingOver F ι₀) - 1) :=
        Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k₀, rfl⟩)
      have e : X s - C (c s) = (X s - C (c s) * X p₁) + C (c s) * (X p₁ - 1) := by ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.mem_sup_left h1) (Ideal.mem_sup_right h2)

  have e1 : (![m] : Fin 1 → K₀ → ℤ) = Fin.snoc (α := fun _ => K₀ → ℤ) Fin.elim0 m := by
    funext i
    fin_cases i
    rfl
  have hmk : ∀ k, m k = m k₀ := fun k => by rw [hk k]
  have hhomℓ : ∀ n : ℕ, IsMultiHomog (ℓ ^ n) (fun _ => n) := fun n => by
    have := isMultiHomog_pow (isMultiHomog_X (F := F) (ι := ι₀) k₀ i₀) n
    convert this using 1
    funext k
    rw [hk k]
    simp
  have h1Q : (1 : MRingOver F ι₀) ∉ Q := fun h => hQp.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  rw [e1]
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg (m k₀)
  · rw [hJ.2 Q 0 Fin.elim0 m (ℓ ^ n) 1 hQ ⟨fun _ => n, 0, hhomℓ n, isMultiHomog_one, hℓpow n, h1Q,
      fun k => by simp [hmk k, hn]⟩, ratDiv, hdivpow, divCycle_one]
    simp [inh_cycEval_single, hpt, hn]
  · rw [hJ.2 Q 0 Fin.elim0 m 1 (ℓ ^ n) hQ ⟨0, fun _ => n, isMultiHomog_one, hhomℓ n, h1Q, hℓpow n,
      fun k => by simp [hmk k, hn]⟩, ratDiv, hdivpow, divCycle_one]
    simp only [Finsupp.mapRange_zero, Finsupp.mapRange_single, zero_sub]
    rw [← Finsupp.single_neg, inh_cycEval_single, hpt, hn]
    simp

end GroundTheory.Heights₂.Heights.Inter
