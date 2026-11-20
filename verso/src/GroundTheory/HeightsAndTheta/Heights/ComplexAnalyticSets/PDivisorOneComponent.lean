import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorOneComponent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceMultGeneral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLeadIdealDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ComplexSets

noncomputable section

namespace DivisorOneComponent

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h f hf => RingHom.mem_ker.2 (h f hf), fun h _ hf => RingHom.mem_ker.1 (h hf)⟩`.
-/
theorem mem_zeroSet_iff {n : ℕ} (K : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    q ∈ zeroSet K ↔ K ≤ RingHom.ker (eval q) :=
  ⟨fun h f hf => RingHom.mem_ker.2 (h f hf), fun h _ hf => RingHom.mem_ker.1 (h hf)⟩

/- English proof (translation)
Establish `: zeroSet K = ⋂ f ∈ K, {x : Fin n → ℂ | eval x f = 0}` using `by ext x; simp [zeroSet]`. Rewrite using `[this]`. Conclude with `isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval f) continuous_const`.
-/
theorem isClosed_zeroSet {n : ℕ} (K : Ideal (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroSet K) := by
  have : zeroSet K = ⋂ f ∈ K, {x : Fin n → ℂ | eval x f = 0} := by ext x; simp [zeroSet]
  rw [this]
  exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval f) continuous_const

/- English proof (translation)
Break down `d with _ | k` into its components or cases. Use `⟨⊥, WithBot.bot_lt_coe _, fun x hx => ?_⟩` and prove the remaining obligations. Consider the cases of `x using WithBot.recBotCoe with`. Consider the case `bot => exact le_rfl`. Consider the case `coe y`.

Establish `: y + 1 ≤ 0` using `by exact_mod_cast hx`. Simplify using `at this`. Use `⟨(k : WithBot ℕ∞), by exact_mod_cast Nat.lt_succ_self k, fun x hx => ?_⟩` and prove the remaining obligations. Consider the cases of `x using WithBot.recBotCoe with`. Consider the case `bot => exact bot_le`.

Consider the case `coe y`. Establish `h1 : y + 1 ≤ ((k + 1 : ℕ) : ℕ∞)` using `by exact_mod_cast hx`. Establish `h2 : y ≤ (k : ℕ∞)`. Consider the cases of `y using ENat.recTopCoe with`. Consider the case `top => simp at h1`.

Consider the case `coe y`. Establish `h3 : y + 1 ≤ k + 1` using `by exact_mod_cast h1`. Conclude with `(by omega : y ≤ k)` after adjusting the coercions. Conclude with `h2` after adjusting the coercions.
-/
theorem exists_bound (d : ℕ) : ∃ N : WithBot ℕ∞, N < (d : WithBot ℕ∞) ∧
    ∀ x : WithBot ℕ∞, x + 1 ≤ (d : WithBot ℕ∞) → x ≤ N := by
  rcases d with _ | k
  · refine ⟨⊥, WithBot.bot_lt_coe _, fun x hx => ?_⟩
    cases x using WithBot.recBotCoe with
    | bot => exact le_rfl
    | coe y =>
      have : y + 1 ≤ 0 := by exact_mod_cast hx
      simp at this
  · refine ⟨(k : WithBot ℕ∞), by exact_mod_cast Nat.lt_succ_self k, fun x hx => ?_⟩
    cases x using WithBot.recBotCoe with
    | bot => exact bot_le
    | coe y =>
      have h1 : y + 1 ≤ ((k + 1 : ℕ) : ℕ∞) := by exact_mod_cast hx
      have h2 : y ≤ (k : ℕ∞) := by
        cases y using ENat.recTopCoe with
        | top => simp at h1
        | coe y =>
          have h3 : y + 1 ≤ k + 1 := by exact_mod_cast h1
          exact_mod_cast (by omega : y ≤ k)
      exact_mod_cast h2

/- English proof (translation)
Establish `_ : W.IsPrime` using `hW.1.1`. Take `⟨x, hxW', hxW⟩ : ∃ x ∈ W', x ∉ W` from `by by_contra! h`. Conclude with `hne (le_antisymm (hW.2 hW'.1 h) h)`. Establish `hle : W ⊔ Ideal.span {x} ≤ W ⊔ W'` using `sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).2 hxW') _`. Establish `hx : x ∈ W ⊔ Ideal.span {x}` using `Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)`.

Establish `hr : Ideal.Quotient.mk W x ∈ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ W)` using `mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])`. Establish `hsurj : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (W ⊔ W')) ≤ ringKrullDim ((MvPolynomial (Fin n) ℂ ⧸ W) ⧸ Ideal.span {Ideal.Quotient.mk W x})`. Use `ringKrullDim_le_of_surjective (Ideal.Quotient.lift _ (Ideal.Quotient.factor (le_sup_left.trans hle)) ?_) (Ideal.Quotient.lift_surjective_of_surjective _ _ (Ideal.Quotient.factor_surjective _))` and prove the remaining obligations. Introduce `y hy`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hy`.

Take `⟨c', rfl⟩` from `Ideal.Quotient.mk_surjective c`. Establish `h0 : Ideal.Quotient.mk (W ⊔ W') (c' * x) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_left _ _ (hle hx))`. Simplify `h0` using `[Ideal.Quotient.factor_mk, map_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem dim_sup_add_one_le {n d : ℕ} {J W W' : Ideal (MvPolynomial (Fin n) ℂ)} [J.IsPrime] {u : Fin n → ℂ}
    (hu : linForm u ∉ J) (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((d + 1 : ℕ) : WithBot ℕ∞))
    (hW : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes)
    (hW' : W' ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes) (hne : W ≠ W') :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (W ⊔ W')) + 1 ≤ (d : WithBot ℕ∞) := by
  have _ : W.IsPrime := hW.1.1
  obtain ⟨x, hxW', hxW⟩ : ∃ x ∈ W', x ∉ W := by
    by_contra! h
    exact hne (le_antisymm (hW.2 hW'.1 h) h)
  have hle : W ⊔ Ideal.span {x} ≤ W ⊔ W' := sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).2 hxW') _
  have hx : x ∈ W ⊔ Ideal.span {x} := Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)
  have hr : Ideal.Quotient.mk W x ∈ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ W) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have hsurj : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (W ⊔ W')) ≤
      ringKrullDim ((MvPolynomial (Fin n) ℂ ⧸ W) ⧸ Ideal.span {Ideal.Quotient.mk W x}) := by
    refine ringKrullDim_le_of_surjective (Ideal.Quotient.lift _ (Ideal.Quotient.factor
      (le_sup_left.trans hle)) ?_) (Ideal.Quotient.lift_surjective_of_surjective _ _
        (Ideal.Quotient.factor_surjective _))
    intro y hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
    have h0 : Ideal.Quotient.mk (W ⊔ W') (c' * x) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_left _ _ (hle hx))
    simpa [Ideal.Quotient.factor_mk, map_mul] using h0
  calc ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (W ⊔ W')) + 1
      ≤ ringKrullDim ((MvPolynomial (Fin n) ℂ ⧸ W) ⧸ Ideal.span {Ideal.Quotient.mk W x}) + 1 := by gcongr
    _ ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr
    _ = (d : WithBot ℕ∞) := ringKrullDim_component hu hW hdim

end DivisorOneComponent

open DivisorOneComponent in

/- English proof (translation)
Introduce `n d J u hJ hdim hu`. Establish `hKq : ∀ x ∈ zeroSet J, linEval u x = 0 → J ⊔ Ideal.span {linForm u} ≤ RingHom.ker (eval x)`. Introduce `x hxJ hxu`. Use `sup_le ((mem_zeroSet_iff J x).1 hxJ) ((Ideal.span_singleton_le_iff_mem _).2 ?_)` and prove the remaining obligations. Simplify `hxu` using `[linForm, linEval]`.

Generalize the expression as in `hK : J ⊔ Ideal.span {linForm u} = K at hKq ⊢`. Establish `hM : K.minimalPrimes.Finite` using `Ideal.finite_minimalPrimes_of_isNoetherianRing _ K`. Take `⟨S, hS⟩ : ∃ S : Finset (Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ)), ∀ p, p ∈ S ↔ p.1 ∈ K.minimalPrimes ∧ p.2 ∈ K.minimalPrimes ∧ p.1 ≠ p.2` from `⟨(hM.prod hM).toFinset.filter fun p => p.1 ≠ p.2, fun p => by rw [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_prod, and_assoc]⟩`. Take `⟨I, hI⟩ : ∃ I, I = S.inf fun p => p.1 ⊔ p.2` from `⟨_, rfl⟩`. Establish `hmemS : ∀ p ∈ S, p.1 ∈ K.minimalPrimes ∧ p.2 ∈ K.minimalPrimes ∧ p.1 ≠ p.2` using `fun p hp => (hS p).1 hp`.

Establish `hpair : ∀ W W', W ∈ K.minimalPrimes → W' ∈ K.minimalPrimes → W ≠ W' → I ≤ W ⊔ W'` using `fun W W' hW hW' hne => by`. Establish `h` using `Finset.inf_le (f := fun p : Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ) => p.1 ⊔ p.2) ((hS (W, W')).2 ⟨hW, hW', hne⟩)`. Rewrite using `[hI]`. Conclude with `h`. Establish `hKI : K ≤ I`.

Establish `h` using `Finset.le_inf (f := fun p : Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ) => p.1 ⊔ p.2) (a := K) (s := S) fun p hp => (hmemS p hp).1.1.2.trans le_sup_left`. Rewrite using `[hI]`. Conclude with `h`. Take `⟨N, hN, hxN⟩` from `exists_bound d`. Use `⟨I, hKI, ?_, ?_⟩` and prove the remaining obligations.

Use `lt_of_le_of_lt (ComplexSets.quotient_dim_le_of_minimalPrimes I fun Z hZ => ?_) hN` and prove the remaining obligations. Establish `hZI : S.inf (fun p : Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ) => p.1 ⊔ p.2) ≤ Z` using `by rw [← hI]; exact hZ.1.2`. Take `⟨p, hp, hpZ⟩` from `(Ideal.IsPrime.inf_le' (f := fun p : Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ) => p.1 ⊔ p.2) hZ.1.1).1 hZI`. Take `⟨h1, h2, h12⟩` from `hmemS p hp`. Conclude with `(ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hpZ)).trans (hxN _ (dim_sup_add_one_le hu hdim (by rw [hK]; exact h1) (by rw [hK]; exact h2) h12))`.

Introduce `q hqJ hqu hqI`. Take `⟨W, hW, hWq⟩` from `Ideal.exists_minimalPrimes_le (hKq q hqJ hqu)`. Establish `huniq : ∀ W' ∈ K.minimalPrimes, q ∈ zeroSet W' → W' = W`. Introduce `W' hW' hq'`. Assume the negation of the conclusion as `hne`.

Conclude with `hqI ((mem_zeroSet_iff I q).2 ((hpair W W' hW hW' (Ne.symm hne)).trans (sup_le hWq ((mem_zeroSet_iff W' q).1 hq'))))`. Use `⟨W, hW, (mem_zeroSet_iff W q).2 hWq, huniq, ⋂ W' ∈ K.minimalPrimes \ {W}, (zeroSet W')ᶜ, ?_, ?_⟩` and prove the remaining obligations. Use `(biInter_mem (hM.subset Set.sdiff_subset)).2 fun W' hW' => (isClosed_zeroSet W').isOpen_compl.mem_nhds ?_` and prove the remaining obligations. Conclude with `fun hq' => hW'.2 (huniq W' hW'.1 hq')`. Introduce and unpack `x ⟨hxJ, hxU⟩ hxu`.

Take `⟨W'', hW'', hW''x⟩` from `Ideal.exists_minimalPrimes_le (hKq x hxJ hxu)`. Distinguish the cases in `h : W'' = W`. Substitute `h` using the available equality. Conclude with `(mem_zeroSet_iff W'' x).2 hW''x`. Conclude with `absurd ((mem_zeroSet_iff W'' x).2 hW''x) (Set.mem_iInter₂.1 hxU W'' ⟨hW'', h⟩)`.
-/
theorem DivisorOneComponent.proof : DivisorOneComponent.Statement := by
  classical
  intro n d J u hJ hdim hu
  have hKq : ∀ x ∈ zeroSet J, linEval u x = 0 → J ⊔ Ideal.span {linForm u} ≤ RingHom.ker (eval x) := by
    intro x hxJ hxu
    refine sup_le ((mem_zeroSet_iff J x).1 hxJ) ((Ideal.span_singleton_le_iff_mem _).2 ?_)
    simpa [linForm, linEval] using hxu
  generalize hK : J ⊔ Ideal.span {linForm u} = K at hKq ⊢
  have hM : K.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ K
  obtain ⟨S, hS⟩ : ∃ S : Finset (Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ)),
      ∀ p, p ∈ S ↔ p.1 ∈ K.minimalPrimes ∧ p.2 ∈ K.minimalPrimes ∧ p.1 ≠ p.2 :=
    ⟨(hM.prod hM).toFinset.filter fun p => p.1 ≠ p.2, fun p => by rw [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_prod, and_assoc]⟩
  obtain ⟨I, hI⟩ : ∃ I, I = S.inf fun p => p.1 ⊔ p.2 := ⟨_, rfl⟩
  have hmemS : ∀ p ∈ S, p.1 ∈ K.minimalPrimes ∧ p.2 ∈ K.minimalPrimes ∧ p.1 ≠ p.2 := fun p hp => (hS p).1 hp
  have hpair : ∀ W W', W ∈ K.minimalPrimes → W' ∈ K.minimalPrimes → W ≠ W' → I ≤ W ⊔ W' :=
    fun W W' hW hW' hne => by
      have h := Finset.inf_le (f := fun p : Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ) => p.1 ⊔ p.2) ((hS (W, W')).2 ⟨hW, hW', hne⟩)
      rw [hI]; exact h
  have hKI : K ≤ I := by
    have h := Finset.le_inf (f := fun p : Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ) => p.1 ⊔ p.2) (a := K) (s := S) fun p hp => (hmemS p hp).1.1.2.trans le_sup_left
    rw [hI]; exact h
  obtain ⟨N, hN, hxN⟩ := exists_bound d
  refine ⟨I, hKI, ?_, ?_⟩
  · refine lt_of_le_of_lt (ComplexSets.quotient_dim_le_of_minimalPrimes I fun Z hZ => ?_) hN
    have hZI : S.inf (fun p : Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ) => p.1 ⊔ p.2) ≤ Z := by rw [← hI]; exact hZ.1.2
    obtain ⟨p, hp, hpZ⟩ := (Ideal.IsPrime.inf_le' (f := fun p : Ideal (MvPolynomial (Fin n) ℂ) × Ideal (MvPolynomial (Fin n) ℂ) => p.1 ⊔ p.2) hZ.1.1).1 hZI
    obtain ⟨h1, h2, h12⟩ := hmemS p hp
    exact (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hpZ)).trans
      (hxN _ (dim_sup_add_one_le hu hdim (by rw [hK]; exact h1) (by rw [hK]; exact h2) h12))
  · intro q hqJ hqu hqI
    obtain ⟨W, hW, hWq⟩ := Ideal.exists_minimalPrimes_le (hKq q hqJ hqu)
    have huniq : ∀ W' ∈ K.minimalPrimes, q ∈ zeroSet W' → W' = W := by
      intro W' hW' hq'
      by_contra hne
      exact hqI ((mem_zeroSet_iff I q).2 ((hpair W W' hW hW' (Ne.symm hne)).trans
        (sup_le hWq ((mem_zeroSet_iff W' q).1 hq'))))
    refine ⟨W, hW, (mem_zeroSet_iff W q).2 hWq, huniq, ⋂ W' ∈ K.minimalPrimes \ {W}, (zeroSet W')ᶜ, ?_, ?_⟩
    · refine (biInter_mem (hM.subset Set.sdiff_subset)).2 fun W' hW' => (isClosed_zeroSet W').isOpen_compl.mem_nhds ?_
      exact fun hq' => hW'.2 (huniq W' hW'.1 hq')
    · rintro x ⟨hxJ, hxU⟩ hxu
      obtain ⟨W'', hW'', hW''x⟩ := Ideal.exists_minimalPrimes_le (hKq x hxJ hxu)
      by_cases h : W'' = W
      · subst h; exact (mem_zeroSet_iff W'' x).2 hW''x
      · exact absurd ((mem_zeroSet_iff W'' x).2 hW''x) (Set.mem_iInter₂.1 hxU W'' ⟨hW'', h⟩)

end

end GroundTheory.Heights₂.Heights
