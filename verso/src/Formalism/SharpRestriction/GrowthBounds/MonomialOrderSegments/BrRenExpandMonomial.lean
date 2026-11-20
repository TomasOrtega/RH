import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SecondValuationOfAdmitted

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

open Formalism.MainNotions.G Formalism.MainNotions.PlaneGramData

section Mono

variable {K : Type} [Field K] {r : ℕ}

/- English proof (translation)
Rewrite using `[MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun a => pow_zero _)]`.
-/
theorem br_monomial_eq (s : Fin r →₀ ℕ) (c : K) :
    (monomial s c : MvPolynomial (Fin r) K) = C c * ∏ a, X a ^ s a := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun a => pow_zero _)]

def brRen (K : Type) [Field K] (r : ℕ) : MvPolynomial (Fin r) K →ₐ[K] MvPolynomial (Unit × Fin r) K :=
  rename fun a => ((), a)

/- English proof (translation)
Introduce `a b h` and use `congrArg Prod.snd h`.
-/
theorem brRen_inj : Function.Injective (fun a : Fin r => ((), a)) := fun a b h => congrArg Prod.snd h

/- English proof (translation)
Rewrite using `[br_monomial_eq, map_mul, map_prod]`. Simplify using `only [brRen, rename_C, map_pow, rename_X, monoL]`.
-/
theorem brRen_monomial (s : Fin r →₀ ℕ) (c : K) : brRen K r (monomial s c) = C c * monoL (K := K) (fun a => s a) := by
  rw [br_monomial_eq, map_mul, map_prod]
  simp only [brRen, rename_C, map_pow, rename_X, monoL]

/- English proof (translation)
Rewrite using `[br_monomial_eq]`. Simplify using `only [map_mul, map_prod, map_pow, expand_C, expand_X, brRen, rename_C, rename_X, monoL, ← pow_mul]`.
-/
theorem brRen_expand_monomial (P : ℕ) (s : Fin r →₀ ℕ) (c : K) :
    brRen K r (expand P (monomial s c)) = C c * monoL (K := K) (fun a => P * s a) := by
  rw [br_monomial_eq]
  simp only [map_mul, map_prod, map_pow, expand_C, expand_X, brRen, rename_C, rename_X, monoL, ← pow_mul]

/- English proof (translation)
Unfold `ddiv`. Rewrite using `[support_monomial, if_neg one_ne_zero, Finset.sum_singleton, coeff_monomial, if_pos rfl, one_mul]`. Use `split_ifs with h`. Use `congr 1`. Rewrite using `[Finsupp.prod]`.

Use `push_cast`. Apply `Finset.prod_subset (Finset.subset_univ _)` to reduce the goal to its premises. Introduce `a _ ha`. Establish `h0 : α a = 0` using `by simpa using ha`. Establish `hM : M a = 0`.

Use `Finsupp.le_def.1 h a` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify using `[h0, hM]`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, α a < M a := by`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Conclude with `h (Finsupp.le_def.2 hc)`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ a) (by simp [Nat.choose_eq_zero_of_lt ha]), monomial_zero]`.
-/
theorem br_ddiv_monomial (M α : Fin r →₀ ℕ) :
    ddiv M (monomial α (1 : K)) = monomial (α - M) (∏ a, (((α a).choose (M a) : ℕ) : K)) := by
  classical
  unfold ddiv
  rw [support_monomial, if_neg one_ne_zero, Finset.sum_singleton, coeff_monomial, if_pos rfl, one_mul]
  split_ifs with h
  · congr 1
    rw [Finsupp.prod]
    push_cast
    apply Finset.prod_subset (Finset.subset_univ _)
    intro a _ ha
    have h0 : α a = 0 := by simpa using ha
    have hM : M a = 0 := by
      have := Finsupp.le_def.1 h a
      omega
    simp [h0, hM]
  · obtain ⟨a, ha⟩ : ∃ a, α a < M a := by
      by_contra hc
      push_neg at hc
      exact h (Finsupp.le_def.2 hc)
    rw [Finset.prod_eq_zero (Finset.mem_univ a) (by simp [Nat.choose_eq_zero_of_lt ha]), monomial_zero]

/- English proof (translation)
Rewrite using `[br_ddiv_monomial, brRen_monomial, Formalism.MainNotions.G.Joints.divDer_monoL]`. Use `congr 2`.
-/
theorem brRen_ddiv (M α : Fin r →₀ ℕ) :
    brRen K r (ddiv M (monomial α (1 : K))) =
      divDer (atLetter () (fun a => M a)) (monoL (K := K) (fun a => α a)) := by
  rw [br_ddiv_monomial, brRen_monomial, Formalism.MainNotions.G.Joints.divDer_monoL]
  congr 2

/- English proof (translation)
Rewrite using `[br_ddiv_monomial, monomial_mul, one_mul, map_mul, brRen_monomial, brRen_expand_monomial]`. Establish `h : (fun a => P * (δ + (β - κ)) a) = fun a => P * (β a - κ a + δ a)`. Use function extensionality and compare the values at `a`. Simplify using `[Finsupp.add_apply, add_comm]`. Rewrite using `[h, map_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem brRen_term (P : ℕ) (ρ' δ κ β : Fin r →₀ ℕ) (x : K) :
    brRen K r (monomial ρ' x * expand P (monomial δ (1 : K) * ddiv κ (monomial β (1 : K)))) =
      C (x * ∏ a, (((β a).choose (κ a) : ℕ) : K)) * monoL (K := K) (fun a => ρ' a) *
        monoL (K := K) (fun a => P * (β a - κ a + δ a)) := by
  rw [br_ddiv_monomial, monomial_mul, one_mul, map_mul, brRen_monomial, brRen_expand_monomial]
  have h : (fun a => P * (δ + (β - κ)) a) = fun a => P * (β a - κ a + δ a) := by
    funext a
    simp [Finsupp.add_apply, add_comm]
  rw [h, map_mul]
  ring

end Mono

section DER

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Unfold `DER`. Introduce `_ r g ρ hρ M c hc`. Take `⟨T, coef, hT, hval⟩` from `h6 g r (fun a => M a) (fun a => ρ a) hρ c hc`. Set `e` to `T.equivFin`. Set `τ : Fin T.card → (Fin r → ℕ) × (Fin r → ℕ) × (Fin r → ℕ)` to `fun t => (e.symm t).1`.

Establish `key : ∀ x : WithTop ℚ, geQ x (c : ℝ) → ((c : ℕ) : WithTop ℚ) ≤ x`. Introduce `x hx`. Proceed by induction on `x using WithTop.recTopCoe with`. Consider the case `top => exact le_top`. Consider the case `coe q`.

Establish `hq` using `hx q rfl`. Establish `hq' : ((c : ℕ) : ℚ) ≤ q` using `by exact_mod_cast hq`. Conclude with `hq'` after adjusting the coercions. Use `⟨T.card, fun t => algebraMap O (KK O) (coef (τ t)), fun t => Finsupp.equivFunOnFinite.symm (τ t).1, fun t => Finsupp.equivFunOnFinite.symm (τ t).2.1, fun t => Finsupp.equivFunOnFinite.symm (τ t).2.2, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `t show (0 : WithTop ℚ) ≤ vK p (algebraMap O (KK O) (coef (τ t)))`.

Distinguish the cases in `h0 : coef (τ t) = 0`. Rewrite using `[h0, map_zero, Formalism.MainNotions.G.GLWeightTheory.valuation_zero_alt p]`. Conclude with `le_top`. Rewrite using `[Formalism.MainNotions.G.Joints.vK_alg p _ h0]`. Conclude with `WithTop.coe_nonneg.2 (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))`.

Introduce `t`. Establish `hb` using `(hT (τ t) (e.symm t).2).2`. Rewrite using `[br_absE, br_absE]`. Simplify using `only [Finsupp.coe_equivFunOnFinite_symm]`. Move the coercions through the operations in `at hb ⊢`.

Conclude with `hb`. Introduce `β γ show ((c : ℕ) : WithTop ℚ) ≤ vK p _`. Establish `hX : ∀ F : MvPolynomial (Fin r) (KK O), F.coeff γ = (brRen (KK O) r F).coeff (γ.mapDomain fun a => ((), a))` using `fun F => (coeff_rename_mapDomain _ brRen_inj F γ).symm`. Rewrite using `[hX, map_sub, map_sum, brRen_ddiv]`. Simplify using `only [brRen_term]`.

Establish `hα : (fun a => (ρ + p ^ g • β) a) = fun a => ρ a + p ^ g * β a`. Use function extensionality and compare the values at `a`. Simplify using the standard rewrite rules. Establish `hsum : (∑ t : Fin T.card, C (algebraMap O (KK O) (coef (τ t)) * ∏ a, (((β a).choose ((Finsupp.equivFunOnFinite.symm (τ t).2.2) a) : ℕ) : KK O)) * monoL (K` using `KK O) (fun a => (Finsupp.equivFunOnFinite.symm (τ t).1) a) * monoL (K := KK O) (fun a => p ^ g * (β a - (Finsupp.equivFunOnFinite.symm (τ t).2.2) a + (Finsupp.equivFunOnFinite.symm (τ t).2.1) a))) = ∑ x ∈ T, C (algebraMap O (KK O) (coef x) * ∏ a, (((β a).choose (x.2.2 a) : ℕ) : K …`. Simplify using `only [Finsupp.coe_equivFunOnFinite_symm]`.

Rewrite using `[← Finset.sum_coe_sort T]`. Conclude with `Fintype.sum_equiv e.symm _ _ (fun t => rfl)`. Rewrite using `[hα, hsum]`. Conclude with `key _ (hval (fun a => β a) (γ.mapDomain fun a => ((), a)))`.
-/
theorem brDER (S0 : UniformizedDVR p O) [CharZero (KK O)] (h6 : Formalism.MainNotions.PlaneGramData.DerivativeCongruenceAtRing p O) :
    DER (KK O) (vQ p S0) p := by
  classical
  unfold DER
  intro _ r g ρ hρ M c hc
  obtain ⟨T, coef, hT, hval⟩ := h6 g r (fun a => M a) (fun a => ρ a) hρ c hc
  let e := T.equivFin
  let τ : Fin T.card → (Fin r → ℕ) × (Fin r → ℕ) × (Fin r → ℕ) := fun t => (e.symm t).1
  have key : ∀ x : WithTop ℚ, geQ x (c : ℝ) → ((c : ℕ) : WithTop ℚ) ≤ x := by
    intro x hx
    induction x using WithTop.recTopCoe with
    | top => exact le_top
    | coe q =>
      have hq := hx q rfl
      have hq' : ((c : ℕ) : ℚ) ≤ q := by exact_mod_cast hq
      exact_mod_cast hq'
  refine ⟨T.card, fun t => algebraMap O (KK O) (coef (τ t)),
    fun t => Finsupp.equivFunOnFinite.symm (τ t).1, fun t => Finsupp.equivFunOnFinite.symm (τ t).2.1,
    fun t => Finsupp.equivFunOnFinite.symm (τ t).2.2, ?_, ?_, ?_⟩
  · intro t
    show (0 : WithTop ℚ) ≤ vK p (algebraMap O (KK O) (coef (τ t)))
    by_cases h0 : coef (τ t) = 0
    · rw [h0, map_zero, Formalism.MainNotions.G.GLWeightTheory.valuation_zero_alt p]
      exact le_top
    · rw [Formalism.MainNotions.G.Joints.vK_alg p _ h0]
      exact WithTop.coe_nonneg.2 (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · intro t
    have hb := (hT (τ t) (e.symm t).2).2
    rw [br_absE, br_absE]
    simp only [Finsupp.coe_equivFunOnFinite_symm]
    push_cast at hb ⊢
    exact hb
  · intro β γ
    show ((c : ℕ) : WithTop ℚ) ≤ vK p _
    have hX : ∀ F : MvPolynomial (Fin r) (KK O),
        F.coeff γ = (brRen (KK O) r F).coeff (γ.mapDomain fun a => ((), a)) :=
      fun F => (coeff_rename_mapDomain _ brRen_inj F γ).symm
    rw [hX, map_sub, map_sum, brRen_ddiv]
    simp only [brRen_term]
    have hα : (fun a => (ρ + p ^ g • β) a) = fun a => ρ a + p ^ g * β a := by
      funext a
      simp
    have hsum : (∑ t : Fin T.card,
        C (algebraMap O (KK O) (coef (τ t)) *
            ∏ a, (((β a).choose ((Finsupp.equivFunOnFinite.symm (τ t).2.2) a) : ℕ) : KK O)) *
          monoL (K := KK O) (fun a => (Finsupp.equivFunOnFinite.symm (τ t).1) a) *
          monoL (K := KK O) (fun a => p ^ g * (β a - (Finsupp.equivFunOnFinite.symm (τ t).2.2) a +
            (Finsupp.equivFunOnFinite.symm (τ t).2.1) a))) =
        ∑ x ∈ T, C (algebraMap O (KK O) (coef x) * ∏ a, (((β a).choose (x.2.2 a) : ℕ) : KK O)) *
          monoL (K := KK O) x.1 * monoL (K := KK O) (fun a => p ^ g * (β a - x.2.2 a + x.2.1 a)) := by
      simp only [Finsupp.coe_equivFunOnFinite_symm]
      rw [← Finset.sum_coe_sort T]
      exact Fintype.sum_equiv e.symm _ _ (fun t => rfl)
    rw [hα, hsum]
    exact key _ (hval (fun a => β a) (γ.mapDomain fun a => ((), a)))

end DER

end Formalism.MainNotions.PlaneGram
