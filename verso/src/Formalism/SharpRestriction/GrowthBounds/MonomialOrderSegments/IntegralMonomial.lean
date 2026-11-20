import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SegDefs
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.DigitPartMonomial
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.AddMemSupportOfMemSupportCoefOut
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.ExistsMonomialOrder

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

section General

variable {K : Type} [Field K] {v : AddValuation K (WithTop ℚ)} {σ : Type}

/- English proof (translation)
Unfold `Integral`. Introduce `α`. Simplify using the standard rewrite rules.
-/
theorem integral_zero' : Integral v (0 : MvPolynomial σ K) := by
  unfold Integral
  intro α
  simp

/- English proof (translation)
Unfold `Integral at *`. Introduce `α`. Rewrite using `[MvPolynomial.coeff_add]`. Conclude with `le_trans (le_min (hF α) (hG α)) (v.map_add _ _)`.
-/
theorem integral_add' {F G : MvPolynomial σ K} (hF : Integral v F) (hG : Integral v G) :
    Integral v (F + G) := by
  unfold Integral at *
  intro α
  rw [MvPolynomial.coeff_add]
  exact le_trans (le_min (hF α) (hG α)) (v.map_add _ _)

/- English proof (translation)
Conclude with `Finset.sum_induction f (fun F => Integral v F) (fun _ _ hF hG => integral_add' hF hG) integral_zero' h`.
-/
theorem integral_sum' {κ : Type} (s : Finset κ) (f : κ → MvPolynomial σ K)
    (h : ∀ k ∈ s, Integral v (f k)) : Integral v (∑ k ∈ s, f k) := by
  exact Finset.sum_induction f (fun F => Integral v F) (fun _ _ hF hG => integral_add' hF hG)
    integral_zero' h

/- English proof (translation)
Unfold `Integral at *`. Introduce `α`. Rewrite using `[MvPolynomial.coeff_smul, smul_eq_mul, AddValuation.map_mul]`. Conclude with `add_nonneg ha (hF α)`.
-/
theorem integral_smul' {a : K} {F : MvPolynomial σ K} (ha : 0 ≤ v a) (hF : Integral v F) :
    Integral v (a • F) := by
  unfold Integral at *
  intro α
  rw [MvPolynomial.coeff_smul, smul_eq_mul, AddValuation.map_mul]
  exact add_nonneg ha (hF α)

/- English proof (translation)
Unfold `Integral at *`. Introduce `α`. Rewrite using `[MvPolynomial.coeff_mul]`. Apply `AddValuation.map_le_sum` to reduce the goal to its premises. Introduce `x _`.

Rewrite using `[AddValuation.map_mul]`. Conclude with `add_nonneg (hF _) (hG _)`.
-/
theorem integral_mul' {F G : MvPolynomial σ K} (hF : Integral v F) (hG : Integral v G) :
    Integral v (F * G) := by
  classical
  unfold Integral at *
  intro α
  rw [MvPolynomial.coeff_mul]
  apply AddValuation.map_le_sum
  intro x _
  rw [AddValuation.map_mul]
  exact add_nonneg (hF _) (hG _)

/- English proof (translation)
Unfold `Integral`. Introduce `β`. Rewrite using `[MvPolynomial.coeff_monomial]`. Use `split_ifs`. Conclude with `hc`.

Simplify using the standard rewrite rules.
-/
theorem integral_monomial' (α : σ →₀ ℕ) {c : K} (hc : 0 ≤ v c) : Integral v (monomial α c) := by
  classical
  unfold Integral
  intro β
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · exact hc
  · simp

end General

section Deg

variable {K : Type} [Field K] {L L' : Type} {r : ℕ}

/- English proof (translation)
Establish `key : ∀ a : Fin r, (Finsupp.mapDomain (Prod.map f (id : Fin r → Fin r)) β) (i', a) = ∑ l, if f l = i' then β (l, a) else 0`. Introduce `a`. Rewrite using `[Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl (fun l _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hl : f l = i'`.

Simplify using `[Finsupp.single_apply, hl]`. Simplify using `[Finsupp.single_apply, hl]`. Simplify using `only [ldeg, key]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun l _ => ?_)` and prove the remaining obligations.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem ldeg_mapDomain [Fintype L] [DecidableEq L] [DecidableEq L'] (f : L → L') (β : L × Fin r →₀ ℕ)
    (i' : L') :
    ldeg (Finsupp.mapDomain (Prod.map f (id : Fin r → Fin r)) β) i' =
      ∑ l, if f l = i' then ldeg β l else 0 := by
  classical
  have key : ∀ a : Fin r, (Finsupp.mapDomain (Prod.map f (id : Fin r → Fin r)) β) (i', a) =
      ∑ l, if f l = i' then β (l, a) else 0 := by
    intro a
    rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum_fintype _ _ (by simp),
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    by_cases hl : f l = i'
    · simp [Finsupp.single_apply, hl]
    · simp [Finsupp.single_apply, hl]
  simp only [ldeg, key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  split_ifs <;> simp

/- English proof (translation)
Establish `hadd : ∀ (β γ : L × Fin r →₀ ℕ) (i : L), ldeg (β + γ) i = ldeg β i + ldeg γ i`. Introduce `β γ i`. Simplify using `[ldeg, Finset.sum_add_distrib]`. Establish `hmul : ∀ (d₁ d₂ : L → ℕ) (F G : MvPolynomial (L × Fin r) K), HomD d₁ F → HomD d₂ G → HomD (fun i => d₁ i + d₂ i) (F * G)`. Introduce `d₁ d₂ F G hF hG β hβ i`.

Take `⟨β₁, h₁, β₂, h₂, rfl⟩` from `Finset.mem_add.mp (MvPolynomial.support_mul F G hβ)`. Rewrite using `[hadd, hF β₁ h₁ i, hG β₂ h₂ i]`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `β hβ i`.

Simplify using `only [Finset.prod_empty, MvPolynomial.support_one, Finset.mem_singleton] at hβ`. Substitute `hβ` using the available equality. Simplify using `[ldeg]`. Consider the case `@insert a s ha ih`. Rewrite using `[Finset.prod_insert ha]`.

Establish `e : (fun i => ∑ k ∈ insert a s, d k i) = fun i => d a i + ∑ k ∈ s, d k i`. Use function extensionality and compare the values at `i`. Rewrite using `[Finset.sum_insert ha]`. Rewrite using `[e]`. Conclude with `hmul _ _ _ _ (h a (Finset.mem_insert_self a s)) (ih (fun k hk => h k (Finset.mem_insert_of_mem hk)))`.
-/
theorem HomD_prod {κ : Type} (s : Finset κ) (d : κ → L → ℕ) (f : κ → MvPolynomial (L × Fin r) K)
    (h : ∀ k ∈ s, HomD (d k) (f k)) : HomD (fun i => ∑ k ∈ s, d k i) (∏ k ∈ s, f k) := by
  classical
  have hadd : ∀ (β γ : L × Fin r →₀ ℕ) (i : L), ldeg (β + γ) i = ldeg β i + ldeg γ i := by
    intro β γ i
    simp [ldeg, Finset.sum_add_distrib]
  have hmul : ∀ (d₁ d₂ : L → ℕ) (F G : MvPolynomial (L × Fin r) K), HomD d₁ F → HomD d₂ G →
      HomD (fun i => d₁ i + d₂ i) (F * G) := by
    intro d₁ d₂ F G hF hG β hβ i
    obtain ⟨β₁, h₁, β₂, h₂, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul F G hβ)
    rw [hadd, hF β₁ h₁ i, hG β₂ h₂ i]
  induction s using Finset.induction_on with
  | empty =>
    intro β hβ i
    simp only [Finset.prod_empty, MvPolynomial.support_one, Finset.mem_singleton] at hβ
    subst hβ
    simp [ldeg]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have e : (fun i => ∑ k ∈ insert a s, d k i) = fun i => d a i + ∑ k ∈ s, d k i := by
      funext i
      rw [Finset.sum_insert ha]
    rw [e]
    exact hmul _ _ _ _ (h a (Finset.mem_insert_self a s))
      (ih (fun k hk => h k (Finset.mem_insert_of_mem hk)))

/- English proof (translation)
Introduce `β hβ i'`. Establish `hinj : Function.Injective (Prod.map f (id : Fin r → Fin r))`. Introduce and unpack `⟨a, b⟩ ⟨c, e⟩ hac`. Simplify using `only [Prod.map, id, Prod.mk.injEq] at hac`. Conclude with `Prod.ext (hf hac.1) hac.2`.

Rewrite `hβ` using `[MvPolynomial.support_rename_of_injective hinj, Finset.mem_image]`. Take `⟨β₀, h₀, rfl⟩` from `hβ`. Rewrite using `[ldeg_mapDomain]`. Use `Finset.sum_congr rfl (fun l _ => ?_)` and prove the remaining obligations. Rewrite using `[hG β₀ h₀ l]`.
-/
theorem HomD_rename [Fintype L] [DecidableEq L] [DecidableEq L'] (f : L → L')
    (hf : Function.Injective f) (d : L → ℕ) (G : MvPolynomial (L × Fin r) K) (hG : HomD d G) :
    HomD (fun i' => ∑ l, if f l = i' then d l else 0) (rename (Prod.map f (id : Fin r → Fin r)) G) := by
  classical
  intro β hβ i'
  have hinj : Function.Injective (Prod.map f (id : Fin r → Fin r)) := by
    rintro ⟨a, b⟩ ⟨c, e⟩ hac
    simp only [Prod.map, id, Prod.mk.injEq] at hac
    exact Prod.ext (hf hac.1) hac.2
  rw [MvPolynomial.support_rename_of_injective hinj, Finset.mem_image] at hβ
  obtain ⟨β₀, h₀, rfl⟩ := hβ
  rw [ldeg_mapDomain]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [hG β₀ h₀ l]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.sum_empty, Finset.prod_empty]`. Simplify using `[valS, lord, MvPolynomial.support_one]`. Introduce `b hb a ha`.

Rewrite `hb`, `ha` using `[MvPolynomial.coeff_one]`. Use `split_ifs at hb ha with hb0`. Rewrite `ha` using `[AddMonoidAlgebra.one_def]`. Unfold `AddMonoidAlgebra.single at ha`. Simplify using `at ha`.

Rewrite `ha` using `[Finsupp.single_apply]`. Use `split_ifs at ha with ha0`. Substitute `ha0` using the available equality. Simplify using the standard rewrite rules. Conclude with `absurd rfl ha`.

Conclude with `absurd rfl hb`. Consider the case `@insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.prod_insert ha]`. Conclude with `(add_le_add le_rfl ih).trans (by apply valS_mul_le)`.
-/
theorem valS_prod_le [DecidableEq L] (sg : L → Bool) (S : Finset L) {κ : Type} (s : Finset κ)
    (f : κ → MvPolynomial (L × Fin r) K) :
    ∑ k ∈ s, valS sg S (f k) ≤ valS sg S (∏ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty]
    simp [valS, lord, MvPolynomial.support_one]
    intro b hb a ha
    rw [MvPolynomial.coeff_one] at hb ha
    split_ifs at hb ha with hb0
    · rw [AddMonoidAlgebra.one_def] at ha
      unfold AddMonoidAlgebra.single at ha
      simp at ha
      rw [Finsupp.single_apply] at ha
      split_ifs at ha with ha0
      · subst ha0
        simp
      · exact absurd rfl ha
    · exact absurd rfl hb
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (add_le_add le_rfl ih).trans (by apply valS_mul_le)

end Deg

end Formalism.MainNotions.PlaneGram
