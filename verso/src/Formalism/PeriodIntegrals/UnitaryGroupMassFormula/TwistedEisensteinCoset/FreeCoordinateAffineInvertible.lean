import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.IaDivDown

open NumberField IsDedekindDomain Module

noncomputable section

namespace PI.TwistedEisensteinNonvanishing.W

open Loc LocE

section XX

variable {E : Type} [Field E]

/- English proof (translation)
Use function extensionality and compare the values at `l`. Simplify using `only [eN, Pi.single_apply]`. Distinguish the cases in `h : l = s`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[if_neg h, if_neg]`. Introduce `h'`. Conclude with `h (Fin.ext h')`.
-/
theorem xxw_eN_eq {N : ℕ} (s : Fin N) : eN E N s.1 = Pi.single s 1 := by
  funext l
  simp only [eN, Pi.single_apply]
  by_cases h : l = s
  · subst h
    simp
  · rw [if_neg h, if_neg]
    intro h'
    exact h (Fin.ext h')

/- English proof (translation)
Use `show (∀ l : Fin (n + c), l.1 ∉ {l | l < n + i} → v l = 0) ↔ _`. Simplify using `only [Set.mem_setOf_eq, not_lt]`.
-/
theorem xxw_mem_Ufl {n c i : ℕ} (v : Fin (n + c) → E) : v ∈ Ufl E n c i ↔ ∀ l : Fin (n + c), n + i ≤ l.1 → v l = 0 := by
  show (∀ l : Fin (n + c), l.1 ∉ {l | l < n + i} → v l = 0) ↔ _
  simp only [Set.mem_setOf_eq, not_lt]

/- English proof (translation)
Simplify using `only [xx1, Matrix.toLin'_apply, Matrix.mulVec_single_one]`. Both sides reduce to the same expression.
-/
theorem xxw_entry {n' c' n c : ℕ} (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) (t : FC n' c' n c → E) (s : Fin (n' + c')) (l : Fin (n + c)) :
    xx1 xj t (Pi.single s 1) l =
      if hf : IsFree n' n c l.1 s.1 then t ⟨(l, s), hf⟩
      else if hs : s.1 < n' then (if hl : l.1 < n then LinearMap.toMatrix' xj ⟨l.1, hl⟩ ⟨s.1, hs⟩ else 0)
      else if l.1 = n + (s.1 - n') then 1 else 0 := by
  simp only [xx1, Matrix.toLin'_apply, Matrix.mulVec_single_one]
  rfl

/- English proof (translation)
Establish `hinX : ∀ u : Fin n → E, inX E n c u ∈ Ufl E n c 0`. Introduce `u`. Rewrite using `[xxw_mem_Ufl]`. Introduce `l hl`. Simplify using `only [inX, LinearMap.pi_apply, dif_neg (show ¬ l.1 < n by omega), LinearMap.zero_apply]`.

Establish `hsum : inX E n c v = ∑ p : Fin n, v p • eN E (n + c) p.1`. Use function extensionality and compare the values at `l`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, eN, mul_ite, mul_one, mul_zero]`. Distinguish the cases in `hl : l.1 < n`.

Simplify using `only [inX, LinearMap.pi_apply, dif_pos hl, LinearMap.proj_apply]`. Rewrite using `[Finset.sum_eq_single ⟨l.1, hl⟩]`. Simplify using the standard rewrite rules. Introduce `p _ hp`. Rewrite using `[if_neg]`.

Introduce `h`. Conclude with `hp (Fin.ext h.symm)`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Simplify using `only [inX, LinearMap.pi_apply, dif_neg hl, LinearMap.zero_apply]`.

Use `symm`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `p _`. Rewrite using `[if_neg]`. Introduce `h`.

Use `p.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use function extensionality and compare the values at `l`. Distinguish the cases in `hl : l.1 < n`. Rewrite using `[hsum, map_sum]`.

Simplify using `only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Simplify using `only [inX, LinearMap.pi_apply, dif_pos hl, LinearMap.proj_apply, resX, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.of_apply]`. Use `Finset.sum_congr rfl (fun p _ => ?_)` and prove the remaining obligations. Rewrite using `[mul_comm]`. Both sides reduce to the same expression.

Establish `h1` using `hρ.1 0 _ (hinX v)`. Rewrite `h1` using `[xxw_mem_Ufl]`. Rewrite using `[h1 l (by omega)]`. Simplify using `only [inX, LinearMap.pi_apply, dif_neg hl, LinearMap.zero_apply]`.
-/
theorem xxw_res {n c : ℕ} {ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)} (hρ : R1cond E n c ρ) (v : Fin n → E) :
    ρ (inX E n c v) = inX E n c (resX ρ v) := by
  have hinX : ∀ u : Fin n → E, inX E n c u ∈ Ufl E n c 0 := by
    intro u
    rw [xxw_mem_Ufl]
    intro l hl
    simp only [inX, LinearMap.pi_apply, dif_neg (show ¬ l.1 < n by omega), LinearMap.zero_apply]
  have hsum : inX E n c v = ∑ p : Fin n, v p • eN E (n + c) p.1 := by
    funext l
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, eN, mul_ite, mul_one, mul_zero]
    by_cases hl : l.1 < n
    · simp only [inX, LinearMap.pi_apply, dif_pos hl, LinearMap.proj_apply]
      rw [Finset.sum_eq_single ⟨l.1, hl⟩]
      · simp
      · intro p _ hp
        rw [if_neg]
        intro h
        exact hp (Fin.ext h.symm)
      · intro h
        exact absurd (Finset.mem_univ _) h
    · simp only [inX, LinearMap.pi_apply, dif_neg hl, LinearMap.zero_apply]
      symm
      apply Finset.sum_eq_zero
      intro p _
      rw [if_neg]
      intro h
      have := p.isLt
      omega
  funext l
  by_cases hl : l.1 < n
  · rw [hsum, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp only [inX, LinearMap.pi_apply, dif_pos hl, LinearMap.proj_apply, resX, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Matrix.of_apply]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [mul_comm]
    rfl
  · have h1 := hρ.1 0 _ (hinX v)
    rw [xxw_mem_Ufl] at h1
    rw [h1 l (by omega)]
    simp only [inX, LinearMap.pi_apply, dif_neg hl, LinearMap.zero_apply]

/- English proof (translation)
Distinguish the cases in `hi : n + i < n + c`. Establish `hw : v - v ⟨n + i, hi⟩ • eN E (n + c) (n + i) ∈ Ufl E n c i`. Rewrite `hv`, the goal using `[xxw_mem_Ufl]`. Introduce `l hl`. Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, eN]`.

Distinguish the cases in `hli : l.1 = n + i`. Establish `hl' : l = ⟨n + i, hi⟩` using `Fin.ext hli`. Rewrite using `[if_pos hli, hl']`. Simplify using the standard rewrite rules. Rewrite using `[if_neg hli, mul_zero, sub_zero]`.

Conclude with `hv l (by omega)`. Establish `h1` using `hρ.1 i _ hw`. Establish `h2` using `hρ.2.2 i`. Establish `e1 : ρ v - v = (ρ (v - v ⟨n + i, hi⟩ • eN E (n + c) (n + i)) - (v - v ⟨n + i, hi⟩ • eN E (n + c) (n + i))) + v ⟨n + i, hi⟩ • (ρ (eN E (n + c) (n + i)) - eN E (n + c) (n + i))`. Rewrite using `[map_sub, map_smul, smul_sub]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e1]`. Conclude with `(Ufl E n c i).add_mem ((Ufl E n c i).sub_mem h1 hw) ((Ufl E n c i).smul_mem _ h2)`. Rewrite using `[xxw_mem_Ufl]`. Introduce `l hl`.

Use `l.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem xxw_step {n c : ℕ} {ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)} (hρ : R1cond E n c ρ) (i : ℕ)
    (v : Fin (n + c) → E) (hv : v ∈ Ufl E n c (i + 1)) : ρ v - v ∈ Ufl E n c i := by
  by_cases hi : n + i < n + c
  · have hw : v - v ⟨n + i, hi⟩ • eN E (n + c) (n + i) ∈ Ufl E n c i := by
      rw [xxw_mem_Ufl] at hv ⊢
      intro l hl
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, eN]
      by_cases hli : l.1 = n + i
      · have hl' : l = ⟨n + i, hi⟩ := Fin.ext hli
        rw [if_pos hli, hl']
        simp
      · rw [if_neg hli, mul_zero, sub_zero]
        exact hv l (by omega)
    have h1 := hρ.1 i _ hw
    have h2 := hρ.2.2 i
    have e1 : ρ v - v = (ρ (v - v ⟨n + i, hi⟩ • eN E (n + c) (n + i)) -
        (v - v ⟨n + i, hi⟩ • eN E (n + c) (n + i))) +
        v ⟨n + i, hi⟩ • (ρ (eN E (n + c) (n + i)) - eN E (n + c) (n + i)) := by
      rw [map_sub, map_smul, smul_sub]
      abel
    rw [e1]
    exact (Ufl E n c i).add_mem ((Ufl E n c i).sub_mem h1 hw) ((Ufl E n c i).smul_mem _ h2)
  · rw [xxw_mem_Ufl]
    intro l hl
    have := l.isLt
    omega

/- English proof (translation)
Use function extensionality and compare the values at `l`. Simplify using `only [xxw_entry, dif_neg hs]`.
-/
private theorem xx1_single_eq_of_not_lt {n' c' n c : ℕ} (xj : (Fin n' → E) →ₗ[E] (Fin n → E))
    (t : FC n' c' n c → E) (s : Fin (n' + c')) (hs : ¬ s.1 < n') :
    xx1 xj t (Pi.single s 1) = xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) t (Pi.single s 1) := by
  funext l
  simp only [xxw_entry, dif_neg hs]

/- English proof (translation)
Use function extensionality and compare the values at `l`. Rewrite using `[xxw_entry]`. Establish `hnf : ¬ IsFree n' n c l.1 s.1` using `fun h => by have := h.1; omega`. Rewrite using `[dif_neg hnf, dif_pos hs]`. Simplify using `only [inX, LinearMap.pi_apply]`.

Distinguish the cases in `hl : l.1 < n`. Rewrite using `[dif_pos hl, dif_pos hl, LinearMap.proj_apply, LinearMap.toMatrix'_apply]`. Rewrite using `[dif_neg hl, dif_neg hl, LinearMap.zero_apply]`.
-/
private theorem xx1_single_eq_inX_of_lt {n' c' n c : ℕ} (xj : (Fin n' → E) →ₗ[E] (Fin n → E))
    (t : FC n' c' n c → E) (s : Fin (n' + c')) (hs : s.1 < n') :
    xx1 xj t (Pi.single s 1) = inX E n c (xj (Pi.single ⟨s.1, hs⟩ 1)) := by
  funext l
  rw [xxw_entry]
  have hnf : ¬ IsFree n' n c l.1 s.1 := fun h => by have := h.1; omega
  rw [dif_neg hnf, dif_pos hs]
  simp only [inX, LinearMap.pi_apply]
  by_cases hl : l.1 < n
  · rw [dif_pos hl, dif_pos hl, LinearMap.proj_apply, LinearMap.toMatrix'_apply]
  · rw [dif_neg hl, dif_neg hl, LinearMap.zero_apply]

/- English proof (translation)
Introduce `l hl`. Rewrite using `[xxw_entry]`. Establish `hnf : ¬ IsFree n' n c l.1 s.1`. Introduce and unpack `⟨-, h | ⟨-, h⟩⟩`. Use linear arithmetic over natural numbers and integers.

Use linear arithmetic over natural numbers and integers. Rewrite using `[dif_neg hnf, dif_neg hs]`. Both sides reduce to the same expression.
-/
private theorem xx1_single_apply_eq_eN_of_le {n' c' n c : ℕ} (xj : (Fin n' → E) →ₗ[E] (Fin n → E))
    (t : FC n' c' n c → E) (s : Fin (n' + c')) (hs : ¬ s.1 < n') (hj : s.1 - n' < c) :
    ∀ l : Fin (n + c), n + (s.1 - n') ≤ l.1 →
      xx1 xj t (Pi.single s 1) l = eN E (n + c) (n + (s.1 - n')) l := by
  intro l hl
  rw [xxw_entry]
  have hnf : ¬ IsFree n' n c l.1 s.1 := by
    rintro ⟨-, h | ⟨-, h⟩⟩
    · omega
    · omega
  rw [dif_neg hnf, dif_neg hs]
  rfl

/- English proof (translation)
Introduce `E _ n' c' n c ρ hρ xj t`. Take `⟨h1, -⟩` from `hρ`. Apply `(Pi.basisFun E (Fin (n' + c'))).ext` to reduce the goal to its premises. Introduce `s`. Rewrite using `[Pi.basisFun_apply]`.

Use function extensionality and compare the values at `l`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[xxw_entry]`. Distinguish the cases in `hf : IsFree n' n c l.1 s.1`. Rewrite using `[dif_pos hf]`.

Establish `hs : ¬ s.1 < n'` using `by have := hf.1; omega`. Rewrite using `[xx1_single_eq_of_not_lt xj t s hs]`. Use `show _ = (ρ.toLinearMap ∘ₗ xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) t) (eN E (n' + c') s.1) l`. Rewrite using `[xxw_eN_eq]`. Both sides reduce to the same expression.

Rewrite using `[dif_neg hf]`. Distinguish the cases in `hs : s.1 < n'`. Rewrite using `[dif_pos hs, xx1_single_eq_inX_of_lt xj t s hs, xxw_res h1]`. Simplify using `only [inX, LinearMap.pi_apply]`. Distinguish the cases in `hl : l.1 < n`.

Rewrite using `[dif_pos hl, dif_pos hl, LinearMap.proj_apply, LinearMap.toMatrix'_apply, LinearMap.comp_apply]`. Rewrite using `[dif_neg hl, dif_neg hl, LinearMap.zero_apply]`. Rewrite using `[dif_neg hs]`. Establish `hj : s.1 - n' < c`. Assume the negation of the conclusion as `hj`.

Apply `hf` to reduce the goal to its premises. Use `⟨by omega, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hjc : s.1 - n' = c`. Conclude with `Or.inl hjc`. Conclude with `Or.inr ⟨by omega, by have := l.isLt; omega⟩`.

Distinguish the cases in `hj0 : s.1 - n' = 0`. Establish `hcol : xx1 xj t (Pi.single s 1) = eN E (n + c) n`. Use function extensionality and compare the values at `l'`. Rewrite using `[xxw_entry]`. Establish `hnf : ¬ IsFree n' n c l'.1 s.1`.

Apply the tactic sequence `rintro ⟨-, h | ⟨h, -⟩⟩ <;> omega`. Rewrite using `[dif_neg hnf, dif_neg hs, hj0, add_zero]`. Both sides reduce to the same expression. Rewrite using `[hcol, h1.2.1, hj0, add_zero]`. Both sides reduce to the same expression.

Establish `hl : n + (s.1 - n') ≤ l.1`. Assume the negation of the conclusion as `hl`. Apply `hf` to reduce the goal to its premises. Conclude with `⟨by omega, Or.inr ⟨by omega, by omega⟩⟩`. Establish `hu : xx1 xj t (Pi.single s 1) - eN E (n + c) (n + (s.1 - n')) ∈ Ufl E n c (s.1 - n')`.

Rewrite using `[xxw_mem_Ufl]`. Introduce `l' hl'`. Rewrite using `[Pi.sub_apply, xx1_single_apply_eq_eN_of_le xj t s hs hj l' hl', sub_self]`. Establish `hA` using `h1.1 _ _ hu`. Establish `hB` using `h1.2.2 (s.1 - n')`.

Establish `hC` using `(Ufl E n c (s.1 - n')).add_mem hA hB`. Rewrite `hC` using `[map_sub, xxw_mem_Ufl]`. Establish `h3` using `hC l hl`. Simplify using `only [Pi.add_apply, Pi.sub_apply] at h3`. Establish `e2 : ρ (xx1 xj t (Pi.single s 1)) l = eN E (n + c) (n + (s.1 - n')) l`.

Take the linear combination `h3`. Rewrite using `[e2]`. Both sides reduce to the same expression.
-/
theorem unfolding_affine_space_invariant : XXP := by
  intro E _ n' c' n c ρ hρ xj t
  obtain ⟨h1, -⟩ := hρ
  apply (Pi.basisFun E (Fin (n' + c'))).ext
  intro s
  rw [Pi.basisFun_apply]
  funext l
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [xxw_entry]
  by_cases hf : IsFree n' n c l.1 s.1
  · rw [dif_pos hf]
    have hs : ¬ s.1 < n' := by have := hf.1; omega
    rw [xx1_single_eq_of_not_lt xj t s hs]
    show _ = (ρ.toLinearMap ∘ₗ xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) t) (eN E (n' + c') s.1) l
    rw [xxw_eN_eq]
    rfl
  · rw [dif_neg hf]
    by_cases hs : s.1 < n'
    · rw [dif_pos hs, xx1_single_eq_inX_of_lt xj t s hs, xxw_res h1]
      simp only [inX, LinearMap.pi_apply]
      by_cases hl : l.1 < n
      · rw [dif_pos hl, dif_pos hl, LinearMap.proj_apply, LinearMap.toMatrix'_apply,
          LinearMap.comp_apply]
      · rw [dif_neg hl, dif_neg hl, LinearMap.zero_apply]
    · rw [dif_neg hs]
      have hj : s.1 - n' < c := by
        by_contra hj
        apply hf
        refine ⟨by omega, ?_⟩
        by_cases hjc : s.1 - n' = c
        · exact Or.inl hjc
        · exact Or.inr ⟨by omega, by have := l.isLt; omega⟩
      by_cases hj0 : s.1 - n' = 0
      · have hcol : xx1 xj t (Pi.single s 1) = eN E (n + c) n := by
          funext l'
          rw [xxw_entry]
          have hnf : ¬ IsFree n' n c l'.1 s.1 := by
            rintro ⟨-, h | ⟨h, -⟩⟩ <;> omega
          rw [dif_neg hnf, dif_neg hs, hj0, add_zero]
          rfl
        rw [hcol, h1.2.1, hj0, add_zero]
        rfl
      · have hl : n + (s.1 - n') ≤ l.1 := by
          by_contra hl
          apply hf
          exact ⟨by omega, Or.inr ⟨by omega, by omega⟩⟩
        have hu : xx1 xj t (Pi.single s 1) - eN E (n + c) (n + (s.1 - n')) ∈ Ufl E n c (s.1 - n') := by
          rw [xxw_mem_Ufl]
          intro l' hl'
          rw [Pi.sub_apply, xx1_single_apply_eq_eN_of_le xj t s hs hj l' hl', sub_self]
        have hA := h1.1 _ _ hu
        have hB := h1.2.2 (s.1 - n')
        have hC := (Ufl E n c (s.1 - n')).add_mem hA hB
        rw [map_sub, xxw_mem_Ufl] at hC
        have h3 := hC l hl
        simp only [Pi.add_apply, Pi.sub_apply] at h3
        have e2 : ρ (xx1 xj t (Pi.single s 1)) l = eN E (n + c) (n + (s.1 - n')) l := by
          linear_combination h3
        rw [e2]
        rfl

/- English proof (translation)
Use function extensionality and compare the values at `p`. Establish `h1` using `congrFun h (Fin.castAdd c p)`. Simplify `h1` using `[inX, LinearMap.pi_apply, Fin.coe_castAdd, p.isLt]`.
-/
theorem xxw_inX_inj {n c : ℕ} {v w : Fin n → E} (h : inX E n c v = inX E n c w) : v = w := by
  funext p
  have h1 := congrFun h (Fin.castAdd c p)
  simpa [inX, LinearMap.pi_apply, Fin.coe_castAdd, p.isLt] using h1

/- English proof (translation)
Introduce `E _ n' n c ρ hρ y`. Take `⟨h1, h2⟩` from `hρ`. Use `⟨resX ρ⁻¹ ∘ₗ y, ?_⟩` and prove the remaining obligations. Establish `key : ∀ u : Fin n → E, resX ρ (resX ρ⁻¹ u) = u`. Introduce `u`.

Apply `xxw_inX_inj (c := c)` to reduce the goal to its premises. Rewrite using `[← xxw_res h1, ← xxw_res h2, ← LinearEquiv.mul_apply, mul_inv_cancel]`. Both sides reduce to the same expression. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`.

Simplify using `only [LinearMap.comp_apply]`. Conclude with `key (y x)`.
-/
theorem restriction_to_affine_surjective : ResXSurjP := by
  intro E _ n' n c ρ hρ y
  obtain ⟨h1, h2⟩ := hρ
  refine ⟨resX ρ⁻¹ ∘ₗ y, ?_⟩
  have key : ∀ u : Fin n → E, resX ρ (resX ρ⁻¹ u) = u := by
    intro u
    apply xxw_inX_inj (c := c)
    rw [← xxw_res h1, ← xxw_res h2, ← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  exact key (y x)

/- English proof (translation)
Use function extensionality and compare the values at `l`. Simplify using `only [Pi.sub_apply, xxw_entry]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem xxw_diff {n' c' n c : ℕ} (t : FC n' c' n c → E) (s : Fin (n' + c')) :
    xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) t (Pi.single s 1) - xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) 0 (Pi.single s 1) =
      fun l => if hf : IsFree n' n c l.1 s.1 then t ⟨(l, s), hf⟩ else 0 := by
  funext l
  simp only [Pi.sub_apply, xxw_entry]
  split_ifs <;> simp

def xxwLin {n' c' n c : ℕ} (ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)) : (FC n' c' n c → E) →ₗ[E] (FC n' c' n c → E) where
  toFun t f := ρ (fun l => if hf : IsFree n' n c l.1 f.1.2.1 then t ⟨(l, f.1.2), hf⟩ else 0) f.1.1
  map_add' t t' := by
    funext f
    have hv : (fun l : Fin (n + c) => if hf : IsFree n' n c l.1 f.1.2.1 then (t + t') ⟨(l, f.1.2), hf⟩ else 0) =
        (fun l : Fin (n + c) => if hf : IsFree n' n c l.1 f.1.2.1 then t ⟨(l, f.1.2), hf⟩ else 0) +
        (fun l : Fin (n + c) => if hf : IsFree n' n c l.1 f.1.2.1 then t' ⟨(l, f.1.2), hf⟩ else 0) := by
      funext l
      simp only [Pi.add_apply]
      split_ifs <;> simp
    show ρ _ f.1.1 = ρ _ f.1.1 + ρ _ f.1.1
    rw [hv, map_add]
    rfl
  map_smul' a t := by
    funext f
    have hv : (fun l : Fin (n + c) => if hf : IsFree n' n c l.1 f.1.2.1 then (a • t) ⟨(l, f.1.2), hf⟩ else 0) =
        a • (fun l : Fin (n + c) => if hf : IsFree n' n c l.1 f.1.2.1 then t ⟨(l, f.1.2), hf⟩ else 0) := by
      funext l
      simp only [Pi.smul_apply, smul_eq_mul]
      split_ifs <;> simp
    show ρ _ f.1.1 = a * ρ _ f.1.1
    rw [hv, map_smul]
    rfl

/- English proof (translation)
Use function extensionality and compare the values at `f`. Simplify using `only [Tr, Pi.add_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[xxw_eN_eq]`. Establish `h` using `xxw_diff (E := E) t f.1.2`. Rewrite `h` using `[sub_eq_iff_eq_add]`.

Rewrite using `[h, map_add, Pi.add_apply]`. Both sides reduce to the same expression.
-/
theorem xxw_tr_eq {n' c' n c : ℕ} (ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)) (t : FC n' c' n c → E) :
    Tr ρ t = xxwLin ρ t + Tr ρ 0 := by
  funext f
  simp only [Tr, Pi.add_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [xxw_eN_eq]
  have h := xxw_diff (E := E) t f.1.2
  rw [sub_eq_iff_eq_add] at h
  rw [h, map_add, Pi.add_apply]
  rfl

/- English proof (translation)
Establish `hρi : ρ⁻¹ ∈ R1 E n c` using `inv_mem hρ`. Establish `e1` using `unfolding_affine_space_invariant E n' c' n c ρ hρ 0 t`. Establish `e2` using `unfolding_affine_space_invariant E n' c' n c ρ⁻¹ hρi 0 (Tr ρ t)`. Rewrite `e1`, `e2` using `[LinearMap.comp_zero]`. Establish `e3 : xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) (Tr ρ⁻¹ (Tr ρ t)) = xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) t`.

Rewrite using `[← e2, ← e1]`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[← LinearEquiv.mul_apply, inv_mul_cancel]`.

Both sides reduce to the same expression. Use function extensionality and compare the values at `f`. Establish `h` using `congrFun (LinearMap.congr_fun e3 (Pi.single f.1.2 1)) f.1.1`. Rewrite `h` using `[xxw_entry, xxw_entry, dif_pos f.2, dif_pos f.2]`. Conclude with `h`.
-/
theorem xxw_tr_inv {n' c' n c : ℕ} {ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)} (hρ : ρ ∈ R1 E n c) (t : FC n' c' n c → E) :
    Tr ρ⁻¹ (Tr ρ t) = t := by
  have hρi : ρ⁻¹ ∈ R1 E n c := inv_mem hρ
  have e1 := unfolding_affine_space_invariant E n' c' n c ρ hρ 0 t
  have e2 := unfolding_affine_space_invariant E n' c' n c ρ⁻¹ hρi 0 (Tr ρ t)
  rw [LinearMap.comp_zero] at e1 e2
  have e3 : xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) (Tr ρ⁻¹ (Tr ρ t)) =
      xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) t := by
    rw [← e2, ← e1]
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]
    rfl
  funext f
  have h := congrFun (LinearMap.congr_fun e3 (Pi.single f.1.2 1)) f.1.1
  rw [xxw_entry, xxw_entry, dif_pos f.2, dif_pos f.2] at h
  exact h

/- English proof (translation)
Introduce `E _ n' c' n c ρ hρ`. Establish `hρi : ρ⁻¹ ∈ R1 E n c` using `inv_mem hρ`. Establish `key : ∀ σ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E), σ ∈ R1 E n c → ∀ t : FC n' c' n c → E, xxwLin σ⁻¹ (xxwLin σ t) = t`. Introduce `σ hσ t`. Establish `h1` using `xxw_tr_inv hσ t`.

Establish `h0` using `xxw_tr_inv hσ (0 : FC n' c' n c → E)`. Rewrite `h1` using `[xxw_tr_eq σ⁻¹, xxw_tr_eq σ t, map_add]`. Rewrite `h0` using `[xxw_tr_eq σ⁻¹]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨{ xxwLin ρ with invFun := xxwLin ρ⁻¹, left_inv := key ρ hρ, right_inv := ?_ }, fun t => xxw_tr_eq ρ t⟩` and prove the remaining obligations.

Introduce `t`. Use `key ρ⁻¹ hρi t` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis.
-/
theorem free_coordinate_affine_invertible : TrAffP := by
  intro E _ n' c' n c ρ hρ
  have hρi : ρ⁻¹ ∈ R1 E n c := inv_mem hρ
  have key : ∀ σ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E), σ ∈ R1 E n c →
      ∀ t : FC n' c' n c → E, xxwLin σ⁻¹ (xxwLin σ t) = t := by
    intro σ hσ t
    have h1 := xxw_tr_inv hσ t
    have h0 := xxw_tr_inv hσ (0 : FC n' c' n c → E)
    rw [xxw_tr_eq σ⁻¹, xxw_tr_eq σ t, map_add] at h1
    rw [xxw_tr_eq σ⁻¹] at h0
    calc xxwLin σ⁻¹ (xxwLin σ t) = (xxwLin σ⁻¹ (xxwLin σ t) + xxwLin σ⁻¹ (Tr σ 0) + Tr σ⁻¹ 0) -
          (xxwLin σ⁻¹ (Tr σ 0) + Tr σ⁻¹ 0) := by abel
      _ = t - 0 := by rw [h1, h0]
      _ = t := sub_zero t
  refine ⟨{ xxwLin ρ with invFun := xxwLin ρ⁻¹, left_inv := key ρ hρ, right_inv := ?_ },
    fun t => xxw_tr_eq ρ t⟩
  intro t
  have := key ρ⁻¹ hρi t
  rwa [inv_inv] at this

/- English proof (translation)
Introduce `E _ n' c' n c ρ hρ xj t`. Take `⟨h1, -⟩` from `hρ`. Unfold `chArg`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun i hi => ?_)` and prove the remaining obligations.

Establish `hic : i < c` using `Finset.mem_range.mp hi`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe]`. Distinguish the cases in `hs : n' + i + 1 < n' + c'`. Take `⟨s, hs_eq⟩ : ∃ s : Fin (n' + c'), s.1 = n' + i + 1` from `⟨⟨_, hs⟩, rfl⟩`. Rewrite using `[← hs_eq, xxw_eN_eq s]`.

Establish `hsn : ¬ s.1 < n'` using `by omega`. Establish `hu : xx1 xj t (Pi.single s 1) - xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) 0 (Pi.single s 1) ∈ Ufl E n c (i + 1)`. Rewrite using `[xx1_single_eq_of_not_lt xj t s hsn, xxw_diff, xxw_mem_Ufl]`. Introduce `l hl`. Establish `hlt` using `l.isLt`.

Rewrite using `[dif_neg]`. Apply the tactic sequence `rintro ⟨-, h | ⟨-, h⟩⟩ <;> omega`. Establish `hstep` using `xxw_step h1 i _ hu`. Rewrite `hstep` using `[xxw_mem_Ufl]`. Establish `hn : n + i < n + c` using `by omega`.

Establish `h2` using `hstep ⟨n + i, hn⟩ le_rfl`. Establish `h0 : xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) 0 (Pi.single s 1) ⟨n + i, hn⟩ = 0`. Rewrite using `[xxw_entry, dif_pos]`. Both sides reduce to the same expression. Use `⟨by omega, Or.inr ⟨by omega, Or.inr ?_⟩⟩` and prove the remaining obligations.

Simplify using `only [Fin.val_mk]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [atN, dif_pos hn]`. Rewrite `h2` using `[map_sub, Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, h0]`. Take the linear combination `h2`.

Establish `h0 : eN E (n' + c') (n' + i + 1) = 0`. Use function extensionality and compare the values at `l`. Simplify using `only [eN, Pi.zero_apply]`. Rewrite using `[if_neg]`. Use `l.isLt` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite using `[h0]`. Simplify using `[atN]`.
-/
theorem character_argument_constant_shift : ChArgP := by
  intro E _ n' c' n c ρ hρ xj t
  obtain ⟨h1, -⟩ := hρ
  unfold chArg
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hic : i < c := Finset.mem_range.mp hi
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  by_cases hs : n' + i + 1 < n' + c'
  · obtain ⟨s, hs_eq⟩ : ∃ s : Fin (n' + c'), s.1 = n' + i + 1 := ⟨⟨_, hs⟩, rfl⟩
    rw [← hs_eq, xxw_eN_eq s]
    have hsn : ¬ s.1 < n' := by omega
    have hu : xx1 xj t (Pi.single s 1) -
        xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) 0 (Pi.single s 1) ∈ Ufl E n c (i + 1) := by
      rw [xx1_single_eq_of_not_lt xj t s hsn, xxw_diff, xxw_mem_Ufl]
      intro l hl
      have hlt := l.isLt
      rw [dif_neg]
      rintro ⟨-, h | ⟨-, h⟩⟩ <;> omega
    have hstep := xxw_step h1 i _ hu
    rw [xxw_mem_Ufl] at hstep
    have hn : n + i < n + c := by omega
    have h2 := hstep ⟨n + i, hn⟩ le_rfl
    have h0 : xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) 0 (Pi.single s 1) ⟨n + i, hn⟩ = 0 := by
      rw [xxw_entry, dif_pos]
      · rfl
      · refine ⟨by omega, Or.inr ⟨by omega, Or.inr ?_⟩⟩
        simp only [Fin.val_mk]
        omega
    simp only [atN, dif_pos hn]
    rw [map_sub, Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, h0] at h2
    linear_combination h2
  · have h0 : eN E (n' + c') (n' + i + 1) = 0 := by
      funext l
      simp only [eN, Pi.zero_apply]
      rw [if_neg]
      have := l.isLt
      omega
    rw [h0]
    simp [atN]

end XX

end PI.TwistedEisensteinNonvanishing.W
