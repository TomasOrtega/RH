import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.BoxBoundAlt

noncomputable section

open NumberField Matrix

namespace PI.UnitaryGroupMassFormula.LCG

open PI.LatCountG

/- English proof (translation)
Simplify using `[hsN, Formalism.REAL.hs]`.
-/
theorem hsN_zero {n : ℕ} : hsN (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  simp [hsN, Formalism.REAL.hs]

/- English proof (translation)
The claim follows from `Real.sqrt_nonneg _`.
-/
theorem hsN_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hsN A := Real.sqrt_nonneg _

/- English proof (translation)
The claim follows from `γ.2`.
-/
theorem mem_gf (I : Formalism.MainNotions.S.AutInst) (γ : I.GFset) :
    ∃ g : GL (Fin I.n) I.E, g ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧
      (∀ v, Formalism.MainNotions.S.uMat ((γ : I.GA).1 v) = (I.P v)⁻¹ * (g : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) ∧
      I.fmat (γ : I.GA).2 = (g : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) := γ.2

def gm (I : Formalism.MainNotions.S.AutInst) (γ : I.GFset) : Matrix (Fin I.n) (Fin I.n) I.E :=
  (((mem_gf I γ).choose : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E)

/- English proof (translation)
The claim follows from `(mem_gf I γ).choose_spec.2`.
-/
theorem gm_spec (I : Formalism.MainNotions.S.AutInst) (γ : I.GFset) :
    (∀ v, Formalism.MainNotions.S.uMat ((γ : I.GA).1 v) = (I.P v)⁻¹ * (gm I γ).map (I.φ v) * I.P v) ∧
      I.fmat (γ : I.GA).2 = (gm I γ).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) := (mem_gf I γ).choose_spec.2

/- English proof (translation)
Take `⟨h1a, h1b⟩` from `gm_spec I γ`. Take `⟨h2a, h2b⟩` from `gm_spec I γ'`. Rewrite `h1a`, `h1b` using `[h]`. Apply `Subtype.ext` to reduce the goal to its premises. Use `Prod.ext (funext fun v => ?_) ?_` and prove the remaining obligations.

Conclude with `Subtype.ext (Units.ext ((h1a v).trans (h2a v).symm))`. Conclude with `Subtype.ext (Units.ext (h1b.trans h2b.symm))`.
-/
theorem gm_inj (I : Formalism.MainNotions.S.AutInst) {γ γ' : I.GFset} (h : gm I γ = gm I γ') : γ = γ' := by
  obtain ⟨h1a, h1b⟩ := gm_spec I γ
  obtain ⟨h2a, h2b⟩ := gm_spec I γ'
  rw [h] at h1a h1b
  apply Subtype.ext
  refine Prod.ext (funext fun v => ?_) ?_
  · exact Subtype.ext (Units.ext ((h1a v).trans (h2a v).symm))
  · exact Subtype.ext (Units.ext (h1b.trans h2b.symm))

/- English proof (translation)
Take `⟨h1, -⟩` from `gm_spec I γ`. Rewrite using `[amat, ← h1 v]`. Simplify using `only [Formalism.MainNotions.S.uMat, Prod.fst_mul, Prod.fst_inv, Pi.mul_apply, Pi.inv_apply, Subgroup.coe_mul, Units.val_mul]`.
-/
theorem phi_eq (I : Formalism.MainNotions.S.AutInst) (x y : I.GA) (γ : I.GFset) (v : InfinitePlace I.F) :
    Formalism.MainNotions.S.uMat ((x⁻¹ * (γ : I.GA) * y).1 v) = amat I x y v (gm I γ) := by
  obtain ⟨h1, -⟩ := gm_spec I γ
  rw [amat, ← h1 v]
  simp only [Formalism.MainNotions.S.uMat, Prod.fst_mul, Prod.fst_inv, Pi.mul_apply, Pi.inv_apply, Subgroup.coe_mul,
    Units.val_mul]

/- English proof (translation)
Establish `hm : (δ₁ - δ₂).map (I.φ v) = δ₁.map (I.φ v) - δ₂.map (I.φ v)`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Simplify using `only [amat, hm, mul_sub, sub_mul]`.
-/
theorem amat_sub (I : Formalism.MainNotions.S.AutInst) (x y : I.GA) (v : InfinitePlace I.F) (δ₁ δ₂ : Matrix (Fin I.n) (Fin I.n) I.E) :
    amat I x y v (δ₁ - δ₂) = amat I x y v δ₁ - amat I x y v δ₂ := by
  have hm : (δ₁ - δ₂).map (I.φ v) = δ₁.map (I.φ v) - δ₂.map (I.φ v) := by
    ext i j; simp
  simp only [amat, hm, mul_sub, sub_mul]

/- English proof (translation)
Introduce `I x y hx hy r hr S hSc`. Establish `hn : 1 ≤ I.n` using `hN I x hx`. Take `⟨ρ, hρdef⟩ : ∃ ρ, ρ = PI.LatCountG.tau1 I x * PI.LatCountG.tau1 I y` from `⟨_, rfl⟩`. Rewrite using `[← hρdef]`. Establish `hρ : 0 < ρ` using `by rw [hρdef]; exact mul_pos hx hy`.

Establish `hτx : PI.LatCountG.tau1 I x ≤ 1 / 2` using `by unfold PI.LatCountG.tau1; exact min_le_left _ _`. Establish `hτy : PI.LatCountG.tau1 I y ≤ 1 / 2` using `by unfold PI.LatCountG.tau1; exact min_le_left _ _`. Establish `hρle : ∀ v, ρ ≤ Real.sqrt I.n * Real.exp (r v)` using `fun v => by`. Establish `h0 : ρ ≤ 1 / 2 * (1 / 2)` using `by rw [hρdef]; exact mul_le_mul hτx hτy hy.le (by norm_num)`. Establish `h2 : (1 : ℝ) ≤ Real.sqrt I.n`.

Rewrite using `[← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hn)`. Establish `h3 : (1 : ℝ) ≤ Real.exp (r v)` using `Real.one_le_exp (hr v)`. Use the polynomial consequences of the given equalities and inequalities. Set `g : I.GFset → (InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ)` to `fun γ v => amat I x y v (gm I γ)`. Establish `hgsub : ∀ γ γ' : I.GFset, ∀ v, g γ v - g γ' v = amat I x y v (gm I γ - gm I γ')` using `fun γ γ' v => (amat_sub I x y v _ _).symm`.

Establish `hlat : ∀ γ ∈ S, ∀ u ∈ PI.LatCountG.latSet I y, gm I γ *ᵥ u ∈ PI.LatCountG.latSet I x` using `fun γ hγ u hu => hLM I x y γ (mem_gf I γ).choose (gm_spec I γ).2 (hSc γ hγ).1 u hu`. Establish `hsep : ∀ γ ∈ S, ∀ γ' ∈ S, gm I γ ≠ gm I γ' → ∃ v, ρ ≤ hsN (g γ v - g γ' v)`. Introduce `γ hγ γ' hγ' hne`. Establish `hδ : gm I γ - gm I γ' ≠ 0` using `sub_ne_zero.mpr hne`. Establish `hmap : ∀ u ∈ PI.LatCountG.latSet I y, (gm I γ - gm I γ') *ᵥ u ∈ PI.LatCountG.latSet I x`.

Introduce `u hu`. Rewrite using `[Matrix.sub_mulVec]`. Conclude with `hLS I x _ _ (hlat γ hγ u hu) (hlat γ' hγ' u hu)`. Establish `hineq` using `hS I x y hx hy _ hδ hmap`. Rewrite `hineq` using `[← hρdef]`.

Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hprod : ∏ v, hsN (g γ v - g γ' v) < ρ ^ I.f`. Rewrite using `[← hC I, ← Finset.card_univ, ← Finset.prod_const]`. Distinguish the cases in `h0 : ∃ v, hsN (g γ v - g γ' v) = 0`.

Take `⟨v, hv⟩` from `h0`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ v) hv]`. Conclude with `Finset.prod_pos fun _ _ => hρ`. Use `push_neg at h0`. Establish `hne' : (Finset.univ : Finset (InfinitePlace I.F)).Nonempty`.

Assume the negation of the conclusion as `he`. Rewrite `he` using `[Finset.not_nonempty_iff_eq_empty, Finset.univ_eq_empty_iff]`. Establish `hf0 : I.f = 0` using `by rw [← hC I]; exact Fintype.card_eq_zero`. Establish `hpos : 0 < I.f` using `by first`. Consider the case `exact (hC I) ▸ Fintype.card_pos`.

Consider the case `unfold Formalism.MainNotions.S.AutInst.f`. Conclude with `Module.finrank_pos`. Use linear arithmetic over natural numbers and integers. Conclude with `Finset.prod_lt_prod_of_nonempty (fun v _ => lt_of_le_of_ne (hsN_nonneg _) (h0 v).symm) (fun v _ => hcon v) hne'`. Simplify using `only [hgsub] at hprod`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hinj : Set.InjOn g S`. Introduce `γ hγ γ' hγ' heq`. Assume the negation of the conclusion as `hne`. Take `⟨v, hv⟩` from `hsep γ hγ γ' hγ' (fun h => hne (gm_inj I h))`.

Rewrite `hv` using `[heq, sub_self, hsN_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbound : ∀ p ∈ S.image g, ∀ v, hsN (p v) ≤ Real.sqrt I.n * Real.exp (r v)`. Introduce `p hp v`. Take `⟨γ, hγ, rfl⟩` from `Finset.mem_image.mp hp`.

Use `show hsN (amat I x y v (gm I γ)) ≤ _`. Rewrite using `[← phi_eq]`. Use `(hB I.n (I.ε v) ((x⁻¹ * (γ : I.GA) * y).1 v)).trans ?_` and prove the remaining obligations. Use `gcongr`. Conclude with `(hSc γ hγ).2 v`.

Establish `hsepT : ∀ p ∈ S.image g, ∀ q ∈ S.image g, p ≠ q → ∃ v, ρ ≤ hsN (p v - q v)`. Introduce `p hp q hq hpq`. Take `⟨γ, hγ, rfl⟩` from `Finset.mem_image.mp hp`. Take `⟨γ', hγ', rfl⟩` from `Finset.mem_image.mp hq`. Conclude with `hsep γ hγ γ' hγ' (fun h => hpq (by simp only [g, h]))`.

Establish `hpack` using `hP (InfinitePlace I.F) I.n (fun v => Real.sqrt I.n * Real.exp (r v)) (fun _ => ρ) (fun _ => hρ) (fun v => by positivity) (S.image g) hbound hsepT`. Establish `hexp : ∏ v, Real.exp (r v) ^ (2 * I.n ^ 2) = Real.exp (2 * (I.n : ℝ) ^ 2 * ∑ v, r v)`. Rewrite using `[Finset.mul_sum, Real.exp_sum]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[← Real.exp_nat_mul]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hnn : ∀ v, 0 ≤ 2 * (Real.sqrt I.n * Real.exp (r v)) + ρ` using `fun v => by`. Use `Real.sqrt_nonneg (I.n : ℝ)` as an intermediate fact.

Use `Real.exp_pos (r v)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation. Use `Finset.prod_le_prod (fun v _ => pow_nonneg (div_nonneg (hnn v) hρ.le) _) (fun v _ => ?_)` and prove the remaining obligations. Use `pow_le_pow_left₀ (div_nonneg (hnn v) hρ.le) ?_ _` and prove the remaining obligations.

Rewrite using `[div_mul_eq_mul_div]`. Use `gcongr`. Use polynomial arithmetic with `[hρle v]`. Use `_ = (∏ v : InfinitePlace I.F, (3 * Real.sqrt I.n / ρ) ^ (2 * I.n ^ 2)) * ∏ v, Real.exp (r v) ^ (2 * I.n ^ 2) := by`. Rewrite using `[← Finset.prod_mul_distrib]`.

Repeatedly rewrite using `[mul_pow]`. Use `_ = _ := by rw [hexp, Finset.prod_const, Finset.card_univ, hC I, ← pow_mul]`.
-/
theorem latCountAll_of (hB : BoxBound) (hLM : LatMap) (hLS : LatSub) (hS : Sep) (hP : PackLem) (hN : NPos)
    (hC : CardPl) : LatCountAll := by
  classical
  intro I x y hx hy r hr S hSc
  have hn : 1 ≤ I.n := hN I x hx
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = PI.LatCountG.tau1 I x * PI.LatCountG.tau1 I y := ⟨_, rfl⟩
  rw [← hρdef]
  have hρ : 0 < ρ := by rw [hρdef]; exact mul_pos hx hy
  have hτx : PI.LatCountG.tau1 I x ≤ 1 / 2 := by unfold PI.LatCountG.tau1; exact min_le_left _ _
  have hτy : PI.LatCountG.tau1 I y ≤ 1 / 2 := by unfold PI.LatCountG.tau1; exact min_le_left _ _
  have hρle : ∀ v, ρ ≤ Real.sqrt I.n * Real.exp (r v) := fun v => by
    have h0 : ρ ≤ 1 / 2 * (1 / 2) := by rw [hρdef]; exact mul_le_mul hτx hτy hy.le (by norm_num)
    have h2 : (1 : ℝ) ≤ Real.sqrt I.n := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
    have h3 : (1 : ℝ) ≤ Real.exp (r v) := Real.one_le_exp (hr v)
    nlinarith
  let g : I.GFset → (InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) :=
    fun γ v => amat I x y v (gm I γ)
  have hgsub : ∀ γ γ' : I.GFset, ∀ v, g γ v - g γ' v = amat I x y v (gm I γ - gm I γ') :=
    fun γ γ' v => (amat_sub I x y v _ _).symm
  have hlat : ∀ γ ∈ S, ∀ u ∈ PI.LatCountG.latSet I y, gm I γ *ᵥ u ∈ PI.LatCountG.latSet I x :=
    fun γ hγ u hu => hLM I x y γ (mem_gf I γ).choose (gm_spec I γ).2 (hSc γ hγ).1 u hu
  have hsep : ∀ γ ∈ S, ∀ γ' ∈ S, gm I γ ≠ gm I γ' → ∃ v, ρ ≤ hsN (g γ v - g γ' v) := by
    intro γ hγ γ' hγ' hne
    have hδ : gm I γ - gm I γ' ≠ 0 := sub_ne_zero.mpr hne
    have hmap : ∀ u ∈ PI.LatCountG.latSet I y,
        (gm I γ - gm I γ') *ᵥ u ∈ PI.LatCountG.latSet I x := by
      intro u hu
      rw [Matrix.sub_mulVec]
      exact hLS I x _ _ (hlat γ hγ u hu) (hlat γ' hγ' u hu)
    have hineq := hS I x y hx hy _ hδ hmap
    rw [← hρdef] at hineq
    by_contra hcon
    push_neg at hcon
    have hprod : ∏ v, hsN (g γ v - g γ' v) < ρ ^ I.f := by
      rw [← hC I, ← Finset.card_univ, ← Finset.prod_const]
      by_cases h0 : ∃ v, hsN (g γ v - g γ' v) = 0
      · obtain ⟨v, hv⟩ := h0
        rw [Finset.prod_eq_zero (Finset.mem_univ v) hv]
        exact Finset.prod_pos fun _ _ => hρ
      · push_neg at h0
        have hne' : (Finset.univ : Finset (InfinitePlace I.F)).Nonempty := by
          by_contra he
          rw [Finset.not_nonempty_iff_eq_empty, Finset.univ_eq_empty_iff] at he
          have hf0 : I.f = 0 := by rw [← hC I]; exact Fintype.card_eq_zero
          have hpos : 0 < I.f := by
            first
              | exact (hC I) ▸ Fintype.card_pos
              | unfold Formalism.MainNotions.S.AutInst.f; exact Module.finrank_pos
          omega
        exact Finset.prod_lt_prod_of_nonempty
          (fun v _ => lt_of_le_of_ne (hsN_nonneg _) (h0 v).symm) (fun v _ => hcon v) hne'
    simp only [hgsub] at hprod
    linarith
  have hinj : Set.InjOn g S := by
    intro γ hγ γ' hγ' heq
    by_contra hne
    obtain ⟨v, hv⟩ := hsep γ hγ γ' hγ' (fun h => hne (gm_inj I h))
    rw [heq, sub_self, hsN_zero] at hv
    linarith
  have hbound : ∀ p ∈ S.image g, ∀ v, hsN (p v) ≤ Real.sqrt I.n * Real.exp (r v) := by
    intro p hp v
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
    show hsN (amat I x y v (gm I γ)) ≤ _
    rw [← phi_eq]
    refine (hB I.n (I.ε v) ((x⁻¹ * (γ : I.GA) * y).1 v)).trans ?_
    gcongr
    exact (hSc γ hγ).2 v
  have hsepT : ∀ p ∈ S.image g, ∀ q ∈ S.image g, p ≠ q → ∃ v, ρ ≤ hsN (p v - q v) := by
    intro p hp q hq hpq
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨γ', hγ', rfl⟩ := Finset.mem_image.mp hq
    exact hsep γ hγ γ' hγ' (fun h => hpq (by simp only [g, h]))
  have hpack := hP (InfinitePlace I.F) I.n (fun v => Real.sqrt I.n * Real.exp (r v)) (fun _ => ρ)
    (fun _ => hρ) (fun v => by positivity) (S.image g) hbound hsepT
  have hexp : ∏ v, Real.exp (r v) ^ (2 * I.n ^ 2) = Real.exp (2 * (I.n : ℝ) ^ 2 * ∑ v, r v) := by
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hnn : ∀ v, 0 ≤ 2 * (Real.sqrt I.n * Real.exp (r v)) + ρ := fun v => by
    have := Real.sqrt_nonneg (I.n : ℝ)
    have := Real.exp_pos (r v)
    nlinarith
  calc (S.card : ℝ) = ((S.image g).card : ℝ) := by rw [Finset.card_image_of_injOn hinj]
    _ ≤ ∏ v, ((2 * (Real.sqrt I.n * Real.exp (r v)) + ρ) / ρ) ^ (2 * I.n ^ 2) := hpack
    _ ≤ ∏ v, ((3 * Real.sqrt I.n / ρ) * Real.exp (r v)) ^ (2 * I.n ^ 2) := by
        refine Finset.prod_le_prod (fun v _ => pow_nonneg (div_nonneg (hnn v) hρ.le) _)
          (fun v _ => ?_)
        refine pow_le_pow_left₀ (div_nonneg (hnn v) hρ.le) ?_ _
        rw [div_mul_eq_mul_div]
        gcongr
        nlinarith [hρle v]
    _ = (∏ v : InfinitePlace I.F, (3 * Real.sqrt I.n / ρ) ^ (2 * I.n ^ 2)) *
          ∏ v, Real.exp (r v) ^ (2 * I.n ^ 2) := by
        rw [← Finset.prod_mul_distrib]; simp_rw [mul_pow]
    _ = _ := by rw [hexp, Finset.prod_const, Finset.card_univ, hC I, ← pow_mul]

end PI.UnitaryGroupMassFormula.LCG
