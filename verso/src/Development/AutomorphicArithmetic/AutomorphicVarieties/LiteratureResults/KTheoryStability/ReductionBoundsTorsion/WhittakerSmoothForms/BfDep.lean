import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.EtaTop

noncomputable section

open Set Filter Topology MeasureTheory

namespace PositivityTheory.KB.WhittakerCocycle

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Γ : Type} [Group Γ]
variable {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ}

def ext' {m : ℕ} (τ : Fin m → Γ) (n : ℕ) : Γ := if h : n < m then τ ⟨n, h⟩ else 1

/- English proof (translation)
Use `show IsClosed ({t : Fin q → ℝ | ∀ j, 0 ≤ t j} ∩ {t | ∑ j, t j ≤ 1})`. Apply `IsClosed.inter` to reduce the goal to its premises. Rewrite using `[Set.setOf_forall]`. Conclude with `isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)`. Conclude with `isClosed_le (continuous_finset_sum _ fun j _ => continuous_apply j) continuous_const`.
-/
private theorem isClosed_simplex_fin_sum_le_one (q : ℕ) : IsClosed {t : Fin q → ℝ | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1} := by
  show IsClosed ({t : Fin q → ℝ | ∀ j, 0 ≤ t j} ∩ {t | ∑ j, t j ≤ 1})
  apply IsClosed.inter
  · rw [Set.setOf_forall]
    exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
  · exact isClosed_le (continuous_finset_sum _ fun j _ => continuous_apply j) continuous_const

/- English proof (translation)
Establish `e : y 0 + ∑ j, t j • (y j.succ - y 0) = ∑ i, (Fin.cons (1 - ∑ j, t j) t : Fin (q + 1) → ℝ) i • y i`. Rewrite using `[Fin.sum_univ_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ, smul_sub, Finset.sum_sub_distrib, sub_smul, one_smul, ← Finset.sum_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`.

Apply `hU.sum_mem` to reduce the goal to its premises. Introduce `i _`. Consider the cases of `i using Fin.cases with`. Consider the case `zero`. Simplify using `only [Fin.cons_zero]`.

Combine the linear relations using `[ht.2]`. Consider the case `succ i`. Simplify using `only [Fin.cons_succ]`. Conclude with `ht.1 i`. Rewrite using `[Fin.sum_univ_succ]`.

Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Expand and normalize the polynomial expressions, which then agree. Introduce `i _`. Conclude with `hy i`.
-/
private theorem simplex_point_mem_of_convex_of_vertices_mem {q : ℕ} (hU : Convex ℝ U) (y : Fin (q + 1) → V) (hy : ∀ i, y i ∈ U)
    (t : Fin q → ℝ) (ht : (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1) :
    y 0 + ∑ j, t j • (y j.succ - y 0) ∈ U := by
  have e : y 0 + ∑ j, t j • (y j.succ - y 0) =
      ∑ i, (Fin.cons (1 - ∑ j, t j) t : Fin (q + 1) → ℝ) i • y i := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, smul_sub, Finset.sum_sub_distrib, sub_smul, one_smul,
      ← Finset.sum_smul]
    abel
  rw [e]
  apply hU.sum_mem
  · intro i _
    cases i using Fin.cases with
    | zero =>
      simp only [Fin.cons_zero]
      linarith [ht.2]
    | succ i =>
      simp only [Fin.cons_succ]
      exact ht.1 i
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    ring
  · intro i _
    exact hy i

/- English proof (translation)
Unfold `intS'`. Apply `setIntegral_congr_fun (isClosed_simplex_fin_sum_le_one q).measurableSet` to reduce the goal to its premises. Introduce `t ht`. Simplify using `only [hω _ (simplex_point_mem_of_convex_of_vertices_mem hU y hy t ht)]`.
-/
private theorem intS'_congr_of_eqOn_convex {q : ℕ} (hU : Convex ℝ U) (ω ω' : V → V [⋀^Fin q]→L[ℝ] ℝ)
    (hω : ∀ x ∈ U, ω x = ω' x) (y : Fin (q + 1) → V) (hy : ∀ i, y i ∈ U) :
    intS' ω y = intS' ω' y := by
  unfold intS'
  apply setIntegral_congr_fun (isClosed_simplex_fin_sum_le_one q).measurableSet
  intro t ht
  simp only [hω _ (simplex_point_mem_of_convex_of_vertices_mem hU y hy t ht)]

/- English proof (translation)
Unfold `intS'`. Apply `setIntegral_congr_fun (isClosed_simplex_fin_sum_le_one q).measurableSet` to reduce the goal to its premises. Introduce `t _`. Simplify using `only [ContinuousAlternatingMap.compContinuousLinearMap_apply, map_add, map_sum, map_smul, map_sub, Function.comp_def]`.
-/
private theorem intS'_comp_continuousLinearMap {q : ℕ} (ω : V → V [⋀^Fin q]→L[ℝ] ℝ) (B : V →L[ℝ] V)
    (y : Fin (q + 1) → V) :
    intS' ω (fun l => B (y l)) = intS' (fun x => (ω (B x)).compContinuousLinearMap B) y := by
  unfold intS'
  apply setIntegral_congr_fun (isClosed_simplex_fin_sum_le_one q).measurableSet
  intro t _
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, map_add, map_sum, map_smul,
    map_sub, Function.comp_def]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [Kf]`. Use `congr 1`. Use function extensionality and compare the values at `γ`. Rewrite using `[hD k c j (cons γ σ) (cons γ σ')]`.

Introduce `n hn`. Consider the cases of `n with`. Consider the case `zero => rfl`. Consider the case `succ m => exact h m (by omega)`.
-/
private theorem kf_eta_congr_of_eq_on_initial_of_pDep (hD : PDep A φ) {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (j : ℕ)
    (σ σ' : ℕ → Γ) (h : ∀ m, m + j ≤ k → σ m = σ' m) :
    Kf A φ (eta A φ c j) σ = Kf A φ (eta A φ c j) σ' := by
  funext x
  simp only [Kf]
  congr 1
  funext γ
  rw [hD k c j (cons γ σ) (cons γ σ')]
  intro n hn
  cases n with
  | zero => rfl
  | succ m => exact h m (by omega)

/- English proof (translation)
Simplify using `only [Bf]`. Rewrite using `[kf_eta_congr_of_eq_on_initial_of_pDep hD c j g g' (fun m hm => h m (by omega))]`. Use `congr 1`. Use function extensionality and compare the values at `l`. Rewrite using `[h _ (by have := l.isLt; omega)]`.
-/
theorem Bf_dep (hD : PDep A φ) {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (o : V) (j : ℕ) (hj : j ≤ k)
    (g g' : ℕ → Γ) (h : ∀ n ≤ k, g n = g' n) : Bf A φ c o j g = Bf A φ c o j g' := by
  simp only [Bf]
  rw [kf_eta_congr_of_eq_on_initial_of_pDep hD c j g g' (fun m hm => h m (by omega))]
  congr 1
  funext l
  rw [h _ (by have := l.isLt; omega)]

/- English proof (translation)
Simplify using `only [Bf]`. Establish `hpts : (fun l : Fin (j + 1) => A (x * g (k - j + ↑l)) o) = fun l : Fin (j + 1) => A x (A (g (k - j + ↑l)) o)`. Use function extensionality and compare the values at `l`. Rewrite using `[map_mul]`. Both sides reduce to the same expression.

Establish `hpsi : ∀ γ, ∀ h ∈ U, psi A φ γ (A x h) = psi A φ (x⁻¹ * γ) h`. Introduce `γ h _`. Simplify using `only [psi]`. Rewrite using `[mul_inv_rev, inv_inv, map_mul]`. Both sides reduce to the same expression.

Rewrite using `[hpts, intS'_comp_continuousLinearMap]`. Use `intS'_congr_of_eqOn_convex H.convex _ _ ?_ _ (fun _ => H.mapsTo _ o ho)` and prove the remaining obligations. Introduce `h hh`. Rewrite using `[(hE H k c hc.inv (A x) x⁻¹ (H.mapsTo x) hpsi j (fun n => x * g n) h hh).2]`. Simplify using `only [inv_mul_cancel_left]`.
-/
theorem Bf_inv (H : Hyp U A φ) (hE : PEquiv U A φ) {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (hc : Coc c)
    {o : V} (ho : o ∈ U) (j : ℕ) (x : Γ) (g : ℕ → Γ) :
    Bf A φ c o j (fun n => x * g n) = Bf A φ c o j g := by
  simp only [Bf]
  have hpts : (fun l : Fin (j + 1) => A (x * g (k - j + ↑l)) o) =
      fun l : Fin (j + 1) => A x (A (g (k - j + ↑l)) o) := by
    funext l
    rw [map_mul]
    rfl
  have hpsi : ∀ γ, ∀ h ∈ U, psi A φ γ (A x h) = psi A φ (x⁻¹ * γ) h := by
    intro γ h _
    simp only [psi]
    rw [mul_inv_rev, inv_inv, map_mul]
    rfl
  rw [hpts, intS'_comp_continuousLinearMap]
  refine intS'_congr_of_eqOn_convex H.convex _ _ ?_ _ (fun _ => H.mapsTo _ o ho)
  intro h hh
  rw [(hE H k c hc.inv (A x) x⁻¹ (H.mapsTo x) hpsi j (fun n => x * g n) h hh).2]
  simp only [inv_mul_cancel_left]

/- English proof (translation)
Simplify using `only [skip]`. Break down `lt_or_ge l.val i.val with hl | hl` into its components or cases. Rewrite using `[Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simpa using hl), if_pos (by omega)]`. Both sides reduce to the same expression. Rewrite using `[Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simpa using hl), if_neg (by omega)]`.

Simplify using `only [Fin.val_succ, Nat.add_assoc]`.
-/
private theorem apply_add_succAbove_eq_skip (g : ℕ → Γ) (a : ℕ) {n : ℕ} (i : Fin (n + 1)) (l : Fin n) :
    g (a + ↑(i.succAbove l)) = skip (a + ↑i) g (a + ↑l) := by
  simp only [skip]
  rcases lt_or_ge l.val i.val with hl | hl
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simpa using hl), if_pos (by omega)]
    rfl
  · rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simpa using hl), if_neg (by omega)]
    simp only [Fin.val_succ, Nat.add_assoc]

/- English proof (translation)
The claim follows from `| 0, _ => ⟨1, Or.inl rfl, fun _ => 0, fun _ _ => rfl, fun _ _ _ => rfl, fun g => by simp⟩ | j + 1, hj => by obtain ⟨s, hs, b, hbi, hbd, hb⟩ := tele H hH hSm hD hC hE hS c hc ho j (by omega) refine ⟨-s * (-1) ^ (k - j), ?_, fun g => b g + s * Bf A φ c o j g, ?_, ?_, fun g => ?_⟩ · …`.
-/
theorem tele (H : Hyp U A φ) (hH : PHom U A φ) (hSm : PSmooth U A φ) (hD : PDep A φ)
    (hC : PCoc U A φ) (hE : PEquiv U A φ) (hS : Stk U) {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ)
    (hc : Coc c) {o : V} (ho : o ∈ U) :
    ∀ j ≤ k + 1, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∃ b : (ℕ → Γ) → ℝ,
      (∀ x g, b (fun n => x * g n) = b g) ∧ (∀ g g', (∀ n ≤ k, g n = g' n) → b g = b g') ∧
      ∀ g, Wf A φ c o 0 g = ∑ i ∈ Finset.range (k + 2), (-1 : ℝ) ^ i * b (skip i g) + s * Wf A φ c o j g
  | 0, _ => ⟨1, Or.inl rfl, fun _ => 0, fun _ _ => rfl, fun _ _ _ => rfl, fun g => by simp⟩
  | j + 1, hj => by
    obtain ⟨s, hs, b, hbi, hbd, hb⟩ := tele H hH hSm hD hC hE hS c hc ho j (by omega)
    refine ⟨-s * (-1) ^ (k - j), ?_, fun g => b g + s * Bf A φ c o j g, ?_, ?_, fun g => ?_⟩
    · rcases hs with rfl | rfl <;> rcases neg_one_pow_eq_or ℝ (k - j) with h | h <;> rw [h] <;> norm_num
    · intro x g
      simp only [hbi, Bf_inv H hE c hc ho]
    · intro g g' hg
      simp only [hbd g g' hg, Bf_dep hD c o j (by omega) g g' hg]
    · rw [hb g]
      have hch := chain H hH hSm hD hC hS c hc ho (k - j) j (by omega) g
      have e : ∑ i ∈ Finset.range (k + 2), (-1 : ℝ) ^ i * (b (skip i g) + s * Bf A φ c o j (skip i g)) =
          ∑ i ∈ Finset.range (k + 2), (-1 : ℝ) ^ i * b (skip i g) +
            s * ∑ i ∈ Finset.range (k + 2), (-1 : ℝ) ^ i * Bf A φ c o j (skip i g) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [e, hch]
      ring

/- English proof (translation)
Establish `ez : eta A φ c 0 (ext' g) = fun _ => ContinuousAlternatingMap.constOfIsEmpty ℝ V (Fin 0) (c fun i => ext' g ↑i)` using `rfl`. Simplify using `only [Wf]`. Rewrite using `[ez]`. Unfold `intS'`. Simplify using `only [ContinuousAlternatingMap.constOfIsEmpty_apply]`.

Establish `hS : {t : Fin 0 → ℝ | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1} = Set.univ`. Use extensionality with `t`. Simplify using the standard rewrite rules. Establish `e : (fun i : Fin (k + 2) => ext' g ↑i) = g`. Use function extensionality and compare the values at `i`.

Simplify using `[ext', i.isLt]`. Rewrite using `[hS, e, setIntegral_univ, integral_const]`. Simplify using `[Measure.real, volume_pi, Measure.pi_empty_univ]`.
-/
private theorem wf_zero_ext'_eq {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (o : V) (g : Fin (k + 2) → Γ) :
    Wf A φ c o 0 (ext' g) = c g := by
  have ez : eta A φ c 0 (ext' g) =
      fun _ => ContinuousAlternatingMap.constOfIsEmpty ℝ V (Fin 0) (c fun i => ext' g ↑i) := rfl
  simp only [Wf]
  rw [ez]
  unfold intS'
  simp only [ContinuousAlternatingMap.constOfIsEmpty_apply]
  have hS : {t : Fin 0 → ℝ | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1} = Set.univ := by
    ext t
    simp
  have e : (fun i : Fin (k + 2) => ext' g ↑i) = g := by
    funext i
    simp [ext', i.isLt]
  rw [hS, e, setIntegral_univ, integral_const]
  simp [Measure.real, volume_pi, Measure.pi_empty_univ]

/- English proof (translation)
Establish `e` using `hC H k c hc (k + 1) le_rfl (cons (σ 0) σ') h hh`. Establish `h1 : eta A φ c (k + 1) (skip 0 (cons (σ 0) σ')) = eta A φ c (k + 1) σ'` using `hD k c (k + 1) _ _ (fun n hn => by`. Take `rfl : n = 0` from `by omega`. Use the proof step `rfl)`. Establish `h2 : eta A φ c (k + 1) (skip 1 (cons (σ 0) σ')) = eta A φ c (k + 1) σ` using `hD k c (k + 1) _ _ (fun n hn => by`.

Take `rfl : n = 0` from `by omega`. Use the proof step `rfl)`. Rewrite `e` using `[Nat.sub_self]`. Simplify using `only [delG, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, pow_zero, pow_one, one_smul, neg_smul, h1, h2] at e`. Rewrite `e` using `[add_neg_eq_zero]`.

Conclude with `e.symm`.
-/
private theorem eta_succ_congr_of_coc_of_mem (H : Hyp U A φ) (hD : PDep A φ) (hC : PCoc U A φ) {k : ℕ}
    (c : (Fin (k + 2) → Γ) → ℝ) (hc : Coc c) (σ σ' : ℕ → Γ) {h : V} (hh : h ∈ U) :
    eta A φ c (k + 1) σ h = eta A φ c (k + 1) σ' h := by
  have e := hC H k c hc (k + 1) le_rfl (cons (σ 0) σ') h hh
  have h1 : eta A φ c (k + 1) (skip 0 (cons (σ 0) σ')) = eta A φ c (k + 1) σ' :=
    hD k c (k + 1) _ _ (fun n hn => by
      obtain rfl : n = 0 := by omega
      rfl)
  have h2 : eta A φ c (k + 1) (skip 1 (cons (σ 0) σ')) = eta A φ c (k + 1) σ :=
    hD k c (k + 1) _ _ (fun n hn => by
      obtain rfl : n = 0 := by omega
      rfl)
  rw [Nat.sub_self] at e
  simp only [delG, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Finset.sum_apply,
    Pi.add_apply, Pi.smul_apply, pow_zero, pow_one, one_smul, neg_smul, h1, h2] at e
  rw [add_neg_eq_zero] at e
  exact e.symm

/- English proof (translation)
Introduce `H hStk k c hc o ho`. Take `⟨s, hs, b, hbi, hbd, hW⟩` from `tele H hH hSm hD hC hE hStk c hc ho (k + 1) le_rfl`. Use `⟨s, hs, fun y => b (ext' y), ?_, ?_⟩` and prove the remaining obligations. Introduce `x y beta_reduce`. Rewrite using `[← hbi x (ext' y)]`.

Apply `hbd` to reduce the goal to its premises. Introduce `n hn`. Simplify using `[ext', show n < k + 1 by omega]`. Introduce `g`. Establish `h0` using `hW (ext' g)`.

Rewrite `h0` using `[wf_zero_ext'_eq c o g]`. Establish `hWk : Wf A φ c o (k + 1) (ext' g) = intS' (eta A φ c (k + 1) fun _ => 1) (fun l : Fin (k + 2) => A (g l) o)`. Simplify using `only [Wf]`. Establish `ep : (fun l : Fin (k + 2) => A (ext' g (k + 1 - (k + 1) + ↑l)) o) = fun l : Fin (k + 2) => A (g l) o`. Use function extensionality and compare the values at `l`.

Simplify using `[ext', l.isLt]`. Rewrite using `[ep]`. Conclude with `intS'_congr_of_eqOn_convex H.convex _ _ (fun h hh => eta_succ_congr_of_coc_of_mem H hD hC c hc _ _ hh) _ (fun _ => H.mapsTo _ o ho)`. Establish `hsum : ∑ i ∈ Finset.range (k + 2), (-1 : ℝ) ^ i * b (skip i (ext' g)) = dC' (fun y => b (ext' y)) g`. Simplify using `only [dC']`.

Rewrite using `[Finset.sum_range]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Use `congr 1`. Apply `hbd` to reduce the goal to its premises.

Introduce `n hn`. Use `apply_add_succAbove_eq_skip (ext' g) 0 i (⟨n, by omega⟩ : Fin (k + 1))` as an intermediate fact. Simplify using `only [zero_add, Fin.val_mk] at this`. Rewrite using `[← this]`. Simplify using `[ext', show n < k + 1 by omega]`.

Rewrite `h0` using `[hWk, hsum]`. Rewrite using `[h0]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pComp (hH : PHom U A φ) (hSm : PSmooth U A φ) (hD : PDep A φ) (hC : PCoc U A φ)
    (hE : PEquiv U A φ) : PComp U A φ := by
  intro H hStk k c hc o ho
  obtain ⟨s, hs, b, hbi, hbd, hW⟩ := tele H hH hSm hD hC hE hStk c hc ho (k + 1) le_rfl
  refine ⟨s, hs, fun y => b (ext' y), ?_, ?_⟩
  · intro x y
    beta_reduce
    rw [← hbi x (ext' y)]
    apply hbd
    intro n hn
    simp [ext', show n < k + 1 by omega]
  · intro g
    have h0 := hW (ext' g)
    rw [wf_zero_ext'_eq c o g] at h0
    have hWk : Wf A φ c o (k + 1) (ext' g) =
        intS' (eta A φ c (k + 1) fun _ => 1) (fun l : Fin (k + 2) => A (g l) o) := by
      simp only [Wf]
      have ep : (fun l : Fin (k + 2) => A (ext' g (k + 1 - (k + 1) + ↑l)) o) =
          fun l : Fin (k + 2) => A (g l) o := by
        funext l
        simp [ext', l.isLt]
      rw [ep]
      exact intS'_congr_of_eqOn_convex H.convex _ _ (fun h hh => eta_succ_congr_of_coc_of_mem H hD hC c hc _ _ hh) _
        (fun _ => H.mapsTo _ o ho)
    have hsum : ∑ i ∈ Finset.range (k + 2), (-1 : ℝ) ^ i * b (skip i (ext' g)) =
        dC' (fun y => b (ext' y)) g := by
      simp only [dC']
      rw [Finset.sum_range]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      apply hbd
      intro n hn
      have := apply_add_succAbove_eq_skip (ext' g) 0 i (⟨n, by omega⟩ : Fin (k + 1))
      simp only [zero_add, Fin.val_mk] at this
      rw [← this]
      simp [ext', show n < k + 1 by omega]
    rw [hWk, hsum] at h0
    rw [h0]
    ring

end PositivityTheory.KB.WhittakerCocycle

end
