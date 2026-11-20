import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldOneVariableTranscendentalFiniteAndEStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceOrderCalculusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceRestrictionExistsPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldFiniteSupportSumOrderEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleAdelicMatrixFamilyPullbackExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleAdelicMatrixFamilyOrdersFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixDegreeLeTwoMulOfUpperTriangularStatement

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef.QuotLine

variable {k K : Type} [Field k] [Field K] [Algebra k K]

/- English proof (translation)
Rewrite using `[Matrix.det_succ_column_zero, Fin.sum_univ_succ]`. Simplify using `[hM]`.
-/
theorem det_fac {r : ℕ} (M : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (hM : ∀ i : Fin r, M i.succ 0 = 0) :
    M.det = M 0 0 * (M.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [hM]

/- English proof (translation)
Establish `h` using `h1.2`. Rewrite `h` using `[det_fac M hM, map_mul, h2.2, mul_one]`. Conclude with `h`.
-/
theorem val_corner {r : ℕ} (v : Place k K) (M : Matrix (Fin (r + 1)) (Fin (r + 1)) K)
    (hM : ∀ i : Fin r, M i.succ 0 = 0) (h1 : Unimod v M)
    (h2 : Unimod v (M.submatrix Fin.succ Fin.succ)) : v.1 (M 0 0) = 1 := by
  have h := h1.2
  rw [det_fac M hM, map_mul, h2.2, mul_one] at h
  exact h

/- English proof (translation)
Simplify using `only [nrm, Fin.univ_succ, Finset.sup_cons, Finset.sup_map, Fin.cons_zero]`. Both sides reduce to the same expression.
-/
theorem nrm_cons {n : ℕ} (v : Place k K) (x : K) (y : Fin n → K) :
    nrm v (Fin.cons x y : Fin (n + 1) → K) = max (v.1 x) (nrm v y) := by
  simp only [nrm, Fin.univ_succ, Finset.sup_cons, Finset.sup_map, Fin.cons_zero]
  rfl

/- English proof (translation)
Establish `h1` using `nrm_cons v x ![y]`. Establish `h2` using `nrm_cons v y ![]`. Establish `h3 : nrm v (![] : Fin 0 → K) = 0` using `by simp [nrm]`. Rewrite `h2` using `[h3, max_eq_left (zero_le' )]`. Conclude with `h1.trans (by rw [← h2]; rfl)`.
-/
theorem nrm_two (v : Place k K) (x y : K) : nrm v ![x, y] = max (v.1 x) (v.1 y) := by
  have h1 := nrm_cons v x ![y]
  have h2 := nrm_cons v y ![]
  have h3 : nrm v (![] : Fin 0 → K) = 0 := by simp [nrm]
  rw [h3, max_eq_left (zero_le' )] at h2
  exact h1.trans (by rw [← h2]; rfl)

/- English proof (translation)
Introduce `k F _ _ _ _ _ hF r g hg hg0 hh b hb E _ _ _ _ _ ρ hρ m hm`. Establish `hE : IsFF k E` using `(GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext k F hF).2 E`. Take `⟨hGa, -, -, hGL⟩` from `GlobalTheory.T.isAdmissibleAdelicMatrixFamily_pullback_extension k F E hF ρ hρ (r + 1) g hg`. Take `⟨hQa, -, -, -⟩` from `GlobalTheory.T.isAdmissibleAdelicMatrixFamily_pullback_extension k F E hF ρ hρ r _ hh`. Establish `hGb` using `hGL b hb`.

Establish `hcF : ∀ v, Unimod v (g v) → Unimod v ((g v).submatrix Fin.succ Fin.succ) → v.1 (g v 0 0) = 1` using `fun v h1 h2 => val_corner v (g v) (hg0 v) h1 h2`. Establish `ha0 : ∀ v, g v 0 0 ≠ 0`. Introduce `v h0`. Apply `hg.1 v` to reduce the goal to its premises. Rewrite using `[det_fac (g v) (hg0 v), h0, zero_mul]`.

Take `⟨a1, ha1def⟩ : ∃ a1 : Place k F → Matrix (Fin 1) (Fin 1) F, a1 = fun v => !![g v 0 0]` from `⟨_, rfl⟩`. Establish `ha1 : admitted a1`. Use `⟨fun v => by simp [ha1def, ha0 v], (hg.2.union hh.2).subset ?_⟩` and prove the remaining obligations. Introduce `v hv`. Assume the negation of the conclusion as `hno`.

Simplify using `only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hno`. Establish `h1` using `hcF v hno.1 hno.2`. Apply `hv` to reduce the goal to its premises. Use `⟨fun i j => ?_, ?_⟩` and prove the remaining obligations. Use `fin_cases i`.

Use `fin_cases j`. Simplify using `[ha1def, h1]`. Simplify using `[ha1def, h1]`. Take `⟨-, hdeg1, -, -⟩` from `GlobalTheory.T.isAdmissibleAdelicMatrixFamily_pullback_extension k F E hF ρ hρ 1 a1 ha1`. Generalize the expression as in `hGdef : pullAd ρ g = G at hGa hGb`.

Generalize the expression as in `hQdef : pullAd ρ (fun v => (g v).submatrix Fin.succ Fin.succ) = Q at hQa ⊢`. Establish `hQG : ∀ p, Q p = (G p).submatrix Fin.succ Fin.succ`. Introduce `p`. Rewrite using `[← hQdef, ← hGdef]`. Both sides reduce to the same expression.

Establish `hG0 : ∀ p (i : Fin r), G p i.succ 0 = 0`. Introduce `p i`. Rewrite using `[← hGdef]`. Simplify using `[pullAd, hg0]`. Establish `hS : ∑ᶠ p, ord p (G p 0 0) = Module.finrank F E * ∑ᶠ v, ord v (g v 0 0)`.

Establish `e1 : deg (pullAd ρ a1) = ∑ᶠ p, ord p (G p 0 0)`. Unfold `deg`. Apply `finsum_congr` to reduce the goal to its premises. Introduce `p`. Rewrite using `[← hGdef]`.

Simplify using `[pullAd, ha1def]`. Establish `e2 : deg a1 = ∑ᶠ v, ord v (g v 0 0)`. Unfold `deg`. Apply `finsum_congr` to reduce the goal to its premises. Introduce `v`.

Simplify using `[ha1def]`. Rewrite using `[← e1, hdeg1, e2]`. Take `⟨-, hQm⟩` from `GlobalTheory.T.admissibleAdelicMatrixFamily_orders_finite k E hE r Q hQa`. Take `⟨hfinQm, hnz⟩` from `hQm m hm`. Establish `hord` using `fun p : Place k E => GlobalTheory.T.functionFieldPlaceOrder_calculus k E p`.

Use `choose idx hidx using fun p : Place k E => (hord p).2.2.2.2.2.2.1 r (Q p *ᵥ m) (hnz p)`. Take `⟨t, ht⟩ : ∃ t : Place k E → Matrix (Fin 2) (Fin 2) E, t = fun p => !![G p 0 0, ∑ j : Fin r, G p 0 j.succ * m j; 0, (Q p *ᵥ m) (idx p)]` from `⟨_, rfl⟩`. Establish `hdett : ∀ p, (t p).det = G p 0 0 * (Q p *ᵥ m) (idx p)`. Introduce `p`. Rewrite using `[ht, Matrix.det_fin_two_of]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hG00 : ∀ p, G p 0 0 ≠ 0`. Introduce `p h0`. Apply `hGa.1 p` to reduce the goal to its premises. Rewrite using `[det_fac (G p) (hG0 p), h0, zero_mul]`.

Establish `hcE : ∀ p, Unimod p (G p) → Unimod p (Q p) → p.1 (G p 0 0) = 1` using `fun p h1 h2 => val_corner p (G p) (hG0 p) h1 (by rw [← hQG]; exact h2)`. Establish `hmfin : ∀ j, {p : Place k E | ¬ p.1 (m j) ≤ 1}.Finite`. Introduce `j`. Distinguish the cases in `hj : m j = 0`. Simplify using `[hj]`.

Conclude with `((GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k E hE (m j) hj).1).subset fun p hp h1 => hp (le_of_eq h1)`. Establish `hta : admitted t`. Use `⟨fun p => by rw [hdett]; exact mul_ne_zero (hG00 p) (hidx p).1, ?_⟩` and prove the remaining obligations. Use `((hGa.2.union hQa.2).union (hfinQm.union (Set.finite_iUnion hmfin))).subset ?_` and prove the remaining obligations. Introduce `p hp`.

Assume the negation of the conclusion as `hno`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_exists, not_not] at hno`. Take `⟨⟨hGu, hQu⟩, hn1, hmj⟩` from `hno`. Apply `hp` to reduce the goal to its premises. Establish `hc1 : p.1 (G p 0 0) = 1` using `hcE p hGu hQu`.

Establish `hm1 : p.1 ((Q p *ᵥ m) (idx p)) = 1` using `by rw [← (hidx p).2.1]; exact hn1`. Establish `hcs : p.1 (∑ j : Fin r, G p 0 j.succ * m j) ≤ 1` using `Valuation.map_sum_le _ fun j _ => by rw [map_mul]; exact mul_le_one' (hGu.1 0 j.succ) (hmj j)`. Use `⟨fun i j => ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rw [ht]; fin_cases i <;> fin_cases j <;> simp [hc1, hm1, hcs]`. Rewrite using `[hdett, map_mul, hc1, hm1, one_mul]`.

Establish `htL : LinesLE t (b * Module.finrank F E)`. Introduce `E' _ _ _ _ _ ρ' hρ' w hw`. Establish `hres` using `(GlobalTheory.T.functionFieldPlace_restriction_exists_pow k E E').2 ρ' hρ'`. Take `⟨w', hw'def⟩ : ∃ w' : Fin (r + 1) → E', w' = Fin.cons (w 0) (fun j => w 1 * algebraMap E E' (m j))` from `⟨_, rfl⟩`. Establish `hw' : w' ≠ 0`.

Introduce `h0`. Apply `hw` to reduce the goal to its premises. Establish `h00 : w 0 = 0` using `by simpa [hw'def] using congr_fun h0 0`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, m j ≠ 0 := by`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Conclude with `hm (funext hc)`. Establish `h1 : w 1 * algebraMap E E' (m j) = 0` using `by simpa [hw'def] using congr_fun h0 j.succ`. Establish `h11 : w 1 = 0`. Break down `mul_eq_zero.1 h1 with h | h` into its components or cases.

Conclude with `h`. Conclude with `absurd ((map_eq_zero_iff _ (algebraMap E E').injective).1 h) hj`. Apply the tactic sequence `ext i; fin_cases i <;> simp [h00, h11]`. Establish `hloc : ∀ p', nrm p' (pullAd ρ' t p' *ᵥ w) = nrm p' (pullAd ρ' G p' *ᵥ w')`. Introduce `p'`.

Take `⟨e, -, he, -⟩` from `hres p'`. Establish `v1 : pullAd ρ' t p' *ᵥ w = ![algebraMap E E' (G (ρ' p') 0 0) * w 0 + algebraMap E E' (∑ j : Fin r, G (ρ' p') 0 j.succ * m j) * w 1, algebraMap E E' ((Q (ρ' p') *ᵥ m) (idx (ρ' p'))) * w 1]`. Apply the tactic sequence `ext i; fin_cases i <;> simp [pullAd, ht, Matrix.mulVec, dotProduct, Fin.sum_univ_two]`. Establish `v2 : pullAd ρ' G p' *ᵥ w' = Fin.cons (algebraMap E E' (G (ρ' p') 0 0) * w 0 + algebraMap E E' (∑ j : Fin r, G (ρ' p') 0 j.succ * m j) * w 1) (fun i => w 1 * algebraMap E E' ((Q (ρ' p') *ᵥ m) i))`. Use extensionality with `i`.

Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Simplify using `only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hw'def, Fin.cons_zero, Fin.cons_succ, pullAd, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul, Fin.cases_zero]`. Use `congr 1`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `j _`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `[pullAd, hw'def, hQG, hG0, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, map_sum, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]`. Rewrite using `[v1, v2, nrm_two, nrm_cons]`. Use `congr 1`. Establish `hs : (fun i => w 1 * algebraMap E E' ((Q (ρ' p') *ᵥ m) i)) = w 1 • (fun i => algebraMap E E' ((Q (ρ' p') *ᵥ m) i))` using `by ext; simp [smul_eq_mul]`.

Rewrite using `[hs, (GlobalTheory.T.functionFieldPlaceOrder_calculus k E' p').2.2.2.2.2.2.2.1, map_mul, mul_comm]`. Use `congr 1`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `Finset.le_sup (f := fun i => p'.1 (algebraMap E E' ((Q (ρ' p') *ᵥ m) i))) (Finset.mem_univ (idx (ρ' p')))`. Apply `Finset.sup_le` to reduce the goal to its premises.

Introduce `j _`. Rewrite using `[he, he]`. Conclude with `pow_le_pow_left' ((hidx (ρ' p')).2.2.2 j) e`. Establish `heq : degLine (pullAd ρ' t) w = degLine (pullAd ρ' G) w'`. Simplify using `only [degLine, ordVec, hloc]`.

Rewrite using `[heq]`. Conclude with `hGb E' ρ' hρ' w' hw'`. Establish `hdeg` using `GlobalTheory.T.adelicMatrixDegree_le_two_mul_of_upperTriangular k E hE t hta (fun p => by simp [ht]) _ htL`. Establish `hs1 : (Function.support fun p : Place k E => ord p (G p 0 0)).Finite`. Use `(hGa.2.union hQa.2).subset ?_` and prove the remaining obligations.

Introduce `p hp`. Assume the negation of the conclusion as `hno`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hno`. Apply `hp` to reduce the goal to its premises. Simplify using `[ord, hcE p hno.1 hno.2]`.

Establish `hs2 : (Function.support fun p : Place k E => ordVec p (Q p *ᵥ m)).Finite`. Use `hfinQm.subset ?_` and prove the remaining obligations. Introduce `p hp hn`. Apply `hp` to reduce the goal to its premises. Simplify using `[ordVec, hn]`.

Establish `hsplit : deg t = (∑ᶠ p, ord p (G p 0 0)) + degLine Q m`. Unfold `deg degLine`. Rewrite using `[← finsum_add_distrib hs1 hs2]`. Apply `finsum_congr` to reduce the goal to its premises. Introduce `p`.

Rewrite using `[hdett, (hord p).1 _ _ (hG00 p) (hidx p).1, (hidx p).2.2.1]`. Rewrite `hsplit` using `[hS]`. Establish `hc : (degLine Q m : ℝ) = (deg t : ℝ) - (Module.finrank F E : ℝ) * ((∑ᶠ v, ord v (g v 0 0) : ℤ) : ℝ)`. Rewrite using `[hsplit]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc]`. Use polynomial arithmetic with `[hdeg]`.
-/
theorem quot_line_le : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (r : ℕ) (g : Place k F → Matrix (Fin (r + 1)) (Fin (r + 1)) F), admitted g → (∀ (v : Place k F) (i : Fin r), g v i.succ 0 = 0) → admitted (fun v => (g v).submatrix Fin.succ Fin.succ) → ∀ b : ℝ, LinesLE g b → LinesLE (fun v => (g v).submatrix Fin.succ Fin.succ) (2 * b - (∑ᶠ v, ord v (g v 0 0) : ℤ)) := by
  intro k F _ _ _ _ _ hF r g hg hg0 hh b hb E _ _ _ _ _ ρ hρ m hm
  have hE : IsFF k E := (GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext k F hF).2 E
  obtain ⟨hGa, -, -, hGL⟩ := GlobalTheory.T.isAdmissibleAdelicMatrixFamily_pullback_extension k F E hF ρ hρ (r + 1) g hg
  obtain ⟨hQa, -, -, -⟩ := GlobalTheory.T.isAdmissibleAdelicMatrixFamily_pullback_extension k F E hF ρ hρ r _ hh
  have hGb := hGL b hb

  have hcF : ∀ v, Unimod v (g v) → Unimod v ((g v).submatrix Fin.succ Fin.succ) → v.1 (g v 0 0) = 1 :=
    fun v h1 h2 => val_corner v (g v) (hg0 v) h1 h2
  have ha0 : ∀ v, g v 0 0 ≠ 0 := by
    intro v h0; apply hg.1 v; rw [det_fac (g v) (hg0 v), h0, zero_mul]
  obtain ⟨a1, ha1def⟩ : ∃ a1 : Place k F → Matrix (Fin 1) (Fin 1) F, a1 = fun v => !![g v 0 0] := ⟨_, rfl⟩
  have ha1 : admitted a1 := by
    refine ⟨fun v => by simp [ha1def, ha0 v], (hg.2.union hh.2).subset ?_⟩
    intro v hv
    by_contra hno
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hno
    have h1 := hcF v hno.1 hno.2
    apply hv
    refine ⟨fun i j => ?_, ?_⟩
    · fin_cases i; fin_cases j; simp [ha1def, h1]
    · simp [ha1def, h1]
  obtain ⟨-, hdeg1, -, -⟩ := GlobalTheory.T.isAdmissibleAdelicMatrixFamily_pullback_extension k F E hF ρ hρ 1 a1 ha1
  generalize hGdef : pullAd ρ g = G at hGa hGb
  generalize hQdef : pullAd ρ (fun v => (g v).submatrix Fin.succ Fin.succ) = Q at hQa ⊢
  have hQG : ∀ p, Q p = (G p).submatrix Fin.succ Fin.succ := by
    intro p; rw [← hQdef, ← hGdef]; rfl
  have hG0 : ∀ p (i : Fin r), G p i.succ 0 = 0 := by
    intro p i; rw [← hGdef]; simp [pullAd, hg0]
  have hS : ∑ᶠ p, ord p (G p 0 0) = Module.finrank F E * ∑ᶠ v, ord v (g v 0 0) := by
    have e1 : deg (pullAd ρ a1) = ∑ᶠ p, ord p (G p 0 0) := by
      unfold deg; apply finsum_congr; intro p; rw [← hGdef]; simp [pullAd, ha1def]
    have e2 : deg a1 = ∑ᶠ v, ord v (g v 0 0) := by
      unfold deg; apply finsum_congr; intro v; simp [ha1def]
    rw [← e1, hdeg1, e2]
  obtain ⟨-, hQm⟩ := GlobalTheory.T.admissibleAdelicMatrixFamily_orders_finite k E hE r Q hQa
  obtain ⟨hfinQm, hnz⟩ := hQm m hm
  have hord := fun p : Place k E => GlobalTheory.T.functionFieldPlaceOrder_calculus k E p
  choose idx hidx using fun p : Place k E => (hord p).2.2.2.2.2.2.1 r (Q p *ᵥ m) (hnz p)
  obtain ⟨t, ht⟩ : ∃ t : Place k E → Matrix (Fin 2) (Fin 2) E, t = fun p =>
      !![G p 0 0, ∑ j : Fin r, G p 0 j.succ * m j; 0, (Q p *ᵥ m) (idx p)] := ⟨_, rfl⟩
  have hdett : ∀ p, (t p).det = G p 0 0 * (Q p *ᵥ m) (idx p) := by
    intro p; rw [ht, Matrix.det_fin_two_of]; ring
  have hG00 : ∀ p, G p 0 0 ≠ 0 := by
    intro p h0; apply hGa.1 p; rw [det_fac (G p) (hG0 p), h0, zero_mul]
  have hcE : ∀ p, Unimod p (G p) → Unimod p (Q p) → p.1 (G p 0 0) = 1 :=
    fun p h1 h2 => val_corner p (G p) (hG0 p) h1 (by rw [← hQG]; exact h2)
  have hmfin : ∀ j, {p : Place k E | ¬ p.1 (m j) ≤ 1}.Finite := by
    intro j
    by_cases hj : m j = 0
    · simp [hj]
    · exact ((GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k E hE (m j) hj).1).subset fun p hp h1 => hp (le_of_eq h1)
  have hta : admitted t := by
    refine ⟨fun p => by rw [hdett]; exact mul_ne_zero (hG00 p) (hidx p).1, ?_⟩
    refine ((hGa.2.union hQa.2).union (hfinQm.union (Set.finite_iUnion hmfin))).subset ?_
    intro p hp
    by_contra hno
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_exists, not_not] at hno
    obtain ⟨⟨hGu, hQu⟩, hn1, hmj⟩ := hno
    apply hp
    have hc1 : p.1 (G p 0 0) = 1 := hcE p hGu hQu
    have hm1 : p.1 ((Q p *ᵥ m) (idx p)) = 1 := by rw [← (hidx p).2.1]; exact hn1
    have hcs : p.1 (∑ j : Fin r, G p 0 j.succ * m j) ≤ 1 :=
      Valuation.map_sum_le _ fun j _ => by rw [map_mul]; exact mul_le_one' (hGu.1 0 j.succ) (hmj j)
    refine ⟨fun i j => ?_, ?_⟩
    · rw [ht]; fin_cases i <;> fin_cases j <;> simp [hc1, hm1, hcs]
    · rw [hdett, map_mul, hc1, hm1, one_mul]
  have htL : LinesLE t (b * Module.finrank F E) := by
    intro E' _ _ _ _ _ ρ' hρ' w hw
    have hres := (GlobalTheory.T.functionFieldPlace_restriction_exists_pow k E E').2 ρ' hρ'
    obtain ⟨w', hw'def⟩ : ∃ w' : Fin (r + 1) → E', w' = Fin.cons (w 0) (fun j => w 1 * algebraMap E E' (m j)) :=
      ⟨_, rfl⟩
    have hw' : w' ≠ 0 := by
      intro h0
      apply hw
      have h00 : w 0 = 0 := by simpa [hw'def] using congr_fun h0 0
      obtain ⟨j, hj⟩ : ∃ j, m j ≠ 0 := by
        by_contra hc; push_neg at hc; exact hm (funext hc)
      have h1 : w 1 * algebraMap E E' (m j) = 0 := by simpa [hw'def] using congr_fun h0 j.succ
      have h11 : w 1 = 0 := by
        rcases mul_eq_zero.1 h1 with h | h
        · exact h
        · exact absurd ((map_eq_zero_iff _ (algebraMap E E').injective).1 h) hj
      ext i; fin_cases i <;> simp [h00, h11]
    have hloc : ∀ p', nrm p' (pullAd ρ' t p' *ᵥ w) = nrm p' (pullAd ρ' G p' *ᵥ w') := by
      intro p'
      obtain ⟨e, -, he, -⟩ := hres p'
      have v1 : pullAd ρ' t p' *ᵥ w = ![algebraMap E E' (G (ρ' p') 0 0) * w 0 +
          algebraMap E E' (∑ j : Fin r, G (ρ' p') 0 j.succ * m j) * w 1,
          algebraMap E E' ((Q (ρ' p') *ᵥ m) (idx (ρ' p'))) * w 1] := by
        ext i; fin_cases i <;> simp [pullAd, ht, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      have v2 : pullAd ρ' G p' *ᵥ w' = Fin.cons (algebraMap E E' (G (ρ' p') 0 0) * w 0 +
          algebraMap E E' (∑ j : Fin r, G (ρ' p') 0 j.succ * m j) * w 1)
          (fun i => w 1 * algebraMap E E' ((Q (ρ' p') *ᵥ m) i)) := by
        ext i; refine Fin.cases ?_ (fun i => ?_) i
        · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hw'def, Fin.cons_zero, Fin.cons_succ,
            pullAd, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul, Fin.cases_zero]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          ring
        · simp [pullAd, hw'def, hQG, hG0, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, map_sum,
            Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
      rw [v1, v2, nrm_two, nrm_cons]
      congr 1
      have hs : (fun i => w 1 * algebraMap E E' ((Q (ρ' p') *ᵥ m) i)) =
          w 1 • (fun i => algebraMap E E' ((Q (ρ' p') *ᵥ m) i)) := by
        ext; simp [smul_eq_mul]
      rw [hs, (GlobalTheory.T.functionFieldPlaceOrder_calculus k E' p').2.2.2.2.2.2.2.1, map_mul, mul_comm]
      congr 1
      apply le_antisymm
      · exact Finset.le_sup (f := fun i => p'.1 (algebraMap E E' ((Q (ρ' p') *ᵥ m) i)))
          (Finset.mem_univ (idx (ρ' p')))
      · apply Finset.sup_le; intro j _
        rw [he, he]; exact pow_le_pow_left' ((hidx (ρ' p')).2.2.2 j) e
    have heq : degLine (pullAd ρ' t) w = degLine (pullAd ρ' G) w' := by
      simp only [degLine, ordVec, hloc]
    rw [heq]; exact hGb E' ρ' hρ' w' hw'
  have hdeg := GlobalTheory.T.adelicMatrixDegree_le_two_mul_of_upperTriangular k E hE t hta (fun p => by simp [ht]) _ htL
  have hs1 : (Function.support fun p : Place k E => ord p (G p 0 0)).Finite := by
    refine (hGa.2.union hQa.2).subset ?_
    intro p hp
    by_contra hno
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hno
    apply hp
    simp [ord, hcE p hno.1 hno.2]
  have hs2 : (Function.support fun p : Place k E => ordVec p (Q p *ᵥ m)).Finite := by
    refine hfinQm.subset ?_
    intro p hp hn
    apply hp
    simp [ordVec, hn]
  have hsplit : deg t = (∑ᶠ p, ord p (G p 0 0)) + degLine Q m := by
    unfold deg degLine
    rw [← finsum_add_distrib hs1 hs2]
    apply finsum_congr; intro p
    rw [hdett, (hord p).1 _ _ (hG00 p) (hidx p).1, (hidx p).2.2.1]
  rw [hS] at hsplit
  have hc : (degLine Q m : ℝ) = (deg t : ℝ) - (Module.finrank F E : ℝ) * ((∑ᶠ v, ord v (g v 0 0) : ℤ) : ℝ) := by
    rw [hsplit]; push_cast; ring
  rw [hc]
  nlinarith [hdeg]

end GlobalTheory.Nef.QuotLine
