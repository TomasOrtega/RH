import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ZScalarVanish
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.MultisetProdNormLeOne

noncomputable section

namespace PI.WGL.XiA

open Formalism.BasicNotions MvPolynomial

/- English proof (translation)
Unfold `embGL blkHom`. Simplify using `[Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply]`. Establish `hl : ∀ (x : Fin N) (hx : x.1 < n), finSumFinEquiv.symm (Fin.cast h.symm x) = (Sum.inl ⟨x.1, hx⟩ : Fin n ⊕ Fin 1)`. Introduce `x hx`. Establish `hc : Fin.cast h.symm x = Fin.castAdd 1 ⟨x.1, hx⟩` using `Fin.ext rfl`.

Rewrite using `[hc, finSumFinEquiv_symm_apply_castAdd]`. Establish `hr : ∀ (x : Fin N), ¬ x.1 < n → finSumFinEquiv.symm (Fin.cast h.symm x) = (Sum.inr 0 : Fin n ⊕ Fin 1)`. Introduce `x hx`. Establish `hxN` using `x.isLt`. Establish `hc : Fin.cast h.symm x = Fin.natAdd n (0 : Fin 1)` using `Fin.ext (by simp; omega)`.

Rewrite using `[hc, finSumFinEquiv_symm_apply_natAdd]`. Apply the tactic sequence `by_cases ha : a.1 < n <;> by_cases hb : b.1 < n`. Rewrite using `[hl a ha, hl b hb]`. Simplify using `[ha, hb]`. Rewrite using `[hl a ha, hr b hb]`.

Simplify using `[ha, hb]`. Rewrite using `[hr a ha, hl b hb]`. Simplify using `[ha, hb]`. Rewrite using `[hr a ha, hr b hb]`. Simplify using `[ha, hb]`.
-/
theorem embGL_apply {n N : ℕ} (h : n + 1 = N) (g : GL (Fin n) ℂ) (a b : Fin N) :
    ((embGL ℂ n N h g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) a b =
      if ha : a.1 < n then (if hb : b.1 < n then (g : Matrix (Fin n) (Fin n) ℂ) ⟨a.1, ha⟩ ⟨b.1, hb⟩ else 0)
      else (if b.1 < n then 0 else 1) := by
  unfold embGL blkHom
  simp [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  have hl : ∀ (x : Fin N) (hx : x.1 < n),
      finSumFinEquiv.symm (Fin.cast h.symm x) = (Sum.inl ⟨x.1, hx⟩ : Fin n ⊕ Fin 1) := by
    intro x hx
    have hc : Fin.cast h.symm x = Fin.castAdd 1 ⟨x.1, hx⟩ := Fin.ext rfl
    rw [hc, finSumFinEquiv_symm_apply_castAdd]
  have hr : ∀ (x : Fin N), ¬ x.1 < n →
      finSumFinEquiv.symm (Fin.cast h.symm x) = (Sum.inr 0 : Fin n ⊕ Fin 1) := by
    intro x hx
    have hxN := x.isLt
    have hc : Fin.cast h.symm x = Fin.natAdd n (0 : Fin 1) := Fin.ext (by simp; omega)
    rw [hc, finSumFinEquiv_symm_apply_natAdd]
  by_cases ha : a.1 < n <;> by_cases hb : b.1 < n
  · rw [hl a ha, hl b hb]
    simp [ha, hb]
  · rw [hl a ha, hr b hb]
    simp [ha, hb]
  · rw [hr a ha, hl b hb]
    simp [ha, hb]
  · rw [hr a ha, hr b hb]
    simp [ha, hb]

/- English proof (translation)
Use `set B : Matrix (Fin s) (Fin s) ℂ := Matrix.of fun p p' => G (I p') (I p) with hB`. Establish `hmat : ((Formalism.GradedWeylDivisibility.rowAct ℂ (n` using `N) G.transpose : MvPolynomial (Fin N × Fin N) ℂ →+* MvPolynomial (Fin N × Fin N) ℂ)).mapMatrix (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin N × Fin N) ℂ)) = (C : ℂ →+* MvPolynomial (Fin N × Fin N) ℂ).mapMatrix B * (Matrix.of fun p q : Fin s => (X (I …`. Use extensionality with `p q`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, hB, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Formalism.GradedWeylDivisibility.rowAct, aeval_X, Matrix.transpose_apply]`. Rewrite using `[XiU.sum_comp_eq I hI.injective]`.

Introduce `b hb`. Establish `: G b (I p) = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hb (hcl p b hne)`. Simplify using `[this]`.

Establish `hBdet : B.det = ∏ p, G (I p) (I p)`. Rewrite using `[Matrix.det_of_isLowerTriangular B]`. Both sides reduce to the same expression. Introduce `p p' hpp'`. Conclude with `hG _ _ (hI (by simpa using hpp'))`.

Establish `hdet` using `RingHom.map_det ((Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) G.transpose : MvPolynomial (Fin N × Fin N) ℂ →+* MvPolynomial (Fin N × Fin N) ℂ)) (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin N × Fin N) ℂ))`. Rewrite `hdet` using `[RingHom.coe_coe]`. Use `show Formalism.GradedWeylDivisibility.rowAct ℂ G.transpose (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin N × Fin N) ℂ)).det = C (∏ p, G (I p) (I p)) * (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin N × Fin N) ℂ)).det`. Rewrite using `[hdet, hmat, Matrix.det_mul, ← RingHom.map_det, hBdet]`.
-/
theorem rowAct_initMinor {N s : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (I : Fin s → Fin N) (hI : StrictMono I)
    (hs : s ≤ N) (hG : ∀ a b : Fin N, a < b → G b a = 0)
    (hcl : ∀ p b, G b (I p) ≠ 0 → b ∈ Set.range I) :
    Formalism.GradedWeylDivisibility.rowAct ℂ G.transpose (Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) I hs) =
      C (∏ p, G (I p) (I p)) * Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) I hs := by
  classical
  set B : Matrix (Fin s) (Fin s) ℂ := Matrix.of fun p p' => G (I p') (I p) with hB
  have hmat : ((Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) G.transpose : MvPolynomial (Fin N × Fin N) ℂ →+* MvPolynomial (Fin N × Fin N) ℂ)).mapMatrix
      (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin N × Fin N) ℂ)) =
      (C : ℂ →+* MvPolynomial (Fin N × Fin N) ℂ).mapMatrix B *
      (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin N × Fin N) ℂ)) := by
    ext p q
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, hB,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Formalism.GradedWeylDivisibility.rowAct, aeval_X, Matrix.transpose_apply]
    rw [XiU.sum_comp_eq I hI.injective]
    intro b hb
    have : G b (I p) = 0 := by
      by_contra hne
      exact hb (hcl p b hne)
    simp [this]
  have hBdet : B.det = ∏ p, G (I p) (I p) := by
    rw [Matrix.det_of_isLowerTriangular B]
    · rfl
    · intro p p' hpp'
      exact hG _ _ (hI (by simpa using hpp'))
  have hdet := RingHom.map_det ((Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) G.transpose :
      MvPolynomial (Fin N × Fin N) ℂ →+* MvPolynomial (Fin N × Fin N) ℂ))
    (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin N × Fin N) ℂ))
  rw [RingHom.coe_coe] at hdet
  show Formalism.GradedWeylDivisibility.rowAct ℂ G.transpose
      (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin N × Fin N) ℂ)).det =
    C (∏ p, G (I p) (I p)) * (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin N × Fin N) ℂ)).det
  rw [hdet, hmat, Matrix.det_mul, ← RingHom.map_det, hBdet]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lpMinor_eq {N : ℕ} (s : ℕ) (hr : s ≤ N) (hn : s ≤ N) :
    Formalism.GradedWeylDivisibility.lpMinor ℂ (r := N) (n := N) s hr hn = Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) (Fin.castLE hr) hn := rfl

/- English proof (translation)
Unfold `rowsZ`. Introduce `p q hpq`. Establish `hpq'` using `Fin.lt_def.mp hpq`. Establish `hq` using `q.isLt`. Establish `hi` using `i.isLt`.

Simplify using `only`. Apply the tactic sequence `split_ifs with h1 h2 h2 <;> simp only [Fin.lt_def] <;> omega`.
-/
theorem rowsZ_strictMono {n N : ℕ} (h : n + 1 = N) (i : Fin n) : StrictMono (rowsZ h i) := by
  unfold rowsZ
  intro p q hpq
  have hpq' := Fin.lt_def.mp hpq
  have hq := q.isLt
  have hi := i.isLt
  simp only
  split_ifs with h1 h2 h2 <;> simp only [Fin.lt_def] <;> omega

def GoodG (n : ℕ) {N : ℕ} (h : n + 1 = N) (G : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  (∀ a b : Fin N, a < b → G b a = 0) ∧ (∀ b : Fin N, b.1 ≠ n → G b ⟨n, by omega⟩ = 0)

def xiScal {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (G : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  ∏ i : Fin n, (∏ p : Fin (i.1 + 1), G (Fin.castLE (by omega) p) (Fin.castLE (by omega) p)) ^ (aa h lam sg i).toNat *
    (∏ p : Fin (i.1 + 1), G (rowsZ h i p) (rowsZ h i p)) ^ (bb h lam sg i).toNat

/- English proof (translation)
Establish `hlp : ∀ i : Fin n, Formalism.GradedWeylDivisibility.rowAct ℂ G.transpose (Formalism.GradedWeylDivisibility.lpMinor ℂ (r` using `N) (n := N) (i.1 + 1) (by omega) (by omega)) = C (∏ p : Fin (i.1 + 1), G (Fin.castLE (by omega) p) (Fin.castLE (by omega) p)) * Formalism.GradedWeylDivisibility.lpMinor ℂ (r := N) (n := N) (i.1 + 1) (by omega) (by omega) := by`. Introduce `i`. Rewrite using `[lpMinor_eq]`. Apply `rowAct_initMinor G _ (Fin.strictMono_castLE _) _ hG.1` to reduce the goal to its premises. Introduce `p b hb`.

Establish `hle : b ≤ Fin.castLE (by omega) p`. Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Conclude with `hb (hG.1 _ _ hlt)`. Use `⟨⟨b.1, ?_⟩, Fin.ext rfl⟩` and prove the remaining obligations.

Use `p.2` as an intermediate fact. Simplify using `only [Fin.le_def, Fin.coe_castLE] at hle`. Use linear arithmetic over natural numbers and integers. Establish `hrz : ∀ i : Fin n, Formalism.GradedWeylDivisibility.rowAct ℂ G.transpose (Formalism.GradedWeylDivisibility.initMinor ℂ (n` using `N) (rowsZ h i) (by omega)) = C (∏ p : Fin (i.1 + 1), G (rowsZ h i p) (rowsZ h i p)) * Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) (rowsZ h i) (by omega) := by`. Introduce `i`.

Apply `rowAct_initMinor G _ (rowsZ_strictMono h i) _ hG.1` to reduce the goal to its premises. Introduce `p b hb`. Distinguish the cases in `hp : p.1 = i.1`. Establish `e : rowsZ h i p = ⟨n, by omega⟩`. Simplify using `only [rowsZ, hp, if_true]`.

Use `ext`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Rewrite `hb` using `[e]`. Establish `hbn : b.1 = n`.

Assume the negation of the conclusion as `hne`. Conclude with `hb (hG.2 b hne)`. Use `⟨⟨i.1, by omega⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [rowsZ, if_true]`. Use `ext`.

Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Establish `e : rowsZ h i p = ⟨p.1, by omega⟩`. Simplify using `only [rowsZ, hp, if_false]`. Rewrite `hb` using `[e]`.

Establish `hle : b.1 ≤ p.1`. Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Conclude with `hb (hG.1 _ _ (by simpa [Fin.lt_def] using hlt))`. Establish `hpi : p.1 < i.1` using `by have := p.2; omega`.

Use `⟨⟨b.1, by omega⟩, ?_⟩` and prove the remaining obligations. Establish `: b.1 ≠ i.1` using `by omega`. Simplify using `only [rowsZ, this, if_false]`. Unfold `xi xiScal`. Rewrite using `[map_prod, map_prod, ← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, map_pow, hlp i, hrz i, mul_pow, mul_pow, map_mul, map_pow, map_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rowAct_xi {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (G : Matrix (Fin N) (Fin N) ℂ) (hG : GoodG n h G) :
    Formalism.GradedWeylDivisibility.rowAct ℂ G.transpose (xi ℂ h lam sg) = C (xiScal h lam sg G) * xi ℂ h lam sg := by
  have hlp : ∀ i : Fin n, Formalism.GradedWeylDivisibility.rowAct ℂ G.transpose
      (Formalism.GradedWeylDivisibility.lpMinor ℂ (r := N) (n := N) (i.1 + 1) (by omega) (by omega)) =
      C (∏ p : Fin (i.1 + 1), G (Fin.castLE (by omega) p) (Fin.castLE (by omega) p)) *
        Formalism.GradedWeylDivisibility.lpMinor ℂ (r := N) (n := N) (i.1 + 1) (by omega) (by omega) := by
    intro i
    rw [lpMinor_eq]
    apply rowAct_initMinor G _ (Fin.strictMono_castLE _) _ hG.1
    intro p b hb
    have hle : b ≤ Fin.castLE (by omega) p := by
      by_contra hlt
      push Not at hlt
      exact hb (hG.1 _ _ hlt)
    refine ⟨⟨b.1, ?_⟩, Fin.ext rfl⟩
    have := p.2
    simp only [Fin.le_def, Fin.coe_castLE] at hle
    omega
  have hrz : ∀ i : Fin n, Formalism.GradedWeylDivisibility.rowAct ℂ G.transpose (Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) (rowsZ h i) (by omega)) =
      C (∏ p : Fin (i.1 + 1), G (rowsZ h i p) (rowsZ h i p)) *
        Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) (rowsZ h i) (by omega) := by
    intro i
    apply rowAct_initMinor G _ (rowsZ_strictMono h i) _ hG.1
    intro p b hb
    by_cases hp : p.1 = i.1
    · have e : rowsZ h i p = ⟨n, by omega⟩ := by
        simp only [rowsZ, hp, if_true]; ext; simp; omega
      rw [e] at hb
      have hbn : b.1 = n := by
        by_contra hne
        exact hb (hG.2 b hne)
      refine ⟨⟨i.1, by omega⟩, ?_⟩
      simp only [rowsZ, if_true]
      ext; simp; omega
    · have e : rowsZ h i p = ⟨p.1, by omega⟩ := by
        simp only [rowsZ, hp, if_false]
      rw [e] at hb
      have hle : b.1 ≤ p.1 := by
        by_contra hlt
        push Not at hlt
        exact hb (hG.1 _ _ (by simpa [Fin.lt_def] using hlt))
      have hpi : p.1 < i.1 := by have := p.2; omega
      refine ⟨⟨b.1, by omega⟩, ?_⟩
      have : b.1 ≠ i.1 := by omega
      simp only [rowsZ, this, if_false]
  unfold xi xiScal
  rw [map_prod, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [map_mul, map_pow, map_pow, hlp i, hrz i, mul_pow, mul_pow, map_mul, map_pow, map_pow]
  ring

/- English proof (translation)
Establish `hm` using `Formalism.GradedWeylDivisibility.bidetMem ℂ N N 1 (fun _ => s) (fun _ => hs) (fun _ => I)`. Establish `e1 : Formalism.GradedWeylDivisibility.bideterminant ℂ (r` using `N) (n := N) (fun _ : Fin 1 => s) (fun _ => hs) (fun _ => I) = Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) I hs := by`. Simplify using `[Formalism.GradedWeylDivisibility.bideterminant]`. Establish `e2 : Formalism.GradedWeylDivisibility.shapeDeg (n` using `N) (fun _ : Fin 1 => s) = fun t : Fin N => if t.1 < s then 1 else 0 := by`. Use function extensionality and compare the values at `t`.

Apply the tactic sequence `by_cases ht : t.1 < s <;> simp [Formalism.GradedWeylDivisibility.shapeDeg, ht]`. Rewrite `hm` using `[e1, e2]`. Then use the resulting hypothesis.
-/
theorem initMinor_mem {N s : ℕ} (I : Fin s → Fin N) (hs : s ≤ N) :
    Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) I hs ∈
      Formalism.GradedWeylDivisibility.dualWeyl ℂ N N (fun t : Fin N => if t.1 < s then 1 else 0) := by
  have hm := Formalism.GradedWeylDivisibility.bidetMem ℂ N N 1 (fun _ => s) (fun _ => hs) (fun _ => I)
  have e1 : Formalism.GradedWeylDivisibility.bideterminant ℂ (r := N) (n := N) (fun _ : Fin 1 => s) (fun _ => hs) (fun _ => I) =
      Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) I hs := by
    simp [Formalism.GradedWeylDivisibility.bideterminant]
  have e2 : Formalism.GradedWeylDivisibility.shapeDeg (n := N) (fun _ : Fin 1 => s) = fun t : Fin N => if t.1 < s then 1 else 0 := by
    funext t
    by_cases ht : t.1 < s <;> simp [Formalism.GradedWeylDivisibility.shapeDeg, ht]
  rwa [e1, e2] at hm

/- English proof (translation)
Unfold `Formalism.GradedWeylDivisibility.dualWeyl at hf hg ⊢`. Rewrite `hf`, `hg`, the goal using `[Submodule.mem_inf]`. Take `⟨hf1, hf2⟩` from `hf`. Take `⟨hg1, hg2⟩` from `hg`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite `hf1`, `hg1`, the goal using `[MvPolynomial.mem_weightedHomogeneousSubmodule]`. Conclude with `hf1.mul hg1`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero] at hf2 hg2 ⊢`. Introduce `l j hlj`. Rewrite using `[map_mul, map_mul, hf2 l j hlj, hg2 l j hlj]`.
-/
private theorem mul_mem_dualWeyl_complex {N : ℕ} (ν μ : Fin N → ℕ) (f g : MvPolynomial (Fin N × Fin N) ℂ)
    (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N ν) (hg : g ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N μ) :
    f * g ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N (ν + μ) := by
  unfold Formalism.GradedWeylDivisibility.dualWeyl at hf hg ⊢
  rw [Submodule.mem_inf] at hf hg ⊢
  obtain ⟨hf1, hf2⟩ := hf
  obtain ⟨hg1, hg2⟩ := hg
  refine ⟨?_, ?_⟩
  · rw [MvPolynomial.mem_weightedHomogeneousSubmodule] at hf1 hg1 ⊢
    exact hf1.mul hg1
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
      sub_eq_zero] at hf2 hg2 ⊢
    intro l j hlj
    rw [map_mul, map_mul, hf2 l j hlj, hg2 l j hlj]

/- English proof (translation)
Unfold `Formalism.GradedWeylDivisibility.dualWeyl`. Rewrite using `[Submodule.mem_inf]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.mem_weightedHomogeneousSubmodule]`. Conclude with `MvPolynomial.isWeightedHomogeneous_one _ _`.

Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero]`. Introduce `l j hlj`. Rewrite using `[map_one, map_one]`.
-/
private theorem one_mem_dualWeyl_complex {N : ℕ} :
    (1 : MvPolynomial (Fin N × Fin N) ℂ) ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N 0 := by
  unfold Formalism.GradedWeylDivisibility.dualWeyl
  rw [Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
    exact MvPolynomial.isWeightedHomogeneous_one _ _
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
      sub_eq_zero]
    intro l j hlj
    rw [map_one, map_one]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using one_mem_dualWeyl_complex (N := N)`. Consider the case `succ k ih`. Rewrite using `[pow_succ, succ_nsmul]`. Conclude with `mul_mem_dualWeyl_complex _ _ _ _ ih hf`.
-/
theorem pow_mem {N : ℕ} (ν : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) ℂ)
    (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N ν) (k : ℕ) : f ^ k ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N (k • ν) := by
  induction k with
  | zero => simpa using one_mem_dualWeyl_complex (N := N)
  | succ k ih =>
    rw [pow_succ, succ_nsmul]
    exact mul_mem_dualWeyl_complex _ _ _ _ ih hf

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using one_mem_dualWeyl_complex (N := N)`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha]`. Conclude with `mul_mem_dualWeyl_complex _ _ _ _ (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))`.
-/
theorem prod_mem {N : ℕ} {ι : Type*} (s : Finset ι) (ν : ι → Fin N → ℕ) (f : ι → MvPolynomial (Fin N × Fin N) ℂ)
    (hf : ∀ i ∈ s, f i ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N (ν i)) :
    ∏ i ∈ s, f i ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N (∑ i ∈ s, ν i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one_mem_dualWeyl_complex (N := N)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact mul_mem_dualWeyl_complex _ _ _ _ (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Establish `ht0 : t = 0` using `by omega`. Substitute `ht0` using the available equality. Simplify using the standard rewrite rules.

Consider the case `succ n ih`. Break down `Nat.lt_or_ge n t with h | h` into its components or cases. Establish `htn : t = n + 1` using `by omega`. Substitute `htn` using the available equality. Rewrite using `[Finset.sum_eq_zero]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_range]`. Rewrite using `[if_neg (by omega)]`. Rewrite using `[Finset.sum_range_succ, ih h, if_pos h]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem tele_sum (ℓ : ℕ → ℤ) (n t : ℕ) (ht : t ≤ n) :
    ∑ i ∈ Finset.range n, (if t ≤ i then ℓ i - ℓ (i + 1) else 0) = ℓ t - ℓ n := by
  induction n with
  | zero =>
    have ht0 : t = 0 := by omega
    subst ht0
    simp
  | succ n ih =>
    rcases Nat.lt_or_ge n t with h | h
    · have htn : t = n + 1 := by omega
      subst htn
      rw [Finset.sum_eq_zero]
      · ring
      · intro i hi
        rw [Finset.mem_range] at hi
        rw [if_neg (by omega)]
    · rw [Finset.sum_range_succ, ih h, if_pos h]
      ring

end PI.WGL.XiA
