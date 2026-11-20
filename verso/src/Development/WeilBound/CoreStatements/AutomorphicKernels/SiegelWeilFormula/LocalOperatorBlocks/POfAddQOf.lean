import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.VacUnique
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.LowerLeftBlockLeviUnipotent
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.IsUnitDenominatorBasePoint

noncomputable section

open scoped Matrix
open MeasureTheory PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.KLI

variable {m n : ℕ}

variable {sg : ℤˣ} {L : LOp m n}

/- English proof (translation)
Rewrite using `[fP_add_smul]`. Conclude with `h.lin y a _ _ (isSw_fP P) (isSw_fP Q)`.
-/
theorem L_fP_lin (h : LocHyp sg L) (y : GR n) (a : ℂ) (P Q : PX m n) :
    L y (fP (a • P + Q)) = a • L y (fP P) + L y (fP Q) := by
  rw [fP_add_smul]
  exact h.lin y a _ _ (isSw_fP P) (isSw_fP Q)

/- English proof (translation)
Establish `e` using `L_fP_lin h y 1 0 0`. Simplify using `only [one_smul, add_zero] at e`. Establish `: L y (fP (0 : PX m n)) + L y (fP 0) - L y (fP 0) = L y (fP 0)` using `by abel`. Rewrite `this` using `[← e]`. Simplify using `using this.symm`.
-/
theorem L_fP_zero (h : LocHyp sg L) (y : GR n) : L y (fP (0 : PX m n)) = 0 := by
  have e := L_fP_lin h y 1 0 0
  simp only [one_smul, add_zero] at e
  have : L y (fP (0 : PX m n)) + L y (fP 0) - L y (fP 0) = L y (fP 0) := by abel
  rw [← e] at this
  simpa using this.symm

def sLOf (h : LocHyp sg L) : PX m n →ₗ[ℂ] (GR n → ℂ) where
  toFun P y := L y (fP P) 0
  map_add' P Q := by
    funext y
    have e := L_fP_lin h y 1 P Q
    simp only [one_smul] at e
    simp [e]
  map_smul' a P := by
    funext y
    have e := L_fP_lin h y a P 0
    simp only [add_zero, L_fP_zero h] at e
    simp [e]

open scoped Classical in

def rhoFun (h : LocHyp sg L) (k : GR n) (P : PX m n) : PX m n :=
  if hk : InK (mR k) then Classical.choose (k_poly h k hk P) else 0

open scoped Classical in
/- English proof (translation)
Simplify using `only [rhoFun, dif_pos hk]`. Conclude with `Classical.choose_spec (k_poly h k hk P)`.
-/
theorem rhoFun_spec (h : LocHyp sg L) {k : GR n} (hk : InK (mR k)) (P : PX m n) :
    (rhoFun h k P).totalDegree ≤ P.totalDegree ∧ L k (fP P) = fP (rhoFun h k P) := by
  simp only [rhoFun, dif_pos hk]
  exact Classical.choose_spec (k_poly h k hk P)

open scoped Classical in

def rhoOf (h : LocHyp sg L) (k : GR n) : PX m n →ₗ[ℂ] PX m n where
  toFun := rhoFun h k
  map_add' P Q := by
    by_cases hk : InK (mR k)
    · apply fP_injective
      rw [← (rhoFun_spec h hk _).2]
      have e := L_fP_lin h k 1 P Q
      simp only [one_smul] at e
      rw [e, (rhoFun_spec h hk P).2, (rhoFun_spec h hk Q).2]
      have e2 := fP_add_smul (1 : ℂ) (rhoFun h k P) (rhoFun h k Q)
      simp only [one_smul] at e2
      rw [e2]
    · simp [rhoFun, dif_neg hk]
  map_smul' a P := by
    by_cases hk : InK (mR k)
    · apply fP_injective
      rw [← (rhoFun_spec h hk _).2]
      have e := L_fP_lin h k a P 0
      simp only [add_zero, L_fP_zero h] at e
      rw [e, (rhoFun_spec h hk P).2]
      have e2 := fP_add_smul a (rhoFun h k P) 0
      simp only [add_zero, fP_zero] at e2
      simp [e2]
    · simp [rhoFun, dif_neg hk]

/- English proof (translation)
Simplify using `[cnt]`.
-/
theorem cnt_true : cnt (fun _ : Fin m => true) true = m := by
  simp [cnt]

/- English proof (translation)
Simplify using `[cnt]`.
-/
theorem cnt_false : cnt (fun _ : Fin m => true) false = 0 := by
  simp [cnt]

/- English proof (translation)
Unfold `pOf qOf`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem pOf_add_qOf (sg : ℤˣ) (m : ℕ) : ((pOf sg m : ℕ) : ℤ) + (qOf sg m : ℕ) = m := by
  unfold pOf qOf
  split_ifs <;> simp

/- English proof (translation)
Take `⟨e, he⟩` from `h.mM'`. Take `⟨C, hC, hJ⟩` from `h.longWeylFunctional`. Establish `hlaw : ∀ (P : PX m n) (y g : GR n), (mR y).toBlocks₂₁ = 0 → sLOf h P (y * g) = F0 (pOf sg m) (qOf sg m) e y * sLOf h P g`. Introduce `P y g hy`. Take `⟨a, b, ha, hb, rfl⟩` from `par_eq y hy`.

Establish `hg` using `h.sw g _ (isSw_fP P)`. Use `show L (mG a * nG b * g) (fP P) 0 = _ * L g (fP P) 0`. Rewrite using `[h.mul _ _ _ (isSw_fP P), h.mul _ _ _ hg, he (mG a) a ha (mR_mG ha) _ (h.sw _ _ hg), h.nU (nG b) b hb (mR_nG hb) _ hg, weight_factor_levi_unipotent _ _ _ a b ha hb, pOf_add_qOf]`. Establish `key : ∀ X : Fin m → Fin n → ℂ, X = 0 → Complex.exp (2 * Real.pi * Complex.I * ((sg : ℤ) : ℂ) * (b * ((Matrix.of X)ᴴ * Matrix.of X)).trace) * L g (fP P) X = L g (fP P) 0`. Introduce and unpack `X rfl`.

Rewrite using `[show Matrix.of (0 : Fin m → Fin n → ℂ) = 0 from rfl]`. Simplify using the standard rewrite rules. Simplify using `only []`. Rewrite using `[key _ (by funext i j; exact congrFun (congrFun (Matrix.zero_mul a) i) j)]`. Establish `hcell : ∀ (P : PX m n) (b : Matrix (Fin n) (Fin n) ℂ), bᴴ = b → sLOf h P (jG n * nG b) = C * secN (fun _ : Fin m => true) (2 * Real.pi) (2 * Real.pi * ((sg : ℤ) : ℝ)) P b`.

Introduce `P b hb`. Use `show L (jG n * nG b) (fP P) 0 = _`. Rewrite using `[h.mul _ _ _ (isSw_fP P), hJ (jG n) mR_jG _ (h.sw _ _ (isSw_fP P)), h.nU (nG b) b hb (mR_nG hb) _ (isSw_fP P)]`. Simplify using `only [secN, gramX_true, fP]`. Use `congr 1`.

Use `MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)` and prove the remaining obligations. Use `push_cast`. Put the polynomial expressions in normal form. Establish `hvac : ∀ g, sLOf h 1 g = F0 (pOf sg m) (qOf sg m) e g`. Use `vac_unique sg e (sLOf h 1) C (h.cont 1 0) ?_ (hlaw 1) (hcell 1)` and prove the remaining obligations.

Use `show L 1 (fP 1) 0 = 1`. Rewrite using `[h.one _ (isSw_fP 1), fP_one_zero]`. Use `⟨sLOf h, rhoOf h, e, ?_, fun P y => rfl, fun k P hk => (rhoFun_spec h hk P).2⟩` and prove the remaining obligations. Use `{ cpos := by positivity sign := ?_ cont := fun P => h.cont P 0 vac := hvac law := hlaw cell := ⟨C, hC, fun P g b hb hg => by rw [eq_jn g b hb hg]; exact hcell P b hb⟩ kact := ?_ kvac := ?_ kfin := ?_ }` and prove the remaining obligations. Break down `Int.units_eq_one_or sg with rfl | rfl` into its components or cases.

Use `left`. Simplify using `[pOf, qOf, cnt_true, cnt_false]`. Use `right`. Simplify using `[pOf, qOf, cnt_true, cnt_false]`. Introduce `P g k hk show L (g * k) (fP P) 0 = L g (fP (rhoFun h k P)) 0`.

Rewrite using `[h.mul _ _ _ (isSw_fP P), (rhoFun_spec h hk P).2]`. Introduce `k hk`. Establish `hd` using `(rhoFun_spec h hk 1).1`. Rewrite `hd` using `[MvPolynomial.totalDegree_one, Nat.le_zero, MvPolynomial.totalDegree_eq_zero_iff_eq_C]`. Establish `h1 : sLOf h (rhoOf h k 1) 1 = sLOf h 1 (1 * k)` using `by show L 1 (fP (rhoFun h k 1)) 0 = L (1 * k) (fP 1) 0`.

Rewrite using `[h.mul _ _ _ (isSw_fP 1), ← (rhoFun_spec h hk 1).2]`. Express the relevant statement in the definitionally equal form `sLOf h (rhoFun h k 1) 1 = _ at h1`. Use `set c := MvPolynomial.coeff 0 (rhoFun h k 1) with hcdef`. Establish `hc : (MvPolynomial.C c : PX m n) = c • (1 : PX m n)` using `by rw [MvPolynomial.smul_eq_C_mul, mul_one]`. Rewrite `h1` using `[hd, hc, map_smul, Pi.smul_apply, one_mul, hvac, weight_factor_one, smul_eq_mul, mul_one]`.

Use `show rhoFun h k 1 = _`. Rewrite using `[hd, hc, h1, hvac]`. Introduce `P`. Use `⟨MvPolynomial.restrictTotalDegree _ ℂ P.totalDegree, fin_deg _, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 le_rfl, ?_, ?_⟩` and prove the remaining obligations. Introduce `k hk Q hQ`.

Rewrite `hQ`, the goal using `[MvPolynomial.mem_restrictTotalDegree]`. Conclude with `((rhoFun_spec h hk Q).1).trans hQ`. Introduce `Q hQ l'`. Rewrite `hQ` using `[MvPolynomial.mem_restrictTotalDegree]`. Use `continuousOn_of_evX P.totalDegree (fun k => rhoOf h k Q) (fun k hk => ((rhoFun_spec h hk Q).1).trans hQ) (fun u => ?_) l'` and prove the remaining obligations.

Establish `hcts : ContinuousOn (fun k => L k (fP Q) u / gs (2 * Real.pi) u) {k | InK (mR k)}` using `((h.cont Q u).div_const _).continuousOn`. Use `hcts.congr (fun k hk => ?_)` and prove the remaining obligations. Use `show evX (rhoFun h k Q) u = L k (fP Q) u / gs (2 * Real.pi) u`. Rewrite using `[(rhoFun_spec h hk Q).2, fP, mul_div_assoc, div_self (show gs (2 * Real.pi) u ≠ 0 from Complex.exp_ne_zero _), mul_one]`.
-/
theorem locData_of (h : LocHyp sg L) :
    ∃ (sL : PX m n →ₗ[ℂ] (GR n → ℂ)) (ρ : GR n → PX m n →ₗ[ℂ] PX m n) (e : ℤ),
      LocData (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((sg : ℤ) : ℝ)) (pOf sg m) (qOf sg m) e sL ρ ∧
      (∀ P y, sL P y = L y (fP P) 0) ∧ ∀ (k : GR n) P, InK (mR k) → L k (fP P) = fP (ρ k P) := by
  obtain ⟨e, he⟩ := h.mM'
  obtain ⟨C, hC, hJ⟩ := h.longWeylFunctional

  have hlaw : ∀ (P : PX m n) (y g : GR n), (mR y).toBlocks₂₁ = 0 →
      sLOf h P (y * g) = F0 (pOf sg m) (qOf sg m) e y * sLOf h P g := by
    intro P y g hy
    obtain ⟨a, b, ha, hb, rfl⟩ := par_eq y hy
    have hg := h.sw g _ (isSw_fP P)
    show L (mG a * nG b * g) (fP P) 0 = _ * L g (fP P) 0
    rw [h.mul _ _ _ (isSw_fP P), h.mul _ _ _ hg, he (mG a) a ha (mR_mG ha) _ (h.sw _ _ hg),
      h.nU (nG b) b hb (mR_nG hb) _ hg, weight_factor_levi_unipotent _ _ _ a b ha hb, pOf_add_qOf]
    have key : ∀ X : Fin m → Fin n → ℂ, X = 0 → Complex.exp (2 * Real.pi * Complex.I * ((sg : ℤ) : ℂ) *
        (b * ((Matrix.of X)ᴴ * Matrix.of X)).trace) * L g (fP P) X = L g (fP P) 0 := by
      rintro X rfl
      rw [show Matrix.of (0 : Fin m → Fin n → ℂ) = 0 from rfl]
      simp
    simp only []
    rw [key _ (by funext i j; exact congrFun (congrFun (Matrix.zero_mul a) i) j)]

  have hcell : ∀ (P : PX m n) (b : Matrix (Fin n) (Fin n) ℂ), bᴴ = b →
      sLOf h P (jG n * nG b) = C * secN (fun _ : Fin m => true) (2 * Real.pi) (2 * Real.pi * ((sg : ℤ) : ℝ)) P b := by
    intro P b hb
    show L (jG n * nG b) (fP P) 0 = _
    rw [h.mul _ _ _ (isSw_fP P), hJ (jG n) mR_jG _ (h.sw _ _ (isSw_fP P)), h.nU (nG b) b hb (mR_nG hb) _ (isSw_fP P)]
    simp only [secN, gramX_true, fP]
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    push_cast
    ring_nf
  have hvac : ∀ g, sLOf h 1 g = F0 (pOf sg m) (qOf sg m) e g := by
    refine vac_unique sg e (sLOf h 1) C (h.cont 1 0) ?_ (hlaw 1) (hcell 1)
    show L 1 (fP 1) 0 = 1
    rw [h.one _ (isSw_fP 1), fP_one_zero]
  refine ⟨sLOf h, rhoOf h, e, ?_, fun P y => rfl, fun k P hk => (rhoFun_spec h hk P).2⟩
  refine
    { cpos := by positivity
      sign := ?_
      cont := fun P => h.cont P 0
      vac := hvac
      law := hlaw
      cell := ⟨C, hC, fun P g b hb hg => by rw [eq_jn g b hb hg]; exact hcell P b hb⟩
      kact := ?_
      kvac := ?_
      kfin := ?_ }
  · rcases Int.units_eq_one_or sg with rfl | rfl
    · left; simp [pOf, qOf, cnt_true, cnt_false]
    · right; simp [pOf, qOf, cnt_true, cnt_false]
  · intro P g k hk
    show L (g * k) (fP P) 0 = L g (fP (rhoFun h k P)) 0
    rw [h.mul _ _ _ (isSw_fP P), (rhoFun_spec h hk P).2]
  · intro k hk
    have hd := (rhoFun_spec h hk 1).1
    rw [MvPolynomial.totalDegree_one, Nat.le_zero, MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hd
    have h1 : sLOf h (rhoOf h k 1) 1 = sLOf h 1 (1 * k) := by
      show L 1 (fP (rhoFun h k 1)) 0 = L (1 * k) (fP 1) 0
      rw [h.mul _ _ _ (isSw_fP 1), ← (rhoFun_spec h hk 1).2]
    change sLOf h (rhoFun h k 1) 1 = _ at h1
    set c := MvPolynomial.coeff 0 (rhoFun h k 1) with hcdef
    have hc : (MvPolynomial.C c : PX m n) = c • (1 : PX m n) := by rw [MvPolynomial.smul_eq_C_mul, mul_one]
    rw [hd, hc, map_smul, Pi.smul_apply, one_mul, hvac, weight_factor_one, smul_eq_mul, mul_one] at h1
    show rhoFun h k 1 = _
    rw [hd, hc, h1, hvac]
  · intro P
    refine ⟨MvPolynomial.restrictTotalDegree _ ℂ P.totalDegree, fin_deg _,
      (MvPolynomial.mem_restrictTotalDegree _ _ _).2 le_rfl, ?_, ?_⟩
    · intro k hk Q hQ
      rw [MvPolynomial.mem_restrictTotalDegree] at hQ ⊢
      exact ((rhoFun_spec h hk Q).1).trans hQ
    · intro Q hQ l'
      rw [MvPolynomial.mem_restrictTotalDegree] at hQ
      refine continuousOn_of_evX P.totalDegree (fun k => rhoOf h k Q)
        (fun k hk => ((rhoFun_spec h hk Q).1).trans hQ) (fun u => ?_) l'
      have hcts : ContinuousOn (fun k => L k (fP Q) u / gs (2 * Real.pi) u) {k | InK (mR k)} :=
        ((h.cont Q u).div_const _).continuousOn
      refine hcts.congr (fun k hk => ?_)
      show evX (rhoFun h k Q) u = L k (fP Q) u / gs (2 * Real.pi) u
      rw [(rhoFun_spec h hk Q).2, fP, mul_div_assoc, div_self (show gs (2 * Real.pi) u ≠ 0 from Complex.exp_ne_zero _), mul_one]

end PositivityTheory.SiegelWeilFormula.KLI

end
