import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationTaylorPowerSeriesOfDerivationsKill
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorIsRingHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallMemFilt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoeffwiseDerivationMvPowerSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSolveMvPowerSeriesMatrixIdentityConstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSingleDerivationTaylorPowerSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesDegreeAdicFiltrationMulLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatePolynomialSubMemMaximalIdealPowStatement
open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

namespace GlobalTheory.FormalOrigin.Extend

noncomputable def pdZ {σ R : Type} [CommRing R] (j : σ) : Derivation ℤ (MvPowerSeries σ R) (MvPowerSeries σ R) where
  toFun := MvPowerSeries.pderiv R j
  map_add' := map_add _
  map_smul' m x := by simpa using map_zsmul (MvPowerSeries.pderiv R j) m x
  map_one_eq_zero' := MvPowerSeries.pderiv_one
  leibniz' := (MvPowerSeries.pderiv R j).leibniz

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pdZ_apply {σ R : Type} [CommRing R] (j : σ) (F : MvPowerSeries σ R) :
    pdZ j F = MvPowerSeries.pderiv R j F := rfl

/- English proof (translation)
Rewrite using `[Derivation.add_apply]`. Use `congr 1`. Rewrite using `[← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]`. Simplify using `[Derivation.smul_apply]`.
-/
theorem add_sum_apply {σ R ι : Type} [CommRing R] [Fintype ι] (E : Derivation ℤ (MvPowerSeries σ R) (MvPowerSeries σ R))
    (G : ι → MvPowerSeries σ R) (P : ι → Derivation ℤ (MvPowerSeries σ R) (MvPowerSeries σ R))
    (F : MvPowerSeries σ R) : (E + ∑ j, G j • P j) F = E F + ∑ j, G j * P j F := by
  rw [Derivation.add_apply]
  congr 1
  rw [← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
  simp [Derivation.smul_apply]

/- English proof (translation)
Introduce `R A _ _ _ _ _ _ _ _ inc ev hev n ds z hz hdz hm hinc d D hdD`. Take `⟨T, hT⟩` from `taylor_isRingHom A R n ev ds`. Simplify using `only [← hT]`. Take `⟨E, hE⟩` from `GlobalTheory.T.exists_coeffwise_derivation_mvPowerSeries (Fin n) R D`. Establish `hEC : ∀ r, E (MvPowerSeries.C r) = MvPowerSeries.C (D r)`.

Introduce `r`. Use extensionality with `α`. Rewrite using `[hE, MvPowerSeries.coeff_C, MvPowerSeries.coeff_C]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hTinc : ∀ r, T (inc r) = MvPowerSeries.C r`.

Introduce `r`. Rewrite using `[hT, taylor_const A R n ev ds (inc r) (fun i => hinc i r), hev]`. Take `⟨G, hG⟩` from `GlobalTheory.T.exists_solve_mvPowerSeries_matrix_identity_const n R (fun i j => pdZ j (T (z i))) (by`. Introduce `i j`. Simplify using `only [pdZ_apply]`.

Rewrite using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv, zero_add, hT, GlobalTheory.T.coeff_single_derivationTaylorPowerSeries, hdz]`. Simplify using `[eq_comm]) (fun i => T (d (z i)) - E (T (z i)))`. Use `set dΩ : Derivation ℤ (MvPowerSeries (Fin n) R) (MvPowerSeries (Fin n) R) := E + ∑ j, G j • pdZ j with hdΩ`. Establish `hΩ : ∀ F, dΩ F = E F + ∑ j, G j * pdZ j F` using `fun F => add_sum_apply E G _ F`. Use `⟨dΩ, fun r => ?_, ?_⟩` and prove the remaining obligations.

Simplify using `[hΩ, hEC, pdZ_apply]`. Use `set e : A → MvPowerSeries (Fin n) R := fun f => dΩ (T f) - T (d f) with he`. Establish `e_add : ∀ f g, e (f + g) = e f + e g`. Introduce `f g`. Simplify using `only [he, map_add]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e_mul : ∀ f g, e (f * g) = T f * e g + T g * e f`. Introduce `f g`. Simplify using `only [he, map_mul, Derivation.leibniz, smul_eq_mul, map_add]`. Expand and normalize the polynomial expressions, which then agree.

Establish `e_neg : ∀ f, e (-f) = - e f`. Introduce `f`. Simplify using `only [he, map_neg]`. Expand and normalize the polynomial expressions, which then agree. Establish `e_one : e 1 = 0` using `by simp [he]`.

Set `Q : Subring A` to `{ carrier := {f | e f = 0} mul_mem' := fun {f g} hf hg => by simp only [Set.mem_setOf_eq] at *; rw [e_mul, hf, hg]; ring one_mem' := e_one add_mem' := fun {f g} hf hg => by simp only [Set.mem_setOf_eq] at *; rw [e_add, hf, hg]; ring zero_mem' := by simp [he] neg_mem' := fun {f} h …`. Establish `hQ : Subring.closure (Set.range inc ∪ Set.range z) ≤ Q`. Rewrite using `[Subring.closure_le]`. Introduce and unpack `_ (⟨r, rfl⟩ | ⟨i, rfl⟩)`. Express the relevant statement in the definitionally equal form `e (inc r) = 0`.

Simplify using `[he, hTinc, hdD, hΩ, hEC, pdZ_apply]`. Express the relevant statement in the definitionally equal form `e (z i) = 0`. Use `hG i` as an intermediate fact. Simplify using `only [he, hΩ]`. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hc0 : ∀ x, MvPowerSeries.constantCoeff (T x) = ev x`. Introduce `x`. Rewrite using `[hT, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]`. Express the relevant statement in the definitionally equal form `(∏ i, (((0 : Fin n →₀ ℕ) i).factorial : ℚ))⁻¹ • ev (iterOp _ 0 x) = _`.

Rewrite using `[iterOp_zero]`. Simplify using the standard rewrite rules. Establish `hloc : ∀ x ∈ maximalIdeal A, ev x ∈ maximalIdeal R`. Introduce `x hx`. Rewrite using `[mem_maximalIdeal, mem_nonunits_iff]`.

Introduce `hu`. Establish `h1 : x - inc (ev x) ∈ maximalIdeal A`. Apply `le_maximalIdeal (RingHom.ker_ne_top ev)` to reduce the goal to its premises. Rewrite using `[RingHom.mem_ker, map_sub, hev, sub_self]`. Establish `h2 : inc (ev x) ∈ maximalIdeal A` using `by simpa using Ideal.sub_mem _ hx h1`.

Conclude with `(mem_maximalIdeal _).1 h2 (hu.map inc)`. Establish `hT1 : ∀ x ∈ maximalIdeal A, T x ∈ filt (maximalIdeal R) 1`. Introduce `x hx α`. Distinguish the cases in `hα : α = 0`. Substitute `hα` using the available equality.

Simplify using `only [map_zero, Nat.sub_zero, pow_one]`. Rewrite using `[MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hc0]`. Conclude with `hloc x hx`. Establish `: 1 - α.degree = 0`. Establish `: α.degree ≠ 0`.

Introduce `h0`. Conclude with `hα ((Finsupp.degree_eq_zero_iff α).1 h0)`. Use linear arithmetic over natural numbers and integers. Rewrite using `[this, pow_zero, Ideal.one_eq_top]`. Discharge the goal by the elementary cases of `trivial`.

Establish `hTk : ∀ k, ∀ x ∈ maximalIdeal A ^ k, T x ∈ filt (maximalIdeal R) k`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro x _ α`. Simplify using the standard rewrite rules.

Consider the case `succ k ih`. Introduce `x hx`. Rewrite `hx` using `[pow_succ']`. Use `Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)` and prove the remaining obligations. Rewrite using `[map_mul, add_comm]`.

Conclude with `GlobalTheory.T.mvPowerSeriesDegreeAdicFiltration_mul_le (Fin n) R _ 1 k (Ideal.mul_mem_mul (hT1 a ha) (ih b hb))`. Rewrite using `[map_add]`. Conclude with `Ideal.add_mem _ ha hb`. Establish `hek : ∀ k, ∀ x ∈ maximalIdeal A ^ (k + 1), e x ∈ filt (maximalIdeal R) k`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => intro x _ α`. Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `x hx`.

Rewrite `hx` using `[pow_succ']`. Use `Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)` and prove the remaining obligations. Rewrite using `[e_mul]`. Use `Ideal.add_mem _ ?_ (Ideal.mul_mem_right _ _ (hTk _ b hb))` and prove the remaining obligations. Rewrite using `[add_comm]`.

Conclude with `GlobalTheory.T.mvPowerSeriesDegreeAdicFiltration_mul_le (Fin n) R _ 1 k (Ideal.mul_mem_mul (hT1 a ha) (ih b hb))`. Rewrite using `[e_add]`. Conclude with `Ideal.add_mem _ ha hb`. Introduce `f`. Establish `: e f = 0`.

Use `eq_zero_of_forall_mem_filt (maximalIdeal R) _ fun k => ?_` and prove the remaining obligations. Take `⟨p, hp, hfp⟩` from `GlobalTheory.T.exists_coordinate_polynomial_sub_mem_maximalIdeal_pow R A inc ev hev n z hm (k + 1) f`. Establish `h1 : e f = e p + e (f - p)` using `by rw [← e_add]; congr 1; ring`. Rewrite using `[h1, show e p = 0 from hQ hp, zero_add]`. Conclude with `hek k _ hfp`.

Conclude with `sub_eq_zero.1 this`.
-/
theorem derivation_extends : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (inc : R →+* A) (ev : A →+* R), (∀ r, ev (inc r) = r) → ∀ (n : ℕ) (ds : Fin n → Derivation ℤ A A) (z : Fin n → A), (∀ i, ev (z i) = 0) → (∀ a i, ev (ds a (z i)) = if a = i then 1 else 0) → maximalIdeal A = (maximalIdeal R).map inc ⊔ Ideal.span (Set.range z) → (∀ a r, ds a (inc r) = 0) → ∀ (d : Derivation ℤ A A) (D : Derivation ℤ R R), (∀ r, d (inc r) = inc (D r)) → ∃ dΩ : Derivation ℤ (MvPowerSeries (Fin n) R) (MvPowerSeries (Fin n) R), (∀ r, dΩ (MvPowerSeries.C r) = MvPowerSeries.C (D r)) ∧ ∀ f, dΩ (taylor ev (fun i => ⇑(ds i)) f) = taylor ev (fun i => ⇑(ds i)) (d f) := by
  intro R A _ _ _ _ _ _ _ _ inc ev hev n ds z hz hdz hm hinc d D hdD
  obtain ⟨T, hT⟩ := taylor_isRingHom A R n ev ds
  simp only [← hT]
  obtain ⟨E, hE⟩ := GlobalTheory.T.exists_coeffwise_derivation_mvPowerSeries (Fin n) R D
  have hEC : ∀ r, E (MvPowerSeries.C r) = MvPowerSeries.C (D r) := by
    intro r; ext α
    rw [hE, MvPowerSeries.coeff_C, MvPowerSeries.coeff_C]
    split_ifs <;> simp
  have hTinc : ∀ r, T (inc r) = MvPowerSeries.C r := by
    intro r; rw [hT, taylor_const A R n ev ds (inc r) (fun i => hinc i r), hev]
  obtain ⟨G, hG⟩ := GlobalTheory.T.exists_solve_mvPowerSeries_matrix_identity_const n R (fun i j => pdZ j (T (z i))) (by
    intro i j
    simp only [pdZ_apply]
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv, zero_add, hT,
      GlobalTheory.T.coeff_single_derivationTaylorPowerSeries, hdz]
    simp [eq_comm]) (fun i => T (d (z i)) - E (T (z i)))
  set dΩ : Derivation ℤ (MvPowerSeries (Fin n) R) (MvPowerSeries (Fin n) R) := E + ∑ j, G j • pdZ j with hdΩ
  have hΩ : ∀ F, dΩ F = E F + ∑ j, G j * pdZ j F := fun F => add_sum_apply E G _ F
  refine ⟨dΩ, fun r => ?_, ?_⟩
  · simp [hΩ, hEC, pdZ_apply]
  ·
    set e : A → MvPowerSeries (Fin n) R := fun f => dΩ (T f) - T (d f) with he
    have e_add : ∀ f g, e (f + g) = e f + e g := by
      intro f g; simp only [he, map_add]; ring
    have e_mul : ∀ f g, e (f * g) = T f * e g + T g * e f := by
      intro f g; simp only [he, map_mul, Derivation.leibniz, smul_eq_mul, map_add]; ring
    have e_neg : ∀ f, e (-f) = - e f := by
      intro f; simp only [he, map_neg]; ring
    have e_one : e 1 = 0 := by simp [he]
    let Q : Subring A :=
      { carrier := {f | e f = 0}
        mul_mem' := fun {f g} hf hg => by simp only [Set.mem_setOf_eq] at *; rw [e_mul, hf, hg]; ring
        one_mem' := e_one
        add_mem' := fun {f g} hf hg => by simp only [Set.mem_setOf_eq] at *; rw [e_add, hf, hg]; ring
        zero_mem' := by simp [he]
        neg_mem' := fun {f} hf => by simp only [Set.mem_setOf_eq] at *; rw [e_neg, hf, neg_zero] }
    have hQ : Subring.closure (Set.range inc ∪ Set.range z) ≤ Q := by
      rw [Subring.closure_le]
      rintro _ (⟨r, rfl⟩ | ⟨i, rfl⟩)
      · change e (inc r) = 0
        simp [he, hTinc, hdD, hΩ, hEC, pdZ_apply]
      · change e (z i) = 0
        have := hG i
        simp only [he, hΩ]
        rw [this]; ring

    have hc0 : ∀ x, MvPowerSeries.constantCoeff (T x) = ev x := by
      intro x
      rw [hT, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
      change (∏ i, (((0 : Fin n →₀ ℕ) i).factorial : ℚ))⁻¹ • ev (iterOp _ 0 x) = _
      rw [iterOp_zero]; simp
    have hloc : ∀ x ∈ maximalIdeal A, ev x ∈ maximalIdeal R := by
      intro x hx
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have h1 : x - inc (ev x) ∈ maximalIdeal A := by
        apply le_maximalIdeal (RingHom.ker_ne_top ev)
        rw [RingHom.mem_ker, map_sub, hev, sub_self]
      have h2 : inc (ev x) ∈ maximalIdeal A := by simpa using Ideal.sub_mem _ hx h1
      exact (mem_maximalIdeal _).1 h2 (hu.map inc)
    have hT1 : ∀ x ∈ maximalIdeal A, T x ∈ filt (maximalIdeal R) 1 := by
      intro x hx α
      by_cases hα : α = 0
      · subst hα
        simp only [map_zero, Nat.sub_zero, pow_one]
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hc0]
        exact hloc x hx
      · have : 1 - α.degree = 0 := by
          have : α.degree ≠ 0 := by
            intro h0; exact hα ((Finsupp.degree_eq_zero_iff α).1 h0)
          omega
        rw [this, pow_zero, Ideal.one_eq_top]; trivial
    have hTk : ∀ k, ∀ x ∈ maximalIdeal A ^ k, T x ∈ filt (maximalIdeal R) k := by
      intro k
      induction k with
      | zero => intro x _ α; simp
      | succ k ih =>
        intro x hx
        rw [pow_succ'] at hx
        refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
        · rw [map_mul, add_comm]
          exact GlobalTheory.T.mvPowerSeriesDegreeAdicFiltration_mul_le (Fin n) R _ 1 k (Ideal.mul_mem_mul (hT1 a ha) (ih b hb))
        · rw [map_add]; exact Ideal.add_mem _ ha hb
    have hek : ∀ k, ∀ x ∈ maximalIdeal A ^ (k + 1), e x ∈ filt (maximalIdeal R) k := by
      intro k
      induction k with
      | zero => intro x _ α; simp
      | succ k ih =>
        intro x hx
        rw [pow_succ'] at hx
        refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
        · rw [e_mul]
          refine Ideal.add_mem _ ?_ (Ideal.mul_mem_right _ _ (hTk _ b hb))
          rw [add_comm]
          exact GlobalTheory.T.mvPowerSeriesDegreeAdicFiltration_mul_le (Fin n) R _ 1 k (Ideal.mul_mem_mul (hT1 a ha) (ih b hb))
        · rw [e_add]; exact Ideal.add_mem _ ha hb
    intro f
    have : e f = 0 := by
      refine eq_zero_of_forall_mem_filt (maximalIdeal R) _ fun k => ?_
      obtain ⟨p, hp, hfp⟩ := GlobalTheory.T.exists_coordinate_polynomial_sub_mem_maximalIdeal_pow R A inc ev hev n z hm (k + 1) f
      have h1 : e f = e p + e (f - p) := by rw [← e_add]; congr 1; ring
      rw [h1, show e p = 0 from hQ hp, zero_add]
      exact hek k _ hfp
    exact sub_eq_zero.1 this

end GlobalTheory.FormalOrigin.Extend
