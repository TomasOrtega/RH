import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AtPBijective
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LebesgueCommonStabilizerEqRadicalLeviMap

noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.RefCovMul

open GlobalTheory.Amp.Swap GlobalTheory.DegVol.Swap

variable {k r j : ℕ}

/- English proof (translation)
By extensionality, compare the relevant components. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem upperIn_0 (β : Fin r → ℕ) : upperIn β 0 = 1 := by
  ext a b
  by_cases h : a < b
  · simp [upperIn, upper, h, h.ne]
  · simp [upperIn, upper, h, Matrix.one_apply]

/- English proof (translation)
A detailed English derivation is pending.
-/
private lemma wI_eq_mI (m : Fin (k + 1)) : wI k r m = UEmb.mI k r m := Fin.ext (by simp [wI, UEmb.mI])

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.
-/
theorem pOf_mul_we (q : PPar k r) (u : Matrix (Fin r) (Fin r) ℂ) (a : Fin (k + 1)) (b : Fin r) :
    (pOf k r q * uEmb k r u) (wI k r a) (eI k r b) = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  refine Rad.cases3 (P := fun l => pOf k r q (wI k r a) l * uEmb k r u l (eI k r b) = 0) ?_ ?_ ?_ l
  · intro c
    simp only [pOf, Rad.pEl_we, zero_mul]
  · intro c
    rw [wI_eq_mI c, UEmb.u_me, mul_zero]
  · intro c
    rw [UEmb.u_se, mul_zero]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.
-/
theorem pOf_mul_se (q : PPar k r) (u : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r) :
    (pOf k r q * uEmb k r u) (esI k r a) (eI k r b) = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  refine Rad.cases3 (P := fun l => pOf k r q (esI k r a) l * uEmb k r u l (eI k r b) = 0) ?_ ?_ ?_ l
  · intro c
    simp only [pOf, Rad.pEl_se, zero_mul]
  · intro c
    rw [wI_eq_mI c, UEmb.u_me, mul_zero]
  · intro c
    rw [UEmb.u_se, mul_zero]

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private lemma crd_eI_eI (β : Fin r → ℕ) (x : (UTin β → ℂ) × PTop k r j) (a b : Fin r) :
    crd k r j β x (eI k r a) (eI k r b) = upperIn β x.1 a b := by
  simp only [crd, pTop]
  exact pOf_mul_ee _ _ a b

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private lemma crd_mI_eI_eq_zero (β : Fin r → ℕ) (x : (UTin β → ℂ) × PTop k r j) (m : Fin (k + 1)) (b : Fin r) :
    crd k r j β x (UEmb.mI k r m) (eI k r b) = 0 := by
  rw [← wI_eq_mI]
  simp only [crd, pTop]
  exact pOf_mul_we _ _ m b

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private lemma crd_esI_eI_eq_zero (β : Fin r → ℕ) (x : (UTin β → ℂ) × PTop k r j) (a b : Fin r) :
    crd k r j β x (esI k r a) (eI k r b) = 0 := by
  simp only [crd, pTop]
  exact pOf_mul_se _ _ a b

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities.
-/
theorem upperIn_mul (β : Fin r → ℕ) (p q w : (UTin β → ℂ) × PTop k r j)
    (h : crd k r j β p * crd k r j β q = crd k r j β w) :
    upperIn β w.1 = upperIn β p.1 * upperIn β q.1 := by
  ext a b
  have e : (crd k r j β p * crd k r j β q) (eI k r a) (eI k r b) = crd k r j β w (eI k r a) (eI k r b) := by
    rw [h]
  rw [crd_eI_eI, Matrix.mul_apply, UEmb.sum_idx] at e
  simp only [crd_mI_eI_eq_zero, crd_esI_eI_eq_zero, crd_eI_eI, mul_zero, Finset.sum_const_zero, add_zero] at e
  rw [← e, Matrix.mul_apply]

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules.

Consider separately whether the proposition holds or fails. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem upper_mul_entry (x y : UT r → ℂ) (i : UT r)
    (hx : ∀ l : UT r, l.1.2.val - l.1.1.val < i.1.2.val - i.1.1.val → x l = 0) :
    (upper x * upper y) i.1.1 i.1.2 = x i + y i := by
  obtain ⟨⟨a, b⟩, hab⟩ := i
  rw [Matrix.mul_apply, Fintype.sum_eq_add a b hab.ne]
  · simp only [upper, lt_irrefl, dif_neg, not_false_eq_true, if_true, dif_pos hab, one_mul, mul_one]
    exact add_comm _ _
  · rintro c ⟨hca, hcb⟩
    simp only [upper]
    by_cases h1 : a < c
    · by_cases h2 : c < b
      · have hl : c.val - a.val < b.val - a.val := by
          have := Fin.lt_def.mp h1; have := Fin.lt_def.mp h2; omega
        rw [dif_pos h1, hx ⟨(a, c), h1⟩ hl, zero_mul]
      · rw [dif_neg h2, if_neg hcb, mul_zero]
    · rw [dif_neg h1, if_neg (Ne.symm hca), zero_mul]

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem first (β : Fin r → ℕ) (p q w : (UTin β → ℂ) × PTop k r j)
    (h : crd k r j β p * crd k r j β q = crd k r j β w) (i : UTin β)
    (hi : ∀ l : UTin β, l.1.1.2.val - l.1.1.1.val < i.1.1.2.val - i.1.1.1.val → p.1 l = 0) :
    w.1 i = p.1 i + q.1 i := by
  have e := congrArg (fun M : Matrix (Fin r) (Fin r) ℂ => M i.1.1.1 i.1.1.2) (upperIn_mul β p q w h)
  simp only [upperIn] at e
  rw [upper_mul_entry _ _ i.1] at e
  · simpa [upper, i.1.2, i.2] using e
  · intro l hl
    split_ifs with hβ
    · exact hi ⟨l, hβ⟩ hl
    · rfl

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem cancel (β : Fin r → ℕ) (p q w : (UTin β → ℂ) × PTop k r j)
    (h : crd k r j β p * crd k r j β q = crd k r j β w) (hp : p.1 = 0) :
    pTop k r j p.2 * pTop k r j q.2 = pTop k r j w.2 := by
  have hm := upperIn_mul β p q w h
  rw [hp, upperIn_0, one_mul] at hm
  set U := upperIn β q.1 with hUdef
  have hT : U.IsUpperTriangular := by
    intro a b hba
    have h1 : ¬ a < b := not_lt.mpr hba.le
    have h2 : a ≠ b := ne_of_gt hba
    simp [hUdef, upperIn, upper, h1, h2]
  have hU : IsUnit U.det := by
    rw [Matrix.det_of_isUpperTriangular hT]
    simp [hUdef, upperIn, upper]
  have hV : uEmb k r U * uEmb k r U⁻¹ = 1 := by
    rw [← UEmb.uEmb_mul, Matrix.mul_nonsing_inv _ hU, UEmb.uEmb_one]
  have h' : pTop k r j p.2 * pTop k r j q.2 * uEmb k r U = pTop k r j w.2 * uEmb k r U := by
    have h2 := h
    simp only [crd, hp, upperIn_0, UEmb.uEmb_one, mul_one, hm] at h2
    rw [mul_assoc]
    exact h2
  calc pTop k r j p.2 * pTop k r j q.2
      = pTop k r j p.2 * pTop k r j q.2 * uEmb k r U * uEmb k r U⁻¹ := by rw [mul_assoc _ (uEmb k r U), hV, mul_one]
    _ = pTop k r j w.2 * uEmb k r U * uEmb k r U⁻¹ := by rw [h']
    _ = pTop k r j w.2 := by rw [mul_assoc, hV, mul_one]

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify to obtain the desired conclusion from the available facts. Substitute using the available equality. Reduce the conclusion to the remaining proof obligations.

By extensionality, compare the relevant components. Simplify to obtain the desired conclusion from the available facts.
-/
private lemma eq_and_eq_of_pEl_eq (B B' : Fin r → Fin (k + 1) → ℂ) (S S' : Matrix (Fin r) (Fin r) ℂ)
    (h : pEl k r B S = pEl k r B' S') : B = B' ∧ S = S' := by
  have hB : B = B' := by
    funext b c
    simpa [Rad.pEl_ws] using
      congrArg (fun M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => M (wI k r c) (esI k r b)) h
  subst hB
  refine ⟨rfl, ?_⟩
  ext a b
  simpa [Rad.pEl_es] using
    congrArg (fun M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => M (eI k r a) (esI k r b)) h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. By extensionality, compare the relevant components.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem crd_mul : ∀ (k r j : ℕ) (β : Fin r → ℕ), crd k r j β 0 = 1 ∧ ∀ p q w : (UTin β → ℂ) × PTop k r j, crd k r j β p * crd k r j β q = crd k r j β w → (∀ i : UTin β, (∀ l : UTin β, l.1.1.2.val - l.1.1.1.val < i.1.1.2.val - i.1.1.1.val → p.1 l = 0) → w.1 i = p.1 i + q.1 i) ∧ (p.1 = 0 → w.2.1 = p.2.1 + q.2.1) ∧ (p.1 = 0 → p.2.1 = 0 → w.2.2 = p.2.2 + q.2.2) := by
  intro k r j β
  refine ⟨?_, fun p q w h => ⟨fun i hi => first β p q w h i hi, fun hp => ?_, fun hp hB => ?_⟩⟩
  · have hS : skewM (r := r) (fun _ => 0) (fun _ => 0) = 0 := by
      ext a b
      simp only [skewM, Matrix.zero_apply]
      split_ifs <;> simp
    simp only [crd, Prod.fst_zero, Prod.snd_zero, upperIn_0, UEmb.uEmb_one, mul_one, pTop, pOf,
      Pi.zero_apply, dite_eq_ite, ite_self, hS]
    exact Rad.pEl_zero
  · have hc := cancel β p q w h hp
    simp only [pTop, pOf] at hc
    rw [Rad.pEl_mul] at hc
    have hB' := (eq_and_eq_of_pEl_eq _ _ _ _ hc).1
    funext a c
    have e := congrFun (congrFun hB' a.1) c
    simpa [a.2] using e.symm
  · have hc := cancel β p q w h hp
    simp only [pTop, pOf, hB, Pi.zero_apply, dite_eq_ite, ite_self] at hc
    rw [Rad.pEl_mul] at hc
    have hS' := (eq_and_eq_of_pEl_eq _ _ _ _ hc).2
    simp only [Rad.herm_Hb] at hS'
    ext x
    · obtain ⟨⟨⟨a, b⟩, hab⟩, hj⟩ := x
      have e := congrFun (congrFun hS' a) b
      simp [skewM, hab, hj] at e
      simpa using e.symm
    · obtain ⟨a, ha⟩ := x
      have e := congrArg Complex.im (congrFun (congrFun hS' a) a)
      simp [skewM, ha] at e
      simpa using e.symm

end GlobalTheory.DegVol.RefCovMul
