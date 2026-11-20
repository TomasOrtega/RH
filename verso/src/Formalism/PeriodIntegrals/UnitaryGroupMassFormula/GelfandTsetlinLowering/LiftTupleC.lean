import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftTupleA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftTupleM

noncomputable section

namespace PI.WGL.LTC

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM

/- English proof (translation)
Introduce `a b hab`. Establish `h1` using `congrArg Fin.val hab`. Simplify using `only [eRow] at h1`. Conclude with `Fin.ext (by simpa using h1)`.
-/
theorem eRow_inj {n N : ℕ} (h : n + 1 = N) : Function.Injective (eRow h) := by
  intro a b hab
  have h1 := congrArg Fin.val hab
  simp only [eRow] at h1
  exact Fin.ext (by simpa using h1)

/- English proof (translation)
Introduce `hb`. Establish `h1` using `congrArg Fin.val hb`. Establish `h2` using `b.2`. Simplify using `[eRow] at h1`. Use linear arithmetic over natural numbers and integers.
-/
theorem eRow_ne_last {n N : ℕ} (h : n + 1 = N) (b : Fin n) : eRow h b ≠ ⟨N - 1, by omega⟩ := by
  intro hb
  have h1 := congrArg Fin.val hb
  have h2 := b.2
  simp [eRow] at h1
  omega

/- English proof (translation)
The claim follows from `exp_gmin id Function.injective_id (Fin.castLE (hsz k))`.
-/
theorem exp_bidet {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (k : Fin K) :
    Exp (id : Fin n → Fin n) (fun ρ : Fin (sz k) → Fin n => initMinor ℤ (n := n) ρ (hsz k)) := exp_gmin id Function.injective_id (Fin.castLE (hsz k))

/- English proof (translation)
Introduce `a b ρ`. Distinguish the cases in `hk : k ∈ L`. Simplify using `only [hk, if_true, ite_true]`. Conclude with `exp_lift (eRow h) (eRow_inj h) ⟨N - 1, by omega⟩ (eRow_ne_last h) (Fin.castLE (by have := hsz k; omega)) a b ρ`. Simplify using `only [hk, if_false, ite_false]`.

Conclude with `exp_gmin (eRow h) (eRow_inj h) (Fin.castLE (by have := hsz k; omega)) a b ρ`.
-/
theorem exp_M {n N : ℕ} (h : n + 1 = N) {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (L : Finset (Fin K))
    (k : Fin K) :
    Exp (eRow h) (fun ρ : Fin (sz k) → Fin n =>
      if k ∈ L then lif h ρ (by have := hsz k; omega) else unl h ρ (by have := hsz k; omega)) := by
  intro a b ρ
  by_cases hk : k ∈ L
  · simp only [hk, if_true, ite_true]
    exact exp_lift (eRow h) (eRow_inj h) ⟨N - 1, by omega⟩ (eRow_ne_last h)
      (Fin.castLE (by have := hsz k; omega)) a b ρ
  · simp only [hk, if_false, ite_false]
    exact exp_gmin (eRow h) (eRow_inj h) (Fin.castLE (by have := hsz k; omega)) a b ρ

/- English proof (translation)
Rewrite using `[rowGen_gmin, Finset.sum_eq_single ∅]`. Establish `hu : upd ρ ∅ a = ρ`. Use function extensionality and compare the values at `p`. Simplify using `[upd]`. Simplify using `[hu]`.

Introduce `S _ hS split_ifs with hc`. Take `⟨p0, hp0⟩` from `Finset.nonempty_iff_ne_empty.mpr hS`. Break down `hρ with ⟨pa, hpa⟩ | hρ` into its components or cases. Establish `hne : pa ≠ p0`. Introduce `h`.

Apply `hab` to reduce the goal to its premises. Rewrite using `[← hpa, h]`. Conclude with `hc p0 hp0`. Establish `hpaS : pa ∉ S` using `fun h => hab (hpa.symm.trans (hc pa h))`. Establish `hz : gmin (upd ρ S a) κ = 0`.

Unfold `gmin`. Apply `Matrix.det_zero_of_row_eq hne` to reduce the goal to its premises. Use function extensionality and compare the values at `q`. Simplify using `[upd, hpaS, hp0, hpa]`. Simplify using `[hz]`.

Conclude with `absurd (hc p0 hp0) (hρ p0)`. Both sides reduce to the same expression. Simplify using the standard rewrite rules.
-/
theorem rowGen_gmin_inv {r c m : ℕ} (a b : Fin r) (hab : a ≠ b) (ρ : Fin m → Fin r) (κ : Fin m → Fin c)
    (hρ : (∃ pa, ρ pa = a) ∨ ∀ p, ρ p ≠ b) :
    rowGen ℤ a b (gmin ρ κ) = Polynomial.C (gmin ρ κ) := by
  classical
  rw [rowGen_gmin, Finset.sum_eq_single ∅]
  · have hu : upd ρ ∅ a = ρ := by
      funext p
      simp [upd]
    simp [hu]
  · intro S _ hS
    split_ifs with hc
    · obtain ⟨p0, hp0⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      rcases hρ with ⟨pa, hpa⟩ | hρ
      · have hne : pa ≠ p0 := by
          intro h
          apply hab
          rw [← hpa, h]
          exact hc p0 hp0
        have hpaS : pa ∉ S := fun h => hab (hpa.symm.trans (hc pa h))
        have hz : gmin (upd ρ S a) κ = 0 := by
          unfold gmin
          apply Matrix.det_zero_of_row_eq hne
          funext q
          simp [upd, hpaS, hp0, hpa]
        simp [hz]
      · exact absurd (hc p0 hp0) (hρ p0)
    · rfl
  · simp

/- English proof (translation)
Establish `hab' : eRow h a ≠ eRow h b` using `fun h' => hab (eRow_inj h h')`. Establish `hlp : ∀ i : Fin n, i.1 + 1 = n → ∀ (hr : i.1 + 1 ≤ N) (hc : i.1 + 1 ≤ N), rowGen ℤ (eRow h a) (eRow h b) (lpMinor ℤ (i.1 + 1) hr hc) = Polynomial.C (lpMinor ℤ (i.1 + 1) hr hc)`. Introduce `i hi hr hc`. Establish `ha` using `a.2`. Conclude with `rowGen_gmin_inv _ _ hab' (Fin.castLE hr) (Fin.castLE hc) (Or.inl ⟨⟨a.1, by omega⟩, Fin.ext (by simp [eRow])⟩)`.

Establish `hrz : ∀ i : Fin n, i.1 = 0 → ∀ (hs : i.1 + 1 ≤ N), rowGen ℤ (eRow h a) (eRow h b) (initMinor ℤ (rowsZ h i) hs) = Polynomial.C (initMinor ℤ (rowsZ h i) hs)`. Introduce `i hi hs`. Use `rowGen_gmin_inv _ _ hab' (rowsZ h i) (Fin.castLE hs) (Or.inr fun p hp => ?_)` and prove the remaining obligations. Establish `hp0 : p.1 = i.1` using `by have := p.2; omega`. Apply `eRow_ne_last h b` to reduce the goal to its premises.

Rewrite using `[← hp]`. Simplify using `[rowsZ, hp0]`. Unfold `C0`. Simplify using `only [map_prod, map_mul]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Use `congr 1`. Use `split_ifs with hi`. Rewrite using `[map_pow, map_pow, hlp i hi]`. Simplify using the standard rewrite rules. Use `split_ifs with hi`.

Rewrite using `[map_pow, map_pow, hrz i hi]`. Simplify using the standard rewrite rules.
-/
theorem polarization_of_constant {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (a b : Fin n) (hab : a ≠ b) :
    rowGen ℤ (eRow h a) (eRow h b) (C0 h lam sg) = Polynomial.C (C0 h lam sg) := by
  have hab' : eRow h a ≠ eRow h b := fun h' => hab (eRow_inj h h')
  have hlp : ∀ i : Fin n, i.1 + 1 = n → ∀ (hr : i.1 + 1 ≤ N) (hc : i.1 + 1 ≤ N),
      rowGen ℤ (eRow h a) (eRow h b) (lpMinor ℤ (i.1 + 1) hr hc) = Polynomial.C (lpMinor ℤ (i.1 + 1) hr hc) := by
    intro i hi hr hc
    have ha := a.2
    exact rowGen_gmin_inv _ _ hab' (Fin.castLE hr) (Fin.castLE hc)
      (Or.inl ⟨⟨a.1, by omega⟩, Fin.ext (by simp [eRow])⟩)
  have hrz : ∀ i : Fin n, i.1 = 0 → ∀ (hs : i.1 + 1 ≤ N),
      rowGen ℤ (eRow h a) (eRow h b) (initMinor ℤ (rowsZ h i) hs) = Polynomial.C (initMinor ℤ (rowsZ h i) hs) := by
    intro i hi hs
    refine rowGen_gmin_inv _ _ hab' (rowsZ h i) (Fin.castLE hs) (Or.inr fun p hp => ?_)
    have hp0 : p.1 = i.1 := by have := p.2; omega
    apply eRow_ne_last h b
    rw [← hp]
    simp [rowsZ, hp0]
  unfold C0
  simp only [map_prod, map_mul]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  · split_ifs with hi
    · rw [map_pow, map_pow, hlp i hi]
    · simp
  · split_ifs with hi
    · rw [map_pow, map_pow, hrz i hi]
    · simp

/- English proof (translation)
Use `⟨twd sz w (Finsupp.single I 1), ?_, ?_⟩` and prove the remaining obligations. Establish `hmap : w.map (fun x => (id x.1, id x.2.1, x.2.2)) = w`. Proceed by induction on `w with`. Consider the case `nil => rfl`. Consider the case `cons x w ih => simp`.

Establish `h1` using `applyWord_comb id sz (fun k ρ => initMinor ℤ (n := n) ρ (hsz k)) (exp_bidet sz hsz) 1 (fun a b _ => by simp) w hw (Finsupp.single I 1)`. Rewrite `h1` using `[hmap, Finsupp.linearCombination_single, one_smul]`. Simplify using `only [one_mul, Finsupp.linearCombination_apply] at h1`. Unfold `bideterminant`. Conclude with `h1`.

Establish `h2` using `applyWord_comb (eRow h) sz (fun k ρ => if k ∈ L then lif h ρ (by have := hsz k; omega) else unl h ρ (by have := hsz k; omega)) (exp_M h sz hsz L) (C0 h lam sg) (fun a b hab => polarization_of_constant h lam sg a b hab) w hw (Finsupp.single I 1)`. Rewrite `h2` using `[Finsupp.linearCombination_single, one_smul]`. Simplify using `only [Finsupp.linearCombination_apply] at h2`. Unfold `Mlift`. Conclude with `h2`.
-/
theorem word_clause {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) {K : ℕ} (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ n) (L : Finset (Fin K)) (I : ∀ k, Fin (sz k) → Fin n)
    (w : List (Fin n × Fin n × ℕ)) (hw : OffDiag w) :
    ∃ d : (∀ k, Fin (sz k) → Fin n) →₀ ℤ,
      applyWord ℤ w (bideterminant ℤ sz hsz I) = d.sum (fun J c => c • bideterminant ℤ sz hsz J) ∧
      applyWord ℤ (liftWord h w) (Mlift h lam sg sz hsz L I) =
        d.sum (fun J c => c • Mlift h lam sg sz hsz L J) := by
  classical
  refine ⟨twd sz w (Finsupp.single I 1), ?_, ?_⟩
  · have hmap : w.map (fun x => (id x.1, id x.2.1, x.2.2)) = w := by
      induction w with
      | nil => rfl
      | cons x w ih => simp
    have h1 := applyWord_comb id sz (fun k ρ => initMinor ℤ (n := n) ρ (hsz k)) (exp_bidet sz hsz) 1
      (fun a b _ => by simp) w hw (Finsupp.single I 1)
    rw [hmap, Finsupp.linearCombination_single, one_smul] at h1
    simp only [one_mul, Finsupp.linearCombination_apply] at h1
    unfold bideterminant
    exact h1
  · have h2 := applyWord_comb (eRow h) sz
      (fun k ρ => if k ∈ L then lif h ρ (by have := hsz k; omega) else unl h ρ (by have := hsz k; omega))
      (exp_M h sz hsz L) (C0 h lam sg) (fun a b hab => polarization_of_constant h lam sg a b hab) w hw (Finsupp.single I 1)
    rw [Finsupp.linearCombination_single, one_smul] at h2
    simp only [Finsupp.linearCombination_apply] at h2
    unfold Mlift
    exact h2

end PI.WGL.LTC
