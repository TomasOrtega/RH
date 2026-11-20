import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.DetPowUnitriB

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions MvPolynomial

def swapM {n : ℕ} (σ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => if σ i = j then 1 else 0

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [swapM, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]`. Rewrite using `[Finset.sum_eq_single (σ i)]`. Simplify using `[hσ]`. Introduce `b _ hb`.

Rewrite using `[if_neg (Ne.symm hb), zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem swapM_sq {n : ℕ} (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j) : swapM σ * swapM σ = 1 := by
  ext i j
  simp only [swapM, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (σ i)]
  · simp [hσ]
  · intro b _ hb
    rw [if_neg (Ne.symm hb), zero_mul]
  · simp

def swapGL {n : ℕ} (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j) : GL (Fin n) ℂ :=
  ⟨swapM σ, swapM σ, swapM_sq σ hσ, swapM_sq σ hσ⟩

def tauB {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (a : Fin N) : Fin N :=
  if ha : a.1 < n then ⟨(σ ⟨a.1, ha⟩).1, by have := (σ ⟨a.1, ha⟩).isLt; omega⟩ else a

/- English proof (translation)
Unfold `tauB`. Rewrite using `[dif_pos ha]`.
-/
theorem tauB_val {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (a : Fin N) (ha : a.1 < n) :
    (tauB h σ a).1 = (σ ⟨a.1, ha⟩).1 := by
  unfold tauB; rw [dif_pos ha]

/- English proof (translation)
Unfold `tauB`. Rewrite using `[dif_neg ha]`.
-/
theorem tauB_of_not {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (a : Fin N) (ha : ¬ a.1 < n) :
    tauB h σ a = a := by
  unfold tauB; rw [dif_neg ha]

/- English proof (translation)
Distinguish the cases in `ha : a.1 < n`. Establish `h2 : (tauB h σ a).1 < n` using `by rw [tauB_val h σ a ha]; exact (σ _).isLt`. Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[tauB_val h σ _ h2]`. Establish `e : (⟨(tauB h σ a).1, h2⟩ : Fin n) = σ ⟨a.1, ha⟩` using `Fin.ext (tauB_val h σ a ha)`.

Rewrite using `[e, hσ]`. Rewrite using `[tauB_of_not h σ a ha, tauB_of_not h σ a ha]`.
-/
theorem tauB_invol {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j) (a : Fin N) :
    tauB h σ (tauB h σ a) = a := by
  by_cases ha : a.1 < n
  · have h2 : (tauB h σ a).1 < n := by rw [tauB_val h σ a ha]; exact (σ _).isLt
    apply Fin.ext
    rw [tauB_val h σ _ h2]
    have e : (⟨(tauB h σ a).1, h2⟩ : Fin n) = σ ⟨a.1, ha⟩ := Fin.ext (tauB_val h σ a ha)
    rw [e, hσ]
  · rw [tauB_of_not h σ a ha, tauB_of_not h σ a ha]

/- English proof (translation)
Establish `ha2` using `a.2`. Establish `hb2` using `b.2`. Rewrite using `[embGL_apply_B]`. Apply the tactic sequence `by_cases hb : b.1 < n <;> by_cases ha : a.1 < n`. Rewrite using `[dif_pos hb, dif_pos ha] show swapM σ ⟨b.1, hb⟩ ⟨a.1, ha⟩ = _`.

Simplify using `only [swapM, Matrix.of_apply]`. Establish `key : σ ⟨b.1, hb⟩ = ⟨a.1, ha⟩ ↔ b = tauB h σ a`. Prove the components needed by the constructor for the conclusion. Introduce `e`. Apply `Fin.ext` to reduce the goal to its premises.

Rewrite using `[tauB_val h σ a ha, ← e, hσ]`. Introduce `e`. Establish `e2 : (⟨b.1, hb⟩ : Fin n) = σ ⟨a.1, ha⟩` using `Fin.ext (by show b.1 = (σ ⟨a.1, ha⟩).1`. Rewrite using `[← tauB_val h σ a ha, e])`. Rewrite using `[e2, hσ]`.

Distinguish the cases in `hk : b = tauB h σ a`. Rewrite using `[if_pos hk, if_pos (key.mpr hk)]`. Rewrite using `[if_neg hk, if_neg (fun e => hk (key.mp e))]`. Rewrite using `[dif_pos hb, dif_neg ha, tauB_of_not h σ a ha, if_neg (fun e : b = a => ha (e ▸ hb))]`. Establish `hne : b ≠ tauB h σ a`.

Introduce `e`. Apply `hb` to reduce the goal to its premises. Rewrite using `[e, tauB_val h σ a ha]`. Conclude with `(σ _).isLt`. Rewrite using `[dif_neg hb, if_pos ha, if_neg hne]`.

Establish `hab : b = a` using `Fin.ext (by omega)`. Rewrite using `[dif_neg hb, if_neg ha, tauB_of_not h σ a ha, if_pos hab]`.
-/
theorem swap_entry_B {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j) (a b : Fin N) :
    ((embGL ℂ n N h (swapGL σ hσ) : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) b a =
      if b = tauB h σ a then 1 else 0 := by
  have ha2 := a.2
  have hb2 := b.2
  rw [embGL_apply_B]
  by_cases hb : b.1 < n <;> by_cases ha : a.1 < n
  · rw [dif_pos hb, dif_pos ha]
    show swapM σ ⟨b.1, hb⟩ ⟨a.1, ha⟩ = _
    simp only [swapM, Matrix.of_apply]
    have key : σ ⟨b.1, hb⟩ = ⟨a.1, ha⟩ ↔ b = tauB h σ a := by
      constructor
      · intro e
        apply Fin.ext
        rw [tauB_val h σ a ha, ← e, hσ]
      · intro e
        have e2 : (⟨b.1, hb⟩ : Fin n) = σ ⟨a.1, ha⟩ := Fin.ext (by
          show b.1 = (σ ⟨a.1, ha⟩).1
          rw [← tauB_val h σ a ha, e])
        rw [e2, hσ]
    by_cases hk : b = tauB h σ a
    · rw [if_pos hk, if_pos (key.mpr hk)]
    · rw [if_neg hk, if_neg (fun e => hk (key.mp e))]
  · rw [dif_pos hb, dif_neg ha, tauB_of_not h σ a ha, if_neg (fun e : b = a => ha (e ▸ hb))]
  · have hne : b ≠ tauB h σ a := by
      intro e
      apply hb
      rw [e, tauB_val h σ a ha]
      exact (σ _).isLt
    rw [dif_neg hb, if_pos ha, if_neg hne]
  · have hab : b = a := Fin.ext (by omega)
    rw [dif_neg hb, if_neg ha, tauB_of_not h σ a ha, if_pos hab]

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Rewrite using `[rowAct_X_B, rename_X]`. Rewrite using `[Finset.sum_eq_single (tauB h σ v.1)]`. Rewrite using `[Matrix.transpose_apply, swap_entry_B, if_pos rfl, map_one, one_mul]`.

Introduce `b _ hb`. Rewrite using `[Matrix.transpose_apply, swap_entry_B, if_neg hb, map_zero, zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem rowAct_swap_B {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := N)
              (((embGL ℂ n N h (swapGL σ hσ) : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).transpose) =
      rename (fun v : Fin N × Fin N => (tauB h σ v.1, v.2)) := by
  apply MvPolynomial.algHom_ext
  intro v
  rw [rowAct_X_B, rename_X]
  rw [Finset.sum_eq_single (tauB h σ v.1)]
  · rw [Matrix.transpose_apply, swap_entry_B, if_pos rfl, map_one, one_mul]
  · intro b _ hb
    rw [Matrix.transpose_apply, swap_entry_B, if_neg hb, map_zero, zero_mul]
  · simp

/- English proof (translation)
Use function extensionality and compare the values at `j`. Distinguish the cases in `ha : v.1.1 < n`. Establish `h2 : (tauB h σ v.1).1 < n` using `by rw [tauB_val h σ _ ha]; exact (σ _).isLt dsimp only [wnB]`. Rewrite using `[dif_pos h2, dif_pos ha]`. Establish `e : (⟨(tauB h σ v.1).1, h2⟩ : Fin n) = σ ⟨v.1.1, ha⟩` using `Fin.ext (tauB_val h σ _ ha)`.

Rewrite using `[e, Pi.single_apply, Pi.single_apply]`. Distinguish the cases in `hj : σ j = ⟨v.1.1, ha⟩`. Rewrite using `[if_pos hj, if_pos (by rw [← hj, hσ])]`. Rewrite using `[if_neg hj, if_neg (fun e => hj (by rw [e, hσ]))]`. Establish `h2 : ¬ (tauB h σ v.1).1 < n` using `by rw [tauB_of_not h σ _ ha]; exact ha dsimp only [wnB]`.

Rewrite using `[dif_neg h2, dif_neg ha]`. Both sides reduce to the same expression.
-/
theorem wnB_tau {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j)
    (v : Fin N × Fin N) : wnB n N (tauB h σ v.1, v.2) = fun j => wnB n N v (σ j) := by
  funext j
  by_cases ha : v.1.1 < n
  · have h2 : (tauB h σ v.1).1 < n := by rw [tauB_val h σ _ ha]; exact (σ _).isLt
    dsimp only [wnB]
    rw [dif_pos h2, dif_pos ha]
    have e : (⟨(tauB h σ v.1).1, h2⟩ : Fin n) = σ ⟨v.1.1, ha⟩ := Fin.ext (tauB_val h σ _ ha)
    rw [e, Pi.single_apply, Pi.single_apply]
    by_cases hj : σ j = ⟨v.1.1, ha⟩
    · rw [if_pos hj, if_pos (by rw [← hj, hσ])]
    · rw [if_neg hj, if_neg (fun e => hj (by rw [e, hσ]))]
  · have h2 : ¬ (tauB h σ v.1).1 < n := by rw [tauB_of_not h σ _ ha]; exact ha
    dsimp only [wnB]
    rw [dif_neg h2, dif_neg ha]
    rfl

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun i (c : ℕ) => c • wnB n N i) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]`. Use function extensionality and compare the values at `j`. Rewrite using `[Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Finset.sum_apply, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, wnB_tau h σ hσ]`.
-/
theorem weight_tau_B {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j)
    (u : Fin N × Fin N →₀ ℕ) :
    Finsupp.weight (wnB n N) (Finsupp.mapDomain (fun v : Fin N × Fin N => (tauB h σ v.1, v.2)) u) =
      fun j => Finsupp.weight (wnB n N) u (σ j) := by
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun i (c : ℕ) => c • wnB n N i) (fun _ => zero_smul _ _)
    (fun _ _ _ => add_smul _ _ _)]
  funext j
  rw [Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Pi.smul_apply, wnB_tau h σ hσ]

/- English proof (translation)
Introduce `d hd`. Take `⟨u, rfl, hu⟩` from `coeff_rename_ne_zero _ _ _ hd`. Rewrite using `[weight_tau_B h σ hσ, hg hu]`.
-/
theorem rename_tau_homog_B {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j)
    (g : MvPolynomial (Fin N × Fin N) ℂ) (m : Fin n → ℕ) (hg : IsWeightedHomogeneous (wnB n N) g m) :
    IsWeightedHomogeneous (wnB n N) (rename (fun v : Fin N × Fin N => (tauB h σ v.1, v.2)) g)
      (fun j => m (σ j)) := by
  intro d hd
  obtain ⟨u, rfl, hu⟩ := coeff_rename_ne_zero _ _ _ hd
  rw [weight_tau_B h σ hσ, hg hu]

/- English proof (translation)
Apply `rename_injective` to reduce the goal to its premises. Introduce `v w e`. Establish `e1` using `congrArg Prod.fst e`. Establish `e2` using `congrArg Prod.snd e`. Simplify using `only at e1 e2`.

Establish `e3 : v.1 = w.1`. Rewrite using `[← tauB_invol h σ hσ v.1, e1, tauB_invol h σ hσ w.1]`. Conclude with `Prod.ext e3 e2`.
-/
theorem rename_tau_inj_B {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j) :
    Function.Injective (rename (R := ℂ) (fun v : Fin N × Fin N => (tauB h σ v.1, v.2))) := by
  apply rename_injective
  intro v w e
  have e1 := congrArg Prod.fst e
  have e2 := congrArg Prod.snd e
  simp only at e1 e2
  have e3 : v.1 = w.1 := by
    rw [← tauB_invol h σ hσ v.1, e1, tauB_invol h σ hσ w.1]
  exact Prod.ext e3 e2

/- English proof (translation)
Establish `h1` using `hW (swapGL σ hσ) g hg`. Unfold `sqAct at h1`. Rewrite `h1` using `[rowAct_swap_B]`. Establish `hu : detPow ℂ N (embGL ℂ n N h (swapGL σ hσ)) lam.detShift ≠ 0` using `Units.ne_zero _`. Use `W.smul_mem (detPow ℂ N (embGL ℂ n N h (swapGL σ hσ)) lam.detShift)⁻¹ h1` as an intermediate fact.

Rewrite `this` using `[smul_smul, inv_mul_cancel₀ hu, one_smul]`. Then use the resulting hypothesis.
-/
theorem swap_mem_B {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (W : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ))
    (hW : IsStable h lam W) (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j) (g : MvPolynomial (Fin N × Fin N) ℂ)
    (hg : g ∈ W) : rename (fun v : Fin N × Fin N => (tauB h σ v.1, v.2)) g ∈ W := by
  have h1 := hW (swapGL σ hσ) g hg
  unfold sqAct at h1
  rw [rowAct_swap_B] at h1
  have hu : detPow ℂ N (embGL ℂ n N h (swapGL σ hσ)) lam.detShift ≠ 0 := Units.ne_zero _
  have := W.smul_mem (detPow ℂ N (embGL ℂ n N h (swapGL σ hσ)) lam.detShift)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hu, one_smul] at this

/- English proof (translation)
Use `set a : Fin n := ⟨i, by omega⟩ with ha`. Use `set b : Fin n := ⟨i + 1, hi⟩ with hb`. Establish `hab : a ≠ b`. Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact.

Simplify using `[ha, hb] at this`. Establish `split : ∀ f : Fin n → ℕ, ∑ j, f j = f a + f b + ∑ j ∈ (Finset.univ.erase a).erase b, f j`. Introduce `f`. Rewrite using `[← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩)]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[PsiB_apply, PsiB_apply, split, split]`. Establish `hrest : ∑ j ∈ (Finset.univ.erase a).erase b, (n - j.1) * m (Equiv.swap a b j) = ∑ j ∈ (Finset.univ.erase a).erase b, (n - j.1) * m j`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Establish `hjb` using `Finset.ne_of_mem_erase hj`. Establish `hja` using `Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)`.

Rewrite using `[Equiv.swap_apply_of_ne_of_ne hja hjb]`. Rewrite using `[hrest, Equiv.swap_apply_left, Equiv.swap_apply_right]`. Establish `e1 : n - a.1 = (n - b.1) + 1` using `by simp only [ha, hb]; omega`. Rewrite using `[e1]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem PsiB_swap_B {n : ℕ} (m : Fin n → ℕ) (i : ℕ) (hi : i + 1 < n)
    (hlt : m ⟨i, by omega⟩ < m ⟨i + 1, hi⟩) :
    PsiB n m < PsiB n (fun j => m (Equiv.swap (⟨i, by omega⟩ : Fin n) ⟨i + 1, hi⟩ j)) := by
  set a : Fin n := ⟨i, by omega⟩ with ha
  set b : Fin n := ⟨i + 1, hi⟩ with hb
  have hab : a ≠ b := by
    intro e
    have := congrArg Fin.val e
    simp [ha, hb] at this
  have split : ∀ f : Fin n → ℕ, ∑ j, f j = f a + f b + ∑ j ∈ (Finset.univ.erase a).erase b, f j := by
    intro f
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩)]
    ring
  rw [PsiB_apply, PsiB_apply, split, split]
  have hrest : ∑ j ∈ (Finset.univ.erase a).erase b, (n - j.1) * m (Equiv.swap a b j) =
      ∑ j ∈ (Finset.univ.erase a).erase b, (n - j.1) * m j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjb := Finset.ne_of_mem_erase hj
    have hja := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)
    rw [Equiv.swap_apply_of_ne_of_ne hja hjb]
  rw [hrest, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have e1 : n - a.1 = (n - b.1) + 1 := by simp only [ha, hb]; omega
  rw [e1]
  nlinarith

/- English proof (translation)
Set `M : ℕ → ℕ` to `fun k => if hk : k < n then m ⟨k, hk⟩ else 0`. Establish `hM : Antitone M`. Use `antitone_nat_of_succ_le fun k => ?_` and prove the remaining obligations. Distinguish the cases in `hk1 : k + 1 < n`. Simplify using `only [M, dif_pos hk1, dif_pos (show k < n by omega)]`.

Conclude with `hdom k hk1`. Simplify using `only [M, dif_neg hk1]`. Conclude with `Nat.zero_le _`. Introduce `a b hab`. Use `hM (Fin.le_def.mp hab)` as an intermediate fact.

Simplify using `only [M, dif_pos a.2, dif_pos b.2] at this`. Conclude with `this`.
-/
theorem antitone_of_succ_B {n : ℕ} (m : Fin n → ℕ)
    (hdom : ∀ (i : ℕ) (hi : i + 1 < n), m ⟨i + 1, hi⟩ ≤ m ⟨i, by omega⟩) : Antitone m := by
  let M : ℕ → ℕ := fun k => if hk : k < n then m ⟨k, hk⟩ else 0
  have hM : Antitone M := by
    refine antitone_nat_of_succ_le fun k => ?_
    by_cases hk1 : k + 1 < n
    · simp only [M, dif_pos hk1, dif_pos (show k < n by omega)]
      exact hdom k hk1
    · simp only [M, dif_neg hk1]
      exact Nat.zero_le _
  intro a b hab
  have := hM (Fin.le_def.mp hab)
  simp only [M, dif_pos a.2, dif_pos b.2] at this
  exact this

/- English proof (translation)
Unfold `sqAct`. Rewrite using `[embGL_diag_B, Matrix.diagonal_transpose, rowAct_diag_homog _ _ _ hm, smul_smul]`. Use `congr 1`. Establish `hdet : Matrix.GeneralLinearGroup.det (embGL ℂ n N h (diagGL ℂ n t)) = ∏ j, t j`. Use `ext`.

Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, embGL_diag_B, Matrix.det_diagonal, Units.coe_prod]`. Substitute `h` using the available equality. Rewrite using `[Fin.prod_univ_castSucc]`. Simplify using `[dB]`. Unfold `detPow`.

Rewrite using `[hdet]`. Establish `hchi : chiB (fun j => ((t j : ℂˣ) : ℂ)) m = ((∏ j, t j ^ (m j) : ℂˣ) : ℂ)`. Simplify using `[chiB, Units.coe_prod]`. Rewrite using `[hchi, ← Units.val_mul]`. Use `congr 1`.

Simplify using `only [zpow_add, Finset.prod_mul_distrib, zpow_natCast, Finset.prod_zpow]`. Rewrite using `[mul_comm]`.
-/
theorem torus_fix_B {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (g : MvPolynomial (Fin N × Fin N) ℂ)
    (m : Fin n → ℕ) (hm : IsWeightedHomogeneous (wnB n N) g m) (t : Fin n → ℂˣ) :
    sqAct ℂ N lam (embGL ℂ n N h (diagGL ℂ n t)) g =
      ((∏ j, t j ^ ((m j : ℤ) + lam.detShift) : ℂˣ) : ℂ) • g := by
  unfold sqAct
  rw [embGL_diag_B, Matrix.diagonal_transpose, rowAct_diag_homog _ _ _ hm, smul_smul]
  congr 1
  have hdet : Matrix.GeneralLinearGroup.det (embGL ℂ n N h (diagGL ℂ n t)) = ∏ j, t j := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, embGL_diag_B, Matrix.det_diagonal, Units.coe_prod]
    subst h
    rw [Fin.prod_univ_castSucc]
    simp [dB]
  unfold detPow
  rw [hdet]
  have hchi : chiB (fun j => ((t j : ℂˣ) : ℂ)) m = ((∏ j, t j ^ (m j) : ℂˣ) : ℂ) := by
    simp [chiB, Units.coe_prod]
  rw [hchi, ← Units.val_mul]
  congr 1
  simp only [zpow_add, Finset.prod_mul_distrib, zpow_natCast, Finset.prod_zpow]
  rw [mul_comm]

/- English proof (translation)
Introduce `n N h lam W hWle hW hne`. Set `Pk : ℕ → Prop` to `fun k => ∃ g ∈ W, g ≠ 0 ∧ ∃ m, IsWeightedHomogeneous (wnB n N) g m ∧ PsiB n m = k`. Establish `hex : ∃ k, Pk k`. Take `⟨f, hfW, hf0⟩` from `(Submodule.ne_bot_iff W).mp hne`. Assume the negation of the conclusion as `hno`.

Use `push_neg at hno`. Apply `hf0` to reduce the goal to its premises. Rewrite using `[← comp_sum_B (wnB n N) f (f.support.image (Finsupp.weight (wnB n N))) (fun e he => Finset.mem_image_of_mem _ he)]`. Use `Finset.sum_eq_zero fun m _ => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hc`.

Conclude with `hno _ ⟨_, graded_B h lam W hW f hfW m, hc, m, weightedHomogeneousComponent_isWeightedHomogeneous _ _, rfl⟩`. Take `⟨k0, hk0⟩` from `hex`. Establish `hPb : ∀ k, Pk k → k ≤ n * ∑ s, lam.natW s`. Introduce and unpack `k ⟨g, hgW, hg0, m, hm, rfl⟩`. Conclude with `bound_B lam g (hWle hgW) hg0 m hm`.

Establish `hK : Pk (Nat.findGreatest Pk (n * ∑ s, lam.natW s))` using `Nat.findGreatest_spec (hPb k0 hk0) hk0`. Establish `hmax : ∀ g ∈ W, g ≠ 0 → ∀ m, IsWeightedHomogeneous (wnB n N) g m → PsiB n m ≤ Nat.findGreatest Pk (n * ∑ s, lam.natW s)`. Introduce `g hgW hg0 m hm`. Conclude with `Nat.le_findGreatest (hPb _ ⟨g, hgW, hg0, m, hm, rfl⟩) ⟨g, hgW, hg0, m, hm, rfl⟩`. Take `⟨g, hgW, hg0, m, hm, hmK⟩` from `hK`.

Establish `hfix : ∀ u : GL (Fin n) ℂ, (∀ i j, j < i → u i j = 0) → (∀ i, u i i = 1) → sqAct ℂ N lam (embGL ℂ n N h u) g = g`. Introduce `u hl hd`. Take `⟨h1, h2, _⟩` from `embGL_unitri_B h u hl hd`. Establish `hs : sqAct ℂ N lam (embGL ℂ n N h u) g = Formalism.GradedWeylDivisibility.rowAct ℂ (n` using `N) (((embGL ℂ n N h u : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).transpose) g := by`. Unfold `sqAct`.

Rewrite using `[detPow_unitri_B h u hl hd, one_smul]`. Rewrite using `[hs]`. Establish `hR : Formalism.GradedWeylDivisibility.rowAct ℂ (n` using `N) (((embGL ℂ n N h u : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).transpose) g - g = 0 := by`. Use `high_zero_B h lam W hW _ hmax _ ?_ ?_` and prove the remaining obligations. Use `W.sub_mem ?_ hgW` and prove the remaining obligations.

Rewrite using `[← hs]`. Conclude with `hW u g hgW`. Use `GoodB_homog (Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (((embGL ℂ n N h u : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).transpose)) (psiB n N) (fun v => GoodB_X_tri _ (fun a => by rw [Matrix.transpose_apply]; exact h1 a) (fun a b hab hne => h2 a b hab (by rwa [Matrix.trans …` as an intermediate fact. Rewrite `this` using `[hmK]`. Then use the resulting hypothesis. Conclude with `sub_eq_zero.mp hR`.

Establish `hdom : ∀ (i : ℕ) (hi : i + 1 < n), m ⟨i + 1, hi⟩ ≤ m ⟨i, by omega⟩`. Introduce `i hi`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Set `σ` to `Equiv.swap (⟨i, by omega⟩ : Fin n) ⟨i + 1, hi⟩`.

Establish `hσ : ∀ j, σ (σ j) = j` using `fun j => Equiv.swap_apply_self _ _ j`. Establish `hgt` using `PsiB_swap_B m i hi hlt`. Establish `hle` using `hmax _ (swap_mem_B h lam W hW σ hσ g hgW) (fun e => hg0 (rename_tau_inj_B h σ hσ (by rw [e, map_zero]))) _ (rename_tau_homog_B h σ hσ g m hm)`. Rewrite `hle` using `[← hmK]`. Conclude with `absurd hle (not_le.mpr hgt)`.

Establish `hanti : Antitone m` using `antitone_of_succ_B m hdom`. Set `mu : DomWeight n` to `⟨fun j => (m j : ℤ) + lam.detShift, fun a b hab => by`. Use `hanti hab` as an intermediate fact. Simplify using `only`. Use the proof step `omega⟩`.

Conclude with `⟨g, hgW, hg0, mu, hfix, fun t => torus_fix_B h lam g m hm t⟩`.
-/
theorem highestVec_B : HighestVec := by
  classical
  intro n N h lam W hWle hW hne
  let Pk : ℕ → Prop := fun k =>
    ∃ g ∈ W, g ≠ 0 ∧ ∃ m, IsWeightedHomogeneous (wnB n N) g m ∧ PsiB n m = k
  have hex : ∃ k, Pk k := by
    obtain ⟨f, hfW, hf0⟩ := (Submodule.ne_bot_iff W).mp hne
    by_contra hno
    push_neg at hno
    apply hf0
    rw [← comp_sum_B (wnB n N) f (f.support.image (Finsupp.weight (wnB n N)))
      (fun e he => Finset.mem_image_of_mem _ he)]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_contra hc
    exact hno _ ⟨_, graded_B h lam W hW f hfW m, hc, m, weightedHomogeneousComponent_isWeightedHomogeneous _ _, rfl⟩
  obtain ⟨k0, hk0⟩ := hex
  have hPb : ∀ k, Pk k → k ≤ n * ∑ s, lam.natW s := by
    rintro k ⟨g, hgW, hg0, m, hm, rfl⟩
    exact bound_B lam g (hWle hgW) hg0 m hm
  have hK : Pk (Nat.findGreatest Pk (n * ∑ s, lam.natW s)) := Nat.findGreatest_spec (hPb k0 hk0) hk0
  have hmax : ∀ g ∈ W, g ≠ 0 → ∀ m, IsWeightedHomogeneous (wnB n N) g m →
      PsiB n m ≤ Nat.findGreatest Pk (n * ∑ s, lam.natW s) := by
    intro g hgW hg0 m hm
    exact Nat.le_findGreatest (hPb _ ⟨g, hgW, hg0, m, hm, rfl⟩) ⟨g, hgW, hg0, m, hm, rfl⟩
  obtain ⟨g, hgW, hg0, m, hm, hmK⟩ := hK
  have hfix : ∀ u : GL (Fin n) ℂ, (∀ i j, j < i → u i j = 0) → (∀ i, u i i = 1) →
      sqAct ℂ N lam (embGL ℂ n N h u) g = g := by
    intro u hl hd
    obtain ⟨h1, h2, _⟩ := embGL_unitri_B h u hl hd
    have hs : sqAct ℂ N lam (embGL ℂ n N h u) g = Formalism.GradedWeylDivisibility.rowAct ℂ (n := N)
        (((embGL ℂ n N h u : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).transpose) g := by
      unfold sqAct
      rw [detPow_unitri_B h u hl hd, one_smul]
    rw [hs]
    have hR : Formalism.GradedWeylDivisibility.rowAct ℂ (n := N)
        (((embGL ℂ n N h u : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).transpose) g - g = 0 := by
      refine high_zero_B h lam W hW _ hmax _ ?_ ?_
      · refine W.sub_mem ?_ hgW
        rw [← hs]
        exact hW u g hgW
      · have := GoodB_homog (Formalism.GradedWeylDivisibility.rowAct ℂ (n := N)
          (((embGL ℂ n N h u : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).transpose)) (psiB n N)
          (fun v => GoodB_X_tri _ (fun a => by rw [Matrix.transpose_apply]; exact h1 a)
            (fun a b hab hne => h2 a b hab (by rwa [Matrix.transpose_apply] at hne)) v) g (PsiB n m)
          (homog_psi_B g m hm)
        rwa [hmK] at this
    exact sub_eq_zero.mp hR
  have hdom : ∀ (i : ℕ) (hi : i + 1 < n), m ⟨i + 1, hi⟩ ≤ m ⟨i, by omega⟩ := by
    intro i hi
    by_contra hlt
    push_neg at hlt
    let σ := Equiv.swap (⟨i, by omega⟩ : Fin n) ⟨i + 1, hi⟩
    have hσ : ∀ j, σ (σ j) = j := fun j => Equiv.swap_apply_self _ _ j
    have hgt := PsiB_swap_B m i hi hlt
    have hle := hmax _ (swap_mem_B h lam W hW σ hσ g hgW)
      (fun e => hg0 (rename_tau_inj_B h σ hσ (by rw [e, map_zero])))
      _ (rename_tau_homog_B h σ hσ g m hm)
    rw [← hmK] at hle
    exact absurd hle (not_le.mpr hgt)
  have hanti : Antitone m := antitone_of_succ_B m hdom
  let mu : DomWeight n := ⟨fun j => (m j : ℤ) + lam.detShift, fun a b hab => by
    have := hanti hab
    simp only
    omega⟩
  exact ⟨g, hgW, hg0, mu, hfix, fun t => torus_fix_B h lam g m hm t⟩

end PI.WGB
