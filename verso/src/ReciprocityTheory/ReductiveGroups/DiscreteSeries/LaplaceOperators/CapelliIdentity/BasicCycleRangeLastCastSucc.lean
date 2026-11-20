import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.CapelliCentralStatement

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

open ReciprocityTheory.ChartRestriction.DS

def permIns {p : ℕ} (i : Fin (p + 1)) (τ : Equiv.Perm (Fin p)) : Equiv.Perm (Fin (p + 1)) :=
  i.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, τ)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem permIns_zero {p : ℕ} (i : Fin (p + 1)) (τ : Equiv.Perm (Fin p)) : permIns i τ 0 = i := by
  simp [permIns, Equiv.Perm.mul_apply]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem permIns_succ {p : ℕ} (i : Fin (p + 1)) (τ : Equiv.Perm (Fin p)) (j : Fin p) :
    permIns i τ j.succ = i.succAbove (τ j) := by
  simp [permIns, Equiv.Perm.mul_apply]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem sign_permIns {p : ℕ} (i : Fin (p + 1)) (τ : Equiv.Perm (Fin p)) :
    ((Equiv.Perm.sign (permIns i τ) : ℤˣ) : ℤ) = (-1) ^ (i : ℕ) * ((Equiv.Perm.sign τ : ℤˣ) : ℤ) := by
  simp [permIns, Equiv.Perm.sign_mul]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Substitute using the available equality. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Simplify using the standard rewrite rules. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem permIns_bijective {p : ℕ} :
    Function.Bijective (fun q : Fin (p + 1) × Equiv.Perm (Fin p) => permIns q.1 q.2) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
  · rintro ⟨i, τ⟩ ⟨i', τ'⟩ h
    have h' : permIns i τ = permIns i' τ' := h
    have hi : i = i' := by
      have h0 := congrArg (fun σ : Equiv.Perm (Fin (p + 1)) => σ 0) h'
      simpa only [permIns_zero] using h0
    subst hi
    have hτ : τ = τ' := by
      refine Equiv.ext fun j => ?_
      have hj := congrArg (fun σ : Equiv.Perm (Fin (p + 1)) => σ j.succ) h'
      simp only [permIns_succ] at hj
      first
      | exact Fin.succAbove_right_injective hj
      | exact Fin.succAbove_right_inj.mp hj
    rw [hτ]
  · simp [Fintype.card_perm, Nat.factorial_succ]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sum_perm_succ {M : Type*} [AddCommMonoid M] {p : ℕ} (F : Equiv.Perm (Fin (p + 1)) → M) :
    ∑ σ, F σ = ∑ i, ∑ τ, F (permIns i τ) := by
  rw [← Equiv.sum_comp (Equiv.ofBijective _ (permIns_bijective (p := p))) F, Fintype.sum_prod_type]
  all_goals rfl

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem basic_zsmul_sign {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] (i : ℕ) (s : ℤ) (a b : 𝒰) :
    ((-1 : ℤ) ^ i * s) • (a * b) = (-1 : ℂ) ^ i • (a * (s • b)) := by
  have h1 : ((-1 : ℂ) ^ i) = (((-1 : ℤ) ^ i : ℤ) : ℂ) := by simp
  rw [h1, Int.cast_smul_eq_zsmul ℂ, mul_smul_comm, mul_smul]
  all_goals rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem basic_sign_mul_sign {p : ℕ} (τ σ : Equiv.Perm (Fin p)) :
    ((Equiv.Perm.sign τ : ℤˣ) : ℤ) * ((Equiv.Perm.sign (τ * σ) : ℤˣ) : ℤ) = ((Equiv.Perm.sign σ : ℤˣ) : ℤ) := by
  rw [← Units.val_mul, Equiv.Perm.sign_mul, ← mul_assoc, Int.units_mul_self, one_mul]

/- English proof (translation)
Establish an intermediate fact. Treat this case separately. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem basic_eq_zero_of_eq_neg {𝒰 : Type*} [AddCommGroup 𝒰] [Module ℂ 𝒰] (c : 𝒰)
    (h : c = ((-1 : ℤˣ) : ℤ) • c) : c = 0 := by
  have h' : c = -c := by
    first
    | (rw [Units.val_neg, Units.val_one, neg_one_smul] at h; exact h)
    | (simp only [Units.val_neg, Units.val_one, neg_smul, one_smul] at h; exact h)
  have h2 : (2 : ℂ) • c = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h']
    simp
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/- English proof (translation)
Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem basic_swap_of_not_inj {α : Type*} {p : ℕ} (R : Fin p → α) (h : ¬ Function.Injective R) :
    ∃ i j : Fin p, i ≠ j ∧ R ∘ Equiv.swap i j = R := by
  have hex : ∃ i j, R i = R j ∧ i ≠ j := by
    by_contra hc
    push_neg at hc
    exact h fun a b hab => hc a b hab
  obtain ⟨i, j, hij, hne⟩ := hex
  refine ⟨i, j, hne, funext fun k => ?_⟩
  simp only [Function.comp_apply, Equiv.swap_apply_def]
  split_ifs with h1 h2
  · rw [h1, hij]
  · rw [h2, hij]
  · rfl

section Ring

variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules.
-/
theorem cminor_succ_col {p : ℕ} (R C : Fin (p + 1) → Fin n) (x : ℂ) :
    cminor E R C x = ∑ i : Fin (p + 1), ((-1 : ℂ) ^ (i : ℕ)) •
      (capEntry E x (R i) (C 0) * cminor E (R ∘ i.succAbove) (C ∘ Fin.succ) (x - 1)) := by
  have e : ∀ t : ℂ, x - (t + 1) = x - 1 - t := fun t => by ring
  unfold cminor
  refine (sum_perm_succ _).trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [sign_permIns, List.ofFn_succ, List.prod_cons, permIns_zero, permIns_succ, Fin.val_zero,
    Fin.val_succ, Nat.cast_zero, sub_zero, Nat.cast_add, Nat.cast_one, e, Function.comp_apply,
    basic_zsmul_sign]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem cminor_perm_rows {p : ℕ} (R C : Fin p → Fin n) (τ : Equiv.Perm (Fin p)) (x : ℂ) :
    cminor E (R ∘ τ) C x = ((Equiv.Perm.sign τ : ℤˣ) : ℤ) • cminor E R C x := by
  unfold cminor
  rw [Finset.smul_sum]
  refine Eq.trans ?_ (Equiv.sum_comp (Equiv.mulLeft τ) _)
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Equiv.coe_mulLeft, Equiv.Perm.mul_apply, smul_smul, basic_sign_mul_sign, Function.comp_apply]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem cminor_rows_not_inj {p : ℕ} (R C : Fin p → Fin n) (x : ℂ) (h : ¬ Function.Injective R) :
    cminor E R C x = 0 := by
  obtain ⟨i, j, hij, hR⟩ := basic_swap_of_not_inj R h
  have h1 := cminor_perm_rows E R C (Equiv.swap i j) x
  rw [hR, Equiv.Perm.sign_swap hij] at h1
  exact basic_eq_zero_of_eq_neg _ h1

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem rminor_succ_row {p : ℕ} (R C : Fin (p + 1) → Fin n) (x : ℂ) :
    rminor E R C x = ∑ j : Fin (p + 1), ((-1 : ℂ) ^ (j : ℕ)) •
      (capEntry E (x - (p : ℂ)) (R 0) (C j) * rminor E (R ∘ Fin.succ) (C ∘ j.succAbove) x) := by
  have e1 : x - ((p : ℂ) + 1) + 1 = x - p := by ring
  have e2 : ∀ t : ℂ, x - (p : ℂ) + (t + 1) = x - p + 1 + t := fun t => by ring
  unfold rminor
  refine (sum_perm_succ _).trans (Finset.sum_congr rfl fun j _ => ?_)
  rw [Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [sign_permIns, List.ofFn_succ, List.prod_cons, permIns_zero, permIns_succ, Fin.val_zero,
    Fin.val_succ, Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one, e1, e2, Function.comp_apply,
    basic_zsmul_sign]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem glRelR_op (hE : GlRelR E) : GlRelR (fun a b => MulOpposite.op (E b a)) := by
  intro a b c d
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_sub, MulOpposite.unop_mul, MulOpposite.unop_op, hE d c b a]
  split_ifs <;> simp_all

end Ring

section Module

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem basic_prod_intertwine {M R' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup R'] [Module ℂ R']
    (l : M →ₗ[ℂ] R') : ∀ {m : ℕ} (f : Fin m → Module.End ℂ M) (g : Fin m → Module.End ℂ R'),
    (∀ j, l ∘ₗ f j = g j ∘ₗ l) → l ∘ₗ (List.ofFn f).prod = (List.ofFn g).prod ∘ₗ l
  | 0, f, g, _ => by simp [Module.End.one_eq_id]
  | m + 1, f, g, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_eq_comp,
      Module.End.mul_eq_comp, ← LinearMap.comp_assoc, h 0, LinearMap.comp_assoc,
      basic_prod_intertwine l _ _ (fun j => h j.succ), ← LinearMap.comp_assoc]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.

By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Simplify using the standard rewrite rules. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem cminor_intertwine {M R' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup R'] [Module ℂ R']
    {n k : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (D : Fin k → Fin k → Module.End ℂ R')
    (ι : Fin k → Fin n) (hι : Function.Injective ι) (l : M →ₗ[ℂ] R')
    (hl : ∀ i j, l ∘ₗ E (ι i) (ι j) = D i j ∘ₗ l) {p : ℕ} (Rw Cw : Fin p → Fin k) (x : ℂ) :
    l ∘ₗ cminor E (ι ∘ Rw) (ι ∘ Cw) x = cminor D Rw Cw x ∘ₗ l := by
  have hc : ∀ (y : ℂ) (a b : Fin k), l ∘ₗ capEntry E y (ι a) (ι b) = capEntry D y a b ∘ₗ l := by
    intro y a b
    have hv : ∀ v, l (E (ι a) (ι b) v) = D a b (l v) := fun v => LinearMap.congr_fun (hl a b) v
    unfold capEntry
    simp only [hι.eq_iff]
    ext v
    split_ifs <;> simp [hv]
  have key : ∀ σ : Equiv.Perm (Fin p),
      l ∘ₗ (List.ofFn fun j : Fin p => capEntry E (x - ((j : ℕ) : ℂ)) ((ι ∘ Rw) (σ j)) ((ι ∘ Cw) j)).prod =
        (List.ofFn fun j : Fin p => capEntry D (x - ((j : ℕ) : ℂ)) (Rw (σ j)) (Cw j)).prod ∘ₗ l := by
    intro σ
    apply basic_prod_intertwine
    intro j
    exact hc _ _ _
  unfold cminor
  ext v
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h1 := LinearMap.congr_fun (key σ) v
  simp only [LinearMap.comp_apply] at h1
  first
  | (rw [LinearMap.smul_apply, LinearMap.smul_apply, map_zsmul, h1])
  | simp [h1, map_zsmul]

end Module

end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
