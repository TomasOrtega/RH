import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.BasicCycleRangeLastCastSucc

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

open ReciprocityTheory.ChartRestriction.DS

variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)

/- English proof (translation)
Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem capEntry_eq_add_smul (x : ℂ) (a b : Fin n) :
    capEntry E x a b = E a b + (if a = b then x else 0) • (1 : 𝒰) := by
  unfold capEntry
  split_ifs <;> simp [Algebra.algebraMap_eq_smul_one]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem add_smul_one_mul_sub_eq_neg_swap_of_commutator (A B C D : 𝒰) (a b c d x : ℂ)
    (h1 : A * B - B * A = c • D - d • C) (h2 : D * C - C * D = b • A - a • B) :
    (A + (a * x) • (1 : 𝒰)) * (B + (b * (x - 1)) • (1 : 𝒰)) -
        (C + (c * x) • (1 : 𝒰)) * (D + (d * (x - 1)) • (1 : 𝒰)) =
      -((D + (d * x) • (1 : 𝒰)) * (C + (c * (x - 1)) • (1 : 𝒰)) -
        (B + (b * x) • (1 : 𝒰)) * (A + (a * (x - 1)) • (1 : 𝒰))) := by
  have hBA : B * A = A * B - (c • D - d • C) := by rw [← h1]; abel
  have hCD : C * D = D * C - (b • A - a • B) := by rw [← h2]; abel
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  rw [hBA, hCD]
  module

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem capEntry_two (hE : GlRelR E) (i k j l : Fin n) (x : ℂ) :
    capEntry E x i j * capEntry E (x - 1) k l - capEntry E x k j * capEntry E (x - 1) i l =
      -(capEntry E x i l * capEntry E (x - 1) k j - capEntry E x k l * capEntry E (x - 1) i j) := by
  have hs : ∀ (a b : Fin n) (y : ℂ),
      capEntry E y a b = E a b + ((if a = b then (1 : ℂ) else 0) * y) • (1 : 𝒰) := by
    intro a b y
    rw [capEntry_eq_add_smul]
    split_ifs <;> simp
  have hd : ∀ (a b : Fin n) (u : 𝒰), (if b = a then u else 0) = (if a = b then (1 : ℂ) else 0) • u := by
    intro a b u
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  have h1 := hE i j k l
  have h2 := hE i l k j
  rw [hd, hd] at h1 h2
  simp only [hs]
  exact add_smul_one_mul_sub_eq_neg_swap_of_commutator (E i j) (E k l) (E k j) (E i l) _ _ _ _ x h1 h2

omit [Algebra ℂ 𝒰] in

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Split into cases according to the possible forms of the given data. Treat this case separately.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Treat this case separately.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem prod_ofFn_split_adj {p : ℕ} (f : Fin (p + 1) → 𝒰) (j : Fin p) : ∃ P Q : 𝒰, ∀ g : Fin (p + 1) → 𝒰,
    (∀ m, m ≠ j.castSucc → m ≠ j.succ → g m = f m) →
      (List.ofFn g).prod = P * g j.castSucc * g j.succ * Q := by
  induction p with
  | zero => exact j.elim0
  | succ q ih =>
    cases j using Fin.cases with
    | zero =>
      refine ⟨1, (List.ofFn fun m : Fin q => f m.succ.succ).prod, fun g hg => ?_⟩
      have hr : (List.ofFn fun m : Fin q => g m.succ.succ) = List.ofFn fun m : Fin q => f m.succ.succ := by
        congr 1
        funext m
        apply hg
        · intro h; have := congrArg Fin.val h; simp at this
        · intro h; have := congrArg Fin.val h; simp at this
      simp only [List.ofFn_succ, List.prod_cons]
      rw [hr]
      simp [mul_assoc]
    | succ j' =>
      obtain ⟨P', Q', hPQ⟩ := ih (fun m => f m.succ) j'
      refine ⟨f 0 * P', Q', fun g hg => ?_⟩
      have h0 : g 0 = f 0 := hg 0
        (by intro h; have := congrArg Fin.val h; simp at this)
        (by intro h; have := congrArg Fin.val h; simp at this)
      have hc : j'.castSucc.succ = j'.succ.castSucc := Fin.ext (by simp)
      have h' := hPQ (fun m => g m.succ) (fun m hm1 hm2 =>
        hg m.succ (fun h => hm1 (Fin.succ_injective _ (h.trans hc.symm)))
          (fun h => hm2 (Fin.succ_injective _ h)))
      try dsimp only at h'
      rw [List.ofFn_succ, List.prod_cons, h', h0, hc]
      simp only [mul_assoc]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

A detailed English derivation is pending.
-/
private theorem sum_eq_zero_of_add_equiv_apply_eq_zero {M α : Type*} [AddCommGroup M] [Module ℂ M] [Fintype α]
    (e : α ≃ α) (G : α → M) (h : ∀ a, G a + G (e a) = 0) : ∑ a, G a = 0 := by
  have h2 : ∑ a, G a + ∑ a, G (e a) = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero (fun a _ => h a)
  rw [Equiv.sum_comp e G, ← two_smul ℂ] at h2
  have h4 : ((1 / 2 : ℂ) * 2) • ∑ a, G a = 0 := by rw [← smul_smul, h2, smul_zero]
  rwa [show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul] at h4

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws. A detailed English derivation is pending.
-/
theorem cminor_swap_adj (hE : GlRelR E) {p : ℕ} (R C : Fin (p + 1) → Fin n) (j : Fin p) (x : ℂ) :
    cminor E R (C ∘ Equiv.swap j.castSucc j.succ) x = -cminor E R C x := by
  obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm (Fin (p + 1)), τ = Equiv.swap j.castSucc j.succ := ⟨_, rfl⟩
  rw [← hτ]
  have hab : j.castSucc ≠ j.succ := (Fin.castSucc_lt_succ : j.castSucc < j.succ).ne
  have hτa : τ j.castSucc = j.succ := by rw [hτ]; exact Equiv.swap_apply_left _ _
  have hτb : τ j.succ = j.castSucc := by rw [hτ]; exact Equiv.swap_apply_right _ _
  have hτm : ∀ m, m ≠ j.castSucc → m ≠ j.succ → τ m = m := fun m h1 h2 => by
    rw [hτ]; exact Equiv.swap_apply_of_ne_of_ne h1 h2
  have hsg : ∀ σ : Equiv.Perm (Fin (p + 1)),
      ((Equiv.Perm.sign (σ * τ) : ℤˣ) : ℤ) = -((Equiv.Perm.sign σ : ℤˣ) : ℤ) := by
    intro σ
    rw [Equiv.Perm.sign_mul, hτ, Equiv.Perm.sign_swap hab]
    simp
  have hxb : x - ((j.succ : ℕ) : ℂ) = x - ((j.castSucc : ℕ) : ℂ) - 1 := by
    simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]; ring
  rw [eq_neg_iff_add_eq_zero]
  unfold cminor
  rw [← Finset.sum_add_distrib]
  apply sum_eq_zero_of_add_equiv_apply_eq_zero (Equiv.mulRight τ)
  intro σ
  simp only [Equiv.coe_mulRight, Equiv.Perm.mul_apply, Function.comp_apply, hsg, neg_smul]
  obtain ⟨P, Q, hPQ⟩ := prod_ofFn_split_adj
    (fun m => capEntry E (x - ((m : ℕ) : ℂ)) (R (σ m)) (C m)) j
  have h1 := hPQ (fun m => capEntry E (x - ((m : ℕ) : ℂ)) (R (σ m)) (C m)) (fun m _ _ => rfl)
  have h2 := hPQ (fun m => capEntry E (x - ((m : ℕ) : ℂ)) (R (σ m)) (C (τ m)))
    (fun m h h' => by simp only [hτm m h h'])
  have h3 := hPQ (fun m => capEntry E (x - ((m : ℕ) : ℂ)) (R (σ (τ m))) (C m))
    (fun m h h' => by simp only [hτm m h h'])
  have h4 := hPQ (fun m => capEntry E (x - ((m : ℕ) : ℂ)) (R (σ (τ m))) (C (τ m)))
    (fun m h h' => by simp only [hτm m h h'])
  simp only [hτa, hτb, hxb] at h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  have hx := eq_neg_iff_add_eq_zero.mp (capEntry_two E hE (R (σ j.castSucc)) (R (σ j.succ))
    (C j.castSucc) (C j.succ) (x - ((j.castSucc : ℕ) : ℂ)))
  have hz := congrArg (fun t => ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • (P * t * Q)) hx
  simp only [mul_zero, zero_mul, smul_zero] at hz
  rw [← hz]
  simp only [mul_add, add_mul, mul_sub, sub_mul, smul_add, smul_sub, mul_assoc]
  abel

/- English proof (translation)
Split into cases according to the possible forms of the given data. Treat this case separately. Establish an intermediate fact. Substitute using the available equality. Simplify using the standard rewrite rules.

Treat this case separately. Introduce a local definition for the expression. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem cminor_perm_cols (hE : GlRelR E) {p : ℕ} (R C : Fin p → Fin n) (τ : Equiv.Perm (Fin p))
    (x : ℂ) : cminor E R (C ∘ τ) x = ((Equiv.Perm.sign τ : ℤˣ) : ℤ) • cminor E R C x := by
  cases p with
  | zero =>
    have : τ = 1 := Subsingleton.elim _ _
    subst this
    simp
  | succ q =>
    let S : Submonoid (Equiv.Perm (Fin (q + 1))) :=
      { carrier := {σ | ∀ C' : Fin (q + 1) → Fin n,
          cminor E R (C' ∘ σ) x = ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • cminor E R C' x}
        mul_mem' := by
          intro a b ha hb
          have ha' : ∀ C' : Fin (q + 1) → Fin n,
              cminor E R (C' ∘ a) x = ((Equiv.Perm.sign a : ℤˣ) : ℤ) • cminor E R C' x := ha
          have hb' : ∀ C' : Fin (q + 1) → Fin n,
              cminor E R (C' ∘ b) x = ((Equiv.Perm.sign b : ℤˣ) : ℤ) • cminor E R C' x := hb
          show ∀ C' : Fin (q + 1) → Fin n,
            cminor E R (C' ∘ ⇑(a * b)) x = ((Equiv.Perm.sign (a * b) : ℤˣ) : ℤ) • cminor E R C' x
          intro C'
          rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hb', ha', smul_smul, Equiv.Perm.sign_mul,
            Units.val_mul, mul_comm]
        one_mem' := by
          show ∀ C' : Fin (q + 1) → Fin n,
            cminor E R (C' ∘ (1 : Equiv.Perm (Fin (q + 1)))) x =
              ((Equiv.Perm.sign (1 : Equiv.Perm (Fin (q + 1))) : ℤˣ) : ℤ) • cminor E R C' x
          intro C'
          simp }
    have hle : Submonoid.closure (Set.range fun i : Fin q => Equiv.swap i.castSucc i.succ) ≤ S := by
      rw [Submonoid.closure_le]
      rintro _ ⟨i, rfl⟩
      show ∀ C' : Fin (q + 1) → Fin n,
        cminor E R (C' ∘ Equiv.swap i.castSucc i.succ) x =
          ((Equiv.Perm.sign (Equiv.swap i.castSucc i.succ) : ℤˣ) : ℤ) • cminor E R C' x
      intro C'
      rw [cminor_swap_adj E hE, Equiv.Perm.sign_swap (Fin.castSucc_lt_succ : i.castSucc < i.succ).ne, Units.val_neg,
        Units.val_one, neg_smul, one_smul]
    have hτ : τ ∈ S := hle (by rw [Equiv.Perm.mclosure_swap_castSucc_succ]; exact Submonoid.mem_top τ)
    have hτ' : ∀ C' : Fin (q + 1) → Fin n,
        cminor E R (C' ∘ τ) x = ((Equiv.Perm.sign τ : ℤˣ) : ℤ) • cminor E R C' x := hτ
    exact hτ' C

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem cminor_cols_not_inj (hE : GlRelR E) {p : ℕ} (R C : Fin p → Fin n) (x : ℂ)
    (h : ¬ Function.Injective C) : cminor E R C x = 0 := by
  obtain ⟨i, k, hik, hC⟩ := basic_swap_of_not_inj C h
  apply basic_eq_zero_of_eq_neg
  have := cminor_perm_cols E hE R C (Equiv.swap i k) x
  rw [hC, Equiv.Perm.sign_swap hik] at this
  exact this

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem cminor_col_at (hE : GlRelR E) {p : ℕ} (R C : Fin (p + 1) → Fin n) (j : Fin (p + 1)) (x : ℂ) :
    cminor E R C x = ∑ i : Fin (p + 1), ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
      (capEntry E x (R i) (C j) * cminor E (R ∘ i.succAbove) (C ∘ j.succAbove) (x - 1)) := by
  have hπ := cminor_perm_cols E hE R C (permIns j 1) x
  rw [sign_permIns, Equiv.Perm.sign_one, Units.val_one, mul_one] at hπ
  have h0 := cminor_succ_col E R (C ∘ permIns j 1) x
  have hC0 : (C ∘ permIns j 1) 0 = C j := by rw [Function.comp_apply, permIns_zero]
  have hCs : (C ∘ permIns j 1) ∘ Fin.succ = C ∘ j.succAbove := by
    funext m
    simp only [Function.comp_apply, permIns_succ, Equiv.Perm.one_apply]
  rw [hC0, hCs, hπ] at h0
  have hsq : cminor E R C x =
      ((-1 : ℤ) ^ (j : ℕ)) • (((-1 : ℤ) ^ (j : ℕ)) • cminor E R C x) := by
    rw [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
  rw [hsq, h0, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Int.cast_smul_eq_zsmul ℂ, smul_smul]
  congr 1
  push_cast
  ring

end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
