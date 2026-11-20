import Development.WeilBound.CoreStatements.FlagImmersions.AltCMul

noncomputable section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics.M5

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def lower (a : Ψ → Fin N → ℕ) (τ : Ψ) (l : Fin N) (m : ℕ) : Ψ → Fin N → ℕ :=
  fun τ' c => if τ' = τ ∧ c = l then a τ' c - m else a τ' c

/- English proof (translation)
Establish `h1 : ∀ σ : Ψ → Equiv.Perm (Fin N), (pk τ m * G).coeff (expo a σ) = ∑ l, if m ≤ a τ l then G.coeff (expo (lower a τ l m) σ) else 0`. Introduce `σ`. Rewrite using `[← Equiv.sum_comp (σ τ), pk, Finset.sum_mul, coeff_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[X_pow_eq_monomial, coeff_monomial_mul', one_mul]`.

Establish `e1 : (Finsupp.single (τ, i) m ≤ expo a σ) ↔ m ≤ a τ (σ τ i)`. Rewrite using `[Finsupp.single_le_iff]`. Simplify using `[expo]`. Establish `e2 : expo a σ - Finsupp.single (τ, i) m = expo (lower a τ (σ τ i) m) σ`. Use extensionality with `⟨t, b⟩`.

Simplify using `only [expo, lower, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.equivFunOnFinite_symm_apply_apply, Finsupp.single_apply, Prod.mk.injEq]`. Distinguish the cases in `ht : t = τ`. Substitute `ht` using the available equality. Distinguish the cases in `hb : b = i`. Substitute `hb` using the available equality.

Simplify using the standard rewrite rules. Establish `: ¬ i = b` using `fun h => hb h.symm`. Simplify using `[hb, this]`. Establish `: ¬ τ = t` using `fun h => ht h.symm`. Simplify using `[ht, this]`.

Rewrite using `[e2]`. Distinguish the cases in `h : m ≤ a τ (σ τ i)`. Rewrite using `[if_pos (e1.mpr h), if_pos h]`. Rewrite using `[if_neg (fun h' => h (e1.mp h')), if_neg h]`. Simplify using `only [alt, h1, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem alt_pk (a : Ψ → Fin N → ℕ) (τ : Ψ) (m : ℕ) (G : RP Ψ N) :
    alt a (pk τ m * G) = ∑ l, if m ≤ a τ l then alt (lower a τ l m) G else 0 := by
  have h1 : ∀ σ : Ψ → Equiv.Perm (Fin N), (pk τ m * G).coeff (expo a σ) =
      ∑ l, if m ≤ a τ l then G.coeff (expo (lower a τ l m) σ) else 0 := by
    intro σ
    rw [← Equiv.sum_comp (σ τ), pk, Finset.sum_mul, coeff_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [X_pow_eq_monomial, coeff_monomial_mul', one_mul]
    have e1 : (Finsupp.single (τ, i) m ≤ expo a σ) ↔ m ≤ a τ (σ τ i) := by
      rw [Finsupp.single_le_iff]; simp [expo]
    have e2 : expo a σ - Finsupp.single (τ, i) m = expo (lower a τ (σ τ i) m) σ := by
      ext ⟨t, b⟩
      simp only [expo, lower, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.equivFunOnFinite_symm_apply_apply,
        Finsupp.single_apply, Prod.mk.injEq]
      by_cases ht : t = τ
      · subst ht
        by_cases hb : b = i
        · subst hb; simp
        · have : ¬ i = b := fun h => hb h.symm
          simp [hb, this]
      · have : ¬ τ = t := fun h => ht h.symm
        simp [ht, this]
    rw [e2]
    by_cases h : m ≤ a τ (σ τ i)
    · rw [if_pos (e1.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (e1.mp h')), if_neg h]
  simp only [alt, h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp

/- English proof (translation)
Unfold `alt`. Rewrite using `[← Equiv.sum_comp (Equiv.mulLeft π), Finset.mul_sum]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← Finset.prod_mul_distrib]`. Use `congr 1`.

Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem alt_perm (a : Ψ → Fin N → ℕ) (π : Ψ → Equiv.Perm (Fin N)) (G : RP Ψ N) :
    alt a G = (∏ τ, ((Equiv.Perm.sign (π τ) : ℤ) : ℝ)) * alt (fun τ c => a τ (π τ c)) G := by
  unfold alt
  rw [← Equiv.sum_comp (Equiv.mulLeft π), Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  · refine Finset.prod_congr rfl fun τ _ => ?_
    simp

/- English proof (translation)
Rewrite using `[alt_perm a (Function.update 1 τ (Equiv.swap p q)) G]`. Establish `e : (fun t c => a t (Function.update (1 : Ψ → Equiv.Perm (Fin N)) τ (Equiv.swap p q) t c)) = b`. Use function extensionality and compare the values at `t c`. Distinguish the cases in `ht : t = τ`. Substitute `ht` using the available equality.

Simplify using `[h1]`. Simplify using `[ht, h2 t ht]`. Rewrite using `[e, Finset.prod_eq_single τ]`. Simplify using `[Equiv.Perm.sign_swap hpq]`. Introduce `t _ ht`.

Simplify using `[ht]`. Simplify using the standard rewrite rules.
-/
theorem alt_swap (a b : Ψ → Fin N → ℕ) (τ : Ψ) (p q : Fin N) (hpq : p ≠ q) (G : RP Ψ N)
    (h1 : ∀ c, b τ c = a τ (Equiv.swap p q c)) (h2 : ∀ t, t ≠ τ → b t = a t) :
    alt a G = - alt b G := by
  rw [alt_perm a (Function.update 1 τ (Equiv.swap p q)) G]
  have e : (fun t c => a t (Function.update (1 : Ψ → Equiv.Perm (Fin N)) τ (Equiv.swap p q) t c)) = b := by
    funext t c
    by_cases ht : t = τ
    · subst ht; simp [h1]
    · simp [ht, h2 t ht]
  rw [e, Finset.prod_eq_single τ]
  · simp [Equiv.Perm.sign_swap hpq]
  · intro t _ ht; simp [ht]
  · simp

/- English proof (translation)
Use `alt_swap a a τ p q hpq G (fun c => by` as an intermediate fact. Rewrite using `[Equiv.swap_apply_def]`. Use `split_ifs with h1 h2`. Rewrite using `[h1, h]`. Rewrite using `[h2, h]`.

Use the proof step `rfl) (fun _ _ => rfl)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem alt_eq_zero (a : Ψ → Fin N → ℕ) (τ : Ψ) (p q : Fin N) (hpq : p ≠ q) (h : a τ p = a τ q)
    (G : RP Ψ N) : alt a G = 0 := by
  have := alt_swap a a τ p q hpq G (fun c => by
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1, h]
    · rw [h2, h]
    · rfl) (fun _ _ => rfl)
  linarith

/- English proof (translation)
Rewrite using `[alt_pk]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Rewrite `h` using `[ha]`. Establish `hl` using `l.isLt`.

Establish `hne : l ≠ ⟨l + m, by omega⟩` using `fun e => by`. Use `congrArg Fin.val e` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Use `alt_eq_zero _ τ l ⟨l + m, by omega⟩ hne ?_ G` and prove the remaining obligations.

Simplify using `only [lower, true_and, if_true, if_neg hne.symm, ha]`. Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression.
-/
theorem alt_pk_zero (a : Ψ → Fin N → ℕ) (τ : Ψ) (ha : ∀ c : Fin N, a τ c = N - 1 - (c : ℕ)) (m : ℕ) (hm : 1 ≤ m)
    (G : RP Ψ N) : alt a (pk τ m * G) = 0 := by
  rw [alt_pk]
  refine Finset.sum_eq_zero fun l _ => ?_
  split_ifs with h
  · rw [ha] at h
    have hl := l.isLt
    have hne : l ≠ ⟨l + m, by omega⟩ := fun e => by
      have := congrArg Fin.val e; simp at this; omega
    refine alt_eq_zero _ τ l ⟨l + m, by omega⟩ hne ?_ G
    simp only [lower, true_and, if_true, if_neg hne.symm, ha]
    omega
  · rfl

/- English proof (translation)
The claim follows from `alt_pk_zero rho τ (fun _ => rfl) m hm G`.
-/
theorem alt_rho_pk (τ : Ψ) (m : ℕ) (hm : 1 ≤ m) (G : RP Ψ N) : alt rho (pk τ m * G) = 0 :=
  alt_pk_zero rho τ (fun _ => rfl) m hm G

/- English proof (translation)
Establish `hl` using `l.isLt`. Use `split_ifs with h1 h2`. Use `set l' : Fin N := ⟨l + m, h1⟩ with hl'`. Establish `hv : (l' : ℕ) = l + m` using `rfl`. Establish `hne : l ≠ l'` using `fun e => by`.

Use `congrArg Fin.val e` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[Finset.sum_eq_add l l' hne]`. Rewrite using `[if_pos (by simp [bump]; omega), if_pos (by simp [bump]; omega)]`. Rewrite using `[alt_swap (lower (bump τ l k) τ l m) (lower (bump τ l' k) τ l m) τ l l' hne G]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `c`. Rewrite using `[Equiv.swap_apply_def]`. Use `split_ifs with c1 c2`. Substitute `c1` using the available equality.

Simplify using `[lower, bump, hne, hne.symm]`. Use linear arithmetic over natural numbers and integers. Substitute `c2` using the available equality. Simplify using `[lower, bump, hne, hne.symm]`. Use linear arithmetic over natural numbers and integers.

Simplify using `[lower, bump, c1, c2]`. Introduce `t ht`. Use function extensionality and compare the values at `c`. Simplify using `[lower, bump, ht]`. Introduce `c _ hc split_ifs with h`.

Use `alt_eq_zero _ τ l l' hne ?_ G` and prove the remaining obligations. Simplify using `[lower, bump, hne.symm, hc.1.symm, hc.2.symm]`. Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Substitute `h2` using the available equality. Rewrite using `[Finset.sum_eq_single l]`. Rewrite using `[if_pos (by simp [bump])]`. Use `congr 1`.

Use function extensionality and compare the values at `t c`. Simplify using `only [lower, bump, rho]`. Apply the tactic sequence `split_ifs <;> omega`. Introduce `c _ hc`. Rewrite using `[if_neg]`.

Simplify using `[bump, hc.symm]`. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. Use `Finset.sum_eq_zero fun c _ => ?_ split_ifs with h` and prove the remaining obligations. Distinguish the cases in `hc : l = c`.

Substitute `hc` using the available equality. Simplify using `only [bump, true_and, if_true] at h`. Use `set q : Fin N := ⟨N - 1 - (N - 1 - l + k - m), by omega⟩ with hq`. Establish `hv : (q : ℕ) = N - 1 - (N - 1 - l + k - m)` using `rfl`. Establish `hne : l ≠ q` using `fun e => by`.

Use `congrArg Fin.val e` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `alt_eq_zero _ τ l q hne ?_ G` and prove the remaining obligations. Simplify using `only [lower, bump, true_and, if_true, if_neg hne.symm]`. Use linear arithmetic over natural numbers and integers.

It suffices to derive a contradiction. Simplify using `[bump, hc] at h`. Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression.
-/
theorem col_sum (τ : Ψ) (k m : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) (hm : 1 ≤ m) (G : RP Ψ N) (l : Fin N) :
    (∑ c, if m ≤ bump τ c k τ l then alt (lower (bump τ c k) τ l m) G else 0) =
      if (l : ℕ) + m < N then 0 else if m = k then alt rho G else 0 := by
  have hl := l.isLt
  split_ifs with h1 h2
  · set l' : Fin N := ⟨l + m, h1⟩ with hl'
    have hv : (l' : ℕ) = l + m := rfl
    have hne : l ≠ l' := fun e => by
      have := congrArg Fin.val e; omega
    rw [Finset.sum_eq_add l l' hne]
    · rw [if_pos (by simp [bump]; omega), if_pos (by simp [bump]; omega)]
      rw [alt_swap (lower (bump τ l k) τ l m) (lower (bump τ l' k) τ l m) τ l l' hne G]
      · ring
      · intro c
        rw [Equiv.swap_apply_def]
        split_ifs with c1 c2
        · subst c1
          simp [lower, bump, hne, hne.symm]; omega
        · subst c2
          simp [lower, bump, hne, hne.symm]; omega
        · simp [lower, bump, c1, c2]
      · intro t ht
        funext c
        simp [lower, bump, ht]
    · intro c _ hc
      split_ifs with h
      · refine alt_eq_zero _ τ l l' hne ?_ G
        simp [lower, bump, hne.symm, hc.1.symm, hc.2.symm]; omega
      · rfl
    · simp
    · simp
  · subst h2
    rw [Finset.sum_eq_single l]
    · rw [if_pos (by simp [bump])]
      congr 1
      funext t c
      simp only [lower, bump, rho]
      split_ifs <;> omega
    · intro c _ hc
      rw [if_neg]
      simp [bump, hc.symm]; omega
    · simp
  · refine Finset.sum_eq_zero fun c _ => ?_
    split_ifs with h
    · by_cases hc : l = c
      · subst hc
        simp only [bump, true_and, if_true] at h
        set q : Fin N := ⟨N - 1 - (N - 1 - l + k - m), by omega⟩ with hq
        have hv : (q : ℕ) = N - 1 - (N - 1 - l + k - m) := rfl
        have hne : l ≠ q := fun e => by
          have := congrArg Fin.val e; omega
        refine alt_eq_zero _ τ l q hne ?_ G
        simp only [lower, bump, true_and, if_true, if_neg hne.symm]
        omega
      · exfalso
        simp [bump, hc] at h; omega
    · rfl

/- English proof (translation)
Distinguish the cases in `ht : τ' = τ`. Substitute `ht` using the available equality. Simplify using `only [lam, alt_pk, true_and]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [col_sum τ' k m hk hkN hm G]`.

Distinguish the cases in `h : m = k`. Substitute `h` using the available equality. Simplify using `only [if_true]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun l => if l + m < N then 0 else alt rho G) N, Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]`. Establish `: (Finset.range N).filter (fun l => ¬ l + m < N) = Finset.Ico (N - m) N`.

Use extensionality with `x`. Simplify using `only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[this, Nat.card_Ico]`. Use `congr 2`.

Use linear arithmetic over natural numbers and integers. Simplify using `[h]`. Rewrite using `[if_neg (fun h => ht h.1)]`. Use `Finset.sum_eq_zero fun c _ => alt_pk_zero _ τ' (fun c' => ?_) m hm G` and prove the remaining obligations. Simplify using `[bump, ht]`.
-/
theorem lam_pk (τ τ' : Ψ) (k m : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) (hm : 1 ≤ m) (hmN : m ≤ N) (G : RP Ψ N) :
    lam τ k (pk τ' m * G) = if τ' = τ ∧ m = k then (k : ℝ) * alt rho G else 0 := by
  by_cases ht : τ' = τ
  · subst ht
    simp only [lam, alt_pk, true_and]
    rw [Finset.sum_comm]
    simp only [col_sum τ' k m hk hkN hm G]
    by_cases h : m = k
    · subst h
      simp only [if_true]
      rw [Fin.sum_univ_eq_sum_range (fun l => if l + m < N then 0 else alt rho G) N, Finset.sum_ite,
        Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
      have : (Finset.range N).filter (fun l => ¬ l + m < N) = Finset.Ico (N - m) N := by
        ext x; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
      rw [this, Nat.card_Ico]
      congr 2; omega
    · simp [h]
  · rw [if_neg (fun h => ht h.1)]
    refine Finset.sum_eq_zero fun c _ => alt_pk_zero _ τ' (fun c' => ?_) m hm G
    simp [bump, ht]

end RootFieldNumerics.M5
