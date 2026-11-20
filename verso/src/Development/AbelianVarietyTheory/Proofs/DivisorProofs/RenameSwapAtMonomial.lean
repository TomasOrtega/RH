import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperFact
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal

open MvPolynomial GlobalTheory.FlagPoly Formalism.DegreeFormula

namespace GlobalTheory.FlagAnti

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intro S _`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `S hS`.

Establish `hne : S.Nonempty` using `Finset.card_pos.1 (by omega)`. Establish `hmem` using `S.max'_mem hne`. Establish `hM : n ≤ S.max' hne`. Establish `hsub : S ⊆ Finset.range (S.max' hne + 1)` using `fun x hx => Finset.mem_range.2 (Nat.lt_succ_of_le (S.le_max' x hx))`. Use `Finset.card_le_card hsub` as an intermediate fact.

Simplify using `only [Finset.card_range] at this`. Use linear arithmetic over natural numbers and integers. Establish `hc : (S.erase (S.max' hne)).card = n`. Rewrite using `[Finset.card_erase_of_mem hmem]`. Use linear arithmetic over natural numbers and integers.

Use `ih _ hc` as an intermediate fact. Rewrite using `[Finset.sum_range_succ, ← Finset.add_sum_erase S _ hmem]`. Use linear arithmetic over natural numbers and integers.
-/
theorem sum_range_le_sum (n : ℕ) : ∀ S : Finset ℕ, S.card = n → ∑ i ∈ Finset.range n, i ≤ ∑ s ∈ S, s := by
  induction n with
  | zero => intro S _; simp
  | succ n ih =>
    intro S hS
    have hne : S.Nonempty := Finset.card_pos.1 (by omega)
    have hmem := S.max'_mem hne
    have hM : n ≤ S.max' hne := by
      have hsub : S ⊆ Finset.range (S.max' hne + 1) := fun x hx =>
        Finset.mem_range.2 (Nat.lt_succ_of_le (S.le_max' x hx))
      have := Finset.card_le_card hsub
      simp only [Finset.card_range] at this
      omega
    have hc : (S.erase (S.max' hne)).card = n := by
      rw [Finset.card_erase_of_mem hmem]; omega
    have := ih _ hc
    rw [Finset.sum_range_succ, ← Finset.add_sum_erase S _ hmem]
    omega

/- English proof (translation)
Establish `h` using `sum_range_le_sum n (Finset.univ.image f) (by rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin])`. Rewrite `h` using `[Finset.sum_image (fun x _ y _ h => hf h), Finset.sum_range_id]`. Conclude with `h`.
-/
theorem le_sum_of_injective {n : ℕ} {f : Fin n → ℕ} (hf : Function.Injective f) : n * (n - 1) / 2 ≤ ∑ i, f i := by
  have h := sum_range_le_sum n (Finset.univ.image f)
    (by rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin])
  rw [Finset.sum_image (fun x _ y _ h => hf h), Finset.sum_range_id] at h
  exact h

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

/- English proof (translation)
Break down `x with ⟨t, i⟩` into its components or cases. Distinguish the cases in `h : t = τ`. Substitute `h` using the available equality. Simplify using `[swapAt]`. Simplify using `[swapAt, h]`.
-/
theorem swapAt_swapAt (τ : ι) (a b : Fin N) (x : ι × Fin N) : swapAt τ a b (swapAt τ a b x) = x := by
  rcases x with ⟨t, i⟩
  by_cases h : t = τ
  · subst h; simp [swapAt]
  · simp [swapAt, h]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Establish `e` using `congrArg (fun w : Equiv.Perm (Fin N) => w x.2) (Equiv.swap_mul_swap_mul_swap hab hac)`. Simplify using `only [Equiv.Perm.mul_apply] at e`. Distinguish the cases in `h : x.1 = τ`. Simplify using `[swapAt, h, e, Equiv.swap_comm c a]`.

Simplify using `[swapAt, h]`.
-/
theorem swapAt_conj (τ : ι) {a b c : Fin N} (hab : a ≠ b) (hac : a ≠ c) :
    swapAt τ b c ∘ swapAt τ a b ∘ swapAt τ b c = swapAt τ a c := by
  funext x
  have e := congrArg (fun w : Equiv.Perm (Fin N) => w x.2) (Equiv.swap_mul_swap_mul_swap hab hac)
  simp only [Equiv.Perm.mul_apply] at e
  by_cases h : x.1 = τ
  · simp [swapAt, h, e, Equiv.swap_comm c a]
  · simp [swapAt, h]

/- English proof (translation)
Take `⟨d, hd⟩ : ∃ d, (c : ℕ) = a + 1 + d` from `⟨c - (a + 1), by have := Fin.lt_def.1 hac; omega⟩`. Use `clear hac`. Proceed by induction on `d generalizing c P with`. Consider the case `zero => exact hL τ a c (by omega) P hP`. Consider the case `succ d ih`.

Set `b : Fin N` to `⟨a + 1 + d, by omega⟩`. Establish `hb : (b : ℕ) = a + 1 + d` using `rfl`. Establish `hab : a ≠ b` using `fun h => by rw [← h] at hb; omega`. Establish `hac : a ≠ c` using `fun h => by rw [← h] at hd; omega`. Establish `hbc : (c : ℕ) = b + 1` using `by omega`.

Rewrite using `[← swapAt_conj τ hab hac, ← rename_rename, ← rename_rename, hL τ b c hbc _ ((hP.rename_isHomogeneous).rename_isHomogeneous), ih (c := b) _ (hP.rename_isHomogeneous) hb, hL τ b c hbc _ hP, neg_neg]`.
-/
theorem anti_swap (L : Pol ι N →ₗ[ℝ] ℝ)
    {k : ℕ} (hL : ∀ (τ : ι) (a b : Fin N), (b : ℕ) = a + 1 → ∀ P : Pol ι N, P.IsHomogeneous k →
      L (rename (swapAt τ a b) P) = -L P)
    (τ : ι) {a c : Fin N} (hac : a < c) (P : Pol ι N) (hP : P.IsHomogeneous k) :
    L (rename (swapAt τ a c) P) = -L P := by
  obtain ⟨d, hd⟩ : ∃ d, (c : ℕ) = a + 1 + d := ⟨c - (a + 1), by have := Fin.lt_def.1 hac; omega⟩
  clear hac
  induction d generalizing c P with
  | zero => exact hL τ a c (by omega) P hP
  | succ d ih =>
    let b : Fin N := ⟨a + 1 + d, by omega⟩
    have hb : (b : ℕ) = a + 1 + d := rfl
    have hab : a ≠ b := fun h => by rw [← h] at hb; omega
    have hac : a ≠ c := fun h => by rw [← h] at hd; omega
    have hbc : (c : ℕ) = b + 1 := by omega
    rw [← swapAt_conj τ hab hac, ← rename_rename, ← rename_rename,
      hL τ b c hbc _ ((hP.rename_isHomogeneous).rename_isHomogeneous), ih (c := b) _ (hP.rename_isHomogeneous) hb,
      hL τ b c hbc _ hP, neg_neg]

/- English proof (translation)
Establish `inj : Function.Injective (swapAt τ a b)` using `Function.LeftInverse.injective (g := swapAt τ a b) (swapAt_swapAt τ a b)`. It suffices to establish `hm : m.mapDomain (swapAt τ a b) = m by rw [rename_monomial, hm]`. Use extensionality with `x`. Rewrite using `[← swapAt_swapAt τ a b x, Finsupp.mapDomain_apply inj, swapAt_swapAt]`. Break down `x with ⟨σ, i⟩` into its components or cases.

Distinguish the cases in `hσ : σ = τ`. Substitute `hσ` using the available equality. Distinguish the cases in `ha : i = a`. Substitute `ha` using the available equality. Simplify using `[swapAt, h]`.

Distinguish the cases in `hb : i = b`. Substitute `hb` using the available equality. Simplify using `[swapAt, h]`. Simplify using `[swapAt, Equiv.swap_apply_of_ne_of_ne ha hb]`. Simplify using `[swapAt, hσ]`.
-/
theorem rename_swapAt_monomial (τ : ι) {a b : Fin N} {m : (ι × Fin N) →₀ ℕ} (h : m (τ, a) = m (τ, b)) (r : ℝ) :
    rename (swapAt τ a b) (monomial m r) = monomial m r := by
  have inj : Function.Injective (swapAt τ a b) :=
    Function.LeftInverse.injective (g := swapAt τ a b) (swapAt_swapAt τ a b)
  suffices hm : m.mapDomain (swapAt τ a b) = m by rw [rename_monomial, hm]
  ext x
  rw [← swapAt_swapAt τ a b x, Finsupp.mapDomain_apply inj, swapAt_swapAt]
  rcases x with ⟨σ, i⟩
  by_cases hσ : σ = τ
  · subst hσ
    by_cases ha : i = a
    · subst ha; simp [swapAt, h]
    · by_cases hb : i = b
      · subst hb; simp [swapAt, h]
      · simp [swapAt, Equiv.swap_apply_of_ne_of_ne ha hb]
  · simp [swapAt, hσ]

/- English proof (translation)
Rewrite using `[P.as_sum, map_sum]`. Use `Finset.sum_eq_zero fun m hm => ?_` and prove the remaining obligations. Establish `hdeg` using `hP (mem_support_iff.1 hm)`. Establish `hsum : ∑ x, m x = k`. Rewrite using `[← hdeg, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]`.

Simplify using the standard rewrite rules. Establish `hsplit : ∑ τ : ι, ∑ i : Fin N, m (τ, i) = k`. Rewrite using `[← Fintype.sum_prod_type']`. Conclude with `hsum`. Establish `hlt : ∑ τ : ι, ∑ i : Fin N, m (τ, i) < ∑ _τ : ι, N * (N - 1) / 2`.

Rewrite using `[hsplit, Finset.sum_const, Finset.card_univ, smul_eq_mul]`. Unfold `dimFl at hk`. Conclude with `hk`. Take `⟨τ, -, hτ⟩` from `Finset.exists_lt_of_sum_lt hlt`. Establish `hni : ¬ Function.Injective fun i : Fin N => m (τ, i)` using `fun hinj => (le_sum_of_injective hinj).not_gt hτ`.

Choose the witnesses or unpack the hypotheses as in `⟨a, b, hab, hne⟩ : ∃ a b : Fin N, m (τ, a) = m (τ, b) ∧ a ≠ b := by`. Simplify using `only [Function.Injective, not_forall] at hni`. Take `⟨a, b, h, hne⟩` from `hni`. Conclude with `⟨a, b, h, hne⟩`. Establish `hmon : (monomial m (coeff m P)).IsHomogeneous k` using `isHomogeneous_monomial _ (by rw [Finsupp.degree_eq_weight_one]; exact hdeg)`.

Break down `lt_or_gt_of_ne hne with h | h` into its components or cases. Establish `e` using `anti_swap L hL τ h (monomial m (coeff m P)) hmon`. Rewrite `e` using `[rename_swapAt_monomial τ hab]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e` using `anti_swap L hL τ h (monomial m (coeff m P)) hmon`.

Rewrite `e` using `[rename_swapAt_monomial τ hab.symm]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eq_zero_of_anti (L : Pol ι N →ₗ[ℝ] ℝ)
    {k : ℕ} (hL : ∀ (τ : ι) (a b : Fin N), (b : ℕ) = a + 1 → ∀ P : Pol ι N, P.IsHomogeneous k →
      L (rename (swapAt τ a b) P) = -L P)
    (hk : k < dimFl ι N) {P : Pol ι N} (hP : P.IsHomogeneous k) : L P = 0 := by
  rw [P.as_sum, map_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hdeg := hP (mem_support_iff.1 hm)
  have hsum : ∑ x, m x = k := by
    rw [← hdeg, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  have hsplit : ∑ τ : ι, ∑ i : Fin N, m (τ, i) = k := by
    rw [← Fintype.sum_prod_type']
    exact hsum
  have hlt : ∑ τ : ι, ∑ i : Fin N, m (τ, i) < ∑ _τ : ι, N * (N - 1) / 2 := by
    rw [hsplit, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    unfold dimFl at hk
    exact hk
  obtain ⟨τ, -, hτ⟩ := Finset.exists_lt_of_sum_lt hlt
  have hni : ¬ Function.Injective fun i : Fin N => m (τ, i) := fun hinj =>
    (le_sum_of_injective hinj).not_gt hτ
  obtain ⟨a, b, hab, hne⟩ : ∃ a b : Fin N, m (τ, a) = m (τ, b) ∧ a ≠ b := by
    simp only [Function.Injective, not_forall] at hni
    obtain ⟨a, b, h, hne⟩ := hni
    exact ⟨a, b, h, hne⟩
  have hmon : (monomial m (coeff m P)).IsHomogeneous k := isHomogeneous_monomial _ (by rw [Finsupp.degree_eq_weight_one]; exact hdeg)
  rcases lt_or_gt_of_ne hne with h | h
  · have e := anti_swap L hL τ h (monomial m (coeff m P)) hmon
    rw [rename_swapAt_monomial τ hab] at e
    linarith
  · have e := anti_swap L hL τ h (monomial m (coeff m P)) hmon
    rw [rename_swapAt_monomial τ hab.symm] at e
    linarith

section Reduction

open GlobalTheory.FlagForm

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

/- English proof (translation)
Unfold `rootForm`. Use `(IsHomogeneous.sum _ _ _ fun a _ => ?_).sub (IsHomogeneous.sum _ _ _ fun b _ => ?_)` and prove the remaining obligations. Use `split_ifs`. Conclude with `isHomogeneous_X _ _`. Conclude with `isHomogeneous_zero _ _ _`.

Use `split_ifs`. Conclude with `isHomogeneous_X _ _`. Conclude with `isHomogeneous_zero _ _ _`.
-/
theorem isHomogeneous_rootForm (x : ι × Fin N) : (rootForm x : FormPol ι N).IsHomogeneous 1 := by
  unfold rootForm
  refine (IsHomogeneous.sum _ _ _ fun a _ => ?_).sub (IsHomogeneous.sum _ _ _ fun b _ => ?_)
  · split_ifs
    · exact isHomogeneous_X _ _
    · exact isHomogeneous_zero _ _ _
  · split_ifs
    · exact isHomogeneous_X _ _
    · exact isHomogeneous_zero _ _ _

/- English proof (translation)
Use `show IsHomogeneous (eval₂ (algebraMap ℝ (FormPol ι N)) rootForm P) k`. Use `hP.eval₂ (algebraMap ℝ (FormPol ι N)) rootForm (fun r => isHomogeneous_C _ r) isHomogeneous_rootForm` as an intermediate fact. Rewrite `this` using `[one_mul]`. Then use the resulting hypothesis.
-/
theorem isHomogeneous_toForm {P : Pol ι N} {k : ℕ} (hP : P.IsHomogeneous k) : (toForm P).IsHomogeneous k := by
  show IsHomogeneous (eval₂ (algebraMap ℝ (FormPol ι N)) rootForm P) k
  have := hP.eval₂ (algebraMap ℝ (FormPol ι N)) rootForm (fun r => isHomogeneous_C _ r) isHomogeneous_rootForm
  rwa [one_mul] at this

/- English proof (translation)
Unfold `bcForm`. Use `IsHomogeneous.sum _ _ _ fun a _ => IsHomogeneous.sum _ _ _ fun b _ => ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `isHomogeneous_X _ _`. Conclude with `isHomogeneous_zero _ _ _`.
-/
theorem isHomogeneous_bcForm (τ : ι) : (bcForm τ : FormPol ι N).IsHomogeneous 1 := by
  unfold bcForm
  refine IsHomogeneous.sum _ _ _ fun a _ => IsHomogeneous.sum _ _ _ fun b _ => ?_
  split_ifs
  · exact isHomogeneous_X _ _
  · exact isHomogeneous_zero _ _ _

/- English proof (translation)
The claim follows from `IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow _ _`.
-/
theorem isHomogeneous_pSum_two (τ : ι) : (pSum τ 2 : Pol ι N).IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow _ _

/- English proof (translation)
Rewrite using `[Finset.sum_comm]`. Establish `e (b : Fin N) : ∑ a : Fin N, (if a < b then 1 else 0 : ℕ) = b`. Rewrite using `[Finset.sum_boole, Nat.cast_id, ← Fin.card_Iio b]`. Use `congr 1`. Use extensionality with `a`.

Simplify using the standard rewrite rules. Simplify using `only [e]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id]`.
-/
theorem sum_ite_lt (N : ℕ) : ∑ a : Fin N, ∑ b : Fin N, (if a < b then 1 else 0 : ℕ) = N * (N - 1) / 2 := by
  rw [Finset.sum_comm]
  have e (b : Fin N) : ∑ a : Fin N, (if a < b then 1 else 0 : ℕ) = b := by
    rw [Finset.sum_boole, Nat.cast_id, ← Fin.card_Iio b]
    congr 1
    ext a
    simp
  simp only [e]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id]

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]`. Establish `e (p : ι × Fin N × Fin N) : (volExp : (ι × Fin N × Fin N) →₀ ℕ) p = if p.2.1 < p.2.2 then 1 else 0` using `rfl`. Simplify using `only [e, Pi.one_apply, smul_eq_mul, mul_one]`. Rewrite using `[Fintype.sum_prod_type]`. Simplify using `only [Fintype.sum_prod_type, sum_ite_lt, Finset.sum_const, Finset.card_univ, smul_eq_mul]`.

Both sides reduce to the same expression.
-/
theorem weight_volExp : Finsupp.weight 1 (volExp : (ι × Fin N × Fin N) →₀ ℕ) = dimFl ι N := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  have e (p : ι × Fin N × Fin N) : (volExp : (ι × Fin N × Fin N) →₀ ℕ) p = if p.2.1 < p.2.2 then 1 else 0 := rfl
  simp only [e, Pi.one_apply, smul_eq_mul, mul_one]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, sum_ite_lt, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rfl

/- English proof (translation)
Establish `hv : Finsupp.degree (volExp : (ι × Fin N × Fin N) →₀ ℕ) = dimFl ι N`. Rewrite using `[Finsupp.degree_eq_weight_one]`. Conclude with `weight_volExp`. Rewrite using `[formDeg, hω.coeff_eq_zero (fun h => hk (h.symm.trans hv)), zero_div]`.
-/
theorem formDeg_eq_zero {ω : FormPol ι N} {k : ℕ} (hω : ω.IsHomogeneous k) (hk : k ≠ dimFl ι N) :
    formDeg ω = 0 := by
  have hv : Finsupp.degree (volExp : (ι × Fin N × Fin N) →₀ ℕ) = dimFl ι N := by
    rw [Finsupp.degree_eq_weight_one]; exact weight_volExp
  rw [formDeg, hω.coeff_eq_zero (fun h => hk (h.symm.trans hv)), zero_div]

noncomputable def defect (hh : Pol ι N →ₗ[ℝ] ℝ) (τ : ι) : Pol ι N →ₗ[ℝ] ℝ where
  toFun Q := hh (pSum τ 2 * Q) - formDeg (bcForm τ * toForm Q)
  map_add' P Q := by
    simp only [mul_add, map_add, toForm, formDeg, coeff_add, add_div]
    ring
  map_smul' c Q := by
    simp only [mul_smul_comm, map_smul, toForm, formDeg, coeff_smul, smul_eq_mul, RingHom.id_apply]
    ring

/- English proof (translation)
It suffices to establish `h : defect hh τ Q = 0 from sub_eq_zero.1 h`. Rewrite using `[← sum_homogeneousComponent Q, map_sum]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Establish `hk` using `homogeneousComponent_isHomogeneous k Q`. Distinguish the cases in `e : k + 1 = dimFl ι N`.

Take `rfl : k = dimFl ι N - 1` from `by omega`. Conclude with `eq_zero_of_anti (defect hh τ) (fun σ a b hab P hP => hswap σ a b hab P hP) (by omega) hk`. Use `show hh _ - formDeg _ = 0`. Rewrite using `[hHh.eq_zero (d := 2 + k) (by omega) ((isHomogeneous_pSum_two τ).mul hk), formDeg_eq_zero ((isHomogeneous_bcForm τ).mul (isHomogeneous_toForm hk)) (by omega), sub_zero]`.
-/
theorem eq_formDeg_of_swap (hh : Pol ι N →ₗ[ℝ] ℝ) (hHh : GlobalTheory.FlagZ.IsHh ι N hh) (τ : ι)
    (hswap : ∀ (σ : ι) (a b : Fin N), (b : ℕ) = a + 1 → ∀ Q : Pol ι N, Q.IsHomogeneous (dimFl ι N - 1) →
      hh (pSum τ 2 * rename (swapAt σ a b) Q) - formDeg (bcForm τ * toForm (rename (swapAt σ a b) Q)) =
        -(hh (pSum τ 2 * Q) - formDeg (bcForm τ * toForm Q)))
    (Q : Pol ι N) : hh (pSum τ 2 * Q) = formDeg (bcForm τ * toForm Q) := by
  suffices h : defect hh τ Q = 0 from sub_eq_zero.1 h
  rw [← sum_homogeneousComponent Q, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  have hk := homogeneousComponent_isHomogeneous k Q
  by_cases e : k + 1 = dimFl ι N
  · obtain rfl : k = dimFl ι N - 1 := by omega
    exact eq_zero_of_anti (defect hh τ) (fun σ a b hab P hP => hswap σ a b hab P hP) (by omega) hk
  · show hh _ - formDeg _ = 0
    rw [hHh.eq_zero (d := 2 + k) (by omega) ((isHomogeneous_pSum_two τ).mul hk),
      formDeg_eq_zero ((isHomogeneous_bcForm τ).mul (isHomogeneous_toForm hk)) (by omega), sub_zero]

end Reduction

end GlobalTheory.FlagAnti
