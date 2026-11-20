import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresDefs

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Use `revert j`. Evaluate the decidable proposition.
-/
private theorem zcases (j : ZMod 2) : j = 0 ∨ j = 1 := by
  revert j; decide

/- English proof (translation)
Simplify using `[sg]`.
-/
private theorem sg0 (K : Type) [CommRing K] : sg K 0 = 1 := by simp [sg]

/- English proof (translation)
Use `show (-1 : K) ^ ((1 : ZMod 2).val) = -1`. Rewrite using `[show (1 : ZMod 2).val = 1 from rfl]`. Simplify using the standard rewrite rules.
-/
private theorem sg1 (K : Type) [CommRing K] : sg K 1 = -1 := by
  show (-1 : K) ^ ((1 : ZMod 2).val) = -1
  rw [show (1 : ZMod 2).val = 1 from rfl]
  simp

/- English proof (translation)
Apply the tactic sequence `rcases zcases i with rfl | rfl <;> rcases zcases j with rfl | rfl`. Simplify using `[sg0]`. Simplify using `[sg0]`. Simplify using `[sg0]`. Rewrite using `[show (1 : ZMod 2) + 1 = 0 from rfl, sg0, sg1]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem sg_add (K : Type) [CommRing K] (i j : ZMod 2) : sg K (i + j) = sg K i * sg K j := by
  rcases zcases i with rfl | rfl <;> rcases zcases j with rfl | rfl
  · simp [sg0]
  · simp [sg0]
  · simp [sg0]
  · rw [show (1 : ZMod 2) + 1 = 0 from rfl, sg0, sg1]
    ring

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [sg0]`. Consider the case `succ k ih => rw [succ_nsmul, sg_add, ih, pow_succ]`.
-/
private theorem sg_nsmul (K : Type) [CommRing K] (m : ℕ) (i : ZMod 2) : sg K (m • i) = sg K i ^ m := by
  induction m with
  | zero => simp [sg0]
  | succ k ih => rw [succ_nsmul, sg_add, ih, pow_succ]

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply]`. Simplify using `only [Finsupp.prod, Finsupp.sum, ← sg_nsmul]`. Generalize the expression as in `n.support = t`. Use `Finset.induction_on t ?_ ?_` and prove the remaining obligations. Simplify using `[sg0]`.

Introduce `a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, ih, sg_add]`.
-/
private theorem sg_weight (K : Type) [CommRing K] {ι : Type} (wt : ι → ZMod 2) (n : ι →₀ ℕ) :
    (n.prod fun s m => sg K (wt s) ^ m) = sg K (Finsupp.weight wt n) := by
  classical
  rw [Finsupp.weight_apply]
  simp only [Finsupp.prod, Finsupp.sum, ← sg_nsmul]
  generalize n.support = t
  refine Finset.induction_on t ?_ ?_
  · simp [sg0]
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, sg_add]

/- English proof (translation)
Apply the tactic sequence `rcases zcases j with rfl | rfl <;> simp [sg0, sg1]`.
-/
private theorem coeff_sg (O : Type) [CommRing O] {ι : Type} (j : ZMod 2) (y : MvPowerSeries ι O) (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n (sg _ j * y) = sg O j * MvPowerSeries.coeff n y := by
  rcases zcases j with rfl | rfl <;> simp [sg0, sg1]

/- English proof (translation)
Introduce `O _ h2 ι _ wt`. Establish `hsq : ∀ i : ZMod 2, sg O i * sg O i = 1`. Introduce `i`. Rewrite using `[← sg_add]`. Break down `zcases i with rfl | rfl` into its components or cases.

Conclude with `sg0 O`. Rewrite using `[show (1 : ZMod 2) + 1 = 0 from rfl]`. Conclude with `sg0 O`. Establish `hne : ∀ i j : ZMod 2, i ≠ j → sg O i = - sg O j`. Introduce `i j hij`.

Apply the tactic sequence `rcases zcases i with rfl | rfl <;> rcases zcases j with rfl | rfl`. Conclude with `absurd rfl hij`. Simplify using `[sg0, sg1]`. Simplify using `[sg0, sg1]`. Conclude with `absurd rfl hij`.

Set `a : ι → O` to `fun s => sg O (wt s)`. Establish `hcoef : ∀ y n, MvPowerSeries.coeff n (MvPowerSeries.rescale a y) = sg O (Finsupp.weight wt n) * MvPowerSeries.coeff n y`. Introduce `y n`. Rewrite using `[MvPowerSeries.coeff_rescale, sg_weight]`. Set `τ : MvPowerSeries ι O →ₐ[O] MvPowerSeries ι O` to `AlgHom.mk (MvPowerSeries.rescale a) (fun r => by`.

Use extensionality with `n`. Use `show MvPowerSeries.coeff n (MvPowerSeries.rescale a (algebraMap O _ r)) = _`. Rewrite using `[hcoef]`. Distinguish the cases in `hn : n = 0`. Substitute `hn` using the available equality.

Simplify using `[sg0]`. Rewrite using `[MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, MvPowerSeries.coeff_C, if_neg hn, mul_zero])`. Establish `hτ : ∀ y n, MvPowerSeries.coeff n (τ y) = sg O (Finsupp.weight wt n) * MvPowerSeries.coeff n y` using `hcoef`. Use `⟨τ, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `y`.

Use extensionality with `n`. Rewrite using `[hτ, hτ, ← mul_assoc, hsq, one_mul]`. Introduce `j`. Use extensionality with `y`. Use `show τ y = sg _ j * y ↔ ∀ n, Finsupp.weight wt n ≠ j → MvPowerSeries.coeff n y = 0`.

Prove the components needed by the constructor for the conclusion. Introduce `h n hn`. Use `congrArg (MvPowerSeries.coeff n) h` as an intermediate fact. Rewrite `this` using `[hτ, coeff_sg, hne _ _ hn]`. Establish `h' : 2 * MvPowerSeries.coeff n y = 0`.

Take the linear combination `(-sg O j) * this - (2 * MvPowerSeries.coeff n y) * hsq j`. Conclude with `(h2.mul_right_eq_zero).mp h'`. Introduce `h`. Use extensionality with `n`. Rewrite using `[hτ, coeff_sg]`.

Distinguish the cases in `hn : Finsupp.weight wt n = j`. Rewrite using `[hn]`. Rewrite using `[h n hn, mul_zero, mul_zero]`. Introduce `j y`. Use extensionality with `n`.

Rewrite using `[two_mul, map_add, coeff_wcomp, map_add, coeff_sg, hτ]`. Use `split_ifs with hn`. Rewrite using `[hn]`. Take the linear combination `(-MvPowerSeries.coeff n y) * hsq j`. Rewrite using `[hne _ _ hn]`.

Take the linear combination `MvPowerSeries.coeff n y * hsq j`.
-/
theorem UpperTheory.V.Fr.ep_ps :
    ∀ (O : Type) [CommRing O], IsUnit (2 : O) → ∀ (ι : Type) [Finite ι] (wt : ι → ZMod 2), ∃ τ : MvPowerSeries ι O →ₐ[O] MvPowerSeries ι O, (∀ y, τ (τ y) = y) ∧ (∀ j, evp τ j = wtPart O wt j) ∧ ∀ j y, (2 : MvPowerSeries ι O) * wcomp O wt j y = y + sg _ j * τ y := by
  classical
  intro O _ h2 ι _ wt
  have hsq : ∀ i : ZMod 2, sg O i * sg O i = 1 := by
    intro i
    rw [← sg_add]
    rcases zcases i with rfl | rfl
    · exact sg0 O
    · rw [show (1 : ZMod 2) + 1 = 0 from rfl]
      exact sg0 O
  have hne : ∀ i j : ZMod 2, i ≠ j → sg O i = - sg O j := by
    intro i j hij
    rcases zcases i with rfl | rfl <;> rcases zcases j with rfl | rfl
    · exact absurd rfl hij
    · simp [sg0, sg1]
    · simp [sg0, sg1]
    · exact absurd rfl hij
  let a : ι → O := fun s => sg O (wt s)
  have hcoef : ∀ y n, MvPowerSeries.coeff n (MvPowerSeries.rescale a y)
      = sg O (Finsupp.weight wt n) * MvPowerSeries.coeff n y := by
    intro y n
    rw [MvPowerSeries.coeff_rescale, sg_weight]
  let τ : MvPowerSeries ι O →ₐ[O] MvPowerSeries ι O :=
    AlgHom.mk (MvPowerSeries.rescale a) (fun r => by
      ext n
      show MvPowerSeries.coeff n (MvPowerSeries.rescale a (algebraMap O _ r)) = _
      rw [hcoef]
      by_cases hn : n = 0
      · subst hn
        simp [sg0]
      · classical
        rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          MvPowerSeries.coeff_C, if_neg hn, mul_zero])
  have hτ : ∀ y n, MvPowerSeries.coeff n (τ y)
      = sg O (Finsupp.weight wt n) * MvPowerSeries.coeff n y := hcoef
  refine ⟨τ, ?_, ?_, ?_⟩
  · intro y
    ext n
    rw [hτ, hτ, ← mul_assoc, hsq, one_mul]
  · intro j
    ext y
    show τ y = sg _ j * y ↔ ∀ n, Finsupp.weight wt n ≠ j → MvPowerSeries.coeff n y = 0
    constructor
    · intro h n hn
      have := congrArg (MvPowerSeries.coeff n) h
      rw [hτ, coeff_sg, hne _ _ hn] at this
      have h' : 2 * MvPowerSeries.coeff n y = 0 := by
        linear_combination (-sg O j) * this - (2 * MvPowerSeries.coeff n y) * hsq j
      exact (h2.mul_right_eq_zero).mp h'
    · intro h
      ext n
      rw [hτ, coeff_sg]
      by_cases hn : Finsupp.weight wt n = j
      · rw [hn]
      · rw [h n hn, mul_zero, mul_zero]
  · intro j y
    ext n
    rw [two_mul, map_add, coeff_wcomp, map_add, coeff_sg, hτ]
    split_ifs with hn
    · rw [hn]
      linear_combination (-MvPowerSeries.coeff n y) * hsq j
    · rw [hne _ _ hn]
      linear_combination MvPowerSeries.coeff n y * hsq j
