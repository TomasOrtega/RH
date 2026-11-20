import Development.WeilBound.ThetaLifts.LocalTheory.StandardValuations.SplitProd
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.ExistsUpperProjectionInverseTranspose

set_option linter.unusedSectionVars false

noncomputable section

open Matrix MeasureTheory ValuativeRel Topology GlobalTheory.SplitFlip GlobalTheory.SplitWeil PositivityTheory.ThK.SplitLoc

namespace PositivityTheory.ThKG.Std

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
attribute [local instance 10000] GlobalTheory.SplitWeil.matrixMeasurableSpace

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n d a a' : ℕ} {ν α β : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ}

def InR (ϖ : kˣ) (c : ℕ) (e : Fin n → Fin d) (Y : Matrix (Fin n) (Fin d) k) : Prop :=
  ∀ i j, valuation k (Y i j) ≤ valuation k (rad ϖ c e j)

open Classical in
/- English proof (translation)
Simplify using `only [ind, Finset.prod_ite_zero, Finset.prod_const_one, Finset.mem_univ, true_imp_iff, InR, Prod.forall]`. Reduce the equality to equality of the corresponding arguments.
-/
theorem prod_ind (e : Fin n → Fin d) (Y : Matrix (Fin n) (Fin d) k) :
    ∏ p : Fin n × Fin d, ind (rad ϖ c e p.2) (Y p.1 p.2) = if InR ϖ c e Y then 1 else 0 := by
  simp only [ind, Finset.prod_ite_zero, Finset.prod_const_one, Finset.mem_univ, true_imp_iff, InR, Prod.forall]
  congr

/- English proof (translation)
Introduce `i j` and use `by rw [Matrix.mul_apply] exact (valuation k).map_sum_le fun l _ => by rw [map_mul]; exact (mul_le_of_le_one_left' (hg i l)).trans (h l j)`.
-/
theorem InR.mul {e : Fin n → Fin d} {Y : Matrix (Fin n) (Fin d) k} (h : InR ϖ c e Y) {g : Matrix (Fin n) (Fin n) k}
    (hg : ∀ i j, g i j ∈ 𝒪[k]) : InR ϖ c e (g * Y) := fun i j => by
  rw [Matrix.mul_apply]
  exact (valuation k).map_sum_le fun l _ => by rw [map_mul]; exact (mul_le_of_le_one_left' (hg i l)).trans (h l j)

open Classical in
/- English proof (translation)
Establish `hb : (g.1 * Y).submatrix id e = g.1`. Rewrite using `[show (g.1 * Y).submatrix id e = g.1 * Y.submatrix id e from rfl, hY, Matrix.mul_one]`. Rewrite using `[std, hb, prod_ind]`. Distinguish the cases in `hg : g ∈ KO k (Fin n)`. Establish `hv` using `valuation_gdet_of_mem_KO hg`.

Rewrite using `[Set.indicator_of_mem hg, show g.1.det = (gdet g : k) from rfl, dl_unit _ hv, apow_of_valuation_eq_one hv]`. Rewrite `hg` using `[mem_KO_iff]`. Establish `: InR ϖ c e (g.1 * Y) ↔ InR ϖ c e Y` using `⟨fun h => by simpa [← Matrix.mul_assoc] using h.mul hg.2, fun h => h.mul hg.1⟩`. Simplify using `[this]`. Rewrite using `[Set.indicator_of_notMem hg]`.

Distinguish the cases in `h1 : InR ϖ c e (g.1 * Y)`. Establish `h2 : ∀ i j, valuation k (g.1 i j) ≤ 1` using `fun i j => by`. Use `h1 i (e j)` as an intermediate fact. Rewrite `this` using `[rad_e, map_one, show (g.1 * Y) i (e j) = g.1 i j from congrFun (congrFun hb i) j]`. Then use the resulting hypothesis. Rewrite using `[dl_of_ne, mul_zero, zero_mul, zero_mul]`.

Introduce `hd`. Use `hg ((mem_KO_iff _).2 ⟨h2, fun i j => ?_⟩)` and prove the remaining obligations. Use `show valuation k _ ≤ 1`. Rewrite using `[Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, map_mul, Ring.inverse_eq_inv', map_inv₀, hd, inv_one, one_mul, adjugate_apply]`. Use `val_det fun p q => ?_` and prove the remaining obligations.

Rewrite using `[updateRow_apply]`. Use `split_ifs`. Apply the tactic sequence `rw [Pi.single_apply]; split_ifs <;> simp`. Conclude with `h2 p q`. Simplify using `[h1]`.
-/
theorem std_mul {e : Fin n → Fin d} {Y : Matrix (Fin n) (Fin d) k} (hY : Y.submatrix id e = 1) (g : GL (Fin n) k) (z : ℂ) :
    std ν ϖ c e (g.1 * Y) * (ν (gdet g) : ℂ) * apow (gdet g) z =
      (KO k (Fin n) : Set _).indicator (fun _ => if InR ϖ c e Y then 1 else 0) g := by
  have hb : (g.1 * Y).submatrix id e = g.1 := by
    rw [show (g.1 * Y).submatrix id e = g.1 * Y.submatrix id e from rfl, hY, Matrix.mul_one]
  rw [std, hb, prod_ind]
  by_cases hg : g ∈ KO k (Fin n)
  · have hv := valuation_gdet_of_mem_KO hg
    rw [Set.indicator_of_mem hg, show g.1.det = (gdet g : k) from rfl, dl_unit _ hv, apow_of_valuation_eq_one hv]
    rw [mem_KO_iff] at hg
    have : InR ϖ c e (g.1 * Y) ↔ InR ϖ c e Y := ⟨fun h => by simpa [← Matrix.mul_assoc] using h.mul hg.2, fun h => h.mul hg.1⟩
    simp [this]
  · rw [Set.indicator_of_notMem hg]
    by_cases h1 : InR ϖ c e (g.1 * Y)
    · have h2 : ∀ i j, valuation k (g.1 i j) ≤ 1 := fun i j => by
        have := h1 i (e j)
        rwa [rad_e, map_one, show (g.1 * Y) i (e j) = g.1 i j from congrFun (congrFun hb i) j] at this
      rw [dl_of_ne, mul_zero, zero_mul, zero_mul]
      intro hd
      refine hg ((mem_KO_iff _).2 ⟨h2, fun i j => ?_⟩)
      show valuation k _ ≤ 1
      rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, map_mul, Ring.inverse_eq_inv', map_inv₀, hd,
        inv_one, one_mul, adjugate_apply]
      refine val_det fun p q => ?_
      rw [updateRow_apply]
      split_ifs
      · rw [Pi.single_apply]; split_ifs <;> simp
      · exact h2 p q
    · simp [h1]

/- English proof (translation)
Rewrite using `[std, show (g * Y).submatrix id e = g * Y.submatrix id e from rfl, det_mul, hY, mul_zero, dl_of_ne (by simp), mul_zero]`.
-/
theorem std_sing {e : Fin n → Fin d} {Y : Matrix (Fin n) (Fin d) k} (hY : (Y.submatrix id e).det = 0) (g : Matrix (Fin n) (Fin n) k) :
    std ν ϖ c e (g * Y) = 0 := by
  rw [std, show (g * Y).submatrix id e = g * Y.submatrix id e from rfl, det_mul, hY, mul_zero, dl_of_ne (by simp), mul_zero]

variable [MeasurableSpace k] [BorelSpace k]

/- English proof (translation)
Rewrite using `[integral_indicator isOpen_KO.measurableSet]`. Simplify using `[Measure.real, haarVol_self isOpen_KO le_rfl]`.
-/
theorem int_KO (A : ℂ) : ∫ g, (KO k (Fin n) : Set _).indicator (fun _ => A) g ∂haarVol (KO k (Fin n)) = A := by
  rw [integral_indicator isOpen_KO.measurableSet]
  simp [Measure.real, haarVol_self isOpen_KO le_rfl]

/- English proof (translation)
Simplify using `[bigF, shellSum, shell, std_sing hY]`.
-/
theorem bigF_sing (μ) {e : Fin n → Fin d} {Y : Matrix (Fin n) (Fin d) k} (hY : (Y.submatrix id e).det = 0) :
    bigF μ ϖ ν (std ν ϖ c e) Y = 0 := by simp [bigF, shellSum, shell, std_sing hY]

/- English proof (translation)
Simplify using `[smallF, std_sing hY]`.
-/
theorem smallF_sing (μ) {e : Fin n → Fin d} {Y : Matrix (Fin n) (Fin d) k} (hY : (Y.submatrix id e).det = 0) :
    smallF μ ν (std ν ϖ c e) Y = 0 := by simp [smallF, std_sing hY]

open Classical in
/- English proof (translation)
Simplify using `only [smallF, std_mul hY, int_KO]`.
-/
theorem smallF_std {e : Fin n → Fin d} {Y : Matrix (Fin n) (Fin d) k} (hY : Y.submatrix id e = 1) :
    smallF (haarVol (KO k (Fin n))) ν (std ν ϖ c e) Y = if InR ϖ c e Y then 1 else 0 := by
  simp only [smallF, std_mul hY, int_KO]

open Classical in
/- English proof (translation)
Rewrite using `[bigF, shellSum, finsum_eq_single _ ⟨0, antitone_const⟩]`. Simplify using `only [shell, std_mul hY, shellSet_zero]`. Rewrite using `[setIntegral_indicator isOpen_KO.measurableSet, Set.inter_self, ← integral_indicator isOpen_KO.measurableSet, int_KO]`. Introduce `m hm`. Simplify using `only [shell, std_mul hY]`.

Use `setIntegral_eq_zero_of_forall_eq_zero fun g hg => Set.indicator_of_notMem (fun hK => hm (Subtype.ext (funext fun i => ?_))) _` and prove the remaining obligations. Take `⟨x, hx, y, hy, rfl⟩` from `mem_shellSet.1 hg`. Establish `h1` using `(mem_KO_iff _).1 ((Subgroup.mul_mem_cancel_left _ hx).1 ((Subgroup.mul_mem_cancel_right _ hy).1 hK))`. Establish `h2 : valuation k ((ϖ : k) ^ m.1 i) ≤ 1` using `by simpa [diagGL_val] using (show valuation k _ ≤ 1 from h1.1 i i)`. Establish `h3 : valuation k ((ϖ : k) ^ (-m.1 i)) ≤ 1`.

Use `(show valuation k _ ≤ 1 from h1.2 i i)` as an intermediate fact. Rewrite using `[show (diagGL fun i => ϖ ^ m.1 i)⁻¹ = diagGL fun i => ϖ ^ (-m.1 i) from inv_eq_of_mul_eq_one_right (Units.ext (by`. Simplify using `[diagGL_val, funext_iff, zpow_ne_zero]))] at this`. Simplify `this` using `[diagGL_val]`. Rewrite `h2`, `h3` using `[map_zpow₀, hϖ, zpow_le_one_iff_right_of_lt_one₀ uniformizer_pos uniformizer_lt_one]`.

Use `show m.1 i = 0`. Use linear arithmetic over natural numbers and integers.
-/
theorem bigF_std (hϖ : IsUnif ϖ) {e : Fin n → Fin d} {Y : Matrix (Fin n) (Fin d) k} (hY : Y.submatrix id e = 1) :
    bigF (haarVol (KO k (Fin n))) ϖ ν (std ν ϖ c e) Y = if InR ϖ c e Y then 1 else 0 := by
  rw [bigF, shellSum, finsum_eq_single _ ⟨0, antitone_const⟩]
  · simp only [shell, std_mul hY, shellSet_zero]
    rw [setIntegral_indicator isOpen_KO.measurableSet, Set.inter_self, ← integral_indicator isOpen_KO.measurableSet, int_KO]
  · intro m hm
    simp only [shell, std_mul hY]
    refine setIntegral_eq_zero_of_forall_eq_zero fun g hg => Set.indicator_of_notMem (fun hK => hm (Subtype.ext (funext fun i => ?_))) _
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_shellSet.1 hg
    have h1 := (mem_KO_iff _).1 ((Subgroup.mul_mem_cancel_left _ hx).1 ((Subgroup.mul_mem_cancel_right _ hy).1 hK))
    have h2 : valuation k ((ϖ : k) ^ m.1 i) ≤ 1 := by simpa [diagGL_val] using (show valuation k _ ≤ 1 from h1.1 i i)
    have h3 : valuation k ((ϖ : k) ^ (-m.1 i)) ≤ 1 := by
      have := (show valuation k _ ≤ 1 from h1.2 i i)
      rw [show (diagGL fun i => ϖ ^ m.1 i)⁻¹ = diagGL fun i => ϖ ^ (-m.1 i) from inv_eq_of_mul_eq_one_right (Units.ext (by
        simp [diagGL_val, funext_iff, zpow_ne_zero]))] at this
      simpa [diagGL_val] using this
    rw [map_zpow₀, hϖ, zpow_le_one_iff_right_of_lt_one₀ uniformizer_pos uniformizer_lt_one] at h2 h3
    show m.1 i = 0
    omega

def eA (a a' : ℕ) (i : Fin a) : Fin (a + a') := finSumFinEquiv (Sum.inl i)

def eB (a a' : ℕ) (i : Fin a') : Fin (a + a') := finSumFinEquiv (Sum.inr i)

def low (y : Matrix (Fin a') (Fin a) k) : GL (Fin (a + a')) k :=
  ⟨(fromBlocks 1 0 y 1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm,
    (fromBlocks 1 0 (-y) 1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm,
    by rw [submatrix_mul_equiv, fromBlocks_multiply]; simp, by rw [submatrix_mul_equiv, fromBlocks_multiply]; simp⟩

/- English proof (translation)
The claim follows from `Units.ext (by show det (Matrix.submatrix _ _ _) = 1 rw [det_submatrix_equiv_self, det_fromBlocks_zero₁₂]; simp)`.
-/
theorem gdet_low (y : Matrix (Fin a') (Fin a) k) : gdet (low y) = 1 := Units.ext (by
  show det (Matrix.submatrix _ _ _) = 1
  rw [det_submatrix_equiv_self, det_fromBlocks_zero₁₂]; simp)

/- English proof (translation)
The claim follows from `if_neg fun ⟨_, h⟩ => by simpa using finSumFinEquiv.injective h`.
-/
theorem rad_AB (j : Fin a') : rad ϖ c (eA a a') (finSumFinEquiv (Sum.inr j)) = (ϖ : k) ^ c :=
  if_neg fun ⟨_, h⟩ => by simpa using finSumFinEquiv.injective h

/- English proof (translation)
The claim follows from `if_neg fun ⟨_, h⟩ => by simpa using finSumFinEquiv.injective h`.
-/
theorem rad_BA (j : Fin a) : rad ϖ c (eB a a') (finSumFinEquiv (Sum.inl j)) = (ϖ : k) ^ c :=
  if_neg fun ⟨_, h⟩ => by simpa using finSumFinEquiv.injective h

/- English proof (translation)
Introduce `i j` and use `by refine (frameMatrixFirstColumnBlock_mul_apply finSumFinEquiv (invT (low y)).1 i _).trans ?_ simp [invT_val, low]`.
-/
theorem low_X (y : Matrix (Fin a') (Fin a) k) : ∀ i (j : Fin a ⊕ Fin a'), (X0 k finSumFinEquiv * (invT (low y)).1 : Matrix (Fin a) (Fin (a + a')) k) i (finSumFinEquiv j) =
    fromBlocks (1 : Matrix (Fin a) (Fin a) k) 0 (-y) (1 : Matrix (Fin a') (Fin a') k) j (Sum.inl i) := fun i j => by
    refine (frameMatrixFirstColumnBlock_mul_apply finSumFinEquiv (invT (low y)).1 i _).trans ?_
    simp [invT_val, low]

/- English proof (translation)
Introduce `i j` and use `by refine (frameMatrixSecondColumnBlock_mul_apply finSumFinEquiv (low y).1 i _).trans ?_ simp [low]`.
-/
theorem low_Y (y : Matrix (Fin a') (Fin a) k) : ∀ i (j : Fin a ⊕ Fin a'), (Y0 k finSumFinEquiv * (low y).1 : Matrix (Fin a') (Fin (a + a')) k) i (finSumFinEquiv j) =
    fromBlocks (1 : Matrix (Fin a) (Fin a) k) 0 y 1 (Sum.inr i) j := fun i j => by
    refine (frameMatrixSecondColumnBlock_mul_apply finSumFinEquiv (low y).1 i _).trans ?_
    simp [low]

open Classical in
/- English proof (translation)
Establish `e` using `low_X (k := k) y`. Rewrite using `[pRam, bigZetaIntegral_eq, gdet_low, bigF_std hϖ (by`. Use extensionality with `i j`. Rewrite using `[submatrix_apply, eA, id]`. Use `erw [e]`.

Simplify using `[one_apply, eq_comm])]`. Simplify using `only [map_one, Units.val_one, apow_one, one_mul]`. Use `if_congr ⟨fun h i j => ?_, fun h i j => ?_⟩ rfl rfl` and prove the remaining obligations. Use `h j (finSumFinEquiv (Sum.inr i)) erw [e, rad_AB] at this` as an intermediate fact. Simplify using `using this`.

Take `⟨j | j, rfl⟩` from `finSumFinEquiv.surjective j`. Use `erw [e, show finSumFinEquiv (Sum.inl j) = eA a a' j from rfl, rad_e]`. Apply the tactic sequence `simp only [fromBlocks_apply₁₁, one_apply]; split_ifs <;> simp`. Use `erw [e, rad_AB]`. Simplify using `using h j i`.
-/
theorem pRam_low (hϖ : IsUnif ϖ) (y : Matrix (Fin a') (Fin a) k) : pRam a a' ϖ ν β (std ν ϖ c (eA a a')) (low y) =
    if ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ c) then 1 else 0 := by
  have e := low_X (k := k) y
  rw [pRam, bigZetaIntegral_eq, gdet_low, bigF_std hϖ (by
    ext i j; rw [submatrix_apply, eA, id]; erw [e]; simp [one_apply, eq_comm])]
  simp only [map_one, Units.val_one, apow_one, one_mul]
  refine if_congr ⟨fun h i j => ?_, fun h i j => ?_⟩ rfl rfl
  · have := h j (finSumFinEquiv (Sum.inr i))
    erw [e, rad_AB] at this
    simpa using this
  · obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j
    · erw [e, show finSumFinEquiv (Sum.inl j) = eA a a' j from rfl, rad_e]
      simp only [fromBlocks_apply₁₁, one_apply]; split_ifs <;> simp
    · erw [e, rad_AB]; simpa using h j i

open Classical in
/- English proof (translation)
Establish `e` using `low_Y (k := k) y`. Establish `hY : (Y0 k finSumFinEquiv * (low y).1 : Matrix (Fin a') (Fin (a + a')) k).submatrix id (eB a a') = 1`. Use extensionality with `i j`. Rewrite using `[submatrix_apply, eB, id, e]`. Simplify using the standard rewrite rules.

Rewrite using `[pRam', smallP, gdet_low]`. Use `erw [smallF_std hY]`. Simplify using `only [map_one, Units.val_one, apow_one, one_mul]`. Use `if_congr ⟨fun h i j => ?_, fun h i j => ?_⟩ rfl rfl` and prove the remaining obligations. Use `h i (finSumFinEquiv (Sum.inl j)) erw [e, rad_BA] at this` as an intermediate fact.

Simplify using `using this`. Take `⟨j | j, rfl⟩` from `finSumFinEquiv.surjective j`. Use `erw [e, rad_BA]`. Simplify using `using h i j`. Use `erw [e, show finSumFinEquiv (Sum.inr j) = eB a a' j from rfl, rad_e]`.

Apply the tactic sequence `simp only [fromBlocks_apply₂₂, one_apply]; split_ifs <;> simp`.
-/
theorem pRam'_low (y : Matrix (Fin a') (Fin a) k) : pRam' a a' ν α (std ν ϖ c (eB a a')) (low y) =
    if ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ c) then 1 else 0 := by
  have e := low_Y (k := k) y
  have hY : (Y0 k finSumFinEquiv * (low y).1 : Matrix (Fin a') (Fin (a + a')) k).submatrix id (eB a a') = 1 := by
    ext i j; rw [submatrix_apply, eB, id, e]; simp
  rw [pRam', smallP, gdet_low]
  erw [smallF_std hY]
  simp only [map_one, Units.val_one, apow_one, one_mul]
  refine if_congr ⟨fun h i j => ?_, fun h i j => ?_⟩ rfl rfl
  · have := h i (finSumFinEquiv (Sum.inl j))
    erw [e, rad_BA] at this
    simpa using this
  · obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j
    · erw [e, rad_BA]; simpa using h i j
    · erw [e, show finSumFinEquiv (Sum.inr j) = eB a a' j from rfl, rad_e]
      simp only [fromBlocks_apply₂₂, one_apply]; split_ifs <;> simp

/- English proof (translation)
Introduce `h` and use `by have := congrFun h (low 0) rw [pRam_low hϖ] at this simp at this`.
-/
theorem pRam_ne (hϖ : IsUnif ϖ) : pRam a a' ϖ ν β (std ν ϖ c (eA a a')) ≠ 0 := fun h => by
  have := congrFun h (low 0)
  rw [pRam_low hϖ] at this
  simp at this

/- English proof (translation)
Use function extensionality and compare the values at `h`. Set `s : Fin a ⊕ Fin a' ≃ Fin (a + a')` to `finSumFinEquiv`. Use `set N := h.1.submatrix s s with hN`. Use `set N' := (h⁻¹).1.submatrix s s with hN'`. Establish `hNN : N * N' = 1` using `by rw [hN, hN', submatrix_mul_equiv, Units.mul_inv, submatrix_one_equiv]`.

Distinguish the cases in `hD : N.toBlocks₂₂.det = 0`. Establish `h1 : N'.toBlocks₁₁.det = 0`. Assume the negation of the conclusion as `h1`. Rewrite `hNN` using `[← fromBlocks_toBlocks N, ← fromBlocks_toBlocks N', fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj]`. Take `⟨-, -, e1, e2⟩` from `hNN`.

Establish `e3 : N.toBlocks₂₁ = -(N.toBlocks₂₂ * N'.toBlocks₂₁ * N'.toBlocks₁₁⁻¹)`. Rewrite using `[← Matrix.neg_mul, ← eq_neg_of_add_eq_zero_left e1, Matrix.mul_nonsing_inv_cancel_right _ _ (Ne.isUnit h1)]`. Establish `e4 : N.toBlocks₂₂ * (N'.toBlocks₂₂ - N'.toBlocks₂₁ * N'.toBlocks₁₁⁻¹ * N'.toBlocks₁₂) = 1`. Rewrite using `[← e2, e3]`. Simplify using `only [Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_assoc]`.

Normalize the expressions using the abelian group laws. Use `congrArg det e4` as an intermediate fact. Rewrite `this` using `[det_mul, hD, zero_mul, det_one]`. Conclude with `zero_ne_one this`. Establish `a1 : ((X0 k finSumFinEquiv * (invT h).1 : Matrix (Fin a) (Fin (a + a')) k).submatrix id (eA a a')).det = 0`.

Rewrite using `[← det_transpose, ← h1]`. Use `congr 1`. Use extensionality with `i j`. Conclude with `frameMatrixFirstColumnBlock_mul_apply s (invT h).1 j _`. Establish `a2 : ((Y0 k finSumFinEquiv * h.1 : Matrix (Fin a') (Fin (a + a')) k).submatrix id (eB a a')).det = 0`.

Rewrite using `[← hD]`. Use `congr 1`. Use extensionality with `i j`. Conclude with `frameMatrixSecondColumnBlock_mul_apply s h.1 i _`. Rewrite using `[pRam, bigZetaIntegral_eq, pRam', smallP]`.

Use `erw [bigF_sing _ a1, smallF_sing _ a2]`. Simplify using the standard rewrite rules. Use `set y := N.toBlocks₂₂⁻¹ * N.toBlocks₂₁ with hy set b := h * (low y)⁻¹ with hb`. Establish `eb : b.1.submatrix s s = N * fromBlocks 1 0 (-y) 1`. Rewrite using `[hb, Units.val_mul, ← submatrix_mul_equiv _ _ _ s]`.

Use `congr 1`. Use extensionality with `i j`. Simplify using `[low, s]`. Establish `e21 : (b.1.submatrix s s).toBlocks₂₁ = 0`. Rewrite using `[eb, ← fromBlocks_toBlocks N, fromBlocks_multiply]`.

Simplify using `[hy, Matrix.mul_nonsing_inv_cancel_left _ _ (Ne.isUnit hD)]`. Establish `hu : IsBlockUpper b` using `fun i j => congrFun (congrFun e21 i) j`. Establish `hdet : (blkA b).det * (blkD b).det ≠ 0`. Establish `: b.1.det = (blkA b).det * (blkD b).det`. Rewrite using `[← det_submatrix_equiv_self s, ← fromBlocks_toBlocks (b.1.submatrix s s), e21, det_fromBlocks_zero₂₁]`.

Both sides reduce to the same expression. Rewrite using `[← this]`. Conclude with `b.det_ne_zero`. Establish `hh : h = b * low y` using `by simp [hb]`. Rewrite using `[hh, (pRam_mem H hr (std_mem H.unif hc hν _)).2 b _ hu (Units.mk0 _ (left_ne_zero_of_mul hdet)) (Units.mk0 _ (right_ne_zero_of_mul hdet)) rfl rfl, (pRam'_mem H (std_mem H.unif hc hν _)).2 b _ hu (Units.mk0 _ (left_ne_zero_of_mul hdet)) (Units.mk0 _ (right_ne_zero_of_mul hdet)) rf …`.
-/
theorem std_pair (H : HidaSetting a a' ϖ α β ν) (hr : ¬ IsUnram ν) (hc : 1 ≤ c) (hν : CondLE ϖ c ν) :
    pRam a a' ϖ ν β (std ν ϖ c (eA a a')) = pRam' a a' ν α (std ν ϖ c (eB a a')) := by
  funext h
  let s : Fin a ⊕ Fin a' ≃ Fin (a + a') := finSumFinEquiv
  set N := h.1.submatrix s s with hN
  set N' := (h⁻¹).1.submatrix s s with hN'
  have hNN : N * N' = 1 := by rw [hN, hN', submatrix_mul_equiv, Units.mul_inv, submatrix_one_equiv]
  by_cases hD : N.toBlocks₂₂.det = 0
  · have h1 : N'.toBlocks₁₁.det = 0 := by
      by_contra h1
      rw [← fromBlocks_toBlocks N, ← fromBlocks_toBlocks N', fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at hNN
      obtain ⟨-, -, e1, e2⟩ := hNN
      have e3 : N.toBlocks₂₁ = -(N.toBlocks₂₂ * N'.toBlocks₂₁ * N'.toBlocks₁₁⁻¹) := by
        rw [← Matrix.neg_mul, ← eq_neg_of_add_eq_zero_left e1, Matrix.mul_nonsing_inv_cancel_right _ _ (Ne.isUnit h1)]
      have e4 : N.toBlocks₂₂ * (N'.toBlocks₂₂ - N'.toBlocks₂₁ * N'.toBlocks₁₁⁻¹ * N'.toBlocks₁₂) = 1 := by
        rw [← e2, e3]; simp only [Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_assoc]; abel
      have := congrArg det e4
      rw [det_mul, hD, zero_mul, det_one] at this
      exact zero_ne_one this
    have a1 : ((X0 k finSumFinEquiv * (invT h).1 : Matrix (Fin a) (Fin (a + a')) k).submatrix id (eA a a')).det = 0 := by
      rw [← det_transpose, ← h1]; congr 1; ext i j
      exact frameMatrixFirstColumnBlock_mul_apply s (invT h).1 j _
    have a2 : ((Y0 k finSumFinEquiv * h.1 : Matrix (Fin a') (Fin (a + a')) k).submatrix id (eB a a')).det = 0 := by
      rw [← hD]; congr 1; ext i j
      exact frameMatrixSecondColumnBlock_mul_apply s h.1 i _
    rw [pRam, bigZetaIntegral_eq, pRam', smallP]
    erw [bigF_sing _ a1, smallF_sing _ a2]
    simp
  · set y := N.toBlocks₂₂⁻¹ * N.toBlocks₂₁ with hy
    set b := h * (low y)⁻¹ with hb
    have eb : b.1.submatrix s s = N * fromBlocks 1 0 (-y) 1 := by
      rw [hb, Units.val_mul, ← submatrix_mul_equiv _ _ _ s]
      congr 1
      ext i j; simp [low, s]
    have e21 : (b.1.submatrix s s).toBlocks₂₁ = 0 := by
      rw [eb, ← fromBlocks_toBlocks N, fromBlocks_multiply]
      simp [hy, Matrix.mul_nonsing_inv_cancel_left _ _ (Ne.isUnit hD)]
    have hu : IsBlockUpper b := fun i j => congrFun (congrFun e21 i) j
    have hdet : (blkA b).det * (blkD b).det ≠ 0 := by
      have : b.1.det = (blkA b).det * (blkD b).det := by
        rw [← det_submatrix_equiv_self s, ← fromBlocks_toBlocks (b.1.submatrix s s), e21, det_fromBlocks_zero₂₁]; rfl
      rw [← this]; exact b.det_ne_zero
    have hh : h = b * low y := by simp [hb]
    rw [hh, (pRam_mem H hr (std_mem H.unif hc hν _)).2 b _ hu (Units.mk0 _ (left_ne_zero_of_mul hdet))
      (Units.mk0 _ (right_ne_zero_of_mul hdet)) rfl rfl, (pRam'_mem H (std_mem H.unif hc hν _)).2 b _ hu
      (Units.mk0 _ (left_ne_zero_of_mul hdet)) (Units.mk0 _ (right_ne_zero_of_mul hdet)) rfl rfl, pRam_low H.unif, pRam'_low]

omit [MeasurableSpace k] [BorelSpace k] in
/- English proof (translation)
Establish `hv` using `valuation_gdet_of_mem_KO hg`. Rewrite `hg` using `[mem_KO_iff]`. Establish `: InR ϖ c e (g.1 * Y) ↔ InR ϖ c e Y` using `⟨fun h => by simpa [← Matrix.mul_assoc] using h.mul hg.2, fun h => h.mul hg.1⟩`. Rewrite using `[std, std, prod_ind, prod_ind, show (g.1 * Y).submatrix id e = g.1 * Y.submatrix id e from rfl, det_mul, show g.1.det = (gdet g : k) from rfl, dl_mul_unit hv, dl_unit _ hv]`. Rewrite using `[propext this, mul_left_comm, ← mul_assoc (ν _ : ℂ), Units.mul_inv, one_mul]`.
-/
theorem std_left {e : Fin n → Fin d} {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) (Y : Matrix (Fin n) (Fin d) k) :
    (ν (gdet g) : ℂ) * std ν ϖ c e (g.1 * Y) = std ν ϖ c e Y := by
  have hv := valuation_gdet_of_mem_KO hg
  rw [mem_KO_iff] at hg
  have : InR ϖ c e (g.1 * Y) ↔ InR ϖ c e Y := ⟨fun h => by simpa [← Matrix.mul_assoc] using h.mul hg.2, fun h => h.mul hg.1⟩
  rw [std, std, prod_ind, prod_ind, show (g.1 * Y).submatrix id e = g.1 * Y.submatrix id e from rfl, det_mul,
    show g.1.det = (gdet g : k) from rfl, dl_mul_unit hv, dl_unit _ hv]
  rw [propext this, mul_left_comm, ← mul_assoc (ν _ : ℂ), Units.mul_inv, one_mul]

omit [MeasurableSpace k] [BorelSpace k] in
/- English proof (translation)
Use function extensionality and compare the values at `Y`. Rewrite using `[← std_left (inv_mem hg) Y]`. Simplify using `[omA, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hg), gdet]`.
-/
theorem omA_std {e : Fin n → Fin d} {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) : omA ν β g 1 (std ν ϖ c e) = std ν ϖ c e := by
  funext Y
  rw [← std_left (inv_mem hg) Y]
  simp [omA, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hg), gdet]

omit [MeasurableSpace k] [BorelSpace k] in
/- English proof (translation)
Use function extensionality and compare the values at `Y`. Rewrite using `[← std_left (inv_mem (invT_mem_KO hg)) Y, invT_inv_val, gdet, map_inv, ← gdet, gdet_invT, inv_inv]`. Simplify using `[omB, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hg), gdet]`.
-/
theorem omB_std {e : Fin n → Fin d} {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) : omB ν α g 1 (std ν ϖ c e) = std ν ϖ c e := by
  funext Y
  rw [← std_left (inv_mem (invT_mem_KO hg)) Y, invT_inv_val, gdet, map_inv, ← gdet, gdet_invT, inv_inv]
  simp [omB, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hg), gdet]

end PositivityTheory.ThKG.Std
