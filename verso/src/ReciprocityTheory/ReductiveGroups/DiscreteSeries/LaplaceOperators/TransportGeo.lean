import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.EquivariantL2Space
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.UniqueU
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.NChart
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.IsCompactUnitaryMat

noncomputable section

open Matrix Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.TransportGeo

open Formalism.QuantumDeterminants ReciprocityTheory.ChartRestriction.DS.Lap.Base ReciprocityTheory.ChartRestriction.DS.Lap.Base.N

variable {k r : ℕ}

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem uh_inv_eq {a : Mat k r} (ha : a ∈ UH (Hpk k r)) : (Hpk k r * aᴴ * Hpk k r) * a = 1 := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc aᴴ, ha', Hpk_sq]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem uh_det {a : Mat k r} (ha : a ∈ UH (Hpk k r)) : IsUnit a.det :=
  Matrix.isUnit_det_of_left_inverse (uh_inv_eq ha)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem uh_mul {a b : Mat k r} (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) :
    a * b ∈ UH (Hpk k r) := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  calc (a * b)ᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem uh_inv {a : Mat k r} (ha : a ∈ UH (Hpk k r)) : a⁻¹ ∈ UH (Hpk k r) := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have h1 : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a (uh_det ha)
  have h2 : (a⁻¹)ᴴ * aᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r
  calc (a⁻¹)ᴴ * Hpk k r * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * Hpk k r * a) * a⁻¹ := by rw [ha']
    _ = ((a⁻¹)ᴴ * aᴴ) * Hpk k r * (a * a⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem inv_mulVec {a : Mat k r} (ha : IsUnit a.det) {x y : Fin (2 * r + k + 1) → ℂ} {t : ℂ}
    (ht : t ≠ 0) (h : a *ᵥ x = t • y) : a⁻¹ *ᵥ y = t⁻¹ • x := by
  have := congrArg (fun v => t⁻¹ • (a⁻¹ *ᵥ v)) h
  simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul a ha, Matrix.one_mulVec,
    Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ ht, one_smul] at this
  exact this.symm

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem fix_iff {a : Mat k r} (ha : IsUnit a.det) {x y : Fin (2 * r + k + 1) → ℂ} {t : ℂ}
    (ht : t ≠ 0) (h : a *ᵥ x = t • y) (g : Mat k r) : g *ᵥ x = x ↔ (a * g * a⁻¹) *ᵥ y = y := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, inv_mulVec ha ht h, Matrix.mulVec_smul,
    Matrix.mulVec_smul]
  constructor
  · intro hg; rw [hg, h, smul_smul, inv_mul_cancel₀ ht, one_smul]
  · intro hg
    have h2 : a *ᵥ (g *ᵥ x) = a *ᵥ x := by
      rw [h, ← hg, smul_smul, mul_inv_cancel₀ ht, one_smul]
    have := congrArg (fun v => a⁻¹ *ᵥ v) h2
    simpa only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul a ha,
      Matrix.one_mul, Matrix.one_mulVec] using this

def Out (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := i.val < r ∨ r + k < i.val

def ColStd (X : Mat k r) : Prop := ∀ j, Out k r j → X *ᵥ bvec j = bvec j

def MidM (X : Mat k r) : Prop := ∀ i j, Out k r i ∨ Out k r j → X i j = if i = j then 1 else 0

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact.

Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem colStd_iff (X : Mat k r) : ColStd X ↔ ∀ a : Fin r,
    X *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ X *ᵥ bvec (esI k r a) = bvec (esI k r a) := by
  refine ⟨fun h a => ⟨h _ (Or.inl a.isLt), h _ (Or.inr ?_)⟩, fun h j hj => ?_⟩
  · have := a.isLt; simp only [esI]; omega
  · have := j.isLt
    rcases hj with hj | hj
    · exact (h ⟨j.val, hj⟩).1
    · have e : j = esI k r ⟨2 * r + k - j.val, by omega⟩ := Fin.ext (by simp only [esI]; omega)
      rw [e]; exact (h _).2

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem out_flip {i : Fin (2 * r + k + 1)} (h : Out k r i) : Out k r (flipB k r i) := by
  have := i.isLt
  unfold Out at *
  rw [flipB_val]; split_ifs <;> omega

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem ColStd.inv {X : Mat k r} (hX : X ∈ UH (Hpk k r)) (h : ColStd X) : ColStd X⁻¹ := fun j hj => by
  simpa using inv_mulVec (uh_det hX) one_ne_zero (y := bvec j) (by rw [h j hj, one_smul])

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem ColStd.mul {X Y : Mat k r} (hX : ColStd X) (hY : ColStd Y) : ColStd (X * Y) := fun j hj => by
  rw [← Matrix.mulVec_mulVec, hY j hj, hX j hj]

/- English proof (translation)
Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails.

Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem ColStd.midM {X : Mat k r} (hX : X ∈ UH (Hpk k r)) (h : ColStd X) : MidM X := by
  rintro i j (hi | hj)
  · have e : X = Hpk k r * (X⁻¹)ᴴ * Hpk k r := by
      rw [← Matrix.inv_eq_left_inv (uh_inv_eq (uh_inv hX)), Matrix.nonsing_inv_nonsing_inv _ (uh_det hX)]
    rw [e, mul_Hpk_apply, Hpk_mul_apply, conjTranspose_apply,
      StandardBasisEmbedding.col_of_fix (h.inv hX _ (out_flip hi))]
    by_cases hij : i = j
    · subst hij; simp only [if_true, star_one, mul_one]; unfold sgnB; split_ifs <;> simp
    · rw [if_neg hij, if_neg, star_zero, mul_zero, zero_mul]
      intro h2; exact hij (by rw [← flipB_flipB i, ← h2, flipB_flipB])
  · exact StandardBasisEmbedding.col_of_fix (h j hj) i

/- English proof (translation)
Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem MidM.mul {X Y : Mat k r} (hX : MidM X) (hY : MidM Y) : MidM (X * Y) := by
  rintro i j (hi | hj)
  · rw [Matrix.mul_apply, sum_eq_single i (fun c _ hc => by
      rw [hX i c (Or.inl hi), if_neg (Ne.symm hc), zero_mul]) (by simp), hX i i (Or.inl hi),
      if_pos rfl, one_mul, hY i j (Or.inl hi)]
  · rw [Matrix.mul_apply, sum_eq_single j (fun c _ hc => by
      rw [hY c j (Or.inr hj), if_neg hc, mul_zero]) (by simp), hY j j (Or.inr hj),
      if_pos rfl, mul_one, hX i j (Or.inr hj)]

/- English proof (translation)
Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem midM_blockW (h : Matrix (Fin k) (Fin k) ℂ) : MidM (Formalism.MainNotions.S.blockW k r h) := by
  rintro i j (hi | hj)
  · exact StandardBasisEmbedding.bw_row h j (by unfold Out at hi; unfold StandardBasisEmbedding.bl; omega)
  · exact StandardBasisEmbedding.bw_col h i (by unfold Out at hj; unfold StandardBasisEmbedding.bl; omega)

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem herm_bvec (j : Fin (2 * r + k + 1)) (v : Fin (2 * r + k + 1) → ℂ) (hj : Out k r j)
    (hv : inWb k r v) : herm (Hpk k r) (bvec j) v = 0 := by
  simp only [herm, bvec, Matrix.mulVec_single_one, dotProduct, Pi.star_apply, Matrix.col_apply]
  refine sum_eq_zero fun i _ => ?_
  by_cases hi : Out k r i
  · rw [hv i hi, star_zero, zero_mul]
  · rw [Hpk_apply, if_neg, mul_zero]
    rintro rfl
    exact hi (by simpa only [flipB_flipB] using out_flip hj)

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem herm_symm (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x y = star (herm (Hpk k r) y x) := by
  simp only [herm]
  rw [star_dotProduct, star_mulVec, Hpk_herm, dotProduct_mulVec]

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. A detailed English derivation is pending.
-/
theorem witt_one {x y : Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x) (hy : inWb k r y)
    (hn : herm (Hpk k r) x x = herm (Hpk k r) y y) (hα : herm (Hpk k r) x x ≠ herm (Hpk k r) x y) :
    ∃ b : Mat k r, b ∈ UH (Hpk k r) ∧ ColStd b ∧ b *ᵥ x = y := by
  set v := x - y with hv
  set α := herm (Hpk k r) x v with hαd
  have hsub : ∀ w, herm (Hpk k r) w v = herm (Hpk k r) w x - herm (Hpk k r) w y := fun w => by
    simp only [herm, hv, star_sub, sub_dotProduct]
  have hα0 : α ≠ 0 := by rw [hαd, hsub]; exact sub_ne_zero.mpr hα
  have hvW : inWb k r v := fun i hi => by simp [hv, hx i hi, hy i hi]
  have hvv : herm (Hpk k r) v v = α + star α := by
    have e : herm (Hpk k r) v v = herm (Hpk k r) x v - herm (Hpk k r) y v := by
      simp only [herm]; conv_lhs => rw [hv, Matrix.mulVec_sub, dotProduct_sub, ← hv]
    rw [e, hαd, hsub, hsub, star_sub, ← herm_symm x x, ← herm_symm y x, hn]; ring
  set R : Mat k r := vecMulVec v (star v) * Hpk k r with hR
  have hRv : ∀ w, R *ᵥ w = herm (Hpk k r) w v • v := fun w => by
    rw [hR, ← Matrix.mulVec_mulVec, Matrix.vecMulVec_mulVec, herm]; simp
  have hRH : Rᴴ * Hpk k r = Hpk k r * R := by
    rw [hR, conjTranspose_mul, Hpk_herm, conjTranspose_vecMulVec, star_star, Matrix.mul_assoc]
  have hRR : R * R = herm (Hpk k r) v v • R := by
    ext i j
    have h1 : (R * R) i j = (R *ᵥ (R *ᵥ bvec j)) i := by
      rw [Matrix.mulVec_mulVec]; simp [bvec]
    have h2 : R i j = (R *ᵥ bvec j) i := by simp [bvec]
    rw [h1, Matrix.smul_apply, h2, hRv (bvec j), Matrix.mulVec_smul, hRv v]
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  refine ⟨1 - α⁻¹ • R, ?_, fun j hj => ?_, ?_⟩
  · show (1 - α⁻¹ • R)ᴴ * Hpk k r * (1 - α⁻¹ • R) = Hpk k r
    have hs : star α ≠ 0 := star_ne_zero.mpr hα0
    rw [conjTranspose_sub, conjTranspose_one, conjTranspose_smul, Matrix.sub_mul, Matrix.one_mul,
      Matrix.smul_mul, hRH, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hRR, hvv, Matrix.mul_smul, smul_smul,
      smul_smul, star_inv₀]
    have e : α⁻¹ * (star α)⁻¹ * (α + star α) = (star α)⁻¹ + α⁻¹ := by field_simp
    rw [e, add_smul]; abel
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hRv, herm_bvec j v hj hvW]; simp
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hRv, ← hαd, smul_smul,
      inv_mul_cancel₀ hα0, one_smul, hv]; abel

/- English proof (translation)
Consider separately whether the proposition holds or fails. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem witt {x y : Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x) (hy : inWb k r y)
    (hn : herm (Hpk k r) x x = herm (Hpk k r) y y) (h0 : herm (Hpk k r) x x ≠ 0) :
    ∃ b : Mat k r, b ∈ UH (Hpk k r) ∧ ColStd b ∧ b *ᵥ x = y := by
  by_cases hα : herm (Hpk k r) x x = herm (Hpk k r) x y
  · have hny : inWb k r (-y) := fun i hi => by simp [hy i hi]
    have e1 : herm (Hpk k r) (-y) (-y) = herm (Hpk k r) y y := by simp [herm, Matrix.mulVec_neg]
    have e2 : herm (Hpk k r) x (-y) = -herm (Hpk k r) x y := by simp [herm]
    have e3 : herm (Hpk k r) (-y) y = -herm (Hpk k r) y y := by simp [herm, Matrix.mulVec_neg]
    have hne : ∀ t : ℂ, t ≠ 0 → t ≠ -t := fun t ht h => ht (by linear_combination h / 2)
    obtain ⟨b1, h1, c1, m1⟩ := witt_one hx hny (hn.trans e1.symm) (by rw [e2, ← hα]; exact hne _ h0)
    obtain ⟨b2, h2, c2, m2⟩ := witt_one hny hy e1 (by rw [e1, e3, ← hn]; exact hne _ h0)
    exact ⟨b2 * b1, uh_mul h2 h1, c2.mul c1, by rw [← Matrix.mulVec_mulVec, m1, m2]⟩
  · exact witt_one hx hy hn hα

def Lev0 (X : Mat k r) : Prop := ∀ i j, levB k r j < levB k r i → X i j = 0

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem Lev0.conj {a b X : Mat k r} (ha : Lev0 a) (hb : Lev0 b) (hX : X ∈ levF (levB k r) 0) :
    a * X * b ∈ levF (levB k r) 0 := by
  intro i j h
  rw [Matrix.mul_apply]
  refine sum_eq_zero fun d _ => ?_
  by_cases hd : levB k r j < levB k r d
  · rw [hb d j hd, mul_zero]
  · rw [Matrix.mul_apply, sum_eq_zero, zero_mul]
    intro c _
    by_cases hc : levB k r c < levB k r i
    · rw [ha i c hc, zero_mul]
    · rw [hX c d (by omega), mul_zero]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem MidM.lev0 {X : Mat k r} (hX : MidM X) : Lev0 X := by
  intro i j h
  rw [hX i j, if_neg (by rintro rfl; omega)]
  unfold levB at h; unfold Out; split_ifs at h <;> omega

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem conj_mem_N {a : Mat k r} (ha : a ∈ UH (Hpk k r)) (h1 : Lev0 a) (h2 : Lev0 a⁻¹) {m : Mat k r}
    (hm : m ∈ Nset k r) : a * m * a⁻¹ ∈ Nset k r := by
  rw [Nset_eq, mem_grpN_iff _ _ Hpk_sq] at hm ⊢
  refine ⟨?_, uh_mul (uh_mul ha hm.2) (uh_inv ha)⟩
  have := h1.conj h2 hm.1
  rwa [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_nonsing_inv _ (uh_det ha)] at this

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem herm_eq_Tz (z : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) z z = -((Tz k r z : ℝ) : ℂ) := by
  have h := congrArg Complex.im (herm_symm z z)
  apply Complex.ext
  · simp [Tz]
  · simp at h ⊢; linarith

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Clear the denominators using the available nonvanishing facts. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Replace the relevant objects with their definitions. Establish an intermediate fact.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Substitute using the available equality. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Replace the relevant objects with their definitions. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities.

Establish an intermediate fact. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Clear the denominators using the available nonvanishing facts. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Establish an intermediate fact. Clear the denominators using the available nonvanishing facts. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem conj_data {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {c c' : Fin r → ℂ}
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hc : ∀ a, c a ≠ 0)
    (hz' : inWb k r z') (hT' : 0 < Tz k r z') (hc' : ∀ a, c' a ≠ 0) :
    ∃ a : Mat k r, a ∈ UH (Hpk k r) ∧ IsUnit a.det ∧
      (∀ h, h ∈ UWset k r z ↔ a * h * a⁻¹ ∈ UWset k r z') ∧
      (∀ m, m ∈ Nset k r ↔ a * m * a⁻¹ ∈ Nset k r) ∧
      (∀ m ∈ Nset k r, Formalism.MainNotions.S.psiGen k r z' c' (a * m * a⁻¹) = Formalism.MainNotions.S.psiGen k r z c m) ∧
      (∀ g, Formalism.MainNotions.S.IsFrameW k r z g → ∃ g', Formalism.MainNotions.S.IsFrameW k r z' g' ∧
        ∀ h, a * (g * Formalism.MainNotions.S.blockW k r h * g⁻¹) * a⁻¹ = g' * Formalism.MainNotions.S.blockW k r h * g'⁻¹) := by
  set s : ℂ := ((Real.sqrt (Tz k r z) / Real.sqrt (Tz k r z') : ℝ) : ℂ) with hs
  have q1 := Real.sqrt_pos.mpr hT
  have q2 := Real.sqrt_pos.mpr hT'
  have hs0 : s ≠ 0 := by rw [hs]; exact_mod_cast (div_pos q1 q2).ne'
  obtain ⟨b, hb, hbc, hbz⟩ := witt (x := z) (y := s • z') hz (fun i hi => by simp [hz' i hi])
    (by
      have e : herm (Hpk k r) (s • z') (s • z') = s * s * herm (Hpk k r) z' z' := by
        simp only [herm, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
          smul_eq_mul, hs, Complex.star_def, Complex.conj_ofReal]; ring
      rw [e, herm_eq_Tz, herm_eq_Tz, hs]
      have : Real.sqrt (Tz k r z) / Real.sqrt (Tz k r z') *
          (Real.sqrt (Tz k r z) / Real.sqrt (Tz k r z')) * Tz k r z' = Tz k r z := by
        rw [div_mul_div_comm, Real.mul_self_sqrt hT.le, Real.mul_self_sqrt hT'.le]; field_simp
      rw [mul_neg]; exact_mod_cast congrArg Neg.neg this.symm)
    (by rw [herm_eq_Tz]; exact neg_ne_zero.mpr (by exact_mod_cast hT.ne'))
  let δ : ℕ → ℂ := fun p => s * ∏ j ∈ univ.filter (fun j : Fin r => p ≤ j.val), c j / c' j
  have hδ0 : ∀ p, δ p ≠ 0 := fun p =>
    mul_ne_zero hs0 (prod_ne_zero_iff.mpr fun j _ => div_ne_zero (hc j) (hc' j))
  have hδ : ∀ p : Fin r, δ p.val = δ (p.val + 1) * (c p / c' p) := fun p => by
    have : univ.filter (fun j : Fin r => p.val ≤ j.val) =
        insert p (univ.filter fun j : Fin r => p.val + 1 ≤ j.val) := by
      ext j; simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]; omega
    simp only [δ]
    rw [this, prod_insert (by simp)]; ring
  have hδr : ∀ p : Fin r, ¬ p.val + 1 < r → δ (p.val + 1) = s := fun p h => by
    simp only [δ]
    rw [filter_eq_empty_iff.mpr (fun j _ => by have := j.isLt; omega), prod_empty, mul_one]
  let dv : Fin (2 * r + k + 1) → ℂ := fun i =>
    if i.val < r then δ i.val else if r + k < i.val then (star (δ (2 * r + k - i.val)))⁻¹ else 1
  have hdv0 : ∀ i, dv i ≠ 0 := fun i => by
    simp only [dv]; split_ifs
    · exact hδ0 _
    · exact inv_ne_zero (star_ne_zero.mpr (hδ0 _))
    · exact one_ne_zero
  have hdmid : ∀ i, ¬ Out k r i → dv i = 1 := fun i hi => by
    unfold Out at hi; simp only [dv]; rw [if_neg (by omega), if_neg (by omega)]
  set d : Mat k r := diagonal dv with hd
  have hdU : d ∈ UH (Hpk k r) := by
    show dᴴ * Hpk k r * d = Hpk k r
    ext i j
    rw [hd, diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, Hpk_apply]
    split_ifs with h
    · subst h
      have hi := i.isLt
      have : star (dv i) * dv (flipB k r i) = 1 := by
        simp only [dv, flipB_val]
        split_ifs <;> first
          | omega
          | (rw [show 2 * r + k - (2 * r + k - i.val) = i.val by omega]
             exact mul_inv_cancel₀ (star_ne_zero.mpr (hδ0 _)))
          | (rw [star_inv₀, star_star]; exact inv_mul_cancel₀ (hδ0 _))
          | simp
      rw [Pi.star_apply]; linear_combination sgnB k r i * this
    · simp
  have hdi : d⁻¹ = diagonal fun i => (dv i)⁻¹ := Matrix.inv_eq_left_inv (by
    rw [hd, diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact inv_mul_cancel₀ (hdv0 i))
  have hbM := hbc.midM hb
  have hbiM := (hbc.inv hb).midM (uh_inv hb)
  have haU : d * b ∈ UH (Hpk k r) := uh_mul hdU hb
  have had := uh_det haU
  have hai : (d * b)⁻¹ = b⁻¹ * d⁻¹ := Matrix.mul_inv_rev d b
  have hcol : ∀ j, Out k r j → (d * b) *ᵥ bvec j = dv j • bvec j := fun j hj => by
    rw [← Matrix.mulVec_mulVec, hbc j hj, hd]
    funext i; by_cases h : i = j <;> simp [bvec, Matrix.mulVec_diagonal, h]
  have haz : (d * b) *ᵥ z = s • z' := by
    rw [← Matrix.mulVec_mulVec, hbz, hd]
    funext i
    rw [Matrix.mulVec_diagonal]
    by_cases hi : Out k r i
    · simp [hz' i hi]
    · rw [hdmid i hi, one_mul]
  have l1 : Lev0 (d * b) := fun i j h => by rw [hd, Matrix.diagonal_mul, hbM.lev0 i j h, mul_zero]
  have l2 : Lev0 (d * b)⁻¹ := fun i j h => by
    rw [hai, hdi, Matrix.mul_diagonal, hbiM.lev0 i j h, zero_mul]
  have hback : ∀ X : Mat k r, (d * b)⁻¹ * (d * b * X * (d * b)⁻¹) * (d * b)⁻¹⁻¹ = X := fun X => by
    rw [Matrix.nonsing_inv_nonsing_inv _ had]
    simp only [Matrix.mul_assoc (d * b), Matrix.nonsing_inv_mul_cancel_left _ _ had]
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ had, Matrix.mul_one]
  refine ⟨d * b, haU, had, fun h => ?_, fun m => ⟨conj_mem_N haU l1 l2, fun hm => ?_⟩,
    fun m _ => ?_, fun g hg => ?_⟩
  · have hfix : ColStd h ↔ ColStd (d * b * h * (d * b)⁻¹) :=
      forall_congr' fun j => imp_congr_right fun hj => fix_iff had (hdv0 j) (hcol j hj) h
    show (h ∈ UH _ ∧ _ ∧ _) ↔ (_ ∈ UH _ ∧ _ ∧ _)
    rw [← colStd_iff, ← colStd_iff, ← hfix, ← fix_iff had hs0 haz h]
    refine and_congr_left fun _ => ⟨fun hh => uh_mul (uh_mul haU hh) (uh_inv haU), fun hh => ?_⟩
    rw [← hback h]
    exact uh_mul (uh_mul (uh_inv haU) hh) (uh_inv (uh_inv haU))
  · rw [← hback m]
    exact conj_mem_N (uh_inv haU) l2 (by rwa [Matrix.nonsing_inv_nonsing_inv _ had]) hm
  · have hrow : ∀ (p : Fin r) (v : Fin (2 * r + k + 1) → ℂ),
        ((d * b) *ᵥ v) (eI k r p) = δ p.val * v (eI k r p) := fun p v => by
      have ho : Out k r (eI k r p) := Or.inl p.isLt
      rw [← Matrix.mulVec_mulVec, hd, Matrix.mulVec_diagonal]
      simp only [Matrix.mulVec, dotProduct, fun j => hbM (eI k r p) j (Or.inl ho), ite_mul, one_mul,
        zero_mul, sum_ite_eq, mem_univ, if_true]
      simp [dv, eI]
    unfold Formalism.MainNotions.S.psiGen
    congr 4
    refine sum_congr rfl fun p _ => ?_
    have hcp := hc' p
    unfold Formalism.MainNotions.S.ellA
    split_ifs with h
    · have ho : Out k r (eI k r ⟨p.val + 1, h⟩) := Or.inl h
      have e1 : ∀ X : Mat k r, X (eI k r p) (eI k r ⟨p.val + 1, h⟩) =
          (X *ᵥ bvec (eI k r ⟨p.val + 1, h⟩)) (eI k r p) := fun X => by simp [bvec]
      have e2 : dv (eI k r ⟨p.val + 1, h⟩) = δ (p.val + 1) := by simp [dv, eI, h]
      rw [e1 (d * b * m * (d * b)⁻¹), e1 m, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        inv_mulVec had (hdv0 _) (hcol _ ho), Matrix.mulVec_smul, hrow, e2, hδ p]
      have := hδ0 (p.val + 1)
      simp only [Pi.smul_apply, smul_eq_mul]; field_simp
    · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, inv_mulVec had hs0 haz,
        Matrix.mulVec_smul, hrow, hδ p, hδr p h]
      simp only [Pi.smul_apply, smul_eq_mul]; field_simp
  · obtain ⟨hgU, hgc, hgz⟩ := hg
    rw [← colStd_iff] at hgc
    refine ⟨b * g, ⟨uh_mul hb hgU, (colStd_iff _).mp (hbc.mul hgc), ?_⟩, fun h => ?_⟩
    · have e : ((Real.sqrt (Tz k r z') : ℝ) : ℂ) = s⁻¹ * ((Real.sqrt (Tz k r z) : ℝ) : ℂ) := by
        rw [hs]; push_cast
        have : ((Real.sqrt (Tz k r z) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast q1.ne'
        field_simp
      rw [e, ← smul_smul, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, hgz, hbz, smul_smul,
        inv_mul_cancel₀ hs0, one_smul]
    · set Y := b * (g * Formalism.MainNotions.S.blockW k r h * g⁻¹) * b⁻¹ with hY
      have hYM : MidM Y := (hbM.mul (((hgc.midM hgU).mul (midM_blockW h)).mul
        ((hgc.inv hgU).midM (uh_inv hgU)))).mul hbiM
      have hcomm : d * Y = Y * d := by
        ext i j
        rw [hd, Matrix.diagonal_mul, Matrix.mul_diagonal]
        by_cases ho : Out k r i ∨ Out k r j
        · rw [hYM i j ho]; split_ifs with e
          · rw [e, mul_comm]
          · simp
        · rw [hdmid i (fun h => ho (Or.inl h)), hdmid j (fun h => ho (Or.inr h)), mul_comm]
      calc d * b * (g * Formalism.MainNotions.S.blockW k r h * g⁻¹) * (d * b)⁻¹ = d * Y * d⁻¹ := by
            rw [hai, hY]; simp only [Matrix.mul_assoc]
        _ = Y := by rw [hcomm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (uh_det hdU), Matrix.mul_one]
        _ = _ := by rw [hY, Matrix.mul_inv_rev]; simp only [Matrix.mul_assoc]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_UJ_allPos {h : Matrix (Fin k) (Fin k) ℂ} :
    h ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k) ↔ hᴴ * h = 1 := by
  show hᴴ * Formalism.REAL.Jm (Formalism.MainNotions.S.allPos k) * h = Formalism.REAL.Jm (Formalism.MainNotions.S.allPos k) ↔ _
  have : Formalism.REAL.Jm (Formalism.MainNotions.S.allPos k) = 1 := by simp [Formalism.REAL.Jm, Formalism.MainNotions.S.allPos]
  rw [this, Matrix.mul_one]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem frame_mulVec {z : Fin (2 * r + k + 1) → ℂ} {g : Mat k r} (hg : Formalism.MainNotions.S.IsFrameW k r z g)
    (hT : 0 < Tz k r z) : g *ᵥ z0 k r = (((Real.sqrt (Tz k r z) : ℝ) : ℂ))⁻¹ • z := by
  have hs : ((Real.sqrt (Tz k r z) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hT).ne'
  have := congrArg (fun v => (((Real.sqrt (Tz k r z) : ℝ) : ℂ))⁻¹ • v) hg.2.2
  simp only [Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hs, one_smul] at this
  exact this

/- English proof (translation)
Establish an intermediate fact. Supply the required witnesses or components.
-/
theorem exists_blockW {y : Mat k r} (hy : y ∈ UH (Hpk k r)) (hc : ColStd y)
    (h0 : y *ᵥ z0 k r = z0 k r) :
    ∃ h₀ ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k), y = Formalism.MainNotions.S.blockW k r h₀ := by
  have hm : y ∈ UWset k r (z0 k r) := ⟨hy, (colStd_iff y).mp hc, h0⟩
  exact ⟨StandardBasisEmbedding.blk y, mem_UJ_allPos.mpr (Matrix.mem_unitaryGroup_iff'.mp (StandardBasisEmbedding.blk_unitary hm)),
    StandardBasisEmbedding.eq_blockW hm⟩

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem uw_eq_frame {z : Fin (2 * r + k + 1) → ℂ} (hT : 0 < Tz k r z) {g : Mat k r}
    (hg : Formalism.MainNotions.S.IsFrameW k r z g) {h : Mat k r} (hh : h ∈ UWset k r z) :
    ∃ h₀ ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k), h = g * Formalism.MainNotions.S.blockW k r h₀ * g⁻¹ := by
  have hd := uh_det hg.1
  have hgc := (colStd_iff g).mpr hg.2.1
  have hs : (((Real.sqrt (Tz k r z) : ℝ) : ℂ))⁻¹ ≠ 0 :=
    inv_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr hT).ne')
  have e : g * (g⁻¹ * h * g) * g⁻¹ = h := by
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd,
      Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  obtain ⟨h₀, h1, h2⟩ := exists_blockW (uh_mul (uh_mul (uh_inv hg.1) hh.1) hg.1)
    (((hgc.inv hg.1).mul ((colStd_iff h).mpr hh.2.1)).mul hgc)
    ((fix_iff hd hs (frame_mulVec hg hT) _).mpr (by rw [e]; exact hh.2.2))
  exact ⟨h₀, h1, by rw [← h2, e]⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Introduce a local definition for the expression.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem pi_conj {k r : ℕ} {u : Fin k → ℝ}
    {Vp Vp' : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [NormedAddCommGroup Vp']
    [InnerProductSpace ℂ Vp'] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mat k r → (Vp →L[ℂ] Vp)}
    {π' : Mat k r → (Vp' →L[ℂ] Vp')} {a : Mat k r} (ha : IsUnit a.det)
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hz' : inWb k r z') (hT' : 0 < Tz k r z')
    (hUW : ∀ h, h ∈ UWset k r z ↔ a * h * a⁻¹ ∈ UWset k r z')
    (hfr : ∀ g, Formalism.MainNotions.S.IsFrameW k r z g → ∃ g', Formalism.MainNotions.S.IsFrameW k r z' g' ∧
      ∀ h, a * (g * Formalism.MainNotions.S.blockW k r h * g⁻¹) * a⁻¹ = g' * Formalism.MainNotions.S.blockW k r h * g'⁻¹)
    (hπ : Formalism.MainNotions.S.IsHCTypeW k r z u π) (hπ' : Formalism.MainNotions.S.IsHCTypeW k r z' u π') :
    ∃ U : Vp ≃ₗᵢ[ℂ] Vp', ∀ h ∈ UWset k r z, ∀ ξ : Vp, π' (a * h * a⁻¹) (U ξ) = U (π h ξ) := by
  obtain ⟨g, hg, hρ⟩ := hπ
  obtain ⟨g2, hg2, hρ2⟩ := hπ'
  obtain ⟨g1, hg1, hconj⟩ := hfr g hg
  obtain ⟨U0, hU0⟩ := HW.hcTypeU_unique _ _ hρ hρ2
  have hd2 := uh_det hg2.1
  have hs : (((Real.sqrt (Tz k r z') : ℝ) : ℂ))⁻¹ ≠ 0 :=
    inv_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr hT').ne')
  obtain ⟨h0, hh0, e0⟩ := exists_blockW (uh_mul (uh_inv hg2.1) hg1.1)
    ((((colStd_iff g2).mpr hg2.2.1).inv hg2.1).mul ((colStd_iff g1).mpr hg1.2.1))
    (by rw [← Matrix.mulVec_mulVec, frame_mulVec hg1 hT', Matrix.mulVec_smul,
      inv_mulVec hd2 hs (frame_mulVec hg2 hT'), smul_smul, mul_inv_cancel₀ hs, one_smul])
  have u1 : h0ᴴ * h0 = 1 := mem_UJ_allPos.mp hh0
  have u2 : h0 * h0ᴴ = 1 := mul_eq_one_comm.mp u1
  have hh0' : h0ᴴ ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k) :=
    mem_UJ_allPos.mpr (by rw [conjTranspose_conjTranspose, u2])
  have hmul : ∀ x ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k), ∀ y ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k),
      x * y ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k) := fun x hx y hy => mem_UJ_allPos.mpr (by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc xᴴ, mem_UJ_allPos.mp hx,
      Matrix.one_mul, mem_UJ_allPos.mp hy])
  set ρ : Matrix (Fin k) (Fin k) ℂ → (Vp' →L[ℂ] Vp') :=
    fun h => π' (g2 * Formalism.MainNotions.S.blockW k r h * g2⁻¹) with hρd
  obtain ⟨-, -, ⟨⟨r1, rm⟩, riso, -⟩, -⟩ := hρ2
  have rm' : ∀ x ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k), ∀ y ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k),
      ∀ v, ρ x (ρ y v) = ρ (x * y) v := fun x hx y hy v => by rw [rm x hx y hy]; rfl
  let W : Vp' ≃ₗᵢ[ℂ] Vp' :=
    { toFun := ρ h0
      invFun := ρ h0ᴴ
      map_add' := map_add _
      map_smul' := map_smul _
      left_inv := fun v => by
        show ρ h0ᴴ (ρ h0 v) = v
        rw [rm' _ hh0' _ hh0, u1, r1]; rfl
      right_inv := fun v => by
        show ρ h0 (ρ h0ᴴ v) = v
        rw [rm' _ hh0 _ hh0', u2, r1]; rfl
      norm_map' := riso h0 hh0 }
  refine ⟨U0.trans W, fun h hh ξ => ?_⟩
  obtain ⟨h1, hh1, rfl⟩ := uw_eq_frame hT hg hh
  have eg1 : g1 = g2 * Formalism.MainNotions.S.blockW k r h0 := by
    rw [← e0, Matrix.mul_nonsing_inv_cancel_left _ _ hd2]
  have einv : (Formalism.MainNotions.S.blockW k r h0)⁻¹ = Formalism.MainNotions.S.blockW k r h0ᴴ :=
    Matrix.inv_eq_left_inv (by rw [← StandardBasisEmbedding.blockW_mul, u1, StandardBasisEmbedding.blockW_one])
  have e1 : g1 * Formalism.MainNotions.S.blockW k r h1 * g1⁻¹ =
      g2 * Formalism.MainNotions.S.blockW k r (h0 * h1 * h0ᴴ) * g2⁻¹ := by
    rw [eg1, Matrix.mul_inv_rev, einv, StandardBasisEmbedding.blockW_mul, StandardBasisEmbedding.blockW_mul]
    simp only [Matrix.mul_assoc]
  rw [hconj, e1]
  show ρ (h0 * h1 * h0ᴴ) (ρ h0 (U0 ξ)) = ρ h0 (U0 (π (g * Formalism.MainNotions.S.blockW k r h1 * g⁻¹) ξ))
  rw [← hU0 h1 hh1 ξ, rm' _ (hmul _ (hmul _ hh0 _ hh1) _ hh0') _ hh0, rm' _ hh0 _ hh1,
    Matrix.mul_assoc, u1, Matrix.mul_one]

end ReciprocityTheory.ChartRestriction.DS.Lap.TransportGeo
