import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LagCoi
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LagNeZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CoiConjSingle

open Polynomial Matrix IsLocalRing TensorProduct

/- English proof (translation)
Introduce `F _ ι _ _ a P ha hP`. Establish `hu : ∀ i j, i ≠ j → IsUnit (a i - a j)` using `fun i j hij => (sub_ne_zero.2 (fun h => hij (ha h))).isUnit`. Establish `hCH : aeval P (∏ i, (X - C (a i))) = 0`. Rewrite using `[← hP]`. Conclude with `Matrix.aeval_self_charpoly P`.

Take `⟨hcoi, -, -, hcomm⟩` from `UpperTheory.V.AlgebraTools.lag_coi a P hu hCH`. Establish `hne` using `UpperTheory.V.AlgebraTools.lag_ne_zero a P hu (by`. Rewrite using `[hP, Polynomial.map_prod]`. Use the proof step `simp)`. Take `⟨g, hg⟩` from `UpperTheory.V.AlgebraTools.coi_conj_single _ hcoi hne`.

Establish `hpoly : ∀ i, ∃ q : F[X], UpperTheory.V.AlgebraTools.lag a P i = aeval P q` using `fun i => ⟨_ • _, by rw [UpperTheory.V.AlgebraTools.lag, map_smul]⟩`. Use `set f := UpperTheory.V.AlgebraTools.lag a P with hf`. Establish `hinj : ∀ A B : Matrix ι ι F, (g : Matrix ι ι F) * A * ((g⁻¹ : GL ι F) : Matrix ι ι F) = (g : Matrix ι ι F) * B * ((g⁻¹ : GL ι F) : Matrix ι ι F) → A = B`. Introduce `A B h`. Conclude with `(Units.mul_right_inj g).1 ((Units.mul_left_inj g⁻¹).1 h)`.

Establish `hmul : ∀ A B : Matrix ι ι F, (g : Matrix ι ι F) * (A * B) * ((g⁻¹ : GL ι F) : Matrix ι ι F) = ((g : Matrix ι ι F) * A * ((g⁻¹ : GL ι F) : Matrix ι ι F)) * ((g : Matrix ι ι F) * B * ((g⁻¹ : GL ι F) : Matrix ι ι F))`. Introduce `A B`. Simplify using `only [mul_assoc, Units.inv_mul_cancel_left]`. Establish `hspan : ∀ Y, P * Y = Y * P → ∃ c : ι → F, Y = ∑ i, c i • f i`. Introduce `Y hY`.

Use `set Z := (g : Matrix ι ι F) * Y * ((g⁻¹ : GL ι F) : Matrix ι ι F) with hZ`. Use `⟨fun i => Z i i, hinj _ _ ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul, hg]`. Rewrite using `[← hZ]`.

Use extensionality with `i j`. Rewrite using `[Matrix.sum_apply, Finset.sum_eq_single i]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules.

Establish `h1 : Z * single j j (1 : F) = single j j 1 * Z`. Rewrite using `[← hg j, hZ, ← hmul, ← hmul, (hcomm Y j hY.symm).eq]`. Establish `h2` using `congrFun (congrFun h1 i) j`. Rewrite `h2` using `[Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne _ _ _ _ _ hij]`. Rewrite `h2` using `[mul_one]`.

Simplify using `[hij, h2]`. Introduce `b _ hb`. Simplify using `[hb]`. Simplify using the standard rewrite rules. Establish `hq : ∀ Y, P * Y = Y * P → ∃ q : F[X], Y = aeval P q`.

Introduce `Y hY`. Take `⟨c, rfl⟩` from `hspan Y hY`. Use `choose q hq using hpoly`. Conclude with `⟨∑ i, c i • q i, by simp [hq]⟩`. Use `⟨?_, hq⟩` and prove the remaining obligations.

Establish `hli : LinearIndependent F f`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc j`. Establish `h1 : (∑ i, c i • f i) * f j = c j • f j`. Rewrite using `[Finset.sum_mul, Finset.sum_eq_single j]`.

Rewrite using `[smul_mul_assoc, (hcoi.idem j).eq]`. Introduce `b _ hb`. Rewrite using `[smul_mul_assoc, hcoi.ortho hb, smul_zero]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[hc, zero_mul]`.

Conclude with `(smul_eq_zero.1 h1.symm).resolve_right (hne j)`. Establish `hker : LinearMap.ker (LinearMap.mulLeft F P - LinearMap.mulRight F P) = Submodule.span F (Set.range f)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `Y hY`. Establish `hY' : P * Y = Y * P` using `by simpa [sub_eq_zero] using hY`.

Take `⟨c, rfl⟩` from `hspan Y hY'`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Use `(hcomm P i (Commute.refl P)).eq` as an intermediate fact.

Simplify `this` using `[sub_eq_zero]`. Rewrite using `[hker, finrank_span_eq_card hli]`.
-/
theorem UpperTheory.V.AlgebraTools.centraliser_rank :
    ∀ {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι → F) (P : Matrix ι ι F), Function.Injective a → P.charpoly = ∏ i, (X - C (a i)) → Module.finrank F (LinearMap.ker (LinearMap.mulLeft F P - LinearMap.mulRight F P)) = Fintype.card ι ∧ ∀ Y, P * Y = Y * P → ∃ q : F[X], Y = aeval P q := by
  intro F _ ι _ _ a P ha hP
  have hu : ∀ i j, i ≠ j → IsUnit (a i - a j) := fun i j hij =>
    (sub_ne_zero.2 (fun h => hij (ha h))).isUnit
  have hCH : aeval P (∏ i, (X - C (a i))) = 0 := by
    rw [← hP]; exact Matrix.aeval_self_charpoly P
  obtain ⟨hcoi, -, -, hcomm⟩ := UpperTheory.V.AlgebraTools.lag_coi a P hu hCH
  have hne := UpperTheory.V.AlgebraTools.lag_ne_zero a P hu (by
    rw [hP, Polynomial.map_prod]; simp)
  obtain ⟨g, hg⟩ := UpperTheory.V.AlgebraTools.coi_conj_single _ hcoi hne
  have hpoly : ∀ i, ∃ q : F[X], UpperTheory.V.AlgebraTools.lag a P i = aeval P q := fun i =>
    ⟨_ • _, by rw [UpperTheory.V.AlgebraTools.lag, map_smul]⟩
  set f := UpperTheory.V.AlgebraTools.lag a P with hf
  have hinj : ∀ A B : Matrix ι ι F, (g : Matrix ι ι F) * A * ((g⁻¹ : GL ι F) : Matrix ι ι F) =
      (g : Matrix ι ι F) * B * ((g⁻¹ : GL ι F) : Matrix ι ι F) → A = B := by
    intro A B h
    exact (Units.mul_right_inj g).1 ((Units.mul_left_inj g⁻¹).1 h)
  have hmul : ∀ A B : Matrix ι ι F, (g : Matrix ι ι F) * (A * B) * ((g⁻¹ : GL ι F) : Matrix ι ι F) =
      ((g : Matrix ι ι F) * A * ((g⁻¹ : GL ι F) : Matrix ι ι F)) *
      ((g : Matrix ι ι F) * B * ((g⁻¹ : GL ι F) : Matrix ι ι F)) := by
    intro A B
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  have hspan : ∀ Y, P * Y = Y * P → ∃ c : ι → F, Y = ∑ i, c i • f i := by
    intro Y hY
    set Z := (g : Matrix ι ι F) * Y * ((g⁻¹ : GL ι F) : Matrix ι ι F) with hZ
    refine ⟨fun i => Z i i, hinj _ _ ?_⟩
    rw [Finset.mul_sum, Finset.sum_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, hg]
    rw [← hZ]
    ext i j
    rw [Matrix.sum_apply, Finset.sum_eq_single i]
    · by_cases hij : i = j
      · subst hij; simp
      · have h1 : Z * single j j (1 : F) = single j j 1 * Z := by
          rw [← hg j, hZ, ← hmul, ← hmul, (hcomm Y j hY.symm).eq]
        have h2 := congrFun (congrFun h1 i) j
        rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne _ _ _ _ _ hij] at h2
        rw [mul_one] at h2
        simp [hij, h2]
    · intro b _ hb
      simp [hb]
    · simp
  have hq : ∀ Y, P * Y = Y * P → ∃ q : F[X], Y = aeval P q := by
    intro Y hY
    obtain ⟨c, rfl⟩ := hspan Y hY
    choose q hq using hpoly
    exact ⟨∑ i, c i • q i, by simp [hq]⟩
  refine ⟨?_, hq⟩
  have hli : LinearIndependent F f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h1 : (∑ i, c i • f i) * f j = c j • f j := by
      rw [Finset.sum_mul, Finset.sum_eq_single j]
      · rw [smul_mul_assoc, (hcoi.idem j).eq]
      · intro b _ hb
        rw [smul_mul_assoc, hcoi.ortho hb, smul_zero]
      · simp
    rw [hc, zero_mul] at h1
    exact (smul_eq_zero.1 h1.symm).resolve_right (hne j)
  have hker : LinearMap.ker (LinearMap.mulLeft F P - LinearMap.mulRight F P) =
      Submodule.span F (Set.range f) := by
    apply le_antisymm
    · intro Y hY
      have hY' : P * Y = Y * P := by simpa [sub_eq_zero] using hY
      obtain ⟨c, rfl⟩ := hspan Y hY'
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have := (hcomm P i (Commute.refl P)).eq
      simpa [sub_eq_zero] using this
  rw [hker, finrank_span_eq_card hli]
