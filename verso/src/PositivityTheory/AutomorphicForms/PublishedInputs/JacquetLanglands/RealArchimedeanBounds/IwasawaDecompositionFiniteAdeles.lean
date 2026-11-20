import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.ATrans

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.IwasawaDecompositionLemmas

/- English proof (translation)
Simplify using `[Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hX, hY]`.
-/
theorem ut_mul {R : Type} [CommRing R] {X Y : GL (Fin 2) R} (hX : (X : Matrix (Fin 2) (Fin 2) R) 1 0 = 0)
    (hY : (Y : Matrix (Fin 2) (Fin 2) R) 1 0 = 0) : ((X * Y : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := by
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hX, hY]

/- English proof (translation)
Establish `hd : IsUnit ((p : Matrix (Fin 2) (Fin 2) R) 0 0 * (p : Matrix (Fin 2) (Fin 2) R) 1 1)`. Use `(Matrix.GeneralLinearGroup.det p).isUnit` as an intermediate fact. Rewrite `this` using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h, mul_zero, sub_zero]`. Then use the resulting hypothesis. Take `⟨a, ha⟩` from `isUnit_of_mul_isUnit_left hd`. Take `⟨d, hdd⟩` from `isUnit_of_mul_isUnit_right hd`.

Use `⟨d, a * d⁻¹, (p : Matrix (Fin 2) (Fin 2) R) 0 1 * ((d⁻¹ : Rˣ) : R), ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_two, ha, hdd, h] <;>`. Rewrite using `[← hdd, mul_left_comm, Units.mul_inv, mul_one]`.
-/
theorem ut_eq {R : Type} [CommRing R] (p : GL (Fin 2) R) (h : (p : Matrix (Fin 2) (Fin 2) R) 1 0 = 0) :
    ∃ (z t : Rˣ) (x : R), p = Matrix.GeneralLinearGroup.scalar (Fin 2) z * aff t x := by
  have hd : IsUnit ((p : Matrix (Fin 2) (Fin 2) R) 0 0 * (p : Matrix (Fin 2) (Fin 2) R) 1 1) := by
    have := (Matrix.GeneralLinearGroup.det p).isUnit
    rwa [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h, mul_zero, sub_zero] at this
  obtain ⟨a, ha⟩ := isUnit_of_mul_isUnit_left hd
  obtain ⟨d, hdd⟩ := isUnit_of_mul_isUnit_right hd
  refine ⟨d, a * d⁻¹, (p : Matrix (Fin 2) (Fin 2) R) 0 1 * ((d⁻¹ : Rˣ) : R), ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_two, ha, hdd, h] <;>
    rw [← hdd, mul_left_comm, Units.mul_inv, mul_one]

def LK {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (m : GL (Fin 2) K) : Prop :=
  (∀ i j, v ((m : Matrix (Fin 2) (Fin 2) K) i j) ≤ 1) ∧ ∀ i j, v (((m⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j) ≤ 1

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun i j => by fin_cases i <;> fin_cases j <;> simp, fun i j => by fin_cases i <;> fin_cases j <;> simp⟩`.
-/
theorem LK_one {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) : LK v 1 :=
  ⟨fun i j => by fin_cases i <;> fin_cases j <;> simp, fun i j => by fin_cases i <;> fin_cases j <;> simp⟩

/- English proof (translation)
Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]`. Apply the tactic sequence `refine (v.map_add _ _).trans (max_le ?_ ?_) <;> rw [map_mul] <;> exact mul_le_one' (hm.1 _ _) (hn.1 _ _)`. Rewrite using `[mul_inv_rev, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]`. Apply the tactic sequence `refine (v.map_add _ _).trans (max_le ?_ ?_) <;> rw [map_mul] <;> exact mul_le_one' (hn.2 _ _) (hm.2 _ _)`.
-/
theorem LK_mul {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {m n : GL (Fin 2) K}
    (hm : LK v m) (hn : LK v n) : LK v (m * n) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    refine (v.map_add _ _).trans (max_le ?_ ?_) <;> rw [map_mul] <;> exact mul_le_one' (hm.1 _ _) (hn.1 _ _)
  · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    refine (v.map_add _ _).trans (max_le ?_ ?_) <;> rw [map_mul] <;> exact mul_le_one' (hn.2 _ _) (hm.2 _ _)

/- English proof (translation)
Establish `hdet : (b : Matrix (Fin 2) (Fin 2) K).det ≠ 0`. Rewrite using `[← Matrix.GeneralLinearGroup.val_det_apply]`. Conclude with `Units.ne_zero _`. Rewrite `hdet` using `[Matrix.det_fin_two]`. Use `set γ := (b : Matrix (Fin 2) (Fin 2) K) 1 0 with hγ`.

Use `set δ := (b : Matrix (Fin 2) (Fin 2) K) 1 1 with hδ`. Distinguish the cases in `h : v γ ≤ v δ`. Establish `hδ0 : δ ≠ 0`. Introduce `h0`. Establish `h1 : γ = 0`.

Rewrite `h` using `[h0, map_zero]`. Conclude with `(Valuation.zero_iff v).1 (le_antisymm h zero_le)`. Apply `hdet` to reduce the goal to its premises. Rewrite using `[h0, h1]`. Expand and normalize the polynomial expressions, which then agree.

Apply the tactic sequence `let k : GL (Fin 2) K := ⟨!![1, 0; γ / δ, 1], !![1, 0; -(γ / δ), 1], by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩`. Use `⟨b * k⁻¹, k, ?_, ⟨fun i j => ?_, fun i j => ?_⟩, (inv_mul_cancel_right b k).symm⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((b : Matrix (Fin 2) (Fin 2) K) * !![1, 0; -(γ / δ), 1]) 1 0 = 0`. Simplify using `only [Matrix.mul_apply, Fin.sum_univ_two]`. Simplify using `[← hγ, ← hδ]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [k]`. Conclude with `div_le_one_of_le₀ h zero_le`. Apply the tactic sequence `change v ((!![1, 0; -(γ / δ), 1] : Matrix (Fin 2) (Fin 2) K) i j) ≤ 1 fin_cases i <;> fin_cases j <;> simp`.

Conclude with `div_le_one_of_le₀ h zero_le`. Establish `hlt : v δ < v γ` using `lt_of_not_ge h`. Establish `hγ0 : γ ≠ 0`. Introduce `h0`. Rewrite `hlt` using `[h0, map_zero]`.

Conclude with `not_lt_zero hlt`. Apply the tactic sequence `let k : GL (Fin 2) K := ⟨!![0, 1; 1, δ / γ], !![-(δ / γ), 1; 1, 0], by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩`. Use `⟨b * k⁻¹, k, ?_, ⟨fun i j => ?_, fun i j => ?_⟩, (inv_mul_cancel_right b k).symm⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((b : Matrix (Fin 2) (Fin 2) K) * !![-(δ / γ), 1; 1, 0]) 1 0 = 0`. Simplify using `only [Matrix.mul_apply, Fin.sum_univ_two]`.

Simplify using `[← hγ, ← hδ]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [k]`. Conclude with `div_le_one_of_le₀ hlt.le zero_le`.

Apply the tactic sequence `change v ((!![-(δ / γ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) i j) ≤ 1 fin_cases i <;> fin_cases j <;> simp`. Conclude with `div_le_one_of_le₀ hlt.le zero_le`.
-/
theorem loc_iw {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (b : GL (Fin 2) K) :
    ∃ p k : GL (Fin 2) K, (p : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ LK v k ∧ b = p * k := by
  have hdet : (b : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
  rw [Matrix.det_fin_two] at hdet
  set γ := (b : Matrix (Fin 2) (Fin 2) K) 1 0 with hγ
  set δ := (b : Matrix (Fin 2) (Fin 2) K) 1 1 with hδ
  by_cases h : v γ ≤ v δ
  · have hδ0 : δ ≠ 0 := by
      intro h0
      have h1 : γ = 0 := by
        rw [h0, map_zero] at h
        exact (Valuation.zero_iff v).1 (le_antisymm h zero_le)
      apply hdet; rw [h0, h1]; ring
    let k : GL (Fin 2) K := ⟨!![1, 0; γ / δ, 1], !![1, 0; -(γ / δ), 1],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
    refine ⟨b * k⁻¹, k, ?_, ⟨fun i j => ?_, fun i j => ?_⟩, (inv_mul_cancel_right b k).symm⟩
    · change ((b : Matrix (Fin 2) (Fin 2) K) * !![1, 0; -(γ / δ), 1]) 1 0 = 0
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      simp [← hγ, ← hδ]
      field_simp
      ring
    · fin_cases i <;> fin_cases j <;> simp [k]
      exact div_le_one_of_le₀ h zero_le
    · change v ((!![1, 0; -(γ / δ), 1] : Matrix (Fin 2) (Fin 2) K) i j) ≤ 1
      fin_cases i <;> fin_cases j <;> simp
      exact div_le_one_of_le₀ h zero_le
  · have hlt : v δ < v γ := lt_of_not_ge h
    have hγ0 : γ ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hlt
      exact not_lt_zero hlt
    let k : GL (Fin 2) K := ⟨!![0, 1; 1, δ / γ], !![-(δ / γ), 1; 1, 0],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
    refine ⟨b * k⁻¹, k, ?_, ⟨fun i j => ?_, fun i j => ?_⟩, (inv_mul_cancel_right b k).symm⟩
    · change ((b : Matrix (Fin 2) (Fin 2) K) * !![-(δ / γ), 1; 1, 0]) 1 0 = 0
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      simp [← hγ, ← hδ]
      field_simp
      ring
    · fin_cases i <;> fin_cases j <;> simp [k]
      exact div_le_one_of_le₀ hlt.le zero_le
    · change v ((!![-(δ / γ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) i j) ≤ 1
      fin_cases i <;> fin_cases j <;> simp
      exact div_le_one_of_le₀ hlt.le zero_le

section Fin

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Use `filter_upwards [x.2] with w hw`. Conclude with `hw`.
-/
theorem ev_int (x : Af F) : ∀ᶠ w in Filter.cofinite, Valued.v (pLoc F w x) ≤ 1 := by
  filter_upwards [x.2] with w hw
  exact hw

/- English proof (translation)
Establish `h1 : ∀ᶠ w in Filter.cofinite, ∀ i j : Fin 2, Valued.v (pLoc F w ((b : Matrix (Fin 2) (Fin 2) (Af F)) i j)) ≤ 1`. Simplify using `only [Filter.eventually_all]`. Conclude with `fun i j => ev_int _`. Establish `h2 : ∀ᶠ w in Filter.cofinite, ∀ i j : Fin 2, Valued.v (pLoc F w (((b⁻¹ : GL (Fin 2) (Af F)) : Matrix (Fin 2) (Fin 2) (Af F)) i j)) ≤ 1`. Simplify using `only [Filter.eventually_all]`.

Conclude with `fun i j => ev_int _`. Use `filter_upwards [h1, h2] with w hw hw'`. Use `⟨fun i j => hw i j, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[← map_inv]`. Conclude with `hw' i j`.
-/
theorem ev_good (b : GL (Fin 2) (Af F)) :
    ∀ᶠ w in Filter.cofinite, LK Valued.v (Matrix.GeneralLinearGroup.map (pLoc F w) b) := by
  have h1 : ∀ᶠ w in Filter.cofinite, ∀ i j : Fin 2,
      Valued.v (pLoc F w ((b : Matrix (Fin 2) (Fin 2) (Af F)) i j)) ≤ 1 := by
    simp only [Filter.eventually_all]
    exact fun i j => ev_int _
  have h2 : ∀ᶠ w in Filter.cofinite, ∀ i j : Fin 2,
      Valued.v (pLoc F w (((b⁻¹ : GL (Fin 2) (Af F)) : Matrix (Fin 2) (Fin 2) (Af F)) i j)) ≤ 1 := by
    simp only [Filter.eventually_all]
    exact fun i j => ev_int _
  filter_upwards [h1, h2] with w hw hw'
  refine ⟨fun i j => hw i j, fun i j => ?_⟩
  rw [← map_inv]
  exact hw' i j

/- English proof (translation)
Establish `key : ∀ v, pLoc F v ((locGL F 2 w p : Matrix (Fin 2) (Fin 2) (Af F)) 1 0) = 0` using `fun v => by`. Express the relevant statement in the definitionally equal form `((Matrix.GeneralLinearGroup.map (pLoc F v) (locGL F 2 w p) : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0`. Distinguish the cases in `hvw : v = w`. Substitute `hvw` using the available equality. Rewrite using `[pLoc_locGL]`.

Conclude with `hp`. Rewrite using `[pLoc_locGL_of_ne hvw]`. Simplify using the standard rewrite rules. Conclude with `FiniteAdeleRing.ext _ fun v => (key v).trans (map_zero (pLoc F v)).symm`.
-/
theorem locGL_10 (w : HeightOneSpectrum (𝓞 F)) (p : GL (Fin 2) (w.adicCompletion F))
    (hp : (p : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) 1 0 = 0) :
    (locGL F 2 w p : Matrix (Fin 2) (Fin 2) (Af F)) 1 0 = 0 := by
  have key : ∀ v, pLoc F v ((locGL F 2 w p : Matrix (Fin 2) (Fin 2) (Af F)) 1 0) = 0 := fun v => by
    change ((Matrix.GeneralLinearGroup.map (pLoc F v) (locGL F 2 w p) : GL (Fin 2) (v.adicCompletion F)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0
    by_cases hvw : v = w
    · subst hvw; rw [pLoc_locGL]; exact hp
    · rw [pLoc_locGL_of_ne hvw]; simp
  exact FiniteAdeleRing.ext _ fun v => (key v).trans (map_zero (pLoc F v)).symm

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Introduce `b hb`. Conclude with `⟨1, b, by simp, fun w => hb w (Finset.notMem_empty w), (one_mul b).symm⟩`. Consider the case `insert w S hw ih`.

Introduce `b hb`. Take `⟨pw, kw, hpw, hkw, e⟩` from `loc_iw Valued.v (Matrix.GeneralLinearGroup.map (pLoc F w) b)`. Take `⟨p, k, hp, hk, e'⟩` from `ih ((locGL F 2 w pw)⁻¹ * b * (locGL F 2 w kw)⁻¹) fun v hv => by`. Distinguish the cases in `hvw : v = w`. Substitute `hvw` using the available equality.

Rewrite using `[map_mul, map_mul, map_inv, map_inv, pLoc_locGL, pLoc_locGL, e, inv_mul_cancel_left, mul_inv_cancel]`. Conclude with `LK_one _`. Rewrite using `[map_mul, map_mul, map_inv, map_inv, pLoc_locGL_of_ne hvw, pLoc_locGL_of_ne hvw, inv_one, one_mul, mul_one]`. Conclude with `hb v (by simp [hvw, hv])`. Use `⟨locGL F 2 w pw * p, k * locGL F 2 w kw, ut_mul (locGL_10 w pw hpw) hp, fun v => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul]`. Use `LK_mul _ (hk v) ?_` and prove the remaining obligations. Distinguish the cases in `hvw : v = w`. Substitute `hvw` using the available equality. Rewrite using `[pLoc_locGL]`.

Conclude with `hkw`. Rewrite using `[pLoc_locGL_of_ne hvw]`. Conclude with `LK_one _`. Rewrite using `[show locGL F 2 w pw * p * (k * locGL F 2 w kw) = locGL F 2 w pw * (p * k) * locGL F 2 w kw by`. Simplify using `only [mul_assoc], ← e']`.

Use `group`.
-/
theorem iwasawa_decomposition_finite_adeles (S : Finset (HeightOneSpectrum (𝓞 F))) : ∀ b : GL (Fin 2) (Af F),
    (∀ w ∉ S, LK Valued.v (Matrix.GeneralLinearGroup.map (pLoc F w) b)) →
    ∃ p k : GL (Fin 2) (Af F), (p : Matrix (Fin 2) (Fin 2) (Af F)) 1 0 = 0 ∧
      (∀ w, LK Valued.v (Matrix.GeneralLinearGroup.map (pLoc F w) k)) ∧ b = p * k := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro b hb
    exact ⟨1, b, by simp, fun w => hb w (Finset.notMem_empty w), (one_mul b).symm⟩
  | insert w S hw ih =>
    intro b hb
    obtain ⟨pw, kw, hpw, hkw, e⟩ := loc_iw Valued.v (Matrix.GeneralLinearGroup.map (pLoc F w) b)
    obtain ⟨p, k, hp, hk, e'⟩ := ih ((locGL F 2 w pw)⁻¹ * b * (locGL F 2 w kw)⁻¹) fun v hv => by
      by_cases hvw : v = w
      · subst hvw
        rw [map_mul, map_mul, map_inv, map_inv, pLoc_locGL, pLoc_locGL, e, inv_mul_cancel_left, mul_inv_cancel]
        exact LK_one _
      · rw [map_mul, map_mul, map_inv, map_inv, pLoc_locGL_of_ne hvw, pLoc_locGL_of_ne hvw, inv_one, one_mul,
          mul_one]
        exact hb v (by simp [hvw, hv])
    refine ⟨locGL F 2 w pw * p, k * locGL F 2 w kw, ut_mul (locGL_10 w pw hpw) hp, fun v => ?_, ?_⟩
    · rw [map_mul]
      refine LK_mul _ (hk v) ?_
      by_cases hvw : v = w
      · subst hvw; rw [pLoc_locGL]; exact hkw
      · rw [pLoc_locGL_of_ne hvw]; exact LK_one _
    · rw [show locGL F 2 w pw * p * (k * locGL F 2 w kw) = locGL F 2 w pw * (p * k) * locGL F 2 w kw by
        simp only [mul_assoc], ← e']
      group

/- English proof (translation)
Establish `hf` using `Filter.eventually_cofinite.1 (ev_good b)`. Use `iwasawa_decomposition_finite_adeles hf.toFinset b fun w hw => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `hw (hf.mem_toFinset.2 h)`.
-/
theorem fin_iw (b : GL (Fin 2) (Af F)) :
    ∃ p k : GL (Fin 2) (Af F), (p : Matrix (Fin 2) (Fin 2) (Af F)) 1 0 = 0 ∧
      (∀ w, LK Valued.v (Matrix.GeneralLinearGroup.map (pLoc F w) k)) ∧ b = p * k := by
  have hf := Filter.eventually_cofinite.1 (ev_good b)
  refine iwasawa_decomposition_finite_adeles hf.toFinset b fun w hw => ?_
  by_contra h
  exact hw (hf.mem_toFinset.2 h)

/- English proof (translation)
Use `(h1 k).2 ⟨fun i j => (h2 _).2 fun w => (hk w).1 i j, fun i j => (h2 _).2 fun w => ?_⟩` and prove the remaining obligations. Use `(hk w).2 i j` as an intermediate fact. Rewrite `this` using `[← map_inv]`. Conclude with `this`.
-/
theorem mem_maximal_compact_of_local (h1 : ∀ g : GF F, g ∈ K0 F ↔ (∀ i j, g.val i j ∈ Ohat F) ∧ ∀ i j, (g⁻¹ : GF F).val i j ∈ Ohat F)
    (h2 : ∀ x : Af F, x ∈ Ohat F ↔ ∀ w : Pl F, Valued.v (pLoc F w x) ≤ 1) {k : GF F}
    (hk : ∀ w, LK Valued.v (Matrix.GeneralLinearGroup.map (pLoc F w) k)) : k ∈ K0 F := by
  refine (h1 k).2 ⟨fun i j => (h2 _).2 fun w => (hk w).1 i j, fun i j => (h2 _).2 fun w => ?_⟩
  have := (hk w).2 i j
  rw [← map_inv] at this
  exact this

end Fin

end UpperTheory.Esk.IwasawaDecompositionLemmas

open UpperTheory.Esk.IwasawaDecompositionLemmas in
/- English proof (translation)
Introduce `hM F _ _ x`. Take `⟨h1, h2, -⟩` from `hM F`. Take `⟨p, k, hp, hk, e⟩` from `fin_iw x`. Take `⟨z, t, u, hz⟩` from `ut_eq p hp`. Use `⟨z, t, u, k, mem_maximal_compact_of_local h1 h2 hk, ?_⟩` and prove the remaining obligations.

Rewrite using `[e, hz]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.Esk.aIw : UpperTheory.Esk.AMem → UpperTheory.Esk.AIw := by
  intro hM F _ _ x
  obtain ⟨h1, h2, -⟩ := hM F
  obtain ⟨p, k, hp, hk, e⟩ := fin_iw x
  obtain ⟨z, t, u, hz⟩ := ut_eq p hp
  refine ⟨z, t, u, k, mem_maximal_compact_of_local h1 h2 hk, ?_⟩
  rw [e, hz]
  rfl
