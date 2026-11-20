import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.MulVecApplyOfRow

open Matrix MeasureTheory
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.SymA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

/- English proof (translation)
Unfold `Hb`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
lemma Hb_mul_self : Hb k * Hb k = 1 := by
  unfold Hb
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  split_ifs <;> norm_num

/- English proof (translation)
Apply `Matrix.isUnit_det_of_left_inverse (B := Hb k * γᴴ * Hb k)` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.
-/
lemma unit_of_frame {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (h : γᴴ * Hb k * γ = Hb k) : IsUnit γ.det := by
  apply Matrix.isUnit_det_of_left_inverse (B := Hb k * γᴴ * Hb k)
  calc Hb k * γᴴ * Hb k * γ = Hb k * (γᴴ * Hb k * γ) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, Hb_mul_self]

/- English proof (translation)
The claim follows from `Matrix.inv_eq_right_inv (by rw [← emb_mul, Matrix.mul_nonsing_inv _ hγ, emb_one])`.
-/
lemma emb_inv {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hγ : IsUnit γ.det) :
    (embWb k r γ)⁻¹ = embWb k r γ⁻¹ :=
  Matrix.inv_eq_right_inv (by rw [← emb_mul, Matrix.mul_nonsing_inv _ hγ, emb_one])

/- English proof (translation)
The claim follows from `Matrix.isUnit_det_of_right_inverse (B := embWb k r γ⁻¹) (by rw [← emb_mul, Matrix.mul_nonsing_inv _ hγ, emb_one])`.
-/
lemma emb_unit {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hγ : IsUnit γ.det) : IsUnit (embWb k r γ).det :=
  Matrix.isUnit_det_of_right_inverse (B := embWb k r γ⁻¹) (by rw [← emb_mul, Matrix.mul_nonsing_inv _ hγ, emb_one])

section gbar

variable (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hE : IsUnit (embWb k r γ).det)
include hE

/- English proof (translation)
Unfold `gbar`. Establish `e : (embWb k r γ)⁻¹ * (g * h) * embWb k r γ = ((embWb k r γ)⁻¹ * g * embWb k r γ) * ((embWb k r γ)⁻¹ * h * embWb k r γ)`. Simplify using `only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hE]`. Rewrite using `[e, Matrix.map_mul]`. Simplify using `only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hE]`.
-/
lemma gbar_mul (g h : Mat k r) : gbar k r γ (g * h) = gbar k r γ g * gbar k r γ h := by
  unfold gbar
  have e : (embWb k r γ)⁻¹ * (g * h) * embWb k r γ =
      ((embWb k r γ)⁻¹ * g * embWb k r γ) * ((embWb k r γ)⁻¹ * h * embWb k r γ) := by
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hE]
  rw [e, Matrix.map_mul]
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hE]

/- English proof (translation)
Unfold `gbar`. Rewrite using `[Matrix.mul_one, Matrix.nonsing_inv_mul _ hE, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.mul_nonsing_inv _ hE]`.
-/
lemma gbar_one : gbar k r γ 1 = 1 := by
  unfold gbar
  rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ hE, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
    Matrix.mul_nonsing_inv _ hE]

/- English proof (translation)
Unfold `gbar`. Establish `h1 : (embWb k r γ)⁻¹ * (embWb k r γ * ((embWb k r γ)⁻¹ * g * embWb k r γ).map (starRingEnd ℂ) * (embWb k r γ)⁻¹) * embWb k r γ = ((embWb k r γ)⁻¹ * g * embWb k r γ).map (starRingEnd ℂ)`. Simplify using `only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hE, Matrix.nonsing_inv_mul _ hE, Matrix.mul_one]`. Rewrite using `[h1]`. Establish `h2 : (((embWb k r γ)⁻¹ * g * embWb k r γ).map (starRingEnd ℂ)).map (starRingEnd ℂ) = (embWb k r γ)⁻¹ * g * embWb k r γ`.

Use extensionality with `i j`. Rewrite using `[Matrix.map_apply, Matrix.map_apply, Complex.conj_conj]`. Rewrite using `[h2]`. Simplify using `only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hE, Matrix.mul_nonsing_inv _ hE, Matrix.mul_one]`.
-/
lemma gbar_gbar (g : Mat k r) : gbar k r γ (gbar k r γ g) = g := by
  unfold gbar
  have h1 : (embWb k r γ)⁻¹ * (embWb k r γ * ((embWb k r γ)⁻¹ * g * embWb k r γ).map (starRingEnd ℂ) *
      (embWb k r γ)⁻¹) * embWb k r γ = ((embWb k r γ)⁻¹ * g * embWb k r γ).map (starRingEnd ℂ) := by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hE, Matrix.nonsing_inv_mul _ hE,
      Matrix.mul_one]
  rw [h1]
  have h2 : (((embWb k r γ)⁻¹ * g * embWb k r γ).map (starRingEnd ℂ)).map (starRingEnd ℂ) =
      (embWb k r γ)⁻¹ * g * embWb k r γ := by
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply, Complex.conj_conj]
  rw [h2]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hE, Matrix.mul_nonsing_inv _ hE,
    Matrix.mul_one]

/- English proof (translation)
Rewrite using `[← gbar_mul γ hE, Matrix.mul_nonsing_inv _ hx, gbar_one γ hE]`.
-/
lemma gbar_mul_inv {x : Mat k r} (hx : IsUnit x.det) : gbar k r γ x * gbar k r γ x⁻¹ = 1 := by
  rw [← gbar_mul γ hE, Matrix.mul_nonsing_inv _ hx, gbar_one γ hE]

/- English proof (translation)
The claim follows from `(Matrix.inv_eq_right_inv (gbar_mul_inv γ hE hx)).symm`.
-/
lemma gbar_inv {x : Mat k r} (hx : IsUnit x.det) : gbar k r γ x⁻¹ = (gbar k r γ x)⁻¹ :=
  (Matrix.inv_eq_right_inv (gbar_mul_inv γ hE hx)).symm

/- English proof (translation)
The claim follows from `Matrix.isUnit_det_of_right_inverse (gbar_mul_inv γ hE hx)`.
-/
lemma gbar_unit {x : Mat k r} (hx : IsUnit x.det) : IsUnit (gbar k r γ x).det :=
  Matrix.isUnit_det_of_right_inverse (gbar_mul_inv γ hE hx)

/- English proof (translation)
Unfold `th at hg ⊢`. Rewrite using `[gbar_mul γ hE, gbar_mul γ hE, gbar_mul γ hE, gbar_mul γ hE, gbar_inv γ hE ha, gbar_inv γ hE hb]`. Simplify using `only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (gbar_unit γ hE ha), Matrix.nonsing_inv_nonsing_inv _ (gbar_unit γ hE hb), hg, Matrix.mul_assoc]`.
-/
lemma th_five {a b g c d : Mat k r} (ha : IsUnit a.det) (hb : IsUnit b.det) (hg : th k r γ g = g) :
    th k r γ (a⁻¹ * b⁻¹ * g * c * d) =
      (gbar k r γ d)⁻¹ * (gbar k r γ c)⁻¹ * g * gbar k r γ b * gbar k r γ a := by
  unfold th at hg ⊢
  rw [gbar_mul γ hE, gbar_mul γ hE, gbar_mul γ hE, gbar_mul γ hE, gbar_inv γ hE ha, gbar_inv γ hE hb]
  simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (gbar_unit γ hE ha),
    Matrix.nonsing_inv_nonsing_inv _ (gbar_unit γ hE hb), hg, Matrix.mul_assoc]

/- English proof (translation)
Unfold `th`. Rewrite using `[gbar_mul γ hE, gbar_inv γ hE hh', Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (gbar_unit γ hE hh')]`.
-/
lemma th_mul_inv {h h' : Mat k r} (hh' : IsUnit h'.det) :
    th k r γ (h * h'⁻¹) = gbar k r γ h' * (gbar k r γ h)⁻¹ := by
  unfold th
  rw [gbar_mul γ hE, gbar_inv γ hE hh', Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (gbar_unit γ hE hh')]

end gbar

/- English proof (translation)
Unfold `psi`. Rewrite using `[ell_conj z (uw_block ha) (uw_block (uw_inv ha)) (uw_inv ha).2.2]`.
-/
lemma psi_conj (z : Fin (2 * r + k + 1) → ℂ) {a : Mat k r} (ha : a ∈ UWset k r z) (c : ℂ) (n : Mat k r) :
    psi k r z c (a * n * a⁻¹) = psi k r z c n := by
  unfold psi
  rw [ell_conj z (uw_block ha) (uw_block (uw_inv ha)) (uw_inv ha).2.2]

/- English proof (translation)
Use `j.isLt` as an intermediate fact. Unfold `tau wI`. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only`. Apply the tactic sequence `split_ifs with h <;> omega`.
-/
lemma tau_wI (j : Fin (k + 1)) : tau k r (wI k r j) = wI k r j := by
  have := j.isLt
  unfold tau wI
  apply Fin.ext
  simp only
  split_ifs with h <;> omega

/- English proof (translation)
Unfold `mud`. Apply the tactic sequence `rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]`.
-/
lemma mud_off (d : ℂ) (x y : Fin (k + 1)) (h : (x ≠ 0 ∧ x ≠ Fin.last k) ∨ (y ≠ 0 ∧ y ≠ Fin.last k)) :
    mud k d x y = if x = y then 1 else 0 := by
  unfold mud
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

/- English proof (translation)
Distinguish the cases in `hi : mid k r i`. Distinguish the cases in `hj : mid k r j`. Rewrite using `[emb_mid _ i j hi hj, mud_off]`. Distinguish the cases in `e : i = j`. Substitute `e` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[if_neg e, if_neg (fun h' => e (by rw [← wI_midx hi, ← wI_midx hj, h']))]`. Break down `h with ⟨h1, h2⟩ | ⟨h1, h2⟩` into its components or cases. Use `left`. Conclude with `⟨fun h' => h1 (by rw [← wI_midx hi, h']), fun h' => h2 (by rw [← wI_midx hi, h'])⟩`.

Use `right`. Conclude with `⟨fun h' => h1 (by rw [← wI_midx hj, h']), fun h' => h2 (by rw [← wI_midx hj, h'])⟩`. Conclude with `emb_out_col _ i j hj`. Conclude with `emb_out_row _ i j hi`.
-/
lemma emb_mud_off (d : ℂ) (i j : Fin (2 * r + k + 1))
    (h : (i ≠ wI k r 0 ∧ i ≠ wI k r (Fin.last k)) ∨ (j ≠ wI k r 0 ∧ j ≠ wI k r (Fin.last k))) :
    embWb k r (mud k d) i j = if i = j then 1 else 0 := by
  by_cases hi : mid k r i
  · by_cases hj : mid k r j
    · rw [emb_mid _ i j hi hj, mud_off]
      · by_cases e : i = j
        · subst e; simp
        · rw [if_neg e, if_neg (fun h' => e (by rw [← wI_midx hi, ← wI_midx hj, h']))]
      · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left
          exact ⟨fun h' => h1 (by rw [← wI_midx hi, h']), fun h' => h2 (by rw [← wI_midx hi, h'])⟩
        · right
          exact ⟨fun h' => h1 (by rw [← wI_midx hj, h']), fun h' => h2 (by rw [← wI_midx hj, h'])⟩
    · exact emb_out_col _ i j hj
  · exact emb_out_row _ i j hi

/- English proof (translation)
Use `set a := wI k r 0`. Use `set b := wI k r (Fin.last k)`. Establish `hne : a ≠ b` using `fun h => by`. Use `congrArg Fin.val (wI_inj h)` as an intermediate fact. Simplify using `at this`.

Use linear arithmetic over natural numbers and integers. Establish `c0` using `col_of_fix h0`. Establish `cL` using `col_of_fix hL`. Establish `r0 : ∀ j, R a j = if a = j then 1 else 0`. Introduce `j`.

Use `row_of_fixed_col hR a c0 j` as an intermediate fact. Rewrite `this` using `[tau_wI]`. Then use the resulting hypothesis. Establish `rL : ∀ j, R b j = if b = j then 1 else 0`. Introduce `j`. Use `row_of_fixed_col hR b cL j` as an intermediate fact.

Rewrite `this` using `[tau_wI]`. Then use the resulting hypothesis. Use `set P : Mat k r := embWb k r (mud k d) - 1 with hPdef`. Establish `hM : embWb k r (mud k d) = 1 + P` using `by rw [hPdef]; abel`. Establish `hP : ∀ i j, ((i ≠ a ∧ i ≠ b) ∨ (j ≠ a ∧ j ≠ b)) → P i j = 0`. Introduce `i j h`.

Rewrite using `[hPdef, Matrix.sub_apply, emb_mud_off d i j h, Matrix.one_apply, sub_self]`. Establish `RP : R * P = P`. Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Fintype.sum_eq_add a b hne (fun l hl => by rw [hP l j (Or.inl hl), mul_zero]), c0, cL]`. Distinguish the cases in `ha : i = a`.

Substitute `ha` using the available equality. Rewrite using `[if_pos rfl, if_neg hne, one_mul, zero_mul, add_zero]`. Distinguish the cases in `hb : i = b`. Substitute `hb` using the available equality. Rewrite using `[if_neg (Ne.symm hne), if_pos rfl, one_mul, zero_mul, zero_add]`.

Rewrite using `[if_neg ha, if_neg hb, zero_mul, zero_mul, add_zero, hP i j (Or.inl ⟨ha, hb⟩)]`. Establish `PR : P * R = P`. Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Fintype.sum_eq_add a b hne (fun l hl => by rw [hP i l (Or.inr hl), zero_mul]), r0, rL]`. Distinguish the cases in `ha : j = a`.

Substitute `ha` using the available equality. Rewrite using `[if_pos rfl, if_neg (Ne.symm hne), mul_one, mul_zero, add_zero]`. Distinguish the cases in `hb : j = b`. Substitute `hb` using the available equality. Rewrite using `[if_neg hne, if_pos rfl, mul_one, mul_zero, zero_add]`.

Rewrite using `[if_neg (Ne.symm ha), if_neg (Ne.symm hb), mul_zero, mul_zero, add_zero, hP i j (Or.inr ⟨ha, hb⟩)]`. Rewrite using `[hM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, RP, PR]`.
-/
lemma comm_mud (hk : 1 ≤ k) {R : Mat k r} (hR : R ∈ UH (Hpk k r))
    (h0 : R *ᵥ bvec (wI k r 0) = bvec (wI k r 0)) (hL : R *ᵥ bvec (wI k r (Fin.last k)) = bvec (wI k r (Fin.last k)))
    (d : ℂ) : R * embWb k r (mud k d) = embWb k r (mud k d) * R := by
  set a := wI k r 0
  set b := wI k r (Fin.last k)
  have hne : a ≠ b := fun h => by
    have := congrArg Fin.val (wI_inj h)
    simp at this
    omega
  have c0 := col_of_fix h0
  have cL := col_of_fix hL
  have r0 : ∀ j, R a j = if a = j then 1 else 0 := by
    intro j
    have := row_of_fixed_col hR a c0 j
    rwa [tau_wI] at this
  have rL : ∀ j, R b j = if b = j then 1 else 0 := by
    intro j
    have := row_of_fixed_col hR b cL j
    rwa [tau_wI] at this
  set P : Mat k r := embWb k r (mud k d) - 1 with hPdef
  have hM : embWb k r (mud k d) = 1 + P := by rw [hPdef]; abel
  have hP : ∀ i j, ((i ≠ a ∧ i ≠ b) ∨ (j ≠ a ∧ j ≠ b)) → P i j = 0 := by
    intro i j h
    rw [hPdef, Matrix.sub_apply, emb_mud_off d i j h, Matrix.one_apply, sub_self]
  have RP : R * P = P := by
    ext i j
    rw [Matrix.mul_apply, Fintype.sum_eq_add a b hne (fun l hl => by rw [hP l j (Or.inl hl), mul_zero]),
      c0, cL]
    by_cases ha : i = a
    · subst ha; rw [if_pos rfl, if_neg hne, one_mul, zero_mul, add_zero]
    · by_cases hb : i = b
      · subst hb; rw [if_neg (Ne.symm hne), if_pos rfl, one_mul, zero_mul, zero_add]
      · rw [if_neg ha, if_neg hb, zero_mul, zero_mul, add_zero, hP i j (Or.inl ⟨ha, hb⟩)]
  have PR : P * R = P := by
    ext i j
    rw [Matrix.mul_apply, Fintype.sum_eq_add a b hne (fun l hl => by rw [hP i l (Or.inr hl), zero_mul]),
      r0, rL]
    by_cases ha : j = a
    · subst ha; rw [if_pos rfl, if_neg (Ne.symm hne), mul_one, mul_zero, add_zero]
    · by_cases hb : j = b
      · subst hb; rw [if_neg hne, if_pos rfl, mul_one, mul_zero, zero_add]
      · rw [if_neg (Ne.symm ha), if_neg (Ne.symm hb), mul_zero, mul_zero, add_zero, hP i j (Or.inr ⟨ha, hb⟩)]
  rw [hM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, RP, PR]

/- English proof (translation)
Establish `hγu` using `unit_of_frame hγ.1`. Establish `hEu : IsUnit (embWb k r γ).det` using `emb_unit hγu`. Establish `hEW : embWb k r γ ∈ UWb k r` using `by rw [(hUWb k r).1]; exact ⟨γ, hγ.1, rfl⟩`. Establish `hEG : embWb k r γ ∈ UH (Hpk k r)` using `hEW.1`. Establish `huW : u ∈ UWb k r` using `(hUWb k r).2.1 z hu.1`.

Use `set E := embWb k r γ with hEdef`. Use `set R := E⁻¹ * u * E with hRdef`. Establish `hR : R ∈ UH (Hpk k r)` using `uh_mul (uh_mul (uh_inv hEG) hu.1.1) hEG`. Establish `fixR : ∀ v, E *ᵥ v = v → True` using `fun _ _ => trivial`. Establish `h0 : R *ᵥ bvec (wI k r 0) = bvec (wI k r 0)`.

Rewrite using `[hRdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`. Express the relevant statement in the definitionally equal form `E⁻¹ *ᵥ (u *ᵥ w1 k r γ) = _`. Rewrite using `[hu.2, w1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hEu, Matrix.one_mulVec]`. Establish `hL : R *ᵥ bvec (wI k r (Fin.last k)) = bvec (wI k r (Fin.last k))`. Rewrite using `[hRdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hγ.2, Matrix.mulVec_smul, hu.1.2.2, ← hγ.2, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hEu, Matrix.one_mulVec]`.

Establish `hRM` using `comm_mud hk hR h0 hL d`. Establish `hu' : u = E * R * E⁻¹`. Rewrite using `[hRdef]`. Simplify using `only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hEu, Matrix.mul_nonsing_inv _ hEu, Matrix.mul_one]`. Establish `key : u * (E * embWb k r (mud k d) * E⁻¹) = E * embWb k r (mud k d) * E⁻¹ * u`.

Rewrite using `[hu']`. Simplify using `only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hEu]`. Rewrite using `[← Matrix.mul_assoc R, hRM, Matrix.mul_assoc]`. Unfold `g0`. Rewrite using `[(hBCF k r c _).1, emb_mul, emb_mul, ← emb_inv hγu]`.

Establish `hc` using `(hUWb k r).2.2 c u huW`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma big_cell_commute_frame_element (hBCF : BigCellFactor) (hUWb : UWbFacts) (hk : 1 ≤ k) {z : Fin (2 * r + k + 1) → ℂ}
    {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hγ : IsZFrame k r z γ) {u : Mat k r} (hu : u ∈ UUset k r z γ)
    (c : Fin r → ℂ) (d : ℂ) : u * g0 k r γ c d = g0 k r γ c d * u := by
  have hγu := unit_of_frame hγ.1
  have hEu : IsUnit (embWb k r γ).det := emb_unit hγu
  have hEW : embWb k r γ ∈ UWb k r := by rw [(hUWb k r).1]; exact ⟨γ, hγ.1, rfl⟩
  have hEG : embWb k r γ ∈ UH (Hpk k r) := hEW.1
  have huW : u ∈ UWb k r := (hUWb k r).2.1 z hu.1
  set E := embWb k r γ with hEdef
  set R := E⁻¹ * u * E with hRdef
  have hR : R ∈ UH (Hpk k r) := uh_mul (uh_mul (uh_inv hEG) hu.1.1) hEG
  have fixR : ∀ v, E *ᵥ v = v → True := fun _ _ => trivial
  have h0 : R *ᵥ bvec (wI k r 0) = bvec (wI k r 0) := by
    rw [hRdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    change E⁻¹ *ᵥ (u *ᵥ w1 k r γ) = _
    rw [hu.2, w1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hEu, Matrix.one_mulVec]
  have hL : R *ᵥ bvec (wI k r (Fin.last k)) = bvec (wI k r (Fin.last k)) := by
    rw [hRdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hγ.2, Matrix.mulVec_smul, hu.1.2.2, ← hγ.2,
      Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hEu, Matrix.one_mulVec]
  have hRM := comm_mud hk hR h0 hL d
  have hu' : u = E * R * E⁻¹ := by
    rw [hRdef]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hEu, Matrix.mul_nonsing_inv _ hEu,
      Matrix.mul_one]
  have key : u * (E * embWb k r (mud k d) * E⁻¹) = E * embWb k r (mud k d) * E⁻¹ * u := by
    rw [hu']
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hEu]
    rw [← Matrix.mul_assoc R, hRM, Matrix.mul_assoc]
  unfold g0
  rw [(hBCF k r c _).1, emb_mul, emb_mul, ← emb_inv hγu]
  have hc := (hUWb k r).2.2 c u huW
  calc u * (bigCell k r c 1 * (E * embWb k r (mud k d) * E⁻¹))
      = bigCell k r c 1 * (u * (E * embWb k r (mud k d) * E⁻¹)) := by rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc]
    _ = bigCell k r c 1 * (E * embWb k r (mud k d) * E⁻¹) * u := by rw [key]; simp only [Matrix.mul_assoc]

end ReciprocityTheory.ChartRestriction.DS.Mult1.SymA
