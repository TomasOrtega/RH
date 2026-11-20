import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TofFinrankIRLe

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `hqpos : 0 < q` using `by linarith`. Establish `hq0 : q ≠ 0` using `hqpos.ne'`. Establish `hr0 : 0 < r` using `by linarith`. Establish `hF0 : 0 ≤ F` using `by linarith`. Establish `hR2 : 0 < R ^ 2` using `by linarith`.

Establish `hRne : R ≠ 0`. Introduce and unpack `rfl`. Evaluate the numerical expressions using `at hR`. Establish `hden : 0 < R ^ 2 * (r ^ 7) ^ 4` using `mul_pos hR2 (pow_pos (pow_pos hr0 7) 4)`. Establish `hC2' : R ^ 2 * (r ^ 7) ^ 4 ≤ q`.

Establish `h` using `mul_le_mul_of_nonneg_right hC2 hden.le`. Establish `e : q / (R ^ 2 * (r ^ 7) ^ 4) * (R ^ 2 * (r ^ 7) ^ 4) = q`. Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion. Establish `harg : 0 ≤ F * R ^ 2 * (r ^ 7) ^ 3 / q` using `div_nonneg (mul_nonneg (mul_nonneg hF0 (sq_nonneg R)) (pow_pos (pow_pos hr0 7) 3).le) hqpos.le`.

Establish `hsq : la * la < F * R ^ 2 * (r ^ 7) ^ 3 / q`. Establish `h` using `mul_self_lt_mul_self hla.le hlt`. Rewrite `h` using `[Real.mul_self_sqrt harg]`. Then use the resulting hypothesis. Establish `hr7 : 0 < r ^ 7` using `pow_pos hr0 7`. Establish `hT : F * R ^ 2 * (r ^ 7) ^ 3 / q * r ^ 7 ≤ F`.

Establish `e : F * R ^ 2 * (r ^ 7) ^ 3 / q * r ^ 7 * q = F * (R ^ 2 * (r ^ 7) ^ 4)` using `by first`. Consider the case `(field_simp; ring)`. Consider the case `field_simp`. Establish `h2 : F * (R ^ 2 * (r ^ 7) ^ 4) ≤ F * q` using `mul_le_mul_of_nonneg_left hC2' hF0`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Establish `h3` using `mul_lt_mul_of_pos_right hc hqpos`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hA : la ^ 2 * r ^ 7 < F`. Establish `h` using `mul_lt_mul_of_pos_right hsq hr7`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hden2 : 0 < r ^ 2 * la ^ 2` using `mul_pos (pow_pos hr0 2) (pow_pos hla 2)`. Establish `hr5 : (1 : ℝ) ≤ r ^ 5`. Establish `h : (16 : ℝ) ^ 5 ≤ r ^ 5` using `by gcongr`. Evaluate the numerical expressions using `at h`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hr71 : (1 : ℝ) ≤ r ^ 7`. Establish `h : (16 : ℝ) ^ 7 ≤ r ^ 7` using `by gcongr`. Evaluate the numerical expressions using `at h`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hd4 : (4 : ℝ) ≤ d ^ 2` using `by nlinarith`. Establish `h1 : r ^ 2 * la ^ 2 ≤ la ^ 2 * r ^ 7`. Establish `h : r ^ 2 * la ^ 2 * 1 ≤ r ^ 2 * la ^ 2 * r ^ 5` using `mul_le_mul_of_nonneg_left hr5 hden2.le`. Combine the equalities or inequalities in the displayed calculation. Establish `h8 : (1 : ℝ) ≤ 8 * (r ^ 7 * d ^ 2)`.

Use polynomial arithmetic with `[mul_le_mul hr71 hd4 (by norm_num) (by linarith)]`. Establish `hK : F ≤ 4 * r ^ 7 * d ^ 2 * (2 * F)`. Establish `h` using `mul_le_mul_of_nonneg_right h8 hF0`. Use the polynomial consequences of the given equalities and inequalities. Establish `key : r ^ 2 * la ^ 2 ≤ 4 * r ^ 7 * d ^ 2 * (2 * F)` using `by linarith`.

Establish `hM : 4 * r ^ 7 * d ^ 2 * (2 * F / (r ^ 2 * la ^ 2)) * (r ^ 2 * la ^ 2) = 4 * r ^ 7 * d ^ 2 * (2 * F)`. Establish `: r ^ 2 * la ^ 2 ≠ 0` using `hden2.ne'`. Use `first`. Consider the case `(field_simp; ring)`. Consider the case `field_simp`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `h` using `mul_lt_mul_of_pos_right hc hden2`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem one_le_four_mul_r7_d_sq_div_of_bounds (r F la d q R : ℝ) (hla : 0 < la) (hr : 16 ≤ r) (hF : 1 ≤ F)
    (hd : 2 ≤ d) (hq : 1 ≤ q) (hR : 270 ≤ R ^ 2)
    (hC2 : 1 ≤ q / (R ^ 2 * (r ^ 7) ^ 4))
    (hlt : la < Real.sqrt (F * R ^ 2 * (r ^ 7) ^ 3 / q)) :
    1 ≤ 4 * r ^ 7 * d ^ 2 * (2 * F / (r ^ 2 * la ^ 2)) := by
  have hqpos : 0 < q := by linarith
  have hq0 : q ≠ 0 := hqpos.ne'
  have hr0 : 0 < r := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hR2 : 0 < R ^ 2 := by linarith
  have hRne : R ≠ 0 := by
    rintro rfl
    norm_num at hR
  have hden : 0 < R ^ 2 * (r ^ 7) ^ 4 := mul_pos hR2 (pow_pos (pow_pos hr0 7) 4)

  have hC2' : R ^ 2 * (r ^ 7) ^ 4 ≤ q := by
    have h := mul_le_mul_of_nonneg_right hC2 hden.le
    have e : q / (R ^ 2 * (r ^ 7) ^ 4) * (R ^ 2 * (r ^ 7) ^ 4) = q := by
      field_simp
    linarith
  have harg : 0 ≤ F * R ^ 2 * (r ^ 7) ^ 3 / q :=
    div_nonneg (mul_nonneg (mul_nonneg hF0 (sq_nonneg R)) (pow_pos (pow_pos hr0 7) 3).le) hqpos.le
  have hsq : la * la < F * R ^ 2 * (r ^ 7) ^ 3 / q := by
    have h := mul_self_lt_mul_self hla.le hlt
    rwa [Real.mul_self_sqrt harg] at h
  have hr7 : 0 < r ^ 7 := pow_pos hr0 7

  have hT : F * R ^ 2 * (r ^ 7) ^ 3 / q * r ^ 7 ≤ F := by
    have e : F * R ^ 2 * (r ^ 7) ^ 3 / q * r ^ 7 * q = F * (R ^ 2 * (r ^ 7) ^ 4) := by
      first
        | (field_simp; ring)
        | field_simp
    have h2 : F * (R ^ 2 * (r ^ 7) ^ 4) ≤ F * q := mul_le_mul_of_nonneg_left hC2' hF0
    by_contra hc
    push_neg at hc
    have h3 := mul_lt_mul_of_pos_right hc hqpos
    linarith
  have hA : la ^ 2 * r ^ 7 < F := by
    have h := mul_lt_mul_of_pos_right hsq hr7
    nlinarith
  have hden2 : 0 < r ^ 2 * la ^ 2 := mul_pos (pow_pos hr0 2) (pow_pos hla 2)
  have hr5 : (1 : ℝ) ≤ r ^ 5 := by
    have h : (16 : ℝ) ^ 5 ≤ r ^ 5 := by gcongr
    norm_num at h
    linarith
  have hr71 : (1 : ℝ) ≤ r ^ 7 := by
    have h : (16 : ℝ) ^ 7 ≤ r ^ 7 := by gcongr
    norm_num at h
    linarith
  have hd4 : (4 : ℝ) ≤ d ^ 2 := by nlinarith
  have h1 : r ^ 2 * la ^ 2 ≤ la ^ 2 * r ^ 7 := by
    have h : r ^ 2 * la ^ 2 * 1 ≤ r ^ 2 * la ^ 2 * r ^ 5 :=
      mul_le_mul_of_nonneg_left hr5 hden2.le
    calc r ^ 2 * la ^ 2 = r ^ 2 * la ^ 2 * 1 := by ring
      _ ≤ r ^ 2 * la ^ 2 * r ^ 5 := h
      _ = la ^ 2 * r ^ 7 := by ring
  have h8 : (1 : ℝ) ≤ 8 * (r ^ 7 * d ^ 2) := by
    nlinarith [mul_le_mul hr71 hd4 (by norm_num) (by linarith)]
  have hK : F ≤ 4 * r ^ 7 * d ^ 2 * (2 * F) := by
    have h := mul_le_mul_of_nonneg_right h8 hF0
    nlinarith
  have key : r ^ 2 * la ^ 2 ≤ 4 * r ^ 7 * d ^ 2 * (2 * F) := by linarith
  have hM : 4 * r ^ 7 * d ^ 2 * (2 * F / (r ^ 2 * la ^ 2)) * (r ^ 2 * la ^ 2)
      = 4 * r ^ 7 * d ^ 2 * (2 * F) := by
    have : r ^ 2 * la ^ 2 ≠ 0 := hden2.ne'
    first
      | (field_simp; ring)
      | field_simp
  by_contra hc
  push_neg at hc
  have h := mul_lt_mul_of_pos_right hc hden2
  linarith

/- English proof (translation)
Establish `hla : 0 < X.la1` using `firstMinimum_pos_bis P`. Establish `hka : P.ka0 = 4 * PT.rd E ^ 7 * (dstar (E` using `E) P.m : ℝ) ^ 2 := rfl`. Establish `hphd : P.ph = if X.la1 < th (E` using `E) P.q P.R0 then 2 * (PT.f E : ℝ) / (PT.rd E ^ 2 * X.la1 ^ 2) else 0 := rfl`. Distinguish the cases in `hlt : X.la1 < th (E := E) P.q P.R0`. Rewrite using `[hphd, if_pos hlt, hka]`.

Establish `hC2 : (1 : ℝ) ≤ (P.q : ℝ) / (P.R0 ^ 2 * (PT.rd E ^ 7) ^ 4)` using `P.C2`. Establish `hlt' : X.la1 < Real.sqrt ((PT.f E : ℝ) * P.R0 ^ 2 * (PT.rd E ^ 7) ^ 3 / (P.q : ℝ))` using `hlt`. Conclude with `one_le_four_mul_r7_d_sq_div_of_bounds (PT.rd E) (PT.f E) X.la1 (dstar (E := E) P.m) P.q P.R0 hla P.hrd (by exact_mod_cast f_pos P) (by exact_mod_cast tof_two_le_dstar P) (by exact_mod_cast P.hq) P.hR0.1 hC2 hlt'`. Rewrite `hph` using `[hphd, if_neg hlt]`. Conclude with `absurd hph (lt_irrefl 0)`.
-/
theorem one_le_kappa_mul_phase [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) (hph : 0 < P.ph) :
    1 ≤ P.ka0 * P.ph := by
  have hla : 0 < X.la1 := firstMinimum_pos_bis P
  have hka : P.ka0 = 4 * PT.rd E ^ 7 * (dstar (E := E) P.m : ℝ) ^ 2 := rfl
  have hphd : P.ph = if X.la1 < th (E := E) P.q P.R0
      then 2 * (PT.f E : ℝ) / (PT.rd E ^ 2 * X.la1 ^ 2) else 0 := rfl
  by_cases hlt : X.la1 < th (E := E) P.q P.R0
  · rw [hphd, if_pos hlt, hka]
    have hC2 : (1 : ℝ) ≤ (P.q : ℝ) / (P.R0 ^ 2 * (PT.rd E ^ 7) ^ 4) := P.C2
    have hlt' : X.la1 < Real.sqrt ((PT.f E : ℝ) * P.R0 ^ 2 * (PT.rd E ^ 7) ^ 3 / (P.q : ℝ)) := hlt
    exact one_le_four_mul_r7_d_sq_div_of_bounds (PT.rd E) (PT.f E) X.la1 (dstar (E := E) P.m) P.q P.R0 hla P.hrd
      (by exact_mod_cast f_pos P) (by exact_mod_cast tof_two_le_dstar P)
      (by exact_mod_cast P.hq) P.hR0.1 hC2 hlt'
  · rw [hphd, if_neg hlt] at hph
    exact absurd hph (lt_irrefl 0)

/- English proof (translation)
Set `K : Submodule ℝ (Vsp X.dim)` to `IR I`. Set `B` to `stdOrthonormalBasis ℝ K`. Set `φ : Vsp X.dim → EuclideanSpace ℝ (Fin (Module.finrank ℝ K))` to `fun v => B.repr (K.orthogonalProjectionOnto (v - u))`. Establish `hmem : ∀ y ∈ F, y - u ∈ K`. Introduce `y hy`.

Take `⟨x, -, rfl⟩` from `hF y hy`. Conclude with `K.sub_mem (isU_uMap I x).1 hu`. Establish `hpr : ∀ y (hy : y ∈ F), K.orthogonalProjectionOnto (y - u) = ⟨y - u, hmem y hy⟩` using `fun y hy => Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨y - u, hmem y hy⟩`. Establish `hφ : ∀ y ∈ F, ∀ y' ∈ F, ‖φ y - φ y'‖ = ‖y - y'‖`. Introduce `y hy y' hy'`.

Use `show ‖B.repr (K.orthogonalProjectionOnto (y - u)) - B.repr (K.orthogonalProjectionOnto (y' - u))‖ = ‖y - y'‖`. Rewrite using `[hpr y hy, hpr y' hy', ← map_sub, LinearIsometryEquiv.norm_map]`. Use `show ‖(y - u) - (y' - u)‖ = ‖y - y'‖`. Use `congr 1`. Normalize the expressions using the abelian group laws.

Establish `hinj : Set.InjOn φ F`. Introduce `y hy y' hy' h`. Establish `e` using `hφ y hy y' hy'`. Rewrite `e` using `[h, sub_self, norm_zero]`. Conclude with `sub_eq_zero.mp (norm_eq_zero.mp e.symm)`.

Establish `hcard : ((F.image φ).card : ℝ) ≤ (3 * R / 1) ^ Module.finrank ℝ K`. Apply `hP (Module.finrank ℝ K) (F.image φ) 1 R one_pos hR` to reduce the goal to its premises. Introduce `z hz`. Take `⟨y, hy, rfl⟩` from `Finset.mem_image.mp hz`. Use `show ‖B.repr (K.orthogonalProjectionOnto (y - u))‖ ≤ R`.

Rewrite using `[hpr y hy, LinearIsometryEquiv.norm_map]`. Use `show ‖y - u‖ ≤ R`. Rewrite using `[norm_sub_rev]`. Conclude with `hFR y hy`. Introduce `z hz z' hz' hne`.

Take `⟨y, hy, rfl⟩` from `Finset.mem_image.mp hz`. Take `⟨y', hy', rfl⟩` from `Finset.mem_image.mp hz'`. Rewrite using `[dist_eq_norm, hφ y hy y' hy']`. Establish `hyy : y ≠ y'` using `fun h => hne (by rw [h])`. Take `⟨x, hx, rfl⟩` from `hF y hy`.

Take `⟨x', hx', rfl⟩` from `hF y' hy'`. Conclude with `tof_uMap_sep P hI hx hx' hyy`. Rewrite `hcard` using `[Finset.card_image_of_injOn hinj, div_one]`. Conclude with `hcard`.
-/
theorem tof_pack_card [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) (hP : Ext.PackingCount) (u : Vsp X.dim) (hu : u ∈ IR I) (R : ℝ) (hR : 1 ≤ R)
    (F : Finset (Vsp X.dim)) (hF : ∀ y ∈ F, ∃ x ∈ X.L, y = uMap I x)
    (hFR : ∀ y ∈ F, ‖u - y‖ ≤ R) : (F.card : ℝ) ≤ (3 * R) ^ Module.finrank ℝ (IR I) := by
  classical

  let K : Submodule ℝ (Vsp X.dim) := IR I
  let B := stdOrthonormalBasis ℝ K
  let φ : Vsp X.dim → EuclideanSpace ℝ (Fin (Module.finrank ℝ K)) :=
    fun v => B.repr (K.orthogonalProjectionOnto (v - u))
  have hmem : ∀ y ∈ F, y - u ∈ K := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := hF y hy
    exact K.sub_mem (isU_uMap I x).1 hu
  have hpr : ∀ y (hy : y ∈ F), K.orthogonalProjectionOnto (y - u) = ⟨y - u, hmem y hy⟩ := fun y hy =>
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨y - u, hmem y hy⟩
  have hφ : ∀ y ∈ F, ∀ y' ∈ F, ‖φ y - φ y'‖ = ‖y - y'‖ := by
    intro y hy y' hy'
    show ‖B.repr (K.orthogonalProjectionOnto (y - u)) - B.repr (K.orthogonalProjectionOnto (y' - u))‖
      = ‖y - y'‖
    rw [hpr y hy, hpr y' hy', ← map_sub, LinearIsometryEquiv.norm_map]
    show ‖(y - u) - (y' - u)‖ = ‖y - y'‖
    congr 1
    abel
  have hinj : Set.InjOn φ F := by
    intro y hy y' hy' h
    have e := hφ y hy y' hy'
    rw [h, sub_self, norm_zero] at e
    exact sub_eq_zero.mp (norm_eq_zero.mp e.symm)
  have hcard : ((F.image φ).card : ℝ) ≤ (3 * R / 1) ^ Module.finrank ℝ K := by
    apply hP (Module.finrank ℝ K) (F.image φ) 1 R one_pos hR
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      show ‖B.repr (K.orthogonalProjectionOnto (y - u))‖ ≤ R
      rw [hpr y hy, LinearIsometryEquiv.norm_map]
      show ‖y - u‖ ≤ R
      rw [norm_sub_rev]
      exact hFR y hy
    · intro z hz z' hz' hne
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hz'
      rw [dist_eq_norm, hφ y hy y' hy']
      have hyy : y ≠ y' := fun h => hne (by rw [h])
      obtain ⟨x, hx, rfl⟩ := hF y hy
      obtain ⟨x', hx', rfl⟩ := hF y' hy'
      exact tof_uMap_sep P hI hx hx' hyy
  rw [Finset.card_image_of_injOn hinj, div_one] at hcard
  exact hcard

/- English proof (translation)
Set `S : Set (Vsp X.dim)` to `{y | (∃ x ∈ X.L, y = uMap I x) ∧ ‖u - y‖ ≤ ‖u‖}`. Establish `hfin : S.Finite`. Assume the negation of the conclusion as `hinf`. Take `⟨t, ht, hcard⟩` from `Set.Infinite.exists_subset_card_eq hinf (Nat.ceil ((3 * (‖u‖ + 1)) ^ Module.finrank ℝ (IR I)) + 1)`. Establish `hb` using `tof_pack_card P hI hP u hu (‖u‖ + 1) (by linarith [norm_nonneg u]) t (fun y hy => (ht (Finset.mem_coe.2 hy)).1) (fun y hy => le_trans (ht (Finset.mem_coe.2 hy)).2 (by linarith))`.

Rewrite `hb` using `[hcard]`. Move the coercions through the operations in `at hb`. Establish `hc` using `Nat.le_ceil ((3 * (‖u‖ + 1)) ^ Module.finrank ℝ (IR I))`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h0 : (0 : Vsp X.dim) ∈ S` using `⟨⟨0, X.L.zero_mem, (map_zero (uMap I)).symm⟩, by rw [sub_zero]⟩`.

Take `⟨y, hyS, hmin⟩` from `hfin.toFinset.exists_min_image (fun y => ‖u - y‖) ⟨0, hfin.mem_toFinset.2 h0⟩`. Take `⟨⟨y0, hy0, rfl⟩, hyu⟩` from `hfin.mem_toFinset.1 hyS`. Use `⟨y0, hy0, fun x hx => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hxs : ‖u - uMap I x‖ ≤ ‖u‖`. Conclude with `hmin _ (hfin.mem_toFinset.2 ⟨⟨x, hx, rfl⟩, hxs⟩)`.

Use `push_neg at hxs`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem tof_exists_nearest [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) (hP : Ext.PackingCount) (u : Vsp X.dim) (hu : u ∈ IR I) :
    ∃ y0 ∈ X.L, ∀ x ∈ X.L, ‖u - uMap I y0‖ ≤ ‖u - uMap I x‖ := by
  classical

  let S : Set (Vsp X.dim) := {y | (∃ x ∈ X.L, y = uMap I x) ∧ ‖u - y‖ ≤ ‖u‖}
  have hfin : S.Finite := by
    by_contra hinf
    obtain ⟨t, ht, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf
      (Nat.ceil ((3 * (‖u‖ + 1)) ^ Module.finrank ℝ (IR I)) + 1)
    have hb := tof_pack_card P hI hP u hu (‖u‖ + 1) (by linarith [norm_nonneg u]) t
      (fun y hy => (ht (Finset.mem_coe.2 hy)).1)
      (fun y hy => le_trans (ht (Finset.mem_coe.2 hy)).2 (by linarith))
    rw [hcard] at hb
    push_cast at hb
    have hc := Nat.le_ceil ((3 * (‖u‖ + 1)) ^ Module.finrank ℝ (IR I))
    linarith
  have h0 : (0 : Vsp X.dim) ∈ S :=
    ⟨⟨0, X.L.zero_mem, (map_zero (uMap I)).symm⟩, by rw [sub_zero]⟩
  obtain ⟨y, hyS, hmin⟩ :=
    hfin.toFinset.exists_min_image (fun y => ‖u - y‖) ⟨0, hfin.mem_toFinset.2 h0⟩
  obtain ⟨⟨y0, hy0, rfl⟩, hyu⟩ := hfin.mem_toFinset.1 hyS
  refine ⟨y0, hy0, fun x hx => ?_⟩
  by_cases hxs : ‖u - uMap I x‖ ≤ ‖u‖
  · exact hmin _ (hfin.mem_toFinset.2 ⟨⟨x, hx, rfl⟩, hxs⟩)
  · push_neg at hxs
    linarith

/- English proof (translation)
Take `⟨y0, hy0, hmin⟩` from `tof_exists_nearest P hI hP u hu`. Use `⟨y0, hy0, fun F hF => ?_⟩` and prove the remaining obligations. Establish `hsum` using `tof_sep_sum P hI hP u hu F hF`. Establish `hc0 : 0 ≤ ‖u - uMap I y0‖` using `norm_nonneg _`. Establish `hterm : ∀ y ∈ F, Real.exp (-Real.pi * ‖u - y‖ ^ 2) ≤ Real.exp (-(Real.pi / 2) * ‖u - uMap I y0‖ ^ 2) * Real.exp (-(Real.pi / 2) * ‖u - y‖ ^ 2)`.

Introduce `y hy`. Take `⟨x, hx, rfl⟩` from `hF y hy`. Establish `h1 : ‖u - uMap I y0‖ ≤ ‖u - uMap I x‖` using `hmin x hx`. Establish `h2 : ‖u - uMap I y0‖ ^ 2 ≤ ‖u - uMap I x‖ ^ 2`. Use polynomial arithmetic with `[mul_self_le_mul_self hc0 h1]`.

Rewrite using `[← Real.exp_add]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h2 Real.pi_pos.le]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`.

Use `_ ≤ Real.exp (-(Real.pi / 2) * ‖u - uMap I y0‖ ^ 2) * (2 * (3 * (dstar (E := E) P.m : ℝ)) ^ dstar (E := E) P.m) := mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le`. Use `_ = 2 * (3 * (dstar (E := E) P.m : ℝ)) ^ dstar (E := E) P.m * Real.exp (-(Real.pi / 2) * ‖u - uMap I y0‖ ^ 2) := by ring`.
-/
theorem tof_gauss_min_sum [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) (hP : Ext.PackingCount) (u : Vsp X.dim) (hu : u ∈ IR I) :
    ∃ y0 ∈ X.L, ∀ F : Finset (Vsp X.dim), (∀ y ∈ F, ∃ x ∈ X.L, y = uMap I x) →
      ∑ y ∈ F, Real.exp (-Real.pi * ‖u - y‖ ^ 2) ≤
        2 * (3 * (dstar (E := E) P.m : ℝ)) ^ dstar (E := E) P.m *
          Real.exp (-(Real.pi / 2) * ‖u - uMap I y0‖ ^ 2) := by
  obtain ⟨y0, hy0, hmin⟩ := tof_exists_nearest P hI hP u hu
  refine ⟨y0, hy0, fun F hF => ?_⟩
  have hsum := tof_sep_sum P hI hP u hu F hF
  have hc0 : 0 ≤ ‖u - uMap I y0‖ := norm_nonneg _

  have hterm : ∀ y ∈ F, Real.exp (-Real.pi * ‖u - y‖ ^ 2) ≤
      Real.exp (-(Real.pi / 2) * ‖u - uMap I y0‖ ^ 2) *
        Real.exp (-(Real.pi / 2) * ‖u - y‖ ^ 2) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hF y hy
    have h1 : ‖u - uMap I y0‖ ≤ ‖u - uMap I x‖ := hmin x hx
    have h2 : ‖u - uMap I y0‖ ^ 2 ≤ ‖u - uMap I x‖ ^ 2 := by
      nlinarith [mul_self_le_mul_self hc0 h1]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left h2 Real.pi_pos.le]
  calc ∑ y ∈ F, Real.exp (-Real.pi * ‖u - y‖ ^ 2)
      ≤ ∑ y ∈ F, Real.exp (-(Real.pi / 2) * ‖u - uMap I y0‖ ^ 2) *
          Real.exp (-(Real.pi / 2) * ‖u - y‖ ^ 2) := Finset.sum_le_sum hterm
    _ = Real.exp (-(Real.pi / 2) * ‖u - uMap I y0‖ ^ 2) *
          ∑ y ∈ F, Real.exp (-(Real.pi / 2) * ‖u - y‖ ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (-(Real.pi / 2) * ‖u - uMap I y0‖ ^ 2) *
          (2 * (3 * (dstar (E := E) P.m : ℝ)) ^ dstar (E := E) P.m) :=
        mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
    _ = 2 * (3 * (dstar (E := E) P.m : ℝ)) ^ dstar (E := E) P.m *
          Real.exp (-(Real.pi / 2) * ‖u - uMap I y0‖ ^ 2) := by ring

end

end ReciprocityTheory.ChartRestriction.G.I2
