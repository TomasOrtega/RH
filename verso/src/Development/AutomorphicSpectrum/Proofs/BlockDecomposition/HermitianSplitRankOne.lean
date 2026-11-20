import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal

namespace GlobalTheory.CompanionTheory.KFin

section SwapHerm

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {c : R →+* R} {h : V → V → R}

/- English proof (translation)
Use `hH.smul_right 0 x 0` as an intermediate fact. Simplify using `using this`.
-/
theorem swapHerm_zero_right (hH : IsHerm c h) (x : V) : h x 0 = 0 := by
  have := hH.smul_right 0 x 0
  simpa using this

/- English proof (translation)
Rewrite using `[hH.symm z (x + y), hH.add_right, map_add, ← hH.symm z x, ← hH.symm z y]`.
-/
theorem swapHerm_add_left (hH : IsHerm c h) (x y z : V) : h (x + y) z = h x z + h y z := by
  rw [hH.symm z (x + y), hH.add_right, map_add, ← hH.symm z x, ← hH.symm z y]

/- English proof (translation)
Rewrite using `[hH.symm y (a • x), hH.smul_right, map_mul, ← hH.symm y x]`.
-/
theorem swapHerm_smul_left (hH : IsHerm c h) (a : R) (x y : V) : h (a • x) y = c a * h x y := by
  rw [hH.symm y (a • x), hH.smul_right, map_mul, ← hH.symm y x]

/- English proof (translation)
Use `hH.add_right x (y - z) z` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Conclude with `eq_sub_of_add_eq this.symm`.
-/
theorem swapHerm_sub_right (hH : IsHerm c h) (x y z : V) : h x (y - z) = h x y - h x z := by
  have := hH.add_right x (y - z) z
  rw [sub_add_cancel] at this
  exact eq_sub_of_add_eq this.symm

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem swapHerm_part {e e' : R} (hce : c e = e') (hH : IsHerm c h) {a : V} (ha : e • a = a) (z : V) :
    h a z = e' * h a z := by
  calc h a z = h (e • a) z := by rw [ha]
    _ = e' * h a z := by rw [swapHerm_smul_left hH, hce]

/- English proof (translation)
Establish `h1 : h a a = e * h a a`. Combine the equalities or inequalities in the displayed calculation. Establish `h2` using `swapHerm_part hce hH ha a`. Rewrite using `[h1, h2, ← mul_assoc, hee, zero_mul]`.
-/
theorem swapHerm_self {e e' : R} (hee : e * e' = 0) (hce : c e = e') (hH : IsHerm c h) {a : V}
    (ha : e • a = a) : h a a = 0 := by
  have h1 : h a a = e * h a a := by
    calc h a a = h a (e • a) := by rw [ha]
      _ = e * h a a := hH.smul_right e a a
  have h2 := swapHerm_part hce hH ha a
  rw [h1, h2, ← mul_assoc, hee, zero_mul]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Conclude with `ha (hP.nondeg a hne)`.
-/
theorem swapHerm_exists_ne (hP : IsPerfect h) {a : V} (ha : a ≠ 0) : ∃ y, h a y ≠ 0 := by
  by_contra hne
  push_neg at hne
  exact ha (hP.nondeg a hne)

/- English proof (translation)
Introduce `hab`. Establish `hee' : e' * e = 0` using `by rw [mul_comm]; exact hee`. Establish `haa : h a a = 0` using `swapHerm_self hee hce hH ha`. Establish `hbb : h b b = 0` using `swapHerm_self hee' hce' hH hb`. Establish `hba : h b a = 0` using `by rw [hH.symm a b, hab, map_zero]`.

Establish `hxx : h (a + b) (a + b) = 0`. Rewrite using `[swapHerm_add_left hH, hH.add_right, hH.add_right, haa, hab, hba, hbb]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨y1, hy1⟩` from `swapHerm_exists_ne hP ha0`. Take `⟨y2, hy2⟩` from `swapHerm_exists_ne hP hb0`.

Establish `hex : ∃ y, h a y ≠ 0 ∧ h b y ≠ 0`. Distinguish the cases in `h1 : h b y1 = 0`. Distinguish the cases in `h2 : h a y2 = 0`. Use `⟨y1 + y2, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hH.add_right, h2, add_zero]`.

Conclude with `hy1`. Rewrite using `[hH.add_right, h1, zero_add]`. Conclude with `hy2`. Conclude with `⟨y2, h2, hy2⟩`. Conclude with `⟨y1, hy1, h1⟩`.

Take `⟨y, hya, hyb⟩` from `hex`. Establish `hpa : h a y = e' * h a y` using `swapHerm_part hce hH ha y`. Establish `hpb : h b y = e * h b y` using `swapHerm_part hce' hH hb y`. Establish `hunit : IsUnit (h (a + b) y)`. Apply `hu` to reduce the goal to its premises.

Rewrite using `[swapHerm_add_left hH, mul_add, hpa, ← mul_assoc, hee, zero_mul, zero_add, ← hpb]`. Conclude with `hyb`. Rewrite using `[swapHerm_add_left hH, mul_add, hpb, ← mul_assoc, hee', zero_mul, add_zero, ← hpa]`. Conclude with `hya`. Take `⟨U, hU⟩` from `hunit`.

Apply `hno (a + b) ((↑U⁻¹ : R) • y) hxx` to reduce the goal to its premises. Rewrite using `[hH.smul_right, ← hU, Units.inv_mul]`.
-/
theorem swapHerm_pair_ne {e e' : R} (hee : e * e' = 0) (hce : c e = e') (hce' : c e' = e)
    (hu : ∀ u, e * u ≠ 0 → e' * u ≠ 0 → IsUnit u) (hH : IsHerm c h) (hP : IsPerfect h)
    (hno : ∀ x y, h x x = 0 → h x y ≠ 1) {a b : V} (ha : e • a = a) (hb : e' • b = b)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) : h a b ≠ 0 := by
  intro hab
  have hee' : e' * e = 0 := by rw [mul_comm]; exact hee
  have haa : h a a = 0 := swapHerm_self hee hce hH ha
  have hbb : h b b = 0 := swapHerm_self hee' hce' hH hb
  have hba : h b a = 0 := by rw [hH.symm a b, hab, map_zero]
  have hxx : h (a + b) (a + b) = 0 := by
    rw [swapHerm_add_left hH, hH.add_right, hH.add_right, haa, hab, hba, hbb]; ring
  obtain ⟨y1, hy1⟩ := swapHerm_exists_ne hP ha0
  obtain ⟨y2, hy2⟩ := swapHerm_exists_ne hP hb0
  have hex : ∃ y, h a y ≠ 0 ∧ h b y ≠ 0 := by
    by_cases h1 : h b y1 = 0
    · by_cases h2 : h a y2 = 0
      · refine ⟨y1 + y2, ?_, ?_⟩
        · rw [hH.add_right, h2, add_zero]; exact hy1
        · rw [hH.add_right, h1, zero_add]; exact hy2
      · exact ⟨y2, h2, hy2⟩
    · exact ⟨y1, hy1, h1⟩
  obtain ⟨y, hya, hyb⟩ := hex
  have hpa : h a y = e' * h a y := swapHerm_part hce hH ha y
  have hpb : h b y = e * h b y := swapHerm_part hce' hH hb y
  have hunit : IsUnit (h (a + b) y) := by
    apply hu
    · rw [swapHerm_add_left hH, mul_add, hpa, ← mul_assoc, hee, zero_mul, zero_add, ← hpb]; exact hyb
    · rw [swapHerm_add_left hH, mul_add, hpb, ← mul_assoc, hee', zero_mul, add_zero, ← hpa]; exact hya
  obtain ⟨U, hU⟩ := hunit
  apply hno (a + b) ((↑U⁻¹ : R) • y) hxx
  rw [hH.smul_right, ← hU, Units.inv_mul]

/- English proof (translation)
Take `⟨y, hy⟩` from `swapHerm_exists_ne hP ha0`. Establish `hidem : e' * e' = e'`. Establish `h0 : e' * e = 0` using `by rw [mul_comm]; exact hee`. Combine the equalities or inequalities in the displayed calculation. Use `⟨e' • y, by rw [← mul_smul, hidem], fun h0 => hy ?_⟩` and prove the remaining obligations.

Establish `h1 : h a (e' • y) = h a y` using `by rw [hH.smul_right, ← swapHerm_part hce hH ha y]`. Rewrite using `[← h1, h0, swapHerm_zero_right hH]`.
-/
theorem swapHerm_partner {e e' : R} (he : e + e' = 1) (hee : e * e' = 0) (hce : c e = e')
    (hH : IsHerm c h) (hP : IsPerfect h) {a : V} (ha : e • a = a) (ha0 : a ≠ 0) :
    ∃ b : V, e' • b = b ∧ b ≠ 0 := by
  obtain ⟨y, hy⟩ := swapHerm_exists_ne hP ha0
  have hidem : e' * e' = e' := by
    have h0 : e' * e = 0 := by rw [mul_comm]; exact hee
    calc e' * e' = e' * (e + e') - e' * e := by ring
      _ = e' := by rw [he, h0, mul_one, sub_zero]
  refine ⟨e' • y, by rw [← mul_smul, hidem], fun h0 => hy ?_⟩
  have h1 : h a (e' • y) = h a y := by rw [hH.smul_right, ← swapHerm_part hce hH ha y]
  rw [← h1, h0, swapHerm_zero_right hH]

/- English proof (translation)
Establish `hβ` using `swapHerm_pair_ne hee hce hce' hu hH hP hno ha hb ha0 hb0`. Establish `hee' : e' * e = 0` using `by rw [mul_comm]; exact hee`. Establish `hidem : e * e = e`. Combine the equalities or inequalities in the displayed calculation. Establish `he0 : e ≠ 0`.

Introduce `h0`. Apply `ha0` to reduce the goal to its premises. Rewrite using `[← ha, h0, zero_smul]`. Establish `hpβ : h a b = e' * h a b` using `swapHerm_part hce hH ha b`. Establish `hpγ : h a z = e' * h a z` using `swapHerm_part hce hH ha z`.

Establish `hunit : IsUnit (e + h a b)`. Apply `hu` to reduce the goal to its premises. Rewrite using `[mul_add, hidem, hpβ, ← mul_assoc, hee, zero_mul, add_zero]`. Conclude with `he0`. Rewrite using `[mul_add, hee', zero_add, ← hpβ]`.

Conclude with `hβ`. Take `⟨U, hU⟩` from `hunit`. Establish `hβU : h a b = e' * ↑U` using `by rw [hU, mul_add, hee', zero_add, ← hpβ]`. Use `⟨h a z * ↑U⁻¹, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Establish `hw : e' • (z - (h a z * ↑U⁻¹) • b) = z - (h a z * ↑U⁻¹) • b`. Rewrite using `[smul_sub, hz, smul_comm, hb]`. Establish `hw0 : z - (h a z * ↑U⁻¹) • b ≠ 0` using `sub_ne_zero.mpr hne`. Apply `swapHerm_pair_ne hee hce hce' hu hH hP hno ha hw ha0 hw0` to reduce the goal to its premises. Rewrite using `[swapHerm_sub_right hH, hH.smul_right, hβU, show h a z * ↑U⁻¹ * (e' * ↑U) = h a z * e' * (↑U⁻¹ * ↑U) by ring, Units.inv_mul, mul_one, mul_comm, ← hpγ, sub_self]`.
-/
theorem swapHerm_coord {e e' : R} (he : e + e' = 1) (hee : e * e' = 0) (hce : c e = e') (hce' : c e' = e)
    (hu : ∀ u, e * u ≠ 0 → e' * u ≠ 0 → IsUnit u) (hH : IsHerm c h) (hP : IsPerfect h)
    (hno : ∀ x y, h x x = 0 → h x y ≠ 1) {a b : V} (ha : e • a = a) (hb : e' • b = b)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) {z : V} (hz : e' • z = z) : ∃ ρ : R, z = ρ • b := by
  have hβ := swapHerm_pair_ne hee hce hce' hu hH hP hno ha hb ha0 hb0
  have hee' : e' * e = 0 := by rw [mul_comm]; exact hee
  have hidem : e * e = e := by
    calc e * e = e * (e + e') - e * e' := by ring
      _ = e := by rw [he, hee, mul_one, sub_zero]
  have he0 : e ≠ 0 := by
    intro h0; apply ha0; rw [← ha, h0, zero_smul]
  have hpβ : h a b = e' * h a b := swapHerm_part hce hH ha b
  have hpγ : h a z = e' * h a z := swapHerm_part hce hH ha z
  have hunit : IsUnit (e + h a b) := by
    apply hu
    · rw [mul_add, hidem, hpβ, ← mul_assoc, hee, zero_mul, add_zero]; exact he0
    · rw [mul_add, hee', zero_add, ← hpβ]; exact hβ
  obtain ⟨U, hU⟩ := hunit
  have hβU : h a b = e' * ↑U := by rw [hU, mul_add, hee', zero_add, ← hpβ]
  refine ⟨h a z * ↑U⁻¹, ?_⟩
  by_contra hne
  have hw : e' • (z - (h a z * ↑U⁻¹) • b) = z - (h a z * ↑U⁻¹) • b := by
    rw [smul_sub, hz, smul_comm, hb]
  have hw0 : z - (h a z * ↑U⁻¹) • b ≠ 0 := sub_ne_zero.mpr hne
  apply swapHerm_pair_ne hee hce hce' hu hH hP hno ha hw ha0 hw0
  rw [swapHerm_sub_right hH, hH.smul_right, hβU,
    show h a z * ↑U⁻¹ * (e' * ↑U) = h a z * e' * (↑U⁻¹ * ↑U) by ring, Units.inv_mul, mul_one,
    mul_comm, ← hpγ, sub_self]

/- English proof (translation)
Establish `hee' : e' * e = 0` using `by rw [mul_comm]; exact hee`. Establish `he' : e' + e = 1` using `by rw [add_comm]; exact he`. Establish `hidem : e * e = e`. Combine the equalities or inequalities in the displayed calculation. Establish `hidem' : e' * e' = e'`.

Combine the equalities or inequalities in the displayed calculation. Establish `he'a : e' • a = 0` using `by rw [← ha, ← mul_smul, hee', zero_smul]`. Establish `heb : e • b = 0` using `by rw [← hb, ← mul_smul, hee, zero_smul]`. Use `⟨fun x => ?_, ?_⟩` and prove the remaining obligations. Take `⟨ρ', hρ'⟩` from `swapHerm_coord he hee hce hce' hu hH hP hno ha hb ha0 hb0 (z := e' • x) (by rw [← mul_smul, hidem'])`.

Take `⟨ρ, hρ⟩` from `swapHerm_coord he' hee' hce' hce (fun u h1 h2 => hu u h2 h1) hH hP hno hb ha hb0 ha0 (z := e • x) (by rw [← mul_smul, hidem])`. Use `⟨ρ * e + ρ' * e', ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add, add_smul, add_smul, mul_smul, mul_smul, mul_smul, mul_smul, ha, hb, he'a, heb, smul_zero, smul_zero, add_zero, zero_add, ← hρ, ← hρ', ← add_smul, he, one_smul]`. Establish `hβ` using `swapHerm_pair_ne hee hce hce' hu hH hP hno ha hb ha0 hb0`. Establish `haa : h a a = 0` using `swapHerm_self hee hce hH ha`.

Establish `hbb : h b b = 0` using `swapHerm_self hee' hce' hH hb`. Establish `hpβ : h a b = e' * h a b` using `swapHerm_part hce hH ha b`. Establish `hpβ' : h b a = e * h b a` using `swapHerm_part hce' hH hb a`. Establish `hβ' : h b a ≠ 0`. Introduce `h0`.

Apply `hβ` to reduce the goal to its premises. Rewrite using `[hH.symm b a, h0, map_zero]`. Rewrite using `[swapHerm_add_left hH, hH.add_right, hH.add_right, haa, hbb, zero_add, add_zero]`. Apply `hu` to reduce the goal to its premises. Rewrite using `[mul_add, hpβ, ← mul_assoc, hee, zero_mul, zero_add, ← hpβ']`.

Conclude with `hβ'`. Rewrite using `[mul_add, hpβ', ← mul_assoc, hee', zero_mul, add_zero, ← hpβ]`. Conclude with `hβ`.
-/
theorem swapHerm_gen {e e' : R} (he : e + e' = 1) (hee : e * e' = 0) (hce : c e = e') (hce' : c e' = e)
    (hu : ∀ u, e * u ≠ 0 → e' * u ≠ 0 → IsUnit u) (hH : IsHerm c h) (hP : IsPerfect h)
    (hno : ∀ x y, h x x = 0 → h x y ≠ 1) {a b : V} (ha : e • a = a) (hb : e' • b = b)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    (∀ x, ∃ r : R, x = r • (a + b)) ∧ IsUnit (h (a + b) (a + b)) := by
  have hee' : e' * e = 0 := by rw [mul_comm]; exact hee
  have he' : e' + e = 1 := by rw [add_comm]; exact he
  have hidem : e * e = e := by
    calc e * e = e * (e + e') - e * e' := by ring
      _ = e := by rw [he, hee, mul_one, sub_zero]
  have hidem' : e' * e' = e' := by
    calc e' * e' = e' * (e + e') - e' * e := by ring
      _ = e' := by rw [he, hee', mul_one, sub_zero]
  have he'a : e' • a = 0 := by rw [← ha, ← mul_smul, hee', zero_smul]
  have heb : e • b = 0 := by rw [← hb, ← mul_smul, hee, zero_smul]
  refine ⟨fun x => ?_, ?_⟩
  · obtain ⟨ρ', hρ'⟩ := swapHerm_coord he hee hce hce' hu hH hP hno ha hb ha0 hb0 (z := e' • x)
      (by rw [← mul_smul, hidem'])
    obtain ⟨ρ, hρ⟩ := swapHerm_coord he' hee' hce' hce (fun u h1 h2 => hu u h2 h1) hH hP hno hb ha hb0 ha0
      (z := e • x) (by rw [← mul_smul, hidem])
    refine ⟨ρ * e + ρ' * e', ?_⟩
    rw [smul_add, add_smul, add_smul, mul_smul, mul_smul, mul_smul, mul_smul, ha, hb, he'a, heb,
      smul_zero, smul_zero, add_zero, zero_add, ← hρ, ← hρ', ← add_smul, he, one_smul]
  · have hβ := swapHerm_pair_ne hee hce hce' hu hH hP hno ha hb ha0 hb0
    have haa : h a a = 0 := swapHerm_self hee hce hH ha
    have hbb : h b b = 0 := swapHerm_self hee' hce' hH hb
    have hpβ : h a b = e' * h a b := swapHerm_part hce hH ha b
    have hpβ' : h b a = e * h b a := swapHerm_part hce' hH hb a
    have hβ' : h b a ≠ 0 := by
      intro h0; apply hβ; rw [hH.symm b a, h0, map_zero]
    rw [swapHerm_add_left hH, hH.add_right, hH.add_right, haa, hbb, zero_add, add_zero]
    apply hu
    · rw [mul_add, hpβ, ← mul_assoc, hee, zero_mul, zero_add, ← hpβ']; exact hβ'
    · rw [mul_add, hpβ', ← mul_assoc, hee', zero_mul, add_zero, ← hpβ]; exact hβ

end SwapHerm

/- English proof (translation)
Take `⟨e, he_def⟩ : ∃ e : R, e = φ.symm (1, 0)` from `⟨_, rfl⟩`. Take `⟨e', he'_def⟩ : ∃ e' : R, e' = φ.symm (0, 1)` from `⟨_, rfl⟩`. Establish `hφe : φ e = (1, 0)` using `by rw [he_def]; simp`. Establish `hφe' : φ e' = (0, 1)` using `by rw [he'_def]; simp`. Apply the tactic sequence `have he : e + e' = 1 := φ.injective (by rw [map_add, hφe, hφe', map_one]; ext <;> simp)`.

Apply the tactic sequence `have hee : e * e' = 0 := φ.injective (by rw [map_mul, hφe, hφe', map_zero]; ext <;> simp)`. Establish `hce : c e = e'` using `φ.injective (by rw [hc, hφe, hφe']; rfl)`. Establish `hce' : c e' = e` using `φ.injective (by rw [hc, hφe, hφe']; rfl)`. Establish `hu : ∀ u : R, e * u ≠ 0 → e' * u ≠ 0 → IsUnit u`. Introduce `u h1 h2`.

Establish `h1' : (φ u).1 ≠ 0`. Introduce `h0`. Apply `h1` to reduce the goal to its premises. Apply `φ.injective` to reduce the goal to its premises. Apply the tactic sequence `rw [map_mul, hφe, map_zero]; ext <;> simp [h0]`.

Establish `h2' : (φ u).2 ≠ 0`. Introduce `h0`. Apply `h2` to reduce the goal to its premises. Apply `φ.injective` to reduce the goal to its premises. Apply the tactic sequence `rw [map_mul, hφe', map_zero]; ext <;> simp [h0]`.

Rewrite using `[← isUnit_map_iff φ, Prod.isUnit_iff]`. Conclude with `⟨isUnit_iff_ne_zero.mpr h1', isUnit_iff_ne_zero.mpr h2'⟩`. Establish `hee' : e' * e = 0` using `by rw [mul_comm]; exact hee`. Establish `he' : e' + e = 1` using `by rw [add_comm]; exact he`. Establish `hidem : e * e = e`.

Combine the equalities or inequalities in the displayed calculation. Establish `hidem' : e' * e' = e'`. Combine the equalities or inequalities in the displayed calculation. Break down `subsingleton_or_nontrivial V with hs | hs` into its components or cases. Conclude with `Or.inl hs`.

Use `right`. Take `⟨v, hv⟩` from `exists_ne (0 : V)`. Establish `hv' : v = e • v + e' • v` using `by rw [← add_smul, he, one_smul]`. Distinguish the cases in `hev : e • v = 0`. Establish `hb0 : e' • v ≠ 0` using `by intro h0; apply hv; rw [hv', hev, h0, add_zero]`.

Establish `hb : e' • (e' • v) = e' • v` using `by rw [← mul_smul, hidem']`. Take `⟨a, ha, ha0⟩` from `swapHerm_partner he' hee' hce' hH hP hb hb0`. Conclude with `⟨_, swapHerm_gen he hee hce hce' hu hH hP hno ha hb ha0 hb0⟩`. Establish `ha : e • (e • v) = e • v` using `by rw [← mul_smul, hidem]`. Take `⟨b, hb, hb0⟩` from `swapHerm_partner he hee hce hH hP ha hev`.

Conclude with `⟨_, swapHerm_gen he hee hce hce' hu hH hP hno ha hb hev hb0⟩`.
-/
theorem hermitian_split_rank_one_struct {k R V : Type} [Field k] [CommRing R] [AddCommGroup V] [Module R V]
    (φ : R ≃+* k × k) (c : R →+* R) (hc : ∀ r, φ (c r) = (φ r).swap) (h : V → V → R)
    (hH : IsHerm c h) (hP : IsPerfect h) (hno : ∀ x y, h x x = 0 → h x y ≠ 1) :
    Subsingleton V ∨ ∃ w₀ : V, (∀ x, ∃ r : R, x = r • w₀) ∧ IsUnit (h w₀ w₀) := by
  obtain ⟨e, he_def⟩ : ∃ e : R, e = φ.symm (1, 0) := ⟨_, rfl⟩
  obtain ⟨e', he'_def⟩ : ∃ e' : R, e' = φ.symm (0, 1) := ⟨_, rfl⟩
  have hφe : φ e = (1, 0) := by rw [he_def]; simp
  have hφe' : φ e' = (0, 1) := by rw [he'_def]; simp
  have he : e + e' = 1 := φ.injective (by rw [map_add, hφe, hφe', map_one]; ext <;> simp)
  have hee : e * e' = 0 := φ.injective (by rw [map_mul, hφe, hφe', map_zero]; ext <;> simp)
  have hce : c e = e' := φ.injective (by rw [hc, hφe, hφe']; rfl)
  have hce' : c e' = e := φ.injective (by rw [hc, hφe, hφe']; rfl)
  have hu : ∀ u : R, e * u ≠ 0 → e' * u ≠ 0 → IsUnit u := by
    intro u h1 h2
    have h1' : (φ u).1 ≠ 0 := by
      intro h0; apply h1; apply φ.injective
      rw [map_mul, hφe, map_zero]; ext <;> simp [h0]
    have h2' : (φ u).2 ≠ 0 := by
      intro h0; apply h2; apply φ.injective
      rw [map_mul, hφe', map_zero]; ext <;> simp [h0]
    rw [← isUnit_map_iff φ, Prod.isUnit_iff]
    exact ⟨isUnit_iff_ne_zero.mpr h1', isUnit_iff_ne_zero.mpr h2'⟩
  have hee' : e' * e = 0 := by rw [mul_comm]; exact hee
  have he' : e' + e = 1 := by rw [add_comm]; exact he
  have hidem : e * e = e := by
    calc e * e = e * (e + e') - e * e' := by ring
      _ = e := by rw [he, hee, mul_one, sub_zero]
  have hidem' : e' * e' = e' := by
    calc e' * e' = e' * (e + e') - e' * e := by ring
      _ = e' := by rw [he, hee', mul_one, sub_zero]
  rcases subsingleton_or_nontrivial V with hs | hs
  · exact Or.inl hs
  right
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hv' : v = e • v + e' • v := by rw [← add_smul, he, one_smul]
  by_cases hev : e • v = 0
  · have hb0 : e' • v ≠ 0 := by intro h0; apply hv; rw [hv', hev, h0, add_zero]
    have hb : e' • (e' • v) = e' • v := by rw [← mul_smul, hidem']
    obtain ⟨a, ha, ha0⟩ := swapHerm_partner he' hee' hce' hH hP hb hb0
    exact ⟨_, swapHerm_gen he hee hce hce' hu hH hP hno ha hb ha0 hb0⟩
  · have ha : e • (e • v) = e • v := by rw [← mul_smul, hidem]
    obtain ⟨b, hb, hb0⟩ := swapHerm_partner he hee hce hH hP ha hev
    exact ⟨_, swapHerm_gen he hee hce hce' hu hH hP hno ha hb hev hb0⟩

/- English proof (translation)
Introduce `k R V _ _ _ _ φ c hc h hH hP hno`. Conclude with `hermitian_split_rank_one_struct φ c hc h hH hP hno`.
-/
theorem hermSwap_struct : ∀ {k R V : Type} [Field k] [CommRing R] [AddCommGroup V] [Module R V]
    (φ : R ≃+* k × k) (c : R →+* R), (∀ r, φ (c r) = (φ r).swap) → ∀ h : V → V → R, IsHerm c h →
    IsPerfect h → (∀ x y, h x x = 0 → h x y ≠ 1) →
    Subsingleton V ∨ ∃ w₀ : V, (∀ x, ∃ r : R, x = r • w₀) ∧ IsUnit (h w₀ w₀) := by
  intro k R V _ _ _ _ φ c hc h hH hP hno
  exact hermitian_split_rank_one_struct φ c hc h hH hP hno

end GlobalTheory.CompanionTheory.KFin
