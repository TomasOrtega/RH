import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.IsogenyRamification
import GroundTheory.ArithmeticGeometry.AbelianVarieties.WeilPairing

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField

universe u

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F] {E E' E'' : WeierstrassCurve F}
  [E.IsElliptic] [E'.IsElliptic] [E''.IsElliptic]

/- English proof (translation)
Use `divisorOf_mul W hf (inv_ne_zero hf)` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel₀ hf, divisorOf_one]`. Conclude with `(neg_eq_of_add_eq_zero_right this.symm).symm`.
-/
theorem divisorOf_inv (W : WeierstrassCurve F) [W.IsElliptic] {f : W.toAffine.FunctionField}
    (hf : f ≠ 0) : divisorOf W f⁻¹ = -divisorOf W f := by
  have := divisorOf_mul W hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf, divisorOf_one] at this
  exact (neg_eq_of_add_eq_zero_right this.symm).symm

/- English proof (translation)
Establish `h` using `weilPairing_add_right hn hS (smul_zero n) (smul_zero n) (W := W)`. Rewrite `h` using `[add_zero]`. Establish `h0` using `weilPairing_ne_zero hn hS (smul_zero n) (W := W)`. Conclude with `(mul_eq_left₀ h0).mp h.symm`.
-/
theorem weilPairing_zero_right (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hn : (n : F) ≠ 0)
    {S : W.toAffine.Point} (hS : n • S = 0) : weilPairing W n S 0 = 1 := by
  have h := weilPairing_add_right hn hS (smul_zero n) (smul_zero n) (W := W)
  rw [add_zero] at h
  have h0 := weilPairing_ne_zero hn hS (smul_zero n) (W := W)
  exact (mul_eq_left₀ h0).mp h.symm

/- English proof (translation)
Establish `h` using `weilPairing_add_left hn (smul_zero n) (smul_zero n) hT (W := W)`. Rewrite `h` using `[add_zero]`. Establish `h0` using `weilPairing_ne_zero hn (smul_zero n) hT (W := W)`. Conclude with `(mul_eq_left₀ h0).mp h.symm`.
-/
theorem weilPairing_zero_left (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hn : (n : F) ≠ 0)
    {T : W.toAffine.Point} (hT : n • T = 0) : weilPairing W n 0 T = 1 := by
  have h := weilPairing_add_left hn (smul_zero n) (smul_zero n) hT (W := W)
  rw [add_zero] at h
  have h0 := weilPairing_ne_zero hn (smul_zero n) hT (W := W)
  exact (mul_eq_left₀ h0).mp h.symm

namespace Isogeny

variable (φ : Isogeny E E')

noncomputable instance fintypeKer : Fintype φ.pointHom.ker := Fintype.ofFinite _

/- English proof (translation)
Rewrite using `[Finsupp.finset_sum_apply]`. Simplify using `only [Finsupp.single_apply]`. Use `split_ifs with h`. Establish `hk : R - R₀ ∈ φ.pointHom.ker`. Rewrite using `[AddMonoidHom.mem_ker, map_sub, pointHom_apply, pointHom_apply, h, sub_self]`.

Rewrite using `[Finset.sum_eq_single ⟨R - R₀, hk⟩]`. Simplify using the standard rewrite rules. Introduce `T _ hT`. Rewrite using `[if_neg]`. Introduce `e`.

Conclude with `hT (Subtype.ext (show (T : E.toAffine.Point) = R - R₀ by rw [← e]; abel))`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Use `Finset.sum_eq_zero fun T _ => if_neg fun e => h ?_` and prove the remaining obligations. Rewrite using `[← e, ← pointHom_apply, ← pointHom_apply, map_add, T.2, add_zero]`.
-/
theorem sum_single_apply (R₀ R : E.toAffine.Point) :
    (∑ T : φ.pointHom.ker, Finsupp.single (R₀ + (T : E.toAffine.Point)) (1 : ℤ)) R =
      if φ.pointMap R = φ.pointMap R₀ then 1 else 0 := by
  classical
  rw [Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply]
  split_ifs with h
  · have hk : R - R₀ ∈ φ.pointHom.ker := by
      rw [AddMonoidHom.mem_ker, map_sub, pointHom_apply, pointHom_apply, h, sub_self]
    rw [Finset.sum_eq_single ⟨R - R₀, hk⟩]
    · simp
    · intro T _ hT
      rw [if_neg]
      intro e
      exact hT (Subtype.ext (show (T : E.toAffine.Point) = R - R₀ by rw [← e]; abel))
    · intro h; exact absurd (Finset.mem_univ _) h
  · refine Finset.sum_eq_zero fun T _ => if_neg fun e => h ?_
    rw [← e, ← pointHom_apply, ← pointHom_apply, map_add, T.2, add_zero]

/- English proof (translation)
Use `φ.sum_single_apply 0 R` as an intermediate fact. Simplify using `only [zero_add] at this`. Rewrite using `[this, ← pointHom_apply φ 0, map_zero]`.
-/
theorem sum_single_zero_apply (R : E.toAffine.Point) :
    (∑ T : φ.pointHom.ker, Finsupp.single (T : E.toAffine.Point) (1 : ℤ)) R =
      if φ.pointMap R = 0 then 1 else 0 := by
  have := φ.sum_single_apply 0 R
  simp only [zero_add] at this
  rw [this, ← pointHom_apply φ 0, map_zero]

noncomputable def pullbackPt (R₀ : E.toAffine.Point) : CurveDivisor E :=
  (φ.ramIdx : ℤ) • ∑ T : φ.pointHom.ker,
    (Finsupp.single (R₀ + (T : E.toAffine.Point)) 1 - Finsupp.single (T : E.toAffine.Point) 1)

/- English proof (translation)
Rewrite using `[pullbackPt, Finsupp.smul_apply, Finset.sum_sub_distrib, Finsupp.sub_apply, φ.sum_single_apply, φ.sum_single_zero_apply, smul_eq_mul]`.
-/
theorem pullbackPt_apply (R₀ R : E.toAffine.Point) :
    φ.pullbackPt R₀ R = (φ.ramIdx : ℤ) *
      ((if φ.pointMap R = φ.pointMap R₀ then 1 else 0) - (if φ.pointMap R = 0 then 1 else 0)) := by
  rw [pullbackPt, Finsupp.smul_apply, Finset.sum_sub_distrib, Finsupp.sub_apply,
    φ.sum_single_apply, φ.sum_single_zero_apply, smul_eq_mul]

/- English proof (translation)
Simplify using `[pullbackPt, map_sum]`.
-/
theorem divisorDegree_pullbackPt (R₀ : E.toAffine.Point) : divisorDegree E (φ.pullbackPt R₀) = 0 := by
  simp [pullbackPt, map_sum]

/- English proof (translation)
Simplify using `only [pullbackPt, map_zsmul, map_sum, map_sub, divisorSum_single, one_smul, add_sub_cancel_right, Finset.sum_const, Finset.card_univ]`. Rewrite using `[← φ.ramIdx_mul_card_ker, Nat.card_eq_fintype_card, ← natCast_zsmul, smul_smul]`. Use `push_cast`. Put the polynomial expressions in normal form.
-/
theorem divisorSum_pullbackPt (R₀ : E.toAffine.Point) :
    divisorSum E (φ.pullbackPt R₀) = (φ.degree : ℤ) • R₀ := by
  simp only [pullbackPt, map_zsmul, map_sum, map_sub, divisorSum_single, one_smul,
    add_sub_cancel_right, Finset.sum_const, Finset.card_univ]
  rw [← φ.ramIdx_mul_card_ker, Nat.card_eq_fintype_card, ← natCast_zsmul, smul_smul]
  push_cast
  ring_nf

/- English proof (translation)
Use extensionality with `R`. Rewrite using `[φ.divisorOf_comap hf', hdiv, Finsupp.smul_apply, Finsupp.smul_apply, pullbackPt_apply, Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply, hR₀]`. Simplify using `only [smul_eq_mul, eq_comm (a := T'), eq_comm (a := (0 : E'.toAffine.Point))]`. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem divisorOf_comap_of_eq {f' : E'.toAffine.FunctionField} (hf' : f' ≠ 0) {n : ℤ}
    {T' : E'.toAffine.Point} (hdiv : divisorOf E' f' = n • (Finsupp.single T' 1 - Finsupp.single 0 1))
    {R₀ : E.toAffine.Point} (hR₀ : φ.pointMap R₀ = T') :
    divisorOf E (φ.comap f') = n • φ.pullbackPt R₀ := by
  ext R
  rw [φ.divisorOf_comap hf', hdiv, Finsupp.smul_apply, Finsupp.smul_apply, pullbackPt_apply,
    Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply, hR₀]
  simp only [smul_eq_mul, eq_comm (a := T'), eq_comm (a := (0 : E'.toAffine.Point))]
  split_ifs <;> ring

/- English proof (translation)
Use `congrArg Isogeny.comap (φ.comp_mulIsogeny n hn)` as an intermediate fact. Rewrite `this` using `[comap_comp, comap_comp]`. Conclude with `DFunLike.congr_fun this f`.
-/
theorem comap_mulIsogeny_comm (n : ℤ) (hn : n ≠ 0) (f : E'.toAffine.FunctionField) :
    (mulIsogeny E n hn).comap (φ.comap f) = φ.comap ((mulIsogeny E' n hn).comap f) := by
  have := congrArg Isogeny.comap (φ.comp_mulIsogeny n hn)
  rw [comap_comp, comap_comp] at this
  exact DFunLike.congr_fun this f

/- English proof (translation)
Take `⟨f', g', hf', hg', hdiv, hn0, hpull⟩` from `exists_isWeilData E' hn hT'`. Take `⟨R₀, hR₀⟩` from `φ.pointMap_surjective T'`. Establish `hdual : φ.dual.pointMap T' = (φ.degree : ℤ) • R₀`. Rewrite using `[← hR₀, ← pointMap_comp, dual_comp, pointMap_mulIsogeny]`. Use `set D₀ := φ.pullbackPt R₀ - (Finsupp.single (φ.dual.pointMap T') 1 - Finsupp.single 0 1)`.

Take `⟨h, hh, hdivh⟩` from `exists_divisorOf_eq E (D := D₀) (by simp [D₀, divisorDegree_pullbackPt]) (by simp [D₀, divisorSum_pullbackPt, hdual])`. Use `set f := φ.comap f' * (h ^ n)⁻¹`. Use `set g := φ.comap g' * (mulIsogeny E n hn0).comap h⁻¹`. Establish `hcf : φ.comap f' ≠ 0` using `(map_ne_zero_iff _ φ.comap.toRingHom.injective).mpr hf'`. Establish `hcg : φ.comap g' ≠ 0` using `(map_ne_zero_iff _ φ.comap.toRingHom.injective).mpr hg'`.

Establish `hnh : (mulIsogeny E n hn0).comap h ≠ 0` using `(map_ne_zero_iff _ (mulIsogeny E n hn0).comap.toRingHom.injective).mpr hh`. Establish `hW : IsWeilData E n (φ.dual.pointMap T') f g`. Use `⟨mul_ne_zero hcf (inv_ne_zero (pow_ne_zero _ hh)), ?_, ?_, hn0, ?_⟩` and prove the remaining obligations. Conclude with `mul_ne_zero hcg (by rw [map_inv₀]; exact inv_ne_zero hnh)`. Rewrite using `[divisorOf_mul E hcf (inv_ne_zero (pow_ne_zero _ hh)), divisorOf_inv E (pow_ne_zero _ hh), divisorOf_pow E hh, hdivh, φ.divisorOf_comap_of_eq hf' hdiv hR₀]`.

Simplify using `only [D₀, natCast_zsmul, smul_sub]`. Normalize the expressions using the abelian group laws. Use `show (mulIsogeny E n hn0).comap f = g ^ n`. Rewrite using `[map_mul, map_inv₀, map_pow, φ.comap_mulIsogeny_comm, show (mulIsogeny E' n hn0).comap f' = g' ^ n from hpull, map_pow, mul_pow, map_inv₀, inv_pow]`. Apply `weilPairing_eq_of_translate_eq hS hW` to reduce the goal to its premises.

Establish `hSz : (n : ℤ) • S = 0` using `by rw [natCast_zsmul]; exact hS`. Establish `hφS : n • φ.pointMap S = 0`. Rewrite using `[← pointHom_apply, ← map_nsmul, hS, map_zero]`. Establish `ht` using `translate_eq_weilPairing_mul hφS ⟨hf', hg', hdiv, hn0, hpull⟩`. Establish `e1 : translate E S (φ.comap g') = φ.comap (translate E' (φ.pointMap S) g')` using `(DFunLike.congr_fun (φ.comap_comp_translate S) g').symm`.

Establish `e2 : translate E S ((mulIsogeny E n hn0).comap h⁻¹) = (mulIsogeny E n hn0).comap h⁻¹` using `translate_mulPullback_of_zsmul_eq_zero E hn0 hSz _`. Rewrite using `[map_mul, e1, e2, ht, map_mul, AlgHom.commutes]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem weilPairing_dual {n : ℕ} (hn : (n : F) ≠ 0) {S : E.toAffine.Point} (hS : n • S = 0)
    {T' : E'.toAffine.Point} (hT' : n • T' = 0) :
    weilPairing E n S (φ.dual.pointMap T') = weilPairing E' n (φ.pointMap S) T' := by
  obtain ⟨f', g', hf', hg', hdiv, hn0, hpull⟩ := exists_isWeilData E' hn hT'
  obtain ⟨R₀, hR₀⟩ := φ.pointMap_surjective T'
  have hdual : φ.dual.pointMap T' = (φ.degree : ℤ) • R₀ := by
    rw [← hR₀, ← pointMap_comp, dual_comp, pointMap_mulIsogeny]
  set D₀ := φ.pullbackPt R₀ - (Finsupp.single (φ.dual.pointMap T') 1 - Finsupp.single 0 1)
  obtain ⟨h, hh, hdivh⟩ := exists_divisorOf_eq E (D := D₀)
    (by simp [D₀, divisorDegree_pullbackPt])
    (by simp [D₀, divisorSum_pullbackPt, hdual])
  set f := φ.comap f' * (h ^ n)⁻¹
  set g := φ.comap g' * (mulIsogeny E n hn0).comap h⁻¹
  have hcf : φ.comap f' ≠ 0 := (map_ne_zero_iff _ φ.comap.toRingHom.injective).mpr hf'
  have hcg : φ.comap g' ≠ 0 := (map_ne_zero_iff _ φ.comap.toRingHom.injective).mpr hg'
  have hnh : (mulIsogeny E n hn0).comap h ≠ 0 :=
    (map_ne_zero_iff _ (mulIsogeny E n hn0).comap.toRingHom.injective).mpr hh
  have hW : IsWeilData E n (φ.dual.pointMap T') f g := by
    refine ⟨mul_ne_zero hcf (inv_ne_zero (pow_ne_zero _ hh)), ?_, ?_, hn0, ?_⟩
    · exact mul_ne_zero hcg (by rw [map_inv₀]; exact inv_ne_zero hnh)
    · rw [divisorOf_mul E hcf (inv_ne_zero (pow_ne_zero _ hh)), divisorOf_inv E (pow_ne_zero _ hh),
        divisorOf_pow E hh, hdivh, φ.divisorOf_comap_of_eq hf' hdiv hR₀]
      simp only [D₀, natCast_zsmul, smul_sub]
      abel
    · show (mulIsogeny E n hn0).comap f = g ^ n
      rw [map_mul, map_inv₀, map_pow, φ.comap_mulIsogeny_comm, show (mulIsogeny E' n hn0).comap f' =
        g' ^ n from hpull, map_pow, mul_pow, map_inv₀, inv_pow]
  apply weilPairing_eq_of_translate_eq hS hW
  have hSz : (n : ℤ) • S = 0 := by rw [natCast_zsmul]; exact hS
  have hφS : n • φ.pointMap S = 0 := by
    rw [← pointHom_apply, ← map_nsmul, hS, map_zero]
  have ht := translate_eq_weilPairing_mul hφS ⟨hf', hg', hdiv, hn0, hpull⟩
  have e1 : translate E S (φ.comap g') = φ.comap (translate E' (φ.pointMap S) g') :=
    (DFunLike.congr_fun (φ.comap_comp_translate S) g').symm
  have e2 : translate E S ((mulIsogeny E n hn0).comap h⁻¹) = (mulIsogeny E n hn0).comap h⁻¹ :=
    translate_mulPullback_of_zsmul_eq_zero E hn0 hSz _
  rw [map_mul, e1, e2, ht, map_mul, AlgHom.commutes]
  ring

end Isogeny

section Hom

noncomputable def homPt (Q : isogHom E E') : E.toAffine.Point →+ E'.toAffine.Point :=
  open Classical in if h : Q = 0 then 0 else (isogOfHom Q h).pointHom

/- English proof (translation)
Distinguish the cases in `h : Q = 0`. Substitute `h` using the available equality. Rewrite using `[homPt, dif_pos rfl, AddMonoidHom.zero_apply, map_zero, add_zero, ZeroMemClass.coe_zero, map_zero]`. Rewrite using `[homPt, dif_neg h]`. Conclude with `(isogOfHom Q h).map_translate R`.
-/
theorem map_translate_hom (Q : isogHom E E') (R : E.toAffine.Point) :
    Point.map (translate E R) Q.1 = Q.1 + constMap E' E.toAffine.FunctionField (homPt Q R) := by
  by_cases h : Q = 0
  · subst h
    rw [homPt, dif_pos rfl, AddMonoidHom.zero_apply, map_zero, add_zero, ZeroMemClass.coe_zero,
      map_zero]
  · rw [homPt, dif_neg h]
    exact (isogOfHom Q h).map_translate R

/- English proof (translation)
Rewrite `h` using `[map_translate_hom, add_right_inj]`. Conclude with `constMap_injective _ _ h`.
-/
theorem homPt_eq_of (Q : isogHom E E') {R : E.toAffine.Point} {c : E'.toAffine.Point}
    (h : Point.map (translate E R) Q.1 = Q.1 + constMap E' E.toAffine.FunctionField c) :
    homPt Q R = c := by
  rw [map_translate_hom, add_right_inj] at h
  exact constMap_injective _ _ h

/- English proof (translation)
Use extensionality with `R`. Apply `homPt_eq_of` to reduce the goal to its premises. Rewrite using `[AddSubgroup.coe_add, map_add, map_translate_hom, map_translate_hom, AddMonoidHom.add_apply, map_add]`. Normalize the expressions using the abelian group laws.
-/
theorem homPt_add (Q₁ Q₂ : isogHom E E') : homPt (Q₁ + Q₂) = homPt Q₁ + homPt Q₂ := by
  ext R
  apply homPt_eq_of
  rw [AddSubgroup.coe_add, map_add, map_translate_hom, map_translate_hom, AddMonoidHom.add_apply,
    map_add]
  abel

/- English proof (translation)
Rewrite using `[homPt, dif_pos rfl]`.
-/
theorem homPt_zero : homPt (0 : isogHom E E') = 0 := by rw [homPt, dif_pos rfl]

noncomputable def homPointHom : isogHom E E' →+ (E.toAffine.Point →+ E'.toAffine.Point) :=
  AddMonoidHom.mk' homPt homPt_add

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem homPointHom_apply (Q : isogHom E E') : homPointHom Q = homPt Q := rfl

/- English proof (translation)
Use extensionality with `R`. Apply `homPt_eq_of` to reduce the goal to its premises. Conclude with `φ.map_translate R`.
-/
theorem homPt_toHom (φ : Isogeny E E') : homPt φ.toHom = φ.pointHom := by
  ext R
  apply homPt_eq_of
  exact φ.map_translate R

noncomputable def homDualFun (Q : isogHom E E') : isogHom E' E :=
  open Classical in if h : Q = 0 then 0 else (isogOfHom Q h).dual.toHom

/- English proof (translation)
Rewrite using `[homDualFun, dif_neg φ.toHom_ne_zero]`. Both sides reduce to the same expression.
-/
theorem homDualFun_toHom (φ : Isogeny E E') : homDualFun φ.toHom = φ.dual.toHom := by
  rw [homDualFun, dif_neg φ.toHom_ne_zero]
  rfl

/- English proof (translation)
Rewrite using `[homDualFun, dif_pos rfl]`.
-/
theorem homDualFun_zero : homDualFun (0 : isogHom E E') = 0 := by rw [homDualFun, dif_pos rfl]

/- English proof (translation)
Distinguish the cases in `h : Q = 0`. Substitute `h` using the available equality. Rewrite using `[homDualFun_zero, homPt_zero, homPt_zero, AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, weilPairing_zero_right E hn hS, weilPairing_zero_left E' hn hT']`. Rewrite using `[← isogOfHom_toHom Q h, homDualFun_toHom, homPt_toHom, homPt_toHom]`. Conclude with `(isogOfHom Q h).weilPairing_dual hn hS hT'`.
-/
theorem weilPairing_homDualFun (Q : isogHom E E') {n : ℕ} (hn : (n : F) ≠ 0) {S : E.toAffine.Point}
    (hS : n • S = 0) {T' : E'.toAffine.Point} (hT' : n • T' = 0) :
    weilPairing E n S (homPt (homDualFun Q) T') = weilPairing E' n (homPt Q S) T' := by
  by_cases h : Q = 0
  · subst h
    rw [homDualFun_zero, homPt_zero, homPt_zero, AddMonoidHom.zero_apply, AddMonoidHom.zero_apply,
      weilPairing_zero_right E hn hS, weilPairing_zero_left E' hn hT']
  · rw [← isogOfHom_toHom Q h, homDualFun_toHom, homPt_toHom, homPt_toHom]
    exact (isogOfHom Q h).weilPairing_dual hn hS hT'

/- English proof (translation)
Assume the negation of the conclusion as `hZ`. Use `set χ := isogOfHom Z hZ`. Establish `hχ : homPt Z = χ.pointHom` using `by rw [← homPt_toHom, isogOfHom_toHom]`. Choose the witnesses or unpack the hypotheses as in `⟨ℓ, hℓ2, hℓ⟩ : ∃ ℓ : ℕ, 2 ≤ ℓ ∧ (ℓ : F) ≠ 0 := by`. Distinguish the cases in `h2 : (2 : F) = 0`.

Use `⟨3, by norm_num, fun h3 => ?_⟩` and prove the remaining obligations. Establish `: (3 : F) - 2 = 1` using `by ring`. Rewrite `h3` using `[show ((3 : ℕ) : F) = 3 by norm_num]`. Rewrite `this` using `[h3, h2, sub_zero]`. Conclude with `zero_ne_one this`.

Conclude with `⟨2, le_refl _, by exact_mod_cast h2⟩`. Use `set N := Nat.card χ.pointHom.ker`. Use `set n := ℓ ^ (N + 1)`. Establish `hn : (n : F) ≠ 0` using `by push_cast [n]; exact pow_ne_zero _ hℓ`. Establish `hnZ : ((n : ℤ) : F) ≠ 0` using `by exact_mod_cast hn`.

Establish `hcard` using `card_zsmul_eq_zero E' hnZ`. Establish `hinj : Function.Injective (fun T' : {P : E'.toAffine.Point // (n : ℤ) • P = 0} => (⟨T'.1, by`. Rewrite using `[AddMonoidHom.mem_ker, ← hχ]`. Conclude with `h n hn T'.1 (by rw [← natCast_zsmul]; exact T'.2)⟩ : χ.pointHom.ker)) := by`. Introduce `a b hab`.

Apply `Subtype.ext` to reduce the goal to its premises. Establish `h2` using `congrArg (fun x : χ.pointHom.ker => (x : E'.toAffine.Point)) hab`. Conclude with `h2`. Establish `hle` using `Nat.card_le_card_of_injective _ hinj`. Rewrite `hle` using `[hcard, Int.natAbs_natCast]`.

Establish `h1 : N < n`. Combine the equalities or inequalities in the displayed calculation. Use `Nat.lt_two_pow_self (n := N)` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Use `_ ≤ n := Nat.pow_le_pow_left hℓ2 _`.

Establish `h2 : n ≤ n ^ 2` using `by nlinarith`. Use linear arithmetic over natural numbers and integers.
-/
theorem eq_zero_of_forall_torsion (Z : isogHom E' E)
    (h : ∀ n : ℕ, (n : F) ≠ 0 → ∀ T' : E'.toAffine.Point, n • T' = 0 → homPt Z T' = 0) : Z = 0 := by
  by_contra hZ
  set χ := isogOfHom Z hZ
  have hχ : homPt Z = χ.pointHom := by rw [← homPt_toHom, isogOfHom_toHom]
  obtain ⟨ℓ, hℓ2, hℓ⟩ : ∃ ℓ : ℕ, 2 ≤ ℓ ∧ (ℓ : F) ≠ 0 := by
    by_cases h2 : (2 : F) = 0
    · refine ⟨3, by norm_num, fun h3 => ?_⟩
      have : (3 : F) - 2 = 1 := by ring
      rw [show ((3 : ℕ) : F) = 3 by norm_num] at h3
      rw [h3, h2, sub_zero] at this
      exact zero_ne_one this
    · exact ⟨2, le_refl _, by exact_mod_cast h2⟩
  set N := Nat.card χ.pointHom.ker
  set n := ℓ ^ (N + 1)
  have hn : (n : F) ≠ 0 := by push_cast [n]; exact pow_ne_zero _ hℓ
  have hnZ : ((n : ℤ) : F) ≠ 0 := by exact_mod_cast hn
  have hcard := card_zsmul_eq_zero E' hnZ
  have hinj : Function.Injective (fun T' : {P : E'.toAffine.Point // (n : ℤ) • P = 0} =>
      (⟨T'.1, by
        rw [AddMonoidHom.mem_ker, ← hχ]
        exact h n hn T'.1 (by rw [← natCast_zsmul]; exact T'.2)⟩ : χ.pointHom.ker)) := by
    intro a b hab
    apply Subtype.ext
    have h2 := congrArg (fun x : χ.pointHom.ker => (x : E'.toAffine.Point)) hab
    exact h2
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [hcard, Int.natAbs_natCast] at hle
  have h1 : N < n := by
    calc N < 2 ^ (N + 1) := by
          have := Nat.lt_two_pow_self (n := N)
          calc N < 2 ^ N := this
            _ ≤ 2 ^ (N + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ N)
      _ ≤ n := Nat.pow_le_pow_left hℓ2 _
  have h2 : n ≤ n ^ 2 := by nlinarith
  omega

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Apply `eq_zero_of_forall_torsion` to reduce the goal to its premises. Introduce `n hn T' hT'`. Establish `htor : ∀ Q : isogHom E' E, n • homPt Q T' = 0` using `fun Q => by`. Rewrite using `[← map_nsmul, hT', map_zero]`.

Establish `htorS : ∀ (Q : isogHom E E') (S : E.toAffine.Point), n • S = 0 → n • homPt Q S = 0` using `fun Q S hS => by rw [← map_nsmul, hS, map_zero]`. Rewrite using `[show homPt (homDualFun (Q₁ + Q₂) - (homDualFun Q₁ + homDualFun Q₂)) = homPt (homDualFun (Q₁ + Q₂)) - homPt (homDualFun Q₁) - homPt (homDualFun Q₂) by`. Rewrite using `[← homPointHom_apply, map_sub, map_add, homPointHom_apply, homPointHom_apply, homPointHom_apply]`. Use the proof step `abel]`. Apply `eq_zero_of_forall_weilPairing_eq_one hn (by` to reduce the goal to its premises.

Simplify using `only [AddMonoidHom.sub_apply, nsmul_sub, htor, sub_zero])`. Introduce `S hS`. Use `set a := homPt (homDualFun (Q₁ + Q₂)) T'`. Use `set b := homPt (homDualFun Q₁) T'`. Use `set c := homPt (homDualFun Q₂) T'`.

Establish `hinv : ∀ x : E.toAffine.Point, n • x = 0 → weilPairing E n S (-x) * weilPairing E n S x = 1`. Introduce `x hx`. Rewrite using `[← weilPairing_add_right hn hS (by rw [smul_neg, hx, neg_zero]) hx, neg_add_cancel, weilPairing_zero_right E hn hS]`. Establish `ha : weilPairing E n S a = weilPairing E n S b * weilPairing E n S c`. Rewrite using `[weilPairing_homDualFun _ hn hS hT', weilPairing_homDualFun _ hn hS hT', weilPairing_homDualFun _ hn hS hT', homPt_add, AddMonoidHom.add_apply, weilPairing_add_left hn (htorS _ _ hS) (htorS _ _ hS) hT']`.

Establish `hA : n • a = 0` using `htor _`. Establish `hB : n • b = 0` using `htor _`. Establish `hC : n • c = 0` using `htor _`. Establish `hx : n • (a - b - c) = 0` using `by rw [nsmul_sub, nsmul_sub, hA, hB, hC, sub_zero, sub_zero]`. Establish `e1 : weilPairing E n S a = weilPairing E n S (a - b - c) * weilPairing E n S b * weilPairing E n S c` using `by conv_lhs => rw [show a = (a - b - c) + b + c by abel]`.

Rewrite using `[weilPairing_add_right hn hS (by rw [nsmul_add, hx, hB, add_zero]) hC, weilPairing_add_right hn hS hx hB]`. Establish `hne : weilPairing E n S b * weilPairing E n S c ≠ 0` using `mul_ne_zero (weilPairing_ne_zero hn hS hB) (weilPairing_ne_zero hn hS hC)`. Rewrite `e1` using `[ha, mul_assoc]`. Conclude with `(mul_eq_right₀ hne).mp e1.symm`.
-/
theorem homDualFun_add (Q₁ Q₂ : isogHom E E') :
    homDualFun (Q₁ + Q₂) = homDualFun Q₁ + homDualFun Q₂ := by
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_torsion
  intro n hn T' hT'
  have htor : ∀ Q : isogHom E' E, n • homPt Q T' = 0 := fun Q => by
    rw [← map_nsmul, hT', map_zero]
  have htorS : ∀ (Q : isogHom E E') (S : E.toAffine.Point), n • S = 0 → n • homPt Q S = 0 :=
    fun Q S hS => by rw [← map_nsmul, hS, map_zero]
  rw [show homPt (homDualFun (Q₁ + Q₂) - (homDualFun Q₁ + homDualFun Q₂)) =
      homPt (homDualFun (Q₁ + Q₂)) - homPt (homDualFun Q₁) - homPt (homDualFun Q₂) by
    rw [← homPointHom_apply, map_sub, map_add, homPointHom_apply, homPointHom_apply,
      homPointHom_apply]; abel]
  apply eq_zero_of_forall_weilPairing_eq_one hn (by
    simp only [AddMonoidHom.sub_apply, nsmul_sub, htor, sub_zero])
  intro S hS
  set a := homPt (homDualFun (Q₁ + Q₂)) T'
  set b := homPt (homDualFun Q₁) T'
  set c := homPt (homDualFun Q₂) T'
  have hinv : ∀ x : E.toAffine.Point, n • x = 0 →
      weilPairing E n S (-x) * weilPairing E n S x = 1 := by
    intro x hx
    rw [← weilPairing_add_right hn hS (by rw [smul_neg, hx, neg_zero]) hx, neg_add_cancel,
      weilPairing_zero_right E hn hS]
  have ha : weilPairing E n S a = weilPairing E n S b * weilPairing E n S c := by
    rw [weilPairing_homDualFun _ hn hS hT', weilPairing_homDualFun _ hn hS hT',
      weilPairing_homDualFun _ hn hS hT', homPt_add, AddMonoidHom.add_apply,
      weilPairing_add_left hn (htorS _ _ hS) (htorS _ _ hS) hT']
  have hA : n • a = 0 := htor _
  have hB : n • b = 0 := htor _
  have hC : n • c = 0 := htor _
  have hx : n • (a - b - c) = 0 := by rw [nsmul_sub, nsmul_sub, hA, hB, hC, sub_zero, sub_zero]
  have e1 : weilPairing E n S a =
      weilPairing E n S (a - b - c) * weilPairing E n S b * weilPairing E n S c := by
    conv_lhs => rw [show a = (a - b - c) + b + c by abel]
    rw [weilPairing_add_right hn hS (by rw [nsmul_add, hx, hB, add_zero]) hC,
      weilPairing_add_right hn hS hx hB]
  have hne : weilPairing E n S b * weilPairing E n S c ≠ 0 :=
    mul_ne_zero (weilPairing_ne_zero hn hS hB) (weilPairing_ne_zero hn hS hC)
  rw [ha, mul_assoc] at e1
  exact (mul_eq_right₀ hne).mp e1.symm

noncomputable def homDual : isogHom E E' →+ isogHom E' E :=
  AddMonoidHom.mk' homDualFun homDualFun_add

/- English proof (translation)
The claim follows from `homDualFun_toHom φ`.
-/
theorem homDual_toHom (φ : Isogeny E E') : homDual φ.toHom = φ.dual.toHom := homDualFun_toHom φ

end Hom

end GroundTheory.Arith.Abelian
