import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.ThetaD

section general
variable {R : Type} [CommRing R] (I : Ideal R)

/- English proof (translation)
Proceed by induction on `y using AdicCompletion.induction_on with`. Consider the case `_ x`. Simplify using `only [AdicCompletion.evalₐ_mk]`. Rewrite using `[← AdicCompletion.Ideal.mk_eq_mk I h x]`. Both sides reduce to the same expression.
-/
theorem factorPow_evalₐ {m n : ℕ} (h : m ≤ n) (y : AdicCompletion I R) :
    Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I n y) = AdicCompletion.evalₐ I m y := by
  induction y using AdicCompletion.induction_on with
  | _ x =>
    simp only [AdicCompletion.evalₐ_mk]
    rw [← AdicCompletion.Ideal.mk_eq_mk I h x]
    rfl

/- English proof (translation)
Establish `key : IsUnit (AdicCompletion.evalₐ I (n + 1) y)`. Take `⟨a, ha⟩` from `Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) y)`. Rewrite `hy` using `[← factorPow_evalₐ I (show 1 ≤ n + 1 by omega), ← ha]`. Take `⟨b, hb⟩` from `hy.exists_right_inv`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective b`.

Establish `h1 : a * b - 1 ∈ I ^ 1`. Rewrite using `[← Ideal.Quotient.eq]`. Conclude with `hb`. Rewrite `h1` using `[pow_one]`. Establish `hn : IsNilpotent (Ideal.Quotient.mk (I ^ (n + 1)) (a * b - 1))` using `⟨n + 1, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow h1 _⟩`.

Establish `hu` using `hn.isUnit_add_one`. Rewrite `hu` using `[map_sub, map_one, sub_add_cancel, map_mul]`. Rewrite using `[← ha]`. Conclude with `isUnit_of_mul_isUnit_left hu`. Rewrite using `[← factorPow_evalₐ I (Nat.le_succ n)]`.

Conclude with `key.map _`.
-/
theorem isUnit_evalₐ (y : AdicCompletion I R) (hy : IsUnit (AdicCompletion.evalₐ I 1 y)) (n : ℕ) :
    IsUnit (AdicCompletion.evalₐ I n y) := by
  have key : IsUnit (AdicCompletion.evalₐ I (n + 1) y) := by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) y)
    rw [← factorPow_evalₐ I (show 1 ≤ n + 1 by omega), ← ha] at hy
    obtain ⟨b, hb⟩ := hy.exists_right_inv
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have h1 : a * b - 1 ∈ I ^ 1 := by
      rw [← Ideal.Quotient.eq]
      exact hb
    rw [pow_one] at h1
    have hn : IsNilpotent (Ideal.Quotient.mk (I ^ (n + 1)) (a * b - 1)) :=
      ⟨n + 1, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow h1 _⟩
    have hu := hn.isUnit_add_one
    rw [map_sub, map_one, sub_add_cancel, map_mul] at hu
    rw [← ha]
    exact isUnit_of_mul_isUnit_left hu
  rw [← factorPow_evalₐ I (Nat.le_succ n)]
  exact key.map _

/- English proof (translation)
Set `f : (n : ℕ) → Localization.Away y →+* R ⧸ I ^ n` to `fun n => IsLocalization.Away.lift (g := (AdicCompletion.evalₐ I n).toRingHom) y (isUnit_evalₐ I y hy n)`. Establish `hf0 : ∀ n x, f n (algebraMap _ _ x) = AdicCompletion.evalₐ I n x` using `fun n x => IsLocalization.Away.lift_eq y _ x`. Establish `hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow I hle).comp (f n) = f m`. Introduce `m n hle`. Use `IsLocalization.ringHom_ext (Submonoid.powers y) (RingHom.ext fun x => ?_)` and prove the remaining obligations.

Simplify using `only [RingHom.comp_apply, hf0, factorPow_evalₐ]`. Establish `e : AdicCompletion.liftRingHom I f hf (algebraMap _ _ y) = y` using `AdicCompletion.ext_evalₐ fun n => by rw [AdicCompletion.evalₐ_liftRingHom, hf0]`. Rewrite using `[← e]`. Conclude with `(IsLocalization.Away.algebraMap_isUnit y).map _`.
-/
theorem isUnit_of_evalₐ (y : AdicCompletion I R) (hy : IsUnit (AdicCompletion.evalₐ I 1 y)) :
    IsUnit y := by
  let f : (n : ℕ) → Localization.Away y →+* R ⧸ I ^ n := fun n =>
    IsLocalization.Away.lift (g := (AdicCompletion.evalₐ I n).toRingHom) y (isUnit_evalₐ I y hy n)
  have hf0 : ∀ n x, f n (algebraMap _ _ x) = AdicCompletion.evalₐ I n x := fun n x =>
    IsLocalization.Away.lift_eq y _ x
  have hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow I hle).comp (f n) = f m := by
    intro m n hle
    refine IsLocalization.ringHom_ext (Submonoid.powers y) (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply, hf0, factorPow_evalₐ]
  have e : AdicCompletion.liftRingHom I f hf (algebraMap _ _ y) = y :=
    AdicCompletion.ext_evalₐ fun n => by rw [AdicCompletion.evalₐ_liftRingHom, hf0]
  rw [← e]
  exact (IsLocalization.Away.algebraMap_isUnit y).map _

end general

variable (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Introduce `x`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Establish `hl : 0 < l` using `(Fact.out : l.Prime).pos`. Take `⟨b, hb⟩` from `IsAlgClosed.exists_pow_nat_eq (a : ℂ_[l]) hl`. Establish `hb1 : b ∈ 𝓞_ℂ_[l]`.

Rewrite using `[GlobalTheory.RingBasics.mem_OC]`. Use `(GlobalTheory.RingBasics.mem_OC _).1 a.2` as an intermediate fact. Rewrite `this` using `[← hb, norm_pow]`. Conclude with `(pow_le_one_iff_of_nonneg (norm_nonneg _) hl.ne').1 this`. Use `⟨Ideal.Quotient.mk _ ⟨b, hb1⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[frobenius_def, ← map_pow]`. Conclude with `congrArg _ (Subtype.ext hb)`.
-/
theorem frob_surj : Function.Surjective (frobenius (ModP (Per.OC l) l) l) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hl : 0 < l := (Fact.out : l.Prime).pos
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (a : ℂ_[l]) hl
  have hb1 : b ∈ 𝓞_ℂ_[l] := by
    rw [GlobalTheory.RingBasics.mem_OC]
    have := (GlobalTheory.RingBasics.mem_OC _).1 a.2
    rw [← hb, norm_pow] at this
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hl.ne').1 this
  refine ⟨Ideal.Quotient.mk _ ⟨b, hb1⟩, ?_⟩
  rw [frobenius_def, ← map_pow]
  exact congrArg _ (Subtype.ext hb)

/- English proof (translation)
The claim follows from `surjective_fontaineTheta (frob_surj l)`.
-/
theorem θ_surj : Function.Surjective (Per.θ l) := surjective_fontaineTheta (frob_surj l)

/- English proof (translation)
The claim follows from `GlobalTheory.RingIface.toC_alg l x`.
-/
theorem toC_alg (x : Per.OC l) : Per.toC l (algebraMap _ _ x) = (x : ℂ_[l]) :=
  GlobalTheory.RingIface.toC_alg l x

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨n, a, ha⟩` from `IsLocalization.Away.surj ((l : ℕ) : Per.OC l) x`. Establish `h` using `congrArg (Per.toC l) ha`. Rewrite `h` using `[map_mul, hx, zero_mul, toC_alg]`.

Establish `h0 : a = 0` using `Subtype.ext h.symm`. Rewrite `ha` using `[h0, map_zero]`. Conclude with `((IsLocalization.Away.algebraMap_isUnit ((l : ℕ) : Per.OC l)).pow n).mul_left_eq_zero.1 ha`.
-/
theorem toC_injective : Function.Injective (Per.toC l) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj ((l : ℕ) : Per.OC l) x
  have h := congrArg (Per.toC l) ha
  rw [map_mul, hx, zero_mul, toC_alg] at h
  have h0 : a = 0 := Subtype.ext h.symm
  rw [h0, map_zero] at ha
  exact ((IsLocalization.Away.algebraMap_isUnit ((l : ℕ) : Per.OC l)).pow n).mul_left_eq_zero.1 ha

/- English proof (translation)
The claim follows from `GlobalTheory.RingIface.fontaineTheta_algebraMap l a`.
-/
theorem fontaineTheta_algebraMap₂ (a : Per.Ainf l) : Per.θP l (algebraMap _ _ a) = (Per.θ l a : ℂ_[l]) :=
  GlobalTheory.RingIface.fontaineTheta_algebraMap l a

/- English proof (translation)
Use `⟨fun h => ?_, fun h => GlobalTheory.RingBasics.fontaineTheta_eq_zero_of_mem_ker l a (by rwa [pow_one])⟩` and prove the remaining obligations. Take `⟨⟨x, s⟩, hx⟩` from `IsLocalization.surj (Submonoid.powers (l : Per.Ainf l)) a`. Establish `hs` using `IsLocalization.map_units (Per.AinfP l) s`. Establish `h1` using `congrArg (Per.θP l) hx`. Rewrite `h1` using `[map_mul, h, zero_mul, fontaineTheta_algebraMap₂]`.

Establish `h2 : Per.θ l x = 0` using `Subtype.ext h1.symm`. Establish `h3` using `GlobalTheory.RingIface.alg_mem_kerP l h2`. Establish `h4 : a * algebraMap (Per.Ainf l) (Per.AinfP l) (s : Per.Ainf l) ∈ Per.kerP l`. Rewrite using `[hx]`. Conclude with `h3`.

Conclude with `(Ideal.mul_unit_mem_iff_mem _ hs).1 h4`.
-/
theorem fontaineTheta_eq_zero (a : Per.AinfP l) : Per.θP l a = 0 ↔ a ∈ Per.kerP l := by
  refine ⟨fun h => ?_, fun h => GlobalTheory.RingBasics.fontaineTheta_eq_zero_of_mem_ker l a (by rwa [pow_one])⟩
  obtain ⟨⟨x, s⟩, hx⟩ := IsLocalization.surj (Submonoid.powers (l : Per.Ainf l)) a
  have hs := IsLocalization.map_units (Per.AinfP l) s
  have h1 := congrArg (Per.θP l) hx
  rw [map_mul, h, zero_mul, fontaineTheta_algebraMap₂] at h1
  have h2 : Per.θ l x = 0 := Subtype.ext h1.symm
  have h3 := GlobalTheory.RingIface.alg_mem_kerP l h2
  have h4 : a * algebraMap (Per.Ainf l) (Per.AinfP l) (s : Per.Ainf l) ∈ Per.kerP l := by
    rw [hx]; exact h3
  exact (Ideal.mul_unit_mem_iff_mem _ hs).1 h4

/- English proof (translation)
Introduce `c`. Choose the witnesses or unpack the hypotheses as in `⟨n, hn⟩ : ∃ n : ℕ, ‖(l : ℂ_[l]) ^ n * c‖ ≤ 1 := by`. Establish `h` using `(tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (l : ℂ_[l])) GlobalTheory.RingBasics.norm_p_lt).mul_const ‖c‖`. Rewrite `h` using `[zero_mul]`. Take `⟨n, hn⟩` from `(h.eventually (ge_mem_nhds one_pos)).exists`.

Conclude with `⟨n, by rwa [norm_mul, norm_pow]⟩`. Take `⟨a, ha⟩` from `θ_surj l ⟨_, (GlobalTheory.RingBasics.mem_OC _).2 hn⟩`. Take `⟨u, hu⟩` from `((GlobalTheory.RingBasics.isUnit_l l).pow n).exists_left_inv`. Use `⟨u * algebraMap _ _ a, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (Per.θP l) hu`.

Rewrite `h` using `[map_mul, map_pow, map_natCast, map_one]`. Rewrite using `[map_mul, fontaineTheta_algebraMap₂, ha]`. Express the relevant statement in the definitionally equal form `_ * (_ * c) = c`. Rewrite using `[← mul_assoc, h, one_mul]`.
-/
theorem fontaineTheta_surjective' : Function.Surjective (Per.θP l) := by
  intro c
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖(l : ℂ_[l]) ^ n * c‖ ≤ 1 := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (l : ℂ_[l])) GlobalTheory.RingBasics.norm_p_lt).mul_const ‖c‖
    rw [zero_mul] at h
    obtain ⟨n, hn⟩ := (h.eventually (ge_mem_nhds one_pos)).exists
    exact ⟨n, by rwa [norm_mul, norm_pow]⟩
  obtain ⟨a, ha⟩ := θ_surj l ⟨_, (GlobalTheory.RingBasics.mem_OC _).2 hn⟩
  obtain ⟨u, hu⟩ := ((GlobalTheory.RingBasics.isUnit_l l).pow n).exists_left_inv
  refine ⟨u * algebraMap _ _ a, ?_⟩
  have h := congrArg (Per.θP l) hu
  rw [map_mul, map_pow, map_natCast, map_one] at h
  rw [map_mul, fontaineTheta_algebraMap₂, ha]
  change _ * (_ * c) = c
  rw [← mul_assoc, h, one_mul]

/- English proof (translation)
Use `RingHom.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers (l : Per.Ainf l)) (j := (Per.θP l).comp (Per.extP (Per.σA g))) (k := (Per.σC g).comp (Per.θP l)) (RingHom.ext fun y => ?_)) a` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply, GlobalTheory.RingBasics.awayMap_algebraMap₂, fontaineTheta_algebraMap₂, GlobalTheory.RingBasics.θ_σA]`. Conclude with `GlobalTheory.RingIface.sigO_coe l g _`.
-/
theorem θP_σ (g : Per.Gq l) (a : Per.AinfP l) :
    Per.θP l (Per.extP (Per.σA g) a) = Per.σC g (Per.θP l a) := by
  refine RingHom.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers (l : Per.Ainf l))
    (j := (Per.θP l).comp (Per.extP (Per.σA g))) (k := (Per.σC g).comp (Per.θP l))
    (RingHom.ext fun y => ?_)) a
  simp only [RingHom.comp_apply, GlobalTheory.RingBasics.awayMap_algebraMap₂, fontaineTheta_algebraMap₂, GlobalTheory.RingBasics.θ_σA]
  exact GlobalTheory.RingIface.sigO_coe l g _

/- English proof (translation)
Establish `h1 : y - algebraMap (Per.AinfP l) (Per.BdRp l) a ∈ Per.FilP l 1`. Rewrite using `[GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, map_sub, GlobalTheory.RingIface.ev_alg, h, sub_self]`. Establish `h2` using `GlobalTheory.RingIface.thetaD_of_mem_FilP l h1`. Rewrite `h2` using `[map_sub, GlobalTheory.RingIface.thetaD_alg, sub_eq_zero]`. Then use the resulting hypothesis.
-/
theorem θD_of_ev (y : Per.BdRp l) (a : Per.AinfP l) (h : Ideal.Quotient.mk _ a = Per.ev l 1 y) :
    Per.θD l y = Per.θP l a := by
  have h1 : y - algebraMap (Per.AinfP l) (Per.BdRp l) a ∈ Per.FilP l 1 := by
    rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, map_sub, GlobalTheory.RingIface.ev_alg, h, sub_self]
  have h2 := GlobalTheory.RingIface.thetaD_of_mem_FilP l h1
  rwa [map_sub, GlobalTheory.RingIface.thetaD_alg, sub_eq_zero] at h2

/- English proof (translation)
The claim follows from `GlobalTheory.RingIface.thetaD_alg l a`.
-/
theorem θD_alg (a : Per.AinfP l) : Per.θD l (algebraMap _ _ a) = Per.θP l a :=
  GlobalTheory.RingIface.thetaD_alg l a

end GlobalTheory.MemLoc.ThetaD

open GlobalTheory.MemLoc.ThetaD in

/- English proof (translation)
Introduce `l _`. Use `⟨fun c => ?_, fun y => ?_, fun y hy => ?_, fun a => ?_, fun g y => ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `fontaineTheta_surjective' l c`. Conclude with `⟨_, θD_alg l a⟩`. Take `⟨a, ha⟩` from `Ideal.Quotient.mk_surjective (Per.ev l 1 y)`.

Rewrite using `[θD_of_ev l y a ha, fontaineTheta_eq_zero, GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, ← ha, Ideal.Quotient.eq_zero_iff_mem, pow_one]`. Take `⟨a, ha⟩` from `Ideal.Quotient.mk_surjective (Per.ev l 1 y)`. Rewrite `hy` using `[θD_of_ev l y a ha]`. Take `⟨b, hb⟩` from `fontaineTheta_surjective' l (Per.θP l a)⁻¹`. Establish `h1 : a * b - 1 ∈ Per.kerP l ^ 1`.

Rewrite using `[pow_one, ← fontaineTheta_eq_zero, map_sub, map_mul, hb, map_one, mul_inv_cancel₀ hy, sub_self]`. Establish `hu : IsUnit (Per.ev l 1 y)`. Rewrite using `[← ha]`. Use `IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ b) ?_` and prove the remaining obligations. Rewrite using `[← map_mul, ← map_one (Ideal.Quotient.mk (Per.kerP l ^ 1)), Ideal.Quotient.eq]`.

Conclude with `h1`. Take `⟨e, -, he⟩` from `GlobalTheory.RingIface.exists_bdRp_equiv l`. Rewrite `hu` using `[← he]`. Establish `h2` using `(isUnit_of_evalₐ (Per.kerP l) (e y) hu).map e.symm`. Rewrite `h2` using `[RingEquiv.symm_apply_apply]`. Then use the resulting hypothesis.

Conclude with `(θD_alg l _).trans (fontaineTheta_algebraMap₂ l a)`. Take `⟨a, ha⟩` from `Ideal.Quotient.mk_surjective (Per.ev l 1 y)`. Rewrite using `[θD_of_ev l y a ha, ← θP_σ]`. Conclude with `θD_of_ev l _ _ (GlobalTheory.RingIface.ev_sigDp l g 1 y a ha.symm).symm`.
-/
theorem GlobalTheory.MemLoc.thetaD_props : ∀ (l : ℕ) [Fact l.Prime], Function.Surjective (Per.θD l) ∧ (∀ y : Per.BdRp l, Per.θD l y = 0 ↔ y ∈ Per.FilP l 1) ∧ (∀ y : Per.BdRp l, Per.θD l y ≠ 0 → IsUnit y) ∧ (∀ a : Per.Ainf l, Per.θD l (aDp l a) = (Per.θ l a : ℂ_[l])) ∧ ∀ (g : Per.Gq l) (y : Per.BdRp l), Per.θD l (Per.σDp g y) = Per.σC g (Per.θD l y) := by
  intro l _
  refine ⟨fun c => ?_, fun y => ?_, fun y hy => ?_, fun a => ?_, fun g y => ?_⟩
  · obtain ⟨a, rfl⟩ := fontaineTheta_surjective' l c
    exact ⟨_, θD_alg l a⟩
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (Per.ev l 1 y)
    rw [θD_of_ev l y a ha, fontaineTheta_eq_zero, GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, ← ha,
      Ideal.Quotient.eq_zero_iff_mem, pow_one]
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (Per.ev l 1 y)
    rw [θD_of_ev l y a ha] at hy
    obtain ⟨b, hb⟩ := fontaineTheta_surjective' l (Per.θP l a)⁻¹
    have h1 : a * b - 1 ∈ Per.kerP l ^ 1 := by
      rw [pow_one, ← fontaineTheta_eq_zero, map_sub, map_mul, hb, map_one, mul_inv_cancel₀ hy, sub_self]
    have hu : IsUnit (Per.ev l 1 y) := by
      rw [← ha]
      refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ b) ?_
      rw [← map_mul, ← map_one (Ideal.Quotient.mk (Per.kerP l ^ 1)), Ideal.Quotient.eq]
      exact h1
    obtain ⟨e, -, he⟩ := GlobalTheory.RingIface.exists_bdRp_equiv l
    rw [← he] at hu
    have h2 := (isUnit_of_evalₐ (Per.kerP l) (e y) hu).map e.symm
    rwa [RingEquiv.symm_apply_apply] at h2
  · exact (θD_alg l _).trans (fontaineTheta_algebraMap₂ l a)
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (Per.ev l 1 y)
    rw [θD_of_ev l y a ha, ← θP_σ]
    exact θD_of_ev l _ _ (GlobalTheory.RingIface.ev_sigDp l g 1 y a ha.symm).symm
