import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CorrFamAddTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneralLinearGroupDetMapFinOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCochainEvEqOfNaturalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexDifferentialValuesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassTateTwistCocycleUniqueNaturalAddiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImageCocycleSemilinearSheafComplexMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectSectionResStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedChernCocycleDegOneSubEqDifferentialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedChernCocycleDegTwoSubEqDefectsStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.RedChern

set_option backward.isDefEq.respectTransparency false

/- English proof (translation)
Apply the tactic sequence `ext i; fin_cases i <;> rfl`.
-/
theorem delta_two_eq : (SimplexCategory.δ (2 : Fin 3) : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 2) =
    SimplexCategory.subinterval 0 1 (by omega) := by
  ext i; fin_cases i <;> rfl

/- English proof (translation)
Apply the tactic sequence `ext i; fin_cases i <;> rfl`.
-/
theorem delta_zero_eq : (SimplexCategory.δ (0 : Fin 3) : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 2) =
    SimplexCategory.subinterval 1 1 (by omega) := by
  ext i; fin_cases i <;> rfl

/- English proof (translation)
Unfold `Sx.face Sx.sub SimplicialObject.δ`. Rewrite using `[delta_two_eq]`.
-/
theorem face_two {E : Spc} {U : Scheme.{0}} (x : Sx E 2 U) : x.face 2 = x.sub 0 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [delta_two_eq]

/- English proof (translation)
Unfold `Sx.face Sx.sub SimplicialObject.δ`. Rewrite using `[delta_zero_eq]`.
-/
theorem face_zero {E : Spc} {U : Scheme.{0}} (x : Sx E 2 U) : x.face 0 = x.sub 1 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [delta_zero_eq]

/- English proof (translation)
Unfold `Sx.sub Sx.res`. Conclude with `NatTrans.naturality_apply (E.map (SimplexCategory.subinterval j l h).op) g.op x`.
-/
theorem sub_res {E : Spc} {N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (x.res g).sub j l h = (x.sub j l h).res g := by
  unfold Sx.sub Sx.res
  exact NatTrans.naturality_apply (E.map (SimplexCategory.subinterval j l h).op) g.op x

open GlobalTheory.EtC.PicSpec

/- English proof (translation)
Use `match p with`. Consider the case `0 => simp [corrFam_zero]`. Consider the case `1`. Take `rfl : s = 0` from `by omega`. Rewrite using `[corrFam_one, corrFam_one, lineUnit_res, GlobalTheory.T.kummerReductionChernDefectSection_res Q q hqQ U _ (hE U ⟨x.face 0⟩) V g]`.

Consider the case `p + 2 => simp [corrFam_add_two]`.
-/
theorem corrFam_nat (Q q : ℕ) [NeZero Q] (hqQ : q ∣ Q) {E : Spc} (hE : Inv Q E) (L : E ⟶ ofCat (glCat 1)) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + 1 = s) (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (corrFam Q q L p s h U x) = corrFam Q q L p s h V (x.res g) := by
  match p with
  | 0 => simp [corrFam_zero]
  | 1 =>
    obtain rfl : s = 0 := by omega
    rw [corrFam_one, corrFam_one, lineUnit_res,
      GlobalTheory.T.kummerReductionChernDefectSection_res Q q hqQ U _ (hE U ⟨x.face 0⟩) V g]
  | p + 2 => simp [corrFam_add_two]

/- English proof (translation)
Introduce `Q q _ hqQ E hE L`. Establish `hq0 : q ≠ 0`. Introduce and unpack `rfl`. Conclude with `NeZero.ne Q (Nat.eq_zero_of_zero_dvd hqQ)`. Use `haveI : NeZero q := ⟨hq0⟩`.

Establish `hUnit : Inv q E` using `fun U hU => by`. Take `⟨k, hk⟩` from `hqQ`. Use `hE U hU` as an intermediate fact. Rewrite `this` using `[hk, Nat.cast_mul]`. Conclude with `isUnit_of_mul_isUnit_left this`.

Take `⟨γ, hγ, hγ0, hγ1, hγ2⟩` from `(GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive Q).1 L hE`. Take `⟨γ', hγ', hγ0', hγ1', hγ2'⟩` from `(GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).1 L hUnit`. Take `⟨β, hβ⟩` from `(GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap _ _ (redMap Q q 1)).1 E 2 γ`. Establish `hred : red Q q E 2 1 (c1 Q L) = CohomologyClass.mk β`. Rewrite using `[← hγ]`.

Conclude with `(GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap _ _ (redMap Q q 1)).2 E 2 γ β hβ`. Rewrite using `[hred, ← hγ']`. Take `⟨α, hα⟩` from `GlobalTheory.T.exists_cochain_ev_eq_of_natural' (ZMod q) (corrFam Q q L) (corrFam_nat Q q hqQ hE L)`. Rewrite using `[← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ 1 (by norm_num)]`. Use `⟨α, ?_⟩` and prove the remaining obligations.

Apply `(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1` to reduce the goal to its premises. Introduce `p t ht U x`. Rewrite using `[Cocycle.coe_sub, ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).1 _ _ p t ht U x).2.1, hβ]`. Use `match p with`. Consider the case `0`.

Take `rfl : t = 2` from `by omega`. Rewrite using `[(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) α U).1 x, hα, corrFam_zero, sec_map_zero, hγ0, hγ0', map_zero, sub_zero]`. Consider the case `1`. Take `rfl : t = 1` from `by omega`. Establish `key` using `(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) α U).2 0 0 1 (by simp) ht x`.

Rewrite using `[key]`. Simplify using `only [hα, corrFam_zero, smul_zero, Finset.sum_const_zero, add_zero, corrFam_one]`. Use `(GlobalTheory.T.reducedChernCocycle_deg_one_sub_eq_differential Q q hqQ U (lineUnit L x) (hE U ⟨x.face 0⟩) _ _ (fun V g v hv => ?_) (fun V g w hw => ?_)).symm` and prove the remaining obligations. Rewrite using `[(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod Q)).2.1 γ.1 1 1 _ V U g x]`. Conclude with `hγ1 V (x.res g) v (by rw [lineUnit_res]; exact hv)`.

Rewrite using `[(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ'.1 1 1 _ V U g x]`. Conclude with `hγ1' V (x.res g) w (by rw [lineUnit_res]; exact hw)`. Consider the case `2`. Take `rfl : t = 0` from `by omega`. Establish `key` using `(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) α U).2 1 (-1) 0 (by simp) ht x`.

Rewrite using `[key]`. Simplify using `only [hα, corrFam_one]`. Rewrite using `[show corrFam Q q L (1 + 1) (-1) (by simp) U x = 0 from rfl, sec_map_zero, zero_add, Fin.sum_univ_three, lineUnit_face, face_zero, face_two]`. Simplify using `only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_smul, neg_smul, Int.reduceNeg]`. Rewrite using `[Int.negOnePow_even 2 (by decide), one_smul, mul_comm (lineUnit L _) (lineUnit L _), ← sub_eq_add_neg]`.

Evaluate the numerical expressions. Use `(GlobalTheory.T.reducedChernCocycle_deg_two_sub_eq_defects Q q hqQ U _ _ (hE U ⟨(x.face 0).face 0⟩) _ _ (fun V g v w hv hw => ?_) (fun V g v w hv hw => ?_)).symm` and prove the remaining obligations. Rewrite using `[(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod Q)).2.1 γ.1 2 0 _ V U g x]`. Conclude with `hγ2 V (x.res g) v w (by rw [sub_res, lineUnit_res]; exact hv) (by rw [sub_res, lineUnit_res]; exact hw)`. Rewrite using `[(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ'.1 2 0 _ V U g x]`.

Conclude with `hγ2' V (x.res g) v w (by rw [sub_res, lineUnit_res]; exact hv) (by rw [sub_res, lineUnit_res]; exact hw)`. Consider the case `p + 3`. Establish `hZ` using `res_isZero (tw q 1) t (by omega)`. Conclude with `(sec_eq_zero hZ _).trans (sec_eq_zero hZ _).symm`.
-/
theorem coefficientReduction_firstChernClass_tateTwist : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ E : Spc, Inv Q E → ∀ L : E ⟶ ofCat (glCat 1),
    red Q q E 2 1 (c1 Q L) = c1 q L := by
  intro Q q _ hqQ E hE L
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact NeZero.ne Q (Nat.eq_zero_of_zero_dvd hqQ)
  haveI : NeZero q := ⟨hq0⟩
  have hUnit : Inv q E := fun U hU => by
    obtain ⟨k, hk⟩ := hqQ
    have := hE U hU
    rw [hk, Nat.cast_mul] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨γ, hγ, hγ0, hγ1, hγ2⟩ := (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive Q).1 L hE
  obtain ⟨γ', hγ', hγ0', hγ1', hγ2'⟩ := (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).1 L hUnit
  obtain ⟨β, hβ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap _ _ (redMap Q q 1)).1 E 2 γ
  have hred : red Q q E 2 1 (c1 Q L) = CohomologyClass.mk β := by
    rw [← hγ]
    exact (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap _ _ (redMap Q q 1)).2 E 2 γ β hβ
  rw [hred, ← hγ']
  obtain ⟨α, hα⟩ := GlobalTheory.T.exists_cochain_ev_eq_of_natural' (ZMod q) (corrFam Q q L) (corrFam_nat Q q hqQ hE L)
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ 1 (by norm_num)]
  refine ⟨α, ?_⟩
  apply (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1
  intro p t ht U x
  rw [Cocycle.coe_sub, ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).1 _ _ p t ht U x).2.1, hβ]
  match p with
  | 0 =>
    obtain rfl : t = 2 := by omega
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) α U).1 x, hα, corrFam_zero, sec_map_zero, hγ0, hγ0', map_zero, sub_zero]
  | 1 =>
    obtain rfl : t = 1 := by omega
    have key := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) α U).2 0 0 1 (by simp) ht x
    rw [key]
    simp only [hα, corrFam_zero, smul_zero, Finset.sum_const_zero, add_zero, corrFam_one]
    refine (GlobalTheory.T.reducedChernCocycle_deg_one_sub_eq_differential Q q hqQ U (lineUnit L x) (hE U ⟨x.face 0⟩) _ _ (fun V g v hv => ?_) (fun V g w hw => ?_)).symm
    · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod Q)).2.1 γ.1 1 1 _ V U g x]
      exact hγ1 V (x.res g) v (by rw [lineUnit_res]; exact hv)
    · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ'.1 1 1 _ V U g x]
      exact hγ1' V (x.res g) w (by rw [lineUnit_res]; exact hw)
  | 2 =>
    obtain rfl : t = 0 := by omega
    have key := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) α U).2 1 (-1) 0 (by simp) ht x
    rw [key]
    simp only [hα, corrFam_one]
    rw [show corrFam Q q L (1 + 1) (-1) (by simp) U x = 0 from rfl, sec_map_zero, zero_add, Fin.sum_univ_three,
      lineUnit_face, face_zero, face_two]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_smul, neg_smul, Int.reduceNeg]
    rw [Int.negOnePow_even 2 (by decide), one_smul, mul_comm (lineUnit L _) (lineUnit L _), ← sub_eq_add_neg]
    norm_num
    refine (GlobalTheory.T.reducedChernCocycle_deg_two_sub_eq_defects Q q hqQ U _ _ (hE U ⟨(x.face 0).face 0⟩) _ _ (fun V g v w hv hw => ?_) (fun V g v w hv hw => ?_)).symm
    · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod Q)).2.1 γ.1 2 0 _ V U g x]
      exact hγ2 V (x.res g) v w (by rw [sub_res, lineUnit_res]; exact hv) (by rw [sub_res, lineUnit_res]; exact hw)
    · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ'.1 2 0 _ V U g x]
      exact hγ2' V (x.res g) v w (by rw [sub_res, lineUnit_res]; exact hv) (by rw [sub_res, lineUnit_res]; exact hw)
  | p + 3 =>
    have hZ := res_isZero (tw q 1) t (by omega)
    exact (sec_eq_zero hZ _).trans (sec_eq_zero hZ _).symm

end GlobalTheory.EtC.RedChern
