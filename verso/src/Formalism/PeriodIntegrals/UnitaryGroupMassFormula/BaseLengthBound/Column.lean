import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorSpanGeneratorsAlt

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem inc_cast {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) {u u' : WeightFamilies.Wt D j}
    (h : u = u') (F : B.Cusp j u) : X.inc u' (h ▸ F) = X.inc u F := by
  subst h; rfl

/- English proof (translation)
Proceed by induction on `a using WithTop.recTopCoe with`. Consider the case `top => exact le_top`. Consider the case `coe n`. Establish `h2 : (0 : ℤ) ≤ n` using `by exact_mod_cast h0`. Establish `h3 : n ≠ 0` using `fun h => h1 (by rw [h]; rfl)`.

Conclude with `(show (1 : ℤ) ≤ n by omega)` after adjusting the coercions.
-/
theorem one_le_of_nonneg_of_ne {a : WithTop ℤ} (h0 : 0 ≤ a) (h1 : a ≠ 0) : 1 ≤ a := by
  induction a using WithTop.recTopCoe with
  | top => exact le_top
  | coe n =>
    have h2 : (0 : ℤ) ≤ n := by exact_mod_cast h0
    have h3 : n ≠ 0 := fun h => h1 (by rw [h]; rfl)
    exact_mod_cast (show (1 : ℤ) ≤ n by omega)

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

/- English proof (translation)
Unfold `wfr`. Use `congr 1`. Conclude with `Subtype.ext (congrArg (emb X la G.N) (inc_cast X (add_zero_weight_one_eq wL).symm (G.w jj)))`.
-/
theorem wfr_eq (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (jj : Fin G.N) :
    fr0 X la G.w 1 ⟨emb X la G.N (X.inc _ ((add_zero_weight_one_eq wL).symm ▸ G.w jj : B.Cusp j (addL (wt0 D j) wL 1))),
      emb_mem_Vw X la G.N _ _⟩ = wfr G la jj := by
  unfold wfr
  congr 1
  exact Subtype.ext (congrArg (emb X la G.N) (inc_cast X (add_zero_weight_one_eq wL).symm (G.w jj)))

/- English proof (translation)
Take `⟨hd1, hd2, -, -, -, hk, -⟩` from `hT ζ`. Establish `e` using `hk 1 ((add_zero_weight_one_eq wL).symm ▸ G.w jj : B.Cusp j (addL (wt0 D j) wL 1))`. Rewrite `e` using `[wfr_eq, inc_cast]`. Establish `hv : X.depth S.sW wL la (Q.y ζ) ≤ X.vAt la (Q.y ζ) (X.inc wL (G.w jj))` using `iInf₂_le _ (hw jj)`. Establish `hd : X.depth S.sW wL la (Q.y ζ) = (((X.depth S.sW wL la (Q.y ζ)).toReal : ℝ) : EReal)` using `(EReal.coe_toReal hd1 hd2).symm`.

Establish `hv' : (((X.depth S.sW wL la (Q.y ζ)).toReal : ℝ) : EReal) ≤ X.vAt la (Q.y ζ) (X.inc wL (G.w jj))`. Rewrite using `[← hd]`. Conclude with `hv`. Establish `hb` using `ereal_bound (ep := ep (unifO X la G.N) ζ) (T := 1) hd hv'`. Establish `key : (((0 : ℤ) : ℝ) : EReal) ≤ toE (ord (unifO X la G.N) ζ (toOsK X la G.w (wfr G la jj)))`.

Rewrite using `[e]`. Use `le_trans (le_of_eq ?_) hb` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using `using le_of_coe_le_toE key`.
-/
theorem ord_wfr_nonneg (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (S : Scal B)
    (hT : Q.InTie S) (hw : ∀ k, G.w k ∈ X.WWc S.sW wL) (ζ : PtsG G la) (jj : Fin G.N) :
    0 ≤ ord (unifO X la G.N) ζ (toOsK X la G.w (wfr G la jj)) := by
  obtain ⟨hd1, hd2, -, -, -, hk, -⟩ := hT ζ
  have e := hk 1 ((add_zero_weight_one_eq wL).symm ▸ G.w jj : B.Cusp j (addL (wt0 D j) wL 1))
  rw [wfr_eq, inc_cast] at e
  have hv : X.depth S.sW wL la (Q.y ζ) ≤ X.vAt la (Q.y ζ) (X.inc wL (G.w jj)) := iInf₂_le _ (hw jj)
  have hd : X.depth S.sW wL la (Q.y ζ) = (((X.depth S.sW wL la (Q.y ζ)).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal hd1 hd2).symm
  have hv' : (((X.depth S.sW wL la (Q.y ζ)).toReal : ℝ) : EReal) ≤ X.vAt la (Q.y ζ) (X.inc wL (G.w jj)) := by
    rw [← hd]; exact hv
  have hb := ereal_bound (ep := ep (unifO X la G.N) ζ) (T := 1) hd hv'
  have key : (((0 : ℤ) : ℝ) : EReal) ≤ toE (ord (unifO X la G.N) ζ (toOsK X la G.w (wfr G la jj))) := by
    rw [e]
    refine le_trans (le_of_eq ?_) hb
    simp
  simpa using le_of_coe_le_toE key

/- English proof (translation)
Establish `h1 : frac X la G.w 1 (sec X la G.w 0) = 1` using `by rw [frac_apply, pow_one, section_mul_inverse_eq_one]`. Establish `h2 : frac X la G.w 1 (sec X la G.w 0) = ∑ k, (algebraMap (Op X la G.N) (Kp X la G.N) (Tv X la G.N (0, k))) • frac X la G.w 1 (emb X la G.N (X.inc wL (G.w k)))`. Rewrite using `[sec, map_sum]`. Simplify using `only [map_smul]`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[OneMemClass.coe_one, ← h1, h2, AddSubmonoidClass.coe_finsetSum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Both sides reduce to the same expression.
-/
theorem one_eq_sum_wfr (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) :
    (1 : ↥(Frac0 X la G.w)) = ∑ k, (algebraMap (Op X la G.N) (Kp X la G.N) (Tv X la G.N (0, k))) • wfr G la k := by
  have h1 : frac X la G.w 1 (sec X la G.w 0) = 1 := by rw [frac_apply, pow_one, section_mul_inverse_eq_one]
  have h2 : frac X la G.w 1 (sec X la G.w 0) = ∑ k, (algebraMap (Op X la G.N) (Kp X la G.N) (Tv X la G.N (0, k))) •
      frac X la G.w 1 (emb X la G.N (X.inc wL (G.w k))) := by
    rw [sec, map_sum]
    simp only [map_smul]
  apply Subtype.ext
  rw [OneMemClass.coe_one, ← h1, h2, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rfl

/- English proof (translation)
Rewrite using `[← map_one (toOsK X la G.w), one_eq_sum_wfr G la, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, Algebra.smul_def, (IsScalarTower.algebraMap_apply (Op X la G.N) (Kp X la G.N) (OsK X la G.w) _).symm]`.
-/
theorem one_eq_sum_toOsK (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) :
    (1 : OsK X la G.w) = ∑ k, algebraMap (Op X la G.N) (OsK X la G.w) (Tv X la G.N (0, k)) *
      toOsK X la G.w (wfr G la k) := by
  rw [← map_one (toOsK X la G.w), one_eq_sum_wfr G la, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Algebra.smul_def, (IsScalarTower.algebraMap_apply (Op X la G.N) (Kp X la G.N) (OsK X la G.w) _).symm]

/- English proof (translation)
Use `Finset.induction_on s (by rw [Finset.sum_empty, ord_zero ζ h]; exact le_top) ?_` and prove the remaining obligations. Introduce `a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `(le_min (hf a) ih).trans (ord_add ζ h _ _)`.
-/
theorem one_le_ord_sum (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (ζ : PtsG G la) [IsDVRAt ζ]
    (h : IsUnif (OsK X la G.w) (unifO X la G.N)) (s : Finset (Fin G.N)) (f : Fin G.N → OsK X la G.w)
    (hf : ∀ k, 1 ≤ ord (unifO X la G.N) ζ (f k)) : 1 ≤ ord (unifO X la G.N) ζ (∑ k ∈ s, f k) := by
  classical
  refine Finset.induction_on s (by rw [Finset.sum_empty, ord_zero ζ h]; exact le_top) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha]
  exact (le_min (hf a) ih).trans (ord_add ζ h _ _)

/- English proof (translation)
Introduce `D B P j X ka wL wF G la Q S CRm T c hOk hw ζ`. Establish `hC` using `hOk.2.1`. Establish `hT` using `hOk.2.2.1`. Establish `h` using `isUnif_of_curve Q hC`. Use `isDVRAt_of_curve Q hC ζ` as an intermediate fact.

Use `⟨fun jj => ord_wfr_nonneg G la Q S hT hw ζ jj, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Establish `hall : ∀ k, 1 ≤ ord (unifO X la G.N) ζ (algebraMap (Op X la G.N) (OsK X la G.w) (Tv X la G.N (0, k)) * toOsK X la G.w (wfr G la k))`. Introduce `k`.

Rewrite using `[ord_mul ζ h]`. Establish `h0 : 0 ≤ ord (unifO X la G.N) ζ (algebraMap (Op X la G.N) (OsK X la G.w) (Tv X la G.N (0, k)))` using `ord_nonneg ζ h (Subalgebra.algebraMap_mem _ _)`. Establish `h1` using `one_le_of_nonneg_of_ne (ord_wfr_nonneg G la Q S hT hw ζ k) (hne k)`. Simplify using `using add_le_add h0 h1`. Establish `h2` using `one_le_ord_sum G la ζ h Finset.univ _ hall`.

Rewrite `h2` using `[← one_eq_sum_toOsK, ord_one ζ h]`. Conclude with `absurd (WithTop.coe_le_coe.1 (show ((1 : ℤ) : WithTop ℤ) ≤ ((0 : ℤ) : WithTop ℤ) from h2)) (by norm_num)`.
-/
theorem column_holds : Column := by
  intro D B P j X ka wL wF G la Q S CRm T c hOk hw ζ
  have hC := hOk.2.1
  have hT := hOk.2.2.1
  have h := isUnif_of_curve Q hC
  have := isDVRAt_of_curve Q hC ζ
  refine ⟨fun jj => ord_wfr_nonneg G la Q S hT hw ζ jj, ?_⟩
  by_contra hne
  push Not at hne
  have hall : ∀ k, 1 ≤ ord (unifO X la G.N) ζ (algebraMap (Op X la G.N) (OsK X la G.w) (Tv X la G.N (0, k)) *
      toOsK X la G.w (wfr G la k)) := by
    intro k
    rw [ord_mul ζ h]
    have h0 : 0 ≤ ord (unifO X la G.N) ζ (algebraMap (Op X la G.N) (OsK X la G.w) (Tv X la G.N (0, k))) :=
      ord_nonneg ζ h (Subalgebra.algebraMap_mem _ _)
    have h1 := one_le_of_nonneg_of_ne (ord_wfr_nonneg G la Q S hT hw ζ k) (hne k)
    simpa using add_le_add h0 h1
  have h2 := one_le_ord_sum G la ζ h Finset.univ _ hall
  rw [← one_eq_sum_toOsK, ord_one ζ h] at h2
  exact absurd (WithTop.coe_le_coe.1 (show ((1 : ℤ) : WithTop ℤ) ≤ ((0 : ℤ) : WithTop ℤ) from h2)) (by norm_num)

end PoleLengthBounds
