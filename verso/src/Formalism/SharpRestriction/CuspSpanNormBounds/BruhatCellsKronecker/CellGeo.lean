import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellDef
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.MainNotions.S Formalism.BasicNotions Matrix

section Abs

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def geoGram (v : ι → S.V) : Matrix ι ι E := fun i k => S.hT (v i) (v k)

def geoC (v : ι → S.V) (i : ι) : S.V →ₗ[E] E := ∑ k, ((geoGram v)⁻¹ i k) • S.hT (v k)

def geoY (v w : ι → S.V) : S.V →ₗ[E] S.V := ∑ i, (geoC v i).smulRight (w i)

/- English proof (translation)
Unfold `geoC`. Rewrite using `[LinearMap.sum_apply]`. Simplify using `only [LinearMap.smul_apply, smul_eq_mul]`.
-/
theorem geo_C_apply (v : ι → S.V) (i : ι) (y : S.V) :
    geoC v i y = ∑ k, (geoGram v)⁻¹ i k * S.hT (v k) y := by
  unfold geoC
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, smul_eq_mul]

/- English proof (translation)
Unfold `geoY`. Rewrite using `[LinearMap.sum_apply]`. Simplify using `only [LinearMap.smulRight_apply]`.
-/
theorem geo_Y_apply (v w : ι → S.V) (y : S.V) : geoY v w y = ∑ i, geoC v i y • w i := by
  unfold geoY
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smulRight_apply]

/- English proof (translation)
Establish `hmul : geoGram v * (geoGram v)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ h`. Establish `hrow : ∀ m, ∑ k, geoGram v l k * (geoGram v)⁻¹ k m = if l = m then 1 else 0`. Introduce `m`. Establish `hm` using `congrFun (congrFun hmul l) m`. Rewrite `hm` using `[Matrix.mul_apply, Matrix.one_apply]`.

Conclude with `hm`. Repeatedly rewrite using `[geo_C_apply, Finset.mul_sum, ← mul_assoc]`. Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[← Finset.sum_mul, hrow]`. Simplify using the standard rewrite rules.
-/
theorem geo_repr (v : ι → S.V) (h : IsUnit (geoGram v).det) (l : ι) (y : S.V) :
    S.hT (v l) y = ∑ k, geoGram v l k * geoC v k y := by
  have hmul : geoGram v * (geoGram v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ h
  have hrow : ∀ m, ∑ k, geoGram v l k * (geoGram v)⁻¹ k m = if l = m then 1 else 0 := by
    intro m
    have hm := congrFun (congrFun hmul l) m
    rw [Matrix.mul_apply, Matrix.one_apply] at hm
    exact hm
  simp_rw [geo_C_apply, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hrow]
  simp

/- English proof (translation)
Rewrite using `[geo_C_apply]`. Establish `h1 : (geoGram v)⁻¹ * geoGram v = 1` using `Matrix.nonsing_inv_mul _ h`. Establish `h2` using `congrFun (congrFun h1 i) l`. Rewrite `h2` using `[Matrix.mul_apply, Matrix.one_apply]`. Conclude with `h2`.
-/
theorem geo_C_v (v : ι → S.V) (h : IsUnit (geoGram v).det) (i l : ι) :
    geoC v i (v l) = if i = l then 1 else 0 := by
  rw [geo_C_apply]
  have h1 : (geoGram v)⁻¹ * geoGram v = 1 := Matrix.nonsing_inv_mul _ h
  have h2 := congrFun (congrFun h1 i) l
  rw [Matrix.mul_apply, Matrix.one_apply] at h2
  exact h2

/- English proof (translation)
Rewrite using `[geo_Y_apply]`. Simplify using `only [geo_C_v v h]`. Simplify using the standard rewrite rules.
-/
theorem geo_Y_v (v w : ι → S.V) (h : IsUnit (geoGram v).det) (l : ι) : geoY v w (v l) = w l := by
  rw [geo_Y_apply]
  simp only [geo_C_v v h]
  simp

/- English proof (translation)
Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun (R := E)).1 hz`. Simplify using `only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[geo_repr v h i y, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [geoGram, mul_assoc]`.
-/
theorem geo_R (v : ι → S.V) (h : IsUnit (geoGram v).det) (z : S.V)
    (hz : z ∈ Submodule.span E (Set.range v)) (y : S.V) :
    S.hT z y = ∑ k, S.hT z (v k) * geoC v k y := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (R := E)).1 hz
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [geo_repr v h i y, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [geoGram, mul_assoc]

/- English proof (translation)
Establish `e1 : S.hT (geoY v w x) y = ∑ i, ∑ k, star (geoC v i x) * (S.hT (w i) (v k) * geoC v k y)`. Rewrite using `[geo_Y_apply]`. Simplify using `only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[geo_R v h (w i) (hw i) y, Finset.mul_sum]`.

Establish `e2 : S.hT x (geoY v w y) = ∑ i, ∑ k, star (geoC v i x) * (S.hT (v i) (w k) * geoC v k y)`. Rewrite using `[geo_Y_apply]`. Simplify using `only [map_sum, map_smul, smul_eq_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Establish `hx : S.hT x (w k) = ∑ i, S.hT (v i) (w k) * star (geoC v i x)`. Rewrite using `[← S.herm.eq (w k) x, geo_R v h (w k) (hw k) x, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, S.herm.eq, starRingEnd_apply]`. Rewrite using `[hx, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2, ← Finset.sum_add_distrib]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`.

Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Take the linear combination `(star (geoC v i x) * geoC v k y) * hsk i k`.
-/
theorem geo_skew (v w : ι → S.V) (h : IsUnit (geoGram v).det)
    (hw : ∀ i, w i ∈ Submodule.span E (Set.range v))
    (hsk : ∀ i k, S.hT (w i) (v k) + S.hT (v i) (w k) = 0) (x y : S.V) :
    S.hT (geoY v w x) y + S.hT x (geoY v w y) = 0 := by
  have e1 : S.hT (geoY v w x) y = ∑ i, ∑ k, star (geoC v i x) * (S.hT (w i) (v k) * geoC v k y) := by
    rw [geo_Y_apply]
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [geo_R v h (w i) (hw i) y, Finset.mul_sum]
  have e2 : S.hT x (geoY v w y) = ∑ i, ∑ k, star (geoC v i x) * (S.hT (v i) (w k) * geoC v k y) := by
    rw [geo_Y_apply]
    simp only [map_sum, map_smul, smul_eq_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hx : S.hT x (w k) = ∑ i, S.hT (v i) (w k) * star (geoC v i x) := by
      rw [← S.herm.eq (w k) x, geo_R v h (w k) (hw k) x, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, S.herm.eq, starRingEnd_apply]
    rw [hx, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e1, e2, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun k _ => ?_
  linear_combination (star (geoC v i x) * geoC v k y) * hsk i k

end Abs

section Flag

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

/- English proof (translation)
Simplify using `[FlagG.fvec]`.
-/
theorem geo_fvec_cast (F : FlagG S r T) (a : Fin r) : F.fvec a.castSucc = F.e a := by
  simp [FlagG.fvec]

/- English proof (translation)
Simplify using `[FlagG.fvec]`.
-/
theorem geo_fvec_last (F : FlagG S r T) : F.fvec (Fin.last r) = F.z := by
  simp [FlagG.fvec]

/- English proof (translation)
Unfold `FlagG.Xa`. Conclude with `Submodule.subset_span ⟨i, h, rfl⟩`.
-/
theorem geo_e_mem_Xa (F : FlagG S r T) (i : Fin r) (a : ℕ) (h : i.val < a) : F.e i ∈ F.Xa a := by
  unfold FlagG.Xa
  exact Submodule.subset_span ⟨i, h, rfl⟩

/- English proof (translation)
Unfold `FlagG.Xa`. Apply `Submodule.span_mono` to reduce the goal to its premises. Apply `Set.image_mono` to reduce the goal to its premises. Introduce `i hi`. Simplify using `only [Set.mem_setOf_eq] at hi ⊢`.

Use linear arithmetic over natural numbers and integers.
-/
theorem geo_Xa_mono (F : FlagG S r T) {a b : ℕ} (h : a ≤ b) : F.Xa a ≤ F.Xa b := by
  unfold FlagG.Xa
  apply Submodule.span_mono
  apply Set.image_mono
  intro i hi
  simp only [Set.mem_setOf_eq] at hi ⊢
  omega

/- English proof (translation)
Unfold `FlagG.Xa FlagG.X`. Conclude with `Submodule.span_mono (Set.image_subset_range _ _)`.
-/
theorem geo_Xa_le_X (F : FlagG S r T) (a : ℕ) : F.Xa a ≤ F.X := by
  unfold FlagG.Xa FlagG.X
  exact Submodule.span_mono (Set.image_subset_range _ _)

/- English proof (translation)
Establish `key : ∀ i, S.hT (F.e i) (F.fvec p) = 0`. Introduce `i`. Break down `Fin.eq_castSucc_or_eq_last p with ⟨a, rfl⟩ | rfl` into its components or cases. Rewrite using `[geo_fvec_cast]`. Conclude with `F.e_iso i a`.

Rewrite using `[geo_fvec_last]`. Conclude with `F.z_orth i`. Unfold `FlagG.X at hx`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun (R := E)).1 hx`. Simplify using `[key]`.
-/
theorem geo_X_fvec (F : FlagG S r T) (x : S.V) (hx : x ∈ F.X) (p : Fin (r + 1)) : S.hT x (F.fvec p) = 0 := by
  have key : ∀ i, S.hT (F.e i) (F.fvec p) = 0 := by
    intro i
    rcases Fin.eq_castSucc_or_eq_last p with ⟨a, rfl⟩ | rfl
    · rw [geo_fvec_cast]
      exact F.e_iso i a
    · rw [geo_fvec_last]
      exact F.z_orth i
  unfold FlagG.X at hx
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (R := E)).1 hx
  simp [key]

/- English proof (translation)
Rewrite using `[← S.herm.eq x (F.fvec p), geo_X_fvec F x hx p, map_zero]`.
-/
theorem geo_fvec_X (F : FlagG S r T) (x : S.V) (hx : x ∈ F.X) (p : Fin (r + 1)) : S.hT (F.fvec p) x = 0 := by
  rw [← S.herm.eq x (F.fvec p), geo_X_fvec F x hx p, map_zero]

/- English proof (translation)
Establish `key : ∀ i, S.hT x (F.e i) = 0` using `fun i => by`. Rewrite using `[← geo_fvec_cast F i]`. Conclude with `geo_X_fvec F x hx _`. Unfold `FlagG.X at hy`. Take `⟨d, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun (R := E)).1 hy`.

Simplify using `[key]`.
-/
theorem geo_X_X (F : FlagG S r T) (x y : S.V) (hx : x ∈ F.X) (hy : y ∈ F.X) : S.hT x y = 0 := by
  have key : ∀ i, S.hT x (F.e i) = 0 := fun i => by
    rw [← geo_fvec_cast F i]
    exact geo_X_fvec F x hx _
  unfold FlagG.X at hy
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (R := E)).1 hy
  simp [key]

/- English proof (translation)
Use `show ∀ x ∈ F.X, S.hT x (F.fvec p) = 0`. Conclude with `fun x hx => geo_X_fvec F x hx p`.
-/
theorem geo_fvec_perp (F : FlagG S r T) (p : Fin (r + 1)) : F.fvec p ∈ perpS S F.X := by
  show ∀ x ∈ F.X, S.hT x (F.fvec p) = 0
  exact fun x hx => geo_X_fvec F x hx p

/- English proof (translation)
Unfold `FlagG.Xa at hy`. Take `⟨l, hl, rfl⟩` from `(Finsupp.mem_span_image_iff_linearCombination (R := E)).1 hy`. Establish `hmem : c • F.e a + Finsupp.linearCombination E F.e l ∈ Submodule.span E (Set.range F.e)`. Use `Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)) ?_` and prove the remaining obligations. Conclude with `Submodule.span_mono (Set.image_subset_range _ _) ((Finsupp.mem_span_image_iff_linearCombination (R := E)).2 ⟨l, hl, rfl⟩)`.

Establish `hla : l a = 0`. Assume the negation of the conclusion as `hne`. Rewrite `hl` using `[Finsupp.mem_supported]`. Use `hl (Finset.mem_coe.2 (Finsupp.mem_support_iff.2 hne))` as an intermediate fact. Simplify using `at this`.

Establish `heq : F.e_indep.repr ⟨_, hmem⟩ = Finsupp.single a c + l`. Apply `F.e_indep.repr_eq` to reduce the goal to its premises. Simplify using `[Finsupp.linearCombination_single]`. Unfold `FlagG.coefX`. Rewrite using `[dif_pos hmem, heq]`.

Simplify using `[hla]`.
-/
theorem geo_coefX (F : FlagG S r T) (a : Fin r) (c : E) (y : S.V) (hy : y ∈ F.Xa a.val) :
    F.coefX (c • F.e a + y) a = c := by
  classical
  unfold FlagG.Xa at hy
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination (R := E)).1 hy
  have hmem : c • F.e a + Finsupp.linearCombination E F.e l ∈ Submodule.span E (Set.range F.e) := by
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)) ?_
    exact Submodule.span_mono (Set.image_subset_range _ _)
      ((Finsupp.mem_span_image_iff_linearCombination (R := E)).2 ⟨l, hl, rfl⟩)
  have hla : l a = 0 := by
    by_contra hne
    rw [Finsupp.mem_supported] at hl
    have := hl (Finset.mem_coe.2 (Finsupp.mem_support_iff.2 hne))
    simp at this
  have heq : F.e_indep.repr ⟨_, hmem⟩ = Finsupp.single a c + l := by
    apply F.e_indep.repr_eq
    simp [Finsupp.linearCombination_single]
  unfold FlagG.coefX
  rw [dif_pos hmem, heq]
  simp [hla]

variable {j : ℕ} (hj : j ≤ r + 1)

/- English proof (translation)
Conclude with `Fin.ext rfl`.
-/
theorem geo_castLE_eq (b : Fin j) (hb : b.val < r) : Fin.castLE hj b = Fin.castSucc ⟨b.val, hb⟩ := by
  exact Fin.ext rfl

/- English proof (translation)
Use `sum_mem fun b _ => ?_` and prove the remaining obligations. Distinguish the cases in `hba : a ≤ b`. Rewrite using `[hA b a hba, zero_smul]`. Conclude with `Submodule.zero_mem _`. Establish `hba' : b.val < a.val` using `Fin.lt_def.1 (not_le.1 hba)`.

Establish `hbr : b.val < r` using `by have := a.isLt; omega`. Rewrite using `[geo_castLE_eq hj b hbr, geo_fvec_cast]`. Conclude with `Submodule.smul_mem _ _ (geo_e_mem_Xa F ⟨b.val, hbr⟩ a.val hba')`.
-/
theorem geo_W_mem (F : FlagG S r T) (A : Matrix (Fin j) (Fin j) E) (hA : StrictUp A) (a : Fin j) :
    ∑ b, A b a • F.fvec (Fin.castLE hj b) ∈ F.Xa a.val := by
  refine sum_mem fun b _ => ?_
  by_cases hba : a ≤ b
  · rw [hA b a hba, zero_smul]
    exact Submodule.zero_mem _
  · have hba' : b.val < a.val := Fin.lt_def.1 (not_le.1 hba)
    have hbr : b.val < r := by have := a.isLt; omega
    rw [geo_castLE_eq hj b hbr, geo_fvec_cast]
    exact Submodule.smul_mem _ _ (geo_e_mem_Xa F ⟨b.val, hbr⟩ a.val hba')

/- English proof (translation)
Establish `hi0 : i.val < j` using `by have := a.isLt; omega`. Use `⟨∑ b ∈ Finset.univ.erase (⟨i.val, hi0⟩ : Fin j), A b a • F.fvec (Fin.castLE hj b), ?_, ?_⟩` and prove the remaining obligations. Use `sum_mem fun b hb => ?_` and prove the remaining obligations. Establish `hne : b ≠ ⟨i.val, hi0⟩` using `Finset.ne_of_mem_erase hb`. Distinguish the cases in `hba : a ≤ b`.

Rewrite using `[hA b a hba, zero_smul]`. Conclude with `Submodule.zero_mem _`. Establish `hba' : b.val < a.val` using `Fin.lt_def.1 (not_le.1 hba)`. Establish `hbv : b.val ≠ i.val` using `fun h => hne (Fin.ext h)`. Establish `hbi : b.val < i.val` using `by omega`.

Establish `hbr : b.val < r` using `by have := i.isLt; omega`. Rewrite using `[geo_castLE_eq hj b hbr, geo_fvec_cast]`. Conclude with `Submodule.smul_mem _ _ (geo_e_mem_Xa F ⟨b.val, hbr⟩ i.val hbi)`. Rewrite using `[← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨i.val, hi0⟩ : Fin j)), geo_castLE_eq hj ⟨i.val, hi0⟩ i.isLt, geo_fvec_cast]`.
-/
theorem geo_W_split (F : FlagG S r T) (A : Matrix (Fin j) (Fin j) E) (hA : StrictUp A) (a : Fin j) (i : Fin r)
    (hi : a.val = i.val + 1) :
    ∃ y ∈ F.Xa i.val, ∑ b, A b a • F.fvec (Fin.castLE hj b) =
      A ⟨i.val, by have := a.isLt; omega⟩ a • F.e i + y := by
  have hi0 : i.val < j := by have := a.isLt; omega
  refine ⟨∑ b ∈ Finset.univ.erase (⟨i.val, hi0⟩ : Fin j), A b a • F.fvec (Fin.castLE hj b), ?_, ?_⟩
  · refine sum_mem fun b hb => ?_
    have hne : b ≠ ⟨i.val, hi0⟩ := Finset.ne_of_mem_erase hb
    by_cases hba : a ≤ b
    · rw [hA b a hba, zero_smul]
      exact Submodule.zero_mem _
    · have hba' : b.val < a.val := Fin.lt_def.1 (not_le.1 hba)
      have hbv : b.val ≠ i.val := fun h => hne (Fin.ext h)
      have hbi : b.val < i.val := by omega
      have hbr : b.val < r := by have := i.isLt; omega
      rw [geo_castLE_eq hj b hbr, geo_fvec_cast]
      exact Submodule.smul_mem _ _ (geo_e_mem_Xa F ⟨b.val, hbr⟩ i.val hbi)
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨i.val, hi0⟩ : Fin j)),
      geo_castLE_eq hj ⟨i.val, hi0⟩ i.isLt, geo_fvec_cast]

/- English proof (translation)
Break down `Nat.lt_or_ge r j with h | h` into its components or cases. Establish `hj1 : j = r + 1` using `by omega`. Substitute `hj1` using the available equality. Rewrite using `[Finset.sum_range_succ, hg r le_rfl, add_zero]`. Rewrite using `[← Finset.sum_range_add_sum_Ico _ h]`.

Rewrite using `[Finset.sum_eq_zero (s := Finset.Ico j r) (fun i hi => hg i (by rw [Finset.mem_Ico] at hi; omega)), add_zero]`.
-/
theorem geo_sum_range (hj' : j ≤ r + 1) (g : ℕ → E) (hg : ∀ i, j ≤ i + 1 → g i = 0) :
    ∑ i ∈ Finset.range r, g i = ∑ i ∈ Finset.range j, g i := by
  rcases Nat.lt_or_ge r j with h | h
  · have hj1 : j = r + 1 := by omega
    subst hj1
    rw [Finset.sum_range_succ, hg r le_rfl, add_zero]
  · rw [← Finset.sum_range_add_sum_Ico _ h]
    rw [Finset.sum_eq_zero (s := Finset.Ico j r) (fun i hi => hg i (by rw [Finset.mem_Ico] at hi; omega)),
      add_zero]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use `show Y ∈ LieU S ∧ (∀ a : ℕ, 1 ≤ a → a ≤ r → ∀ x ∈ F.Xa a, Y x ∈ F.Xa (a - 1)) ∧ ∀ x ∈ perpS S F.X, Y x ∈ F.X`. Use `⟨H1, ?_, fun x hx => (H3 x hx).1⟩` and prove the remaining obligations. Introduce `a ha1 har x hx`. Establish `hsub : F.Xa a ≤ (F.Xa (a - 1)).comap Y` using `by show Submodule.span E (F.e '' {i | i.1 < a}) ≤ _`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, hi, rfl⟩`. Establish `hi' : i.val < a` using `hi`. Use `show Y (F.e i) ∈ F.Xa (a - 1)`. Distinguish the cases in `hij : i.val < j`.

Establish `he : F.e i = F.fvec (Fin.castLE hj ⟨i.val, hij⟩)`. Rewrite using `[geo_castLE_eq hj ⟨i.val, hij⟩ i.isLt, geo_fvec_cast]`. Establish `hle : i.val ≤ a - 1` using `by omega`. Rewrite using `[he, H2]`. Conclude with `geo_Xa_mono F hle (geo_W_mem hj F A hA ⟨i.val, hij⟩)`.

Establish `hperp : F.e i ∈ perpS S F.X`. Rewrite using `[← geo_fvec_cast F i]`. Conclude with `geo_fvec_perp F _`. Establish `hjr : j ≤ r` using `by have := i.isLt; omega`. Establish `hle : j - 1 ≤ a - 1` using `by omega`.

Conclude with `geo_Xa_mono F hle ((H3 _ hperp).2 hjr)`. Conclude with `hsub hx`. Set `G : ℕ → E` to `fun n => if h : n + 1 < j then A ⟨n, by omega⟩ ⟨n + 1, h⟩ else 0`. Establish `hg : ∀ i : Fin r, F.coefX (Y (F.fvec i.succ)) i = G i.val`. Introduce `i`.

Distinguish the cases in `h : i.val + 1 < j`. Simplify using `only [G, dif_pos h]`. Take `⟨y, hy, hyeq⟩` from `geo_W_split hj F A hA ⟨i.val + 1, h⟩ i rfl`. Establish `hsucc : F.fvec i.succ = F.fvec (Fin.castLE hj ⟨i.val + 1, h⟩)` using `rfl`. Rewrite using `[hsucc, H2, hyeq]`.

Conclude with `geo_coefX F i _ y hy`. Simplify using `only [G, dif_neg h]`. Establish `hjr : j ≤ r` using `by have := i.isLt; omega`. Establish `hle : j - 1 ≤ i.val` using `by omega`. Establish `hmem : Y (F.fvec i.succ) ∈ F.Xa i.val` using `geo_Xa_mono F hle ((H3 _ (geo_fvec_perp F _)).2 hjr)`.

Use `geo_coefX F i 0 _ hmem` as an intermediate fact. Rewrite `this` using `[zero_smul, zero_add]`. Then use the resulting hypothesis. Establish `e1 : F.ell Y = ∑ n ∈ Finset.range r, G n`. Unfold `FlagG.ell`. Rewrite using `[← Fin.sum_univ_eq_sum_range G r]`.

Conclude with `Finset.sum_congr rfl fun i _ => hg i`. Establish `e2 : supSum A = ∑ n ∈ Finset.range j, G n`. Rewrite using `[← Fin.sum_univ_eq_sum_range G j]`. Both sides reduce to the same expression. Rewrite using `[e1, e2]`.

Conclude with `geo_sum_range hj G fun n hn => by`. Simplify using `only [G]`. Rewrite using `[dif_neg (show ¬ (n + 1 < j) by omega)]`.
-/
theorem geo_side (F : FlagG S r T) (A : Matrix (Fin j) (Fin j) E) (hA : StrictUp A) (Y : S.V →ₗ[E] S.V)
    (H1 : Y ∈ LieU S)
    (H2 : ∀ a : Fin j, Y (F.fvec (Fin.castLE hj a)) = ∑ b, A b a • F.fvec (Fin.castLE hj b))
    (H3 : ∀ x ∈ perpS S F.X, Y x ∈ F.X ∧ (j ≤ r → Y x ∈ F.Xa (j - 1))) :
    Y ∈ F.LieN ∧ F.ell Y = supSum A := by
  constructor
  · show Y ∈ LieU S ∧ (∀ a : ℕ, 1 ≤ a → a ≤ r → ∀ x ∈ F.Xa a, Y x ∈ F.Xa (a - 1)) ∧
      ∀ x ∈ perpS S F.X, Y x ∈ F.X
    refine ⟨H1, ?_, fun x hx => (H3 x hx).1⟩
    intro a ha1 har x hx
    have hsub : F.Xa a ≤ (F.Xa (a - 1)).comap Y := by
      show Submodule.span E (F.e '' {i | i.1 < a}) ≤ _
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      have hi' : i.val < a := hi
      show Y (F.e i) ∈ F.Xa (a - 1)
      by_cases hij : i.val < j
      · have he : F.e i = F.fvec (Fin.castLE hj ⟨i.val, hij⟩) := by
          rw [geo_castLE_eq hj ⟨i.val, hij⟩ i.isLt, geo_fvec_cast]
        have hle : i.val ≤ a - 1 := by omega
        rw [he, H2]
        exact geo_Xa_mono F hle (geo_W_mem hj F A hA ⟨i.val, hij⟩)
      · have hperp : F.e i ∈ perpS S F.X := by
          rw [← geo_fvec_cast F i]
          exact geo_fvec_perp F _
        have hjr : j ≤ r := by have := i.isLt; omega
        have hle : j - 1 ≤ a - 1 := by omega
        exact geo_Xa_mono F hle ((H3 _ hperp).2 hjr)
    exact hsub hx
  · let G : ℕ → E := fun n => if h : n + 1 < j then A ⟨n, by omega⟩ ⟨n + 1, h⟩ else 0
    have hg : ∀ i : Fin r, F.coefX (Y (F.fvec i.succ)) i = G i.val := by
      intro i
      by_cases h : i.val + 1 < j
      · simp only [G, dif_pos h]
        obtain ⟨y, hy, hyeq⟩ := geo_W_split hj F A hA ⟨i.val + 1, h⟩ i rfl
        have hsucc : F.fvec i.succ = F.fvec (Fin.castLE hj ⟨i.val + 1, h⟩) := rfl
        rw [hsucc, H2, hyeq]
        exact geo_coefX F i _ y hy
      · simp only [G, dif_neg h]
        have hjr : j ≤ r := by have := i.isLt; omega
        have hle : j - 1 ≤ i.val := by omega
        have hmem : Y (F.fvec i.succ) ∈ F.Xa i.val :=
          geo_Xa_mono F hle ((H3 _ (geo_fvec_perp F _)).2 hjr)
        have := geo_coefX F i 0 _ hmem
        rwa [zero_smul, zero_add] at this
    have e1 : F.ell Y = ∑ n ∈ Finset.range r, G n := by
      unfold FlagG.ell
      rw [← Fin.sum_univ_eq_sum_range G r]
      exact Finset.sum_congr rfl fun i _ => hg i
    have e2 : supSum A = ∑ n ∈ Finset.range j, G n := by
      rw [← Fin.sum_univ_eq_sum_range G j]
      rfl
    rw [e1, e2]
    exact geo_sum_range hj G fun n hn => by
      simp only [G]
      rw [dif_neg (show ¬ (n + 1 < j) by omega)]

end Flag

section Pair

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E} {j : ℕ}

def geoImg (F : FlagG S r T) (hj : j ≤ r + 1) (A : Matrix (Fin j) (Fin j) E) (a : Fin j) : S.V :=
  ∑ b, A b a • F.fvec (Fin.castLE hj b)

def geoV (F : FlagG S r T) (F' : FlagG S r T') (hj : j ≤ r + 1) : Fin j ⊕ Fin j → S.V :=
  Sum.elim (fun a => F.fvec (Fin.castLE hj a)) (fun a => F'.fvec (Fin.castLE hj a))

def geoW (F : FlagG S r T) (F' : FlagG S r T') (hj : j ≤ r + 1) (A A' : Matrix (Fin j) (Fin j) E) :
    Fin j ⊕ Fin j → S.V :=
  Sum.elim (geoImg F hj A) (geoImg F' hj A')

def GeoDec (F : FlagG S r T) (F' : FlagG S r T') (hj : j ≤ r + 1) (A A' : Matrix (Fin j) (Fin j) E)
    (Y : S.V →ₗ[E] S.V) : Prop :=
  ∀ y : S.V, ∃ α β : Fin j → E,
    Y y = ∑ a, α a • geoImg F hj A a + ∑ a, β a • geoImg F' hj A' a ∧
    (∀ a, S.hT (F.fvec (Fin.castLE hj a)) y =
      ∑ c, S.hT (F.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c)) * α c +
        ∑ c, S.hT (F.fvec (Fin.castLE hj a)) (F'.fvec (Fin.castLE hj c)) * β c) ∧
    (∀ a, S.hT (F'.fvec (Fin.castLE hj a)) y =
      ∑ c, S.hT (F'.fvec (Fin.castLE hj a)) (F'.fvec (Fin.castLE hj c)) * β c +
        ∑ c, S.hT (F'.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c)) * α c)

/- English proof (translation)
Unfold `GeoDec at h ⊢`. Introduce `y`. Take `⟨α, β, h1, h2, h3⟩` from `h y`. Conclude with `⟨β, α, by rw [h1, add_comm], h3, h2⟩`.
-/
theorem GeoDec.symm {F : FlagG S r T} {F' : FlagG S r T'} {hj : j ≤ r + 1} {A A' : Matrix (Fin j) (Fin j) E}
    {Y : S.V →ₗ[E] S.V} (h : GeoDec F F' hj A A' Y) : GeoDec F' F hj A' A Y := by
  unfold GeoDec at h ⊢
  intro y
  obtain ⟨α, β, h1, h2, h3⟩ := h y
  exact ⟨β, α, by rw [h1, add_comm], h3, h2⟩

/- English proof (translation)
Conclude with `geo_W_mem hj F A hA a`.
-/
theorem geo_img_mem (F : FlagG S r T) (hj : j ≤ r + 1) (A : Matrix (Fin j) (Fin j) E) (hA : StrictUp A) (a : Fin j) :
    geoImg F hj A a ∈ F.Xa a.val := by
  exact geo_W_mem hj F A hA a

/- English proof (translation)
Introduce `x hx`. Establish `hx' : ∀ u ∈ F.X, S.hT u x = 0` using `hx`. Establish `H1' : ∀ x y, S.hT (Y x) y + S.hT x (Y y) = 0` using `H1`. Take `⟨α, β, hYx, h2, -⟩` from `hdec x`. Establish `hP : ∑ a, α a • geoImg F hj A a ∈ F.X` using `sum_mem fun a _ => Submodule.smul_mem _ _ (geo_Xa_le_X F _ (geo_img_mem F hj A hA a))`.

Break down `hcase with ⟨hjr, hdet⟩ | ⟨hjr, han⟩` into its components or cases. Establish `hFX : ∀ a : Fin j, F.fvec (Fin.castLE hj a) ∈ F.X`. Introduce `a`. Establish `ha : a.val < r` using `by have := a.isLt; omega`. Rewrite using `[geo_castLE_eq hj a ha, geo_fvec_cast]`.

Conclude with `Submodule.subset_span ⟨_, rfl⟩`. Establish `hβ : β = 0`. Use `Matrix.eq_zero_of_mulVec_eq_zero hdet ?_` and prove the remaining obligations. Use function extensionality and compare the values at `a`. Establish `e` using `h2 a`.

Establish `hz : ∀ c, S.hT (F.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c)) = 0` using `fun c => geo_X_X F _ _ (hFX a) (hFX c)`. Rewrite `e` using `[hx' _ (hFX a)]`. Simplify using `only [hz, zero_mul, Finset.sum_const_zero, zero_add] at e`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]`. Conclude with `e.symm`.

Substitute `hβ` using the available equality. Simplify using `only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero] at hYx`. Establish `hmem : Y x ∈ F.Xa (j - 1)`. Rewrite using `[hYx]`. Use `sum_mem fun a _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations.

Establish `ha : a.val ≤ j - 1` using `by have := a.isLt; omega`. Conclude with `geo_Xa_mono F ha (geo_img_mem F hj A hA a)`. Conclude with `⟨geo_Xa_le_X F _ hmem, fun _ => hmem⟩`. Use `⟨?_, fun h => absurd h (by omega)⟩` and prove the remaining obligations. Establish `hQ : ∑ a, β a • geoImg F' hj A' a ∈ F'.X` using `sum_mem fun a _ => Submodule.smul_mem _ _ (geo_Xa_le_X F' _ (geo_img_mem F' hj A' hA' a))`.

Establish `hYimg : ∀ a : Fin j, Y (geoImg F hj A a) ∈ F.X`. Introduce `a`. Simplify using `only [geoImg, map_sum, map_smul, H2]`. Conclude with `sum_mem fun b _ => Submodule.smul_mem _ _ (geo_Xa_le_X F _ (geo_img_mem F hj A hA b))`. Establish `hs1 : S.hT (Y x) (∑ a, α a • geoImg F hj A a) = 0`.

Rewrite using `[map_sum]`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`. Establish `h1` using `H1' x (geoImg F hj A a)`. Establish `h0 : S.hT x (Y (geoImg F hj A a)) = 0`.

Rewrite using `[← S.herm.eq (Y (geoImg F hj A a)) x, hx' _ (hYimg a), map_zero]`. Rewrite `h1` using `[h0, add_zero]`. Rewrite using `[h1, smul_zero]`. Use `set P := ∑ a, α a • geoImg F hj A a with hPdef`. Use `set Q := ∑ a, β a • geoImg F' hj A' a with hQdef`.

Apply `han` to reduce the goal to its premises. Introduce `p`. Establish `hp : p.val < j` using `by have := p.isLt; omega`. Establish `hpe : F.fvec p = F.fvec (Fin.castLE hj ⟨p.val, hp⟩)` using `rfl`. Establish `h1` using `H1' (F.fvec p) x`.

Rewrite `h1` using `[hpe, H2, hx' _ (geo_Xa_le_X F _ (geo_img_mem F hj A hA _)), zero_add]`. Rewrite using `[hpe]`. Conclude with `h1`. Establish `hPP : S.hT P P = 0` using `geo_X_X F _ _ hP hP`. Establish `hQQ : S.hT Q Q = 0` using `geo_X_X F' _ _ hQ hQ`.

Establish `hQP : S.hT Q P = 0`. Establish `h5` using `hs1`. Rewrite `h5` using `[hYx, map_add, LinearMap.add_apply, hPP, zero_add]`. Conclude with `h5`. Establish `hPQ : S.hT P Q = 0`.

Rewrite using `[← S.herm.eq Q P, hQP, map_zero]`. Rewrite using `[hYx]`. Simplify using `only [map_add, LinearMap.add_apply, hPP, hQQ, hPQ, hQP, add_zero]`.
-/
theorem geometric_decomposition_maps_perp_into_flag (F : FlagG S r T) (F' : FlagG S r T') (hj : j ≤ r + 1) (A A' : Matrix (Fin j) (Fin j) E)
    (hA : StrictUp A) (hA' : StrictUp A') (Y : S.V →ₗ[E] S.V) (hdec : GeoDec F F' hj A A' Y) (H1 : Y ∈ LieU S)
    (H2 : ∀ a : Fin j, Y (F.fvec (Fin.castLE hj a)) = geoImg F hj A a)
    (hcase : (j ≤ r ∧ (Matrix.of fun a c : Fin j =>
        S.hT (F.fvec (Fin.castLE hj a)) (F'.fvec (Fin.castLE hj c))).det ≠ 0) ∨
      (j = r + 1 ∧ ∀ y : S.V, (∀ a, S.hT (F.fvec a) y = 0) → S.hT y y = 0 → y ∈ F.X)) :
    ∀ x ∈ perpS S F.X, Y x ∈ F.X ∧ (j ≤ r → Y x ∈ F.Xa (j - 1)) := by
  intro x hx
  have hx' : ∀ u ∈ F.X, S.hT u x = 0 := hx
  have H1' : ∀ x y, S.hT (Y x) y + S.hT x (Y y) = 0 := H1
  obtain ⟨α, β, hYx, h2, -⟩ := hdec x
  have hP : ∑ a, α a • geoImg F hj A a ∈ F.X :=
    sum_mem fun a _ => Submodule.smul_mem _ _ (geo_Xa_le_X F _ (geo_img_mem F hj A hA a))
  rcases hcase with ⟨hjr, hdet⟩ | ⟨hjr, han⟩
  · have hFX : ∀ a : Fin j, F.fvec (Fin.castLE hj a) ∈ F.X := by
      intro a
      have ha : a.val < r := by have := a.isLt; omega
      rw [geo_castLE_eq hj a ha, geo_fvec_cast]
      exact Submodule.subset_span ⟨_, rfl⟩
    have hβ : β = 0 := by
      refine Matrix.eq_zero_of_mulVec_eq_zero hdet ?_
      funext a
      have e := h2 a
      have hz : ∀ c, S.hT (F.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c)) = 0 :=
        fun c => geo_X_X F _ _ (hFX a) (hFX c)
      rw [hx' _ (hFX a)] at e
      simp only [hz, zero_mul, Finset.sum_const_zero, zero_add] at e
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
      exact e.symm
    subst hβ
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero] at hYx
    have hmem : Y x ∈ F.Xa (j - 1) := by
      rw [hYx]
      refine sum_mem fun a _ => Submodule.smul_mem _ _ ?_
      have ha : a.val ≤ j - 1 := by have := a.isLt; omega
      exact geo_Xa_mono F ha (geo_img_mem F hj A hA a)
    exact ⟨geo_Xa_le_X F _ hmem, fun _ => hmem⟩
  · refine ⟨?_, fun h => absurd h (by omega)⟩
    have hQ : ∑ a, β a • geoImg F' hj A' a ∈ F'.X :=
      sum_mem fun a _ => Submodule.smul_mem _ _ (geo_Xa_le_X F' _ (geo_img_mem F' hj A' hA' a))
    have hYimg : ∀ a : Fin j, Y (geoImg F hj A a) ∈ F.X := by
      intro a
      simp only [geoImg, map_sum, map_smul, H2]
      exact sum_mem fun b _ => Submodule.smul_mem _ _ (geo_Xa_le_X F _ (geo_img_mem F hj A hA b))
    have hs1 : S.hT (Y x) (∑ a, α a • geoImg F hj A a) = 0 := by
      rw [map_sum]
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [map_smul]
      have h1 := H1' x (geoImg F hj A a)
      have h0 : S.hT x (Y (geoImg F hj A a)) = 0 := by
        rw [← S.herm.eq (Y (geoImg F hj A a)) x, hx' _ (hYimg a), map_zero]
      rw [h0, add_zero] at h1
      rw [h1, smul_zero]
    set P := ∑ a, α a • geoImg F hj A a with hPdef
    set Q := ∑ a, β a • geoImg F' hj A' a with hQdef
    apply han
    · intro p
      have hp : p.val < j := by have := p.isLt; omega
      have hpe : F.fvec p = F.fvec (Fin.castLE hj ⟨p.val, hp⟩) := rfl
      have h1 := H1' (F.fvec p) x
      rw [hpe, H2, hx' _ (geo_Xa_le_X F _ (geo_img_mem F hj A hA _)), zero_add] at h1
      rw [hpe]
      exact h1
    · have hPP : S.hT P P = 0 := geo_X_X F _ _ hP hP
      have hQQ : S.hT Q Q = 0 := geo_X_X F' _ _ hQ hQ
      have hQP : S.hT Q P = 0 := by
        have h5 := hs1
        rw [hYx, map_add, LinearMap.add_apply, hPP, zero_add] at h5
        exact h5
      have hPQ : S.hT P Q = 0 := by
        rw [← S.herm.eq Q P, hQP, map_zero]
      rw [hYx]
      simp only [map_add, LinearMap.add_apply, hPP, hQQ, hPQ, hQP, add_zero]

end Pair

section Main

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E} {j : ℕ}

/- English proof (translation)
Break down `i with a | a` into its components or cases. Simplify using `only [geoW, Sum.elim_inl, geoImg]`. Conclude with `sum_mem fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl b, rfl⟩)`. Simplify using `only [geoW, Sum.elim_inr, geoImg]`. Conclude with `sum_mem fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr b, rfl⟩)`.
-/
theorem geo_hw (F : FlagG S r T) (F' : FlagG S r T') (hj : j ≤ r + 1) (A A' : Matrix (Fin j) (Fin j) E)
    (i : Fin j ⊕ Fin j) : geoW F F' hj A A' i ∈ Submodule.span E (Set.range (geoV F F' hj)) := by
  rcases i with a | a
  · simp only [geoW, Sum.elim_inl, geoImg]
    exact sum_mem fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl b, rfl⟩)
  · simp only [geoW, Sum.elim_inr, geoImg]
    exact sum_mem fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr b, rfl⟩)

/- English proof (translation)
Simplify using `only [geoImg, map_sum, map_smulₛₗ, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, Zhat, brS]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun b _ => mul_comm _ _`.
-/
theorem geo_cross (F : FlagG S r T) (F' : FlagG S r T') (hj : j ≤ r + 1) (A A' : Matrix (Fin j) (Fin j) E)
    (a c : Fin j) :
    S.hT (geoImg F hj A a) (F'.fvec (Fin.castLE hj c)) + S.hT (F.fvec (Fin.castLE hj a)) (geoImg F' hj A' c) =
      (Aᴴ * (Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj) +
        (Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj) * A') a c := by
  simp only [geoImg, map_sum, map_smulₛₗ, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, Matrix.add_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.submatrix_apply, Zhat, brS]
  congr 1
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

/- English proof (translation)
Apply the tactic sequence `rcases i with a | a <;> rcases k with c | c <;> simp only [geoW, geoV, Sum.elim_inl, Sum.elim_inr]`. Establish `h1` using `geo_Xa_le_X F _ (geo_img_mem F hj A hA a)`. Establish `h2` using `geo_Xa_le_X F _ (geo_img_mem F hj A hA c)`. Rewrite using `[geo_X_fvec F _ h1, geo_fvec_X F _ h2, add_zero]`. Establish `P` using `geo_cross F F' hj A A' a c`.

Rewrite `P` using `[hR]`. Simplify using `using P`. Establish `P` using `geo_cross F F' hj A A' c a`. Rewrite `P` using `[hR, Matrix.zero_apply]`. Rewrite using `[← S.herm.eq (F.fvec (Fin.castLE hj c)) (geoImg F' hj A' a), ← S.herm.eq (geoImg F hj A c) (F'.fvec (Fin.castLE hj a)), add_comm, ← map_add, P, map_zero]`.

Establish `h1` using `geo_Xa_le_X F' _ (geo_img_mem F' hj A' hA' a)`. Establish `h2` using `geo_Xa_le_X F' _ (geo_img_mem F' hj A' hA' c)`. Rewrite using `[geo_X_fvec F' _ h1, geo_fvec_X F' _ h2, add_zero]`.
-/
theorem geo_hsk (F : FlagG S r T) (F' : FlagG S r T') (hj : j ≤ r + 1) (A A' : Matrix (Fin j) (Fin j) E)
    (hA : StrictUp A) (hA' : StrictUp A')
    (hR : Aᴴ * (Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj) +
      (Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj) * A' = 0) (i k : Fin j ⊕ Fin j) :
    S.hT (geoW F F' hj A A' i) (geoV F F' hj k) + S.hT (geoV F F' hj i) (geoW F F' hj A A' k) = 0 := by
  rcases i with a | a <;> rcases k with c | c <;> simp only [geoW, geoV, Sum.elim_inl, Sum.elim_inr]
  · have h1 := geo_Xa_le_X F _ (geo_img_mem F hj A hA a)
    have h2 := geo_Xa_le_X F _ (geo_img_mem F hj A hA c)
    rw [geo_X_fvec F _ h1, geo_fvec_X F _ h2, add_zero]
  · have P := geo_cross F F' hj A A' a c
    rw [hR] at P
    simpa using P
  · have P := geo_cross F F' hj A A' c a
    rw [hR, Matrix.zero_apply] at P
    rw [← S.herm.eq (F.fvec (Fin.castLE hj c)) (geoImg F' hj A' a),
      ← S.herm.eq (geoImg F hj A c) (F'.fvec (Fin.castLE hj a)), add_comm, ← map_add, P, map_zero]
  · have h1 := geo_Xa_le_X F' _ (geo_img_mem F' hj A' hA' a)
    have h2 := geo_Xa_le_X F' _ (geo_img_mem F' hj A' hA' c)
    rw [geo_X_fvec F' _ h1, geo_fvec_X F' _ h2, add_zero]

/- English proof (translation)
Unfold `Dl leadMinorE at h`. Rewrite `h` using `[dif_pos hj]`. Conclude with `h`.
-/
theorem geo_Z_det (F : FlagG S r T) (F' : FlagG S r T') (hj : j ≤ r + 1) (h : Dl F F' j ≠ 0) :
    ((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj)).det ≠ 0 := by
  unfold Dl leadMinorE at h
  rw [dif_pos hj] at h
  exact h

/- English proof (translation)
Rewrite using `[isUnit_iff_ne_zero]`. Introduce `hdet0`. Take `⟨w, hw0, hw⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 hdet0`. Apply `hw0` to reduce the goal to its premises. Establish `rowL : ∀ a : Fin j, ∑ c, S.hT (F.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c)) * w (Sum.inl c) + ∑ c, S.hT (F.fvec (Fin.castLE hj a)) (F'.fvec (Fin.castLE hj c)) * w (Sum.inr c) = 0`.

Introduce `a`. Establish `e` using `congrFun hw (Sum.inl a)`. Simplify using `only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Pi.zero_apply] at e`. Conclude with `e`. Establish `rowR : ∀ a : Fin j, ∑ c, S.hT (F'.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c)) * w (Sum.inl c) + ∑ c, S.hT (F'.fvec (Fin.castLE hj a)) (F'.fvec (Fin.castLE hj c)) * w (Sum.inr c) = 0`.

Introduce `a`. Establish `e` using `congrFun hw (Sum.inr a)`. Simplify using `only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Pi.zero_apply] at e`. Conclude with `e`. Establish `hZ : ∀ a c : Fin j, S.hT (F'.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c)) = ((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj))ᴴ a c`.

Introduce `a c`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.submatrix_apply, Zhat, brS]`. Conclude with `(S.herm.eq _ _).symm`. Establish `hmvL : ∀ a : Fin j, (((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj)) *ᵥ (fun c => w (Sum.inr c))) a = ∑ c, S.hT (F.fvec (Fin.castLE hj a)) (F'.fvec (Fin.castLE hj c)) * w (Sum.inr c)` using `fun a => rfl`. Establish `hmvR : ∀ a : Fin j, (((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj))ᴴ *ᵥ (fun c => w (Sum.inl c))) a = ∑ c, S.hT (F'.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c)) * w (Sum.inl c)`.

Introduce `a`. Simplify using `only [Matrix.mulVec, dotProduct, hZ]`. Establish `hw_of : (fun c => w (Sum.inl c)) = 0 → (fun c => w (Sum.inr c)) = 0 → w = 0`. Introduce `h1 h2`. Use function extensionality and compare the values at `k`.

Break down `k with c | c` into its components or cases. Conclude with `congrFun h1 c`. Conclude with `congrFun h2 c`. Break down `hcase with ⟨hjr, hD⟩ | ⟨hjr, hG⟩` into its components or cases. Establish `hdet` using `geo_Z_det F F' hj hD`.

Establish `hFX : ∀ a : Fin j, F.fvec (Fin.castLE hj a) ∈ F.X`. Introduce `a`. Establish `ha : a.val < r` using `by have := a.isLt; omega`. Rewrite using `[geo_castLE_eq hj a ha, geo_fvec_cast]`. Conclude with `Submodule.subset_span ⟨_, rfl⟩`.

Establish `hF'X : ∀ a : Fin j, F'.fvec (Fin.castLE hj a) ∈ F'.X`. Introduce `a`. Establish `ha : a.val < r` using `by have := a.isLt; omega`. Rewrite using `[geo_castLE_eq hj a ha, geo_fvec_cast]`. Conclude with `Submodule.subset_span ⟨_, rfl⟩`.

Apply `hw_of` to reduce the goal to its premises. Establish `hdetH : (((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj))ᴴ).det ≠ 0`. Rewrite using `[Matrix.det_conjTranspose]`. Conclude with `fun h0 => hdet (star_eq_zero.1 h0)`. Use `Matrix.eq_zero_of_mulVec_eq_zero hdetH ?_` and prove the remaining obligations.

Use function extensionality and compare the values at `a`. Rewrite using `[hmvR a, Pi.zero_apply]`. Establish `hz : ∀ c : Fin j, S.hT (F'.fvec (Fin.castLE hj a)) (F'.fvec (Fin.castLE hj c)) = 0` using `fun c => geo_X_X F' _ _ (hF'X a) (hF'X c)`. Establish `e` using `rowR a`. Simplify using `only [hz, zero_mul, Finset.sum_const_zero, add_zero] at e`.

Conclude with `e`. Use `Matrix.eq_zero_of_mulVec_eq_zero hdet ?_` and prove the remaining obligations. Use function extensionality and compare the values at `a`. Rewrite using `[hmvL a, Pi.zero_apply]`. Establish `hz : ∀ c : Fin j, S.hT (F.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c)) = 0` using `fun c => geo_X_X F _ _ (hFX a) (hFX c)`.

Establish `e` using `rowL a`. Simplify using `only [hz, zero_mul, Finset.sum_const_zero, zero_add] at e`. Conclude with `e`. Substitute `hjr` using the available equality. Establish `hcl : ∀ c : Fin (r + 1), Fin.castLE hj c = c` using `fun c => Fin.ext rfl`.

Establish `hPL : ∀ a : Fin (r + 1), ∑ c, S.hT (F.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c)) * w (Sum.inl c) = if a = Fin.last r then -T * w (Sum.inl (Fin.last r)) else 0`. Introduce `a`. Simplify using `only [hcl]`. Rewrite using `[Fin.sum_univ_castSucc]`. Break down `Fin.eq_castSucc_or_eq_last a with ⟨b, rfl⟩ | rfl` into its components or cases.

Rewrite using `[if_neg (Fin.castSucc_lt_last b).ne]`. Establish `he : ∀ c : Fin r, S.hT (F.fvec b.castSucc) (F.fvec c.castSucc) = 0` using `fun c => by`. Rewrite using `[geo_fvec_cast, geo_fvec_cast]`. Conclude with `F.e_iso b c`. Simplify using `only [he, zero_mul, Finset.sum_const_zero, zero_add]`.

Rewrite using `[geo_fvec_cast, geo_fvec_last, F.z_orth b, zero_mul]`. Rewrite using `[if_pos rfl]`. Establish `hz0 : ∀ c : Fin r, S.hT (F.fvec (Fin.last r)) (F.fvec c.castSucc) = 0` using `fun c => by`. Rewrite using `[geo_fvec_last, geo_fvec_cast, ← S.herm.eq (F.e c) F.z, F.z_orth c, map_zero]`. Simplify using `only [hz0, zero_mul, Finset.sum_const_zero, zero_add]`.

Rewrite using `[geo_fvec_last, F.z_norm]`. Establish `hUR : ∀ a : Fin (r + 1), ∑ c, S.hT (F'.fvec (Fin.castLE hj a)) (F'.fvec (Fin.castLE hj c)) * w (Sum.inr c) = if a = Fin.last r then -T' * w (Sum.inr (Fin.last r)) else 0`. Introduce `a`. Simplify using `only [hcl]`. Rewrite using `[Fin.sum_univ_castSucc]`.

Break down `Fin.eq_castSucc_or_eq_last a with ⟨b, rfl⟩ | rfl` into its components or cases. Rewrite using `[if_neg (Fin.castSucc_lt_last b).ne]`. Establish `he : ∀ c : Fin r, S.hT (F'.fvec b.castSucc) (F'.fvec c.castSucc) = 0` using `fun c => by`. Rewrite using `[geo_fvec_cast, geo_fvec_cast]`. Conclude with `F'.e_iso b c`.

Simplify using `only [he, zero_mul, Finset.sum_const_zero, zero_add]`. Rewrite using `[geo_fvec_cast, geo_fvec_last, F'.z_orth b, zero_mul]`. Rewrite using `[if_pos rfl]`. Establish `hz0 : ∀ c : Fin r, S.hT (F'.fvec (Fin.last r)) (F'.fvec c.castSucc) = 0` using `fun c => by`. Rewrite using `[geo_fvec_last, geo_fvec_cast, ← S.herm.eq (F'.e c) F'.z, F'.z_orth c, map_zero]`.

Simplify using `only [hz0, zero_mul, Finset.sum_const_zero, zero_add]`. Rewrite using `[geo_fvec_last, F'.z_norm]`. Establish `hZy : ((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj)) *ᵥ (fun c => w (Sum.inr c)) = Pi.single (Fin.last r) (T * w (Sum.inl (Fin.last r)))`. Use function extensionality and compare the values at `a`. Establish `e` using `rowL a`.

Rewrite `e` using `[hPL a]`. Rewrite using `[hmvL a]`. Break down `Fin.eq_castSucc_or_eq_last a with ⟨b, rfl⟩ | rfl` into its components or cases. Rewrite `e` using `[if_neg (Fin.castSucc_lt_last b).ne, zero_add]`. Rewrite using `[Pi.single_eq_of_ne (Fin.castSucc_lt_last b).ne]`.

Conclude with `e`. Rewrite `e` using `[if_pos rfl]`. Rewrite using `[Pi.single_eq_same]`. Take the linear combination `e`. Establish `hZx : ((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj))ᴴ *ᵥ (fun c => w (Sum.inl c)) = Pi.single (Fin.last r) (T' * w (Sum.inr (Fin.last r)))`.

Use function extensionality and compare the values at `a`. Establish `e` using `rowR a`. Rewrite `e` using `[hUR a]`. Rewrite using `[hmvR a]`. Break down `Fin.eq_castSucc_or_eq_last a with ⟨b, rfl⟩ | rfl` into its components or cases.

Rewrite `e` using `[if_neg (Fin.castSucc_lt_last b).ne, add_zero]`. Rewrite using `[Pi.single_eq_of_ne (Fin.castSucc_lt_last b).ne]`. Conclude with `e`. Rewrite `e` using `[if_pos rfl]`. Rewrite using `[Pi.single_eq_same]`.

Take the linear combination `e`. Establish `hadj : ∀ (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (v : Fin (r + 1) → E) (s : E), M *ᵥ v = Pi.single (Fin.last r) s → M.det * v (Fin.last r) = M.adjugate (Fin.last r) (Fin.last r) * s`. Introduce `M v s hv`. Establish `h1 : M.adjugate *ᵥ (M *ᵥ v) = M.det • v`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.adjugate_mul]`.

Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, Matrix.one_apply]`. Rewrite `h1` using `[hv]`. Establish `h2` using `congrFun h1 (Fin.last r)`. Simplify using `only [Matrix.mulVec_single, Pi.smul_apply, smul_eq_mul] at h2`.

Conclude with `h2.symm`. Establish `hdl : Dl F F' r = (((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj)).submatrix Fin.castSucc Fin.castSucc).det`. Unfold `Dl leadMinorE`. Conclude with `dif_pos (Nat.le_succ r)`. Establish `hDl : Dl F F' (r + 1) = ((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj)).det`.

Unfold `Dl leadMinorE`. Conclude with `dif_pos hj`. Establish `hadjll : ((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj)).adjugate (Fin.last r) (Fin.last r) = Dl F F' r`. Rewrite using `[Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last, hdl, Fin.val_last, (Even.neg_one_pow ⟨r, rfl⟩ : ((-1 : E) ^ (r + r)) = 1), one_mul]`. Establish `E1` using `hadj _ _ _ hZy`.

Establish `E2` using `hadj _ _ _ hZx`. Rewrite `E1` using `[hadjll, ← hDl]`. Rewrite `E2` using `[Matrix.det_conjTranspose, ← Matrix.adjugate_conjTranspose, Matrix.conjTranspose_apply, hadjll, ← hDl]`. Unfold `Gflag at hG`. Establish `hx0 : w (Sum.inl (Fin.last r)) = 0`.

Establish `h0 : w (Sum.inl (Fin.last r)) * (Dl F F' (r + 1) * star (Dl F F' (r + 1)) - T * T' * (Dl F F' r * star (Dl F F' r))) = 0`. Take the linear combination `Dl F F' (r + 1) * E2 + star (Dl F F' r) * T' * E1`. Break down `mul_eq_zero.1 h0 with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd h hG`.

Establish `hy0 : w (Sum.inr (Fin.last r)) = 0`. Establish `h0 : w (Sum.inr (Fin.last r)) * (Dl F F' (r + 1) * star (Dl F F' (r + 1)) - T * T' * (Dl F F' r * star (Dl F F' r))) = 0`. Take the linear combination `star (Dl F F' (r + 1)) * E1 + Dl F F' r * T * E2`. Break down `mul_eq_zero.1 h0 with h | h` into its components or cases. Conclude with `h`.

Conclude with `absurd h hG`. Establish `hZy0 : ((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj)) *ᵥ (fun c => w (Sum.inr c)) = 0`. Rewrite using `[hZy, hx0, mul_zero, Pi.single_zero]`. Establish `hZx0 : ((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj))ᴴ *ᵥ (fun c => w (Sum.inl c)) = 0`. Rewrite using `[hZx, hy0, mul_zero, Pi.single_zero]`.

Establish `lead : ∀ (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (v : Fin (r + 1) → E), M *ᵥ v = 0 → v (Fin.last r) = 0 → (M.submatrix Fin.castSucc Fin.castSucc).det ≠ 0 → v = 0`. Introduce `M v hMv hvl hdet`. Establish `hv' : (fun c : Fin r => v c.castSucc) = 0`. Use `Matrix.eq_zero_of_mulVec_eq_zero hdet ?_` and prove the remaining obligations. Use function extensionality and compare the values at `a`.

Establish `e` using `congrFun hMv a.castSucc`. Simplify using `only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hvl, mul_zero, add_zero, Pi.zero_apply] at e`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Pi.zero_apply]`. Conclude with `e`. Use function extensionality and compare the values at `c`.

Break down `Fin.eq_castSucc_or_eq_last c with ⟨b, rfl⟩ | rfl` into its components or cases. Conclude with `congrFun hv' b`. Conclude with `hvl`. Establish `full : ∀ (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (v : Fin (r + 1) → E), M *ᵥ v = 0 → v (Fin.last r) = 0 → (M.det ≠ 0 ∨ (M.submatrix Fin.castSucc Fin.castSucc).det ≠ 0) → v = 0`. Introduce `M v hMv hvl h`.

Break down `h with h | h` into its components or cases. Conclude with `Matrix.eq_zero_of_mulVec_eq_zero h hMv`. Conclude with `lead M v hMv hvl h`. Establish `hor : Dl F F' (r + 1) ≠ 0 ∨ Dl F F' r ≠ 0`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Apply `hG` to reduce the goal to its premises. Rewrite using `[hc.1, hc.2]`. Expand and normalize the polynomial expressions, which then agree. Apply `hw_of` to reduce the goal to its premises.

Apply `full _ _ hZx0 hx0` to reduce the goal to its premises. Break down `hor with h | h` into its components or cases. Use `left`. Rewrite using `[Matrix.det_conjTranspose, ← hDl]`. Conclude with `fun h0 => h (star_eq_zero.1 h0)`.

Use `right`. Rewrite using `[← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose, ← hdl]`. Conclude with `fun h0 => h (star_eq_zero.1 h0)`. Apply `full _ _ hZy0 hy0` to reduce the goal to its premises. Break down `hor with h | h` into its components or cases.

Use `left`. Rewrite using `[← hDl]`. Conclude with `h`. Use `right`. Rewrite using `[← hdl]`.

Conclude with `h`.
-/
theorem geo_gram_unit (F : FlagG S r T) (F' : FlagG S r T') (hj : j ≤ r + 1)
    (hcase : (j ≤ r ∧ Dl F F' j ≠ 0) ∨ (j = r + 1 ∧ Gflag F F' ≠ 0)) :
    IsUnit (geoGram (geoV F F' hj)).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet0
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet0
  apply hw0
  have rowL : ∀ a : Fin j, ∑ c, S.hT (F.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c)) * w (Sum.inl c) +
      ∑ c, S.hT (F.fvec (Fin.castLE hj a)) (F'.fvec (Fin.castLE hj c)) * w (Sum.inr c) = 0 := by
    intro a
    have e := congrFun hw (Sum.inl a)
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Pi.zero_apply] at e
    exact e
  have rowR : ∀ a : Fin j, ∑ c, S.hT (F'.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c)) * w (Sum.inl c) +
      ∑ c, S.hT (F'.fvec (Fin.castLE hj a)) (F'.fvec (Fin.castLE hj c)) * w (Sum.inr c) = 0 := by
    intro a
    have e := congrFun hw (Sum.inr a)
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Pi.zero_apply] at e
    exact e
  have hZ : ∀ a c : Fin j, S.hT (F'.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c)) =
      ((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj))ᴴ a c := by
    intro a c
    simp only [Matrix.conjTranspose_apply, Matrix.submatrix_apply, Zhat, brS]
    exact (S.herm.eq _ _).symm
  have hmvL : ∀ a : Fin j, (((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj)) *ᵥ
      (fun c => w (Sum.inr c))) a =
      ∑ c, S.hT (F.fvec (Fin.castLE hj a)) (F'.fvec (Fin.castLE hj c)) * w (Sum.inr c) := fun a => rfl
  have hmvR : ∀ a : Fin j, (((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj))ᴴ *ᵥ
      (fun c => w (Sum.inl c))) a =
      ∑ c, S.hT (F'.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c)) * w (Sum.inl c) := by
    intro a
    simp only [Matrix.mulVec, dotProduct, hZ]
  have hw_of : (fun c => w (Sum.inl c)) = 0 → (fun c => w (Sum.inr c)) = 0 → w = 0 := by
    intro h1 h2
    funext k
    rcases k with c | c
    · exact congrFun h1 c
    · exact congrFun h2 c
  rcases hcase with ⟨hjr, hD⟩ | ⟨hjr, hG⟩
  · have hdet := geo_Z_det F F' hj hD
    have hFX : ∀ a : Fin j, F.fvec (Fin.castLE hj a) ∈ F.X := by
      intro a
      have ha : a.val < r := by have := a.isLt; omega
      rw [geo_castLE_eq hj a ha, geo_fvec_cast]
      exact Submodule.subset_span ⟨_, rfl⟩
    have hF'X : ∀ a : Fin j, F'.fvec (Fin.castLE hj a) ∈ F'.X := by
      intro a
      have ha : a.val < r := by have := a.isLt; omega
      rw [geo_castLE_eq hj a ha, geo_fvec_cast]
      exact Submodule.subset_span ⟨_, rfl⟩
    apply hw_of
    · have hdetH : (((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj))ᴴ).det ≠ 0 := by
        rw [Matrix.det_conjTranspose]
        exact fun h0 => hdet (star_eq_zero.1 h0)
      refine Matrix.eq_zero_of_mulVec_eq_zero hdetH ?_
      funext a
      rw [hmvR a, Pi.zero_apply]
      have hz : ∀ c : Fin j, S.hT (F'.fvec (Fin.castLE hj a)) (F'.fvec (Fin.castLE hj c)) = 0 :=
        fun c => geo_X_X F' _ _ (hF'X a) (hF'X c)
      have e := rowR a
      simp only [hz, zero_mul, Finset.sum_const_zero, add_zero] at e
      exact e
    · refine Matrix.eq_zero_of_mulVec_eq_zero hdet ?_
      funext a
      rw [hmvL a, Pi.zero_apply]
      have hz : ∀ c : Fin j, S.hT (F.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c)) = 0 :=
        fun c => geo_X_X F _ _ (hFX a) (hFX c)
      have e := rowL a
      simp only [hz, zero_mul, Finset.sum_const_zero, zero_add] at e
      exact e
  · subst hjr
    have hcl : ∀ c : Fin (r + 1), Fin.castLE hj c = c := fun c => Fin.ext rfl
    have hPL : ∀ a : Fin (r + 1), ∑ c, S.hT (F.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c)) *
        w (Sum.inl c) = if a = Fin.last r then -T * w (Sum.inl (Fin.last r)) else 0 := by
      intro a
      simp only [hcl]
      rw [Fin.sum_univ_castSucc]
      rcases Fin.eq_castSucc_or_eq_last a with ⟨b, rfl⟩ | rfl
      · rw [if_neg (Fin.castSucc_lt_last b).ne]
        have he : ∀ c : Fin r, S.hT (F.fvec b.castSucc) (F.fvec c.castSucc) = 0 := fun c => by
          rw [geo_fvec_cast, geo_fvec_cast]
          exact F.e_iso b c
        simp only [he, zero_mul, Finset.sum_const_zero, zero_add]
        rw [geo_fvec_cast, geo_fvec_last, F.z_orth b, zero_mul]
      · rw [if_pos rfl]
        have hz0 : ∀ c : Fin r, S.hT (F.fvec (Fin.last r)) (F.fvec c.castSucc) = 0 := fun c => by
          rw [geo_fvec_last, geo_fvec_cast, ← S.herm.eq (F.e c) F.z, F.z_orth c, map_zero]
        simp only [hz0, zero_mul, Finset.sum_const_zero, zero_add]
        rw [geo_fvec_last, F.z_norm]
    have hUR : ∀ a : Fin (r + 1), ∑ c, S.hT (F'.fvec (Fin.castLE hj a)) (F'.fvec (Fin.castLE hj c)) *
        w (Sum.inr c) = if a = Fin.last r then -T' * w (Sum.inr (Fin.last r)) else 0 := by
      intro a
      simp only [hcl]
      rw [Fin.sum_univ_castSucc]
      rcases Fin.eq_castSucc_or_eq_last a with ⟨b, rfl⟩ | rfl
      · rw [if_neg (Fin.castSucc_lt_last b).ne]
        have he : ∀ c : Fin r, S.hT (F'.fvec b.castSucc) (F'.fvec c.castSucc) = 0 := fun c => by
          rw [geo_fvec_cast, geo_fvec_cast]
          exact F'.e_iso b c
        simp only [he, zero_mul, Finset.sum_const_zero, zero_add]
        rw [geo_fvec_cast, geo_fvec_last, F'.z_orth b, zero_mul]
      · rw [if_pos rfl]
        have hz0 : ∀ c : Fin r, S.hT (F'.fvec (Fin.last r)) (F'.fvec c.castSucc) = 0 := fun c => by
          rw [geo_fvec_last, geo_fvec_cast, ← S.herm.eq (F'.e c) F'.z, F'.z_orth c, map_zero]
        simp only [hz0, zero_mul, Finset.sum_const_zero, zero_add]
        rw [geo_fvec_last, F'.z_norm]
    have hZy : ((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj)) *ᵥ (fun c => w (Sum.inr c)) =
        Pi.single (Fin.last r) (T * w (Sum.inl (Fin.last r))) := by
      funext a
      have e := rowL a
      rw [hPL a] at e
      rw [hmvL a]
      rcases Fin.eq_castSucc_or_eq_last a with ⟨b, rfl⟩ | rfl
      · rw [if_neg (Fin.castSucc_lt_last b).ne, zero_add] at e
        rw [Pi.single_eq_of_ne (Fin.castSucc_lt_last b).ne]
        exact e
      · rw [if_pos rfl] at e
        rw [Pi.single_eq_same]
        linear_combination e
    have hZx : ((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj))ᴴ *ᵥ (fun c => w (Sum.inl c)) =
        Pi.single (Fin.last r) (T' * w (Sum.inr (Fin.last r))) := by
      funext a
      have e := rowR a
      rw [hUR a] at e
      rw [hmvR a]
      rcases Fin.eq_castSucc_or_eq_last a with ⟨b, rfl⟩ | rfl
      · rw [if_neg (Fin.castSucc_lt_last b).ne, add_zero] at e
        rw [Pi.single_eq_of_ne (Fin.castSucc_lt_last b).ne]
        exact e
      · rw [if_pos rfl] at e
        rw [Pi.single_eq_same]
        linear_combination e
    have hadj : ∀ (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (v : Fin (r + 1) → E) (s : E),
        M *ᵥ v = Pi.single (Fin.last r) s → M.det * v (Fin.last r) = M.adjugate (Fin.last r) (Fin.last r) * s := by
      intro M v s hv
      have h1 : M.adjugate *ᵥ (M *ᵥ v) = M.det • v := by
        rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul]
        funext i
        simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
      rw [hv] at h1
      have h2 := congrFun h1 (Fin.last r)
      simp only [Matrix.mulVec_single, Pi.smul_apply, smul_eq_mul] at h2
      exact h2.symm
    have hdl : Dl F F' r = (((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj)).submatrix
        Fin.castSucc Fin.castSucc).det := by
      unfold Dl leadMinorE
      exact dif_pos (Nat.le_succ r)
    have hDl : Dl F F' (r + 1) = ((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj)).det := by
      unfold Dl leadMinorE
      exact dif_pos hj
    have hadjll : ((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj)).adjugate (Fin.last r) (Fin.last r) =
        Dl F F' r := by
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last, hdl, Fin.val_last,
        (Even.neg_one_pow ⟨r, rfl⟩ : ((-1 : E) ^ (r + r)) = 1), one_mul]
    have E1 := hadj _ _ _ hZy
    have E2 := hadj _ _ _ hZx
    rw [hadjll, ← hDl] at E1
    rw [Matrix.det_conjTranspose, ← Matrix.adjugate_conjTranspose, Matrix.conjTranspose_apply, hadjll, ← hDl] at E2
    unfold Gflag at hG
    have hx0 : w (Sum.inl (Fin.last r)) = 0 := by
      have h0 : w (Sum.inl (Fin.last r)) * (Dl F F' (r + 1) * star (Dl F F' (r + 1)) -
          T * T' * (Dl F F' r * star (Dl F F' r))) = 0 := by
        linear_combination Dl F F' (r + 1) * E2 + star (Dl F F' r) * T' * E1
      rcases mul_eq_zero.1 h0 with h | h
      · exact h
      · exact absurd h hG
    have hy0 : w (Sum.inr (Fin.last r)) = 0 := by
      have h0 : w (Sum.inr (Fin.last r)) * (Dl F F' (r + 1) * star (Dl F F' (r + 1)) -
          T * T' * (Dl F F' r * star (Dl F F' r))) = 0 := by
        linear_combination star (Dl F F' (r + 1)) * E1 + Dl F F' r * T * E2
      rcases mul_eq_zero.1 h0 with h | h
      · exact h
      · exact absurd h hG
    have hZy0 : ((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj)) *ᵥ (fun c => w (Sum.inr c)) = 0 := by
      rw [hZy, hx0, mul_zero, Pi.single_zero]
    have hZx0 : ((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj))ᴴ *ᵥ (fun c => w (Sum.inl c)) = 0 := by
      rw [hZx, hy0, mul_zero, Pi.single_zero]
    have lead : ∀ (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (v : Fin (r + 1) → E),
        M *ᵥ v = 0 → v (Fin.last r) = 0 → (M.submatrix Fin.castSucc Fin.castSucc).det ≠ 0 → v = 0 := by
      intro M v hMv hvl hdet
      have hv' : (fun c : Fin r => v c.castSucc) = 0 := by
        refine Matrix.eq_zero_of_mulVec_eq_zero hdet ?_
        funext a
        have e := congrFun hMv a.castSucc
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hvl, mul_zero, add_zero,
          Pi.zero_apply] at e
        simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Pi.zero_apply]
        exact e
      funext c
      rcases Fin.eq_castSucc_or_eq_last c with ⟨b, rfl⟩ | rfl
      · exact congrFun hv' b
      · exact hvl
    have full : ∀ (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (v : Fin (r + 1) → E),
        M *ᵥ v = 0 → v (Fin.last r) = 0 → (M.det ≠ 0 ∨ (M.submatrix Fin.castSucc Fin.castSucc).det ≠ 0) →
        v = 0 := by
      intro M v hMv hvl h
      rcases h with h | h
      · exact Matrix.eq_zero_of_mulVec_eq_zero h hMv
      · exact lead M v hMv hvl h
    have hor : Dl F F' (r + 1) ≠ 0 ∨ Dl F F' r ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply hG
      rw [hc.1, hc.2]
      ring
    apply hw_of
    · apply full _ _ hZx0 hx0
      rcases hor with h | h
      · left
        rw [Matrix.det_conjTranspose, ← hDl]
        exact fun h0 => h (star_eq_zero.1 h0)
      · right
        rw [← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose, ← hdl]
        exact fun h0 => h (star_eq_zero.1 h0)
    · apply full _ _ hZy0 hy0
      rcases hor with h | h
      · left
        rw [← hDl]
        exact h
      · right
        rw [← hdl]
        exact h

/- English proof (translation)
Unfold `GeoDec`. Introduce `y`. Use `⟨fun a => geoC (geoV F F' hj) (Sum.inl a) y, fun a => geoC (geoV F F' hj) (Sum.inr a) y, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `e` using `geo_Y_apply (geoV F F' hj) (geoW F F' hj A A') y`. Rewrite `e` using `[Fintype.sum_sum_type]`.

Conclude with `e`. Introduce `a`. Establish `e` using `geo_repr (geoV F F' hj) h (Sum.inl a) y`. Rewrite `e` using `[Fintype.sum_sum_type]`. Conclude with `e`.

Introduce `a`. Establish `e` using `geo_repr (geoV F F' hj) h (Sum.inr a) y`. Rewrite `e` using `[Fintype.sum_sum_type, add_comm]`. Conclude with `e`.
-/
theorem geo_dec (F : FlagG S r T) (F' : FlagG S r T') (hj : j ≤ r + 1) (A A' : Matrix (Fin j) (Fin j) E)
    (h : IsUnit (geoGram (geoV F F' hj)).det) :
    GeoDec F F' hj A A' (geoY (geoV F F' hj) (geoW F F' hj A A')) := by
  unfold GeoDec
  intro y
  refine ⟨fun a => geoC (geoV F F' hj) (Sum.inl a) y, fun a => geoC (geoV F F' hj) (Sum.inr a) y, ?_, ?_, ?_⟩
  · have e := geo_Y_apply (geoV F F' hj) (geoW F F' hj A A') y
    rw [Fintype.sum_sum_type] at e
    exact e
  · intro a
    have e := geo_repr (geoV F F' hj) h (Sum.inl a) y
    rw [Fintype.sum_sum_type] at e
    exact e
  · intro a
    have e := geo_repr (geoV F F' hj) h (Sum.inr a) y
    rw [Fintype.sum_sum_type, add_comm] at e
    exact e

/- English proof (translation)
Establish `hu` using `geo_gram_unit F F' hj hcase`. Use `set Y := geoY (geoV F F' hj) (geoW F F' hj A A') with hY`. Establish `H1 : Y ∈ LieU S` using `fun x y => geo_skew _ _ hu (geo_hw F F' hj A A') (geo_hsk F F' hj A A' hA hA' hR) x y`. Establish `H2 : ∀ a : Fin j, Y (F.fvec (Fin.castLE hj a)) = geoImg F hj A a` using `fun a => geo_Y_v (geoV F F' hj) (geoW F F' hj A A') hu (Sum.inl a)`. Establish `H2' : ∀ a : Fin j, Y (F'.fvec (Fin.castLE hj a)) = geoImg F' hj A' a` using `fun a => geo_Y_v (geoV F F' hj) (geoW F F' hj A A') hu (Sum.inr a)`.

Establish `hdec` using `geo_dec F F' hj A A' hu`. Establish `c1 : (j ≤ r ∧ (Matrix.of fun a c : Fin j => S.hT (F.fvec (Fin.castLE hj a)) (F'.fvec (Fin.castLE hj c))).det ≠ 0) ∨ (j = r + 1 ∧ ∀ y : S.V, (∀ a, S.hT (F.fvec a) y = 0) → S.hT y y = 0 → y ∈ F.X)`. Break down `hcase with ⟨h, hD⟩ | ⟨h, _⟩` into its components or cases. Conclude with `Or.inl ⟨h, geo_Z_det F F' hj hD⟩`. Conclude with `Or.inr ⟨h, han⟩`.

Establish `c2 : (j ≤ r ∧ (Matrix.of fun a c : Fin j => S.hT (F'.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c))).det ≠ 0) ∨ (j = r + 1 ∧ ∀ y : S.V, (∀ a, S.hT (F'.fvec a) y = 0) → S.hT y y = 0 → y ∈ F'.X)`. Break down `hcase with ⟨h, hD⟩ | ⟨h, _⟩` into its components or cases. Use `Or.inl ⟨h, ?_⟩` and prove the remaining obligations. Establish `e : (Matrix.of fun a c : Fin j => S.hT (F'.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c))) = ((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj))ᴴ`. Use extensionality with `a c`.

Use `show S.hT (F'.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c)) = star (S.hT (F.fvec _) (F'.fvec _))`. Rewrite using `[← S.herm.eq]`. Both sides reduce to the same expression. Rewrite using `[e, Matrix.det_conjTranspose]`. Conclude with `star_ne_zero.2 (geo_Z_det F F' hj hD)`.

Conclude with `Or.inr ⟨h, han'⟩`. Establish `s1` using `geo_side hj F A hA Y H1 H2 (geometric_decomposition_maps_perp_into_flag F F' hj A A' hA hA' Y hdec H1 H2 c1)`. Establish `s2` using `geo_side hj F' A' hA' Y H1 H2' (geometric_decomposition_maps_perp_into_flag F' F hj A' A hA' hA Y hdec.symm H1 H2' c2)`. Use `hrel Y ⟨s1.1, s2.1⟩` as an intermediate fact. Unfold `FlagG.dpsi at this`.

Rewrite `this` using `[s1.2, s2.2]`. Then use the resulting hypothesis.
-/
theorem geo_main (K : Type) [Field K] [Algebra K E] (F : FlagG S r T) (F' : FlagG S r T')
    (han : ∀ y : S.V, (∀ a, S.hT (F.fvec a) y = 0) → S.hT y y = 0 → y ∈ F.X)
    (han' : ∀ y : S.V, (∀ a, S.hT (F'.fvec a) y = 0) → S.hT y y = 0 → y ∈ F'.X)
    (hrel : Relevant K F F') (hj : j ≤ r + 1)
    (hcase : (j ≤ r ∧ Dl F F' j ≠ 0) ∨ (j = r + 1 ∧ Gflag F F' ≠ 0)) (A A' : Matrix (Fin j) (Fin j) E)
    (hA : StrictUp A) (hA' : StrictUp A')
    (hR : Aᴴ * (Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj) +
      (Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj) * A' = 0) :
    Algebra.trace K E (supSum A) = Algebra.trace K E (supSum A') := by
  have hu := geo_gram_unit F F' hj hcase
  set Y := geoY (geoV F F' hj) (geoW F F' hj A A') with hY
  have H1 : Y ∈ LieU S := fun x y =>
    geo_skew _ _ hu (geo_hw F F' hj A A') (geo_hsk F F' hj A A' hA hA' hR) x y
  have H2 : ∀ a : Fin j, Y (F.fvec (Fin.castLE hj a)) = geoImg F hj A a := fun a =>
    geo_Y_v (geoV F F' hj) (geoW F F' hj A A') hu (Sum.inl a)
  have H2' : ∀ a : Fin j, Y (F'.fvec (Fin.castLE hj a)) = geoImg F' hj A' a := fun a =>
    geo_Y_v (geoV F F' hj) (geoW F F' hj A A') hu (Sum.inr a)
  have hdec := geo_dec F F' hj A A' hu
  have c1 : (j ≤ r ∧ (Matrix.of fun a c : Fin j =>
        S.hT (F.fvec (Fin.castLE hj a)) (F'.fvec (Fin.castLE hj c))).det ≠ 0) ∨
      (j = r + 1 ∧ ∀ y : S.V, (∀ a, S.hT (F.fvec a) y = 0) → S.hT y y = 0 → y ∈ F.X) := by
    rcases hcase with ⟨h, hD⟩ | ⟨h, _⟩
    · exact Or.inl ⟨h, geo_Z_det F F' hj hD⟩
    · exact Or.inr ⟨h, han⟩
  have c2 : (j ≤ r ∧ (Matrix.of fun a c : Fin j =>
        S.hT (F'.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c))).det ≠ 0) ∨
      (j = r + 1 ∧ ∀ y : S.V, (∀ a, S.hT (F'.fvec a) y = 0) → S.hT y y = 0 → y ∈ F'.X) := by
    rcases hcase with ⟨h, hD⟩ | ⟨h, _⟩
    · refine Or.inl ⟨h, ?_⟩
      have e : (Matrix.of fun a c : Fin j => S.hT (F'.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c))) =
          ((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj))ᴴ := by
        ext a c
        show S.hT (F'.fvec (Fin.castLE hj a)) (F.fvec (Fin.castLE hj c)) = star (S.hT (F.fvec _) (F'.fvec _))
        rw [← S.herm.eq]; rfl
      rw [e, Matrix.det_conjTranspose]
      exact star_ne_zero.2 (geo_Z_det F F' hj hD)
    · exact Or.inr ⟨h, han'⟩
  have s1 := geo_side hj F A hA Y H1 H2 (geometric_decomposition_maps_perp_into_flag F F' hj A A' hA hA' Y hdec H1 H2 c1)
  have s2 := geo_side hj F' A' hA' Y H1 H2' (geometric_decomposition_maps_perp_into_flag F' F hj A' A hA' hA Y hdec.symm H1 H2' c2)
  have := hrel Y ⟨s1.1, s2.1⟩
  unfold FlagG.dpsi at this
  rwa [s1.2, s2.2] at this

/- English proof (translation)
Unfold `supSum`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem geo_supSum_smul {n : ℕ} (c : E) (A : Matrix (Fin n) (Fin n) E) : supSum (c • A) = c * supSum A := by
  unfold supSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> simp

/- English proof (translation)
Unfold `StrictUp at h ⊢`. Introduce `a b hab`. Simplify using `[h a b hab]`.
-/
theorem geo_strict_smul {n : ℕ} (c : E) (A : Matrix (Fin n) (Fin n) E) (h : StrictUp A) : StrictUp (c • A) := by
  unfold StrictUp at h ⊢
  intro a b hab
  simp [h a b hab]

end Main

/- English proof (translation)
Unfold `LeadingBlocksRelevant`. Introduce `K E _ _ _ _ _ S r T T' F F' htr han han' hrel j hj hcase`. Unfold `MatRel`. Introduce `A A' hA hA' hR`. Establish `key : ∀ c : E, Algebra.trace K E (c * supSum A) = Algebra.trace K E (star c * supSum A')`.

Introduce `c`. Establish `h` using `geo_main K F F' han han' hrel hj hcase (c • A) (star c • A') (geo_strict_smul c A hA) (geo_strict_smul (star c) A' hA') (by`. Rewrite using `[Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hR, smul_zero])`. Rewrite `h` using `[geo_supSum_smul, geo_supSum_smul]`. Then use the resulting hypothesis. Establish `h1` using `congrArg (algebraMap K E) (key (star (supSum A - star (supSum A'))))`.

Rewrite `h1` using `[htr, htr]`. Simplify using `only [star_mul', star_star, star_sub] at h1`. Establish `h2 : (supSum A - star (supSum A')) * (star (supSum A) - supSum A') = 0`. Take the linear combination `(1 / 2 : E) * h1`. Establish `h3 : supSum A - star (supSum A') = 0`.

Break down `mul_eq_zero.1 h2 with h | h` into its components or cases. Conclude with `h`. Establish `h4 : star (supSum A - star (supSum A')) = 0`. Rewrite using `[star_sub, star_star]`. Conclude with `h`.

Conclude with `star_eq_zero.1 h4`. Conclude with `sub_eq_zero.1 h3`.
-/
theorem cell_geom : LeadingBlocksRelevant := by
  unfold LeadingBlocksRelevant
  intro K E _ _ _ _ _ S r T T' F F' htr han han' hrel j hj hcase
  unfold MatRel
  intro A A' hA hA' hR
  have key : ∀ c : E, Algebra.trace K E (c * supSum A) = Algebra.trace K E (star c * supSum A') := by
    intro c
    have h := geo_main K F F' han han' hrel hj hcase (c • A) (star c • A') (geo_strict_smul c A hA)
      (geo_strict_smul (star c) A' hA') (by
        rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hR, smul_zero])
    rwa [geo_supSum_smul, geo_supSum_smul] at h
  have h1 := congrArg (algebraMap K E) (key (star (supSum A - star (supSum A'))))
  rw [htr, htr] at h1
  simp only [star_mul', star_star, star_sub] at h1
  have h2 : (supSum A - star (supSum A')) * (star (supSum A) - supSum A') = 0 := by
    linear_combination (1 / 2 : E) * h1
  have h3 : supSum A - star (supSum A') = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · exact h
    · have h4 : star (supSum A - star (supSum A')) = 0 := by
        rw [star_sub, star_star]
        exact h
      exact star_eq_zero.1 h4
  exact sub_eq_zero.1 h3

end Formalism.MainNotions.BridgeLemma

end
