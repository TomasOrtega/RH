import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.UnipotentFrameFixers

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.AtPt Matrix Polynomial

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.Uniq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

variable {K : Type*} [Field K]

/- English proof (translation)
Rewrite using `[adjugate_apply, det_succ_row _ (Fin.last r), Finset.sum_eq_single (Fin.last r)]`. Establish `hsub : ((M.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)).submatrix (Fin.last r).succAbove (Fin.last r).succAbove) = M.submatrix Fin.castSucc Fin.castSucc`. Use extensionality with `i j`. Simplify using `[Fin.succAbove_last, updateRow_ne (Fin.castSucc_lt_last i).ne]`. Rewrite using `[hsub]`.

Simplify using `[← two_mul, pow_mul]`. Introduce `j _ hj`. Simplify using `[Pi.single_apply, hj]`. Simplify using the standard rewrite rules.
-/
theorem adjugate_last (r : ℕ) (M : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    M.adjugate (Fin.last r) (Fin.last r) = (M.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [adjugate_apply, det_succ_row _ (Fin.last r), Finset.sum_eq_single (Fin.last r)]
  · have hsub : ((M.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)).submatrix
        (Fin.last r).succAbove (Fin.last r).succAbove) = M.submatrix Fin.castSucc Fin.castSucc := by
      ext i j
      simp [Fin.succAbove_last, updateRow_ne (Fin.castSucc_lt_last i).ne]
    rw [hsub]
    simp [← two_mul, pow_mul]
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · simp

/- English proof (translation)
Establish `h : W - single (Fin.last r) (Fin.last r) c = W.updateRow (Fin.last r) (W (Fin.last r) + (-c) • Pi.single (Fin.last r) 1)`. Use extensionality with `i j`. Distinguish the cases in `hi : i = Fin.last r`. Substitute `hi` using the available equality. Distinguish the cases in `hj : j = Fin.last r`.

Substitute `hj` using the available equality. Simplify using `[sub_eq_add_neg]`. Simplify using `[hj, single_apply, Ne.symm hj]`. Simplify using `[hi, single_apply, Ne.symm hi]`. Rewrite using `[h, det_updateRow_add, det_updateRow_smul, updateRow_eq_self, adjugate_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_sub_single (r : ℕ) (W : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (c : K) :
    (W - single (Fin.last r) (Fin.last r) c).det =
      W.det - c * W.adjugate (Fin.last r) (Fin.last r) := by
  have h : W - single (Fin.last r) (Fin.last r) c =
      W.updateRow (Fin.last r) (W (Fin.last r) + (-c) • Pi.single (Fin.last r) 1) := by
    ext i j
    by_cases hi : i = Fin.last r
    · subst hi
      by_cases hj : j = Fin.last r
      · subst hj; simp [sub_eq_add_neg]
      · simp [hj, single_apply, Ne.symm hj]
    · simp [hi, single_apply, Ne.symm hi]
  rw [h, det_updateRow_add, det_updateRow_smul, updateRow_eq_self, adjugate_apply]
  ring

/- English proof (translation)
Set `_` to `Z.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hZ)`. Rewrite using `[det_fromBlocks₁₁]`. Rewrite using `[invOf_eq_nonsing_inv, single_mul_mul_single, det_sub_single, inv_def, Ring.inverse_eq_inv']`. Simplify using `only [Matrix.smul_apply, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem det_blocks_of_ne (r : ℕ) (Z W : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (a b : K) (hZ : Z.det ≠ 0) :
    (fromBlocks Z (single (Fin.last r) (Fin.last r) a) (single (Fin.last r) (Fin.last r) b) W).det = Z.det * W.det - a * b * Z.adjugate (Fin.last r) (Fin.last r) * W.adjugate (Fin.last r) (Fin.last r) := by
  let _ := Z.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hZ)
  rw [det_fromBlocks₁₁]
  rw [invOf_eq_nonsing_inv, single_mul_mul_single, det_sub_single, inv_def, Ring.inverse_eq_inv']
  simp only [Matrix.smul_apply, smul_eq_mul]
  field_simp

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [map_apply, single_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem single_map {L M : Type*} [Ring L] [Ring M] (f : L →+* M) (r : ℕ) (c : L) :
    (single (Fin.last r) (Fin.last r) c).map f = single (Fin.last r) (Fin.last r) (f c) := by
  ext i j
  simp only [map_apply, single_apply]
  split_ifs <;> simp

/- English proof (translation)
Use `set P : Matrix (Fin (r + 1)) (Fin (r + 1)) K[X] := charmatrix (-Z) with hPdef`. Establish `hP : P.det ≠ 0` using `(charpoly_monic (-Z)).ne_zero`. Use `set φ : K[X] →+* RatFunc K := algebraMap K[X] (RatFunc K)`. Establish `hinj : Function.Injective φ` using `IsFractionRing.injective K[X] (RatFunc K)`. Establish `hPφ : (P.map φ).det ≠ 0`.

Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `(map_ne_zero_iff φ hinj).mpr hP`. Establish `key` using `det_blocks_of_ne r (P.map φ) ((W.map C).map φ) (φ (C a)) (φ (C b)) hPφ`. Establish `key2 : (fromBlocks P (single (Fin.last r) (Fin.last r) (C a)) (single (Fin.last r) (Fin.last r) (C b)) (W.map C)).det = P.det * (W.map C).det - C a * C b * P.adjugate (Fin.last r) (Fin.last r) * (W.map C).adjugate (Fin.last r) (Fin.last r)`. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, fromBlocks_map, single_map, single_map]`. Rewrite using `[key]`. Simplify using `only [map_sub, map_mul, RingHom.map_det, RingHom.mapMatrix_apply]`. Use `congr 3`. Conclude with `(congrFun (congrFun (RingHom.map_adjugate φ P) _) _).symm`.

Conclude with `(congrFun (congrFun (RingHom.map_adjugate φ (W.map C)) _) _).symm`. Use `set ψ : K[X] →+* K := Polynomial.evalRingHom 0`. Establish `hPψ : P.map ψ = Z`. Use extensionality with `i j`. Distinguish the cases in `h : i = j`.

Substitute `h` using the available equality. Simplify using `[hPdef, ψ]`. Simplify using `[hPdef, ψ, h]`. Establish `hWψ : (W.map C).map ψ = W`. Use extensionality with `i j`.

Simplify using `[ψ]`. Establish `key3` using `congrArg ψ key2`. Establish `hCa : ψ (C a) = a` using `by simp [ψ]`. Establish `hCb : ψ (C b) = b` using `by simp [ψ]`. Rewrite `key3` using `[RingHom.map_det, RingHom.mapMatrix_apply, fromBlocks_map, single_map, single_map, hPψ, hWψ, hCa, hCb]`.

Rewrite using `[key3]`. Simplify using `only [map_sub, map_mul, RingHom.map_det, RingHom.mapMatrix_apply, hPψ, hWψ]`. Establish `e1 : ψ (P.adjugate (Fin.last r) (Fin.last r)) = Z.adjugate (Fin.last r) (Fin.last r)`. Rewrite using `[← hPψ]`. Conclude with `congrFun (congrFun (RingHom.map_adjugate ψ P) _) _`.

Establish `e2 : ψ ((W.map C).adjugate (Fin.last r) (Fin.last r)) = W.adjugate (Fin.last r) (Fin.last r)`. Establish `e` using `congrFun (congrFun (RingHom.map_adjugate ψ (W.map C)) (Fin.last r)) (Fin.last r)`. Rewrite `e` using `[RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hWψ]`. Conclude with `e`. Rewrite using `[e1, e2]`.

Simplify using `[ψ]`.
-/
theorem det_blocks (r : ℕ) (Z W : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (a b : K) :
    (fromBlocks Z (single (Fin.last r) (Fin.last r) a) (single (Fin.last r) (Fin.last r) b) W).det =
      Z.det * W.det - a * b * Z.adjugate (Fin.last r) (Fin.last r) * W.adjugate (Fin.last r) (Fin.last r) := by
  set P : Matrix (Fin (r + 1)) (Fin (r + 1)) K[X] := charmatrix (-Z) with hPdef
  have hP : P.det ≠ 0 := (charpoly_monic (-Z)).ne_zero
  set φ : K[X] →+* RatFunc K := algebraMap K[X] (RatFunc K)
  have hinj : Function.Injective φ := IsFractionRing.injective K[X] (RatFunc K)
  have hPφ : (P.map φ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff φ hinj).mpr hP
  have key := det_blocks_of_ne r (P.map φ) ((W.map C).map φ) (φ (C a)) (φ (C b)) hPφ
  have key2 : (fromBlocks P (single (Fin.last r) (Fin.last r) (C a)) (single (Fin.last r) (Fin.last r) (C b))
      (W.map C)).det = P.det * (W.map C).det - C a * C b * P.adjugate (Fin.last r) (Fin.last r) *
        (W.map C).adjugate (Fin.last r) (Fin.last r) := by
    apply hinj
    rw [RingHom.map_det, RingHom.mapMatrix_apply, fromBlocks_map, single_map, single_map]
    rw [key]
    simp only [map_sub, map_mul, RingHom.map_det, RingHom.mapMatrix_apply]
    congr 3
    · exact (congrFun (congrFun (RingHom.map_adjugate φ P) _) _).symm
    · exact (congrFun (congrFun (RingHom.map_adjugate φ (W.map C)) _) _).symm
  set ψ : K[X] →+* K := Polynomial.evalRingHom 0
  have hPψ : P.map ψ = Z := by
    ext i j
    by_cases h : i = j
    · subst h; simp [hPdef, ψ]
    · simp [hPdef, ψ, h]
  have hWψ : (W.map C).map ψ = W := by
    ext i j; simp [ψ]
  have key3 := congrArg ψ key2
  have hCa : ψ (C a) = a := by simp [ψ]
  have hCb : ψ (C b) = b := by simp [ψ]
  rw [RingHom.map_det, RingHom.mapMatrix_apply, fromBlocks_map, single_map, single_map, hPψ, hWψ, hCa, hCb] at key3
  rw [key3]
  simp only [map_sub, map_mul, RingHom.map_det, RingHom.mapMatrix_apply, hPψ, hWψ]
  have e1 : ψ (P.adjugate (Fin.last r) (Fin.last r)) = Z.adjugate (Fin.last r) (Fin.last r) := by
    rw [← hPψ]; exact congrFun (congrFun (RingHom.map_adjugate ψ P) _) _
  have e2 : ψ ((W.map C).adjugate (Fin.last r) (Fin.last r)) = W.adjugate (Fin.last r) (Fin.last r) := by
    have e := congrFun (congrFun (RingHom.map_adjugate ψ (W.map C)) (Fin.last r)) (Fin.last r)
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hWψ] at e
    exact e
  rw [e1, e2]
  simp [ψ]

end Generic

/- English proof (translation)
Establish `h : (fromBlocks (0 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) (0 : Matrix (Fin n) (Fin n) K)) = fromBlocks (0 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) * …`. Rewrite using `[fromBlocks_multiply]`. Simplify using the standard rewrite rules. Rewrite using `[h, det_mul, det_fromBlocks_one₂₂, det_fromBlocks_zero₂₁]`. Simplify using `[det_neg]`.
-/
theorem det_swap {K : Type*} [Field K] (n : ℕ) :
    (fromBlocks (0 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K)
      (0 : Matrix (Fin n) (Fin n) K)).det = (-1) ^ n := by
  have h : (fromBlocks (0 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K)
      (0 : Matrix (Fin n) (Fin n) K)) =
      fromBlocks (0 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K)
          (1 : Matrix (Fin n) (Fin n) K) *
        fromBlocks (1 : Matrix (Fin n) (Fin n) K) (-1 : Matrix (Fin n) (Fin n) K) (0 : Matrix (Fin n) (Fin n) K)
          (1 : Matrix (Fin n) (Fin n) K) := by
    rw [fromBlocks_multiply]
    simp
  rw [h, det_mul, det_fromBlocks_one₂₂, det_fromBlocks_zero₂₁]
  simp [det_neg]

/- English proof (translation)
Unfold `leadMinorE`. Rewrite using `[dif_pos le_rfl]`. Use `congr 1`.
-/
theorem leadMinorE_full (D : Formalism.BasicNotions.D7) (Z : MatZ D) : leadMinorE Z (D.R.rS + 1) = Z.det := by
  unfold leadMinorE
  rw [dif_pos le_rfl]
  congr 1

/- English proof (translation)
Unfold `leadMinorE`. Rewrite using `[dif_pos (Nat.le_succ _), adjugate_last]`. Use `congr 1`.
-/
theorem leadMinorE_r (D : Formalism.BasicNotions.D7) (Z : MatZ D) :
    leadMinorE Z D.R.rS = Z.adjugate (Fin.last D.R.rS) (Fin.last D.R.rS) := by
  unfold leadMinorE
  rw [dif_pos (Nat.le_succ _), adjugate_last]
  congr 1

/- English proof (translation)
Establish `hA : ∀ c : D.host.E, (Matrix.of fun a b : Fin (D.R.rS + 1) => if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then c else 0) = single (Fin.last D.R.rS) (Fin.last D.R.rS) c`. Introduce `c`. Use extensionality with `a b`. Simplify using `only [of_apply, single_apply]`. Apply the tactic sequence `by_cases ha : a = Fin.last D.R.rS <;> by_cases hb : b = Fin.last D.R.rS <;> simp [ha, hb, eq_comm]`.

Establish `hS : Ga T T' Z * fromBlocks (0 : MatZ D) (1 : MatZ D) (1 : MatZ D) (0 : MatZ D) = fromBlocks Z (single (Fin.last D.R.rS) (Fin.last D.R.rS) (-T)) (single (Fin.last D.R.rS) (Fin.last D.R.rS) (-T')) Z.conjTranspose`. Rewrite using `[Ga, hA, hA, fromBlocks_multiply]`. Simplify using the standard rewrite rules. Establish `h` using `congrArg det hS`. Rewrite `h` using `[det_mul, det_swap, det_blocks]`.

Establish `hsq : ((-1 : D.host.E) ^ (D.R.rS + 1)) * (-1) ^ (D.R.rS + 1) = 1`. Rewrite using `[← mul_pow]`. Evaluate the numerical expressions. Establish `h2 : (Ga T T' Z).det = (-1) ^ (D.R.rS + 1) * ((Ga T T' Z).det * (-1) ^ (D.R.rS + 1))`. Rewrite using `[mul_comm ((Ga T T' Z).det), ← mul_assoc, hsq, one_mul]`.

Rewrite using `[h2, h]`. Use `congr 1`. Establish `hadj : Z.conjTranspose.adjugate (Fin.last D.R.rS) (Fin.last D.R.rS) = star (Z.adjugate (Fin.last D.R.rS) (Fin.last D.R.rS))`. Rewrite using `[adjugate_last, adjugate_last, ← det_conjTranspose, conjTranspose_submatrix]`. Rewrite using `[GZ, leadMinorE_full, leadMinorE_r, det_conjTranspose, hadj]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem detGa' (D : Formalism.BasicNotions.D7) (T T' : D.host.E) (Z : MatZ D) :
    (Ga T T' Z).det = (-1) ^ (D.R.rS + 1) * GZ T T' Z := by
  have hA : ∀ c : D.host.E, (Matrix.of fun a b : Fin (D.R.rS + 1) =>
      if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then c else 0) =
      single (Fin.last D.R.rS) (Fin.last D.R.rS) c := by
    intro c
    ext a b
    simp only [of_apply, single_apply]
    by_cases ha : a = Fin.last D.R.rS <;> by_cases hb : b = Fin.last D.R.rS <;> simp [ha, hb, eq_comm]
  have hS : Ga T T' Z * fromBlocks (0 : MatZ D) (1 : MatZ D) (1 : MatZ D) (0 : MatZ D) =
      fromBlocks Z (single (Fin.last D.R.rS) (Fin.last D.R.rS) (-T))
        (single (Fin.last D.R.rS) (Fin.last D.R.rS) (-T')) Z.conjTranspose := by
    rw [Ga, hA, hA, fromBlocks_multiply]
    simp
  have h := congrArg det hS
  rw [det_mul, det_swap, det_blocks] at h
  have hsq : ((-1 : D.host.E) ^ (D.R.rS + 1)) * (-1) ^ (D.R.rS + 1) = 1 := by
    rw [← mul_pow]; norm_num
  have h2 : (Ga T T' Z).det = (-1) ^ (D.R.rS + 1) * ((Ga T T' Z).det * (-1) ^ (D.R.rS + 1)) := by
    rw [mul_comm ((Ga T T' Z).det), ← mul_assoc, hsq, one_mul]
  rw [h2, h]
  congr 1
  have hadj : Z.conjTranspose.adjugate (Fin.last D.R.rS) (Fin.last D.R.rS) =
      star (Z.adjugate (Fin.last D.R.rS) (Fin.last D.R.rS)) := by
    rw [adjugate_last, adjugate_last, ← det_conjTranspose, conjTranspose_submatrix]
  rw [GZ, leadMinorE_full, leadMinorE_r, det_conjTranspose, hadj]
  ring

/- English proof (translation)
Take `⟨L, U, hL, hU, hc⟩` from `hZ`. Establish `key : ∀ l (hl : l ≤ D.R.rS + 1), leadMinorE Z l * epsL (D` using `D) D.R.rS l hl = Dmin w l := by`. Introduce `l hl`. Rewrite using `[← leadMinor_Sg, ← zhatOM_eq, hc, leadMinor_LMU (isLo_of_uni hL) (isUp_of_uni hU), dmin_eq']`. Establish `n1` using `norm_eq_of _ _ _ (key (D.R.rS + 1) le_rfl) (epsL_sq _ _) (star_epsL _ _)`.

Establish `n2` using `norm_eq_of _ _ _ (key D.R.rS (Nat.le_succ _)) (epsL_sq _ _) (star_epsL _ _)`. Simplify using `only [GZ, Gpt, conjF_star]`. Rewrite using `[n1, n2]`.
-/
theorem gz_atMat {D : D7} {w : Point D.host.E (D.R.rS + 1)} {Z : PairVal.MatR D} (hZ : AtMat w Z) (T T' : ℕ) :
    GZ (T : D.host.E) (T' : D.host.E) Z = Gpt T T' w := by
  obtain ⟨L, U, hL, hU, hc⟩ := hZ
  have key : ∀ l (hl : l ≤ D.R.rS + 1), leadMinorE Z l * epsL (D := D) D.R.rS l hl = Dmin w l := by
    intro l hl
    rw [← leadMinor_Sg, ← zhatOM_eq, hc, leadMinor_LMU (isLo_of_uni hL) (isUp_of_uni hU), dmin_eq']
  have n1 := norm_eq_of _ _ _ (key (D.R.rS + 1) le_rfl) (epsL_sq _ _) (star_epsL _ _)
  have n2 := norm_eq_of _ _ _ (key D.R.rS (Nat.le_succ _)) (epsL_sq _ _) (star_epsL _ _)
  simp only [GZ, Gpt, conjF_star]
  rw [n1, n2]

section Geo

variable {D : D7}

/- English proof (translation)
Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨j, rfl⟩ := hx`. Conclude with `hw j`. Consider the case `zero => simp`.

Consider the case `add a b _ _ ha hb => simp [ha, hb]`. Consider the case `smul c a _ ha => simp [ha]`.
-/
theorem mem_orth_of_span {ι : Type*} (v : ι → (VS D).V) (w : (VS D).V) (hw : ∀ j, (VS D).hT (v j) w = 0) :
    ∀ y ∈ Submodule.span D.host.E (Set.range v), (VS D).hT y w = 0 := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hw j
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | smul c a _ ha => simp [ha]

/- English proof (translation)
Simplify using `[map_sum, map_smul]`.
-/
theorem hT_sum {ι : Type*} [Fintype ι] (x : (VS D).V) (c : ι → D.host.E) (v : ι → (VS D).V) :
    (VS D).hT x (∑ i, c i • v i) = ∑ i, c i * (VS D).hT x (v i) := by
  simp [map_sum, map_smul]

/- English proof (translation)
Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun D.host.E).1 hd`. Establish `hc : (Matrix.of fun j i => (VS D).hT (v j) (v i)).mulVec c = 0`. Use function extensionality and compare the values at `j`. Use `h0 j` as an intermediate fact. Rewrite `this` using `[hT_sum]`.

Simplify using `only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]`. Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`. Use `Matrix.eq_zero_of_mulVec_eq_zero hM hc` as an intermediate fact. Simplify using `[this]`.
-/
theorem eq_zero_of_gram {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → (VS D).V)
    (hM : (Matrix.of fun j i => (VS D).hT (v j) (v i)).det ≠ 0) {d : (VS D).V}
    (hd : d ∈ Submodule.span D.host.E (Set.range v)) (h0 : ∀ j, (VS D).hT (v j) d = 0) : d = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hd
  have hc : (Matrix.of fun j i => (VS D).hT (v j) (v i)).mulVec c = 0 := by
    funext j
    have := h0 j
    rw [hT_sum] at this
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have := Matrix.eq_zero_of_mulVec_eq_zero hM hc
  simp [this]

/- English proof (translation)
Use `set M := Matrix.of fun j i => (VS D).hT (v j) (v i)`. Use `set b : ι → D.host.E := fun j => (VS D).hT (v j) x`. Use `⟨M⁻¹.mulVec b, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, hT_sum]`. Establish `hMi : M * M⁻¹ = 1` using `Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hM)`.

Establish `e : (M.mulVec (M⁻¹.mulVec b)) j = b j` using `by rw [Matrix.mulVec_mulVec, hMi, Matrix.one_mulVec]`. Rewrite using `[sub_eq_zero]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mulVec, dotProduct, M, Matrix.of_apply]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`.
-/
theorem decomp_gram {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → (VS D).V)
    (hM : (Matrix.of fun j i => (VS D).hT (v j) (v i)).det ≠ 0) (x : (VS D).V) :
    ∃ c : ι → D.host.E, ∀ j, (VS D).hT (v j) (x - ∑ i, c i • v i) = 0 := by
  set M := Matrix.of fun j i => (VS D).hT (v j) (v i)
  set b : ι → D.host.E := fun j => (VS D).hT (v j) x
  refine ⟨M⁻¹.mulVec b, fun j => ?_⟩
  rw [map_sub, hT_sum]
  have hMi : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hM)
  have e : (M.mulVec (M⁻¹.mulVec b)) j = b j := by rw [Matrix.mulVec_mulVec, hMi, Matrix.one_mulVec]
  rw [sub_eq_zero]
  calc (VS D).hT (v j) x = b j := rfl
    _ = (M.mulVec (M⁻¹.mulVec b)) j := e.symm
    _ = ∑ i, (M⁻¹.mulVec b) i * (VS D).hT (v j) (v i) := by
      simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/- English proof (translation)
Use extensionality with `x`. Take `⟨c, hc⟩` from `decomp_gram v hM x`. Use `set u := ∑ i, c i • v i`. Use `set w := x - u`. Establish `hu : a u = b u` using `by simp only [u, map_sum, map_smul, hab]`.

Establish `hwX : ∀ y ∈ X, (VS D).hT y w = 0` using `fun y hy => mem_orth_of_span v w hc y (hX hy)`. Establish `hd : a w - b w ∈ X`. Use `Submodule.sub_mem _ (haX w hwX) (hbX w hwX)` as an intermediate fact. Rewrite `this` using `[sub_sub_sub_cancel_right]`. Then use the resulting hypothesis. Establish `hM' : (Matrix.of fun j i => (VS D).hT ((a ∘ v) j) ((a ∘ v) i)).det ≠ 0`.

Simplify `hM` using `only [Function.comp_apply, ha]`. Establish `hspan : X ≤ Submodule.span D.host.E (Set.range (a ∘ v))`. Introduce `y hy`. Rewrite using `[← hafix y hy]`. Establish `: a y ∈ (Submodule.span D.host.E (Set.range v)).map (a : (VS D).V →ₗ[D.host.E] (VS D).V)` using `Submodule.mem_map_of_mem (hX hy)`.

Rewrite `this` using `[Submodule.map_span, ← Set.range_comp]`. Then use the resulting hypothesis. Establish `h0 : ∀ j, (VS D).hT ((a ∘ v) j) (a w - b w) = 0`. Introduce `j`. Simplify using `only [Function.comp_apply, map_sub]`. Rewrite using `[ha, hab j, hb, hc j, sub_self]`.

Establish `hw : a w = b w` using `sub_eq_zero.1 (eq_zero_of_gram (a ∘ v) hM' (hspan hd) h0)`. Establish `hx : x = u + w` using `by simp [w]`. Rewrite using `[hx, map_add, map_add, hu, hw]`.
-/
theorem rigid {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → (VS D).V)
    (hM : (Matrix.of fun j i => (VS D).hT (v j) (v i)).det ≠ 0) (X : Submodule D.host.E (VS D).V)
    (hX : X ≤ Submodule.span D.host.E (Set.range v)) (a b : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ha : ∀ x y, (VS D).hT (a x) (a y) = (VS D).hT x y) (hb : ∀ x y, (VS D).hT (b x) (b y) = (VS D).hT x y)
    (haX : ∀ w, (∀ x ∈ X, (VS D).hT x w = 0) → a w - w ∈ X) (hbX : ∀ w, (∀ x ∈ X, (VS D).hT x w = 0) → b w - w ∈ X)
    (hafix : ∀ x ∈ X, a x = x) (hab : ∀ j, a (v j) = b (v j)) : a = b := by
  ext x
  obtain ⟨c, hc⟩ := decomp_gram v hM x
  set u := ∑ i, c i • v i
  set w := x - u
  have hu : a u = b u := by simp only [u, map_sum, map_smul, hab]
  have hwX : ∀ y ∈ X, (VS D).hT y w = 0 := fun y hy => mem_orth_of_span v w hc y (hX hy)
  have hd : a w - b w ∈ X := by
    have := Submodule.sub_mem _ (haX w hwX) (hbX w hwX)
    rwa [sub_sub_sub_cancel_right] at this
  have hM' : (Matrix.of fun j i => (VS D).hT ((a ∘ v) j) ((a ∘ v) i)).det ≠ 0 := by
    simpa only [Function.comp_apply, ha] using hM
  have hspan : X ≤ Submodule.span D.host.E (Set.range (a ∘ v)) := by
    intro y hy
    rw [← hafix y hy]
    have : a y ∈ (Submodule.span D.host.E (Set.range v)).map (a : (VS D).V →ₗ[D.host.E] (VS D).V) :=
      Submodule.mem_map_of_mem (hX hy)
    rwa [Submodule.map_span, ← Set.range_comp] at this
  have h0 : ∀ j, (VS D).hT ((a ∘ v) j) (a w - b w) = 0 := by
    intro j
    simp only [Function.comp_apply, map_sub]
    rw [ha, hab j, hb, hc j, sub_self]
  have hw : a w = b w := sub_eq_zero.1 (eq_zero_of_gram (a ∘ v) hM' (hspan hd) h0)
  have hx : x = u + w := by simp [w]
  rw [hx, map_add, map_add, hu, hw]

end Geo

section N0

variable {D : D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

/- English proof (translation)
Simplify using `[orth, Submodule.mem_iInf]`.
-/
theorem mem_orth_iff (U : Submodule D.host.E (VS D).V) (w : (VS D).V) :
    w ∈ orth (VS D) U ↔ ∀ x ∈ U, (VS D).hT x w = 0 := by
  simp [orth, Submodule.mem_iInf]

/- English proof (translation)
Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => obtain ⟨a, rfl⟩ := hy`. Conclude with `he a`. Consider the case `zero => simp`.

Consider the case `add a b _ _ ha hb => rw [map_add, ha, hb]`. Consider the case `smul c a _ ha => rw [map_smul, ha]`.
-/
theorem fix_X {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (he : ∀ a, n (F0.e a) = F0.e a) : ∀ x ∈ F0.X, n x = x := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨a, rfl⟩ := hy; exact he a
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, ha, hb]
  | smul c a _ ha => rw [map_smul, ha]

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_subset_range _ _)`.
-/
theorem Xa_le_X (j : ℕ) : F0.Xa j ≤ F0.X := Submodule.span_mono (Set.image_subset_range _ _)

/- English proof (translation)
Introduce `x hx` and use `by rw [← hfix x hx, hiso, hw x hx]`.
-/
theorem perp_iso {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hiso : ∀ x y, (VS D).hT (n x) (n y) = (VS D).hT x y)
    (hfix : ∀ x ∈ F0.X, n x = x) (w : (VS D).V) (hw : ∀ x ∈ F0.X, (VS D).hT x w = 0) :
    ∀ x ∈ F0.X, (VS D).hT x (n w) = 0 := fun x hx => by rw [← hfix x hx, hiso, hw x hx]

/- English proof (translation)
Proceed by induction on `i using Fin.lastCases with`. Consider the case `last => simp only [FlagG.fvec, Fin.snoc_last]`. Conclude with `hz`. Consider the case `cast j => simp only [FlagG.fvec, Fin.snoc_castSucc]`. Conclude with `he j`.
-/
theorem fix_fvec {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (he : ∀ a, n (F0.e a) = F0.e a) (hz : n F0.z = F0.z)
    (i : Fin (D.R.rS + 1)) : n (F0.fvec i) = F0.fvec i := by
  induction i using Fin.lastCases with
  | last => simp only [FlagG.fvec, Fin.snoc_last]; exact hz
  | cast j => simp only [FlagG.fvec, Fin.snoc_castSucc]; exact he j

/- English proof (translation)
Proceed by induction on `i using Fin.lastCases with`. Consider the case `last => simp only [FlagG.fvec, Fin.snoc_last]`. Conclude with `h.2`. Consider the case `cast j => simp only [FlagG.fvec, Fin.snoc_castSucc]`. Conclude with `h.1 j`.
-/
theorem moves_fvec {T' : D.host.E} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} {A B : LFlag (VS D) D.R.rS T'}
    (h : Moves n A B) (i : Fin (D.R.rS + 1)) : n (A.fl.fvec i) = B.fl.fvec i := by
  induction i using Fin.lastCases with
  | last => simp only [FlagG.fvec, Fin.snoc_last]; exact h.2
  | cast j => simp only [FlagG.fvec, Fin.snoc_castSucc]; exact h.1 j

variable {F0}

/- English proof (translation)
Use `⟨⟨⟨hiso, ?_⟩, fun j x hx => ?_, fun x hx => hperp x ((mem_orth_iff _ x).1 hx)⟩, he, hz⟩` and prove the remaining obligations. Apply `SetLike.coe_injective` to reduce the goal to its premises. Rewrite using `[Formalism.HermitianLatticesTheory.gmap, Submodule.map_coe]`. Conclude with `hΛ`. Rewrite using `[fix_X F0 he x (Xa_le_X F0 _ hx), sub_self]`.

Conclude with `Submodule.zero_mem _`.
-/
theorem mem_unipotent_fixer_of {Λ : Submodule (𝓞 D.host.E) (VS D).V} {k : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hiso : ∀ x y, (VS D).hT (k x) (k y) = (VS D).hT x y) (hΛ : (k : (VS D).V → (VS D).V) '' Λ = Λ)
    (hperp : ∀ w, (∀ x ∈ F0.X, (VS D).hT x w = 0) → k w - w ∈ F0.X) (he : ∀ a, k (F0.e a) = F0.e a)
    (hz : k F0.z = F0.z) : k ∈ N0 F0 Λ := by
  refine ⟨⟨⟨hiso, ?_⟩, fun j x hx => ?_, fun x hx => hperp x ((mem_orth_iff _ x).1 hx)⟩, he, hz⟩
  · apply SetLike.coe_injective
    rw [Formalism.HermitianLatticesTheory.gmap, Submodule.map_coe]
    exact hΛ
  · rw [fix_X F0 he x (Xa_le_X F0 _ hx), sub_self]; exact Submodule.zero_mem _

/- English proof (translation)
Take `⟨⟨⟨hiso, hΛ⟩, -, hperp⟩, he, hz⟩` from `hk`. Use `⟨hiso, ?_, fun w hw => hperp w ((mem_orth_iff _ w).2 hw), he, hz⟩` and prove the remaining obligations. Use `congrArg (fun P : Submodule (𝓞 D.host.E) (VS D).V => (P : Set (VS D).V)) hΛ` as an intermediate fact. Simplify using `only [Formalism.HermitianLatticesTheory.gmap, Submodule.map_coe] at this`. Conclude with `this`.
-/
theorem unipotent_lattice_fixer_props {Λ : Submodule (𝓞 D.host.E) (VS D).V} {k : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hk : k ∈ N0 F0 Λ) :
    (∀ x y, (VS D).hT (k x) (k y) = (VS D).hT x y) ∧ (k : (VS D).V → (VS D).V) '' Λ = Λ ∧
      (∀ w, (∀ x ∈ F0.X, (VS D).hT x w = 0) → k w - w ∈ F0.X) ∧ (∀ a, k (F0.e a) = F0.e a) ∧ k F0.z = F0.z := by
  obtain ⟨⟨⟨hiso, hΛ⟩, -, hperp⟩, he, hz⟩ := hk
  refine ⟨hiso, ?_, fun w hw => hperp w ((mem_orth_iff _ w).2 hw), he, hz⟩
  have := congrArg (fun P : Submodule (𝓞 D.host.E) (VS D).V => (P : Set (VS D).V)) hΛ
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.map_coe] at this
  exact this

/- English proof (translation)
Take `⟨hiso, -, hperp, he, hz⟩` from `hk`. Conclude with `⟨hiso, fun w hw => hperp w ((mem_orth_iff _ w).2 hw), he, hz⟩`.
-/
theorem unipotent_frame_fixer_props {k : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hk : k ∈ unipotentFrameFixers F0) :
    (∀ x y, (VS D).hT (k x) (k y) = (VS D).hT x y) ∧
      (∀ w, (∀ x ∈ F0.X, (VS D).hT x w = 0) → k w - w ∈ F0.X) ∧ (∀ a, k (F0.e a) = F0.e a) ∧ k F0.z = F0.z := by
  obtain ⟨hiso, -, hperp, he, hz⟩ := hk
  exact ⟨hiso, fun w hw => hperp w ((mem_orth_iff _ w).2 hw), he, hz⟩

/- English proof (translation)
Take `⟨hiso, hΛ, hperp, he, hz⟩` from `unipotent_lattice_fixer_props hk`. Establish `hfix` using `fix_X F0 he`. Use `mem_unipotent_fixer_of (fun x y => ?_) ?_ (fun w hw => ?_) (fun a => ?_) ?_` and prove the remaining obligations. Rewrite using `[← hiso, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`. Use `conv_lhs => rw [← hΛ]`.

Rewrite using `[Set.image_image]`. Simplify using the standard rewrite rules. Establish `hy : ∀ x ∈ F0.X, (VS D).hT x (k.symm w) = 0` using `fun x hx => by`. Rewrite using `[← hiso, hfix x hx, LinearEquiv.apply_symm_apply]`. Conclude with `hw x hx`.

Use `hperp _ hy` as an intermediate fact. Rewrite `this` using `[LinearEquiv.apply_symm_apply]`. Use `Submodule.neg_mem _ this` as an intermediate fact. Rewrite `this` using `[neg_sub]`. Then use the resulting hypothesis. Conclude with `(LinearEquiv.symm_apply_eq _).2 (he a).symm`.

Conclude with `(LinearEquiv.symm_apply_eq _).2 hz.symm`.
-/
theorem unipotent_fixer_symm {Λ : Submodule (𝓞 D.host.E) (VS D).V} {k : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hk : k ∈ N0 F0 Λ) :
    k.symm ∈ N0 F0 Λ := by
  obtain ⟨hiso, hΛ, hperp, he, hz⟩ := unipotent_lattice_fixer_props hk
  have hfix := fix_X F0 he
  refine mem_unipotent_fixer_of (fun x y => ?_) ?_ (fun w hw => ?_) (fun a => ?_) ?_
  · rw [← hiso, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  · conv_lhs => rw [← hΛ]
    rw [Set.image_image]; simp
  · have hy : ∀ x ∈ F0.X, (VS D).hT x (k.symm w) = 0 := fun x hx => by
      rw [← hiso, hfix x hx, LinearEquiv.apply_symm_apply]; exact hw x hx
    have := hperp _ hy
    rw [LinearEquiv.apply_symm_apply] at this
    have := Submodule.neg_mem _ this
    rwa [neg_sub] at this
  · exact (LinearEquiv.symm_apply_eq _).2 (he a).symm
  · exact (LinearEquiv.symm_apply_eq _).2 hz.symm

/- English proof (translation)
Take `⟨hiso, hΛ, hperp, he, hz⟩` from `unipotent_lattice_fixer_props hk`. Take `⟨hiso', hΛ', hperp', he', hz'⟩` from `unipotent_lattice_fixer_props hl`. Use `mem_unipotent_fixer_of (fun x y => ?_) ?_ (fun w hw => ?_) (fun a => ?_) ?_` and prove the remaining obligations. Simplify using `only [LinearEquiv.trans_apply, hiso', hiso]`. Rewrite using `[show ⇑(k.trans l) = ⇑l ∘ ⇑k from rfl, Set.image_comp, hΛ, hΛ']`.

Simplify using `only [LinearEquiv.trans_apply]`. Establish `h1` using `hperp' (k w) (perp_iso F0 hiso (fix_X F0 he) w hw)`. Establish `h2` using `hperp w hw`. Use `Submodule.add_mem _ h1 h2` as an intermediate fact. Rewrite `this` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis.

Simplify using `only [LinearEquiv.trans_apply, he, he']`. Simplify using `only [LinearEquiv.trans_apply, hz, hz']`.
-/
theorem unipotent_fixer_trans {Λ : Submodule (𝓞 D.host.E) (VS D).V} {k l : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hk : k ∈ N0 F0 Λ)
    (hl : l ∈ N0 F0 Λ) : k.trans l ∈ N0 F0 Λ := by
  obtain ⟨hiso, hΛ, hperp, he, hz⟩ := unipotent_lattice_fixer_props hk
  obtain ⟨hiso', hΛ', hperp', he', hz'⟩ := unipotent_lattice_fixer_props hl
  refine mem_unipotent_fixer_of (fun x y => ?_) ?_ (fun w hw => ?_) (fun a => ?_) ?_
  · simp only [LinearEquiv.trans_apply, hiso', hiso]
  · rw [show ⇑(k.trans l) = ⇑l ∘ ⇑k from rfl, Set.image_comp, hΛ, hΛ']
  · simp only [LinearEquiv.trans_apply]
    have h1 := hperp' (k w) (perp_iso F0 hiso (fix_X F0 he) w hw)
    have h2 := hperp w hw
    have := Submodule.add_mem _ h1 h2
    rwa [sub_add_sub_cancel] at this
  · simp only [LinearEquiv.trans_apply, he, he']
  · simp only [LinearEquiv.trans_apply, hz, hz']

/- English proof (translation)
The claim follows from `mem_unipotent_fixer_of (fun _ _ => rfl) (by rw [show ⇑(LinearEquiv.refl D.host.E (VS D).V) = id from rfl, Set.image_id]) (fun w _ => by rw [LinearEquiv.refl_apply, sub_self]; exact Submodule.zero_mem _) (fun _ => rfl) rfl`.
-/
theorem unipotent_fixer_refl (Λ : Submodule (𝓞 D.host.E) (VS D).V) : LinearEquiv.refl D.host.E (VS D).V ∈ N0 F0 Λ :=
  mem_unipotent_fixer_of (fun _ _ => rfl) (by rw [show ⇑(LinearEquiv.refl D.host.E (VS D).V) = id from rfl, Set.image_id])
    (fun w _ => by rw [LinearEquiv.refl_apply, sub_self]; exact Submodule.zero_mem _) (fun _ => rfl) rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, unipotent_fixer_refl Λ, fun _ => rfl, rfl⟩`.
-/
theorem nilradical_relation_refl {T' : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V) (A : LFlag (VS D) D.R.rS T') :
    NilradicalFlagMoved F0 Λ A A := ⟨_, unipotent_fixer_refl Λ, fun _ => rfl, rfl⟩

/- English proof (translation)
Take `⟨k, hk, he, hz⟩` from `h`. Conclude with `⟨k.symm, unipotent_fixer_symm hk, fun a => (LinearEquiv.symm_apply_eq _).2 (he a).symm, (LinearEquiv.symm_apply_eq _).2 hz.symm⟩`.
-/
theorem lattice_flag_relation_symm {T' : D.host.E} {Λ : Submodule (𝓞 D.host.E) (VS D).V} {A B : LFlag (VS D) D.R.rS T'}
    (h : NilradicalFlagMoved F0 Λ A B) : NilradicalFlagMoved F0 Λ B A := by
  obtain ⟨k, hk, he, hz⟩ := h
  exact ⟨k.symm, unipotent_fixer_symm hk, fun a => (LinearEquiv.symm_apply_eq _).2 (he a).symm,
    (LinearEquiv.symm_apply_eq _).2 hz.symm⟩

/- English proof (translation)
Take `⟨k, hk, he, hz⟩` from `h1`. Take `⟨l, hl, he', hz'⟩` from `h2`. Conclude with `⟨k.trans l, unipotent_fixer_trans hk hl, fun a => by simp [he, he'], by simp [hz, hz']⟩`.
-/
theorem lattice_flag_relation_trans {T' : D.host.E} {Λ : Submodule (𝓞 D.host.E) (VS D).V} {A B C : LFlag (VS D) D.R.rS T'}
    (h1 : NilradicalFlagMoved F0 Λ A B) (h2 : NilradicalFlagMoved F0 Λ B C) : NilradicalFlagMoved F0 Λ A C := by
  obtain ⟨k, hk, he, hz⟩ := h1
  obtain ⟨l, hl, he', hz'⟩ := h2
  exact ⟨k.trans l, unipotent_fixer_trans hk hl, fun a => by simp [he, he'], by simp [hz, hz']⟩

end N0

section Main

variable {D : D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂) in

/- English proof (translation)
Introduce `γ Z hCtx F'₂ φ φ' hS F' F'' Λ₂ Λ₃ hP' hP'' hR2 hR3`. Take `⟨n, hn, hmn, hnΛ⟩` from `hR2`. Take `⟨m, hm, hmm, hmΛ⟩` from `hR3`. Take `⟨hiso_n, hperp_n, he_n, hz_n⟩` from `unipotent_frame_fixer_props hn`. Take `⟨hiso_m, hperp_m, he_m, hz_m⟩` from `unipotent_frame_fixer_props hm`.

Prove the components needed by the constructor for the conclusion. Introduce `hΛ`. Substitute `hΛ` using the available equality. Use `set k := n.symm.trans m`. Establish `hk : k ∈ N0 F0 γ.lam`.

Use `mem_unipotent_fixer_of (fun x y => ?_) ?_ (fun w hw => ?_) (fun a => ?_) ?_` and prove the remaining obligations. Simplify using `only [k, LinearEquiv.trans_apply, hiso_m]`. Rewrite using `[← hiso_n, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`. Establish `h1 : (n.symm : (VS D).V → (VS D).V) '' γ.lam = Λ₂`. Rewrite using `[← hnΛ, Set.image_image]`.

Simplify using the standard rewrite rules. Rewrite using `[show ⇑k = ⇑m ∘ ⇑n.symm from rfl, Set.image_comp, h1, hmΛ]`. Establish `hy : ∀ x ∈ F0.X, (VS D).hT x (n.symm w) = 0` using `fun x hx => by`. Rewrite using `[← hiso_n, fix_X F0 he_n x hx, LinearEquiv.apply_symm_apply]`. Conclude with `hw x hx`.

Establish `h1` using `hperp_m _ hy`. Establish `h2` using `hperp_n _ hy`. Rewrite `h2` using `[LinearEquiv.apply_symm_apply]`. Use `Submodule.sub_mem _ h1 h2` as an intermediate fact. Simplify using `only [k, LinearEquiv.trans_apply]`.

Rewrite `this` using `[sub_sub_sub_cancel_right]`. Then use the resulting hypothesis. Simplify using `only [k, LinearEquiv.trans_apply]`. Rewrite using `[(LinearEquiv.symm_apply_eq _).2 (he_n a).symm, he_m]`. Simplify using `only [k, LinearEquiv.trans_apply]`. Rewrite using `[(LinearEquiv.symm_apply_eq _).2 hz_n.symm, hz_m]`.

Establish `hrel : NilradicalFlagMoved F0 γ.lam F' F''`. Use `⟨k, hk, fun a => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [k, LinearEquiv.trans_apply]`. Rewrite using `[(LinearEquiv.symm_apply_eq _).2 (hmn.1 a).symm, hmm.1 a]`. Simplify using `only [k, LinearEquiv.trans_apply]`.

Rewrite using `[(LinearEquiv.symm_apply_eq _).2 hmn.2.symm, hmm.2]`. Use extensionality with `F'''`. Simplify using `only [cls, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hE, hr⟩`.

Conclude with `⟨hE, lattice_flag_relation_trans (lattice_flag_relation_symm hrel) hr⟩`. Introduce and unpack `⟨hE, hr⟩`. Conclude with `⟨hE, lattice_flag_relation_trans hrel hr⟩`. Introduce `hcls`. Establish `hmem : F'' ∈ cls γ Z F''` using `⟨hP''.1, nilradical_relation_refl γ.lam F''⟩`.

Rewrite `hmem` using `[← hcls]`. Take `⟨-, k, hk, hke, hkz⟩` from `hmem`. Take `⟨hiso_k, hΛk, hperp_k, he_k, hz_k⟩` from `unipotent_lattice_fixer_props hk`. Take `⟨w, -, w', hG', -, hZ⟩` from `hCtx`. Use `set v : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (VS D).V := Sum.elim F0.fvec F'₂.fl.fvec`.

Establish `hGa : (Matrix.of fun j i => (VS D).hT (v j) (v i)) = Ga (CntLocal.Tn u) ((Tu D u' : ℕ) : D.host.E) (Formalism.MainNotions.S.Zhat F0 F'₂.fl)`. Use extensionality with `j i`. Rewrite using `[ga_gram]`. Both sides reduce to the same expression. Establish `hGZ : GZ (CntLocal.Tn u) ((Tu D u' : ℕ) : D.host.E) Z ≠ 0`.

Use `gz_atMat hZ (D.mem u).A.T (D.mem u').A.T` as an intermediate fact. Introduce `h0`. Apply `hG'` to reduce the goal to its premises. Rewrite using `[← this]`. Conclude with `h0`.

Establish `hM : (Matrix.of fun j i => (VS D).hT (v j) (v i)).det ≠ 0`. Rewrite using `[hGa, detGa']`. Use `mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) ?_` and prove the remaining obligations. Establish `hZ' : Formalism.MainNotions.S.Zhat F0 F'₂.fl = Z` using `hS.1`. Rewrite using `[hZ']`.

Conclude with `hGZ`. Establish `hX : F0.X ≤ Submodule.span D.host.E (Set.range v)`. Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨a, rfl⟩`. Use `⟨Sum.inl a.castSucc, ?_⟩` and prove the remaining obligations.

Simplify using `[v, FlagG.fvec]`. Establish `heq : n.trans k = m`. Use `rigid v hM F0.X hX (n.trans k) m (fun x y => ?_) hiso_m (fun w hw => ?_) hperp_m (fun x hx => ?_) (fun j => ?_)` and prove the remaining obligations. Simplify using `only [LinearEquiv.trans_apply, hiso_k, hiso_n]`. Simplify using `only [LinearEquiv.trans_apply]`.

Establish `h1` using `hperp_k (n w) (perp_iso F0 hiso_n (fix_X F0 he_n) w hw)`. Establish `h2` using `hperp_n w hw`. Use `Submodule.add_mem _ h1 h2` as an intermediate fact. Rewrite `this` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis. Simplify using `only [LinearEquiv.trans_apply, fix_X F0 he_n x hx, fix_X F0 he_k x hx]`.

Break down `j with i | i` into its components or cases. Simplify using `only [v, Sum.elim_inl, LinearEquiv.trans_apply, fix_fvec F0 he_n hz_n, fix_fvec F0 he_k hz_k, fix_fvec F0 he_m hz_m]`. Simplify using `only [v, Sum.elim_inr, LinearEquiv.trans_apply, moves_fvec hmn, moves_fvec hmm]`. Conclude with `moves_fvec (n := k) ⟨hke, hkz⟩ i`. Establish `h2 : (m : (VS D).V → (VS D).V) '' Λ₂ = γ.lam`.

Rewrite using `[← heq, show ⇑(n.trans k) = ⇑k ∘ ⇑n from rfl, Set.image_comp, hnΛ, hΛk]`. Apply `SetLike.coe_injective` to reduce the goal to its premises. Conclude with `Set.image_injective.2 m.injective (h2.trans hmΛ.symm)`.
-/
theorem uniqC_holds : UniqC Zd u u' F0 what₂ := by
  intro γ Z hCtx F'₂ φ φ' hS F' F'' Λ₂ Λ₃ hP' hP'' hR2 hR3
  obtain ⟨n, hn, hmn, hnΛ⟩ := hR2
  obtain ⟨m, hm, hmm, hmΛ⟩ := hR3
  obtain ⟨hiso_n, hperp_n, he_n, hz_n⟩ := unipotent_frame_fixer_props hn
  obtain ⟨hiso_m, hperp_m, he_m, hz_m⟩ := unipotent_frame_fixer_props hm
  constructor
  ·
    intro hΛ
    subst hΛ
    set k := n.symm.trans m
    have hk : k ∈ N0 F0 γ.lam := by
      refine mem_unipotent_fixer_of (fun x y => ?_) ?_ (fun w hw => ?_) (fun a => ?_) ?_
      · simp only [k, LinearEquiv.trans_apply, hiso_m]
        rw [← hiso_n, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      · have h1 : (n.symm : (VS D).V → (VS D).V) '' γ.lam = Λ₂ := by
          rw [← hnΛ, Set.image_image]; simp
        rw [show ⇑k = ⇑m ∘ ⇑n.symm from rfl, Set.image_comp, h1, hmΛ]
      · have hy : ∀ x ∈ F0.X, (VS D).hT x (n.symm w) = 0 := fun x hx => by
          rw [← hiso_n, fix_X F0 he_n x hx, LinearEquiv.apply_symm_apply]; exact hw x hx
        have h1 := hperp_m _ hy
        have h2 := hperp_n _ hy
        rw [LinearEquiv.apply_symm_apply] at h2
        have := Submodule.sub_mem _ h1 h2
        simp only [k, LinearEquiv.trans_apply]
        rwa [sub_sub_sub_cancel_right] at this
      · simp only [k, LinearEquiv.trans_apply]
        rw [(LinearEquiv.symm_apply_eq _).2 (he_n a).symm, he_m]
      · simp only [k, LinearEquiv.trans_apply]
        rw [(LinearEquiv.symm_apply_eq _).2 hz_n.symm, hz_m]
    have hrel : NilradicalFlagMoved F0 γ.lam F' F'' := by
      refine ⟨k, hk, fun a => ?_, ?_⟩
      · simp only [k, LinearEquiv.trans_apply]
        rw [(LinearEquiv.symm_apply_eq _).2 (hmn.1 a).symm, hmm.1 a]
      · simp only [k, LinearEquiv.trans_apply]
        rw [(LinearEquiv.symm_apply_eq _).2 hmn.2.symm, hmm.2]
    ext F'''
    simp only [cls, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hE, hr⟩; exact ⟨hE, lattice_flag_relation_trans (lattice_flag_relation_symm hrel) hr⟩
    · rintro ⟨hE, hr⟩; exact ⟨hE, lattice_flag_relation_trans hrel hr⟩
  ·
    intro hcls
    have hmem : F'' ∈ cls γ Z F'' := ⟨hP''.1, nilradical_relation_refl γ.lam F''⟩
    rw [← hcls] at hmem
    obtain ⟨-, k, hk, hke, hkz⟩ := hmem
    obtain ⟨hiso_k, hΛk, hperp_k, he_k, hz_k⟩ := unipotent_lattice_fixer_props hk

    obtain ⟨w, -, w', hG', -, hZ⟩ := hCtx
    set v : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (VS D).V := Sum.elim F0.fvec F'₂.fl.fvec
    have hGa : (Matrix.of fun j i => (VS D).hT (v j) (v i)) =
        Ga (CntLocal.Tn u) ((Tu D u' : ℕ) : D.host.E) (Formalism.MainNotions.S.Zhat F0 F'₂.fl) := by
      ext j i
      rw [ga_gram]
      rfl
    have hGZ : GZ (CntLocal.Tn u) ((Tu D u' : ℕ) : D.host.E) Z ≠ 0 := by
      have := gz_atMat hZ (D.mem u).A.T (D.mem u').A.T
      intro h0
      apply hG'
      rw [← this]
      exact h0
    have hM : (Matrix.of fun j i => (VS D).hT (v j) (v i)).det ≠ 0 := by
      rw [hGa, detGa']
      refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) ?_
      have hZ' : Formalism.MainNotions.S.Zhat F0 F'₂.fl = Z := hS.1
      rw [hZ']
      exact hGZ
    have hX : F0.X ≤ Submodule.span D.host.E (Set.range v) := by
      apply Submodule.span_mono
      rintro _ ⟨a, rfl⟩
      refine ⟨Sum.inl a.castSucc, ?_⟩
      simp [v, FlagG.fvec]
    have heq : n.trans k = m := by
      refine rigid v hM F0.X hX (n.trans k) m (fun x y => ?_) hiso_m (fun w hw => ?_) hperp_m
        (fun x hx => ?_) (fun j => ?_)
      · simp only [LinearEquiv.trans_apply, hiso_k, hiso_n]
      · simp only [LinearEquiv.trans_apply]
        have h1 := hperp_k (n w) (perp_iso F0 hiso_n (fix_X F0 he_n) w hw)
        have h2 := hperp_n w hw
        have := Submodule.add_mem _ h1 h2
        rwa [sub_add_sub_cancel] at this
      · simp only [LinearEquiv.trans_apply, fix_X F0 he_n x hx, fix_X F0 he_k x hx]
      · rcases j with i | i
        · simp only [v, Sum.elim_inl, LinearEquiv.trans_apply, fix_fvec F0 he_n hz_n, fix_fvec F0 he_k hz_k,
            fix_fvec F0 he_m hz_m]
        · simp only [v, Sum.elim_inr, LinearEquiv.trans_apply, moves_fvec hmn, moves_fvec hmm]
          exact moves_fvec (n := k) ⟨hke, hkz⟩ i
    have h2 : (m : (VS D).V → (VS D).V) '' Λ₂ = γ.lam := by
      rw [← heq, show ⇑(n.trans k) = ⇑k ∘ ⇑n from rfl, Set.image_comp, hnΛ, hΛk]
    apply SetLike.coe_injective
    exact Set.image_injective.2 m.injective (h2.trans hmΛ.symm)

end Main

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.Uniq
