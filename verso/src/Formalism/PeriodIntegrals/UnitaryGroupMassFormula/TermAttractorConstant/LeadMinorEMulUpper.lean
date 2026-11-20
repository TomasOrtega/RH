import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RelativeEquivalence.DCRelEquivAllHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUpUniMulAlt

noncomputable section

open scoped Classical

namespace PI.TermAttrConst.UnitaryGroupMassFormula

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.DCRelEquiv PI.DCRelEquiv.UnitaryGroupMassFormula

section Mat

variable {K : Type*} [CommRing K]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply]`. Set `e : Fin l ↪ Fin N` to `⟨Fin.castLE h, Fin.castLE_injective h⟩`. Establish `hs : ∑ k : Fin l, A (Fin.castLE h i) (Fin.castLE h k) * Z (Fin.castLE h k) (Fin.castLE h j) = ∑ k ∈ Finset.univ.map e, A (Fin.castLE h i) k * Z k (Fin.castLE h j)`. Rewrite using `[Finset.sum_map]`.

Both sides reduce to the same expression. Rewrite using `[hs]`. Use `symm`. Apply `Finset.sum_subset (Finset.subset_univ _)` to reduce the goal to its premises. Introduce `k _ hk`.

Establish `hkl : l ≤ k.val`. Assume the negation of the conclusion as `hc`. Conclude with `hk (Finset.mem_map.2 ⟨⟨k.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)`. Rewrite using `[hA _ _ (by rw [Fin.lt_def]; simp; omega), zero_mul]`.
-/
theorem sub_mul_lower {N l : ℕ} (h : l ≤ N) (A Z : Matrix (Fin N) (Fin N) K)
    (hA : ∀ a c : Fin N, a < c → A a c = 0) :
    (A * Z).submatrix (Fin.castLE h) (Fin.castLE h) =
      A.submatrix (Fin.castLE h) (Fin.castLE h) * Z.submatrix (Fin.castLE h) (Fin.castLE h) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  let e : Fin l ↪ Fin N := ⟨Fin.castLE h, Fin.castLE_injective h⟩
  have hs : ∑ k : Fin l, A (Fin.castLE h i) (Fin.castLE h k) * Z (Fin.castLE h k) (Fin.castLE h j) =
      ∑ k ∈ Finset.univ.map e, A (Fin.castLE h i) k * Z k (Fin.castLE h j) := by
    rw [Finset.sum_map]; rfl
  rw [hs]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k _ hk
  have hkl : l ≤ k.val := by
    by_contra hc
    exact hk (Finset.mem_map.2 ⟨⟨k.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
  rw [hA _ _ (by rw [Fin.lt_def]; simp; omega), zero_mul]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply]`. Set `e : Fin l ↪ Fin N` to `⟨Fin.castLE h, Fin.castLE_injective h⟩`. Establish `hs : ∑ k : Fin l, Z (Fin.castLE h i) (Fin.castLE h k) * B (Fin.castLE h k) (Fin.castLE h j) = ∑ k ∈ Finset.univ.map e, Z (Fin.castLE h i) k * B k (Fin.castLE h j)`. Rewrite using `[Finset.sum_map]`.

Both sides reduce to the same expression. Rewrite using `[hs]`. Use `symm`. Apply `Finset.sum_subset (Finset.subset_univ _)` to reduce the goal to its premises. Introduce `k _ hk`.

Establish `hkl : l ≤ k.val`. Assume the negation of the conclusion as `hc`. Conclude with `hk (Finset.mem_map.2 ⟨⟨k.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)`. Rewrite using `[hB _ _ (by rw [Fin.lt_def]; simp; omega), mul_zero]`.
-/
theorem sub_mul_upper {N l : ℕ} (h : l ≤ N) (Z B : Matrix (Fin N) (Fin N) K)
    (hB : ∀ c b : Fin N, b < c → B c b = 0) :
    (Z * B).submatrix (Fin.castLE h) (Fin.castLE h) =
      Z.submatrix (Fin.castLE h) (Fin.castLE h) * B.submatrix (Fin.castLE h) (Fin.castLE h) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  let e : Fin l ↪ Fin N := ⟨Fin.castLE h, Fin.castLE_injective h⟩
  have hs : ∑ k : Fin l, Z (Fin.castLE h i) (Fin.castLE h k) * B (Fin.castLE h k) (Fin.castLE h j) =
      ∑ k ∈ Finset.univ.map e, Z (Fin.castLE h i) k * B k (Fin.castLE h j) := by
    rw [Finset.sum_map]; rfl
  rw [hs]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k _ hk
  have hkl : l ≤ k.val := by
    by_contra hc
    exact hk (Finset.mem_map.2 ⟨⟨k.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
  rw [hB _ _ (by rw [Fin.lt_def]; simp; omega), mul_zero]

/- English proof (translation)
Rewrite using `[Matrix.det_of_isLowerTriangular A (fun i j hij => hA i j (OrderDual.toDual_lt_toDual.1 hij))]`. Simplify using `[hd]`.
-/
theorem det_lower_one {N : ℕ} (A : Matrix (Fin N) (Fin N) K)
    (hA : ∀ a c : Fin N, a < c → A a c = 0) (hd : ∀ a, A a a = 1) : A.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular A (fun i j hij => hA i j (OrderDual.toDual_lt_toDual.1 hij))]
  simp [hd]

/- English proof (translation)
Rewrite using `[Matrix.det_of_isUpperTriangular (M := B) (fun i j hij => hB i j hij)]`. Simplify using `[hd]`.
-/
theorem det_upper_one {N : ℕ} (B : Matrix (Fin N) (Fin N) K)
    (hB : ∀ c b : Fin N, b < c → B c b = 0) (hd : ∀ a, B a a = 1) : B.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (M := B) (fun i j hij => hB i j hij)]
  simp [hd]

/- English proof (translation)
Introduce `i j`. Use `⟨fun hij => ?_, fun hij => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Break down `lt_or_ge i k with hik | hki` into its components or cases.

Rewrite using `[(hA i k).1 hik, zero_mul]`. Rewrite using `[(hL k j).1 (lt_of_le_of_lt hki hij), mul_zero]`. Substitute `hij` using the available equality. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single i]`. Rewrite using `[(hA i i).2 rfl, (hL i i).2 rfl, one_mul]`.

Introduce `k _ hk`. Break down `lt_or_gt_of_ne hk with hki | hik` into its components or cases. Rewrite using `[(hL k i).1 hki, mul_zero]`. Rewrite using `[(hA i k).1 hik, zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem isLoUni_mul {N : ℕ} {A L : Matrix (Fin N) (Fin N) K} (hA : IsLoUni A) (hL : IsLoUni L) :
    IsLoUni (A * L) := by
  intro i j
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge i k with hik | hki
    · rw [(hA i k).1 hik, zero_mul]
    · rw [(hL k j).1 (lt_of_le_of_lt hki hij), mul_zero]
  · subst hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [(hA i i).2 rfl, (hL i i).2 rfl, one_mul]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hki | hik
      · rw [(hL k i).1 hki, mul_zero]
      · rw [(hA i k).1 hik, zero_mul]
    · simp

/- English proof (translation)
Apply the tactic sequence `first | exact GlobalTheory.UpperUnipotentProductInertiaEigenvalues.isUpUni_mul .. | (apply GlobalTheory.UpperUnipotentProductInertiaEigenvalues.isUpUni_mul <;> assumption) | (intros; apply GlobalTheory.UpperUnipotentProductInertiaEigenvalues.isUpUni_mul <;> assumption) | (apply @ …`.
-/
theorem isUpUni_mul {N : ℕ} {U B : Matrix (Fin N) (Fin N) K} (hU : IsUpUni U) (hB : IsUpUni B) :
    IsUpUni (U * B) := by
  first | exact GlobalTheory.UpperUnipotentProductInertiaEigenvalues.isUpUni_mul .. | (apply GlobalTheory.UpperUnipotentProductInertiaEigenvalues.isUpUni_mul <;> assumption) | (intros; apply GlobalTheory.UpperUnipotentProductInertiaEigenvalues.isUpUni_mul <;> assumption) | (apply @GlobalTheory.UpperUnipotentProductInertiaEigenvalues.isUpUni_mul <;> assumption) | (intros; apply @GlobalTheory.UpperUnipotentProductInertiaEigenvalues.isUpUni_mul <;> assumption) | (apply @GlobalTheory.UpperUnipotentProductInertiaEigenvalues.isUpUni_mul <;> first | assumption | infer_instance) | exact @GlobalTheory.UpperUnipotentProductInertiaEigenvalues.isUpUni_mul K ‹_› N U B hU hB | exact @GlobalTheory.UpperUnipotentProductInertiaEigenvalues.isUpUni_mul K ‹_› N U B hU | exact @GlobalTheory.UpperUnipotentProductInertiaEigenvalues.isUpUni_mul K ‹_› N U B | exact @GlobalTheory.UpperUnipotentProductInertiaEigenvalues.isUpUni_mul K ‹_› N U | exact @GlobalTheory.UpperUnipotentProductInertiaEigenvalues.isUpUni_mul K ‹_› N | exact @GlobalTheory.UpperUnipotentProductInertiaEigenvalues.isUpUni_mul K ‹_› | exact @GlobalTheory.UpperUnipotentProductInertiaEigenvalues.isUpUni_mul K

end Mat

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

/- English proof (translation)
Unfold `leadMinorE`. Use `split_ifs with h`. Rewrite using `[sub_mul_lower h A Z (fun a c hac => (hA a c).1 hac), Matrix.det_mul, det_lower_one (A.submatrix (Fin.castLE h) (Fin.castLE h)) (fun a c hac => (hA _ _).1 hac) (fun a => (hA _ _).2 rfl), one_mul]`. Both sides reduce to the same expression.
-/
theorem leadMinorE_lower_mul {N : ℕ} (A Z : Matrix (Fin N) (Fin N) E) (hA : IsLoUni A) (l : ℕ) :
    leadMinorE (A * Z) l = leadMinorE Z l := by
  unfold leadMinorE
  split_ifs with h
  · rw [sub_mul_lower h A Z (fun a c hac => (hA a c).1 hac), Matrix.det_mul,
      det_lower_one (A.submatrix (Fin.castLE h) (Fin.castLE h)) (fun a c hac => (hA _ _).1 hac)
        (fun a => (hA _ _).2 rfl), one_mul]
  · rfl

/- English proof (translation)
Unfold `leadMinorE`. Use `split_ifs with h`. Rewrite using `[sub_mul_upper h Z B (fun c b hbc => (hB c b).1 hbc), Matrix.det_mul, det_upper_one (B.submatrix (Fin.castLE h) (Fin.castLE h)) (fun c b hbc => (hB _ _).1 hbc) (fun a => (hB _ _).2 rfl), mul_one]`. Both sides reduce to the same expression.
-/
theorem leadMinorE_mul_upper {N : ℕ} (Z B : Matrix (Fin N) (Fin N) E) (hB : IsUpUni B) (l : ℕ) :
    leadMinorE (Z * B) l = leadMinorE Z l := by
  unfold leadMinorE
  split_ifs with h
  · rw [sub_mul_upper h Z B (fun c b hbc => (hB c b).1 hbc), Matrix.det_mul,
      det_upper_one (B.submatrix (Fin.castLE h) (Fin.castLE h)) (fun c b hbc => (hB _ _).1 hbc)
        (fun a => (hB _ _).2 rfl), mul_one]
  · rfl

/- English proof (translation)
Rewrite `hv` using `[Finsupp.mem_span_image_iff_linearCombination]`. Take `⟨l, hl, rfl⟩` from `hv`. Use `⟨l, fun d hd => ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `: d ∈ (l.support : Set (Fin N))` using `by simpa using hne`.

Conclude with `hd ((Finsupp.mem_supported E l).1 hl this)`. Rewrite using `[Finsupp.linearCombination_apply, Finsupp.sum_fintype]`. Introduce `i`. Simplify using the standard rewrite rules.
-/
theorem exists_coeffs {N : ℕ} (f : Fin N → S.V) (a : Fin N) (v : S.V)
    (hv : v ∈ Submodule.span E (f '' {c | c < a})) :
    ∃ c : Fin N → E, (∀ d, ¬ d < a → c d = 0) ∧ ∑ d, c d • f d = v := by
  rw [Finsupp.mem_span_image_iff_linearCombination] at hv
  obtain ⟨l, hl, rfl⟩ := hv
  refine ⟨l, fun d hd => ?_, ?_⟩
  · by_contra hne
    have : d ∈ (l.support : Set (Fin N)) := by simpa using hne
    exact hd ((Finsupp.mem_supported E l).1 hl this)
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; simp

/- English proof (translation)
Use `choose c hc0 hcs using fun a => exists_coeffs f a _ (h a)`. Use `⟨Matrix.of fun a d => (if a = d then (1 : E) else 0) + star (c a d), ?_, ?_⟩` and prove the remaining obligations. Introduce `i j`. Use `⟨fun hij => ?_, fun hij => ?_⟩` and prove the remaining obligations. Simplify using `[ne_of_lt hij, hc0 i j (lt_asymm hij)]`.

Substitute `hij` using the available equality. Simplify using `[hc0 i i (lt_irrefl i)]`. Use extensionality with `a b`. Establish `hg : g a = f a + ∑ d, c a d • f d` using `by rw [hcs a]; abel`. Establish `key : S.hT (g a) (w b) = S.hT (f a) (w b) + ∑ d, star (c a d) * S.hT (f d) (w b)`.

Rewrite using `[hg, map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply]`. Use `congr 1`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]`. Rewrite using `[Matrix.mul_apply]`.

Simplify using `only [Matrix.of_apply, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Conclude with `key`.
-/
theorem gram_first {N : ℕ} (f g w : Fin N → S.V)
    (h : ∀ a, g a - f a ∈ Submodule.span E (f '' {c | c < a})) :
    ∃ A : Matrix (Fin N) (Fin N) E, IsLoUni A ∧
      (Matrix.of fun a b => S.hT (g a) (w b)) = A * Matrix.of fun a b => S.hT (f a) (w b) := by
  choose c hc0 hcs using fun a => exists_coeffs f a _ (h a)
  refine ⟨Matrix.of fun a d => (if a = d then (1 : E) else 0) + star (c a d), ?_, ?_⟩
  · intro i j
    refine ⟨fun hij => ?_, fun hij => ?_⟩
    · simp [ne_of_lt hij, hc0 i j (lt_asymm hij)]
    · subst hij; simp [hc0 i i (lt_irrefl i)]
  · ext a b
    have hg : g a = f a + ∑ d, c a d • f d := by rw [hcs a]; abel
    have key : S.hT (g a) (w b) = S.hT (f a) (w b) + ∑ d, star (c a d) * S.hT (f d) (w b) := by
      rw [hg, map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply]
      congr 1
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact key

/- English proof (translation)
Use `choose c hc0 hcs using fun b => exists_coeffs w b _ (h b)`. Use `⟨Matrix.of fun d b => (if d = b then (1 : E) else 0) + c b d, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j`. Use `⟨fun hji => ?_, fun hij => ?_⟩` and prove the remaining obligations. Simplify using `[ne_of_gt hji, hc0 j i (lt_asymm hji)]`.

Substitute `hij` using the available equality. Simplify using `[hc0 i i (lt_irrefl i)]`. Use extensionality with `a b`. Establish `hw : w' b = w b + ∑ d, c b d • w d` using `by rw [hcs b]; abel`. Establish `key : S.hT (f a) (w' b) = S.hT (f a) (w b) + ∑ d, S.hT (f a) (w d) * c b d`.

Rewrite using `[hw, map_add, map_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul, mul_comm]`. Rewrite using `[Matrix.mul_apply]`.

Simplify using `only [Matrix.of_apply, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Conclude with `key`.
-/
theorem gram_second {N : ℕ} (f w w' : Fin N → S.V)
    (h : ∀ b, w' b - w b ∈ Submodule.span E (w '' {c | c < b})) :
    ∃ B : Matrix (Fin N) (Fin N) E, IsUpUni B ∧
      (Matrix.of fun a b => S.hT (f a) (w' b)) = (Matrix.of fun a b => S.hT (f a) (w b)) * B := by
  choose c hc0 hcs using fun b => exists_coeffs w b _ (h b)
  refine ⟨Matrix.of fun d b => (if d = b then (1 : E) else 0) + c b d, ?_, ?_⟩
  · intro i j
    refine ⟨fun hji => ?_, fun hij => ?_⟩
    · simp [ne_of_gt hji, hc0 j i (lt_asymm hji)]
    · subst hij; simp [hc0 i i (lt_irrefl i)]
  · ext a b
    have hw : w' b = w b + ∑ d, c b d • w d := by rw [hcs b]; abel
    have key : S.hT (f a) (w' b) = S.hT (f a) (w b) + ∑ d, S.hT (f a) (w d) * c b d := by
      rw [hw, map_add, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact key

variable {T T' : E}

/- English proof (translation)
Simplify using `[frame, Formalism.MainNotions.S.FlagG.fvec]`.
-/
theorem frame_castSucc (F : LFlag S r T) (i : Fin r) : frame F (Fin.castSucc i) = F.fl.e i := by
  simp [frame, Formalism.MainNotions.S.FlagG.fvec]

/- English proof (translation)
Simplify using `[frame, Formalism.MainNotions.S.FlagG.fvec]`.
-/
theorem frame_last (F : LFlag S r T) : frame F (Fin.last r) = F.fl.z := by
  simp [frame, Formalism.MainNotions.S.FlagG.fvec]

/- English proof (translation)
Rewrite using `[mem_orth_iff]`. Introduce `x hx`. Simplify using `only [Xsp, Formalism.MainNotions.S.FlagG.X] at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨i, rfl⟩` from `hy`. Conclude with `F.fl.z_orth i`. Consider the case `zero => simp`. Consider the case `add y y' _ _ h1 h2 => rw [map_add, LinearMap.add_apply, h1, h2, add_zero]`. Consider the case `smul c y _ h => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, h, smul_zero]`.
-/
theorem z_mem_orth (F : LFlag S r T) : F.fl.z ∈ orth S (Xsp F) := by
  rw [mem_orth_iff]
  intro x hx
  dsimp only [Xsp, Formalism.MainNotions.S.FlagG.X] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact F.fl.z_orth i
  | zero => simp
  | add y y' _ _ h1 h2 => rw [map_add, LinearMap.add_apply, h1, h2, add_zero]
  | smul c y _ h => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, h, smul_zero]

/- English proof (translation)
Proceed by induction on `a using Fin.lastCases with`. Consider the case `last`. Establish `h` using `hn.2.2 _ (z_mem_orth F)`. Rewrite using `[frame_last]`. Use `(show Xsp F ≤ _ from ?_) h` and prove the remaining obligations.

Simplify using `only [Xsp, Formalism.MainNotions.S.FlagG.X]`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `⟨Fin.castSucc j, Fin.castSucc_lt_last j, frame_castSucc F j⟩`. Consider the case `cast i`.

Establish `h` using `hn.2.1 i.1 _ (e_mem_Xflag F i)`. Rewrite using `[frame_castSucc]`. Use `(show Xflag F i.1 ≤ _ from ?_) h` and prove the remaining obligations. Simplify using `only [Xflag, Formalism.MainNotions.S.FlagG.Xa]`. Use `Submodule.span_mono ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨j, hj, rfl⟩`. Conclude with `⟨Fin.castSucc j, Fin.castSucc_lt_castSucc_iff.2 hj, frame_castSucc F j⟩`.
-/
theorem nlam_frame (Λ : Submodule (𝓞 E) S.V) {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F)
    (a : Fin (r + 1)) : n (frame F a) - frame F a ∈ Submodule.span E (frame F '' {c | c < a}) := by
  induction a using Fin.lastCases with
  | last =>
    have h := hn.2.2 _ (z_mem_orth F)
    rw [frame_last]
    refine (show Xsp F ≤ _ from ?_) h
    dsimp only [Xsp, Formalism.MainNotions.S.FlagG.X]
    refine Submodule.span_mono ?_
    rintro _ ⟨j, rfl⟩
    exact ⟨Fin.castSucc j, Fin.castSucc_lt_last j, frame_castSucc F j⟩
  | cast i =>
    have h := hn.2.1 i.1 _ (e_mem_Xflag F i)
    rw [frame_castSucc]
    refine (show Xflag F i.1 ≤ _ from ?_) h
    dsimp only [Xflag, Formalism.MainNotions.S.FlagG.Xa]
    refine Submodule.span_mono ?_
    rintro _ ⟨j, hj, rfl⟩
    exact ⟨Fin.castSucc j, Fin.castSucc_lt_castSucc_iff.2 hj, frame_castSucc F j⟩

/- English proof (translation)
Use extensionality with `a b`. Both sides reduce to the same expression.
-/
theorem zhat_eq (F : LFlag S r T) (F' : LFlag S r T') :
    ZhatL F F' = Matrix.of fun a b => S.hT (frame F a) (frame F' b) := by
  ext a b; rfl

/- English proof (translation)
Take `⟨n, hn, m, hm, hfr, -⟩` from `h`. Establish `hni` using `nlam_inv hn`. Take `⟨A, hA, hAe⟩` from `gram_first (frame F) (fun a => n⁻¹ (frame F a)) (fun b => m (frame F₁ b)) (fun a => nlam_frame Λ hni a)`. Take `⟨B, hB, hBe⟩` from `gram_second (frame F) (frame F₁) (fun b => m (frame F₁ b)) (fun b => nlam_frame Λ hm b)`. Use `⟨A, B, hA, hB, ?_⟩` and prove the remaining obligations.

Establish `h2 : ZhatL F F₂ = Matrix.of fun a b => S.hT (n⁻¹ (frame F a)) (m (frame F₁ b))`. Rewrite using `[zhat_eq]`. Use extensionality with `a b`. Simplify using `only [Matrix.of_apply]`. Rewrite using `[hfr b, ← isom_app hn.1.1 (n⁻¹ (frame F a)) (m (frame F₁ b))]`.

Rewrite using `[show n (n⁻¹ (frame F a)) = frame F a from n.apply_symm_apply _]`. Rewrite using `[h2, hAe, hBe, zhat_eq, Matrix.mul_assoc]`.
-/
theorem zhat_factor (Λ : Submodule (𝓞 E) S.V) {F : LFlag S r T} {F₁ F₂ : LFlag S r T'}
    (h : DCRel Λ F F₁ F₂) :
    ∃ A B : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsLoUni A ∧ IsUpUni B ∧
      ZhatL F F₂ = A * ZhatL F F₁ * B := by
  obtain ⟨n, hn, m, hm, hfr, -⟩ := h
  have hni := nlam_inv hn
  obtain ⟨A, hA, hAe⟩ := gram_first (frame F) (fun a => n⁻¹ (frame F a)) (fun b => m (frame F₁ b))
    (fun a => nlam_frame Λ hni a)
  obtain ⟨B, hB, hBe⟩ := gram_second (frame F) (frame F₁) (fun b => m (frame F₁ b))
    (fun b => nlam_frame Λ hm b)
  refine ⟨A, B, hA, hB, ?_⟩
  have h2 : ZhatL F F₂ = Matrix.of fun a b => S.hT (n⁻¹ (frame F a)) (m (frame F₁ b)) := by
    rw [zhat_eq]
    ext a b
    simp only [Matrix.of_apply]
    rw [hfr b, ← isom_app hn.1.1 (n⁻¹ (frame F a)) (m (frame F₁ b))]
    rw [show n (n⁻¹ (frame F a)) = frame F a from n.apply_symm_apply _]
  rw [h2, hAe, hBe, zhat_eq, Matrix.mul_assoc]

/- English proof (translation)
Take `⟨A, B, hA, hB, he⟩` from `zhat_factor Λ h`. Establish `: Formalism.MainNotions.S.Zhat F.fl F₂.fl = A * Formalism.MainNotions.S.Zhat F.fl F₁.fl * B` using `he`. Unfold `Formalism.MainNotions.S.Dl`. Rewrite using `[this, leadMinorE_mul_upper _ _ hB, leadMinorE_lower_mul _ _ hA]`.
-/
theorem dl_eq (Λ : Submodule (𝓞 E) S.V) {F : LFlag S r T} {F₁ F₂ : LFlag S r T'}
    (h : DCRel Λ F F₁ F₂) (l : ℕ) : Formalism.MainNotions.S.Dl F.fl F₂.fl l = Formalism.MainNotions.S.Dl F.fl F₁.fl l := by
  obtain ⟨A, B, hA, hB, he⟩ := zhat_factor Λ h
  have : Formalism.MainNotions.S.Zhat F.fl F₂.fl = A * Formalism.MainNotions.S.Zhat F.fl F₁.fl * B := he
  unfold Formalism.MainNotions.S.Dl
  rw [this, leadMinorE_mul_upper _ _ hB, leadMinorE_lower_mul _ _ hA]

/- English proof (translation)
Introduce `x y h`. Establish `h' : DCRel Λ F x.1 y.1` using `h`. Use `show Formalism.MainNotions.S.Gflag F.fl x.1.fl = Formalism.MainNotions.S.Gflag F.fl y.1.fl`. Unfold `Formalism.MainNotions.S.Gflag`. Rewrite using `[dl_eq Λ h', dl_eq Λ h']`.
-/
theorem gFun_all (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (P : LFlag S r T' → Prop) :
    GFun Λ F P := by
  intro x y h
  have h' : DCRel Λ F x.1 y.1 := h
  show Formalism.MainNotions.S.Gflag F.fl x.1.fl = Formalism.MainNotions.S.Gflag F.fl y.1.fl
  unfold Formalism.MainNotions.S.Gflag
  rw [dl_eq Λ h', dl_eq Λ h']

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[ZhatOM, Matrix.mul_diagonal, mul_comm]`.
-/
theorem zhatOM_eq_mul {K : Type*} [CommRing K] (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    ZhatOM Z = Z * Matrix.diagonal (fun b : Fin (r + 1) => ((-1 : K) ^ (r - b.val))) := by
  ext a b
  simp [ZhatOM, Matrix.mul_diagonal, mul_comm]

/- English proof (translation)
Rewrite using `[← mul_pow]`. Simplify using the standard rewrite rules.
-/
theorem sgn_sq {K : Type*} [CommRing K] (b : Fin (r + 1)) :
    ((-1 : K) ^ (r - b.val)) * ((-1 : K) ^ (r - b.val)) = 1 := by
  rw [← mul_pow]; simp

/- English proof (translation)
Introduce `i j`. Use `⟨fun hji => ?_, fun hij => ?_⟩` and prove the remaining obligations. Simplify using `[Matrix.mul_diagonal, Matrix.diagonal_mul, (hB i j).1 hji]`. Substitute `hij` using the available equality. Simplify using `only [Matrix.mul_diagonal, Matrix.diagonal_mul, (hB i i).2 rfl, mul_one]`.

Conclude with `sgn_sq i`.
-/
theorem isUpUni_conj_sgn {K : Type*} [CommRing K] {B : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (hB : IsUpUni B) :
    IsUpUni (Matrix.diagonal (fun b : Fin (r + 1) => ((-1 : K) ^ (r - b.val))) * B *
      Matrix.diagonal (fun b : Fin (r + 1) => ((-1 : K) ^ (r - b.val)))) := by
  intro i j
  refine ⟨fun hji => ?_, fun hij => ?_⟩
  · simp [Matrix.mul_diagonal, Matrix.diagonal_mul, (hB i j).1 hji]
  · subst hij
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, (hB i i).2 rfl, mul_one]
    exact sgn_sq i

/- English proof (translation)
Take `⟨L, U, hL, hU, hZ⟩` from `hc`. Use `set Ds := Matrix.diagonal (fun b : Fin (r + 1) => ((-1 : K) ^ (r - b.val))) with hDs`. Establish `hDD : Ds * Ds = 1`. Rewrite using `[hDs, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`.

Use function extensionality and compare the values at `b`. Conclude with `sgn_sq b`. Use `⟨A * L, U * (Ds * B * Ds), isLoUni_mul hA hL, isUpUni_mul hU (isUpUni_conj_sgn hB), ?_⟩` and prove the remaining obligations. Rewrite `hZ`, the goal using `[zhatOM_eq_mul]`. Rewrite using `[he]`.

Establish `e1 : A * Z * B * Ds = A * (Z * Ds) * (Ds * B * Ds)`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc Ds Ds (B * Ds), hDD, Matrix.one_mul]`. Rewrite using `[e1, hZ]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem cell_step {K : Type*} [CommRing K] {Z Z₂ A B : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (hA : IsLoUni A) (hB : IsUpUni B) (he : Z₂ = A * Z * B) (w : Point K (r + 1))
    (hc : IsInCell (ZhatOM Z) w) : IsInCell (ZhatOM Z₂) w := by
  obtain ⟨L, U, hL, hU, hZ⟩ := hc
  set Ds := Matrix.diagonal (fun b : Fin (r + 1) => ((-1 : K) ^ (r - b.val))) with hDs
  have hDD : Ds * Ds = 1 := by
    rw [hDs, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext b
    exact sgn_sq b
  refine ⟨A * L, U * (Ds * B * Ds), isLoUni_mul hA hL, isUpUni_mul hU (isUpUni_conj_sgn hB), ?_⟩
  rw [zhatOM_eq_mul] at hZ ⊢
  rw [he]
  have e1 : A * Z * B * Ds = A * (Z * Ds) * (Ds * B * Ds) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Ds Ds (B * Ds), hDD, Matrix.one_mul]
  rw [e1, hZ]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Introduce `x y h w`. Establish `h' : DCRel Λ F x.1 y.1` using `h`. Establish `hs : DCRel Λ F y.1 x.1` using `(dCRelEquivAll_holds E S r T T' Λ F).symm h'`. Take `⟨A, B, hA, hB, he⟩` from `zhat_factor Λ h'`. Take `⟨A', B', hA', hB', he'⟩` from `zhat_factor Λ hs`.

Conclude with `⟨cell_step hA hB he w, cell_step hA' hB' he' w⟩`.
-/
theorem cellFun_all (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (P : LFlag S r T' → Prop) :
    CellFun Λ F P := by
  intro x y h w
  have h' : DCRel Λ F x.1 y.1 := h
  have hs : DCRel Λ F y.1 x.1 := (dCRelEquivAll_holds E S r T T' Λ F).symm h'
  obtain ⟨A, B, hA, hB, he⟩ := zhat_factor Λ h'
  obtain ⟨A', B', hA', hB', he'⟩ := zhat_factor Λ hs
  exact ⟨cell_step hA hB he w, cell_step hA' hB' he' w⟩

/- English proof (translation)
Take `⟨n1, hn1, h1⟩` from `hx`. Take `⟨n, hn, m, hm, hfr, -⟩` from `h`. Establish `hTT : T' = T`. Establish `e1` using `isom_app hn1.1.1 (frame F (Fin.last r)) (frame F (Fin.last r))`. Rewrite `e1` using `[h1, frame_last, frame_last, x.fl.z_norm, F.fl.z_norm]`.

Conclude with `neg_injective e1`. Substitute `hTT` using the available equality. Establish `hc` using `(nLamConj_holds E S r T' Λ F x n1 hn1.1 (fun a => (h1 a).symm) m).1 hm`. Use `⟨n * m * n1, ?_, fun a => ?_⟩` and prove the remaining obligations. Establish `e : n * m * n1 = n * n1 * (n1⁻¹ * m * n1)` using `by group`.

Rewrite using `[e]`. Conclude with `nlam_mul (nlam_mul hn hn1) hc`. Rewrite using `[hfr a, ← h1 a]`. Both sides reduce to the same expression.
-/
theorem feqF_fwd (Λ : Submodule (𝓞 E) S.V) {F : LFlag S r T} {x y : LFlag S r T'} (h : DCRel Λ F x y)
    (hx : ∃ n ∈ NLam Λ F, ∀ a, n (frame F a) = frame x a) :
    ∃ n ∈ NLam Λ F, ∀ a, n (frame F a) = frame y a := by
  obtain ⟨n1, hn1, h1⟩ := hx
  obtain ⟨n, hn, m, hm, hfr, -⟩ := h
  have hTT : T' = T := by
    have e1 := isom_app hn1.1.1 (frame F (Fin.last r)) (frame F (Fin.last r))
    rw [h1, frame_last, frame_last, x.fl.z_norm, F.fl.z_norm] at e1
    exact neg_injective e1
  subst hTT
  have hc := (nLamConj_holds E S r T' Λ F x n1 hn1.1 (fun a => (h1 a).symm) m).1 hm
  refine ⟨n * m * n1, ?_, fun a => ?_⟩
  · have e : n * m * n1 = n * n1 * (n1⁻¹ * m * n1) := by group
    rw [e]
    exact nlam_mul (nlam_mul hn hn1) hc
  · rw [hfr a, ← h1 a]
    rfl

/- English proof (translation)
Introduce `x y h`. Establish `h' : DCRel Λ F x.1 y.1` using `h`. Establish `hs : DCRel Λ F y.1 x.1` using `(dCRelEquivAll_holds E S r T T' Λ F).symm h'`. Conclude with `⟨feqF_fwd Λ h', feqF_fwd Λ hs⟩`.
-/
theorem feqFFun_all (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (P : LFlag S r T' → Prop) :
    FeqFFun Λ F P := by
  intro x y h
  have h' : DCRel Λ F x.1 y.1 := h
  have hs : DCRel Λ F y.1 x.1 := (dCRelEquivAll_holds E S r T T' Λ F).symm h'
  exact ⟨feqF_fwd Λ h', feqF_fwd Λ hs⟩

end Gen

end PI.TermAttrConst.UnitaryGroupMassFormula
