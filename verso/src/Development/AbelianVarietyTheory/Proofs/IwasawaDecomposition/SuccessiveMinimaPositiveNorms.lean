import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SInfMulNormPlk

open GlobalTheory.LineNorm

namespace GlobalTheory.LineNorm.Covol

open Matrix

/- English proof (translation)
Unfold `minor`. Simplify using `only [Matrix.det_apply', Matrix.of_apply, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_mul_distrib]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_prod_mul_minor {C : Type} [CommRing C] {g m k : ℕ} (h : Fin k → Fin g → C) (a : Fin m → Fin g → C)
    (hk : k ≤ m) :
    ∑ s : Fin k → Fin g, (∏ i, h i (s i)) * minor a hk s =
      (Matrix.of fun l i => ∑ t, h i t * a (Fin.castLE hk l) t).det := by
  unfold minor
  simp only [Matrix.det_apply', Matrix.of_apply, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

/- English proof (translation)
Set `e` to `Fintype.equivFin J`. Establish `hg' : LinearIndependent L (g.submatrix e.symm id)ᵀ` using `hg.map' (LinearEquiv.funCongrLeft L L e.symm).toLinearMap (LinearEquiv.ker _)`. Take `⟨ι, u, b, h1, h2, h3, h4, h5, h6⟩` from `GlobalTheory.exists_integral_pivot_decomposition L W _ _ _ hg'`. Use `⟨fun i => e.symm (ι i), u.submatrix e id, b, fun _ _ => h1 _ _, fun i j hij => ?_, fun i => ?_, h4, h5, ?_⟩` and prove the remaining obligations. Simplify using `using h2 i j hij`.

Simplify using `using h3 i`. Use extensionality with `j l`. Use `congrFun (congrFun h6 (e j)) l` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply]`.
-/
theorem exists_pivot {L : Type} [Field L] (W : ValuationSubring L) {J : Type} [Fintype J] {r : ℕ}
    (g : Matrix J (Fin r) L) (hg : LinearIndependent L gᵀ) :
    ∃ (ι : Fin r → J) (u : Matrix J (Fin r) L) (b : Matrix (Fin r) (Fin r) L),
      (∀ i j, u i j ∈ W) ∧ (∀ i j : Fin r, i < j → u (ι i) j = 0) ∧
      (∀ i : Fin r, u (ι i) i = 1) ∧ b.BlockTriangular id ∧ (∀ i, b i i ≠ 0) ∧ g = u * b := by
  let e := Fintype.equivFin J
  have hg' : LinearIndependent L (g.submatrix e.symm id)ᵀ :=
    hg.map' (LinearEquiv.funCongrLeft L L e.symm).toLinearMap (LinearEquiv.ker _)
  obtain ⟨ι, u, b, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.exists_integral_pivot_decomposition L W _ _ _ hg'
  refine ⟨fun i => e.symm (ι i), u.submatrix e id, b, fun _ _ => h1 _ _, fun i j hij => ?_, fun i => ?_, h4, h5, ?_⟩
  · simpa using h2 i j hij
  · simpa using h3 i
  · ext j l
    have := congrFun (congrFun h6 (e j)) l
    simpa [Matrix.mul_apply] using this

/- English proof (translation)
Establish `h1 : (u * b).submatrix σ (Fin.castLE hk) = u.submatrix σ (Fin.castLE hk) * b.submatrix (Fin.castLE hk) (Fin.castLE hk)`. Use extensionality with `l' l`. Rewrite using `[submatrix_apply, mul_apply, mul_apply]`. Use `symm`. Use `Fintype.sum_of_injective (Fin.castLE hk) (Fin.castLE_injective hk) _ _ ?_ (fun _ => rfl)` and prove the remaining obligations.

Introduce `j hj`. Establish `: b j (Fin.castLE hk l) = 0`. Apply `hb` to reduce the goal to its premises. Assume the negation of the conclusion as `hlt`. Establish `hle : (j : ℕ) ≤ l` using `Fin.le_def.mp (not_lt.mp hlt)`.

Conclude with `hj ⟨⟨j, lt_of_le_of_lt hle l.2⟩, rfl⟩`. Rewrite using `[this, mul_zero]`. Establish `h3 : (b.submatrix (Fin.castLE hk) (Fin.castLE hk)).BlockTriangular id` using `fun i j hij => hb hij`. Rewrite using `[h1, det_mul, Matrix.det_of_isUpperTriangular h3]`. Both sides reduce to the same expression.
-/
theorem det_eq {C : Type} [Field C] {J : Type} {n : ℕ}
    (u : Matrix J (Fin n) C) (b : Matrix (Fin n) (Fin n) C) (hb : b.BlockTriangular id)
    {k : ℕ} (hk : k ≤ n) (σ : Fin k → J) :
    ((u * b).submatrix σ (Fin.castLE hk)).det =
      (u.submatrix σ (Fin.castLE hk)).det * ∏ l : Fin k, b (Fin.castLE hk l) (Fin.castLE hk l) := by
  have h1 : (u * b).submatrix σ (Fin.castLE hk) =
      u.submatrix σ (Fin.castLE hk) * b.submatrix (Fin.castLE hk) (Fin.castLE hk) := by
    ext l' l
    rw [submatrix_apply, mul_apply, mul_apply]
    symm
    refine Fintype.sum_of_injective (Fin.castLE hk) (Fin.castLE_injective hk) _ _ ?_ (fun _ => rfl)
    intro j hj
    have : b j (Fin.castLE hk l) = 0 := by
      apply hb
      by_contra hlt
      have hle : (j : ℕ) ≤ l := Fin.le_def.mp (not_lt.mp hlt)
      exact hj ⟨⟨j, lt_of_le_of_lt hle l.2⟩, rfl⟩
    rw [this, mul_zero]
  have h3 : (b.submatrix (Fin.castLE hk) (Fin.castLE hk)).BlockTriangular id := fun i j hij => hb hij
  rw [h1, det_mul, Matrix.det_of_isUpperTriangular h3]
  rfl

/- English proof (translation)
The claim follows from `GlobalTheory.FlagEmb.GradedNorm.mem_of_mulVec W id (u.submatrix ι id) (fun _ _ => huW _ _) hu0 hu1 y (fun s => hy (ι s)) i`.
-/
theorem mem_of_mulVec {C : Type} [Field C] (W : ValuationSubring C) {J : Type} {n : ℕ} (ι : Fin n → J)
    (u : Matrix J (Fin n) C) (huW : ∀ i j, u i j ∈ W)
    (hu0 : ∀ i j : Fin n, i < j → u (ι i) j = 0) (hu1 : ∀ i, u (ι i) i = 1) (y : Fin n → C)
    (hy : ∀ s, (u *ᵥ y) s ∈ W) (i : Fin n) : y i ∈ W :=
  GlobalTheory.FlagEmb.GradedNorm.mem_of_mulVec W id (u.submatrix ι id) (fun _ _ => huW _ _) hu0 hu1 y
    (fun s => hy (ι s)) i

/- English proof (translation)
Introduce `C _ _ g J _ h hh m a ha N hN`. Set `W : ValuationSubring C` to `(NormedField.valuation (K := C)).valuationSubring`. Establish `hW : ∀ x, x ∈ W ↔ ‖x‖ ≤ 1` using `fun x => by`. Rewrite using `[Valuation.mem_valuationSubring_iff, NormedField.valuation_apply]`. Conclude with `Iff.rfl`.

Set `G : Matrix J (Fin m) C` to `Matrix.of fun j l => ∑ t, h j t * a l t`. Establish `hli : LinearIndependent C Gᵀ`. Establish `hker : LinearMap.ker (Matrix.mulVecLin (Matrix.of h)) = ⊥` using `LinearMap.ker_eq_bot'.mpr fun c hc => hh c fun j => congrFun hc j`. Conclude with `ha.map' _ hker`. Take `⟨ι, u, b, huW, hu0, hu1, hb, hbd, hc⟩` from `exists_pivot W G hli`.

Establish `hsum : ∀ (cf : Fin m → C) (j : J), ∑ i, h j i * ∑ l', cf l' * a l' i = (u *ᵥ (b *ᵥ cf)) j` using `fun cf j => by`. Rewrite using `[mulVec_mulVec, ← hc]`. Simplify using `only [G, mulVec, dotProduct, of_apply, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.

Establish `hbdet : IsUnit b.det`. Rewrite using `[Matrix.det_of_isUpperTriangular hb]`. Conclude with `(Finset.prod_ne_zero_iff.mpr fun i _ => hbd i).isUnit`. Establish `hNb : ∀ i, N i = ‖b i i‖`. Introduce `i`.

Establish `hdiag : ∀ cf : Fin m → C, (∀ k, i < k → cf k = 0) → (b *ᵥ cf) i = b i i * cf i` using `fun cf hcf => by`. Rewrite using `[mulVec, dotProduct]`. Use `Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)` and prove the remaining obligations. Break down `lt_or_gt_of_ne hj with h | h` into its components or cases. Rewrite using `[hb h, zero_mul]`.

Rewrite using `[hcf j h, mul_zero]`. Rewrite using `[hN]`. Apply `IsLeast.csInf_eq` to reduce the goal to its premises. Prove the components needed by the constructor for the conclusion. Use `letI := b.invertibleOfIsUnitDet hbdet`.

Establish `hinv : (b⁻¹).BlockTriangular id` using `Matrix.blockTriangular_inv_of_blockTriangular hb`. Establish `hz : ∀ k, i < k → (b⁻¹ *ᵥ Pi.single i 1 : Fin m → C) k = 0` using `fun k hk => by`. Rewrite using `[mulVec_single_one]`. Conclude with `hinv hk`. Establish `hbb : b *ᵥ (b⁻¹ *ᵥ Pi.single i 1) = Pi.single i 1`.

Rewrite using `[mulVec_mulVec, mul_nonsing_inv _ hbdet, one_mulVec]`. Establish `h1` using `hdiag _ hz`. Rewrite `h1` using `[hbb, Pi.single_eq_same]`. Use `⟨b⁻¹ *ᵥ Pi.single i 1, right_ne_zero_of_mul (h1 ▸ one_ne_zero), hz, fun s => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hsum, hbb, mulVec_single_one]`.

Conclude with `(hW _).1 (huW _ _)`. Rewrite using `[eq_inv_of_mul_eq_one_left h1.symm, norm_inv]`. Introduce and unpack `r ⟨cf, hcf, hz, hint, rfl⟩`. Establish `h1` using `(hW _).1 (mem_of_mulVec W ι u huW hu0 hu1 (b *ᵥ cf) (fun s => (hW _).2 (hsum cf s ▸ hint s)) i)`. Rewrite `h1` using `[hdiag cf hz, norm_mul]`.

Rewrite using `[← one_div, le_div_iff₀ (norm_pos_iff.2 hcf)]`. Conclude with `h1`. Use `⟨fun l => hNb l ▸ norm_pos_iff.2 (hbd l), fun k hk => ?_⟩` and prove the remaining obligations. Establish `hdet : ∀ σ : Fin k → J, ‖∑ s : Fin k → Fin g, (∏ i, h (σ i) (s i)) * minor a hk s‖ = ‖(u.submatrix σ (Fin.castLE hk)).det‖ * ∏ l : Fin k, N (Fin.castLE hk l)` using `fun σ => by`. Rewrite using `[sum_prod_mul_minor (fun i => h (σ i)) a hk, ← det_transpose]`.

Express the relevant statement in the definitionally equal form `‖(G.submatrix σ (Fin.castLE hk)).det‖ = _`. Rewrite using `[hc, det_eq u b hb hk, norm_mul, norm_prod]`. Simplify using `only [hNb]`. Use `symm`. Apply `IsGreatest.csSup_eq` to reduce the goal to its premises.

Prove the components needed by the constructor for the conclusion. Use `⟨ι ∘ Fin.castLE hk, ?_⟩` and prove the remaining obligations. Establish `hMt : (u.submatrix (ι ∘ Fin.castLE hk) (Fin.castLE hk)).BlockTriangular OrderDual.toDual` using `fun i j hij => hu0 _ _ hij`. Use `beta_reduce`. Rewrite using `[hdet, Matrix.det_of_isLowerTriangular _ hMt]`.

Simplify using `[hu1]`. Introduce and unpack `_ ⟨σ, rfl⟩ beta_reduce`. Rewrite using `[hdet]`. Conclude with `mul_le_of_le_one_left (Finset.prod_nonneg fun _ _ => hNb _ ▸ norm_nonneg _) ((hW _).1 (GlobalTheory.FlagEmb.GradedNorm.det_mem W _ fun _ _ => huW _ _))`.
-/
theorem prod_grNorm_eq_iSup_minor : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (g : ℕ) (J : Type) [Fintype J] (h : J → Fin g → C), (∀ c : Fin g → C, (∀ j, ∑ i, h j i * c i = 0) → c = 0) → ∀ (m : ℕ) (a : Fin m → Fin g → C), LinearIndependent C a → ∀ (N : Fin m → ℝ), (∀ l, N l = sInf {r | ∃ cf : Fin m → C, cf l ≠ 0 ∧ (∀ l', l < l' → cf l' = 0) ∧ (∀ j, ‖∑ i, h j i * ∑ l', cf l' * a l' i‖ ≤ 1) ∧ r = ‖cf l‖⁻¹}) → (∀ l, 0 < N l) ∧ ∀ (k : ℕ) (hk : k ≤ m), ∏ l : Fin k, N (Fin.castLE hk l) = ⨆ σ : Fin k → J, ‖∑ s : Fin k → Fin g, (∏ i, h (σ i) (s i)) * minor a hk s‖ := by
  intro C _ _ g J _ h hh m a ha N hN
  let W : ValuationSubring C := (NormedField.valuation (K := C)).valuationSubring
  have hW : ∀ x, x ∈ W ↔ ‖x‖ ≤ 1 := fun x => by
    rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply]
    exact Iff.rfl
  let G : Matrix J (Fin m) C := Matrix.of fun j l => ∑ t, h j t * a l t
  have hli : LinearIndependent C Gᵀ := by
    have hker : LinearMap.ker (Matrix.mulVecLin (Matrix.of h)) = ⊥ :=
      LinearMap.ker_eq_bot'.mpr fun c hc => hh c fun j => congrFun hc j
    exact ha.map' _ hker
  obtain ⟨ι, u, b, huW, hu0, hu1, hb, hbd, hc⟩ := exists_pivot W G hli
  have hsum : ∀ (cf : Fin m → C) (j : J), ∑ i, h j i * ∑ l', cf l' * a l' i = (u *ᵥ (b *ᵥ cf)) j := fun cf j => by
    rw [mulVec_mulVec, ← hc]
    simp only [G, mulVec, dotProduct, of_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hbdet : IsUnit b.det := by
    rw [Matrix.det_of_isUpperTriangular hb]
    exact (Finset.prod_ne_zero_iff.mpr fun i _ => hbd i).isUnit
  have hNb : ∀ i, N i = ‖b i i‖ := by
    intro i
    have hdiag : ∀ cf : Fin m → C, (∀ k, i < k → cf k = 0) → (b *ᵥ cf) i = b i i * cf i := fun cf hcf => by
      rw [mulVec, dotProduct]
      refine Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)
      rcases lt_or_gt_of_ne hj with h | h
      · rw [hb h, zero_mul]
      · rw [hcf j h, mul_zero]
    rw [hN]
    apply IsLeast.csInf_eq
    constructor
    · letI := b.invertibleOfIsUnitDet hbdet
      have hinv : (b⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hb
      have hz : ∀ k, i < k → (b⁻¹ *ᵥ Pi.single i 1 : Fin m → C) k = 0 := fun k hk => by
        rw [mulVec_single_one]
        exact hinv hk
      have hbb : b *ᵥ (b⁻¹ *ᵥ Pi.single i 1) = Pi.single i 1 := by
        rw [mulVec_mulVec, mul_nonsing_inv _ hbdet, one_mulVec]
      have h1 := hdiag _ hz
      rw [hbb, Pi.single_eq_same] at h1
      refine ⟨b⁻¹ *ᵥ Pi.single i 1, right_ne_zero_of_mul (h1 ▸ one_ne_zero), hz, fun s => ?_, ?_⟩
      · rw [hsum, hbb, mulVec_single_one]
        exact (hW _).1 (huW _ _)
      · rw [eq_inv_of_mul_eq_one_left h1.symm, norm_inv]
    · rintro r ⟨cf, hcf, hz, hint, rfl⟩
      have h1 := (hW _).1 (mem_of_mulVec W ι u huW hu0 hu1 (b *ᵥ cf)
        (fun s => (hW _).2 (hsum cf s ▸ hint s)) i)
      rw [hdiag cf hz, norm_mul] at h1
      rw [← one_div, le_div_iff₀ (norm_pos_iff.2 hcf)]
      exact h1
  refine ⟨fun l => hNb l ▸ norm_pos_iff.2 (hbd l), fun k hk => ?_⟩
  have hdet : ∀ σ : Fin k → J, ‖∑ s : Fin k → Fin g, (∏ i, h (σ i) (s i)) * minor a hk s‖ =
      ‖(u.submatrix σ (Fin.castLE hk)).det‖ * ∏ l : Fin k, N (Fin.castLE hk l) := fun σ => by
    rw [sum_prod_mul_minor (fun i => h (σ i)) a hk, ← det_transpose]
    change ‖(G.submatrix σ (Fin.castLE hk)).det‖ = _
    rw [hc, det_eq u b hb hk, norm_mul, norm_prod]
    simp only [hNb]
  symm
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨ι ∘ Fin.castLE hk, ?_⟩
    have hMt : (u.submatrix (ι ∘ Fin.castLE hk) (Fin.castLE hk)).BlockTriangular OrderDual.toDual :=
      fun i j hij => hu0 _ _ hij
    beta_reduce
    rw [hdet, Matrix.det_of_isLowerTriangular _ hMt]
    simp [hu1]
  · rintro _ ⟨σ, rfl⟩
    beta_reduce
    rw [hdet]
    exact mul_le_of_le_one_left (Finset.prod_nonneg fun _ _ => hNb _ ▸ norm_nonneg _)
      ((hW _).1 (GlobalTheory.FlagEmb.GradedNorm.det_mem W _ fun _ _ => huW _ _))

end GlobalTheory.LineNorm.Covol
