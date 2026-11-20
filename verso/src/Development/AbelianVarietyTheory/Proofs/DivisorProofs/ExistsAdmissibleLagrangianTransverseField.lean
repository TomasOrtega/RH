import Mathlib
open Matrix

namespace GlobalTheory

/- English proof (translation)
Establish `h` using `congrArg (fun M => u ⬝ᵥ (M *ᵥ (c ∘ w))) hiso`. Simplify using `only [add_mulVec, dotProduct_add, dotProduct_mulVec, zero_mulVec, dotProduct_zero] at h`. Establish `e1 : u ᵥ* (Aᵀ * S * C.map c) = 0`. Rewrite using `[← vecMul_vecMul, ← vecMul_vecMul, vecMul_transpose, hu, zero_vecMul, zero_vecMul]`. Establish `e2 : u ᵥ* (Cᵀ * S * A.map c) ⬝ᵥ (c ∘ w) = ((C *ᵥ u) ᵥ* S) ⬝ᵥ (c ∘ (A *ᵥ w))`.

Rewrite using `[← vecMul_vecMul, ← dotProduct_mulVec, ← vecMul_vecMul, vecMul_transpose]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `(RingHom.map_mulVec c A w i).symm`. Rewrite `h` using `[e1, zero_dotProduct, zero_add, e2]`.

Conclude with `h`.
-/
theorem lagr_functional_kills_image {k : Type} [Field k] (c : k →+* k) {n : ℕ}
    (S A C : Matrix (Fin n) (Fin n) k)
    (hiso : Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0)
    (u : Fin n → k) (hu : A *ᵥ u = 0) (w : Fin n → k) :
    ((C *ᵥ u) ᵥ* S) ⬝ᵥ (c ∘ (A *ᵥ w)) = 0 := by
  have h := congrArg (fun M => u ⬝ᵥ (M *ᵥ (c ∘ w))) hiso
  simp only [add_mulVec, dotProduct_add, dotProduct_mulVec, zero_mulVec, dotProduct_zero] at h
  have e1 : u ᵥ* (Aᵀ * S * C.map c) = 0 := by
    rw [← vecMul_vecMul, ← vecMul_vecMul, vecMul_transpose, hu, zero_vecMul, zero_vecMul]
  have e2 : u ᵥ* (Cᵀ * S * A.map c) ⬝ᵥ (c ∘ w) = ((C *ᵥ u) ᵥ* S) ⬝ᵥ (c ∘ (A *ᵥ w)) := by
    rw [← vecMul_vecMul, ← dotProduct_mulVec, ← vecMul_vecMul, vecMul_transpose]
    congr 1
    funext i
    exact (RingHom.map_mulVec c A w i).symm
  rw [e1, zero_dotProduct, zero_add, e2] at h
  exact h

def lagrRankOne {k : Type} [Field k] {n : ℕ} (S : Matrix (Fin n) (Fin n) k) (j : Fin n) :
    Matrix (Fin n) (Fin n) k :=
  Matrix.of fun a b => if a = j then S b j else 0

/- English proof (translation)
Use extensionality with `a b`. Establish `h1 : c (S b j) = - S j b`. Establish `h2 : Sᵀ b j = (-S.map c) b j` using `by rw [hS]`. Rewrite `h2` using `[transpose_apply, Matrix.neg_apply, Matrix.map_apply]`. Rewrite using `[h2, neg_neg]`.

Establish `h3 : ∀ l, c (if l = j then S b j else 0) = if l = j then c (S b j) else 0`. Apply the tactic sequence `intro l; split_ifs <;> simp`. Simplify using `[Matrix.mul_apply, lagrRankOne, h3, h1]`.
-/
theorem lagrRankOne_adm {k : Type} [Field k] (c : k →+* k) {n : ℕ}
    (S : Matrix (Fin n) (Fin n) k) (hS : Sᵀ = -S.map c) (j : Fin n) :
    (lagrRankOne S j)ᵀ * S + S * (lagrRankOne S j).map c = 0 := by
  ext a b
  have h1 : c (S b j) = - S j b := by
    have h2 : Sᵀ b j = (-S.map c) b j := by rw [hS]
    rw [transpose_apply, Matrix.neg_apply, Matrix.map_apply] at h2
    rw [h2, neg_neg]
  have h3 : ∀ l, c (if l = j then S b j else 0) = if l = j then c (S b j) else 0 := by
    intro l; split_ifs <;> simp
  simp [Matrix.mul_apply, lagrRankOne, h3, h1]

/- English proof (translation)
Use function extensionality and compare the values at `a`. Distinguish the cases in `h : a = j`. Substitute `h` using the available equality. Simplify using `[lagrRankOne, mulVec, vecMul, dotProduct, mul_comm]`. Simplify using `[lagrRankOne, mulVec, dotProduct, h]`.
-/
theorem lagrRankOne_mulVec {k : Type} [Field k] {n : ℕ}
    (S : Matrix (Fin n) (Fin n) k) (j : Fin n) (v : Fin n → k) :
    lagrRankOne S j *ᵥ v = Pi.single j ((v ᵥ* S) j) := by
  funext a
  by_cases h : a = j
  · subst h; simp [lagrRankOne, mulVec, vecMul, dotProduct, mul_comm]
  · simp [lagrRankOne, mulVec, dotProduct, h]

/- English proof (translation)
Establish `hx : C *ᵥ u ≠ 0` using `fun h => hu0 (hinj u hu h)`. Establish `hxS : (C *ᵥ u) ᵥ* S ≠ 0`. Introduce `h`. Establish `hI : Function.Injective fun v : Fin n → k => v ᵥ* S` using `vecMul_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det S).mpr hSu)`. Apply `hx` to reduce the goal to its premises.

Apply `hI` to reduce the goal to its premises. Simplify using `only [h, zero_vecMul]`. Take `⟨j, hj⟩` from `Function.ne_iff.mp hxS`. Simplify using `only [Pi.zero_apply] at hj`. Use `⟨j, ?_, ?_⟩` and prove the remaining obligations.

Introduce `w hw`. Rewrite `hw` using `[add_mulVec, ← mulVec_mulVec, lagrRankOne_mulVec]`. Use `set t := ((C *ᵥ w) ᵥ* S) j with ht`. Establish `hAw : A *ᵥ w = - Pi.single j t` using `eq_neg_of_add_eq_zero_left hw`. Establish `hφ` using `lagr_functional_kills_image c S A C hiso u hu w`.

Establish `hc : (c ∘ (A *ᵥ w)) = Pi.single j (-(c t))`. Rewrite using `[hAw]`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = j`. Substitute `hi` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[hi]`. Rewrite `hφ` using `[hc, dotProduct_single]`. Establish `hct : c t = 0`. Break down `mul_eq_zero.mp hφ with h | h` into its components or cases.

Conclude with `absurd h hj`. Conclude with `neg_eq_zero.mp h`. Establish `ht0 : t = 0` using `(map_eq_zero c).mp hct`. Rewrite using `[hAw, ht0, Pi.single_zero, neg_zero]`. Rewrite using `[add_mulVec, ← mulVec_mulVec, lagrRankOne_mulVec, hu, zero_add]`.

Introduce `h`. Use `congrFun h j` as an intermediate fact. Simplify using `only [Pi.single_eq_same, Pi.zero_apply] at this`. Conclude with `hj this`.
-/
theorem lagr_step {k : Type} [Field k] (c : k →+* k) {n : ℕ}
    (S : Matrix (Fin n) (Fin n) k) (hSu : IsUnit S.det)
    (A C : Matrix (Fin n) (Fin n) k)
    (hinj : ∀ u : Fin n → k, A *ᵥ u = 0 → C *ᵥ u = 0 → u = 0)
    (hiso : Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0)
    (u : Fin n → k) (hu0 : u ≠ 0) (hu : A *ᵥ u = 0) :
    ∃ j : Fin n, (∀ w, (A + lagrRankOne S j * C) *ᵥ w = 0 → A *ᵥ w = 0) ∧
      (A + lagrRankOne S j * C) *ᵥ u ≠ 0 := by
  have hx : C *ᵥ u ≠ 0 := fun h => hu0 (hinj u hu h)
  have hxS : (C *ᵥ u) ᵥ* S ≠ 0 := by
    intro h
    have hI : Function.Injective fun v : Fin n → k => v ᵥ* S :=
      vecMul_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det S).mpr hSu)
    apply hx
    apply hI
    simp only [h, zero_vecMul]
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hxS
  simp only [Pi.zero_apply] at hj
  refine ⟨j, ?_, ?_⟩
  · intro w hw
    rw [add_mulVec, ← mulVec_mulVec, lagrRankOne_mulVec] at hw
    set t := ((C *ᵥ w) ᵥ* S) j with ht
    have hAw : A *ᵥ w = - Pi.single j t := eq_neg_of_add_eq_zero_left hw
    have hφ := lagr_functional_kills_image c S A C hiso u hu w
    have hc : (c ∘ (A *ᵥ w)) = Pi.single j (-(c t)) := by
      rw [hAw]
      funext i
      by_cases hi : i = j
      · subst hi; simp
      · simp [hi]
    rw [hc, dotProduct_single] at hφ
    have hct : c t = 0 := by
      rcases mul_eq_zero.mp hφ with h | h
      · exact absurd h hj
      · exact neg_eq_zero.mp h
    have ht0 : t = 0 := (map_eq_zero c).mp hct
    rw [hAw, ht0, Pi.single_zero, neg_zero]
  · rw [add_mulVec, ← mulVec_mulVec, lagrRankOne_mulVec, hu, zero_add]
    intro h
    have := congrFun h j
    simp only [Pi.single_eq_same, Pi.zero_apply] at this
    exact hj this

/- English proof (translation)
Establish `e : (A + X * C)ᵀ * S * C.map c + Cᵀ * S * (A + X * C).map c = (Aᵀ * S * C.map c + Cᵀ * S * A.map c) + Cᵀ * (Xᵀ * S + S * X.map c) * C.map c`. Rewrite using `[Matrix.map_add c (map_add c)]`. Simplify using `only [transpose_add, transpose_mul, Matrix.map_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws. Rewrite using `[e, hiso, hX, Matrix.mul_zero, Matrix.zero_mul, add_zero]`.
-/
theorem lagr_iso_update {k : Type} [Field k] (c : k →+* k) {n : ℕ}
    (S A C X : Matrix (Fin n) (Fin n) k)
    (hX : Xᵀ * S + S * X.map c = 0)
    (hiso : Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0) :
    (A + X * C)ᵀ * S * C.map c + Cᵀ * S * (A + X * C).map c = 0 := by
  have e : (A + X * C)ᵀ * S * C.map c + Cᵀ * S * (A + X * C).map c =
      (Aᵀ * S * C.map c + Cᵀ * S * A.map c) + Cᵀ * (Xᵀ * S + S * X.map c) * C.map c := by
    rw [Matrix.map_add c (map_add c)]
    simp only [transpose_add, transpose_mul, Matrix.map_mul, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_assoc]
    abel
  rw [e, hiso, hX, Matrix.mul_zero, Matrix.zero_mul, add_zero]

/- English proof (translation)
Establish `e : (X + Y)ᵀ * S + S * (X + Y).map c = (Xᵀ * S + S * X.map c) + (Yᵀ * S + S * Y.map c)`. Rewrite using `[Matrix.map_add c (map_add c)]`. Simplify using `only [transpose_add, Matrix.mul_add, Matrix.add_mul]`. Normalize the expressions using the abelian group laws. Rewrite using `[e, hX, hY, add_zero]`.
-/
theorem transpose_mul_add_mul_map_eq_zero_add {k : Type} [Field k] (c : k →+* k) {n : ℕ}
    (S X Y : Matrix (Fin n) (Fin n) k)
    (hX : Xᵀ * S + S * X.map c = 0) (hY : Yᵀ * S + S * Y.map c = 0) :
    (X + Y)ᵀ * S + S * (X + Y).map c = 0 := by
  have e : (X + Y)ᵀ * S + S * (X + Y).map c = (Xᵀ * S + S * X.map c) + (Yᵀ * S + S * Y.map c) := by
    rw [Matrix.map_add c (map_add c)]
    simp only [transpose_add, Matrix.mul_add, Matrix.add_mul]
    abel
  rw [e, hX, hY, add_zero]

/- English proof (translation)
Introduce `k _ c _ _ n S hSu hS A C hinj hiso`. It suffices to establish `H : ∀ m : ℕ, ∀ A : Matrix (Fin n) (Fin n) k, Module.finrank k (LinearMap.ker A.mulVecLin) < m → (∀ u : Fin n → k, A *ᵥ u = 0 → C *ᵥ u = 0 → u = 0) → Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0 → ∃ X : Matrix (Fin n) (Fin n) k, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det from H …`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro A h`.

Conclude with `absurd h (Nat.not_lt_zero _)`. Consider the case `succ m ih`. Introduce `A hm hinj hiso`. Distinguish the cases in `hdet : IsUnit A.det`. Conclude with `⟨0, by simp, by simpa using hdet⟩`.

Establish `hd : A.det = 0` using `by simpa [isUnit_iff_ne_zero] using hdet`. Take `⟨u, hu0, hu⟩` from `exists_mulVec_eq_zero_iff.mpr hd`. Take `⟨j, hker, hne⟩` from `lagr_step c S hSu A C hinj hiso u hu0 hu`. Establish `hX1` using `lagrRankOne_adm c S hS j`. Establish `hlt : LinearMap.ker (A + lagrRankOne S j * C).mulVecLin < LinearMap.ker A.mulVecLin`.

Use `lt_of_le_of_ne ?_ ?_` and prove the remaining obligations. Introduce `w hw`. Simplify using `only [LinearMap.mem_ker, mulVecLin_apply] at hw ⊢`. Conclude with `hker w hw`. Introduce `heq`.

Apply `hne` to reduce the goal to its premises. Establish `hmem : u ∈ LinearMap.ker A.mulVecLin`. Simplify `hu` using `[LinearMap.mem_ker, mulVecLin_apply]`. Rewrite `hmem` using `[← heq]`. Rewrite `hmem` using `[LinearMap.mem_ker, mulVecLin_apply]`.

Conclude with `hmem`. Establish `hfin` using `Submodule.finrank_lt_finrank_of_lt hlt`. Establish `hinj' : ∀ w : Fin n → k, (A + lagrRankOne S j * C) *ᵥ w = 0 → C *ᵥ w = 0 → w = 0`. Introduce `w h1 h2`. Apply `hinj w _ h2` to reduce the goal to its premises.

Rewrite `h1` using `[add_mulVec, ← mulVec_mulVec, h2, mulVec_zero, add_zero]`. Conclude with `h1`. Take `⟨X2, hX2, hdet2⟩` from `ih (A + lagrRankOne S j * C) (by omega) hinj' (lagr_iso_update c S A C _ hX1 hiso)`. Use `⟨lagrRankOne S j + X2, transpose_mul_add_mul_map_eq_zero_add c S _ _ hX1 hX2, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.add_mul, ← add_assoc]` and apply the resulting hypothesis.
-/
theorem lagrangian_transverse_field :
    ∀ {k : Type} [Field k] (c : k →+* k), (∀ x, c (c x) = x) → (2 : k) ≠ 0 →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) k), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A C : Matrix (Fin n) (Fin n) k), (∀ u : Fin n → k, A *ᵥ u = 0 → C *ᵥ u = 0 → u = 0) →
      Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0 →
      ∃ X : Matrix (Fin n) (Fin n) k, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det := by
  intro k _ c _ _ n S hSu hS A C hinj hiso
  suffices H : ∀ m : ℕ, ∀ A : Matrix (Fin n) (Fin n) k,
      Module.finrank k (LinearMap.ker A.mulVecLin) < m →
      (∀ u : Fin n → k, A *ᵥ u = 0 → C *ᵥ u = 0 → u = 0) →
      Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0 →
      ∃ X : Matrix (Fin n) (Fin n) k, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det from
    H _ A (Nat.lt_succ_self _) hinj hiso
  intro m
  induction m with
  | zero => intro A h; exact absurd h (Nat.not_lt_zero _)
  | succ m ih =>
    intro A hm hinj hiso
    by_cases hdet : IsUnit A.det
    · exact ⟨0, by simp, by simpa using hdet⟩
    · have hd : A.det = 0 := by simpa [isUnit_iff_ne_zero] using hdet
      obtain ⟨u, hu0, hu⟩ := exists_mulVec_eq_zero_iff.mpr hd
      obtain ⟨j, hker, hne⟩ := lagr_step c S hSu A C hinj hiso u hu0 hu
      have hX1 := lagrRankOne_adm c S hS j
      have hlt : LinearMap.ker (A + lagrRankOne S j * C).mulVecLin <
          LinearMap.ker A.mulVecLin := by
        refine lt_of_le_of_ne ?_ ?_
        · intro w hw
          simp only [LinearMap.mem_ker, mulVecLin_apply] at hw ⊢
          exact hker w hw
        · intro heq
          apply hne
          have hmem : u ∈ LinearMap.ker A.mulVecLin := by
            simpa [LinearMap.mem_ker, mulVecLin_apply] using hu
          rw [← heq] at hmem
          rw [LinearMap.mem_ker, mulVecLin_apply] at hmem
          exact hmem
      have hfin := Submodule.finrank_lt_finrank_of_lt hlt
      have hinj' : ∀ w : Fin n → k, (A + lagrRankOne S j * C) *ᵥ w = 0 → C *ᵥ w = 0 → w = 0 := by
        intro w h1 h2
        apply hinj w _ h2
        rw [add_mulVec, ← mulVec_mulVec, h2, mulVec_zero, add_zero] at h1
        exact h1
      obtain ⟨X2, hX2, hdet2⟩ := ih (A + lagrRankOne S j * C) (by omega) hinj'
        (lagr_iso_update c S A C _ hX1 hiso)
      refine ⟨lagrRankOne S j + X2, transpose_mul_add_mul_map_eq_zero_add c S _ _ hX1 hX2, ?_⟩
      rwa [Matrix.add_mul, ← add_assoc]

end GlobalTheory
