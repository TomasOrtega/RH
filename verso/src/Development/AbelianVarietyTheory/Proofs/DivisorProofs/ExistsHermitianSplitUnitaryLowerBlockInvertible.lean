import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

section Transverse

variable {k : Type} [Field k] {ν : Type} [Fintype ν] [DecidableEq ν]

/- English proof (translation)
Establish `h` using `congrArg (fun M => u ⬝ᵥ (M *ᵥ (c ∘ w))) hiso`. Simplify using `only [add_mulVec, dotProduct_add, dotProduct_mulVec, zero_mulVec, dotProduct_zero] at h`. Establish `e1 : u ᵥ* (Aᵀ * S * C.map c) = 0`. Rewrite using `[← vecMul_vecMul, ← vecMul_vecMul, vecMul_transpose, hu, zero_vecMul, zero_vecMul]`. Establish `e2 : u ᵥ* (Cᵀ * S * A.map c) ⬝ᵥ (c ∘ w) = ((C *ᵥ u) ᵥ* S) ⬝ᵥ (c ∘ (A *ᵥ w))`.

Rewrite using `[← vecMul_vecMul, ← dotProduct_mulVec, ← vecMul_vecMul, vecMul_transpose]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `(RingHom.map_mulVec c A w i).symm`. Rewrite `h` using `[e1, zero_dotProduct, zero_add, e2]`.

Conclude with `h`.
-/
theorem transv_kills (c : k →+* k) (S A C : Matrix ν ν k)
    (hiso : Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0)
    (u : ν → k) (hu : A *ᵥ u = 0) (w : ν → k) :
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

def transvRankOne (S : Matrix ν ν k) (j : ν) : Matrix ν ν k :=
  Matrix.of fun a b => if a = j then S b j else 0

/- English proof (translation)
Use extensionality with `a b`. Establish `h1 : c (S b j) = - S j b`. Establish `h2 : Sᵀ b j = (-S.map c) b j` using `by rw [hS]`. Rewrite `h2` using `[transpose_apply, Matrix.neg_apply, Matrix.map_apply]`. Rewrite using `[h2, neg_neg]`.

Establish `h3 : ∀ l, c (if l = j then S b j else 0) = if l = j then c (S b j) else 0`. Apply the tactic sequence `intro l; split_ifs <;> simp`. Simplify using `[Matrix.mul_apply, transvRankOne, h3, h1]`.
-/
theorem transvRankOne_adm (c : k →+* k) (S : Matrix ν ν k) (hS : Sᵀ = -S.map c) (j : ν) :
    (transvRankOne S j)ᵀ * S + S * (transvRankOne S j).map c = 0 := by
  ext a b
  have h1 : c (S b j) = - S j b := by
    have h2 : Sᵀ b j = (-S.map c) b j := by rw [hS]
    rw [transpose_apply, Matrix.neg_apply, Matrix.map_apply] at h2
    rw [h2, neg_neg]
  have h3 : ∀ l, c (if l = j then S b j else 0) = if l = j then c (S b j) else 0 := by
    intro l; split_ifs <;> simp
  simp [Matrix.mul_apply, transvRankOne, h3, h1]

/- English proof (translation)
Use function extensionality and compare the values at `a`. Distinguish the cases in `h : a = j`. Substitute `h` using the available equality. Simplify using `[transvRankOne, mulVec, vecMul, dotProduct, mul_comm]`. Simplify using `[transvRankOne, mulVec, dotProduct, h]`.
-/
theorem transvRankOne_mulVec (S : Matrix ν ν k) (j : ν) (v : ν → k) :
    transvRankOne S j *ᵥ v = Pi.single j ((v ᵥ* S) j) := by
  funext a
  by_cases h : a = j
  · subst h; simp [transvRankOne, mulVec, vecMul, dotProduct, mul_comm]
  · simp [transvRankOne, mulVec, dotProduct, h]

/- English proof (translation)
Establish `hx : C *ᵥ u ≠ 0` using `fun h => hu0 (hinj u hu h)`. Establish `hxS : (C *ᵥ u) ᵥ* S ≠ 0`. Introduce `h`. Establish `hI : Function.Injective fun v : ν → k => v ᵥ* S` using `vecMul_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det S).mpr hSu)`. Apply `hx` to reduce the goal to its premises.

Apply `hI` to reduce the goal to its premises. Simplify using `only [h, zero_vecMul]`. Take `⟨j, hj⟩` from `Function.ne_iff.mp hxS`. Simplify using `only [Pi.zero_apply] at hj`. Use `⟨j, ?_, ?_⟩` and prove the remaining obligations.

Introduce `w hw`. Rewrite `hw` using `[add_mulVec, ← mulVec_mulVec, transvRankOne_mulVec]`. Use `set t := ((C *ᵥ w) ᵥ* S) j with ht`. Establish `hAw : A *ᵥ w = - Pi.single j t` using `eq_neg_of_add_eq_zero_left hw`. Establish `hφ` using `transv_kills c S A C hiso u hu w`.

Establish `hc : (c ∘ (A *ᵥ w)) = Pi.single j (-(c t))`. Rewrite using `[hAw]`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = j`. Substitute `hi` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[hi]`. Rewrite `hφ` using `[hc, dotProduct_single]`. Establish `hct : c t = 0`. Break down `mul_eq_zero.mp hφ with h | h` into its components or cases.

Conclude with `absurd h hj`. Conclude with `neg_eq_zero.mp h`. Establish `ht0 : t = 0` using `(map_eq_zero c).mp hct`. Rewrite using `[hAw, ht0, Pi.single_zero, neg_zero]`. Rewrite using `[add_mulVec, ← mulVec_mulVec, transvRankOne_mulVec, hu, zero_add]`.

Introduce `h`. Use `congrFun h j` as an intermediate fact. Simplify using `only [Pi.single_eq_same, Pi.zero_apply] at this`. Conclude with `hj this`.
-/
theorem transv_step (c : k →+* k) (S : Matrix ν ν k) (hSu : IsUnit S.det) (A C : Matrix ν ν k)
    (hinj : ∀ u : ν → k, A *ᵥ u = 0 → C *ᵥ u = 0 → u = 0)
    (hiso : Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0)
    (u : ν → k) (hu0 : u ≠ 0) (hu : A *ᵥ u = 0) :
    ∃ j : ν, (∀ w, (A + transvRankOne S j * C) *ᵥ w = 0 → A *ᵥ w = 0) ∧
      (A + transvRankOne S j * C) *ᵥ u ≠ 0 := by
  have hx : C *ᵥ u ≠ 0 := fun h => hu0 (hinj u hu h)
  have hxS : (C *ᵥ u) ᵥ* S ≠ 0 := by
    intro h
    have hI : Function.Injective fun v : ν → k => v ᵥ* S :=
      vecMul_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det S).mpr hSu)
    apply hx
    apply hI
    simp only [h, zero_vecMul]
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hxS
  simp only [Pi.zero_apply] at hj
  refine ⟨j, ?_, ?_⟩
  · intro w hw
    rw [add_mulVec, ← mulVec_mulVec, transvRankOne_mulVec] at hw
    set t := ((C *ᵥ w) ᵥ* S) j with ht
    have hAw : A *ᵥ w = - Pi.single j t := eq_neg_of_add_eq_zero_left hw
    have hφ := transv_kills c S A C hiso u hu w
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
  · rw [add_mulVec, ← mulVec_mulVec, transvRankOne_mulVec, hu, zero_add]
    intro h
    have := congrFun h j
    simp only [Pi.single_eq_same, Pi.zero_apply] at this
    exact hj this

/- English proof (translation)
Establish `e : (A + X * C)ᵀ * S * C.map c + Cᵀ * S * (A + X * C).map c = (Aᵀ * S * C.map c + Cᵀ * S * A.map c) + Cᵀ * (Xᵀ * S + S * X.map c) * C.map c`. Rewrite using `[Matrix.map_add c (map_add c)]`. Simplify using `only [transpose_add, transpose_mul, Matrix.map_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws. Rewrite using `[e, hiso, hX, Matrix.mul_zero, Matrix.zero_mul, add_zero]`.
-/
theorem transv_iso_update (c : k →+* k) (S A C X : Matrix ν ν k)
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
theorem skewAdmissibleMatrix_add (c : k →+* k) (S X Y : Matrix ν ν k)
    (hX : Xᵀ * S + S * X.map c = 0) (hY : Yᵀ * S + S * Y.map c = 0) :
    (X + Y)ᵀ * S + S * (X + Y).map c = 0 := by
  have e : (X + Y)ᵀ * S + S * (X + Y).map c = (Xᵀ * S + S * X.map c) + (Yᵀ * S + S * Y.map c) := by
    rw [Matrix.map_add c (map_add c)]
    simp only [transpose_add, Matrix.mul_add, Matrix.add_mul]
    abel
  rw [e, hX, hY, add_zero]

/- English proof (translation)
It suffices to establish `H : ∀ m : ℕ, ∀ A : Matrix ν ν k, Module.finrank k (LinearMap.ker A.mulVecLin) < m → (∀ u : ν → k, A *ᵥ u = 0 → C *ᵥ u = 0 → u = 0) → Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0 → ∃ X : Matrix ν ν k, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det from H _ A (Nat.lt_succ_self _) hin …`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro A h`. Conclude with `absurd h (Nat.not_lt_zero _)`.

Consider the case `succ m ih`. Introduce `A hm hinj hiso`. Distinguish the cases in `hdet : IsUnit A.det`. Conclude with `⟨0, by simp, by simpa using hdet⟩`. Establish `hd : A.det = 0` using `by simpa [isUnit_iff_ne_zero] using hdet`.

Take `⟨u, hu0, hu⟩` from `exists_mulVec_eq_zero_iff.mpr hd`. Take `⟨j, hker, hne⟩` from `transv_step c S hSu A C hinj hiso u hu0 hu`. Establish `hX1` using `transvRankOne_adm c S hS j`. Establish `hlt : LinearMap.ker (A + transvRankOne S j * C).mulVecLin < LinearMap.ker A.mulVecLin`. Use `lt_of_le_of_ne ?_ ?_` and prove the remaining obligations.

Introduce `w hw`. Simplify using `only [LinearMap.mem_ker, mulVecLin_apply] at hw ⊢`. Conclude with `hker w hw`. Introduce `heq`. Apply `hne` to reduce the goal to its premises.

Establish `hmem : u ∈ LinearMap.ker A.mulVecLin`. Simplify `hu` using `[LinearMap.mem_ker, mulVecLin_apply]`. Rewrite `hmem` using `[← heq]`. Rewrite `hmem` using `[LinearMap.mem_ker, mulVecLin_apply]`. Conclude with `hmem`.

Establish `hfin` using `Submodule.finrank_lt_finrank_of_lt hlt`. Establish `hinj' : ∀ w : ν → k, (A + transvRankOne S j * C) *ᵥ w = 0 → C *ᵥ w = 0 → w = 0`. Introduce `w h1 h2`. Apply `hinj w _ h2` to reduce the goal to its premises. Rewrite `h1` using `[add_mulVec, ← mulVec_mulVec, h2, mulVec_zero, add_zero]`.

Conclude with `h1`. Take `⟨X2, hX2, hdet2⟩` from `ih (A + transvRankOne S j * C) (by omega) hinj' (transv_iso_update c S A C _ hX1 hiso)`. Use `⟨transvRankOne S j + X2, skewAdmissibleMatrix_add c S _ _ hX1 hX2, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.add_mul, ← add_assoc]` and apply the resulting hypothesis.
-/
theorem transv_field (c : k →+* k) (S : Matrix ν ν k) (hSu : IsUnit S.det) (hS : Sᵀ = -S.map c)
    (A C : Matrix ν ν k) (hinj : ∀ u : ν → k, A *ᵥ u = 0 → C *ᵥ u = 0 → u = 0)
    (hiso : Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0) :
    ∃ X : Matrix ν ν k, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det := by
  suffices H : ∀ m : ℕ, ∀ A : Matrix ν ν k,
      Module.finrank k (LinearMap.ker A.mulVecLin) < m →
      (∀ u : ν → k, A *ᵥ u = 0 → C *ᵥ u = 0 → u = 0) →
      Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0 →
      ∃ X : Matrix ν ν k, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det from
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
      obtain ⟨j, hker, hne⟩ := transv_step c S hSu A C hinj hiso u hu0 hu
      have hX1 := transvRankOne_adm c S hS j
      have hlt : LinearMap.ker (A + transvRankOne S j * C).mulVecLin <
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
      have hinj' : ∀ w : ν → k, (A + transvRankOne S j * C) *ᵥ w = 0 → C *ᵥ w = 0 → w = 0 := by
        intro w h1 h2
        apply hinj w _ h2
        rw [add_mulVec, ← mulVec_mulVec, h2, mulVec_zero, add_zero] at h1
        exact h1
      obtain ⟨X2, hX2, hdet2⟩ := ih (A + transvRankOne S j * C) (by omega) hinj'
        (transv_iso_update c S A C _ hX1 hiso)
      refine ⟨transvRankOne S j + X2, skewAdmissibleMatrix_add c S _ _ hX1 hX2, ?_⟩
      rwa [Matrix.add_mul, ← add_assoc]

end Transverse

end GlobalTheory.KSp

namespace GlobalTheory.KSp

/- English proof (translation)
Introduce `F _ _ E _ _ c δ hE ν _ _ g`. Establish `hδ : δ ≠ 0` using `hE.unit.ne_zero`. Use `set M := mat c g with hMdef`. Use `set cc := M.toBlocks₂₁`. Use `set dd := M.toBlocks₂₂`.

Establish `hU` using `(mem_UG_iff c _).mp g.2`. Express the relevant statement in the definitionally equal form `M * stdJ ν E * (M.map c)ᵀ = stdJ ν E at hU`. Establish `key : cc * (dd.map c)ᵀ = dd * (cc.map c)ᵀ`. Establish `h` using `congrArg Matrix.toBlocks₂₂ hU`. Rewrite `h` using `[← fromBlocks_toBlocks M]`.

Simplify using `only [stdJ, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, toBlocks_fromBlocks₂₂] at h`. Simplify using `only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero, Matrix.neg_mul] at h`. Establish `h' : cc * (dd.map c)ᵀ + -(dd * (cc.map c)ᵀ) = 0` using `by rw [← h]; abel`. Conclude with `eq_of_sub_eq_zero (by rw [sub_eq_add_neg]; exact h')`. Use `set S : Matrix ν ν E := δ • (1 : Matrix ν ν E)`.

Establish `hcδ : c δ = -δ` using `hE.anti`. Establish `hSu : IsUnit S.det`. Rewrite using `[isUnit_iff_ne_zero]`. Simplify using `[S, Matrix.det_smul, hδ]`. Establish `hS : Sᵀ = -S.map (c : E →+* E)`.

Apply the tactic sequence `ext i j; by_cases h : i = j <;> simp [S, Matrix.one_apply, h, hcδ, eq_comm]`. Establish `hmapC : (δ • ddᵀ).map (c : E →+* E) = (-δ) • (dd.map c)ᵀ`. Use extensionality with `i j`. Simplify using `[hcδ]`. Establish `hiso : (ccᵀ)ᵀ * S * (δ • ddᵀ).map (c : E →+* E) + (δ • ddᵀ)ᵀ * S * (ccᵀ).map (c : E →+* E) = 0`.

Rewrite using `[hmapC]`. Establish `e1 : (ccᵀ).map (c : E →+* E) = (cc.map c)ᵀ` using `rfl`. Rewrite using `[e1]`. Simplify using `only [S, transpose_transpose, transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul, key]`. Rewrite using `[← add_smul]`.

Simplify using the standard rewrite rules. Establish `hinj : ∀ u : ν → E, ccᵀ *ᵥ u = 0 → (δ • ddᵀ) *ᵥ u = 0 → u = 0`. Introduce `u h1 h2`. Rewrite `h1` using `[mulVec_transpose]`. Rewrite `h2` using `[smul_mulVec, mulVec_transpose, smul_eq_zero]`.

Establish `h2' : u ᵥ* dd = 0` using `h2.resolve_left hδ`. Establish `hw : (Sum.elim 0 u : ν ⊕ ν → E) ᵥ* M = 0`. Rewrite using `[← fromBlocks_toBlocks M]`. Use function extensionality and compare the values at `i`. Break down `i with i | i` into its components or cases.

Use `congrFun h1 i` as an intermediate fact. Simplify `this` using `[vecMul, dotProduct, fromBlocks, Fintype.sum_sum_type, cc]`. Use `congrFun h2' i` as an intermediate fact. Simplify `this` using `[vecMul, dotProduct, fromBlocks, Fintype.sum_sum_type, dd]`. Establish `hinv : M * ((g⁻¹ : UG c (stdJ ν E)) : GL (ν ⊕ ν) E) = 1`.

Express the relevant statement in the definitionally equal form `(((g * g⁻¹ : UG c (stdJ ν E)) : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) = 1`. Rewrite using `[mul_inv_cancel]`. Both sides reduce to the same expression. Establish `hw0 : (Sum.elim 0 u : ν ⊕ ν → E) = 0`. Rewrite using `[← vecMul_one (Sum.elim 0 u : ν ⊕ ν → E), ← hinv, ← vecMul_vecMul, hw, zero_vecMul]`.

Use function extensionality and compare the values at `i`. Simplify using `using congrFun hw0 (Sum.inr i)`. Take `⟨X, hX, hdet⟩` from `transv_field (c : E →+* E) S hSu hS ccᵀ (δ • ddᵀ) hinj hiso`. Use `⟨δ • Xᵀ, ?_, ?_⟩` and prove the remaining obligations. Establish `hX' : δ • Xᵀ + δ • X.map (c : E →+* E) = 0`.

Simplify `hX` using `[S, Matrix.mul_smul, Matrix.smul_mul]`. Rewrite `hX'` using `[← smul_add, smul_eq_zero]`. Establish `hX'' : X.map (c : E →+* E) = -Xᵀ` using `eq_neg_of_add_eq_zero_right (hX'.resolve_left hδ)`. Establish `e : (δ • Xᵀ).map c = (-δ) • (X.map (c : E →+* E))ᵀ` using `by ext i j; simp [hcδ]`. Rewrite using `[e, hX'']`.

Simplify using the standard rewrite rules. Establish `e : (ccᵀ + X * (δ • ddᵀ))ᵀ = cc + dd * (δ • Xᵀ)`. Simplify using `[transpose_add, transpose_mul, Matrix.mul_smul, Matrix.smul_mul]`. Rewrite using `[← e, det_transpose]`. Conclude with `(isUnit_iff_ne_zero).mp hdet`.
-/
theorem exists_herm_transverse : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E)
    (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (g : UG c (stdJ ν E)),
    ∃ t : Matrix ν ν E, (t.map c)ᵀ = t ∧ ((mat c g).toBlocks₂₁ + (mat c g).toBlocks₂₂ * t).det ≠ 0 := by
  intro F _ _ E _ _ c δ hE ν _ _ g
  have hδ : δ ≠ 0 := hE.unit.ne_zero
  set M := mat c g with hMdef
  set cc := M.toBlocks₂₁
  set dd := M.toBlocks₂₂
  have hU := (mem_UG_iff c _).mp g.2
  change M * stdJ ν E * (M.map c)ᵀ = stdJ ν E at hU
  have key : cc * (dd.map c)ᵀ = dd * (cc.map c)ᵀ := by
    have h := congrArg Matrix.toBlocks₂₂ hU
    rw [← fromBlocks_toBlocks M] at h
    simp only [stdJ, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, toBlocks_fromBlocks₂₂] at h
    simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero, Matrix.neg_mul] at h
    have h' : cc * (dd.map c)ᵀ + -(dd * (cc.map c)ᵀ) = 0 := by rw [← h]; abel
    exact eq_of_sub_eq_zero (by rw [sub_eq_add_neg]; exact h')

  set S : Matrix ν ν E := δ • (1 : Matrix ν ν E)
  have hcδ : c δ = -δ := hE.anti
  have hSu : IsUnit S.det := by
    rw [isUnit_iff_ne_zero]; simp [S, Matrix.det_smul, hδ]
  have hS : Sᵀ = -S.map (c : E →+* E) := by
    ext i j; by_cases h : i = j <;> simp [S, Matrix.one_apply, h, hcδ, eq_comm]
  have hmapC : (δ • ddᵀ).map (c : E →+* E) = (-δ) • (dd.map c)ᵀ := by
    ext i j; simp [hcδ]
  have hiso : (ccᵀ)ᵀ * S * (δ • ddᵀ).map (c : E →+* E) + (δ • ddᵀ)ᵀ * S * (ccᵀ).map (c : E →+* E) = 0 := by
    rw [hmapC]
    have e1 : (ccᵀ).map (c : E →+* E) = (cc.map c)ᵀ := rfl
    rw [e1]
    simp only [S, transpose_transpose, transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul, key]
    rw [← add_smul]; simp
  have hinj : ∀ u : ν → E, ccᵀ *ᵥ u = 0 → (δ • ddᵀ) *ᵥ u = 0 → u = 0 := by
    intro u h1 h2
    rw [mulVec_transpose] at h1
    rw [smul_mulVec, mulVec_transpose, smul_eq_zero] at h2
    have h2' : u ᵥ* dd = 0 := h2.resolve_left hδ
    have hw : (Sum.elim 0 u : ν ⊕ ν → E) ᵥ* M = 0 := by
      rw [← fromBlocks_toBlocks M]
      funext i
      rcases i with i | i
      · have := congrFun h1 i
        simpa [vecMul, dotProduct, fromBlocks, Fintype.sum_sum_type, cc] using this
      · have := congrFun h2' i
        simpa [vecMul, dotProduct, fromBlocks, Fintype.sum_sum_type, dd] using this
    have hinv : M * ((g⁻¹ : UG c (stdJ ν E)) : GL (ν ⊕ ν) E) = 1 := by
      change (((g * g⁻¹ : UG c (stdJ ν E)) : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) = 1
      rw [mul_inv_cancel]; rfl
    have hw0 : (Sum.elim 0 u : ν ⊕ ν → E) = 0 := by
      rw [← vecMul_one (Sum.elim 0 u : ν ⊕ ν → E), ← hinv, ← vecMul_vecMul, hw, zero_vecMul]
    funext i
    simpa using congrFun hw0 (Sum.inr i)
  obtain ⟨X, hX, hdet⟩ := transv_field (c : E →+* E) S hSu hS ccᵀ (δ • ddᵀ) hinj hiso
  refine ⟨δ • Xᵀ, ?_, ?_⟩
  · have hX' : δ • Xᵀ + δ • X.map (c : E →+* E) = 0 := by
      simpa [S, Matrix.mul_smul, Matrix.smul_mul] using hX
    rw [← smul_add, smul_eq_zero] at hX'
    have hX'' : X.map (c : E →+* E) = -Xᵀ := eq_neg_of_add_eq_zero_right (hX'.resolve_left hδ)
    have e : (δ • Xᵀ).map c = (-δ) • (X.map (c : E →+* E))ᵀ := by ext i j; simp [hcδ]
    rw [e, hX'']
    simp
  · have e : (ccᵀ + X * (δ • ddᵀ))ᵀ = cc + dd * (δ • Xᵀ) := by
      simp [transpose_add, transpose_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [← e, det_transpose]
    exact (isUnit_iff_ne_zero).mp hdet

end GlobalTheory.KSp
