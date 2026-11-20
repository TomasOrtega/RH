import Mathlib
import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
import Formalism.GL3MeanSquares.HookFormulaTorsion.DimensionMassJointBound

noncomputable section

open Matrix Finset IsDedekindDomain NumberField

namespace Formalism.L2.Col

/- English proof (translation)
Rewrite using `[List.sum_replicate, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem add_add_sum_replicate_eq_add_mul_succ (k t j : ℕ) : (k + j) + (List.replicate j t).sum = k + j * (t + 1) := by
  rw [List.sum_replicate, smul_eq_mul]; ring

/- English proof (translation)
Rewrite using `[List.sum_replicate, smul_eq_mul]`.
-/
theorem add_sum_replicate_eq_add_mul (r t j : ℕ) : r + (List.replicate j t).sum = r + j * t := by
  rw [List.sum_replicate, smul_eq_mul]

/- English proof (translation)
Proceed by induction on `j generalizing i with`. Consider the case `zero => simp only [List.replicate_zero, blkIdx]`. Consider the case `succ j ih`. Rewrite using `[List.replicate_succ]`. Simplify using `only [blkIdx]`.

Rewrite `h` using `[Nat.add_mul, one_mul]`. Rewrite using `[if_neg (by omega), ih (i - t) (by omega)]`.
-/
theorem blkIdx_replicate_of_le (t j i : ℕ) (h : j * t ≤ i) : blkIdx (List.replicate j t) i = j := by
  induction j generalizing i with
  | zero => simp only [List.replicate_zero, blkIdx]
  | succ j ih =>
    rw [List.replicate_succ]
    simp only [blkIdx]
    rw [Nat.add_mul, one_mul] at h
    rw [if_neg (by omega), ih (i - t) (by omega)]

/- English proof (translation)
Proceed by induction on `j generalizing i with`. Consider the case `zero => simp at h`. Consider the case `succ j ih`. Rewrite using `[List.replicate_succ]`. Simplify using `only [blkIdx]`.

Rewrite `h` using `[Nat.add_mul, one_mul]`. Use `split_ifs with hit`. Use linear arithmetic over natural numbers and integers. Use `ih (i - t) (by omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem blkIdx_replicate_lt (t j i : ℕ) (h : i < j * t) : blkIdx (List.replicate j t) i < j := by
  induction j generalizing i with
  | zero => simp at h
  | succ j ih =>
    rw [List.replicate_succ]
    simp only [blkIdx]
    rw [Nat.add_mul, one_mul] at h
    split_ifs with hit
    · omega
    · have := ih (i - t) (by omega)
      omega

section

variable {n : ℕ} {κ : Type} [CommRing κ] {K : Type} [Field K]

/- English proof (translation)
Unfold `SX`. Use extensionality with `i`. Simplify using `only [Finset.mem_filter, Finset.mem_range, add_zero]`. Prove the components needed by the constructor for the conclusion. Conclude with `fun h => h.1`.

Introduce `h; exact ⟨h, Or.inl (by omega)⟩`.
-/
theorem SX_zero (k m : ℕ) : SX k m 0 = Finset.range (k - 1) := by
  unfold SX
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, add_zero]
  constructor
  · exact fun h => h.1
  · intro h; exact ⟨h, Or.inl (by omega)⟩

/- English proof (translation)
Unfold `SX`. Use extensionality with `i`. Simplify using the standard rewrite rules.
-/
theorem SX_top (k j : ℕ) : SX k (j + 1) j = Finset.range (k + j - 1) := by
  unfold SX
  ext i
  simp

/- English proof (translation)
Unfold `lamGen detChar`. Simplify using the standard rewrite rules.
-/
theorem lamGen_nil (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (n a : ℕ) (S : Finset ℕ) :
    lamGen ψ χ n a [] S = supChar ψ n a [] S := by
  unfold lamGen detChar
  simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem HX_zero (k t : ℕ) : HX κ k k t 0 = HU κ k := rfl

/- English proof (translation)
Unfold `lamX psiU`. Rewrite using `[SX_zero]`. Conclude with `lamGen_nil ψ χ k k _`.
-/
theorem lamX_zero (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (k m t : ℕ) : lamX ψ χ k k m t 0 = psiU ψ k := by
  unfold lamX psiU
  rw [SX_zero]
  exact lamGen_nil ψ χ k k _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem HX_top (n k t j : ℕ) : HX κ n k t j = HJ κ n (k + j) t j := rfl

/- English proof (translation)
Unfold `lamX lamJ`. Rewrite using `[SX_top]`.
-/
theorem lamX_top (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (n k t j : ℕ) : lamX ψ χ n k (j + 1) t j = lamJ ψ χ n (k + j) t j := by
  unfold lamX lamJ
  rw [SX_top]

/- English proof (translation)
Unfold `lamJ psiU`. Conclude with `lamGen_nil ψ χ r r _`.
-/
theorem lamJ_zero (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (r t : ℕ) : lamJ ψ χ r r t 0 = psiU ψ r := by
  unfold lamJ psiU
  exact lamGen_nil ψ χ r r _

/- English proof (translation)
Establish `hv : ((diagEmb κ h g : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) = diagMat s n (g : Matrix (Fin s) (Fin s) κ)` using `rfl`. Take `⟨h1, h2⟩` from `hg`. Use `show diagEmb κ h g ∈ btG n κ (fine a bl) ∧ ∀ i : Fin n, i.val < a → ((diagEmb κ h g : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) i i = 1`. Use `⟨?_, fun i hi => ?_⟩` and prove the remaining obligations. Use `show ((diagEmb κ h g : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).BlockTriangular (fun i => fine a bl i.val)`.

Introduce `i j hij`. Rewrite using `[hv]`. Simplify using `only [diagMat]`. Use `split_ifs with hs`. Conclude with `h1 (i := ⟨i.val, hs.1⟩) (j := ⟨j.val, hs.2⟩) hij`.

Conclude with `Matrix.one_apply_ne (fun e => by subst e; exact lt_irrefl _ hij)`. Rewrite using `[hv]`. Simplify using `only [diagMat]`. Use `split_ifs with hs`. Conclude with `h2 ⟨i.val, hs.1⟩ hi`.

Conclude with `Matrix.one_apply_eq i`.
-/
theorem diagEmb_mem_uniUT {s : ℕ} (h : s ≤ n) {a : ℕ} {bl : List ℕ} {g : GL (Fin s) κ} (hg : g ∈ uniUT s κ a bl) :
    diagEmb κ h g ∈ uniUT n κ a bl := by
  have hv : ((diagEmb κ h g : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) = diagMat s n (g : Matrix (Fin s) (Fin s) κ) := rfl
  obtain ⟨h1, h2⟩ := hg
  show diagEmb κ h g ∈ btG n κ (fine a bl) ∧ ∀ i : Fin n, i.val < a → ((diagEmb κ h g : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) i i = 1
  refine ⟨?_, fun i hi => ?_⟩
  · show ((diagEmb κ h g : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).BlockTriangular (fun i => fine a bl i.val)
    intro i j hij
    rw [hv]
    simp only [diagMat]
    split_ifs with hs
    · exact h1 (i := ⟨i.val, hs.1⟩) (j := ⟨j.val, hs.2⟩) hij
    · exact Matrix.one_apply_ne (fun e => by subst e; exact lt_irrefl _ hij)
  · rw [hv]
    simp only [diagMat]
    split_ifs with hs
    · exact h2 ⟨i.val, hs.1⟩ hi
    · exact Matrix.one_apply_eq i

/- English proof (translation)
Use `show ∀ i j : Fin n, j.val = c → ((diagEmb κ h g : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) i j = (1 : Matrix (Fin n) (Fin n) κ) i j`. Introduce `i j hj`. Use `show diagMat s n (g : Matrix (Fin s) (Fin s) κ) i j = (1 : Matrix (Fin n) (Fin n) κ) i j`. Simplify using `only [diagMat]`. Use `split_ifs with hs`.

Conclude with `absurd hs.2 (by omega)`. Both sides reduce to the same expression.
-/
theorem diagEmb_mem_fixCol {s : ℕ} (h : s ≤ n) {c : ℕ} (hc : s ≤ c) (g : GL (Fin s) κ) : diagEmb κ h g ∈ fixCol n κ c := by
  show ∀ i j : Fin n, j.val = c → ((diagEmb κ h g : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) i j = (1 : Matrix (Fin n) (Fin n) κ) i j
  intro i j hj
  show diagMat s n (g : Matrix (Fin s) (Fin s) κ) i j = (1 : Matrix (Fin n) (Fin n) κ) i j
  simp only [diagMat]
  split_ifs with hs
  · exact absurd hs.2 (by omega)
  · rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply]`. Rewrite using `[Fin.sum_univ_castSucc, hA i, zero_mul, add_zero]`.
-/
theorem sub_mul {s : ℕ} (A B : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) (hA : ∀ i : Fin s, A i.castSucc (Fin.last s) = 0) :
    (A * B).submatrix Fin.castSucc Fin.castSucc = A.submatrix Fin.castSucc Fin.castSucc * B.submatrix Fin.castSucc Fin.castSucc := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [Fin.sum_univ_castSucc, hA i, zero_mul, add_zero]

/- English proof (translation)
Establish `hcol : ∀ i : Fin (s + 1), (M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) i (Fin.last s) = (1 : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) i (Fin.last s)` using `fun i => hc i (Fin.last s) rfl`. Establish `hc' : M⁻¹ ∈ fixCol (s + 1) κ s` using `Subgroup.inv_mem _ hc`. Establish `hcol' : ∀ i : Fin (s + 1), ((M⁻¹ : GL (Fin (s + 1)) κ) : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) i (Fin.last s) = (1 : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) i (Fin.last s)` using `fun i => hc' i (Fin.last s) rfl`. Establish `hA : ∀ i : Fin s, (M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) i.castSucc (Fin.last s) = 0`. Introduce `i`.

Rewrite using `[hcol, Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne]`. Establish `hA' : ∀ i : Fin s, ((M⁻¹ : GL (Fin (s + 1)) κ) : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) i.castSucc (Fin.last s) = 0`. Introduce `i`. Rewrite using `[hcol', Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne]`. Establish `hmul : (M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ).submatrix Fin.castSucc Fin.castSucc * ((M⁻¹ : GL (Fin (s + 1)) κ) : Matrix (Fin (s + 1)) (Fin (s + 1)) κ).submatrix Fin.castSucc Fin.castSucc = 1`.

Rewrite using `[← Formalism.L2.Col.sub_mul _ _ hA, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.submatrix_one _ (Fin.castSucc_injective s)]`. Establish `hmul' : ((M⁻¹ : GL (Fin (s + 1)) κ) : Matrix (Fin (s + 1)) (Fin (s + 1)) κ).submatrix Fin.castSucc Fin.castSucc * (M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ).submatrix Fin.castSucc Fin.castSucc = 1`. Rewrite using `[← Formalism.L2.Col.sub_mul _ _ hA', ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.submatrix_one _ (Fin.castSucc_injective s)]`. Use `⟨⟨_, _, hmul, hmul'⟩, ?_, fun i j => rfl⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises.

Use extensionality with `i j`. Use `show diagMat s (s + 1) ((M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ).submatrix Fin.castSucc Fin.castSucc) i j = (M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) i j`. Simplify using `only [diagMat]`. Use `split_ifs with hs`. Both sides reduce to the same expression.

Establish `hi2` using `i.2`. Establish `hj2` using `j.2`. Distinguish the cases in `hj : j.val = s`. Establish `hjl : j = Fin.last s` using `Fin.ext hj`. Substitute `hjl` using the available equality.

Conclude with `(hcol i).symm`. Establish `hil : i = Fin.last s` using `Fin.ext (by simp only [Fin.val_last]; omega)`. Substitute `hil` using the available equality. Rewrite using `[hr j (by omega)]`. Conclude with `Matrix.one_apply_ne (fun e => hj (by rw [← e]; rfl))`.
-/
theorem exists_diagEmb {s : ℕ} (M : GL (Fin (s + 1)) κ) (hc : M ∈ fixCol (s + 1) κ s)
    (hr : ∀ j : Fin (s + 1), j.val < s → (M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) (Fin.last s) j = 0) :
    ∃ g : GL (Fin s) κ, diagEmb κ (Nat.le_succ s) g = M ∧
      ∀ i j : Fin s, (g : Matrix (Fin s) (Fin s) κ) i j = (M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) i.castSucc j.castSucc := by
  have hcol : ∀ i : Fin (s + 1), (M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) i (Fin.last s) = (1 : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) i (Fin.last s) :=
    fun i => hc i (Fin.last s) rfl
  have hc' : M⁻¹ ∈ fixCol (s + 1) κ s := Subgroup.inv_mem _ hc
  have hcol' : ∀ i : Fin (s + 1), ((M⁻¹ : GL (Fin (s + 1)) κ) : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) i (Fin.last s) = (1 : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) i (Fin.last s) :=
    fun i => hc' i (Fin.last s) rfl
  have hA : ∀ i : Fin s, (M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) i.castSucc (Fin.last s) = 0 := by
    intro i; rw [hcol, Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne]
  have hA' : ∀ i : Fin s, ((M⁻¹ : GL (Fin (s + 1)) κ) : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) i.castSucc (Fin.last s) = 0 := by
    intro i; rw [hcol', Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne]
  have hmul : (M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ).submatrix Fin.castSucc Fin.castSucc *
      ((M⁻¹ : GL (Fin (s + 1)) κ) : Matrix (Fin (s + 1)) (Fin (s + 1)) κ).submatrix Fin.castSucc Fin.castSucc = 1 := by
    rw [← Formalism.L2.Col.sub_mul _ _ hA, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.submatrix_one _ (Fin.castSucc_injective s)]
  have hmul' : ((M⁻¹ : GL (Fin (s + 1)) κ) : Matrix (Fin (s + 1)) (Fin (s + 1)) κ).submatrix Fin.castSucc Fin.castSucc *
      (M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ).submatrix Fin.castSucc Fin.castSucc = 1 := by
    rw [← Formalism.L2.Col.sub_mul _ _ hA', ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.submatrix_one _ (Fin.castSucc_injective s)]
  refine ⟨⟨_, _, hmul, hmul'⟩, ?_, fun i j => rfl⟩
  apply Units.ext
  ext i j
  show diagMat s (s + 1) ((M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ).submatrix Fin.castSucc Fin.castSucc) i j = (M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) i j
  simp only [diagMat]
  split_ifs with hs
  · rfl
  · have hi2 := i.2
    have hj2 := j.2
    by_cases hj : j.val = s
    · have hjl : j = Fin.last s := Fin.ext hj
      subst hjl
      exact (hcol i).symm
    · have hil : i = Fin.last s := Fin.ext (by simp only [Fin.val_last]; omega)
      subst hil
      rw [hr j (by omega)]
      exact Matrix.one_apply_ne (fun e => hj (by rw [← e]; rfl))

/- English proof (translation)
Use extensionality with `M`. Prove the components needed by the constructor for the conclusion. Introduce `hM`. Take `⟨hJ, hF⟩` from `hM`. Establish `hlast : fine r (List.replicate m t) (r + m * t) = r + m`.

Unfold `fine`. Distinguish the cases in `h0 : r + m * t < r`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg h0, Nat.add_sub_cancel_left, blkIdx_replicate_of_le t m (m * t) le_rfl]`. Establish `hr : ∀ j : Fin (r + m * t + 1), j.val < r + m * t → (M : Matrix (Fin (r + m * t + 1)) (Fin (r + m * t + 1)) κ) (Fin.last (r + m * t)) j = 0`.

Introduce `j hj`. Apply `hJ.1` to reduce the goal to its premises. Use `show fine r (List.replicate m t) j.val < fine r (List.replicate m t) (Fin.last (r + m * t)).val`. Rewrite using `[Fin.val_last, hlast]`. Unfold `fine`.

Use `split_ifs with h0`. Use linear arithmetic over natural numbers and integers. Use `blkIdx_replicate_lt t m (j.val - r) (by omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨g, hg, hge⟩` from `exists_diagEmb M hF hr`.

Establish `hgm : g ∈ HJ κ (r + m * t) r t m` using `by show g ∈ btG (r + m * t) κ (fine r (List.replicate m t)) ∧ ∀ i : Fin (r + m * t), i.val < r → (g : Matrix (Fin (r + m * t)) (Fin (r + m * t)) κ) i i = 1`. Use `⟨?_, fun i hi => ?_⟩` and prove the remaining obligations. Use `show (g : Matrix (Fin (r + m * t)) (Fin (r + m * t)) κ).BlockTriangular (fun i => fine r (List.replicate m t) i.val)`. Introduce `i j hij`. Rewrite using `[hge]`.

Conclude with `hJ.1 (i := i.castSucc) (j := j.castSucc) hij`. Rewrite using `[hge]`. Conclude with `hJ.2 i.castSucc hi`. Conclude with `⟨g, hgm, hg⟩`. Introduce and unpack `⟨g, hg, rfl⟩ show diagEmb κ (Nat.le_succ (r + m * t)) g ∈ HJ κ (r + m * t + 1) r t m ⊓ fixCol (r + m * t + 1) κ (r + m * t)`.

Conclude with `Subgroup.mem_inf.mpr ⟨diagEmb_mem_uniUT _ hg, diagEmb_mem_fixCol _ le_rfl g⟩`.
-/
theorem HXm_eq_map (r t m : ℕ) :
    HXm κ (r + m * t + 1) r t m = (HJ κ (r + m * t) r t m).map (diagEmb κ (Nat.le_succ (r + m * t))) := by
  ext M
  constructor
  · intro hM
    obtain ⟨hJ, hF⟩ := hM
    have hlast : fine r (List.replicate m t) (r + m * t) = r + m := by
      unfold fine
      by_cases h0 : r + m * t < r
      · omega
      · rw [if_neg h0, Nat.add_sub_cancel_left, blkIdx_replicate_of_le t m (m * t) le_rfl]
    have hr : ∀ j : Fin (r + m * t + 1), j.val < r + m * t →
        (M : Matrix (Fin (r + m * t + 1)) (Fin (r + m * t + 1)) κ) (Fin.last (r + m * t)) j = 0 := by
      intro j hj
      apply hJ.1
      show fine r (List.replicate m t) j.val < fine r (List.replicate m t) (Fin.last (r + m * t)).val
      rw [Fin.val_last, hlast]
      unfold fine
      split_ifs with h0
      · omega
      · have := blkIdx_replicate_lt t m (j.val - r) (by omega)
        omega
    obtain ⟨g, hg, hge⟩ := exists_diagEmb M hF hr
    have hgm : g ∈ HJ κ (r + m * t) r t m := by
      show g ∈ btG (r + m * t) κ (fine r (List.replicate m t)) ∧
        ∀ i : Fin (r + m * t), i.val < r → (g : Matrix (Fin (r + m * t)) (Fin (r + m * t)) κ) i i = 1
      refine ⟨?_, fun i hi => ?_⟩
      · show (g : Matrix (Fin (r + m * t)) (Fin (r + m * t)) κ).BlockTriangular (fun i => fine r (List.replicate m t) i.val)
        intro i j hij
        rw [hge]
        exact hJ.1 (i := i.castSucc) (j := j.castSucc) hij
      · rw [hge]
        exact hJ.2 i.castSucc hi
    exact ⟨g, hgm, hg⟩
  · rintro ⟨g, hg, rfl⟩
    show diagEmb κ (Nat.le_succ (r + m * t)) g ∈ HJ κ (r + m * t + 1) r t m ⊓ fixCol (r + m * t + 1) κ (r + m * t)
    exact Subgroup.mem_inf.mpr ⟨diagEmb_mem_uniUT _ hg, diagEmb_mem_fixCol _ le_rfl g⟩

/- English proof (translation)
Establish `h1 : ∀ (X : GL (Fin (r + m * t)) κ) (i j : Fin (r + m * t)), ((diagEmb κ (Nat.le_succ (r + m * t)) X : GL (Fin (r + m * t + 1)) κ) : Matrix (Fin (r + m * t + 1)) (Fin (r + m * t + 1)) κ) i.castSucc j.castSucc = (X : Matrix (Fin (r + m * t)) (Fin (r + m * t)) κ) i j`. Introduce `X i j`. Use `show diagMat (r + m * t) (r + m * t + 1) (X : Matrix (Fin (r + m * t)) (Fin (r + m * t)) κ) i.castSucc j.castSucc = _`. Simplify using `[diagMat]`. Establish `inj : Function.Injective (diagEmb κ (Nat.le_succ (r + m * t)))`.

Introduce `g g' he`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Rewrite using `[← h1 g i j, ← h1 g' i j, he]`. Rewrite using `[HXm_eq_map, Subgroup.comap_map_eq_self_of_injective inj]`.
-/
theorem HXm_comap (r t m : ℕ) :
    (HXm κ (r + m * t + 1) r t m).comap (diagEmb κ (Nat.le_succ (r + m * t))) = HJ κ (r + m * t) r t m := by
  have h1 : ∀ (X : GL (Fin (r + m * t)) κ) (i j : Fin (r + m * t)),
      ((diagEmb κ (Nat.le_succ (r + m * t)) X : GL (Fin (r + m * t + 1)) κ) : Matrix (Fin (r + m * t + 1)) (Fin (r + m * t + 1)) κ) i.castSucc j.castSucc =
        (X : Matrix (Fin (r + m * t)) (Fin (r + m * t)) κ) i j := by
    intro X i j
    show diagMat (r + m * t) (r + m * t + 1) (X : Matrix (Fin (r + m * t)) (Fin (r + m * t)) κ) i.castSucc j.castSucc = _
    simp [diagMat]
  have inj : Function.Injective (diagEmb κ (Nat.le_succ (r + m * t))) := by
    intro g g' he
    apply Units.ext
    ext i j
    rw [← h1 g i j, ← h1 g' i j, he]
  rw [HXm_eq_map, Subgroup.comap_map_eq_self_of_injective inj]

end

section Uni

variable {n : ℕ} {κ : Type} [CommRing κ] {K : Type} [Field K]

def uMat (P : Fin n → Fin n → Prop) [∀ i j, Decidable (P i j)] (f : {p : Fin n × Fin n // P p.1 p.2} → κ) :
    Matrix (Fin n) (Fin n) κ :=
  fun i j => if i = j then 1 else if h : P i j then f ⟨(i, j), h⟩ else 0

/- English proof (translation)
Simplify using `[uMat]`.
-/
theorem uMat_diag (P : Fin n → Fin n → Prop) [∀ i j, Decidable (P i j)] (f : {p : Fin n × Fin n // P p.1 p.2} → κ) (i : Fin n) :
    uMat P f i i = 1 := by
  simp [uMat]

/- English proof (translation)
Simplify using `only [uMat, if_neg hne, dif_pos h]`.
-/
theorem uMat_pos {P : Fin n → Fin n → Prop} [∀ i j, Decidable (P i j)] (f : {p : Fin n × Fin n // P p.1 p.2} → κ) {i j : Fin n}
    (hne : i ≠ j) (h : P i j) : uMat P f i j = f ⟨(i, j), h⟩ := by
  simp only [uMat, if_neg hne, dif_pos h]

/- English proof (translation)
Simplify using `only [uMat, if_neg hne, dif_neg h]`.
-/
theorem uMat_neg {P : Fin n → Fin n → Prop} [∀ i j, Decidable (P i j)] (f : {p : Fin n × Fin n // P p.1 p.2} → κ) {i j : Fin n}
    (hne : i ≠ j) (h : ¬ P i j) : uMat P f i j = 0 := by
  simp only [uMat, if_neg hne, dif_neg h]

/- English proof (translation)
Rewrite using `[Matrix.det_of_upperTriangular]`. Simplify using `[uMat_diag]`. Introduce `i j hji`. Establish `hne : i ≠ j` using `(ne_of_lt hji).symm`. Conclude with `uMat_neg f hne (fun h => absurd hji (not_lt.mpr (le_of_lt (hP i j h))))`.
-/
theorem uMat_det {P : Fin n → Fin n → Prop} [∀ i j, Decidable (P i j)] (hP : ∀ i j, P i j → i < j)
    (f : {p : Fin n × Fin n // P p.1 p.2} → κ) : (uMat P f).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [uMat_diag]
  · intro i j hji
    have hne : i ≠ j := (ne_of_lt hji).symm
    exact uMat_neg f hne (fun h => absurd hji (not_lt.mpr (le_of_lt (hP i j h))))

def uGL {P : Fin n → Fin n → Prop} [∀ i j, Decidable (P i j)] (hP : ∀ i j, P i j → i < j)
    (f : {p : Fin n × Fin n // P p.1 p.2} → κ) : GL (Fin n) κ :=
  Matrix.GeneralLinearGroup.mk'' (uMat P f) (by rw [uMat_det hP]; exact isUnit_one)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem uGL_val {P : Fin n → Fin n → Prop} [∀ i j, Decidable (P i j)] (hP : ∀ i j, P i j → i < j)
    (f : {p : Fin n × Fin n // P p.1 p.2} → κ) : (uGL hP f : Matrix (Fin n) (Fin n) κ) = uMat P f := rfl

def uSet (κ : Type) [CommRing κ] (P : Fin n → Fin n → Prop) : Set (GL (Fin n) κ) :=
  {M | (∀ i, (M : Matrix (Fin n) (Fin n) κ) i i = 1) ∧ ∀ i j, i ≠ j → ¬ P i j → (M : Matrix (Fin n) (Fin n) κ) i j = 0}

def uEquiv {P : Fin n → Fin n → Prop} [∀ i j, Decidable (P i j)] (hP : ∀ i j, P i j → i < j) :
    ↥(uSet κ P) ≃ ({p : Fin n × Fin n // P p.1 p.2} → κ) where
  toFun M p := (M.1 : Matrix (Fin n) (Fin n) κ) p.1.1 p.1.2
  invFun f := ⟨uGL hP f, fun i => uMat_diag P f i, fun _ _ hne h => uMat_neg f hne h⟩
  left_inv M := by
    apply Subtype.ext
    apply Units.ext
    apply Matrix.ext
    intro i j
    show uMat P (fun p => (M.1 : Matrix (Fin n) (Fin n) κ) p.1.1 p.1.2) i j = _
    by_cases hne : i = j
    · rw [hne, uMat_diag, M.2.1]
    · by_cases h : P i j
      · rw [uMat_pos _ hne h]
      · rw [uMat_neg _ hne h, M.2.2 i j hne h]
  right_inv f := by
    funext p
    show uMat P f p.1.1 p.1.2 = _
    rw [uMat_pos f (ne_of_lt (hP _ _ p.2)) p.2]

/- English proof (translation)
Rewrite using `[Nat.card_congr (uEquiv hP), Nat.card_fun]`.
-/
theorem card_uSet {P : Fin n → Fin n → Prop} [∀ i j, Decidable (P i j)] (hP : ∀ i j, P i j → i < j) :
    Nat.card ↥(uSet κ P) = Nat.card κ ^ Nat.card {p : Fin n × Fin n // P p.1 p.2} := by
  rw [Nat.card_congr (uEquiv hP), Nat.card_fun]

/- English proof (translation)
Use extensionality with `M`. Simplify using `only [SetLike.mem_coe, uSet, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `hM`. Take `⟨h1, h2⟩` from `hM`.

Use `⟨fun i => h2 i i.2, fun i j hne hlt => ?_⟩` and prove the remaining obligations. Establish `hji : j < i` using `lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne)`. Conclude with `h1 ((fine_lt_right i.2).mpr hji)`. Introduce and unpack `⟨h1, h2⟩ show M ∈ btG n κ (fine n []) ∧ ∀ i : Fin n, i.val < n → (M : Matrix (Fin n) (Fin n) κ) i i = 1`. Use `⟨?_, fun i _ => h1 i⟩` and prove the remaining obligations.

Use `show (M : Matrix (Fin n) (Fin n) κ).BlockTriangular (fun i => fine n [] i.val)`. Introduce `i j hji`. Establish `hji' : j.val < i.val` using `(fine_lt_right i.2).mp hji`. Conclude with `h2 i j (fun e => by subst e; exact lt_irrefl _ hji') (fun h => absurd hji' (not_lt.mpr (le_of_lt h)))`.
-/
theorem uniUT_full_eq : ((uniUT n κ n [] : Subgroup (GL (Fin n) κ)) : Set (GL (Fin n) κ)) = uSet κ (fun i j : Fin n => i < j) := by
  ext M
  simp only [SetLike.mem_coe, uSet, Set.mem_setOf_eq]
  constructor
  · intro hM
    obtain ⟨h1, h2⟩ := hM
    refine ⟨fun i => h2 i i.2, fun i j hne hlt => ?_⟩
    have hji : j < i := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne)
    exact h1 ((fine_lt_right i.2).mpr hji)
  · rintro ⟨h1, h2⟩
    show M ∈ btG n κ (fine n []) ∧ ∀ i : Fin n, i.val < n → (M : Matrix (Fin n) (Fin n) κ) i i = 1
    refine ⟨?_, fun i _ => h1 i⟩
    show (M : Matrix (Fin n) (Fin n) κ).BlockTriangular (fun i => fine n [] i.val)
    intro i j hji
    have hji' : j.val < i.val := (fine_lt_right i.2).mp hji
    exact h2 i j (fun e => by subst e; exact lt_irrefl _ hji') (fun h => absurd hji' (not_lt.mpr (le_of_lt h)))

/- English proof (translation)
Establish `e : {p : Fin k × Fin k // p.1 < p.2} ≃ Σ j : Fin k, Fin j.val` using `{ toFun := fun p => ⟨p.1.2, ⟨p.1.1.val, p.2⟩⟩ invFun := fun q => ⟨(⟨q.2.val, lt_trans q.2.2 q.1.2⟩, q.1), q.2.2⟩ left_inv := fun p => rfl right_inv := fun q => rfl }`. Rewrite using `[Nat.card_eq_fintype_card, Fintype.card_congr e, Fintype.card_sigma]`. Simplify using `only [Fintype.card_fin]`. Establish `h2 : ∑ j : Fin k, (j : ℕ) = ∑ i ∈ Finset.range k, i` using `Fin.sum_univ_eq_sum_range (fun i => i) k`. Rewrite using `[h2, Finset.sum_range_id]`.
-/
theorem card_lt_pairs (k : ℕ) : Nat.card {p : Fin k × Fin k // p.1 < p.2} = k * (k - 1) / 2 := by
  have e : {p : Fin k × Fin k // p.1 < p.2} ≃ Σ j : Fin k, Fin j.val :=
    { toFun := fun p => ⟨p.1.2, ⟨p.1.1.val, p.2⟩⟩
      invFun := fun q => ⟨(⟨q.2.val, lt_trans q.2.2 q.1.2⟩, q.1), q.2.2⟩
      left_inv := fun p => rfl
      right_inv := fun q => rfl }
  rw [Nat.card_eq_fintype_card, Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  have h2 : ∑ j : Fin k, (j : ℕ) = ∑ i ∈ Finset.range k, i := Fin.sum_univ_eq_sum_range (fun i => i) k
  rw [h2, Finset.sum_range_id]

/- English proof (translation)
Establish `h1 : Nat.card ↥(HU κ k) = Nat.card ↥(uSet κ (fun i j : Fin k => i < j))`. Rewrite using `[← uniUT_full_eq]`. Both sides reduce to the same expression. Rewrite using `[h1, card_uSet (fun _ _ h => h)]`. Use `congr 1`.

Conclude with `card_lt_pairs k`.
-/
theorem card_HU (κ : Type) [CommRing κ] (k : ℕ) : Nat.card ↥(HU κ k) = Nat.card κ ^ (k * (k - 1) / 2) := by
  have h1 : Nat.card ↥(HU κ k) = Nat.card ↥(uSet κ (fun i j : Fin k => i < j)) := by
    rw [← uniUT_full_eq]; rfl
  rw [h1, card_uSet (fun _ _ h => h)]
  congr 1
  exact card_lt_pairs k

/- English proof (translation)
Use `show uGL hP f ∈ btG n κ (fine a bl) ∧ ∀ i : Fin n, i.val < a → (uGL hP f : Matrix (Fin n) (Fin n) κ) i i = 1`. Use `⟨?_, fun i _ => by rw [uGL_val]; exact uMat_diag P f i⟩` and prove the remaining obligations. Use `show (uGL hP f : Matrix (Fin n) (Fin n) κ).BlockTriangular (fun i => fine a bl i.val)`. Introduce `i j hij`. Rewrite using `[uGL_val]`.

Establish `hne : i ≠ j` using `fun e => by subst e; exact lt_irrefl _ hij`. Use `uMat_neg f hne (fun hp => ?_)` and prove the remaining obligations. Establish `h1` using `hP i j hp`. Establish `h2` using `hPa i j hp`. Establish `h3 : i.val < a` using `lt_trans (show i.val < j.val from h1) h2`.

Establish `hij'` using `(fine_lt_right (bl := bl) h3).mp hij`. Conclude with `absurd hij' (not_lt.mpr (le_of_lt h1))`.
-/
theorem uGL_mem_uniUT {a : ℕ} (bl : List ℕ) {P : Fin n → Fin n → Prop} [∀ i j, Decidable (P i j)]
    (hP : ∀ i j, P i j → i < j) (hPa : ∀ i j, P i j → j.val < a) (f : {p : Fin n × Fin n // P p.1 p.2} → κ) :
    uGL hP f ∈ uniUT n κ a bl := by
  show uGL hP f ∈ btG n κ (fine a bl) ∧ ∀ i : Fin n, i.val < a → (uGL hP f : Matrix (Fin n) (Fin n) κ) i i = 1
  refine ⟨?_, fun i _ => by rw [uGL_val]; exact uMat_diag P f i⟩
  show (uGL hP f : Matrix (Fin n) (Fin n) κ).BlockTriangular (fun i => fine a bl i.val)
  intro i j hij
  rw [uGL_val]
  have hne : i ≠ j := fun e => by subst e; exact lt_irrefl _ hij
  refine uMat_neg f hne (fun hp => ?_)
  have h1 := hP i j hp
  have h2 := hPa i j hp
  have h3 : i.val < a := lt_trans (show i.val < j.val from h1) h2
  have hij' := (fine_lt_right (bl := bl) h3).mp hij
  exact absurd hij' (not_lt.mpr (le_of_lt h1))

/- English proof (translation)
Unfold `detChar`. Rewrite using `[MonoidHom.finset_prod_apply]`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `s _`. Rewrite using `[MonoidHom.comp_apply]`.

Establish `hb : blkDet n κ (coarse a bl) (s + 1) ⟨uGL hP f, uniUT_le_blockUT n κ a bl (uGL_mem_uniUT bl hP hPa f)⟩ = 1`. Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Matrix.det ((uGL hP f : Matrix (Fin n) (Fin n) κ).toSquareBlock (fun i => coarse a bl i.val) (s + 1)) = (1 : κ)`. Establish `hI : (uGL hP f : Matrix (Fin n) (Fin n) κ).toSquareBlock (fun i => coarse a bl i.val) (s + 1) = 1`. Use extensionality with `i j`.

Simplify using `only [Matrix.toSquareBlock_def, Matrix.of_apply, uGL_val, Matrix.one_apply]`. Use `split_ifs with h`. Rewrite using `[h]`. Conclude with `uMat_diag P f _`. Use `uMat_neg f (fun e => h (Subtype.ext e)) (fun hp => ?_)` and prove the remaining obligations.

Establish `h1` using `hPa _ _ hp`. Establish `h3 : coarse a bl (j : Fin n).val = 0` using `by simp only [coarse, blkIdx, if_pos h1]`. Establish `h4 : coarse a bl (j : Fin n).val = s + 1` using `j.2`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hI, Matrix.det_one]`.

Rewrite using `[hb, map_one]`.
-/
theorem detChar_uGL (χ : ℕ → κˣ →* Kˣ) {a : ℕ} (bl : List ℕ) {P : Fin n → Fin n → Prop} [∀ i j, Decidable (P i j)]
    (hP : ∀ i j, P i j → i < j) (hPa : ∀ i j, P i j → j.val < a) (f : {p : Fin n × Fin n // P p.1 p.2} → κ) :
    detChar χ n a bl ⟨uGL hP f, uniUT_le_blockUT n κ a bl (uGL_mem_uniUT bl hP hPa f)⟩ = 1 := by
  unfold detChar
  rw [MonoidHom.finset_prod_apply]
  apply Finset.prod_eq_one
  intro s _
  rw [MonoidHom.comp_apply]
  have hb : blkDet n κ (coarse a bl) (s + 1) ⟨uGL hP f, uniUT_le_blockUT n κ a bl (uGL_mem_uniUT bl hP hPa f)⟩ = 1 := by
    apply Units.ext
    change Matrix.det ((uGL hP f : Matrix (Fin n) (Fin n) κ).toSquareBlock (fun i => coarse a bl i.val) (s + 1)) = (1 : κ)
    have hI : (uGL hP f : Matrix (Fin n) (Fin n) κ).toSquareBlock (fun i => coarse a bl i.val) (s + 1) = 1 := by
      ext i j
      simp only [Matrix.toSquareBlock_def, Matrix.of_apply, uGL_val, Matrix.one_apply]
      split_ifs with h
      · rw [h]; exact uMat_diag P f _
      · refine uMat_neg f (fun e => h (Subtype.ext e)) (fun hp => ?_)
        have h1 := hPa _ _ hp
        have h3 : coarse a bl (j : Fin n).val = 0 := by simp only [coarse, blkIdx, if_pos h1]
        have h4 : coarse a bl (j : Fin n).val = s + 1 := j.2
        omega
    rw [hI, Matrix.det_one]
  rw [hb, map_one]

/- English proof (translation)
Unfold `lamGen`. Rewrite using `[MonoidHom.mul_apply, MonoidHom.comp_apply]`. Establish `hi : Subgroup.inclusion (uniUT_le_blockUT n κ a bl) M = ⟨M.1, uniUT_le_blockUT n κ a bl M.2⟩` using `rfl`. Rewrite using `[hi, hd, mul_one]`. Both sides reduce to the same expression.
-/
theorem lamGen_val_of_det (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) {a : ℕ} (bl : List ℕ) (S : Finset ℕ) (M : ↥(uniUT n κ a bl))
    (hd : detChar χ n a bl ⟨M.1, uniUT_le_blockUT n κ a bl M.2⟩ = 1) :
    ((lamGen ψ χ n a bl S M : Kˣ) : K) = ψ (supSum a S (M.1 : Matrix (Fin n) (Fin n) κ)) := by
  unfold lamGen
  rw [MonoidHom.mul_apply, MonoidHom.comp_apply]
  have hi : Subgroup.inclusion (uniUT_le_blockUT n κ a bl) M = ⟨M.1, uniUT_le_blockUT n κ a bl M.2⟩ := rfl
  rw [hi, hd, mul_one]
  rfl

/- English proof (translation)
Unfold `supSum`. Rewrite using `[Finset.sum_eq_single i₀, Finset.sum_eq_single j₀]`. Rewrite using `[if_pos ⟨h₀, ha, hS⟩, uMat_pos _ (fun e => by rw [e] at h₀; omega) ⟨rfl, rfl⟩]`. Introduce `j _ hj split_ifs with h`. Conclude with `uMat_neg _ (fun e => by rw [e] at h; exact absurd h.1 (by omega)) (fun hp => hj hp.2)`.

Both sides reduce to the same expression. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Introduce `i _ hi`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `j _`. Use `split_ifs with h`. Conclude with `uMat_neg _ (fun e => by rw [e] at h; exact absurd h.1 (by omega)) (fun hp => hi hp.1)`. Both sides reduce to the same expression. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem supSum_elem {a : ℕ} (S : Finset ℕ) (i₀ j₀ : Fin n) (h₀ : i₀.val + 1 = j₀.val) (ha : j₀.val < a) (hS : i₀.val ∈ S) (c : κ) :
    supSum a S (uMat (fun i j : Fin n => i = i₀ ∧ j = j₀) (fun _ => c)) = c := by
  unfold supSum
  rw [Finset.sum_eq_single i₀, Finset.sum_eq_single j₀]
  · rw [if_pos ⟨h₀, ha, hS⟩, uMat_pos _ (fun e => by rw [e] at h₀; omega) ⟨rfl, rfl⟩]
  · intro j _ hj
    split_ifs with h
    · exact uMat_neg _ (fun e => by rw [e] at h; exact absurd h.1 (by omega)) (fun hp => hj hp.2)
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    split_ifs with h
    · exact uMat_neg _ (fun e => by rw [e] at h; exact absurd h.1 (by omega)) (fun hp => hi hp.1)
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Establish `hP : ∀ i j : Fin n, (i = i₀ ∧ j = j₀) → i < j`. Introduce and unpack `i j ⟨rfl, rfl⟩`. Use `show i.val < j.val`. Use linear arithmetic over natural numbers and integers. Establish `hPa : ∀ i j : Fin n, (i = i₀ ∧ j = j₀) → j.val < a`.

Introduce and unpack `i j ⟨rfl, rfl⟩`. Conclude with `ha`. Use `⟨⟨uGL hP (fun _ => c), uGL_mem_uniUT bl hP hPa _⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[lamGen_val_of_det ψ χ bl S ⟨uGL hP (fun _ => c), uGL_mem_uniUT bl hP hPa _⟩ (detChar_uGL χ bl hP hPa _)]`. Use `congr 1`.

Conclude with `supSum_elem S i₀ j₀ h₀ ha hS c`.
-/
theorem lamGen_elem (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) {a : ℕ} (bl : List ℕ) (S : Finset ℕ) (i₀ j₀ : Fin n)
    (h₀ : i₀.val + 1 = j₀.val) (ha : j₀.val < a) (hS : i₀.val ∈ S) (c : κ) :
    ∃ M : ↥(uniUT n κ a bl), ((lamGen ψ χ n a bl S M : Kˣ) : K) = ψ c := by
  have hP : ∀ i j : Fin n, (i = i₀ ∧ j = j₀) → i < j := by
    rintro i j ⟨rfl, rfl⟩; show i.val < j.val; omega
  have hPa : ∀ i j : Fin n, (i = i₀ ∧ j = j₀) → j.val < a := by
    rintro i j ⟨rfl, rfl⟩; exact ha
  refine ⟨⟨uGL hP (fun _ => c), uGL_mem_uniUT bl hP hPa _⟩, ?_⟩
  rw [lamGen_val_of_det ψ χ bl S ⟨uGL hP (fun _ => c), uGL_mem_uniUT bl hP hPa _⟩ (detChar_uGL χ bl hP hPa _)]
  congr 1
  exact supSum_elem S i₀ j₀ h₀ ha hS c

/- English proof (translation)
Introduce `h`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c, ψ c ≠ 1 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hψ (DFunLike.ext _ _ fun x => (hcon x).trans (AddChar.one_apply x).symm)`.

Take `⟨M, hM⟩` from `lamGen_elem ψ χ bl S (⟨i₀, by omega⟩ : Fin n) (⟨i₀ + 1, by omega⟩ : Fin n) rfl ha hS c`. Rewrite `hM` using `[h, MonoidHom.one_apply, Units.val_one]`. Conclude with `hc hM.symm`.
-/
theorem lamGen_ne_one {ψ : AddChar κ K} (hψ : ψ ≠ 1) (χ : ℕ → κˣ →* Kˣ) {a : ℕ} (bl : List ℕ) {S : Finset ℕ} {i₀ : ℕ}
    (hS : i₀ ∈ S) (ha : i₀ + 1 < a) (han : a ≤ n) : lamGen ψ χ n a bl S ≠ 1 := by
  intro h
  obtain ⟨c, hc⟩ : ∃ c, ψ c ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact hψ (DFunLike.ext _ _ fun x => (hcon x).trans (AddChar.one_apply x).symm)
  obtain ⟨M, hM⟩ := lamGen_elem ψ χ bl S (⟨i₀, by omega⟩ : Fin n) (⟨i₀ + 1, by omega⟩ : Fin n) rfl ha hS c
  rw [h, MonoidHom.one_apply, Units.val_one] at hM
  exact hc hM.symm

/- English proof (translation)
Unfold `lamX`. Use `lamGen_ne_one hψ χ _ (i₀ := 0) ?_ (by omega) hn` and prove the remaining obligations. Unfold `SX`. Simplify using `only [Finset.mem_filter, Finset.mem_range]`. Conclude with `⟨by omega, Or.inl (by omega)⟩`.
-/
theorem lamX_ne_one {ψ : AddChar κ K} (hψ : ψ ≠ 1) (χ : ℕ → κˣ →* Kˣ) {k : ℕ} (m t j : ℕ) (hk : 2 ≤ k) (hn : k + j ≤ n) :
    lamX ψ χ n k m t j ≠ 1 := by
  unfold lamX
  refine lamGen_ne_one hψ χ _ (i₀ := 0) ?_ (by omega) hn
  unfold SX
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, Or.inl (by omega)⟩

/- English proof (translation)
Unfold `lamJ`. Conclude with `lamGen_ne_one hψ χ _ (i₀ := 0) (Finset.mem_range.mpr (by omega)) (by omega) hn`.
-/
theorem lamJ_ne_one {ψ : AddChar κ K} (hψ : ψ ≠ 1) (χ : ℕ → κˣ →* Kˣ) {r : ℕ} (t j : ℕ) (hr : 2 ≤ r) (hn : r ≤ n) :
    lamJ ψ χ n r t j ≠ 1 := by
  unfold lamJ
  exact lamGen_ne_one hψ χ _ (i₀ := 0) (Finset.mem_range.mpr (by omega)) (by omega) hn

end Uni

/- English proof (translation)
Rewrite using `[← map_pow, pow_card_eq_one', map_one]`.
-/
theorem char_pow_card {G K : Type} [Group G] [Finite G] [Field K] (lam : G →* Kˣ) (x : G) : lam x ^ Nat.card G = 1 := by
  rw [← map_pow, pow_card_eq_one', map_one]

/- English proof (translation)
Establish `h1 : (φ (lam x : K)) ^ Nat.card G = 1`. Rewrite using `[← map_pow, ← Units.val_pow_eq_pow_val, char_pow_card, Units.val_one, map_one]`. Establish `hpos : 0 < Nat.card G` using `Nat.card_pos`. Establish `h2 : ‖φ (lam x : K)‖ ^ Nat.card G = 1` using `by rw [← norm_pow, h1, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hpos.ne').mp h2`.
-/
theorem char_norm_one {G K : Type} [Group G] [Finite G] [Field K] (lam : G →* Kˣ) (x : G) (φ : K →+* ℂ) :
    ‖φ (lam x : K)‖ = 1 := by
  have h1 : (φ (lam x : K)) ^ Nat.card G = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, char_pow_card, Units.val_one, map_one]
  have hpos : 0 < Nat.card G := Nat.card_pos
  have h2 : ‖φ (lam x : K)‖ ^ Nat.card G = 1 := by rw [← norm_pow, h1, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hpos.ne').mp h2

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `@insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.prod_insert ha]`. Take `⟨i1, i2, i3⟩` from `ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi)) (fun i hi => h1 i (Finset.mem_insert_of_mem hi))`.

Establish `fa0` using `h0 a (Finset.mem_insert_self a s)`. Establish `fa1` using `h1 a (Finset.mem_insert_self a s)`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use polynomial arithmetic with `[mul_nonneg fa0 (sub_nonneg.mpr i2)]`. Use polynomial arithmetic with `[mul_nonneg fa0 i3]`.

Conclude with `mul_nonneg (by linarith) i3`.
-/
private theorem prod_one_sub_lemma {ι : Type} (s : Finset ι) (f : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ f i)
    (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) ∧ ∏ i ∈ s, (1 - f i) ≤ 1 ∧ 0 ≤ ∏ i ∈ s, (1 - f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    obtain ⟨i1, i2, i3⟩ := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have fa0 := h0 a (Finset.mem_insert_self a s)
    have fa1 := h1 a (Finset.mem_insert_self a s)
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [mul_nonneg fa0 (sub_nonneg.mpr i2)]
    · nlinarith [mul_nonneg fa0 i3]
    · exact mul_nonneg (by linarith) i3

/- English proof (translation)
Establish `hq3 : (3 : ℝ) ≤ (Fintype.card F : ℝ)` using `by exact_mod_cast h3`. Establish `hqpos : (0 : ℝ) < (Fintype.card F : ℝ)` using `by linarith`. Establish `hqn : (0 : ℝ) < (Fintype.card F : ℝ) ^ n` using `pow_pos hqpos n`. Establish `hx0 : ∀ i : Fin n, 0 ≤ (Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n` using `fun i => by positivity`. Establish `hx1 : ∀ i : Fin n, (Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n ≤ 1`.

Introduce `i`. Rewrite using `[div_le_one hqn]`. Establish `: Fintype.card F ^ (i : ℕ) ≤ Fintype.card F ^ n` using `Nat.pow_le_pow_right (by omega) i.2.le`. Conclude with `this` after adjusting the coercions. Establish `hsum : ∑ i : Fin n, (Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n ≤ 1 / 2`.

Establish `hgs : ∑ i : Fin n, (Fintype.card F : ℝ) ^ (i : ℕ) = ∑ i ∈ Finset.range n, (Fintype.card F : ℝ) ^ i` using `Fin.sum_univ_eq_sum_range (fun i => (Fintype.card F : ℝ) ^ i) n`. Rewrite using `[← Finset.sum_div, hgs, geom_sum_eq (by linarith), div_div, div_le_iff₀ (by nlinarith)]`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.mpr hq3) hqn.le]`. Establish `hb` using `prod_one_sub_lemma Finset.univ (fun i : Fin n => (Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n) (fun i _ => hx0 i) (fun i _ => hx1 i)`. Establish `b1 : 1 - ∑ i : Fin n, (Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n ≤ ∏ i : Fin n, (1 - (Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n)` using `hb.1`.

Establish `b2 : ∏ i : Fin n, (1 - (Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n) ≤ 1` using `hb.2.1`. Use `⟨∏ i : Fin n, (1 - (Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n), by linarith, b2, ?_⟩` and prove the remaining obligations. Establish `hrhs : (Fintype.card F : ℝ) ^ (n * n) = ∏ _i : Fin n, (Fintype.card F : ℝ) ^ n`. Rewrite using `[Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]`. Rewrite using `[Matrix.card_GL_field, Nat.cast_prod, hrhs, ← Finset.prod_mul_distrib]`.

Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `i _`. Establish `hle : Fintype.card F ^ (i : ℕ) ≤ Fintype.card F ^ n` using `Nat.pow_le_pow_right (by omega) i.2.le`. Establish `hcan : (Fintype.card F : ℝ) ^ n * ((Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n) = (Fintype.card F : ℝ) ^ (i : ℕ)`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow, mul_sub, mul_one, hcan]`.
-/
private theorem card_GL_eq_card_pow_mul_theta (F : Type) [Field F] [Fintype F] (n : ℕ) (h3 : 3 ≤ Fintype.card F) :
    ∃ θ : ℝ, 1 / 2 ≤ θ ∧ θ ≤ 1 ∧
      (Nat.card (GL (Fin n) F) : ℝ) = (Fintype.card F : ℝ) ^ (n * n) * θ := by
  have hq3 : (3 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast h3
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by linarith
  have hqn : (0 : ℝ) < (Fintype.card F : ℝ) ^ n := pow_pos hqpos n
  have hx0 : ∀ i : Fin n, 0 ≤ (Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n := fun i => by positivity
  have hx1 : ∀ i : Fin n, (Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n ≤ 1 := by
    intro i
    rw [div_le_one hqn]
    have : Fintype.card F ^ (i : ℕ) ≤ Fintype.card F ^ n := Nat.pow_le_pow_right (by omega) i.2.le
    exact_mod_cast this
  have hsum : ∑ i : Fin n, (Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n ≤ 1 / 2 := by
    have hgs : ∑ i : Fin n, (Fintype.card F : ℝ) ^ (i : ℕ) = ∑ i ∈ Finset.range n, (Fintype.card F : ℝ) ^ i :=
      Fin.sum_univ_eq_sum_range (fun i => (Fintype.card F : ℝ) ^ i) n
    rw [← Finset.sum_div, hgs, geom_sum_eq (by linarith), div_div, div_le_iff₀ (by nlinarith)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hq3) hqn.le]
  have hb := prod_one_sub_lemma Finset.univ (fun i : Fin n => (Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n)
    (fun i _ => hx0 i) (fun i _ => hx1 i)
  have b1 : 1 - ∑ i : Fin n, (Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n ≤
      ∏ i : Fin n, (1 - (Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n) := hb.1
  have b2 : ∏ i : Fin n, (1 - (Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n) ≤ 1 := hb.2.1
  refine ⟨∏ i : Fin n, (1 - (Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n), by linarith, b2, ?_⟩
  have hrhs : (Fintype.card F : ℝ) ^ (n * n) = ∏ _i : Fin n, (Fintype.card F : ℝ) ^ n := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  rw [Matrix.card_GL_field, Nat.cast_prod, hrhs, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hle : Fintype.card F ^ (i : ℕ) ≤ Fintype.card F ^ n := Nat.pow_le_pow_right (by omega) i.2.le
  have hcan : (Fintype.card F : ℝ) ^ n * ((Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n) =
      (Fintype.card F : ℝ) ^ (i : ℕ) := by
    field_simp
  rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow, mul_sub, mul_one, hcan]

/- English proof (translation)
Take `⟨θ, h1, h2, hc⟩` from `card_GL_eq_card_pow_mul_theta F k h3`. Use `⟨θ, h1, h2, ?_⟩` and prove the remaining obligations. Establish `hH : Nat.card ↥(HU F k) = Fintype.card F ^ (k * (k - 1) / 2)`. Rewrite using `[card_HU, Nat.card_eq_fintype_card (α := F)]`. Establish `hmul` using `Subgroup.card_mul_index (HU F k)`.

Rewrite `hmul` using `[hH]`. Establish `hexp : k * k = k * (k - 1) / 2 + k * (k + 1) / 2`. Consider the cases of `k with`. Consider the case `zero => rfl`. Consider the case `succ k`.

Establish `hA : (k + 1) * (k + 1 - 1) = (k + 1) * k` using `by simp`. Establish `hB : (k + 1) * (k + 1 + 1) = (k + 1) * k + 2 * (k + 1)` using `by ring`. Establish `hC : (k + 1) * (k + 1) = (k + 1) * k + (k + 1)` using `by ring`. Establish `hE : (k + 1) * k % 2 = 0`. Break down `Nat.even_mul_succ_self k with ⟨t, ht⟩` into its components or cases.

Rewrite using `[Nat.mul_comm, ht]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hA, hB, hC, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]`. Generalize the expression as in `(k + 1) * k = A at hE ⊢`. Use linear arithmetic over natural numbers and integers.

Establish `hpos : (0 : ℝ) < (Fintype.card F : ℝ) ^ (k * (k - 1) / 2)`. Establish `: (0 : ℝ) < (Fintype.card F : ℝ)`. Establish `: (3 : ℝ) ≤ (Fintype.card F : ℝ)` using `by exact_mod_cast h3`. Combine the linear equalities and inequalities to obtain the conclusion. Check the signs of the components of the expression.

Establish `hR : (Fintype.card F : ℝ) ^ (k * (k - 1) / 2) * ((HU F k).index : ℝ) = (Fintype.card F : ℝ) ^ (k * (k - 1) / 2) * ((Fintype.card F : ℝ) ^ (k * (k + 1) / 2) * θ)`. Establish `hm` using `congrArg (fun x : ℕ => (x : ℝ)) hmul`. Move the coercions through the operations in `at hm`. Rewrite using `[hm, hc, hexp, pow_add, mul_assoc]`. Conclude with `mul_left_cancel₀ hpos.ne' hR`.
-/
theorem index_HU (F : Type) [Field F] [Fintype F] [DecidableEq F] (k : ℕ) (h3 : 3 ≤ Fintype.card F) :
    ∃ θ : ℝ, 1 / 2 ≤ θ ∧ θ ≤ 1 ∧ ((HU F k).index : ℝ) = (Fintype.card F : ℝ) ^ (k * (k + 1) / 2) * θ := by
  obtain ⟨θ, h1, h2, hc⟩ := card_GL_eq_card_pow_mul_theta F k h3
  refine ⟨θ, h1, h2, ?_⟩
  have hH : Nat.card ↥(HU F k) = Fintype.card F ^ (k * (k - 1) / 2) := by
    rw [card_HU, Nat.card_eq_fintype_card (α := F)]
  have hmul := Subgroup.card_mul_index (HU F k)
  rw [hH] at hmul
  have hexp : k * k = k * (k - 1) / 2 + k * (k + 1) / 2 := by
    cases k with
    | zero => rfl
    | succ k =>
      have hA : (k + 1) * (k + 1 - 1) = (k + 1) * k := by simp
      have hB : (k + 1) * (k + 1 + 1) = (k + 1) * k + 2 * (k + 1) := by ring
      have hC : (k + 1) * (k + 1) = (k + 1) * k + (k + 1) := by ring
      have hE : (k + 1) * k % 2 = 0 := by
        rcases Nat.even_mul_succ_self k with ⟨t, ht⟩
        rw [Nat.mul_comm, ht]
        omega
      rw [hA, hB, hC, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
      generalize (k + 1) * k = A at hE ⊢
      omega
  have hpos : (0 : ℝ) < (Fintype.card F : ℝ) ^ (k * (k - 1) / 2) := by
    have : (0 : ℝ) < (Fintype.card F : ℝ) := by
      have : (3 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast h3
      linarith
    positivity
  have hR : (Fintype.card F : ℝ) ^ (k * (k - 1) / 2) * ((HU F k).index : ℝ) =
      (Fintype.card F : ℝ) ^ (k * (k - 1) / 2) * ((Fintype.card F : ℝ) ^ (k * (k + 1) / 2) * θ) := by
    have hm := congrArg (fun x : ℕ => (x : ℝ)) hmul
    push_cast at hm
    rw [hm, hc, hexp, pow_add, mul_assoc]
  exact mul_left_cancel₀ hpos.ne' hR

section Diag

variable {n : ℕ} {κ : Type} [CommRing κ] {K : Type} [Field K]

def dGL (i₀ : Fin n) (u : κˣ) : GL (Fin n) κ :=
  Units.map (Matrix.diagonalRingHom (Fin n) κ).toMonoidHom (MulEquiv.piUnits.symm (Function.update 1 i₀ u))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dGL_val (i₀ : Fin n) (u : κˣ) :
    (dGL i₀ u : Matrix (Fin n) (Fin n) κ) = Matrix.diagonal fun i => ((Function.update (1 : Fin n → κˣ) i₀ u i : κˣ) : κ) := rfl

/- English proof (translation)
Use `show (dGL i₀ u : Matrix (Fin n) (Fin n) κ).BlockTriangular (fun i => β i.val)`. Rewrite using `[dGL_val]`. Conclude with `Matrix.blockTriangular_diagonal _`.
-/
theorem dGL_mem_btG (β : ℕ → ℕ) (i₀ : Fin n) (u : κˣ) : dGL i₀ u ∈ btG n κ β := by
  show (dGL i₀ u : Matrix (Fin n) (Fin n) κ).BlockTriangular (fun i => β i.val)
  rw [dGL_val]
  exact Matrix.blockTriangular_diagonal _

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Matrix.det ((dGL i₀ u : Matrix (Fin n) (Fin n) κ).toSquareBlock (fun i => β i.val) c) = _`. Rewrite using `[dGL_val]`. Establish `hd : (Matrix.diagonal fun i => ((Function.update (1 : Fin n → κˣ) i₀ u i : κˣ) : κ)).toSquareBlock (fun i => β i.val) c = Matrix.diagonal (fun i : {i : Fin n // β i.val = c} => ((Function.update (1 : Fin n → κˣ) i₀ u i.1 : κˣ) : κ))`. Use extensionality with `i j`.

Simplify using `only [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.diagonal_apply, Subtype.ext_iff]`. Rewrite using `[hd, Matrix.det_diagonal]`. Use `split_ifs with hc`. Rewrite using `[Finset.prod_eq_single ⟨i₀, hc⟩]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Rewrite using `[Function.update_apply, if_neg (fun e => hb (Subtype.ext e))]`. Simplify using the standard rewrite rules. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.

Rewrite using `[Units.val_one]`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `b _`. Rewrite using `[Function.update_apply, if_neg (fun e => hc (by rw [← e]; exact b.2))]`. Simplify using the standard rewrite rules.
-/
theorem blkDet_dGL (β : ℕ → ℕ) (c : ℕ) (i₀ : Fin n) (u : κˣ) :
    blkDet n κ β c ⟨dGL i₀ u, dGL_mem_btG β i₀ u⟩ = if β i₀.val = c then u else 1 := by
  apply Units.ext
  change Matrix.det ((dGL i₀ u : Matrix (Fin n) (Fin n) κ).toSquareBlock (fun i => β i.val) c) = _
  rw [dGL_val]
  have hd : (Matrix.diagonal fun i => ((Function.update (1 : Fin n → κˣ) i₀ u i : κˣ) : κ)).toSquareBlock (fun i => β i.val) c =
      Matrix.diagonal (fun i : {i : Fin n // β i.val = c} => ((Function.update (1 : Fin n → κˣ) i₀ u i.1 : κˣ) : κ)) := by
    ext i j
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.diagonal_apply, Subtype.ext_iff]
  rw [hd, Matrix.det_diagonal]
  split_ifs with hc
  · rw [Finset.prod_eq_single ⟨i₀, hc⟩]
    · simp
    · intro b _ hb
      rw [Function.update_apply, if_neg (fun e => hb (Subtype.ext e))]
      simp
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Units.val_one]
    apply Finset.prod_eq_one
    intro b _
    rw [Function.update_apply, if_neg (fun e => hc (by rw [← e]; exact b.2))]
    simp

/- English proof (translation)
Use `⟨⟨dGL i₀ u, dGL_mem_btG _ i₀ u⟩, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, MonoidHom.mem_ker]`. Use extensionality with `i j`. Rewrite using `[blkHom_apply, dGL_val]`. Establish `hi : (i.1 : Fin n).val < r`.

Assume the negation of the conclusion as `hh`. Conclude with `absurd i.2 (by simp only [coarse, blkIdx, if_neg hh]; omega)`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Establish `hne : (i.1 : Fin n) ≠ i₀` using `fun e => by rw [← e] at h₀; omega`.

Simplify using `[Function.update_apply, hne]`. Establish `hne : (i.1 : Fin n) ≠ j.1` using `fun e => hij (Subtype.ext e)`. Simplify using `[hij, hne]`.
-/
theorem dGL_mem_HK {r : ℕ} (bl : List ℕ) (i₀ : Fin n) (h₀ : r ≤ i₀.val) (u : κˣ) : dGL i₀ u ∈ HK n κ r bl := by
  refine ⟨⟨dGL i₀ u, dGL_mem_btG _ i₀ u⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  ext i j
  rw [blkHom_apply, dGL_val]
  have hi : (i.1 : Fin n).val < r := by
    by_contra hh
    exact absurd i.2 (by simp only [coarse, blkIdx, if_neg hh]; omega)
  by_cases hij : i = j
  · subst hij
    have hne : (i.1 : Fin n) ≠ i₀ := fun e => by rw [← e] at h₀; omega
    simp [Function.update_apply, hne]
  · have hne : (i.1 : Fin n) ≠ j.1 := fun e => hij (Subtype.ext e)
    simp [hij, hne]

/- English proof (translation)
Unfold `detChar`. Rewrite using `[MonoidHom.finset_prod_apply, Finset.prod_eq_single s]`. Rewrite using `[MonoidHom.comp_apply, blkDet_dGL, if_pos h₀]`. Introduce `c _ hc`. Rewrite using `[MonoidHom.comp_apply, blkDet_dGL, if_neg (by omega), map_one]`.

Introduce `h`. Conclude with `absurd (Finset.mem_range.mpr hs) h`.
-/
theorem detChar_dGL (χ : ℕ → κˣ →* Kˣ) {a : ℕ} (bl : List ℕ) (i₀ : Fin n) {s : ℕ} (hs : s < bl.length)
    (h₀ : coarse a bl i₀.val = s + 1) (u : κˣ) : detChar χ n a bl ⟨dGL i₀ u, dGL_mem_btG _ i₀ u⟩ = χ s u := by
  unfold detChar
  rw [MonoidHom.finset_prod_apply, Finset.prod_eq_single s]
  · rw [MonoidHom.comp_apply, blkDet_dGL, if_pos h₀]
  · intro c _ hc
    rw [MonoidHom.comp_apply, blkDet_dGL, if_neg (by omega), map_one]
  · intro h; exact absurd (Finset.mem_range.mpr hs) h

/- English proof (translation)
Introduce `h`. Choose the witnesses or unpack the hypotheses as in `⟨u, hu⟩ : ∃ u, χ s u ≠ 1 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hχ (MonoidHom.ext hcon)`.

Establish `hr : r ≤ i₀.val`. Assume the negation of the conclusion as `hh`. Establish `: coarse r bl i₀.val = 0` using `by simp only [coarse, blkIdx, if_pos (by omega : i₀.val < r)]`. Use linear arithmetic over natural numbers and integers. Establish `h1` using `congrArg (fun f => f ⟨dGL i₀ u, dGL_mem_HK bl i₀ hr u⟩) h`.

Simplify using `only [MonoidHom.one_apply] at h1`. Unfold `lamK at h1`. Rewrite `h1` using `[MonoidHom.comp_apply]`. Establish `e : Subgroup.inclusion (HK_le_blockUT n κ r bl) ⟨dGL i₀ u, dGL_mem_HK bl i₀ hr u⟩ = ⟨dGL i₀ u, dGL_mem_btG _ i₀ u⟩` using `rfl`. Rewrite `h1` using `[e, detChar_dGL χ bl i₀ hs h₀ u]`.

Conclude with `hu h1`.
-/
theorem lamK_ne_one (χ : ℕ → κˣ →* Kˣ) {r : ℕ} (bl : List ℕ) (i₀ : Fin n) {s : ℕ} (hs : s < bl.length)
    (h₀ : coarse r bl i₀.val = s + 1) (hχ : χ s ≠ 1) : lamK χ n r bl ≠ 1 := by
  intro h
  obtain ⟨u, hu⟩ : ∃ u, χ s u ≠ 1 := by
    by_contra hcon; push_neg at hcon; exact hχ (MonoidHom.ext hcon)
  have hr : r ≤ i₀.val := by
    by_contra hh
    have : coarse r bl i₀.val = 0 := by simp only [coarse, blkIdx, if_pos (by omega : i₀.val < r)]
    omega
  have h1 := congrArg (fun f => f ⟨dGL i₀ u, dGL_mem_HK bl i₀ hr u⟩) h
  simp only [MonoidHom.one_apply] at h1
  unfold lamK at h1
  rw [MonoidHom.comp_apply] at h1
  have e : Subgroup.inclusion (HK_le_blockUT n κ r bl) ⟨dGL i₀ u, dGL_mem_HK bl i₀ hr u⟩ = ⟨dGL i₀ u, dGL_mem_btG _ i₀ u⟩ := rfl
  rw [e, detChar_dGL χ bl i₀ hs h₀ u] at h1
  exact hu h1

/- English proof (translation)
Unfold `coarse`. Simplify using `only [blkIdx]`. Rewrite using `[if_neg (by omega)]`. Use `congr 1`. Rewrite using `[Nat.add_sub_cancel_left]`.

Proceed by induction on `s generalizing j with`. Consider the case `zero`. Take `⟨j', rfl⟩ : ∃ j', j = j' + 1` from `⟨j - 1, by omega⟩`. Simplify using `only [List.replicate_succ, blkIdx, zero_mul, if_pos ht]`. Consider the case `succ s ih`.

Take `⟨j', rfl⟩ : ∃ j', j = j' + 1` from `⟨j - 1, by omega⟩`. Rewrite using `[List.replicate_succ]`. Simplify using `only [blkIdx]`. Rewrite using `[Nat.add_mul, one_mul, if_neg (by omega), Nat.add_sub_cancel, ih (by omega)]`.
-/
theorem coarse_replicate {r t j s : ℕ} (ht : 0 < t) (hs : s < j) : coarse r (List.replicate j t) (r + s * t) = s + 1 := by
  unfold coarse
  simp only [blkIdx]
  rw [if_neg (by omega)]
  congr 1
  rw [Nat.add_sub_cancel_left]
  induction s generalizing j with
  | zero =>
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    simp only [List.replicate_succ, blkIdx, zero_mul, if_pos ht]
  | succ s ih =>
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [List.replicate_succ]
    simp only [blkIdx]
    rw [Nat.add_mul, one_mul, if_neg (by omega), Nat.add_sub_cancel, ih (by omega)]

/- English proof (translation)
Unfold `lamKJ`. Establish `hst : s * t < j * t` using `Nat.mul_lt_mul_of_pos_right hs ht`. Conclude with `lamK_ne_one χ (List.replicate j t) (⟨r + s * t, by omega⟩ : Fin n) (by simpa using hs) (coarse_replicate ht hs) hχ`.
-/
theorem lamKJ_ne_one (χ : ℕ → κˣ →* Kˣ) {r t j s : ℕ} (ht : 0 < t) (hs : s < j) (hn : r + j * t ≤ n) (hχ : χ s ≠ 1) :
    lamKJ χ n r t j ≠ 1 := by
  unfold lamKJ
  have hst : s * t < j * t := Nat.mul_lt_mul_of_pos_right hs ht
  exact lamK_ne_one χ (List.replicate j t) (⟨r + s * t, by omega⟩ : Fin n) (by simpa using hs) (coarse_replicate ht hs) hχ

/- English proof (translation)
Introduce `h`. Choose the witnesses or unpack the hypotheses as in `⟨u, hu⟩ : ∃ u, ξ u ≠ 1 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hξ (MonoidHom.ext hcon)`.

Establish `hc : coarse a [b] (⟨a, by omega⟩ : Fin n).val = 0 + 1`. Simplify using `[coarse, blkIdx, hb]`. Establish `h1` using `congrArg (fun f => f ⟨dGL (⟨a, by omega⟩ : Fin n) u, dGL_mem_btG _ _ u⟩) h`. Simplify using `only [MonoidHom.one_apply] at h1`. Unfold `lamQ at h1`.

Rewrite `h1` using `[detChar_dGL (fun _ => ξ) [b] _ (by simp) hc u]`. Conclude with `hu h1`.
-/
theorem lamQ_ne_one {ξ : κˣ →* Kˣ} {a b : ℕ} (hb : 0 < b) (hn : a + b ≤ n) (hξ : ξ ≠ 1) : lamQ ξ n a b ≠ 1 := by
  intro h
  obtain ⟨u, hu⟩ : ∃ u, ξ u ≠ 1 := by
    by_contra hcon; push_neg at hcon; exact hξ (MonoidHom.ext hcon)
  have hc : coarse a [b] (⟨a, by omega⟩ : Fin n).val = 0 + 1 := by
    simp [coarse, blkIdx, hb]
  have h1 := congrArg (fun f => f ⟨dGL (⟨a, by omega⟩ : Fin n) u, dGL_mem_btG _ _ u⟩) h
  simp only [MonoidHom.one_apply] at h1
  unfold lamQ at h1
  rw [detChar_dGL (fun _ => ξ) [b] _ (by simp) hc u] at h1
  exact hu h1

/- English proof (translation)
Establish `hD : diagEmb κ h g ∈ blockUT n κ r bl` using `by show ((diagEmb κ h g : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).BlockTriangular (fun i => coarse r bl i.val)`. Introduce `i j hij`. Use `show diagMat r n (g : Matrix (Fin r) (Fin r) κ) i j = 0`. Simplify using `only [diagMat]`. Establish `hi : ¬ i.val < r`.

Introduce `hi`. Establish `h0 : coarse r bl i.val = 0` using `by simp only [coarse, blkIdx, if_pos hi]`. Establish `hij' : coarse r bl j.val < coarse r bl i.val` using `hij`. Use linear arithmetic over natural numbers and integers. Rewrite using `[dif_neg (fun hc => hi hc.1)]`.

Conclude with `Matrix.one_apply_ne (fun e => by subst e; exact lt_irrefl _ hij)`. Unfold `HK at hM ⊢`. Rewrite `hM`, the goal using `[Subgroup.mem_map]`. Take `⟨M', hM', hMe⟩` from `hM`. Use `⟨⟨diagEmb κ h g, hD⟩ * M' * ⟨diagEmb κ h g, hD⟩⁻¹, ?_, ?_⟩` and prove the remaining obligations.

Rewrite `hM'`, the goal using `[MonoidHom.mem_ker]`. Rewrite using `[map_mul, map_mul, hM', mul_one, ← map_mul, mul_inv_cancel, map_one]`. Rewrite using `[← hMe, map_mul, map_mul, map_inv]`. Both sides reduce to the same expression.
-/
theorem HK_conj_diagEmb {r : ℕ} (h : r ≤ n) {bl : List ℕ} (g : GL (Fin r) κ) {M : GL (Fin n) κ} (hM : M ∈ HK n κ r bl) :
    diagEmb κ h g * M * (diagEmb κ h g)⁻¹ ∈ HK n κ r bl := by
  have hD : diagEmb κ h g ∈ blockUT n κ r bl := by
    show ((diagEmb κ h g : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).BlockTriangular (fun i => coarse r bl i.val)
    intro i j hij
    show diagMat r n (g : Matrix (Fin r) (Fin r) κ) i j = 0
    simp only [diagMat]
    have hi : ¬ i.val < r := by
      intro hi
      have h0 : coarse r bl i.val = 0 := by simp only [coarse, blkIdx, if_pos hi]
      have hij' : coarse r bl j.val < coarse r bl i.val := hij
      omega
    rw [dif_neg (fun hc => hi hc.1)]
    exact Matrix.one_apply_ne (fun e => by subst e; exact lt_irrefl _ hij)
  unfold HK at hM ⊢
  rw [Subgroup.mem_map] at hM ⊢
  obtain ⟨M', hM', hMe⟩ := hM
  refine ⟨⟨diagEmb κ h g, hD⟩ * M' * ⟨diagEmb κ h g, hD⟩⁻¹, ?_, ?_⟩
  · rw [MonoidHom.mem_ker] at hM' ⊢
    rw [map_mul, map_mul, hM', mul_one, ← map_mul, mul_inv_cancel, map_one]
  · rw [← hMe, map_mul, map_mul, map_inv]
    rfl

/- English proof (translation)
Unfold `lamK`. Rewrite using `[MonoidHom.comp_apply, MonoidHom.comp_apply]`. Establish `hD : diagEmb κ h g ∈ blockUT n κ r bl` using `by show ((diagEmb κ h g : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).BlockTriangular (fun i => coarse r bl i.val)`. Introduce `i j hij`. Use `show diagMat r n (g : Matrix (Fin r) (Fin r) κ) i j = 0`.

Simplify using `only [diagMat]`. Establish `hi : ¬ i.val < r`. Introduce `hi`. Establish `h0 : coarse r bl i.val = 0` using `by simp only [coarse, blkIdx, if_pos hi]`. Establish `hij' : coarse r bl j.val < coarse r bl i.val` using `hij`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[dif_neg (fun hc => hi hc.1)]`. Conclude with `Matrix.one_apply_ne (fun e => by subst e; exact lt_irrefl _ hij)`. Establish `e : Subgroup.inclusion (HK_le_blockUT n κ r bl) ⟨diagEmb κ h g * M.1 * (diagEmb κ h g)⁻¹, HK_conj_diagEmb h g M.2⟩ = ⟨diagEmb κ h g, hD⟩ * Subgroup.inclusion (HK_le_blockUT n κ r bl) M * ⟨diagEmb κ h g, hD⟩⁻¹` using `rfl`. Rewrite using `[e, map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]`.
-/
theorem lamK_conj_diagEmb (χ : ℕ → κˣ →* Kˣ) {r : ℕ} (h : r ≤ n) {bl : List ℕ} (g : GL (Fin r) κ) (M : ↥(HK n κ r bl)) :
    lamK χ n r bl ⟨diagEmb κ h g * M.1 * (diagEmb κ h g)⁻¹, HK_conj_diagEmb h g M.2⟩ = lamK χ n r bl M := by
  unfold lamK
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
  have hD : diagEmb κ h g ∈ blockUT n κ r bl := by
    show ((diagEmb κ h g : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).BlockTriangular (fun i => coarse r bl i.val)
    intro i j hij
    show diagMat r n (g : Matrix (Fin r) (Fin r) κ) i j = 0
    simp only [diagMat]
    have hi : ¬ i.val < r := by
      intro hi
      have h0 : coarse r bl i.val = 0 := by simp only [coarse, blkIdx, if_pos hi]
      have hij' : coarse r bl j.val < coarse r bl i.val := hij
      omega
    rw [dif_neg (fun hc => hi hc.1)]
    exact Matrix.one_apply_ne (fun e => by subst e; exact lt_irrefl _ hij)
  have e : Subgroup.inclusion (HK_le_blockUT n κ r bl) ⟨diagEmb κ h g * M.1 * (diagEmb κ h g)⁻¹, HK_conj_diagEmb h g M.2⟩ =
      ⟨diagEmb κ h g, hD⟩ * Subgroup.inclusion (HK_le_blockUT n κ r bl) M * ⟨diagEmb κ h g, hD⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]

end Diag

instance finite_res (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) : Finite (𝓞 E ⧸ w.asIdeal) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot

instance finite_GLs (E : Type) [Field E] [NumberField E] (SG : Finset (HeightOneSpectrum (𝓞 E))) (n : ℕ) : Finite (GLs E SG n) :=
  Pi.finite

/- English proof (translation)
Rewrite using `[card_HU]`. Simplify using the standard rewrite rules.
-/
example : Nat.card ↥(HU (ZMod 3) 2) = 3 := by rw [card_HU]; simp

/- English proof (translation)
Rewrite using `[card_HU]`. Simplify using the standard rewrite rules.
-/
example : Nat.card ↥(HU (ZMod 5) 4) = 5 ^ 6 := by rw [card_HU]; simp

/- English proof (translation)
Establish `hp` using `ZMod.isPrimitive_stdAddChar 3`. Establish `h` using `hp (a := 1) (by decide)`. Rewrite `h` using `[AddChar.mulShift_one]`. Then use the resulting hypothesis.
-/
theorem stdAddChar_ne_one : (ZMod.stdAddChar (N := 3)) ≠ 1 := by
  have hp := ZMod.isPrimitive_stdAddChar 3
  have h := hp (a := 1) (by decide)
  rwa [AddChar.mulShift_one] at h

/- English proof (translation)
The claim follows from `lamX_ne_one stdAddChar_ne_one _ 2 4 1 (by norm_num) (by norm_num)`.
-/
example : lamX (ZMod.stdAddChar (N := 3)) (fun _ => 1) 8 3 2 4 1 ≠ 1 :=
  lamX_ne_one stdAddChar_ne_one _ 2 4 1 (by norm_num) (by norm_num)

section DiagChar

variable {n : ℕ} {κ : Type} [CommRing κ] {K : Type} [Field K]

/- English proof (translation)
Unfold `supSum`. Use `symm`. Use `Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ ?_` and prove the remaining obligations. Introduce `i hi`. Establish `his : s ≤ i.val`.

Assume the negation of the conclusion as `hh`. Conclude with `hi ⟨⟨i.val, by omega⟩, rfl⟩`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `j _`. Rewrite using `[if_neg]`.

Introduce `hc`. Use `hc.1` as an intermediate fact. Use `hc.2.1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Introduce `i`.

Use `Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ ?_` and prove the remaining obligations. Introduce `j hj`. Establish `hjs : s ≤ j.val`. Assume the negation of the conclusion as `hh`. Conclude with `hj ⟨⟨j.val, by omega⟩, rfl⟩`.

Rewrite using `[if_neg]`. Introduce `hc`. Use `hc.2.1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Introduce `j`.

Simplify using `only [Fin.coe_castLE]`. Use `split_ifs`. Simplify using `[diagMat]`. Both sides reduce to the same expression.
-/
theorem supSum_diagMat {s a : ℕ} (h : s ≤ n) (ha : a ≤ s) (S : Finset ℕ) (g : Matrix (Fin s) (Fin s) κ) :
    supSum a S (diagMat s n g) = supSum a S g := by
  unfold supSum
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ ?_
  · intro i hi
    have his : s ≤ i.val := by
      by_contra hh
      exact hi ⟨⟨i.val, by omega⟩, rfl⟩
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg]
    intro hc
    have := hc.1
    have := hc.2.1
    omega
  · intro i
    refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ ?_
    · intro j hj
      have hjs : s ≤ j.val := by
        by_contra hh
        exact hj ⟨⟨j.val, by omega⟩, rfl⟩
      rw [if_neg]
      intro hc
      have := hc.2.1
      omega
    · intro j
      simp only [Fin.coe_castLE]
      split_ifs
      · simp [diagMat]
      · rfl

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Matrix.det ((diagMat s n (g : Matrix (Fin s) (Fin s) κ)).toSquareBlock (fun i => β i.val) c) = Matrix.det ((g : Matrix (Fin s) (Fin s) κ).toSquareBlock (fun i => β i.val) c)`. Set `e : {i : Fin s // β i.val = c} ≃ {i : Fin n // β i.val = c}` to `{ toFun := fun i => ⟨⟨i.1.val, lt_of_lt_of_le i.1.2 h⟩, i.2⟩ invFun := fun i => ⟨⟨i.1.val, by`. Assume the negation of the conclusion as `hh`. Conclude with `hc i.1.val (by omega) i.2⟩, i.2⟩`.

Use `left_inv := fun i => rfl`. Use `right_inv := fun i => rfl }`. Establish `hb : (diagMat s n (g : Matrix (Fin s) (Fin s) κ)).toSquareBlock (fun i => β i.val) c = ((g : Matrix (Fin s) (Fin s) κ).toSquareBlock (fun i => β i.val) c).submatrix e.symm e.symm`. Use extensionality with `i j`. Establish `hi : (i.1 : Fin n).val < s`.

Assume the negation of the conclusion as `hh`. Conclude with `hc _ (by omega) i.2`. Establish `hj : (j.1 : Fin n).val < s`. Assume the negation of the conclusion as `hh`. Conclude with `hc _ (by omega) j.2`.

Simplify using `only [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.submatrix_apply, diagMat]`. Rewrite using `[dif_pos ⟨hi, hj⟩]`. Both sides reduce to the same expression. Rewrite using `[hb, Matrix.det_submatrix_equiv_self]`.
-/
theorem blkDet_diagEmb {s : ℕ} (h : s ≤ n) (β : ℕ → ℕ) (c : ℕ) (hc : ∀ i : ℕ, s ≤ i → β i ≠ c) (g : GL (Fin s) κ)
    (hg : g ∈ btG s κ β) (hg' : diagEmb κ h g ∈ btG n κ β) :
    blkDet n κ β c ⟨diagEmb κ h g, hg'⟩ = blkDet s κ β c ⟨g, hg⟩ := by
  apply Units.ext
  change Matrix.det ((diagMat s n (g : Matrix (Fin s) (Fin s) κ)).toSquareBlock (fun i => β i.val) c) =
    Matrix.det ((g : Matrix (Fin s) (Fin s) κ).toSquareBlock (fun i => β i.val) c)
  let e : {i : Fin s // β i.val = c} ≃ {i : Fin n // β i.val = c} :=
    { toFun := fun i => ⟨⟨i.1.val, lt_of_lt_of_le i.1.2 h⟩, i.2⟩
      invFun := fun i => ⟨⟨i.1.val, by
        by_contra hh
        exact hc i.1.val (by omega) i.2⟩, i.2⟩
      left_inv := fun i => rfl
      right_inv := fun i => rfl }
  have hb : (diagMat s n (g : Matrix (Fin s) (Fin s) κ)).toSquareBlock (fun i => β i.val) c =
      ((g : Matrix (Fin s) (Fin s) κ).toSquareBlock (fun i => β i.val) c).submatrix e.symm e.symm := by
    ext i j
    have hi : (i.1 : Fin n).val < s := by
      by_contra hh
      exact hc _ (by omega) i.2
    have hj : (j.1 : Fin n).val < s := by
      by_contra hh
      exact hc _ (by omega) j.2
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.submatrix_apply, diagMat]
    rw [dif_pos ⟨hi, hj⟩]
    rfl
  rw [hb, Matrix.det_submatrix_equiv_self]

/- English proof (translation)
Unfold `lamGen`. Rewrite using `[MonoidHom.mul_apply, MonoidHom.mul_apply]`. Use `congr 1`. Apply `Units.ext show ψ (supSum a S (diagMat s n (g.1 : Matrix (Fin s) (Fin s) κ))) = ψ (supSum a S (g.1 : Matrix (Fin s) (Fin s) κ))` to reduce the goal to its premises. Rewrite using `[supSum_diagMat h ha]`.

Rewrite using `[MonoidHom.comp_apply, MonoidHom.comp_apply]`. Establish `e1 : Subgroup.inclusion (uniUT_le_blockUT n κ a bl) ⟨diagEmb κ h g.1, diagEmb_mem_uniUT h g.2⟩ = ⟨diagEmb κ h g.1, uniUT_le_blockUT n κ a bl (diagEmb_mem_uniUT h g.2)⟩` using `rfl`. Establish `e2 : Subgroup.inclusion (uniUT_le_blockUT s κ a bl) g = ⟨g.1, uniUT_le_blockUT s κ a bl g.2⟩` using `rfl`. Rewrite using `[e1, e2]`. Unfold `detChar`.

Rewrite using `[MonoidHom.finset_prod_apply, MonoidHom.finset_prod_apply]`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `c hc`. Rewrite using `[MonoidHom.comp_apply, MonoidHom.comp_apply]`. Use `congr 1`.

Establish `hcl` using `Finset.mem_range.mp hc`. Conclude with `blkDet_diagEmb h (coarse a bl) (c + 1) (fun i hi => by have := hs i hi; omega) g.1 _ _`.
-/
theorem lamGen_diagEmb (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) {s a : ℕ} (h : s ≤ n) (ha : a ≤ s) (bl : List ℕ) (S : Finset ℕ)
    (hs : ∀ i : ℕ, s ≤ i → bl.length < coarse a bl i) (g : ↥(uniUT s κ a bl)) :
    lamGen ψ χ n a bl S ⟨diagEmb κ h g.1, diagEmb_mem_uniUT h g.2⟩ = lamGen ψ χ s a bl S g := by
  unfold lamGen
  rw [MonoidHom.mul_apply, MonoidHom.mul_apply]
  congr 1
  · apply Units.ext
    show ψ (supSum a S (diagMat s n (g.1 : Matrix (Fin s) (Fin s) κ))) = ψ (supSum a S (g.1 : Matrix (Fin s) (Fin s) κ))
    rw [supSum_diagMat h ha]
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    have e1 : Subgroup.inclusion (uniUT_le_blockUT n κ a bl) ⟨diagEmb κ h g.1, diagEmb_mem_uniUT h g.2⟩ =
        ⟨diagEmb κ h g.1, uniUT_le_blockUT n κ a bl (diagEmb_mem_uniUT h g.2)⟩ := rfl
    have e2 : Subgroup.inclusion (uniUT_le_blockUT s κ a bl) g = ⟨g.1, uniUT_le_blockUT s κ a bl g.2⟩ := rfl
    rw [e1, e2]
    unfold detChar
    rw [MonoidHom.finset_prod_apply, MonoidHom.finset_prod_apply]
    apply Finset.prod_congr rfl
    intro c hc
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    congr 1
    have hcl := Finset.mem_range.mp hc
    exact blkDet_diagEmb h (coarse a bl) (c + 1) (fun i hi => by have := hs i hi; omega) g.1 _ _

/- English proof (translation)
Unfold `lamXm lamJ`. Rewrite using `[MonoidHom.comp_apply]`. Use `lamGen_diagEmb ψ χ (Nat.le_succ _) (by omega) _ _ (fun i hi => ?_) g` and prove the remaining obligations. Establish `h1 : coarse r (List.replicate m t) i = m + 1`. Unfold `coarse`.

Simplify using `only [blkIdx]`. Rewrite using `[if_neg (by omega), blkIdx_replicate_of_le t m (i - r) (by omega)]`. Rewrite using `[h1, List.length_replicate]`. Use linear arithmetic over natural numbers and integers.
-/
theorem lamXm_diagEmb (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (r t m : ℕ) (g : ↥(HJ κ (r + m * t) r t m)) :
    lamXm ψ χ (r + m * t + 1) r t m
      ⟨diagEmb κ (Nat.le_succ (r + m * t)) g.1, ⟨diagEmb_mem_uniUT _ g.2, diagEmb_mem_fixCol _ le_rfl g.1⟩⟩ =
      lamJ ψ χ (r + m * t) r t m g := by
  unfold lamXm lamJ
  rw [MonoidHom.comp_apply]
  refine lamGen_diagEmb ψ χ (Nat.le_succ _) (by omega) _ _ (fun i hi => ?_) g
  have h1 : coarse r (List.replicate m t) i = m + 1 := by
    unfold coarse
    simp only [blkIdx]
    rw [if_neg (by omega), blkIdx_replicate_of_le t m (i - r) (by omega)]
  rw [h1, List.length_replicate]
  omega

end DiagChar

section Sym

variable {n : ℕ} {κ : Type} [CommRing κ]

/- English proof (translation)
Use extensionality with `M`. Simplify using `only [SetLike.mem_coe, uSet, Set.mem_setOf_eq]`. Establish `hU` using `Set.ext_iff.mp (uniUT_full_eq (n := n) (κ := κ)) M`. Simplify using `only [SetLike.mem_coe, uSet, Set.mem_setOf_eq] at hU`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2⟩`. Take `⟨d, o⟩` from `hU.mp h1`. Use `⟨d, fun i j hne hP => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hlt : i < j`. Establish `hh : rS ≤ i.val ∧ i.val < rS + k ∧ j.val = rS + k`.

Assume the negation of the conclusion as `hc`. Conclude with `hP ⟨hlt, hc⟩`. Conclude with `h2 i j hh.1 hh.2.1 hh.2.2`. Conclude with `o i j hne hlt`. Introduce and unpack `⟨d, o⟩ show M ∈ uniUT n κ n [] ∧ ∀ i j : Fin n, rS ≤ i.val → i.val < rS + k → j.val = rS + k → (M : Matrix (Fin n) (Fin n) κ) i j = 0`.

Use `⟨hU.mpr ⟨d, fun i j hne hlt => o i j hne (fun h => hlt h.1)⟩, fun i j h1 h2 h3 => ?_⟩` and prove the remaining obligations. Establish `hlt : i < j` using `by show i.val < j.val`. Use linear arithmetic over natural numbers and integers. Conclude with `o i j (ne_of_lt hlt) (fun h => h.2 ⟨h1, h2, h3⟩)`.
-/
theorem HPsym_eq (k rS : ℕ) : ((HPsym κ n k rS : Subgroup (GL (Fin n) κ)) : Set (GL (Fin n) κ)) =
    uSet κ (fun i j : Fin n => i < j ∧ ¬ (rS ≤ i.val ∧ i.val < rS + k ∧ j.val = rS + k)) := by
  ext M
  simp only [SetLike.mem_coe, uSet, Set.mem_setOf_eq]
  have hU := Set.ext_iff.mp (uniUT_full_eq (n := n) (κ := κ)) M
  simp only [SetLike.mem_coe, uSet, Set.mem_setOf_eq] at hU
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨d, o⟩ := hU.mp h1
    refine ⟨d, fun i j hne hP => ?_⟩
    by_cases hlt : i < j
    · have hh : rS ≤ i.val ∧ i.val < rS + k ∧ j.val = rS + k := by
        by_contra hc
        exact hP ⟨hlt, hc⟩
      exact h2 i j hh.1 hh.2.1 hh.2.2
    · exact o i j hne hlt
  · rintro ⟨d, o⟩
    show M ∈ uniUT n κ n [] ∧ ∀ i j : Fin n, rS ≤ i.val → i.val < rS + k → j.val = rS + k → (M : Matrix (Fin n) (Fin n) κ) i j = 0
    refine ⟨hU.mpr ⟨d, fun i j hne hlt => o i j hne (fun h => hlt h.1)⟩, fun i j h1 h2 h3 => ?_⟩
    have hlt : i < j := by
      show i.val < j.val
      omega
    exact o i j (ne_of_lt hlt) (fun h => h.2 ⟨h1, h2, h3⟩)

/- English proof (translation)
Establish `hA : Nat.card {p : Fin n × Fin n // p.1 < p.2} = n * (n - 1) / 2` using `card_lt_pairs n`. Rewrite `hA`, the goal using `[Nat.card_eq_fintype_card, Fintype.card_subtype]`. Rewrite using `[← hA]`. Establish `hsub : (Finset.univ.filter fun p : Fin n × Fin n => rS ≤ p.1.val ∧ p.1.val < rS + k ∧ p.2.val = rS + k) ⊆ Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2`. Introduce `p hp`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢`. Take `⟨h1, h2, h3⟩` from `hp`. Use `show p.1.val < p.2.val`. Use linear arithmetic over natural numbers and integers. Establish `hB : (Finset.univ.filter fun p : Fin n × Fin n => rS ≤ p.1.val ∧ p.1.val < rS + k ∧ p.2.val = rS + k).card = k`.

Rewrite using `[← Fintype.card_subtype]`. Establish `e : {p : Fin n × Fin n // rS ≤ p.1.val ∧ p.1.val < rS + k ∧ p.2.val = rS + k} ≃ Fin k` using `{ toFun := fun p => ⟨p.1.1.val - rS, by obtain ⟨h1, h2, h3⟩ := p.2; omega⟩ invFun := fun i => ⟨(⟨rS + i.val, by omega⟩, ⟨rS + k, hn⟩), Nat.le_add_right _ _, Nat.add_lt_add_left i.2 _, rfl⟩ left_inv := fun p => by`. Take `⟨⟨a, b⟩, h1, h2, h3⟩` from `p`. Simplify using `only at h1 h2 h3`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Prod.ext` to reduce the goal to its premises. Apply `Fin.ext show rS + (a.val - rS) = a.val` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers. Apply `Fin.ext show rS + k = b.val` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers.

Use `right_inv := fun i => by`. Apply `Fin.ext` to reduce the goal to its premises. Use `show rS + i.val - rS = i.val`. Use `omega }`. Rewrite using `[Fintype.card_congr e, Fintype.card_fin]`.

Establish `hsd : (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ ¬ (rS ≤ p.1.val ∧ p.1.val < rS + k ∧ p.2.val = rS + k)) = (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2) \ (Finset.univ.filter fun p : Fin n × Fin n => rS ≤ p.1.val ∧ p.1.val < rS + k ∧ p.2.val = rS + k)`. Use extensionality with `p`. Simplify using `only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]`. Rewrite using `[hsd, Finset.card_sdiff_of_subset hsub, hB]`.
-/
theorem card_sym_pairs (k rS : ℕ) (hn : rS + k < n) :
    Nat.card {p : Fin n × Fin n // p.1 < p.2 ∧ ¬ (rS ≤ p.1.val ∧ p.1.val < rS + k ∧ p.2.val = rS + k)} = n * (n - 1) / 2 - k := by
  have hA : Nat.card {p : Fin n × Fin n // p.1 < p.2} = n * (n - 1) / 2 := card_lt_pairs n
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hA ⊢
  rw [← hA]
  have hsub : (Finset.univ.filter fun p : Fin n × Fin n => rS ≤ p.1.val ∧ p.1.val < rS + k ∧ p.2.val = rS + k) ⊆
      Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    obtain ⟨h1, h2, h3⟩ := hp
    show p.1.val < p.2.val
    omega
  have hB : (Finset.univ.filter fun p : Fin n × Fin n => rS ≤ p.1.val ∧ p.1.val < rS + k ∧ p.2.val = rS + k).card = k := by
    rw [← Fintype.card_subtype]
    have e : {p : Fin n × Fin n // rS ≤ p.1.val ∧ p.1.val < rS + k ∧ p.2.val = rS + k} ≃ Fin k :=
      { toFun := fun p => ⟨p.1.1.val - rS, by obtain ⟨h1, h2, h3⟩ := p.2; omega⟩
        invFun := fun i => ⟨(⟨rS + i.val, by omega⟩, ⟨rS + k, hn⟩), Nat.le_add_right _ _, Nat.add_lt_add_left i.2 _, rfl⟩
        left_inv := fun p => by
          obtain ⟨⟨a, b⟩, h1, h2, h3⟩ := p
          dsimp only at h1 h2 h3
          apply Subtype.ext
          apply Prod.ext
          · apply Fin.ext
            show rS + (a.val - rS) = a.val
            omega
          · apply Fin.ext
            show rS + k = b.val
            omega
        right_inv := fun i => by
          apply Fin.ext
          show rS + i.val - rS = i.val
          omega }
    rw [Fintype.card_congr e, Fintype.card_fin]
  have hsd : (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ ¬ (rS ≤ p.1.val ∧ p.1.val < rS + k ∧ p.2.val = rS + k)) =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2) \
        (Finset.univ.filter fun p : Fin n × Fin n => rS ≤ p.1.val ∧ p.1.val < rS + k ∧ p.2.val = rS + k) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
  rw [hsd, Finset.card_sdiff_of_subset hsub, hB]

/- English proof (translation)
Establish `h1 : Nat.card ↥(HPsym κ n k rS) = Nat.card ↥(uSet κ (fun i j : Fin n => i < j ∧ ¬ (rS ≤ i.val ∧ i.val < rS + k ∧ j.val = rS + k)))`. Rewrite using `[← HPsym_eq]`. Both sides reduce to the same expression. Rewrite using `[h1, card_uSet (P := fun i j : Fin n => i < j ∧ ¬ (rS ≤ i.val ∧ i.val < rS + k ∧ j.val = rS + k)) (fun _ _ h => h.1)]`. Use `congr 1`.

Conclude with `card_sym_pairs k rS hn`.
-/
theorem card_HPsym (κ : Type) [CommRing κ] (n k rS : ℕ) (hn : rS + k < n) :
    Nat.card ↥(HPsym κ n k rS) = Nat.card κ ^ (n * (n - 1) / 2 - k) := by
  have h1 : Nat.card ↥(HPsym κ n k rS) =
      Nat.card ↥(uSet κ (fun i j : Fin n => i < j ∧ ¬ (rS ≤ i.val ∧ i.val < rS + k ∧ j.val = rS + k))) := by
    rw [← HPsym_eq]; rfl
  rw [h1, card_uSet (P := fun i j : Fin n => i < j ∧ ¬ (rS ≤ i.val ∧ i.val < rS + k ∧ j.val = rS + k)) (fun _ _ h => h.1)]
  congr 1
  exact card_sym_pairs k rS hn

/- English proof (translation)
Establish `e1 : k + 2 * s + 1 - 1 = k + 2 * s` using `by omega`. Establish `e2 : (k + 2 * s + 1) * (k + 2 * s) = k * (k - 1) + 2 * (k + s * (2 * k + 2 * s + 1))`. Consider the cases of `k with`. Consider the case `zero => simp`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `succ k => simp only [Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree. Establish `e4 : (k + 2 * s + 1) ^ 2 = (k + 1) ^ 2 + 2 * s + 2 * (s * (2 * k + 2 * s + 1))` using `by ring`. Establish `e3 : (k + 2 * s + 1) ^ 2 - (k + 1) ^ 2 - 2 * s = 2 * (s * (2 * k + 2 * s + 1))`. Rewrite using `[e4, Nat.add_assoc, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]`.

Rewrite using `[e1, e2, e3, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]`. Generalize the expression as in `k * (k - 1) / 2 = A`. Generalize the expression as in `s * (2 * k + 2 * s + 1) = B`. Use linear arithmetic over natural numbers and integers.
-/
theorem sym_arith (k s : ℕ) :
    (k + 2 * s + 1) * (k + 2 * s + 1 - 1) / 2 - k =
      ((k + 2 * s + 1) ^ 2 - (k + 1) ^ 2 - 2 * s) / 2 + k * (k - 1) / 2 := by
  have e1 : k + 2 * s + 1 - 1 = k + 2 * s := by omega
  have e2 : (k + 2 * s + 1) * (k + 2 * s) = k * (k - 1) + 2 * (k + s * (2 * k + 2 * s + 1)) := by
    cases k with
    | zero => simp; ring
    | succ k => simp only [Nat.add_sub_cancel]; ring
  have e4 : (k + 2 * s + 1) ^ 2 = (k + 1) ^ 2 + 2 * s + 2 * (s * (2 * k + 2 * s + 1)) := by ring
  have e3 : (k + 2 * s + 1) ^ 2 - (k + 1) ^ 2 - 2 * s = 2 * (s * (2 * k + 2 * s + 1)) := by
    rw [e4, Nat.add_assoc, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
  rw [e1, e2, e3, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
  generalize k * (k - 1) / 2 = A
  generalize s * (2 * k + 2 * s + 1) = B
  omega

end Sym

/- English proof (translation)
Take `⟨p, hp⟩` from `hev`. Take `⟨θ, h1, h2, hc⟩` from `card_GL_eq_card_pow_mul_theta F (k + m - 1) h3`. Use `⟨θ, h1, h2, ?_⟩` and prove the remaining obligations. Establish `hlt : m / 2 - 1 + k < k + m - 1` using `by omega`. Establish `hH` using `card_HPsym F (k + m - 1) k (m / 2 - 1) hlt`.

Rewrite `hH` using `[Nat.card_eq_fintype_card (α := F)]`. Establish `hmul` using `Subgroup.card_mul_index (HPsym F (k + m - 1) k (m / 2 - 1))`. Rewrite `hmul` using `[hH]`. Establish `hexp : (k + m - 1) * (k + m - 1) = ((k + m - 1) * (k + m - 1 - 1) / 2 - k) + ((k + m - 1) ^ 2 + 3 * k + 1 + 2 * (m / 2 - 1)) / 2`. Substitute `hp` using the available equality.

Take `⟨q', rfl⟩ : ∃ q', p = q' + 1` from `⟨p - 1, by omega⟩`. Establish `hr : k + (q' + 1 + (q' + 1)) - 1 = k + 2 * q' + 1` using `by omega`. Establish `hd : (q' + 1 + (q' + 1)) / 2 - 1 = q'` using `by omega`. Rewrite using `[hr, hd]`. Establish `e1 : k + 2 * q' + 1 - 1 = k + 2 * q'` using `by omega`.

Rewrite using `[e1]`. Establish `e2 : (k + 2 * q' + 1) ^ 2 + 3 * k + 1 + 2 * q' = (k + 2 * q' + 1) * (k + 2 * q') + 2 * (k + 2 * q' + 1) + 2 * k` using `by ring`. Establish `e3 : (k + 2 * q' + 1) * (k + 2 * q' + 1) = (k + 2 * q' + 1) * (k + 2 * q') + (k + 2 * q' + 1)` using `by ring`. Establish `hE : (k + 2 * q' + 1) * (k + 2 * q') % 2 = 0`. Break down `Nat.even_mul_succ_self (k + 2 * q') with ⟨t, ht⟩` into its components or cases.

Rewrite using `[Nat.mul_comm, ht]`. Use linear arithmetic over natural numbers and integers. Establish `hK : 2 * k ≤ (k + 2 * q' + 1) * (k + 2 * q')`. Break down `Nat.eq_zero_or_pos k with hk | hk` into its components or cases. Substitute `hk` using the available equality.

Simplify using the standard rewrite rules. Conclude with `Nat.mul_le_mul (by omega) (by omega)`. Rewrite using `[e2, e3]`. Generalize the expression as in `(k + 2 * q' + 1) * (k + 2 * q') = A at hE hK ⊢`. Use linear arithmetic over natural numbers and integers.

Establish `hpos : (0 : ℝ) < (Fintype.card F : ℝ) ^ ((k + m - 1) * (k + m - 1 - 1) / 2 - k)`. Establish `: (0 : ℝ) < (Fintype.card F : ℝ)`. Establish `: (3 : ℝ) ≤ (Fintype.card F : ℝ)` using `by exact_mod_cast h3`. Combine the linear equalities and inequalities to obtain the conclusion. Check the signs of the components of the expression.

Establish `hR : (Fintype.card F : ℝ) ^ ((k + m - 1) * (k + m - 1 - 1) / 2 - k) * ((HPsym F (k + m - 1) k (m / 2 - 1)).index : ℝ) = (Fintype.card F : ℝ) ^ ((k + m - 1) * (k + m - 1 - 1) / 2 - k) * ((Fintype.card F : ℝ) ^ (((k + m - 1) ^ 2 + 3 * k + 1 + 2 * (m / 2 - 1)) / 2) * θ)`. Establish `hm` using `congrArg (fun x : ℕ => (x : ℝ)) hmul`. Move the coercions through the operations in `at hm`. Rewrite using `[hm, hc, hexp, pow_add, mul_assoc]`. Conclude with `mul_left_cancel₀ hpos.ne' hR`.
-/
theorem index_HPsym (F : Type) [Field F] [Fintype F] [DecidableEq F] (k m : ℕ) (hm : 2 ≤ m) (hev : Even m)
    (h3 : 3 ≤ Fintype.card F) :
    ∃ θ : ℝ, 1 / 2 ≤ θ ∧ θ ≤ 1 ∧ ((HPsym F (k + m - 1) k (m / 2 - 1)).index : ℝ) =
      (Fintype.card F : ℝ) ^ (((k + m - 1) ^ 2 + 3 * k + 1 + 2 * (m / 2 - 1)) / 2) * θ := by
  obtain ⟨p, hp⟩ := hev
  obtain ⟨θ, h1, h2, hc⟩ := card_GL_eq_card_pow_mul_theta F (k + m - 1) h3
  refine ⟨θ, h1, h2, ?_⟩
  have hlt : m / 2 - 1 + k < k + m - 1 := by omega
  have hH := card_HPsym F (k + m - 1) k (m / 2 - 1) hlt
  rw [Nat.card_eq_fintype_card (α := F)] at hH
  have hmul := Subgroup.card_mul_index (HPsym F (k + m - 1) k (m / 2 - 1))
  rw [hH] at hmul
  have hexp : (k + m - 1) * (k + m - 1) = ((k + m - 1) * (k + m - 1 - 1) / 2 - k) +
      ((k + m - 1) ^ 2 + 3 * k + 1 + 2 * (m / 2 - 1)) / 2 := by
    subst hp
    obtain ⟨q', rfl⟩ : ∃ q', p = q' + 1 := ⟨p - 1, by omega⟩
    have hr : k + (q' + 1 + (q' + 1)) - 1 = k + 2 * q' + 1 := by omega
    have hd : (q' + 1 + (q' + 1)) / 2 - 1 = q' := by omega
    rw [hr, hd]
    have e1 : k + 2 * q' + 1 - 1 = k + 2 * q' := by omega
    rw [e1]
    have e2 : (k + 2 * q' + 1) ^ 2 + 3 * k + 1 + 2 * q' = (k + 2 * q' + 1) * (k + 2 * q') + 2 * (k + 2 * q' + 1) + 2 * k := by ring
    have e3 : (k + 2 * q' + 1) * (k + 2 * q' + 1) = (k + 2 * q' + 1) * (k + 2 * q') + (k + 2 * q' + 1) := by ring
    have hE : (k + 2 * q' + 1) * (k + 2 * q') % 2 = 0 := by
      rcases Nat.even_mul_succ_self (k + 2 * q') with ⟨t, ht⟩
      rw [Nat.mul_comm, ht]
      omega
    have hK : 2 * k ≤ (k + 2 * q' + 1) * (k + 2 * q') := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp
      · exact Nat.mul_le_mul (by omega) (by omega)
    rw [e2, e3]
    generalize (k + 2 * q' + 1) * (k + 2 * q') = A at hE hK ⊢
    omega
  have hpos : (0 : ℝ) < (Fintype.card F : ℝ) ^ ((k + m - 1) * (k + m - 1 - 1) / 2 - k) := by
    have : (0 : ℝ) < (Fintype.card F : ℝ) := by
      have : (3 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast h3
      linarith
    positivity
  have hR : (Fintype.card F : ℝ) ^ ((k + m - 1) * (k + m - 1 - 1) / 2 - k) * ((HPsym F (k + m - 1) k (m / 2 - 1)).index : ℝ) =
      (Fintype.card F : ℝ) ^ ((k + m - 1) * (k + m - 1 - 1) / 2 - k) *
        ((Fintype.card F : ℝ) ^ (((k + m - 1) ^ 2 + 3 * k + 1 + 2 * (m / 2 - 1)) / 2) * θ) := by
    have hm := congrArg (fun x : ℕ => (x : ℝ)) hmul
    push_cast at hm
    rw [hm, hc, hexp, pow_add, mul_assoc]
  exact mul_left_cancel₀ hpos.ne' hR

section More

variable {κ : Type} [CommRing κ] {K : Type} [Field K]

/- English proof (translation)
Substitute `hn` using the available equality. Conclude with `HXm_eq_map r t m`.
-/
theorem HXm_eq_map' (n' r t m : ℕ) (hn : n' = r + m * t) :
    HXm κ (n' + 1) r t m = (HJ κ n' r t m).map (diagEmb κ (Nat.le_succ n')) := by
  subst hn
  exact HXm_eq_map r t m

/- English proof (translation)
Substitute `hn` using the available equality. Conclude with `lamXm_diagEmb ψ χ r t m h`.
-/
theorem lamXm_diag (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (n' r t m : ℕ) (hn : n' = r + m * t) (h : ↥(HJ κ n' r t m))
    (hm : diagEmb κ (Nat.le_succ n') h.1 ∈ HXm κ (n' + 1) r t m) :
    lamXm ψ χ (n' + 1) r t m ⟨_, hm⟩ = lamJ ψ χ n' r t m h := by
  subst hn
  exact lamXm_diagEmb ψ χ r t m h

/- English proof (translation)
Unfold `lamJ lamKJ lamK lamGen`. Simplify using `only [MonoidHom.mul_apply, MonoidHom.comp_apply]`. Establish `hs : supChar ψ n r (List.replicate j t) (Finset.range (r - 1)) (Subgroup.inclusion (HK_le_uniUT n κ r (List.replicate j t)) M) = 1`. Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `ψ (supSum r (Finset.range (r - 1)) ((M.1 : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ)) = 1`.

Establish `h0 : supSum r (Finset.range (r - 1)) ((M.1 : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) = 0`. Take `⟨M', hM', hMe⟩` from `M.2`. Establish `hker : blkHom n κ (coarse r (List.replicate j t)) 0 M' = 1` using `hM'`. Unfold `supSum`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `i _`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `j' _`. Use `split_ifs with hc`. Take `⟨hc1, hc2, -⟩` from `hc`.

Establish `hi0 : coarse r (List.replicate j t) i.val = 0`. Simplify using `only [coarse, blkIdx, if_pos (show i.val < r by omega)]`. Establish `hj0 : coarse r (List.replicate j t) j'.val = 0`. Simplify using `only [coarse, blkIdx, if_pos hc2]`. Establish `hk` using `congrFun (congrFun hker ⟨i, hi0⟩) ⟨j', hj0⟩`.

Rewrite using `[blkHom_apply, Matrix.one_apply_ne (fun e => by`. Use `congrArg (fun x => x.1.val) e` as an intermediate fact. Simplify using `only at this`. Use the proof step `omega)] at hk`. Rewrite using `[← hMe]`.

Conclude with `hk`. Both sides reduce to the same expression. Rewrite using `[h0, AddChar.map_zero_eq_one]`. Rewrite using `[hs, one_mul]`. Both sides reduce to the same expression.
-/
theorem lamJ_on_HKJ (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (n r t j : ℕ) (M : ↥(HKJ κ n r t j)) :
    lamJ ψ χ n r t j (Subgroup.inclusion (HK_le_uniUT n κ r _) M) = lamKJ χ n r t j M := by
  unfold lamJ lamKJ lamK lamGen
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply]
  have hs : supChar ψ n r (List.replicate j t) (Finset.range (r - 1)) (Subgroup.inclusion (HK_le_uniUT n κ r (List.replicate j t)) M) = 1 := by
    apply Units.ext
    change ψ (supSum r (Finset.range (r - 1)) ((M.1 : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ)) = 1
    have h0 : supSum r (Finset.range (r - 1)) ((M.1 : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) = 0 := by
      obtain ⟨M', hM', hMe⟩ := M.2
      have hker : blkHom n κ (coarse r (List.replicate j t)) 0 M' = 1 := hM'
      unfold supSum
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j' _
      split_ifs with hc
      · obtain ⟨hc1, hc2, -⟩ := hc
        have hi0 : coarse r (List.replicate j t) i.val = 0 := by
          simp only [coarse, blkIdx, if_pos (show i.val < r by omega)]
        have hj0 : coarse r (List.replicate j t) j'.val = 0 := by
          simp only [coarse, blkIdx, if_pos hc2]
        have hk := congrFun (congrFun hker ⟨i, hi0⟩) ⟨j', hj0⟩
        rw [blkHom_apply, Matrix.one_apply_ne (fun e => by
          have := congrArg (fun x => x.1.val) e
          simp only at this
          omega)] at hk
        rw [← hMe]
        exact hk
      · rfl
    rw [h0, AddChar.map_zero_eq_one]
  rw [hs, one_mul]
  rfl

/- English proof (translation)
Use `show (diagMat n (n + 1) (h : Matrix (Fin n) (Fin n) κ)).mulVec (Fin.snoc (α := fun _ => κ) v c) = Fin.snoc (α := fun _ => κ) ((h : Matrix (Fin n) (Fin n) κ).mulVec v) c`. Use extensionality with `i`. Use `Fin.lastCases ?_ (fun i => ?_) i` and prove the remaining obligations. Simplify using `[Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, diagMat, Matrix.one_apply]`. Simplify using `[Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, diagMat, Matrix.one_apply, (Fin.castSucc_lt_last i).ne]`.
-/
theorem diagEmb_mulVec_snoc {n : ℕ} (h : GL (Fin n) κ) (v : Fin n → κ) (c : κ) :
    (diagEmb κ (Nat.le_succ n) h).1.mulVec (Fin.snoc (α := fun _ => κ) v c) =
      Fin.snoc (α := fun _ => κ) (h.1.mulVec v) c := by
  show (diagMat n (n + 1) (h : Matrix (Fin n) (Fin n) κ)).mulVec (Fin.snoc (α := fun _ => κ) v c) = Fin.snoc (α := fun _ => κ) ((h : Matrix (Fin n) (Fin n) κ).mulVec v) c
  ext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, diagMat, Matrix.one_apply]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, diagMat, Matrix.one_apply, (Fin.castSucc_lt_last i).ne]

end More

section Res

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

/- English proof (translation)
Unfold `lamQP`. Use `congr 1`. Unfold `Formalism.L2.DIV.resChar`. Rewrite using `[dif_pos ⟨χ, hχ⟩]`. Conclude with `huniq _ (Exists.choose_spec _)`.
-/
theorem lambdaAtPrime_eq_of_residueCharacter (ξ : Formalism.L2.DIV.Chr F E L) (P : HeightOneSpectrum (𝓞 E)) (n a b : ℕ) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Lˣ)
    (hχ : Formalism.L2.DIV.IsResChar ξ P χ) (huniq : ∀ χ', Formalism.L2.DIV.IsResChar ξ P χ' → χ' = χ) :
    lamQP ξ P n a b = lamQ χ n a b := by
  unfold lamQP
  congr 1
  unfold Formalism.L2.DIV.resChar
  rw [dif_pos ⟨χ, hχ⟩]
  exact huniq _ (Exists.choose_spec _)

/- English proof (translation)
Unfold `lamQP`. Establish `h1 : Formalism.L2.DIV.resChar ξ P = 1`. Unfold `Formalism.L2.DIV.resChar`. Rewrite using `[dif_neg hno]`. Rewrite using `[h1]`.

Unfold `lamQ detChar`. Simplify using the standard rewrite rules.
-/
theorem lambdaAtPrime_eq_one_of_no_residueCharacter (ξ : Formalism.L2.DIV.Chr F E L) (P : HeightOneSpectrum (𝓞 E)) (n a b : ℕ)
    (hno : ¬ ∃ χ, Formalism.L2.DIV.IsResChar ξ P χ) : lamQP ξ P n a b = 1 := by
  unfold lamQP
  have h1 : Formalism.L2.DIV.resChar ξ P = 1 := by
    unfold Formalism.L2.DIV.resChar
    rw [dif_neg hno]
  rw [h1]
  unfold lamQ detChar
  simp

end Res

section ParId

variable {n : ℕ} {κ : Type} [CommRing κ]

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `M _`. Use `show (M : Matrix (Fin r) (Fin r) κ).BlockTriangular (fun i => coarse r [] i.val)`. Introduce `i j hij`. It suffices to derive a contradiction.

Simplify using `only [coarse, blkIdx, if_pos i.2, if_pos j.2] at hij`. Conclude with `lt_irrefl _ hij`.
-/
theorem blockUT_self_top (r : ℕ) : blockUT r κ r [] = ⊤ := by
  rw [eq_top_iff]
  intro M _
  show (M : Matrix (Fin r) (Fin r) κ).BlockTriangular (fun i => coarse r [] i.val)
  intro i j hij
  exfalso
  simp only [coarse, blkIdx, if_pos i.2, if_pos j.2] at hij
  exact lt_irrefl _ hij

/- English proof (translation)
Use extensionality with `M`. Unfold `HPar`. Rewrite using `[Subgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce `hM`.

Use `⟨⟨M, uniUT_le_blockUT n κ r bl hM⟩, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[Subgroup.mem_comap]`. Take `⟨h1, h2⟩` from `id hM`. Use `show blk0 n κ h bl ⟨M, uniUT_le_blockUT n κ r bl hM⟩ ∈ btG r κ (fine r []) ∧ ∀ i : Fin r, i.val < r → ((blk0 n κ h bl ⟨M, uniUT_le_blockUT n κ r bl hM⟩ : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i i = 1`. Use `⟨?_, fun i _ => ?_⟩` and prove the remaining obligations.

Use `show (restr h (M : Matrix (Fin n) (Fin n) κ)).BlockTriangular (fun i => fine r [] i.val)`. Introduce `i j hij`. Conclude with `h1 (i := Fin.castLE h i) (j := Fin.castLE h j) ((fine_lt_right (bl := bl) (show (Fin.castLE h i).val < r from i.2)).mpr ((fine_lt_right (bl := []) i.2).mp hij))`. Use `show restr h (M : Matrix (Fin n) (Fin n) κ) i i = 1`. Conclude with `h2 (Fin.castLE h i) i.2`.

Introduce and unpack `⟨M', hM', rfl⟩`. Rewrite `hM'` using `[Subgroup.mem_comap]`. Take `⟨h1, h2⟩` from `hM'`. Establish `hB` using `M'.2`. Use `show (M' : GL (Fin n) κ) ∈ btG n κ (fine r bl) ∧ ∀ i : Fin n, i.val < r → ((M' : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) i i = 1`.

Use `⟨?_, fun i hi => h2 ⟨i.val, hi⟩ hi⟩` and prove the remaining obligations. Use `show ((M' : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).BlockTriangular (fun i => fine r bl i.val)`. Introduce `i j hij`. Establish `hij' : fine r bl j.val < fine r bl i.val` using `hij`. Distinguish the cases in `hi : i.val < r`.

Establish `hfi : fine r bl i.val = i.val` using `by simp only [fine, if_pos hi]`. Establish `hj : j.val < r`. Assume the negation of the conclusion as `hj`. Establish `hfj : fine r bl j.val = r + blkIdx bl (j.val - r)` using `by simp only [fine, if_neg hj]`. Use linear arithmetic over natural numbers and integers.

Establish `hfj : fine r bl j.val = j.val` using `by simp only [fine, if_pos hj]`. Conclude with `h1 (i := ⟨i.val, hi⟩) (j := ⟨j.val, hj⟩) (show fine r [] j.val < fine r [] i.val by simp only [fine, if_pos hi, if_pos hj]; omega)`. Apply `hB show coarse r bl j.val < coarse r bl i.val` to reduce the goal to its premises. Establish `hfi : fine r bl i.val = r + blkIdx bl (i.val - r)` using `by simp only [fine, if_neg hi]`. Establish `hci : coarse r bl i.val = blkIdx bl (i.val - r) + 1` using `by simp only [coarse, blkIdx, if_neg hi]`.

Rewrite using `[hci]`. Distinguish the cases in `hj : j.val < r`. Establish `hcj : coarse r bl j.val = 0` using `by simp only [coarse, blkIdx, if_pos hj]`. Use linear arithmetic over natural numbers and integers. Establish `hfj : fine r bl j.val = r + blkIdx bl (j.val - r)` using `by simp only [fine, if_neg hj]`.

Establish `hcj : coarse r bl j.val = blkIdx bl (j.val - r) + 1` using `by simp only [coarse, blkIdx, if_neg hj]`. Use linear arithmetic over natural numbers and integers.
-/
theorem uniUT_eq_HPar {r : ℕ} (h : r ≤ n) (bl : List ℕ) : uniUT n κ r bl = HPar n κ h bl (HU κ r) := by
  ext M
  unfold HPar
  rw [Subgroup.mem_map]
  constructor
  · intro hM
    refine ⟨⟨M, uniUT_le_blockUT n κ r bl hM⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    obtain ⟨h1, h2⟩ := id hM
    show blk0 n κ h bl ⟨M, uniUT_le_blockUT n κ r bl hM⟩ ∈ btG r κ (fine r []) ∧
      ∀ i : Fin r, i.val < r → ((blk0 n κ h bl ⟨M, uniUT_le_blockUT n κ r bl hM⟩ : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i i = 1
    refine ⟨?_, fun i _ => ?_⟩
    · show (restr h (M : Matrix (Fin n) (Fin n) κ)).BlockTriangular (fun i => fine r [] i.val)
      intro i j hij
      exact h1 (i := Fin.castLE h i) (j := Fin.castLE h j)
        ((fine_lt_right (bl := bl) (show (Fin.castLE h i).val < r from i.2)).mpr ((fine_lt_right (bl := []) i.2).mp hij))
    · show restr h (M : Matrix (Fin n) (Fin n) κ) i i = 1
      exact h2 (Fin.castLE h i) i.2
  · rintro ⟨M', hM', rfl⟩
    rw [Subgroup.mem_comap] at hM'
    obtain ⟨h1, h2⟩ := hM'
    have hB := M'.2
    show (M' : GL (Fin n) κ) ∈ btG n κ (fine r bl) ∧ ∀ i : Fin n, i.val < r → ((M' : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) i i = 1
    refine ⟨?_, fun i hi => h2 ⟨i.val, hi⟩ hi⟩
    show ((M' : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).BlockTriangular (fun i => fine r bl i.val)
    intro i j hij
    have hij' : fine r bl j.val < fine r bl i.val := hij
    by_cases hi : i.val < r
    · have hfi : fine r bl i.val = i.val := by simp only [fine, if_pos hi]
      have hj : j.val < r := by
        by_contra hj
        have hfj : fine r bl j.val = r + blkIdx bl (j.val - r) := by simp only [fine, if_neg hj]
        omega
      have hfj : fine r bl j.val = j.val := by simp only [fine, if_pos hj]
      exact h1 (i := ⟨i.val, hi⟩) (j := ⟨j.val, hj⟩)
        (show fine r [] j.val < fine r [] i.val by simp only [fine, if_pos hi, if_pos hj]; omega)
    · apply hB
      show coarse r bl j.val < coarse r bl i.val
      have hfi : fine r bl i.val = r + blkIdx bl (i.val - r) := by simp only [fine, if_neg hi]
      have hci : coarse r bl i.val = blkIdx bl (i.val - r) + 1 := by simp only [coarse, blkIdx, if_neg hi]
      rw [hci]
      by_cases hj : j.val < r
      · have hcj : coarse r bl j.val = 0 := by simp only [coarse, blkIdx, if_pos hj]
        omega
      · have hfj : fine r bl j.val = r + blkIdx bl (j.val - r) := by simp only [fine, if_neg hj]
        have hcj : coarse r bl j.val = blkIdx bl (j.val - r) + 1 := by simp only [coarse, blkIdx, if_neg hj]
        omega

/- English proof (translation)
Unfold `HK HPar`. Use `congr 1`. Use extensionality with `M`. Rewrite using `[MonoidHom.mem_ker, Subgroup.mem_comap, Subgroup.mem_bot]`. Prove the components needed by the constructor for the conclusion.

Introduce `hM`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Use `show restr h (M.1 : Matrix (Fin n) (Fin n) κ) i j = (1 : Matrix (Fin r) (Fin r) κ) i j`. Establish `hi0 : coarse r bl (Fin.castLE h i).val = 0` using `by simp only [coarse, blkIdx, Fin.coe_castLE, if_pos i.2]`.

Establish `hj0 : coarse r bl (Fin.castLE h j).val = 0` using `by simp only [coarse, blkIdx, Fin.coe_castLE, if_pos j.2]`. Establish `hk` using `congrFun (congrFun hM ⟨Fin.castLE h i, hi0⟩) ⟨Fin.castLE h j, hj0⟩`. Rewrite `hk` using `[blkHom_apply]`. Establish `hk' : restr h (M.1 : Matrix (Fin n) (Fin n) κ) i j = (1 : Matrix {x : Fin n // coarse r bl x.val = 0} {x : Fin n // coarse r bl x.val = 0} κ) ⟨Fin.castLE h i, hi0⟩ ⟨Fin.castLE h j, hj0⟩` using `hk`. Rewrite using `[hk']`.

Simplify using `[Matrix.one_apply, Subtype.ext_iff, Fin.ext_iff]`. Introduce `hM`. Use extensionality with `i j`. Rewrite using `[blkHom_apply]`. Establish `hi : (i.1 : Fin n).val < r`.

Assume the negation of the conclusion as `hh`. Conclude with `absurd i.2 (by simp only [coarse, blkIdx, if_neg hh]; omega)`. Establish `hj : (j.1 : Fin n).val < r`. Assume the negation of the conclusion as `hh`. Conclude with `absurd j.2 (by simp only [coarse, blkIdx, if_neg hh]; omega)`.

Establish `hk` using `congrArg (fun X : GL (Fin r) κ => (X : Matrix (Fin r) (Fin r) κ) ⟨i.1.val, hi⟩ ⟨j.1.val, hj⟩) hM`. Establish `hk' : (M.1 : Matrix (Fin n) (Fin n) κ) i.1 j.1 = (1 : Matrix (Fin r) (Fin r) κ) ⟨i.1.val, hi⟩ ⟨j.1.val, hj⟩` using `hk`. Rewrite using `[hk']`. Simplify using `[Matrix.one_apply, Subtype.ext_iff, Fin.ext_iff]`.
-/
theorem HK_eq_HPar {r : ℕ} (h : r ≤ n) (bl : List ℕ) : HK n κ r bl = HPar n κ h bl ⊥ := by
  unfold HK HPar
  congr 1
  ext M
  rw [MonoidHom.mem_ker, Subgroup.mem_comap, Subgroup.mem_bot]
  constructor
  · intro hM
    apply Units.ext
    ext i j
    show restr h (M.1 : Matrix (Fin n) (Fin n) κ) i j = (1 : Matrix (Fin r) (Fin r) κ) i j
    have hi0 : coarse r bl (Fin.castLE h i).val = 0 := by simp only [coarse, blkIdx, Fin.coe_castLE, if_pos i.2]
    have hj0 : coarse r bl (Fin.castLE h j).val = 0 := by simp only [coarse, blkIdx, Fin.coe_castLE, if_pos j.2]
    have hk := congrFun (congrFun hM ⟨Fin.castLE h i, hi0⟩) ⟨Fin.castLE h j, hj0⟩
    rw [blkHom_apply] at hk
    have hk' : restr h (M.1 : Matrix (Fin n) (Fin n) κ) i j = (1 : Matrix {x : Fin n // coarse r bl x.val = 0} {x : Fin n // coarse r bl x.val = 0} κ) ⟨Fin.castLE h i, hi0⟩ ⟨Fin.castLE h j, hj0⟩ := hk
    rw [hk']
    simp [Matrix.one_apply, Subtype.ext_iff, Fin.ext_iff]
  · intro hM
    ext i j
    rw [blkHom_apply]
    have hi : (i.1 : Fin n).val < r := by
      by_contra hh
      exact absurd i.2 (by simp only [coarse, blkIdx, if_neg hh]; omega)
    have hj : (j.1 : Fin n).val < r := by
      by_contra hh
      exact absurd j.2 (by simp only [coarse, blkIdx, if_neg hh]; omega)
    have hk := congrArg (fun X : GL (Fin r) κ => (X : Matrix (Fin r) (Fin r) κ) ⟨i.1.val, hi⟩ ⟨j.1.val, hj⟩) hM
    have hk' : (M.1 : Matrix (Fin n) (Fin n) κ) i.1 j.1 = (1 : Matrix (Fin r) (Fin r) κ) ⟨i.1.val, hi⟩ ⟨j.1.val, hj⟩ := hk
    rw [hk']
    simp [Matrix.one_apply, Subtype.ext_iff, Fin.ext_iff]

end ParId

end Formalism.L2.Col
