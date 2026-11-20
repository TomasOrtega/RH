import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralElementsUnitFactorization
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.CardJ

variable {R : Type*} [CommRing R] [IsLocalRing R]

/- English proof (translation)
Establish `hpm : p ∈ IsLocalRing.maximalIdeal R` using `(IsLocalRing.mem_maximalIdeal _).2 hp`. Establish `hmem : p ^ n * z ∈ IsLocalRing.maximalIdeal R`. Apply `Ideal.mul_mem_right` to reduce the goal to its premises. Take `⟨m, rfl⟩ : ∃ m, n = m + 1` from `⟨n - 1, by omega⟩`. Rewrite using `[pow_succ]`.

Conclude with `Ideal.mul_mem_left _ _ hpm`. Establish `hu : IsUnit (1 + p ^ n * z)`. Assume the negation of the conclusion as `hc`. Establish `h1 : (1 + p ^ n * z) ∈ IsLocalRing.maximalIdeal R` using `(IsLocalRing.mem_maximalIdeal _).2 hc`. Establish `h2 : (1 : R) ∈ IsLocalRing.maximalIdeal R`.

Use `Ideal.sub_mem _ h1 hmem` as an intermediate fact. Simplify using `using this`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h2)`. Rewrite `hu` using `[← h]`. Conclude with `isUnit_of_mul_isUnit_left hu`.
-/
theorem isUnit_of_mul_eq_one_add_pow (p : R) (hp : ¬ IsUnit p) {n : ℕ} (hn : 1 ≤ n) {x y z : R}
    (h : x * y = 1 + p ^ n * z) : IsUnit x := by
  have hpm : p ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hp
  have hmem : p ^ n * z ∈ IsLocalRing.maximalIdeal R := by
    apply Ideal.mul_mem_right
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ]; exact Ideal.mul_mem_left _ _ hpm
  have hu : IsUnit (1 + p ^ n * z) := by
    by_contra hc
    have h1 : (1 + p ^ n * z) ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hc
    have h2 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
      have := Ideal.sub_mem _ h1 hmem
      simpa using this
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h2)
  rw [← h] at hu
  exact isUnit_of_mul_isUnit_left hu

end GlobalTheory.CardJ

namespace GlobalTheory.CardJ

variable {R : Type*} [CommRing R] [IsLocalRing R]

/- English proof (translation)
Use `set I : Ideal R := Ideal.span {p ^ n} with hI`. Use `set π : R →+* R ⧸ I := Ideal.Quotient.mk I with hπ`. Establish `hdvd : ∀ x : R, p ^ n ∣ x ↔ π x = 0` using `fun x => by`. Rewrite using `[hπ, Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton]`. Establish `hpm : p ∈ IsLocalRing.maximalIdeal R` using `(IsLocalRing.mem_maximalIdeal _).2 hp`.

Establish `hres0 : IsLocalRing.residue R p = 0` using `(IsLocalRing.residue_eq_zero_iff p).2 hpm`. Establish `hres : ∀ x : R, π x = 0 → IsLocalRing.residue R x = 0`. Introduce `x hx`. Take `⟨y, rfl⟩` from `(hdvd x).2 hx`. Take `⟨m, rfl⟩ : ∃ m, n = m + 1` from `⟨n - 1, by omega⟩`.

Simplify using `[map_mul, map_pow, hres0]`. Use `set M := Q * U with hM`. Use `set S' := Uinv * S with hS'`. Establish `hMS : M * S' = Q * S`. Rewrite using `[hM, hS', Matrix.mul_assoc, ← Matrix.mul_assoc U, hUU', Matrix.one_mul]`.

Establish `hQS1 : ∀ i j, π ((Q * S) i j) = (1 : Matrix (Fin d) (Fin d) (R ⧸ I)) i j`. Introduce `i j`. Use `(hdvd _).1 (hQS i j)` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, map_sub, sub_eq_zero]`. Rewrite using `[this, Matrix.one_apply, Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `hoff : ∀ j ∉ J, ∀ i, π (M i j) = 0` using `fun j hj i => (hdvd _).1 (hJ j hj i)`. Establish `hsum : ∀ (i : Fin d) (x : Fin d' → R ⧸ I), ∑ j, π (M i j) * x j = ∑ j : J, π (M i (j : Fin d')) * x j`. Introduce `i x`. Establish `h1` using `Finset.sum_coe_sort J (fun j => π (M i j) * x j)`.

Rewrite using `[h1]`. Use `symm`. Apply `Finset.sum_subset (Finset.subset_univ J)` to reduce the goal to its premises. Introduce `j _ hj`. Rewrite using `[hoff j hj i, zero_mul]`.

Use `set MJ : Matrix (Fin d) J R := M.submatrix id (fun j : J => (j : Fin d')) with hMJ`. Use `set SJ : Matrix J (Fin d) R := S'.submatrix (fun j : J => (j : Fin d')) id with hSJ`. Establish `hMJS : ∀ i k, π ((MJ * SJ) i k) = (1 : Matrix (Fin d) (Fin d) (R ⧸ I)) i k`. Introduce `i k`. Rewrite using `[← hQS1, ← hMS]`.

Simplify using `only [Matrix.mul_apply, map_sum, map_mul, hMJ, hSJ, Matrix.submatrix_apply, id]`. Conclude with `(hsum i (fun j => π (S' j k))).symm`. Establish `hE : ∀ j j0 : J, IsLocalRing.residue R ((SJ * MJ) j j0) = (1 : Matrix J J (IsLocalRing.ResidueField R)) j j0`. Introduce `j j0`. Use `set c : Fin d' → R := fun j' => if h : j' ∈ J then (SJ * MJ - (1 : Matrix J J R)) ⟨j', h⟩ j0 else 0 with hc`.

Establish `hUc : Uinv *ᵥ (U *ᵥ c) = c`. Rewrite using `[Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]`. Establish `hQc : ∀ i, p ^ n ∣ (Q *ᵥ (U *ᵥ c)) i`. Introduce `i`. Rewrite using `[Matrix.mulVec_mulVec, ← hM, hdvd]`.

Establish `hA : (MJ.map π) * ((SJ * MJ - (1 : Matrix J J R)).map π) = 0`. Establish `h1 : (MJ.map π) * (SJ.map π) = 1`. Use extensionality with `i k`. Rewrite using `[← Matrix.map_mul]`. Conclude with `hMJS i k`.

Rewrite using `[Matrix.map_sub _ (fun a b => map_sub π a b), Matrix.map_mul, Matrix.map_one _ (map_zero π) (map_one π), Matrix.mul_sub, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_one, sub_self]`. Establish `h2` using `congrFun (congrFun hA i) j0`. Rewrite `h2` using `[Matrix.zero_apply, Matrix.mul_apply]`. Rewrite using `[← h2]`. Simplify using `only [Matrix.mulVec, dotProduct, map_sum, map_mul]`.

Rewrite using `[hsum i (fun j' => π (c j'))]`. Use `Finset.sum_congr rfl (fun j' _ => ?_)` and prove the remaining obligations. Simplify using `[hc, hMJ, Matrix.map_apply]`. Establish `hp1` using `hker _ hQc j j.2`. Rewrite `hp1` using `[hUc]`.

Establish `hcj : c j = (SJ * MJ - (1 : Matrix J J R)) j j0` using `by simp [hc]`. Rewrite `hp1` using `[hcj]`. Take `⟨y, hy⟩` from `hp1`. Use `congrArg (IsLocalRing.residue R) hy` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, map_sub, map_mul, hres0, zero_mul, sub_eq_zero]`.

Rewrite using `[this, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hcard : Fintype.card J = d` using `by set κ := IsLocalRing.ResidueField R set ρ : R →+* κ := IsLocalRing.residue R`. Establish `hAB : (MJ.map ρ) * (SJ.map ρ) = 1`. Use extensionality with `i k`.

Rewrite using `[← Matrix.map_mul, Matrix.map_apply]`. Establish `h` using `hMJS i k`. Establish `h0 : π ((MJ * SJ - (1 : Matrix (Fin d) (Fin d) R)) i k) = 0`. Apply the tactic sequence `rw [Matrix.sub_apply, map_sub, h, Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp`. Use `hres _ h0` as an intermediate fact.

Rewrite `this` using `[Matrix.sub_apply, map_sub, sub_eq_zero]`. Apply the tactic sequence `rw [this, Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp`. Establish `hBA : (SJ.map ρ) * (MJ.map ρ) = 1`. Use extensionality with `j j0`. Rewrite using `[← Matrix.map_mul, Matrix.map_apply]`.

Conclude with `hE j j0`. Establish `h1 : d ≤ Fintype.card J`. Use `Matrix.rank_mul_le_left (MJ.map ρ) (SJ.map ρ)` as an intermediate fact. Rewrite `this` using `[hAB, Matrix.rank_one, Fintype.card_fin]`. Conclude with `this.trans (Matrix.rank_le_card_width _)`.

Establish `h2 : Fintype.card J ≤ d`. Use `Matrix.rank_mul_le_left (SJ.map ρ) (MJ.map ρ)` as an intermediate fact. Rewrite `this` using `[hBA, Matrix.rank_one]`. Conclude with `(this.trans (Matrix.rank_le_card_width _)).trans (by rw [Fintype.card_fin])`. Use linear arithmetic over natural numbers and integers.

Set `e : Fin d ≃ J` to `(Fintype.equivFinOfCardEq hcard).symm`. Use `⟨e, ?_, ?_⟩` and prove the remaining obligations. Use `set T := Q * U.submatrix id (fun k => (e k : Fin d')) with hT set B := S'.submatrix (fun k => (e k : Fin d')) id with hB`. Establish `hTe : ∀ i k, T i k = M i (e k)`. Introduce `i k`.

Simplify using `[hT, hM, Matrix.mul_apply]`. Establish `hTB : ∀ i k, π ((T * B) i k) = (1 : Matrix (Fin d) (Fin d) (R ⧸ I)) i k`. Introduce `i k`. Rewrite using `[← hQS1, ← hMS]`. Simplify using `only [Matrix.mul_apply, map_sum, map_mul, hTe, hB, Matrix.submatrix_apply, id]`.

Rewrite using `[hsum i (fun j => π (S' j k))]`. Conclude with `Equiv.sum_comp e (fun j : J => π (M i (j : Fin d')) * π (S' j k))`. Establish `hdet : π ((T * B).det) = 1`. Rewrite using `[RingHom.map_det]`. Establish `: π.mapMatrix (T * B) = 1` using `by ext i k; exact hTB i k`.

Rewrite using `[this, Matrix.det_one]`. Rewrite `hdet` using `[Matrix.det_mul]`. Establish `h0 : π (T.det * B.det - 1) = 0` using `by rw [map_sub, hdet, map_one, sub_self]`. Take `⟨z, hz⟩` from `(hdvd _).2 h0`. Rewrite using `[Matrix.isUnit_iff_isUnit_det]`.

Conclude with `GlobalTheory.CardJ.isUnit_of_mul_eq_one_add_pow p hp hn (y := B.det) (z := z) (by rw [← hz]; ring)`. Introduce `i k`. Rewrite using `[hdvd, Matrix.sub_apply, map_sub, sub_eq_zero]`. Establish `hQ : Q = M * Uinv` using `by rw [hM, Matrix.mul_assoc, hUU', Matrix.mul_one]`. Use `conv_lhs => rw [hQ]`.

Simplify using `only [Matrix.mul_apply, map_sum, map_mul, Matrix.submatrix_apply, id]`. Rewrite using `[hsum i (fun j => π (Uinv j k))]`. Rewrite using `[← Equiv.sum_comp e (fun j : J => π (M i (j : Fin d')) * π (Uinv j k))]`. Use `Finset.sum_congr rfl (fun t _ => ?_)` and prove the remaining obligations. Simplify using `[hM, Matrix.mul_apply]`.
-/
theorem exists_cols_of_rightInv (p : R) (hp : ¬ IsUnit p) (d d' n : ℕ)
    (Q : Matrix (Fin d) (Fin d') R) (S : Matrix (Fin d') (Fin d) R)
    (U Uinv : Matrix (Fin d') (Fin d') R) (J : Finset (Fin d')) (hn : 1 ≤ n)
    (hQS : ∀ i j, p ^ n ∣ (Q * S - (1 : Matrix (Fin d) (Fin d) R)) i j) (hUU : Uinv * U = 1) (hUU' : U * Uinv = 1)
    (hJ : ∀ j ∉ J, ∀ i, p ^ n ∣ (Q * U) i j)
    (hker : ∀ v : Fin d' → R, (∀ i, p ^ n ∣ (Q *ᵥ v) i) → ∀ j ∈ J, p ∣ (Uinv *ᵥ v) j) :
    ∃ e : Fin d ≃ J, IsUnit (Q * U.submatrix id (fun k => (e k : Fin d'))) ∧
      ∀ i j, p ^ n ∣ (Q - (Q * U.submatrix id (fun k => (e k : Fin d'))) *
        Uinv.submatrix (fun k => (e k : Fin d')) id) i j := by
  classical
  set I : Ideal R := Ideal.span {p ^ n} with hI
  set π : R →+* R ⧸ I := Ideal.Quotient.mk I with hπ
  have hdvd : ∀ x : R, p ^ n ∣ x ↔ π x = 0 := fun x => by
    rw [hπ, Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton]
  have hpm : p ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hp
  have hres0 : IsLocalRing.residue R p = 0 := (IsLocalRing.residue_eq_zero_iff p).2 hpm
  have hres : ∀ x : R, π x = 0 → IsLocalRing.residue R x = 0 := by
    intro x hx
    obtain ⟨y, rfl⟩ := (hdvd x).2 hx
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [map_mul, map_pow, hres0]
  set M := Q * U with hM
  set S' := Uinv * S with hS'
  have hMS : M * S' = Q * S := by
    rw [hM, hS', Matrix.mul_assoc, ← Matrix.mul_assoc U, hUU', Matrix.one_mul]
  have hQS1 : ∀ i j, π ((Q * S) i j) = (1 : Matrix (Fin d) (Fin d) (R ⧸ I)) i j := by
    intro i j
    have := (hdvd _).1 (hQS i j)
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hoff : ∀ j ∉ J, ∀ i, π (M i j) = 0 := fun j hj i => (hdvd _).1 (hJ j hj i)
  have hsum : ∀ (i : Fin d) (x : Fin d' → R ⧸ I),
      ∑ j, π (M i j) * x j = ∑ j : J, π (M i (j : Fin d')) * x j := by
    intro i x
    have h1 := Finset.sum_coe_sort J (fun j => π (M i j) * x j)
    rw [h1]
    symm
    apply Finset.sum_subset (Finset.subset_univ J)
    intro j _ hj; rw [hoff j hj i, zero_mul]

  set MJ : Matrix (Fin d) J R := M.submatrix id (fun j : J => (j : Fin d')) with hMJ
  set SJ : Matrix J (Fin d) R := S'.submatrix (fun j : J => (j : Fin d')) id with hSJ
  have hMJS : ∀ i k, π ((MJ * SJ) i k) = (1 : Matrix (Fin d) (Fin d) (R ⧸ I)) i k := by
    intro i k
    rw [← hQS1, ← hMS]
    simp only [Matrix.mul_apply, map_sum, map_mul, hMJ, hSJ, Matrix.submatrix_apply, id]
    exact (hsum i (fun j => π (S' j k))).symm

  have hE : ∀ j j0 : J, IsLocalRing.residue R ((SJ * MJ) j j0) = (1 : Matrix J J (IsLocalRing.ResidueField R)) j j0 := by
    intro j j0
    set c : Fin d' → R := fun j' => if h : j' ∈ J then (SJ * MJ - (1 : Matrix J J R)) ⟨j', h⟩ j0 else 0 with hc
    have hUc : Uinv *ᵥ (U *ᵥ c) = c := by
      rw [Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
    have hQc : ∀ i, p ^ n ∣ (Q *ᵥ (U *ᵥ c)) i := by
      intro i
      rw [Matrix.mulVec_mulVec, ← hM, hdvd]
      have hA : (MJ.map π) * ((SJ * MJ - (1 : Matrix J J R)).map π) = 0 := by
        have h1 : (MJ.map π) * (SJ.map π) = 1 := by
          ext i k; rw [← Matrix.map_mul]; exact hMJS i k
        rw [Matrix.map_sub _ (fun a b => map_sub π a b), Matrix.map_mul, Matrix.map_one _ (map_zero π) (map_one π), Matrix.mul_sub,
          ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_one, sub_self]
      have h2 := congrFun (congrFun hA i) j0
      rw [Matrix.zero_apply, Matrix.mul_apply] at h2
      rw [← h2]
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
      rw [hsum i (fun j' => π (c j'))]
      refine Finset.sum_congr rfl (fun j' _ => ?_)
      simp [hc, hMJ, Matrix.map_apply]
    have hp1 := hker _ hQc j j.2
    rw [hUc] at hp1
    have hcj : c j = (SJ * MJ - (1 : Matrix J J R)) j j0 := by simp [hc]
    rw [hcj] at hp1
    obtain ⟨y, hy⟩ := hp1
    have := congrArg (IsLocalRing.residue R) hy
    rw [Matrix.sub_apply, map_sub, map_mul, hres0, zero_mul, sub_eq_zero] at this
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

  have hcard : Fintype.card J = d := by
    set κ := IsLocalRing.ResidueField R
    set ρ : R →+* κ := IsLocalRing.residue R
    have hAB : (MJ.map ρ) * (SJ.map ρ) = 1 := by
      ext i k
      rw [← Matrix.map_mul, Matrix.map_apply]
      have h := hMJS i k
      have h0 : π ((MJ * SJ - (1 : Matrix (Fin d) (Fin d) R)) i k) = 0 := by
        rw [Matrix.sub_apply, map_sub, h, Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
      have := hres _ h0
      rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
      rw [this, Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    have hBA : (SJ.map ρ) * (MJ.map ρ) = 1 := by
      ext j j0; rw [← Matrix.map_mul, Matrix.map_apply]; exact hE j j0
    have h1 : d ≤ Fintype.card J := by
      have := Matrix.rank_mul_le_left (MJ.map ρ) (SJ.map ρ)
      rw [hAB, Matrix.rank_one, Fintype.card_fin] at this
      exact this.trans (Matrix.rank_le_card_width _)
    have h2 : Fintype.card J ≤ d := by
      have := Matrix.rank_mul_le_left (SJ.map ρ) (MJ.map ρ)
      rw [hBA, Matrix.rank_one] at this
      exact (this.trans (Matrix.rank_le_card_width _)).trans (by rw [Fintype.card_fin])
    omega

  let e : Fin d ≃ J := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨e, ?_, ?_⟩
  · set T := Q * U.submatrix id (fun k => (e k : Fin d')) with hT
    set B := S'.submatrix (fun k => (e k : Fin d')) id with hB
    have hTe : ∀ i k, T i k = M i (e k) := by
      intro i k; simp [hT, hM, Matrix.mul_apply]
    have hTB : ∀ i k, π ((T * B) i k) = (1 : Matrix (Fin d) (Fin d) (R ⧸ I)) i k := by
      intro i k
      rw [← hQS1, ← hMS]
      simp only [Matrix.mul_apply, map_sum, map_mul, hTe, hB, Matrix.submatrix_apply, id]
      rw [hsum i (fun j => π (S' j k))]
      exact Equiv.sum_comp e (fun j : J => π (M i (j : Fin d')) * π (S' j k))
    have hdet : π ((T * B).det) = 1 := by
      rw [RingHom.map_det]
      have : π.mapMatrix (T * B) = 1 := by ext i k; exact hTB i k
      rw [this, Matrix.det_one]
    rw [Matrix.det_mul] at hdet
    have h0 : π (T.det * B.det - 1) = 0 := by rw [map_sub, hdet, map_one, sub_self]
    obtain ⟨z, hz⟩ := (hdvd _).2 h0
    rw [Matrix.isUnit_iff_isUnit_det]
    exact GlobalTheory.CardJ.isUnit_of_mul_eq_one_add_pow p hp hn (y := B.det) (z := z) (by rw [← hz]; ring)
  · intro i k
    rw [hdvd, Matrix.sub_apply, map_sub, sub_eq_zero]
    have hQ : Q = M * Uinv := by rw [hM, Matrix.mul_assoc, hUU', Matrix.mul_one]
    conv_lhs => rw [hQ]
    simp only [Matrix.mul_apply, map_sum, map_mul, Matrix.submatrix_apply, id]
    rw [hsum i (fun j => π (Uinv j k))]
    rw [← Equiv.sum_comp e (fun j : J => π (M i (j : Fin d')) * π (Uinv j k))]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    simp [hM, Matrix.mul_apply]

end GlobalTheory.CardJ

namespace GlobalTheory.CardJ

/- English proof (translation)
Introduce `l _ d d' n Q S U Uinv J hn hQS hUU hUU' hJ hker`. Use `haveI : PerfectRing (Cb l) l := GlobalTheory.OEDvr.perfectRing_Cb`. Conclude with `exists_cols_of_rightInv (l : WCb l) (WittVector.irreducible l).not_isUnit d d' n Q S U Uinv J hn hQS hUU hUU' hJ hker`.
-/
theorem exists_cols_of_rightInv_WCb : ∀ (l : ℕ) [Fact l.Prime] (d d' n : ℕ) (Q : Matrix (Fin d) (Fin d') (WCb l)) (S : Matrix (Fin d') (Fin d) (WCb l)) (U Uinv : Matrix (Fin d') (Fin d') (WCb l)) (J : Finset (Fin d')), 1 ≤ n → (∀ i j, (l : WCb l) ^ n ∣ (Q * S - (1 : Matrix (Fin d) (Fin d) (WCb l))) i j) → Uinv * U = 1 → U * Uinv = 1 → (∀ j ∉ J, ∀ i, (l : WCb l) ^ n ∣ (Q * U) i j) → (∀ v : Fin d' → WCb l, (∀ i, (l : WCb l) ^ n ∣ (Q *ᵥ v) i) → ∀ j ∈ J, (l : WCb l) ∣ (Uinv *ᵥ v) j) → ∃ e : Fin d ≃ J, IsUnit (Q * U.submatrix id (fun k => (e k : Fin d'))) ∧ ∀ i j, (l : WCb l) ^ n ∣ (Q - (Q * U.submatrix id (fun k => (e k : Fin d'))) * Uinv.submatrix (fun k => (e k : Fin d')) id) i j := by
  intro l _ d d' n Q S U Uinv J hn hQS hUU hUU' hJ hker
  haveI : PerfectRing (Cb l) l := GlobalTheory.OEDvr.perfectRing_Cb
  exact exists_cols_of_rightInv (l : WCb l) (WittVector.irreducible l).not_isUnit d d' n Q S U Uinv J
    hn hQS hUU hUU' hJ hker

end GlobalTheory.CardJ
