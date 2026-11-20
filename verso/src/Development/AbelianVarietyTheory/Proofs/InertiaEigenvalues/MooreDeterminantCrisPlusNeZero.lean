import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrisPlusFrobEigenvectorRatioPadicStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisPlusFrobeniusStableSubringInFilZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPeriodRingFieldTPowFiltrationUnitsStatement

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.MooreDeterminant

variable {B Q : Type} [CommRing B] [IsDomain B] [Field Q] [Algebra Q B]

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Establish `hz : S 0` using `by simpa using h0 0`. Use `Finset.sum_induction _ S hadd hz ?_` and prove the remaining obligations. Introduce `σ _`. Rewrite using `[Units.smul_def, zsmul_eq_mul]`.

Apply `hmul` to reduce the goal to its premises. Use `h0 (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : Q)` as an intermediate fact. Simplify using `using this`. Establish `h1 : S 1` using `by simpa using h0 1`. Conclude with `Finset.prod_induction _ S hmul h1 (fun i _ => hM _ _)`.
-/
theorem det_mem (S : B → Prop) (h0 : ∀ q : Q, S (algebraMap Q B q))
    (hadd : ∀ a b, S a → S b → S (a + b)) (hmul : ∀ a b, S a → S b → S (a * b))
    {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι B) (hM : ∀ i j, S (M i j)) : S M.det := by
  rw [Matrix.det_apply]
  have hz : S 0 := by simpa using h0 0
  refine Finset.sum_induction _ S hadd hz ?_
  intro σ _
  rw [Units.smul_def, zsmul_eq_mul]
  apply hmul
  · have := h0 (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : Q)
    simpa using this
  · have h1 : S 1 := by simpa using h0 1
    exact Finset.prod_induction _ S hmul h1 (fun i _ => hM _ _)

/- English proof (translation)
The claim follows from `RingHom.coe_pow φ m`.
-/
theorem iter_eq (φ : B →+* B) (m : ℕ) : ⇑(φ ^ m) = (⇑φ)^[m] := RingHom.coe_pow φ m

/- English proof (translation)
Establish `hSit : ∀ (i : ℕ) b, S b → S (φ^[i] b)`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => intro b hb`. Simplify using `using hb`.

Consider the case `succ i ih => intro b hb`. Rewrite using `[Function.iterate_succ_apply']`. Conclude with `hφ _ (ih b hb)`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero`. Introduce `a _ _ _ ha`. Rewrite using `[Matrix.det_fin_one]`. Simplify using `using ha.ne_zero 0`. Consider the case `succ n ih`.

Introduce `a hk hSa hfa ha hdet`. Use `set M : Matrix (Fin (n + 2)) (Fin (n + 2)) B := Matrix.of fun i j => φ^[i] (a j) with hMdef`. Establish `hA` using `ih (a ∘ Fin.castSucc) (by omega) (fun j => hSa _) (fun j => hfa _) (ha.comp _ (Fin.castSucc_injective _))`. Use `set ω : Fin (n + 2) → B := fun m => (Matrix.of fun i j : Fin (n + 1) => φ^[i] (a (m.succAbove j))).det with hωdef`. Establish `hωl : ω (Fin.last _) = (Matrix.of fun i j : Fin (n + 1) => φ^[i] ((a ∘ Fin.castSucc) j)).det`.

Simplify using `[ω, Fin.succAbove_last]`. Establish `hωl0 : ω (Fin.last _) ≠ 0` using `by rw [hωl]; exact hA`. Establish `hu : ∀ m, M.adjugate m (Fin.last _) = (-1) ^ ((n + 1 : ℕ) + (m : ℕ)) * ω m`. Introduce `m`. Rewrite using `[Matrix.adjugate_fin_succ_eq_det_submatrix]`.

Simplify using `only [Fin.val_last, Fin.succAbove_last, ω]`. Use `congr 2`. Establish `hw : ∀ m, M.adjugate m 0 = (-1) ^ (m : ℕ) * φ (ω m)`. Introduce `m`. Rewrite using `[Matrix.adjugate_fin_succ_eq_det_submatrix, hωdef]`.

Simplify using `only [Fin.val_zero, zero_add, Fin.succAbove_zero]`. Rewrite using `[RingHom.map_det]`. Use `congr 2`. Use extensionality with `i j`. Simplify using `[M, Matrix.submatrix_apply, RingHom.mapMatrix_apply, Function.iterate_succ_apply']`.

Establish `hK : M * M.adjugate = 0` using `by rw [Matrix.mul_adjugate, hdet, zero_smul]`. Establish `hker : ∀ i c, ∑ m, M i m * M.adjugate m c = 0` using `fun i c => by`. Use `congrFun (congrFun hK i) c` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply]`. Use `set v : Fin (n + 2) → B := fun m => M.adjugate (Fin.last _) (Fin.last _) * M.adjugate m 0 - M.adjugate (Fin.last _) 0 * M.adjugate m (Fin.last _) with hvdef`.

Establish `hv : ∀ i, ∑ m, M i m * v m = 0`. Introduce `i`. Establish `e1` using `hker i 0`. Establish `e2` using `hker i (Fin.last _)`. Simplify using `only [v, mul_sub, Finset.sum_sub_distrib]`.

Establish `: ∑ m, M i m * (M.adjugate (Fin.last _) (Fin.last _) * M.adjugate m 0) = M.adjugate (Fin.last _) (Fin.last _) * ∑ m, M i m * M.adjugate m 0`. Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring`. Establish `: ∑ m, M i m * (M.adjugate (Fin.last _) 0 * M.adjugate m (Fin.last _)) = M.adjugate (Fin.last _) 0 * ∑ m, M i m * M.adjugate m (Fin.last _)`. Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring`. Simplify the hypotheses and the goal together.

Establish `hvl : v (Fin.last _) = 0` using `by simp only [v]; ring`. Establish `hv' : Matrix.mulVec (Matrix.of fun i j : Fin (n + 1) => φ^[i] ((a ∘ Fin.castSucc) j)) (v ∘ Fin.castSucc) = 0`. Use function extensionality and compare the values at `i`. Use `hv (Fin.castSucc i)` as an intermediate fact. Rewrite `this` using `[Fin.sum_univ_castSucc, hvl, mul_zero, add_zero]`.

Simplify `this` using `[Matrix.mulVec, dotProduct, M]`. Establish `hv0` using `Matrix.eq_zero_of_mulVec_eq_zero hA hv'`. Establish `hvall : ∀ m, v m = 0`. Introduce `m`. Use `Fin.lastCases hvl (fun j => ?_) m` and prove the remaining obligations.

Conclude with `congrFun hv0 j`. Establish `hcomm : ∀ m, φ (ω m) * ω (Fin.last _) = ω m * φ (ω (Fin.last _))`. Introduce `m`. Establish `E` using `hvall m`. Simplify using `only [v, hu, hw, Fin.val_last, pow_add] at E`.

Establish `hs : ((-1 : B) ^ (m : ℕ)) ^ 2 = 1` using `by rw [← pow_mul, mul_comm, pow_mul]; simp`. Establish `he : ((-1 : B) ^ (n + 1)) ^ 2 = 1` using `by rw [← pow_mul, mul_comm, pow_mul]; simp`. Take the linear combination `((-1 : B) ^ (m : ℕ)) * E - (φ (ω m) * ω (Fin.last _) - ω m * φ (ω (Fin.last _))) * hs - (φ (ω m) * ω (Fin.last _) - ω m * φ (ω (Fin.last _))) * ((-1 : B) ^ (m : ℕ)) ^ 2 * he`. Establish `hSω : ∀ m, S (ω m)` using `fun m => det_mem S h0 hadd hmul _ (fun i j => hSit _ _ (hSa _))`. Establish `hLi : ∀ i : ℕ, φ^[i] L = L` using `fun i => Function.iterate_fixed hL i`.

Establish `hfω : ∀ m, φ^[h] (ω m) = L ^ (n + 1) * ω m`. Introduce `m`. Rewrite using `[← iter_eq, hωdef]`. Simplify using `only`. Rewrite using `[RingHom.map_det]`.

Establish `: (φ ^ h).mapMatrix (Matrix.of fun i j : Fin (n + 1) => φ^[i] (a (m.succAbove j))) = L • (Matrix.of fun i j : Fin (n + 1) => φ^[i] (a (m.succAbove j)))`. Use extensionality with `i j`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, iter_eq]`. Rewrite using `[← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, hfa, ← iter_eq, map_mul, iter_eq, hLi]`. Rewrite using `[this, Matrix.det_smul, Fintype.card_fin]`.

Establish `hrat : ∀ m, ∃ c : Q, ω m = c • ω (Fin.last _)` using `fun m => ratio (n + 1) (by omega) _ _ (hSω m) (hSω _) (hfω m) (hfω _) hωl0 (hcomm m)`. Use `choose c hc using hrat`. Establish `hrow` using `hker 0 (Fin.last _)`. Use `set d : Fin (n + 2) → Q := fun m => (-1) ^ ((n + 1 : ℕ) + (m : ℕ)) * c m with hd`. Establish `hsum : (∑ m, d m • a m) * ω (Fin.last _) = 0`.

Rewrite using `[← hrow, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[hu, hc m]`. Simplify using `only [M, Matrix.of_apply, Fin.val_zero, Function.iterate_zero, id, hd, Algebra.smul_def, map_mul, map_pow, map_neg, map_one]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hsum0 : ∑ m, d m • a m = 0` using `(mul_eq_zero.1 hsum).resolve_right hωl0`. Establish `hdl` using `Fintype.linearIndependent_iff.1 ha d hsum0 (Fin.last _)`. Establish `hcl : c (Fin.last _) = 0`. Simplify using `only [hd, mul_eq_zero, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, false_and, false_or] at hdl`. Conclude with `hdl`.

Apply `hωl0` to reduce the goal to its premises. Rewrite using `[hc (Fin.last _), hcl, zero_smul]`.
-/
theorem moore_core (φ : B →+* B) (S : B → Prop)
    (hφ : ∀ b, S b → S (φ b)) (h0 : ∀ q : Q, S (algebraMap Q B q))
    (hadd : ∀ a b, S a → S b → S (a + b)) (hmul : ∀ a b, S a → S b → S (a * b))
    (L : B) (hL : φ L = L) (h : ℕ)
    (ratio : ∀ s, s < h → ∀ ω ω' : B, S ω → S ω' → φ^[h] ω = L ^ s * ω → φ^[h] ω' = L ^ s * ω' → ω' ≠ 0 →
      φ ω * ω' = ω * φ ω' → ∃ c : Q, ω = c • ω') :
    ∀ (n : ℕ) (a : Fin (n + 1) → B), n + 1 ≤ h → (∀ j, S (a j)) → (∀ j, φ^[h] (a j) = L * a j) →
      LinearIndependent Q a → (Matrix.of fun i j : Fin (n + 1) => φ^[i] (a j)).det ≠ 0 := by
  have hSit : ∀ (i : ℕ) b, S b → S (φ^[i] b) := by
    intro i
    induction i with
    | zero => intro b hb; simpa using hb
    | succ i ih => intro b hb; rw [Function.iterate_succ_apply']; exact hφ _ (ih b hb)
  intro n
  induction n with
  | zero =>
    intro a _ _ _ ha
    rw [Matrix.det_fin_one]
    simpa using ha.ne_zero 0
  | succ n ih =>
    intro a hk hSa hfa ha hdet
    set M : Matrix (Fin (n + 2)) (Fin (n + 2)) B := Matrix.of fun i j => φ^[i] (a j) with hMdef

    have hA := ih (a ∘ Fin.castSucc) (by omega) (fun j => hSa _) (fun j => hfa _)
      (ha.comp _ (Fin.castSucc_injective _))
    set ω : Fin (n + 2) → B := fun m => (Matrix.of fun i j : Fin (n + 1) => φ^[i] (a (m.succAbove j))).det with hωdef
    have hωl : ω (Fin.last _) = (Matrix.of fun i j : Fin (n + 1) => φ^[i] ((a ∘ Fin.castSucc) j)).det := by
      simp [ω, Fin.succAbove_last]
    have hωl0 : ω (Fin.last _) ≠ 0 := by rw [hωl]; exact hA
    have hu : ∀ m, M.adjugate m (Fin.last _) = (-1) ^ ((n + 1 : ℕ) + (m : ℕ)) * ω m := by
      intro m
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
      simp only [Fin.val_last, Fin.succAbove_last, ω]
      congr 2
    have hw : ∀ m, M.adjugate m 0 = (-1) ^ (m : ℕ) * φ (ω m) := by
      intro m
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix, hωdef]
      simp only [Fin.val_zero, zero_add, Fin.succAbove_zero]
      rw [RingHom.map_det]
      congr 2
      ext i j
      simp [M, Matrix.submatrix_apply, RingHom.mapMatrix_apply, Function.iterate_succ_apply']
    have hK : M * M.adjugate = 0 := by rw [Matrix.mul_adjugate, hdet, zero_smul]
    have hker : ∀ i c, ∑ m, M i m * M.adjugate m c = 0 := fun i c => by
      have := congrFun (congrFun hK i) c
      simpa [Matrix.mul_apply] using this

    set v : Fin (n + 2) → B := fun m => M.adjugate (Fin.last _) (Fin.last _) * M.adjugate m 0 -
      M.adjugate (Fin.last _) 0 * M.adjugate m (Fin.last _) with hvdef
    have hv : ∀ i, ∑ m, M i m * v m = 0 := by
      intro i
      have e1 := hker i 0
      have e2 := hker i (Fin.last _)
      simp only [v, mul_sub, Finset.sum_sub_distrib]
      have : ∑ m, M i m * (M.adjugate (Fin.last _) (Fin.last _) * M.adjugate m 0) =
          M.adjugate (Fin.last _) (Fin.last _) * ∑ m, M i m * M.adjugate m 0 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      have : ∑ m, M i m * (M.adjugate (Fin.last _) 0 * M.adjugate m (Fin.last _)) =
          M.adjugate (Fin.last _) 0 * ∑ m, M i m * M.adjugate m (Fin.last _) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      simp_all
    have hvl : v (Fin.last _) = 0 := by simp only [v]; ring
    have hv' : Matrix.mulVec (Matrix.of fun i j : Fin (n + 1) => φ^[i] ((a ∘ Fin.castSucc) j)) (v ∘ Fin.castSucc) = 0 := by
      funext i
      have := hv (Fin.castSucc i)
      rw [Fin.sum_univ_castSucc, hvl, mul_zero, add_zero] at this
      simpa [Matrix.mulVec, dotProduct, M] using this
    have hv0 := Matrix.eq_zero_of_mulVec_eq_zero hA hv'
    have hvall : ∀ m, v m = 0 := by
      intro m
      refine Fin.lastCases hvl (fun j => ?_) m
      exact congrFun hv0 j

    have hcomm : ∀ m, φ (ω m) * ω (Fin.last _) = ω m * φ (ω (Fin.last _)) := by
      intro m
      have E := hvall m
      simp only [v, hu, hw, Fin.val_last, pow_add] at E
      have hs : ((-1 : B) ^ (m : ℕ)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
      have he : ((-1 : B) ^ (n + 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
      linear_combination ((-1 : B) ^ (m : ℕ)) * E
        - (φ (ω m) * ω (Fin.last _) - ω m * φ (ω (Fin.last _))) * hs
        - (φ (ω m) * ω (Fin.last _) - ω m * φ (ω (Fin.last _))) * ((-1 : B) ^ (m : ℕ)) ^ 2 * he

    have hSω : ∀ m, S (ω m) := fun m => det_mem S h0 hadd hmul _ (fun i j => hSit _ _ (hSa _))
    have hLi : ∀ i : ℕ, φ^[i] L = L := fun i => Function.iterate_fixed hL i
    have hfω : ∀ m, φ^[h] (ω m) = L ^ (n + 1) * ω m := by
      intro m
      rw [← iter_eq, hωdef]
      simp only
      rw [RingHom.map_det]
      have : (φ ^ h).mapMatrix (Matrix.of fun i j : Fin (n + 1) => φ^[i] (a (m.succAbove j))) =
          L • (Matrix.of fun i j : Fin (n + 1) => φ^[i] (a (m.succAbove j))) := by
        ext i j
        simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, iter_eq]
        rw [← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, hfa, ← iter_eq, map_mul, iter_eq, hLi]
      rw [this, Matrix.det_smul, Fintype.card_fin]

    have hrat : ∀ m, ∃ c : Q, ω m = c • ω (Fin.last _) := fun m =>
      ratio (n + 1) (by omega) _ _ (hSω m) (hSω _) (hfω m) (hfω _) hωl0 (hcomm m)
    choose c hc using hrat

    have hrow := hker 0 (Fin.last _)
    set d : Fin (n + 2) → Q := fun m => (-1) ^ ((n + 1 : ℕ) + (m : ℕ)) * c m with hd
    have hsum : (∑ m, d m • a m) * ω (Fin.last _) = 0 := by
      rw [← hrow, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hu, hc m]
      simp only [M, Matrix.of_apply, Fin.val_zero, Function.iterate_zero, id, hd, Algebra.smul_def, map_mul, map_pow,
        map_neg, map_one]
      ring
    have hsum0 : ∑ m, d m • a m = 0 := (mul_eq_zero.1 hsum).resolve_right hωl0
    have hdl := Fintype.linearIndependent_iff.1 ha d hsum0 (Fin.last _)
    have hcl : c (Fin.last _) = 0 := by
      simp only [hd, mul_eq_zero, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, false_and, false_or] at hdl
      exact hdl
    apply hωl0
    rw [hc (Fin.last _), hcl, zero_smul]

end GlobalTheory.PMon.MooreDeterminant

namespace GlobalTheory.PMon

/- English proof (translation)
Introduce `l _ P AI T h k hk a hPa hfa ha`. Take `⟨hF, hinj, -⟩` from `GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T`. Take `⟨hpφ, -, hpR, hpQ, -⟩` from `GlobalTheory.T.bcrisPlus_frobeniusStable_subring_in_filZero l P AI T`. Use `haveI : IsDomain P.R.BdR := hF.isDomain`. Use `haveI : IsDomain P.R.B := Function.Injective.isDomain (P.ιB : P.R.B →+* P.R.BdR) hinj`.

Consider the cases of `k with`. Consider the case `zero => simp`. Consider the case `succ n`. Conclude with `GlobalTheory.PMon.MooreDeterminant.moore_core (Q := ℚ_[l]) (P.φB : P.R.B →+* P.R.B) (Plus T) hpφ hpQ (fun a b ha hb => (hpR a b ha hb).1) (fun a b ha hb => (hpR a b ha hb).2) (l : P.R.B) (map_natCast _ l) h (fun s hs ω ω' h1 h2 h3 h4 h5 h6 => GlobalTheory.T.crisPlus_frob_eigenvec …`.
-/
theorem moore_statement : Moore := by
  intro l _ P AI T h k hk a hPa hfa ha
  obtain ⟨hF, hinj, -⟩ := GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T
  obtain ⟨hpφ, -, hpR, hpQ, -⟩ := GlobalTheory.T.bcrisPlus_frobeniusStable_subring_in_filZero l P AI T
  haveI : IsDomain P.R.BdR := hF.isDomain
  haveI : IsDomain P.R.B := Function.Injective.isDomain (P.ιB : P.R.B →+* P.R.BdR) hinj
  cases k with
  | zero => simp
  | succ n =>
    exact GlobalTheory.PMon.MooreDeterminant.moore_core (Q := ℚ_[l]) (P.φB : P.R.B →+* P.R.B) (Plus T) hpφ hpQ
      (fun a b ha hb => (hpR a b ha hb).1) (fun a b ha hb => (hpR a b ha hb).2) (l : P.R.B) (map_natCast _ l) h
      (fun s hs ω ω' h1 h2 h3 h4 h5 h6 => GlobalTheory.T.crisPlus_frob_eigenvector_ratio_padic l P AI T h s hs ω ω' h1 h2 h3 h4 h5 h6)
      n a hk hPa hfa ha

end GlobalTheory.PMon
