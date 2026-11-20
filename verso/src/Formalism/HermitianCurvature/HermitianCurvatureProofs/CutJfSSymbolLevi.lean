import Formalism.HermitianCurvature.HermitianCurvatureProofs.FltZeroEq

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

def pw (i : Fin (2 * r + k + 1)) : ℂ := if r ≤ i.val ∧ i.val ≤ r + k then 1 else 0

/- English proof (translation)
The claim follows from `mulVec_diagonal _ _ _`.
-/
theorem pw_mulVec (x : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (diagonal (pw (k := k) (r := r)) *ᵥ x) i = pw (k := k) (r := r) i * x i := mulVec_diagonal _ _ _

/- English proof (translation)
Introduce `i hi`. Rewrite using `[pw_mulVec, pw, if_neg (by omega), zero_mul]`.
-/
theorem pw_inWb (x : Fin (2 * r + k + 1) → ℂ) : inWb k r (diagonal (pw (k := k) (r := r)) *ᵥ x) := by
  intro i hi
  rw [pw_mulVec, pw, if_neg (by omega), zero_mul]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[pw_mulVec, pw]`. Use `split_ifs with h`. Rewrite using `[one_mul]`. Rewrite using `[zero_mul, hu i (by omega)]`.
-/
theorem pw_fix {u : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) : diagonal (pw (k := k) (r := r)) *ᵥ u = u := by
  funext i
  rw [pw_mulVec, pw]
  split_ifs with h
  · rw [one_mul]
  · rw [zero_mul, hu i (by omega)]

/- English proof (translation)
Rewrite using `[herm_eq, herm_eq]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[hpk_mulVec_wb hv, pw_mulVec, pw]`. Use `split_ifs with h`. Rewrite using `[one_mul]`.

Rewrite using `[hv i (by omega), mul_zero, mul_zero, mul_zero]`.
-/
theorem herm_pw_right {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (x : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v (diagonal (pw (k := k) (r := r)) *ᵥ x) = herm (Hpk k r) v x := by
  rw [herm_eq, herm_eq]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hpk_mulVec_wb hv, pw_mulVec, pw]
  split_ifs with h
  · rw [one_mul]
  · rw [hv i (by omega), mul_zero, mul_zero, mul_zero]

/- English proof (translation)
Rewrite using `[herm_swap, herm_pw_right hv, ← herm_swap]`.
-/
theorem herm_pw_left {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (x : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (diagonal (pw (k := k) (r := r)) *ᵥ x) v = herm (Hpk k r) x v := by
  rw [herm_swap, herm_pw_right hv, ← herm_swap]

/- English proof (translation)
Introduce `i hi`. Rewrite using `[Pi.sub_apply, pw_mulVec, pw]`. Distinguish the cases in `h : i.val ≤ r + k`. Rewrite using `[if_pos ⟨hi, h⟩, one_mul, sub_self]`. Establish `e : i = esI k r ⟨2 * r + k - i.val, by omega⟩` using `by apply Fin.ext; simp [esI]; omega`.

Rewrite using `[if_neg (by omega), zero_mul, sub_zero, e, hx]`.
-/
theorem flt_sub_pw (x : Fin (2 * r + k + 1) → ℂ) (hx : ∀ b : Fin r, x (esI k r b) = 0) :
    Flt r (x - diagonal (pw (k := k) (r := r)) *ᵥ x) := by
  intro i hi
  rw [Pi.sub_apply, pw_mulVec, pw]
  by_cases h : i.val ≤ r + k
  · rw [if_pos ⟨hi, h⟩, one_mul, sub_self]
  · have e : i = esI k r ⟨2 * r + k - i.val, by omega⟩ := by apply Fin.ext; simp [esI]; omega
    rw [if_neg (by omega), zero_mul, sub_zero, e, hx]

/- English proof (translation)
Introduce `i hi`. Distinguish the cases in `h2 : i.val ≤ r + k`. Establish `hw` using `herm_w x i hi h2`. Establish `h0` using `h (bvec i) (fun b => by`. Establish `: esI k r b ≠ i` using `by intro e; have := congrArg Fin.val e; simp [esI] at this; omega`.

Simplify using `[bvec, this])`. Rewrite `h0` using `[hw]`. Use `split_ifs at h0`. Conclude with `neg_eq_zero.1 h0`. Conclude with `h0`.

Establish `e : i = esI k r ⟨2 * r + k - i.val, by omega⟩` using `by apply Fin.ext; simp [esI]; omega`. Establish `e2` using `herm_e x ⟨2 * r + k - i.val, by omega⟩`. Rewrite `e2` using `[← e]`. Rewrite using `[← e2]`. Use `h _ (fun b => ?_)` and prove the remaining obligations.

Establish `: esI k r b ≠ eI k r ⟨2 * r + k - i.val, by omega⟩`. Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact. Simplify using `[esI, eI] at this`. Use linear arithmetic over natural numbers and integers.

Simplify using `[bvec, this]`.
-/
theorem flt_of_orth (x : Fin (2 * r + k + 1) → ℂ)
    (h : ∀ v : Fin (2 * r + k + 1) → ℂ, (∀ b : Fin r, v (esI k r b) = 0) → herm (Hpk k r) x v = 0) : Flt r x := by
  intro i hi
  by_cases h2 : i.val ≤ r + k
  · have hw := herm_w x i hi h2
    have h0 := h (bvec i) (fun b => by
      have : esI k r b ≠ i := by intro e; have := congrArg Fin.val e; simp [esI] at this; omega
      simp [bvec, this])
    rw [hw] at h0
    split_ifs at h0
    · exact neg_eq_zero.1 h0
    · exact h0
  · have e : i = esI k r ⟨2 * r + k - i.val, by omega⟩ := by apply Fin.ext; simp [esI]; omega
    have e2 := herm_e x ⟨2 * r + k - i.val, by omega⟩
    rw [← e] at e2
    rw [← e2]
    refine h _ (fun b => ?_)
    have : esI k r b ≠ eI k r ⟨2 * r + k - i.val, by omega⟩ := by
      intro e; have := congrArg Fin.val e; simp [esI, eI] at this; omega
    simp [bvec, this]

/- English proof (translation)
Introduce `k r z z' _ hz _ hT _ g hg hgO ξ hξ hn hS hS'`. Take `⟨N, hN⟩` from `hn`. Use `set H := Hpk k r with hH`. Establish `hgu : gᴴ * H * g = H` using `hg`. Establish `hdetH : H.det ≠ 0`.

Use `congrArg Matrix.det (Formalism.QuantumDeterminants.WeylGroupFacts.hpk_sq (k := k) (r := r))` as an intermediate fact. Rewrite `this` using `[det_mul, det_one]`. Conclude with `left_ne_zero_of_mul_eq_one this`. Establish `hdetg : IsUnit g.det`. Rewrite using `[isUnit_iff_ne_zero]`.

Introduce `h0`. Use `congrArg Matrix.det hgu` as an intermediate fact. Rewrite `this` using `[det_mul, det_mul, h0, mul_zero]`. Conclude with `hdetH this.symm`. Establish `hgg : g * g⁻¹ = 1` using `Matrix.mul_nonsing_inv g hdetg`.

Establish `hgg' : g⁻¹ * g = 1` using `Matrix.nonsing_inv_mul g hdetg`. Use `set η := g⁻¹ * ξ * g with hηdef`. Establish `hgη : g * η = ξ * g`. Rewrite using `[hηdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hgg, Matrix.one_mul]`. Establish `hηpow : ∀ m, η ^ m = g⁻¹ * ξ ^ m * g`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => rw [pow_zero, pow_zero, Matrix.mul_one, hgg']`. Consider the case `succ m ih`. Rewrite using `[pow_succ, ih, pow_succ, hηdef]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = g⁻¹ * (ξ ^ m * ξ) * g := by rw [hgg, Matrix.mul_one]; simp only [Matrix.mul_assoc]`. Establish `hηN : η ^ N = 0` using `by rw [hηpow, hN, Matrix.mul_zero, Matrix.zero_mul]`. Establish `e1 : (g⁻¹)ᴴ * H = H * g`.

Combine the equalities or inequalities in the displayed calculation. Establish `e2 : H * g⁻¹ = gᴴ * H`. Combine the equalities or inequalities in the displayed calculation. Establish `hη : B.inLie k r η`. Establish `hξ' : ξᴴ * H + H * ξ = 0` using `hξ`.

Use `show ηᴴ * H + H * η = 0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hηdef]`. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = gᴴ * (ξᴴ * H + H * ξ) * g := by`.

Rewrite using `[e1, e2]`. Simplify using `only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]`. Use `_ = 0 := by rw [hξ', Matrix.mul_zero, Matrix.zero_mul]`. Establish `hS'η : ∀ X ∈ lieOf (Sset k r z'), (Matrix.trace (η * X)).re = 0`. Introduce `X hX`.

Use `hS' X hX` as an intermediate fact. Establish `e : Matrix.trace (ξ * (g * X * g⁻¹)) = Matrix.trace (η * X)`. Rewrite using `[show ξ * (g * X * g⁻¹) = (ξ * g * X) * g⁻¹ by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm, hηdef]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← e]`.

Conclude with `this`. Establish `hD : ∀ a (ha : a ≤ r), Dmin k r z z' g ⟨a, by omega⟩ ≠ 0`. Introduce `a ha`. Consider the cases of `a with`. Consider the case `zero => rw [dmin_eq z z' g 0 ha, Matrix.det_fin_zero]`.

Conclude with `one_ne_zero`. Consider the case `succ b => exact hgO.2 ⟨b, by omega⟩`. Establish `hX` using `killX z z' g hD ξ η hξ N hN hηN hgη (colN hξ z hS) (colN hη z' hS'η) r le_rfl`. Establish `hξgX : ∀ c : Fin r, ξ *ᵥ (g *ᵥ bvec (eI k r c)) = 0`. Introduce `c`.

Rewrite using `[mulVec_mulVec, ← hgη, ← mulVec_mulVec, (hX _ (flt_bvec r c c.isLt)).2, mulVec_zero]`. Establish `hξe : ∀ c : Fin r, ξ *ᵥ bvec (eI k r c) = 0` using `fun c => (hX _ (flt_bvec r c c.isLt)).1`. Establish `hrange : ∀ v b, (ξ *ᵥ v) (esI k r b) = 0`. Introduce `v b`. Rewrite using `[← herm_e (ξ *ᵥ v) b, herm_skew hξ, hξe, herm_zero_right, neg_zero]`.

Use `set P : B.Mat k r := diagonal (pw (k := k) (r := r)) with hP`. Establish `hξP : ∀ y, (∀ b : Fin r, y (esI k r b) = 0) → ξ *ᵥ (P *ᵥ y) = ξ *ᵥ y`. Introduce `y hy`. Use `(hX _ (flt_sub_pw y hy)).1` as an intermediate fact. Rewrite `this` using `[mulVec_sub, sub_eq_zero]`.

Conclude with `this.symm`. Establish `hcomp : ∀ w, (P * ξ * P) *ᵥ w = P *ᵥ (ξ *ᵥ (P *ᵥ w))`. Introduce `w`. Rewrite using `[mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]`. Establish `hPfix : ∀ u, inWb k r u → P *ᵥ u = u` using `fun u hu => by rw [hP]; exact pw_fix hu`.

Establish `hPin : ∀ x, inWb k r (P *ᵥ x)` using `fun x => by rw [hP]; exact pw_inWb x`. Establish `hPl : ∀ v, inWb k r v → ∀ x, herm (Hpk k r) (P *ᵥ x) v = herm (Hpk k r) x v` using `fun v hv x => by rw [hP]; exact herm_pw_left hv x`. Establish `hWcomp : ∀ u, inWb k r u → ∀ m, ((P * ξ * P) ^ m) *ᵥ u = P *ᵥ ((ξ ^ m) *ᵥ u)`. Introduce `u hu m`. Proceed by induction on `m with`.

Consider the case `zero => rw [pow_zero, pow_zero, one_mulVec, hPfix u hu]`. Consider the case `succ m ih`. Establish `hy : ∀ b : Fin r, ((ξ ^ m) *ᵥ u) (esI k r b) = 0`. Introduce `b`. Consider the cases of `m with`.

Consider the case `zero => rw [pow_zero, one_mulVec]; exact hu _ (Or.inr (by simp [esI]; omega))`. Consider the case `succ m => rw [pow_succ', ← mulVec_mulVec]`. Conclude with `hrange _ b`. Rewrite using `[pow_succ', ← mulVec_mulVec, ih, hcomp, hPfix _ (hPin _), hξP _ hy, pow_succ', ← mulVec_mulVec]`. Establish `hW` using `fun X (hX : X ∈ lieOf (UWset k r z)) => hS X (lieOf_mono (UWset_sub_Sset k r z) hX)`.

Establish `hcore` using `coreW hz hT (P * ξ * P) (fun u _ => by rw [hcomp]; exact hPin _) (fun u v hu hv => by`. Rewrite using `[hcomp, hcomp, hPfix u hu, hPfix v hv, hPl v hv, herm_swap u, hPl u hu, herm_skew hξ u v, herm_swap u])`. Use the proof step `(fun u v hu hv huz hvz => by`. Rewrite using `[hcomp, hPfix u hu, hPl v hv]`. Conclude with `herm_zero_of_lieW hξ z hW u v hu hv huz hvz)`.

Use `N (fun u hu => by rw [hWcomp u hu, hN, zero_mulVec, mulVec_zero])`. Establish `hWb : ∀ u, inWb k r u → ξ *ᵥ u = 0`. Introduce `u hu`. Establish `hc` using `hcore u hu`. Rewrite `hc` using `[hcomp, hPfix u hu, hP]`.

Establish `hflt : Flt r (ξ *ᵥ u)`. Introduce `i hi`. Distinguish the cases in `h2 : i.val ≤ r + k`. Use `congrFun hc i` as an intermediate fact. Rewrite `this` using `[pw_mulVec, pw, if_pos ⟨hi, h2⟩, one_mul]`.

Conclude with `this`. Establish `e : i = esI k r ⟨2 * r + k - i.val, by omega⟩` using `by apply Fin.ext; simp [esI]; omega`. Rewrite using `[e]`. Conclude with `hrange u _`. Use `dlem_ii z z' g r le_rfl (hD r le_rfl) _ hflt (fun c _ => ?_)` and prove the remaining obligations.

Rewrite using `[herm_skew hξ, hξgX, herm_zero_right, neg_zero]`. Establish `hperp : ∀ y, (∀ b : Fin r, y (esI k r b) = 0) → ξ *ᵥ y = 0`. Introduce `y hy`. Rewrite using `[← hξP y hy]`. Conclude with `hWb _ (pw_inWb _)`.

Establish `hstar : ∀ b : Fin r, ξ *ᵥ bvec (esI k r b) = 0`. Introduce `b`. Establish `hflt : Flt r (ξ *ᵥ bvec (esI k r b))`. Use `flt_of_orth _ (fun v hv => ?_)` and prove the remaining obligations. Rewrite using `[herm_skew hξ, hperp v hv, herm_zero_right, neg_zero]`.

Use `dlem_ii z z' g r le_rfl (hD r le_rfl) _ hflt (fun c _ => ?_)` and prove the remaining obligations. Rewrite using `[herm_skew hξ, hξgX, herm_zero_right, neg_zero]`. Apply `Matrix.ext` to reduce the goal to its premises. Introduce `i j`. Rewrite using `[mat_eq_mulVec_bvec ξ i j]`.

Distinguish the cases in `hj : j.val ≤ r + k`. Rewrite using `[hperp (bvec j) (fun b => by`. Establish `: esI k r b ≠ j` using `by intro e; have := congrArg Fin.val e; simp [esI] at this; omega`. Simplify using `[bvec, this])]`. Both sides reduce to the same expression.

Establish `e : j = esI k r ⟨2 * r + k - j.val, by omega⟩` using `by apply Fin.ext; simp [esI]; omega`. Rewrite using `[e, hstar]`. Both sides reduce to the same expression.
-/
theorem symbolNil_direct : SymbolNil := by
  intro k r z z' _ hz _ hT _ g hg hgO ξ hξ hn hS hS'
  obtain ⟨N, hN⟩ := hn
  set H := Hpk k r with hH
  have hgu : gᴴ * H * g = H := hg
  have hdetH : H.det ≠ 0 := by
    have := congrArg Matrix.det (Formalism.QuantumDeterminants.WeylGroupFacts.hpk_sq (k := k) (r := r))
    rw [det_mul, det_one] at this
    exact left_ne_zero_of_mul_eq_one this
  have hdetg : IsUnit g.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have := congrArg Matrix.det hgu
    rw [det_mul, det_mul, h0, mul_zero] at this
    exact hdetH this.symm
  have hgg : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hdetg
  have hgg' : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hdetg
  set η := g⁻¹ * ξ * g with hηdef
  have hgη : g * η = ξ * g := by
    rw [hηdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hgg, Matrix.one_mul]
  have hηpow : ∀ m, η ^ m = g⁻¹ * ξ ^ m * g := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, Matrix.mul_one, hgg']
    | succ m ih =>
      rw [pow_succ, ih, pow_succ, hηdef]
      calc g⁻¹ * ξ ^ m * g * (g⁻¹ * ξ * g) = g⁻¹ * ξ ^ m * (g * g⁻¹) * ξ * g := by
            simp only [Matrix.mul_assoc]
        _ = g⁻¹ * (ξ ^ m * ξ) * g := by rw [hgg, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hηN : η ^ N = 0 := by rw [hηpow, hN, Matrix.mul_zero, Matrix.zero_mul]
  have e1 : (g⁻¹)ᴴ * H = H * g := by
    calc (g⁻¹)ᴴ * H = (g⁻¹)ᴴ * (gᴴ * H * g) := by rw [hgu]
      _ = (g * g⁻¹)ᴴ * H * g := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = H * g := by rw [hgg, conjTranspose_one, Matrix.one_mul]
  have e2 : H * g⁻¹ = gᴴ * H := by
    calc H * g⁻¹ = gᴴ * H * g * g⁻¹ := by rw [hgu]
      _ = gᴴ * H := by rw [Matrix.mul_assoc, hgg, Matrix.mul_one]
  have hη : B.inLie k r η := by
    have hξ' : ξᴴ * H + H * ξ = 0 := hξ
    show ηᴴ * H + H * η = 0
    calc ηᴴ * H + H * η = gᴴ * ξᴴ * ((g⁻¹)ᴴ * H) + (H * g⁻¹) * ξ * g := by
          rw [hηdef]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = gᴴ * (ξᴴ * H + H * ξ) * g := by
          rw [e1, e2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hξ', Matrix.mul_zero, Matrix.zero_mul]
  have hS'η : ∀ X ∈ lieOf (Sset k r z'), (Matrix.trace (η * X)).re = 0 := by
    intro X hX
    have := hS' X hX
    have e : Matrix.trace (ξ * (g * X * g⁻¹)) = Matrix.trace (η * X) := by
      rw [show ξ * (g * X * g⁻¹) = (ξ * g * X) * g⁻¹ by simp only [Matrix.mul_assoc],
        Matrix.trace_mul_comm, hηdef]
      simp only [Matrix.mul_assoc]
    rw [← e]; exact this
  have hD : ∀ a (ha : a ≤ r), Dmin k r z z' g ⟨a, by omega⟩ ≠ 0 := by
    intro a ha
    cases a with
    | zero => rw [dmin_eq z z' g 0 ha, Matrix.det_fin_zero]; exact one_ne_zero
    | succ b => exact hgO.2 ⟨b, by omega⟩
  have hX := killX z z' g hD ξ η hξ N hN hηN hgη (colN hξ z hS) (colN hη z' hS'η) r le_rfl
  have hξgX : ∀ c : Fin r, ξ *ᵥ (g *ᵥ bvec (eI k r c)) = 0 := by
    intro c
    rw [mulVec_mulVec, ← hgη, ← mulVec_mulVec, (hX _ (flt_bvec r c c.isLt)).2, mulVec_zero]
  have hξe : ∀ c : Fin r, ξ *ᵥ bvec (eI k r c) = 0 := fun c => (hX _ (flt_bvec r c c.isLt)).1
  have hrange : ∀ v b, (ξ *ᵥ v) (esI k r b) = 0 := by
    intro v b
    rw [← herm_e (ξ *ᵥ v) b, herm_skew hξ, hξe, herm_zero_right, neg_zero]
  set P : B.Mat k r := diagonal (pw (k := k) (r := r)) with hP
  have hξP : ∀ y, (∀ b : Fin r, y (esI k r b) = 0) → ξ *ᵥ (P *ᵥ y) = ξ *ᵥ y := by
    intro y hy
    have := (hX _ (flt_sub_pw y hy)).1
    rw [mulVec_sub, sub_eq_zero] at this
    exact this.symm
  have hcomp : ∀ w, (P * ξ * P) *ᵥ w = P *ᵥ (ξ *ᵥ (P *ᵥ w)) := by
    intro w; rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have hPfix : ∀ u, inWb k r u → P *ᵥ u = u := fun u hu => by rw [hP]; exact pw_fix hu
  have hPin : ∀ x, inWb k r (P *ᵥ x) := fun x => by rw [hP]; exact pw_inWb x
  have hPl : ∀ v, inWb k r v → ∀ x, herm (Hpk k r) (P *ᵥ x) v = herm (Hpk k r) x v :=
    fun v hv x => by rw [hP]; exact herm_pw_left hv x
  have hWcomp : ∀ u, inWb k r u → ∀ m, ((P * ξ * P) ^ m) *ᵥ u = P *ᵥ ((ξ ^ m) *ᵥ u) := by
    intro u hu m
    induction m with
    | zero => rw [pow_zero, pow_zero, one_mulVec, hPfix u hu]
    | succ m ih =>
      have hy : ∀ b : Fin r, ((ξ ^ m) *ᵥ u) (esI k r b) = 0 := by
        intro b
        cases m with
        | zero => rw [pow_zero, one_mulVec]; exact hu _ (Or.inr (by simp [esI]; omega))
        | succ m => rw [pow_succ', ← mulVec_mulVec]; exact hrange _ b
      rw [pow_succ', ← mulVec_mulVec, ih, hcomp, hPfix _ (hPin _), hξP _ hy, pow_succ', ← mulVec_mulVec]
  have hW := fun X (hX : X ∈ lieOf (UWset k r z)) => hS X (lieOf_mono (UWset_sub_Sset k r z) hX)
  have hcore := coreW hz hT (P * ξ * P)
    (fun u _ => by rw [hcomp]; exact hPin _)
    (fun u v hu hv => by
      rw [hcomp, hcomp, hPfix u hu, hPfix v hv, hPl v hv, herm_swap u, hPl u hu, herm_skew hξ u v, herm_swap u])
    (fun u v hu hv huz hvz => by
      rw [hcomp, hPfix u hu, hPl v hv]
      exact herm_zero_of_lieW hξ z hW u v hu hv huz hvz)
    N (fun u hu => by rw [hWcomp u hu, hN, zero_mulVec, mulVec_zero])
  have hWb : ∀ u, inWb k r u → ξ *ᵥ u = 0 := by
    intro u hu
    have hc := hcore u hu
    rw [hcomp, hPfix u hu, hP] at hc
    have hflt : Flt r (ξ *ᵥ u) := by
      intro i hi
      by_cases h2 : i.val ≤ r + k
      · have := congrFun hc i
        rw [pw_mulVec, pw, if_pos ⟨hi, h2⟩, one_mul] at this
        exact this
      · have e : i = esI k r ⟨2 * r + k - i.val, by omega⟩ := by apply Fin.ext; simp [esI]; omega
        rw [e]; exact hrange u _
    refine dlem_ii z z' g r le_rfl (hD r le_rfl) _ hflt (fun c _ => ?_)
    rw [herm_skew hξ, hξgX, herm_zero_right, neg_zero]
  have hperp : ∀ y, (∀ b : Fin r, y (esI k r b) = 0) → ξ *ᵥ y = 0 := by
    intro y hy
    rw [← hξP y hy]
    exact hWb _ (pw_inWb _)
  have hstar : ∀ b : Fin r, ξ *ᵥ bvec (esI k r b) = 0 := by
    intro b
    have hflt : Flt r (ξ *ᵥ bvec (esI k r b)) := by
      refine flt_of_orth _ (fun v hv => ?_)
      rw [herm_skew hξ, hperp v hv, herm_zero_right, neg_zero]
    refine dlem_ii z z' g r le_rfl (hD r le_rfl) _ hflt (fun c _ => ?_)
    rw [herm_skew hξ, hξgX, herm_zero_right, neg_zero]
  apply Matrix.ext
  intro i j
  rw [mat_eq_mulVec_bvec ξ i j]
  by_cases hj : j.val ≤ r + k
  · rw [hperp (bvec j) (fun b => by
      have : esI k r b ≠ j := by intro e; have := congrArg Fin.val e; simp [esI] at this; omega
      simp [bvec, this])]
    rfl
  · have e : j = esI k r ⟨2 * r + k - j.val, by omega⟩ := by apply Fin.ext; simp [esI]; omega
    rw [e, hstar]
    rfl

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

namespace Formalism.FourierDecayAlt.P.CutMP.JfS

/- English proof (translation)
The claim follows from `Sym.symbolNil_direct`.
-/
theorem symbol_nilpotent_holds : SymbolNil := Sym.symbolNil_direct

end Formalism.FourierDecayAlt.P.CutMP.JfS
