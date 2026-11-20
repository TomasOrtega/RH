import Formalism.HermitianCurvature.FrameExists2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AnisotropicColumnSums
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity

open Matrix Finset Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace HermitianFormSums

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [herm]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Qx8.herm_add_left', Qx8.herm_smul_left', ih]`.
-/
theorem herm_lsum {N : ℕ} {ι : Type*} (H : Matrix (Fin N) (Fin N) ℂ) (s : Finset ι) (c : ι → ℂ) (v : ι → Fin N → ℂ)
    (w : Fin N → ℂ) : herm H (∑ a ∈ s, c a • v a) w = ∑ a ∈ s, c a * herm H (v a) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [herm]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Qx8.herm_add_left', Qx8.herm_smul_left', ih]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [herm]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Qx8.herm_add_right', Qx8.herm_smul_right', ih]`.
-/
theorem herm_rsum {N : ℕ} {ι : Type*} (H : Matrix (Fin N) (Fin N) ℂ) (s : Finset ι) (c : ι → ℂ) (v : ι → Fin N → ℂ)
    (w : Fin N → ℂ) : herm H w (∑ a ∈ s, c a • v a) = ∑ a ∈ s, star (c a) * herm H w (v a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [herm]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Qx8.herm_add_right', Qx8.herm_smul_right', ih]

variable {k r : ℕ}

/- English proof (translation)
Introduce `i hi`. Rewrite using `[Finset.sum_apply]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `a _`. Rewrite using `[Pi.smul_apply, hv a i hi, smul_zero]`.
-/
theorem inWb_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (v : ι → Fin (2 * r + k + 1) → ℂ)
    (hv : ∀ a, inWb k r (v a)) : inWb k r (∑ a ∈ s, c a • v a) := by
  intro i hi
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro a _
  rw [Pi.smul_apply, hv a i hi, smul_zero]

/- English proof (translation)
Rewrite using `[herm_lsum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `a _`. Rewrite using `[herm_rsum]`. Simplify using `only [hC.2.1, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.
-/
theorem herm_comb {m : ℕ} {vs : List (Fin (2 * r + k + 1) → ℂ)} {C : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hC : IsFrameOf k r vs C) (f g : Fin m → ℂ) :
    herm (Hpk k r) (∑ a, f a • C a) (∑ b, g b • C b) = ∑ a, f a * star (g a) := by
  rw [herm_lsum]
  apply Finset.sum_congr rfl
  intro a _
  rw [herm_rsum]
  simp only [hC.2.1, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/- English proof (translation)
Rewrite using `[Fin.sum_univ_eq_sum_range, AnisotropicColumnSums.mdim_last, Finset.sum_range_succ, Fin.sum_univ_eq_sum_range]`.
-/
theorem sum_mdim {X : Type*} [AddCommMonoid X] (F : ℕ → X) :
    ∑ j : Fin (mdim k r (Fin.last r)), F j.val = ∑ a : Fin k, F a.val + F k := by
  rw [Fin.sum_univ_eq_sum_range, AnisotropicColumnSums.mdim_last, Finset.sum_range_succ, Fin.sum_univ_eq_sum_range]

/- English proof (translation)
Use `set P : Matrix (Fin (mdim k r (Fin.last r))) (Fin (mdim k r (Fin.last r))) ℂ := Matrix.of fun c j => AnisotropicColumnSums.bcol k r x Bs j (posL k r (Fin.last r) c) with hP`. Use `set Q : Matrix (Fin (mdim k r (Fin.last r))) (Fin (mdim k r (Fin.last r))) ℂ := Matrix.of fun j d => herm (Hpk k r) (bvec (posL k r (Fin.last r) d)) (AnisotropicColumnSums.bcol k r x Bs j) * AnisotropicColumnSums.nrm k r x j with hQ`. Establish `hQP : Q * P = 1`. Use extensionality with `j j'`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply, ← AnisotropicColumnSums.gram hxx hB j j', ← AnisotropicColumnSums.sum_last (AnisotropicColumnSums.bcol_inWb hx hB j'), Finset.sum_mul]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `d _`. Simplify using `only [hP, hQ, Matrix.of_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `hPQ : P * Q = 1` using `mul_eq_one_comm.1 hQP`.

Establish `key : v = ∑ j : Fin (mdim k r (Fin.last r)), (herm (Hpk k r) v (AnisotropicColumnSums.bcol k r x Bs j) * AnisotropicColumnSums.nrm k r x j) • AnisotropicColumnSums.bcol k r x Bs j`. Use function extensionality and compare the values at `p`. Distinguish the cases in `hp : p.val < r ∨ r + k < p.val`. Rewrite using `[hv p hp, inWb_sum _ _ _ (AnisotropicColumnSums.bcol_inWb hx hB) p hp]`. Choose the witnesses or unpack the hypotheses as in `⟨c, rfl⟩ : ∃ c, posL k r (Fin.last r) c = p := by`.

Use `⟨⟨p.val - r, by rw [AnisotropicColumnSums.mdim_last]; omega⟩, Fin.ext ?_⟩` and prove the remaining obligations. Simplify using `only [posL, Fin.val_last]`. Use linear arithmetic over natural numbers and integers. Establish `h1 : ((P * Q) *ᵥ fun d => v (posL k r (Fin.last r) d)) c = v (posL k r (Fin.last r) c)`. Rewrite using `[hPQ, Matrix.one_mulVec]`.

Rewrite using `[← h1, ← Matrix.mulVec_mulVec, Finset.sum_apply]`. Use `show ∑ j, P c j * (Q *ᵥ fun d => v (posL k r (Fin.last r) d)) j = _`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `j _`. Establish `h2 : (Q *ᵥ fun d => v (posL k r (Fin.last r) d)) j = herm (Hpk k r) v (AnisotropicColumnSums.bcol k r x Bs j) * AnisotropicColumnSums.nrm k r x j`.

Rewrite using `[← AnisotropicColumnSums.sum_last hv, Finset.sum_mul]`. Use `show ∑ d, Q j d * v (posL k r (Fin.last r) d) = _`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `d _`. Simplify using `only [hQ, Matrix.of_apply]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`. Simplify using `only [hP, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3` using `sum_mdim (k := k) (r := r) (fun i : ℕ => if h : i < k then herm (Hpk k r) v (Bs ⟨i, h⟩) • Bs ⟨i, h⟩ else (herm (Hpk k r) v x * (herm (Hpk k r) x x)⁻¹) • x)`.

Establish `h4 : ∀ j : Fin (mdim k r (Fin.last r)), (herm (Hpk k r) v (AnisotropicColumnSums.bcol k r x Bs j) * AnisotropicColumnSums.nrm k r x j) • AnisotropicColumnSums.bcol k r x Bs j = if h : j.val < k then herm (Hpk k r) v (Bs ⟨j.val, h⟩) • Bs ⟨j.val, h⟩ else (herm (Hpk k r) v x * (herm …`. Introduce `j`. Unfold `AnisotropicColumnSums.bcol AnisotropicColumnSums.nrm`. Use `split_ifs with h`. Rewrite using `[mul_one]`.

Both sides reduce to the same expression. Rewrite `key` using `[Finset.sum_congr rfl fun j _ => h4 j, h3]`. Simplify using `using key`.
-/
theorem complete {x : Fin (2 * r + k + 1) → ℂ} {Bs : Fin k → Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x)
    (hxx : herm (Hpk k r) x x ≠ 0) (hB : IsFrameOf k r [x] Bs) {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    v = ∑ a, herm (Hpk k r) v (Bs a) • Bs a + (herm (Hpk k r) v x * (herm (Hpk k r) x x)⁻¹) • x := by
  set P : Matrix (Fin (mdim k r (Fin.last r))) (Fin (mdim k r (Fin.last r))) ℂ :=
    Matrix.of fun c j => AnisotropicColumnSums.bcol k r x Bs j (posL k r (Fin.last r) c) with hP
  set Q : Matrix (Fin (mdim k r (Fin.last r))) (Fin (mdim k r (Fin.last r))) ℂ :=
    Matrix.of fun j d => herm (Hpk k r) (bvec (posL k r (Fin.last r) d)) (AnisotropicColumnSums.bcol k r x Bs j) * AnisotropicColumnSums.nrm k r x j
    with hQ
  have hQP : Q * P = 1 := by
    ext j j'
    rw [Matrix.mul_apply, Matrix.one_apply, ← AnisotropicColumnSums.gram hxx hB j j', ← AnisotropicColumnSums.sum_last (AnisotropicColumnSums.bcol_inWb hx hB j'),
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    simp only [hP, hQ, Matrix.of_apply]
    ring
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  have key : v = ∑ j : Fin (mdim k r (Fin.last r)),
      (herm (Hpk k r) v (AnisotropicColumnSums.bcol k r x Bs j) * AnisotropicColumnSums.nrm k r x j) • AnisotropicColumnSums.bcol k r x Bs j := by
    funext p
    by_cases hp : p.val < r ∨ r + k < p.val
    · rw [hv p hp, inWb_sum _ _ _ (AnisotropicColumnSums.bcol_inWb hx hB) p hp]
    · obtain ⟨c, rfl⟩ : ∃ c, posL k r (Fin.last r) c = p := by
        refine ⟨⟨p.val - r, by rw [AnisotropicColumnSums.mdim_last]; omega⟩, Fin.ext ?_⟩
        simp only [posL, Fin.val_last]
        omega
      have h1 : ((P * Q) *ᵥ fun d => v (posL k r (Fin.last r) d)) c = v (posL k r (Fin.last r) c) := by
        rw [hPQ, Matrix.one_mulVec]
      rw [← h1, ← Matrix.mulVec_mulVec, Finset.sum_apply]
      show ∑ j, P c j * (Q *ᵥ fun d => v (posL k r (Fin.last r) d)) j = _
      apply Finset.sum_congr rfl
      intro j _
      have h2 : (Q *ᵥ fun d => v (posL k r (Fin.last r) d)) j =
          herm (Hpk k r) v (AnisotropicColumnSums.bcol k r x Bs j) * AnisotropicColumnSums.nrm k r x j := by
        rw [← AnisotropicColumnSums.sum_last hv, Finset.sum_mul]
        show ∑ d, Q j d * v (posL k r (Fin.last r) d) = _
        apply Finset.sum_congr rfl
        intro d _
        simp only [hQ, Matrix.of_apply]
        ring
      rw [h2]
      simp only [hP, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
      ring
  have h3 := sum_mdim (k := k) (r := r) (fun i : ℕ =>
    if h : i < k then herm (Hpk k r) v (Bs ⟨i, h⟩) • Bs ⟨i, h⟩
    else (herm (Hpk k r) v x * (herm (Hpk k r) x x)⁻¹) • x)
  have h4 : ∀ j : Fin (mdim k r (Fin.last r)),
      (herm (Hpk k r) v (AnisotropicColumnSums.bcol k r x Bs j) * AnisotropicColumnSums.nrm k r x j) • AnisotropicColumnSums.bcol k r x Bs j =
      if h : j.val < k then herm (Hpk k r) v (Bs ⟨j.val, h⟩) • Bs ⟨j.val, h⟩
      else (herm (Hpk k r) v x * (herm (Hpk k r) x x)⁻¹) • x := by
    intro j
    unfold AnisotropicColumnSums.bcol AnisotropicColumnSums.nrm
    split_ifs with h
    · rw [mul_one]
    · rfl
  rw [Finset.sum_congr rfl fun j _ => h4 j, h3] at key
  simpa using key

/- English proof (translation)
Establish `h` using `complete hx hxx hB hv`. Rewrite `h` using `[hvx, zero_mul, zero_smul, add_zero]`. Then use the resulting hypothesis.
-/
theorem complete0 {x : Fin (2 * r + k + 1) → ℂ} {Bs : Fin k → Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x)
    (hxx : herm (Hpk k r) x x ≠ 0) (hB : IsFrameOf k r [x] Bs) {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v)
    (hvx : herm (Hpk k r) v x = 0) : v = ∑ a, herm (Hpk k r) v (Bs a) • Bs a := by
  have h := complete hx hxx hB hv
  rwa [hvx, zero_mul, zero_smul, add_zero] at h

/- English proof (translation)
Introduce `h`. Unfold `Tz at hT`. Rewrite `hT` using `[h]`. Simplify using `at hT`.
-/
theorem hzz {z : Fin (2 * r + k + 1) → ℂ} (hT : 0 < Tz k r z) : herm (Hpk k r) z z ≠ 0 := by
  intro h
  unfold Tz at hT
  rw [h] at hT
  simp at hT

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Establish `h` using `(hE W k r z π hπ Z0 Z0 h0 h0).2.1 0`. Simplify using `using h`. Consider the case `insert a s ha ih`.

Establish `h1` using `(hE W k r z π hπ (Z a) (Z a) (hZ a) (hZ a)).2.1 (c a)`. Establish `h2` using `(hE W k r z π hπ _ _ h1.1 ih.1).1`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`. Conclude with `⟨h2.1, by rw [h2.2, h1.2, ih.2]⟩`.
-/
theorem ec_sum (hE : Formalism.FourierDecayAlt.Qr.EcLie) {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)} (hπ : IsRepW k r z π) {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (Z : ι → Mx k r) (hZ : ∀ i, InGlW k r z (Z i)) (Z0 : Mx k r) (h0 : InGlW k r z Z0) :
    InGlW k r z (∑ i ∈ s, c i • Z i) ∧ ecOp π (∑ i ∈ s, c i • Z i) = ∑ i ∈ s, c i • ecOp π (Z i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := (hE W k r z π hπ Z0 Z0 h0 h0).2.1 0
    simpa using h
  | insert a s ha ih =>
    have h1 := (hE W k r z π hπ (Z a) (Z a) (hZ a) (hZ a)).2.1 (c a)
    have h2 := (hE W k r z π hπ _ _ h1.1 ih.1).1
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨h2.1, by rw [h2.2, h1.2, ih.2]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨hB.1, hB.2.1, fun a v hv => hB.2.2 a v (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢; exact Or.inl hv)⟩`.
-/
theorem frame_sub {m : ℕ} {z e : Fin (2 * r + k + 1) → ℂ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hB : IsFrameOf k r [z, e] Bs) : IsFrameOf k r [z] Bs :=
  ⟨hB.1, hB.2.1, fun a v hv => hB.2.2 a v (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢; exact Or.inl hv)⟩

end HermitianFormSums

/- English proof (translation)
Introduce `n r z e hz hT he hez hee`. Take `⟨C, hC⟩` from `Qx8.frame_exists hz hT`. Establish `hexp` using `HermitianFormSums.complete0 hz (HermitianFormSums.hzz hT) hC he hez`. Use `set ε : Fin (n + 1) → ℂ := fun a => herm (Hpk (n + 1) r) e (C a) with hε`. Establish `hnorm : ∑ a, ε a * star (ε a) = 1`.

Rewrite using `[← HermitianFormSums.herm_comb hC ε ε, ← hexp, hee]`. Set `εE : EuclideanSpace ℂ (Fin (n + 1))` to `WithLp.toLp 2 ε`. Establish `hin : ∀ x y : EuclideanSpace ℂ (Fin (n + 1)), inner ℂ x y = ∑ a, y a * star (x a)`. Introduce `x y`. Rewrite using `[PiLp.inner_apply]`.

Both sides reduce to the same expression. Establish `hεn : ‖εE‖ = 1`. Establish `h1 : inner ℂ εE εE = (1 : ℂ)` using `by rw [hin]; exact hnorm`. Establish `h2 : ‖εE‖ ^ 2 = 1` using `by rw [@norm_sq_eq_re_inner ℂ, h1]; simp`. Use polynomial arithmetic with `[norm_nonneg εE, sq_nonneg (‖εE‖ - 1), sq_nonneg (‖εE‖ + 1)]`.

Establish `hon : Orthonormal ℂ (({Fin.last n} : Set (Fin (n + 1))).domRestrict fun _ => εE)`. Use `⟨fun _ => hεn, fun i j hij => ?_⟩` and prove the remaining obligations. Conclude with `absurd (Subsingleton.elim i j) hij`. Take `⟨b, hb⟩` from `hon.exists_orthonormalBasis_extension_of_card_eq (by simp)`. Establish `hbl : b (Fin.last n) = εE` using `hb _ rfl`.

Use `⟨fun j => ∑ a, (b j.castSucc) a • C a, fun j => HermitianFormSums.inWb_sum _ _ _ hC.1, fun i j => ?_, fun j v hv => ?_⟩` and prove the remaining obligations. Rewrite using `[HermitianFormSums.herm_comb hC, ← hin, orthonormal_iff_ite.1 b.orthonormal]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[if_neg h, if_neg]`. Introduce `h'`. Conclude with `h (Fin.castSucc_injective _ h').symm`. Simplify using `only [List.mem_cons, List.not_mem_nil, or_false] at hv`. Break down `hv with rfl | rfl` into its components or cases.

Rewrite using `[HermitianFormSums.herm_lsum]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `a _`. Rewrite using `[hC.2.2 a v (by simp), mul_zero]`. Rewrite using `[hexp, HermitianFormSums.herm_comb hC]`.

Establish `h1 : ∑ a, (b j.castSucc) a * star (ε a) = inner ℂ (b (Fin.last n)) (b j.castSucc)`. Rewrite using `[hin, hbl]`. Rewrite using `[show (∑ a, (b j.castSucc) a * star (herm (Hpk (n + 1) r) v (C a))) = ∑ a, (b j.castSucc) a * star (ε a) from rfl, h1, orthonormal_iff_ite.1 b.orthonormal, if_neg]`. Conclude with `(Fin.castSucc_lt_last j).ne'`.
-/
theorem exists_frame_two : Formalism.FourierDecayAlt.Qr.FrameExists2 := by
  intro n r z e hz hT he hez hee
  obtain ⟨C, hC⟩ := Qx8.frame_exists hz hT
  have hexp := HermitianFormSums.complete0 hz (HermitianFormSums.hzz hT) hC he hez
  set ε : Fin (n + 1) → ℂ := fun a => herm (Hpk (n + 1) r) e (C a) with hε
  have hnorm : ∑ a, ε a * star (ε a) = 1 := by
    rw [← HermitianFormSums.herm_comb hC ε ε, ← hexp, hee]
  let εE : EuclideanSpace ℂ (Fin (n + 1)) := WithLp.toLp 2 ε
  have hin : ∀ x y : EuclideanSpace ℂ (Fin (n + 1)), inner ℂ x y = ∑ a, y a * star (x a) := by
    intro x y
    rw [PiLp.inner_apply]
    rfl
  have hεn : ‖εE‖ = 1 := by
    have h1 : inner ℂ εE εE = (1 : ℂ) := by rw [hin]; exact hnorm
    have h2 : ‖εE‖ ^ 2 = 1 := by rw [@norm_sq_eq_re_inner ℂ, h1]; simp
    nlinarith [norm_nonneg εE, sq_nonneg (‖εE‖ - 1), sq_nonneg (‖εE‖ + 1)]
  have hon : Orthonormal ℂ (({Fin.last n} : Set (Fin (n + 1))).domRestrict fun _ => εE) := by
    refine ⟨fun _ => hεn, fun i j hij => ?_⟩
    exact absurd (Subsingleton.elim i j) hij
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have hbl : b (Fin.last n) = εE := hb _ rfl
  refine ⟨fun j => ∑ a, (b j.castSucc) a • C a, fun j => HermitianFormSums.inWb_sum _ _ _ hC.1, fun i j => ?_, fun j v hv => ?_⟩
  · rw [HermitianFormSums.herm_comb hC, ← hin, orthonormal_iff_ite.1 b.orthonormal]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg]
      intro h'
      exact h (Fin.castSucc_injective _ h').symm
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · rw [HermitianFormSums.herm_lsum]
      apply Finset.sum_eq_zero
      intro a _
      rw [hC.2.2 a v (by simp), mul_zero]
    · rw [hexp, HermitianFormSums.herm_comb hC]
      have h1 : ∑ a, (b j.castSucc) a * star (ε a) = inner ℂ (b (Fin.last n)) (b j.castSucc) := by
        rw [hin, hbl]
      rw [show (∑ a, (b j.castSucc) a * star (herm (Hpk (n + 1) r) v (C a))) = ∑ a, (b j.castSucc) a * star (ε a) from rfl,
        h1, orthonormal_iff_ite.1 b.orthonormal, if_neg]
      exact (Fin.castSucc_lt_last j).ne'

/- English proof (translation)
Introduce `hEc hFG W _ _ _ n r z e π Bs Bs' hz hT he hez hee hπ hB hB' w`. Establish `hB1` using `HermitianFormSums.frame_sub hB`. Establish `hB1'` using `HermitianFormSums.frame_sub hB'`. Use `set C : Fin (n + 1) → Fin (2 * r + (n + 1) + 1) → ℂ := Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Bs' e with hCdef`. Establish `hCc : ∀ a : Fin n, C a.castSucc = Bs' a` using `fun a => by rw [hCdef, Fin.snoc_castSucc]`.

Establish `hCl : C (Fin.last n) = e` using `by rw [hCdef, Fin.snoc_last]`. Establish `hBe : ∀ a, herm (Hpk (n + 1) r) (Bs' a) e = 0` using `fun a => hB'.2.2 a e (by simp)`. Establish `heB : ∀ a, herm (Hpk (n + 1) r) e (Bs' a) = 0` using `fun a => by`. Rewrite using `[← Qx2.herm_star, hBe, star_zero]`. Establish `hC : IsFrameOf (n + 1) r [z] C`.

Use `⟨fun a => ?_, fun a b => ?_, fun a v hv => ?_⟩` and prove the remaining obligations. Use `Fin.lastCases ?_ (fun a => ?_) a` and prove the remaining obligations. Rewrite using `[hCl]`. Conclude with `he`. Rewrite using `[hCc]`.

Conclude with `hB'.1 a`. Use `Fin.lastCases ?_ (fun a => ?_) a` and prove the remaining obligations. Use `Fin.lastCases ?_ (fun b => ?_) b` and prove the remaining obligations. Rewrite using `[hCl, hee, if_pos rfl]`. Rewrite using `[hCl, hCc, heB, if_neg (Fin.castSucc_lt_last b).ne']`.

Use `Fin.lastCases ?_ (fun b => ?_) b` and prove the remaining obligations. Rewrite using `[hCl, hCc, hBe, if_neg (Fin.castSucc_lt_last a).ne]`. Rewrite using `[hCc, hCc, hB'.2.1]`. Simplify using `only [Fin.castSucc_inj]`. Simplify using `only [List.mem_cons, List.not_mem_nil, or_false] at hv`.

Substitute `hv` using the available equality. Use `Fin.lastCases ?_ (fun a => ?_) a` and prove the remaining obligations. Rewrite using `[hCl]`. Conclude with `hez`. Rewrite using `[hCc]; exact hB'.2.2 a v (by simp)`.

Use `set P : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun c a => herm (Hpk (n + 1) r) (Bs a) (Bs' c) with hP`. Use `set Q : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun b d => herm (Hpk (n + 1) r) (Bs' d) (Bs b) with hQ`. Establish `hexp : ∀ a, Bs a = ∑ c, P c a • Bs' c`. Introduce `a`. Establish `h` using `HermitianFormSums.complete0 hz (HermitianFormSums.hzz hT) hC (hB.1 a) (hB.2.2 a z (by simp))`.

Rewrite `h` using `[Fin.sum_univ_castSucc, hCl, hB.2.2 a e (by simp), zero_smul, add_zero]`. Simplify using `only [hCc] at h`. Conclude with `h`. Establish `hQP : Q * P = 1`. Use extensionality with `b a`.

Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Establish `h1 : herm (Hpk (n + 1) r) (Bs a) (Bs b) = herm (Hpk (n + 1) r) (∑ c, P c a • Bs' c) (Bs b)`. Rewrite using `[← hexp a]`. Rewrite `h1` using `[HermitianFormSums.herm_lsum, hB.2.1]`. Rewrite using `[show (if b = a then (1 : ℂ) else 0) = if a = b then 1 else 0 by simp only [eq_comm], h1]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `c _`. Simplify using `only [hQ, Matrix.of_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `hPQ : P * Q = 1` using `mul_eq_one_comm.1 hQP`.

Establish `hunit : ∀ a b, unitB (Hpk (n + 1) r) Bs a b = ∑ x ∈ (Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n)), (P x.1 a * Q b x.2) • unitB (Hpk (n + 1) r) Bs' x.1 x.2`. Introduce `a b`. Rewrite using `[Finset.sum_product]`. Use extensionality with `p q`. Establish `h1 : Bs a p = ∑ c, P c a * Bs' c p`.

Use `congrFun (hexp a) p` as an intermediate fact. Rewrite `this` using `[Finset.sum_apply]`. Conclude with `this`. Establish `h2 : herm (Hpk (n + 1) r) (bvec q) (Bs b) = ∑ d, Q b d * herm (Hpk (n + 1) r) (bvec q) (Bs' d)`. Establish `h3 : herm (Hpk (n + 1) r) (bvec q) (Bs b) = herm (Hpk (n + 1) r) (bvec q) (∑ d, P d b • Bs' d)`.

Rewrite using `[← hexp b]`. Rewrite using `[h3, HermitianFormSums.herm_rsum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `d _`. Simplify using `only [hP, hQ, Matrix.of_apply, Qx2.herm_star]`.

Simplify using `only [Matrix.sum_apply, Matrix.smul_apply, unitB, Matrix.of_apply, smul_eq_mul]`. Rewrite using `[h1, h2, Finset.sum_mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `c _`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `d _`. Expand and normalize the polynomial expressions, which then agree. Establish `hEB : EB π Bs = Econj (EB π Bs') P Q`. Use function extensionality and compare the values at `a b`. Unfold `EB Econj`.

Rewrite using `[hunit a b, (HermitianFormSums.ec_sum hEc hπ _ _ (fun x : Fin n × Fin n => unitB (Hpk (n + 1) r) Bs' x.1 x.2) (fun x => QrD.frame_lie hB1' x.1 x.2) _ (QrD.frame_lie hB1' a a)).2, Finset.sum_product]`. Use extensionality with `v`. Simplify using the standard rewrite rules. Rewrite using `[hEB]`. Conclude with `((contractions_covariant (Module.End ℂ W) n (EB π Bs') P Q (hFG W (n + 1) r n z π Bs' hπ hB1').1 hQP hPQ w 0 0 0 0).1)`.
-/
theorem qr_frameChange_of : Formalism.FourierDecayAlt.Qr.EcLie → Formalism.FourierDecayAlt.Qr.FrameGl → Formalism.FourierDecayAlt.Qr.FrameChange := by
  intro hEc hFG W _ _ _ n r z e π Bs Bs' hz hT he hez hee hπ hB hB' w
  have hB1 := HermitianFormSums.frame_sub hB
  have hB1' := HermitianFormSums.frame_sub hB'
  set C : Fin (n + 1) → Fin (2 * r + (n + 1) + 1) → ℂ :=
    Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Bs' e with hCdef
  have hCc : ∀ a : Fin n, C a.castSucc = Bs' a := fun a => by rw [hCdef, Fin.snoc_castSucc]
  have hCl : C (Fin.last n) = e := by rw [hCdef, Fin.snoc_last]
  have hBe : ∀ a, herm (Hpk (n + 1) r) (Bs' a) e = 0 := fun a => hB'.2.2 a e (by simp)
  have heB : ∀ a, herm (Hpk (n + 1) r) e (Bs' a) = 0 := fun a => by
    rw [← Qx2.herm_star, hBe, star_zero]
  have hC : IsFrameOf (n + 1) r [z] C := by
    refine ⟨fun a => ?_, fun a b => ?_, fun a v hv => ?_⟩
    · refine Fin.lastCases ?_ (fun a => ?_) a
      · rw [hCl]; exact he
      · rw [hCc]; exact hB'.1 a
    · refine Fin.lastCases ?_ (fun a => ?_) a
      · refine Fin.lastCases ?_ (fun b => ?_) b
        · rw [hCl, hee, if_pos rfl]
        · rw [hCl, hCc, heB, if_neg (Fin.castSucc_lt_last b).ne']
      · refine Fin.lastCases ?_ (fun b => ?_) b
        · rw [hCl, hCc, hBe, if_neg (Fin.castSucc_lt_last a).ne]
        · rw [hCc, hCc, hB'.2.1]
          simp only [Fin.castSucc_inj]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      subst hv
      refine Fin.lastCases ?_ (fun a => ?_) a
      · rw [hCl]; exact hez
      · rw [hCc]; exact hB'.2.2 a v (by simp)
  set P : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun c a => herm (Hpk (n + 1) r) (Bs a) (Bs' c) with hP
  set Q : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun b d => herm (Hpk (n + 1) r) (Bs' d) (Bs b) with hQ
  have hexp : ∀ a, Bs a = ∑ c, P c a • Bs' c := by
    intro a
    have h := HermitianFormSums.complete0 hz (HermitianFormSums.hzz hT) hC (hB.1 a) (hB.2.2 a z (by simp))
    rw [Fin.sum_univ_castSucc, hCl, hB.2.2 a e (by simp), zero_smul, add_zero] at h
    simp only [hCc] at h
    exact h
  have hQP : Q * P = 1 := by
    ext b a
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h1 : herm (Hpk (n + 1) r) (Bs a) (Bs b) = herm (Hpk (n + 1) r) (∑ c, P c a • Bs' c) (Bs b) := by
      rw [← hexp a]
    rw [HermitianFormSums.herm_lsum, hB.2.1] at h1
    rw [show (if b = a then (1 : ℂ) else 0) = if a = b then 1 else 0 by simp only [eq_comm], h1]
    apply Finset.sum_congr rfl
    intro c _
    simp only [hQ, Matrix.of_apply]
    ring
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  have hunit : ∀ a b, unitB (Hpk (n + 1) r) Bs a b =
      ∑ x ∈ (Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n)),
        (P x.1 a * Q b x.2) • unitB (Hpk (n + 1) r) Bs' x.1 x.2 := by
    intro a b
    rw [Finset.sum_product]
    ext p q
    have h1 : Bs a p = ∑ c, P c a * Bs' c p := by
      have := congrFun (hexp a) p
      rw [Finset.sum_apply] at this
      exact this
    have h2 : herm (Hpk (n + 1) r) (bvec q) (Bs b) = ∑ d, Q b d * herm (Hpk (n + 1) r) (bvec q) (Bs' d) := by
      have h3 : herm (Hpk (n + 1) r) (bvec q) (Bs b) = herm (Hpk (n + 1) r) (bvec q) (∑ d, P d b • Bs' d) := by
        rw [← hexp b]
      rw [h3, HermitianFormSums.herm_rsum]
      apply Finset.sum_congr rfl
      intro d _
      simp only [hP, hQ, Matrix.of_apply, Qx2.herm_star]
    simp only [Matrix.sum_apply, Matrix.smul_apply, unitB, Matrix.of_apply, smul_eq_mul]
    rw [h1, h2, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    ring
  have hEB : EB π Bs = Econj (EB π Bs') P Q := by
    funext a b
    unfold EB Econj
    rw [hunit a b, (HermitianFormSums.ec_sum hEc hπ _ _ (fun x : Fin n × Fin n => unitB (Hpk (n + 1) r) Bs' x.1 x.2)
      (fun x => QrD.frame_lie hB1' x.1 x.2) _ (QrD.frame_lie hB1' a a)).2, Finset.sum_product]
    ext v
    simp
  rw [hEB]
  exact ((contractions_covariant (Module.End ℂ W) n (EB π Bs') P Q
    (hFG W (n + 1) r n z π Bs' hπ hB1').1 hQP hPQ w 0 0 0 0).1)

end Formalism.FourierDecayAlt.P
