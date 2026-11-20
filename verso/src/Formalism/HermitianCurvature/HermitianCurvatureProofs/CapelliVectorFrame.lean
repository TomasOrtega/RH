import Formalism.HermitianCurvature.StatementTL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SingleMulVecOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AnisotropicColumnSums

open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.TL

namespace TLC

variable {k r : ℕ}

/- English proof (translation)
Use `set P : Matrix (Fin k) (Fin k) ℂ := Matrix.of fun c a => herm (Hpk k r) (Bs a) (Bs' c) with hP`. Use `set Q : Matrix (Fin k) (Fin k) ℂ := Matrix.of fun b d => herm (Hpk k r) (Bs' d) (Bs b) with hQ`. Establish `hexp : ∀ a, Bs a = ∑ c, P c a • Bs' c`. Introduce `a`. Conclude with `HermitianFormSums.complete0 hz (HermitianFormSums.hzz hT) hB' (hB.1 a) (hB.2.2 a z (by simp))`.

Establish `hQP : Q * P = 1`. Use extensionality with `b a`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Establish `h1 : herm (Hpk k r) (Bs a) (Bs b) = herm (Hpk k r) (∑ c, P c a • Bs' c) (Bs b)`. Rewrite using `[← hexp a]`.

Rewrite `h1` using `[HermitianFormSums.herm_lsum, hB.2.1]`. Rewrite using `[show (if b = a then (1 : ℂ) else 0) = if a = b then 1 else 0 by simp only [eq_comm], h1]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `c _`. Simplify using `only [hQ, Matrix.of_apply]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hPQ : P * Q = 1` using `mul_eq_one_comm.1 hQP`. Establish `hunit : ∀ a b, unitB (Hpk k r) Bs a b = ∑ x ∈ (Finset.univ : Finset (Fin k)) ×ˢ (Finset.univ : Finset (Fin k)), (P x.1 a * Q b x.2) • unitB (Hpk k r) Bs' x.1 x.2`. Introduce `a b`. Rewrite using `[Finset.sum_product]`.

Use extensionality with `p q`. Establish `h1 : Bs a p = ∑ c, P c a * Bs' c p`. Use `congrFun (hexp a) p` as an intermediate fact. Rewrite `this` using `[Finset.sum_apply]`. Conclude with `this`.

Establish `h2 : herm (Hpk k r) (bvec q) (Bs b) = ∑ d, Q b d * herm (Hpk k r) (bvec q) (Bs' d)`. Establish `h3 : herm (Hpk k r) (bvec q) (Bs b) = herm (Hpk k r) (bvec q) (∑ d, P d b • Bs' d)`. Rewrite using `[← hexp b]`. Rewrite using `[h3, HermitianFormSums.herm_rsum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `d _`. Simplify using `only [hP, hQ, Matrix.of_apply, Qx2.herm_star]`. Simplify using `only [Matrix.sum_apply, Matrix.smul_apply, unitB, Matrix.of_apply, smul_eq_mul]`. Rewrite using `[h1, h2, Finset.sum_mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `c _`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `d _`. Expand and normalize the polynomial expressions, which then agree. Use `⟨hQP, hPQ, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `a b`. Unfold `EB Econj`. Rewrite using `[hunit a b, (HermitianFormSums.ec_sum elementary_lie_elements hπ _ _ (fun x : Fin k × Fin k => unitB (Hpk k r) Bs' x.1 x.2) (fun x => QrD.frame_lie hB' x.1 x.2) _ (QrD.frame_lie hB' a a)).2, Finset.sum_product]`. Use extensionality with `v`. Simplify using the standard rewrite rules.
-/
theorem cap_econj {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hπ : IsRepW k r z π) {Bs Bs' : Fin k → Fin (2 * r + k + 1) → ℂ} (hB : IsFrameOf k r [z] Bs)
    (hB' : IsFrameOf k r [z] Bs') :
    (Matrix.of fun b d => herm (Hpk k r) (Bs' d) (Bs b)) * (Matrix.of fun c a => herm (Hpk k r) (Bs a) (Bs' c)) = 1 ∧
    (Matrix.of fun c a => herm (Hpk k r) (Bs a) (Bs' c)) * (Matrix.of fun b d => herm (Hpk k r) (Bs' d) (Bs b)) = 1 ∧
    EB π Bs = Econj (EB π Bs') (Matrix.of fun c a => herm (Hpk k r) (Bs a) (Bs' c))
      (Matrix.of fun b d => herm (Hpk k r) (Bs' d) (Bs b)) := by
  set P : Matrix (Fin k) (Fin k) ℂ := Matrix.of fun c a => herm (Hpk k r) (Bs a) (Bs' c) with hP
  set Q : Matrix (Fin k) (Fin k) ℂ := Matrix.of fun b d => herm (Hpk k r) (Bs' d) (Bs b) with hQ
  have hexp : ∀ a, Bs a = ∑ c, P c a • Bs' c := by
    intro a
    exact HermitianFormSums.complete0 hz (HermitianFormSums.hzz hT) hB' (hB.1 a) (hB.2.2 a z (by simp))
  have hQP : Q * P = 1 := by
    ext b a
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h1 : herm (Hpk k r) (Bs a) (Bs b) = herm (Hpk k r) (∑ c, P c a • Bs' c) (Bs b) := by
      rw [← hexp a]
    rw [HermitianFormSums.herm_lsum, hB.2.1] at h1
    rw [show (if b = a then (1 : ℂ) else 0) = if a = b then 1 else 0 by simp only [eq_comm], h1]
    apply Finset.sum_congr rfl
    intro c _
    simp only [hQ, Matrix.of_apply]
    ring
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  have hunit : ∀ a b, unitB (Hpk k r) Bs a b =
      ∑ x ∈ (Finset.univ : Finset (Fin k)) ×ˢ (Finset.univ : Finset (Fin k)),
        (P x.1 a * Q b x.2) • unitB (Hpk k r) Bs' x.1 x.2 := by
    intro a b
    rw [Finset.sum_product]
    ext p q
    have h1 : Bs a p = ∑ c, P c a * Bs' c p := by
      have := congrFun (hexp a) p
      rw [Finset.sum_apply] at this
      exact this
    have h2 : herm (Hpk k r) (bvec q) (Bs b) = ∑ d, Q b d * herm (Hpk k r) (bvec q) (Bs' d) := by
      have h3 : herm (Hpk k r) (bvec q) (Bs b) = herm (Hpk k r) (bvec q) (∑ d, P d b • Bs' d) := by
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
  refine ⟨hQP, hPQ, ?_⟩
  funext a b
  unfold EB Econj
  rw [hunit a b, (HermitianFormSums.ec_sum elementary_lie_elements hπ _ _ (fun x : Fin k × Fin k => unitB (Hpk k r) Bs' x.1 x.2)
    (fun x => QrD.frame_lie hB' x.1 x.2) _ (QrD.frame_lie hB' a a)).2, Finset.sum_product]
  ext v
  simp

/- English proof (translation)
Use `⟨HermitianFormSums.inWb_sum _ _ _ hB0.1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[HermitianFormSums.herm_lsum]`. Conclude with `Finset.sum_eq_zero fun j _ => by rw [hB0.2.2 j z' (by simp), mul_zero]`. Rewrite using `[HermitianFormSums.herm_comb hB0]`. Establish `: ∀ a, ν a * star (ν a) = ((Complex.normSq (ν a) : ℝ) : ℂ)` using `fun a => Complex.mul_conj (ν a)`.

Simplify using `only [this]`. Rewrite using `[← Complex.ofReal_sum]`. Unfold `C6.sq2 at hν`. Rewrite using `[hν, Complex.ofReal_one]`.
-/
theorem cap_vec {B0 : Fin k → Fin (2 * r + k + 1) → ℂ} {z' : Fin (2 * r + k + 1) → ℂ}
    (hB0 : IsFrameOf k r [z'] B0) {ν : Fin k → ℂ} (hν : C6.sq2 ν = 1) :
    inWb k r (∑ j, ν j • B0 j) ∧ herm (Hpk k r) (∑ j, ν j • B0 j) z' = 0 ∧
      herm (Hpk k r) (∑ j, ν j • B0 j) (∑ j, ν j • B0 j) = 1 := by
  refine ⟨HermitianFormSums.inWb_sum _ _ _ hB0.1, ?_, ?_⟩
  · rw [HermitianFormSums.herm_lsum]
    exact Finset.sum_eq_zero fun j _ => by rw [hB0.2.2 j z' (by simp), mul_zero]
  · rw [HermitianFormSums.herm_comb hB0]
    have : ∀ a, ν a * star (ν a) = ((Complex.normSq (ν a) : ℝ) : ℂ) := fun a => Complex.mul_conj (ν a)
    simp only [this]
    rw [← Complex.ofReal_sum]
    unfold C6.sq2 at hν
    rw [hν, Complex.ofReal_one]

end TLC

open TLC in
/- English proof (translation)
Introduce `Wq _ _ _ k r z' π' B0 Bs ν hk hz hT hπ hB0 hν hBs w v`. Take `⟨n, rfl⟩ : ∃ n, k = n + 1` from `⟨k - 1, by omega⟩`. Take `⟨he, hez, hee⟩` from `cap_vec hB0 hν`. Use `set e := ∑ j, ν j • B0 j with hedef`. Establish `hBs1` using `HermitianFormSums.frame_sub hBs`.

Use `set C : Fin (n + 1) → Fin (2 * r + (n + 1) + 1) → ℂ := Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Bs e with hCdef`. Establish `hCc : ∀ a : Fin n, C a.castSucc = Bs a` using `fun a => by rw [hCdef, Fin.snoc_castSucc]`. Establish `hCl : C (Fin.last n) = e` using `by rw [hCdef, Fin.snoc_last]`. Establish `hBe : ∀ a, herm (Hpk (n + 1) r) (Bs a) e = 0` using `fun a => hBs.2.2 a e (by simp)`. Establish `heB : ∀ a, herm (Hpk (n + 1) r) e (Bs a) = 0` using `fun a => by`.

Rewrite using `[← Qx2.herm_star, hBe, star_zero]`. Establish `hC : IsFrameOf (n + 1) r [z'] C`. Use `⟨fun a => ?_, fun a b => ?_, fun a v hv => ?_⟩` and prove the remaining obligations. Use `Fin.lastCases ?_ (fun a => ?_) a` and prove the remaining obligations. Rewrite using `[hCl]`.

Conclude with `he`. Rewrite using `[hCc]`. Conclude with `hBs.1 a`. Use `Fin.lastCases ?_ (fun a => ?_) a` and prove the remaining obligations. Use `Fin.lastCases ?_ (fun b => ?_) b` and prove the remaining obligations.

Rewrite using `[hCl, hee, if_pos rfl]`. Rewrite using `[hCl, hCc, heB, if_neg (Fin.castSucc_lt_last b).ne']`. Use `Fin.lastCases ?_ (fun b => ?_) b` and prove the remaining obligations. Rewrite using `[hCl, hCc, hBe, if_neg (Fin.castSucc_lt_last a).ne]`. Rewrite using `[hCc, hCc, hBs.2.1]`.

Simplify using `only [Fin.castSucc_inj]`. Simplify using `only [List.mem_cons, List.not_mem_nil, or_false] at hv`. Substitute `hv` using the available equality. Use `Fin.lastCases ?_ (fun a => ?_) a` and prove the remaining obligations. Rewrite using `[hCl]`.

Conclude with `hez`. Rewrite using `[hCc]; exact hBs.2.2 a v (by simp)`. Take `⟨hQP, hPQ, hEB⟩` from `cap_econj hz hT hπ hC hB0`. Use `set P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Matrix.of fun c a => herm (Hpk (n + 1) r) (C a) (B0 c) with hP`. Use `set Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Matrix.of fun b d => herm (Hpk (n + 1) r) (B0 d) (C b) with hQ`.

Establish `hcol : (fun p => P p (Fin.last n)) = ν`. Use function extensionality and compare the values at `p`. Simplify using `only [hP, Matrix.of_apply, hCl, hedef, HermitianFormSums.herm_lsum, hB0.2.1, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Establish `hβ : ∀ j, (star ν ᵥ* P) j = if j = Fin.last n then 1 else 0`. Introduce `j`.

Establish `h1 : (star ν ᵥ* P) j = herm (Hpk (n + 1) r) (C j) e`. Rewrite using `[hedef, HermitianFormSums.herm_rsum]`. Simplify using `only [Matrix.vecMul, dotProduct, hP, Matrix.of_apply, Pi.star_apply]`. Rewrite using `[h1, ← hCl, hC.2.1, eq_comm]`. Establish `hGl` using `(frame_general_linear Wq (n + 1) r (n + 1) z' π' B0 hπ hB0).1`.

Establish `key` using `AnisotropicColumnSums.chat_gen (n + 1) n rfl (Module.End ℂ Wq) (EB π' B0) P Q (Fin.last n) (by simp) Fin.castSucc (fun a => rfl) hGl hQP hPQ w (star ν) (fun j hj => by rw [hβ j, if_neg hj])`. Rewrite `key` using `[hcol, hβ, if_pos rfl, one_smul, ← hEB, ← BorderedDeterminants.qdet_sub]`. Establish `hsub : subA (EB π' C) = EB π' Bs`. Use function extensionality and compare the values at `a b`. Simplify using `only [subA, EB, unitB, hCc]`.

Rewrite `key` using `[hsub]`. Establish `hcap` using `(frame_general_linear Wq (n + 1) r n z' π' Bs hπ hBs1).2 w v`. Rewrite using `[hcap, ← key]`. Both sides reduce to the same expression.
-/
theorem capelli_vector_frame : TL.CapVFrame := by
  intro Wq _ _ _ k r z' π' B0 Bs ν hk hz hT hπ hB0 hν hBs w v
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨he, hez, hee⟩ := cap_vec hB0 hν
  set e := ∑ j, ν j • B0 j with hedef
  have hBs1 := HermitianFormSums.frame_sub hBs
  set C : Fin (n + 1) → Fin (2 * r + (n + 1) + 1) → ℂ :=
    Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Bs e with hCdef
  have hCc : ∀ a : Fin n, C a.castSucc = Bs a := fun a => by rw [hCdef, Fin.snoc_castSucc]
  have hCl : C (Fin.last n) = e := by rw [hCdef, Fin.snoc_last]
  have hBe : ∀ a, herm (Hpk (n + 1) r) (Bs a) e = 0 := fun a => hBs.2.2 a e (by simp)
  have heB : ∀ a, herm (Hpk (n + 1) r) e (Bs a) = 0 := fun a => by
    rw [← Qx2.herm_star, hBe, star_zero]
  have hC : IsFrameOf (n + 1) r [z'] C := by
    refine ⟨fun a => ?_, fun a b => ?_, fun a v hv => ?_⟩
    · refine Fin.lastCases ?_ (fun a => ?_) a
      · rw [hCl]; exact he
      · rw [hCc]; exact hBs.1 a
    · refine Fin.lastCases ?_ (fun a => ?_) a
      · refine Fin.lastCases ?_ (fun b => ?_) b
        · rw [hCl, hee, if_pos rfl]
        · rw [hCl, hCc, heB, if_neg (Fin.castSucc_lt_last b).ne']
      · refine Fin.lastCases ?_ (fun b => ?_) b
        · rw [hCl, hCc, hBe, if_neg (Fin.castSucc_lt_last a).ne]
        · rw [hCc, hCc, hBs.2.1]
          simp only [Fin.castSucc_inj]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      subst hv
      refine Fin.lastCases ?_ (fun a => ?_) a
      · rw [hCl]; exact hez
      · rw [hCc]; exact hBs.2.2 a v (by simp)
  obtain ⟨hQP, hPQ, hEB⟩ := cap_econj hz hT hπ hC hB0
  set P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Matrix.of fun c a => herm (Hpk (n + 1) r) (C a) (B0 c) with hP
  set Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Matrix.of fun b d => herm (Hpk (n + 1) r) (B0 d) (C b) with hQ
  have hcol : (fun p => P p (Fin.last n)) = ν := by
    funext p
    simp only [hP, Matrix.of_apply, hCl, hedef, HermitianFormSums.herm_lsum, hB0.2.1, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hβ : ∀ j, (star ν ᵥ* P) j = if j = Fin.last n then 1 else 0 := by
    intro j
    have h1 : (star ν ᵥ* P) j = herm (Hpk (n + 1) r) (C j) e := by
      rw [hedef, HermitianFormSums.herm_rsum]
      simp only [Matrix.vecMul, dotProduct, hP, Matrix.of_apply, Pi.star_apply]
    rw [h1, ← hCl, hC.2.1, eq_comm]
  have hGl := (frame_general_linear Wq (n + 1) r (n + 1) z' π' B0 hπ hB0).1
  have key := AnisotropicColumnSums.chat_gen (n + 1) n rfl (Module.End ℂ Wq) (EB π' B0) P Q (Fin.last n) (by simp) Fin.castSucc
    (fun a => rfl) hGl hQP hPQ w (star ν) (fun j hj => by rw [hβ j, if_neg hj])
  rw [hcol, hβ, if_pos rfl, one_smul, ← hEB, ← BorderedDeterminants.qdet_sub] at key
  have hsub : subA (EB π' C) = EB π' Bs := by
    funext a b
    simp only [subA, EB, unitB, hCc]
  rw [hsub] at key
  have hcap := (frame_general_linear Wq (n + 1) r n z' π' Bs hπ hBs1).2 w v
  rw [hcap, ← key]
  rfl

end Formalism.FourierDecayAlt.P
