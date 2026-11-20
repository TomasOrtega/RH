import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXIntWittAlg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TopoGram

noncomputable section

namespace Formalism.L2.SG.Pf.NcX.IntWittAlg

open Matrix Formalism.UG

/- English proof (translation)
Introduce `S _ s O hs hsO n J J' hJ hJJ hJO hJ'O a β β' hβ hβ' hββ hch x y hx hy hxx hyy`. Establish `hconj` using `hform_conj s J hs hJ`. Establish `mkGL : ∀ M : Matrix (Fin n) (Fin n) S, cT s M * J * M = J → (∀ i j, M i j ∈ O) → ∃ g : GL (Fin n) S, (g : Matrix (Fin n) (Fin n) S) = M ∧ g ∈ UJ s J ∧ ∀ i j, ((g⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) i j ∈ O`. Introduce `M hM hMO`. Establish `hL : (J' * cT s M * J) * M = 1`.

Combine the equalities or inequalities in the displayed calculation. Establish `hR : M * (J' * cT s M * J) = 1` using `mul_eq_one_comm.mp hL`. Use `⟨⟨M, J' * cT s M * J, hR, hL⟩, rfl, hM, ?_⟩` and prove the remaining obligations. Introduce `i j`. Use `show (J' * cT s M * J) i j ∈ O`.

Conclude with `mul_mem' O _ _ (mul_mem' O _ _ hJ'O (cT_mem O s hsO M hMO)) hJO i j`. Establish `hsβ : ∀ i, s (β i) = β i`. Introduce `i`. Use `hconj (y i) (y i)` as an intermediate fact. Rewrite `this` using `[hyy i i, if_pos rfl]`.

Conclude with `this`. Establish `hsβ' : ∀ i, s (β' i) = β' i`. Introduce `i`. Combine the equalities or inequalities in the displayed calculation. Establish `main : ∀ m ≤ a, ∃ g : GL (Fin n) S, g ∈ UJ s J ∧ (∀ i j, (g : Matrix (Fin n) (Fin n) S) i j ∈ O) ∧ (∀ i j, ((g⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) i j ∈ O) ∧ ∀ i : Fin a, i.val < m → (g : Matrix (Fin n) (Fin n) S) *ᵥ y i = x i`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `_`. Use `⟨1, (UJ s J).one_mem, ?_, ?_, fun i h => absurd h (Nat.not_lt_zero _)⟩` and prove the remaining obligations.

Introduce `i j`. Rewrite using `[Units.val_one]`. Conclude with `one_mem' O i j`. Introduce `i j`. Rewrite using `[inv_one, Units.val_one]`.

Conclude with `one_mem' O i j`. Consider the case `succ m ih`. Introduce `hm`. Take `⟨g, hg, hgO, hgiO, hgy⟩` from `ih (by omega)`. Set `i0 : Fin a` to `⟨m, by omega⟩`.

Use `set G := (g : Matrix (Fin n) (Fin n) S) with hG`. Use `set Gi := ((g⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) with hGi`. Establish `hGiG : Gi * G = 1` using `by rw [hG, hGi, ← Units.val_mul, inv_mul_cancel, Units.val_one]`. Establish `hGGi : G * Gi = 1` using `by rw [hG, hGi, ← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `hgi : g⁻¹ ∈ UJ s J` using `(UJ s J).inv_mem hg`.

Establish `hGiU : ∀ z w, hform s J (Gi *ᵥ z) (Gi *ᵥ w) = hform s J z w`. Introduce `z w`. Rewrite using `[PI.VolStabW.TopoGram.hform_mulVec]`. Conclude with `congrArg (fun K => hform s K z w) hgi`. Establish `hyGi : ∀ i : Fin a, i.val < m → Gi *ᵥ x i = y i`.

Introduce `i hi`. Rewrite using `[← hgy i hi, mulVec_mulVec, hGiG, one_mulVec]`. Use `set xp := Gi *ᵥ x i0 with hxpdef`. Establish `hxpO : ∀ k, xp k ∈ O` using `mulVec_mem O _ hgiO _ (hx i0)`. Establish `hxpy : ∀ i : Fin a, i.val < m → hform s J xp (y i) = 0`.

Introduce `i hi`. Rewrite using `[hxpdef, ← hyGi i hi, hGiU, hxx, if_neg]`. Introduce `h`. Rewrite `hi` using `[← h]`. Conclude with `lt_irrefl _ hi`.

Establish `hxpxp : hform s J xp xp = hform s J (y i0) (y i0)`. Rewrite using `[hxpdef, hGiU, hxx, hyy, if_pos rfl]`. Establish `htO : hform s J xp (y i0) ∈ O` using `hform_mem O s hsO J hJO _ _ hxpO (hy i0)`. Take `⟨lam, hlamO, hlam, ci, hciO, hci⟩` from `hch i0 _ htO`. Establish `hβ0 : β i0 = hform s J (y i0) (y i0)` using `by rw [hyy, if_pos rfl]`.

Use `set c := hform s J (y i0) (y i0) - s lam * hform s J xp (y i0) with hcdef`. Establish `e2 : ci * c = 1` using `by rw [mul_comm, hcdef, ← hβ0]; exact hci`. Use `set u := y i0 - lam • xp with hudef`. Establish `huO : ∀ k, u k ∈ O`. Introduce `k`.

Simplify using `only [hudef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Conclude with `O.sub_mem (hy i0 k) (O.mul_mem hlamO (hxpO k))`. Establish `hux : hform s J u (y i0) = c`. Rewrite using `[hudef, hform_sub_left, hform_smul_left]`. Establish `huu : hform s J u u = c + s c`.

Rewrite using `[hudef, hcdef]`. Simplify using `only [hform_sub_left, hform_sub_right, hform_smul_left, hform_smul_right, map_sub, map_mul, hs, hconj]`. Take the linear combination `(s lam * lam) * hxpxp + hform s J (y i0) (y i0) * hlam`. Establish `huy : ∀ i : Fin a, i.val < m → hform s J u (y i) = 0`. Introduce `i hi`.

Rewrite using `[hudef, hform_sub_left, hform_smul_left, hxpy i hi, hyy, if_neg, mul_zero, sub_zero]`. Introduce `h`. Rewrite `hi` using `[← h]`. Conclude with `lt_irrefl _ hi`. Use `set T := rT s J u ci lam with hTdef`.

Establish `hTy0 : T *ᵥ y i0 = xp`. Rewrite using `[hTdef, rT_mulVec, hux, e2, one_smul, hudef, sub_sub_cancel, smul_smul, mul_comm, hlam, one_smul]`. Establish `hTy : ∀ i : Fin a, i.val < m → T *ᵥ y i = s lam • y i`. Introduce `i hi`. Rewrite using `[hTdef, rT_mulVec, huy i hi, mul_zero, zero_smul, sub_zero]`.

Establish `hTU` using `rT_preserves s J hs hJ u c ci lam hlam huu e2`. Set `t : Finset (Fin a)` to `Finset.univ.filter (fun i => i.val < m)`. Establish `hmt : ∀ i, i ∈ t ↔ i.val < m` using `fun i => by simp [t]`. Use `set Pm := pM s J t y β' with hPm`. Use `set Dm := (1 : Matrix (Fin n) (Fin n) S) + (lam - 1) • Pm with hDm`.

Establish `hPy : ∀ i : Fin a, i.val < m → Pm *ᵥ y i = y i`. Introduce `i hi`. Rewrite using `[hPm, pM_mulVec, Finset.sum_eq_single i]`. Rewrite using `[hyy, if_pos rfl, mul_comm, hββ, one_smul]`. Introduce `j _ hji`.

Rewrite using `[hyy, if_neg hji, mul_zero, zero_smul]`. Introduce `h`. Conclude with `absurd ((hmt i).2 hi) h`. Establish `hPy0 : Pm *ᵥ y i0 = 0`. Rewrite using `[hPm, pM_mulVec]`.

Use `Finset.sum_eq_zero fun j hj => ?_` and prove the remaining obligations. Rewrite using `[hyy, if_neg, mul_zero, zero_smul]`. Introduce `h`. Use `(hmt j).1 hj` as an intermediate fact. Rewrite `this` using `[h]`.

Conclude with `lt_irrefl _ this`. Establish `hDy : ∀ i : Fin a, i.val < m → Dm *ᵥ y i = lam • y i`. Introduce `i hi`. Rewrite using `[hDm, add_mulVec, one_mulVec, smul_mulVec, hPy i hi, sub_smul, one_smul]`. Normalize the expressions using the abelian group laws.

Establish `hDy0 : Dm *ᵥ y i0 = y i0`. Rewrite using `[hDm, add_mulVec, one_mulVec, smul_mulVec, hPy0, smul_zero, add_zero]`. Establish `hDU : ∀ z w, hform s J (Dm *ᵥ z) (Dm *ᵥ w) = hform s J z w`. Introduce `z w`. Use `set p := ∑ j ∈ t, β' j * hform s J (y j) w * hform s J z (y j) with hp`.

Establish `h1 : hform s J z (Pm *ᵥ w) = p`. Rewrite using `[hPm, pM_mulVec, hform_sum_right]`. Establish `h2 : hform s J (Pm *ᵥ z) w = p`. Rewrite using `[hPm, pM_mulVec, hform_sum_left, hp]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, hsβ', hconj]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : hform s J (Pm *ᵥ z) (Pm *ᵥ w) = p`. Rewrite using `[hPm, pM_mulVec, hform_sum_left, hp]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations.

Rewrite using `[← hPm, pM_mulVec, hform_sum_right, Finset.sum_eq_single j]`. Rewrite using `[hyy, if_pos rfl, map_mul, hsβ', hconj]`. Take the linear combination `(β' j * hform s J (y j) w * hform s J z (y j)) * hββ j`. Introduce `l _ hlj`. Rewrite using `[hyy, if_neg (Ne.symm hlj), mul_zero]`.

Introduce `h`. Conclude with `absurd hj h`. Rewrite using `[hDm, add_mulVec, add_mulVec, one_mulVec, one_mulVec, smul_mulVec, smul_mulVec, hform_add_left, hform_add_right, hform_add_right, hform_smul_left, hform_smul_left, hform_smul_right, hform_smul_right, h1, h2, h3, map_sub, map_one]`. Take the linear combination `p * hlam`. Use `set M := T * Dm with hM`.

Establish `hMU : cT s M * J * M = J`. Use `unitary_of s J M fun z w => ?_` and prove the remaining obligations. Rewrite using `[hM, ← mulVec_mulVec, ← mulVec_mulVec, hTU, hDU]`. Establish `hMO : ∀ i j, M i j ∈ O`. Introduce `i j`.

Use `mul_mem' O _ _ (rT_mem O s hsO J hJO u huO ci lam hciO hlamO) ?_ i j` and prove the remaining obligations. Introduce `i j`. Simplify using `only [hDm, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`. Conclude with `O.add_mem (one_mem' O i j) (O.mul_mem (O.sub_mem hlamO O.one_mem) (pM_mem O s hsO J hJO t y hy β' hβ' i j))`. Take `⟨g', hg'M, hg'U, hg'iO⟩` from `mkGL M hMU hMO`.

Use `⟨g * g', (UJ s J).mul_mem hg hg'U, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j`. Rewrite using `[Units.val_mul, hg'M]`. Conclude with `mul_mem' O _ _ hgO hMO i j`. Introduce `i j`.

Rewrite using `[_root_.mul_inv_rev, Units.val_mul]`. Conclude with `mul_mem' O _ _ hg'iO hgiO i j`. Introduce `i hi`. Rewrite using `[Units.val_mul, hg'M, ← mulVec_mulVec, hM, ← mulVec_mulVec]`. Break down `Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi` into its components or cases.

Rewrite using `[hDy i hi, mulVec_smul, hTy i hi, smul_smul, hlam, one_smul]`. Conclude with `hgy i hi`. Establish `: i = i0` using `Fin.ext hi`. Rewrite using `[this, hDy0, hTy0, hxpdef, mulVec_mulVec, ← hG, hGGi, one_mulVec]`. Take `⟨g, hg, hgO, hgiO, hgy⟩` from `main a le_rfl`.

Conclude with `⟨g, hg, hgO, hgiO, fun i => hgy i i.2⟩`.
-/
theorem algWitt : Formalism.L2.SG.Pf.NcX.IntWittPf.AlgWitt := by
  intro S _ s O hs hsO n J J' hJ hJJ hJO hJ'O a β β' hβ hβ' hββ hch x y hx hy hxx hyy
  have hconj := hform_conj s J hs hJ

  have mkGL : ∀ M : Matrix (Fin n) (Fin n) S, cT s M * J * M = J → (∀ i j, M i j ∈ O) →
      ∃ g : GL (Fin n) S, (g : Matrix (Fin n) (Fin n) S) = M ∧ g ∈ UJ s J ∧
        ∀ i j, ((g⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) i j ∈ O := by
    intro M hM hMO
    have hL : (J' * cT s M * J) * M = 1 := by
      calc (J' * cT s M * J) * M = J' * (cT s M * J * M) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hM, hJJ]
    have hR : M * (J' * cT s M * J) = 1 := mul_eq_one_comm.mp hL
    refine ⟨⟨M, J' * cT s M * J, hR, hL⟩, rfl, hM, ?_⟩
    intro i j
    show (J' * cT s M * J) i j ∈ O
    exact mul_mem' O _ _ (mul_mem' O _ _ hJ'O (cT_mem O s hsO M hMO)) hJO i j
  have hsβ : ∀ i, s (β i) = β i := by
    intro i
    have := hconj (y i) (y i)
    rw [hyy i i, if_pos rfl] at this
    exact this
  have hsβ' : ∀ i, s (β' i) = β' i := by
    intro i
    calc s (β' i) = s (β' i) * (β i * β' i) := by rw [hββ, mul_one]
      _ = s (β i * β' i) * β' i := by rw [map_mul, hsβ]; ring
      _ = β' i := by rw [hββ, map_one, one_mul]
  have main : ∀ m ≤ a, ∃ g : GL (Fin n) S, g ∈ UJ s J ∧ (∀ i j, (g : Matrix (Fin n) (Fin n) S) i j ∈ O) ∧
      (∀ i j, ((g⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) i j ∈ O) ∧
      ∀ i : Fin a, i.val < m → (g : Matrix (Fin n) (Fin n) S) *ᵥ y i = x i := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨1, (UJ s J).one_mem, ?_, ?_, fun i h => absurd h (Nat.not_lt_zero _)⟩
      · intro i j; rw [Units.val_one]; exact one_mem' O i j
      · intro i j; rw [inv_one, Units.val_one]; exact one_mem' O i j
    | succ m ih =>
      intro hm
      obtain ⟨g, hg, hgO, hgiO, hgy⟩ := ih (by omega)
      let i0 : Fin a := ⟨m, by omega⟩
      set G := (g : Matrix (Fin n) (Fin n) S) with hG
      set Gi := ((g⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) with hGi
      have hGiG : Gi * G = 1 := by rw [hG, hGi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      have hGGi : G * Gi = 1 := by rw [hG, hGi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      have hgi : g⁻¹ ∈ UJ s J := (UJ s J).inv_mem hg
      have hGiU : ∀ z w, hform s J (Gi *ᵥ z) (Gi *ᵥ w) = hform s J z w := by
        intro z w
        rw [PI.VolStabW.TopoGram.hform_mulVec]
        exact congrArg (fun K => hform s K z w) hgi
      have hyGi : ∀ i : Fin a, i.val < m → Gi *ᵥ x i = y i := by
        intro i hi
        rw [← hgy i hi, mulVec_mulVec, hGiG, one_mulVec]
      set xp := Gi *ᵥ x i0 with hxpdef
      have hxpO : ∀ k, xp k ∈ O := mulVec_mem O _ hgiO _ (hx i0)
      have hxpy : ∀ i : Fin a, i.val < m → hform s J xp (y i) = 0 := by
        intro i hi
        rw [hxpdef, ← hyGi i hi, hGiU, hxx, if_neg]
        intro h; rw [← h] at hi; exact lt_irrefl _ hi
      have hxpxp : hform s J xp xp = hform s J (y i0) (y i0) := by
        rw [hxpdef, hGiU, hxx, hyy, if_pos rfl]
      have htO : hform s J xp (y i0) ∈ O := hform_mem O s hsO J hJO _ _ hxpO (hy i0)
      obtain ⟨lam, hlamO, hlam, ci, hciO, hci⟩ := hch i0 _ htO
      have hβ0 : β i0 = hform s J (y i0) (y i0) := by rw [hyy, if_pos rfl]
      set c := hform s J (y i0) (y i0) - s lam * hform s J xp (y i0) with hcdef
      have e2 : ci * c = 1 := by rw [mul_comm, hcdef, ← hβ0]; exact hci
      set u := y i0 - lam • xp with hudef
      have huO : ∀ k, u k ∈ O := by
        intro k
        simp only [hudef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        exact O.sub_mem (hy i0 k) (O.mul_mem hlamO (hxpO k))
      have hux : hform s J u (y i0) = c := by
        rw [hudef, hform_sub_left, hform_smul_left]
      have huu : hform s J u u = c + s c := by
        rw [hudef, hcdef]
        simp only [hform_sub_left, hform_sub_right, hform_smul_left, hform_smul_right, map_sub, map_mul, hs,
          hconj]
        linear_combination (s lam * lam) * hxpxp + hform s J (y i0) (y i0) * hlam
      have huy : ∀ i : Fin a, i.val < m → hform s J u (y i) = 0 := by
        intro i hi
        rw [hudef, hform_sub_left, hform_smul_left, hxpy i hi, hyy, if_neg, mul_zero, sub_zero]
        intro h; rw [← h] at hi; exact lt_irrefl _ hi

      set T := rT s J u ci lam with hTdef
      have hTy0 : T *ᵥ y i0 = xp := by
        rw [hTdef, rT_mulVec, hux, e2, one_smul, hudef, sub_sub_cancel, smul_smul, mul_comm, hlam, one_smul]
      have hTy : ∀ i : Fin a, i.val < m → T *ᵥ y i = s lam • y i := by
        intro i hi
        rw [hTdef, rT_mulVec, huy i hi, mul_zero, zero_smul, sub_zero]
      have hTU := rT_preserves s J hs hJ u c ci lam hlam huu e2

      let t : Finset (Fin a) := Finset.univ.filter (fun i => i.val < m)
      have hmt : ∀ i, i ∈ t ↔ i.val < m := fun i => by simp [t]
      set Pm := pM s J t y β' with hPm
      set Dm := (1 : Matrix (Fin n) (Fin n) S) + (lam - 1) • Pm with hDm
      have hPy : ∀ i : Fin a, i.val < m → Pm *ᵥ y i = y i := by
        intro i hi
        rw [hPm, pM_mulVec, Finset.sum_eq_single i]
        · rw [hyy, if_pos rfl, mul_comm, hββ, one_smul]
        · intro j _ hji
          rw [hyy, if_neg hji, mul_zero, zero_smul]
        · intro h; exact absurd ((hmt i).2 hi) h
      have hPy0 : Pm *ᵥ y i0 = 0 := by
        rw [hPm, pM_mulVec]
        refine Finset.sum_eq_zero fun j hj => ?_
        rw [hyy, if_neg, mul_zero, zero_smul]
        intro h; have := (hmt j).1 hj; rw [h] at this; exact lt_irrefl _ this
      have hDy : ∀ i : Fin a, i.val < m → Dm *ᵥ y i = lam • y i := by
        intro i hi
        rw [hDm, add_mulVec, one_mulVec, smul_mulVec, hPy i hi, sub_smul, one_smul]
        abel
      have hDy0 : Dm *ᵥ y i0 = y i0 := by
        rw [hDm, add_mulVec, one_mulVec, smul_mulVec, hPy0, smul_zero, add_zero]
      have hDU : ∀ z w, hform s J (Dm *ᵥ z) (Dm *ᵥ w) = hform s J z w := by
        intro z w
        set p := ∑ j ∈ t, β' j * hform s J (y j) w * hform s J z (y j) with hp
        have h1 : hform s J z (Pm *ᵥ w) = p := by
          rw [hPm, pM_mulVec, hform_sum_right]
        have h2 : hform s J (Pm *ᵥ z) w = p := by
          rw [hPm, pM_mulVec, hform_sum_left, hp]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_mul, hsβ', hconj]
          ring
        have h3 : hform s J (Pm *ᵥ z) (Pm *ᵥ w) = p := by
          rw [hPm, pM_mulVec, hform_sum_left, hp]
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [← hPm, pM_mulVec, hform_sum_right, Finset.sum_eq_single j]
          · rw [hyy, if_pos rfl, map_mul, hsβ', hconj]
            linear_combination (β' j * hform s J (y j) w * hform s J z (y j)) * hββ j
          · intro l _ hlj
            rw [hyy, if_neg (Ne.symm hlj), mul_zero]
          · intro h; exact absurd hj h
        rw [hDm, add_mulVec, add_mulVec, one_mulVec, one_mulVec, smul_mulVec, smul_mulVec, hform_add_left,
          hform_add_right, hform_add_right, hform_smul_left, hform_smul_left, hform_smul_right, hform_smul_right,
          h1, h2, h3, map_sub, map_one]
        linear_combination p * hlam

      set M := T * Dm with hM
      have hMU : cT s M * J * M = J := by
        refine unitary_of s J M fun z w => ?_
        rw [hM, ← mulVec_mulVec, ← mulVec_mulVec, hTU, hDU]
      have hMO : ∀ i j, M i j ∈ O := by
        intro i j
        refine mul_mem' O _ _ (rT_mem O s hsO J hJO u huO ci lam hciO hlamO) ?_ i j
        intro i j
        simp only [hDm, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        exact O.add_mem (one_mem' O i j) (O.mul_mem (O.sub_mem hlamO O.one_mem)
          (pM_mem O s hsO J hJO t y hy β' hβ' i j))
      obtain ⟨g', hg'M, hg'U, hg'iO⟩ := mkGL M hMU hMO
      refine ⟨g * g', (UJ s J).mul_mem hg hg'U, ?_, ?_, ?_⟩
      · intro i j
        rw [Units.val_mul, hg'M]
        exact mul_mem' O _ _ hgO hMO i j
      · intro i j
        rw [_root_.mul_inv_rev, Units.val_mul]
        exact mul_mem' O _ _ hg'iO hgiO i j
      · intro i hi
        rw [Units.val_mul, hg'M, ← mulVec_mulVec, hM, ← mulVec_mulVec]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
        · rw [hDy i hi, mulVec_smul, hTy i hi, smul_smul, hlam, one_smul]
          exact hgy i hi
        · have : i = i0 := Fin.ext hi
          rw [this, hDy0, hTy0, hxpdef, mulVec_mulVec, ← hG, hGGi, one_mulVec]
  obtain ⟨g, hg, hgO, hgiO, hgy⟩ := main a le_rfl
  exact ⟨g, hg, hgO, hgiO, fun i => hgy i i.2⟩

end Formalism.L2.SG.Pf.NcX.IntWittAlg
