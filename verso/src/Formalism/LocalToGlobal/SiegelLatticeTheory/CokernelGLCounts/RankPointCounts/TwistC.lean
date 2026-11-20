import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NatMulMem

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh

namespace Formalism.L2.SG.Pf.StabIntLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Introduce `δ M hA hodd w y`. Establish `hm : 2 * mOdd D = gS D + 1` using `by unfold mOdd; obtain ⟨k, hk⟩ := hodd; omega`. Establish `hm' : (1 : D.host.E) - 2 * (mOdd D : D.host.E) = -((gS D : ℕ) : D.host.E)`. Establish `: ((2 * mOdd D : ℕ) : D.host.E) = ((gS D + 1 : ℕ) : D.host.E)` using `by rw [hm]`. Move the coercions through the operations in `at this`.

Take the linear combination `-this`. Establish `hEq` using `E_q w y`. Establish `hτs : ∀ q, selfP w q → τA w q y = (mOdd D : D.host.E) * cf w y q` using `fun q h => by simp [τA, h]`. Establish `hτu : ∀ q, ¬ selfP w q → upperM w q → τA w q y = sgq w (qbar w q) * D.conjF (-(y (qbar w q)) + cf w y (qbar w q))` using `fun q h1 h2 => by`. Simplify using `[τA, h1, h2]`.

Establish `hτl : ∀ q, ¬ selfP w q → ¬ upperM w q → τA w q y = 0` using `fun q h1 h2 => by simp [τA, h1, h2]`. Establish `hΛs : ∀ q, selfP w q → ∀ z, z ∈ Λq w q ↔ z ∈ ddPow D (hgt w q) ∧ z + sgq w q * D.conjF z ∈ qdPow D (hgt w q)` using `fun q h z => by`. Simplify using `only [Λq, h, if_true]`. Both sides reduce to the same expression. Establish `hΛu : ∀ q, ¬ selfP w q → upperM w q → ∀ z, z ∈ Λq w q ↔ z ∈ qdPow D (hgt w q)` using `fun q h1 h2 z => by`.

Simplify using `only [Λq, Iq, h1, h2, if_false, not_true_eq_false, or_self]`. Both sides reduce to the same expression. Establish `hΛl : ∀ q, ¬ selfP w q → ¬ upperM w q → ∀ z, z ∈ Λq w q ↔ z ∈ ddPow D (hgt w q)` using `fun q h1 h2 z => by`. Simplify using `only [Λq, Iq, h1, h2, if_false, not_false_eq_true, or_true, if_true]`. Both sides reduce to the same expression.

Establish `hup : ∀ q, ¬ selfP w q → upperM w q → y q - τA w q y = (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2`. Introduce `q h1 h2`. Rewrite using `[hτu q h1 h2, hEq, sgq_qbar, neg_add_eq_sub]`. Establish `hsq : ∀ q, ¬ selfP w q → ¬ selfP w (qbar w q)` using `fun q h1 h => h1 (by`. Unfold `selfP at h ⊢`.

Rewrite `h` using `[qbar_qbar]`. Conclude with `h.symm)`. Establish `hgc : ∀ q, (1 - 2 * (mOdd D : D.host.E)) * cf w y q ∈ qdPow D (hgt w q) ∨ ¬ (cf w y q ∈ ddPow D (hgt w q))` using `fun q => by`. Distinguish the cases in `hc : cf w y q ∈ ddPow D (hgt w q)`. Use `left`.

Rewrite using `[hm', neg_mul]`. Conclude with `(qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).neg_mem (gS_mul_qd _ hc)`. Use `right`. Conclude with `hc`. Rewrite using `[condX_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hy, hE⟩ q`. Distinguish the cases in `h1 : selfP w q`. Rewrite using `[hτs q h1, hΛs q h1]`. Establish `hc` using `cf_mem w y q (fun p _ => hy p)`.

Use `⟨(ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).sub_mem (hy q) (nat_mul_mem _ (mOdd D) hc), ?_⟩` and prove the remaining obligations. Establish `hqq : qbar w q = q` using `h1`. Establish `hEq'` using `hEq q`. Rewrite `hEq'` using `[hqq]`. Rewrite using `[self_id (sgq w q) (y q) (cf w y q) _ (mOdd D) (sgq_sq w q) (sgq_conj w q) hEq']`.

Establish `e1` using `hE q`. Establish `e2 : sgq w q * D.conjF ((Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2) - (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2 ∈ qdPow D (hgt w q)` using `(qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).sub_mem (sg_qd w δ M hA (hgt_le w q) q e1) e1`. Establish `e3 : (1 - 2 * (mOdd D : D.host.E)) * cf w y q ∈ qdPow D (hgt w q)`. Break down `hgc q with h | h` into its components or cases. Conclude with `h`.

Conclude with `absurd hc h`. Conclude with `(qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).add_mem ((qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).sub_mem ((qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).add_mem e1 e2) (nat_mul_mem _ (mOdd D) e2)) e3`. Distinguish the cases in `h2 : upperM w q`. Rewrite using `[hΛu q h1 h2, hup q h1 h2]`. Conclude with `hE q`.

Rewrite using `[hτl q h1 h2, sub_zero, hΛl q h1 h2]`. Conclude with `hy q`. Introduce `ht`. Establish `hy : ∀ q, y q ∈ ddPow D (hgt w q)`. Establish `key : ∀ n, ∀ q, hgt w q = n → y q ∈ ddPow D (hgt w q)`.

Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `q hq`. Establish `hlow : ∀ p, hgt w p < hgt w q → y p ∈ ddPow D (hgt w p)` using `fun p hp => ih _ (hq ▸ hp) p rfl`.

Distinguish the cases in `h1 : selfP w q`. Establish `h3` using `(hΛs q h1 _).1 (ht q)`. Rewrite `h3` using `[hτs q h1]`. Establish `hc` using `cf_mem w y q hlow`. Use `(ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).add_mem h3.1 (nat_mul_mem _ (mOdd D) hc)` as an intermediate fact.

Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Distinguish the cases in `h2 : upperM w q`. Establish `h3` using `(hΛu q h1 h2 _).1 (ht q)`. Rewrite `h3` using `[hτu q h1 h2]`. Take `⟨hp1, hp2⟩` from `upper_qbar w h2`.

Establish `hyp : y (qbar w q) ∈ ddPow D (hgt w (qbar w q))`. Use `(hΛl _ hp1 hp2 _).1 (ht (qbar w q))` as an intermediate fact. Rewrite `this` using `[hτl _ hp1 hp2, sub_zero]`. Then use the resulting hypothesis. Rewrite `hyp` using `[hgt_qbar]`. Establish `hcp` using `cf_mem w y (qbar w q) (fun p hp => hlow p (by rwa [hgt_qbar] at hp))`.

Rewrite `hcp` using `[hgt_qbar]`. Establish `hτ` using `sg_dd w δ M hA (hgt_le w q) (qbar w q) ((ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).add_mem ((ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).neg_mem hyp) hcp)`. Use `(ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).add_mem (qd_le_dd _ h3) hτ` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Use `(hΛl q h1 h2 _).1 (ht q)` as an intermediate fact.

Rewrite `this` using `[hτl q h1 h2, sub_zero]`. Then use the resulting hypothesis. Conclude with `fun q => key _ q rfl`. Establish `hG` using `Xmat_grD w y hy`. Use `⟨hy, ?_⟩` and prove the remaining obligations. Establish `hB2 : IsBlockDiagonalMatrix w (Xmat w y - Psi w (Xmat w y)⁻¹)` using `fun a c h => by`.

Rewrite using `[Matrix.sub_apply, Xmat_blk w y a c h, Psi_blk w (blk_inv w (Xmat_upU w y) (Xmat_blk w y)) a c h, sub_self]`. Establish `key2 : ∀ n, ∀ q, hgt w q = n → (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2 ∈ qdPow D (hgt w q)`. Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`.

Introduce `q hq`. Establish `hU` using `unitCons w δ M hA (Xmat_upU w y) (Xmat_blk w y) hG q.2.1 (fun i j hij hh => by`. Distinguish the cases in `hb : blkOf w.1 i.val = blkOf w.1 j.val`. Conclude with `ih _ (by rw [← hq]; exact hh) ⟨(i, j), hij, hb⟩ rfl`. Rewrite using `[hB2 i j hb]`.

Conclude with `FractionalIdeal.zero_mem _)`. Establish `hPsiq : Psi w (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2 = sgq w q * D.conjF ((Xmat w y - Psi w (Xmat w y)⁻¹) (qbar w q).1.1 (qbar w q).1.2)` using `rfl`. Rewrite `hU` using `[hPsiq]`. Distinguish the cases in `h1 : selfP w q`. Establish `hqq : qbar w q = q` using `h1`.

Rewrite `hU` using `[hqq]`. Establish `hT` using `((hΛs q h1 _).1 (ht q)).2`. Rewrite `hT` using `[hτs q h1]`. Establish `hEq'` using `hEq q`. Rewrite `hEq'` using `[hqq]`.

Rewrite `hT` using `[self_id (sgq w q) (y q) (cf w y q) _ (mOdd D) (sgq_sq w q) (sgq_conj w q) hEq']`. Establish `hc` using `cf_mem w y q (fun p _ => hy p)`. Establish `e3 : (1 - 2 * (mOdd D : D.host.E)) * cf w y q ∈ qdPow D (hgt w q)`. Break down `hgc q with h | h` into its components or cases. Conclude with `h`.

Conclude with `absurd hc h`. Use `set Ee := (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2 with hEe`. Establish `h5` using `(qdPow D (hgt w q) : Submodule (𝓞 D.host.E) D.host.E).sub_mem ((qdPow D (hgt w q) : Submodule (𝓞 D.host.E) D.host.E).add_mem ((qdPow D (hgt w q) : Submodule (𝓞 D.host.E) D.host.E).sub_mem hT e3) (nat_mul_mem _ (mOdd D) hU)) hU`. Establish `eq : Ee + (sgq w q * D.conjF Ee - Ee) - (mOdd D : D.host.E) * (sgq w q * D.conjF Ee - Ee) + (1 - 2 * (mOdd D : D.host.E)) * cf w y q - (1 - 2 * (mOdd D : D.host.E)) * cf w y q + (mOdd D : D.host.E) * (sgq w q * D.conjF Ee - Ee) - (sgq w q * D.conjF Ee - Ee) = Ee` using `by ring`. Rewrite `h5` using `[eq]`.

Conclude with `h5`. Distinguish the cases in `h2 : upperM w q`. Rewrite using `[← hup q h1 h2]`. Conclude with `(hΛu q h1 h2 _).1 (ht q)`. Establish `hpu` using `lower_qbar w h1 h2`.

Establish `hps` using `hsq q h1`. Establish `hEp : (Xmat w y - Psi w (Xmat w y)⁻¹) (qbar w q).1.1 (qbar w q).1.2 ∈ qdPow D (hgt w (qbar w q))`. Rewrite using `[← hup _ hps hpu]`. Conclude with `(hΛu _ hps hpu _).1 (ht _)`. Rewrite `hEp` using `[hgt_qbar]`.

Establish `hs` using `sg_qd w δ M hA (hgt_le w q) q hEp`. Use `(qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).sub_mem hs hU` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Conclude with `fun q => key2 _ q rfl`.
-/
theorem twistC : TwistC D := by
  intro δ M hA hodd w y
  have hm : 2 * mOdd D = gS D + 1 := by unfold mOdd; obtain ⟨k, hk⟩ := hodd; omega
  have hm' : (1 : D.host.E) - 2 * (mOdd D : D.host.E) = -((gS D : ℕ) : D.host.E) := by
    have : ((2 * mOdd D : ℕ) : D.host.E) = ((gS D + 1 : ℕ) : D.host.E) := by rw [hm]
    push_cast at this; linear_combination -this
  have hEq := E_q w y
  have hτs : ∀ q, selfP w q → τA w q y = (mOdd D : D.host.E) * cf w y q := fun q h => by simp [τA, h]
  have hτu : ∀ q, ¬ selfP w q → upperM w q →
      τA w q y = sgq w (qbar w q) * D.conjF (-(y (qbar w q)) + cf w y (qbar w q)) := fun q h1 h2 => by
    simp [τA, h1, h2]
  have hτl : ∀ q, ¬ selfP w q → ¬ upperM w q → τA w q y = 0 := fun q h1 h2 => by simp [τA, h1, h2]
  have hΛs : ∀ q, selfP w q → ∀ z, z ∈ Λq w q ↔
      z ∈ ddPow D (hgt w q) ∧ z + sgq w q * D.conjF z ∈ qdPow D (hgt w q) := fun q h z => by
    simp only [Λq, h, if_true]; rfl
  have hΛu : ∀ q, ¬ selfP w q → upperM w q → ∀ z, z ∈ Λq w q ↔ z ∈ qdPow D (hgt w q) := fun q h1 h2 z => by
    simp only [Λq, Iq, h1, h2, if_false, not_true_eq_false, or_self]; rfl
  have hΛl : ∀ q, ¬ selfP w q → ¬ upperM w q → ∀ z, z ∈ Λq w q ↔ z ∈ ddPow D (hgt w q) := fun q h1 h2 z => by
    simp only [Λq, Iq, h1, h2, if_false, not_false_eq_true, or_true, if_true]; rfl
  have hup : ∀ q, ¬ selfP w q → upperM w q →
      y q - τA w q y = (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2 := by
    intro q h1 h2
    rw [hτu q h1 h2, hEq, sgq_qbar, neg_add_eq_sub]
  have hsq : ∀ q, ¬ selfP w q → ¬ selfP w (qbar w q) := fun q h1 h => h1 (by
    unfold selfP at h ⊢; rw [qbar_qbar] at h; exact h.symm)
  have hgc : ∀ q, (1 - 2 * (mOdd D : D.host.E)) * cf w y q ∈ qdPow D (hgt w q) ∨
      ¬ (cf w y q ∈ ddPow D (hgt w q)) := fun q => by
    by_cases hc : cf w y q ∈ ddPow D (hgt w q)
    · left; rw [hm', neg_mul]; exact (qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).neg_mem (gS_mul_qd _ hc)
    · right; exact hc
  rw [condX_iff]
  constructor
  · rintro ⟨hy, hE⟩ q
    by_cases h1 : selfP w q
    · rw [hτs q h1, hΛs q h1]
      have hc := cf_mem w y q (fun p _ => hy p)
      refine ⟨(ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).sub_mem (hy q) (nat_mul_mem _ (mOdd D) hc), ?_⟩
      have hqq : qbar w q = q := h1
      have hEq' := hEq q
      rw [hqq] at hEq'
      rw [self_id (sgq w q) (y q) (cf w y q) _ (mOdd D) (sgq_sq w q) (sgq_conj w q) hEq']
      have e1 := hE q
      have e2 : sgq w q * D.conjF ((Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2) -
          (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2 ∈ qdPow D (hgt w q) :=
        (qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).sub_mem (sg_qd w δ M hA (hgt_le w q) q e1) e1
      have e3 : (1 - 2 * (mOdd D : D.host.E)) * cf w y q ∈ qdPow D (hgt w q) := by
        rcases hgc q with h | h
        · exact h
        · exact absurd hc h
      exact (qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).add_mem
        ((qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).sub_mem
          ((qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).add_mem e1 e2) (nat_mul_mem _ (mOdd D) e2)) e3
    · by_cases h2 : upperM w q
      · rw [hΛu q h1 h2, hup q h1 h2]; exact hE q
      · rw [hτl q h1 h2, sub_zero, hΛl q h1 h2]; exact hy q
  · intro ht
    have hy : ∀ q, y q ∈ ddPow D (hgt w q) := by
      have key : ∀ n, ∀ q, hgt w q = n → y q ∈ ddPow D (hgt w q) := by
        intro n
        induction n using Nat.strong_induction_on with
        | _ n ih =>
          intro q hq
          have hlow : ∀ p, hgt w p < hgt w q → y p ∈ ddPow D (hgt w p) := fun p hp => ih _ (hq ▸ hp) p rfl
          by_cases h1 : selfP w q
          · have h3 := (hΛs q h1 _).1 (ht q)
            rw [hτs q h1] at h3
            have hc := cf_mem w y q hlow
            have := (ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).add_mem h3.1 (nat_mul_mem _ (mOdd D) hc)
            rwa [sub_add_cancel] at this
          · by_cases h2 : upperM w q
            · have h3 := (hΛu q h1 h2 _).1 (ht q)
              rw [hτu q h1 h2] at h3
              obtain ⟨hp1, hp2⟩ := upper_qbar w h2
              have hyp : y (qbar w q) ∈ ddPow D (hgt w (qbar w q)) := by
                have := (hΛl _ hp1 hp2 _).1 (ht (qbar w q))
                rwa [hτl _ hp1 hp2, sub_zero] at this
              rw [hgt_qbar] at hyp
              have hcp := cf_mem w y (qbar w q) (fun p hp => hlow p (by rwa [hgt_qbar] at hp))
              rw [hgt_qbar] at hcp
              have hτ := sg_dd w δ M hA (hgt_le w q) (qbar w q)
                ((ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).add_mem
                  ((ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).neg_mem hyp) hcp)
              have := (ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).add_mem (qd_le_dd _ h3) hτ
              rwa [sub_add_cancel] at this
            · have := (hΛl q h1 h2 _).1 (ht q)
              rwa [hτl q h1 h2, sub_zero] at this
      exact fun q => key _ q rfl
    have hG := Xmat_grD w y hy
    refine ⟨hy, ?_⟩
    have hB2 : IsBlockDiagonalMatrix w (Xmat w y - Psi w (Xmat w y)⁻¹) := fun a c h => by
      rw [Matrix.sub_apply, Xmat_blk w y a c h,
        Psi_blk w (blk_inv w (Xmat_upU w y) (Xmat_blk w y)) a c h, sub_self]
    have key2 : ∀ n, ∀ q, hgt w q = n →
        (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2 ∈ qdPow D (hgt w q) := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro q hq
        have hU := unitCons w δ M hA (Xmat_upU w y) (Xmat_blk w y) hG q.2.1 (fun i j hij hh => by
          by_cases hb : blkOf w.1 i.val = blkOf w.1 j.val
          · exact ih _ (by rw [← hq]; exact hh) ⟨(i, j), hij, hb⟩ rfl
          · rw [hB2 i j hb]; exact FractionalIdeal.zero_mem _)
        have hPsiq : Psi w (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2 = sgq w q *
            D.conjF ((Xmat w y - Psi w (Xmat w y)⁻¹) (qbar w q).1.1 (qbar w q).1.2) := rfl
        rw [hPsiq] at hU
        by_cases h1 : selfP w q
        · have hqq : qbar w q = q := h1
          rw [hqq] at hU
          have hT := ((hΛs q h1 _).1 (ht q)).2
          rw [hτs q h1] at hT
          have hEq' := hEq q
          rw [hqq] at hEq'
          rw [self_id (sgq w q) (y q) (cf w y q) _ (mOdd D) (sgq_sq w q) (sgq_conj w q) hEq'] at hT
          have hc := cf_mem w y q (fun p _ => hy p)
          have e3 : (1 - 2 * (mOdd D : D.host.E)) * cf w y q ∈ qdPow D (hgt w q) := by
            rcases hgc q with h | h
            · exact h
            · exact absurd hc h
          set Ee := (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2 with hEe
          have h5 := (qdPow D (hgt w q) : Submodule (𝓞 D.host.E) D.host.E).sub_mem
            ((qdPow D (hgt w q) : Submodule (𝓞 D.host.E) D.host.E).add_mem
              ((qdPow D (hgt w q) : Submodule (𝓞 D.host.E) D.host.E).sub_mem hT e3) (nat_mul_mem _ (mOdd D) hU)) hU
          have eq : Ee + (sgq w q * D.conjF Ee - Ee) - (mOdd D : D.host.E) * (sgq w q * D.conjF Ee - Ee) +
              (1 - 2 * (mOdd D : D.host.E)) * cf w y q - (1 - 2 * (mOdd D : D.host.E)) * cf w y q +
              (mOdd D : D.host.E) * (sgq w q * D.conjF Ee - Ee) - (sgq w q * D.conjF Ee - Ee) = Ee := by ring
          rw [eq] at h5
          exact h5
        · by_cases h2 : upperM w q
          · rw [← hup q h1 h2]; exact (hΛu q h1 h2 _).1 (ht q)
          · have hpu := lower_qbar w h1 h2
            have hps := hsq q h1
            have hEp : (Xmat w y - Psi w (Xmat w y)⁻¹) (qbar w q).1.1 (qbar w q).1.2 ∈
                qdPow D (hgt w (qbar w q)) := by
              rw [← hup _ hps hpu]; exact (hΛu _ hps hpu _).1 (ht _)
            rw [hgt_qbar] at hEp
            have hs := sg_qd w δ M hA (hgt_le w q) q hEp
            have := (qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).sub_mem hs hU
            rwa [sub_sub_cancel] at this
    exact fun q => key2 _ q rfl

end Formalism.L2.SG.Pf.StabIntLat
