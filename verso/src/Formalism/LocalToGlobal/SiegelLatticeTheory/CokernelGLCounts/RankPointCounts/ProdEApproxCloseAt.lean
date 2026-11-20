import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxModes

noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section CloseAt

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

/- English proof (translation)
Simplify using `[Matrix.diagonal_mul, Matrix.mul_diagonal]`.
-/
theorem diag_mul_diag_apply {K : Type*} [CommRing K] {n : ℕ} (a b : Fin n → K) (X : Matrix (Fin n) (Fin n) K)
    (i j : Fin n) : (Matrix.diagonal a * X * Matrix.diagonal b) i j = a i * X i j * b j := by
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal]

set_option maxHeartbeats 800000 in
/- English proof (translation)
Take `⟨ex, ey, d, di, gg, ggi, hexO, heyO, hxx, hyy, hsum, hxy, hd, hg, hlin⟩` from `mode_data M δ hA`. Take `⟨N, Ni, hN, hN', ⟨ν, hν, hNν⟩, hfix⟩` from `exists_unit_monomial_stable_of_Y0 M δ u u' w hA`. Use `set σ := Formalism.L2.SG.Pf.fσ w with hσd`. Establish `hσ : ∀ a, σ (σ a) = a` using `Formalism.L2.SG.Pf.fσ_fσ w`. Use `set h1 : ProdE.GLp p := h.1.1 with hh1d`.

Use `set h2 : ProdE.GLp p := h.1.2.unop with hh2d`. Take `⟨hh1, hh2, hh3⟩` from `h.2`. Establish `hh : (h1 : ProdE.MP p) * N * (h2 : ProdE.MP p) = N` using `hfix _ _ hh1 hh2 hh3`. Take `⟨hi1, hi2, -⟩` from `(h⁻¹).2`. Establish `hΔ : Matrix.diagonal d * Matrix.diagonal di = 1`.

Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `hd i`. Establish `hΓ : Matrix.diagonal gg * Matrix.diagonal ggi = 1`.

Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `hg i`. Establish `hΓ' : Matrix.diagonal ggi * Matrix.diagonal gg = 1`.

Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[mul_comm]`. Conclude with `hg i`.

Take `⟨c', hc'0, hc'O, hcl⟩` from `close ex ey hexO heyO hxx hyy hsum hxy N Ni (Matrix.diagonal d) (Matrix.diagonal di) (Matrix.diagonal gg) (Matrix.diagonal ggi) hN hN' hΔ hΓ hΓ' h1 h2 hh c hc0 hc`. Establish `h1inv : ((h1⁻¹ : ProdE.GLp p) : ProdE.MP p) * (h1 : ProdE.MP p) = 1`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`. Establish `h2inv : (h2 : ProdE.MP p) * ((h2⁻¹ : ProdE.GLp p) : ProdE.MP p) = 1`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`.

Establish `rel1 : (h1 : ProdE.MP p) * mono σ ν = mono σ ν * ((h2⁻¹ : ProdE.GLp p) : ProdE.MP p)`. Rewrite using `[← hNν]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h2inv, Matrix.mul_one]`. Use `_ = N * ((h2⁻¹ : ProdE.GLp p) : ProdE.MP p) := by rw [← Matrix.mul_assoc, hh]`.

Establish `rel2 : ((h1⁻¹ : ProdE.GLp p) : ProdE.MP p) * mono σ ν = mono σ ν * (h2 : ProdE.MP p)`. Rewrite using `[← hNν]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨ex • (Matrix.diagonal di * (h1 : ProdE.MP p) * Matrix.diagonal d) + ey • (Matrix.diagonal gg * (h2 : ProdE.MP p) * Matrix.diagonal ggi).transpose, ?_, ?_, ?_, c', hc'0, hc'O, ?_⟩` and prove the remaining obligations. Introduce `i j hij`.

Establish `a1 : (h1 : ProdE.MP p) i j = 0` using `(hh1 i j).1 hij`. Establish `a2 : (h2 : ProdE.MP p) j i = 0` using `(hh2 j i).1 hij`. Rewrite using `[Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.transpose_apply, diag_mul_diag_apply, diag_mul_diag_apply, a1, a2]`. Simplify using the standard rewrite rules. Introduce `i`.

Establish `a1 : (h1 : ProdE.MP p) i i = 1` using `(hh1 i i).2 rfl`. Establish `a2 : (h2 : ProdE.MP p) i i = 1` using `(hh2 i i).2 rfl`. Establish `t1 : (Matrix.diagonal di * (h1 : ProdE.MP p) * Matrix.diagonal d) i i = 1`. Rewrite using `[diag_mul_diag_apply, a1, mul_one, mul_comm, hd i]`. Establish `t2 : (Matrix.diagonal gg * (h2 : ProdE.MP p) * Matrix.diagonal ggi) i i = 1`.

Rewrite using `[diag_mul_diag_apply, a2, mul_one, hg i]`. Rewrite using `[Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.transpose_apply, t1, t2, smul_eq_mul, smul_eq_mul, mul_one, mul_one, hsum]`. Introduce `i j hij`. Establish `e1 : (h1 : ProdE.MP p) i j = 0` using `fix_pat hσ ν hν (fun a b hab => (hi2 a b).1 hab) rel1 i j hij`. Establish `e2 : (h2 : ProdE.MP p) j i = 0`.

Establish `z : ((h1⁻¹ : ProdE.GLp p) : ProdE.MP p) (σ j) (σ i) = 0` using `(hi1 (σ j) (σ i)).1 hij`. Apply the tactic sequence `have := fix_entry hσ ν rel2 (σ j) (σ i)`. Rewrite `this` using `[hσ, hσ, z, zero_mul]`. Conclude with `(hν (σ j)).mul_right_eq_zero.1 this.symm`. Rewrite using `[Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.transpose_apply, diag_mul_diag_apply, diag_mul_diag_apply, e1, e2]`.

Simplify using the standard rewrite rules. Introduce `g hG set π := ProdE.πP M δ u u' w hA g with hπd set l : ProdE.GLp p := π.1.1 with hld set ρ : ProdE.GLp p := π.1.2.unop with hρd`. Take `⟨hk1, hk2, -⟩` from `(h⁻¹ * π).2`. Take `⟨hπl, hπρ, hπ⟩` from `π.2`. Establish `ek1 : ((h⁻¹ * π).1.1 : ProdE.GLp p) = h1⁻¹ * l` using `rfl`.

Establish `ek2 : ((h⁻¹ * π).1.2.unop : ProdE.GLp p) = ρ * h2⁻¹` using `rfl`. Establish `hk1' : Formalism.MainNotions.S.IsLoUni (((h1⁻¹ * l : ProdE.GLp p)) : ProdE.MP p)` using `by rw [← ek1]; exact hk1`. Establish `hk2' : Formalism.MainNotions.S.IsUpUni (((ρ * h2⁻¹ : ProdE.GLp p)) : ProdE.MP p)` using `by rw [← ek2]; exact hk2`. Establish `hl : ex • ((l : ProdE.GLp p) : ProdE.MP p) = ex • (Matrix.diagonal d * ((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D).map (D.s.atP p).ιE * Matrix.diagonal di)` using `(hlin (g : Formalism.L2.SG.PairVal.GLR D) (Formalism.L2.SG.Pf.VolPinAsm.bOf w g)).1`. Establish `hρ : ey • ((ρ : ProdE.GLp p) : ProdE.MP p) = ey • (Matrix.diagonal ggi * (((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D).map (D.s.atP p).ιE).transpose * Matrix.diagonal gg)` using `(hlin (g : Formalism.L2.SG.PairVal.GLR D) (Formalism.L2.SG.Pf.VolPinAsm.bOf w g)).2`.

Establish `hlN : ((l : ProdE.GLp p) : ProdE.MP p) * N * ((ρ : ProdE.GLp p) : ProdE.MP p) = N` using `hfix _ _ hπl hπρ hπ`. Establish `res` using `hcl l ρ (((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D).map (D.s.atP p).ιE) (fun i j hij => by`. Break down `lt_or_eq_of_le hij with h' | h'` into its components or cases. Rewrite using `[Matrix.sub_apply, (hk1' i j).1 h', Matrix.one_apply_ne (ne_of_lt h'), sub_zero]`. Substitute `h'` using the available equality.

Rewrite using `[Matrix.sub_apply, (hk1' i i).2 rfl, Matrix.one_apply_eq, sub_self])`. Use the proof step `(fun i j hij => by`. Break down `lt_or_eq_of_le hij with h' | h'` into its components or cases. Rewrite using `[Matrix.sub_apply, (hk2' i j).1 h', Matrix.one_apply_ne (ne_of_gt h'), sub_zero]`. Substitute `h'` using the available equality.

Rewrite using `[Matrix.sub_apply, (hk2' j j).2 rfl, Matrix.one_apply_eq, sub_self])`. Use `hlN hl hρ hG`. Rewrite using `[ek1, ek2]`. Conclude with `res`.
-/
theorem close_at {p : PlF D} (hA : Agree δ M p) (h : ProdE.StP M δ u u' w p) (c : (D.s.atP p).Fp) (hc0 : c ≠ 0)
    (hc : c ∈ 𝒪[(D.s.atP p).Fp]) :
    ∃ τ : ProdE.MP p, (∀ i j, i < j → τ i j = 0) ∧ (∀ i, τ i i = 1) ∧
      (∀ i j, Formalism.L2.SG.Pf.fσ w j < Formalism.L2.SG.Pf.fσ w i → τ i j = 0) ∧
      ∃ c' : (D.s.atP p).Fp, c' ≠ 0 ∧ c' ∈ 𝒪[(D.s.atP p).Fp] ∧ ∀ g : Formalism.L2.SG.Pf.VolPinAsm.StG w,
        EntIn (latS (D.s.atP p) c') (((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D).map (D.s.atP p).ιE - τ) →
        EntIn (latS (D.s.atP p) c) (((h⁻¹ * ProdE.πP M δ u u' w hA g).1.1 : ProdE.MP p) - 1) ∧
          EntIn (latS (D.s.atP p) c) (((h⁻¹ * ProdE.πP M δ u u' w hA g).1.2.unop : ProdE.MP p) - 1) := by
  obtain ⟨ex, ey, d, di, gg, ggi, hexO, heyO, hxx, hyy, hsum, hxy, hd, hg, hlin⟩ := mode_data M δ hA
  obtain ⟨N, Ni, hN, hN', ⟨ν, hν, hNν⟩, hfix⟩ := exists_unit_monomial_stable_of_Y0 M δ u u' w hA
  set σ := Formalism.L2.SG.Pf.fσ w with hσd
  have hσ : ∀ a, σ (σ a) = a := Formalism.L2.SG.Pf.fσ_fσ w
  set h1 : ProdE.GLp p := h.1.1 with hh1d
  set h2 : ProdE.GLp p := h.1.2.unop with hh2d
  obtain ⟨hh1, hh2, hh3⟩ := h.2
  have hh : (h1 : ProdE.MP p) * N * (h2 : ProdE.MP p) = N := hfix _ _ hh1 hh2 hh3
  obtain ⟨hi1, hi2, -⟩ := (h⁻¹).2
  have hΔ : Matrix.diagonal d * Matrix.diagonal di = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact hd i
  have hΓ : Matrix.diagonal gg * Matrix.diagonal ggi = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact hg i
  have hΓ' : Matrix.diagonal ggi * Matrix.diagonal gg = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; rw [mul_comm]; exact hg i
  obtain ⟨c', hc'0, hc'O, hcl⟩ := close ex ey hexO heyO hxx hyy hsum hxy N Ni (Matrix.diagonal d) (Matrix.diagonal di)
    (Matrix.diagonal gg) (Matrix.diagonal ggi) hN hN' hΔ hΓ hΓ' h1 h2 hh c hc0 hc

  have h1inv : ((h1⁻¹ : ProdE.GLp p) : ProdE.MP p) * (h1 : ProdE.MP p) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2inv : (h2 : ProdE.MP p) * ((h2⁻¹ : ProdE.GLp p) : ProdE.MP p) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have rel1 : (h1 : ProdE.MP p) * mono σ ν = mono σ ν * ((h2⁻¹ : ProdE.GLp p) : ProdE.MP p) := by
    rw [← hNν]
    calc (h1 : ProdE.MP p) * N = (h1 : ProdE.MP p) * N * ((h2 : ProdE.MP p) * ((h2⁻¹ : ProdE.GLp p) : ProdE.MP p)) := by
          rw [h2inv, Matrix.mul_one]
      _ = N * ((h2⁻¹ : ProdE.GLp p) : ProdE.MP p) := by rw [← Matrix.mul_assoc, hh]
  have rel2 : ((h1⁻¹ : ProdE.GLp p) : ProdE.MP p) * mono σ ν = mono σ ν * (h2 : ProdE.MP p) := by
    rw [← hNν]
    calc ((h1⁻¹ : ProdE.GLp p) : ProdE.MP p) * N
        = ((h1⁻¹ : ProdE.GLp p) : ProdE.MP p) * ((h1 : ProdE.MP p) * N * (h2 : ProdE.MP p)) := by rw [hh]
      _ = N * (h2 : ProdE.MP p) := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1inv, Matrix.one_mul]
  refine ⟨ex • (Matrix.diagonal di * (h1 : ProdE.MP p) * Matrix.diagonal d) +
      ey • (Matrix.diagonal gg * (h2 : ProdE.MP p) * Matrix.diagonal ggi).transpose, ?_, ?_, ?_, c', hc'0, hc'O, ?_⟩
  · intro i j hij
    have a1 : (h1 : ProdE.MP p) i j = 0 := (hh1 i j).1 hij
    have a2 : (h2 : ProdE.MP p) j i = 0 := (hh2 j i).1 hij
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.transpose_apply, diag_mul_diag_apply,
      diag_mul_diag_apply, a1, a2]
    simp
  · intro i
    have a1 : (h1 : ProdE.MP p) i i = 1 := (hh1 i i).2 rfl
    have a2 : (h2 : ProdE.MP p) i i = 1 := (hh2 i i).2 rfl
    have t1 : (Matrix.diagonal di * (h1 : ProdE.MP p) * Matrix.diagonal d) i i = 1 := by
      rw [diag_mul_diag_apply, a1, mul_one, mul_comm, hd i]
    have t2 : (Matrix.diagonal gg * (h2 : ProdE.MP p) * Matrix.diagonal ggi) i i = 1 := by
      rw [diag_mul_diag_apply, a2, mul_one, hg i]
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.transpose_apply, t1, t2, smul_eq_mul,
      smul_eq_mul, mul_one, mul_one, hsum]
  · intro i j hij
    have e1 : (h1 : ProdE.MP p) i j = 0 :=
      fix_pat hσ ν hν (fun a b hab => (hi2 a b).1 hab) rel1 i j hij
    have e2 : (h2 : ProdE.MP p) j i = 0 := by
      have z : ((h1⁻¹ : ProdE.GLp p) : ProdE.MP p) (σ j) (σ i) = 0 := (hi1 (σ j) (σ i)).1 hij
      have := fix_entry hσ ν rel2 (σ j) (σ i)
      rw [hσ, hσ, z, zero_mul] at this
      exact (hν (σ j)).mul_right_eq_zero.1 this.symm
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.transpose_apply, diag_mul_diag_apply,
      diag_mul_diag_apply, e1, e2]
    simp
  · intro g hG
    set π := ProdE.πP M δ u u' w hA g with hπd
    set l : ProdE.GLp p := π.1.1 with hld
    set ρ : ProdE.GLp p := π.1.2.unop with hρd
    obtain ⟨hk1, hk2, -⟩ := (h⁻¹ * π).2
    obtain ⟨hπl, hπρ, hπ⟩ := π.2
    have ek1 : ((h⁻¹ * π).1.1 : ProdE.GLp p) = h1⁻¹ * l := rfl
    have ek2 : ((h⁻¹ * π).1.2.unop : ProdE.GLp p) = ρ * h2⁻¹ := rfl
    have hk1' : Formalism.MainNotions.S.IsLoUni (((h1⁻¹ * l : ProdE.GLp p)) : ProdE.MP p) := by rw [← ek1]; exact hk1
    have hk2' : Formalism.MainNotions.S.IsUpUni (((ρ * h2⁻¹ : ProdE.GLp p)) : ProdE.MP p) := by rw [← ek2]; exact hk2
    have hl : ex • ((l : ProdE.GLp p) : ProdE.MP p) =
        ex • (Matrix.diagonal d * ((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D).map (D.s.atP p).ιE *
          Matrix.diagonal di) :=
      (hlin (g : Formalism.L2.SG.PairVal.GLR D) (Formalism.L2.SG.Pf.VolPinAsm.bOf w g)).1
    have hρ : ey • ((ρ : ProdE.GLp p) : ProdE.MP p) =
        ey • (Matrix.diagonal ggi * (((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D).map
          (D.s.atP p).ιE).transpose * Matrix.diagonal gg) :=
      (hlin (g : Formalism.L2.SG.PairVal.GLR D) (Formalism.L2.SG.Pf.VolPinAsm.bOf w g)).2
    have hlN : ((l : ProdE.GLp p) : ProdE.MP p) * N * ((ρ : ProdE.GLp p) : ProdE.MP p) = N := hfix _ _ hπl hπρ hπ
    have res := hcl l ρ (((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D).map (D.s.atP p).ιE)
      (fun i j hij => by
        rcases lt_or_eq_of_le hij with h' | h'
        · rw [Matrix.sub_apply, (hk1' i j).1 h', Matrix.one_apply_ne (ne_of_lt h'), sub_zero]
        · subst h'
          rw [Matrix.sub_apply, (hk1' i i).2 rfl, Matrix.one_apply_eq, sub_self])
      (fun i j hij => by
        rcases lt_or_eq_of_le hij with h' | h'
        · rw [Matrix.sub_apply, (hk2' i j).1 h', Matrix.one_apply_ne (ne_of_gt h'), sub_zero]
        · subst h'
          rw [Matrix.sub_apply, (hk2' j j).2 rfl, Matrix.one_apply_eq, sub_self])
      hlN hl hρ hG
    rw [ek1, ek2]
    exact res

end CloseAt

end Formalism.L2.SG.Pf.ProdEApprox
