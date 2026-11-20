import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxCong

noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Split

variable {F K : Type*} [Field F] [CommRing K] [Algebra F K] {r : ℕ}

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.smul_apply, smul_eq_mul]`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, AlgEquiv.apply_symm_apply]`. Use `congrFun (congrFun h i) j` as an intermediate fact.

Simplify using `only [cx, Matrix.map_apply, RingHom.comp_apply, RingHom.coe_fst, RingHom.coe_coe] at this`. Use `ext`. Simplify using `[this]`. Simplify using the standard rewrite rules.
-/
theorem smul_eq_of_cx (e : K ≃ₐ[F] F × F) {X Y : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : cx e X = cx e Y) :
    e.symm (1, 0) • X = e.symm (1, 0) • Y := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  apply e.injective
  rw [map_mul, map_mul, AlgEquiv.apply_symm_apply]
  have := congrFun (congrFun h i) j
  simp only [cx, Matrix.map_apply, RingHom.comp_apply, RingHom.coe_fst, RingHom.coe_coe] at this
  ext
  · simp [this]
  · simp

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.smul_apply, smul_eq_mul]`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, AlgEquiv.apply_symm_apply]`. Use `congrFun (congrFun h i) j` as an intermediate fact.

Simplify using `only [cy, Matrix.map_apply, RingHom.comp_apply, RingHom.coe_snd, RingHom.coe_coe] at this`. Use `ext`. Simplify using the standard rewrite rules. Simplify using `[this]`.
-/
theorem smul_eq_of_cy (e : K ≃ₐ[F] F × F) {X Y : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : cy e X = cy e Y) :
    e.symm (0, 1) • X = e.symm (0, 1) • Y := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  apply e.injective
  rw [map_mul, map_mul, AlgEquiv.apply_symm_apply]
  have := congrFun (congrFun h i) j
  simp only [cy, Matrix.map_apply, RingHom.comp_apply, RingHom.coe_snd, RingHom.coe_coe] at this
  ext
  · simp
  · simp [this]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [cx, Matrix.map_apply, Matrix.diagonal_apply, RingHom.comp_apply, RingHom.coe_fst, RingHom.coe_coe]`. Apply the tactic sequence `split_ifs <;> simp [AlgEquiv.commutes]`.
-/
theorem cx_diag (e : K ≃ₐ[F] F × F) (d : Fin (r + 1) → F) :
    cx e (Matrix.diagonal fun i => algebraMap F K (d i)) = Matrix.diagonal d := by
  ext i j
  simp only [cx, Matrix.map_apply, Matrix.diagonal_apply, RingHom.comp_apply, RingHom.coe_fst, RingHom.coe_coe]
  split_ifs <;> simp [AlgEquiv.commutes]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [cy, Matrix.map_apply, Matrix.diagonal_apply, RingHom.comp_apply, RingHom.coe_snd, RingHom.coe_coe]`. Apply the tactic sequence `split_ifs <;> simp [AlgEquiv.commutes]`.
-/
theorem cy_diag (e : K ≃ₐ[F] F × F) (d : Fin (r + 1) → F) :
    cy e (Matrix.diagonal fun i => algebraMap F K (d i)) = Matrix.diagonal d := by
  ext i j
  simp only [cy, Matrix.map_apply, Matrix.diagonal_apply, RingHom.comp_apply, RingHom.coe_snd, RingHom.coe_coe]
  split_ifs <;> simp [AlgEquiv.commutes]

end Split

section Data

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp)

/- English proof (translation)
Take `⟨-, -, -, -, -, hsp⟩` from `id hA`. Consider the cases of `hM : (M p).split with`. Consider the case `none`. Use `⟨1, 0, fun i => (M p).L.cj (frFac δ p i), fun i => Ring.inverse ((M p).L.cj (frFac δ p i)), fun _ => 1, fun _ => 1, (D.s.atP p).O.one_mem, (D.s.atP p).O.zero_mem, mul_one 1, mul_zero 0, add_zero 1, mul_zero 1, fun i => Ring.mul_inverse_cancel _ ((frFac_unit δ M hA i).map _), fun …` and prove the remaining obligations. Simplify using `only [lOf, hM, one_smul]`.

Conclude with `lL_eq _ _ _ a`. Simplify using `only [zero_smul]`. Consider the case `some g`. Break down `hR : (D.s.atP p).split with _ | sg` into its components or cases. Simplify using `[hM, hR] at hsp`.

Establish `hsp' : g.e = sg.e ∧ g.q = sg.q` using `by simpa [hM, hR] using hsp`. Establish `hx` using `fun i => (split_units δ M hA g i).1`. Establish `hy` using `fun i => (split_units δ M hA g i).2`. Establish `hmemO : ∀ a b : (D.s.atP p).Fp, a ∈ 𝒪[(D.s.atP p).Fp] → b ∈ 𝒪[(D.s.atP p).Fp] → g.e.symm (a, b) ∈ (D.s.atP p).O`. Introduce `a b ha hb`.

Rewrite using `[Formalism.MainNotions.BridgeLemma.O_split (D.s.atP p) sg, ← hsp'.1, AlgEquiv.apply_symm_apply]`. Conclude with `⟨ha, hb⟩`. Use `⟨g.e.symm (1, 0), g.e.symm (0, 1), fun i => algebraMap _ _ ((g.e (frFac δ p i)).2), fun i => algebraMap _ _ ((g.e (frFac δ p i)).2)⁻¹, fun i => algebraMap _ _ ((g.e (frFac δ p i)).1), fun i => algebraMap _ _ ((g.e (frFac δ p i)).1)⁻¹, hmemO 1 0 (Subring.one_mem _) (Subring.zero_m …` and prove the remaining obligations. Apply `g.e.injective` to reduce the goal to its premises. Simplify using the standard rewrite rules.

Apply `g.e.injective` to reduce the goal to its premises. Simplify using the standard rewrite rules. Apply `g.e.injective` to reduce the goal to its premises. Simplify using the standard rewrite rules. Apply `g.e.injective` to reduce the goal to its premises.

Simplify using the standard rewrite rules. Simplify using `only [lOf, hM]`. Apply `smul_eq_of_cx` to reduce the goal to its premises. Rewrite using `[cx_lG, cx_mul, cx_mul, cx_diag, cx_diag]`. Both sides reduce to the same expression.

Simplify using `only [ρOf, hM]`. Apply `smul_eq_of_cy` to reduce the goal to its premises. Rewrite using `[cy_ρG, cy_mul, cy_mul, cy_diag, cy_diag]`. Both sides reduce to the same expression.
-/
theorem mode_data {p : PlF D} (hA : Agree δ M p) :
    ∃ (ex ey : (D.s.atP p).Ep) (d di gg ggi : Fin (D.R.rS + 1) → (D.s.atP p).Ep),
      ex ∈ (D.s.atP p).O ∧ ey ∈ (D.s.atP p).O ∧ ex * ex = ex ∧ ey * ey = ey ∧ ex + ey = 1 ∧ ex * ey = 0 ∧
      (∀ i, d i * di i = 1) ∧ (∀ i, gg i * ggi i = 1) ∧
      ∀ a b : Formalism.L2.SG.PairVal.MatR D,
        ex • lOf δ M p a b = ex • (Matrix.diagonal d * a.map (D.s.atP p).ιE * Matrix.diagonal di) ∧
        ey • ρOf δ M p a b = ey • (Matrix.diagonal ggi * (a.map (D.s.atP p).ιE).transpose * Matrix.diagonal gg) := by
  obtain ⟨-, -, -, -, -, hsp⟩ := id hA
  cases hM : (M p).split with
  | none =>
    refine ⟨1, 0, fun i => (M p).L.cj (frFac δ p i), fun i => Ring.inverse ((M p).L.cj (frFac δ p i)),
      fun _ => 1, fun _ => 1, (D.s.atP p).O.one_mem, (D.s.atP p).O.zero_mem, mul_one 1, mul_zero 0, add_zero 1,
      mul_zero 1, fun i => Ring.mul_inverse_cancel _ ((frFac_unit δ M hA i).map _), fun _ => mul_one 1, fun a b => ⟨?_, ?_⟩⟩
    · simp only [lOf, hM, one_smul]
      exact lL_eq _ _ _ a
    · simp only [zero_smul]
  | some g =>
    rcases hR : (D.s.atP p).split with _ | sg
    · simp [hM, hR] at hsp
    · have hsp' : g.e = sg.e ∧ g.q = sg.q := by simpa [hM, hR] using hsp
      have hx := fun i => (split_units δ M hA g i).1
      have hy := fun i => (split_units δ M hA g i).2
      have hmemO : ∀ a b : (D.s.atP p).Fp, a ∈ 𝒪[(D.s.atP p).Fp] → b ∈ 𝒪[(D.s.atP p).Fp] →
          g.e.symm (a, b) ∈ (D.s.atP p).O := by
        intro a b ha hb
        rw [Formalism.MainNotions.BridgeLemma.O_split (D.s.atP p) sg, ← hsp'.1, AlgEquiv.apply_symm_apply]
        exact ⟨ha, hb⟩
      refine ⟨g.e.symm (1, 0), g.e.symm (0, 1),
        fun i => algebraMap _ _ ((g.e (frFac δ p i)).2), fun i => algebraMap _ _ ((g.e (frFac δ p i)).2)⁻¹,
        fun i => algebraMap _ _ ((g.e (frFac δ p i)).1), fun i => algebraMap _ _ ((g.e (frFac δ p i)).1)⁻¹,
        hmemO 1 0 (Subring.one_mem _) (Subring.zero_mem _), hmemO 0 1 (Subring.zero_mem _) (Subring.one_mem _),
        ?_, ?_, ?_, ?_, fun i => by rw [← map_mul, mul_inv_cancel₀ (hy i), map_one],
        fun i => by rw [← map_mul, mul_inv_cancel₀ (hx i), map_one], fun a b => ⟨?_, ?_⟩⟩
      · apply g.e.injective; simp
      · apply g.e.injective; simp
      · apply g.e.injective; simp
      · apply g.e.injective; simp
      · simp only [lOf, hM]
        apply smul_eq_of_cx
        rw [cx_lG, cx_mul, cx_mul, cx_diag, cx_diag]
        rfl
      · simp only [ρOf, hM]
        apply smul_eq_of_cy
        rw [cy_ρG, cy_mul, cy_mul, cy_diag, cy_diag]
        rfl

end Data

end Formalism.L2.SG.Pf.ProdEApprox
