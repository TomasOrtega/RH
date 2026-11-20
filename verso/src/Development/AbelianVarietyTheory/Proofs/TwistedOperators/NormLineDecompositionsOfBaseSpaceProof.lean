import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Proof.normLineDecompositionsOfBaseSpace_proof

open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents

/- English proof (translation)
Use `D.host.der.cm` as an intermediate fact. Take `⟨ψ⟩` from `(inferInstance : Nonempty (D.host.E →+* ℂ))`. Establish `hc : ∀ y, ψ (D.host.conj y) = starRingEnd ℂ (ψ y)` using `(D.host.der.conj_iff ψ D.host.conj).2 (MulEquiv.apply_symm_apply _ _)`. Apply `ψ.injective` to reduce the goal to its premises. Rewrite using `[hc]`.

Conclude with `NumberField.IsCMField.complexEmbedding_complexConj _ ψ x`.
-/
theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  have := D.host.der.cm
  obtain ⟨ψ⟩ := (inferInstance : Nonempty (D.host.E →+* ℂ))
  have hc : ∀ y, ψ (D.host.conj y) = starRingEnd ℂ (ψ y) :=
    (D.host.der.conj_iff ψ D.host.conj).2 (MulEquiv.apply_symm_apply _ _)
  apply ψ.injective
  rw [hc]
  exact NumberField.IsCMField.complexEmbedding_complexConj _ ψ x

/- English proof (translation)
Rewrite using `[← S.herm.eq x y, h, map_zero]`.
-/
theorem hT_zero_symm {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) {x y : S.V}
    (h : S.hT x y = 0) : S.hT y x = 0 := by
  rw [← S.herm.eq x y, h, map_zero]

/- English proof (translation)
Establish `hm : 0 < D.R.m` using `by have := D.R.two_le_m; omega`. Establish `hsym : ∀ a b : (D.sp.Y 0).V, (D.sp.Y 0).hT a b = 0 → (D.sp.Y 0).hT b a = 0` using `fun a b h => hT_zero_symm (D.sp.Y 0) h`. Use `{ isom := D.sp.iXY_isom 0 hm a_le := le_rfl rank := ?_ z_norm := ?_ z_X := ?_ ee := ?_ ff := ?_ ef := ?_ hyp_X := ?_ hyperbolicDecomp_hyp_orthogonal_line := ?_ }` and prove the remaining obligations. Rewrite using `[D.sp.Y_rank 0 (Nat.zero_le _), D.sp.X_rank 0 (Nat.zero_le _)]`. Take `⟨j, hj⟩` from `D.R.m_even`.

Simplify using `only [Formalism.BasicNotions.Ranks.rankY, Formalism.BasicNotions.Ranks.N, Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS]`. Use linear arithmetic over natural numbers and integers. Introduce `i`. Simplify using `only [HSpace.hD, LinearMap.map_smulₛₗ₂, map_smul, D.sp.zm_norm, starRingEnd_apply, smul_eq_mul, D.sp_T]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `i x`. Simplify using `only [HSpace.hD, LinearMap.map_smulₛₗ₂, hsym _ _ (D.sp.zm_orth x), smul_zero]`. Introduce `i j`. Conclude with `D.sp.hyp_ee j i`. Introduce `i j`.

Conclude with `D.sp.hyp_ff j i`. Introduce `i j`. Simplify using `only [HSpace.hD]`. Rewrite using `[← (D.sp.Y 0).herm.eq (D.sp.hypE i) (D.sp.hypF j), D.sp.hyp_ef]`. Apply the tactic sequence `split_ifs <;> simp`.

Introduce `i x`. Conclude with `⟨hsym _ _ (D.sp.hyp_orthX i x).1, hsym _ _ (D.sp.hyp_orthX i x).2⟩`. Introduce `i j`. Simplify using `only [HSpace.hD, map_smul, hsym _ _ (D.sp.hyp_orthz i).1, hsym _ _ (D.sp.hyp_orthz i).2, smul_zero, and_self]`.
-/
theorem isDec_smul (D : D7) (t : D.host.E) :
    IsDec (D.sp.Y 0) (D.sp.X 0) (D.sp.iXY 0) (fun _ : Fin 1 => t • D.sp.zm)
      (-(t * star t * ((D.mem D.u₀).A.T : D.host.E))) D.sp.hypE D.sp.hypF := by
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hsym : ∀ a b : (D.sp.Y 0).V, (D.sp.Y 0).hT a b = 0 → (D.sp.Y 0).hT b a = 0 :=
    fun a b h => hT_zero_symm (D.sp.Y 0) h
  refine
    { isom := D.sp.iXY_isom 0 hm
      a_le := le_rfl
      rank := ?_
      z_norm := ?_
      z_X := ?_
      ee := ?_
      ff := ?_
      ef := ?_
      hyp_X := ?_
      hyperbolicDecomp_hyp_orthogonal_line := ?_ }
  · rw [D.sp.Y_rank 0 (Nat.zero_le _), D.sp.X_rank 0 (Nat.zero_le _)]
    obtain ⟨j, hj⟩ := D.R.m_even
    simp only [Formalism.BasicNotions.Ranks.rankY, Formalism.BasicNotions.Ranks.N, Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS]
    omega
  · intro i
    simp only [HSpace.hD, LinearMap.map_smulₛₗ₂, map_smul, D.sp.zm_norm, starRingEnd_apply, smul_eq_mul,
      D.sp_T]
    ring
  · intro i x
    simp only [HSpace.hD, LinearMap.map_smulₛₗ₂, hsym _ _ (D.sp.zm_orth x), smul_zero]
  · intro i j
    exact D.sp.hyp_ee j i
  · intro i j
    exact D.sp.hyp_ff j i
  · intro i j
    simp only [HSpace.hD]
    rw [← (D.sp.Y 0).herm.eq (D.sp.hypE i) (D.sp.hypF j), D.sp.hyp_ef]
    split_ifs <;> simp
  · intro i x
    exact ⟨hsym _ _ (D.sp.hyp_orthX i x).1, hsym _ _ (D.sp.hyp_orthX i x).2⟩
  · intro i j
    simp only [HSpace.hD, map_smul, hsym _ _ (D.sp.hyp_orthz i).1, hsym _ _ (D.sp.hyp_orthz i).2, smul_zero,
      and_self]

/- English proof (translation)
Use `⟨fun u => ?_, ?_⟩` and prove the remaining obligations. Establish `hc0` using `D.cOf_ne u`. Establish `hc1 : D.host.conj (D.cOf u) ≠ 0` using `(map_ne_zero _).2 hc0`. Establish `h` using `isDec_smul D (D.cOf u)⁻¹`. Establish `hs : -((D.cOf u)⁻¹ * star (D.cOf u)⁻¹ * ((D.mem D.u₀).A.T : D.host.E)) = -Tu D u`.

Rewrite using `[star_inv₀, star_eq_conj, ← D.cOf_eq u]`. Clear the denominators using the available nonvanishing facts. Rewrite `h` using `[hs]`. Conclude with `h`. Take `⟨π, -, hπ, -⟩` from `D.T_norm D.u₀`.

Establish `hT : ((D.mem D.u₀).A.T : D.host.E) ≠ 0`. Rewrite using `[← D.sp_T]`. Conclude with `D.sp.T_prime.ne_zero` after adjusting the coercions. Establish `hπ0 : (π : D.host.E) ≠ 0`. Introduce and unpack `h0`.

Rewrite `hπ` using `[h0, zero_mul]`. Conclude with `hT hπ.symm`. Establish `hπ1 : D.host.conj (π : D.host.E) ≠ 0` using `(map_ne_zero _).2 hπ0`. Use `⟨(π : D.host.E)⁻¹ • D.sp.zm, ?_⟩` and prove the remaining obligations. Establish `h` using `isDec_smul D (π : D.host.E)⁻¹`.

Establish `hs : -((π : D.host.E)⁻¹ * star (π : D.host.E)⁻¹ * ((D.mem D.u₀).A.T : D.host.E)) = -1`. Rewrite using `[star_inv₀, star_eq_conj, ← hπ]`. Clear the denominators using the available nonvanishing facts. Rewrite `h` using `[hs]`. Conclude with `h`.
-/
theorem recordDec (D : D7) : RecordDecSt D := by
  refine ⟨fun u => ?_, ?_⟩
  · have hc0 := D.cOf_ne u
    have hc1 : D.host.conj (D.cOf u) ≠ 0 := (map_ne_zero _).2 hc0
    have h := isDec_smul D (D.cOf u)⁻¹
    have hs : -((D.cOf u)⁻¹ * star (D.cOf u)⁻¹ * ((D.mem D.u₀).A.T : D.host.E)) = -Tu D u := by
      rw [star_inv₀, star_eq_conj, ← D.cOf_eq u]
      field_simp
    rw [hs] at h
    exact h
  · obtain ⟨π, -, hπ, -⟩ := D.T_norm D.u₀
    have hT : ((D.mem D.u₀).A.T : D.host.E) ≠ 0 := by
      rw [← D.sp_T]
      exact_mod_cast D.sp.T_prime.ne_zero
    have hπ0 : (π : D.host.E) ≠ 0 := by
      rintro h0
      rw [h0, zero_mul] at hπ
      exact hT hπ.symm
    have hπ1 : D.host.conj (π : D.host.E) ≠ 0 := (map_ne_zero _).2 hπ0
    refine ⟨(π : D.host.E)⁻¹ • D.sp.zm, ?_⟩
    have h := isDec_smul D (π : D.host.E)⁻¹
    have hs : -((π : D.host.E)⁻¹ * star (π : D.host.E)⁻¹ * ((D.mem D.u₀).A.T : D.host.E)) = -1 := by
      rw [star_inv₀, star_eq_conj, ← hπ]
      field_simp
    rw [hs] at h
    exact h

end GlobalTheory.Proof.normLineDecompositionsOfBaseSpace_proof
