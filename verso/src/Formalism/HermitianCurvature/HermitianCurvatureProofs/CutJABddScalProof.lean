import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddScalBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddGen
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.CutMP.JA.BStar Formalism.FourierDecayAlt.P.MAx2.Adj Formalism.FourierDecayAlt.P.MAx1.An Formalism.QuantumDeterminants
open scoped ComplexConjugate Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

section deriv

variable {k r : ℕ} {F F' : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup F'] [NormedSpace ℂ F']

/- English proof (translation)
Use function extensionality and compare the values at `g`. Unfold `B.LdV`. Conclude with `P.JCTx6.Pos.deriv_cle_comp L L' hL (fun t : ℝ => f (NormedSpace.exp (-((t : ℂ) • X)) * g)) 0`.
-/
theorem ldV_rl (L : F →L[ℝ] F') (L' : F' →L[ℝ] F) (hL : ∀ y, L' (L y) = y) (X : B.Mat k r) (f : B.Mat k r → F) :
    B.LdV X (fun g => L (f g)) = fun g => L (B.LdV X f g) := by
  funext g
  unfold B.LdV
  exact P.JCTx6.Pos.deriv_cle_comp L L' hL (fun t : ℝ => f (NormedSpace.exp (-((t : ℂ) • X)) * g)) 0

/- English proof (translation)
Use function extensionality and compare the values at `g`. Unfold `Formalism.REAL.RdV`. Conclude with `P.JCTx6.Pos.deriv_cle_comp L L' hL (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0`.
-/
theorem rdV_rl (L : F →L[ℝ] F') (L' : F' →L[ℝ] F) (hL : ∀ y, L' (L y) = y) (X : B.Mat k r) (f : B.Mat k r → F) :
    Formalism.REAL.RdV X (fun g => L (f g)) = fun g => L (Formalism.REAL.RdV X f g) := by
  funext g
  unfold Formalism.REAL.RdV
  exact P.JCTx6.Pos.deriv_cle_comp L L' hL (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0

/- English proof (translation)
The claim follows from `| [], _ => rfl | X :: v, f => by show Formalism.REAL.RdV X (B.Rw v fun g => L (f g)) = fun g => L (Formalism.REAL.RdV X (B.Rw v f) g) rw [rw_rl L L' hL v f, rdV_rl L L' hL X]`.
-/
theorem rw_rl (L : F →L[ℝ] F') (L' : F' →L[ℝ] F) (hL : ∀ y, L' (L y) = y) :
    ∀ (v : List (B.Mat k r)) (f : B.Mat k r → F), B.Rw v (fun g => L (f g)) = fun g => L (B.Rw v f g)
  | [], _ => rfl
  | X :: v, f => by
    show Formalism.REAL.RdV X (B.Rw v fun g => L (f g)) = fun g => L (Formalism.REAL.RdV X (B.Rw v f) g)
    rw [rw_rl L L' hL v f, rdV_rl L L' hL X]

/- English proof (translation)
The claim follows from `| [], f => rw_rl L L' hL w f | X :: u, f => by show B.LdV X (B.dLR u w fun g => L (f g)) = fun g => L (B.LdV X (B.dLR u w f) g) rw [dLR_rl L L' hL w u f, ldV_rl L L' hL X]`.
-/
theorem dLR_rl (L : F →L[ℝ] F') (L' : F' →L[ℝ] F) (hL : ∀ y, L' (L y) = y) (w : List (B.Mat k r)) :
    ∀ (u : List (B.Mat k r)) (f : B.Mat k r → F), B.dLR u w (fun g => L (f g)) = fun g => L (B.dLR u w f g)
  | [], f => rw_rl L L' hL w f
  | X :: u, f => by
    show B.LdV X (B.dLR u w fun g => L (f g)) = fun g => L (B.LdV X (B.dLR u w f) g)
    rw [dLR_rl L L' hL w u f, ldV_rl L L' hL X]

/- English proof (translation)
The claim follows from `dLR_rl (Complex.conjCLE : ℂ →L[ℝ] ℂ) (Complex.conjCLE : ℂ →L[ℝ] ℂ) (fun y => by simp) w u f`.
-/
theorem dLR_conj (u w : List (B.Mat k r)) (f : B.Mat k r → ℂ) :
    B.dLR u w (fun g => conj (f g)) = fun g => conj (B.dLR u w f g) :=
  dLR_rl (Complex.conjCLE : ℂ →L[ℝ] ℂ) (Complex.conjCLE : ℂ →L[ℝ] ℂ) (fun y => by simp) w u f

/- English proof (translation)
Distinguish the cases in `hA : A = 0`. Substitute `hA` using the available equality. Simplify using `only [smul_zero]`. Conclude with `Formalism.FourierDecayAlt.P.BetaSesquilinearity.dLR_zero u w`. Take `⟨ℓ, -, hℓ⟩` from `exists_dual_vector ℂ A (norm_ne_zero_iff.2 hA)`.

Establish `hn : ((‖A‖ : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast norm_ne_zero_iff.2 hA`. Set `L : ℂ →L[ℝ] F` to `((ContinuousLinearMap.id ℂ ℂ).smulRight A).restrictScalars ℝ`. Set `L' : F →L[ℝ] ℂ` to `((((‖A‖ : ℝ) : ℂ))⁻¹ • ℓ).restrictScalars ℝ`. Establish `hL : ∀ y, L' (L y) = y` using `fun y => by`. Simplify using `only [L, L', ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, map_smul, hℓ, smul_eq_mul]`.

Clear the denominators using the available nonvanishing facts. Use `norm_cast`. Conclude with `dLR_rl L L' hL w u f`.
-/
theorem dLR_smulc (A : F) (u w : List (B.Mat k r)) (f : B.Mat k r → ℂ) :
    B.dLR u w (fun g => f g • A) = fun g => B.dLR u w f g • A := by
  by_cases hA : A = 0
  · subst hA; simp only [smul_zero]; exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.dLR_zero u w
  obtain ⟨ℓ, -, hℓ⟩ := exists_dual_vector ℂ A (norm_ne_zero_iff.2 hA)
  have hn : ((‖A‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hA
  let L : ℂ →L[ℝ] F := ((ContinuousLinearMap.id ℂ ℂ).smulRight A).restrictScalars ℝ
  let L' : F →L[ℝ] ℂ := ((((‖A‖ : ℝ) : ℂ))⁻¹ • ℓ).restrictScalars ℝ
  have hL : ∀ y, L' (L y) = y := fun y => by
    simp only [L, L', ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, map_smul, hℓ, smul_eq_mul]
    field_simp
    norm_cast
  exact dLR_rl L L' hL w u f

end deriv

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ D Bg φ hφ`. Use `⟨fun g₀ hg₀ => ?_, fun ε hε m => ?_⟩` and prove the remaining obligations. Take `⟨U, φ', hU, hg, hφ', he⟩` from `hφ.1 g₀ hg₀`. Use `⟨U, fun g => conj (φ' g), hU, hg, ?_, fun g hgU hgG => by simp only; rw [he g hgU hgG]⟩` and prove the remaining obligations. Conclude with `(Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp_contDiffOn hφ'`.

Take `⟨C, hC⟩` from `hφ.2 ε hε m`. Use `⟨C, fun u w hu hw hl g hg hG => ?_⟩` and prove the remaining obligations. Rewrite using `[dLR_conj, Complex.norm_conj]`. Conclude with `hC u w hu hw hl g hg hG`.
-/
theorem scalar_conjugation_transfer : JAScalConj := by
  intro k r Wp Wq _ _ _ _ D Bg φ hφ
  refine ⟨fun g₀ hg₀ => ?_, fun ε hε m => ?_⟩
  · obtain ⟨U, φ', hU, hg, hφ', he⟩ := hφ.1 g₀ hg₀
    refine ⟨U, fun g => conj (φ' g), hU, hg, ?_, fun g hgU hgG => by simp only; rw [he g hgU hgG]⟩
    exact (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp_contDiffOn hφ'
  · obtain ⟨C, hC⟩ := hφ.2 ε hε m
    refine ⟨C, fun u w hu hw hl g hg hG => ?_⟩
    rw [dLR_conj, Complex.norm_conj]
    exact hC u w hu hw hl g hg hG

section real

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
  [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

/- English proof (translation)
Establish `hφc` using `scalar_conjugation_transfer _ _ _ _ (T v).base _ φ hφ`. Use `SSn.real_to_bounded_holds E Wp Wq S T v hPl e Cb (fun g => φ g • ContinuousLinearMap.id ℂ (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (fun g => conj (φ g) • ContinuousLinearMap.id ℂ (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (fun ρ π q => if ρ = π then evD (D.parOf S v) q β else 0) _ hFr ⟨?_, ?_, ?_, …` and prove the remaining obligations. Introduce `x A B'`. Simplify using `only [B.hsInner, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, P.TBBx2.Tri.hsVec_smul, inner_smul_left, inner_smul_right, Complex.conj_conj]`. Introduce `g₀ hg₀`.

Take `⟨U, φ', hU, hg, hφ', he⟩` from `hφ.1 g₀ hg₀`. Conclude with `⟨U, fun g => φ' g • ContinuousLinearMap.id ℂ (Wq (S.pl v) →L[ℂ] Wp (S.pl v)), hU, hg, hφ'.smul contDiffOn_const, fun g hgU hgG => by simp only; rw [he g hgU hgG]⟩`. Introduce `g₀ hg₀`. Take `⟨U, φ', hU, hg, hφ', he⟩` from `hφc.1 g₀ hg₀`. Conclude with `⟨U, fun g => φ' g • ContinuousLinearMap.id ℂ (Wq (S.pl v) →L[ℂ] Wp (S.pl v)), hU, hg, hφ'.smul contDiffOn_const, fun g hgU hgG => by show conj (φ g) • _ = φ' g • _`.

Rewrite using `[show conj (φ g) = φ' g from he g hgU hgG]⟩`. Introduce `p hp g _ X`. Simplify using `only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, hinv p hp g, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]`. Introduce `p hp g _ X`. Simplify using `only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, hinv p hp g, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]`.

Introduce `ε hε m`. Take `⟨C, hC⟩` from `hφ.2 ε hε m`. Use `⟨C, fun u w hu hw hl g hg hG => ?_⟩` and prove the remaining obligations. Rewrite using `[dLR_smulc]`. Conclude with `(norm_smul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le).trans (hC u w hu hw hl g hg hG))`.

Introduce `ε hε m`. Take `⟨C, hC⟩` from `hφc.2 ε hε m`. Use `⟨C, fun u w hu hw hl g hg hG => ?_⟩` and prove the remaining obligations. Rewrite using `[dLR_smulc]`. Conclude with `(norm_smul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le).trans (hC u w hu hw hl g hg hG))`.

Introduce `q hq ρ π`. Simplify using `only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, P.TBBx2.Tri.hsVec_smul, inner_smul_right, (hFr.2 q.2 hq.2).2.1 ρ π, hval q hq]`. Apply the tactic sequence `split_ifs <;> simp`. Introduce `ρ π`. Distinguish the cases in `h : ρ = π`.

Substitute `h` using the available equality. Conclude with `⟨β, by rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq], fun q => by simp⟩`. Use `⟨0, ?_, fun q => by simp [h]⟩` and prove the remaining obligations. Rewrite using `[Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h, cjD_zero, multiplierPair_zero]`.
-/
theorem scal_real (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π')
    (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (hFr : IsFrame S T v e) (Cb : ℝ)
    (φ : B.Mat S.G.k S.G.r → ℂ) (hφ : ScalOK (T v).base (Cb * ((S.G.r : ℝ) + 1)) φ)
    (hinv : ∀ p, (T v).base.inSS p → ∀ g, φ (B.sgs p g) = φ g)
    (β : (DQ (D.parOf S v)).R)
    (hval : ∀ (q : MA.E (D.parOf S v).r) (hq : q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT),
      φ (B.gq (T v).base q) = evD (D.parOf S v) ⟨q, hq⟩ β) :
    BddReal S T v e Cb (Matrix.scalar (M.Ty (D.parOf S v)) ((DQ (D.parOf S v)).fnP β (cjD (D.parOf S v) β))) := by
  have hφc := scalar_conjugation_transfer _ _ _ _ (T v).base _ φ hφ
  refine SSn.real_to_bounded_holds E Wp Wq S T v hPl e Cb
    (fun g => φ g • ContinuousLinearMap.id ℂ (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (fun g => conj (φ g) • ContinuousLinearMap.id ℂ (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (fun ρ π q => if ρ = π then evD (D.parOf S v) q β else 0) _ hFr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_
  · intro x A B'
    simp only [B.hsInner, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      P.TBBx2.Tri.hsVec_smul, inner_smul_left, inner_smul_right, Complex.conj_conj]
  · intro g₀ hg₀
    obtain ⟨U, φ', hU, hg, hφ', he⟩ := hφ.1 g₀ hg₀
    exact ⟨U, fun g => φ' g • ContinuousLinearMap.id ℂ (Wq (S.pl v) →L[ℂ] Wp (S.pl v)), hU, hg,
      hφ'.smul contDiffOn_const, fun g hgU hgG => by simp only; rw [he g hgU hgG]⟩
  · intro g₀ hg₀
    obtain ⟨U, φ', hU, hg, hφ', he⟩ := hφc.1 g₀ hg₀
    exact ⟨U, fun g => φ' g • ContinuousLinearMap.id ℂ (Wq (S.pl v) →L[ℂ] Wp (S.pl v)), hU, hg,
      hφ'.smul contDiffOn_const, fun g hgU hgG => by
        show conj (φ g) • _ = φ' g • _
        rw [show conj (φ g) = φ' g from he g hgU hgG]⟩
  · intro p hp g _ X
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, hinv p hp g,
      ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  · intro p hp g _ X
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, hinv p hp g,
      ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  · intro ε hε m
    obtain ⟨C, hC⟩ := hφ.2 ε hε m
    refine ⟨C, fun u w hu hw hl g hg hG => ?_⟩
    rw [dLR_smulc]
    exact (norm_smul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le).trans
      (hC u w hu hw hl g hg hG))
  · intro ε hε m
    obtain ⟨C, hC⟩ := hφc.2 ε hε m
    refine ⟨C, fun u w hu hw hl g hg hG => ?_⟩
    rw [dLR_smulc]
    exact (norm_smul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le).trans
      (hC u w hu hw hl g hg hG))
  · intro q hq ρ π
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, P.TBBx2.Tri.hsVec_smul,
      inner_smul_right, (hFr.2 q.2 hq.2).2.1 ρ π, hval q hq]
    split_ifs <;> simp
  · intro ρ π
    by_cases h : ρ = π
    · subst h
      exact ⟨β, by rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq], fun q => by simp⟩
    · refine ⟨0, ?_, fun q => by simp [h]⟩
      rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h, cjD_zero, multiplierPair_zero]

end real

section main

/- English proof (translation)
Unfold `phiR`. Rewrite using `[P.BigCellZetaMinors.dmin_sgs D hp, P.BigCellZetaMinors.dmin_sgs D hp]`.
-/
theorem phiR_sgs {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : D.inSS p)
    (g : B.Mat k r) : phiR k r D.z D.z' (B.sgs p g) = phiR k r D.z D.z' g := by
  unfold phiR; rw [P.BigCellZetaMinors.dmin_sgs D hp, P.BigCellZetaMinors.dmin_sgs D hp]

/- English proof (translation)
Unfold `phiD`. Rewrite using `[P.BigCellZetaMinors.dmin_sgs D hp]`.
-/
theorem phiD_sgs {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : D.inSS p)
    (g : B.Mat k r) : phiD k r D.z D.z' (B.sgs p g) = phiD k r D.z D.z' g := by
  unfold phiD; rw [P.BigCellZetaMinors.dmin_sgs D hp]

/- English proof (translation)
Establish `h1 : Dmin k r D.z D.z' (B.gq D q) ⟨r, by omega⟩ = ∏ a, q.1 a`. Use `(bigCellMinors k r D.z D.z' q.1 (D.μsec q.2) D.z_mem D.z'_mem).1 (Fin.last r)` as an intermediate fact. Simplify using `only [Fin.val_last] at this`. Rewrite using `[show B.gq D q = bigCell k r q.1 (D.μsec q.2) from rfl, this]`. Conclude with `Finset.prod_congr (by ext a; simp) fun _ _ => rfl`.

Use `⟨h1, ?_⟩` and prove the remaining obligations. Establish `hz` using `P.BigCellZetaMinors.zeta_gq D hq`. Establish `hne : Dmin k r D.z D.z' (B.gq D q) ⟨r, by omega⟩ ≠ 0`. Rewrite using `[h1]`. Conclude with `Finset.prod_ne_zero_iff.2 fun a _ => hq.1 a`.

Unfold `zeta at hz`. Rewrite using `[← hz, ← h1, div_mul_cancel₀ _ hne]`.
-/
theorem dmin_gq {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) {q : (Fin r → ℂ) × ℂ}
    (hq : q ∈ JF.QDom k r D.z D.z') :
    Dmin k r D.z D.z' (B.gq D q) ⟨r, by omega⟩ = ∏ a, q.1 a ∧
      Dmin k r D.z D.z' (B.gq D q) (Fin.last (r + 1)) = q.2 * ∏ a, q.1 a := by
  have h1 : Dmin k r D.z D.z' (B.gq D q) ⟨r, by omega⟩ = ∏ a, q.1 a := by
    have := (bigCellMinors k r D.z D.z' q.1 (D.μsec q.2) D.z_mem D.z'_mem).1 (Fin.last r)
    simp only [Fin.val_last] at this
    rw [show B.gq D q = bigCell k r q.1 (D.μsec q.2) from rfl, this]
    exact Finset.prod_congr (by ext a; simp) fun _ _ => rfl
  refine ⟨h1, ?_⟩
  have hz := P.BigCellZetaMinors.zeta_gq D hq
  have hne : Dmin k r D.z D.z' (B.gq D q) ⟨r, by omega⟩ ≠ 0 := by
    rw [h1]; exact Finset.prod_ne_zero_iff.2 fun a _ => hq.1 a
  unfold zeta at hz
  rw [← hz, ← h1, div_mul_cancel₀ _ hne]

/- English proof (translation)
Take `⟨K, hK0, hK⟩` from `scalar_transfer_bound_holds`. Use `⟨K, hK0, fun Cc Cb _ hCb E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr _ hL b hb => ?_⟩` and prove the remaining obligations. Establish `hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π'` using `(hB.1.2.2.2.1.2 v).2.2.2.1`. Establish `hT : Tz S.G.k S.G.r (T v).base.z = S.T` using `hPl.2.2.2.1`. Establish `hT' : Tz S.G.k S.G.r (T v).base.z' = S.T'` using `hPl.2.2.2.2.1`.

Establish `hTT : Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' = (D.parOf S v).TT`. Rewrite using `[hT, hT']`. Both sides reduce to the same expression. Establish `hTpos : 0 < (D.parOf S v).TT`. Rewrite using `[← hTT]`.

Conclude with `mul_pos (T v).base.T_pos (T v).base.T'_pos`. Establish `hT0` using `hTpos.le`. Establish `hQD : ∀ q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, q ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z'` using `fun q hq => ⟨hq.1, by rw [hTT]; exact hq.2⟩`. Establish `hBg : K * ((S.G.r : ℝ) + 1) ≤ Cb * ((S.G.r : ℝ) + 1)` using `mul_le_mul_of_nonneg_right hCb (by positivity)`. Take `⟨hR, hD⟩` from `hK S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base _ hBg`.

Establish `hRc` using `scalar_conjugation_transfer _ _ _ _ (T v).base _ _ hR`. Establish `hDc` using `scalar_conjugation_transfer _ _ _ _ (T v).base _ _ hD`. Take `⟨-, -, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, -, -, -, -, -⟩` from `hL`. Establish `vR : ∀ q (hq : q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT), phiR S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base q) = (q.2)⁻¹` using `fun q hq => by`. Establish `hz'` using `P.BigCellZetaMinors.zeta_gq (T v).base (hQD q hq)`.

Unfold `zeta at hz'`. Unfold `phiR`. Rewrite using `[← hz', inv_div]`. Establish `vD : ∀ q (hq : q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT), phiD S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base q) = (∏ a, q.1 a) * q.2 * ((conj q.2)⁻¹ * ∏ a, (conj (q.1 a))⁻¹)` using `fun q hq => by`. Establish `h` using `(dmin_gq (T v).base (hQD q hq)).2`.

Establish `hz0 : q.2 ≠ 0` using `BStar.z_ne hT0 ⟨q, hq⟩`. Establish `hc0 : ∀ a, q.1 a ≠ 0` using `hq.1`. Unfold `phiD`. Rewrite using `[h, map_mul, map_prod, Finset.prod_inv_distrib, div_eq_mul_inv, mul_inv]`. Expand and normalize the polynomial expressions, which then agree.

Break down `hb with rfl | rfl | rfl | rfl` into its components or cases. Rewrite using `[BStar.rep_zi hzi, ← BStar.cjD_izi hT0]`. Use `scal_real S T v hPl e hFr Cb _ hR (fun p hp g => phiR_sgs _ hp g) _ fun q hq => ?_` and prove the remaining obligations. Rewrite using `[vR q hq, BStar.evD_inv _ hT0, coordE_vz]`. Rewrite using `[BStar.rep_zbi hzbi, ← BStar.cjD_izbi hT0]`.

Use `scal_real S T v hPl e hFr Cb _ hRc (fun p hp g => by simp only [phiR_sgs _ hp g]) _ fun q hq => ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[vR q hq, BStar.evD_inv _ hT0, coordE_vzb, map_inv₀]`. Establish `e1 : L.D * L.Dbi = Matrix.scalar (M.Ty (D.parOf S v)) ((DQ (D.parOf S v)).fnP (βD (D.parOf S v)) (βDb (D.parOf S v)))`. Rewrite using `[LevelData.D, LevelData.Dbi, rep_Dr hc, zeta_eq_scalar_matrix hz, rep_zbi hzbi, rep_Drbi hcbi, scalar_mul_fnP, scalar_mul_fnP, scalar_mul_fnP]`.

Both sides reduce to the same expression. Rewrite using `[e1, ← BStar.cjD_βD hT0]`. Use `scal_real S T v hPl e hFr Cb _ hD (fun p hp g => phiD_sgs _ hp g) _ fun q hq => ?_` and prove the remaining obligations. Rewrite using `[vD q hq]`. Simplify using `only [βD, map_mul, map_prod, evaluation_of_coordinate_variable, BStar.evD_inv _ hT0, coordE_vc, coordE_vcb, coordE_vz, coordE_vzb]`.

Establish `e2 : L.Db * L.Di = Matrix.scalar (M.Ty (D.parOf S v)) ((DQ (D.parOf S v)).fnP (βDb (D.parOf S v)) (βD (D.parOf S v)))`. Rewrite using `[LevelData.Db, LevelData.Di, rep_Drb hcb, rep_zb hzb, rep_zi hzi, rep_Dri hci, scalar_mul_fnP, scalar_mul_fnP, scalar_mul_fnP]`. Both sides reduce to the same expression. Rewrite using `[e2, ← BStar.cjD_βDb hT0]`. Use `scal_real S T v hPl e hFr Cb _ hDc (fun p hp g => by simp only [phiD_sgs _ hp g]) _ fun q hq => ?_` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[vD q hq, ← BStar.cjD_βD hT0, evD_cjD]`. Simplify using `only [βD, map_mul, map_prod, evaluation_of_coordinate_variable, BStar.evD_inv _ hT0, coordE_vc, coordE_vcb, coordE_vz, coordE_vzb]`.
-/
theorem bounded_scalar_transfer_holds : JABddScal := by
  obtain ⟨K, hK0, hK⟩ := scalar_transfer_bound_holds
  refine ⟨K, hK0, fun Cc Cb _ hCb E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr _ hL b hb => ?_⟩
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hT : Tz S.G.k S.G.r (T v).base.z = S.T := hPl.2.2.2.1
  have hT' : Tz S.G.k S.G.r (T v).base.z' = S.T' := hPl.2.2.2.2.1
  have hTT : Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' = (D.parOf S v).TT := by
    rw [hT, hT']; rfl
  have hTpos : 0 < (D.parOf S v).TT := by
    rw [← hTT]; exact mul_pos (T v).base.T_pos (T v).base.T'_pos
  have hT0 := hTpos.le
  have hQD : ∀ q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, q ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' :=
    fun q hq => ⟨hq.1, by rw [hTT]; exact hq.2⟩
  have hBg : K * ((S.G.r : ℝ) + 1) ≤ Cb * ((S.G.r : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right hCb (by positivity)
  obtain ⟨hR, hD⟩ := hK S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base _ hBg
  have hRc := scalar_conjugation_transfer _ _ _ _ (T v).base _ _ hR
  have hDc := scalar_conjugation_transfer _ _ _ _ (T v).base _ _ hD
  obtain ⟨-, -, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, -, -, -, -, -⟩ := hL

  have vR : ∀ q (hq : q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT),
      phiR S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base q) = (q.2)⁻¹ := fun q hq => by
    have hz' := P.BigCellZetaMinors.zeta_gq (T v).base (hQD q hq)
    unfold zeta at hz'
    unfold phiR
    rw [← hz', inv_div]
  have vD : ∀ q (hq : q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT),
      phiD S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base q) =
        (∏ a, q.1 a) * q.2 * ((conj q.2)⁻¹ * ∏ a, (conj (q.1 a))⁻¹) := fun q hq => by
    have h := (dmin_gq (T v).base (hQD q hq)).2
    have hz0 : q.2 ≠ 0 := BStar.z_ne hT0 ⟨q, hq⟩
    have hc0 : ∀ a, q.1 a ≠ 0 := hq.1
    unfold phiD
    rw [h, map_mul, map_prod, Finset.prod_inv_distrib, div_eq_mul_inv, mul_inv]
    ring
  rcases hb with rfl | rfl | rfl | rfl
  · rw [BStar.rep_zi hzi, ← BStar.cjD_izi hT0]
    refine scal_real S T v hPl e hFr Cb _ hR (fun p hp g => phiR_sgs _ hp g) _ fun q hq => ?_
    rw [vR q hq, BStar.evD_inv _ hT0, coordE_vz]
  · rw [BStar.rep_zbi hzbi, ← BStar.cjD_izbi hT0]
    refine scal_real S T v hPl e hFr Cb _ hRc (fun p hp g => by simp only [phiR_sgs _ hp g]) _ fun q hq => ?_
    simp only
    rw [vR q hq, BStar.evD_inv _ hT0, coordE_vzb, map_inv₀]
  · have e1 : L.D * L.Dbi = Matrix.scalar (M.Ty (D.parOf S v))
        ((DQ (D.parOf S v)).fnP (βD (D.parOf S v)) (βDb (D.parOf S v))) := by
      rw [LevelData.D, LevelData.Dbi, rep_Dr hc, zeta_eq_scalar_matrix hz, rep_zbi hzbi, rep_Drbi hcbi, scalar_mul_fnP,
        scalar_mul_fnP, scalar_mul_fnP]; rfl
    rw [e1, ← BStar.cjD_βD hT0]
    refine scal_real S T v hPl e hFr Cb _ hD (fun p hp g => phiD_sgs _ hp g) _ fun q hq => ?_
    rw [vD q hq]
    simp only [βD, map_mul, map_prod, evaluation_of_coordinate_variable, BStar.evD_inv _ hT0, coordE_vc, coordE_vcb, coordE_vz, coordE_vzb]
  · have e2 : L.Db * L.Di = Matrix.scalar (M.Ty (D.parOf S v))
        ((DQ (D.parOf S v)).fnP (βDb (D.parOf S v)) (βD (D.parOf S v))) := by
      rw [LevelData.Db, LevelData.Di, rep_Drb hcb, rep_zb hzb, rep_zi hzi, rep_Dri hci, scalar_mul_fnP,
        scalar_mul_fnP, scalar_mul_fnP]; rfl
    rw [e2, ← BStar.cjD_βDb hT0]
    refine scal_real S T v hPl e hFr Cb _ hDc (fun p hp g => by simp only [phiD_sgs _ hp g]) _ fun q hq => ?_
    simp only
    rw [vD q hq, ← BStar.cjD_βD hT0, evD_cjD]
    simp only [βD, map_mul, map_prod, evaluation_of_coordinate_variable, BStar.evD_inv _ hT0, coordE_vc, coordE_vcb, coordE_vz, coordE_vzb]

end main

end

end Formalism.FourierDecayAlt.P.CutMP.JA
