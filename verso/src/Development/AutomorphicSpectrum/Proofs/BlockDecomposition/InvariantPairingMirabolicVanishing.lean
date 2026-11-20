import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicFourierExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCharacterEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGlLastRowEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedKernelConjugation

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

namespace GlobalTheory.CompanionTheory.MirPsiPair

section Det

variable {k : Type} [Field k]

/- English proof (translation)
Establish `hsub : (glEmbMat k n A).submatrix Fin.castSucc Fin.castSucc = A`. Use extensionality with `i j`. Simplify using `[glEmbMat]`. Rewrite using `[Matrix.det_succ_row _ (Fin.last n), Fin.sum_univ_castSucc]`. Simplify using `[glEmbMat, hsub]`.
-/
theorem det_glEmbMat (n : ℕ) (A : Matrix (Fin n) (Fin n) k) : (glEmbMat k n A).det = A.det := by
  have hsub : (glEmbMat k n A).submatrix Fin.castSucc Fin.castSucc = A := by
    ext i j
    simp [glEmbMat]
  rw [Matrix.det_succ_row _ (Fin.last n), Fin.sum_univ_castSucc]
  simp [glEmbMat, hsub]

/- English proof (translation)
Establish `htri : (((unip k n v : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)).BlockTriangular id`. Introduce `i j hij`. Establish `hij' : j < i` using `hij`. Establish `hj : j ≠ Fin.last n` using `fun h => by`. Substitute `h` using the available equality.

Conclude with `absurd hij' (not_lt.2 (Fin.le_last i))`. Simplify using `[unip, colMat, hj, one_apply, hij'.ne']`. Rewrite using `[Matrix.det_of_upperTriangular htri]`. Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Proceed by induction on `i using Fin.lastCases with`.

Consider the case `last => simp [unip, colMat]`. Consider the case `cast i => simp [unip, colMat, Fin.castSucc_ne_last]`.
-/
theorem det_unip (n : ℕ) (v : Multiplicative (Fin n → k)) :
    ((unip k n v : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k).det = 1 := by
  have htri : (((unip k n v : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)).BlockTriangular id := by
    intro i j hij
    have hij' : j < i := hij
    have hj : j ≠ Fin.last n := fun h => by
      subst h
      exact absurd hij' (not_lt.2 (Fin.le_last i))
    simp [unip, colMat, hj, one_apply, hij'.ne']
  rw [Matrix.det_of_upperTriangular htri]
  refine Finset.prod_eq_one fun i _ => ?_
  induction i using Fin.lastCases with
  | last => simp [unip, colMat]
  | cast i => simp [unip, colMat, Fin.castSucc_ne_last]

end Det

section Fix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use extensionality with `u`. Simplify using `[thetaA, chrA]`.
-/
theorem thetaA_zero (ψ : AddChar k Circle) (n : ℕ) : thetaA k ψ (0 : Fin n → k) = 1 := by
  ext u
  simp [thetaA, chrA]

/- English proof (translation)
Establish `htop : twKer T (MirUin k (n + 1)) (mirChar k ψ n) = ⊤` using `(Submodule.eq_top_iff' ).2 fun x => (Submodule.Quotient.mk_eq_zero _).1 (Subsingleton.elim _ _)`. Establish `hall : ∀ a : Fin (n + 1) → k, T (u : Mir k (n + 1)) v - v ∈ twKer T (MirUin k (n + 1)) (thetaA k ψ a)`. Introduce `a`. Distinguish the cases in `ha : a = 0`. Substitute `ha` using the available equality.

Rewrite using `[thetaA_zero]`. Conclude with `Submodule.subset_span ⟨u, v, by simp⟩`. Take `⟨m, hm⟩` from `GlobalTheory.CompanionTheory.LinAlg.exists_GL_lastRow_eq k n a ha`. Rewrite using `[← hm]`. Use `(GlobalTheory.CompanionTheory.BZMirabolic.twKerConj k ψ (n + 1) V T (Pi.single (Fin.last n) 1) m _).2 ?_` and prove the remaining obligations.

Rewrite using `[← GlobalTheory.CompanionTheory.BZMir.mirChar_eq_thetaA_single k ψ n, htop]`. Discharge the goal by the elementary cases of `trivial`. Conclude with `sub_eq_zero.1 (GlobalTheory.CompanionTheory.MirFourier.fourier k ψ hψ h1 (n + 1) V T hT _ hall)`.
-/
theorem unip_fixes (ψ : AddChar k Circle) (hψ : Continuous ψ) (h1 : ψ ≠ 1) (n : ℕ) {V : Type}
    [AddCommGroup V] [Module ℂ V] (T : Representation ℂ (Mir k (n + 1)) V) (hT : IsSmooth T)
    (hsub : Subsingleton (TwJacquet T (MirUin k (n + 1)) (mirChar k ψ n)))
    (u : MirUin k (n + 1)) (v : V) : T (u : Mir k (n + 1)) v = v := by
  have htop : twKer T (MirUin k (n + 1)) (mirChar k ψ n) = ⊤ :=
    (Submodule.eq_top_iff' ).2 fun x => (Submodule.Quotient.mk_eq_zero _).1 (Subsingleton.elim _ _)
  have hall : ∀ a : Fin (n + 1) → k,
      T (u : Mir k (n + 1)) v - v ∈ twKer T (MirUin k (n + 1)) (thetaA k ψ a) := by
    intro a
    by_cases ha : a = 0
    · subst ha
      rw [thetaA_zero]
      exact Submodule.subset_span ⟨u, v, by simp⟩
    · obtain ⟨m, hm⟩ := GlobalTheory.CompanionTheory.LinAlg.exists_GL_lastRow_eq k n a ha
      rw [← hm]
      refine (GlobalTheory.CompanionTheory.BZMirabolic.twKerConj k ψ (n + 1) V T (Pi.single (Fin.last n) 1) m _).2 ?_
      rw [← GlobalTheory.CompanionTheory.BZMir.mirChar_eq_thetaA_single k ψ n, htop]
      trivial
  exact sub_eq_zero.1 (GlobalTheory.CompanionTheory.MirFourier.fourier k ψ hψ h1 (n + 1) V T hT _ hall)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem psiMinus_mk {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k n) V)
    (g : GL (Fin n) k) (v : V) :
    psiMinus k τ g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (τ (levi k n g) v) := rfl

/- English proof (translation)
Take `⟨v, hv⟩` from `(u.2 : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)`. Establish `hdet : Matrix.GeneralLinearGroup.det ((u : Mir k n) : GL (Fin (n + 1)) k) = 1`. Establish `hv' : ((u : Mir k n) : GL (Fin (n + 1)) k) = unip k n v` using `hv.symm`. Use `ext`. Rewrite using `[hv']`.

Simplify using `using det_unip n v`. Rewrite using `[detChar_apply, hdet, map_one]`.
-/
theorem detChar_unip (χ : kˣ →* ℂˣ) (n : ℕ) (u : MirUin k n) :
    detChar (Fin (n + 1)) χ ((u : Mir k n) : GL (Fin (n + 1)) k) = 1 := by
  obtain ⟨v, hv⟩ := (u.2 : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  have hdet : Matrix.GeneralLinearGroup.det ((u : Mir k n) : GL (Fin (n + 1)) k) = 1 := by
    have hv' : ((u : Mir k n) : GL (Fin (n + 1)) k) = unip k n v := hv.symm
    ext
    rw [hv']
    simpa using det_unip n v
  rw [detChar_apply, hdet, map_one]

/- English proof (translation)
Establish `hdet : Matrix.GeneralLinearGroup.det ((levi k n g : Mir k n) : GL (Fin (n + 1)) k) = Matrix.GeneralLinearGroup.det g`. Use `ext`. Conclude with `det_glEmbMat n (g : Matrix (Fin n) (Fin n) k)`. Rewrite using `[detChar_apply, detChar_apply, hdet]`.
-/
theorem detChar_levi (χ : kˣ →* ℂˣ) (n : ℕ) (g : GL (Fin n) k) :
    detChar (Fin (n + 1)) χ ((levi k n g : Mir k n) : GL (Fin (n + 1)) k) = detChar (Fin n) χ g := by
  have hdet : Matrix.GeneralLinearGroup.det ((levi k n g : Mir k n) : GL (Fin (n + 1)) k) =
      Matrix.GeneralLinearGroup.det g := by
    ext
    exact det_glEmbMat n (g : Matrix (Fin n) (Fin n) k)
  rw [detChar_apply, detChar_apply, hdet]

end Fix

section Descent

variable {G V V' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

/- English proof (translation)
Establish `hR : twKer T' N 1 ≤ LinearMap.ker B.flip`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `w ⟨u, x, rfl⟩`. Use `LinearMap.mem_ker.2 (LinearMap.ext fun v => ?_)` and prove the remaining obligations. Simplify using `[hinv u v x]`.

Set `Bq` to `(twKer T' N 1).liftQ B.flip hR`. Establish `hL : twKer T N 1 ≤ LinearMap.ker Bq.flip`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `w ⟨u, x, rfl⟩`. Simplify using `[hfix u x]`.

Conclude with `⟨(twKer T N 1).liftQ Bq.flip hL, fun v v' => rfl⟩`.
-/
theorem exists_descent (N : Subgroup G) (T : Representation ℂ G V) (T' : Representation ℂ G V')
    (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (hfix : ∀ (u : N) v, T (u : G) v = v)
    (hinv : ∀ (u : N) v x, B v (T' (u : G) x) = B v x) :
    ∃ B' : TwJacquet T N 1 →ₗ[ℂ] TwJacquet T' N 1 →ₗ[ℂ] ℂ,
      ∀ v v', B' (Submodule.Quotient.mk v) (Submodule.Quotient.mk v') = B v v' := by
  have hR : twKer T' N 1 ≤ LinearMap.ker B.flip := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨u, x, rfl⟩
    refine LinearMap.mem_ker.2 (LinearMap.ext fun v => ?_)
    simp [hinv u v x]
  let Bq := (twKer T' N 1).liftQ B.flip hR
  have hL : twKer T N 1 ≤ LinearMap.ker Bq.flip := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨u, x, rfl⟩
    simp [hfix u x]
  exact ⟨(twKer T N 1).liftQ Bq.flip hL, fun v v' => rfl⟩

end Descent

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `k _ _ _ _ ψ hψ h1 n s V V' _ _ _ _ T T' hT _ B hB hnd hsub`. Establish `hfix` using `unip_fixes ψ hψ h1 n T hT hsub`. Establish `hinv : ∀ (u : MirUin k (n + 1)) v x, B v (T' (u : Mir k (n + 1)) x) = B v x`. Introduce `u v x`. Establish `h` using `hB (u : Mir k (n + 1)) v x`.

Rewrite `h` using `[hfix u v, detChar_unip]`. Simplify using `using h`. Take `⟨B', hB'⟩` from `exists_descent (MirUin k (n + 1)) T T' B hfix hinv`. Use `⟨B', ?_, ?_⟩` and prove the remaining obligations. Introduce `g w w'`.

Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ w`. Take `⟨v', rfl⟩` from `Submodule.Quotient.mk_surjective _ w'`. Establish `h` using `hB (levi k (n + 1) g) v v'`. Rewrite `h` using `[detChar_levi]`. Rewrite using `[psiMinus_mk, psiMinus_mk, hB', hB', h]`.

Introduce `w hw`. Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ w`. Establish `hv : v ≠ 0` using `fun h => hw (by rw [h]; exact Submodule.Quotient.mk_zero _)`. Take `⟨v', hv'⟩` from `hnd v hv`. Conclude with `⟨Submodule.Quotient.mk v', by rw [hB']; exact hv'⟩`.
-/
theorem pair_psi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n s : ℕ) (V V' : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V'),
    IsSmooth T → IsSmooth T' → ∀ B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ,
    (∀ (p : Mir k (n + 1)) v v', B (T p v) (T' p v') =
      ((detChar (Fin (n + 1 + 1)) (absPow k (s : ℂ)) (p : GL (Fin (n + 1 + 1)) k) : ℂˣ) : ℂ) * B v v') →
    (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) →
    Subsingleton (TwJacquet T (MirUin k (n + 1)) (mirChar k ψ n)) →
    ∃ B' : TwJacquet T (MirUin k (n + 1)) 1 →ₗ[ℂ] TwJacquet T' (MirUin k (n + 1)) 1 →ₗ[ℂ] ℂ,
      (∀ (g : GL (Fin (n + 1)) k) w w', B' (psiMinus k T g w) (psiMinus k T' g w') =
        ((detChar (Fin (n + 1)) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) * B' w w') ∧
      (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0) := by
  intro k _ _ _ _ ψ hψ h1 n s V V' _ _ _ _ T T' hT _ B hB hnd hsub
  have hfix := unip_fixes ψ hψ h1 n T hT hsub

  have hinv : ∀ (u : MirUin k (n + 1)) v x, B v (T' (u : Mir k (n + 1)) x) = B v x := by
    intro u v x
    have h := hB (u : Mir k (n + 1)) v x
    rw [hfix u v, detChar_unip] at h
    simpa using h
  obtain ⟨B', hB'⟩ := exists_descent (MirUin k (n + 1)) T T' B hfix hinv
  refine ⟨B', ?_, ?_⟩
  · intro g w w'
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    obtain ⟨v', rfl⟩ := Submodule.Quotient.mk_surjective _ w'
    have h := hB (levi k (n + 1) g) v v'
    rw [detChar_levi] at h
    rw [psiMinus_mk, psiMinus_mk, hB', hB', h]
  · intro w hw
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    have hv : v ≠ 0 := fun h => hw (by rw [h]; exact Submodule.Quotient.mk_zero _)
    obtain ⟨v', hv'⟩ := hnd v hv
    exact ⟨Submodule.Quotient.mk v', by rw [hB']; exact hv'⟩

end GlobalTheory.CompanionTheory.MirPsiPair

end
