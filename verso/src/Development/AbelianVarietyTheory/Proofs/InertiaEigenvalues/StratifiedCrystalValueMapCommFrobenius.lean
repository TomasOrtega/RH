import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FramedCrystalFrobeniusCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrismCoverReceivingBreuilKisinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveAndRangeOfPrismCoverStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinHomEisensteinSpanAndNonZeroDivisorStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Establish `e1 : (fun i => φ (Y.mulVec u i)) = (Y.map φ).mulVec fun i => φ (u i)`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct]`. Rewrite `h2` using `[e1, Matrix.mulVec_mulVec]`. Establish `h3` using `congrArg Y.mulVec h1`.

Rewrite `h3` using `[Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_zero]`. Establish `h4` using `congrArg (fun Z => Matrix.mulVec Z fun i => φ (u i)) hY`. Simplify using `only [Matrix.smul_mulVec] at h4`. Use function extensionality and compare the values at `i`. Establish `h2i` using `congrFun h2 i`.

Establish `h3i` using `congrFun h3 i`. Establish `h4i` using `congrFun h4 i`. Simplify using `only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at h2i h3i h4i ⊢`. Rewrite using `[← sub_eq_zero]`. Use `(mem_nonZeroDivisors_iff.1 (pow_mem hE (a + a'))).1 _ ?_` and prove the remaining obligations.

Take the linear combination `(T ^ r * T ^ k * E ^ a) * h2i - (T ^ r' * T ^ j * E ^ a') * h3i + T ^ (r + r' + k + j) * h4i`.
-/
theorem frob_coord_compat {C : Type} [CommRing C] {d d' : ℕ} (φ : C →+* C) (E T : C) (hE : E ∈ nonZeroDivisors C)
    (A : Matrix (Fin d) (Fin d) C) (A' : Matrix (Fin d') (Fin d') C) (Y : Matrix (Fin d') (Fin d) C)
    (a a' r r' k j : ℕ) (hY : E ^ a • (A' * Y.map φ) = E ^ a' • (Y * A)) (u m : Fin d → C) (n : Fin d' → C)
    (h1 : T ^ r • (E ^ a • m - T ^ k • A.mulVec fun i => φ (u i)) = 0)
    (h2 : T ^ r' • (E ^ a' • n - T ^ j • A'.mulVec fun i => φ (Y.mulVec u i)) = 0) :
    T ^ (r + r') • (T ^ k • n) = T ^ (r + r') • (T ^ j • Y.mulVec m) := by
  have e1 : (fun i => φ (Y.mulVec u i)) = (Y.map φ).mulVec fun i => φ (u i) := by
    funext i
    simp [Matrix.mulVec, dotProduct]
  rw [e1, Matrix.mulVec_mulVec] at h2
  have h3 := congrArg Y.mulVec h1
  rw [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    Matrix.mulVec_zero] at h3
  have h4 := congrArg (fun Z => Matrix.mulVec Z fun i => φ (u i)) hY
  simp only [Matrix.smul_mulVec] at h4
  funext i
  have h2i := congrFun h2 i
  have h3i := congrFun h3 i
  have h4i := congrFun h4 i
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at h2i h3i h4i ⊢
  rw [← sub_eq_zero]
  refine (mem_nonZeroDivisors_iff.1 (pow_mem hE (a + a'))).1 _ ?_
  linear_combination (T ^ r * T ^ k * E ^ a) * h2i - (T ^ r' * T ^ j * E ^ a') * h3i +
    T ^ (r + r' + k + j) * h4i

/- English proof (translation)
Introduce `l _ K bk d d' S S' M e M' e' hF hF' Y hY B V V' hV hV' w hw t x m k hx`. Use `(GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B).elim fun C hC => hC.elim fun h hC => hC.1.elim fun g => ?_` and prove the remaining obligations. Establish `hc` using `hC.2`. Establish `hinj` using `(GlobalTheory.T.injective_and_range_of_prism_cover l K bk d' S' B C (M'.M B) V' h g hc).1`. Establish `hE` using `(GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk C g).2`.

Establish `hnj : ∃ n j, IsFrac (t : B.A) (M'.Φ B t (w x)) n j`. Proceed by induction on `M'.Φ B t (w x) using LocalizedModule.induction_on with`. Consider the case `h n s`. Take `⟨_, j, rfl⟩` from `s`. Conclude with `⟨n, j, rfl⟩`.

Use `hnj.elim fun n hn => hn.elim fun j hn => ?_` and prove the remaining obligations. Use `(GlobalTheory.T.framedCrystal_frobenius_coordinates l K bk d S M e hF B V hV t x m k hx C h g).elim fun r h1 => ?_` and prove the remaining obligations. Use `(GlobalTheory.T.framedCrystal_frobenius_coordinates l K bk d' S' M' e' hF' B V' hV' t (w x) n j hn C h g).elim fun r' h2 => ?_` and prove the remaining obligations. Rewrite `h2` using `[hw]`. Establish `hY' : BK.hf g bk.E ^ S.a • (S'.A.map (BK.hf g) * (Y.map (BK.hf g)).map C.D.φ) = BK.hf g bk.E ^ S'.a • (Y.map (BK.hf g) * S.A.map (BK.hf g))`.

Establish `e1 : (Y.map (BK.hf g)).map C.D.φ = (Y.map (frobS l bk.a)).map (BK.hf g)`. Use extensionality with `i j`. Conclude with `(g.f_φ (Y i j)).symm`. Rewrite using `[e1, ← Matrix.map_mul, ← Matrix.map_mul]`. Use extensionality with `i j`.

Establish `h5` using `congrArg (BK.hf g) (congrFun (congrFun hY.φ i) j)`. Simplify `h5` using `only [Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, Matrix.map_apply]`. Establish `key` using `frob_coord_compat C.D.φ _ _ hE _ _ _ _ _ _ _ _ _ hY' _ _ _ h1 h2`. Unfold `IsFrac at hn ⊢`. Rewrite using `[hn, LocalizedModule.mk_eq]`.

Use `⟨⟨(t : B.A) ^ (r + r'), r + r', rfl⟩, hinj ?_⟩` and prove the remaining obligations. Simplify using `only [Submonoid.smul_def, LinearMap.map_smulₛₗ, map_pow, hw]`. Conclude with `key`.
-/
theorem eval_map_Φ : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) (M' : FCrys l ↥(OL K)) (e' : Module.Basis (Fin d') bk.prism.A (M'.M bk.prism)), Framed S M e → Framed S' M' e' → ∀ Y : Matrix (Fin d') (Fin d) bk.S, IsStratHom S S' Y → ∀ (B : Obj l ↥(OL K)) (V : Eval S B (M.M B)) (V' : Eval S' B (M'.M B)), IsCoord e V → IsCoord e' V' → ∀ w : M.M B →ₗ[B.A] M'.M B, (∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q) (x : M.M B), V'.v a g (w x) = (Y.map (BK.hf g)).mulVec (V.v a g x)) → ∀ (t : ↥B.I) (x m : M.M B) (k : ℕ), IsFrac (t : B.A) (M.Φ B t x) m k → IsFrac (t : B.A) (M'.Φ B t (w x)) (w m) k := by
  intro l _ K bk d d' S S' M e M' e' hF hF' Y hY B V V' hV hV' w hw t x m k hx
  refine (GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B).elim fun C hC => hC.elim fun h hC => hC.1.elim fun g => ?_
  have hc := hC.2
  have hinj := (GlobalTheory.T.injective_and_range_of_prism_cover l K bk d' S' B C (M'.M B) V' h g hc).1
  have hE := (GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk C g).2
  have hnj : ∃ n j, IsFrac (t : B.A) (M'.Φ B t (w x)) n j := by
    induction M'.Φ B t (w x) using LocalizedModule.induction_on with
    | h n s =>
      obtain ⟨_, j, rfl⟩ := s
      exact ⟨n, j, rfl⟩
  refine hnj.elim fun n hn => hn.elim fun j hn => ?_
  refine (GlobalTheory.T.framedCrystal_frobenius_coordinates l K bk d S M e hF B V hV t x m k hx C h g).elim fun r h1 => ?_
  refine (GlobalTheory.T.framedCrystal_frobenius_coordinates l K bk d' S' M' e' hF' B V' hV' t (w x) n j hn C h g).elim fun r' h2 => ?_
  rw [hw] at h2
  have hY' : BK.hf g bk.E ^ S.a • (S'.A.map (BK.hf g) * (Y.map (BK.hf g)).map C.D.φ) =
      BK.hf g bk.E ^ S'.a • (Y.map (BK.hf g) * S.A.map (BK.hf g)) := by
    have e1 : (Y.map (BK.hf g)).map C.D.φ = (Y.map (frobS l bk.a)).map (BK.hf g) := by
      ext i j
      exact (g.f_φ (Y i j)).symm
    rw [e1, ← Matrix.map_mul, ← Matrix.map_mul]
    ext i j
    have h5 := congrArg (BK.hf g) (congrFun (congrFun hY.φ i) j)
    simpa only [Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, Matrix.map_apply] using h5
  have key := frob_coord_compat C.D.φ _ _ hE _ _ _ _ _ _ _ _ _ hY' _ _ _ h1 h2
  unfold IsFrac at hn ⊢
  rw [hn, LocalizedModule.mk_eq]
  refine ⟨⟨(t : B.A) ^ (r + r'), r + r', rfl⟩, hinj ?_⟩
  simp only [Submonoid.smul_def, LinearMap.map_smulₛₗ, map_pow, hw]
  exact key

end GlobalTheory.BSP
