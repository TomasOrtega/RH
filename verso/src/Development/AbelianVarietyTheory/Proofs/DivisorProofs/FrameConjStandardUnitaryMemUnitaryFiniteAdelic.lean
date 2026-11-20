import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrConjApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

noncomputable section

namespace GlobalTheory.FrameTransport

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, h]`.
-/
theorem cT_map' {A B : Type} [CommRing A] [CommRing B] {m p : Type} (s : A →+* A) (t : B →+* B) (ι : A →+* B)
    (h : ∀ a, t (ι a) = ι (s a)) (M : Matrix m p A) :
    Formalism.UG.cT t (M.map ι) = (Formalism.UG.cT s M).map ι := by
  ext i j
  simp [Formalism.UG.cT, h]

/- English proof (translation)
Establish `hJ : J = Formalism.UG.cT s Q * Q`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hPQ, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]`. Use `_ = Formalism.UG.cT s Q * (Formalism.UG.cT s P * J * P) * Q := by`. Rewrite using `[Formalism.UG.cT_mul]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = Formalism.UG.cT s Q * Q := by rw [hfr, Matrix.mul_one]`. Establish `hHu : Formalism.UG.cT u (H.map φ) * H.map φ = 1`. Rewrite using `[cT_map' t u φ hφ, ← Matrix.map_mul, hH, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hQP' : Q.map ι * P.map ι = 1`.

Rewrite using `[← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hPQc : Formalism.UG.cT u (P.map ι) * Formalism.UG.cT u (Q.map ι) = 1`. Rewrite using `[← Formalism.UG.cT_mul, hQP', Formalism.UG.cT_one]`. Establish `hJ' : J.map ι = Formalism.UG.cT u (Q.map ι) * Q.map ι`. Rewrite using `[hJ, Matrix.map_mul, cT_map' s u ι hι]`.

Rewrite using `[hJ']`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Formalism.UG.cT_mul, Formalism.UG.cT_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Formalism.UG.cT u (Q.map ι) * Q.map ι := by`.

Rewrite using `[hPQc, hQP', Matrix.mul_one, Matrix.mul_one, hHu, Matrix.mul_one]`.
-/
theorem conj_unitary {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {n : Type} [Fintype n] [DecidableEq n]
    (s : A →+* A) (t : C →+* C) (u : B →+* B) (ι : A →+* B) (φ : C →+* B)
    (hι : ∀ a, u (ι a) = ι (s a)) (hφ : ∀ c, u (φ c) = φ (t c))
    (P Q J : Matrix n n A) (H : Matrix n n C) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hfr : Formalism.UG.cT s P * J * P = 1) (hH : Formalism.UG.cT t H * H = 1) :
    Formalism.UG.cT u (P.map ι * H.map φ * Q.map ι) * J.map ι * (P.map ι * H.map φ * Q.map ι) = J.map ι := by
  have hJ : J = Formalism.UG.cT s Q * Q := by
    calc J = Formalism.UG.cT s (P * Q) * J * (P * Q) := by
            rw [hPQ, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
      _ = Formalism.UG.cT s Q * (Formalism.UG.cT s P * J * P) * Q := by
            rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT s Q * Q := by rw [hfr, Matrix.mul_one]
  have hHu : Formalism.UG.cT u (H.map φ) * H.map φ = 1 := by
    rw [cT_map' t u φ hφ, ← Matrix.map_mul, hH, Matrix.map_one _ (map_zero _) (map_one _)]
  have hQP' : Q.map ι * P.map ι = 1 := by
    rw [← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _)]
  have hPQc : Formalism.UG.cT u (P.map ι) * Formalism.UG.cT u (Q.map ι) = 1 := by
    rw [← Formalism.UG.cT_mul, hQP', Formalism.UG.cT_one]
  have hJ' : J.map ι = Formalism.UG.cT u (Q.map ι) * Q.map ι := by
    rw [hJ, Matrix.map_mul, cT_map' s u ι hι]
  rw [hJ']
  calc Formalism.UG.cT u (P.map ι * H.map φ * Q.map ι) * (Formalism.UG.cT u (Q.map ι) * Q.map ι) * (P.map ι * H.map φ * Q.map ι)
      = Formalism.UG.cT u (Q.map ι) * (Formalism.UG.cT u (H.map φ) * (Formalism.UG.cT u (P.map ι) * Formalism.UG.cT u (Q.map ι))
          * (Q.map ι * P.map ι) * H.map φ) * Q.map ι := by
        rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT u (Q.map ι) * Q.map ι := by
        rw [hPQc, hQP', Matrix.mul_one, Matrix.mul_one, hHu, Matrix.mul_one]

/- English proof (translation)
Unfold `adSwap`. Simplify using `only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]`. Rewrite using `[GlobalTheory.BotFormula.toAfE_sgA]`. Generalize the expression as in `(GlobalTheory.BotFormula.toAfE D) y = x`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a e`. Simplify using `[Lev.swapAE, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.UG.sigR, Algebra.TensorProduct.map_tmul]`. Consider the case `add x y hx hy => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, hx, hy, RingHom.map_add]`.
-/
theorem adSwap_sgA (D : D7) (y : StandardLatticesGL3.AE D) :
    adSwap D (StandardLatticesGL3.sgA D y) = Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (adSwap D y) := by
  unfold adSwap
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [GlobalTheory.BotFormula.toAfE_sgA]
  generalize (GlobalTheory.BotFormula.toAfE D) y = x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp [Lev.swapAE, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.UG.sigR, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, hx, hy, RingHom.map_add]

/- English proof (translation)
Simplify using `only [inclEAf, Formalism.UG.sigR, Formalism.UG.inclE, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]`.
-/
theorem sigR_inclEAf (D : D7) (a : D.host.E) :
    Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (inclEAf D a) = inclEAf D (D.sp.cm.sig a) := by
  simp only [inclEAf, Formalism.UG.sigR, Formalism.UG.inclE, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]

/- English proof (translation)
Establish `h2 : Formalism.UG.cT (StandardLatticesGL3.sgA D) (h.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D)) * (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (StandardLatticesGL3.inc D) * (h.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D)) = (1 : Matr …` using `h.2`. Rewrite `h2` using `[Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]`. Establish `key` using `conj_unitary (D.sp.cm.sig : D.host.E →+* D.host.E) (StandardLatticesGL3.sgA D) (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (inclEAf D) (adSwap D) (sigR_inclEAf D) (fun y => (adSwap_sgA D y).symm) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) ((fr⁻¹ : GL (Fi …`. Conclude with `key`.
-/
theorem frConj_mem_UA {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E)
    (hfr : Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram
      * (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1)
    (h : StandardLatticesGL3.GA D V.rank) : GlobalTheory.FrameTransport.frConj fr h.1 ∈ UA D.sp.cm V.gram := by
  have h2 : Formalism.UG.cT (StandardLatticesGL3.sgA D) (h.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D))
      * (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (StandardLatticesGL3.inc D) * (h.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D)) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (StandardLatticesGL3.inc D) := h.2
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at h2
  have key := conj_unitary (D.sp.cm.sig : D.host.E →+* D.host.E) (StandardLatticesGL3.sgA D) (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
    (inclEAf D) (adSwap D) (sigR_inclEAf D) (fun y => (adSwap_sgA D y).symm)
    (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) ((fr⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E)
    V.gram (h.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D))
    (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]) hfr h2
  exact key

end GlobalTheory.FrameTransport

end
