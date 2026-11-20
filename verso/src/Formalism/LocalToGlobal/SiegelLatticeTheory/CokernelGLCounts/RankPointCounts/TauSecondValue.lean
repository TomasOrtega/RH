import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TauTau

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D)

/- English proof (translation)
Simplify using `[Formalism.L2.SG.LsDatumB.sgnP, Matrix.mul_diagonal, Matrix.diagonal_mul]`.
-/
theorem sconj_apply (ρ : MP p) (a b : Fin (D.R.rS + 1)) :
    (Formalism.L2.SG.LsDatumB.sgnP p * ρ * Formalism.L2.SG.LsDatumB.sgnP p) a b =
      (-1 : (D.s.atP p).Ep) ^ (D.R.rS - a.val) * ρ a b * (-1) ^ (D.R.rS - b.val) := by
  simp [Formalism.L2.SG.LsDatumB.sgnP, Matrix.mul_diagonal, Matrix.diagonal_mul]

/- English proof (translation)
Introduce `a b`. Use `⟨fun hab => ?_, fun hab => ?_⟩` and prove the remaining obligations. Rewrite using `[sconj_apply, (h a b).1 hab]`. Simplify using the standard rewrite rules. Substitute `hab` using the available equality.

Rewrite using `[sconj_apply, (h a a).2 rfl, mul_one, ← pow_add, ← two_mul, pow_mul]`. Simplify using the standard rewrite rules.
-/
theorem sconj_up {ρ : MP p} (h : IsUpUni ρ) :
    IsUpUni (Formalism.L2.SG.LsDatumB.sgnP p * ρ * Formalism.L2.SG.LsDatumB.sgnP p) := by
  intro a b
  refine ⟨fun hab => ?_, fun hab => ?_⟩
  · rw [sconj_apply, (h a b).1 hab]; simp
  · subst hab
    rw [sconj_apply, (h a a).2 rfl, mul_one, ← pow_add, ← two_mul, pow_mul]; simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tau_second_value (x : GG p) : (((tau p x).2.unop : GLp p) : MP p) =
    Formalism.L2.SG.LsDatumB.sgnP p * ((x.2.unop : GLp p) : MP p) * Formalism.L2.SG.LsDatumB.sgnP p := rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨hx.1, by rw [tau_second_value]; exact sconj_up p hx.2⟩`.
-/
theorem tau_mem_UP {x : GG p} (hx : x ∈ UP p) : tau p x ∈ UP p :=
  ⟨hx.1, by rw [tau_second_value]; exact sconj_up p hx.2⟩

/- English proof (translation)
Use `⟨hx.1, ?_⟩` and prove the remaining obligations. Use `show Formalism.MainNotions.S.TieN.IntUp (M p) (((tau p x).2.unop : GLp p) : MP p)`. Rewrite using `[tau_second_value]`. Take `⟨h1, h2, h3⟩` from `hx.2`. Use `⟨fun a => ?_, fun a b hab => ?_, fun a b => ?_⟩` and prove the remaining obligations.

Rewrite using `[sconj_apply, h1 a, mul_one, ← pow_add, ← two_mul, pow_mul]`. Simplify using the standard rewrite rules. Rewrite using `[sconj_apply, h2 a b hab]`. Simplify using the standard rewrite rules. Rewrite using `[sconj_apply]`.

Conclude with `Subring.mul_mem _ (Subring.mul_mem _ (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _) (h3 a b)) (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)`.
-/
theorem tau_mem_KP {x : GG p} (hx : x ∈ KP M p) : tau p x ∈ KP M p := by
  refine ⟨hx.1, ?_⟩
  show Formalism.MainNotions.S.TieN.IntUp (M p) (((tau p x).2.unop : GLp p) : MP p)
  rw [tau_second_value]
  obtain ⟨h1, h2, h3⟩ := hx.2
  refine ⟨fun a => ?_, fun a b hab => ?_, fun a b => ?_⟩
  · rw [sconj_apply, h1 a, mul_one, ← pow_add, ← two_mul, pow_mul]; simp
  · rw [sconj_apply, h2 a b hab]; simp
  · rw [sconj_apply]
    exact Subring.mul_mem _ (Subring.mul_mem _ (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _) (h3 a b))
      (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)

def phi (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) (Z : MP p) : MP p :=
  Z * Formalism.L2.SG.LsDatumB.sgnP p + Formalism.L2.SG.Pf.LocOrbSumPf.shM δ T T' p w

/- English proof (translation)
Establish `hss` using `Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ (D := D) p`. Establish `hc : ((x.1 : GLp p) : MP p) * Formalism.L2.SG.Pf.LocOrbSumPf.shM δ T T' p w * (Formalism.L2.SG.LsDatumB.sgnP p * ((x.2.unop : GLp p) : MP p) * Formalism.L2.SG.LsDatumB.sgnP p) = Formalism.L2.SG.Pf.LocOrbSumPf.shM δ T T' p w`. Establish `hu` using `sconj_up p hx.2`. Use `Formalism.L2.SG.Pf.FibQ.corner_fix p (fun a b h => (hx.1 a b).1 h) (fun a => (hx.1 a a).2 rfl) (fun a b h => (hu a b).1 h) (fun a => (hu a a).2 rfl) (fun a b h => ?_)` and prove the remaining obligations. Simplify using `only [Formalism.L2.SG.Pf.LocOrbSumPf.shM, Matrix.of_apply]`.

Rewrite using `[if_neg h]`. Simplify using `only [phi, smul_def, tau_second_value]`. Use `show ((x.1 : GLp p) : MP p) * Z * ((x.2.unop : GLp p) : MP p) * Formalism.L2.SG.LsDatumB.sgnP p + Formalism.L2.SG.Pf.LocOrbSumPf.shM δ T T' p w = ((x.1 : GLp p) : MP p) * (Z * Formalism.L2.SG.LsDatumB.sgnP p + Formalism.L2.SG.Pf.LocOrbSumPf.shM δ T T' p w) * (Formalism.L2.SG.LsDa …`. Rewrite using `[Matrix.mul_add, Matrix.add_mul, hc]`. Use `congr 1`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (Formalism.L2.SG.LsDatumB.sgnP p) (Formalism.L2.SG.LsDatumB.sgnP p), hss, Matrix.one_mul]`.
-/
theorem phi_smul (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) {x : GG p}
    (hx : x ∈ UP p) (Z : MP p) : phi p δ T T' w (x • Z) = tau p x • phi p δ T T' w Z := by
  have hss := Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ (D := D) p
  have hc : ((x.1 : GLp p) : MP p) * Formalism.L2.SG.Pf.LocOrbSumPf.shM δ T T' p w *
      (Formalism.L2.SG.LsDatumB.sgnP p * ((x.2.unop : GLp p) : MP p) * Formalism.L2.SG.LsDatumB.sgnP p) =
      Formalism.L2.SG.Pf.LocOrbSumPf.shM δ T T' p w := by
    have hu := sconj_up p hx.2
    refine Formalism.L2.SG.Pf.FibQ.corner_fix p (fun a b h => (hx.1 a b).1 h) (fun a => (hx.1 a a).2 rfl)
      (fun a b h => (hu a b).1 h) (fun a => (hu a a).2 rfl) (fun a b h => ?_)
    simp only [Formalism.L2.SG.Pf.LocOrbSumPf.shM, Matrix.of_apply]
    rw [if_neg h]
  simp only [phi, smul_def, tau_second_value]
  show ((x.1 : GLp p) : MP p) * Z * ((x.2.unop : GLp p) : MP p) * Formalism.L2.SG.LsDatumB.sgnP p +
      Formalism.L2.SG.Pf.LocOrbSumPf.shM δ T T' p w =
    ((x.1 : GLp p) : MP p) * (Z * Formalism.L2.SG.LsDatumB.sgnP p + Formalism.L2.SG.Pf.LocOrbSumPf.shM δ T T' p w) *
      (Formalism.L2.SG.LsDatumB.sgnP p * ((x.2.unop : GLp p) : MP p) * Formalism.L2.SG.LsDatumB.sgnP p)
  rw [Matrix.mul_add, Matrix.add_mul, hc]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Formalism.L2.SG.LsDatumB.sgnP p) (Formalism.L2.SG.LsDatumB.sgnP p), hss, Matrix.one_mul]

/- English proof (translation)
Establish `hss` using `Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ (D := D) p`. Unfold `phi at h`. Establish `h2` using `add_right_cancel h`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem phi_inj (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) {Z Z' : MP p}
    (h : phi p δ T T' w Z = phi p δ T T' w Z') : Z = Z' := by
  have hss := Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ (D := D) p
  unfold phi at h
  have h2 := add_right_cancel h
  calc Z = Z * Formalism.L2.SG.LsDatumB.sgnP p * Formalism.L2.SG.LsDatumB.sgnP p := by rw [Matrix.mul_assoc, hss, Matrix.mul_one]
    _ = Z' * Formalism.L2.SG.LsDatumB.sgnP p * Formalism.L2.SG.LsDatumB.sgnP p := by rw [h2]
    _ = Z' := by rw [Matrix.mul_assoc, hss, Matrix.mul_one]

end Formalism.L2.SG.Pf.CountAt
