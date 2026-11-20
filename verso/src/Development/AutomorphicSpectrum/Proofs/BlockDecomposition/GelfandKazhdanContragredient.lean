import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
open scoped Matrix

namespace GlobalTheory.CompanionTheory.ThetaW

def revMat (A : Type) [CommRing A] (N : ℕ) : Matrix (Fin N) (Fin N) A :=
  (1 : Matrix (Fin N) (Fin N) A).submatrix Fin.rev id

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[revMat, Matrix.mul_apply, Matrix.one_apply]`.
-/
theorem revMat_mul {A : Type} [CommRing A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A) :
    revMat A N * M = M.submatrix Fin.rev id := by
  ext i j
  simp [revMat, Matrix.mul_apply, Matrix.one_apply]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [revMat, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply, id]`. Rewrite using `[Finset.sum_eq_single (Fin.rev j)]`. Simplify using the standard rewrite rules. Introduce `b _ hb`.

Rewrite using `[if_neg, mul_zero]`. Introduce `h`. Conclude with `hb (by rw [← h, Fin.rev_rev])`. Simplify using the standard rewrite rules.
-/
theorem mul_revMat {A : Type} [CommRing A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A) :
    M * revMat A N = M.submatrix id Fin.rev := by
  ext i j
  simp only [revMat, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply, id]
  rw [Finset.sum_eq_single (Fin.rev j)]
  · simp
  · intro b _ hb
    rw [if_neg, mul_zero]
    intro h
    exact hb (by rw [← h, Fin.rev_rev])
  · simp

/- English proof (translation)
Rewrite using `[revMat_mul]`. Use extensionality with `i j`. Simplify using `[revMat, Matrix.one_apply]`.
-/
theorem revMat_mul_self (A : Type) [CommRing A] (N : ℕ) : revMat A N * revMat A N = 1 := by
  rw [revMat_mul]
  ext i j
  simp [revMat, Matrix.one_apply]

def w₀ (A : Type) [CommRing A] (N : ℕ) : GL (Fin N) A :=
  ⟨revMat A N, revMat A N, revMat_mul_self A N, revMat_mul_self A N⟩

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use `show _ = revMat A N * (invT g).1 * revMat A N`. Rewrite using `[revMat_mul, mul_revMat]`. Use extensionality with `i j`. Simplify using `[thetaW, Matrix.reindexAlgEquiv_apply]`.
-/
theorem thetaW_eq_conj (A : Type) [CommRing A] (N : ℕ) (g : GL (Fin N) A) :
    thetaW A N g = w₀ A N * invT g * (w₀ A N)⁻¹ := by
  apply Units.ext
  show _ = revMat A N * (invT g).1 * revMat A N
  rw [revMat_mul, mul_revMat]
  ext i j
  simp [thetaW, Matrix.reindexAlgEquiv_apply]

def compInvTEquiv {A : Type} [CommRing A] {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) A) V) :
    Representation.Equiv (π.comp invT) (π.comp (thetaW A N)) :=
  Representation.Equiv.mk
    (LinearEquiv.ofLinear (π (w₀ A N)) (π (w₀ A N)⁻¹)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl))
    fun g => LinearMap.ext fun v => by
      show π (w₀ A N) (π (invT g) v) = π (thetaW A N g) (π (w₀ A N) v)
      rw [thetaW_eq_conj, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
        inv_mul_cancel_right]

/- English proof (translation)
Introduce `k _ _ _ _ hGK N V _ _ π hs hi`. Take `⟨e⟩` from `hGK N π hs hi`. Conclude with `⟨(compInvTEquiv π).symm.trans e⟩`.
-/
theorem comp_thetaW_equiv_contra : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GKLocal k → ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible →
    Nonempty (Representation.Equiv (π.comp (thetaW k N)) (contra π)) := by
  intro k _ _ _ _ hGK N V _ _ π hs hi
  obtain ⟨e⟩ := hGK N π hs hi
  exact ⟨(compInvTEquiv π).symm.trans e⟩

end GlobalTheory.CompanionTheory.ThetaW

end
