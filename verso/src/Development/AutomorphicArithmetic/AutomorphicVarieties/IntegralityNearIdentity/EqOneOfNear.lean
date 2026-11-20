import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraAlt
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqOneOfNear
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraBis
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MirabolicColumnBlock
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FinitelyGeneratedModPow

namespace UpperTheory.V.Lib.Small

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.S6.norm_le_one_of_isIntegral l x hx`.
-/
theorem norm_le_one_of_isIntegral (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.S6.norm_le_one_of_isIntegral l x hx

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.S7.eq_one_of_near hm hu h`.
-/
theorem eq_one_of_near {l : ℕ} [Fact l.Prime] {u : PadicAlgCl l} {m : ℕ} (hm : ¬ l ∣ m) (hu : u ^ m = 1)
    (h : ‖u - 1‖ < 1) : u = 1 :=
  _root_.UpperTheory.Reformulated.B.S7.eq_one_of_near hm hu h

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.S8.diag_mul X Y hX hY a`.
-/
theorem diag_mul {R : Type} [CommRing R] {n : ℕ} (X Y : Matrix (Fin n) (Fin n) R) (hX : ∀ i j, j < i → X i j = 0)
    (hY : ∀ i j, j < i → Y i j = 0) (a : Fin n) : (X * Y) a a = X a a * Y a a :=
  _root_.UpperTheory.Reformulated.B.S8.diag_mul X Y hX hY a

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.FinitelyGeneratedModPow.fg_mod_pow m hres n`.
-/
theorem fg_mod_pow {O A : Type} [CommRing O] [CommRing A] [Algebra O A] [IsNoetherianRing A]
    (m : Ideal A) (hres : ∀ x : A, ∃ a : O, x - algebraMap O A a ∈ m) (n : ℕ) :
    ∃ N : Submodule O A, N.FG ∧ ∀ x : A, ∃ y ∈ N, x - y ∈ m ^ n :=
  _root_.UpperTheory.Reformulated.B.FinitelyGeneratedModPow.fg_mod_pow m hres n

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.MirabolicColumnBlock.conj_diagonal d hd M hM`.
-/
theorem conj_diagonal {K : Type} [Field K] {n : ℕ} (d : Fin n → K) (hd : Function.Injective d)
    (M : Matrix (Fin n) (Fin n) K) (hM : M.charpoly = ∏ a, (Polynomial.X - Polynomial.C (d a))) :
    ∃ h : GL (Fin n) K, ((h⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M * h = Matrix.diagonal d :=
  _root_.UpperTheory.Reformulated.B.MirabolicColumnBlock.conj_diagonal d hd M hM

end UpperTheory.V.Lib.Small
