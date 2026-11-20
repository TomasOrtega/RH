import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

namespace GlobalTheory

namespace PDivGroup

/- English proof (translation)
Rewrite using `[← frobTwistDual_verschiebung h (G := G) n χ, ← relFrob_app_frobProj h (G := G) n a]`. Establish `e : (verschiebung h G).app n ((relFrob h G).app n ((frobProj h G).app n a)) = mulBy R _ p ((frobProj h G).app n a)`. Rewrite using `[← prime_smul_id_app]`. Conclude with `(congrArg (fun f => Hom.app f n ((frobProj h G).app n a)) (verschiebung_comp_relFrob h G))`. Rewrite using `[e, ← SemiBialgHom.map_mulBy, frobTwistDual_frobProj]`.
-/
theorem convPow_prime_apply_pow_prime (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0)
    (G : PDivGroup p R) (n : ℕ) (χ : CartierDual R (G.A n)) (a : G.A n) :
    (χ ^ p) (a ^ p) = χ (mulBy R (G.A n) p a) ^ p := by
  rw [← frobTwistDual_verschiebung h (G := G) n χ, ← relFrob_app_frobProj h (G := G) n a]
  have e : (verschiebung h G).app n ((relFrob h G).app n ((frobProj h G).app n a)) =
      mulBy R _ p ((frobProj h G).app n a) := by
    rw [← prime_smul_id_app]
    exact (congrArg (fun f => Hom.app f n ((frobProj h G).app n a)) (verschiebung_comp_relFrob h G))
  rw [e, ← SemiBialgHom.map_mulBy, frobTwistDual_frobProj]

/- English proof (translation)
Proceed by induction on `r generalizing a with`. Consider the case `zero`. Simplify using `only [pow_zero, pow_one]`. Rewrite using `[mulBy, pow_one]`. Both sides reduce to the same expression.

Consider the case `succ r ih`. Rewrite using `[pow_succ, pow_mul, pow_mul, convPow_prime_apply_pow_prime p R h G n, map_pow, ih, mulBy_mulBy, ← pow_mul, mul_comm (p ^ r) p, ← pow_succ']`.
-/
theorem convPow_primePow_apply_pow (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0)
    (G : PDivGroup p R) (n r : ℕ) (χ : CartierDual R (G.A n)) (a : G.A n) :
    (χ ^ p ^ r) (a ^ p ^ r) = χ (mulBy R (G.A n) (p ^ r) a) ^ p ^ r := by
  induction r generalizing a with
  | zero =>
    simp only [pow_zero, pow_one]
    rw [mulBy, pow_one]
    rfl
  | succ r ih =>
    rw [pow_succ, pow_mul, pow_mul, convPow_prime_apply_pow_prime p R h G n, map_pow, ih,
      mulBy_mulBy, ← pow_mul, mul_comm (p ^ r) p, ← pow_succ']

end PDivGroup

end GlobalTheory
