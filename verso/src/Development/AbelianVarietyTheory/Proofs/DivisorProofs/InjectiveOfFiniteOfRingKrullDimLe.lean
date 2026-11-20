import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionEtaleCompletionToCompleteLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FiniteMapInj

/- English proof (translation)
Introduce `hfin hdim`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Assume the negation of the conclusion as `hx0`. Use `set I := RingHom.ker b`.

Establish `hxI : x ∈ I` using `hx`. Establish `hcomp : b.kerLift.comp (Ideal.Quotient.mk I) = b`. Use extensionality with `a`. Both sides reduce to the same expression. Establish `hfin' : b.kerLift.Finite`.

Rewrite `hfin` using `[← hcomp]`. Conclude with `RingHom.Finite.of_comp_finite hfin`. Use `letI : Algebra (A ⧸ I) R := b.kerLift.toAlgebra`. Use `haveI : Algebra.IsIntegral (A ⧸ I) R := ⟨hfin'.to_isIntegral⟩`. Establish `h1 : ringKrullDim R ≤ ringKrullDim (A ⧸ I)` using `Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap (A ⧸ I) R)) fun P Q h => Ideal.IsIntegral.comap_lt_comap (I := P.asIdeal) (J := Q.asIdeal) h`.

Establish `h2 : ringKrullDim (A ⧸ I) + 1 ≤ ringKrullDim A` using `ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_of_ne_zero hx0) (Ideal.Quotient.eq_zero_iff_mem.mpr hxI)`. Establish `h3 : ringKrullDim R + 1 ≤ ringKrullDim R` using `((by gcongr : ringKrullDim R + 1 ≤ ringKrullDim (A ⧸ I) + 1).trans h2).trans hdim`. Establish `htop : ringKrullDim R + 1 < ⊤` using `((by gcongr : ringKrullDim R + 1 ≤ ringKrullDim (A ⧸ I) + 1).trans h2).trans_lt ringKrullDim_lt_top`. Establish `hbot : ringKrullDim R ≠ ⊥` using `fun h => by`. Use `ringKrullDim_nonneg_of_nontrivial (R := R)` as an intermediate fact.

Rewrite `this` using `[h]`. Conclude with `absurd this (by simp)`. Generalize the expression as in `ringKrullDim R = d at h3 htop hbot`. Proceed by induction on `d with`. Consider the case `bot => exact hbot rfl`.

Consider the case `coe e`. Proceed by induction on `e with`. Consider the case `top`. Conclude with `absurd htop (by rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]; exact lt_irrefl _)`. Consider the case `coe n`.

Establish `: ((n + 1 : ℕ) : WithBot ℕ∞) ≤ (n : ℕ)` using `by exact_mod_cast h3`. Normalize the coercions in `at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem injective_of_finite_of_ringKrullDim_le (A R : Type) [CommRing A] [IsDomain A]
    [IsLocalRing A] [IsNoetherianRing A] [CommRing R] [IsLocalRing R] (b : A →+* R) :
    b.Finite → ringKrullDim A ≤ ringKrullDim R → Function.Injective b := by
  intro hfin hdim
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  set I := RingHom.ker b
  have hxI : x ∈ I := hx

  have hcomp : b.kerLift.comp (Ideal.Quotient.mk I) = b := by
    ext a; rfl
  have hfin' : b.kerLift.Finite := by
    rw [← hcomp] at hfin
    exact RingHom.Finite.of_comp_finite hfin
  letI : Algebra (A ⧸ I) R := b.kerLift.toAlgebra
  haveI : Algebra.IsIntegral (A ⧸ I) R := ⟨hfin'.to_isIntegral⟩
  have h1 : ringKrullDim R ≤ ringKrullDim (A ⧸ I) :=
    Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap (A ⧸ I) R))
      fun P Q h => Ideal.IsIntegral.comap_lt_comap (I := P.asIdeal) (J := Q.asIdeal) h
  have h2 : ringKrullDim (A ⧸ I) + 1 ≤ ringKrullDim A :=
    ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      (mem_nonZeroDivisors_of_ne_zero hx0) (Ideal.Quotient.eq_zero_iff_mem.mpr hxI)
  have h3 : ringKrullDim R + 1 ≤ ringKrullDim R :=
    ((by gcongr : ringKrullDim R + 1 ≤ ringKrullDim (A ⧸ I) + 1).trans h2).trans hdim
  have htop : ringKrullDim R + 1 < ⊤ :=
    ((by gcongr : ringKrullDim R + 1 ≤ ringKrullDim (A ⧸ I) + 1).trans h2).trans_lt
      ringKrullDim_lt_top
  have hbot : ringKrullDim R ≠ ⊥ := fun h => by
    have := ringKrullDim_nonneg_of_nontrivial (R := R)
    rw [h] at this
    exact absurd this (by simp)
  generalize ringKrullDim R = d at h3 htop hbot
  induction d with
  | bot => exact hbot rfl
  | coe e =>
    induction e with
    | top =>
      exact absurd htop (by rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]; exact lt_irrefl _)
    | coe n =>
      have : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ (n : ℕ) := by exact_mod_cast h3
      norm_cast at this
      omega

end GlobalTheory.FiniteMapInj
