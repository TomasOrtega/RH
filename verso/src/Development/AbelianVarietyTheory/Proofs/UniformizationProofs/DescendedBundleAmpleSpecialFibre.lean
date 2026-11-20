import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubWeilOfGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecPullNeZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PairingNondegenerate
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfLbIso

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU.AmpleZero

/- English proof (translation)
Use `(Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 ?_` and prove the remaining obligations. Rewrite using `[zero_add, pow_one]`. Use `infer_instance`.
-/
theorem isField_quot (V : Type) [CommRing V] [IsLocalRing V] :
    IsField (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) := by
  refine (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 ?_
  rw [zero_add, pow_one]
  infer_instance

/- English proof (translation)
Take `⟨p, hp⟩` from `CharP.exists F`. Take `⟨n, hn, hpr⟩` from `Nat.exists_infinite_primes (max m p + 1)`. Use `⟨n, hpr, by omega, fun h => ?_⟩` and prove the remaining obligations. Establish `hd` using `(CharP.cast_eq_zero_iff F p n).1 h`. Break down `(Nat.dvd_prime hpr).1 hd with e | e` into its components or cases.

Conclude with `CharP.char_ne_one F p e`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_prime_ne_zero (F : Type) [Field F] (m : ℕ) : ∃ n : ℕ, n.Prime ∧ m < n ∧ (n : F) ≠ 0 := by
  obtain ⟨p, hp⟩ := CharP.exists F
  obtain ⟨n, hn, hpr⟩ := Nat.exists_infinite_primes (max m p + 1)
  refine ⟨n, hpr, by omega, fun h => ?_⟩
  have hd := (CharP.cast_eq_zero_iff F p n).1 h
  rcases (Nat.dvd_prime hpr).1 hd with e | e
  · exact CharP.char_ne_one F p e
  · omega

/- English proof (translation)
Introduce `hc hL V _ _ _ A G _ _ s t`. Take `⟨k, σ, hk, hσ⟩` from `GlobalTheory.UU.EffSpecial.exists_sec_special hL V A G s t`. Establish `hF` using `isField_quot V`. Choose the witnesses or unpack the hypotheses as in `⟨K, _, _, φ, -⟩ : ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) →+* K), True := by`. Set `` to `hF.toField`.

Conclude with `⟨AlgebraicClosure (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)), inferInstance, inferInstance, algebraMap _ _, trivial⟩`. Take `⟨n, hn, hlt, hne⟩` from `exists_prime_ne_zero K (2 * k)`. Establish `hu : IsUnit (n : V)`. Assume the negation of the conclusion as `h`. Establish `hm : (n : V) ∈ IsLocalRing.maximalIdeal V ^ (0 + 1)`.

Rewrite using `[zero_add, pow_one]`. Conclude with `h`. Establish `e` using `congrArg φ (Ideal.Quotient.eq_zero_iff_mem.2 hm)`. Rewrite `e` using `[map_natCast, map_natCast, map_zero]`. Conclude with `hne e`.

Use `GlobalTheory.AmpleCrit.relAmple_of_effective hc _ hF (t.l 0).Q.B (t.l 0).Q.isAb (t.l 0).D.M.L (t.l 0).D.M.c k σ hk hσ K (Spec.map (CommRingCat.ofHom φ)) n hn hne (Nat.not_dvd_of_pos_of_lt (by omega) hlt) fun x hx hT => ?_` and prove the remaining obligations. Conclude with `GlobalTheory.UU.SpecialPairing.pairing_nondegenerate hc hL V A G s t K _ n hu x hx fun y hy => KerPair.cubWeil_of_gen hL.globalFns _ _ (t.l 0).Q.isAb _ _ n _ x y hx hy hT`.
-/
theorem relAmple_zero : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → Laws → AllSet fun s => ∀ t : Tower s, RelAmple (t.l 0).Q.B (t.l 0).D.M.L.L := by
  intro hc hL V _ _ _ A G _ _ s t
  obtain ⟨k, σ, hk, hσ⟩ := GlobalTheory.UU.EffSpecial.exists_sec_special hL V A G s t
  have hF := isField_quot V
  obtain ⟨K, _, _, φ, -⟩ : ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K)
      (_ : (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) →+* K), True := by
    let := hF.toField
    exact ⟨AlgebraicClosure (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)), inferInstance, inferInstance,
      algebraMap _ _, trivial⟩
  obtain ⟨n, hn, hlt, hne⟩ := exists_prime_ne_zero K (2 * k)
  have hu : IsUnit (n : V) := by
    by_contra h
    have hm : (n : V) ∈ IsLocalRing.maximalIdeal V ^ (0 + 1) := by
      rw [zero_add, pow_one]; exact h
    have e := congrArg φ (Ideal.Quotient.eq_zero_iff_mem.2 hm)
    rw [map_natCast, map_natCast, map_zero] at e
    exact hne e
  refine GlobalTheory.AmpleCrit.relAmple_of_effective hc _ hF (t.l 0).Q.B (t.l 0).Q.isAb (t.l 0).D.M.L (t.l 0).D.M.c k σ hk hσ K
    (Spec.map (CommRingCat.ofHom φ)) n hn hne (Nat.not_dvd_of_pos_of_lt (by omega) hlt) fun x hx hT => ?_
  exact GlobalTheory.UU.SpecialPairing.pairing_nondegenerate hc hL V A G s t K _ n hu x hx fun y hy =>
    KerPair.cubWeil_of_gen hL.globalFns _ _ (t.l 0).Q.isAb _ _ n _ x y hx hy hT

end GlobalTheory.UU.AmpleZero
end
