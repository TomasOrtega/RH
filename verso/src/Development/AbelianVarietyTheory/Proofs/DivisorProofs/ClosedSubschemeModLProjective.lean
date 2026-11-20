import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverBaseChangeOfProperQuasiProjective
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverBaseChangeAndFiniteRestrict

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

namespace GlobalTheory.VertProj

/- English proof (translation)
Introduce `k _ X p D hX Z i _ l _ _`. Establish `: Module.Finite ℤ k` using `hX.finite`. Establish `hfin : (Int.castRingHom k).Finite` using `(RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance`. Establish `: IsProper p` using `(isProper_and_exists_isAmpleLB_of_isProjOver hX.isProjOver).1`. Establish `: IsFinite (spMap (Int.castRingHom k))`.

Rewrite using `[spMap, IsFinite.SpecMap_iff]`. Conclude with `hfin`. Establish `e : i ≫ p ≫ spMap (Int.castRingHom k) = strHom (ZMod l) Z ≫ spMap (Int.castRingHom (ZMod l))` using `specZIsTerminal.hom_ext _ _`. Establish `: IsProper (strHom (ZMod l) Z ≫ spMap (Int.castRingHom (ZMod l)))`. Rewrite using `[← e]`.

Use `infer_instance`. Establish `hpr : IsProper (strHom (ZMod l) Z)` using `IsProper.of_comp _ (spMap (Int.castRingHom (ZMod l)))`. Establish `hq : IsQProjOver p`. Take `⟨N, j, hj, hjp⟩` from `hX.isProjOver`. Conclude with `⟨N, j, inferInstance, inferInstance, hjp⟩`.

Establish `hq₁` using `isQProjOver_comp_spMap_of_finiteType hfin.finiteType hq`. Establish `hq₂` using `isQProjOver_of_isPullback_spMap (Int.castRingHom (ZMod l)) (IsPullback.of_hasPullback (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod l)))) hq₁`. Set `u` to `Limits.pullback.lift (f := p ≫ spMap (Int.castRingHom k)) (g := spMap (Int.castRingHom (ZMod l))) i (strHom (ZMod l) Z) e`. Establish `: IsImmersion u`. Establish `: IsImmersion (u ≫ Limits.pullback.fst _ _)`.

Rewrite using `[Limits.pullback.lift_fst]`. Use `infer_instance`. Conclude with `IsImmersion.of_comp u (Limits.pullback.fst _ _)`. Establish `hu : u ≫ Limits.pullback.snd _ _ = strHom (ZMod l) Z` using `Limits.pullback.lift_snd _ _ _`. Rewrite `hpr`, the goal using `[← hu]`.

Conclude with `isProjOver_of_isProper_of_isImmersion _ hq₂`.
-/
theorem isProjOver_strHom_zmod : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] (l : ℕ) [Fact l.Prime]
    [Algebra (ZMod l) Γ(Z, ⊤)], IsProjOver (strHom (ZMod l) Z) := by
  intro k _ X p D hX Z i _ l _ _
  have : Module.Finite ℤ k := hX.finite
  have hfin : (Int.castRingHom k).Finite := (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have : IsProper p := (isProper_and_exists_isAmpleLB_of_isProjOver hX.isProjOver).1
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact hfin
  have e : i ≫ p ≫ spMap (Int.castRingHom k) =
      strHom (ZMod l) Z ≫ spMap (Int.castRingHom (ZMod l)) := specZIsTerminal.hom_ext _ _
  have : IsProper (strHom (ZMod l) Z ≫ spMap (Int.castRingHom (ZMod l))) := by
    rw [← e]; infer_instance
  have hpr : IsProper (strHom (ZMod l) Z) := IsProper.of_comp _ (spMap (Int.castRingHom (ZMod l)))
  have hq : IsQProjOver p := by
    obtain ⟨N, j, hj, hjp⟩ := hX.isProjOver
    exact ⟨N, j, inferInstance, inferInstance, hjp⟩
  have hq₁ := isQProjOver_comp_spMap_of_finiteType hfin.finiteType hq
  have hq₂ := isQProjOver_of_isPullback_spMap (Int.castRingHom (ZMod l))
    (IsPullback.of_hasPullback (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod l)))) hq₁
  let u := Limits.pullback.lift (f := p ≫ spMap (Int.castRingHom k))
    (g := spMap (Int.castRingHom (ZMod l))) i (strHom (ZMod l) Z) e
  have : IsImmersion u := by
    have : IsImmersion (u ≫ Limits.pullback.fst _ _) := by
      rw [Limits.pullback.lift_fst]; infer_instance
    exact IsImmersion.of_comp u (Limits.pullback.fst _ _)
  have hu : u ≫ Limits.pullback.snd _ _ = strHom (ZMod l) Z := Limits.pullback.lift_snd _ _ _
  rw [← hu] at hpr ⊢
  exact isProjOver_of_isProper_of_isImmersion _ hq₂

end GlobalTheory.VertProj
