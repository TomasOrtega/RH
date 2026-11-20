import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniversalSectionBasisPolarisedFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSinglePolarisationGeneratorAllTraits
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin

/- English proof (translation)
The claim follows from `(isGenSec_iff _).2 fun s => by obtain ⟨c, hc, -⟩ := he K' i x' h s exact ⟨c, hc⟩`.
-/
theorem isGenSec_of_univBasis {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {K K' : Type} [CommRing K]
    [CommRing K'] {x : Sp K ⟶ S} {e : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x))} (he : UnivBasis G L x e)
    (i : K →+* K') {x' : Sp K' ⟶ S} (h : spMap i ≫ x = x') :
    IsGenSec G L ((1 : ℕ) : ℤ) (VVRank.pullS G _ (Over.homMk (spMap i) h : Over.mk x' ⟶ Over.mk x) e) :=
  (isGenSec_iff _).2 fun s => by
    obtain ⟨c, hc, -⟩ := he K' i x' h s
    exact ⟨c, hc⟩

/- English proof (translation)
Rewrite using `[← Spec.map_id]`. Both sides reduce to the same expression.
-/
theorem spMap_id (K : Type) [CommRing K] : spMap (RingHom.id K) = 𝟙 _ := by
  rw [← Spec.map_id]; rfl

/- English proof (translation)
Introduce `S G _ L hL g K _ x hP`. Take `⟨P, α, -, hp, hw⟩` from `hP`. Take `⟨e, he⟩` from `exists_univBasis_of_fibre abelianSchemeLaws_all.2 S (Sp K) G L hL P x α hp hw K (𝟙 _) x (Category.id_comp x)`. Establish `h0 : spMap (RingHom.id K) ≫ x = x` using `by rw [spMap_id, Category.id_comp]`. Use `⟨⟨_, isGenSec_of_univBasis he (RingHom.id K) h0⟩, fun θ hθ K' _ i => ?_⟩` and prove the remaining obligations.

Use `set e₀ := VVRank.pullS G _ (Over.homMk (spMap (RingHom.id K)) h0 : Over.mk x ⟶ Over.mk x) e with he₀`. Take `⟨c, hc, -⟩` from `he K (RingHom.id K) x h0 (SecM.ofSec G θ)`. Take `⟨r, hr⟩` from `(isGenSec_iff θ).1 hθ (SecM.ofSec G e₀)`. Take `⟨c₀, -, hu⟩` from `he K (RingHom.id K) x h0 (SecM.ofSec G e₀)`. Establish `hrc : r * c = 1`.

Establish `e1 : SecM.ofSec G e₀ = (r * c) • SecM.ofSec G e₀` using `by conv_lhs => rw [hr, hc]`. Rewrite using `[smul_smul]`. Conclude with `(hu _ e1).trans (hu 1 (one_smul _ _).symm).symm`. Establish `hcu : IsUnit c` using `⟨⟨c, r, by rw [mul_comm]; exact hrc, hrc⟩, rfl⟩`. Establish `ha : IsUnit ((fnR x).symm c)` using `hcu.map (fnR x).symm`.

Establish `hb` using `he.smul_pull hL (RingHom.id K) h0 ha`. Establish `eq : SecM.toSec G (fnR x ((fnR x).symm c) • pl (RingHom.id K) h0 (SecM.ofSec G e)) = θ`. Rewrite using `[RingEquiv.apply_symm_apply, pl_ofSec, ← hc]`. Both sides reduce to the same expression. Rewrite `hb` using `[eq]`.

Conclude with `isGenSec_of_univBasis hb i rfl`.
-/
theorem gen_of_polFib : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → ∀ (g : ℕ) (K : Type)
    [Field K] (x : Sp K ⟶ S), PolFib G L g x → (∃ θ : SecAt G L x, IsGenSec G L _ θ) ∧
    ∀ θ : SecAt G L x, IsGenSec G L _ θ → ∀ (K' : Type) [Field K'] (i : K →+* K'),
      IsGenSec G L _ (SecAt.pull G L θ i) := by
  intro S G _ L hL g K _ x hP
  obtain ⟨P, α, -, hp, hw⟩ := hP
  obtain ⟨e, he⟩ := exists_univBasis_of_fibre abelianSchemeLaws_all.2 S (Sp K) G L hL P x α hp hw K (𝟙 _) x
    (Category.id_comp x)
  have h0 : spMap (RingHom.id K) ≫ x = x := by rw [spMap_id, Category.id_comp]
  refine ⟨⟨_, isGenSec_of_univBasis he (RingHom.id K) h0⟩, fun θ hθ K' _ i => ?_⟩
  set e₀ := VVRank.pullS G _ (Over.homMk (spMap (RingHom.id K)) h0 : Over.mk x ⟶ Over.mk x) e with he₀
  obtain ⟨c, hc, -⟩ := he K (RingHom.id K) x h0 (SecM.ofSec G θ)
  obtain ⟨r, hr⟩ := (isGenSec_iff θ).1 hθ (SecM.ofSec G e₀)
  obtain ⟨c₀, -, hu⟩ := he K (RingHom.id K) x h0 (SecM.ofSec G e₀)
  have hrc : r * c = 1 := by
    have e1 : SecM.ofSec G e₀ = (r * c) • SecM.ofSec G e₀ := by
      conv_lhs => rw [hr, hc]
      rw [smul_smul]
    exact (hu _ e1).trans (hu 1 (one_smul _ _).symm).symm
  have hcu : IsUnit c := ⟨⟨c, r, by rw [mul_comm]; exact hrc, hrc⟩, rfl⟩
  have ha : IsUnit ((fnR x).symm c) := hcu.map (fnR x).symm
  have hb := he.smul_pull hL (RingHom.id K) h0 ha
  have eq : SecM.toSec G (fnR x ((fnR x).symm c) • pl (RingHom.id K) h0 (SecM.ofSec G e)) = θ := by
    rw [RingEquiv.apply_symm_apply, pl_ofSec, ← hc]
    rfl
  rw [eq] at hb
  exact isGenSec_of_univBasis hb i rfl

end GlobalTheory.UMin
