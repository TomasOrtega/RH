import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinitePointExtendsSectionStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.Ar.BT.Transl

/- English proof (translation)
Introduce `R _ _ _ T _ _ Γ U U' hU hU' _ g hg`. Use `haveI := Γ.flat`. Use `haveI := Γ.separated`. Set `p0 : Spec (CommRingCat.of R)` to `⟨⊥, Ideal.bot_prime⟩`. Establish `hp0 : p0 ⤳ Γ.G.hom g` using `(PrimeSpectrum.le_iff_specializes _ _).1 bot_le`.

Take `⟨g', hg'g, hg'⟩` from `Flat.generalizingMap Γ.G.hom hp0`. Take `⟨s, x, hx⟩` from `Γ.pt_onto g' (by rw [hg'])`. Establish `hsU : (Γ.pt s).left x ∈ U`. Rewrite using `[hx]`. Conclude with `hg'g.mem_open U.isOpen hg`.

Establish `hsub : ∀ z z' : Spec (CommRingCat.of (FractionRing R)), z = z'` using `fun z z' => PrimeSpectrum.ext (by haveI := z.isPrime haveI := z'.isPrime`. Rewrite using `[Ideal.eq_bot_of_prime z.asIdeal, Ideal.eq_bot_of_prime z'.asIdeal])`. Establish `hsall : ∀ z, (Γ.pt s).left z ∈ U` using `fun z => hsub x z ▸ hsU`. Establish `hinvU : ∀ z, (Γ.pt s⁻¹).left z ∈ U`. Rewrite using `[map_inv]`.

Conclude with `hU.inv _ _ hsall`. Take `⟨σ, -, hσ⟩` from `GlobalTheory.T.finite_point_extends_section R T Γ U hU.finite s⁻¹ (fun z _ => hinvU z)`. Use `⟨σ, s⁻¹, hσ, ?_⟩` and prove the remaining obligations. Use `set τ := (toUnit Γ.G ≫ σ) * 𝟙 Γ.G with hτ`. Establish `hτpt : Γ.pt s ≫ τ = 1`.

Rewrite using `[hτ, Hom.mul_def, ← Category.assoc, comp_lift, ← Category.assoc, comp_toUnit, hσ, Category.comp_id, ← Hom.mul_def, ← map_mul, inv_mul_cancel, map_one]`. Establish `hτx : τ.left ((Γ.pt s).left x) = (η[Γ.G]).left ((toUnit (genPt R)).left x)`. Establish `h1 : (Γ.pt s ≫ τ).left = (toUnit (genPt R) ≫ η[Γ.G]).left`. Rewrite using `[hτpt, Hom.one_def]`. Rewrite `h1` using `[Over.comp_left, Over.comp_left]`.

Establish `h2` using `congrArg (fun h => h x) h1`. Simplify using `using h2`. Establish `hw : (η[Γ.G]).left ≫ Γ.G.hom = 𝟙 _` using `Over.w _`. Use `haveI : UniversallyClosed ((η[Γ.G]).left ≫ Γ.G.hom) := by rw [hw]; infer_instance`. Use `haveI : UniversallyClosed (η[Γ.G]).left := UniversallyClosed.of_comp_of_isSeparated _ Γ.G.hom`.

Establish `hcl : IsClosed (Set.range (η[Γ.G]).left)`. Establish `h` using `(η[Γ.G]).left.isClosedMap _ isClosed_univ`. Rewrite `h` using `[Set.image_univ]`. Then use the resulting hypothesis. Establish `hspec : τ.left ((Γ.pt s).left x) ⤳ τ.left g`. Rewrite using `[hx]`.

Conclude with `hg'g.map τ.left.continuous`. Establish `hsubset : ({τ.left ((Γ.pt s).left x)} : Set Γ.G.left) ⊆ Set.range (η[Γ.G]).left` using `Set.singleton_subset_iff.2 ⟨_, hτx.symm⟩`. Establish `hmem : τ.left g ∈ Set.range (η[Γ.G]).left` using `closure_minimal hsubset hcl (specializes_iff_mem_closure.1 hspec)`. Take `⟨z, hz⟩` from `hmem`. Rewrite using `[← hz]`.

Conclude with `hU'.one z`.
-/
theorem translates_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U U' : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.IsFinOpenSub U' → U' ≤ U → ∀ g ∈ U, ∃ (σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γ.G) (t : T), toUnit (genPt R) ≫ σ = Γ.pt t ∧ ((toUnit Γ.G ≫ σ) * 𝟙 Γ.G).left g ∈ U' := by
  intro R _ _ _ T _ _ Γ U U' hU hU' _ g hg
  haveI := Γ.flat
  haveI := Γ.separated
  let p0 : Spec (CommRingCat.of R) := ⟨⊥, Ideal.bot_prime⟩
  have hp0 : p0 ⤳ Γ.G.hom g := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  obtain ⟨g', hg'g, hg'⟩ := Flat.generalizingMap Γ.G.hom hp0
  obtain ⟨s, x, hx⟩ := Γ.pt_onto g' (by rw [hg'])
  have hsU : (Γ.pt s).left x ∈ U := by
    rw [hx]; exact hg'g.mem_open U.isOpen hg
  have hsub : ∀ z z' : Spec (CommRingCat.of (FractionRing R)), z = z' := fun z z' =>
    PrimeSpectrum.ext (by
      haveI := z.isPrime
      haveI := z'.isPrime
      rw [Ideal.eq_bot_of_prime z.asIdeal, Ideal.eq_bot_of_prime z'.asIdeal])
  have hsall : ∀ z, (Γ.pt s).left z ∈ U := fun z => hsub x z ▸ hsU
  have hinvU : ∀ z, (Γ.pt s⁻¹).left z ∈ U := by
    rw [map_inv]; exact hU.inv _ _ hsall
  obtain ⟨σ, -, hσ⟩ := GlobalTheory.T.finite_point_extends_section R T Γ U hU.finite s⁻¹ (fun z _ => hinvU z)
  refine ⟨σ, s⁻¹, hσ, ?_⟩
  set τ := (toUnit Γ.G ≫ σ) * 𝟙 Γ.G with hτ
  have hτpt : Γ.pt s ≫ τ = 1 := by
    rw [hτ, Hom.mul_def, ← Category.assoc, comp_lift, ← Category.assoc, comp_toUnit, hσ,
      Category.comp_id, ← Hom.mul_def, ← map_mul, inv_mul_cancel, map_one]
  have hτx : τ.left ((Γ.pt s).left x) = (η[Γ.G]).left ((toUnit (genPt R)).left x) := by
    have h1 : (Γ.pt s ≫ τ).left = (toUnit (genPt R) ≫ η[Γ.G]).left := by
      rw [hτpt, Hom.one_def]
    rw [Over.comp_left, Over.comp_left] at h1
    have h2 := congrArg (fun h => h x) h1
    simpa using h2
  have hw : (η[Γ.G]).left ≫ Γ.G.hom = 𝟙 _ := Over.w _
  haveI : UniversallyClosed ((η[Γ.G]).left ≫ Γ.G.hom) := by rw [hw]; infer_instance
  haveI : UniversallyClosed (η[Γ.G]).left :=
    UniversallyClosed.of_comp_of_isSeparated _ Γ.G.hom
  have hcl : IsClosed (Set.range (η[Γ.G]).left) := by
    have h := (η[Γ.G]).left.isClosedMap _ isClosed_univ
    rwa [Set.image_univ] at h
  have hspec : τ.left ((Γ.pt s).left x) ⤳ τ.left g := by
    rw [hx]; exact hg'g.map τ.left.continuous
  have hsubset : ({τ.left ((Γ.pt s).left x)} : Set Γ.G.left) ⊆ Set.range (η[Γ.G]).left :=
    Set.singleton_subset_iff.2 ⟨_, hτx.symm⟩
  have hmem : τ.left g ∈ Set.range (η[Γ.G]).left :=
    closure_minimal hsubset hcl (specializes_iff_mem_closure.1 hspec)
  obtain ⟨z, hz⟩ := hmem
  rw [← hz]
  exact hU'.one z

end GlobalTheory.CompanionTheory.Ar.BT.Transl
