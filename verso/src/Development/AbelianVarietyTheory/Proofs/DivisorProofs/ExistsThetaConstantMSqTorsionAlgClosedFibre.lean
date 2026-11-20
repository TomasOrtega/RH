import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaPointNormalisedThetaConstant
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaConstantsOverAlgClosedExtens
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin

/- English proof (translation)
Introduce `S G _ _ L ρ hL hρ g m K _ _ x θ p hm hK hP hpm`. Take `⟨P, α, -, hp, w, hw⟩` from `hP`. Establish `hLaw : Laws` using `GlobalTheory.firstFiveLaws.1`. Establish `hL₁` using `P.isLB`. Use `P.isAb.comm` as an intermediate fact.

Take `⟨ρ', hρ', hr⟩` from `exists_rigidificationPullbackCompatibleIso hp hw hL hL₁ hρ`. Set `τ : (baseOver (Sp K)).left ⟶ (Over.mk x).left` to `𝟙 (Sp K)`. Use `haveI : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp K)))`. Establish `hτ : τ ≫ (Over.mk x).hom = (baseOver (Sp K)).hom ≫ x` using `rfl`. Establish `hi : inv τ = 𝟙 (Sp K)` using `IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)`.

Take `⟨q, hq, hqm⟩` from `exists_torsion_down hp τ hτ p hpm`. Take `⟨v, hv⟩` from `ThetaPtExist.exists_isThetaPt hLaw K P m hm hK (fun _ : Unit => q) (fun _ => hqm)`. Set `c' : K` to `(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (v ())`. Establish `hvc : v = fun _ => GlobalTheory.Ex.fnOf c'` using `funext fun u => ((Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id_apply (v u)).symm`. Rewrite `hv` using `[hvc]`.

Take `⟨thP, hg, hth⟩` from `exists_gen_thG_of_isThetaPt K P ρ' hρ' m Unit (fun _ => q) (fun _ => c') (fun _ => hqm) hv`. Take `⟨th, hrel⟩` from `GlobalTheory.ThetaPtMove.exists_secRel_up hp τ hτ hw hL hL₁ thP`. Establish `hgen` using `ThetaPtUp.isGenSec_up hp τ hτ hw hL hL₁ hrel hg`. Establish `up` using `ThG.up hp τ hτ hw hL hL₁ hr hq hpm hrel (hth ())`. Rewrite `up` using `[hi]`.

Take `⟨r, hr'⟩` from `hgen θ`. Establish `e₁ : SecM.ofSec G θ = r • SecM.ofSec G th` using `Subtype.ext (funext hr')`. Establish `q'` using `ThG.smul hL e₁ up`. Use `⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (show Γ(Sp K, ⊤) from r) * c', ?_⟩` and prove the remaining obligations. Use `q' using 1` and compare the differences between its conclusion and the goal.

Simplify using `[GlobalTheory.ZH.fn, GlobalTheory.Ex.fnOf, c']`.
-/
theorem exists_thG_of_polFib : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (θ : SecAt G L x) (p : Over.mk x ⟶ G), Odd m → (m : K) ≠ 0 → PolFib G L g x → p ^ (m ^ 2) = 1 → ∃ c : K, ThG G L ρ m θ p (GlobalTheory.ZH.fn c) := by
  intro S G _ _ L ρ hL hρ g m K _ _ x θ p hm hK hP hpm
  obtain ⟨P, α, -, hp, w, hw⟩ := hP
  have hLaw : Laws := GlobalTheory.firstFiveLaws.1
  have hL₁ := P.isLB
  have := P.isAb.comm
  obtain ⟨ρ', hρ', hr⟩ := exists_rigidificationPullbackCompatibleIso hp hw hL hL₁ hρ
  let τ : (baseOver (Sp K)).left ⟶ (Over.mk x).left := 𝟙 (Sp K)
  haveI : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp K)))
  have hτ : τ ≫ (Over.mk x).hom = (baseOver (Sp K)).hom ≫ x := rfl
  have hi : inv τ = 𝟙 (Sp K) := IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)
  obtain ⟨q, hq, hqm⟩ := exists_torsion_down hp τ hτ p hpm
  obtain ⟨v, hv⟩ := ThetaPtExist.exists_isThetaPt hLaw K P m hm hK (fun _ : Unit => q) (fun _ => hqm)
  let c' : K := (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (v ())
  have hvc : v = fun _ => GlobalTheory.Ex.fnOf c' := funext fun u =>
    ((Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id_apply (v u)).symm
  rw [hvc] at hv
  obtain ⟨thP, hg, hth⟩ := exists_gen_thG_of_isThetaPt K P ρ' hρ' m Unit (fun _ => q) (fun _ => c') (fun _ => hqm) hv
  obtain ⟨th, hrel⟩ := GlobalTheory.ThetaPtMove.exists_secRel_up hp τ hτ hw hL hL₁ thP
  have hgen := ThetaPtUp.isGenSec_up hp τ hτ hw hL hL₁ hrel hg
  have up := ThG.up hp τ hτ hw hL hL₁ hr hq hpm hrel (hth ())
  rw [hi] at up
  obtain ⟨r, hr'⟩ := hgen θ
  have e₁ : SecM.ofSec G θ = r • SecM.ofSec G th := Subtype.ext (funext hr')
  have q' := ThG.smul hL e₁ up
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (show Γ(Sp K, ⊤) from r) * c', ?_⟩
  convert q' using 1
  simp [GlobalTheory.ZH.fn, GlobalTheory.Ex.fnOf, c']

end GlobalTheory.UMin
