import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaConstantsOverAlgClosedExtens
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedThetaConstantsEqScalarMulRootStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

noncomputable section

namespace GlobalTheory.Poinc.Sep.ModelRatio

/- English proof (translation)
Introduce `g n hn hodd`. Take `⟨j₀, hcore⟩` from `GlobalTheory.T.normalised_thetaConstants_eq_scalar_mul_root n hn hodd`. Use `⟨j₀, fun j hj V₁ _ _ _ hV hunit D hg X C _ e u mo hmo hT K _ _ ev k₀ hk₀ hrat o _ J b s t π₁ hp hL v hv a a' hne => ?_⟩` and prove the remaining obligations. Use `haveI : IsAlgClosed k₀ := hk₀`. Use `t.ab.comm` as an intermediate fact.

Take `⟨ρ₀, hρ₀⟩` from `D.P.rigid`. Take `⟨w, hw⟩` from `hL`. Take `⟨ρ, hρ, hr⟩` from `GlobalTheory.Ex.OneGen.exists_rigidificationPullbackCompatibleIso hp hw D.P.isLB t.isLB hρ₀`. Set `x : ZM.Ix g ((n ^ j) ^ 2) → (baseOver (Sp K) ⟶ t.pol.A)` to `fun a => (Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) ≫ t.lab a`. Establish `hx : ∀ i, x i ^ ((n ^ j) ^ 2) = 1` using `fun i => by show ((Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) ≫ t.lab i) ^ ((n ^ j) ^ 2) = 1`.

Rewrite using `[← MonObj.comp_pow, GlobalTheory.ThetaPtUp.lab_pow t i, MonObj.comp_one]`. Take `⟨thP, hg, hth⟩` from `GlobalTheory.T.exists_generator_thetaPoint_normalised_thetaConstants K t.pol ρ hρ (n ^ j) _ x v hx hv`. Set `τ : (baseOver (Sp K)).left ⟶ (Over.mk (spMap ev)).left` to `𝟙 (Sp K)`. Use `haveI : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp K)))`. Establish `hτ : τ ≫ (Over.mk (spMap ev)).hom = (baseOver (Sp K)).hom ≫ spMap ev` using `rfl`.

Establish `hi : inv τ = 𝟙 (Sp K)` using `IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)`. Take `⟨th, hrel⟩` from `GlobalTheory.ThetaPtMove.exists_secRel_up hp τ hτ hw D.P.isLB t.isLB thP`. Establish `hgen` using `GlobalTheory.ThetaPtUp.isGenSec_up hp τ hτ hw D.P.isLB t.isLB hrel hg`. Take `⟨M, lam, hM, hval⟩` from `hcore j hj V₁ hV hunit D X C e u mo hmo hT K ev ρ₀ hρ₀ th hgen`. Establish `up : ∀ i, ∃ c₀ : C, ∃ ζ : K, ζ ^ M = 1 ∧ v i = lam * ζ * ev (u 0 c₀)` using `fun i => by`.

Take `⟨y, hy, hy'⟩` from `GlobalTheory.Ex.OneGen.exists_torsion_up hp τ hτ (x i) (hx i)`. Establish `q` using `GlobalTheory.Ex.OneGen.ThG.up hp τ hτ hw D.P.isLB t.isLB hr hy hy' hrel (hth i)`. Rewrite `q` using `[hi]`. Conclude with `hval y (v i) q`. Take `⟨c₁, hc₁⟩` from `(hmo 0).2`.

Take `⟨c₀, ζ, hζ, hva⟩` from `up a`. Take `⟨c₀', ζ', hζ', hva'⟩` from `up a'`. Take `⟨s₁, hs₁, hs₁e⟩` from `hrat 0 c₀ c₁ hc₁`. Take `⟨s₂, hs₂, hs₂e⟩` from `hrat 0 c₀' c₁ hc₁`. Establish `hζk : ζ ∈ k₀` using `GlobalTheory.Poinc.Sep.Frames.mem_of_pow_mem k₀ hM (by rw [hζ]; exact k₀.one_mem)`.

Establish `hζk' : ζ' ∈ k₀` using `GlobalTheory.Poinc.Sep.Frames.mem_of_pow_mem k₀ hM (by rw [hζ']; exact k₀.one_mem)`. Rewrite `hne` using `[hva', hs₂e]`. Establish `h₁ : ζ' * s₂ ≠ 0` using `fun h => hne (by rw [show lam * ζ' * (s₂ * ev (u 0 c₁)) = lam * (ζ' * s₂) * ev (u 0 c₁) by ring, h]; ring)`. Use `⟨ζ * s₁ * (ζ' * s₂)⁻¹, k₀.mul_mem (k₀.mul_mem hζk hs₁) (k₀.inv_mem (k₀.mul_mem hζk' hs₂)), ?_⟩` and prove the remaining obligations. Rewrite using `[hva, hva', hs₁e, hs₂e]`.

Establish `e₁ : ζ * s₁ * (ζ' * s₂)⁻¹ * (lam * ζ' * (s₂ * ev (u 0 c₁))) = ζ * s₁ * ((ζ' * s₂)⁻¹ * (ζ' * s₂)) * (lam * ev (u 0 c₁))` using `by ring`. Rewrite using `[e₁, inv_mul_cancel₀ h₁]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem main : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (o : Type) [CommRing o] (J : Type) (b : ZM.TBase o ((n ^ j) ^ 2)) (s : Sp K ⟶ Sp o) (t : ZM.TObj g ((n ^ j) ^ 2) J b s) (π₁ : t.A.left ⟶ D.P.A.left), IsGrpPullback t.A D.P.A (spMap ev) π₁ → LBIso t.L (D.P.L.pull π₁) → ∀ v : ZM.Ix g ((n ^ j) ^ 2) → K, t.HasTh (𝟙 _) v → ∀ a a', v a' ≠ 0 → ∃ r ∈ k₀, v a = r * v a' := by
  intro g n hn hodd
  obtain ⟨j₀, hcore⟩ := GlobalTheory.T.normalised_thetaConstants_eq_scalar_mul_root n hn hodd
  refine ⟨j₀, fun j hj V₁ _ _ _ hV hunit D hg X C _ e u mo hmo hT K _ _ ev k₀ hk₀ hrat o _ J b s t π₁ hp hL v hv a a' hne => ?_⟩
  haveI : IsAlgClosed k₀ := hk₀
  have := t.ab.comm
  obtain ⟨ρ₀, hρ₀⟩ := D.P.rigid
  obtain ⟨w, hw⟩ := hL
  obtain ⟨ρ, hρ, hr⟩ := GlobalTheory.Ex.OneGen.exists_rigidificationPullbackCompatibleIso hp hw D.P.isLB t.isLB hρ₀
  let x : ZM.Ix g ((n ^ j) ^ 2) → (baseOver (Sp K) ⟶ t.pol.A) :=
    fun a => (Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) ≫ t.lab a
  have hx : ∀ i, x i ^ ((n ^ j) ^ 2) = 1 := fun i => by
    show ((Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) ≫ t.lab i) ^ ((n ^ j) ^ 2) = 1
    rw [← MonObj.comp_pow, GlobalTheory.ThetaPtUp.lab_pow t i, MonObj.comp_one]
  obtain ⟨thP, hg, hth⟩ := GlobalTheory.T.exists_generator_thetaPoint_normalised_thetaConstants K t.pol ρ hρ (n ^ j) _ x v hx hv
  let τ : (baseOver (Sp K)).left ⟶ (Over.mk (spMap ev)).left := 𝟙 (Sp K)
  haveI : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp K)))
  have hτ : τ ≫ (Over.mk (spMap ev)).hom = (baseOver (Sp K)).hom ≫ spMap ev := rfl
  have hi : inv τ = 𝟙 (Sp K) := IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)
  obtain ⟨th, hrel⟩ := GlobalTheory.ThetaPtMove.exists_secRel_up hp τ hτ hw D.P.isLB t.isLB thP
  have hgen := GlobalTheory.ThetaPtUp.isGenSec_up hp τ hτ hw D.P.isLB t.isLB hrel hg
  obtain ⟨M, lam, hM, hval⟩ := hcore j hj V₁ hV hunit D X C e u mo hmo hT K ev ρ₀ hρ₀ th hgen
  have up : ∀ i, ∃ c₀ : C, ∃ ζ : K, ζ ^ M = 1 ∧ v i = lam * ζ * ev (u 0 c₀) := fun i => by
    obtain ⟨y, hy, hy'⟩ := GlobalTheory.Ex.OneGen.exists_torsion_up hp τ hτ (x i) (hx i)
    have q := GlobalTheory.Ex.OneGen.ThG.up hp τ hτ hw D.P.isLB t.isLB hr hy hy' hrel (hth i)
    rw [hi] at q
    exact hval y (v i) q
  obtain ⟨c₁, hc₁⟩ := (hmo 0).2
  obtain ⟨c₀, ζ, hζ, hva⟩ := up a
  obtain ⟨c₀', ζ', hζ', hva'⟩ := up a'
  obtain ⟨s₁, hs₁, hs₁e⟩ := hrat 0 c₀ c₁ hc₁
  obtain ⟨s₂, hs₂, hs₂e⟩ := hrat 0 c₀' c₁ hc₁
  have hζk : ζ ∈ k₀ := GlobalTheory.Poinc.Sep.Frames.mem_of_pow_mem k₀ hM (by rw [hζ]; exact k₀.one_mem)
  have hζk' : ζ' ∈ k₀ := GlobalTheory.Poinc.Sep.Frames.mem_of_pow_mem k₀ hM (by rw [hζ']; exact k₀.one_mem)
  rw [hva', hs₂e] at hne
  have h₁ : ζ' * s₂ ≠ 0 := fun h => hne (by rw [show lam * ζ' * (s₂ * ev (u 0 c₁)) = lam * (ζ' * s₂) * ev (u 0 c₁) by ring, h]; ring)
  refine ⟨ζ * s₁ * (ζ' * s₂)⁻¹, k₀.mul_mem (k₀.mul_mem hζk hs₁) (k₀.inv_mem (k₀.mul_mem hζk' hs₂)), ?_⟩
  rw [hva, hva', hs₁e, hs₂e]
  have e₁ : ζ * s₁ * (ζ' * s₂)⁻¹ * (lam * ζ' * (s₂ * ev (u 0 c₁))) =
      ζ * s₁ * ((ζ' * s₂)⁻¹ * (ζ' * s₂)) * (lam * ev (u 0 c₁)) := by ring
  rw [e₁, inv_mul_cancel₀ h₁]
  ring

end GlobalTheory.Poinc.Sep.ModelRatio
