import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedGLMassFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralPointsOpenCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPositiveHermitianFormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryGroupCompactQuotientStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedCentralizerUnitaryIffStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwCentRatFCommStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTorsionCentralizerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTorsionLatticeCompactStatement

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.RatFinG

/- English proof (translation)
Establish `hX : IsCompact ((fun p : G × G => p.1 * n₀ * p.2⁻¹) '' (C ×ˢ C))` using `(hC.prod hC).image (by fun_prop)`. Establish `hF` using `hfin _ hX`. Set `rep : G → G` to `fun f => if h : ∃ γ ∈ Γ, γ⁻¹ * n₀ * γ = f then h.choose else 1`. Establish `hrep : ∀ f, (∃ γ ∈ Γ, γ⁻¹ * n₀ * γ = f) → rep f ∈ Γ ∧ (rep f)⁻¹ * n₀ * rep f = f`. Introduce `f h`.

Simplify using `only [rep, dif_pos h]`. Conclude with `h.choose_spec`. Use `⟨⋃ f ∈ (Γ : Set G) ∩ _, (fun c => rep f * c) '' C, hF.isCompact_biUnion fun f _ => hC.image (by fun_prop), ?_⟩` and prove the remaining obligations. Introduce `t ht hcomm`. Take `⟨γ, hγ, c, hc, rfl⟩` from `hcov t ht`.

Use `set f := γ⁻¹ * n₀ * γ with hf`. Establish `hfc : f = c * n₀ * c⁻¹`. Establish `e : γ⁻¹ * n₀ * γ * c = c * n₀`. Establish `: n₀ * (γ * c) = γ * c * n₀` using `hcomm.symm`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hf, eq_mul_inv_iff_mul_eq, e]`. Establish `hfΓ : f ∈ Γ` using `mul_mem (mul_mem (inv_mem hγ) hn) hγ`. Take `⟨h1, h2⟩` from `hrep f ⟨γ, hγ, rfl⟩`. Use `⟨γ * (rep f)⁻¹, mul_mem hγ (inv_mem h1), ?_, rep f * c, ?_, by group⟩` and prove the remaining obligations. Establish `e : (rep f)⁻¹ * n₀ * rep f = γ⁻¹ * n₀ * γ` using `h2`.

Combine the equalities or inequalities in the displayed calculation. Use `Set.mem_biUnion (x := f) ⟨hfΓ, ⟨(c, c), ⟨hc, hc⟩, hfc.symm⟩⟩ ⟨c, hc, rfl⟩` and prove the remaining obligations.
-/
theorem selberg {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U Γ : Subgroup G) (C : Set G) (n₀ : G)
    (hC : IsCompact C) (hcov : ∀ g ∈ U, ∃ γ ∈ Γ, ∃ c ∈ C, g = γ * c)
    (hfin : ∀ X : Set G, IsCompact X → ((Γ : Set G) ∩ X).Finite) (hn : n₀ ∈ Γ) :
    ∃ C' : Set G, IsCompact C' ∧ ∀ t ∈ U, t * n₀ = n₀ * t → ∃ γ ∈ Γ, γ * n₀ = n₀ * γ ∧ ∃ c ∈ C', t = γ * c := by
  have hX : IsCompact ((fun p : G × G => p.1 * n₀ * p.2⁻¹) '' (C ×ˢ C)) :=
    (hC.prod hC).image (by fun_prop)
  have hF := hfin _ hX
  let rep : G → G := fun f => if h : ∃ γ ∈ Γ, γ⁻¹ * n₀ * γ = f then h.choose else 1
  have hrep : ∀ f, (∃ γ ∈ Γ, γ⁻¹ * n₀ * γ = f) → rep f ∈ Γ ∧ (rep f)⁻¹ * n₀ * rep f = f := by
    intro f h
    simp only [rep, dif_pos h]
    exact h.choose_spec
  refine ⟨⋃ f ∈ (Γ : Set G) ∩ _, (fun c => rep f * c) '' C, hF.isCompact_biUnion fun f _ =>
    hC.image (by fun_prop), ?_⟩
  intro t ht hcomm
  obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov t ht
  set f := γ⁻¹ * n₀ * γ with hf
  have hfc : f = c * n₀ * c⁻¹ := by
    have e : γ⁻¹ * n₀ * γ * c = c * n₀ := by
      have : n₀ * (γ * c) = γ * c * n₀ := hcomm.symm
      calc γ⁻¹ * n₀ * γ * c = γ⁻¹ * (n₀ * (γ * c)) := by group
        _ = γ⁻¹ * (γ * c * n₀) := by rw [this]
        _ = c * n₀ := by group
    rw [hf, eq_mul_inv_iff_mul_eq, e]
  have hfΓ : f ∈ Γ := mul_mem (mul_mem (inv_mem hγ) hn) hγ
  obtain ⟨h1, h2⟩ := hrep f ⟨γ, hγ, rfl⟩
  refine ⟨γ * (rep f)⁻¹, mul_mem hγ (inv_mem h1), ?_, rep f * c, ?_, by group⟩
  · have e : (rep f)⁻¹ * n₀ * rep f = γ⁻¹ * n₀ * γ := h2
    calc γ * (rep f)⁻¹ * n₀ = γ * ((rep f)⁻¹ * n₀ * rep f) * (rep f)⁻¹ := by group
      _ = γ * (γ⁻¹ * n₀ * γ) * (rep f)⁻¹ := by rw [e]
      _ = n₀ * (γ * (rep f)⁻¹) := by group
  · refine Set.mem_biUnion (x := f) ⟨hfΓ, ⟨(c, c), ⟨hc, hc⟩, hfc.symm⟩⟩ ⟨c, hc, rfl⟩

abbrev gam1 (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (δ : GL (Fin n) E) : Subgroup (GL (Fin n) (Af E)) :=
  (ratF E n).range ⊓ twCent (thF E n) (ratF E n δ)

/- English proof (translation)
Use `haveI : Nontrivial (Af E) := by`. Take `⟨P, hP⟩` from `Ideal.exists_maximal (𝓞 E)`. Conclude with `(Formalism.UG.evalV E ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)⟩).toRingHom.domain_nontrivial`. Conclude with `(algebraMap E (Af E)).injective`.
-/
theorem algebraMap_inj (E : Type) [Field E] [NumberField E] : Function.Injective (algebraMap E (Af E)) := by
  haveI : Nontrivial (Af E) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 E)
    exact (Formalism.UG.evalV E ⟨P, hP.isPrime,
      Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)⟩).toRingHom.domain_nontrivial
  exact (algebraMap E (Af E)).injective

/- English proof (translation)
Introduce `a b h`. Use `Units.ext (Matrix.ext fun i j => algebraMap_inj E ?_)` and prove the remaining obligations. Conclude with `congrArg (fun g : GL (Fin n) (Af E) => g.val i j) h`.
-/
theorem ratF_injective (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    Function.Injective (ratF E n) := by
  intro a b h
  refine Units.ext (Matrix.ext fun i j => algebraMap_inj E ?_)
  exact congrArg (fun g : GL (Fin n) (Af E) => g.val i j) h

/- English proof (translation)
Establish `hi` using `algebraMap_inj E`. Establish `hv : (ratF E n γ).val = γ.val.map (algebraMap E (Af E))` using `rfl`. Establish `hcT : cT (conjFin (IsCMField.complexConj E).toRingEquiv) (γ.val.map (algebraMap E (Af E))) = (cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.val).map (algebraMap E (Af E))`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Conclude with `conjFin_algebraMap _ _`.

Express the relevant statement in the definitionally equal form `cT _ (ratF E n γ).val * _ * (ratF E n γ).val = _ ↔ cT _ γ.val * H * γ.val = H`. Rewrite using `[hv, hcT, ← Matrix.map_mul, ← Matrix.map_mul]`. Conclude with `⟨fun h => Matrix.map_injective hi h, fun h => by rw [h]⟩`.
-/
theorem ratF_mem_UJ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (H : Matrix (Fin n) (Fin n) E)
    (γ : GL (Fin n) E) : ratF E n γ ∈ UJ (conjFin (IsCMField.complexConj E).toRingEquiv) (H.map (algebraMap E (Af E))) ↔
      γ ∈ UJ (IsCMField.complexConj E).toRingEquiv.toRingHom H := by
  have hi := algebraMap_inj E
  have hv : (ratF E n γ).val = γ.val.map (algebraMap E (Af E)) := rfl
  have hcT : cT (conjFin (IsCMField.complexConj E).toRingEquiv) (γ.val.map (algebraMap E (Af E))) =
      (cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.val).map (algebraMap E (Af E)) := by
    refine Matrix.ext fun i j => ?_
    exact conjFin_algebraMap _ _
  change cT _ (ratF E n γ).val * _ * (ratF E n γ).val = _ ↔ cT _ γ.val * H * γ.val = H
  rw [hv, hcT, ← Matrix.map_mul, ← Matrix.map_mul]
  exact ⟨fun h => Matrix.map_injective hi h, fun h => by rw [h]⟩

/- English proof (translation)
Establish `hs : (δ * thE E n δ).val.charpoly.Separable` using `hδ.2.2.1`. Establish `hr : ∀ τ : E →+* ℂ, ∀ z ∈ ((δ * thE E n δ).val.charpoly.map τ).roots, ‖z‖ = 1` using `hδ.2.2.2`. Take `⟨H, hu, hh, hN, hp⟩` from `GlobalTheory.T.exists_positive_hermitian_form E n _ hs hr`. Take `⟨⟨C₀, hC₀, hcov⟩, hfin⟩` from `GlobalTheory.T.unitary_group_compact_quotient E n H hu hh hp`. Establish `hc` using `GlobalTheory.T.twisted_centralizer_unitary_iff E n δ H hs hu hN`.

Use `set U := UJ (conjFin (IsCMField.complexConj E).toRingEquiv) (H.map (algebraMap E (Af E))) with hU`. Use `set Γ := (UJ (IsCMField.complexConj E).toRingEquiv.toRingHom H).map (ratF E n) with hΓ`. Establish `hΓfin : ∀ X : Set (GL (Fin n) (Af E)), IsCompact X → ((Γ : Set (GL (Fin n) (Af E))) ∩ X).Finite`. Introduce `X hX`. Use `((hfin X hX).image (ratF E n)).subset ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨⟨γ, hγ, rfl⟩, hx⟩`. Conclude with `⟨γ, ⟨hγ, hx⟩, rfl⟩`. Establish `hsub : ∀ y ∈ gam1 E n δ, y ∈ Γ`. Introduce and unpack `_ ⟨⟨γ, rfl⟩, ht⟩`. Conclude with `⟨γ, (ratF_mem_UJ E n H γ).1 ((hc _).1 ht).1, rfl⟩`.

Take `⟨C', hC', hsel⟩` from `selberg U Γ C₀ (ratF E n (δ * thE E n δ)) hC₀ (fun g hg => by`. Take `⟨γ, hγ, k, hk, e⟩` from `hcov g hg`. Conclude with `⟨_, ⟨γ, hγ, rfl⟩, k, hk, e⟩)`. Use `hΓfin ⟨_, hN, rfl⟩`. Use `⟨⟨C', hC', fun t ht => ?_⟩, fun X hX => (hΓfin X hX).subset fun y hy => ⟨hsub y hy.1, hy.2⟩, ?_⟩` and prove the remaining obligations.

Take `⟨h1, h2⟩` from `(hc t).1 ht`. Take `⟨γ, hγ, hcm, c, hc', e⟩` from `hsel t h1 h2`. Take `⟨γ₀, hγ₀, rfl⟩` from `hγ`. Conclude with `⟨ratF E n γ₀, ⟨⟨γ₀, rfl⟩, (hc _).2 ⟨(ratF_mem_UJ E n H γ₀).2 hγ₀, hcm⟩⟩, c, hc', e⟩`. Use `((GlobalTheory.T.finite_torsion_centralizer_alt E n _ hs).image (ratF E n)).subset ?_` and prove the remaining obligations.

Introduce and unpack `y ⟨hy, hfo⟩`. Take `⟨⟨γ, rfl⟩, ht⟩` from `hy`. Use `⟨γ, ⟨ratF_injective E n ?_, ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[map_mul (ratF E n) γ, map_mul (ratF E n) _ γ]`. Conclude with `((hc _).1 ht).2`.

Conclude with `(ratF_injective E n).isOfFinOrder_iff.1 hfo`.
-/
theorem factor (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (δ : GL (Fin n) E) (hδ : polE δ ∈ Ell E n) :
    (∃ C : Set (GL (Fin n) (Af E)), IsCompact C ∧ ∀ t ∈ twCent (thF E n) (ratF E n δ), ∃ γ ∈ gam1 E n δ, ∃ c ∈ C, t = γ * c) ∧
    (∀ X : Set (GL (Fin n) (Af E)), IsCompact X → ((gam1 E n δ : Set (GL (Fin n) (Af E))) ∩ X).Finite) ∧
    {γ : GL (Fin n) (Af E) | γ ∈ gam1 E n δ ∧ IsOfFinOrder γ}.Finite := by
  have hs : (δ * thE E n δ).val.charpoly.Separable := hδ.2.2.1
  have hr : ∀ τ : E →+* ℂ, ∀ z ∈ ((δ * thE E n δ).val.charpoly.map τ).roots, ‖z‖ = 1 := hδ.2.2.2
  obtain ⟨H, hu, hh, hN, hp⟩ := GlobalTheory.T.exists_positive_hermitian_form E n _ hs hr
  obtain ⟨⟨C₀, hC₀, hcov⟩, hfin⟩ := GlobalTheory.T.unitary_group_compact_quotient E n H hu hh hp
  have hc := GlobalTheory.T.twisted_centralizer_unitary_iff E n δ H hs hu hN
  set U := UJ (conjFin (IsCMField.complexConj E).toRingEquiv) (H.map (algebraMap E (Af E))) with hU
  set Γ := (UJ (IsCMField.complexConj E).toRingEquiv.toRingHom H).map (ratF E n) with hΓ
  have hΓfin : ∀ X : Set (GL (Fin n) (Af E)), IsCompact X → ((Γ : Set (GL (Fin n) (Af E))) ∩ X).Finite := by
    intro X hX
    refine ((hfin X hX).image (ratF E n)).subset ?_
    rintro _ ⟨⟨γ, hγ, rfl⟩, hx⟩
    exact ⟨γ, ⟨hγ, hx⟩, rfl⟩
  have hsub : ∀ y ∈ gam1 E n δ, y ∈ Γ := by
    rintro _ ⟨⟨γ, rfl⟩, ht⟩
    exact ⟨γ, (ratF_mem_UJ E n H γ).1 ((hc _).1 ht).1, rfl⟩
  obtain ⟨C', hC', hsel⟩ := selberg U Γ C₀ (ratF E n (δ * thE E n δ)) hC₀
    (fun g hg => by
      obtain ⟨γ, hγ, k, hk, e⟩ := hcov g hg
      exact ⟨_, ⟨γ, hγ, rfl⟩, k, hk, e⟩)
    hΓfin ⟨_, hN, rfl⟩
  refine ⟨⟨C', hC', fun t ht => ?_⟩, fun X hX => (hΓfin X hX).subset fun y hy => ⟨hsub y hy.1, hy.2⟩, ?_⟩
  · obtain ⟨h1, h2⟩ := (hc t).1 ht
    obtain ⟨γ, hγ, hcm, c, hc', e⟩ := hsel t h1 h2
    obtain ⟨γ₀, hγ₀, rfl⟩ := hγ
    exact ⟨ratF E n γ₀, ⟨⟨γ₀, rfl⟩, (hc _).2 ⟨(ratF_mem_UJ E n H γ₀).2 hγ₀, hcm⟩⟩, c, hc', e⟩
  · refine ((GlobalTheory.T.finite_torsion_centralizer_alt E n _ hs).image (ratF E n)).subset ?_
    rintro y ⟨hy, hfo⟩
    obtain ⟨⟨γ, rfl⟩, ht⟩ := hy
    refine ⟨γ, ⟨ratF_injective E n ?_, ?_⟩, rfl⟩
    · rw [map_mul (ratF E n) γ, map_mul (ratF E n) _ γ]
      exact ((hc _).1 ht).2
    · exact (ratF_injective E n).isOfFinOrder_iff.1 hfo

/- English proof (translation)
Express the relevant statement in the definitionally equal form `p * (x, y) = (x, y) * thP E a b p ↔ p.1 * x = x * thF E a p.1 ∧ p.2 * y = y * thF E b p.2`. Conclude with `Prod.ext_iff`.
-/
theorem mem_twCent_thP {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (x : GL (Fin a) (Af E)) (y : GL (Fin b) (Af E))
    (p : Gf E a b) : p ∈ twCent (thP E a b) (x, y) ↔ p.1 ∈ twCent (thF E a) x ∧ p.2 ∈ twCent (thF E b) y := by
  change p * (x, y) = (x, y) * thP E a b p ↔ p.1 * x = x * thF E a p.1 ∧ p.2 * y = y * thF E b p.2
  exact Prod.ext_iff

/- English proof (translation)
Rewrite using `[gam, Subgroup.mem_inf, mem_twCent_thP, gam1, gam1, Subgroup.mem_inf, Subgroup.mem_inf]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨q, rfl⟩, h1, h2⟩`. Conclude with `⟨⟨⟨q.1, rfl⟩, h1⟩, ⟨q.2, rfl⟩, h2⟩`. Introduce and unpack `⟨⟨⟨q₁, e₁⟩, h1⟩, ⟨q₂, e₂⟩, h2⟩`.

Conclude with `⟨⟨(q₁, q₂), Prod.ext e₁ e₂⟩, h1, h2⟩`.
-/
theorem mem_gam {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E)
    (p : Gf E a b) : p ∈ gam δ₁ δ₂ ↔ p.1 ∈ gam1 E a δ₁ ∧ p.2 ∈ gam1 E b δ₂ := by
  rw [gam, Subgroup.mem_inf, mem_twCent_thP, gam1, gam1, Subgroup.mem_inf, Subgroup.mem_inf]
  constructor
  · rintro ⟨⟨q, rfl⟩, h1, h2⟩
    exact ⟨⟨⟨q.1, rfl⟩, h1⟩, ⟨q.2, rfl⟩, h2⟩
  · rintro ⟨⟨⟨q₁, e₁⟩, h1⟩, ⟨q₂, e₂⟩, h2⟩
    exact ⟨⟨(q₁, q₂), Prod.ext e₁ e₂⟩, h1, h2⟩

/- English proof (translation)
Introduce `E _ _ _ _ a b δ₁ δ₂ h₁ h₂`. Use `haveI : T2Space (Af E) := inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) Filter.cofinite))`. Take `⟨⟨C₁, hC₁, hc₁⟩, hf₁, ht₁⟩` from `factor E a δ₁ h₁`. Take `⟨⟨C₂, hC₂, hc₂⟩, hf₂, ht₂⟩` from `factor E b δ₂ h₂`. Establish `hs₁ : (δ₁ * thE E a δ₁).val.charpoly.Separable` using `h₁.2.2.1`.

Establish `hs₂ : (δ₂ * thE E b δ₂).val.charpoly.Separable` using `h₂.2.2.1`. Establish `hK₁` using `GlobalTheory.T.finite_kernel_compact_open E a`. Establish `hK₂` using `GlobalTheory.T.finite_kernel_compact_open E b`. Establish `hKc : (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) = (Kf E a : Set _) ×ˢ (Kf E b : Set _)` using `Subgroup.coe_prod _ _`. Establish `hKo : IsOpen (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b))`.

Rewrite using `[hKc]`. Conclude with `hK₁.1.prod hK₂.1`. Establish `hKcp : IsCompact (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b))`. Rewrite using `[hKc]`. Conclude with `hK₁.2.prod hK₂.2`.

Establish `hcl : IsClosed ((twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂) : Subgroup (Gf E a b)) : Set (Gf E a b))`. Establish `e : ((twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂) : Subgroup (Gf E a b)) : Set (Gf E a b)) = (twCent (thF E a) (ratF E a δ₁) : Set _) ×ˢ (twCent (thF E b) (ratF E b δ₂) : Set _)`. Use extensionality with `p`. Conclude with `mem_twCent_thP _ _ p`. Rewrite using `[e]`.

Conclude with `(GlobalTheory.MassNorm.isClosed_twCent_thF E a _).prod (GlobalTheory.MassNorm.isClosed_twCent_thF E b _)`. Use `set T := twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂) with hTdef`. Establish `hcomm : ∀ p ∈ T, ∀ q ∈ T, p * q = q * p` using `fun p hp q hq => by`. Rewrite `hp`, `hq` using `[hTdef, mem_twCent_thP]`. Conclude with `Prod.ext (GlobalTheory.T.twCent_comm_of_charpoly_separable E a δ₁ hs₁ _ hp.1 _ hq.1) (GlobalTheory.T.twCent_comm_of_charpoly_separable E b δ₂ hs₂ _ hp.2 _ hq.2)`.

Establish `hle : gam δ₁ δ₂ ≤ T` using `fun p hp => hp.2`. Establish `hcov : ∀ t ∈ T, ∃ γ ∈ gam δ₁ δ₂, ∃ c ∈ C₁ ×ˢ C₂, t = γ * c` using `fun t ht => by`. Rewrite `ht` using `[hTdef, mem_twCent_thP]`. Take `⟨γ₁, hγ₁, c₁, hcc₁, e₁⟩` from `hc₁ _ ht.1`. Take `⟨γ₂, hγ₂, c₂, hcc₂, e₂⟩` from `hc₂ _ ht.2`.

Conclude with `⟨(γ₁, γ₂), (mem_gam δ₁ δ₂ _).2 ⟨hγ₁, hγ₂⟩, (c₁, c₂), ⟨hcc₁, hcc₂⟩, Prod.ext e₁ e₂⟩`. Establish `hfin : ∀ X : Set (Gf E a b), IsCompact X → ((gam δ₁ δ₂ : Set (Gf E a b)) ∩ X).Finite` using `fun X hX => by`. Establish `h1` using `hf₁ _ (hX.image continuous_fst)`. Establish `h2` using `hf₂ _ (hX.image continuous_snd)`. Use `(h1.prod h2).subset ?_` and prove the remaining obligations.

Introduce and unpack `p ⟨hp, hx⟩`. Establish `hp'` using `(mem_gam δ₁ δ₂ p).1 hp`. Conclude with `⟨⟨hp'.1, ⟨p, hx, rfl⟩⟩, hp'.2, ⟨p, hx, rfl⟩⟩`. Establish `htor : {γ : Gf E a b | γ ∈ gam δ₁ δ₂ ∧ IsOfFinOrder γ}.Finite`. Use `(ht₁.prod ht₂).subset ?_` and prove the remaining obligations.

Introduce and unpack `p ⟨hp, hfo⟩`. Establish `hp'` using `(mem_gam δ₁ δ₂ p).1 hp`. Take `⟨k, hk, e⟩` from `isOfFinOrder_iff_pow_eq_one.1 hfo`. Establish `e' : p.1 ^ k = 1 ∧ p.2 ^ k = 1` using `Prod.ext_iff.1 e`. Conclude with `⟨⟨hp'.1, isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, e'.1⟩⟩, hp'.2, isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, e'.2⟩⟩`.

Establish `hmain` using `GlobalTheory.T.finite_torsion_lattice_compact (Gf E a b) ((Kf E a).prod (Kf E b)) T (gam δ₁ δ₂) (C₁ ×ˢ C₂) hKo hKcp hcl hcomm hle (hC₁.prod hC₂) hcov hfin htor`. Conclude with `⟨⟨hcomm, hmain.1⟩, hmain.2.1, hmain.2.2.1, hmain.2.2.2⟩`.
-/
theorem ratFin : PositivityTheory.Rg.BcB.G8.Fin.RatFin := by
  intro E _ _ _ _ a b δ₁ δ₂ h₁ h₂
  haveI : T2Space (Af E) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) Filter.cofinite))
  obtain ⟨⟨C₁, hC₁, hc₁⟩, hf₁, ht₁⟩ := factor E a δ₁ h₁
  obtain ⟨⟨C₂, hC₂, hc₂⟩, hf₂, ht₂⟩ := factor E b δ₂ h₂
  have hs₁ : (δ₁ * thE E a δ₁).val.charpoly.Separable := h₁.2.2.1
  have hs₂ : (δ₂ * thE E b δ₂).val.charpoly.Separable := h₂.2.2.1
  have hK₁ := GlobalTheory.T.finite_kernel_compact_open E a
  have hK₂ := GlobalTheory.T.finite_kernel_compact_open E b
  have hKc : (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) = (Kf E a : Set _) ×ˢ (Kf E b : Set _) :=
    Subgroup.coe_prod _ _
  have hKo : IsOpen (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) := by
    rw [hKc]; exact hK₁.1.prod hK₂.1
  have hKcp : IsCompact (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) := by
    rw [hKc]; exact hK₁.2.prod hK₂.2
  have hcl : IsClosed ((twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂) : Subgroup (Gf E a b)) : Set (Gf E a b)) := by
    have e : ((twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂) : Subgroup (Gf E a b)) : Set (Gf E a b)) =
        (twCent (thF E a) (ratF E a δ₁) : Set _) ×ˢ (twCent (thF E b) (ratF E b δ₂) : Set _) := by
      ext p
      exact mem_twCent_thP _ _ p
    rw [e]
    exact (GlobalTheory.MassNorm.isClosed_twCent_thF E a _).prod (GlobalTheory.MassNorm.isClosed_twCent_thF E b _)
  set T := twCent (thP E a b) (ratF E a δ₁, ratF E b δ₂) with hTdef
  have hcomm : ∀ p ∈ T, ∀ q ∈ T, p * q = q * p := fun p hp q hq => by
    rw [hTdef, mem_twCent_thP] at hp hq
    exact Prod.ext (GlobalTheory.T.twCent_comm_of_charpoly_separable E a δ₁ hs₁ _ hp.1 _ hq.1) (GlobalTheory.T.twCent_comm_of_charpoly_separable E b δ₂ hs₂ _ hp.2 _ hq.2)
  have hle : gam δ₁ δ₂ ≤ T := fun p hp => hp.2
  have hcov : ∀ t ∈ T, ∃ γ ∈ gam δ₁ δ₂, ∃ c ∈ C₁ ×ˢ C₂, t = γ * c := fun t ht => by
    rw [hTdef, mem_twCent_thP] at ht
    obtain ⟨γ₁, hγ₁, c₁, hcc₁, e₁⟩ := hc₁ _ ht.1
    obtain ⟨γ₂, hγ₂, c₂, hcc₂, e₂⟩ := hc₂ _ ht.2
    exact ⟨(γ₁, γ₂), (mem_gam δ₁ δ₂ _).2 ⟨hγ₁, hγ₂⟩, (c₁, c₂), ⟨hcc₁, hcc₂⟩, Prod.ext e₁ e₂⟩
  have hfin : ∀ X : Set (Gf E a b), IsCompact X → ((gam δ₁ δ₂ : Set (Gf E a b)) ∩ X).Finite := fun X hX => by
    have h1 := hf₁ _ (hX.image continuous_fst)
    have h2 := hf₂ _ (hX.image continuous_snd)
    refine (h1.prod h2).subset ?_
    rintro p ⟨hp, hx⟩
    have hp' := (mem_gam δ₁ δ₂ p).1 hp
    exact ⟨⟨hp'.1, ⟨p, hx, rfl⟩⟩, hp'.2, ⟨p, hx, rfl⟩⟩
  have htor : {γ : Gf E a b | γ ∈ gam δ₁ δ₂ ∧ IsOfFinOrder γ}.Finite := by
    refine (ht₁.prod ht₂).subset ?_
    rintro p ⟨hp, hfo⟩
    have hp' := (mem_gam δ₁ δ₂ p).1 hp
    obtain ⟨k, hk, e⟩ := isOfFinOrder_iff_pow_eq_one.1 hfo
    have e' : p.1 ^ k = 1 ∧ p.2 ^ k = 1 := Prod.ext_iff.1 e
    exact ⟨⟨hp'.1, isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, e'.1⟩⟩, hp'.2, isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, e'.2⟩⟩
  have hmain := GlobalTheory.T.finite_torsion_lattice_compact (Gf E a b) ((Kf E a).prod (Kf E b)) T (gam δ₁ δ₂)
    (C₁ ×ˢ C₂) hKo hKcp hcl hcomm hle (hC₁.prod hC₂) hcov hfin htor
  exact ⟨⟨hcomm, hmain.1⟩, hmain.2.1, hmain.2.2.1, hmain.2.2.2⟩

end GlobalTheory.CompanionTheory.RatFinG
