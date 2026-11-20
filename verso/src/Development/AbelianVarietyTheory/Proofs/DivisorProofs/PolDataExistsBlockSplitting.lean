import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterExponentListStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryMaximalCompactLocalConjStatement
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstOfPolConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOrbitContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatchingExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalCharactersParabolicInductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDataLocalExpansionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCompactElementInStabilizerStatement

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ThK.ThetaKV

/- English proof (translation)
Establish `hsurj : Function.Surjective (Z ∘ₗ S.subtype)`. Introduce `u`. Establish `hu : u ∈ S.map Z` using `by rw [hon]; trivial`. Take `⟨ψ, hψ, e⟩` from `hu`. Conclude with `⟨⟨ψ, hψ⟩, e⟩`.

Take `⟨s, hs⟩` from `(Z ∘ₗ S.subtype).exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hsurj)`. Conclude with `⟨S.subtype ∘ₗ s, fun u => ⟨(s u).2, LinearMap.congr_fun hs u⟩⟩`.
-/
theorem exists_section {P V : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup V] [Module ℂ V]
    (S : Submodule ℂ P) (Z : P →ₗ[ℂ] V) (hon : S.map Z = ⊤) : ∃ s : V →ₗ[ℂ] P, ∀ u, s u ∈ S ∧ Z (s u) = u := by
  have hsurj : Function.Surjective (Z ∘ₗ S.subtype) := by
    intro u
    have hu : u ∈ S.map Z := by rw [hon]; trivial
    obtain ⟨ψ, hψ, e⟩ := hu
    exact ⟨⟨ψ, hψ⟩, e⟩
  obtain ⟨s, hs⟩ := (Z ∘ₗ S.subtype).exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hsurj)
  exact ⟨S.subtype ∘ₗ s, fun u => ⟨(s u).2, LinearMap.congr_fun hs u⟩⟩

/- English proof (translation)
Establish `h3` using `hL (hker _ (sub_mem h₁ h₂) (by rw [map_sub, h, sub_self]))`. Rewrite `h3` using `[LinearMap.mem_ker, map_sub, sub_eq_zero]`. Then use the resulting hypothesis.
-/
theorem eq_of_eq_of_ker {P V Y : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup V] [Module ℂ V] [AddCommGroup Y]
    [Module ℂ Y] {S N : Submodule ℂ P} {Z : P →ₗ[ℂ] V} (hker : ∀ φ ∈ S, Z φ = 0 → φ ∈ N) {L : P →ₗ[ℂ] Y}
    (hL : N ≤ LinearMap.ker L) {ψ₁ ψ₂ : P} (h₁ : ψ₁ ∈ S) (h₂ : ψ₂ ∈ S) (h : Z ψ₁ = Z ψ₂) : L ψ₁ = L ψ₂ := by
  have h3 := hL (hker _ (sub_mem h₁ h₂) (by rw [map_sub, h, sub_self]))
  rwa [LinearMap.mem_ker, map_sub, sub_eq_zero] at h3

/- English proof (translation)
Rewrite using `[← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]`. Use `congr 2`. Use `group`.
-/
theorem rep_conj {Gp V : Type} [Group Gp] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ Gp V) (B₀ g : Gp) (w : V) :
    π (B₀ * g * B₀⁻¹) (π B₀ w) = π B₀ (π g w) := by
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  group

/- English proof (translation)
Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`.
-/
theorem rep_inv {Gp V : Type} [Group Gp] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ Gp V) (B₀ : Gp) (w : V) :
    π B₀ (π B₀⁻¹ w) = w := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ B a a' G X om om' hK hT c hc hσc Φ hΦ B₀`. Take `⟨b, hb, χ, hbl, hsm, hun, Z, hon, hker, heq⟩` from `GlobalTheory.T.exists_local_characters_parabolic_induction F E σ B a a' G X om om' hK hT`. Take `⟨m, φ, L, hφ, hL0, hLeq, hI⟩` from `GlobalTheory.T.polynomial_data_local_expansion F E σ B a a' G X om om' hK hT Φ hΦ`. Use `⟨b, hb, χ, hbl, hsm, hun, ?_⟩` and prove the remaining obligations. Take `⟨s, hs⟩` from `exists_section _ Z hon`.

Establish `h1 : (1 : UA σ G.V.J) ∈ UAt σ G.V (evFin F B.v₁)`. Introduce `u _`. Use `show u • (mat (1 : UA σ G.V.J) - 1) = 0`. Establish `e1 : mat (1 : UA σ G.V.J) = 1` using `rfl`. Rewrite using `[e1, sub_self, smul_zero]`.

Use `⟨m, fun j => LinearMap.funLeft ℂ ℂ (toGAd hσ G.W.J hc).symm ∘ₗ L j ∘ₗ s ∘ₗ pairInd (Fv F B.v₁) b hb χ B₀, fun j => pairInd (Fv F B.v₁) b hb χ B₀⁻¹ (Z (φ j)), fun j => ?_, ?_⟩` and prove the remaining obligations. Introduce `g x hx w y`. Take `⟨hh, hmat⟩` from `GlobalTheory.T.local_compact_element_in_stabilizer F E σ hσ (a + a') G.W c hc B.v₁ B.τ₁ B₀ g x hx`. Take `⟨ψ₁, ⟨hψ₁, hact⟩, -⟩` from `(GlobalTheory.T.theta_action_exists hK.base F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ (GlobalTheory.ThKConst.isPair_big hT) B.v₁).1 1 h1 ((toGAd hσ G.W.J hc).symm (emb σ (c • G.W.J.map σ) B.v₁ x)) hh (s (pairInd (Fv F B.v₁) b hb χ B₀ w)) (hs _).1`. Establish `hZ` using `heq (B₀ * g * B₀⁻¹) _ hh hmat _ (hs _).1 ψ₁ hψ₁ hact`.

Rewrite `hZ` using `[(hs _).2, rep_conj]`. Establish `e2` using `eq_of_eq_of_ker hker (hL0 j) (hs (pairInd (Fv F B.v₁) b hb χ B₀ (pairInd (Fv F B.v₁) b hb χ g w))).1 hψ₁ (by rw [(hs _).2, hZ])`. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, LinearMap.funLeft_apply]`. Establish `e3` using `hLeq j ((toGAd hσ G.W.J hc).symm (emb σ (c • G.W.J.map σ) B.v₁ x)) hh (s (pairInd (Fv F B.v₁) b hb χ B₀ w)) (hs (pairInd (Fv F B.v₁) b hb χ B₀ w)).1 ψ₁ hψ₁ hact ((toGAd hσ G.W.J hc).symm y)`. Rewrite `e3` using `[← map_mul]`.

Rewrite using `[e2]`. Conclude with `e3`. Establish `hj : ∀ j, (LinearMap.funLeft ℂ ℂ (toGAd hσ G.W.J hc).symm ∘ₗ L j ∘ₗ s ∘ₗ pairInd (Fv F B.v₁) b hb χ B₀) (pairInd (Fv F B.v₁) b hb χ B₀⁻¹ (Z (φ j))) = fun y => L j (φ j) ((toGAd hσ G.W.J hc).symm y)` using `fun j => by`. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, rep_inv]`. Rewrite using `[eq_of_eq_of_ker hker (hL0 j) (hs _).1 (hφ j) (hs _).2]`.

Both sides reduce to the same expression. Simplify using `only [hj]`. Use function extensionality and compare the values at `y`. Rewrite using `[hI, Finset.sum_apply, Finset.sum_apply]`.
-/
theorem theta_sum_intertw : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M,
    ∀ B₀ : GL (Fin (a + a')) (Fv F B.v₁), ∃ (b : Fin 2 → ℕ) (hb : b 0 + b 1 = a + a') (χ : Fin 2 → (Fv F B.v₁)ˣ →* ℂˣ),
      ((b 0 = a ∧ b 1 = a') ∨ (b 0 = a' ∧ b 1 = a)) ∧ (∀ j, IsSmoothChar (χ j)) ∧ (∀ j y, ‖((χ j y : ℂˣ) : ℂ)‖ = 1) ∧
      ∃ (m : ℕ) (T : Fin m → IndSp (pairPlace b hb) (ofChar (pairChar (Fv F B.v₁) b χ)) →ₗ[ℂ] (GAd σ (c • G.W.J.map σ) → ℂ))
        (x : Fin m → IndSp (pairPlace b hb) (ofChar (pairChar (Fv F B.v₁) b χ))),
        (∀ j, IsIntertw σ (c • G.W.J.map σ) B.τ₁ B₀ (pairInd (Fv F B.v₁) b hb χ) (T j)) ∧
        (fun y => G.M.I om Φ ((toGAd hσ G.W.J hc).symm y)) = ∑ j, T j (x j) := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hK hT c hc hσc Φ hΦ B₀
  obtain ⟨b, hb, χ, hbl, hsm, hun, Z, hon, hker, heq⟩ := GlobalTheory.T.exists_local_characters_parabolic_induction F E σ B a a' G X om om' hK hT
  obtain ⟨m, φ, L, hφ, hL0, hLeq, hI⟩ := GlobalTheory.T.polynomial_data_local_expansion F E σ B a a' G X om om' hK hT Φ hΦ
  refine ⟨b, hb, χ, hbl, hsm, hun, ?_⟩
  obtain ⟨s, hs⟩ := exists_section _ Z hon
  have h1 : (1 : UA σ G.V.J) ∈ UAt σ G.V (evFin F B.v₁) := by
    intro u _
    show u • (mat (1 : UA σ G.V.J) - 1) = 0
    have e1 : mat (1 : UA σ G.V.J) = 1 := rfl
    rw [e1, sub_self, smul_zero]
  refine ⟨m, fun j => LinearMap.funLeft ℂ ℂ (toGAd hσ G.W.J hc).symm ∘ₗ L j ∘ₗ s ∘ₗ pairInd (Fv F B.v₁) b hb χ B₀,
    fun j => pairInd (Fv F B.v₁) b hb χ B₀⁻¹ (Z (φ j)), fun j => ?_, ?_⟩
  · intro g x hx w y
    obtain ⟨hh, hmat⟩ := GlobalTheory.T.local_compact_element_in_stabilizer F E σ hσ (a + a') G.W c hc B.v₁ B.τ₁ B₀ g x hx
    obtain ⟨ψ₁, ⟨hψ₁, hact⟩, -⟩ := (GlobalTheory.T.theta_action_exists hK.base F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _
      (GlobalTheory.ThKConst.isPair_big hT) B.v₁).1 1 h1 ((toGAd hσ G.W.J hc).symm (emb σ (c • G.W.J.map σ) B.v₁ x)) hh
      (s (pairInd (Fv F B.v₁) b hb χ B₀ w)) (hs _).1
    have hZ := heq (B₀ * g * B₀⁻¹) _ hh hmat _ (hs _).1 ψ₁ hψ₁ hact
    rw [(hs _).2, rep_conj] at hZ
    have e2 := eq_of_eq_of_ker hker (hL0 j) (hs (pairInd (Fv F B.v₁) b hb χ B₀ (pairInd (Fv F B.v₁) b hb χ g w))).1 hψ₁
      (by rw [(hs _).2, hZ])
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.funLeft_apply]
    have e3 := hLeq j ((toGAd hσ G.W.J hc).symm (emb σ (c • G.W.J.map σ) B.v₁ x)) hh
      (s (pairInd (Fv F B.v₁) b hb χ B₀ w)) (hs (pairInd (Fv F B.v₁) b hb χ B₀ w)).1 ψ₁ hψ₁ hact ((toGAd hσ G.W.J hc).symm y)
    rw [← map_mul] at e3
    rw [e2]
    exact e3
  · have hj : ∀ j, (LinearMap.funLeft ℂ ℂ (toGAd hσ G.W.J hc).symm ∘ₗ L j ∘ₗ s ∘ₗ pairInd (Fv F B.v₁) b hb χ B₀)
        (pairInd (Fv F B.v₁) b hb χ B₀⁻¹ (Z (φ j))) = fun y => L j (φ j) ((toGAd hσ G.W.J hc).symm y) := fun j => by
      simp only [LinearMap.coe_comp, Function.comp_apply, rep_inv]
      rw [eq_of_eq_of_ker hker (hL0 j) (hs _).1 (hφ j) (hs _).2]
      rfl
    simp only [hj]
    funext y
    rw [hI, Finset.sum_apply, Finset.sum_apply]

end GlobalTheory.ThK.ThetaKV
