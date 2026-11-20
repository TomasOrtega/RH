import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusOfSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSummandGoodPlaceIndicator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralEqWeightedLatticeOrbitCountStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexCentralizerStabilizerEqLatticeStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackOfTranslatedStandardLatticeMulIntegralGLStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackLatticeEqIffSameIntegralGLCosetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntegralHermitianCompletionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCommutingEqMulNormOneTorusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackLatticeMulEqMulLeftImageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryCommutingOfMemNormOneTorusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackLatticeSelfDualOfUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackLatticeStableIffPrincipalCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemPrincipalCongruenceSubgroupIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompactPartCentralizerIffTorusIntegralUnitsStatement

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

namespace GlobalTheory.KapOrb

/- English proof (translation)
Introduce `E _ _ _ w hw K e hBr k t ht htk n Q B u x hsep hF hu γ hγ hM`. Take `⟨ψ, hψ⟩` from `(isModel_iff w e B u x γ).1 hM`. Establish `hψ1` using `hψ.1`. Establish `hψ3` using `hψ.2.2`. Set `δ : UL n w` to `⟨γ, hγ⟩`.

Set `M : UL n w → Submodule K.O B.A` to `fun g => pullLat w B ψ g.1`. Set `τ : UL n w → B.Aˣ` to `fun g => torusOf w B ψ g.1`. Establish `hcomm : ∀ h ∈ twCent (MonoidHom.id (UL n w)) δ, h.1 * γ = γ * h.1`. Introduce `h hh`. Use `congrArg Subtype.val hh` as an intermediate fact.

Simplify using `using this`. Establish `h1 : ∀ g kk : UL n w, kk ∈ KL n w → M (g * kk) = M g` using `fun g kk hk => GlobalTheory.T.pullbackOfTranslatedStandardLattice_mul_integralGL E w K B n ψ g.1 kk.1 (Subgroup.mem_subgroupOf.1 hk)`. Establish `h2 : ∀ g g' : UL n w, M g = M g' → g⁻¹ * g' ∈ KL n w` using `fun g g' hgg => Subgroup.mem_subgroupOf.2 (by simpa using GlobalTheory.T.pullbackLattice_eq_iff_same_integralGL_coset E w K e hBr B n ψ hψ1 g.1 g'.1 hgg)`. Establish `h3 : ∀ L ∈ B.X x, ∃ g, M g = L`. Introduce `L hL`.

Take `⟨hlat, -, hsd⟩` from `hL`. Take `⟨g, hg, hgL⟩` from `GlobalTheory.T.lattice_integral_hermitian_completion E w hw K e hBr B x n ψ hψ1 hψ3 L hlat hsd`. Conclude with `⟨⟨g, hg⟩, hgL⟩`. Establish `hT : ∀ h ∈ twCent (MonoidHom.id (UL n w)) δ, τ h ∈ B.T ∧ ∀ y, ψ ((τ h : B.A) * y) = h.1.val *ᵥ ψ y` using `fun h hh => GlobalTheory.T.unitary_commuting_eq_mul_normOneTorus E w hw K e B Q u x n γ ψ hF hψ h.1 h.2 (hcomm h hh)`. Establish `h4 : ∀ h ∈ twCent (MonoidHom.id (UL n w)) δ, τ h ∈ B.T ∧ ∀ g, M (h * g) = GlobalTheory.UnitLemma.mulLat K.O (τ h : B.A) (M g)` using `fun h hh => ⟨(hT h hh).1, fun g => GlobalTheory.T.pullbackLattice_mul_eq_mulLeftImage E w K B n ψ h.1 g.1 _ (hT h hh).2⟩`.

Establish `h5 : ∀ s ∈ B.T, ∃ h ∈ twCent (MonoidHom.id (UL n w)) δ, τ h = s`. Introduce `s hs`. Take `⟨h, hU, hc, hspec⟩` from `GlobalTheory.T.exists_unitary_commuting_of_mem_normOneTorus E w K e B u x n γ ψ hψ s hs`. Use `⟨⟨h, hU⟩, ?_, torusOf_spec w B ψ h s hspec⟩` and prove the remaining obligations. Use `show (⟨h, hU⟩ : UL n w) * δ = δ * (MonoidHom.id (UL n w)) ⟨h, hU⟩`.

Conclude with `Subtype.ext hc`. Establish `hiff : ∀ g : UL n w, M g ∈ B.X x ↔ g.1⁻¹ * γ * g.1 ∈ congSet w n k`. Introduce `g`. Take `⟨hlat, hsd⟩` from `GlobalTheory.T.pullbackLattice_selfDual_of_unitary E w hw K e hBr B x n ψ hψ1 hψ3 g.1 g.2`. Rewrite using `[← GlobalTheory.T.pullbackLattice_stable_iff_principalCongruence E w hw K e hBr k t ht htk B u x n γ ψ hψ hu hγ g.1 g.2]`.

Conclude with `⟨fun h => h.2.1, fun h => ⟨hlat, h, hsd⟩⟩`. Establish `h6 : ∀ g : UL n w, avg (fun kk : KL n w => (({g : UL n w | g.1 ∈ congSet w n k} : Set (UL n w)).indicator 1) ((g * kk)⁻¹ * δ * (MonoidHom.id (UL n w)) (g * kk))) = if M g ∈ B.X x then 1 else 0`. Introduce `g`. Establish `hfun : (fun kk : KL n w => (({g : UL n w | g.1 ∈ congSet w n k} : Set (UL n w)).indicator 1) ((g * kk)⁻¹ * δ * (MonoidHom.id (UL n w)) (g * kk))) = fun _ => (if g.1⁻¹ * γ * g.1 ∈ congSet w n k then 1 else 0 : ℂ)`. Use function extensionality and compare the values at `kk`.

Rewrite using `[Set.indicator_apply]`. Establish `hc : ((g * kk)⁻¹ * δ * (MonoidHom.id (UL n w)) (g * kk)).1 = (kk.1.1)⁻¹ * (g.1⁻¹ * γ * g.1) * kk.1.1`. Simplify using `[δ, mul_assoc]`. Establish `hm : ((g * kk)⁻¹ * δ * (MonoidHom.id (UL n w)) (g * kk)) ∈ ({g : UL n w | g.1 ∈ congSet w n k} : Set (UL n w)) ↔ g.1⁻¹ * γ * g.1 ∈ congSet w n k` using `by show ((g * kk)⁻¹ * δ * (MonoidHom.id (UL n w)) (g * kk)).1 ∈ congSet w n k ↔ _`. Rewrite using `[hc]`.

Conclude with `GlobalTheory.T.conj_mem_principalCongruenceSubgroup_iff E w n k _ _ (Subgroup.mem_subgroupOf.1 kk.2)`. Distinguish the cases in `h : g.1⁻¹ * γ * g.1 ∈ congSet w n k`. Rewrite using `[if_pos (hm.2 h), if_pos h]`. Both sides reduce to the same expression. Rewrite using `[if_neg (fun h' => h (hm.1 h')), if_neg h]`.

Rewrite using `[hfun, GlobalTheory.TwOrbGood.avg_const]`. Distinguish the cases in `h : g.1⁻¹ * γ * g.1 ∈ congSet w n k`. Rewrite using `[if_pos h, if_pos ((hiff g).2 h)]`. Rewrite using `[if_neg h, if_neg (fun h' => h ((hiff g).1 h'))]`. Establish `hmul : ∀ h ∈ twCent (MonoidHom.id (UL n w)) δ, ∀ h' ∈ twCent (MonoidHom.id (UL n w)) δ, τ (h * h') = τ h * τ h'`.

Introduce `h hh h' hh'`. Apply `torusOf_spec` to reduce the goal to its premises. Introduce `y`. Rewrite using `[Units.val_mul, mul_assoc, (hT h hh).2, (hT h' hh').2, Matrix.mulVec_mulVec]`. Both sides reduce to the same expression.

Establish `hinj : ∀ h ∈ twCent (MonoidHom.id (UL n w)) δ, ∀ h' ∈ twCent (MonoidHom.id (UL n w)) δ, τ h = τ h' → h = h'`. Introduce `h hh h' hh' heq`. Establish `hv : ∀ v, h.1.val *ᵥ v = h'.1.val *ᵥ v`. Introduce `v`. Take `⟨y, rfl⟩` from `ψ.surjective v`.

Rewrite using `[← (hT h hh).2, ← (hT h' hh').2, heq]`. Establish `hm : h.1.val = h'.1.val` using `Matrix.toLin'.injective (LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using hv v)`. Conclude with `Subtype.ext (Units.ext hm)`. Establish `hcpt : ∀ h ∈ twCent (MonoidHom.id (UL n w)) δ, h ∈ cptPart (twCent (MonoidHom.id (UL n w)) δ) ↔ τ h ∈ GlobalTheory.UnitLemma.intUnits K.O B.A` using `fun h hh => GlobalTheory.T.mem_compactPart_centralizer_iff_torus_integral_units E w hw K e hBr B Q u x n γ hγ ψ hF hψ h hh`. Establish `h7` using `GlobalTheory.T.relIndex_centralizerStabilizer_eq_latticeStabilizer (KL n w) δ B.T M τ h1 h2 h4 h5 hmul hinj hcpt`.

Conclude with `GlobalTheory.T.orbitalIntegral_eq_weighted_lattice_orbit_count (KL n w) δ _ B.T (B.X x) M τ h1 h2 h3 h4 h5 h6 h7`.
-/
theorem twOrb_congruence_eq_N : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (k : ℕ) (t : K.O), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (n : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A), Q.Separable → Fits w e B Q u → u = 1 + algebraMap K.O B.A t * B.g → ∀ (γ : GLw n w) (hγ : γ ∈ UL n w), IsModel w e B u x γ → twOrb (MonoidHom.id (UL n w)) (KL n w) ⟨γ, hγ⟩ (({g : UL n w | g.1 ∈ congSet w n k} : Set (UL n w)).indicator 1) = ((B.N x : ℚ) : ℂ) := by
  intro E _ _ _ w hw K e hBr k t ht htk n Q B u x hsep hF hu γ hγ hM
  obtain ⟨ψ, hψ⟩ := (isModel_iff w e B u x γ).1 hM
  have hψ1 := hψ.1
  have hψ3 := hψ.2.2
  let δ : UL n w := ⟨γ, hγ⟩
  let M : UL n w → Submodule K.O B.A := fun g => pullLat w B ψ g.1
  let τ : UL n w → B.Aˣ := fun g => torusOf w B ψ g.1
  have hcomm : ∀ h ∈ twCent (MonoidHom.id (UL n w)) δ, h.1 * γ = γ * h.1 := by
    intro h hh
    have := congrArg Subtype.val hh
    simpa using this
  have h1 : ∀ g kk : UL n w, kk ∈ KL n w → M (g * kk) = M g := fun g kk hk =>
    GlobalTheory.T.pullbackOfTranslatedStandardLattice_mul_integralGL E w K B n ψ g.1 kk.1 (Subgroup.mem_subgroupOf.1 hk)
  have h2 : ∀ g g' : UL n w, M g = M g' → g⁻¹ * g' ∈ KL n w := fun g g' hgg =>
    Subgroup.mem_subgroupOf.2 (by simpa using GlobalTheory.T.pullbackLattice_eq_iff_same_integralGL_coset E w K e hBr B n ψ hψ1 g.1 g'.1 hgg)
  have h3 : ∀ L ∈ B.X x, ∃ g, M g = L := by
    intro L hL
    obtain ⟨hlat, -, hsd⟩ := hL
    obtain ⟨g, hg, hgL⟩ := GlobalTheory.T.lattice_integral_hermitian_completion E w hw K e hBr B x n ψ hψ1 hψ3 L hlat hsd
    exact ⟨⟨g, hg⟩, hgL⟩
  have hT : ∀ h ∈ twCent (MonoidHom.id (UL n w)) δ, τ h ∈ B.T ∧ ∀ y, ψ ((τ h : B.A) * y) = h.1.val *ᵥ ψ y :=
    fun h hh => GlobalTheory.T.unitary_commuting_eq_mul_normOneTorus E w hw K e B Q u x n γ ψ hF hψ h.1 h.2 (hcomm h hh)
  have h4 : ∀ h ∈ twCent (MonoidHom.id (UL n w)) δ, τ h ∈ B.T ∧
      ∀ g, M (h * g) = GlobalTheory.UnitLemma.mulLat K.O (τ h : B.A) (M g) :=
    fun h hh => ⟨(hT h hh).1, fun g => GlobalTheory.T.pullbackLattice_mul_eq_mulLeftImage E w K B n ψ h.1 g.1 _ (hT h hh).2⟩
  have h5 : ∀ s ∈ B.T, ∃ h ∈ twCent (MonoidHom.id (UL n w)) δ, τ h = s := by
    intro s hs
    obtain ⟨h, hU, hc, hspec⟩ := GlobalTheory.T.exists_unitary_commuting_of_mem_normOneTorus E w K e B u x n γ ψ hψ s hs
    refine ⟨⟨h, hU⟩, ?_, torusOf_spec w B ψ h s hspec⟩
    show (⟨h, hU⟩ : UL n w) * δ = δ * (MonoidHom.id (UL n w)) ⟨h, hU⟩
    exact Subtype.ext hc
  have hiff : ∀ g : UL n w, M g ∈ B.X x ↔ g.1⁻¹ * γ * g.1 ∈ congSet w n k := by
    intro g
    obtain ⟨hlat, hsd⟩ := GlobalTheory.T.pullbackLattice_selfDual_of_unitary E w hw K e hBr B x n ψ hψ1 hψ3 g.1 g.2
    rw [← GlobalTheory.T.pullbackLattice_stable_iff_principalCongruence E w hw K e hBr k t ht htk B u x n γ ψ hψ hu hγ g.1 g.2]
    exact ⟨fun h => h.2.1, fun h => ⟨hlat, h, hsd⟩⟩
  have h6 : ∀ g : UL n w, avg (fun kk : KL n w => (({g : UL n w | g.1 ∈ congSet w n k} : Set (UL n w)).indicator 1)
      ((g * kk)⁻¹ * δ * (MonoidHom.id (UL n w)) (g * kk))) = if M g ∈ B.X x then 1 else 0 := by
    intro g
    have hfun : (fun kk : KL n w => (({g : UL n w | g.1 ∈ congSet w n k} : Set (UL n w)).indicator 1)
        ((g * kk)⁻¹ * δ * (MonoidHom.id (UL n w)) (g * kk))) =
        fun _ => (if g.1⁻¹ * γ * g.1 ∈ congSet w n k then 1 else 0 : ℂ) := by
      funext kk
      rw [Set.indicator_apply]
      have hc : ((g * kk)⁻¹ * δ * (MonoidHom.id (UL n w)) (g * kk)).1 =
          (kk.1.1)⁻¹ * (g.1⁻¹ * γ * g.1) * kk.1.1 := by
        simp [δ, mul_assoc]
      have hm : ((g * kk)⁻¹ * δ * (MonoidHom.id (UL n w)) (g * kk)) ∈
          ({g : UL n w | g.1 ∈ congSet w n k} : Set (UL n w)) ↔ g.1⁻¹ * γ * g.1 ∈ congSet w n k := by
        show ((g * kk)⁻¹ * δ * (MonoidHom.id (UL n w)) (g * kk)).1 ∈ congSet w n k ↔ _
        rw [hc]
        exact GlobalTheory.T.conj_mem_principalCongruenceSubgroup_iff E w n k _ _ (Subgroup.mem_subgroupOf.1 kk.2)
      by_cases h : g.1⁻¹ * γ * g.1 ∈ congSet w n k
      · rw [if_pos (hm.2 h), if_pos h]; rfl
      · rw [if_neg (fun h' => h (hm.1 h')), if_neg h]
    rw [hfun, GlobalTheory.TwOrbGood.avg_const]
    by_cases h : g.1⁻¹ * γ * g.1 ∈ congSet w n k
    · rw [if_pos h, if_pos ((hiff g).2 h)]
    · rw [if_neg h, if_neg (fun h' => h ((hiff g).1 h'))]
  have hmul : ∀ h ∈ twCent (MonoidHom.id (UL n w)) δ, ∀ h' ∈ twCent (MonoidHom.id (UL n w)) δ,
      τ (h * h') = τ h * τ h' := by
    intro h hh h' hh'
    apply torusOf_spec
    intro y
    rw [Units.val_mul, mul_assoc, (hT h hh).2, (hT h' hh').2, Matrix.mulVec_mulVec]
    rfl
  have hinj : ∀ h ∈ twCent (MonoidHom.id (UL n w)) δ, ∀ h' ∈ twCent (MonoidHom.id (UL n w)) δ,
      τ h = τ h' → h = h' := by
    intro h hh h' hh' heq
    have hv : ∀ v, h.1.val *ᵥ v = h'.1.val *ᵥ v := by
      intro v
      obtain ⟨y, rfl⟩ := ψ.surjective v
      rw [← (hT h hh).2, ← (hT h' hh').2, heq]
    have hm : h.1.val = h'.1.val :=
      Matrix.toLin'.injective (LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using hv v)
    exact Subtype.ext (Units.ext hm)
  have hcpt : ∀ h ∈ twCent (MonoidHom.id (UL n w)) δ,
      h ∈ cptPart (twCent (MonoidHom.id (UL n w)) δ) ↔ τ h ∈ GlobalTheory.UnitLemma.intUnits K.O B.A :=
    fun h hh => GlobalTheory.T.mem_compactPart_centralizer_iff_torus_integral_units E w hw K e hBr B Q u x n γ hγ ψ hF hψ h hh
  have h7 := GlobalTheory.T.relIndex_centralizerStabilizer_eq_latticeStabilizer (KL n w) δ B.T M τ h1 h2 h4 h5 hmul hinj hcpt
  exact GlobalTheory.T.orbitalIntegral_eq_weighted_lattice_orbit_count (KL n w) δ _ B.T (B.X x) M τ h1 h2 h3 h4 h5 h6 h7

end GlobalTheory.KapOrb
