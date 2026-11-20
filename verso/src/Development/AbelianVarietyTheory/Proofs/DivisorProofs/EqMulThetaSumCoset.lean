import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorCosetScaledIntegralEqRestrictedProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTracePairingBilinearNondegenerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeInvariantDistributionCharactersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiFinRat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxLatticeDiscreteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxLatticeIsZlatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralTraceDualRationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMemScaledIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalApproxScaledStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxLatticeDualCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharacterDecomposeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSumCosetLatticeStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

namespace GlobalTheory.CosetTheta
open GlobalTheory.BoxLattice GlobalTheory.EvAdm

/- English proof (translation)
The claim follows from `GlobalTheory.T.box_lattice_discrete`.
-/
theorem lat_disc : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F),
    DiscreteTopology (boxLat F κ a) := GlobalTheory.T.box_lattice_discrete

/- English proof (translation)
The claim follows from `GlobalTheory.T.box_lattice_is_zlattice`.
-/
theorem lat_full : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ [DiscreteTopology (boxLat F κ a)], IsZLattice ℝ (boxLat F κ a) := GlobalTheory.T.box_lattice_is_zlattice

/- English proof (translation)
The claim follows from `GlobalTheory.T.integral_trace_dual_rational`.
-/
theorem dual_rat : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ μ : κ → mixedEmbedding.mixedSpace F, (∀ l ∈ boxLat F κ a, ∃ k : ℤ, GlobalTheory.VacLn.trPair F κ l μ = k) →
      ∃ z : κ → F, μ = ratInf F κ z := GlobalTheory.T.integral_trace_dual_rational

/- English proof (translation)
The claim follows from `GlobalTheory.T.rational_mem_scaled_iff`.
-/
theorem ratFin_mem_iff : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ η : κ → F, ratFin F κ η ∈ scaledInt F κ a ↔ ∃ b : κ → 𝓞 F, η = fun i => a * (b i : F) := GlobalTheory.T.rational_mem_scaled_iff

/- English proof (translation)
The claim follows from `GlobalTheory.T.rational_approx_scaled`.
-/
theorem exists_rat_coset : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ r : κ → FiniteAdeleRing (𝓞 F) F, ∃ ρ : κ → F, ratFin F κ ρ - r ∈ scaledInt F κ a := GlobalTheory.T.rational_approx_scaled

/- English proof (translation)
The claim follows from `GlobalTheory.T.box_lattice_dual_character`.
-/
theorem psi_fin_box : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ a : F, a ≠ 0 → ∀ z : κ → F, (∀ l ∈ boxLat F κ a, ∃ k : ℤ, GlobalTheory.VacLn.trPair F κ l (ratInf F κ z) = k) →
      ∀ u ∈ scaledInt F κ a, ψ (pairA F 0 (u ⬝ᵥ ratFin F κ z)) = 1 := GlobalTheory.T.box_lattice_dual_character

/- English proof (translation)
The claim follows from `GlobalTheory.T.standard_character_decompose`.
-/
theorem psi_split : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (x : κ → AF F) (z : κ → F), ψ (x ⬝ᵥ fun i => algebraMap F (AF F) (z i)) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (GlobalTheory.VacLn.trPair F κ (fun i => evI F (x i)) (ratInf F κ z) : ℂ)) *
        ψ (pairA F 0 ((fun i => (x i).2) ⬝ᵥ ratFin F κ z)) := GlobalTheory.T.standard_character_decompose

/- English proof (translation)
The claim follows from `GlobalTheory.T.theta_sum_coset_lattice`.
-/
theorem thetaSum_coset : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ (r : κ → FiniteAdeleRing (𝓞 F) F) (ρ : κ → F), ratFin F κ ρ - r ∈ scaledInt F κ a →
    ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      thetaSum F (pureA F f (Set.indicator {y | y - r ∈ scaledInt F κ a} fun _ => (1 : ℂ))) =
        ∑' l : boxLat F κ a, f (ratInf F κ ρ + l) := GlobalTheory.T.theta_sum_coset_lattice

end GlobalTheory.CosetTheta

namespace GlobalTheory.CosetTheta
open GlobalTheory.BoxLattice GlobalTheory.EvAdm
open scoped Classical

/- English proof (translation)
Establish `hsymm : ∀ x y, GlobalTheory.VacLn.trPair F κ x y = GlobalTheory.VacLn.trPair F κ y x` using `fun x y => by`. Simplify using `only [GlobalTheory.VacLn.trPair_apply, mul_comm]`. Use `⟨fun x hx => GlobalTheory.VacLn.trPair_nondeg x fun y => ?_, fun y hy => GlobalTheory.VacLn.trPair_nondeg y fun x => ?_⟩` and prove the remaining obligations. Establish `h` using `hx y`. Rewrite `h` using `[LinearMap.neg_apply, LinearMap.neg_apply, neg_eq_zero]`.

Rewrite using `[hsymm]`. Conclude with `h`. Establish `h` using `hy x`. Rewrite `h` using `[LinearMap.neg_apply, LinearMap.neg_apply, neg_eq_zero]`. Conclude with `h`.
-/
theorem neg_trPair_nondeg (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    (-(GlobalTheory.VacLn.trPair F κ)).Nondegenerate := by
  have hsymm : ∀ x y, GlobalTheory.VacLn.trPair F κ x y = GlobalTheory.VacLn.trPair F κ y x := fun x y => by
    simp only [GlobalTheory.VacLn.trPair_apply, mul_comm]
  refine ⟨fun x hx => GlobalTheory.VacLn.trPair_nondeg x fun y => ?_, fun y hy => GlobalTheory.VacLn.trPair_nondeg y fun x => ?_⟩
  · have h := hx y
    rw [LinearMap.neg_apply, LinearMap.neg_apply, neg_eq_zero] at h
    rw [hsymm]
    exact h
  · have h := hy x
    rw [LinearMap.neg_apply, LinearMap.neg_apply, neg_eq_zero] at h
    exact h

/- English proof (translation)
Introduce `F _ _ κ _ ψ hψ L hadd hsmul hadm htr hch a ha r`. Use `set U := scaledInt F κ a with hU`. Use `set g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := Set.indicator {y | y - r ∈ U} fun _ => (1 : ℂ) with hgdef`. Establish `hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)`. Take `⟨φ, hφ, hcof, heq⟩` from `GlobalTheory.EvAdm.indicator_coset_scaledInt_eq_finprod F κ a r ha`.

Establish `e : g = fun y => ∏ᶠ v, φ v fun i => evalV F v (y i)` using `funext heq`. Rewrite using `[e]`. Conclude with `⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hφ hcof, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hφ hcof⟩`. Take `⟨T, hT⟩` from `hadm g hg`. Take `⟨ρ, hρ⟩` from `exists_rat_coset F κ a ha r`.

Use `haveI := lat_disc F κ a`. Use `haveI := lat_full F κ a ha`. Establish `hmemA : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, pureA F f g ∈ schA F κ` using `fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩`. Establish `htrT : ∀ l ∈ boxLat F κ a, ∀ f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, (∀ x, f' x = f (x + l)) → T f' = T f`. Introduce `l hl f f' hf'`.

Take `⟨b, rfl⟩` from `hl`. Use `set ξ : κ → F := fun i => a * (b i : F) with hξ`. Establish `hξU : ratFin F κ ξ ∈ U` using `(ratFin_mem_iff F κ a ha ξ).2 ⟨b, rfl⟩`. Establish `h1` using `htr ξ (pureA F f g) (hmemA f)`. Establish `e : (fun x => pureA F f g (x + fun i => algebraMap F (AF F) (ξ i))) = pureA F f' g`.

Use function extensionality and compare the values at `x`. Simplify using `only [pureA]`. Use `congr 1`. Rewrite using `[hf']`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Use `show InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i).1 + (algebraMap F (AF F) (ξ i)).1) = _`. Rewrite using `[map_add]`. Use `congr 1`. Conclude with `(InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp (K := F)).symm`.

Use `show g ((fun i => (x i).2) + ratFin F κ ξ) = g (fun i => (x i).2)`. Simplify using `only [hgdef, Set.indicator, Set.mem_setOf_eq]`. Establish `: (fun i => (x i).2) + ratFin F κ ξ - r ∈ U ↔ (fun i => (x i).2) - r ∈ U`. Rewrite using `[show (fun i => (x i).2) + ratFin F κ ξ - r = ((fun i => (x i).2) - r) + ratFin F κ ξ by abel]`. Conclude with `⟨fun h => by simpa using sub_mem h hξU, fun h => add_mem h hξU⟩`.

Simplify using `only [this]`. Rewrite using `[← hT, ← hT, ← e, h1]`. Establish `hmodT : ∀ μ : κ → mixedEmbedding.mixedSpace F, (∀ l ∈ boxLat F κ a, ∃ k : ℤ, (-(GlobalTheory.VacLn.trPair F κ)) l μ = k) → ∀ f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, (∀ x, f' x = Complex.exp (2 * Real.pi * Complex.I * ((-(GlobalTheory.VacLn.trPair F κ)) x μ : ℂ)) * …`. Introduce `μ hμ f f' hf'`. Establish `hμ' : ∀ l ∈ boxLat F κ a, ∃ k : ℤ, GlobalTheory.VacLn.trPair F κ l μ = k` using `fun l hl => by`.

Take `⟨k, hk⟩` from `hμ l hl`. Use `⟨-k, ?_⟩` and prove the remaining obligations. Rewrite `hk` using `[LinearMap.neg_apply, LinearMap.neg_apply]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨z, rfl⟩` from `dual_rat F κ a ha μ hμ'`. Use `set χ : ℂ := ψ (pairA F 0 (ratFin F κ ρ ⬝ᵥ ratFin F κ z)) with hχ`. Establish `hχv` using `psi_fin_rat hψ ρ z`. Rewrite `hχv` using `[← hχ]`. Establish `e : (fun x => ψ (x ⬝ᵥ fun i => algebraMap F (AF F) (z i)) * pureA F f g x) = χ • pureA F f' g`.

Use function extensionality and compare the values at `x`. Simplify using `only [Pi.smul_apply, smul_eq_mul, pureA]`. Distinguish the cases in `hx : (fun i => (x i).2) - r ∈ U`. Establish `hxg : g (fun i => (x i).2) = 1` using `Set.indicator_of_mem (show (fun i => (x i).2) ∈ {y | y - r ∈ U} from hx) _`. Establish `hu : (fun i => (x i).2) - ratFin F κ ρ ∈ U`.

Use `sub_mem hx hρ` as an intermediate fact. Rewrite `this` using `[sub_sub_sub_cancel_right]`. Then use the resulting hypothesis. Establish `hsplit` using `psi_split F κ ψ hψ x z`. Establish `hfin : ψ (pairA F 0 ((fun i => (x i).2) ⬝ᵥ ratFin F κ z)) = χ`. Establish `h0` using `psi_fin_box F κ ψ hψ a ha z hμ' _ hu`.

Establish `eadd : pairA F 0 ((fun i => (x i).2) ⬝ᵥ ratFin F κ z) = pairA F 0 (((fun i => (x i).2) - ratFin F κ ρ) ⬝ᵥ ratFin F κ z) + pairA F 0 (ratFin F κ ρ ⬝ᵥ ratFin F κ z)`. Rewrite using `[sub_dotProduct]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show (0 : InfiniteAdeleRing F) = 0 + 0`. Rewrite using `[add_zero]`.

Conclude with `(sub_add_cancel _ _).symm`. Rewrite using `[eadd, AddChar.map_add_eq_mul, h0, one_mul]`. Rewrite using `[hxg, hsplit, hfin, hf']`. Simplify using `only [LinearMap.neg_apply, evI]`. Use `push_cast`.

Put the polynomial expressions in normal form. Establish `hxg : g (fun i => (x i).2) = 0` using `Set.indicator_of_notMem (show (fun i => (x i).2) ∉ {y | y - r ∈ U} from hx) _`. Rewrite using `[hxg]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `hch z (pureA F f g) (hmemA f)`.

Rewrite `h1` using `[e, hsmul χ _ (hmemA f'), hT, hT]`. Rewrite using `[← h1, hχv, ← mul_assoc, ← Complex.exp_add]`. Simplify using `only [LinearMap.neg_apply]`. Use `push_cast`. Put the polynomial expressions in normal form.

Simplify using the standard rewrite rules. Take `⟨c, hc⟩` from `GlobalTheory.T.lattice_invariant_distribution_characters (κ → mixedEmbedding.mixedSpace F) (-(GlobalTheory.VacLn.trPair F κ)) (neg_trPair_nondeg F κ) (boxLat F κ a) (ratInf F κ ρ) T htrT hmodT`. Use `⟨c, fun f => ?_⟩` and prove the remaining obligations. Rewrite using `[hT f, hc f, thetaSum_coset F κ a ha r ρ hρ f]`.
-/
theorem eq_mul_thetaSum_coset : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ L : ((κ → AF F) → ℂ) → ℂ, (∀ Ψ ∈ schA F κ, ∀ Ψ' ∈ schA F κ, L (Ψ + Ψ') = L Ψ + L Ψ') →
      (∀ c : ℂ, ∀ Ψ ∈ schA F κ, L (c • Ψ) = c * L Ψ) →
      (∀ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∃ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
        ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, L (pureA F f g) = T f) →
      (∀ ξ : κ → F, ∀ Ψ ∈ schA F κ, L (fun x => Ψ (x + fun i => algebraMap F (AF F) (ξ i))) = L Ψ) →
      (∀ z : κ → F, ∀ Ψ ∈ schA F κ, L (fun x => ψ (x ⬝ᵥ fun i => algebraMap F (AF F) (z i)) * Ψ x) = L Ψ) →
      ∀ a : F, a ≠ 0 → ∀ r : κ → FiniteAdeleRing (𝓞 F) F, ∃ c : ℂ,
        ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
          L (pureA F f (Set.indicator {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} fun _ => (1 : ℂ))) =
            c * thetaSum F (pureA F f (Set.indicator {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} fun _ => (1 : ℂ))) := by
  intro F _ _ κ _ ψ hψ L hadd hsmul hadm htr hch a ha r
  set U := scaledInt F κ a with hU
  set g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := Set.indicator {y | y - r ∈ U} fun _ => (1 : ℂ) with hgdef
  have hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
    obtain ⟨φ, hφ, hcof, heq⟩ := GlobalTheory.EvAdm.indicator_coset_scaledInt_eq_finprod F κ a r ha
    have e : g = fun y => ∏ᶠ v, φ v fun i => evalV F v (y i) := funext heq
    rw [e]
    exact ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hφ hcof,
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hφ hcof⟩
  obtain ⟨T, hT⟩ := hadm g hg
  obtain ⟨ρ, hρ⟩ := exists_rat_coset F κ a ha r
  haveI := lat_disc F κ a
  haveI := lat_full F κ a ha
  have hmemA : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, pureA F f g ∈ schA F κ :=
    fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩
  have htrT : ∀ l ∈ boxLat F κ a, ∀ f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      (∀ x, f' x = f (x + l)) → T f' = T f := by
    intro l hl f f' hf'
    obtain ⟨b, rfl⟩ := hl
    set ξ : κ → F := fun i => a * (b i : F) with hξ
    have hξU : ratFin F κ ξ ∈ U := (ratFin_mem_iff F κ a ha ξ).2 ⟨b, rfl⟩
    have h1 := htr ξ (pureA F f g) (hmemA f)
    have e : (fun x => pureA F f g (x + fun i => algebraMap F (AF F) (ξ i))) = pureA F f' g := by
      funext x
      simp only [pureA]
      congr 1
      · rw [hf']
        congr 1
        funext i
        show InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i).1 + (algebraMap F (AF F) (ξ i)).1) = _
        rw [map_add]
        congr 1
        exact (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp (K := F)).symm
      · show g ((fun i => (x i).2) + ratFin F κ ξ) = g (fun i => (x i).2)
        simp only [hgdef, Set.indicator, Set.mem_setOf_eq]
        have : (fun i => (x i).2) + ratFin F κ ξ - r ∈ U ↔ (fun i => (x i).2) - r ∈ U := by
          rw [show (fun i => (x i).2) + ratFin F κ ξ - r = ((fun i => (x i).2) - r) + ratFin F κ ξ by abel]
          exact ⟨fun h => by simpa using sub_mem h hξU, fun h => add_mem h hξU⟩
        simp only [this]
    rw [← hT, ← hT, ← e, h1]
  have hmodT : ∀ μ : κ → mixedEmbedding.mixedSpace F, (∀ l ∈ boxLat F κ a, ∃ k : ℤ, (-(GlobalTheory.VacLn.trPair F κ)) l μ = k) →
      ∀ f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      (∀ x, f' x = Complex.exp (2 * Real.pi * Complex.I * ((-(GlobalTheory.VacLn.trPair F κ)) x μ : ℂ)) * f x) →
      T f' = Complex.exp (2 * Real.pi * Complex.I * ((-(GlobalTheory.VacLn.trPair F κ)) (ratInf F κ ρ) μ : ℂ)) * T f := by
    intro μ hμ f f' hf'
    have hμ' : ∀ l ∈ boxLat F κ a, ∃ k : ℤ, GlobalTheory.VacLn.trPair F κ l μ = k := fun l hl => by
      obtain ⟨k, hk⟩ := hμ l hl
      refine ⟨-k, ?_⟩
      rw [LinearMap.neg_apply, LinearMap.neg_apply] at hk
      push_cast
      linarith
    obtain ⟨z, rfl⟩ := dual_rat F κ a ha μ hμ'
    set χ : ℂ := ψ (pairA F 0 (ratFin F κ ρ ⬝ᵥ ratFin F κ z)) with hχ
    have hχv := psi_fin_rat hψ ρ z
    rw [← hχ] at hχv
    have e : (fun x => ψ (x ⬝ᵥ fun i => algebraMap F (AF F) (z i)) * pureA F f g x) = χ • pureA F f' g := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul, pureA]
      by_cases hx : (fun i => (x i).2) - r ∈ U
      · have hxg : g (fun i => (x i).2) = 1 := Set.indicator_of_mem (show (fun i => (x i).2) ∈ {y | y - r ∈ U} from hx) _
        have hu : (fun i => (x i).2) - ratFin F κ ρ ∈ U := by
          have := sub_mem hx hρ
          rwa [sub_sub_sub_cancel_right] at this
        have hsplit := psi_split F κ ψ hψ x z
        have hfin : ψ (pairA F 0 ((fun i => (x i).2) ⬝ᵥ ratFin F κ z)) = χ := by
          have h0 := psi_fin_box F κ ψ hψ a ha z hμ' _ hu
          have eadd : pairA F 0 ((fun i => (x i).2) ⬝ᵥ ratFin F κ z) =
              pairA F 0 (((fun i => (x i).2) - ratFin F κ ρ) ⬝ᵥ ratFin F κ z) +
                pairA F 0 (ratFin F κ ρ ⬝ᵥ ratFin F κ z) := by
            rw [sub_dotProduct]
            refine Prod.ext ?_ ?_
            · show (0 : InfiniteAdeleRing F) = 0 + 0
              rw [add_zero]
            · exact (sub_add_cancel _ _).symm
          rw [eadd, AddChar.map_add_eq_mul, h0, one_mul]
        rw [hxg, hsplit, hfin, hf']
        simp only [LinearMap.neg_apply, evI]
        push_cast
        ring_nf
      · have hxg : g (fun i => (x i).2) = 0 := Set.indicator_of_notMem (show (fun i => (x i).2) ∉ {y | y - r ∈ U} from hx) _
        rw [hxg]
        ring
    have h1 := hch z (pureA F f g) (hmemA f)
    rw [e, hsmul χ _ (hmemA f'), hT, hT] at h1
    rw [← h1, hχv, ← mul_assoc, ← Complex.exp_add]
    simp only [LinearMap.neg_apply]
    push_cast
    ring_nf
    simp
  obtain ⟨c, hc⟩ := GlobalTheory.T.lattice_invariant_distribution_characters (κ → mixedEmbedding.mixedSpace F) (-(GlobalTheory.VacLn.trPair F κ)) (neg_trPair_nondeg F κ)
    (boxLat F κ a) (ratInf F κ ρ) T htrT hmodT
  refine ⟨c, fun f => ?_⟩
  rw [hT f, hc f, thetaSum_coset F κ a ha r ρ hρ f]

end GlobalTheory.CosetTheta
