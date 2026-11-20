import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ExpToSat
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.SatakeSocle.SatBridge
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardBlocksExponent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExpSat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatBridge
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerPowTendstoZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetQuotientEigenvector
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemCharIdem
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.CuspRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.ExpProd

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[le_uniformizer_iff]`. Conclude with `GlobalTheory.CompanionTheory.UnifPow.valuation_unifU_lt_one k`. Take `⟨y, hy⟩` from `valuation_surjective (uniformizer k)`. Establish `hy1 : valuation k y < 1` using `hy ▸ uniformizer_lt_one`.

Establish `hyO : y ∈ 𝒪[k]` using `hy1.le`. Establish `hm : (⟨y, hyO⟩ : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k]`. Rewrite using `[IsLocalRing.mem_maximalIdeal]`. Introduce `hu`. Conclude with `hy1.ne (((Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one).1 hu)`.

Rewrite `hm` using `[(Zls.irreducible_unif (k := k)).maximalIdeal_eq, Ideal.mem_span_singleton]`. Rewrite using `[← hy]`. Conclude with `(Valuation.Integers.le_iff_dvd (Valuation.integer.integers (valuation k))).2 hm`.
-/
theorem val_unifU (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    valuation k ((Zls.unifU k : kˣ) : k) = uniformizer k := by
  apply le_antisymm
  · rw [le_uniformizer_iff]
    exact GlobalTheory.CompanionTheory.UnifPow.valuation_unifU_lt_one k
  · obtain ⟨y, hy⟩ := valuation_surjective (uniformizer k)
    have hy1 : valuation k y < 1 := hy ▸ uniformizer_lt_one
    have hyO : y ∈ 𝒪[k] := hy1.le
    have hm : (⟨y, hyO⟩ : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
      rw [IsLocalRing.mem_maximalIdeal]
      intro hu
      exact hy1.ne (((Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one).1 hu)
    rw [(Zls.irreducible_unif (k := k)).maximalIdeal_eq, Ideal.mem_span_singleton] at hm
    rw [← hy]
    exact (Valuation.Integers.le_iff_dvd (Valuation.integer.integers (valuation k))).2 hm

/- English proof (translation)
The claim follows from `funext fun i => unrChar_uniformizer k (ξ i) (val_unifU k)`.
-/
theorem atUnif_unrChar (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (ξ : Fin n → ℂˣ) : PositivityTheory.SphericalProduct.atUnif k (fun i => unrChar k (ξ i)) = ξ :=
  funext fun i => unrChar_uniformizer k (ξ i) (val_unifU k)

/- English proof (translation)
Introduce `E _ _ w c n N h σ P ξ hsub hmono ⟨y, hy0, hy⟩`. Use `haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective`. Establish `hd : ∑ _a : Fin n, 1 = n` using `by simp`. Take `⟨v, hv0, hv⟩` from `GlobalTheory.CompanionTheory.StandardBlocks.stdBridge (w.adicCompletion E) n hd P.V P.ρ _ y hy0 hy`. Establish `hadm : IsAdmissible P.ρ` using `(GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness (w.adicCompletion E)).1 _ P.V P.ρ P.smooth P.irred`.

Establish `hanti : PositivityTheory.SphericalProduct.AbsAnti (PositivityTheory.SphericalProduct.atUnif (w.adicCompletion E) (fun i => unrChar (w.adicCompletion E) (ξ i)))`. Rewrite using `[atUnif_unrChar]`. Conclude with `fun i j hij => hmono i j hij`. Establish `hsat` using `GlobalTheory.CompanionTheory.LocGL.expSat (w.adicCompletion E) n hd P.V P.ρ P.smooth hadm P.irred (fun i => unrChar (w.adicCompletion E) (ξ i)) (fun i => isUnram_unrChar _ _) hanti ⟨v, hv0, hv⟩`. Rewrite `hsat` using `[atUnif_unrChar]`.

Establish `hG` using `(GlobalTheory.CompanionTheory.SatakeBridge.satBridge E w n P.V P.ρ P.smooth P.irred ξ).1 hsat`. Take `⟨x, hx⟩` from `hG.exists_vec`. Take `⟨S, f, hf⟩` from `hsub`. Establish `hsm : IsSmooth (locProd h w σ)` using `GlobalTheory.SmGL.isSmooth_parInd _ _`. Establish `hSs : IsSmooth S.toRepresentation` using `GlobalTheory.CompanionTheory.JacExp.isSmooth_sub hsm S`.

Establish `hc` using `GlobalTheory.SatInd.isCompact_KGL (w := w) (n := n)`. Take `⟨s, rfl⟩` from `hf x`. Take `⟨u, hu, hfu⟩` from `GlobalTheory.LocGL.exists_mem_fixed_map_eq hSs hc f hx.2.1`. Establish `hu0 : u ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hx.1 (by rw [← hfu, map_zero])`. Establish `hfix : u.1 ∈ fixed (locProd h w σ) (GlobalTheory.LFun.KGL w n)` using `GlobalTheory.LGrp.mem_fixed.2 fun g hg => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hu g hg)`. Establish `hne : u.1 ≠ 0` using `fun e => hu0 (Subtype.ext e)`. Take `⟨B, hB, hBv⟩` from `GlobalTheory.SatInd.exists_sat_multiProd h (π := fun i => (σ i).ρ) (fun i => (σ i).smooth) (fun i => (σ i).irred) hfix hne`. Establish `h1 : GlobalTheory.LFun.IsSatVecGL w S.toRepresentation u (∑ a, B a)` using `GlobalTheory.LFun.IsSatVecGL.of_map S.toSubmodule.subtype (fun g y => rfl) Subtype.val_injective hBv`.

Establish `h2` using `h1.map (ρ' := P.ρ) f.toLinearMap (fun g y => f.isIntertwining _ _ g y) (by`. Express the relevant statement in the definitionally equal form `f u ≠ 0`. Rewrite using `[hfu]`. Conclude with `hx.1)`. Express the relevant statement in the definitionally equal form `GlobalTheory.LFun.IsSatVecGL w P.ρ (f u) _ at h2`.

Rewrite `h2` using `[hfu]`. Conclude with `⟨fun i => (hB i).1, B, hB, h2.unique hx⟩`.
-/
theorem expToSat : PositivityTheory.Rg.BcB.F.Tail.PExp.ExpToSat := by
  intro E _ _ w c n N h σ P ξ hsub hmono ⟨y, hy0, hy⟩
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have hd : ∑ _a : Fin n, 1 = n := by simp
  obtain ⟨v, hv0, hv⟩ := GlobalTheory.CompanionTheory.StandardBlocks.stdBridge (w.adicCompletion E) n hd P.V P.ρ _ y hy0 hy
  have hadm : IsAdmissible P.ρ :=
    (GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness (w.adicCompletion E)).1 _ P.V P.ρ P.smooth P.irred
  have hanti : PositivityTheory.SphericalProduct.AbsAnti (PositivityTheory.SphericalProduct.atUnif (w.adicCompletion E)
      (fun i => unrChar (w.adicCompletion E) (ξ i))) := by
    rw [atUnif_unrChar]
    exact fun i j hij => hmono i j hij
  have hsat := GlobalTheory.CompanionTheory.LocGL.expSat (w.adicCompletion E) n hd P.V P.ρ P.smooth hadm P.irred
    (fun i => unrChar (w.adicCompletion E) (ξ i)) (fun i => isUnram_unrChar _ _) hanti ⟨v, hv0, hv⟩
  rw [atUnif_unrChar] at hsat
  have hG := (GlobalTheory.CompanionTheory.SatakeBridge.satBridge E w n P.V P.ρ P.smooth P.irred ξ).1 hsat
  obtain ⟨x, hx⟩ := hG.exists_vec
  obtain ⟨S, f, hf⟩ := hsub
  have hsm : IsSmooth (locProd h w σ) := GlobalTheory.SmGL.isSmooth_parInd _ _
  have hSs : IsSmooth S.toRepresentation := GlobalTheory.CompanionTheory.JacExp.isSmooth_sub hsm S
  have hc := GlobalTheory.SatInd.isCompact_KGL (w := w) (n := n)
  obtain ⟨s, rfl⟩ := hf x
  obtain ⟨u, hu, hfu⟩ := GlobalTheory.LocGL.exists_mem_fixed_map_eq hSs hc f hx.2.1
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hx.1 (by rw [← hfu, map_zero])
  have hfix : u.1 ∈ fixed (locProd h w σ) (GlobalTheory.LFun.KGL w n) :=
    GlobalTheory.LGrp.mem_fixed.2 fun g hg => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hu g hg)
  have hne : u.1 ≠ 0 := fun e => hu0 (Subtype.ext e)
  obtain ⟨B, hB, hBv⟩ := GlobalTheory.SatInd.exists_sat_multiProd h (π := fun i => (σ i).ρ)
    (fun i => (σ i).smooth) (fun i => (σ i).irred) hfix hne
  have h1 : GlobalTheory.LFun.IsSatVecGL w S.toRepresentation u (∑ a, B a) :=
    GlobalTheory.LFun.IsSatVecGL.of_map S.toSubmodule.subtype (fun g y => rfl) Subtype.val_injective hBv
  have h2 := h1.map (ρ' := P.ρ) f.toLinearMap (fun g y => f.isIntertwining _ _ g y) (by
    change f u ≠ 0
    rw [hfu]
    exact hx.1)
  change GlobalTheory.LFun.IsSatVecGL w P.ρ (f u) _ at h2
  rw [hfu] at h2
  exact ⟨fun i => (hB i).1, B, hB, h2.unique hx⟩

end GlobalTheory.CompanionTheory.ExpProd

end
