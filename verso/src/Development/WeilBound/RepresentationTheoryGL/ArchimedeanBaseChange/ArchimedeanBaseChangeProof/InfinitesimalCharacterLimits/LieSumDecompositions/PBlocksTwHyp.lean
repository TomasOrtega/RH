import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.SplitInv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TensorOperatorTrees.InfTree
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PrHolds
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PProjA
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PChordA

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open scoped Classical

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockTwistCharacters

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

/- English proof (translation)
Establish `h` using `ChordArithmetic.mulChi_absC_cancel (E := E) a (-w) ψ`. Rewrite `h` using `[neg_neg]`. Then use the resulting hypothesis.
-/
theorem mulChi_neg_cancel (w : ℂ) (ψ : Sm E a) :
    mulChi a (Model.absC E (-w)) (mulChi a (Model.absC E w) ψ) = ψ := by
  have h := ChordArithmetic.mulChi_absC_cancel (E := E) a (-w) ψ
  rwa [neg_neg] at h

/- English proof (translation)
Use `⟨ParabolicProjection.isStable_tw hV.1 w, fun φ hφ => ?_⟩` and prove the remaining obligations. Take `⟨ψ, hψ, rfl⟩` from `Submodule.mem_map.1 hφ`. Conclude with `(hV.2 ψ hψ).mulChi _`.
-/
theorem isAutSt_tw {V : Submodule ℂ (Sm E a)} (hV : IsAutSt V) (w : ℂ) : IsAutSt (tw V w) := by
  refine ⟨ParabolicProjection.isStable_tw hV.1 w, fun φ hφ => ?_⟩
  obtain ⟨ψ, hψ, rfl⟩ := Submodule.mem_map.1 hφ
  exact (hV.2 ψ hψ).mulChi _

/- English proof (translation)
Take `⟨S, hS, hgen⟩` from `hV`. Use `⟨S.image (mulChi a (Model.absC E w)), ?_, fun W hW hSW => ?_⟩` and prove the remaining obligations. Introduce `x hx`. Take `⟨y, hy, rfl⟩` from `Finset.mem_image.1 (Finset.mem_coe.1 hx)`. Conclude with `Submodule.mem_map_of_mem (hS (Finset.mem_coe.2 hy))`.

Establish `hle : V ≤ tw W (-w)` using `hgen _ (ParabolicProjection.isStable_tw hW (-w)) (fun y hy => by`. Establish `hmem : mulChi a (Model.absC E w) y ∈ W` using `hSW (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hy)))`. Establish `h : (mulChi a (Model.absC E (-w))).toLinearMap (mulChi a (Model.absC E w) y) ∈ tw W (-w)` using `Submodule.mem_map_of_mem hmem`. Rewrite `h` using `[LinearEquiv.coe_coe, mulChi_neg_cancel]`. Conclude with `h)`.

Introduce `φ hφ`. Take `⟨ψ, hψ, rfl⟩` from `Submodule.mem_map.1 hφ`. Take `⟨χ, hχ, rfl⟩` from `Submodule.mem_map.1 (hle hψ)`. Establish `e` using `ChordArithmetic.mulChi_absC_cancel (E := E) a w χ`. Simplify using `only [LinearEquiv.coe_coe] at e ⊢`.

Rewrite using `[e]`. Conclude with `hχ`.
-/
theorem finGen_tw {V : Submodule ℂ (Sm E a)} (hV : FinGen V) (w : ℂ) : FinGen (tw V w) := by
  obtain ⟨S, hS, hgen⟩ := hV
  refine ⟨S.image (mulChi a (Model.absC E w)), ?_, fun W hW hSW => ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    exact Submodule.mem_map_of_mem (hS (Finset.mem_coe.2 hy))
  · have hle : V ≤ tw W (-w) := hgen _ (ParabolicProjection.isStable_tw hW (-w)) (fun y hy => by
      have hmem : mulChi a (Model.absC E w) y ∈ W :=
        hSW (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hy)))
      have h : (mulChi a (Model.absC E (-w))).toLinearMap (mulChi a (Model.absC E w) y) ∈ tw W (-w) :=
        Submodule.mem_map_of_mem hmem
      rw [LinearEquiv.coe_coe, mulChi_neg_cancel] at h
      exact h)
    intro φ hφ
    obtain ⟨ψ, hψ, rfl⟩ := Submodule.mem_map.1 hφ
    obtain ⟨χ, hχ, rfl⟩ := Submodule.mem_map.1 (hle hψ)
    have e := ChordArithmetic.mulChi_absC_cancel (E := E) a w χ
    simp only [LinearEquiv.coe_coe] at e ⊢
    rw [e]
    exact hχ

/- English proof (translation)
Take `⟨m, hm, hnd⟩` from `h`. Conclude with `⟨m.map (· + w), SpectralAccumulation.Trees.hasInfCharGL_tw hm w, hnd.map (add_left_injective w)⟩`.
-/
theorem infNodup_tw {V : Submodule ℂ (Sm E a)} {τ : E →+* ℂ} (h : ∃ m, HasInfCharGL V τ m ∧ m.Nodup) (w : ℂ) :
    ∃ m, HasInfCharGL (tw V w) τ m ∧ m.Nodup := by
  obtain ⟨m, hm, hnd⟩ := h
  exact ⟨m.map (· + w), SpectralAccumulation.Trees.hasInfCharGL_tw hm w, hnd.map (add_left_injective w)⟩

/- English proof (translation)
Introduce `τ` and use `infNodup_tw (hV τ) w`.
-/
theorem regAll_tw {V : Submodule ℂ (Sm E a)} (hV : RegAll V) (w : ℂ) : RegAll (tw V w) :=
  fun τ => infNodup_tw (hV τ) w

/- English proof (translation)
Assemble the required witnesses or components as `⟨isAutSt_tw hA w, finGen_tw hF w, hN, hC, infNodup_tw hI w, regAll_tw hR w⟩`.
-/
theorem hyp_tw {V : Submodule ℂ (Sm E a)} {τ : E →+* ℂ} (w : ℂ) (hA : IsAutSt V) (hF : FinGen V)
    (hI : ∃ m, HasInfCharGL V τ m ∧ m.Nodup) (hR : RegAll V) (hN : SpectralAccumulation.NonPos (tw V w)) (hC : SpectralAccumulation.CentIm (tw V w)) :
    Hyp τ (tw V w) :=
  ⟨isAutSt_tw hA w, finGen_tw hF w, hN, hC, infNodup_tw hI w, regAll_tw hR w⟩

/- English proof (translation)
Use extensionality with `φ`. Prove the components needed by the constructor for the conclusion. Introduce `hφ`. Take `⟨χ, hχ, rfl⟩` from `Submodule.mem_map.1 hφ`. Take `⟨ψ, hψ, rfl⟩` from `Submodule.mem_map.1 hχ`.

Simplify using `only [LinearEquiv.coe_coe]`. Rewrite using `[ChordArithmetic.mulChi_absC_cancel]`. Conclude with `hψ`. Introduce `hφ`. Establish `h1 : (mulChi a (Model.absC E (-w))).toLinearMap φ ∈ tw V (-w)` using `Submodule.mem_map_of_mem hφ`.

Establish `h2` using `Submodule.mem_map_of_mem (f := (mulChi a (Model.absC E w)).toLinearMap) h1`. Simplify using `only [LinearEquiv.coe_coe] at h2`. Rewrite `h2` using `[ChordArithmetic.mulChi_absC_cancel]`. Conclude with `h2`.
-/
theorem tw_tw_neg (V : Submodule ℂ (Sm E a)) (w : ℂ) : tw (tw V (-w)) w = V := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨χ, hχ, rfl⟩ := Submodule.mem_map.1 hφ
    obtain ⟨ψ, hψ, rfl⟩ := Submodule.mem_map.1 hχ
    simp only [LinearEquiv.coe_coe]
    rw [ChordArithmetic.mulChi_absC_cancel]
    exact hψ
  · intro hφ
    have h1 : (mulChi a (Model.absC E (-w))).toLinearMap φ ∈ tw V (-w) := Submodule.mem_map_of_mem hφ
    have h2 := Submodule.mem_map_of_mem (f := (mulChi a (Model.absC E w)).toLinearMap) h1
    simp only [LinearEquiv.coe_coe] at h2
    rw [ChordArithmetic.mulChi_absC_cancel] at h2
    exact h2

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockTwistCharacters

end
