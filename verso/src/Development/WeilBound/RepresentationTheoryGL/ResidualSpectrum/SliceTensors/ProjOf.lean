import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PProjA

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs

open ParabolicProjection in
/- English proof (translation)
Introduce `E _ _ _ r s _ _ V hV c z₁ z₂ T hTs hL2`. Establish `hmem` using `hT E r s V hV c z₁ z₂ T hTs hL2`. Take `⟨φ₀, hφ₀V, hφ₀⟩` from `hTs.ne`. Take `⟨k₀, g₀, m₀, hm₀⟩` from `exists_slice_ne hφ₀ (hTs.unipInv φ₀ hφ₀V)`. Take `⟨n, ψ₁, ψ₂, h₁, h₂, hsum⟩` from `tensor_pair_finite_sum ((hmem φ₀ hφ₀V).2 k₀ g₀)`.

Establish `hne : ∑ i, (ψ₁ i).1 m₀.1 * (ψ₂ i).1 m₀.2 ≠ 0` using `(hsum m₀) ▸ hm₀`. Take `⟨hst₁, hsep₁⟩` from `hP E r`. Take `⟨hst₂, hsep₂⟩` from `hP E s`. Take `⟨χ₁, hχ₁, hχ₁e⟩ : ∑ i, (ψ₂ i).1 m₀.2 • ψ₁ i ∈ tw (A2 E r) z₁` from `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h₁ i)`. Establish `hχ₁0 : χ₁ ≠ 0` using `fun h => sum_left_ne hne (by rw [← hχ₁e, h, map_zero])`.

Take `⟨V₁, p₁, hV₁, hp₁V, hp₁e, hp₁0⟩` from `hsep₁ χ₁ hχ₁ hχ₁0`. Establish `hf₁ : twMap r z₁ p₁ (∑ i, (ψ₂ i).1 m₀.2 • ψ₁ i) ≠ 0`. Rewrite using `[← hχ₁e]`. Express the relevant statement in the definitionally equal form `twMap r z₁ p₁ (mulChi r (Model.absC E z₁) χ₁) ≠ 0`. Rewrite using `[twMap_apply, mulChi_absC_neg, Ne, LinearEquiv.map_eq_zero_iff]`.

Conclude with `hp₁0`. Take `⟨b₁, hb₁⟩` from `step_left (twMap r z₁ p₁) hf₁`. Take `⟨χ₂, hχ₂, hχ₂e⟩ : ∑ i, (twMap r z₁ p₁ (ψ₁ i)).1 b₁ • ψ₂ i ∈ tw (A2 E s) z₂` from `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h₂ i)`. Establish `hχ₂0 : χ₂ ≠ 0` using `fun h => sum_right_ne hb₁ (by rw [← hχ₂e, h, map_zero])`. Take `⟨V₂, p₂, hV₂, hp₂V, hp₂e, hp₂0⟩` from `hsep₂ χ₂ hχ₂ hχ₂0`.

Establish `hf₂ : twMap s z₂ p₂ (∑ i, (twMap r z₁ p₁ (ψ₁ i)).1 b₁ • ψ₂ i) ≠ 0`. Rewrite using `[← hχ₂e]`. Express the relevant statement in the definitionally equal form `twMap s z₂ p₂ (mulChi s (Model.absC E z₂) χ₂) ≠ 0`. Rewrite using `[twMap_apply, mulChi_absC_neg, Ne, LinearEquiv.map_eq_zero_iff]`. Conclude with `hp₂0`.

Take `⟨b₂, hb₂⟩` from `step_right (twMap s z₂ p₂) hf₂`. Take `⟨T', hT'e, hT'u, hT's⟩` from `hI E r s V (tw (A2 E r) z₁) (tw (A2 E s) z₂) T (twMap r z₁ p₁) (twMap s z₂ p₂) hV.stable hV.aut (isStable_tw hst₁ z₁) (isStable_tw hst₂ z₂) hTs.equiv hmem (twMap_equiv hst₁ hp₁e) (twMap_equiv hst₂ hp₂e)`. Use `⟨V₁, V₂, hV₁, hV₂, T', fun φ hφ => ⟨hT'u φ hφ, fun k g => ?_⟩, inj_of_irred hV hT'e ⟨φ₀, hφ₀V, fun h => ?_⟩, hT'e⟩` and prove the remaining obligations. Take `⟨n', ψ₁', ψ₂', h₁', h₂', hs'⟩` from `tensor_pair_finite_sum ((hmem φ hφ).2 k g)`. Establish `e` using `hT's φ hφ k g n' ψ₁' ψ₂' h₁' h₂' hs'`.

Rewrite using `[show (fun m : GA E r × GA E s => (T' φ).1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) = fun m => ∑ i, (twMap r z₁ p₁ (ψ₁' i)).1 m.1 * (twMap s z₂ p₂ (ψ₂' i)).1 m.2 from funext e]`. Conclude with `sum_mem_tens2 (fun i => twMap_mem hp₁V _ (h₁' i)) (fun i => twMap_mem hp₂V _ (h₂' i))`. Establish `e` using `hT's φ₀ hφ₀V k₀ g₀ n ψ₁ ψ₂ h₁ h₂ hsum (b₁, b₂)`. Rewrite `e` using `[h]`. Conclude with `hb₂ e.symm`.
-/
theorem proj_of (hP : Pr) (hT : SliceTens) (hI : IndMap) : Proj := by
  intro E _ _ _ r s _ _ V hV c z₁ z₂ T hTs hL2
  have hmem := hT E r s V hV c z₁ z₂ T hTs hL2
  obtain ⟨φ₀, hφ₀V, hφ₀⟩ := hTs.ne
  obtain ⟨k₀, g₀, m₀, hm₀⟩ := exists_slice_ne hφ₀ (hTs.unipInv φ₀ hφ₀V)
  obtain ⟨n, ψ₁, ψ₂, h₁, h₂, hsum⟩ := tensor_pair_finite_sum ((hmem φ₀ hφ₀V).2 k₀ g₀)
  have hne : ∑ i, (ψ₁ i).1 m₀.1 * (ψ₂ i).1 m₀.2 ≠ 0 := (hsum m₀) ▸ hm₀
  obtain ⟨hst₁, hsep₁⟩ := hP E r
  obtain ⟨hst₂, hsep₂⟩ := hP E s

  obtain ⟨χ₁, hχ₁, hχ₁e⟩ : ∑ i, (ψ₂ i).1 m₀.2 • ψ₁ i ∈ tw (A2 E r) z₁ :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h₁ i)
  have hχ₁0 : χ₁ ≠ 0 := fun h => sum_left_ne hne (by rw [← hχ₁e, h, map_zero])
  obtain ⟨V₁, p₁, hV₁, hp₁V, hp₁e, hp₁0⟩ := hsep₁ χ₁ hχ₁ hχ₁0
  have hf₁ : twMap r z₁ p₁ (∑ i, (ψ₂ i).1 m₀.2 • ψ₁ i) ≠ 0 := by
    rw [← hχ₁e]
    change twMap r z₁ p₁ (mulChi r (Model.absC E z₁) χ₁) ≠ 0
    rw [twMap_apply, mulChi_absC_neg, Ne, LinearEquiv.map_eq_zero_iff]
    exact hp₁0
  obtain ⟨b₁, hb₁⟩ := step_left (twMap r z₁ p₁) hf₁

  obtain ⟨χ₂, hχ₂, hχ₂e⟩ : ∑ i, (twMap r z₁ p₁ (ψ₁ i)).1 b₁ • ψ₂ i ∈ tw (A2 E s) z₂ :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h₂ i)
  have hχ₂0 : χ₂ ≠ 0 := fun h => sum_right_ne hb₁ (by rw [← hχ₂e, h, map_zero])
  obtain ⟨V₂, p₂, hV₂, hp₂V, hp₂e, hp₂0⟩ := hsep₂ χ₂ hχ₂ hχ₂0
  have hf₂ : twMap s z₂ p₂ (∑ i, (twMap r z₁ p₁ (ψ₁ i)).1 b₁ • ψ₂ i) ≠ 0 := by
    rw [← hχ₂e]
    change twMap s z₂ p₂ (mulChi s (Model.absC E z₂) χ₂) ≠ 0
    rw [twMap_apply, mulChi_absC_neg, Ne, LinearEquiv.map_eq_zero_iff]
    exact hp₂0
  obtain ⟨b₂, hb₂⟩ := step_right (twMap s z₂ p₂) hf₂

  obtain ⟨T', hT'e, hT'u, hT's⟩ := hI E r s V (tw (A2 E r) z₁) (tw (A2 E s) z₂) T (twMap r z₁ p₁) (twMap s z₂ p₂)
    hV.stable hV.aut (isStable_tw hst₁ z₁) (isStable_tw hst₂ z₂) hTs.equiv hmem (twMap_equiv hst₁ hp₁e)
    (twMap_equiv hst₂ hp₂e)
  refine ⟨V₁, V₂, hV₁, hV₂, T', fun φ hφ => ⟨hT'u φ hφ, fun k g => ?_⟩, inj_of_irred hV hT'e ⟨φ₀, hφ₀V, fun h => ?_⟩, hT'e⟩
  · obtain ⟨n', ψ₁', ψ₂', h₁', h₂', hs'⟩ := tensor_pair_finite_sum ((hmem φ hφ).2 k g)
    have e := hT's φ hφ k g n' ψ₁' ψ₂' h₁' h₂' hs'
    rw [show (fun m : GA E r × GA E s => (T' φ).1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) *
      finGL E (r + s) g))) = fun m => ∑ i, (twMap r z₁ p₁ (ψ₁' i)).1 m.1 * (twMap s z₂ p₂ (ψ₂' i)).1 m.2 from funext e]
    exact sum_mem_tens2 (fun i => twMap_mem hp₁V _ (h₁' i)) (fun i => twMap_mem hp₂V _ (h₂' i))
  · have e := hT's φ₀ hφ₀V k₀ g₀ n ψ₁ ψ₂ h₁ h₂ hsum (b₁, b₂)
    rw [h] at e
    exact hb₂ e.symm

end PositivityTheory.Rg.Rs

end
