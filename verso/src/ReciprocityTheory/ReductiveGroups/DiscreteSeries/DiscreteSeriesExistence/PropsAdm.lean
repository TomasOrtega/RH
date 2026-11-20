import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsKfin

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

/- English proof (translation)
Establish `hU` using `isInfUnitary_of_isDerivedOn hσ hD`. Establish `hE` using `hD.glRep`. Take `⟨k, hk⟩` from `khw_mem_layer hE hU hV hc hgap μ`. Establish `hLf : FiniteDimensional ℂ (layer ε E V k)` using `finiteDimensional_layer hV.1 k`. Establish `hLK` using `kStable_of_isKStableSub hσ hD (layer ε E V k) hLf (layer_kStable hE hV.2.1 k)`.

Establish `hMf : FiniteDimensional ℂ ((layer ε E V k).map D.subtype)` using `Module.Finite.map _ _`. Establish `hle : (sSup {S : Submodule ℂ H | S ≤ closGen E V ∧ Formalism.MainNotions.S.IsKTypeOf ε σ μ S} : Submodule ℂ H) ≤ (layer ε E V k).map D.subtype`. Use `sSup_le fun S hSmem => ?_` and prove the remaining obligations. Take `⟨hS, hST⟩` from `hSmem`. Take `⟨hSf, hSK, hirr, -, -⟩` from `id hST`.

Establish `hSM` using `data_kfin_le hgap hσ hD hV hc hVK S hS hSf (fun g hg x hx => hSK g hg x hx)`. Establish `hSD : S ≤ D` using `hSM.trans (Submodule.map_subtype_le _ _)`. Take `⟨w, hwS, hw0, hwμ⟩` from `exists_isKHWVec_of_isKTypeOf hσ hD hST hSD`. Establish `hwg : w ∈ genSub E V`. Take `⟨y, hy, hyw⟩` from `Submodule.mem_map.1 (hSM hwS)`.

Establish `: y = w` using `Subtype.ext hyw`. Conclude with `this ▸ hy`. Establish `hwL` using `hk w hwg hwμ`. Establish `hS'K : Formalism.MainNotions.S.IsKStableOn ε σ (S ⊓ (layer ε E V k).map D.subtype)`. Introduce `g hg v hv`.

Use `⟨hSK g hg v hv.1, ?_⟩` and prove the remaining obligations. Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.1 hv.2`. Take `⟨z, hz, hzeq⟩` from `hLK g hg y hy`. Conclude with `Submodule.mem_map.2 ⟨z, hz, hzeq⟩`. Break down `hirr _ inf_le_left hS'K with h0 | hEq` into its components or cases.

It suffices to derive a contradiction. Establish `hmem : (w : H) ∈ S ⊓ (layer ε E V k).map D.subtype` using `⟨hwS, Submodule.mem_map_of_mem hwL⟩`. Rewrite `hmem` using `[h0, Submodule.mem_bot]`. Conclude with `hw0 (Subtype.ext hmem)`. Rewrite using `[← hEq]`.

Conclude with `inf_le_right`. Conclude with `Submodule.finiteDimensional_of_le hle`.
-/
theorem data_admissible (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (μ : Fin n → ℝ) :
    FiniteDimensional ℂ
      (sSup {S : Submodule ℂ H | S ≤ closGen E V ∧ Formalism.MainNotions.S.IsKTypeOf ε σ μ S} : Submodule ℂ H) := by
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  have hE := hD.glRep
  obtain ⟨k, hk⟩ := khw_mem_layer hE hU hV hc hgap μ
  have hLf : FiniteDimensional ℂ (layer ε E V k) := finiteDimensional_layer hV.1 k
  have hLK := kStable_of_isKStableSub hσ hD (layer ε E V k) hLf (layer_kStable hE hV.2.1 k)
  have hMf : FiniteDimensional ℂ ((layer ε E V k).map D.subtype) := Module.Finite.map _ _
  have hle : (sSup {S : Submodule ℂ H | S ≤ closGen E V ∧ Formalism.MainNotions.S.IsKTypeOf ε σ μ S} : Submodule ℂ H) ≤
      (layer ε E V k).map D.subtype := by
    refine sSup_le fun S hSmem => ?_
    obtain ⟨hS, hST⟩ := hSmem
    obtain ⟨hSf, hSK, hirr, -, -⟩ := id hST
    have hSM := data_kfin_le hgap hσ hD hV hc hVK S hS hSf (fun g hg x hx => hSK g hg x hx)
    have hSD : S ≤ D := hSM.trans (Submodule.map_subtype_le _ _)
    obtain ⟨w, hwS, hw0, hwμ⟩ := exists_isKHWVec_of_isKTypeOf hσ hD hST hSD
    have hwg : w ∈ genSub E V := by
      obtain ⟨y, hy, hyw⟩ := Submodule.mem_map.1 (hSM hwS)
      have : y = w := Subtype.ext hyw
      exact this ▸ hy
    have hwL := hk w hwg hwμ
    have hS'K : Formalism.MainNotions.S.IsKStableOn ε σ (S ⊓ (layer ε E V k).map D.subtype) := by
      intro g hg v hv
      refine ⟨hSK g hg v hv.1, ?_⟩
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hv.2
      obtain ⟨z, hz, hzeq⟩ := hLK g hg y hy
      exact Submodule.mem_map.2 ⟨z, hz, hzeq⟩
    rcases hirr _ inf_le_left hS'K with h0 | hEq
    · exfalso
      have hmem : (w : H) ∈ S ⊓ (layer ε E V k).map D.subtype :=
        ⟨hwS, Submodule.mem_map_of_mem hwL⟩
      rw [h0, Submodule.mem_bot] at hmem
      exact hw0 (Subtype.ext hmem)
    · rw [← hEq]
      exact inf_le_right
  exact Submodule.finiteDimensional_of_le hle

end ReciprocityTheory.ChartRestriction.DS
