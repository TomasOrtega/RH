import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.ValsExtOf

noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.Gal.GamX

/- English proof (translation)
Unfold `GamOneOf GamOne`. Introduce `hC hV hS K L _ _ _ _ _ _ _ _ hp n hn π P hW v w hw s s' hs hs'`. Establish `hsub : Subsingleton (PlacesOver L v)` using `⟨fun a b => (hw a).trans (hw b).symm⟩`. Establish `key : ∀ (u : PlacesOver L v) (h : w = u), SuppAt P u.1 (h ▸ s')`. Introduce and unpack `u rfl`.

Conclude with `hs'`. Establish `hval : ∀ θ : (v.adicCompletion K)ˣ →* ℂˣ, IsSmoothChar θ → vals (chs s') (θ.comp (nm w)) = vals (up w s) (θ.comp (nm w))`. Introduce `θ hθ`. Establish `h` using `hS K L hp n hn π P hW v s (fun u => (hw u).symm ▸ s') hs (fun u => key u (hw u).symm) θ hθ`. Rewrite `h` using `[Fintype.sum_subsingleton _ w, Fintype.sum_subsingleton _ w]`.

Conclude with `h`. Use `Multiset.ext.2 fun ζ => ?_` and prove the remaining obligations. Distinguish the cases in `hT : Thru w ζ`. Take `⟨χ, hχ, hu⟩` from `id hT`. Establish `hf` using `hV (w.1.adicCompletion L) (chs s') (up w s) (χ.comp (nm w)) (hval χ hχ)`.

Establish `hc` using `congrArg (Multiset.count ζ) hf`. Rewrite `hc` using `[Multiset.count_filter_of_pos (p := fun ξ => IsUnram (ξ * χ.comp (nm w))) hu, Multiset.count_filter_of_pos (p := fun ξ => IsUnram (ξ * χ.comp (nm w))) hu]`. Rewrite using `[Multiset.count_filter_of_pos hT]`. Conclude with `hc`. Rewrite using `[Multiset.count_filter_of_neg hT, eq_comm, Multiset.count_eq_zero]`.

Introduce `hm`. Take `⟨ξ, hξ, rfl⟩` from `Multiset.mem_map.1 hm`. Conclude with `hT ⟨ξ⁻¹, ((hC _ s).2.1 ξ hξ).inv, fun x _ => by simp⟩`.
-/
theorem gamOneOf : GamOneOf := by
  unfold GamOneOf GamOne
  intro hC hV hS K L _ _ _ _ _ _ _ _ hp n hn π P hW v w hw s s' hs hs'
  have hsub : Subsingleton (PlacesOver L v) := ⟨fun a b => (hw a).trans (hw b).symm⟩
  have key : ∀ (u : PlacesOver L v) (h : w = u), SuppAt P u.1 (h ▸ s') := by
    rintro u rfl
    exact hs'
  have hval : ∀ θ : (v.adicCompletion K)ˣ →* ℂˣ, IsSmoothChar θ →
      vals (chs s') (θ.comp (nm w)) = vals (up w s) (θ.comp (nm w)) := by
    intro θ hθ
    have h := hS K L hp n hn π P hW v s (fun u => (hw u).symm ▸ s') hs
      (fun u => key u (hw u).symm) θ hθ
    rw [Fintype.sum_subsingleton _ w, Fintype.sum_subsingleton _ w] at h
    exact h
  refine Multiset.ext.2 fun ζ => ?_
  by_cases hT : Thru w ζ
  · obtain ⟨χ, hχ, hu⟩ := id hT
    have hf := hV (w.1.adicCompletion L) (chs s') (up w s) (χ.comp (nm w)) (hval χ hχ)
    have hc := congrArg (Multiset.count ζ) hf
    rw [Multiset.count_filter_of_pos (p := fun ξ => IsUnram (ξ * χ.comp (nm w))) hu,
      Multiset.count_filter_of_pos (p := fun ξ => IsUnram (ξ * χ.comp (nm w))) hu] at hc
    rw [Multiset.count_filter_of_pos hT]
    exact hc
  · rw [Multiset.count_filter_of_neg hT, eq_comm, Multiset.count_eq_zero]
    intro hm
    obtain ⟨ξ, hξ, rfl⟩ := Multiset.mem_map.1 hm
    exact hT ⟨ξ⁻¹, ((hC _ s).2.1 ξ hξ).inv, fun x _ => by simp⟩

end UpperTheory.Gal.GamX
