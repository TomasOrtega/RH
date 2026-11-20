import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.T2SpaceOfNonarchimedeanLocalField
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.IotaDense

/- English proof (translation)
Introduce `D p c hc`. Take `⟨hR, -, -, -, hO, -, -, -, hunit, hcl⟩` from `GlobalTheory.LocAtTopology.locAt_topology D.sp.cm D.conjF (fun x => by rw [D.conjF_eq, Formalism.BasicNotions.Examples₂.star_eq_conj]) p (D.s.atP p)`. Establish `hg : ((gS D : ℕ) : D.host.E) ≠ 0`. Establish `: gS D ≠ 0`. Unfold `gS`.

Conclude with `mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero`. Conclude with `this` after adjusting the coercions. Take `⟨w, hw⟩` from `hunit _ hg`. Use `set S : Set (D.s.atP p).Ep := (fun z => ((w⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) * (c - z)) ⁻¹' ((D.s.atP p).O : Set _) with hSdef`. Establish `hSo : IsOpen S` using `hO.preimage (continuous_const.mul (continuous_const.sub continuous_id))`.

Establish `hcS : c ∈ S` using `by show _ * (c - c) ∈ (D.s.atP p).O`. Rewrite using `[sub_self, mul_zero]`. Conclude with `zero_mem _`. Establish `hcc : c ∈ closure (Set.range fun x : 𝓞 D.host.E => (D.s.atP p).ιE (x : D.host.E))`. Rewrite using `[hcl]`.

Conclude with `hc`. Take `⟨z, hzS, a, rfl⟩` from `mem_closure_iff.1 hcc S hSo hcS`. Use `⟨a, _, hzS, ?_⟩` and prove the remaining obligations. Use `show c = _ + _ * (((w⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) * (c - _))`. Rewrite using `[← hw, ← mul_assoc, Units.mul_inv, one_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem iota_dense : ∀ (D : D7) (p : PlF D), ∀ c ∈ (D.s.atP p).O, ∃ a : 𝓞 D.host.E, ∃ o ∈ (D.s.atP p).O,
    c = (D.s.atP p).ιE (a : D.host.E) + (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o := by
  intro D p c hc
  obtain ⟨hR, -, -, -, hO, -, -, -, hunit, hcl⟩ := GlobalTheory.LocAtTopology.locAt_topology D.sp.cm D.conjF
    (fun x => by rw [D.conjF_eq, Formalism.BasicNotions.Examples₂.star_eq_conj]) p (D.s.atP p)
  have hg : ((gS D : ℕ) : D.host.E) ≠ 0 := by
    have : gS D ≠ 0 := by
      unfold gS
      exact mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
    exact_mod_cast this
  obtain ⟨w, hw⟩ := hunit _ hg
  set S : Set (D.s.atP p).Ep := (fun z => ((w⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) * (c - z)) ⁻¹' ((D.s.atP p).O : Set _)
    with hSdef
  have hSo : IsOpen S := hO.preimage (continuous_const.mul (continuous_const.sub continuous_id))
  have hcS : c ∈ S := by
    show _ * (c - c) ∈ (D.s.atP p).O
    rw [sub_self, mul_zero]; exact zero_mem _
  have hcc : c ∈ closure (Set.range fun x : 𝓞 D.host.E => (D.s.atP p).ιE (x : D.host.E)) := by
    rw [hcl]; exact hc
  obtain ⟨z, hzS, a, rfl⟩ := mem_closure_iff.1 hcc S hSo hcS
  refine ⟨a, _, hzS, ?_⟩
  show c = _ + _ * (((w⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) * (c - _))
  rw [← hw, ← mul_assoc, Units.mul_inv, one_mul]
  ring

end GlobalTheory.IotaDense
