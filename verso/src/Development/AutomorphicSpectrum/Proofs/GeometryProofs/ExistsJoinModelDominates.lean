import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinCoordsCentreChartStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueDominatingMapStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModelNonemptyStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtLocalOrderFractionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtChartLocalizationStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

/- English proof (translation)
Introduce `o _ Ω _ _ κ _ x M Ω' _ _ i κ' _ w hi ⟨l, hl⟩ hcl`. Set `p : Cpt M.ξ` to `⟨genPt M.ξ, specializes_rfl⟩`. Take `⟨c, hc⟩` from `M.tie.cover p`. Establish `hic : i (x c) ≠ 0` using `(map_ne_zero i).2 hc.1`. Establish `hJ : joinCo i x w (c, l) ≠ 0` using `mul_ne_zero hic hl`.

Establish `hgen : ∀ j l', joinCo i x w (j, l') / joinCo i x w (c, l) ∈ chRing o (joinCo i x w) (c, l)` using `fun j l' => Algebra.subset_adjoin ⟨(j, l'), rfl⟩`. Establish `hmap : ∀ a ∈ chRing o x c, i a ∈ chRing o (joinCo i x w) (c, l)`. Introduce `a ha`. Establish `ha' : a ∈ Algebra.adjoin o (Set.range fun j => x j / x c)` using `ha`. Proceed by induction on `ha' using Algebra.adjoin_induction with`.

Consider the case `mem y hy`. Take `⟨j, rfl⟩` from `hy`. Establish `: i (x j / x c) = joinCo i x w (j, l) / joinCo i x w (c, l)`. Simplify using `only [joinCo, map_div₀]`. Rewrite using `[mul_div_mul_right _ _ hl]`.

Rewrite using `[this]`. Conclude with `hgen _ _`. Consider the case `algebraMap r`. Rewrite using `[hi]`. Conclude with `Subalgebra.algebraMap_mem _ r`.

Consider the case `add y z _ _ hy hz`. Rewrite using `[map_add]`. Conclude with `add_mem (hy (by assumption)) (hz (by assumption))`. Consider the case `mul y z _ _ hy hz`. Rewrite using `[map_mul]`.

Conclude with `mul_mem (hy (by assumption)) (hz (by assumption))`. Establish `hAF : ∀ a ∈ chRing o (joinCo i x w) (c, l), a ∈ Subfield.closure (chRing o (joinCo i x w) (c, l) : Set Ω')` using `fun a ha => Subfield.subset_closure ha`. Establish `hiF : ∀ a : Ω, i a ∈ Subfield.closure (chRing o (joinCo i x w) (c, l) : Set Ω')`. Introduce `a`. Establish `h2` using `(GlobalTheory.T.regAt_chart_localization o Ω κ x M c p hc).2`.

Establish `key : ∀ b ∈ regAt M.ξ p, i b ∈ Subfield.closure (chRing o (joinCo i x w) (c, l) : Set Ω')`. Introduce `b hb`. Take `⟨s, hs, t, ht, -, rfl⟩` from `(h2 b).1 hb`. Rewrite using `[map_div₀]`. Conclude with `div_mem (hAF _ (hmap _ hs)) (hAF _ (hmap _ ht))`.

Take `⟨u, hu, v, hv, -, rfl⟩` from `(GlobalTheory.T.regAt_local_order_fraction M.X Ω M.ξ).2.2 M.tie.gen p a`. Rewrite using `[map_div₀]`. Conclude with `div_mem (key u hu) (key v hv)`. Establish `hw : ∀ l', w l' / w l ∈ chRing o (joinCo i x w) (c, l)`. Introduce `l'`.

Establish `: w l' / w l = joinCo i x w (c, l') / joinCo i x w (c, l)`. Simplify using `only [joinCo]`. Rewrite using `[mul_div_mul_left _ _ hic]`. Rewrite using `[this]`. Conclude with `hgen _ _`.

Establish `hle : Subfield.closure (Set.range i ∪ {a | ∃ l l', a = w l / w l'}) ≤ Subfield.closure (chRing o (joinCo i x w) (c, l) : Set Ω')`. Use `Subfield.closure_le.2 (Set.union_subset ?_ ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `hiF a`. Introduce and unpack `_ ⟨a, b, rfl⟩`.

Rewrite using `[← div_div_div_cancel_right₀ hl (w a) (w b)]`. Conclude with `div_mem (hAF _ (hw a)) (hAF _ (hw b))`. Establish `hfrac : ∀ a : Ω', ∃ u ∈ chRing o (joinCo i x w) (c, l), ∃ v ∈ chRing o (joinCo i x w) (c, l), a = u / v`. Introduce `a`. Establish `ha : a ∈ Subfield.closure (chRing o (joinCo i x w) (c, l) : Set Ω')` using `hle (by rw [hcl]; exact Subfield.mem_top a)`.

Take `⟨y, hy, z, hz, rfl⟩` from `Subfield.mem_closure_iff.1 ha`. Establish `hs : Subring.closure (chRing o (joinCo i x w) (c, l) : Set Ω') = (chRing o (joinCo i x w) (c, l)).toSubring` using `Subring.closure_eq (chRing o (joinCo i x w) (c, l)).toSubring`. Rewrite `hy`, `hz` using `[hs]`. Conclude with `⟨y, hy, z, hz, rfl⟩`. Take `⟨M'⟩` from `GlobalTheory.T.projective_model_nonempty o Ω' (κ × κ') (joinCo i x w) ⟨(c, l), hJ, hfrac⟩`.

Establish `hctr : ∀ p', p' ∈ ctrSet o x i M'.ξ` using `fun p' => (GlobalTheory.T.join_coords_centre_chart o Ω κ κ' x Ω' i w M' hi p').1`. Take `⟨f, hf, -⟩` from `GlobalTheory.T.existsUnique_dominating_map o Ω κ x M o Ω' (κ × κ') (joinCo i x w) M' i hctr`. Conclude with `⟨M', f, hf⟩`.
-/
theorem join_exists : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (i : Ω →+* Ω') (κ' : Type) [Finite κ'] (w : κ' → Ω'), (∀ a : o, i (algebraMap o Ω a) = algebraMap o Ω' a) → (∃ l, w l ≠ 0) → Subfield.closure (Set.range i ∪ {a | ∃ l l', a = w l / w l'}) = ⊤ → ∃ (M' : PModel o (joinCo i x w)) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f i := by
  intro o _ Ω _ _ κ _ x M Ω' _ _ i κ' _ w hi ⟨l, hl⟩ hcl
  let p : Cpt M.ξ := ⟨genPt M.ξ, specializes_rfl⟩
  obtain ⟨c, hc⟩ := M.tie.cover p
  have hic : i (x c) ≠ 0 := (map_ne_zero i).2 hc.1
  have hJ : joinCo i x w (c, l) ≠ 0 := mul_ne_zero hic hl
  have hgen : ∀ j l', joinCo i x w (j, l') / joinCo i x w (c, l) ∈ chRing o (joinCo i x w) (c, l) :=
    fun j l' => Algebra.subset_adjoin ⟨(j, l'), rfl⟩
  have hmap : ∀ a ∈ chRing o x c, i a ∈ chRing o (joinCo i x w) (c, l) := by
    intro a ha
    have ha' : a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := ha
    induction ha' using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      have : i (x j / x c) = joinCo i x w (j, l) / joinCo i x w (c, l) := by
        simp only [joinCo, map_div₀]
        rw [mul_div_mul_right _ _ hl]
      rw [this]
      exact hgen _ _
    | algebraMap r =>
      rw [hi]
      exact Subalgebra.algebraMap_mem _ r
    | add y z _ _ hy hz =>
      rw [map_add]
      exact add_mem (hy (by assumption)) (hz (by assumption))
    | mul y z _ _ hy hz =>
      rw [map_mul]
      exact mul_mem (hy (by assumption)) (hz (by assumption))
  have hAF : ∀ a ∈ chRing o (joinCo i x w) (c, l),
      a ∈ Subfield.closure (chRing o (joinCo i x w) (c, l) : Set Ω') :=
    fun a ha => Subfield.subset_closure ha
  have hiF : ∀ a : Ω, i a ∈ Subfield.closure (chRing o (joinCo i x w) (c, l) : Set Ω') := by
    intro a
    have h2 := (GlobalTheory.T.regAt_chart_localization o Ω κ x M c p hc).2
    have key : ∀ b ∈ regAt M.ξ p, i b ∈ Subfield.closure (chRing o (joinCo i x w) (c, l) : Set Ω') := by
      intro b hb
      obtain ⟨s, hs, t, ht, -, rfl⟩ := (h2 b).1 hb
      rw [map_div₀]
      exact div_mem (hAF _ (hmap _ hs)) (hAF _ (hmap _ ht))
    obtain ⟨u, hu, v, hv, -, rfl⟩ := (GlobalTheory.T.regAt_local_order_fraction M.X Ω M.ξ).2.2 M.tie.gen p a
    rw [map_div₀]
    exact div_mem (key u hu) (key v hv)
  have hw : ∀ l', w l' / w l ∈ chRing o (joinCo i x w) (c, l) := by
    intro l'
    have : w l' / w l = joinCo i x w (c, l') / joinCo i x w (c, l) := by
      simp only [joinCo]
      rw [mul_div_mul_left _ _ hic]
    rw [this]
    exact hgen _ _
  have hle : Subfield.closure (Set.range i ∪ {a | ∃ l l', a = w l / w l'}) ≤
      Subfield.closure (chRing o (joinCo i x w) (c, l) : Set Ω') := by
    refine Subfield.closure_le.2 (Set.union_subset ?_ ?_)
    · rintro _ ⟨a, rfl⟩
      exact hiF a
    · rintro _ ⟨a, b, rfl⟩
      rw [← div_div_div_cancel_right₀ hl (w a) (w b)]
      exact div_mem (hAF _ (hw a)) (hAF _ (hw b))
  have hfrac : ∀ a : Ω', ∃ u ∈ chRing o (joinCo i x w) (c, l), ∃ v ∈ chRing o (joinCo i x w) (c, l),
      a = u / v := by
    intro a
    have ha : a ∈ Subfield.closure (chRing o (joinCo i x w) (c, l) : Set Ω') :=
      hle (by rw [hcl]; exact Subfield.mem_top a)
    obtain ⟨y, hy, z, hz, rfl⟩ := Subfield.mem_closure_iff.1 ha
    have hs : Subring.closure (chRing o (joinCo i x w) (c, l) : Set Ω') =
        (chRing o (joinCo i x w) (c, l)).toSubring :=
      Subring.closure_eq (chRing o (joinCo i x w) (c, l)).toSubring
    rw [hs] at hy hz
    exact ⟨y, hy, z, hz, rfl⟩
  obtain ⟨M'⟩ := GlobalTheory.T.projective_model_nonempty o Ω' (κ × κ') (joinCo i x w) ⟨(c, l), hJ, hfrac⟩
  have hctr : ∀ p', p' ∈ ctrSet o x i M'.ξ := fun p' => (GlobalTheory.T.join_coords_centre_chart o Ω κ κ' x Ω' i w M' hi p').1
  obtain ⟨f, hf, -⟩ := GlobalTheory.T.existsUnique_dominating_map o Ω κ x M o Ω' (κ × κ') (joinCo i x w) M' i hctr
  exact ⟨M', f, hf⟩

end GlobalTheory.CompanionTheory.Ar
