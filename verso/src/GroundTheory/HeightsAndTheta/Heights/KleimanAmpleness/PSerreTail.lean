import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v

/- English proof (translation)
Introduce `S _ _ N M _ _ _ _ 𝓜 hM c₁`. Establish `hfg : ∀ c : ℤ, ∃ s : Finset (Cech.Cochain (locSys S N M) 0), Submodule.span S (s : Set _) = Cech.cocyDeg (locSys S N M) (degLoc 𝓜 c) locResS 0`. Introduce `c`. Establish `h0 : (Cech.bdryDeg (locSys S N M) (degLoc 𝓜 c) locResS 0).comap (Cech.cocyDeg (locSys S N M) (degLoc 𝓜 c) locResS 0).subtype = ⊥`. Express the relevant statement in the definitionally equal form `Submodule.comap _ ⊥ = ⊥`.

Rewrite using `[Submodule.comap_bot, Submodule.ker_subtype]`. Establish `hf : Module.Finite S (Cech.cocyDeg (locSys S N M) (degLoc 𝓜 c) locResS 0 ⧸ (Cech.bdryDeg (locSys S N M) (degLoc 𝓜 c) locResS 0).comap (Cech.cocyDeg (locSys S N M) (degLoc 𝓜 c) locResS 0).subtype)` using `hFin S N M 𝓜 hM 0 c`. Establish `hf' : Module.Finite S (Cech.cocyDeg (locSys S N M) (degLoc 𝓜 c) locResS 0)` using `Module.Finite.equiv (Submodule.quotEquivOfEqBot _ h0)`. Take `⟨s, hs⟩` from `Module.Finite.iff_fg.mp hf'`. Conclude with `⟨s, hs⟩`.

Use `choose s hs using hfg`. Take `⟨c₀, hc₀⟩` from `hOnto S N M 𝓜 hM`. Use `set c₂ := max c₀ c₁`. Set `Φ : M →ₗ[Poly S N] Cech.Cochain (locSys S N M) 0` to `LinearMap.pi fun I => locMk M I.1.1`. Set `T : Finset (Cech.Cochain (locSys S N M) 0)` to `(Finset.Ico c₁ c₂).biUnion s`.

Set `B : Submodule (Poly S N) (Cech.Cochain (locSys S N M) 0)` to `LinearMap.range Φ ⊔ Submodule.span (Poly S N) (T : Set _)`. Establish `hB : B.FG`. Use `Submodule.FG.sup ?_ (Submodule.fg_span T.finite_toSet)` and prove the remaining obligations. Rewrite using `[LinearMap.range_eq_map]`. Conclude with `(Module.Finite.fg_top).map Φ`.

Establish `hA : H0tail 𝓜 c₁ ≤ B.restrictScalars S`. Use `iSup₂_le fun c hc => ?_` and prove the remaining obligations. Introduce `z hz`. Distinguish the cases in `hc2 : c₂ ≤ c`. Take `⟨m, hm⟩` from `hc₀ c (le_trans (le_max_left _ _) hc2) (Submodule.Quotient.mk ⟨z, hz⟩)`.

Establish `hz' : (constCochain (m : M) : Cech.Cochain (locSys S N M) 0) = z`. Use `(Submodule.Quotient.eq _).mp hm` as an intermediate fact. Express the relevant statement in the definitionally equal form `_ ∈ Submodule.comap _ ⊥ at this`. Rewrite `this` using `[Submodule.mem_comap, Submodule.mem_bot, map_sub, sub_eq_zero]`. Conclude with `this`.

Rewrite using `[← hz']`. Conclude with `Submodule.mem_sup_left ⟨(m : M), rfl⟩`. Establish `hcI : c ∈ Finset.Ico c₁ c₂` using `Finset.mem_Ico.mpr ⟨hc, lt_of_not_ge hc2⟩`. Rewrite `hz` using `[← hs c]`. Use `Submodule.mem_sup_right (Submodule.span_le_restrictScalars S (Poly S N) _ ?_)` and prove the remaining obligations.

Use `Submodule.span_mono ?_ hz` and prove the remaining obligations. Introduce `y hy`. Conclude with `Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨c, hcI, hy⟩)`. Establish `hspan : Submodule.span (Poly S N) (H0tail 𝓜 c₁ : Set (Cech.Cochain (locSys S N M) 0)) ≤ B` using `Submodule.span_le.mpr hA`. Establish `: IsNoetherian (Poly S N) B` using `isNoetherian_of_fg_of_noetherian B hB`.

Take `⟨t, ht, hteq⟩` from `(Submodule.fg_span_iff_fg_span_finset_subset _).mp (Submodule.FG.of_le_of_isNoetherian hspan)`. Use `⟨t, fun z hz => ht hz, fun z hz => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `z ∈ Submodule.span (Poly S N) (t : Set _)`. Rewrite using `[← hteq]`. Conclude with `Submodule.subset_span hz`.
-/
theorem SerreTail.proof (hFin : SerreFinite.Statement.{u, v}) (hOnto : SerreOnto.Statement.{u, v}) :
    SerreTail.Statement.{u, v} := by
  classical
  intro S _ _ N M _ _ _ _ 𝓜 hM c₁

  have hfg : ∀ c : ℤ, ∃ s : Finset (Cech.Cochain (locSys S N M) 0),
      Submodule.span S (s : Set _) = Cech.cocyDeg (locSys S N M) (degLoc 𝓜 c) locResS 0 := by
    intro c
    have h0 : (Cech.bdryDeg (locSys S N M) (degLoc 𝓜 c) locResS 0).comap
        (Cech.cocyDeg (locSys S N M) (degLoc 𝓜 c) locResS 0).subtype = ⊥ := by
      change Submodule.comap _ ⊥ = ⊥
      rw [Submodule.comap_bot, Submodule.ker_subtype]
    have hf : Module.Finite S (Cech.cocyDeg (locSys S N M) (degLoc 𝓜 c) locResS 0 ⧸
        (Cech.bdryDeg (locSys S N M) (degLoc 𝓜 c) locResS 0).comap
          (Cech.cocyDeg (locSys S N M) (degLoc 𝓜 c) locResS 0).subtype) := hFin S N M 𝓜 hM 0 c
    have hf' : Module.Finite S (Cech.cocyDeg (locSys S N M) (degLoc 𝓜 c) locResS 0) :=
      Module.Finite.equiv (Submodule.quotEquivOfEqBot _ h0)
    obtain ⟨s, hs⟩ := Module.Finite.iff_fg.mp hf'
    exact ⟨s, hs⟩
  choose s hs using hfg
  obtain ⟨c₀, hc₀⟩ := hOnto S N M 𝓜 hM
  set c₂ := max c₀ c₁

  let Φ : M →ₗ[Poly S N] Cech.Cochain (locSys S N M) 0 := LinearMap.pi fun I => locMk M I.1.1
  let T : Finset (Cech.Cochain (locSys S N M) 0) := (Finset.Ico c₁ c₂).biUnion s
  let B : Submodule (Poly S N) (Cech.Cochain (locSys S N M) 0) :=
    LinearMap.range Φ ⊔ Submodule.span (Poly S N) (T : Set _)
  have hB : B.FG := by
    refine Submodule.FG.sup ?_ (Submodule.fg_span T.finite_toSet)
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map Φ

  have hA : H0tail 𝓜 c₁ ≤ B.restrictScalars S := by
    refine iSup₂_le fun c hc => ?_
    intro z hz
    by_cases hc2 : c₂ ≤ c
    · obtain ⟨m, hm⟩ := hc₀ c (le_trans (le_max_left _ _) hc2) (Submodule.Quotient.mk ⟨z, hz⟩)
      have hz' : (constCochain (m : M) : Cech.Cochain (locSys S N M) 0) = z := by
        have := (Submodule.Quotient.eq _).mp hm
        change _ ∈ Submodule.comap _ ⊥ at this
        rw [Submodule.mem_comap, Submodule.mem_bot, map_sub, sub_eq_zero] at this
        exact this
      rw [← hz']
      exact Submodule.mem_sup_left ⟨(m : M), rfl⟩
    · have hcI : c ∈ Finset.Ico c₁ c₂ := Finset.mem_Ico.mpr ⟨hc, lt_of_not_ge hc2⟩
      rw [← hs c] at hz
      refine Submodule.mem_sup_right (Submodule.span_le_restrictScalars S (Poly S N) _ ?_)
      refine Submodule.span_mono ?_ hz
      intro y hy
      exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨c, hcI, hy⟩)
  have hspan : Submodule.span (Poly S N) (H0tail 𝓜 c₁ : Set (Cech.Cochain (locSys S N M) 0)) ≤ B :=
    Submodule.span_le.mpr hA
  have : IsNoetherian (Poly S N) B := isNoetherian_of_fg_of_noetherian B hB
  obtain ⟨t, ht, hteq⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).mp
    (Submodule.FG.of_le_of_isNoetherian hspan)
  refine ⟨t, fun z hz => ht hz, fun z hz => ?_⟩
  change z ∈ Submodule.span (Poly S N) (t : Set _)
  rw [← hteq]
  exact Submodule.subset_span hz

end

end GroundTheory.Heights₂.Heights.Kleiman
