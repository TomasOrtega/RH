import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolOrb
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CntIso
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OFRepAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OrbitCountSecondStage
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OrbitFiniteOf

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolFin

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal PI.UnitaryGroupMassFormula.CntFormula
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Distinguish the cases in `hne : (EZ (Tn u') F0 Λ Z).Nonempty`. Take `⟨F₁, hF₁⟩` from `hne`. Simplify using `only [EZ, Set.mem_ofPred_eq] at hF₁`. Establish `hG` using `hF₁.1.2.2`. Rewrite `hG` using `[gz_eq, hF₁.2.2.2.2]`.

Take `⟨R, hR1⟩` from `rank_gram D _ _ Z hG`. Establish `hfix` using `fixedOK_of_rows D u F0 what₂ hR hΛ`. Take `⟨Wf, hWf, hW⟩` from `orbit_count_first_stage D (Tn u') F0 Λ hfix Z R hR1`. Take `⟨Af, hAf, hA⟩` from `orbit_count_second_stage D (Tn u') F0 Λ hfix Z R hR1 Wf hWf`. Use `⟨_, finite_level_index D (Tn u') F0 Λ hfix Z R hR1 Wf Af hWf hAf, ?_⟩` and prove the remaining obligations.

Introduce `F' hF'`. Establish `hx` using `good_places_integral D (Tn u') F0 Λ Z F' hF'`. Take `⟨n₁, hn₁, h₁⟩` from `hW _ hx`. Establish `hx₁` using `good_move D (Tn u') F0 Λ Z hx hn₁`. Take `⟨n₂, hn₂, h₂, h₃⟩` from `hA _ hx₁ h₁`.

Use `⟨n₁.trans n₂, (unipotent_integral_isGroup D F0 Λ).2.2 n₁ hn₁ n₂ hn₂, ?_⟩` and prove the remaining obligations. Use `⟨good_move D (Tn u') F0 Λ Z hx₁ hn₂, ?_, h₃⟩` and prove the remaining obligations. Establish `h₄ : pWf D (act D n₂ (act D n₁ (F'.fl.e, F'.fl.z))) ∈ Wf` using `h₂ ▸ h₁`. Conclude with `h₄`. Conclude with `⟨∅, Set.finite_empty, fun F' hF' => (hne ⟨F', hF'⟩).elim⟩`.
-/
theorem reps (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hR : RowsOf u F0 what₂) (Z : MatZ D)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) :
    ∃ K : Set ((Fin D.R.rS → (VS D).V) × (VS D).V), K.Finite ∧
      ∀ F' ∈ EZ (Tn u') F0 Λ Z, ∃ n ∈ N0 F0 Λ, ((fun a => n (F'.fl.e a)), n F'.fl.z) ∈ K := by
  by_cases hne : (EZ (Tn u') F0 Λ Z).Nonempty
  · obtain ⟨F₁, hF₁⟩ := hne
    simp only [EZ, Set.mem_ofPred_eq] at hF₁
    have hG := hF₁.1.2.2
    rw [gz_eq, hF₁.2.2.2.2] at hG
    obtain ⟨R, hR1⟩ := rank_gram D _ _ Z hG
    have hfix := fixedOK_of_rows D u F0 what₂ hR hΛ
    obtain ⟨Wf, hWf, hW⟩ := orbit_count_first_stage D (Tn u') F0 Λ hfix Z R hR1
    obtain ⟨Af, hAf, hA⟩ := orbit_count_second_stage D (Tn u') F0 Λ hfix Z R hR1 Wf hWf
    refine ⟨_, finite_level_index D (Tn u') F0 Λ hfix Z R hR1 Wf Af hWf hAf, ?_⟩
    intro F' hF'
    have hx := good_places_integral D (Tn u') F0 Λ Z F' hF'
    obtain ⟨n₁, hn₁, h₁⟩ := hW _ hx
    have hx₁ := good_move D (Tn u') F0 Λ Z hx hn₁
    obtain ⟨n₂, hn₂, h₂, h₃⟩ := hA _ hx₁ h₁
    refine ⟨n₁.trans n₂, (unipotent_integral_isGroup D F0 Λ).2.2 n₁ hn₁ n₂ hn₂, ?_⟩
    refine ⟨good_move D (Tn u') F0 Λ Z hx₁ hn₂, ?_, h₃⟩
    have h₄ : pWf D (act D n₂ (act D n₁ (F'.fl.e, F'.fl.z))) ∈ Wf := h₂ ▸ h₁
    exact h₄
  · exact ⟨∅, Set.finite_empty, fun F' hF' => (hne ⟨F', hF'⟩).elim⟩

/- English proof (translation)
Take `⟨K, hK, hKrep⟩` from `reps D u u' F0 what₂ hR Z Λ hΛ`. Establish `hgrp` using `unipotent_integral_isGroup D F0 Λ`. Set `g : ((Fin D.R.rS → (VS D).V) × (VS D).V) → Set (LFlag (VS D) D.R.rS (Tn u'))` to `fun k => {F'' | F'' ∈ EZ (Tn u') F0 Λ Z ∧ ∃ n ∈ N0 F0 Λ, ((fun a => n (F''.fl.e a)), n F''.fl.z) = k}`. Establish `hsub : {O | ∃ F' ∈ EZ (Tn u') F0 Λ Z, O = {F'' | F'' ∈ EZ (Tn u') F0 Λ Z ∧ NilradicalFlagMoved F0 Λ F' F''}} ⊆ g '' K`. Introduce and unpack `O ⟨F', hF', rfl⟩`.

Take `⟨n, hn, hk⟩` from `hKrep F' hF'`. Use `⟨_, hk, ?_⟩` and prove the remaining obligations. Use extensionality with `F''`. Simplify using `only [g, Set.mem_ofPred_eq]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hF'', m, hm, hme⟩`. Use `⟨hF'', n.trans m.symm, hgrp.2.2 n hn _ (hgrp.2.1 m hm), fun a => ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `congrFun (congrArg Prod.fst hme) a`. Simplify using `only at h`. Simplify using `[← h]`.

Establish `h` using `congrArg Prod.snd hme`. Simplify using `only at h`. Simplify using `[← h]`. Introduce and unpack `⟨hF'', m, hm, he, hz⟩`. Use `⟨hF'', m.symm.trans n, hgrp.2.2 _ (hgrp.2.1 m hm) n hn, ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `ext a <;> simp [← he, ← hz]`. Simplify using `only [cntE]`. Conclude with `((hK.image g).subset hsub).encard_lt_top.ne`.
-/
theorem fin0 (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hR : RowsOf u F0 what₂) (Z : MatZ D)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) : cntE (Tn u') F0 Λ Z ≠ ⊤ := by
  obtain ⟨K, hK, hKrep⟩ := reps D u u' F0 what₂ hR Z Λ hΛ
  have hgrp := unipotent_integral_isGroup D F0 Λ
  let g : ((Fin D.R.rS → (VS D).V) × (VS D).V) → Set (LFlag (VS D) D.R.rS (Tn u')) :=
    fun k => {F'' | F'' ∈ EZ (Tn u') F0 Λ Z ∧
      ∃ n ∈ N0 F0 Λ, ((fun a => n (F''.fl.e a)), n F''.fl.z) = k}
  have hsub : {O | ∃ F' ∈ EZ (Tn u') F0 Λ Z,
      O = {F'' | F'' ∈ EZ (Tn u') F0 Λ Z ∧ NilradicalFlagMoved F0 Λ F' F''}} ⊆ g '' K := by
    rintro O ⟨F', hF', rfl⟩
    obtain ⟨n, hn, hk⟩ := hKrep F' hF'
    refine ⟨_, hk, ?_⟩
    ext F''
    simp only [g, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hF'', m, hm, hme⟩
      refine ⟨hF'', n.trans m.symm, hgrp.2.2 n hn _ (hgrp.2.1 m hm), fun a => ?_, ?_⟩
      · have h := congrFun (congrArg Prod.fst hme) a
        simp only at h
        simp [← h]
      · have h := congrArg Prod.snd hme
        simp only at h
        simp [← h]
    · rintro ⟨hF'', m, hm, he, hz⟩
      refine ⟨hF'', m.symm.trans n, hgrp.2.2 _ (hgrp.2.1 m hm) n hn, ?_⟩
      ext a <;> simp [← he, ← hz]
  simp only [cntE]
  exact ((hK.image g).subset hsub).encard_lt_top.ne

/- English proof (translation)
Take `⟨F1, he1, hz1⟩` from `Formalism.MainNotions.S.Inh.tie_flagG_nonempty D u`. Establish `hT : Tn u ≠ 0` using `by exact_mod_cast (Formalism.MainNotions.BridgeLemma.tie_Tu_pos D u).ne'`. Take `⟨β, hβ, hβe, hβz⟩` from `Formalism.L2.SG.Pf.WittFlags.flag_witt hT rfl F0 F1`. Establish `hrows` using `Formalism.L2.SG.Pf.WittFlags.RowRepsIso_holds D β hβ F0 what₂ hR`. Establish `hmem : Formalism.HermitianLatticesTheory.gmap β Λ ∈ what₂.image (Formalism.HermitianLatticesTheory.gmap β)` using `Finset.mem_image_of_mem _ hΛ`.

Establish `hRo : RowsOf u (Formalism.L2.SG.Saturated.mapFlag β hβ F0) (what₂.image (Formalism.HermitianLatticesTheory.gmap β))`. Use `⟨?_, ?_, hrows, ⟨_, hmem⟩⟩` and prove the remaining obligations. Rewrite using `[← he1]`. Use function extensionality and compare the values at `a`. Conclude with `hβe a`.

Rewrite using `[← hz1]`. Conclude with `hβz`. Establish `h` using `fin0 D u u' _ _ hRo Z _ hmem`. Rewrite `h` using `[Formalism.L2.SG.Pf.Cnt.counting_iso_inverse D β hβ (Tn u') F0 Λ Z]`. Then use the resulting hypothesis.
-/
theorem finR (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hR : IsRowReps D F0 what₂) (Z : MatZ D)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) : cntE (Tn u') F0 Λ Z ≠ ⊤ := by
  obtain ⟨F1, he1, hz1⟩ := Formalism.MainNotions.S.Inh.tie_flagG_nonempty D u
  have hT : Tn u ≠ 0 := by exact_mod_cast (Formalism.MainNotions.BridgeLemma.tie_Tu_pos D u).ne'
  obtain ⟨β, hβ, hβe, hβz⟩ := Formalism.L2.SG.Pf.WittFlags.flag_witt hT rfl F0 F1
  have hrows := Formalism.L2.SG.Pf.WittFlags.RowRepsIso_holds D β hβ F0 what₂ hR
  have hmem : Formalism.HermitianLatticesTheory.gmap β Λ ∈ what₂.image (Formalism.HermitianLatticesTheory.gmap β) := Finset.mem_image_of_mem _ hΛ
  have hRo : RowsOf u (Formalism.L2.SG.Saturated.mapFlag β hβ F0) (what₂.image (Formalism.HermitianLatticesTheory.gmap β)) := by
    refine ⟨?_, ?_, hrows, ⟨_, hmem⟩⟩
    · rw [← he1]
      funext a
      exact hβe a
    · rw [← hz1]
      exact hβz
  have h := fin0 D u u' _ _ hRo Z _ hmem
  rwa [Formalism.L2.SG.Pf.Cnt.counting_iso_inverse D β hβ (Tn u') F0 Λ Z] at h

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

/- English proof (translation)
Introduce `γ w F' L U hH`. Establish `hfin` using `finR D u u' F0 what₂ hH.2.2.1 (ZhatL (lf D F0) F') γ.lam γ.mem`. Unfold `cntE at hfin`. Use `(Set.encard_ne_top_iff.mp hfin).subset ?_` and prove the remaining obligations. Introduce and unpack `O ⟨F'', hF'', _, rfl⟩`.

Conclude with `⟨F'', hF'', rfl⟩`.
-/
theorem orbitFinite_holds : Formalism.L2.SG.Pf.ZsVolOrb.OrbFinE M δ u u' F0 what₂ := by
  intro γ w F' L U hH
  have hfin := finR D u u' F0 what₂ hH.2.2.1 (ZhatL (lf D F0) F') γ.lam γ.mem
  unfold cntE at hfin
  refine (Set.encard_ne_top_iff.mp hfin).subset ?_
  rintro O ⟨F'', hF'', _, rfl⟩
  exact ⟨F'', hF'', rfl⟩

end Formalism.L2.SG.Pf.ZsVolFin

end
