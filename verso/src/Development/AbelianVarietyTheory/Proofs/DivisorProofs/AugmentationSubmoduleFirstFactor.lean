import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatRankDeficientReductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanCharacterTranslatesCoinvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalCharactersLinearBarStatement

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IrrCoinvV

/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv hnr N hAN hNS hstab`. Take `⟨ν₀, β₀, ι, ⟨t, ht⟩, s1, u1, s2, u2, hbij, hg1, hg2, hh⟩` from `GlobalTheory.T.exists_local_characters_linear_bar hP F E σ B a a' G X om om' hT v hv`. Establish `hϖ : GlobalTheory.SplitFlip.IsUnif (unifAt v)` using `(GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec`. Establish `hν : ν₀ (unifAt v) ≠ 1`. Establish `h1` using `hnr t 1 one_ne_zero`.

Rewrite `h1` using `[zpow_one]`. Break down `ht with rfl | rfl` into its components or cases. Conclude with `h1`. Introduce `h`. Apply `h1` to reduce the goal to its premises.

Simplify using `using congrArg (·⁻¹) h`. Use `set augL : Submodule ℂ (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ) := Submodule.span ℂ {z | ∃ (g : GL (Fin a) (Fv F v)) (Ψ : Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ), Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) ∧ z = GlobalTheory.SplitFlip.omA ν₀ β₀ g 1 …`. Establish `augS : augAt om v ≤ SB _` using `Submodule.span_le.mpr fun _ ⟨_, _, _, hφ, _, hφ₁, _, e⟩ => e ▸ sub_mem hφ₁ hφ`. Establish `c1 : augAt om v ≤ augL.comap ι`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩`. Take `⟨g', hg'⟩` from `hg1 g hg`. Use `show ι (φ₁ - φ) ∈ augL`. Rewrite using `[map_sub, hg' φ hφ φ₁ hφ₁ hA]`. Conclude with `Submodule.subset_span ⟨g', ι φ, hbij.mapsTo hφ, rfl⟩`.

Establish `c2 : augL ≤ (augAt om v).map ι`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g', Ψ, hΨ, rfl⟩`. Take `⟨φ, hφ, rfl⟩` from `hbij.surjOn hΨ`. Take `⟨g, hg, hgg⟩` from `hg2 g'`.

Take `⟨φ₁, hφ₁, hA, he⟩` from `hgg φ hφ`. Use `⟨φ₁ - φ, Submodule.subset_span ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, he]`. Establish `c3 : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ι φ ∈ augL → φ ∈ augAt om v`. Introduce `φ hφ h`.

Take `⟨ψ, hψ, he⟩` from `c2 h`. Rewrite using `[← hbij.injOn (augS hψ) hφ he]` and apply the resulting hypothesis. Use `set N' := N.map ι with hN'`. Establish `n1 : augL ≤ N'` using `c2.trans (Submodule.map_mono hAN)`. Establish `n2 : N' ≤ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) (Fv F v))`.

Introduce and unpack `_ ⟨φ, hφ, rfl⟩`. Conclude with `hbij.mapsTo (hNS hφ)`. Establish `n3 : ∀ (h' : GL (Fin (a + a')) (Fv F v)), ∀ Ψ ∈ N', GlobalTheory.SplitFlip.omA ν₀ β₀ 1 h' Ψ ∈ N'`. Introduce and unpack `h' _ ⟨φ, hφ, rfl⟩`. Take `⟨h, hhW, hk⟩` from `hh h'`.

Take `⟨φ₁, hφ₁, hA, he⟩` from `hk φ (hNS hφ)`. Conclude with `⟨φ₁, hstab h hhW φ hφ φ₁ hφ₁ hA, he⟩`. Establish `hle : a ≤ a + a'` using `Nat.le_add_right a a'`. Break down `GlobalTheory.T.span_character_translates_coinvariant hP.bernsteinUnitaryProductIrreducible (Fv F v) a (a + a') hle ν₀ β₀ s1 u1 s2 u2 N' n1 n2 n3 with hA | hB` into its components or cases. Use `left`.

Use `le_antisymm (fun φ hφ => ?_) hAN` and prove the remaining obligations. Establish `hφS` using `hNS hφ`. Take `⟨Ψ₀, hΨ₀, hr, hd⟩` from `GlobalTheory.T.schwartzBruhat_rank_deficient_reduction (Fv F v) a (a + a') hle ν₀ β₀ s1 u1 (unifAt v) hϖ hν (ι φ) (hbij.mapsTo hφS)`. Establish `h0 : Ψ₀ ∈ N'`. Use `N'.sub_mem (Submodule.mem_map_of_mem hφ) (n1 hd)` as an intermediate fact.

Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Establish `h1` using `hA Ψ₀ h0 hr`. Use `c3 φ hφS ?_` and prove the remaining obligations. Use `augL.add_mem hd h1` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis.

Use `right`. Use `le_antisymm hNS (fun φ hφS => ?_)` and prove the remaining obligations. Take `⟨Ψ₀, hΨ₀, hr, hd⟩` from `GlobalTheory.T.schwartzBruhat_rank_deficient_reduction (Fv F v) a (a + a') hle ν₀ β₀ s1 u1 (unifAt v) hϖ hν (ι φ) (hbij.mapsTo hφS)`. Establish `h0 : ι φ ∈ N'`. Use `N'.add_mem (n1 hd) (hB Ψ₀ hΨ₀ hr)` as an intermediate fact.

Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Take `⟨n, hn, he⟩` from `h0`. Rewrite using `[← hbij.injOn (hNS hn) hφS he]` and apply the resulting hypothesis.
-/
theorem irrV : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) →
    ∀ N : Submodule ℂ ((Fin a × Fin (a + a') → Fv F v) → ℂ), augAt om v ≤ N → N ≤ SB _ →
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ N, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h)) φ φ₁ → φ₁ ∈ N) →
      N = augAt om v ∨ N = SB _ := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv hnr N hAN hNS hstab
  obtain ⟨ν₀, β₀, ι, ⟨t, ht⟩, s1, u1, s2, u2, hbij, hg1, hg2, hh⟩ := GlobalTheory.T.exists_local_characters_linear_bar hP F E σ B a a' G X om om' hT v hv
  have hϖ : GlobalTheory.SplitFlip.IsUnif (unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  have hν : ν₀ (unifAt v) ≠ 1 := by
    have h1 := hnr t 1 one_ne_zero
    rw [zpow_one] at h1
    rcases ht with rfl | rfl
    · exact h1
    · intro h; apply h1; simpa using congrArg (·⁻¹) h
  set augL : Submodule ℂ (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ) := Submodule.span ℂ
    {z | ∃ (g : GL (Fin a) (Fv F v)) (Ψ : Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ),
      Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) ∧ z = GlobalTheory.SplitFlip.omA ν₀ β₀ g 1 Ψ - Ψ} with haugL
  have augS : augAt om v ≤ SB _ :=
    Submodule.span_le.mpr fun _ ⟨_, _, _, hφ, _, hφ₁, _, e⟩ => e ▸ sub_mem hφ₁ hφ
  have c1 : augAt om v ≤ augL.comap ι := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩
    obtain ⟨g', hg'⟩ := hg1 g hg
    show ι (φ₁ - φ) ∈ augL
    rw [map_sub, hg' φ hφ φ₁ hφ₁ hA]
    exact Submodule.subset_span ⟨g', ι φ, hbij.mapsTo hφ, rfl⟩
  have c2 : augL ≤ (augAt om v).map ι := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨g', Ψ, hΨ, rfl⟩
    obtain ⟨φ, hφ, rfl⟩ := hbij.surjOn hΨ
    obtain ⟨g, hg, hgg⟩ := hg2 g'
    obtain ⟨φ₁, hφ₁, hA, he⟩ := hgg φ hφ
    refine ⟨φ₁ - φ, Submodule.subset_span ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩, ?_⟩
    rw [map_sub, he]
  have c3 : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ι φ ∈ augL → φ ∈ augAt om v := by
    intro φ hφ h
    obtain ⟨ψ, hψ, he⟩ := c2 h
    rwa [← hbij.injOn (augS hψ) hφ he]
  set N' := N.map ι with hN'
  have n1 : augL ≤ N' := c2.trans (Submodule.map_mono hAN)
  have n2 : N' ≤ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) := by
    rintro _ ⟨φ, hφ, rfl⟩; exact hbij.mapsTo (hNS hφ)
  have n3 : ∀ (h' : GL (Fin (a + a')) (Fv F v)), ∀ Ψ ∈ N', GlobalTheory.SplitFlip.omA ν₀ β₀ 1 h' Ψ ∈ N' := by
    rintro h' _ ⟨φ, hφ, rfl⟩
    obtain ⟨h, hhW, hk⟩ := hh h'
    obtain ⟨φ₁, hφ₁, hA, he⟩ := hk φ (hNS hφ)
    exact ⟨φ₁, hstab h hhW φ hφ φ₁ hφ₁ hA, he⟩
  have hle : a ≤ a + a' := Nat.le_add_right a a'
  rcases GlobalTheory.T.span_character_translates_coinvariant hP.bernsteinUnitaryProductIrreducible (Fv F v) a (a + a') hle ν₀ β₀ s1 u1 s2 u2 N' n1 n2 n3 with hA | hB
  · left
    refine le_antisymm (fun φ hφ => ?_) hAN
    have hφS := hNS hφ
    obtain ⟨Ψ₀, hΨ₀, hr, hd⟩ := GlobalTheory.T.schwartzBruhat_rank_deficient_reduction (Fv F v) a (a + a') hle ν₀ β₀ s1 u1 (unifAt v) hϖ hν (ι φ) (hbij.mapsTo hφS)
    have h0 : Ψ₀ ∈ N' := by
      have := N'.sub_mem (Submodule.mem_map_of_mem hφ) (n1 hd)
      rwa [sub_sub_cancel] at this
    have h1 := hA Ψ₀ h0 hr
    refine c3 φ hφS ?_
    have := augL.add_mem hd h1
    rwa [sub_add_cancel] at this
  · right
    refine le_antisymm hNS (fun φ hφS => ?_)
    obtain ⟨Ψ₀, hΨ₀, hr, hd⟩ := GlobalTheory.T.schwartzBruhat_rank_deficient_reduction (Fv F v) a (a + a') hle ν₀ β₀ s1 u1 (unifAt v) hϖ hν (ι φ) (hbij.mapsTo hφS)
    have h0 : ι φ ∈ N' := by
      have := N'.add_mem (n1 hd) (hB Ψ₀ hΨ₀ hr)
      rwa [sub_add_cancel] at this
    obtain ⟨n, hn, he⟩ := h0
    rwa [← hbij.injOn (hNS hn) hφS he]

end GlobalTheory.IrrCoinvV
