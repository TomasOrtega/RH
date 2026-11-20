import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLineAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeIffLocalComponentSatake
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGLLocalComponentsEventuallySatake
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.FormsFiniteGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MuCharacterExists

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

/- English proof (translation)
Introduce `hPl hLF hRF E _ _ _ n hn π hns μ e hμ`. Take `⟨⟨S, hS⟩, hc, hInf, hSec⟩` from `hPl E`. Establish `hF` using `UpperTheory.V.Af.formsFiniteGL`. Establish `hbad : {w : Pl E | ¬ ((∃ B, (CG.mk π).HasSat w B) ∧ μ.UnrAt w)}.Finite` using `Filter.eventually_cofinite.1 ((GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep hF E n π).and (GlobalTheory.Mem.UnrAe.unr_ae_and_level E μ).1)`. Take `⟨Bd, hBd⟩ : ∃ Bd : Finset (Pl E), ∀ w, w ∈ Bd ↔ ¬ ((∃ B, (CG.mk π).HasSat w B) ∧ μ.UnrAt w)` from `⟨hbad.toFinset, fun w => by simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]⟩`.

Establish `hgood : ∀ w, w ∉ Bd → (∃ B, (CG.mk π).HasSat w B) ∧ μ.UnrAt w` using `fun w hw => by`. Assume the negation of the conclusion as `h`. Conclude with `hw ((hBd w).2 h)`. Establish `hsplit : ∀ w ∈ Bd, IsSplitAt w` using `fun w hw => by`. Assume the negation of the conclusion as `hs`.

Conclude with `(hBd w).1 hw ⟨hns w hs, fun x hx => by`. Rewrite using `[hμ.2.2.1 w hs]`. Conclude with `GlobalTheory.CompanionTheory.MuOpen.unrChar_apply_of_isUnitAt w _ x hx⟩`. Establish `hcs : ∀ w, IsSplitAt w → IsSplitAt (cPl w)` using `fun w hw => (hc (cPl w)).2.2 (by rw [(hc w).1]; exact ((hc w).2.1 hw).symm)`. Take `⟨m, hm⟩ : ∃ m : Pl E → Pl E, ∀ w, m w ∈ S ∧ (m w = w ∨ m w = cPl w)` from `⟨fun w => if w ∈ S then w else cPl w, fun w => by`.

Distinguish the cases in `h : w ∈ S`. Simplify using `[h]`. Simplify `((hSec S hS w).1.resolve_left h)⟩` using `[h]`. Establish `hms : ∀ w, IsSplitAt w → IsSplitAt (m w)` using `fun w hw => by`. Break down `(hm w).2 with e | e` into its components or cases.

Rewrite using `[e]` and apply the resulting hypothesis. Rewrite using `[e]`. Conclude with `hcs w hw`. Take `⟨w₀, hw₀, hw₀'⟩` from `(hInf.diff (Bd ∪ Bd.image cPl).finite_toSet).nonempty`. Establish `hn₀ : w₀ ∉ Bd` using `fun h => hw₀' (by simp [h])`.

Establish `hn₁ : cPl w₀ ∉ Bd` using `fun h => hw₀' (by`. Use `Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_image.2 ⟨_, h, (hc w₀).1⟩)))` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨w₁, hw₁, hw₁S, hw₁s⟩ : ∃ w₁, w₁ ∉ Bd ∧ w₁ ∈ S ∧ IsSplitAt w₁ := by`. Use `⟨m w₀, ?_, (hm w₀).1, hms w₀ hw₀⟩` and prove the remaining obligations. Apply the tactic sequence `rcases (hm w₀).2 with e | e <;> rwa [e]`.

Use `choose! B hB using fun w (h : ∃ B, (CG.mk π).HasSat w B) => h`. Use `choose τ hτ using fun w => GlobalTheory.CuspRep.LocEx.exists_isLocComp hF E n π w`. Establish `hf : ∀ w : Pl E, ∃ g : GLw n w → ℂ, Lc (KGL w n) g ∧ trc (τ w).ρ (KGL w n) g ≠ 0 ∧ (w = w₁ → ∀ y, g y ≠ 0 → y.val.charpoly.Separable)` using `fun w => by`. Distinguish the cases in `h : w = w₁`. Substitute `h` using the available equality.

Take `⟨b, hb⟩` from `(hgood w hw₁).1`. Take `⟨g, h1, h2, h3⟩` from `hRF E n w (τ w) b (((GlobalTheory.Cong.satake_locComp E n π w (τ w) (hτ w).1).1 b).1 hb)`. Conclude with `⟨g, h1, h2, fun _ => h3⟩`. Take `⟨g, h1, h2⟩` from `hLF E n w (τ w)`. Conclude with `⟨g, h1, h2, fun e => absurd e h⟩`.

Use `choose f hf1 hf2 hf3 using hf`. Use `⟨S, insert w₁ (Bd.image m), B, τ, f, hS, fun w hw => ?_, fun w hw => ?_, fun w _ => ⟨(hτ w).1, hf1 w, hf2 w⟩, w₁, Finset.mem_insert_self _ _, hf3 w₁ rfl⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hw with rfl | h` into its components or cases. Conclude with `⟨hw₁S, hw₁s⟩`. Take `⟨u, hu, rfl⟩` from `Finset.mem_image.1 h`.

Conclude with `⟨(hm u).1, hms u (hsplit u hu)⟩`. Establish `hw' : w ∉ Bd` using `fun h => by`. Establish `hi : m w ∈ insert w₁ (Bd.image m)` using `Finset.mem_insert_of_mem (Finset.mem_image_of_mem m h)`. Break down `(hm w).2 with e | e` into its components or cases. Conclude with `hw.1 (e ▸ hi)`.

Conclude with `hw.2 (e ▸ hi)`. Conclude with `⟨hB w (hgood w hw').1, (hgood w hw').2⟩`.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.rChoice :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.RChoice := by
  classical
  intro hPl hLF hRF E _ _ _ n hn π hns μ e hμ
  obtain ⟨⟨S, hS⟩, hc, hInf, hSec⟩ := hPl E
  have hF := UpperTheory.V.Af.formsFiniteGL
  have hbad : {w : Pl E | ¬ ((∃ B, (CG.mk π).HasSat w B) ∧ μ.UnrAt w)}.Finite :=
    Filter.eventually_cofinite.1 ((GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep hF E n π).and
      (GlobalTheory.Mem.UnrAe.unr_ae_and_level E μ).1)
  obtain ⟨Bd, hBd⟩ : ∃ Bd : Finset (Pl E), ∀ w, w ∈ Bd ↔ ¬ ((∃ B, (CG.mk π).HasSat w B) ∧ μ.UnrAt w) :=
    ⟨hbad.toFinset, fun w => by simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]⟩
  have hgood : ∀ w, w ∉ Bd → (∃ B, (CG.mk π).HasSat w B) ∧ μ.UnrAt w := fun w hw => by
    by_contra h
    exact hw ((hBd w).2 h)
  have hsplit : ∀ w ∈ Bd, IsSplitAt w := fun w hw => by
    by_contra hs
    exact (hBd w).1 hw ⟨hns w hs, fun x hx => by
      rw [hμ.2.2.1 w hs]
      exact GlobalTheory.CompanionTheory.MuOpen.unrChar_apply_of_isUnitAt w _ x hx⟩
  have hcs : ∀ w, IsSplitAt w → IsSplitAt (cPl w) := fun w hw =>
    (hc (cPl w)).2.2 (by rw [(hc w).1]; exact ((hc w).2.1 hw).symm)
  obtain ⟨m, hm⟩ : ∃ m : Pl E → Pl E, ∀ w, m w ∈ S ∧ (m w = w ∨ m w = cPl w) :=
    ⟨fun w => if w ∈ S then w else cPl w, fun w => by
      by_cases h : w ∈ S
      · simp [h]
      · simpa [h] using ((hSec S hS w).1.resolve_left h)⟩
  have hms : ∀ w, IsSplitAt w → IsSplitAt (m w) := fun w hw => by
    rcases (hm w).2 with e | e
    · rwa [e]
    · rw [e]; exact hcs w hw
  obtain ⟨w₀, hw₀, hw₀'⟩ := (hInf.diff (Bd ∪ Bd.image cPl).finite_toSet).nonempty
  have hn₀ : w₀ ∉ Bd := fun h => hw₀' (by simp [h])
  have hn₁ : cPl w₀ ∉ Bd := fun h => hw₀' (by
    refine Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_image.2 ⟨_, h, (hc w₀).1⟩)))
  obtain ⟨w₁, hw₁, hw₁S, hw₁s⟩ : ∃ w₁, w₁ ∉ Bd ∧ w₁ ∈ S ∧ IsSplitAt w₁ := by
    refine ⟨m w₀, ?_, (hm w₀).1, hms w₀ hw₀⟩
    rcases (hm w₀).2 with e | e <;> rwa [e]
  choose! B hB using fun w (h : ∃ B, (CG.mk π).HasSat w B) => h
  choose τ hτ using fun w => GlobalTheory.CuspRep.LocEx.exists_isLocComp hF E n π w
  have hf : ∀ w : Pl E, ∃ g : GLw n w → ℂ, Lc (KGL w n) g ∧ trc (τ w).ρ (KGL w n) g ≠ 0 ∧
      (w = w₁ → ∀ y, g y ≠ 0 → y.val.charpoly.Separable) := fun w => by
    by_cases h : w = w₁
    · subst h
      obtain ⟨b, hb⟩ := (hgood w hw₁).1
      obtain ⟨g, h1, h2, h3⟩ := hRF E n w (τ w) b
        (((GlobalTheory.Cong.satake_locComp E n π w (τ w) (hτ w).1).1 b).1 hb)
      exact ⟨g, h1, h2, fun _ => h3⟩
    · obtain ⟨g, h1, h2⟩ := hLF E n w (τ w)
      exact ⟨g, h1, h2, fun e => absurd e h⟩
  choose f hf1 hf2 hf3 using hf
  refine ⟨S, insert w₁ (Bd.image m), B, τ, f, hS, fun w hw => ?_, fun w hw => ?_,
    fun w _ => ⟨(hτ w).1, hf1 w, hf2 w⟩, w₁, Finset.mem_insert_self _ _, hf3 w₁ rfl⟩
  · rcases Finset.mem_insert.1 hw with rfl | h
    · exact ⟨hw₁S, hw₁s⟩
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 h
      exact ⟨(hm u).1, hms u (hsplit u hu)⟩
  · have hw' : w ∉ Bd := fun h => by
      have hi : m w ∈ insert w₁ (Bd.image m) := Finset.mem_insert_of_mem (Finset.mem_image_of_mem m h)
      rcases (hm w).2 with e | e
      · exact hw.1 (e ▸ hi)
      · exact hw.2 (e ▸ hi)
    exact ⟨hB w (hgood w hw').1, (hgood w hw').2⟩
