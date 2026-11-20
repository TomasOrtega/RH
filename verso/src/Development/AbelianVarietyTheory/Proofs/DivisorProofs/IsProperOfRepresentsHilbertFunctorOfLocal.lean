import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapEqKerIff
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue

namespace GlobalTheory.HilbGlue

/- English proof (translation)
Introduce `S Z z r H u hu hloc`. Use `choose W hsW T y π hπ hy hT using hloc`. Use `IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper) W ?_ ?_` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce `s _`.

Conclude with `TopologicalSpace.Opens.mem_iSup.mpr ⟨s, hsW s⟩`. Introduce `s`. Use `set V : H.Opens := u.1 ⁻¹ᵁ W s`. Establish `hx1 : (HPt.map V.ι u).1 = (u.1 ∣_ W s) ≫ (W s).ι`. Express the relevant statement in the definitionally equal form `V.ι ≫ u.1 = _`.

Rewrite using `[morphismRestrict_ι]`. Take `⟨φ, hφ, -⟩` from `hT s V (HPt.map V.ι u) (u.1 ∣_ W s) hx1`. Take `⟨ψ, hψ, -⟩` from `hu (T s) (y s)`. Establish `hψ1 : ψ ≫ u.1 = π s ≫ (W s).ι`. Rewrite using `[← hy s, ← hψ]`.

Both sides reduce to the same expression. Establish `hrange : Set.range ψ ⊆ Set.range V.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨t, rfl⟩`. Express the relevant statement in the definitionally equal form `u.1 (ψ t) ∈ W s`.

Establish `: u.1 (ψ t) = (W s).ι (π s t)`. Rewrite using `[← Scheme.Hom.comp_apply, hψ1, Scheme.Hom.comp_apply]`. Rewrite using `[this]`. Conclude with `((π s) t).2`. Set `ψ' : T s ⟶ V` to `IsOpenImmersion.lift V.ι ψ hrange`.

Establish `hψ' : ψ' ≫ V.ι = ψ` using `IsOpenImmersion.lift_fac _ _ _`. Establish `h1 : ψ' ≫ φ = 𝟙 _`. Take `⟨c, -, hc⟩` from `hT s (T s) (y s) (π s) (hy s)`. Establish `e1 : HPt.map (ψ' ≫ φ) (y s) = y s`. Rewrite using `[HPt.map_comp, hφ, ← HPt.map_comp, hψ', hψ]`.

Establish `e2 : HPt.map (𝟙 (T s)) (y s) = y s` using `HPt.map_id _`. Conclude with `(hc _ e1).trans (hc _ e2).symm`. Establish `h2 : φ ≫ ψ' = 𝟙 _`. Take `⟨c, -, hc⟩` from `hu V (HPt.map V.ι u)`. Establish `e1 : HPt.map ((φ ≫ ψ') ≫ V.ι) u = HPt.map V.ι u`.

Rewrite using `[Category.assoc, hψ', HPt.map_comp, hψ, hφ]`. Establish `e2` using `(hc _ e1).trans (hc _ rfl).symm`. Rewrite using `[← cancel_mono V.ι, e2, Category.id_comp]`. Establish `hiso : IsIso φ` using `⟨⟨ψ', h2, h1⟩⟩`. Establish `hcomp : φ ≫ π s = u.1 ∣_ W s`.

Rewrite using `[← cancel_mono (W s).ι, Category.assoc, ← hy s, ← hx1, ← hφ]`. Both sides reduce to the same expression. Rewrite using `[← hcomp]`. Use `haveI := hπ s`. Use `infer_instance`.
-/
theorem isProper_of_represents_of_local_proper : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (H : Scheme.{0}) (u : GlobalTheory.HilbGlue.HPt z r H), (∀ (T : Scheme.{0}) (x : GlobalTheory.HilbGlue.HPt z r T), ∃! c : T ⟶ H, GlobalTheory.HilbGlue.HPt.map c u = x) → (∀ s : S, ∃ W : S.Opens, s ∈ W ∧ ∃ (T : Scheme.{0}) (y : GlobalTheory.HilbGlue.HPt z r T) (π : T ⟶ W.toScheme), IsProper π ∧ y.1 = π ≫ W.ι ∧ ∀ (Y : Scheme.{0}) (x : GlobalTheory.HilbGlue.HPt z r Y) (b : Y ⟶ W.toScheme), x.1 = b ≫ W.ι → ∃! c : Y ⟶ T, GlobalTheory.HilbGlue.HPt.map c y = x) → IsProper u.1 := by
  intro S Z z r H u hu hloc
  choose W hsW T y π hπ hy hT using hloc
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper) W ?_ ?_
  · rw [eq_top_iff]
    intro s _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨s, hsW s⟩
  intro s
  set V : H.Opens := u.1 ⁻¹ᵁ W s
  have hx1 : (HPt.map V.ι u).1 = (u.1 ∣_ W s) ≫ (W s).ι := by
    change V.ι ≫ u.1 = _
    rw [morphismRestrict_ι]
  obtain ⟨φ, hφ, -⟩ := hT s V (HPt.map V.ι u) (u.1 ∣_ W s) hx1
  obtain ⟨ψ, hψ, -⟩ := hu (T s) (y s)
  have hψ1 : ψ ≫ u.1 = π s ≫ (W s).ι := by
    rw [← hy s, ← hψ]; rfl
  have hrange : Set.range ψ ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    change u.1 (ψ t) ∈ W s
    have : u.1 (ψ t) = (W s).ι (π s t) := by
      rw [← Scheme.Hom.comp_apply, hψ1, Scheme.Hom.comp_apply]
    rw [this]
    exact ((π s) t).2
  let ψ' : T s ⟶ V := IsOpenImmersion.lift V.ι ψ hrange
  have hψ' : ψ' ≫ V.ι = ψ := IsOpenImmersion.lift_fac _ _ _
  have h1 : ψ' ≫ φ = 𝟙 _ := by
    obtain ⟨c, -, hc⟩ := hT s (T s) (y s) (π s) (hy s)
    have e1 : HPt.map (ψ' ≫ φ) (y s) = y s := by
      rw [HPt.map_comp, hφ, ← HPt.map_comp, hψ', hψ]
    have e2 : HPt.map (𝟙 (T s)) (y s) = y s := HPt.map_id _
    exact (hc _ e1).trans (hc _ e2).symm
  have h2 : φ ≫ ψ' = 𝟙 _ := by
    obtain ⟨c, -, hc⟩ := hu V (HPt.map V.ι u)
    have e1 : HPt.map ((φ ≫ ψ') ≫ V.ι) u = HPt.map V.ι u := by
      rw [Category.assoc, hψ', HPt.map_comp, hψ, hφ]
    have e2 := (hc _ e1).trans (hc _ rfl).symm
    rw [← cancel_mono V.ι, e2, Category.id_comp]
  have hiso : IsIso φ := ⟨⟨ψ', h2, h1⟩⟩
  have hcomp : φ ≫ π s = u.1 ∣_ W s := by
    rw [← cancel_mono (W s).ι, Category.assoc, ← hy s, ← hx1, ← hφ]
    rfl
  rw [← hcomp]
  haveI := hπ s
  infer_instance

end GlobalTheory.HilbGlue
