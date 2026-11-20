import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Establish `h1 : ∀ i (z : Z), p z ∈ nonzeroLocus (σ i) ↔ y z ∈ nonzeroLocus (τ i)`. Introduce `i z`. Take `⟨a, a', c, ha, ha', e⟩` from `H z`. Rewrite using `[GlobalTheory.mem_nonzeroLocus_iff_pull (σ i) p z ha, GlobalTheory.mem_nonzeroLocus_iff_pull (τ i) y z ha', e i, IsUnit.mul_iff]`. Conclude with `⟨fun h => h.2, fun h => ⟨c.isUnit, h⟩⟩`.

Establish `hs : ⨆ i, nonzeroLocus (GlobalTheory.secPull (σ i) p) = ⊤`. Use `top_le_iff.1 fun z _ => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 (hτ.ge (Set.mem_univ (y z)))`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨i, (GlobalTheory.nonzeroLocus_secPull (σ i) p).ge ((h1 i z).2 hi)⟩`. Use `⟨h1, hs, GlobalTheory.ProjSpace.toProj_eq_comp_of_locally hτ y hs fun z => ?_⟩` and prove the remaining obligations.

Take `⟨a, a', c, ha, ha', e⟩` from `H z`. Take `⟨W, hW, u, hu⟩` from `Z.presheaf.exists_germ_eq c.val`. Establish `hall : ∀ {U : Z.Opens}, z ∈ U → W ≤ U` using `fun hU x _ => (Subsingleton.elim z x) ▸ hU`. Establish `hl : z ∈ (A.pull p).U fun _ => a` using `Set.mem_iInter.2 fun _ => ha`. Use `⟨W, hW, a', hall ha', fun _ => a, hall hl, u, fun j => fn_ext fun x hx => ?_⟩` and prove the remaining obligations.

Take `rfl : z = x` from `Subsingleton.elim _ _`. Establish `e₁ : gs (𝟙 Z) z W (resG Z (hall hl) ((GlobalTheory.secPull (σ j) p).f fun _ => a)) = gs p z _ ((σ j).f a)` using `(gs_res (𝟙 Z) z (hall hl) hW _).trans ((GlobalTheory.gs_chartSec (GlobalTheory.chartPullPull A p) (σ j) (𝟙 Z) z (fun _ => a) hl).trans (by rw [Category.id_comp]; rfl))`. Establish `e₂ : gs (𝟙 Z) z W u = c.val` using `(gs_eq (𝟙 Z) z W hW u).trans hu`. Establish `e₃ : gs (𝟙 Z) z W ((y.appLE _ W (hall ha')).hom ((τ j).f a')) = gs y z _ ((τ j).f a')` using `(ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_appLE y _ _ _ (𝟙 Z) z hW _).trans (by rw [Category.id_comp])`. Rewrite using `[e₁, gs_mul (𝟙 Z) z W hW, e₂, e₃, e j]`.
-/
theorem toProj_secPull_of_gs {R : Type} [CommRing R] {Y Y' Z : Scheme.{0}} [Subsingleton Z] {A : LB Y} {A' : LB Y'}
    {N : ℕ} (σ : Fin (N + 1) → A.Sec) (τ : Fin (N + 1) → A'.Sec) (s : Y' ⟶ Sp R)
    (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤) (p : Z ⟶ Y) (y : Z ⟶ Y')
    (H : ∀ z : Z, ∃ (a : A.ι) (a' : A'.ι) (c : (Z.presheaf.stalk z)ˣ), p z ∈ A.U a ∧ y z ∈ A'.U a' ∧
      ∀ i, gs p z _ ((σ i).f a) = c.val * gs y z _ ((τ i).f a')) :
    (∀ i (z : Z), p z ∈ nonzeroLocus (σ i) ↔ y z ∈ nonzeroLocus (τ i)) ∧
      ∃ hs, GlobalTheory.ProjSpace.toProj (y ≫ s) (fun i => GlobalTheory.secPull (σ i) p) hs = y ≫ GlobalTheory.ProjSpace.toProj s τ hτ := by
  have h1 : ∀ i (z : Z), p z ∈ nonzeroLocus (σ i) ↔ y z ∈ nonzeroLocus (τ i) := by
    intro i z
    obtain ⟨a, a', c, ha, ha', e⟩ := H z
    rw [GlobalTheory.mem_nonzeroLocus_iff_pull (σ i) p z ha, GlobalTheory.mem_nonzeroLocus_iff_pull (τ i) y z ha', e i,
      IsUnit.mul_iff]
    exact ⟨fun h => h.2, fun h => ⟨c.isUnit, h⟩⟩
  have hs : ⨆ i, nonzeroLocus (GlobalTheory.secPull (σ i) p) = ⊤ := by
    refine top_le_iff.1 fun z _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hτ.ge (Set.mem_univ (y z)))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (GlobalTheory.nonzeroLocus_secPull (σ i) p).ge ((h1 i z).2 hi)⟩
  refine ⟨h1, hs, GlobalTheory.ProjSpace.toProj_eq_comp_of_locally hτ y hs fun z => ?_⟩
  obtain ⟨a, a', c, ha, ha', e⟩ := H z
  obtain ⟨W, hW, u, hu⟩ := Z.presheaf.exists_germ_eq c.val
  have hall : ∀ {U : Z.Opens}, z ∈ U → W ≤ U := fun hU x _ => (Subsingleton.elim z x) ▸ hU
  have hl : z ∈ (A.pull p).U fun _ => a := Set.mem_iInter.2 fun _ => ha
  refine ⟨W, hW, a', hall ha', fun _ => a, hall hl, u, fun j => fn_ext fun x hx => ?_⟩
  obtain rfl : z = x := Subsingleton.elim _ _
  have e₁ : gs (𝟙 Z) z W (resG Z (hall hl) ((GlobalTheory.secPull (σ j) p).f fun _ => a)) = gs p z _ ((σ j).f a) :=
    (gs_res (𝟙 Z) z (hall hl) hW _).trans
      ((GlobalTheory.gs_chartSec (GlobalTheory.chartPullPull A p) (σ j) (𝟙 Z) z (fun _ => a) hl).trans (by rw [Category.id_comp]; rfl))
  have e₂ : gs (𝟙 Z) z W u = c.val := (gs_eq (𝟙 Z) z W hW u).trans hu
  have e₃ : gs (𝟙 Z) z W ((y.appLE _ W (hall ha')).hom ((τ j).f a')) = gs y z _ ((τ j).f a') :=
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_appLE y _ _ _ (𝟙 Z) z hW _).trans (by rw [Category.id_comp])
  rw [e₁, gs_mul (𝟙 Z) z W hW, e₂, e₃, e j]

/- English proof (translation)
Introduce `R Ω _ _ X X' Y Y' L L' h h' k N σ τ s hτ p y hL hL' H`. Use `haveI : Subsingleton (Sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))`. Use `toProj_secPull_of_gs σ τ s hτ p y fun z => ?_` and prove the remaining obligations. Use `choose J hJ using fun χ : Sp Ω ⟶ X => exists_chart hL (χ z)`. Use `choose J' hJ' using fun χ : Sp Ω ⟶ X' => exists_chart hL' (χ z)`.

Take `⟨c, hc⟩` from `H z J J' hJ hJ'`. Conclude with `⟨_, _, c, Good.mem hJ _ p, Good.mem hJ' _ y, hc⟩`.
-/
theorem toProj_secPull_of_sval : ∀ (R Ω : Type) [CommRing R] [Field Ω] (X X' Y Y' : Scheme.{0}) (L : LB X) (L' : LB X') (h : Y ⟶ X) (h' : Y' ⟶ X') (k N : ℕ) (σ : Fin (N + 1) → SecK L h k) (τ : Fin (N + 1) → SecK L' h' k) (s : Y' ⟶ Sp R) (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤) (p : Sp Ω ⟶ Y) (y : Sp Ω ⟶ Y'), L.IsLB → L'.IsLB → (∀ z J J', Good L z J → Good L' z J' → ∃ c : ((Sp Ω).presheaf.stalk z)ˣ, ∀ i, sval (σ i) p z J = c.val * sval (τ i) y z J') → (∀ i (z : Sp Ω), p z ∈ nonzeroLocus (σ i) ↔ y z ∈ nonzeroLocus (τ i)) ∧ ∃ hs, GlobalTheory.ProjSpace.toProj (y ≫ s) (fun i => GlobalTheory.secPull (σ i) p) hs = y ≫ GlobalTheory.ProjSpace.toProj s τ hτ := by
  intro R Ω _ _ X X' Y Y' L L' h h' k N σ τ s hτ p y hL hL' H
  haveI : Subsingleton (Sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  refine toProj_secPull_of_gs σ τ s hτ p y fun z => ?_
  choose J hJ using fun χ : Sp Ω ⟶ X => exists_chart hL (χ z)
  choose J' hJ' using fun χ : Sp Ω ⟶ X' => exists_chart hL' (χ z)
  obtain ⟨c, hc⟩ := H z J J' hJ hJ'
  exact ⟨_, _, c, Good.mem hJ _ p, Good.mem hJ' _ y, hc⟩

end GlobalTheory.Mum
