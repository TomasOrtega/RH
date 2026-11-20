import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenLevelFixingThetaFunction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitaryComponentAtPlaceLawsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitaryClosureLocalComponentsOpenStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFactorStableUnitaryGroupsAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPureTensorBaseVectorAndLocalFactorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationPlaceByPlaceOnPureTensorsStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor.PureOm

/- English proof (translation)
Introduce `D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ`. Take `⟨U, U', hU, hU', hfix⟩` from `GlobalTheory.Mem.ThetaLevel.exists_level D ψ hW.std S T om (GlobalTheory.Ker.isWeak_of_datum hW) hW.om_cont f₀ (base_theta hB)`. Establish `hgen` using `GlobalTheory.T.weilRepresentation_placeByPlace_on_pureTensors D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ`. Take `⟨hp0, hploc⟩` from `GlobalTheory.T.isPureTensor_base_vector_and_local_factor D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ`. Establish `hstab` using `GlobalTheory.T.localFactor_stable_unitaryGroupsAtPlace D ψ θ S T χS χT om sS sT ΛS ΛT hW (base_inf hB)`.

Establish `hgat` using `(GlobalTheory.T.adelicUnitaryComponentAtPlace_laws D).1`. Set `Good : GA D S → GA D T → Prop` to `fun g h => ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => om (gAt S p g, gAt T p h) (x p)) (om (g, h) f)`. Establish `om1 : ∀ u : WO S T → ℂ, om (1, 1) u = u` using `fun u => by`. Establish `: om (1, 1) = 1` using `map_one om`. Rewrite using `[this]`.

Both sides reduce to the same expression. Establish `omm : ∀ (g g' : GA D S) (h h' : GA D T) (u : WO S T → ℂ), om (g * g', h * h') u = om (g, h) (om (g', h') u)` using `fun g g' h h' u => by`. Establish `: om (g * g', h * h') = om (g, h) * om (g', h')` using `map_mul om (g, h) (g', h')`. Rewrite using `[this]`. Both sides reduce to the same expression.

Establish `G1 : Good 1 1` using `fun x f hx => by`. Simplify `hx` using `only [gAt_one, om1]`. Establish `Gmul : ∀ g h g' h', Good g h → Good g' h' → Good (g * g') (h * h')` using `fun g h g' h' a b x f hx => by`. Simplify `a _ _ (b x f hx)` using `only [gAt_mul, omm]`. Establish `Gloc : ∀ q g h, gAt S q g = g → gAt T q h = h → Good g h` using `fun q g h hg hh => by`.

Establish `e1 : ∀ p, p ≠ q → gAt S p g = 1` using `fun p hp => by`. Rewrite using `[← hg]`. Conclude with `(hgat S q g).2.2 p hp`. Establish `e2 : ∀ p, p ≠ q → gAt T p h = 1` using `fun p hp => by`. Rewrite using `[← hh]`.

Conclude with `(hgat T q h).2.2 p hp`. Use `hgen g h ?_ ?_` and prove the remaining obligations. Use `(Set.finite_singleton q).subset fun p hp => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hpq`. Conclude with `hp (by rw [e1 p hpq, e2 p hpq, om1])`.

Use `hploc q (fun p => om (gAt S p g⁻¹, gAt T p h⁻¹) f₀) (hstab q f₀ (base_isLocal hB q) _ _) (fun p hp => by simp only [gAt_inv, e1 p hp, e2 p hp, inv_one, om1])` as an intermediate fact. Establish `e : om (gAt S q g⁻¹, gAt T q h⁻¹) f₀ = om (g⁻¹, h⁻¹) f₀` using `by rw [gAt_inv, gAt_inv, hg, hh]`. Simplify using `only [e] at this`. Conclude with `this`. Establish `Gfin : ∀ g h, (g ∈ U ∧ g ∈ GfC S ∧ ∀ p, gAt S p g ∈ U ∧ gAt S p g ∈ GfC S) → (h ∈ U' ∧ h ∈ GfC T ∧ ∀ p, gAt T p h ∈ U' ∧ gAt T p h ∈ GfC T) → Good g h` using `fun g h hg hh => by`.

Use `hgen g h ?_ ?_` and prove the remaining obligations. Use `Set.finite_empty.subset fun p hp => ?_` and prove the remaining obligations. Conclude with `hp (hfix _ (hg.2.2 p).1 (hg.2.2 p).2 _ (hh.2.2 p).1 (hh.2.2 p).2)`. Establish `e : (fun p => om (gAt S p g⁻¹, gAt T p h⁻¹) f₀) = fun _ => f₀` using `funext fun p => by`. Rewrite using `[gAt_inv, gAt_inv]`.

Conclude with `hfix _ (inv_mem (hg.2.2 p).1) (inv_mem (hg.2.2 p).2) _ (inv_mem (hh.2.2 p).1) (inv_mem (hh.2.2 p).2)`. Rewrite using `[e, hfix _ (inv_mem hg.1) (inv_mem hg.2.1) _ (inv_mem hh.1) (inv_mem hh.2.1)]`. Conclude with `hp0`. Establish `GS : ∀ g, Good g 1` using `fun g => by`. Establish `hg : g ∈ Submonoid.closure _` using `(GlobalTheory.T.adelicUnitary_closure_local_components_open D S U hU).2 ▸ Submonoid.mem_top g`.

Proceed by induction on `hg using Submonoid.closure_induction with`. Consider the case `mem g hg`. Break down `hg with ⟨q, hq⟩ | hg` into its components or cases. Conclude with `Gloc q g 1 hq (gAt_one T q)`. Conclude with `Gfin g 1 hg ⟨one_mem _, one_mem _, fun p => by rw [gAt_one]; exact ⟨one_mem _, one_mem _⟩⟩`.

Consider the case `one => exact G1`. Consider the case `mul a b _ _ ha hb => simpa only [mul_one] using Gmul _ _ _ _ ha hb`. Establish `GT : ∀ h, Good 1 h` using `fun h => by`. Establish `hh : h ∈ Submonoid.closure _` using `(GlobalTheory.T.adelicUnitary_closure_local_components_open D T U' hU').2 ▸ Submonoid.mem_top h`. Proceed by induction on `hh using Submonoid.closure_induction with`.

Consider the case `mem h hh`. Break down `hh with ⟨q, hq⟩ | hh` into its components or cases. Conclude with `Gloc q 1 h (gAt_one S q) hq`. Conclude with `Gfin 1 h ⟨one_mem _, one_mem _, fun p => by rw [gAt_one]; exact ⟨one_mem _, one_mem _⟩⟩ hh`. Consider the case `one => exact G1`.

Consider the case `mul a b _ _ ha hb => simpa only [mul_one] using Gmul _ _ _ _ ha hb`. Introduce `x f hx g h`. Use `Gmul _ _ _ _ (GS g) (GT h)` as an intermediate fact. Rewrite `this` using `[mul_one, one_mul]`. Conclude with `this x f hx`.
-/
theorem isPure_om : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → ∀ (g : GA D S) (h : GA D T), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => om (gAt S p g, gAt T p h) (x p)) (om (g, h) f) := by
  intro D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ
  obtain ⟨U, U', hU, hU', hfix⟩ := GlobalTheory.Mem.ThetaLevel.exists_level D ψ hW.std S T om (GlobalTheory.Ker.isWeak_of_datum hW)
    hW.om_cont f₀ (base_theta hB)
  have hgen := GlobalTheory.T.weilRepresentation_placeByPlace_on_pureTensors D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ
  obtain ⟨hp0, hploc⟩ := GlobalTheory.T.isPureTensor_base_vector_and_local_factor D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ
  have hstab := GlobalTheory.T.localFactor_stable_unitaryGroupsAtPlace D ψ θ S T χS χT om sS sT ΛS ΛT hW (base_inf hB)
  have hgat := (GlobalTheory.T.adelicUnitaryComponentAtPlace_laws D).1
  let Good : GA D S → GA D T → Prop := fun g h => ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ),
    IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f →
      IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => om (gAt S p g, gAt T p h) (x p)) (om (g, h) f)
  have om1 : ∀ u : WO S T → ℂ, om (1, 1) u = u := fun u => by
    have : om (1, 1) = 1 := map_one om
    rw [this]; rfl
  have omm : ∀ (g g' : GA D S) (h h' : GA D T) (u : WO S T → ℂ),
      om (g * g', h * h') u = om (g, h) (om (g', h') u) := fun g g' h h' u => by
    have : om (g * g', h * h') = om (g, h) * om (g', h') := map_mul om (g, h) (g', h')
    rw [this]; rfl
  have G1 : Good 1 1 := fun x f hx => by
    simpa only [gAt_one, om1] using hx
  have Gmul : ∀ g h g' h', Good g h → Good g' h' → Good (g * g') (h * h') := fun g h g' h' a b x f hx => by
    simpa only [gAt_mul, omm] using a _ _ (b x f hx)
  have Gloc : ∀ q g h, gAt S q g = g → gAt T q h = h → Good g h := fun q g h hg hh => by
    have e1 : ∀ p, p ≠ q → gAt S p g = 1 := fun p hp => by
      rw [← hg]; exact (hgat S q g).2.2 p hp
    have e2 : ∀ p, p ≠ q → gAt T p h = 1 := fun p hp => by
      rw [← hh]; exact (hgat T q h).2.2 p hp
    refine hgen g h ?_ ?_
    · refine (Set.finite_singleton q).subset fun p hp => ?_
      by_contra hpq
      exact hp (by rw [e1 p hpq, e2 p hpq, om1])
    · have := hploc q (fun p => om (gAt S p g⁻¹, gAt T p h⁻¹) f₀) (hstab q f₀ (base_isLocal hB q) _ _)
        (fun p hp => by simp only [gAt_inv, e1 p hp, e2 p hp, inv_one, om1])
      have e : om (gAt S q g⁻¹, gAt T q h⁻¹) f₀ = om (g⁻¹, h⁻¹) f₀ := by rw [gAt_inv, gAt_inv, hg, hh]
      simp only [e] at this
      exact this
  have Gfin : ∀ g h, (g ∈ U ∧ g ∈ GfC S ∧ ∀ p, gAt S p g ∈ U ∧ gAt S p g ∈ GfC S) →
      (h ∈ U' ∧ h ∈ GfC T ∧ ∀ p, gAt T p h ∈ U' ∧ gAt T p h ∈ GfC T) → Good g h := fun g h hg hh => by
    refine hgen g h ?_ ?_
    · refine Set.finite_empty.subset fun p hp => ?_
      exact hp (hfix _ (hg.2.2 p).1 (hg.2.2 p).2 _ (hh.2.2 p).1 (hh.2.2 p).2)
    · have e : (fun p => om (gAt S p g⁻¹, gAt T p h⁻¹) f₀) = fun _ => f₀ := funext fun p => by
        rw [gAt_inv, gAt_inv]
        exact hfix _ (inv_mem (hg.2.2 p).1) (inv_mem (hg.2.2 p).2) _ (inv_mem (hh.2.2 p).1) (inv_mem (hh.2.2 p).2)
      rw [e, hfix _ (inv_mem hg.1) (inv_mem hg.2.1) _ (inv_mem hh.1) (inv_mem hh.2.1)]
      exact hp0
  have GS : ∀ g, Good g 1 := fun g => by
    have hg : g ∈ Submonoid.closure _ := (GlobalTheory.T.adelicUnitary_closure_local_components_open D S U hU).2 ▸ Submonoid.mem_top g
    induction hg using Submonoid.closure_induction with
    | mem g hg =>
      rcases hg with ⟨q, hq⟩ | hg
      · exact Gloc q g 1 hq (gAt_one T q)
      · exact Gfin g 1 hg ⟨one_mem _, one_mem _, fun p => by rw [gAt_one]; exact ⟨one_mem _, one_mem _⟩⟩
    | one => exact G1
    | mul a b _ _ ha hb => simpa only [mul_one] using Gmul _ _ _ _ ha hb
  have GT : ∀ h, Good 1 h := fun h => by
    have hh : h ∈ Submonoid.closure _ := (GlobalTheory.T.adelicUnitary_closure_local_components_open D T U' hU').2 ▸ Submonoid.mem_top h
    induction hh using Submonoid.closure_induction with
    | mem h hh =>
      rcases hh with ⟨q, hq⟩ | hh
      · exact Gloc q 1 h (gAt_one S q) hq
      · exact Gfin 1 h ⟨one_mem _, one_mem _, fun p => by rw [gAt_one]; exact ⟨one_mem _, one_mem _⟩⟩ hh
    | one => exact G1
    | mul a b _ _ ha hb => simpa only [mul_one] using Gmul _ _ _ _ ha hb
  intro x f hx g h
  have := Gmul _ _ _ _ (GS g) (GT h)
  rw [mul_one, one_mul] at this
  exact this x f hx

end GlobalTheory.PlaceTensor.PureOm
