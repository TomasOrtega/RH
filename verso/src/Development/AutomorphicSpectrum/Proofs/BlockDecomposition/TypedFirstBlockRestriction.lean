import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV.SliceL

/- English proof (translation)
Introduce `hK hW`. Establish `hcf : cf (r + s) k t = finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k)`. Rewrite using `[cf, infGL_comm]`. Use `⟨Slice1.levelOne s K t, W.map (LinearMap.funLeft ℂ ℂ fun κ : Kinf E r => Slice1.levK E r s κ * k), Slice1.isOpen_levelOne hK t, inferInstance, ?_⟩` and prove the remaining obligations. Introduce `f hf y`.

Use `⟨fun u hu g => ?_, fun g => ?_⟩` and prove the remaining obligations. Establish `h` using `Slice1.lev_finGL_right g u y t (Unitary.toUnits k)`. Establish `h'` using `hf.1 _ (Slice1.mem_levelOne.1 hu) (lev (Ad E) r s (g, y) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k))`. Rewrite `h'` using `[← h]`. Simplify `h'` using `only [hcf, mul_assoc]`.

Use `⟨_, hf.2 (lev (Ad E) r s (g, y) * finGL E (r + s) t), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `κ`. Establish `h` using `Slice1.lev_infGL_right g (Unitary.toUnits κ) y t (Unitary.toUnits k)`. Establish `e : lev (Cinf E) r s (Unitary.toUnits κ, 1) * Unitary.toUnits k = Unitary.toUnits (Slice1.levK E r s κ * k)`. Rewrite using `[map_mul, Slice1.toUnits_levK]`.

Rewrite `h` using `[e]`. Simplify using `only [LinearMap.funLeft_apply, hcf]`. Rewrite using `[← h]`. Simplify using `only [mul_assoc]`.
-/
theorem slice_typeF {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ} (k : Kinf E (r + s))
    (t : GL (Fin (r + s)) (Af E)) (K : Subgroup (GL (Fin (r + s)) (Af E))) (W : Submodule ℂ (Kinf E (r + s) → ℂ)) :
    IsOpen (K : Set (GL (Fin (r + s)) (Af E))) → FiniteDimensional ℂ W →
    ∃ (K₁ : Subgroup (GL (Fin r) (Af E))) (W₁ : Submodule ℂ (Kinf E r → ℂ)),
      IsOpen (K₁ : Set (GL (Fin r) (Af E))) ∧ FiniteDimensional ℂ W₁ ∧
      ∀ f ∈ typeF K W, ∀ y : GA E s,
        (fun x : GA E r => f (lev (Ad E) r s (x, y) * cf (r + s) k t)) ∈ typeF K₁ W₁ := by
  intro hK hW
  have hcf : cf (r + s) k t = finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k) := by
    rw [cf, infGL_comm]
  refine ⟨Slice1.levelOne s K t,
    W.map (LinearMap.funLeft ℂ ℂ fun κ : Kinf E r => Slice1.levK E r s κ * k),
    Slice1.isOpen_levelOne hK t, inferInstance, ?_⟩
  intro f hf y
  refine ⟨fun u hu g => ?_, fun g => ?_⟩
  · have h := Slice1.lev_finGL_right g u y t (Unitary.toUnits k)
    have h' := hf.1 _ (Slice1.mem_levelOne.1 hu)
      (lev (Ad E) r s (g, y) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k))
    rw [← h] at h'
    simpa only [hcf, mul_assoc] using h'
  · refine ⟨_, hf.2 (lev (Ad E) r s (g, y) * finGL E (r + s) t), ?_⟩
    funext κ
    have h := Slice1.lev_infGL_right g (Unitary.toUnits κ) y t (Unitary.toUnits k)
    have e : lev (Cinf E) r s (Unitary.toUnits κ, 1) * Unitary.toUnits k =
        Unitary.toUnits (Slice1.levK E r s κ * k) := by
      rw [map_mul, Slice1.toUnits_levK]
    rw [e] at h
    simp only [LinearMap.funLeft_apply, hcf]
    rw [← h]
    simp only [mul_assoc]

end GlobalTheory.CompanionTheory.LimV.SliceL

end
