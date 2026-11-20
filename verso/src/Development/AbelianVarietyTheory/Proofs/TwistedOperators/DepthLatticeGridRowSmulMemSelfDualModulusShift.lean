import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsValuationOneElementAtGridPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
namespace GlobalTheory.DepHalf

open scoped Pointwise

/- English proof (translation)
Introduce `D T L sc μ₀ hL hQ G i hi e he u hu`. Establish `h1 : e • u ∈ hatMx (G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0)))` using `hu.2 e he`. Establish `hmB : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0`. Use `FractionalIdeal.coeIdeal_ne_zero.2 ?_` and prove the remaining obligations. Unfold `Places.modulBar`.

Introduce `h`. Apply `G.pl.modul_ne_bot sc` to reduce the goal to its premises. Use `congrArg (fun J : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • J) h` as an intermediate fact. Simplify `this` using `[smul_smul]`. Establish `hone : (1 : D.host.E) ∈ ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹`.

Establish `hle : (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤ ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹`. Use `FractionalIdeal.inv_anti_mono hmB one_ne_zero FractionalIdeal.coeIdeal_le_one` as an intermediate fact. Rewrite `this` using `[inv_one]`. Then use the resulting hypothesis. Conclude with `hle (FractionalIdeal.one_mem_one _)`. Establish `hsub : G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0)) ≤ homLat (G.Λ (.grid (i + 1) 0)) (idLat (shiftId G) (G.Λ (.grid i 0)))`.

Use `Submodule.smul_le.2 fun r hr x hx y hy => ?_` and prove the remaining obligations. Rewrite using `[smul_mulVec]`. Use `Submodule.subset_span ⟨algebraMap (𝓞 D.host.E) D.host.E r, ?_, x *ᵥ y, hx y hy, ?_⟩` and prove the remaining obligations. Unfold `shiftId`. Rewrite using `[show algebraMap (𝓞 D.host.E) D.host.E r = algebraMap (𝓞 D.host.E) D.host.E r * 1 by rw [mul_one]]`.

Conclude with `FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hr) hone`. Conclude with `(algebraMap_smul D.host.E r (x *ᵥ y)).symm`. Establish `h2 : e • u ∈ hatMx (homLat (G.Λ (.grid (i + 1) 0)) (idLat (shiftId G) (G.Λ (.grid i 0))))`. Use `AddSubgroup.closure_mono ?_ h1` and prove the remaining obligations. Introduce and unpack `w ⟨α, hα, x, hx, rfl⟩`.

Conclude with `⟨α, hα, x, hsub hx, rfl⟩`. Establish `hhalf : IsHalf e (e • u)` using `fun a b => by`. Rewrite using `[Matrix.smul_apply, smul_eq_mul, ← mul_assoc, GlobalTheory.PlaceDatum.idemSum_mul_self he]`. Establish `h0 : ∀ j, (Node.grid (i + 1) 0 : Node) ≠ .grid 0 j` using `fun j h => by injection h with h'`. Use linear arithmetic over natural numbers and integers.

Establish `hsd : IsSelfDualC (G.V (.grid (i + 1) 0)) (G.Λ (.grid (i + 1) 0))` using `(G.isV (show (Node.grid (i + 1) 0 : Node).InRange D.R.m from ⟨hi, Nat.zero_le _⟩) h0).sd`. Conclude with `GlobalTheory.RowLatChi.mem_latO_of_mem_hatMx hsd he (GlobalTheory.AAUnit.exists_valuation_one_element_at_grid_places hQ hL G) hhalf h2`.
-/
theorem smul_mem_latBig : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → OffQ D →
    ∀ (G : GridData L sc) (i : ℕ), i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ u ∈ latRow G i, e • u ∈ latBig G i := by
  intro D T L sc μ₀ hL hQ G i hi e he u hu
  have h1 : e • u ∈ hatMx (G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) := hu.2 e he
  have hmB : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    refine FractionalIdeal.coeIdeal_ne_zero.2 ?_
    unfold Places.modulBar
    intro h
    apply G.pl.modul_ne_bot sc
    have := congrArg (fun J : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • J) h
    simpa [smul_smul] using this
  have hone : (1 : D.host.E) ∈ ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹ := by
    have hle : (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤
        ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹ := by
      have := FractionalIdeal.inv_anti_mono hmB one_ne_zero FractionalIdeal.coeIdeal_le_one
      rwa [inv_one] at this
    exact hle (FractionalIdeal.one_mem_one _)
  have hsub : G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0)) ≤
      homLat (G.Λ (.grid (i + 1) 0)) (idLat (shiftId G) (G.Λ (.grid i 0))) := by
    refine Submodule.smul_le.2 fun r hr x hx y hy => ?_
    rw [smul_mulVec]
    refine Submodule.subset_span ⟨algebraMap (𝓞 D.host.E) D.host.E r, ?_, x *ᵥ y, hx y hy, ?_⟩
    · unfold shiftId
      rw [show algebraMap (𝓞 D.host.E) D.host.E r = algebraMap (𝓞 D.host.E) D.host.E r * 1 by rw [mul_one]]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hr) hone
    · exact (algebraMap_smul D.host.E r (x *ᵥ y)).symm
  have h2 : e • u ∈ hatMx (homLat (G.Λ (.grid (i + 1) 0)) (idLat (shiftId G) (G.Λ (.grid i 0)))) := by
    refine AddSubgroup.closure_mono ?_ h1
    rintro w ⟨α, hα, x, hx, rfl⟩
    exact ⟨α, hα, x, hsub hx, rfl⟩
  have hhalf : IsHalf e (e • u) := fun a b => by
    rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, GlobalTheory.PlaceDatum.idemSum_mul_self he]
  have h0 : ∀ j, (Node.grid (i + 1) 0 : Node) ≠ .grid 0 j := fun j h => by
    injection h with h'
    omega
  have hsd : IsSelfDualC (G.V (.grid (i + 1) 0)) (G.Λ (.grid (i + 1) 0)) := (G.isV (show (Node.grid (i + 1) 0 : Node).InRange D.R.m from ⟨hi, Nat.zero_le _⟩) h0).sd
  exact GlobalTheory.RowLatChi.mem_latO_of_mem_hatMx hsd he (GlobalTheory.AAUnit.exists_valuation_one_element_at_grid_places hQ hL G) hhalf h2

end GlobalTheory.DepHalf
