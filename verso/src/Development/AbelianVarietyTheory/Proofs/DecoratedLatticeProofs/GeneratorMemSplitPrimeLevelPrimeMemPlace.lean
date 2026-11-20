import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointsLieOverDistinctPlaces

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.GenOver

open GlobalTheory.AdForm.PlacesDistinct in

/- English proof (translation)
Assume the negation of the conclusion as `hxv`. Establish `hx0 : x ≠ 0` using `fun h => hxv (h ▸ p.v.asIdeal.zero_mem)`. Establish `hy0 : y ≠ 0`. Introduce `h`. Apply `hx0` to reduce the goal to its premises.

Establish `: algebraMap D.host.F D.host.E (x : D.host.F) = 0` using `by rw [← hxy, h]; rfl`. Rewrite `this` using `[map_eq_zero_iff _ (algebraMap D.host.F D.host.E).injective]`. Conclude with `RingOfIntegers.coe_eq_zero_iff.mp this`. Apply `(hI.2 y hy0).1 hy` to reduce the goal to its premises. Take `⟨ε, hε, hsum⟩` from `p.above`.

Establish `he : p.e = p.e * algebraMap (AF D.host.F) (AE D) ε`. Rewrite using `[← hsum, mul_add, p.split.1, p.split.2.1, add_zero]`. Use `set c : AF D.host.F := algebraMap D.host.F (AF D.host.F) ((x : D.host.F)⁻¹) with hc`. Establish `hinc : incA D ((y : D.host.E)⁻¹) = algebraMap (AF D.host.F) (AE D) c`. Rewrite using `[hxy, ← map_inv₀, hc]`.

Use `show Algebra.TensorProduct.includeRight _ = _`. Conclude with `(Algebra.TensorProduct.includeRight.commutes _).trans (IsScalarTower.algebraMap_apply _ _ _ _)`. Establish `h2 : finPart D (algebraMap (AF D.host.F) (AE D) (ε * c)) ∈ intAE D`. Rewrite using `[Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]`. Establish `hf : finPart D ((ε * c) ⊗ₜ[D.host.F] (1 : D.host.E)) = sndA D.host.F (ε * c) ⊗ₜ[D.host.F] (1 : D.host.E)` using `rfl`.

Rewrite using `[hf]`. Use `AddSubgroup.subset_closure ⟨sndA D.host.F (ε * c), ?_, 1, by simp⟩` and prove the remaining obligations. Introduce `v'`. Take `⟨α, rfl, h1, h0⟩` from `hε`. Establish `hs : sndA D.host.F (pairA D.host.F 0 α * c) = α * algebraMap D.host.F (Af D.host.F) ((x : D.host.F)⁻¹)`.

Rewrite using `[map_mul, hc, AlgHom.commutes]`. Both sides reduce to the same expression. Rewrite using `[hs, map_mul, AlgHom.commutes]`. Distinguish the cases in `hv : v' = p.v`. Substitute `hv` using the available equality.

Rewrite using `[h1, one_mul, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀]`. Establish `hv1 : Valued.v (algebraMap D.host.F (Fv D.host.F p.v) (x : D.host.F)) = 1`. Use `IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := D.host.F) p.v x` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations. Rewrite using `[IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]`.

Conclude with `IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.2 hxv`. Rewrite using `[hv1, inv_one]`. Rewrite using `[h0 v' hv, zero_mul]`. Conclude with `zero_mem _`. Rewrite using `[hinc, he, mul_assoc, ← map_mul, map_mul]`.

Conclude with `FrameLat.mul_mem_intAE (finPart_idem_int hI) h2`.
-/
theorem mem_place_of_mem_prime {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.E)} (hI : Formalism.L2.NTheta.IsIdemAt p.e w)
    (x : 𝓞 D.host.F) (y : 𝓞 D.host.E) (hxy : (y : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F))
    (hy : y ∈ w.asIdeal) : x ∈ p.v.asIdeal := by
  by_contra hxv
  have hx0 : x ≠ 0 := fun h => hxv (h ▸ p.v.asIdeal.zero_mem)
  have hy0 : y ≠ 0 := by
    intro h
    apply hx0
    have : algebraMap D.host.F D.host.E (x : D.host.F) = 0 := by rw [← hxy, h]; rfl
    rw [map_eq_zero_iff _ (algebraMap D.host.F D.host.E).injective] at this
    exact RingOfIntegers.coe_eq_zero_iff.mp this
  apply (hI.2 y hy0).1 hy
  obtain ⟨ε, hε, hsum⟩ := p.above
  have he : p.e = p.e * algebraMap (AF D.host.F) (AE D) ε := by
    rw [← hsum, mul_add, p.split.1, p.split.2.1, add_zero]
  set c : AF D.host.F := algebraMap D.host.F (AF D.host.F) ((x : D.host.F)⁻¹) with hc
  have hinc : incA D ((y : D.host.E)⁻¹) = algebraMap (AF D.host.F) (AE D) c := by
    rw [hxy, ← map_inv₀, hc]
    show Algebra.TensorProduct.includeRight _ = _
    exact (Algebra.TensorProduct.includeRight.commutes _).trans (IsScalarTower.algebraMap_apply _ _ _ _)
  have h2 : finPart D (algebraMap (AF D.host.F) (AE D) (ε * c)) ∈ intAE D := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    have hf : finPart D ((ε * c) ⊗ₜ[D.host.F] (1 : D.host.E)) = sndA D.host.F (ε * c) ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
    rw [hf]
    refine AddSubgroup.subset_closure ⟨sndA D.host.F (ε * c), ?_, 1, by simp⟩
    intro v'
    obtain ⟨α, rfl, h1, h0⟩ := hε
    have hs : sndA D.host.F (pairA D.host.F 0 α * c) = α * algebraMap D.host.F (Af D.host.F) ((x : D.host.F)⁻¹) := by
      rw [map_mul, hc, AlgHom.commutes]; rfl
    rw [hs, map_mul, AlgHom.commutes]
    by_cases hv : v' = p.v
    · subst hv
      rw [h1, one_mul, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀]
      have hv1 : Valued.v (algebraMap D.host.F (Fv D.host.F p.v) (x : D.host.F)) = 1 := by
        have := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := D.host.F) p.v x
        refine this.trans ?_
        rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        exact IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.2 hxv
      rw [hv1, inv_one]
    · rw [h0 v' hv, zero_mul]
      exact zero_mem _
  rw [hinc, he, mul_assoc, ← map_mul, map_mul]
  exact FrameLat.mul_mem_intAE (finPart_idem_int hI) h2

/- English proof (translation)
The claim follows from `mem_place_of_mem_prime p hI (n : 𝓞 D.host.F) (n : 𝓞 D.host.E) (by simp) hn`.
-/
theorem natCast_mem_place {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.E)} (hI : Formalism.L2.NTheta.IsIdemAt p.e w) (n : ℕ)
    (hn : (n : 𝓞 D.host.E) ∈ w.asIdeal) : (n : 𝓞 D.host.F) ∈ p.v.asIdeal :=
  mem_place_of_mem_prime p hI (n : 𝓞 D.host.F) (n : 𝓞 D.host.E) (by simp) hn

end GlobalTheory.AdForm.GenOver

open GlobalTheory.AdForm.GenOver in

/- English proof (translation)
Introduce `B X I _ l Z u k _ _ _ _ p P hI`. Take `⟨-, hPr, -⟩` from `GlobalTheory.Mem.Col2.base_fields_primes_ok B X`. Establish `h1 : X.piT u ∈ P.1.asIdeal` using `(Formalism.L2.Col.mem_divs (hPr.piT_ne_zero u) _).1 P.2`. Establish `hT : ((B.T u : ℕ) : 𝓞 B.fields.E) ∈ P.1.asIdeal`. Establish `: X.piT u * B.fields.conjO (X.piT u) = ((B.T u : ℕ) : 𝓞 B.fields.E)` using `hPr.piT_norm u`.

Rewrite using `[← this]`. Conclude with `Ideal.mul_mem_right _ _ h1`. Conclude with `⟨h1, natCast_mem_place p hI (B.T u) hT⟩`.
-/
theorem GlobalTheory.AdForm.piT_mem_and_T_mem_place : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt (I.rec7 l Z) k) (P : (B.primes X).vT u), Formalism.L2.NTheta.IsIdemAt p.e P.1 → X.piT u ∈ P.1.asIdeal ∧ ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ p.v.asIdeal := by
  intro B X I _ l Z u k _ _ _ _ p P hI
  obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have h1 : X.piT u ∈ P.1.asIdeal := (Formalism.L2.Col.mem_divs (hPr.piT_ne_zero u) _).1 P.2
  have hT : ((B.T u : ℕ) : 𝓞 B.fields.E) ∈ P.1.asIdeal := by
    have : X.piT u * B.fields.conjO (X.piT u) = ((B.T u : ℕ) : 𝓞 B.fields.E) := hPr.piT_norm u
    rw [← this]
    exact Ideal.mul_mem_right _ _ h1
  exact ⟨h1, natCast_mem_place p hI (B.T u) hT⟩
