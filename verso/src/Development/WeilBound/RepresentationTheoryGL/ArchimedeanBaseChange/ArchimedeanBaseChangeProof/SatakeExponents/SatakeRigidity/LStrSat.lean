import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.ThetaOfCsdR
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.AscSeedHolds2
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatAsc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehDataUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Rig

/- English proof (translation)
Introduce `i j h` and use `by have h' : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by unfold spehExp at h linarith exact Fin.ext (by exact_mod_cast h')`.
-/
theorem spehExp_injective (d : ℕ) : Function.Injective (spehExp d) := fun i j h => by
  have h' : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by
    unfold spehExp at h
    linarith
  exact Fin.ext (by exact_mod_cast h')

/- English proof (translation)
Introduce `E _ _ _ N a d V P σ hN hV hPu hPn hA hloc ν hν`. Establish `hd : 1 ≤ d`. Take `⟨hsum, -⟩` from `hA`. Break down `Nat.eq_zero_or_pos d with rfl | h` into its components or cases. Simplify using `at hsum`.

Use linear arithmetic over natural numbers and integers. Conclude with `h`. Establish `hex : ∀ s : ℝ, ∃ χ : Formalism.L2.Host.HChar E, χ.IsAbsPow s` using `fun s => ⟨_, GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s⟩`. Use `choose χ0 hχ0 using hex`. Set `μ : ℝ → Formalism.L2.Host.HChar E` to `fun s => if h : ∃ k, spehExp d k = s then ν h.choose else χ0 s`.

Establish `hμ : ∀ s, (μ s).IsAbsPow s` using `fun s => by`. Distinguish the cases in `h : ∃ k, spehExp d k = s`. Simplify using `only [μ, dif_pos h]`. Use `hν h.choose` as an intermediate fact. Rewrite `this` using `[h.choose_spec]`. Then use the resulting hypothesis.

Simplify using `only [μ, dif_neg h]`. Conclude with `hχ0 s`. Establish `hμk : ∀ k, μ (spehExp d k) = ν k` using `fun k => by`. Establish `h : ∃ k', spehExp d k' = spehExp d k` using `⟨k, rfl⟩`. Simplify using `only [μ, dif_pos h]`.

Rewrite using `[spehExp_injective d h.choose_spec]`. Use `filter_upwards [GlobalTheory.SpehPair.eventually_spherical hV] with w hw`. Establish `hsph` using `hw (σ w) (hloc w)`. Take `⟨T, hT⟩` from `GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible (σ w).smooth (σ w).irred hsph`. Take `⟨τ, hτ, -⟩` from `GlobalTheory.CuspRep.LocEx.exists_isLocComp PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL E a P w`.

Establish `hS` using `PositivityTheory.Rg.Rs.ascSeed_holds2.2 E N a d V P hN hV hPu hPn hA w τ (σ w) hτ (hloc w)`. Take `⟨B, hB, hBT⟩` from `GlobalTheory.SpehPair.exists_sat_twist hd hτ hS hT μ hμ`. Establish `hsum : ∑ k : Fin d, B k.rev = T`. Rewrite using `[← hBT]`. Conclude with `Fintype.sum_equiv Fin.revPerm _ _ fun _ => rfl`.

Use `⟨fun k => B k.rev, fun k => ?_, hsph, hsum ▸ hT⟩` and prove the remaining obligations. Use `hB k.rev` as an intermediate fact. Rewrite `this` using `[PositivityTheory.Rg.Rs.satakeAscent.spehExp_rev, neg_neg, hμk, CG.twist_mk]`. Then use the resulting hypothesis.
-/
theorem strSat : StrSat := by
  intro E _ _ _ N a d V P σ hN hV hPu hPn hA hloc ν hν
  have hd : 1 ≤ d := by
    obtain ⟨hsum, -⟩ := hA
    rcases Nat.eq_zero_or_pos d with rfl | h
    · simp at hsum
      omega
    · exact h
  have hex : ∀ s : ℝ, ∃ χ : Formalism.L2.Host.HChar E, χ.IsAbsPow s :=
    fun s => ⟨_, GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s⟩
  choose χ0 hχ0 using hex
  classical
  let μ : ℝ → Formalism.L2.Host.HChar E := fun s =>
    if h : ∃ k, spehExp d k = s then ν h.choose else χ0 s
  have hμ : ∀ s, (μ s).IsAbsPow s := fun s => by
    by_cases h : ∃ k, spehExp d k = s
    · simp only [μ, dif_pos h]
      have := hν h.choose
      rwa [h.choose_spec] at this
    · simp only [μ, dif_neg h]
      exact hχ0 s
  have hμk : ∀ k, μ (spehExp d k) = ν k := fun k => by
    have h : ∃ k', spehExp d k' = spehExp d k := ⟨k, rfl⟩
    simp only [μ, dif_pos h]
    rw [spehExp_injective d h.choose_spec]
  filter_upwards [GlobalTheory.SpehPair.eventually_spherical hV] with w hw
  have hsph := hw (σ w) (hloc w)
  obtain ⟨T, hT⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible (σ w).smooth (σ w).irred hsph
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL E a P w
  have hS := PositivityTheory.Rg.Rs.ascSeed_holds2.2 E N a d V P hN hV hPu hPn hA w τ (σ w) hτ (hloc w)
  obtain ⟨B, hB, hBT⟩ := GlobalTheory.SpehPair.exists_sat_twist hd hτ hS hT μ hμ
  have hsum : ∑ k : Fin d, B k.rev = T := by
    rw [← hBT]
    exact Fintype.sum_equiv Fin.revPerm _ _ fun _ => rfl
  refine ⟨fun k => B k.rev, fun k => ?_, hsph, hsum ▸ hT⟩
  have := hB k.rev
  rwa [PositivityTheory.Rg.Rs.satakeAscent.spehExp_rev, neg_neg, hμk, CG.twist_mk] at this

end PositivityTheory.Rg.BcB.F.Rig

end
