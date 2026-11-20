import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GalPolLiftsOfSplit
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRepUniform
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.GalAllPlaces
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.CuspRep GlobalTheory.WeilDeligne Polynomial
end GlobalTheory.GalAllPlaces
end
noncomputable section
namespace GlobalTheory.GalAllPlaces
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
/- English proof (translation)
Introduce `hL hF hG hCh D T C K _ e π hc hr hsplit`. Establish `ha : 1 ≤ D.R.r`. Use `D.R.two_le_m` as an intermediate fact. Simplify using `only [Formalism.BasicNotions.Ranks.r]`. Use linear arithmetic over natural numbers and integers.

Take `⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ)` from `GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2`. Use `set P : HeightOneSpectrum (𝓞 D.host.E) → ℂ[X] := fun w => galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2)) with hP`. Establish `hU : ∀ᶠ w in Filter.cofinite, ((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal ∧ D.naut.unr (D.naut.locG π w)` using `(eventually_natCast_notMem D.host.E 2).and (D.naut.locG_unr_ae π)`. Take `⟨ρ, hρc, hρ⟩` from `_root_.GlobalTheory.GalAllPlaces.exists_rep_uniform_alt_alt hL hF hG C 2 ι ha π hc hr`. Use `letI : Algebra K ℂ := e.toAlgebra`.

Establish `key : ∀ γ : ℂ ≃ₐ[K] ℂ, ∀ w, (((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal ∧ D.naut.unr (D.naut.locG π w)) → (P w).map (γ : ℂ →+* ℂ) = P w`. Introduce `γ`. Take `⟨ρ', hρ'c, hρ'⟩` from `_root_.GlobalTheory.GalAllPlaces.exists_rep_uniform_alt_alt hL hF hG C 2 (ι.trans γ.toRingEquiv) ha π hc hr`. Establish `hfix : ∀ᶠ w in Filter.cofinite, IsSplitPl D.host w → (P w).map (γ : ℂ →+* ℂ) = P w` using `hsplit.mono fun w hw hs => by`. Take `⟨q, hq⟩` from `(Polynomial.mem_lifts _).1 (hw hs)`.

Simplify using `only [hP]`. Rewrite using `[← hq, Polynomial.map_map]`. Use `congr 1`. Use extensionality with `x`. Conclude with `γ.commutes x`.

Establish `hall` using `hU.and hfix`. Rewrite `hall` using `[Filter.eventually_cofinite]`. Use `set S := hall.toFinset with hS`. Establish `hmap : ∀ g, (((ρ' g : GL (Fin D.R.r) (Qbar 2)) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar 2)).charpoly.map (ι.trans γ.toRingEquiv).toRingHom) = ((((ρ' g : GL (Fin D.R.r) (Qbar 2)) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar 2)).charpoly.map ι.toRingHom).map (γ : ℂ →+* ℂ))`. Introduce `g`.

Rewrite using `[Polynomial.map_map]`. Both sides reduce to the same expression. Establish `heq` using `GlobalTheory.charpoly_eq_of_eqOn_dense (fun g => ((ρ g : GL (Fin D.R.r) (Qbar 2)) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar 2))) (fun g => ((ρ' g : GL (Fin D.R.r) (Qbar 2)) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar 2))) hρc hρ'c _ (GlobalTheory.ChebSplitDense.chebSplit_nd hCh D S) (by`. Introduce and unpack `g ⟨w, hwS, hsp, B, hB, hFr⟩`. Establish `hw : (((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal ∧ D.naut.unr (D.naut.locG π w)) ∧ (IsSplitPl D.host w → (P w).map (γ : ℂ →+* ℂ) = P w)`.

Assume the negation of the conclusion as `h`. Conclude with `hwS (by rw [hS, Set.Finite.mem_toFinset]; exact h)`. Apply `Polynomial.map_injective ι.toRingHom ι.injective` to reduce the goal to its premises. Rewrite using `[hρ w hw.1.1 hw.1.2 B g hB hFr]`. Apply `Polynomial.map_injective (γ : ℂ →+* ℂ) γ.injective` to reduce the goal to its premises.

Rewrite using `[← hmap, hρ' w hw.1.1 hw.1.2 B g hB hFr, hw.2 hsp])`. Introduce `w hw`. Take `⟨σ, hσ⟩` from `exists_isFrob (D.nd.plOm.2 w)`. Establish `h1` using `hρ w hw.1 hw.2 _ σ (D.nd.plOm.2 w) hσ`. Establish `h2` using `hρ' w hw.1 hw.2 _ σ (D.nd.plOm.2 w) hσ`.

Rewrite `h2` using `[hmap, ← heq σ, h1]`. Conclude with `h2`. Use `filter_upwards [hU] with w hw`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Introduce `n`.

Conclude with `GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv ((P w).coeff n) fun γ => by`. Use `congrArg (fun p : ℂ[X] => p.coeff n) (key γ w hw)` as an intermediate fact. Simplify `this` using `[Polynomial.coeff_map]`.
-/
theorem galPol_lpTw_mem_lifts_eventually : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, GlobalTheory.Published.AutomorphicFormsFiniteGL → _root_.UpperTheory.GalS.CuspUAlt → GlobalTheory.Published.ChebotarevDegreeOne → ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), _root_.GlobalTheory.HeightCounting.CGTrueT hL D T → ∀ (K : Type) [Field K] (e : K →+* ℂ) (π : D.naut.CG D.R.r), D.naut.csd π → D.naut.ralg π → (∀ᶠ w in Filter.cofinite, IsSplitPl D.host w → galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2)) ∈ Polynomial.lifts e) → ∀ᶠ w in Filter.cofinite, galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2)) ∈ Polynomial.lifts e := by
  intro hL hF hG hCh D T C K _ e π hc hr hsplit
  have ha : 1 ≤ D.R.r := by
    have := D.R.two_le_m
    simp only [Formalism.BasicNotions.Ranks.r]
    omega
  obtain ⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  set P : HeightOneSpectrum (𝓞 D.host.E) → ℂ[X] :=
    fun w => galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2)) with hP
  have hU : ∀ᶠ w in Filter.cofinite, ((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal ∧ D.naut.unr (D.naut.locG π w) :=
    (eventually_natCast_notMem D.host.E 2).and (D.naut.locG_unr_ae π)
  obtain ⟨ρ, hρc, hρ⟩ := _root_.GlobalTheory.GalAllPlaces.exists_rep_uniform_alt_alt hL hF hG C 2 ι ha π hc hr
  letI : Algebra K ℂ := e.toAlgebra
  have key : ∀ γ : ℂ ≃ₐ[K] ℂ, ∀ w, (((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal ∧ D.naut.unr (D.naut.locG π w)) →
      (P w).map (γ : ℂ →+* ℂ) = P w := by
    intro γ
    obtain ⟨ρ', hρ'c, hρ'⟩ := _root_.GlobalTheory.GalAllPlaces.exists_rep_uniform_alt_alt hL hF hG C 2 (ι.trans γ.toRingEquiv) ha π hc hr
    have hfix : ∀ᶠ w in Filter.cofinite, IsSplitPl D.host w → (P w).map (γ : ℂ →+* ℂ) = P w :=
      hsplit.mono fun w hw hs => by
        obtain ⟨q, hq⟩ := (Polynomial.mem_lifts _).1 (hw hs)
        simp only [hP]
        rw [← hq, Polynomial.map_map]
        congr 1
        ext x
        exact γ.commutes x
    have hall := hU.and hfix
    rw [Filter.eventually_cofinite] at hall
    set S := hall.toFinset with hS
    have hmap : ∀ g, (((ρ' g : GL (Fin D.R.r) (Qbar 2)) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar 2)).charpoly.map
        (ι.trans γ.toRingEquiv).toRingHom) = ((((ρ' g : GL (Fin D.R.r) (Qbar 2)) :
          Matrix (Fin D.R.r) (Fin D.R.r) (Qbar 2)).charpoly.map ι.toRingHom).map (γ : ℂ →+* ℂ)) := by
      intro g
      rw [Polynomial.map_map]
      rfl
    have heq := GlobalTheory.charpoly_eq_of_eqOn_dense
      (fun g => ((ρ g : GL (Fin D.R.r) (Qbar 2)) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar 2)))
      (fun g => ((ρ' g : GL (Fin D.R.r) (Qbar 2)) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar 2))) hρc hρ'c _
      (GlobalTheory.ChebSplitDense.chebSplit_nd hCh D S) (by
        rintro g ⟨w, hwS, hsp, B, hB, hFr⟩
        have hw : (((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal ∧ D.naut.unr (D.naut.locG π w)) ∧
            (IsSplitPl D.host w → (P w).map (γ : ℂ →+* ℂ) = P w) := by
          by_contra h
          exact hwS (by rw [hS, Set.Finite.mem_toFinset]; exact h)
        apply Polynomial.map_injective ι.toRingHom ι.injective
        rw [hρ w hw.1.1 hw.1.2 B g hB hFr]
        apply Polynomial.map_injective (γ : ℂ →+* ℂ) γ.injective
        rw [← hmap, hρ' w hw.1.1 hw.1.2 B g hB hFr, hw.2 hsp])
    intro w hw
    obtain ⟨σ, hσ⟩ := exists_isFrob (D.nd.plOm.2 w)
    have h1 := hρ w hw.1 hw.2 _ σ (D.nd.plOm.2 w) hσ
    have h2 := hρ' w hw.1 hw.2 _ σ (D.nd.plOm.2 w) hσ
    rw [hmap, ← heq σ, h1] at h2
    exact h2
  filter_upwards [hU] with w hw
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro n
  exact GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv ((P w).coeff n) fun γ => by
    have := congrArg (fun p : ℂ[X] => p.coeff n) (key γ w hw)
    simpa [Polynomial.coeff_map] using this
end GlobalTheory.GalAllPlaces
end
end
