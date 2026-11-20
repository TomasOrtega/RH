import Formalism.HarderNarasimhan.StatementPl
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SatBasic
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.ShiftInvariance
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax

open Module NumberField

noncomputable section

namespace Formalism.HN

/- English proof (translation)
Establish `key : Module.finrank ℚ K = 2 * nPl K`. Establish `h1` using `NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K`. Use `haveI : IsEmpty {w : InfinitePlace K // w.IsReal} := by`. Use `⟨fun w => ?_⟩` and prove the remaining obligations. Establish `hc : w.1.IsComplex` using `IsTotallyComplex.isComplex w.1`.

Use `first`. Consider the case `exact (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hc) w.2`. Consider the case `exact (NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr w.2) hc`. Establish `h3 : Nat.card {w : InfinitePlace K // w.IsComplex} = Nat.card (InfinitePlace K)` using `Nat.card_congr (Equiv.subtypeUnivEquiv (fun w => IsTotallyComplex.isComplex w))`. Simplify using `only [Fintype.card_eq_nat_card, Nat.card_of_isEmpty, h3] at h1`.

Simplify using `only [nPl, Fintype.card_eq_nat_card]`. Use linear arithmetic over natural numbers and integers. Conclude with `key` after adjusting the coercions.
-/
theorem twist_finrank_eq (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] :
    (Module.finrank ℚ K : ℝ) = 2 * (nPl K : ℝ) := by
  have key : Module.finrank ℚ K = 2 * nPl K := by
    have h1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
    haveI : IsEmpty {w : InfinitePlace K // w.IsReal} := by
      refine ⟨fun w => ?_⟩
      have hc : w.1.IsComplex := IsTotallyComplex.isComplex w.1
      first
        | exact (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hc) w.2
        | exact (NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr w.2) hc
    have h3 : Nat.card {w : InfinitePlace K // w.IsComplex} = Nat.card (InfinitePlace K) :=
      Nat.card_congr (Equiv.subtypeUnivEquiv (fun w => IsTotallyComplex.isComplex w))
    simp only [Fintype.card_eq_nat_card, Nat.card_of_isEmpty, h3] at h1
    simp only [nPl, Fintype.card_eq_nat_card]
    omega
  exact_mod_cast key

/- English proof (translation)
Introduce `K V ι _ _ _ _ _ _ _ _ _ _ b X c hX hc`. Simplify using `only`. Introduce `L hL`. Establish `hX' : ∀ v, IsUnit (((c v : ℂ)) • X v).det`. Introduce `v`.

Rewrite using `[Matrix.det_smul]`. Conclude with `((isUnit_iff_ne_zero.mpr (by exact_mod_cast (hc v).ne' : ((c v : ℂ)) ≠ 0)).pow _).mul (hX v)`. Establish `hfg : ∀ N : Submodule (𝓞 K) V, N ≤ L → N.FG`. Introduce `N hN`. Use `haveI := isNoetherian_of_fg_of_noetherian L hL`.

Establish `h1' : (N.comap L.subtype).FG` using `IsNoetherian.noetherian _`. Establish `h2'` using `h1'.map L.subtype`. Rewrite `h2'` using `[Submodule.map_comap_subtype, inf_eq_right.mpr hN]`. Then use the resulting hypothesis. Establish `hnPl : (nPl K : ℝ) ≠ 0`. Establish `: 0 < nPl K` using `Fintype.card_pos`.

Conclude with `this.ne'` after adjusting the coercions. Establish `hfr` using `twist_finrank_eq K`. Establish `hP : 0 < ∏ v, c v` using `Finset.prod_pos fun v _ => hc v`. Establish `hlogP : Real.log (∏ v, c v) = ∑ v, Real.log (c v)` using `Real.log_prod fun v _ => (hc v).ne'`. Establish `hkey : ∀ N : Submodule (𝓞 K) V, N ≤ L → rk (Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v)) N = rk (Formalism.HermitianLatticesTheory.realize b X) N ∧ deg (Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v)) N = deg (Formalism.Hermi …`.

Introduce `N hN`. Establish `hNfg` using `hfg N hN`. Take `⟨hlat, hrk, -⟩` from `h2 K V ι b X hX N hNfg`. Take `⟨-, hrk₂, -⟩` from `h2 K V ι b (fun v => ((c v : ℂ)) • X v) hX' N hNfg`. Use `⟨by rw [hrk, hrk₂], ?_⟩` and prove the remaining obligations.

Establish `hcov` using `h1 K V ι b X c hX hc N hNfg`. Use `haveI := hlat.2`. Establish `hC` using `Formalism.F.covol_pos (zl (Formalism.HermitianLatticesTheory.realize b X) N)`. Simplify using `only [deg, Formalism.F.deg]`. Rewrite using `[hcov, Real.log_mul (Real.rpow_pos_of_pos hP _).ne' hC.ne', Real.log_rpow hP, hlogP, hrk]`.

Use `push_cast`. Rewrite using `[hfr]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Take `⟨hlatL, hrkL, -⟩` from `h2 K V ι b X hX L hL`.

Take `⟨hlatL₂, -, -⟩` from `h2 K V ι b (fun v => ((c v : ℂ)) • X v) hX' L hL`. Take `⟨-, hmu, hstep, -⟩` from `h3 (𝓞 K) V _ _ (Formalism.HermitianLatticesTheory.realize b X) (Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v)) L ((1 / (nPl K : ℝ)) * ∑ v, Real.log (c v)) hlatL hlatL₂ hkey`. Establish `hrkpos : L ≠ ⊥ → (rk (Formalism.HermitianLatticesTheory.realize b X) L : ℝ) ≠ 0`. Introduce `hne`. Rewrite using `[hrkL]`.

Establish `h1' : 0 < Module.finrank ℚ K` using `Module.finrank_pos`. Establish `h2' : 0 < rkK L`. Take `⟨s, hs⟩` from `hL`. Unfold `rkK`. Rewrite using `[← hs, Submodule.span_span_of_tower (𝓞 K) K (s : Set V)]`.

Use `haveI : FiniteDimensional K (Submodule.span K (s : Set V)) := FiniteDimensional.span_finset K s`. Rewrite using `[Module.finrank_pos_iff, Submodule.nontrivial_iff_ne_bot]`. Introduce `h0`. Apply `hne` to reduce the goal to its premises. Rewrite using `[← hs, eq_bot_iff]`.

Introduce `x hx`. Establish `hx'` using `Submodule.span_le_restrictScalars (𝓞 K) K (s : Set V) hx`. Establish `hx0 : x = 0` using `by simpa [h0] using hx'`. Simplify using `[hx0]`. Conclude with `(Nat.mul_pos h1' h2').ne'` after adjusting the coercions.

Establish `hslope : L ≠ ⊥ → slope (Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v)) L = slope (Formalism.HermitianLatticesTheory.realize b X) L + (1 / (nPl K : ℝ)) * ∑ v, Real.log (c v)`. Introduce `hne`. Establish `hs : ∀ ρ' : V →+ EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2), slope ρ' L = deg ρ' L / (rk ρ' L : ℝ)` using `fun _ => rfl`. Rewrite using `[hs, hs, (hkey L le_rfl).1, (hkey L le_rfl).2, add_div, mul_div_assoc, div_self (hrkpos hne), mul_one]`. Use `⟨hslope, hmu, fun hne => ?_, fun θ => hstep θ⟩` and prove the remaining obligations.

Simplify using `only [muDef, muMaxDef, muMinDef, hslope hne, (hmu hne).1, (hmu hne).2]`. Use `⟨by ring, by ring, by ring⟩` and prove the remaining obligations.
-/
theorem twist_of (h1 : RescaleCovol) (h2 : PlLat) (h3 : ShiftInvariance.{0, 0, 0, 0}) : Twist := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X c hX hc
  dsimp only
  intro L hL
  have hX' : ∀ v, IsUnit (((c v : ℂ)) • X v).det := by
    intro v
    rw [Matrix.det_smul]
    exact ((isUnit_iff_ne_zero.mpr (by exact_mod_cast (hc v).ne' : ((c v : ℂ)) ≠ 0)).pow _).mul (hX v)
  have hfg : ∀ N : Submodule (𝓞 K) V, N ≤ L → N.FG := by
    intro N hN
    haveI := isNoetherian_of_fg_of_noetherian L hL
    have h1' : (N.comap L.subtype).FG := IsNoetherian.noetherian _
    have h2' := h1'.map L.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hN] at h2'
  have hnPl : (nPl K : ℝ) ≠ 0 := by
    have : 0 < nPl K := Fintype.card_pos
    exact_mod_cast this.ne'
  have hfr := twist_finrank_eq K
  have hP : 0 < ∏ v, c v := Finset.prod_pos fun v _ => hc v
  have hlogP : Real.log (∏ v, c v) = ∑ v, Real.log (c v) := Real.log_prod fun v _ => (hc v).ne'
  have hkey : ∀ N : Submodule (𝓞 K) V, N ≤ L →
      rk (Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v)) N = rk (Formalism.HermitianLatticesTheory.realize b X) N ∧
      deg (Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v)) N = deg (Formalism.HermitianLatticesTheory.realize b X) N +
        (1 / (nPl K : ℝ)) * (∑ v, Real.log (c v)) * (rk (Formalism.HermitianLatticesTheory.realize b X) N : ℝ) := by
    intro N hN
    have hNfg := hfg N hN
    obtain ⟨hlat, hrk, -⟩ := h2 K V ι b X hX N hNfg
    obtain ⟨-, hrk₂, -⟩ := h2 K V ι b (fun v => ((c v : ℂ)) • X v) hX' N hNfg
    refine ⟨by rw [hrk, hrk₂], ?_⟩
    have hcov := h1 K V ι b X c hX hc N hNfg
    haveI := hlat.2
    have hC := Formalism.F.covol_pos (zl (Formalism.HermitianLatticesTheory.realize b X) N)
    simp only [deg, Formalism.F.deg]
    rw [hcov, Real.log_mul (Real.rpow_pos_of_pos hP _).ne' hC.ne', Real.log_rpow hP, hlogP, hrk]
    push_cast
    rw [hfr]
    field_simp
    ring
  obtain ⟨hlatL, hrkL, -⟩ := h2 K V ι b X hX L hL
  obtain ⟨hlatL₂, -, -⟩ := h2 K V ι b (fun v => ((c v : ℂ)) • X v) hX' L hL
  obtain ⟨-, hmu, hstep, -⟩ := h3 (𝓞 K) V _ _ (Formalism.HermitianLatticesTheory.realize b X)
    (Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v)) L ((1 / (nPl K : ℝ)) * ∑ v, Real.log (c v))
    hlatL hlatL₂ hkey
  have hrkpos : L ≠ ⊥ → (rk (Formalism.HermitianLatticesTheory.realize b X) L : ℝ) ≠ 0 := by
    intro hne
    rw [hrkL]
    have h1' : 0 < Module.finrank ℚ K := Module.finrank_pos
    have h2' : 0 < rkK L := by
      obtain ⟨s, hs⟩ := hL
      unfold rkK
      rw [← hs, Submodule.span_span_of_tower (𝓞 K) K (s : Set V)]
      haveI : FiniteDimensional K (Submodule.span K (s : Set V)) := FiniteDimensional.span_finset K s
      rw [Module.finrank_pos_iff, Submodule.nontrivial_iff_ne_bot]
      intro h0
      apply hne
      rw [← hs, eq_bot_iff]
      intro x hx
      have hx' := Submodule.span_le_restrictScalars (𝓞 K) K (s : Set V) hx
      have hx0 : x = 0 := by simpa [h0] using hx'
      simp [hx0]
    exact_mod_cast (Nat.mul_pos h1' h2').ne'
  have hslope : L ≠ ⊥ → slope (Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v)) L =
      slope (Formalism.HermitianLatticesTheory.realize b X) L + (1 / (nPl K : ℝ)) * ∑ v, Real.log (c v) := by
    intro hne
    have hs : ∀ ρ' : V →+ EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2),
        slope ρ' L = deg ρ' L / (rk ρ' L : ℝ) := fun _ => rfl
    rw [hs, hs, (hkey L le_rfl).1, (hkey L le_rfl).2, add_div, mul_div_assoc, div_self (hrkpos hne),
      mul_one]
  refine ⟨hslope, hmu, fun hne => ?_, fun θ => hstep θ⟩
  simp only [muDef, muMaxDef, muMinDef, hslope hne, (hmu hne).1, (hmu hne).2]
  refine ⟨by ring, by ring, by ring⟩

end Formalism.HN
