import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ThetaBasic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeBasicOfConjPlaces

noncomputable section

open NumberField IsDedekindDomain Matrix Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1 PositivityTheory.Rg.BcB.E1
open GlobalTheory.CompanionTheory.Size

namespace GlobalTheory.CompanionTheory.SizeCont

/- English proof (translation)
Break down `isEmpty_or_nonempty ι with h | h` into its components or cases. Simplify `continuous_const` using `[Real.iSup_of_isEmpty]`. Establish `: (fun x => ⨆ i, f i x) = fun x => Finset.univ.sup' Finset.univ_nonempty fun i => f i x`. Use function extensionality and compare the values at `x`. Rewrite using `[Finset.sup'_univ_eq_ciSup]`.

Rewrite using `[this]`. Conclude with `Continuous.finset_sup'_apply _ fun i _ => hf i`.
-/
theorem continuous_iSup_fin {X ι : Type} [TopologicalSpace X] [Fintype ι] (f : ι → X → ℝ)
    (hf : ∀ i, Continuous (f i)) : Continuous fun x => ⨆ i, f i x := by
  rcases isEmpty_or_nonempty ι with h | h
  · simpa [Real.iSup_of_isEmpty] using continuous_const
  · have : (fun x => ⨆ i, f i x) = fun x => Finset.univ.sup' Finset.univ_nonempty fun i => f i x := by
      funext x
      rw [Finset.sup'_univ_eq_ciSup]
    rw [this]
    exact Continuous.finset_sup'_apply _ fun i _ => hf i

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

/- English proof (translation)
The claim follows from `(RestrictedProduct.continuous_eval w).comp continuous_snd`.
-/
theorem continuous_cW (w : HeightOneSpectrum (𝓞 E)) : Continuous (cW w : Ad E → w.adicCompletion E) :=
  (RestrictedProduct.continuous_eval w).comp continuous_snd

/- English proof (translation)
The claim follows from `continuous_id.matrix_elem p.1 p.2`.
-/
theorem continuous_elem (p : Fin n × Fin n) :
    Continuous fun A : Matrix (Fin n) (Fin n) (Ad E) => A p.1 p.2 :=
  continuous_id.matrix_elem p.1 p.2

/- English proof (translation)
The claim follows from `Real.continuous_posLog.comp (continuous_iSup_fin _ fun p => (((continuous_cV v).comp (continuous_elem p)).norm).pow 2)`.
-/
theorem continuous_inf (v : InfinitePlace E) : Continuous fun A : Matrix (Fin n) (Fin n) (Ad E) =>
    Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (A p.1 p.2)‖ ^ 2) :=
  Real.continuous_posLog.comp (continuous_iSup_fin _ fun p =>
    (((continuous_cV v).comp (continuous_elem p)).norm).pow 2)

/- English proof (translation)
The claim follows from `Real.continuous_posLog.comp (continuous_iSup_fin _ fun p => ((continuous_cW w).comp (continuous_elem p)).norm)`.
-/
theorem continuous_fin (w : HeightOneSpectrum (𝓞 E)) : Continuous fun A : Matrix (Fin n) (Fin n) (Ad E) =>
    Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (A p.1 p.2)‖) :=
  Real.continuous_posLog.comp (continuous_iSup_fin _ fun p =>
    ((continuous_cW w).comp (continuous_elem p)).norm)

/- English proof (translation)
Establish `hev : ∀ p : Fin n × Fin n, ∀ᶠ A : Matrix (Fin n) (Fin n) (Ad E) in 𝓝 A₀, ∀ w, ‖cW w (A p.1 p.2)‖ ≤ max ‖cW w (A₀ p.1 p.2)‖ 1` using `fun p => (continuous_elem p).continuousAt.eventually (eventually_fin (A₀ p.1 p.2))`. Use `filter_upwards [Filter.eventually_all.2 hev] with A hA`. Use `finsum_eq_sum_of_support_subset _ fun w hw => ?_` and prove the remaining obligations. Rewrite using `[Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq]`. Assume the negation of the conclusion as `hn`.

Establish `h0 : sz (A₀.map (cW w)) ≤ 1` using `not_lt.1 hn`. Use `hw ((Real.posLog_eq_zero_iff _).2 ?_)` and prove the remaining obligations. Establish `h1 : 0 ≤ ⨆ p : Fin n × Fin n, ‖cW w (A p.1 p.2)‖` using `Real.iSup_nonneg fun _ => norm_nonneg _`. Rewrite using `[abs_of_nonneg h1]`. Use `Real.iSup_le (fun p => (hA p w).trans (max_le ?_ le_rfl)) zero_le_one` and prove the remaining obligations.

Conclude with `(le_sup (fun q : Fin n × Fin n => ‖cW w (A₀ q.1 q.2)‖) p).trans h0`.
-/
theorem eventually_finsum (hS : SzFin) (A₀ : Matrix (Fin n) (Fin n) (Ad E)) :
    ∀ᶠ A in 𝓝 A₀, ∑ᶠ w, Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (A p.1 p.2)‖) =
      ∑ w ∈ (hS E (Fin n) (Fin n) A₀).toFinset,
        Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (A p.1 p.2)‖) := by
  have hev : ∀ p : Fin n × Fin n, ∀ᶠ A : Matrix (Fin n) (Fin n) (Ad E) in 𝓝 A₀,
      ∀ w, ‖cW w (A p.1 p.2)‖ ≤ max ‖cW w (A₀ p.1 p.2)‖ 1 := fun p =>
    (continuous_elem p).continuousAt.eventually (eventually_fin (A₀ p.1 p.2))
  filter_upwards [Filter.eventually_all.2 hev] with A hA
  refine finsum_eq_sum_of_support_subset _ fun w hw => ?_
  rw [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  by_contra hn
  have h0 : sz (A₀.map (cW w)) ≤ 1 := not_lt.1 hn
  refine hw ((Real.posLog_eq_zero_iff _).2 ?_)
  have h1 : 0 ≤ ⨆ p : Fin n × Fin n, ‖cW w (A p.1 p.2)‖ := Real.iSup_nonneg fun _ => norm_nonneg _
  rw [abs_of_nonneg h1]
  refine Real.iSup_le (fun p => (hA p w).trans (max_le ?_ le_rfl)) zero_le_one
  exact (le_sup (fun q : Fin n × Fin n => ‖cW w (A₀ q.1 q.2)‖) p).trans h0

/- English proof (translation)
Use `continuous_iff_continuousAt.2 fun A₀ => ?_` and prove the remaining obligations. Establish `hc : Continuous fun A : Matrix (Fin n) (Fin n) (Ad E) => ∑ v, Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (A p.1 p.2)‖ ^ 2) + ∑ w ∈ (hS E (Fin n) (Fin n) A₀).toFinset, Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (A p.1 p.2)‖)` using `(continuous_finset_sum _ fun v _ => continuous_inf v).add (continuous_finset_sum _ fun w _ => continuous_fin w)`. Use `hc.continuousAt.congr ?_` and prove the remaining obligations. Use `filter_upwards [eventually_finsum hS A₀] with A hA`. Rewrite using `[logSizeM, hA]`.
-/
theorem continuous_logSizeM (hS : SzFin) :
    Continuous (logSizeM : Matrix (Fin n) (Fin n) (Ad E) → ℝ) := by
  refine continuous_iff_continuousAt.2 fun A₀ => ?_
  have hc : Continuous fun A : Matrix (Fin n) (Fin n) (Ad E) =>
      ∑ v, Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (A p.1 p.2)‖ ^ 2) +
        ∑ w ∈ (hS E (Fin n) (Fin n) A₀).toFinset,
          Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (A p.1 p.2)‖) :=
    (continuous_finset_sum _ fun v _ => continuous_inf v).add
      (continuous_finset_sum _ fun w _ => continuous_fin w)
  refine hc.continuousAt.congr ?_
  filter_upwards [eventually_finsum hS A₀] with A hA
  rw [logSizeM, hA]

/- English proof (translation)
Introduce `hS E _ _ _ n`. Establish `h` using `continuous_logSizeM (E := E) (n := n) hS`. Conclude with `(h.comp Units.continuous_val).add (h.comp Units.continuous_coe_inv)`.
-/
theorem sizeCont : SzFin → SizeCont := by
  intro hS E _ _ _ n
  have h := continuous_logSizeM (E := E) (n := n) hS
  exact (h.comp Units.continuous_val).add (h.comp Units.continuous_coe_inv)

end GlobalTheory.CompanionTheory.SizeCont

end
