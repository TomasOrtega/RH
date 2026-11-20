import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlurisubharmonicLocal
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeCovolumePositiveStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicFamilySmoothEntries
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetCuspFramePlurisubharmonicStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CuspSubmodulesLocallyFiniteStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Corr

open ReciprocityTheory.AnForm.A (IsPsh)

/- English proof (translation)
Use `⟨hφ.1.add hψ.1, fun z w hd => ?_⟩` and prove the remaining obligations. Take `⟨h1, h2⟩` from `hφ.2 z w hd`. Take `⟨h3, h4⟩` from `hψ.2 z w hd`. Use `⟨h1.add h3, ?_⟩` and prove the remaining obligations. Rewrite using `[Real.circleAverage_fun_add h1 h3]`.

Conclude with `add_le_add h2 h4`.
-/
theorem psh_add {d : ℕ} {U : Set (Fin d → ℂ)} {φ ψ : (Fin d → ℂ) → ℝ} (hφ : IsPsh U φ) (hψ : IsPsh U ψ) :
    IsPsh U (fun z => φ z + ψ z) := by
  refine ⟨hφ.1.add hψ.1, fun z w hd => ?_⟩
  obtain ⟨h1, h2⟩ := hφ.2 z w hd
  obtain ⟨h3, h4⟩ := hψ.2 z w hd
  refine ⟨h1.add h3, ?_⟩
  rw [Real.circleAverage_fun_add h1 h3]
  exact add_le_add h2 h4

/- English proof (translation)
Use `⟨upperSemicontinuousOn_const, fun z w _ => ⟨circleIntegrable_const c 0 1, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Real.circleAverage_const]`.
-/
theorem psh_const {d : ℕ} (U : Set (Fin d → ℂ)) (c : ℝ) : IsPsh U (fun _ => c) := by
  refine ⟨upperSemicontinuousOn_const, fun z w _ => ⟨circleIntegrable_const c 0 1, ?_⟩⟩
  rw [Real.circleAverage_const]

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simpa using psh_const U 0`. Consider the case `insert a S ha ih`. Simplify using `only [Finset.sum_insert ha]`. Conclude with `psh_add (h a (Finset.mem_insert_self a S)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem psh_sum {d : ℕ} {U : Set (Fin d → ℂ)} {ι : Type} (S : Finset ι) {f : ι → (Fin d → ℂ) → ℝ}
    (h : ∀ i ∈ S, IsPsh U (f i)) : IsPsh U (fun z => ∑ i ∈ S, f i z) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using psh_const U 0
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    exact psh_add (h a (Finset.mem_insert_self a S)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Use `⟨fun z hz y hy => ?_, fun z w hd => ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ᶠ x in nhdsWithin z U, φ x < y` using `hφ.1 z hz y (by show φ z < y; rw [h z hz]; exact hy) filter_upwards [h1, self_mem_nhdsWithin] with x hx hxU`. Rewrite using `[← h x hxU]` and apply the resulting hypothesis. Take `⟨h1, h2⟩` from `hφ.2 z w hd`. Establish `e : ∀ θ : ℝ, φ (z + circleMap 0 1 θ • w) = ψ (z + circleMap 0 1 θ • w)` using `fun θ => h _ (hd _ (by simp))`.

Establish `hz : z ∈ U` using `by simpa using hd 0 (by simp)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `CircleIntegrable at h1 ⊢`. Simplify `h1` using `only [e]`. Rewrite using `[← h z hz]`.

Simplify `h2` using `only [Real.circleAverage_def, e]`.
-/
theorem psh_congr {d : ℕ} {U : Set (Fin d → ℂ)} {φ ψ : (Fin d → ℂ) → ℝ} (h : ∀ z ∈ U, φ z = ψ z)
    (hφ : IsPsh U φ) : IsPsh U ψ := by
  refine ⟨fun z hz y hy => ?_, fun z w hd => ?_⟩
  · have h1 : ∀ᶠ x in nhdsWithin z U, φ x < y := hφ.1 z hz y (by show φ z < y; rw [h z hz]; exact hy)
    filter_upwards [h1, self_mem_nhdsWithin] with x hx hxU
    rwa [← h x hxU]
  · obtain ⟨h1, h2⟩ := hφ.2 z w hd
    have e : ∀ θ : ℝ, φ (z + circleMap 0 1 θ • w) = ψ (z + circleMap 0 1 θ • w) := fun θ =>
      h _ (hd _ (by simp))
    have hz : z ∈ U := by simpa using hd 0 (by simp)
    refine ⟨?_, ?_⟩
    · unfold CircleIntegrable at h1 ⊢
      simpa only [e] using h1
    · rw [← h z hz]
      simpa only [Real.circleAverage_def, e] using h2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
  {Ψ : Type} [Fintype Ψ]

noncomputable def term (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (F : Finset (Submodule (𝓞 E) Λ)) :
    Option F → ℝ
  | none => 0
  | some I => -Real.log (R.nz σ I.1)

/- English proof (translation)
Establish `h0 : 0 ≤ Finset.univ.sup' Finset.univ_nonempty (term R σ F)` using `Finset.le_sup' (term R σ F) (Finset.mem_univ none)`. Establish `hb : ∀ x ∈ {x | ∃ I, R.IsCusp I ∧ x = -Real.log (R.nz σ I)}, x ≤ Finset.univ.sup' Finset.univ_nonempty (term R σ F)`. Introduce and unpack `x ⟨I, hI, rfl⟩`. Distinguish the cases in `h : R.nz σ I ≤ 1`. Conclude with `Finset.le_sup' (term R σ F) (Finset.mem_univ (some ⟨I, h2 I hI h⟩))`.

Use `Real.log_nonneg (not_le.1 h).le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Unfold `RiemLat.cuspW`. Use `le_antisymm (max_le h0 (Real.sSup_le hb h0)) (Finset.sup'_le _ _ fun o _ => ?_)` and prove the remaining obligations. Consider the cases of `o with`.

Consider the case `none => exact le_max_left _ _`. Consider the case `some I => exact le_max_of_le_right (le_csSup ⟨_, hb⟩ ⟨I.1, h1 I.1 I.2, rfl⟩)`.
-/
theorem cuspW_eq (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (F : Finset (Submodule (𝓞 E) Λ))
    (h1 : ∀ I ∈ F, R.IsCusp I) (h2 : ∀ I, R.IsCusp I → R.nz σ I ≤ 1 → I ∈ F) :
    R.cuspW σ = Finset.univ.sup' Finset.univ_nonempty (term R σ F) := by
  have h0 : 0 ≤ Finset.univ.sup' Finset.univ_nonempty (term R σ F) :=
    Finset.le_sup' (term R σ F) (Finset.mem_univ none)
  have hb : ∀ x ∈ {x | ∃ I, R.IsCusp I ∧ x = -Real.log (R.nz σ I)},
      x ≤ Finset.univ.sup' Finset.univ_nonempty (term R σ F) := by
    rintro x ⟨I, hI, rfl⟩
    by_cases h : R.nz σ I ≤ 1
    · exact Finset.le_sup' (term R σ F) (Finset.mem_univ (some ⟨I, h2 I hI h⟩))
    · have := Real.log_nonneg (not_le.1 h).le
      linarith
  unfold RiemLat.cuspW
  refine le_antisymm (max_le h0 (Real.sSup_le hb h0)) (Finset.sup'_le _ _ fun o _ => ?_)
  cases o with
  | none => exact le_max_left _ _
  | some I => exact le_max_of_le_right (le_csSup ⟨_, hb⟩ ⟨I.1, h1 I.1 I.2, rfl⟩)

/- English proof (translation)
Use `le_antisymm (Finset.sup'_le _ _ fun j hj => ?_) ?_` and prove the remaining obligations. Use `Finset.le_sup' f hj` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨j, hj, e⟩` from `Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι)) f`. Rewrite using `[e]`.

Conclude with `Finset.le_sup' (fun j => a + f j) hj`.
-/
theorem add_sup {ι : Type} [Fintype ι] [Nonempty ι] (a : ℝ) (f : ι → ℝ) :
    Finset.univ.sup' Finset.univ_nonempty (fun j => a + f j) = a + Finset.univ.sup' Finset.univ_nonempty f := by
  refine le_antisymm (Finset.sup'_le _ _ fun j hj => ?_) ?_
  · have := Finset.le_sup' f hj
    linarith
  · obtain ⟨j, hj, e⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι)) f
    rw [e]
    exact Finset.le_sup' (fun j => a + f j) hj

end GlobalTheory.CompanionTheory.Ar.Cusp.Corr

open GlobalTheory.CompanionTheory.Ar.Cusp.Corr in
/- English proof (translation)
Introduce `E _ _ _ g Λ _ _ Ψ _ n U R σ m b hU hH hσ hb`. Establish `hrank : ∀ t ∈ U, (R t).HasRank σ m`. Introduce `t ht τ`. Establish `h` using `hb.2 t ht τ`. Establish `e : Module.finrank ℂ (Submodule.span ℂ (Set.range fun i => b τ i t)) = m`.

Rewrite using `[finrank_span_eq_card h.1, Fintype.card_fin]`. Rewrite `e` using `[h.2]`. Conclude with `e`. Establish `hL : ReciprocityTheory.AnForm.A.IsPsh U (fun t => (R t).logDet (fun τ i => b τ i t))` using `psh_sum Finset.univ fun τ _ => (GlobalTheory.CompanionTheory.Relay.holomorphic_family_smooth_entries E g Λ Ψ n U R hU hH).2.2 m (b τ) (hb.1 τ) (fun t ht => (hb.2 t ht τ).1)`. Establish `hloc : ∀ t₀ ∈ U, ∃ W : Set (Fin n → ℂ), IsOpen W ∧ t₀ ∈ W ∧ ReciprocityTheory.AnForm.A.IsPsh (U ∩ W) (fun t => (R t).logDet (fun τ i => b τ i t) + (R t).cuspW σ) ∧ ContinuousOn (fun t => (R t).cuspW σ) (U ∩ W)`.

Introduce `t₀ ht₀`. Take `⟨ε, F, hε, hF⟩` from `GlobalTheory.T.cusp_submodules_locally_finite E g Λ Ψ n U R σ m hU hH hσ hrank t₀ ht₀`. Establish `hVo : IsOpen (U ∩ Metric.ball t₀ ε)` using `hU.inter Metric.isOpen_ball`. Establish `hVU : U ∩ Metric.ball t₀ ε ⊆ U` using `Set.inter_subset_left`. Establish `hphi` using `fun I : F => GlobalTheory.T.log_det_cusp_frame_plurisubharmonic E g Λ Ψ n (U ∩ Metric.ball t₀ ε) R σ m b I.1 hVo ⟨fun t ht t' ht' => hH.1 t ht.1 t' ht'.1, fun x => (hH.2 x).mono hVU⟩ hσ ⟨fun τ i => (hb.1 τ i).mono hVU, fun t ht => hb.2 t ht.1⟩ (fun t ht => (hF t ht).1 I.1 I.2)`.

Establish `heq : ∀ t ∈ U ∩ Metric.ball t₀ ε, (R t).cuspW σ = Finset.univ.sup' Finset.univ_nonempty (term (R t) σ F)` using `fun t ht => cuspW_eq (R t) σ F (hF t ht).1 (hF t ht).2`. Use `⟨Metric.ball t₀ ε, Metric.isOpen_ball, Metric.mem_ball_self hε, ?_, ?_⟩` and prove the remaining obligations. Establish `hs` using `ReciprocityTheory.AnForm.A.isPsh_sup_thm n (Option F) (U ∩ Metric.ball t₀ ε) (fun o t => (R t).logDet (fun τ i => b τ i t) + term (R t) σ F o) hVo (fun o => by`. Consider the cases of `o with`. Consider the case `none`.

Conclude with `psh_congr (fun z _ => (add_zero _).symm) (GlobalTheory.CompanionTheory.AnForm.PshLocal.isPsh_mono hVU hL)`. Consider the case `some I => exact psh_congr (fun z _ => sub_eq_add_neg _ _) (hphi I).1)`. Use `psh_congr (fun t ht => ?_) hs` and prove the remaining obligations. Rewrite using `[heq t ht]`. Conclude with `add_sup _ _`.

Establish `hc : ∀ o : Option F, ContinuousOn (fun t => term (R t) σ F o) (U ∩ Metric.ball t₀ ε)`. Introduce `o`. Consider the cases of `o with`. Consider the case `none => exact continuousOn_const`. Consider the case `some I`.

Use `ContinuousOn.neg ((hphi I).2.log fun t ht => ?_)` and prove the remaining obligations. Establish `hI` using `(hF t ht).1 I.1 I.2`. Take `⟨⟨r, v, hv⟩, h2⟩` from `GlobalTheory.T.isotropic_sublattice_covolume_positive E g Λ Ψ (R t) σ I.1 hσ hI.2.2 hI.1`. Conclude with `(h2 r v hv).2.1.ne'`. Establish `hs : ContinuousOn (fun t => Finset.univ.sup' Finset.univ_nonempty (fun o => term (R t) σ F o)) (U ∩ Metric.ball t₀ ε)` using `ContinuousOn.finset_sup'_apply Finset.univ_nonempty fun o _ => hc o`.

Conclude with `hs.congr heq`. Use `⟨hL, GlobalTheory.CompanionTheory.AnForm.PshLocal.isPsh_of_locally n U _ hU fun z hz => ?_, continuousOn_of_locally_continuousOn fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨W, h1, h2, h3, -⟩` from `hloc z hz`. Conclude with `⟨U ∩ W, hU.inter h1, ⟨hz, h2⟩, h3⟩`. Take `⟨W, h1, h2, -, h4⟩` from `hloc z hz`.

Conclude with `⟨W, h1, h2, h4⟩`.
-/
theorem _root_.GlobalTheory.CompanionTheory.Relay.log_det_eigen_frame_plurisubharmonic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (n : ℕ) (U : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ) (b : Ψ → Fin m → (Fin n → ℂ) → Fin g → ℂ), IsOpen U → IsHolFam U R → IsCMFam σ → IsEigFrames U (fun t => (R t).B) σ b → ReciprocityTheory.AnForm.A.IsPsh U (fun t => (R t).logDet (fun τ i => b τ i t)) ∧ ReciprocityTheory.AnForm.A.IsPsh U (fun t => (R t).logDet (fun τ i => b τ i t) + (R t).cuspW σ) ∧ ContinuousOn (fun t => (R t).cuspW σ) U := by
  intro E _ _ _ g Λ _ _ Ψ _ n U R σ m b hU hH hσ hb
  have hrank : ∀ t ∈ U, (R t).HasRank σ m := by
    intro t ht τ
    have h := hb.2 t ht τ
    have e : Module.finrank ℂ (Submodule.span ℂ (Set.range fun i => b τ i t)) = m := by
      rw [finrank_span_eq_card h.1, Fintype.card_fin]
    rw [h.2] at e
    exact e
  have hL : ReciprocityTheory.AnForm.A.IsPsh U (fun t => (R t).logDet (fun τ i => b τ i t)) :=
    psh_sum Finset.univ fun τ _ =>
      (GlobalTheory.CompanionTheory.Relay.holomorphic_family_smooth_entries E g Λ Ψ n U R hU hH).2.2 m (b τ) (hb.1 τ) (fun t ht => (hb.2 t ht τ).1)
  have hloc : ∀ t₀ ∈ U, ∃ W : Set (Fin n → ℂ), IsOpen W ∧ t₀ ∈ W ∧
      ReciprocityTheory.AnForm.A.IsPsh (U ∩ W) (fun t => (R t).logDet (fun τ i => b τ i t) + (R t).cuspW σ) ∧
      ContinuousOn (fun t => (R t).cuspW σ) (U ∩ W) := by
    intro t₀ ht₀
    obtain ⟨ε, F, hε, hF⟩ := GlobalTheory.T.cusp_submodules_locally_finite E g Λ Ψ n U R σ m hU hH hσ hrank t₀ ht₀
    have hVo : IsOpen (U ∩ Metric.ball t₀ ε) := hU.inter Metric.isOpen_ball
    have hVU : U ∩ Metric.ball t₀ ε ⊆ U := Set.inter_subset_left
    have hphi := fun I : F => GlobalTheory.T.log_det_cusp_frame_plurisubharmonic E g Λ Ψ n (U ∩ Metric.ball t₀ ε) R σ m b I.1 hVo
      ⟨fun t ht t' ht' => hH.1 t ht.1 t' ht'.1, fun x => (hH.2 x).mono hVU⟩ hσ
      ⟨fun τ i => (hb.1 τ i).mono hVU, fun t ht => hb.2 t ht.1⟩ (fun t ht => (hF t ht).1 I.1 I.2)
    have heq : ∀ t ∈ U ∩ Metric.ball t₀ ε,
        (R t).cuspW σ = Finset.univ.sup' Finset.univ_nonempty (term (R t) σ F) :=
      fun t ht => cuspW_eq (R t) σ F (hF t ht).1 (hF t ht).2
    refine ⟨Metric.ball t₀ ε, Metric.isOpen_ball, Metric.mem_ball_self hε, ?_, ?_⟩
    · have hs := ReciprocityTheory.AnForm.A.isPsh_sup_thm n (Option F) (U ∩ Metric.ball t₀ ε)
        (fun o t => (R t).logDet (fun τ i => b τ i t) + term (R t) σ F o) hVo (fun o => by
          cases o with
          | none =>
            exact psh_congr (fun z _ => (add_zero _).symm) (GlobalTheory.CompanionTheory.AnForm.PshLocal.isPsh_mono hVU hL)
          | some I => exact psh_congr (fun z _ => sub_eq_add_neg _ _) (hphi I).1)
      refine psh_congr (fun t ht => ?_) hs
      rw [heq t ht]
      exact add_sup _ _
    · have hc : ∀ o : Option F, ContinuousOn (fun t => term (R t) σ F o) (U ∩ Metric.ball t₀ ε) := by
        intro o
        cases o with
        | none => exact continuousOn_const
        | some I =>
          refine ContinuousOn.neg ((hphi I).2.log fun t ht => ?_)
          have hI := (hF t ht).1 I.1 I.2
          obtain ⟨⟨r, v, hv⟩, h2⟩ := GlobalTheory.T.isotropic_sublattice_covolume_positive E g Λ Ψ (R t) σ I.1 hσ hI.2.2 hI.1
          exact (h2 r v hv).2.1.ne'
      have hs : ContinuousOn (fun t => Finset.univ.sup' Finset.univ_nonempty (fun o => term (R t) σ F o))
          (U ∩ Metric.ball t₀ ε) :=
        ContinuousOn.finset_sup'_apply Finset.univ_nonempty fun o _ => hc o
      exact hs.congr heq
  refine ⟨hL, GlobalTheory.CompanionTheory.AnForm.PshLocal.isPsh_of_locally n U _ hU fun z hz => ?_,
    continuousOn_of_locally_continuousOn fun z hz => ?_⟩
  · obtain ⟨W, h1, h2, h3, -⟩ := hloc z hz
    exact ⟨U ∩ W, hU.inter h1, ⟨hz, h2⟩, h3⟩
  · obtain ⟨W, h1, h2, -, h4⟩ := hloc z hz
    exact ⟨W, h1, h2, h4⟩
