import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ProperActionOrbitMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupProjectionsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyRealStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresContinuityStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresInvariantStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleCompactSetsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramMatrixLocalGlobalStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjectionsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountableStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionArtinianRingStatement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PiDens

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.FactS

section Abstract

variable {ι : Type} [Fintype ι]
  {G₀ : Type} [Group G₀] [TopologicalSpace G₀] [IsTopologicalGroup G₀] [T2Space G₀]
  [LocallyCompactSpace G₀] [SecondCountableTopology G₀]
  {G : ι → Type} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
  [∀ i, T2Space (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, SecondCountableTopology (G i)]
  {W₀ : Type} [TopologicalSpace W₀] [T2Space W₀] [LocallyCompactSpace W₀]
  [SecondCountableTopology W₀] [MeasurableSpace W₀] [BorelSpace W₀]
  {W : ι → Type} [∀ i, TopologicalSpace (W i)] [∀ i, T2Space (W i)] [∀ i, LocallyCompactSpace (W i)]
  [∀ i, SecondCountableTopology (W i)] [∀ i, MeasurableSpace (W i)] [∀ i, BorelSpace (W i)]

/- English proof (translation)
Establish `hmeas₀ : ∀ g, Measurable (a₀ g)` using `fun g => (hc₀.comp (Continuous.prodMk_right g)).measurable`. Establish `hmeas : ∀ i g, Measurable (a i g)` using `fun i g => ((hc i).comp (Continuous.prodMk_right g)).measurable`. Distinguish the cases in `hne : (Z₀ ×ˢ Set.univ.pi Z).Nonempty`. Take `⟨⟨x₀, x⟩, hx₀, hx⟩` from `hne`. Establish `hxi : ∀ i, x i ∈ Z i` using `fun i => hx i (Set.mem_univ i)`.

Use `letI : MeasurableSpace (G₀ × ∀ i, G i) := borel _`. Use `haveI : BorelSpace (G₀ × ∀ i, G i) := ⟨rfl⟩`. Establish `hνinv : ∀ g : G₀ × ∀ i, G i, (m₀.prod (Measure.pi m)).map (fun x => (a₀ g.1 x.1, fun i => a i (g.2 i) (x.2 i))) = m₀.prod (Measure.pi m)`. Introduce `g`. Establish `hp : Measurable fun z : ∀ i, W i => fun i => a i (g.2 i) (z i)` using `measurable_pi_lambda _ fun i => (hmeas i (g.2 i)).comp (measurable_pi_apply i)`.

Establish `e` using `Measure.map_prod_map m₀ (Measure.pi m) (hmeas₀ g.1) hp`. Establish `e2 : (Measure.pi m).map (fun z i => a i (g.2 i) (z i)) = Measure.pi m`. Establish `: ∀ i, SigmaFinite ((m i).map (a i (g.2 i)))` using `fun i => by`. Rewrite using `[hi i]`. Use `infer_instance`.

Rewrite using `[Measure.pi_map_pi (fun i => (hmeas i (g.2 i)).aemeasurable)]`. Simplify using `only [hi]`. Rewrite `e` using `[e2, hi₀]`. Conclude with `e.symm`. Establish `hνZ : (m₀.prod (Measure.pi m)) (Z₀ ×ˢ Set.univ.pi Z)ᶜ = 0`.

Establish `A : ∀ᵐ y ∂(m₀.prod (Measure.pi m)), y.1 ∈ Z₀` using `Measure.quasiMeasurePreserving_fst.ae (measure_eq_zero_iff_ae_notMem.mp hz₀ |>.mono fun y h => by simpa using h)`. Establish `B : ∀ᵐ y ∂(m₀.prod (Measure.pi m)), ∀ i, y.2 i ∈ Z i`. Rewrite using `[ae_all_iff]`. Introduce `i`. Establish `B1 : ∀ᵐ z ∂(Measure.pi m), z i ∈ Z i` using `(Measure.quasiMeasurePreserving_eval m i).ae (measure_eq_zero_iff_ae_notMem.mp (hz i) |>.mono fun y h => by simpa using h)`.

Conclude with `Measure.quasiMeasurePreserving_snd.ae B1`. Use `A.and B` as an intermediate fact. Use `measure_eq_zero_iff_ae_notMem.mpr (this.mono fun y hy => ?_)` and prove the remaining obligations. Simplify using `using (show y ∈ Z₀ ×ˢ Set.univ.pi Z from ⟨hy.1, fun i _ => hy.2 i⟩)`. Establish `hνne : m₀.prod (Measure.pi m) ≠ 0`.

Introduce `h0`. Establish `e1 : (m₀.prod (Measure.pi m)) (Set.univ ×ˢ Set.univ) = 0` using `by rw [h0]; simp`. Rewrite `e1` using `[Measure.prod_prod, Measure.pi_univ, mul_eq_zero, Finset.prod_eq_zero_iff]`. Break down `e1 with e1 | ⟨i, -, e1⟩` into its components or cases. Conclude with `hn₀ ⟨x₀, hx₀⟩ (Measure.measure_univ_eq_zero.mp e1)`.

Conclude with `hn i ⟨x i, hxi i⟩ (Measure.measure_univ_eq_zero.mp e1)`. Take `⟨c, hcP⟩` from `GlobalTheory.T.proper_action_orbit_measure (G₀ × ∀ i, G i) (W₀ × ∀ i, W i) (fun g x => (a₀ g.1 x.1, fun i => a i (g.2 i) (x.2 i))) (by`. Use `Continuous.prodMk ?_ (continuous_pi fun i => ?_)` and prove the remaining obligations. Conclude with `hc₀.comp ((continuous_fst.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd))`. Conclude with `(hc i).comp ((((continuous_apply i).comp continuous_snd).comp continuous_fst).prodMk ((continuous_apply i).comp (continuous_snd.comp continuous_snd))))`.

Apply the tactic sequence `(by intro y; ext <;> simp [h1₀, h1])`. Apply the tactic sequence `(by intro g h y; ext <;> simp [hm₀, hm])`. Use the proof step `(Z₀ ×ˢ Set.univ.pi Z) (hZ₀.prod (isClosed_set_pi fun i _ => hZ i))`. Use the proof step `(fun g y hy => ⟨hs₀ _ _ hy.1, fun i _ => hs i _ _ (hy.2 i (Set.mem_univ i))⟩)`. Use the proof step `(fun y hy y' hy' => by`.

Take `⟨g₀, e₀⟩` from `ht₀ _ hy.1 _ hy'.1`. Use `choose g e using fun i => ht i _ (hy.2 i (Set.mem_univ i)) _ (hy'.2 i (Set.mem_univ i))`. Conclude with `⟨(g₀, g), Prod.ext e₀ (funext e)⟩)`. Use `P (m₀.prod (Measure.pi m)) inferInstance inferInstance hPZ hνZ (fun g => hP g.1 g.2) hνinv hνne`. Use `⟨c, fun f₀ f hf₀ hf => ?_⟩` and prove the remaining obligations.

Rewrite using `[hcP, lintegral_smul_measure, lintegral_prod_mul (f := f₀) (g := fun z : ∀ i, W i => ∏ i, f i (z i)) hf₀.aemeasurable (Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)).aemeasurable, PI.AprimeInfG.lintegral_fintype_prod f hf]`. Both sides reduce to the same expression. Establish `hemp : Z₀ ×ˢ Set.univ.pi Z = ∅` using `Set.not_nonempty_iff_eq_empty.mp hne`. Establish `hP0 : P = 0`. Rewrite `hPZ` using `[hemp, Set.compl_empty]`.

Conclude with `Measure.measure_univ_eq_zero.mp hPZ`. Use `⟨0, fun f₀ f _ _ => ?_⟩` and prove the remaining obligations. Simplify using `[hP0]`.
-/
theorem prod_factor
    (a₀ : G₀ → W₀ → W₀) (a : ∀ i, G i → W i → W i)
    (hc₀ : Continuous fun p : G₀ × W₀ => a₀ p.1 p.2) (h1₀ : ∀ x, a₀ 1 x = x)
    (hm₀ : ∀ g h x, a₀ (g * h) x = a₀ g (a₀ h x))
    (hc : ∀ i, Continuous fun p : G i × W i => a i p.1 p.2) (h1 : ∀ i x, a i 1 x = x)
    (hm : ∀ i g h x, a i (g * h) x = a i g (a i h x))
    (Z₀ : Set W₀) (Z : ∀ i, Set (W i)) (hZ₀ : IsClosed Z₀) (hZ : ∀ i, IsClosed (Z i))
    (hs₀ : ∀ g, ∀ x ∈ Z₀, a₀ g x ∈ Z₀) (hs : ∀ i g, ∀ x ∈ Z i, a i g x ∈ Z i)
    (ht₀ : ∀ x ∈ Z₀, ∀ y ∈ Z₀, ∃ g, a₀ g x = y) (ht : ∀ i, ∀ x ∈ Z i, ∀ y ∈ Z i, ∃ g, a i g x = y)
    (m₀ : Measure W₀) (m : ∀ i, Measure (W i)) [IsLocallyFiniteMeasure m₀]
    [∀ i, IsLocallyFiniteMeasure (m i)]
    (hi₀ : ∀ g, m₀.map (a₀ g) = m₀) (hi : ∀ i g, (m i).map (a i g) = m i)
    (hz₀ : m₀ Z₀ᶜ = 0) (hz : ∀ i, m i (Z i)ᶜ = 0)
    (hn₀ : Z₀.Nonempty → m₀ ≠ 0) (hn : ∀ i, (Z i).Nonempty → m i ≠ 0)
    (P : Measure (W₀ × ∀ i, W i)) [IsLocallyFiniteMeasure P]
    (hP : ∀ (g₀ : G₀) (g : ∀ i, G i),
      P.map (fun x => (a₀ g₀ x.1, fun i => a i (g i) (x.2 i))) = P)
    (hPZ : P (Z₀ ×ˢ Set.univ.pi Z)ᶜ = 0) :
    ∃ c : ℝ≥0, ∀ (f₀ : W₀ → ℝ≥0∞) (f : ∀ i, W i → ℝ≥0∞), Measurable f₀ →
      (∀ i, Measurable (f i)) →
      ∫⁻ x, f₀ x.1 * ∏ i, f i (x.2 i) ∂P =
        (c : ℝ≥0∞) * ((∫⁻ x, f₀ x ∂m₀) * ∏ i, ∫⁻ x, f i x ∂(m i)) := by
  classical
  have hmeas₀ : ∀ g, Measurable (a₀ g) := fun g =>
    (hc₀.comp (Continuous.prodMk_right g)).measurable
  have hmeas : ∀ i g, Measurable (a i g) := fun i g =>
    ((hc i).comp (Continuous.prodMk_right g)).measurable
  by_cases hne : (Z₀ ×ˢ Set.univ.pi Z).Nonempty
  · obtain ⟨⟨x₀, x⟩, hx₀, hx⟩ := hne
    have hxi : ∀ i, x i ∈ Z i := fun i => hx i (Set.mem_univ i)
    letI : MeasurableSpace (G₀ × ∀ i, G i) := borel _
    haveI : BorelSpace (G₀ × ∀ i, G i) := ⟨rfl⟩
    have hνinv : ∀ g : G₀ × ∀ i, G i,
        (m₀.prod (Measure.pi m)).map
          (fun x => (a₀ g.1 x.1, fun i => a i (g.2 i) (x.2 i))) = m₀.prod (Measure.pi m) := by
      intro g
      have hp : Measurable fun z : ∀ i, W i => fun i => a i (g.2 i) (z i) :=
        measurable_pi_lambda _ fun i => (hmeas i (g.2 i)).comp (measurable_pi_apply i)
      have e := Measure.map_prod_map m₀ (Measure.pi m) (hmeas₀ g.1) hp
      have e2 : (Measure.pi m).map (fun z i => a i (g.2 i) (z i)) = Measure.pi m := by
        have : ∀ i, SigmaFinite ((m i).map (a i (g.2 i))) := fun i => by
          rw [hi i]; infer_instance
        rw [Measure.pi_map_pi (fun i => (hmeas i (g.2 i)).aemeasurable)]
        simp only [hi]
      rw [e2, hi₀] at e
      exact e.symm
    have hνZ : (m₀.prod (Measure.pi m)) (Z₀ ×ˢ Set.univ.pi Z)ᶜ = 0 := by
      have A : ∀ᵐ y ∂(m₀.prod (Measure.pi m)), y.1 ∈ Z₀ :=
        Measure.quasiMeasurePreserving_fst.ae (measure_eq_zero_iff_ae_notMem.mp hz₀ |>.mono fun y h => by simpa using h)
      have B : ∀ᵐ y ∂(m₀.prod (Measure.pi m)), ∀ i, y.2 i ∈ Z i := by
        rw [ae_all_iff]
        intro i
        have B1 : ∀ᵐ z ∂(Measure.pi m), z i ∈ Z i :=
          (Measure.quasiMeasurePreserving_eval m i).ae
            (measure_eq_zero_iff_ae_notMem.mp (hz i) |>.mono fun y h => by simpa using h)
        exact Measure.quasiMeasurePreserving_snd.ae B1
      have := A.and B
      refine measure_eq_zero_iff_ae_notMem.mpr (this.mono fun y hy => ?_)
      simpa using (show y ∈ Z₀ ×ˢ Set.univ.pi Z from ⟨hy.1, fun i _ => hy.2 i⟩)
    have hνne : m₀.prod (Measure.pi m) ≠ 0 := by
      intro h0
      have e1 : (m₀.prod (Measure.pi m)) (Set.univ ×ˢ Set.univ) = 0 := by rw [h0]; simp
      rw [Measure.prod_prod, Measure.pi_univ, mul_eq_zero, Finset.prod_eq_zero_iff] at e1
      rcases e1 with e1 | ⟨i, -, e1⟩
      · exact hn₀ ⟨x₀, hx₀⟩ (Measure.measure_univ_eq_zero.mp e1)
      · exact hn i ⟨x i, hxi i⟩ (Measure.measure_univ_eq_zero.mp e1)
    obtain ⟨c, hcP⟩ := GlobalTheory.T.proper_action_orbit_measure (G₀ × ∀ i, G i) (W₀ × ∀ i, W i)
      (fun g x => (a₀ g.1 x.1, fun i => a i (g.2 i) (x.2 i)))
      (by
        refine Continuous.prodMk ?_ (continuous_pi fun i => ?_)
        · exact hc₀.comp ((continuous_fst.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd))
        · exact (hc i).comp ((((continuous_apply i).comp continuous_snd).comp continuous_fst).prodMk
            ((continuous_apply i).comp (continuous_snd.comp continuous_snd))))
      (by intro y; ext <;> simp [h1₀, h1])
      (by intro g h y; ext <;> simp [hm₀, hm])
      (Z₀ ×ˢ Set.univ.pi Z) (hZ₀.prod (isClosed_set_pi fun i _ => hZ i))
      (fun g y hy => ⟨hs₀ _ _ hy.1, fun i _ => hs i _ _ (hy.2 i (Set.mem_univ i))⟩)
      (fun y hy y' hy' => by
        obtain ⟨g₀, e₀⟩ := ht₀ _ hy.1 _ hy'.1
        choose g e using fun i => ht i _ (hy.2 i (Set.mem_univ i)) _ (hy'.2 i (Set.mem_univ i))
        exact ⟨(g₀, g), Prod.ext e₀ (funext e)⟩)
      P (m₀.prod (Measure.pi m)) inferInstance inferInstance hPZ hνZ (fun g => hP g.1 g.2) hνinv hνne
    refine ⟨c, fun f₀ f hf₀ hf => ?_⟩
    rw [hcP, lintegral_smul_measure,
      lintegral_prod_mul (f := f₀) (g := fun z : ∀ i, W i => ∏ i, f i (z i)) hf₀.aemeasurable
        (Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)).aemeasurable,
      PI.AprimeInfG.lintegral_fintype_prod f hf]
    rfl
  · have hemp : Z₀ ×ˢ Set.univ.pi Z = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hP0 : P = 0 := by
      rw [hemp, Set.compl_empty] at hPZ
      exact Measure.measure_univ_eq_zero.mp hPZ
    refine ⟨0, fun f₀ f _ _ => ?_⟩
    simp [hP0]

end Abstract

section Concrete

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Introduce `a i k`. Establish `e : (N : Fv F v ⊗[F] E) * Y a i = N • Y a i` using `(nsmul_eq_mul _ _).symm`. Simplify using `only [e, map_nsmul, Finsupp.smul_apply]`. Conclude with `nsmul_mem (hY a i k) N`.
-/
theorem lat_natMul {d M n : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (Y : Fin n → Fin M → Fv F v ⊗[F] E) (hY : Y ∈ latV b v) (N : ℕ) :
    (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v := by
  intro a i k
  have e : (N : Fv F v ⊗[F] E) * Y a i = N • Y a i := (nsmul_eq_mul _ _).symm
  simp only [e, map_nsmul, Finsupp.smul_apply]
  exact nsmul_mem (hY a i k) N

/- English proof (translation)
Introduce `a i k`. Simplify using `only [Pi.zero_apply, map_zero, Finsupp.coe_zero]`. Conclude with `zero_mem _`.
-/
theorem zero_mem_lat {d M n : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    (0 : Fin n → Fin M → Fv F v ⊗[F] E) ∈ latV b v := by
  intro a i k
  simp only [Pi.zero_apply, map_zero, Finsupp.coe_zero]
  exact zero_mem _

/- English proof (translation)
Take `⟨tr, lc, sc, t2, -⟩` from `GlobalTheory.T.completion_is_local_ring F v`. Establish `tk` using `GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)`. Use `haveI := tk.1`. Take `⟨-, -, -, hlat, -, -, -, hglue, -⟩` from `GlobalTheory.T.adelic_tuple_projections F E σ hσ d b n M`. Establish `hpt : ∀ Y : Fin n → Fin M → Fv F v ⊗[F] E, ∃ N : ℕ, 0 < N ∧ (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v`.

Introduce `Y`. Establish `hev : ∀ᶠ w in Filter.cofinite, (Pi.single v Y : ∀ w : HeightOneSpectrum (𝓞 F), Fin n → Fin M → Fv F w ⊗[F] E) w ∈ latV b w`. Rewrite using `[Filter.eventually_cofinite]`. Use `(Set.finite_singleton v).subset fun w hw => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Apply `hw` to reduce the goal to its premises. Rewrite using `[Pi.single_eq_of_ne (by simpa using hne)]`. Conclude with `zero_mem_lat b w`. Take `⟨X, -, hX⟩` from `hglue 0 _ hev`. Take `⟨N, r, hN, -, h⟩` from `(GlobalTheory.T.adelic_tuple_compact_sets F E σ hσ d b n M).2 {X} isCompact_singleton`.

Use `⟨N, hN, ?_⟩` and prove the remaining obligations. Use `(h X rfl).1 v` as an intermediate fact. Rewrite `this` using `[hX, Pi.single_eq_same]`. Then use the resulting hypothesis. Set `A : ℕ → Set (Fin n → Fin M → Fv F v ⊗[F] E)` to `fun k => {Y | (fun a i => ((k + 1 : ℕ) : Fv F v ⊗[F] E) * Y a i) ∈ latV b v}`. Establish `hAo : ∀ k, IsOpen (A k)` using `fun k => by`.

Establish `hc : Continuous fun (Y : Fin n → Fin M → Fv F v ⊗[F] E) (a : Fin n) (i : Fin M) => ((k + 1 : ℕ) : Fv F v ⊗[F] E) * Y a i` using `continuous_pi fun a => continuous_pi fun i => continuous_const.mul ((continuous_apply i).comp (continuous_apply a))`. Conclude with `hc.isOpen_preimage _ (hlat v).2`. Establish `hcov : K ⊆ ⋃ k, A k`. Introduce `Y _`. Take `⟨N, hN, hY⟩` from `hpt Y`.

Use `Set.mem_iUnion.mpr ⟨N - 1, ?_⟩` and prove the remaining obligations. Use `show _ ∈ latV b v`. Rewrite using `[Nat.sub_add_cancel hN]` and apply the resulting hypothesis. Take `⟨t, ht⟩` from `hK.elim_finite_subcover A hAo hcov`. Use `⟨∏ k ∈ t, (k + 1), Finset.prod_pos fun k _ => Nat.succ_pos k, fun Y hY => ?_⟩` and prove the remaining obligations.

Take `⟨k, hk, hYk⟩ : ∃ k ∈ t, Y ∈ A k` from `by simpa using ht hY`. Take `⟨q, hq⟩` from `Finset.dvd_prod_of_mem (fun k => k + 1) hk`. Establish `h` using `lat_natMul b v _ hYk q`. Establish `e : (fun a i => ((∏ k ∈ t, (k + 1) : ℕ) : Fv F v ⊗[F] E) * Y a i) = fun a i => (q : Fv F v ⊗[F] E) * (((k + 1 : ℕ) : Fv F v ⊗[F] E) * Y a i)`. Use function extensionality and compare the values at `a i`.

Rewrite using `[hq, Nat.cast_mul, ← mul_assoc, mul_comm ((k + 1 : ℕ) : Fv F v ⊗[F] E)]`. Rewrite using `[e]`. Conclude with `h`.
-/
theorem exists_scale (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (n M : ℕ) (v : HeightOneSpectrum (𝓞 F)) (K : Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hK : IsCompact K) :
    ∃ N : ℕ, 0 < N ∧ ∀ Y ∈ K, (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v := by
  classical
  obtain ⟨tr, lc, sc, t2, -⟩ := GlobalTheory.T.completion_is_local_ring F v
  have tk := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)
  haveI := tk.1
  obtain ⟨-, -, -, hlat, -, -, -, hglue, -⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hσ d b n M
  have hpt : ∀ Y : Fin n → Fin M → Fv F v ⊗[F] E, ∃ N : ℕ, 0 < N ∧
      (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v := by
    intro Y
    have hev : ∀ᶠ w in Filter.cofinite,
        (Pi.single v Y : ∀ w : HeightOneSpectrum (𝓞 F), Fin n → Fin M → Fv F w ⊗[F] E) w ∈
          latV b w := by
      rw [Filter.eventually_cofinite]
      refine (Set.finite_singleton v).subset fun w hw => ?_
      by_contra hne
      apply hw
      rw [Pi.single_eq_of_ne (by simpa using hne)]
      exact zero_mem_lat b w
    obtain ⟨X, -, hX⟩ := hglue 0 _ hev
    obtain ⟨N, r, hN, -, h⟩ := (GlobalTheory.T.adelic_tuple_compact_sets F E σ hσ d b n M).2 {X} isCompact_singleton
    refine ⟨N, hN, ?_⟩
    have := (h X rfl).1 v
    rwa [hX, Pi.single_eq_same] at this
  let A : ℕ → Set (Fin n → Fin M → Fv F v ⊗[F] E) := fun k =>
    {Y | (fun a i => ((k + 1 : ℕ) : Fv F v ⊗[F] E) * Y a i) ∈ latV b v}
  have hAo : ∀ k, IsOpen (A k) := fun k => by
    have hc : Continuous fun (Y : Fin n → Fin M → Fv F v ⊗[F] E) (a : Fin n) (i : Fin M) =>
        ((k + 1 : ℕ) : Fv F v ⊗[F] E) * Y a i :=
      continuous_pi fun a => continuous_pi fun i =>
        continuous_const.mul ((continuous_apply i).comp (continuous_apply a))
    exact hc.isOpen_preimage _ (hlat v).2
  have hcov : K ⊆ ⋃ k, A k := by
    intro Y _
    obtain ⟨N, hN, hY⟩ := hpt Y
    refine Set.mem_iUnion.mpr ⟨N - 1, ?_⟩
    show _ ∈ latV b v
    rwa [Nat.sub_add_cancel hN]
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover A hAo hcov
  refine ⟨∏ k ∈ t, (k + 1), Finset.prod_pos fun k _ => Nat.succ_pos k, fun Y hY => ?_⟩
  obtain ⟨k, hk, hYk⟩ : ∃ k ∈ t, Y ∈ A k := by simpa using ht hY
  obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (fun k => k + 1) hk
  have h := lat_natMul b v _ hYk q
  have e : (fun a i => ((∏ k ∈ t, (k + 1) : ℕ) : Fv F v ⊗[F] E) * Y a i) =
      fun a i => (q : Fv F v ⊗[F] E) * (((k + 1 : ℕ) : Fv F v ⊗[F] E) * Y a i) := by
    funext a i
    rw [hq, Nat.cast_mul, ← mul_assoc, mul_comm ((k + 1 : ℕ) : Fv F v ⊗[F] E)]
  rw [e]
  exact h

def pr {n M : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F))) (X : Fin n → Fin M → AF F ⊗[F] E) :
    (Fin n → Fin M → Ainf F ⊗[F] E) × ∀ v : S, Fin n → Fin M → Fv F v.1 ⊗[F] E :=
  (projInf X, fun v => projV v.1 (projFin X))

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, -, hsz⟩` from `GlobalTheory.T.adelic_tuple_projections F E σ hσ d b n M`. Establish `hK₀ : IsCompact (Prod.fst '' K)` using `hK.image continuous_fst`. Establish `hKv : ∀ v : S, IsCompact ((fun x => x.2 v) '' K)` using `fun v => hK.image ((continuous_apply v).comp continuous_snd)`. Take `⟨r, hr⟩` from `(hK₀.image hsz).bddAbove`. Use `choose N hN hNK using fun v : S => exists_scale σ hσ b n M v.1 _ (hKv v)`.

Establish `hL : 0 < ∏ v : S, N v` using `Finset.prod_pos fun v _ => hN v`. Establish `hcpt` using `(GlobalTheory.T.adelic_tuple_compact_sets F E σ hσ d b n M).1 (∏ v : S, N v) r hL`. Use `lt_of_le_of_lt (measure_mono ?_) hcpt.measure_lt_top` and prove the remaining obligations. Introduce and unpack `X ⟨hXK, hXo⟩`. Use `⟨fun v => ?_, hr ⟨_, ⟨_, hXK, rfl⟩, rfl⟩⟩` and prove the remaining obligations.

Distinguish the cases in `hv : v ∈ S`. Take `⟨q, hq⟩` from `Finset.dvd_prod_of_mem N (Finset.mem_univ (⟨v, hv⟩ : S))`. Establish `h` using `lat_natMul b v _ (hNK ⟨v, hv⟩ _ ⟨_, hXK, rfl⟩) q`. Establish `e : (fun a i => ((∏ w : S, N w : ℕ) : Fv F v ⊗[F] E) * projV v (projFin X) a i) = fun a i => (q : Fv F v ⊗[F] E) * ((N ⟨v, hv⟩ : Fv F v ⊗[F] E) * projV v (projFin X) a i)`. Use function extensionality and compare the values at `a i`.

Rewrite using `[hq, Nat.cast_mul, ← mul_assoc, mul_comm (N ⟨v, hv⟩ : Fv F v ⊗[F] E)]`. Rewrite using `[e]`. Conclude with `h`. Conclude with `lat_natMul b v _ (hXo v hv) _`.
-/
theorem preimage_lt_top (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    {n M : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F))) (I : Measure (Fin n → Fin M → AF F ⊗[F] E))
    [IsLocallyFiniteMeasure I]
    (K : Set ((Fin n → Fin M → Ainf F ⊗[F] E) × ∀ v : S, Fin n → Fin M → Fv F v.1 ⊗[F] E))
    (hK : IsCompact K) : I (pr S ⁻¹' K ∩ intOff b S) < ⊤ := by
  classical
  obtain ⟨-, -, -, -, -, -, -, -, hsz⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hσ d b n M
  have hK₀ : IsCompact (Prod.fst '' K) := hK.image continuous_fst
  have hKv : ∀ v : S, IsCompact ((fun x => x.2 v) '' K) := fun v =>
    hK.image ((continuous_apply v).comp continuous_snd)
  obtain ⟨r, hr⟩ := (hK₀.image hsz).bddAbove
  choose N hN hNK using fun v : S => exists_scale σ hσ b n M v.1 _ (hKv v)
  have hL : 0 < ∏ v : S, N v := Finset.prod_pos fun v _ => hN v
  have hcpt := (GlobalTheory.T.adelic_tuple_compact_sets F E σ hσ d b n M).1 (∏ v : S, N v) r hL
  refine lt_of_le_of_lt (measure_mono ?_) hcpt.measure_lt_top
  rintro X ⟨hXK, hXo⟩
  refine ⟨fun v => ?_, hr ⟨_, ⟨_, hXK, rfl⟩, rfl⟩⟩
  by_cases hv : v ∈ S
  · obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ (⟨v, hv⟩ : S))
    have h := lat_natMul b v _ (hNK ⟨v, hv⟩ _ ⟨_, hXK, rfl⟩) q
    have e : (fun a i => ((∏ w : S, N w : ℕ) : Fv F v ⊗[F] E) * projV v (projFin X) a i) =
        fun a i => (q : Fv F v ⊗[F] E) *
          ((N ⟨v, hv⟩ : Fv F v ⊗[F] E) * projV v (projFin X) a i) := by
      funext a i
      rw [hq, Nat.cast_mul, ← mul_assoc, mul_comm (N ⟨v, hv⟩ : Fv F v ⊗[F] E)]
    rw [e]
    exact h
  · exact lat_natMul b v _ (hXo v hv) _

/- English proof (translation)
Take `⟨pinf, p, hcomp, -, hex⟩` from `GlobalTheory.T.adelic_unitary_group_projections F E σ hσ M J hJ`. Take `⟨h, hh₀, hhS, hhO⟩` from `hex S g₀ (fun v => if hv : v ∈ S then g ⟨v, hv⟩ else 1)`. Establish `hpre : actW (AF F) σ J h ⁻¹' (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E)) = intOff b S`. Use extensionality with `X`. Establish `key : ∀ v, v ∉ S → projV v (projFin (actW (AF F) σ J h X)) = projV v (projFin X)`.

Introduce `v hv`. Rewrite using `[(hcomp n h X).2 v, hhO v hv, hone]`. Prove the components needed by the constructor for the conclusion. Introduce `hX v hv`. Rewrite using `[← key v hv]`.

Conclude with `hX v hv`. Introduce `hX v hv show projV v (projFin (actW (AF F) σ J h X)) ∈ latV b v`. Rewrite using `[key v hv]`. Conclude with `hX v hv`. Establish `hres : (I.restrict (intOff b S)).map (actW (AF F) σ J h) = I.restrict (intOff b S)`.

Use `Measure.restrict_map (μ := I) (hf h) hint` as an intermediate fact. Rewrite `this` using `[hI h, hpre]`. Conclude with `this.symm`. Rewrite using `[Measure.map_map hA hpr]`. Establish `e : ((fun x : (Fin n → Fin M → Ainf F ⊗[F] E) × ∀ v : S, Fin n → Fin M → Fv F v.1 ⊗[F] E => (actW (Ainf F) σ J g₀ x.1, fun v => actW (Fv F v.1) σ J (g v) (x.2 v))) ∘ pr S) = pr S ∘ actW (AF F) σ J h`.

Use function extensionality and compare the values at `X`. Use `Prod.ext ?_ (funext fun v => ?_)` and prove the remaining obligations. Use `show actW (Ainf F) σ J g₀ (projInf X) = projInf (actW (AF F) σ J h X)`. Rewrite using `[(hcomp n h X).1, hh₀]`. Use `show actW (Fv F v.1) σ J (g v) (projV v.1 (projFin X)) = projV v.1 (projFin (actW (AF F) σ J h X))`.

Rewrite using `[(hcomp n h X).2 v.1, hhS v.1 v.2, dif_pos v.2]`. Rewrite using `[e, ← Measure.map_map hpr (hf h), hres]`.
-/
theorem push_inv (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) {d : ℕ} (b : Module.Basis (Fin d) F E) {n : ℕ}
    (S : Finset (HeightOneSpectrum (𝓞 F))) (I : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (hI : ∀ h : HA (AF F) σ J, I.map (actW (AF F) σ J h) = I)
    (hone : ∀ (v : HeightOneSpectrum (𝓞 F)) (X : Fin n → Fin M → Fv F v ⊗[F] E),
      actW (Fv F v) σ J 1 X = X)
    (hpr : Measurable (pr S : (Fin n → Fin M → AF F ⊗[F] E) → _))
    (hf : ∀ h : HA (AF F) σ J, Measurable (actW (AF F) σ J h : (Fin n → Fin M → AF F ⊗[F] E) → _))
    (hint : MeasurableSet (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E)))
    (g₀ : HA (Ainf F) σ J) (g : ∀ v : S, HA (Fv F v.1) σ J)
    (hA : Measurable fun x : (Fin n → Fin M → Ainf F ⊗[F] E) ×
        ∀ v : S, Fin n → Fin M → Fv F v.1 ⊗[F] E =>
      (actW (Ainf F) σ J g₀ x.1, fun v => actW (Fv F v.1) σ J (g v) (x.2 v))) :
    ((I.restrict (intOff b S)).map (pr S)).map
      (fun x => (actW (Ainf F) σ J g₀ x.1, fun v => actW (Fv F v.1) σ J (g v) (x.2 v))) =
      (I.restrict (intOff b S)).map (pr S) := by
  classical
  obtain ⟨pinf, p, hcomp, -, hex⟩ := GlobalTheory.T.adelic_unitary_group_projections F E σ hσ M J hJ
  obtain ⟨h, hh₀, hhS, hhO⟩ := hex S g₀ (fun v => if hv : v ∈ S then g ⟨v, hv⟩ else 1)
  have hpre : actW (AF F) σ J h ⁻¹' (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E)) =
      intOff b S := by
    ext X
    have key : ∀ v, v ∉ S → projV v (projFin (actW (AF F) σ J h X)) = projV v (projFin X) := by
      intro v hv
      rw [(hcomp n h X).2 v, hhO v hv, hone]
    constructor
    · intro hX v hv
      rw [← key v hv]
      exact hX v hv
    · intro hX v hv
      show projV v (projFin (actW (AF F) σ J h X)) ∈ latV b v
      rw [key v hv]
      exact hX v hv
  have hres : (I.restrict (intOff b S)).map (actW (AF F) σ J h) = I.restrict (intOff b S) := by
    have := Measure.restrict_map (μ := I) (hf h) hint
    rw [hI h, hpre] at this
    exact this.symm
  rw [Measure.map_map hA hpr]
  have e : ((fun x : (Fin n → Fin M → Ainf F ⊗[F] E) × ∀ v : S, Fin n → Fin M → Fv F v.1 ⊗[F] E =>
      (actW (Ainf F) σ J g₀ x.1, fun v => actW (Fv F v.1) σ J (g v) (x.2 v))) ∘ pr S) =
      pr S ∘ actW (AF F) σ J h := by
    funext X
    refine Prod.ext ?_ (funext fun v => ?_)
    · show actW (Ainf F) σ J g₀ (projInf X) = projInf (actW (AF F) σ J h X)
      rw [(hcomp n h X).1, hh₀]
    · show actW (Fv F v.1) σ J (g v) (projV v.1 (projFin X)) =
        projV v.1 (projFin (actW (AF F) σ J h X))
      rw [(hcomp n h X).2 v.1, hhS v.1 v.2, dif_pos v.2]
  rw [e, ← Measure.map_map hpr (hf h), hres]

/- English proof (translation)
Take `⟨tr, lc, sc, t2, art, red, -⟩` from `id hR`. Use `haveI := tr`. Use `haveI := lc`. Use `haveI := sc`. Use `haveI := t2`.

Use `haveI := art`. Use `haveI := red`. Take `⟨-, hW, hH⟩` from `GlobalTheory.T.coordinate_haar_measure F E σ hσ R d b lam hlam`. Use `haveI := hW n M`. Use `haveI := hH n`.

Establish `hfin` using `GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hσ M J hJ R hR n _ _ m (hW n M) (hH n) hm (hermOf R σ T hT)`. Establish `hinv` using `GlobalTheory.T.gram_fiber_measures_invariant F E σ hσ M J hJ R hR n _ _ m (hW n M) (hH n) hm`. Establish `hunit : ∀ X : Fin n → Fin M → R ⊗[F] E, gramR R σ J X = T.map (inclR R) → IsUnit (gramR R σ J X).det`. Introduce `X hX`. Rewrite using `[hX]`.

Establish `e : (T.map (inclR (F` using `F) R)).det = inclR (F := F) R T.det := ((inclR (F := F) R).map_det T).symm`. Rewrite using `[e]`. Conclude with `(isUnit_iff_ne_zero.mpr hdet).map (inclR (F := F) R)`. Use `⟨hfin.1, fun h => hinv h _, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `measure_mono_null (Set.compl_subset_compl.mpr ?_) (hm.1 (hermOf R σ T hT))` and prove the remaining obligations.

Introduce and unpack `Y ⟨hY, -⟩`. Conclude with `hY`. Introduce and unpack `⟨X, hX⟩ h0`. Use `hfin.2 Set.univ isOpen_univ ⟨X, Set.mem_univ X, hX, hunit X hX⟩` as an intermediate fact. Conclude with `this (by rw [h0]; rfl)`.

Introduce `X hX Y hY`. Conclude with `GlobalTheory.T.witt_extension_artinian_ring F E σ hσ M J hJ R n X Y (hX.trans hY.symm) (hunit X hX)`.
-/
theorem local_pack (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [MeasurableSpace R] [BorelSpace R] (hR : IsLocR R) {n : ℕ} (T : Matrix (Fin n) (Fin n) E)
    (hT : ∀ a b, σ (T b a) = T a b) (hdet : T.det ≠ 0) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lam : Measure R) (hlam : lam.IsAddHaarMeasure)
    (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (hm : IsGramFib R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m) :
    IsLocallyFiniteMeasure (m (hermOf R σ T hT)) ∧
    (∀ h : HA R σ J, (m (hermOf R σ T hT)).map (actW R σ J h) = m (hermOf R σ T hT)) ∧
    m (hermOf R σ T hT) {Y | gramR R σ J Y = T.map (inclR R)}ᶜ = 0 ∧
    ({Y : Fin n → Fin M → R ⊗[F] E | gramR R σ J Y = T.map (inclR R)}.Nonempty →
      m (hermOf R σ T hT) ≠ 0) ∧
    (∀ X ∈ {Y : Fin n → Fin M → R ⊗[F] E | gramR R σ J Y = T.map (inclR R)},
      ∀ Y ∈ {Y : Fin n → Fin M → R ⊗[F] E | gramR R σ J Y = T.map (inclR R)},
      ∃ h : HA R σ J, actW R σ J h X = Y) := by
  obtain ⟨tr, lc, sc, t2, art, red, -⟩ := id hR
  haveI := tr
  haveI := lc
  haveI := sc
  haveI := t2
  haveI := art
  haveI := red
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ R d b lam hlam
  haveI := hW n M
  haveI := hH n
  have hfin := GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hσ M J hJ R hR n _ _ m (hW n M) (hH n) hm (hermOf R σ T hT)
  have hinv := GlobalTheory.T.gram_fiber_measures_invariant F E σ hσ M J hJ R hR n _ _ m (hW n M) (hH n) hm
  have hunit : ∀ X : Fin n → Fin M → R ⊗[F] E, gramR R σ J X = T.map (inclR R) →
      IsUnit (gramR R σ J X).det := by
    intro X hX
    rw [hX]
    have e : (T.map (inclR (F := F) R)).det = inclR (F := F) R T.det :=
      ((inclR (F := F) R).map_det T).symm
    rw [e]
    exact (isUnit_iff_ne_zero.mpr hdet).map (inclR (F := F) R)
  refine ⟨hfin.1, fun h => hinv h _, ?_, ?_, ?_⟩
  · refine measure_mono_null (Set.compl_subset_compl.mpr ?_) (hm.1 (hermOf R σ T hT))
    rintro Y ⟨hY, -⟩
    exact hY
  · rintro ⟨X, hX⟩ h0
    have := hfin.2 Set.univ isOpen_univ ⟨X, Set.mem_univ X, hX, hunit X hX⟩
    exact this (by rw [h0]; rfl)
  · intro X hX Y hY
    exact GlobalTheory.T.witt_extension_artinian_ring F E σ hσ M J hJ R n X Y (hX.trans hY.symm) (hunit X hX)

end Concrete

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ M J hJ n T hT hdet d b laminf lam hinf hlam minf hminf m hm I hIl hIinv hIT S`. Take `⟨⟨lcA, scA, t2A⟩, -⟩` from `GlobalTheory.T.adeles_locally_compact_second_countable F`. Establish `hRI` using `GlobalTheory.T.infinite_adeles_local_ring_totally_real F hσ.1`. Establish `hRv` using `GlobalTheory.T.completion_is_local_ring F`. Take `⟨trI, lcI, scI, t2I, -⟩` from `id hRI`.

Use `haveI : ∀ v, IsTopologicalRing (Fv F v) := fun v => (hRv v).1`. Use `haveI : ∀ v, LocallyCompactSpace (Fv F v) := fun v => (hRv v).2.1`. Use `haveI : ∀ v, SecondCountableTopology (Fv F v) := fun v => (hRv v).2.2.1`. Use `haveI : ∀ v, T2Space (Fv F v) := fun v => (hRv v).2.2.2.1`. Use `haveI : BorelSpace (Ainf F) := ⟨rfl⟩`.

Use `haveI : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩`. Establish `kA` using `GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (AF F)`. Establish `kI` using `GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)`. Establish `kV` using `fun v => GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)`. Use `haveI := kA.1`.

Use `haveI := kA.2.1`. Use `haveI := kA.2.2.1`. Use `haveI := kA.2.2.2.1`. Use `haveI := kA.2.2.2.2.2.2.2.1 n M`. Use `haveI := kI.1`.

Use `haveI := kI.2.1`. Use `haveI := kI.2.2.1`. Use `haveI := kI.2.2.2.1`. Use `haveI := kI.2.2.2.2.2.2.2.1 n M`. Use `haveI : ∀ v, IsTopologicalRing (Fv F v ⊗[F] E) := fun v => (kV v).1`.

Use `haveI : ∀ v, LocallyCompactSpace (Fv F v ⊗[F] E) := fun v => (kV v).2.1`. Use `haveI : ∀ v, SecondCountableTopology (Fv F v ⊗[F] E) := fun v => (kV v).2.2.1`. Use `haveI : ∀ v, T2Space (Fv F v ⊗[F] E) := fun v => (kV v).2.2.2.1`. Use `haveI : ∀ v, BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := fun v => (kV v).2.2.2.2.2.2.2.1 n M`. Establish `uA` using `GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (AF F)`.

Establish `uI` using `GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (Ainf F)`. Establish `uV` using `fun v => GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (Fv F v)`. Use `haveI := uI.1`. Use `haveI := uI.2.1`. Use `haveI := uI.2.2.1`.

Use `haveI := uI.2.2.2.1`. Use `haveI : ∀ v, IsTopologicalGroup (HA (Fv F v) σ J) := fun v => (uV v).1`. Use `haveI : ∀ v, LocallyCompactSpace (HA (Fv F v) σ J) := fun v => (uV v).2.1`. Use `haveI : ∀ v, SecondCountableTopology (HA (Fv F v) σ J) := fun v => (uV v).2.2.1`. Use `haveI : ∀ v, T2Space (HA (Fv F v) σ J) := fun v => (uV v).2.2.2.1`.

Establish `LI` using `local_pack σ hσ J hJ (Ainf F) hRI T hT hdet b laminf hinf.1 minf hminf`. Establish `LV` using `fun v => local_pack σ hσ J hJ (Fv F v) (hRv v) T hT hdet b (lam v) (hlam v).1 (m v) (hm v)`. Use `haveI := LI.1`. Use `haveI : ∀ v : S, IsLocallyFiniteMeasure (m v.1 (hermOf (Fv F v.1) σ T hT)) := fun v => (LV v.1).1`. Take `⟨cI, cF, cV, hlat, hint, -, -, -, -⟩` from `GlobalTheory.T.adelic_tuple_projections F E σ hσ d b n M`.

Establish `hprc : Continuous (pr S : (Fin n → Fin M → AF F ⊗[F] E) → _)` using `cI.prodMk (continuous_pi fun v => (cV v.1).comp cF)`. Establish `hprm : Measurable (pr S : (Fin n → Fin M → AF F ⊗[F] E) → _)` using `hprc.measurable`. Establish `hintm : MeasurableSet (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E))` using `(hint S).measurableSet`. Establish `actC : ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] , (Continuous fun p : HA R σ J × (Fin n → Fin M → R ⊗[F] E) => actW R σ J p.1 p.2) → ∀ h : HA R σ J, Continuous (actW R σ J h : (Fin n → Fin M → R ⊗[F] E) → _)` using `fun R _ _ _ hc h => hc.comp (Continuous.prodMk_right h)`. Establish `cAI` using `(uI.2.2.2.2.2 n).1`.

Establish `cAV` using `fun v => ((uV v).2.2.2.2.2 n).1`. Establish `cAA` using `(uA.2.2.2.2.2 n).1`. Use `set P := (I.restrict (intOff b S)).map (pr S) with hPdef`. Use `haveI hPc : IsFiniteMeasureOnCompacts P := ⟨fun K hK => by`. Rewrite using `[hPdef, Measure.map_apply hprm hK.isClosed.measurableSet, Measure.restrict_apply (hprm hK.isClosed.measurableSet)]`.

Conclude with `preimage_lt_top σ hσ b S I K hK⟩`. Use `haveI hPl : IsLocallyFiniteMeasure P := inferInstance`. Establish `hPinv : ∀ (g₀ : HA (Ainf F) σ J) (g : ∀ v : S, HA (Fv F v.1) σ J), P.map (fun x => (actW (Ainf F) σ J g₀ x.1, fun v => actW (Fv F v.1) σ J (g v) (x.2 v))) = P`. Introduce `g₀ g`. Use `push_inv σ hσ J hJ b S I hIinv (fun v X => ((uV v).2.2.2.2.2 n).2.1 X) hprm (fun h => (actC _ cAA h).measurable) hintm g₀ g ?_` and prove the remaining obligations.

Use `Continuous.measurable (Continuous.prodMk ((actC _ cAI g₀).comp continuous_fst) (continuous_pi fun v => ?_))` and prove the remaining obligations. Conclude with `(actC _ (cAV v.1) (g v)).comp ((continuous_apply v).comp continuous_snd)`. Establish `hZ₀ : IsClosed {Y : Fin n → Fin M → Ainf F ⊗[F] E | gramR (Ainf F) σ J Y = T.map (inclR (Ainf F))}` using `isClosed_eq (kI.2.2.2.2.2.2.2.2.2 n M J) continuous_const`. Establish `hZ : ∀ v : S, IsClosed {Y : Fin n → Fin M → Fv F v.1 ⊗[F] E | gramR (Fv F v.1) σ J Y = T.map (inclR (Fv F v.1))}` using `fun v => isClosed_eq ((kV v.1).2.2.2.2.2.2.2.2.2 n M J) continuous_const`. Establish `hPZ : P ({Y : Fin n → Fin M → Ainf F ⊗[F] E | gramR (Ainf F) σ J Y = T.map (inclR (Ainf F))} ×ˢ Set.univ.pi fun v : S => {Y : Fin n → Fin M → Fv F v.1 ⊗[F] E | gramR (Fv F v.1) σ J Y = T.map (inclR (Fv F v.1))})ᶜ = 0`.

Establish `hcl` using `hZ₀.prod (isClosed_set_pi fun v (_ : v ∈ Set.univ) => hZ v)`. Rewrite using `[hPdef, Measure.map_apply hprm hcl.measurableSet.compl]`. Use `le_antisymm (le_trans (Measure.restrict_apply_le _ _) ?_) bot_le` and prove the remaining obligations. Use `le_trans (measure_mono ?_) hIT.le` and prove the remaining obligations. Introduce `X hX hXT`.

Apply `hX` to reduce the goal to its premises. Establish `hg` using `((GlobalTheory.T.gram_matrix_local_global F E σ hσ M J hJ n X T).1.mp hXT)`. Conclude with `⟨hg.1, fun v _ => hg.2 v.1⟩`. Take `⟨c, hc⟩` from `prod_factor (ι := S) (G := fun v : S => HA (Fv F v.1) σ J) (W := fun v : S => Fin n → Fin M → Fv F v.1 ⊗[F] E) (actW (Ainf F) σ J) (fun v => actW (Fv F v.1) σ J) cAI (uI.2.2.2.2.2 n).2.1 (uI.2.2.2.2.2 n).2.2.1 (fun v => cAV v.1) (fun v => ((uV v.1).2.2.2.2.2 n).2.1) (fun v => ((u …`. Use `⟨c, fun φinf φ hφinf hφ => ?_⟩` and prove the remaining obligations.

Establish `h` using `hc φinf (fun v => φ v.1) hφinf (fun v => hφ v.1)`. Establish `hΦ : Measurable fun x : (Fin n → Fin M → Ainf F ⊗[F] E) × ∀ v : S, Fin n → Fin M → Fv F v.1 ⊗[F] E => φinf x.1 * ∏ v : S, φ v.1 (x.2 v)` using `(hφinf.comp measurable_fst).mul (Finset.measurable_prod _ fun v _ => (hφ v.1).comp ((measurable_pi_apply v).comp measurable_snd))`. Rewrite `h` using `[hPdef, lintegral_map hΦ hprm, Finset.prod_coe_sort S fun v => ∫⁻ X, φ v X ∂(m v (hermOf (Fv F v) σ T hT))]`. Rewrite using `[← h]`. Unfold `pureL`.

Rewrite using `[lintegral_indicator hintm]`. Use `lintegral_congr fun X => ?_` and prove the remaining obligations. Simplify using `only [pr]`. Rewrite using `[Finset.prod_coe_sort S fun v => φ v (projV v (projFin X))]`.
-/
theorem fact_S : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ), ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E)), IsGramFib (Ainf F) σ J n (coordW (Ainf F) b laminf n M) (coordHerm (Ainf F) σ b laminf n) minf → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFib (Fv F v) σ J n (coordW (Fv F v) b (lam v) n M) (coordHerm (Fv F v) σ b (lam v) n) (m v)) → ∀ I : Measure (Fin n → Fin M → AF F ⊗[F] E), IsLocallyFiniteMeasure I → (∀ h : HA (AF F) σ J, I.map (actW (AF F) σ J h) = I) → I {X | gramR (AF F) σ J X = T.map (inclR (AF F))}ᶜ = 0 → ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ c : ℝ≥0, ∀ (φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable φinf → (∀ v, Measurable (φ v)) → ∫⁻ X, pureL b S φinf φ X ∂I = (c : ℝ≥0∞) * ((∫⁻ X, φinf X ∂(minf (hermOf (Ainf F) σ T hT))) * ∏ v ∈ S, ∫⁻ X, φ v X ∂(m v (hermOf (Fv F v) σ T hT))) := by
  intro F E _ _ _ _ _ σ hσ M J hJ n T hT hdet d b laminf lam hinf hlam minf hminf m hm I hIl hIinv
    hIT S
  classical
  obtain ⟨⟨lcA, scA, t2A⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  have hRI := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hσ.1
  have hRv := GlobalTheory.T.completion_is_local_ring F
  obtain ⟨trI, lcI, scI, t2I, -⟩ := id hRI
  haveI : ∀ v, IsTopologicalRing (Fv F v) := fun v => (hRv v).1
  haveI : ∀ v, LocallyCompactSpace (Fv F v) := fun v => (hRv v).2.1
  haveI : ∀ v, SecondCountableTopology (Fv F v) := fun v => (hRv v).2.2.1
  haveI : ∀ v, T2Space (Fv F v) := fun v => (hRv v).2.2.2.1
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  have kA := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (AF F)
  have kI := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  have kV := fun v => GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)
  haveI := kA.1
  haveI := kA.2.1
  haveI := kA.2.2.1
  haveI := kA.2.2.2.1
  haveI := kA.2.2.2.2.2.2.2.1 n M
  haveI := kI.1
  haveI := kI.2.1
  haveI := kI.2.2.1
  haveI := kI.2.2.2.1
  haveI := kI.2.2.2.2.2.2.2.1 n M
  haveI : ∀ v, IsTopologicalRing (Fv F v ⊗[F] E) := fun v => (kV v).1
  haveI : ∀ v, LocallyCompactSpace (Fv F v ⊗[F] E) := fun v => (kV v).2.1
  haveI : ∀ v, SecondCountableTopology (Fv F v ⊗[F] E) := fun v => (kV v).2.2.1
  haveI : ∀ v, T2Space (Fv F v ⊗[F] E) := fun v => (kV v).2.2.2.1
  haveI : ∀ v, BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := fun v => (kV v).2.2.2.2.2.2.2.1 n M
  have uA := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (AF F)
  have uI := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (Ainf F)
  have uV := fun v => GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (Fv F v)
  haveI := uI.1
  haveI := uI.2.1
  haveI := uI.2.2.1
  haveI := uI.2.2.2.1
  haveI : ∀ v, IsTopologicalGroup (HA (Fv F v) σ J) := fun v => (uV v).1
  haveI : ∀ v, LocallyCompactSpace (HA (Fv F v) σ J) := fun v => (uV v).2.1
  haveI : ∀ v, SecondCountableTopology (HA (Fv F v) σ J) := fun v => (uV v).2.2.1
  haveI : ∀ v, T2Space (HA (Fv F v) σ J) := fun v => (uV v).2.2.2.1
  have LI := local_pack σ hσ J hJ (Ainf F) hRI T hT hdet b laminf hinf.1 minf hminf
  have LV := fun v => local_pack σ hσ J hJ (Fv F v) (hRv v) T hT hdet b (lam v) (hlam v).1 (m v) (hm v)
  haveI := LI.1
  haveI : ∀ v : S, IsLocallyFiniteMeasure (m v.1 (hermOf (Fv F v.1) σ T hT)) := fun v => (LV v.1).1
  obtain ⟨cI, cF, cV, hlat, hint, -, -, -, -⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hσ d b n M
  have hprc : Continuous (pr S : (Fin n → Fin M → AF F ⊗[F] E) → _) :=
    cI.prodMk (continuous_pi fun v => (cV v.1).comp cF)
  have hprm : Measurable (pr S : (Fin n → Fin M → AF F ⊗[F] E) → _) := hprc.measurable
  have hintm : MeasurableSet (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E)) :=
    (hint S).measurableSet
  have actC : ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] ,
      (Continuous fun p : HA R σ J × (Fin n → Fin M → R ⊗[F] E) => actW R σ J p.1 p.2) →
      ∀ h : HA R σ J, Continuous (actW R σ J h : (Fin n → Fin M → R ⊗[F] E) → _) :=
    fun R _ _ _ hc h => hc.comp (Continuous.prodMk_right h)
  have cAI := (uI.2.2.2.2.2 n).1
  have cAV := fun v => ((uV v).2.2.2.2.2 n).1
  have cAA := (uA.2.2.2.2.2 n).1
  set P := (I.restrict (intOff b S)).map (pr S) with hPdef
  haveI hPc : IsFiniteMeasureOnCompacts P := ⟨fun K hK => by
    rw [hPdef, Measure.map_apply hprm hK.isClosed.measurableSet,
      Measure.restrict_apply (hprm hK.isClosed.measurableSet)]
    exact preimage_lt_top σ hσ b S I K hK⟩
  haveI hPl : IsLocallyFiniteMeasure P := inferInstance
  have hPinv : ∀ (g₀ : HA (Ainf F) σ J) (g : ∀ v : S, HA (Fv F v.1) σ J),
      P.map (fun x => (actW (Ainf F) σ J g₀ x.1, fun v => actW (Fv F v.1) σ J (g v) (x.2 v))) = P := by
    intro g₀ g
    refine push_inv σ hσ J hJ b S I hIinv (fun v X => ((uV v).2.2.2.2.2 n).2.1 X) hprm
      (fun h => (actC _ cAA h).measurable) hintm g₀ g ?_
    refine Continuous.measurable (Continuous.prodMk ((actC _ cAI g₀).comp continuous_fst)
      (continuous_pi fun v => ?_))
    exact (actC _ (cAV v.1) (g v)).comp ((continuous_apply v).comp continuous_snd)
  have hZ₀ : IsClosed {Y : Fin n → Fin M → Ainf F ⊗[F] E | gramR (Ainf F) σ J Y = T.map (inclR (Ainf F))} :=
    isClosed_eq (kI.2.2.2.2.2.2.2.2.2 n M J) continuous_const
  have hZ : ∀ v : S, IsClosed {Y : Fin n → Fin M → Fv F v.1 ⊗[F] E |
      gramR (Fv F v.1) σ J Y = T.map (inclR (Fv F v.1))} := fun v =>
    isClosed_eq ((kV v.1).2.2.2.2.2.2.2.2.2 n M J) continuous_const
  have hPZ : P ({Y : Fin n → Fin M → Ainf F ⊗[F] E | gramR (Ainf F) σ J Y = T.map (inclR (Ainf F))} ×ˢ
      Set.univ.pi fun v : S => {Y : Fin n → Fin M → Fv F v.1 ⊗[F] E |
        gramR (Fv F v.1) σ J Y = T.map (inclR (Fv F v.1))})ᶜ = 0 := by
    have hcl := hZ₀.prod (isClosed_set_pi fun v (_ : v ∈ Set.univ) => hZ v)
    rw [hPdef, Measure.map_apply hprm hcl.measurableSet.compl]
    refine le_antisymm (le_trans (Measure.restrict_apply_le _ _) ?_) bot_le
    refine le_trans (measure_mono ?_) hIT.le
    intro X hX hXT
    apply hX
    have hg := ((GlobalTheory.T.gram_matrix_local_global F E σ hσ M J hJ n X T).1.mp hXT)
    exact ⟨hg.1, fun v _ => hg.2 v.1⟩
  obtain ⟨c, hc⟩ := prod_factor (ι := S) (G := fun v : S => HA (Fv F v.1) σ J)
    (W := fun v : S => Fin n → Fin M → Fv F v.1 ⊗[F] E)
    (actW (Ainf F) σ J) (fun v => actW (Fv F v.1) σ J)
    cAI (uI.2.2.2.2.2 n).2.1 (uI.2.2.2.2.2 n).2.2.1
    (fun v => cAV v.1) (fun v => ((uV v.1).2.2.2.2.2 n).2.1) (fun v => ((uV v.1).2.2.2.2.2 n).2.2.1)
    _ _ hZ₀ hZ
    (fun g x hx => ((uI.2.2.2.2.2 n).2.2.2 g x).trans hx)
    (fun v g x hx => (((uV v.1).2.2.2.2.2 n).2.2.2 g x).trans hx)
    LI.2.2.2.2 (fun v => (LV v.1).2.2.2.2)
    (minf (hermOf (Ainf F) σ T hT)) (fun v => m v.1 (hermOf (Fv F v.1) σ T hT))
    LI.2.1 (fun v => (LV v.1).2.1) LI.2.2.1 (fun v => (LV v.1).2.2.1)
    LI.2.2.2.1 (fun v => (LV v.1).2.2.2.1) P hPinv hPZ
  refine ⟨c, fun φinf φ hφinf hφ => ?_⟩
  have h := hc φinf (fun v => φ v.1) hφinf (fun v => hφ v.1)
  have hΦ : Measurable fun x : (Fin n → Fin M → Ainf F ⊗[F] E) ×
      ∀ v : S, Fin n → Fin M → Fv F v.1 ⊗[F] E => φinf x.1 * ∏ v : S, φ v.1 (x.2 v) :=
    (hφinf.comp measurable_fst).mul
      (Finset.measurable_prod _ fun v _ => (hφ v.1).comp ((measurable_pi_apply v).comp measurable_snd))
  rw [hPdef, lintegral_map hΦ hprm, Finset.prod_coe_sort S fun v => ∫⁻ X, φ v X ∂(m v (hermOf (Fv F v) σ T hT))] at h
  rw [← h]
  unfold pureL
  rw [lintegral_indicator hintm]
  refine lintegral_congr fun X => ?_
  simp only [pr]
  rw [Finset.prod_coe_sort S fun v => φ v (projV v (projFin X))]

end GlobalTheory.CompanionTheory.SW.FactS
