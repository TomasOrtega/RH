import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.GeoTransport

open MeasureTheory NumberField IsDedekindDomain PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Z.Tf.Orb
open PositivityTheory.Rg.Tf.Geo (mapGL incFin galFin)
open scoped ENNReal

/- English proof (translation)
Use `⟨?_, fun a ha b hb => ?_⟩` and prove the remaining obligations. Establish `: ((Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) = {x | x * γ = γ * x}`. Use extensionality with `x`. Simplify using `[Subgroup.mem_centralizer_singleton_iff]`. Rewrite using `[this]`.

Conclude with `isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)`. Rewrite `ha`, `hb` using `[Subgroup.mem_centralizer_singleton_iff]`. Conclude with `Units.ext (hCC k n γ a b hγ (congrArg Units.val ha) (congrArg Units.val hb))`.
-/
private theorem cent_facts (hCC : CentComm) {k : Type} [Field k] [TopologicalSpace k] {n : ℕ} [T2Space (GL (Fin n) k)]
    [ContinuousMul (GL (Fin n) k)] {γ : GL (Fin n) k} (hγ : IsRegSemisimple γ) :
    IsClosed ((Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) ∧
    ∀ a ∈ (Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)), ∀ b ∈ (Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)),
        Commute a b := by
  refine ⟨?_, fun a ha b hb => ?_⟩
  · have : ((Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) = {x | x * γ = γ * x} := by
      ext x; simp [Subgroup.mem_centralizer_singleton_iff]
    rw [this]
    exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  · rw [Subgroup.mem_centralizer_singleton_iff] at ha hb
    exact Units.ext (hCC k n γ a b hγ (congrArg Units.val ha) (congrArg Units.val hb))

/- English proof (translation)
Use function extensionality and compare the values at `x`. Distinguish the cases in `h : u x ∈ A`. Rewrite using `[Set.indicator_of_mem h, Set.indicator_of_mem (show x ∈ u ⁻¹' A from h)]`. Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem h, Set.indicator_of_notMem (show x ∉ u ⁻¹' A from h)]`.
-/
private theorem ind_comp {X Y M : Type} [Zero M] [One M] (u : X → Y) (A : Set Y) :
    (fun x => A.indicator (1 : Y → M) (u x)) = (u ⁻¹' A).indicator 1 := by
  funext x
  by_cases h : u x ∈ A
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show x ∈ u ⁻¹' A from h)]; rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show x ∉ u ⁻¹' A from h)]

/- English proof (translation)
Introduce `hT hC hCC hTw hH hQ hU hB k E _ _ _ _ _ _ _ _ _ _ _ _ _ hur σ hσ n _ _ _ _ μE μk hE hk vE vk`. Take `⟨a1, a2, a3, -⟩` from `hT E n`. Take `⟨b1, b2, b3, -⟩` from `hT k n`. Establish `hσc : Continuous (sigmaGL σ : GL (Fin n) E → GL (Fin n) E)` using `((hC k E).2.2 n).2 σ`. Take `⟨h1, h2⟩` from `hB k E hur σ hσ n μE μk hE hk vE vk`.

Establish `hk' : ∀ (γ : GL (Fin n) k) (μγ : Measure (Subgroup.centralizer {γ})), IsRegSemisimple γ → μγ.IsHaarMeasure → orbIntegralC μk γ μγ (unitFnC k) = ((orbIntegral μk γ μγ (unitFn k)).toReal : ℂ)` using `fun γ μγ hγ hμ => by`. Take `⟨c1, c2⟩` from `cent_facts hCC hγ`. Take `⟨s1, -, -⟩` from `hH _ _ c1 c2 μγ hμ`. Unfold `orbIntegralC orbIntegral unitFnC unitFn`. Rewrite using `[ind_comp (fun g : GL (Fin n) k => g⁻¹ * γ * g), ind_comp (fun g : GL (Fin n) k => g⁻¹ * γ * g)]`.

Conclude with `hQ _ μk _ μγ _ (((hU k n).1.preimage ((continuous_inv.mul continuous_const).mul continuous_id)).measurableSet)`. Use `⟨fun δ γ h μδ μγ hδ hN hμδ hμγ hm => ?_, fun γ μγ hγ hn hμ => ?_⟩` and prove the remaining obligations. Establish `hγ : IsRegSemisimple γ`. Establish `e : ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly = (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k E)`. Rewrite using `[hN, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj, ← Matrix.charpoly_map]`.

Both sides reduce to the same expression. Use `hδ` as an intermediate fact. Unfold `IsTwRegSemisimple at this`. Rewrite `this` using `[e]`. Conclude with `(Polynomial.separable_map _).1 this`.

Take `⟨c1, c2⟩` from `hTw k E σ hσ n δ hδ`. Take `⟨s1, -, -⟩` from `hH _ _ c1 c2 μδ hμδ`. Rewrite using `[hk' γ μγ hγ hμγ, ← h1 δ γ h μδ μγ hδ hN hμδ hμγ hm]`. Unfold `twOrbIntegralC twOrbIntegral unitFnC unitFn`. Rewrite using `[ind_comp (fun g : GL (Fin n) E => twConj (sigmaGL σ) g δ), ind_comp (fun g : GL (Fin n) E => twConj (sigmaGL σ) g δ)]`.

Conclude with `hQ _ μE _ μδ _ (((hU E n).1.preimage ((continuous_inv.mul continuous_const).mul hσc)).measurableSet)`. Rewrite using `[hk' γ μγ hγ hμ, h2 γ μγ hγ hn hμ]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.V.Z.Tf.Orb.unitMatch :
    UpperTheory.V.Z.Tf.Orb.GLTop → UpperTheory.V.Z.Tf.Orb.ExtCont → UpperTheory.V.Z.Tf.Orb.CentComm → UpperTheory.V.Z.Tf.Orb.TwCent → UpperTheory.V.Z.Tf.Orb.HaarComm → UpperTheory.V.Z.Tf.Orb.QuotReal → UpperTheory.V.Z.Tf.Orb.UnitSB → UpperTheory.V.Z.Tf.Orb.UnitMatch := by
  intro hT hC hCC hTw hH hQ hU hB k E _ _ _ _ _ _ _ _ _ _ _ _ _ hur σ hσ n _ _ _ _ μE μk hE hk vE vk
  obtain ⟨a1, a2, a3, -⟩ := hT E n
  obtain ⟨b1, b2, b3, -⟩ := hT k n
  have hσc : Continuous (sigmaGL σ : GL (Fin n) E → GL (Fin n) E) := ((hC k E).2.2 n).2 σ
  obtain ⟨h1, h2⟩ := hB k E hur σ hσ n μE μk hE hk vE vk
  have hk' : ∀ (γ : GL (Fin n) k) (μγ : Measure (Subgroup.centralizer {γ})), IsRegSemisimple γ → μγ.IsHaarMeasure →
      orbIntegralC μk γ μγ (unitFnC k) = ((orbIntegral μk γ μγ (unitFn k)).toReal : ℂ) := fun γ μγ hγ hμ => by
    obtain ⟨c1, c2⟩ := cent_facts hCC hγ
    obtain ⟨s1, -, -⟩ := hH _ _ c1 c2 μγ hμ
    unfold orbIntegralC orbIntegral unitFnC unitFn
    rw [ind_comp (fun g : GL (Fin n) k => g⁻¹ * γ * g), ind_comp (fun g : GL (Fin n) k => g⁻¹ * γ * g)]
    exact hQ _ μk _ μγ _ (((hU k n).1.preimage ((continuous_inv.mul continuous_const).mul continuous_id)).measurableSet)
  refine ⟨fun δ γ h μδ μγ hδ hN hμδ hμγ hm => ?_, fun γ μγ hγ hn hμ => ?_⟩
  · have hγ : IsRegSemisimple γ := by
      have e : ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly =
          (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k E) := by
        rw [hN, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj, ← Matrix.charpoly_map]
        rfl
      have := hδ
      unfold IsTwRegSemisimple at this
      rw [e] at this
      exact (Polynomial.separable_map _).1 this
    obtain ⟨c1, c2⟩ := hTw k E σ hσ n δ hδ
    obtain ⟨s1, -, -⟩ := hH _ _ c1 c2 μδ hμδ
    rw [hk' γ μγ hγ hμγ, ← h1 δ γ h μδ μγ hδ hN hμδ hμγ hm]
    unfold twOrbIntegralC twOrbIntegral unitFnC unitFn
    rw [ind_comp (fun g : GL (Fin n) E => twConj (sigmaGL σ) g δ), ind_comp (fun g : GL (Fin n) E => twConj (sigmaGL σ) g δ)]
    exact hQ _ μE _ μδ _ (((hU E n).1.preimage ((continuous_inv.mul continuous_const).mul hσc)).measurableSet)
  · rw [hk' γ μγ hγ hμ, h2 γ μγ hγ hn hμ]
    simp
