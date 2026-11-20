import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Iwa
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.FockSt

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

/- English proof (translation)
Use `haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK`. Set `r : V → Module.Dual ℂ U` to `fun v => (ev v).domRestrict U`. Set `S : Submodule ℂ (Module.Dual ℂ U)` to `Submodule.span ℂ (Set.range r)`. Establish `hS : S = ⊤`. Establish `hco : S.dualCoannihilator = ⊥`.

Rewrite using `[eq_bot_iff]`. Introduce `u hu`. Rewrite `hu` using `[Submodule.mem_dualCoannihilator]`. Establish `: (u : T) = 0` using `hev _ fun v => hu (r v) (Submodule.subset_span ⟨v, rfl⟩)`. Simplify using `using this`.

Use `Subspace.dualCoannihilator_dualAnnihilator_eq (W := S)` as an intermediate fact. Rewrite `this` using `[hco]`. Rewrite using `[← this]`. Simplify using the standard rewrite rules. Set `g : K → U` to `fun k => ⟨f k.1, hf k.1 k.2⟩`.

Establish `hcont : ∀ l : Module.Dual ℂ U, Continuous fun k : K => l (g k)`. Introduce `l`. Establish `hl : l ∈ S` using `hS ▸ Submodule.mem_top`. Proceed by induction on `hl using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨v, rfl⟩` from `hx`. Conclude with `continuousOn_iff_continuous_restrict.mp (hc v)`. Consider the case `zero => simpa using continuous_const`. Consider the case `add x y _ _ hx hy`. Express the relevant statement in the definitionally equal form `Continuous fun k : K => x (g k) + y (g k)`.

Conclude with `hx.add hy`. Consider the case `smul a x _ hx`. Express the relevant statement in the definitionally equal form `Continuous fun k : K => a * x (g k)`. Conclude with `continuous_const.mul hx`. Set `b` to `Module.finBasis ℂ U`.

Establish `hbd : ∀ i, ∃ R : ℝ, 0 < R ∧ ∀ k : K, ‖b.coord i (g k)‖ ≤ R`. Introduce `i`. Take `⟨R, hR⟩` from `isCompact_univ.exists_bound_of_continuousOn (hcont (b.coord i)).continuousOn`. Conclude with `⟨max R 1, by positivity, fun k => (hR k (Set.mem_univ _)).trans (le_max_left _ _)⟩`. Use `choose R hR0 hR using hbd`.

Use `⟨_, fun i => (R i : ℂ) • ((b i : U) : T), fun k hk => ?_⟩` and prove the remaining obligations. Use `⟨fun i => b.coord i (g ⟨k, hk⟩) / (R i : ℂ), fun i => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[norm_div, Complex.norm_real, Real.norm_of_nonneg (hR0 i).le]`. Conclude with `(div_le_one (hR0 i)).mpr (hR i _)`. Establish `h : ((∑ i, b.repr (g ⟨k, hk⟩) i • b i : U) : T) = f k` using `by rw [b.sum_repr]`.

Rewrite `h` using `[AddSubmonoidClass.coe_finset_sum]`. Establish `h2 : f k = ∑ i, b.coord i (g ⟨k, hk⟩) • ((b i : U) : T)` using `h.symm`. Rewrite using `[h2]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hne : (R i : ℂ) ≠ 0` using `by exact_mod_cast (hR0 i).ne'`.

Rewrite using `[smul_smul, div_mul_cancel₀ _ hne]`.
-/
private theorem finite_family_of_compact {X T V : Type} [TopologicalSpace X] [AddCommGroup T] [Module ℂ T]
    (ev : V → T →ₗ[ℂ] ℂ) (hev : ∀ t : T, (∀ v, ev v t = 0) → t = 0)
    (U : Submodule ℂ T) [FiniteDimensional ℂ U] (K : Set X) (hK : IsCompact K) (f : X → T)
    (hf : ∀ k ∈ K, f k ∈ U) (hc : ∀ v, ContinuousOn (fun k => ev v (f k)) K) :
    ∃ (n : ℕ) (e : Fin n → T), ∀ k ∈ K, ∃ c : Fin n → ℂ, (∀ i, ‖c i‖ ≤ 1) ∧ f k = ∑ i, c i • e i := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let r : V → Module.Dual ℂ U := fun v => (ev v).domRestrict U
  let S : Submodule ℂ (Module.Dual ℂ U) := Submodule.span ℂ (Set.range r)
  have hS : S = ⊤ := by
    have hco : S.dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      rw [Submodule.mem_dualCoannihilator] at hu
      have : (u : T) = 0 := hev _ fun v => hu (r v) (Submodule.subset_span ⟨v, rfl⟩)
      simpa using this
    have := Subspace.dualCoannihilator_dualAnnihilator_eq (W := S)
    rw [hco] at this
    rw [← this]
    simp
  let g : K → U := fun k => ⟨f k.1, hf k.1 k.2⟩
  have hcont : ∀ l : Module.Dual ℂ U, Continuous fun k : K => l (g k) := by
    intro l
    have hl : l ∈ S := hS ▸ Submodule.mem_top
    induction hl using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      exact continuousOn_iff_continuous_restrict.mp (hc v)
    | zero => simpa using continuous_const
    | add x y _ _ hx hy =>
      change Continuous fun k : K => x (g k) + y (g k)
      exact hx.add hy
    | smul a x _ hx =>
      change Continuous fun k : K => a * x (g k)
      exact continuous_const.mul hx
  let b := Module.finBasis ℂ U
  have hbd : ∀ i, ∃ R : ℝ, 0 < R ∧ ∀ k : K, ‖b.coord i (g k)‖ ≤ R := by
    intro i
    obtain ⟨R, hR⟩ := isCompact_univ.exists_bound_of_continuousOn (hcont (b.coord i)).continuousOn
    exact ⟨max R 1, by positivity, fun k => (hR k (Set.mem_univ _)).trans (le_max_left _ _)⟩
  choose R hR0 hR using hbd
  refine ⟨_, fun i => (R i : ℂ) • ((b i : U) : T), fun k hk => ?_⟩
  refine ⟨fun i => b.coord i (g ⟨k, hk⟩) / (R i : ℂ), fun i => ?_, ?_⟩
  · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (hR0 i).le]
    exact (div_le_one (hR0 i)).mpr (hR i _)
  · have h : ((∑ i, b.repr (g ⟨k, hk⟩) i • b i : U) : T) = f k := by rw [b.sum_repr]
    rw [AddSubmonoidClass.coe_finset_sum] at h
    have h2 : f k = ∑ i, b.coord i (g ⟨k, hk⟩) • ((b i : U) : T) := h.symm
    rw [h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hne : (R i : ℂ) ≠ 0 := by exact_mod_cast (hR0 i).ne'
    rw [smul_smul, div_mul_cancel₀ _ hne]

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ D W φ hφ`. Take `⟨hKc, -⟩` from `iwa F`. Take `⟨U, -, hfd, hmem⟩` from `(fockSt F E D W).om φ hφ (KK F) hKc fun k hk => hk.1`. Set `ev : V4 F → S4 F →ₗ[ℂ] ℂ` to `fun v => { toFun := fun t => t.1 v, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`. Use `finite_family_of_compact ev (fun t ht => Subtype.ext (funext ht)) U (KK F) hKc (fun k => W.Om k φ) hmem fun v => ?_` and prove the remaining obligations.

Establish `h` using `W.cont φ`. Conclude with `(h.comp (Continuous.prodMk continuous_id continuous_const : Continuous fun k : G1 F => (k, v))).continuousOn`.
-/
theorem UpperTheory.ConvolutionTheory.R2.Ff.omFin :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D), OmFin W := by
  intro F E _ _ _ _ _ _ _ D W φ hφ
  obtain ⟨hKc, -⟩ := iwa F
  obtain ⟨U, -, hfd, hmem⟩ := (fockSt F E D W).om φ hφ (KK F) hKc fun k hk => hk.1
  let ev : V4 F → S4 F →ₗ[ℂ] ℂ := fun v =>
    { toFun := fun t => t.1 v, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  refine finite_family_of_compact ev (fun t ht => Subtype.ext (funext ht)) U (KK F) hKc
    (fun k => W.Om k φ) hmem fun v => ?_
  have h := W.cont φ
  exact (h.comp (Continuous.prodMk continuous_id continuous_const : Continuous fun k : G1 F => (k, v))).continuousOn
