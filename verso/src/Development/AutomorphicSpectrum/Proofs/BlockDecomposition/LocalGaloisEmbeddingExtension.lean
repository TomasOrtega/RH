import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasPeriods
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniqueEmbeddingExtension
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical Topology

namespace GlobalTheory.CompanionTheory.EmbBridge

variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Introduce `s hs`. Take `⟨γ, hγ⟩` from `Valued.mem_nhds_zero.1 hs`. Establish `hpos : (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) ≠ 0` using `by simp`. Establish `: ∃ n : ℕ, (Valued.v x) ^ n < MonoidWithZeroHom.ValueGroup₀.embedding γ.1`. Conclude with `exists_pow_lt₀ hx (Units.mk0 _ hpos)`.

Take `⟨n, hn⟩` from `this`. Use `Filter.mem_map.2 (Filter.mem_atTop_sets.2 ⟨n, fun m hm => hγ ?_⟩)` and prove the remaining obligations. Establish `e : Valued.v (x ^ m) < MonoidWithZeroHom.ValueGroup₀.embedding γ.1`. Rewrite using `[map_pow]`. Conclude with `(pow_le_pow_of_le_one zero_le' hx.le hm).trans_lt hn`.

Conclude with `(Valuation.restrict_lt_iff_lt_embedding _).2 e`.
-/
theorem tendsto_pow_zero (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E)
    (hx : Valued.v x < 1) : Filter.Tendsto (fun n : ℕ => x ^ n) Filter.atTop (𝓝 0) := by
  intro s hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  have hpos : (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) ≠ 0 := by simp
  have : ∃ n : ℕ, (Valued.v x) ^ n < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
    exact exists_pow_lt₀ hx (Units.mk0 _ hpos)
  obtain ⟨n, hn⟩ := this
  refine Filter.mem_map.2 (Filter.mem_atTop_sets.2 ⟨n, fun m hm => hγ ?_⟩)
  have e : Valued.v (x ^ m) < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
    rw [map_pow]
    exact (pow_le_pow_of_le_one zero_le' hx.le hm).trans_lt hn
  exact (Valuation.restrict_lt_iff_lt_embedding _).2 e

/- English proof (translation)
Establish `h1 : Filter.Tendsto (fun n : ℕ => φ x ^ n) Filter.atTop (𝓝 0)`. Use `(hφ.tendsto 0).comp (tendsto_pow_zero w x hx)` as an intermediate fact. Simplify `this` using `[Function.comp_def, map_pow]`. Assume the negation of the conclusion as `hge`. Establish `h2 : ∀ n : ℕ, 1 ≤ ‖φ x ^ n‖` using `fun n => by`.

Rewrite using `[norm_pow]`. Conclude with `one_le_pow₀ (not_lt.1 hge)`. Establish `h3` using `h1.norm`. Rewrite `h3` using `[norm_zero]`. Use `ge_of_tendsto' h3 h2` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_lt_one (w : HeightOneSpectrum (𝓞 E)) (φ : w.adicCompletion E →+* Om l) (hφ : Continuous φ)
    (x : w.adicCompletion E) (hx : Valued.v x < 1) : ‖φ x‖ < 1 := by
  have h1 : Filter.Tendsto (fun n : ℕ => φ x ^ n) Filter.atTop (𝓝 0) := by
    have := (hφ.tendsto 0).comp (tendsto_pow_zero w x hx)
    simpa [Function.comp_def, map_pow] using this
  by_contra hge
  have h2 : ∀ n : ℕ, 1 ≤ ‖φ x ^ n‖ := fun n => by
    rw [norm_pow]; exact one_le_pow₀ (not_lt.1 hge)
  have h3 := h1.norm
  rw [norm_zero] at h3
  have := ge_of_tendsto' h3 h2
  linarith

/- English proof (translation)
Assume the negation of the conclusion as `hgt`. Establish `hgt'` using `not_le.1 hgt`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hgt'`.

Establish `h1 : Valued.v x⁻¹ < 1`. Rewrite using `[map_inv₀]`. Conclude with `inv_lt_one_of_one_lt₀ hgt'`. Establish `h2` using `norm_lt_one w φ hφ _ h1`. Rewrite `h2` using `[map_inv₀, norm_inv]`.

Establish `hpos : 0 < ‖φ x‖` using `norm_pos_iff.2 ((map_ne_zero φ).2 hx0)`. Use `(one_lt_inv₀ hpos).2 hx` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem v_le_one (w : HeightOneSpectrum (𝓞 E)) (φ : w.adicCompletion E →+* Om l) (hφ : Continuous φ)
    (x : w.adicCompletion E) (hx : ‖φ x‖ < 1) : Valued.v x ≤ 1 := by
  by_contra hgt
  have hgt' := not_le.1 hgt
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hgt'
  have h1 : Valued.v x⁻¹ < 1 := by
    rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hgt'
  have h2 := norm_lt_one w φ hφ _ h1
  rw [map_inv₀, norm_inv] at h2
  have hpos : 0 < ‖φ x‖ := norm_pos_iff.2 ((map_ne_zero φ).2 hx0)
  have := (one_lt_inv₀ hpos).2 hx
  linarith

/- English proof (translation)
Take `⟨y, hyw, hy0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot`. Use `⟨algebraMap E _ (y : E), ?_, ?_⟩` and prove the remaining obligations. Simplify using `using hy0`. Establish `h : w.valuation E (y : E) < 1` using `(HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w y).2 hyw`. Establish `e : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) = w.valuation E (y : E)` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (y : E)`.

Rewrite using `[e]`. Conclude with `h`.
-/
theorem exists_v_lt_one (w : HeightOneSpectrum (𝓞 E)) :
    ∃ π : w.adicCompletion E, π ≠ 0 ∧ Valued.v π < 1 := by
  obtain ⟨y, hyw, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  refine ⟨algebraMap E _ (y : E), ?_, ?_⟩
  · simpa using hy0
  · have h : w.valuation E (y : E) < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w y).2 hyw
    have e : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) = w.valuation E (y : E) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (y : E)
    rw [e]
    exact h

/- English proof (translation)
Rewrite using `[IsTopologicalAddGroup.isInducing_iff_nhds_zero]`. Use `le_antisymm (by simpa using (hφ.tendsto 0).le_comap) ?_` and prove the remaining obligations. Introduce `s hs`. Take `⟨γ, hγ⟩` from `Valued.mem_nhds_zero.1 hs`. Take `⟨π, hπ0, hπ⟩` from `exists_v_lt_one w`.

Establish `hpos : (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) ≠ 0` using `by simp`. Take `⟨n, hn⟩ : ∃ n : ℕ, (Valued.v π) ^ n < MonoidWithZeroHom.ValueGroup₀.embedding γ.1` from `exists_pow_lt₀ hπ (Units.mk0 _ hpos)`. Establish `hε : 0 < ‖φ (π ^ n)‖` using `norm_pos_iff.2 ((map_ne_zero φ).2 (pow_ne_zero n hπ0))`. Use `Filter.mem_comap.2 ⟨Metric.ball 0 ‖φ (π ^ n)‖, Metric.ball_mem_nhds _ hε, fun x hx => hγ ?_⟩` and prove the remaining obligations. Establish `hx' : ‖φ x‖ < ‖φ (π ^ n)‖` using `by simpa using hx`.

Establish `h1 : ‖φ (x / π ^ n)‖ < 1`. Rewrite using `[map_div₀, norm_div]`. Conclude with `(div_lt_one hε).2 hx'`. Establish `h2` using `v_le_one w φ hφ _ h1`. Establish `hv : 0 < Valued.v π ^ n` using `zero_lt_iff.2 (pow_ne_zero n ((Valuation.ne_zero_iff _).2 hπ0))`.

Rewrite `h2` using `[map_div₀, map_pow, div_le_one₀ hv]`. Conclude with `(Valuation.restrict_lt_iff_lt_embedding _).2 (h2.trans_lt hn)`.
-/
theorem isInducing (w : HeightOneSpectrum (𝓞 E)) (φ : w.adicCompletion E →+* Om l) (hφ : Continuous φ) :
    Topology.IsInducing φ := by
  rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
  refine le_antisymm (by simpa using (hφ.tendsto 0).le_comap) ?_
  intro s hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  obtain ⟨π, hπ0, hπ⟩ := exists_v_lt_one w
  have hpos : (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) ≠ 0 := by simp
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (Valued.v π) ^ n < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 :=
    exists_pow_lt₀ hπ (Units.mk0 _ hpos)
  have hε : 0 < ‖φ (π ^ n)‖ := norm_pos_iff.2 ((map_ne_zero φ).2 (pow_ne_zero n hπ0))
  refine Filter.mem_comap.2 ⟨Metric.ball 0 ‖φ (π ^ n)‖, Metric.ball_mem_nhds _ hε, fun x hx => hγ ?_⟩
  have hx' : ‖φ x‖ < ‖φ (π ^ n)‖ := by simpa using hx
  have h1 : ‖φ (x / π ^ n)‖ < 1 := by
    rw [map_div₀, norm_div]
    exact (div_lt_one hε).2 hx'
  have h2 := v_le_one w φ hφ _ h1
  have hv : 0 < Valued.v π ^ n := zero_lt_iff.2 (pow_ne_zero n ((Valuation.ne_zero_iff _).2 hπ0))
  rw [map_div₀, map_pow, div_le_one₀ hv] at h2
  exact (Valuation.restrict_lt_iff_lt_embedding _).2 (h2.trans_lt hn)

end GlobalTheory.CompanionTheory.EmbBridge

namespace GlobalTheory.CompanionTheory.EmbBridge

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ l _ w A hA O _ _ _ Bw hI LL' hLL j`. Establish `hKL : Bw.Kw.1 ≤ LL'.1` using `fun x hx => hLL (Bw.LL_split Bw.Kw.1.val ⟨x, hx⟩)`. Take `⟨⟨φ, hφc⟩, hφ, -⟩` from `GlobalTheory.CompanionTheory.EmbUniq.existsUnique_continuous_induced w A hA O Bw hI LL' (IntermediateField.inclusion hKL)`. Establish `hφE : ∀ y : E, φ (algebraMap E (w.adicCompletion E) y) = Bw.j (algebraMap E Ω y)` using `fun y => hφ y`. Use `haveI : FiniteDimensional ℚ_[l] ↥Bw.Kw.1 := Bw.Kw.2`.

Establish `hKc : IsClosed (Bw.Kw.1 : Set (Om l))` using `Submodule.closed_of_finiteDimensional (Subalgebra.toSubmodule Bw.Kw.1.toSubalgebra)`. Establish `hmem : ∀ x, φ x ∈ Bw.Kw.1` using `fun x => (HeightOneSpectrum.denseRange_algebraMap E w).induction_on (p := fun x => φ x ∈ (Bw.Kw.1 : Set (Om l))) x (hKc.preimage hφc) (fun y => by show φ _ ∈ Bw.Kw.1`. Rewrite using `[hφE]`. Conclude with `Bw.j_E y)`. Establish `hind` using `isInducing w φ hφc`.

Establish `hrc : IsClosed (Set.range φ)` using `(AddMonoidHom.isUniformInducing_of_isInducing (f := φ.toAddMonoidHom) hind).isComplete_range.isClosed`. Establish `hsurj : ∀ k : ↥Bw.Kw.1, ∃ x, φ x = k` using `fun k => by`. Establish `h1 : (k : Om l) ∈ closure (Set.range fun x : E => Bw.j (algebraMap E Ω x))` using `Bw.j_dense k.2`. Establish `h2 : (Set.range fun x : E => Bw.j (algebraMap E Ω x)) ⊆ Set.range φ`. Introduce and unpack `_ ⟨y, rfl⟩`.

Conclude with `⟨_, hφE y⟩`. Conclude with `hrc.closure_subset_iff.2 h2 h1`. Set `φ' : w.adicCompletion E →+* ↥Bw.Kw.1` to `φ.codRestrict Bw.Kw.1 hmem`. Establish `hbij : Function.Bijective φ'` using `⟨fun a b h => φ.injective (congrArg Subtype.val h), fun k => by`. Take `⟨x, hx⟩` from `hsurj k`.

Conclude with `⟨x, Subtype.ext hx⟩⟩`. Set `e : w.adicCompletion E ≃+* ↥Bw.Kw.1` to `RingEquiv.ofBijective φ' hbij`. Establish `hei : Topology.IsInducing e`. Use `Topology.IsInducing.of_comp ?_ continuous_subtype_val hind` and prove the remaining obligations. Conclude with `hφc.subtype_mk hmem`.

Establish `hes : Continuous e.symm` using `(e.toEquiv.toHomeomorphOfIsInducing hei).symm.continuous`. Set `ψ : ↥Bw.Kw.1 →+* Om l` to `j.1.comp (e.symm : ↥Bw.Kw.1 →+* w.adicCompletion E)`. Establish `hψc : Continuous ψ` using `j.2.comp hes`. Establish `hlin : ∀ a : ℚ_[l], ψ (algebraMap ℚ_[l] ↥Bw.Kw.1 a) = algebraMap ℚ_[l] (Om l) a` using `fun a => by`. Establish `c1 : Continuous fun a : ℚ_[l] => ψ (algebraMap ℚ_[l] ↥Bw.Kw.1 a)` using `hψc.comp (continuous_algebraMap ℚ_[l] ↥Bw.Kw.1)`.

Establish `c2 : Continuous fun a : ℚ_[l] => algebraMap ℚ_[l] (Om l) a` using `continuous_algebraMap ℚ_[l] (Om l)`. Use `congrFun ((Padic.denseRange_ratCast l).equalizer c1 c2 (funext fun q => ?_)) a` and prove the remaining obligations. Simplify using the standard rewrite rules. Set `μ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l` to `{ ψ with commutes' := hlin }`. Set `τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1` to `μ.codRestrict LL'.1.toSubalgebra fun x => hLL (Bw.LL_split μ x)`.

Establish `hτ : ∀ x (hx : φ x ∈ Bw.Kw.1), ((τ ⟨φ x, hx⟩ : ↥LL'.1) : Om l) = j.1 x` using `fun x hx => by`. Establish `: e.symm ⟨φ x, hx⟩ = x` using `e.symm_apply_apply x`. Use `show j.1 (e.symm ⟨φ x, hx⟩) = j.1 x`. Rewrite using `[this]`. Establish `key : ∀ y : E, ((τ (GlobalTheory.CompanionTheory.EmbUniq.toKw Bw y) : ↥LL'.1) : Om l) = j.1 (algebraMap E _ y)` using `fun y => by`.

Establish `e1 : GlobalTheory.CompanionTheory.EmbUniq.toKw Bw y = ⟨φ (algebraMap E _ y), hmem _⟩` using `Subtype.ext (hφE y).symm`. Rewrite using `[e1]`. Conclude with `hτ _ _`. Establish `hd : DenseRange (GlobalTheory.CompanionTheory.EmbUniq.toKw Bw)` using `fun k => by`. Rewrite using `[Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, ← Set.range_comp]`.

Conclude with `Bw.j_dense k.2`. Establish `hc : ∀ t : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1, Continuous fun x => ((t x : ↥LL'.1) : Om l)` using `fun t => by`. Use `Metric.continuous_iff.2 fun b ε hε => ⟨ε, hε, fun a h => ?_⟩` and prove the remaining obligations. Establish `h' : ‖(a : Om l) - (b : Om l)‖ < ε` using `by rwa [← dist_eq_norm]`. Rewrite using `[dist_eq_norm]`.

Establish `e2 : ((t a : ↥LL'.1) : Om l) - ((t b : ↥LL'.1) : Om l) = ((t (a - b) : ↥LL'.1) : Om l)`. Simplify using the standard rewrite rules. Rewrite using `[e2, GlobalTheory.CompanionTheory.EmbUniq.norm_coe_algHom]`. Conclude with `h'`. Use `⟨φ, τ, hφc, hφE, fun x => ⟨hmem x, hτ x _⟩, fun τ' => ⟨fun h => ?_, ?_⟩⟩` and prove the remaining obligations.

Use `AlgHom.ext fun x => Subtype.ext (congrFun (hd.equalizer (hc τ') (hc τ) (funext fun y => ?_)) x)` and prove the remaining obligations. Conclude with `(h y).symm.trans (key y).symm`. Introduce and unpack `rfl y`. Conclude with `(key y).symm`.
-/
theorem embeddings_of_continuous : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw → ∀ (LL' : FinExt l), Bw.LL.1 ≤ LL'.1 →
    ∀ (j : {j : w.adicCompletion E →+* Qbar l // Continuous j}),
    ∃ (φ : w.adicCompletion E →+* Om l) (τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), Continuous φ ∧
      (∀ y : E, φ (algebraMap E (w.adicCompletion E) y) = Bw.j (algebraMap E Ω y)) ∧
      (∀ x, ∃ hx : φ x ∈ Bw.Kw.1, ((τ ⟨φ x, hx⟩ : ↥LL'.1) : Om l) = j.1 x) ∧
      ∀ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1,
        IsInduced Bw (j.1.comp (algebraMap E (w.adicCompletion E))) τ' ↔ τ' = τ := by
  intro E Ω _ _ _ _ _ l _ w A hA O _ _ _ Bw hI LL' hLL j
  have hKL : Bw.Kw.1 ≤ LL'.1 := fun x hx => hLL (Bw.LL_split Bw.Kw.1.val ⟨x, hx⟩)
  obtain ⟨⟨φ, hφc⟩, hφ, -⟩ := GlobalTheory.CompanionTheory.EmbUniq.existsUnique_continuous_induced w A hA O Bw hI LL'
    (IntermediateField.inclusion hKL)
  have hφE : ∀ y : E, φ (algebraMap E (w.adicCompletion E) y) = Bw.j (algebraMap E Ω y) := fun y => hφ y
  haveI : FiniteDimensional ℚ_[l] ↥Bw.Kw.1 := Bw.Kw.2
  have hKc : IsClosed (Bw.Kw.1 : Set (Om l)) :=
    Submodule.closed_of_finiteDimensional (Subalgebra.toSubmodule Bw.Kw.1.toSubalgebra)
  have hmem : ∀ x, φ x ∈ Bw.Kw.1 := fun x =>
    (HeightOneSpectrum.denseRange_algebraMap E w).induction_on (p := fun x => φ x ∈ (Bw.Kw.1 : Set (Om l))) x
      (hKc.preimage hφc) (fun y => by
        show φ _ ∈ Bw.Kw.1
        rw [hφE]; exact Bw.j_E y)
  have hind := isInducing w φ hφc
  have hrc : IsClosed (Set.range φ) :=
    (AddMonoidHom.isUniformInducing_of_isInducing (f := φ.toAddMonoidHom) hind).isComplete_range.isClosed
  have hsurj : ∀ k : ↥Bw.Kw.1, ∃ x, φ x = k := fun k => by
    have h1 : (k : Om l) ∈ closure (Set.range fun x : E => Bw.j (algebraMap E Ω x)) := Bw.j_dense k.2
    have h2 : (Set.range fun x : E => Bw.j (algebraMap E Ω x)) ⊆ Set.range φ := by
      rintro _ ⟨y, rfl⟩
      exact ⟨_, hφE y⟩
    exact hrc.closure_subset_iff.2 h2 h1
  let φ' : w.adicCompletion E →+* ↥Bw.Kw.1 := φ.codRestrict Bw.Kw.1 hmem
  have hbij : Function.Bijective φ' := ⟨fun a b h => φ.injective (congrArg Subtype.val h), fun k => by
    obtain ⟨x, hx⟩ := hsurj k
    exact ⟨x, Subtype.ext hx⟩⟩
  let e : w.adicCompletion E ≃+* ↥Bw.Kw.1 := RingEquiv.ofBijective φ' hbij
  have hei : Topology.IsInducing e := by
    refine Topology.IsInducing.of_comp ?_ continuous_subtype_val hind
    exact hφc.subtype_mk hmem
  have hes : Continuous e.symm := (e.toEquiv.toHomeomorphOfIsInducing hei).symm.continuous
  let ψ : ↥Bw.Kw.1 →+* Om l := j.1.comp (e.symm : ↥Bw.Kw.1 →+* w.adicCompletion E)
  have hψc : Continuous ψ := j.2.comp hes
  have hlin : ∀ a : ℚ_[l], ψ (algebraMap ℚ_[l] ↥Bw.Kw.1 a) = algebraMap ℚ_[l] (Om l) a := fun a => by
    have c1 : Continuous fun a : ℚ_[l] => ψ (algebraMap ℚ_[l] ↥Bw.Kw.1 a) :=
      hψc.comp (continuous_algebraMap ℚ_[l] ↥Bw.Kw.1)
    have c2 : Continuous fun a : ℚ_[l] => algebraMap ℚ_[l] (Om l) a := continuous_algebraMap ℚ_[l] (Om l)
    refine congrFun ((Padic.denseRange_ratCast l).equalizer c1 c2 (funext fun q => ?_)) a
    simp
  let μ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l := { ψ with commutes' := hlin }
  let τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1 := μ.codRestrict LL'.1.toSubalgebra fun x => hLL (Bw.LL_split μ x)
  have hτ : ∀ x (hx : φ x ∈ Bw.Kw.1), ((τ ⟨φ x, hx⟩ : ↥LL'.1) : Om l) = j.1 x := fun x hx => by
    have : e.symm ⟨φ x, hx⟩ = x := e.symm_apply_apply x
    show j.1 (e.symm ⟨φ x, hx⟩) = j.1 x
    rw [this]
  have key : ∀ y : E, ((τ (GlobalTheory.CompanionTheory.EmbUniq.toKw Bw y) : ↥LL'.1) : Om l) = j.1 (algebraMap E _ y) := fun y => by
    have e1 : GlobalTheory.CompanionTheory.EmbUniq.toKw Bw y = ⟨φ (algebraMap E _ y), hmem _⟩ := Subtype.ext (hφE y).symm
    rw [e1]
    exact hτ _ _
  have hd : DenseRange (GlobalTheory.CompanionTheory.EmbUniq.toKw Bw) := fun k => by
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, ← Set.range_comp]
    exact Bw.j_dense k.2
  have hc : ∀ t : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1, Continuous fun x => ((t x : ↥LL'.1) : Om l) := fun t => by
    refine Metric.continuous_iff.2 fun b ε hε => ⟨ε, hε, fun a h => ?_⟩
    have h' : ‖(a : Om l) - (b : Om l)‖ < ε := by rwa [← dist_eq_norm]
    rw [dist_eq_norm]
    have e2 : ((t a : ↥LL'.1) : Om l) - ((t b : ↥LL'.1) : Om l) = ((t (a - b) : ↥LL'.1) : Om l) := by
      simp
    rw [e2, GlobalTheory.CompanionTheory.EmbUniq.norm_coe_algHom]
    exact h'
  refine ⟨φ, τ, hφc, hφE, fun x => ⟨hmem x, hτ x _⟩, fun τ' => ⟨fun h => ?_, ?_⟩⟩
  · refine AlgHom.ext fun x => Subtype.ext (congrFun (hd.equalizer (hc τ') (hc τ) (funext fun y => ?_)) x)
    exact (h y).symm.trans (key y).symm
  · rintro rfl y
    exact (key y).symm

end GlobalTheory.CompanionTheory.EmbBridge
