import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TransferenceA

namespace ReciprocityTheory.ChartRestriction.G.T0

open Module Submodule Matrix

/- English proof (translation)
Use `set V : Submodule ℝ E := Submodule.span ℝ (Set.range u) with hV`. Establish `hfin : Module.finrank ℝ V = N` using `by rw [finrank_span_eq_card hu, Fintype.card_fin]`. Use `haveI : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Set.finite_range u)`. Set `f : OrthonormalBasis (Fin N) ℝ V` to `(stdOrthonormalBasis ℝ V).reindex (finCongr hfin)`. Set `uV : Fin N → V` to `fun i => ⟨u i, Submodule.subset_span ⟨i, rfl⟩⟩`.

Establish `huV : LinearIndependent ℝ uV` using `LinearIndependent.of_comp V.subtype hu`. Set `vb : Fin N → (Fin N → ℝ)` to `fun i => (f.repr (uV i)).ofLp`. Establish `hvb : LinearIndependent ℝ vb` using `huV.map' (f.repr.toLinearEquiv.trans (WithLp.linearEquiv 2 ℝ (Fin N → ℝ))).toLinearMap (LinearEquiv.ker _)`. Use `haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩`. Set `b : Module.Basis (Fin N) ℝ (Fin N → ℝ)` to `basisOfLinearIndependentOfCardEqFinrank hvb (by simp)`.

Establish `hb : ∀ i, b i = vb i` using `fun i => by simp [b]`. Use `set d := (Matrix.of ⇑b).det with hd`. Establish `hgram : (gram ℝ u).det = d ^ 2`. Establish `hG : gram ℝ u = Matrix.of ⇑b * (Matrix.of ⇑b).transpose`. Use extensionality with `i j`.

Rewrite using `[Matrix.gram_apply, Matrix.mul_apply]`. Simplify using `only [Matrix.of_apply, Matrix.transpose_apply, hb]`. Establish `e1 : inner ℝ (u i) (u j) = inner ℝ (f.repr (uV i)) (f.repr (uV j))`. Rewrite using `[LinearIsometryEquiv.inner_map_map]`. Both sides reduce to the same expression.

Rewrite using `[e1, PiLp.inner_apply]`. Simplify using `[vb, mul_comm]`. Rewrite using `[hG, Matrix.det_mul, Matrix.det_transpose, sq]`. Use `set t : ℝ := |d| ^ ((N : ℝ)⁻¹) with ht`. Establish `ht0 : 0 ≤ t` using `Real.rpow_nonneg (abs_nonneg _) _`.

Establish `htN : t ^ N = |d|` using `Real.rpow_inv_natCast_pow (abs_nonneg _) (by omega)`. Use `haveI : Countable ↥(Submodule.span ℤ (Set.range b)).toAddSubgroup := by`. Establish `hc : ((Submodule.span ℤ (Set.range b)).toAddSubgroup : Set (Fin N → ℝ)) ⊆ Set.range (fun c : Fin N → ℤ => ∑ i, c i • b i)`. Introduce `z hz`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).mp hz`.

Conclude with `⟨c, hc⟩`. Conclude with `((Set.countable_range _).mono hc).to_subtype`. Take `⟨x, hx0, hxs⟩` from `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure (μ := MeasureTheory.volume) (L := (Submodule.span ℤ (Set.range b)).toAddSubgroup) (s := Set.Icc (-(fun _ : Fin N => t)) (fun _ : Fin N => t)) (ZSpan.isAddFundamentalDomain b MeasureTheory.volume) (fun z hz …`. Rewrite using `[ZSpan.volume_fundamentalDomain, Real.volume_Icc_pi, Module.finrank_fin_fun]`. Establish `e2 : ∏ i : Fin N, ENNReal.ofReal ((fun _ : Fin N => t) i - (-(fun _ : Fin N => t)) i) = 2 ^ N * ENNReal.ofReal |d|`.

Simplify using `only [Pi.neg_apply, sub_neg_eq_add, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Rewrite using `[← ENNReal.ofReal_pow (by positivity), show t + t = 2 * t by ring, mul_pow, htN, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]`. Simplify using the standard rewrite rules. Rewrite using `[e2, ← hd, mul_comm])`. Take `⟨y, hy⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).mp x.2`.

Establish `hxj : ∀ j, |(x : Fin N → ℝ) j| ≤ t` using `fun j => abs_le.mpr ⟨by simpa using hxs.1 j, hxs.2 j⟩`. Use `⟨y, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Apply `hx0` to reduce the goal to its premises. Establish `: ((x : Fin N → ℝ)) = 0` using `by rw [← hy]; simp`.

Conclude with `Subtype.ext this`. Establish `hcoe : (∑ i, y i • u i) = ((∑ i, y i • uV i : V) : E)` using `by simp [uV]`. Establish `hrepr : (f.repr (∑ i, y i • uV i)).ofLp = (x : Fin N → ℝ)`. Rewrite using `[← hy]`. Use extensionality with `j`.

Simplify using `[map_sum, hb, vb, Finset.sum_apply]`. Establish `hnorm : ‖∑ i, y i • u i‖ ^ 2 = ∑ j, ((x : Fin N → ℝ) j) ^ 2`. Rewrite using `[hcoe]`. Express the relevant statement in the definitionally equal form `‖(∑ i, y i • uV i : V)‖ ^ 2 = _`. Rewrite using `[← f.repr.norm_map, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), hrepr]`.

Simplify using `[Real.norm_eq_abs, sq_abs]`. Rewrite using `[hnorm]`. Combine the equalities or inequalities in the displayed calculation. Use `pow_le_pow_left₀ (abs_nonneg _) (hxj j) 2` as an intermediate fact. Rewrite `this` using `[sq_abs]`. Then use the resulting hypothesis.

Use `_ = N * (gram ℝ u).det ^ (1 / (N : ℝ)) := by`. Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hgram, ht, one_div]`. Use `congr 1`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg d), mul_comm, Real.rpow_mul (abs_nonneg d), Real.rpow_natCast, sq_abs]`.
-/
theorem exists_int_combination_norm_sq_le_gram_det {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {N : ℕ}
    (hN : 0 < N) (u : Fin N → E) (hu : LinearIndependent ℝ u) :
    ∃ y : Fin N → ℤ, y ≠ 0 ∧ ‖∑ i, y i • u i‖ ^ 2 ≤ N * (gram ℝ u).det ^ (1 / (N : ℝ)) := by
  classical
  set V : Submodule ℝ E := Submodule.span ℝ (Set.range u) with hV
  have hfin : Module.finrank ℝ V = N := by rw [finrank_span_eq_card hu, Fintype.card_fin]
  haveI : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Set.finite_range u)
  let f : OrthonormalBasis (Fin N) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr hfin)
  let uV : Fin N → V := fun i => ⟨u i, Submodule.subset_span ⟨i, rfl⟩⟩
  have huV : LinearIndependent ℝ uV := LinearIndependent.of_comp V.subtype hu
  let vb : Fin N → (Fin N → ℝ) := fun i => (f.repr (uV i)).ofLp
  have hvb : LinearIndependent ℝ vb :=
    huV.map' (f.repr.toLinearEquiv.trans (WithLp.linearEquiv 2 ℝ (Fin N → ℝ))).toLinearMap
      (LinearEquiv.ker _)
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let b : Module.Basis (Fin N) ℝ (Fin N → ℝ) :=
    basisOfLinearIndependentOfCardEqFinrank hvb (by simp)
  have hb : ∀ i, b i = vb i := fun i => by simp [b]
  set d := (Matrix.of ⇑b).det with hd
  have hgram : (gram ℝ u).det = d ^ 2 := by
    have hG : gram ℝ u = Matrix.of ⇑b * (Matrix.of ⇑b).transpose := by
      ext i j
      rw [Matrix.gram_apply, Matrix.mul_apply]
      simp only [Matrix.of_apply, Matrix.transpose_apply, hb]
      have e1 : inner ℝ (u i) (u j) = inner ℝ (f.repr (uV i)) (f.repr (uV j)) := by
        rw [LinearIsometryEquiv.inner_map_map]
        rfl
      rw [e1, PiLp.inner_apply]
      simp [vb, mul_comm]
    rw [hG, Matrix.det_mul, Matrix.det_transpose, sq]
  set t : ℝ := |d| ^ ((N : ℝ)⁻¹) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg (abs_nonneg _) _
  have htN : t ^ N = |d| := Real.rpow_inv_natCast_pow (abs_nonneg _) (by omega)
  haveI : Countable ↥(Submodule.span ℤ (Set.range b)).toAddSubgroup := by
    have hc : ((Submodule.span ℤ (Set.range b)).toAddSubgroup : Set (Fin N → ℝ)) ⊆
        Set.range (fun c : Fin N → ℤ => ∑ i, c i • b i) := by
      intro z hz
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hz
      exact ⟨c, hc⟩
    exact ((Set.countable_range _).mono hc).to_subtype
  obtain ⟨x, hx0, hxs⟩ := MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
    (μ := MeasureTheory.volume) (L := (Submodule.span ℤ (Set.range b)).toAddSubgroup)
    (s := Set.Icc (-(fun _ : Fin N => t)) (fun _ : Fin N => t))
    (ZSpan.isAddFundamentalDomain b MeasureTheory.volume)
    (fun z hz => ⟨neg_le_neg hz.2, by simpa using neg_le_neg hz.1⟩) (convex_Icc _ _) isCompact_Icc
    (by
      rw [ZSpan.volume_fundamentalDomain, Real.volume_Icc_pi, Module.finrank_fin_fun]
      have e2 : ∏ i : Fin N, ENNReal.ofReal ((fun _ : Fin N => t) i - (-(fun _ : Fin N => t)) i) =
          2 ^ N * ENNReal.ofReal |d| := by
        simp only [Pi.neg_apply, sub_neg_eq_add, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
        rw [← ENNReal.ofReal_pow (by positivity), show t + t = 2 * t by ring, mul_pow, htN,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
        simp
      rw [e2, ← hd, mul_comm])
  obtain ⟨y, hy⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp x.2
  have hxj : ∀ j, |(x : Fin N → ℝ) j| ≤ t := fun j =>
    abs_le.mpr ⟨by simpa using hxs.1 j, hxs.2 j⟩
  refine ⟨y, ?_, ?_⟩
  · rintro rfl
    apply hx0
    have : ((x : Fin N → ℝ)) = 0 := by rw [← hy]; simp
    exact Subtype.ext this
  have hcoe : (∑ i, y i • u i) = ((∑ i, y i • uV i : V) : E) := by simp [uV]
  have hrepr : (f.repr (∑ i, y i • uV i)).ofLp = (x : Fin N → ℝ) := by
    rw [← hy]
    ext j
    simp [map_sum, hb, vb, Finset.sum_apply]
  have hnorm : ‖∑ i, y i • u i‖ ^ 2 = ∑ j, ((x : Fin N → ℝ) j) ^ 2 := by
    rw [hcoe]
    change ‖(∑ i, y i • uV i : V)‖ ^ 2 = _
    rw [← f.repr.norm_map, EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), hrepr]
    simp [Real.norm_eq_abs, sq_abs]
  rw [hnorm]
  calc ∑ j, ((x : Fin N → ℝ) j) ^ 2 ≤ ∑ _j : Fin N, t ^ 2 := Finset.sum_le_sum fun j _ => by
        have := pow_le_pow_left₀ (abs_nonneg _) (hxj j) 2
        rwa [sq_abs] at this
    _ = N * (gram ℝ u).det ^ (1 / (N : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hgram, ht, one_div]
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg d), mul_comm,
          Real.rpow_mul (abs_nonneg d), Real.rpow_natCast, sq_abs]

/- English proof (translation)
Conclude with `AddSubgroup.nsmul_relIndex_mem H hx`.
-/
theorem relIndex_nsmul_mem {E : Type*} [AddCommGroup E] (H L : AddSubgroup E) {x : E}
    (hx : x ∈ L) : H.relIndex L • x ∈ H := by
  exact AddSubgroup.nsmul_relIndex_mem H hx

/- English proof (translation)
Use `set S : AddSubgroup E := (span ℤ (Set.range w)).toAddSubgroup with hS`. Use `set I : ℕ := S.relIndex Λ with hIdef`. Establish `hI0 : (I : ℝ) ≠ 0` using `Nat.cast_ne_zero.mpr hI`. Use `set V : Submodule ℝ E := Submodule.span ℝ (Set.range w) with hV`. Establish `hSV : ∀ x ∈ S, x ∈ V`.

Introduce `x hx`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).mp hx`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Int.cast_smul_eq_zsmul ℝ]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Establish `hΛV : ∀ x ∈ Λ, x ∈ V`. Introduce `x hx`. Establish `h1 : I • x ∈ S` using `relIndex_nsmul_mem S Λ hx`. Establish `h2 : (I : ℝ) • x ∈ V` using `by rw [Nat.cast_smul_eq_nsmul]; exact hSV _ h1`. Establish `h3` using `V.smul_mem ((I : ℝ)⁻¹) h2`.

Rewrite `h3` using `[smul_smul, inv_mul_cancel₀ hI0, one_smul]`. Then use the resulting hypothesis. Establish `hSΛ : S ≤ Λ`. Introduce `x hx`. Establish `hle : span ℤ (Set.range w) ≤ Λ.toIntSubmodule` using `Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hΛ i)`. Conclude with `hle hx`.

Establish `hfin : Module.finrank ℝ V = N` using `by rw [finrank_span_eq_card hw, Fintype.card_fin]`. Use `haveI : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Set.finite_range w)`. Set `f : OrthonormalBasis (Fin N) ℝ V` to `(stdOrthonormalBasis ℝ V).reindex (finCongr hfin)`. Set `wV : Fin N → V` to `fun i => ⟨w i, Submodule.subset_span ⟨i, rfl⟩⟩`. Establish `hwV : LinearIndependent ℝ wV` using `LinearIndependent.of_comp V.subtype hw`.

Set `φ : V ≃ₗ[ℝ] (Fin N → ℝ)` to `f.repr.toLinearEquiv.trans (WithLp.linearEquiv 2 ℝ (Fin N → ℝ))`. Establish `hφ : ∀ v : V, φ v = (f.repr v).ofLp` using `fun v => rfl`. Set `vb : Fin N → (Fin N → ℝ)` to `fun i => φ (wV i)`. Establish `hvb : LinearIndependent ℝ vb` using `hwV.map' φ.toLinearMap (LinearEquiv.ker _)`. Use `haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩`.

Set `b : Module.Basis (Fin N) ℝ (Fin N → ℝ)` to `basisOfLinearIndependentOfCardEqFinrank hvb (by simp)`. Establish `hb : ∀ i, b i = φ (wV i)` using `fun i => by simp [b, vb]`. Use `set d := (Matrix.of ⇑b).det with hd`. Establish `hgram : (gram ℝ w).det = d ^ 2`. Establish `hG : gram ℝ w = Matrix.of ⇑b * (Matrix.of ⇑b).transpose`.

Use extensionality with `i j`. Rewrite using `[Matrix.gram_apply, Matrix.mul_apply]`. Simplify using `only [Matrix.of_apply, Matrix.transpose_apply, hb, hφ]`. Establish `e1 : inner ℝ (w i) (w j) = inner ℝ (f.repr (wV i)) (f.repr (wV j))`. Rewrite using `[LinearIsometryEquiv.inner_map_map]`.

Both sides reduce to the same expression. Rewrite using `[e1, PiLp.inner_apply]`. Simplify using `[mul_comm]`. Rewrite using `[hG, Matrix.det_mul, Matrix.det_transpose, sq]`. Establish `hnorm : ∀ v : V, ‖(v : E)‖ ^ 2 = ∑ j, (φ v j) ^ 2`.

Introduce `v`. Express the relevant statement in the definitionally equal form `‖v‖ ^ 2 = _`. Rewrite using `[← f.repr.norm_map, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]`. Simplify using `[Real.norm_eq_abs, sq_abs, hφ]`. Set `χ : V →+ (Fin N → ℝ)` to `φ.toLinearMap.toAddMonoidHom`.

Establish `hχ : Function.Injective χ` using `φ.injective`. Set `ι : V →+ E` to `V.subtype.toAddMonoidHom`. Set `L2g : AddSubgroup (Fin N → ℝ)` to `(Λ.comap ι).map χ`. Set `L1 : Submodule ℤ (Fin N → ℝ)` to `span ℤ (Set.range b)`. Establish `hL1g : L1.toAddSubgroup = (S.comap ι).map χ`.

Use extensionality with `x`. Simplify using `only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_map, AddSubgroup.mem_comap]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).mp hx`.

Use `⟨∑ i, c i • wV i, ?_, ?_⟩` and prove the remaining obligations. Use `show ((∑ i, c i • wV i : V) : E) ∈ S`. Rewrite using `[hS, Submodule.mem_toAddSubgroup, Submodule.mem_span_range_iff_exists_fun ℤ]`. Conclude with `⟨c, by simp [wV]⟩`. Simplify using `[χ, hb, map_sum]`.

Introduce and unpack `⟨v, hv, rfl⟩`. Establish `hv' : (v : E) ∈ span ℤ (Set.range w)` using `hv`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).mp hv'`. Establish `hvc : v = ∑ i, c i • wV i` using `Subtype.ext (by simp [wV, ← hc])`. Rewrite using `[hvc]`.

Conclude with `(Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨c, by simp [χ, hb, map_sum]⟩`. Establish `hΛr : Λ ≤ ι.range` using `fun x hx => ⟨⟨x, hΛV x hx⟩, rfl⟩`. Establish `hrel : L1.toAddSubgroup.relIndex L2g = I`. Rewrite using `[hL1g, AddSubgroup.relIndex_map_map_of_injective _ _ hχ, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self hΛr]`. Set `L2 : Submodule ℤ (Fin N → ℝ)` to `L2g.toIntSubmodule`.

Establish `hL12 : L1 ≤ L2`. Introduce `x hx`. Establish `h1 : x ∈ L1.toAddSubgroup` using `hx`. Rewrite `h1` using `[hL1g]`. Conclude with `AddSubgroup.map_mono (AddSubgroup.comap_mono hSΛ) h1`.

Set `b' : Module.Basis (Fin N) ℝ (Fin N → ℝ)` to `b.unitsSMul (fun _ => Units.mk0 ((I : ℝ)⁻¹) (inv_ne_zero hI0))`. Establish `hb' : ∀ i, b' i = (I : ℝ)⁻¹ • b i` using `fun i => by show (b.unitsSMul _) i = _`. Rewrite using `[Module.Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0]`. Establish `hL2sub : (L2 : Set (Fin N → ℝ)) ⊆ span ℤ (Set.range b')`. Introduce `x hx`.

Establish `h1 : L1.toAddSubgroup.relIndex L2g • x ∈ L1.toAddSubgroup` using `relIndex_nsmul_mem _ _ hx`. Rewrite `h1` using `[hrel]`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).mp h1`. Use `(Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨c, ?_⟩` and prove the remaining obligations. Establish `hx' : x = (I : ℝ)⁻¹ • (I • x)`.

Rewrite using `[← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hI0, one_smul]`. Rewrite using `[hx', ← hc, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hb', smul_comm]`. Use `haveI : DiscreteTopology L2 := DiscreteTopology.of_subset (inferInstance : DiscreteTopology (span ℤ (Set.range b'))) hL2sub`.

Use `haveI : IsZLattice ℝ L2 := ⟨by`. Rewrite using `[eq_top_iff, ← b.span_eq]`. Conclude with `Submodule.span_le.mpr fun x hx => Submodule.subset_span (hL12 (Submodule.subset_span hx))⟩`. Establish `hcov1 : ZLattice.covolume L1 MeasureTheory.volume = |d|`. Rewrite using `[ZLattice.covolume_eq_measure_fundamentalDomain L1 MeasureTheory.volume (ZSpan.isAddFundamentalDomain b MeasureTheory.volume), MeasureTheory.Measure.real, ZSpan.volume_fundamentalDomain, ENNReal.toReal_ofReal (abs_nonneg _)]`.

Establish `hcov2 : ZLattice.covolume L2 MeasureTheory.volume = |d| / I`. Establish `h` using `ZLattice.covolume_div_covolume_eq_relIndex L1 L2 hL12`. Establish `h' : L1.toAddSubgroup.relIndex L2.toAddSubgroup = I` using `hrel`. Rewrite `h` using `[h', hcov1]`. Establish `hpos : 0 < ZLattice.covolume L2 MeasureTheory.volume` using `ZLattice.covolume_pos L2 _`.

Clear denominators, using `at h ⊢` for the nonvanishing conditions. Combine the linear equalities and inequalities to obtain the conclusion. Set `b2` to `(Module.Free.chooseBasis ℤ L2).ofZLatticeBasis ℝ L2`. Establish `hspan2 : span ℤ (Set.range b2) = L2` using `Module.Basis.ofZLatticeBasis_span ℝ L2 _`. Establish `hF2 : MeasureTheory.IsAddFundamentalDomain L2 (ZSpan.fundamentalDomain b2) MeasureTheory.volume`.

Use `ZSpan.isAddFundamentalDomain b2 MeasureTheory.volume` as an intermediate fact. Rewrite `this` using `[hspan2]`. Then use the resulting hypothesis. Establish `hvolF2 : MeasureTheory.volume (ZSpan.fundamentalDomain b2) = ENNReal.ofReal (|d| / I)`. Rewrite using `[← hcov2, ZLattice.covolume_eq_measure_fundamentalDomain L2 MeasureTheory.volume hF2, MeasureTheory.Measure.real, ENNReal.ofReal_toReal (ZSpan.fundamentalDomain_isBounded b2).measure_lt_top.ne]`. Use `haveI : Countable ↥L2.toAddSubgroup := by`.

Establish `hc : ((L2.toAddSubgroup : AddSubgroup (Fin N → ℝ)) : Set (Fin N → ℝ)) ⊆ Set.range (fun c : Fin N → ℤ => ∑ i, c i • b' i)`. Introduce `z hz`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).mp (hL2sub hz)`. Conclude with `⟨c, hc⟩`. Conclude with `((Set.countable_range _).mono hc).to_subtype`.

Use `haveI : DiscreteTopology ↥L2.toAddSubgroup := inferInstanceAs (DiscreteTopology L2)`. Use `set t : ℝ := (|d| / I) ^ ((N : ℝ)⁻¹) with ht`. Establish `hq : 0 ≤ |d| / I` using `div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)`. Establish `ht0 : 0 ≤ t` using `Real.rpow_nonneg hq _`. Establish `htN : t ^ N = |d| / I` using `Real.rpow_inv_natCast_pow hq (by omega)`.

Take `⟨x, hx0, hxs⟩` from `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure (μ := MeasureTheory.volume) (L := L2.toAddSubgroup) (s := Set.Icc (-(fun _ : Fin N => t)) (fun _ : Fin N => t)) hF2 (fun z hz => ⟨neg_le_neg hz.2, by simpa using neg_le_neg hz.1⟩) (convex_Icc _ _) isCompac …`. Rewrite using `[hvolF2, Real.volume_Icc_pi, Module.finrank_fin_fun]`. Establish `e2 : ∏ i : Fin N, ENNReal.ofReal ((fun _ : Fin N => t) i - (-(fun _ : Fin N => t)) i) = 2 ^ N * ENNReal.ofReal (|d| / I)`. Simplify using `only [Pi.neg_apply, sub_neg_eq_add, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Rewrite using `[← ENNReal.ofReal_pow (by positivity), show t + t = 2 * t by ring, mul_pow, htN, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]`.

Simplify using the standard rewrite rules. Rewrite using `[e2, mul_comm])`. Establish `hxL2 : (x : Fin N → ℝ) ∈ L2g` using `x.2`. Take `⟨v, hv, hvx⟩` from `AddSubgroup.mem_map.mp hxL2`. Establish `hxj : ∀ j, |(x : Fin N → ℝ) j| ≤ t` using `fun j => abs_le.mpr ⟨by simpa using hxs.1 j, hxs.2 j⟩`.

Use `⟨(v : E), hv, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Apply `hx0` to reduce the goal to its premises. Establish `hv0 : v = 0` using `Subtype.ext h0`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[← hvx, hv0, map_zero]`. Both sides reduce to the same expression. Establish `hxv : ∀ j, φ v j = (x : Fin N → ℝ) j` using `fun j => by rw [← hvx]; rfl`. Rewrite using `[hnorm v]`. Combine the equalities or inequalities in the displayed calculation.

Use `pow_le_pow_left₀ (abs_nonneg _) (hxj j) 2` as an intermediate fact. Rewrite `this` using `[sq_abs, ← hxv j]`. Then use the resulting hypothesis. Use `_ = N * ((gram ℝ w).det / (I : ℝ) ^ 2) ^ (1 / (N : ℝ)) := by`. Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hgram, ht, one_div]`. Use `congr 1`.

Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hq, mul_comm, Real.rpow_mul hq, Real.rpow_natCast, div_pow, sq_abs]`.
-/
theorem exists_ne_zero_mem_norm_sq_le_gram_det_div_relIndex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {N : ℕ}
    (hN : 0 < N) (w : Fin N → E) (hw : LinearIndependent ℝ w) (Λ : AddSubgroup E)
    (hΛ : ∀ i, w i ∈ Λ) (hI : (span ℤ (Set.range w)).toAddSubgroup.relIndex Λ ≠ 0) :
    ∃ v ∈ Λ, v ≠ 0 ∧ ‖v‖ ^ 2 ≤ N * ((gram ℝ w).det /
      ((span ℤ (Set.range w)).toAddSubgroup.relIndex Λ : ℝ) ^ 2) ^ (1 / (N : ℝ)) := by
  classical
  set S : AddSubgroup E := (span ℤ (Set.range w)).toAddSubgroup with hS
  set I : ℕ := S.relIndex Λ with hIdef
  have hI0 : (I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hI
  set V : Submodule ℝ E := Submodule.span ℝ (Set.range w) with hV
  have hSV : ∀ x ∈ S, x ∈ V := by
    intro x hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hΛV : ∀ x ∈ Λ, x ∈ V := by
    intro x hx
    have h1 : I • x ∈ S := relIndex_nsmul_mem S Λ hx
    have h2 : (I : ℝ) • x ∈ V := by rw [Nat.cast_smul_eq_nsmul]; exact hSV _ h1
    have h3 := V.smul_mem ((I : ℝ)⁻¹) h2
    rwa [smul_smul, inv_mul_cancel₀ hI0, one_smul] at h3
  have hSΛ : S ≤ Λ := by
    intro x hx
    have hle : span ℤ (Set.range w) ≤ Λ.toIntSubmodule :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hΛ i)
    exact hle hx
  have hfin : Module.finrank ℝ V = N := by rw [finrank_span_eq_card hw, Fintype.card_fin]
  haveI : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Set.finite_range w)
  let f : OrthonormalBasis (Fin N) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr hfin)
  let wV : Fin N → V := fun i => ⟨w i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hwV : LinearIndependent ℝ wV := LinearIndependent.of_comp V.subtype hw
  let φ : V ≃ₗ[ℝ] (Fin N → ℝ) := f.repr.toLinearEquiv.trans (WithLp.linearEquiv 2 ℝ (Fin N → ℝ))
  have hφ : ∀ v : V, φ v = (f.repr v).ofLp := fun v => rfl
  let vb : Fin N → (Fin N → ℝ) := fun i => φ (wV i)
  have hvb : LinearIndependent ℝ vb := hwV.map' φ.toLinearMap (LinearEquiv.ker _)
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let b : Module.Basis (Fin N) ℝ (Fin N → ℝ) :=
    basisOfLinearIndependentOfCardEqFinrank hvb (by simp)
  have hb : ∀ i, b i = φ (wV i) := fun i => by simp [b, vb]
  set d := (Matrix.of ⇑b).det with hd
  have hgram : (gram ℝ w).det = d ^ 2 := by
    have hG : gram ℝ w = Matrix.of ⇑b * (Matrix.of ⇑b).transpose := by
      ext i j
      rw [Matrix.gram_apply, Matrix.mul_apply]
      simp only [Matrix.of_apply, Matrix.transpose_apply, hb, hφ]
      have e1 : inner ℝ (w i) (w j) = inner ℝ (f.repr (wV i)) (f.repr (wV j)) := by
        rw [LinearIsometryEquiv.inner_map_map]
        rfl
      rw [e1, PiLp.inner_apply]
      simp [mul_comm]
    rw [hG, Matrix.det_mul, Matrix.det_transpose, sq]
  have hnorm : ∀ v : V, ‖(v : E)‖ ^ 2 = ∑ j, (φ v j) ^ 2 := by
    intro v
    change ‖v‖ ^ 2 = _
    rw [← f.repr.norm_map, EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simp [Real.norm_eq_abs, sq_abs, hφ]
  let χ : V →+ (Fin N → ℝ) := φ.toLinearMap.toAddMonoidHom
  have hχ : Function.Injective χ := φ.injective
  let ι : V →+ E := V.subtype.toAddMonoidHom
  let L2g : AddSubgroup (Fin N → ℝ) := (Λ.comap ι).map χ
  let L1 : Submodule ℤ (Fin N → ℝ) := span ℤ (Set.range b)
  have hL1g : L1.toAddSubgroup = (S.comap ι).map χ := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_map, AddSubgroup.mem_comap]
    constructor
    · intro hx
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
      refine ⟨∑ i, c i • wV i, ?_, ?_⟩
      · show ((∑ i, c i • wV i : V) : E) ∈ S
        rw [hS, Submodule.mem_toAddSubgroup, Submodule.mem_span_range_iff_exists_fun ℤ]
        exact ⟨c, by simp [wV]⟩
      · simp [χ, hb, map_sum]
    · rintro ⟨v, hv, rfl⟩
      have hv' : (v : E) ∈ span ℤ (Set.range w) := hv
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hv'
      have hvc : v = ∑ i, c i • wV i := Subtype.ext (by simp [wV, ← hc])
      rw [hvc]
      exact (Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨c, by simp [χ, hb, map_sum]⟩
  have hΛr : Λ ≤ ι.range := fun x hx => ⟨⟨x, hΛV x hx⟩, rfl⟩
  have hrel : L1.toAddSubgroup.relIndex L2g = I := by
    rw [hL1g, AddSubgroup.relIndex_map_map_of_injective _ _ hχ, AddSubgroup.relIndex_comap,
      AddSubgroup.map_comap_eq_self hΛr]
  let L2 : Submodule ℤ (Fin N → ℝ) := L2g.toIntSubmodule
  have hL12 : L1 ≤ L2 := by
    intro x hx
    have h1 : x ∈ L1.toAddSubgroup := hx
    rw [hL1g] at h1
    exact AddSubgroup.map_mono (AddSubgroup.comap_mono hSΛ) h1
  let b' : Module.Basis (Fin N) ℝ (Fin N → ℝ) := b.unitsSMul (fun _ => Units.mk0 ((I : ℝ)⁻¹) (inv_ne_zero hI0))
  have hb' : ∀ i, b' i = (I : ℝ)⁻¹ • b i := fun i => by
    show (b.unitsSMul _) i = _
    rw [Module.Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0]
  have hL2sub : (L2 : Set (Fin N → ℝ)) ⊆ span ℤ (Set.range b') := by
    intro x hx
    have h1 : L1.toAddSubgroup.relIndex L2g • x ∈ L1.toAddSubgroup := relIndex_nsmul_mem _ _ hx
    rw [hrel] at h1
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp h1
    refine (Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨c, ?_⟩
    have hx' : x = (I : ℝ)⁻¹ • (I • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hI0, one_smul]
    rw [hx', ← hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb', smul_comm]
  haveI : DiscreteTopology L2 := DiscreteTopology.of_subset (inferInstance :
    DiscreteTopology (span ℤ (Set.range b'))) hL2sub
  haveI : IsZLattice ℝ L2 := ⟨by
    rw [eq_top_iff, ← b.span_eq]
    exact Submodule.span_le.mpr fun x hx => Submodule.subset_span (hL12 (Submodule.subset_span hx))⟩
  have hcov1 : ZLattice.covolume L1 MeasureTheory.volume = |d| := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L1 MeasureTheory.volume
      (ZSpan.isAddFundamentalDomain b MeasureTheory.volume), MeasureTheory.Measure.real,
      ZSpan.volume_fundamentalDomain, ENNReal.toReal_ofReal (abs_nonneg _)]
  have hcov2 : ZLattice.covolume L2 MeasureTheory.volume = |d| / I := by
    have h := ZLattice.covolume_div_covolume_eq_relIndex L1 L2 hL12
    have h' : L1.toAddSubgroup.relIndex L2.toAddSubgroup = I := hrel
    rw [h', hcov1] at h
    have hpos : 0 < ZLattice.covolume L2 MeasureTheory.volume := ZLattice.covolume_pos L2 _
    field_simp at h ⊢
    linarith
  let b2 := (Module.Free.chooseBasis ℤ L2).ofZLatticeBasis ℝ L2
  have hspan2 : span ℤ (Set.range b2) = L2 := Module.Basis.ofZLatticeBasis_span ℝ L2 _
  have hF2 : MeasureTheory.IsAddFundamentalDomain L2 (ZSpan.fundamentalDomain b2) MeasureTheory.volume := by
    have := ZSpan.isAddFundamentalDomain b2 MeasureTheory.volume
    rwa [hspan2] at this
  have hvolF2 : MeasureTheory.volume (ZSpan.fundamentalDomain b2) = ENNReal.ofReal (|d| / I) := by
    rw [← hcov2, ZLattice.covolume_eq_measure_fundamentalDomain L2 MeasureTheory.volume hF2,
      MeasureTheory.Measure.real, ENNReal.ofReal_toReal
        (ZSpan.fundamentalDomain_isBounded b2).measure_lt_top.ne]
  haveI : Countable ↥L2.toAddSubgroup := by
    have hc : ((L2.toAddSubgroup : AddSubgroup (Fin N → ℝ)) : Set (Fin N → ℝ)) ⊆
        Set.range (fun c : Fin N → ℤ => ∑ i, c i • b' i) := by
      intro z hz
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hL2sub hz)
      exact ⟨c, hc⟩
    exact ((Set.countable_range _).mono hc).to_subtype
  haveI : DiscreteTopology ↥L2.toAddSubgroup := inferInstanceAs (DiscreteTopology L2)
  set t : ℝ := (|d| / I) ^ ((N : ℝ)⁻¹) with ht
  have hq : 0 ≤ |d| / I := div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
  have ht0 : 0 ≤ t := Real.rpow_nonneg hq _
  have htN : t ^ N = |d| / I := Real.rpow_inv_natCast_pow hq (by omega)
  obtain ⟨x, hx0, hxs⟩ := MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
    (μ := MeasureTheory.volume) (L := L2.toAddSubgroup)
    (s := Set.Icc (-(fun _ : Fin N => t)) (fun _ : Fin N => t))
    hF2 (fun z hz => ⟨neg_le_neg hz.2, by simpa using neg_le_neg hz.1⟩) (convex_Icc _ _) isCompact_Icc
    (by
      rw [hvolF2, Real.volume_Icc_pi, Module.finrank_fin_fun]
      have e2 : ∏ i : Fin N, ENNReal.ofReal ((fun _ : Fin N => t) i - (-(fun _ : Fin N => t)) i) =
          2 ^ N * ENNReal.ofReal (|d| / I) := by
        simp only [Pi.neg_apply, sub_neg_eq_add, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
        rw [← ENNReal.ofReal_pow (by positivity), show t + t = 2 * t by ring, mul_pow, htN,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
        simp
      rw [e2, mul_comm])
  have hxL2 : (x : Fin N → ℝ) ∈ L2g := x.2
  obtain ⟨v, hv, hvx⟩ := AddSubgroup.mem_map.mp hxL2
  have hxj : ∀ j, |(x : Fin N → ℝ) j| ≤ t := fun j =>
    abs_le.mpr ⟨by simpa using hxs.1 j, hxs.2 j⟩
  refine ⟨(v : E), hv, ?_, ?_⟩
  · intro h0
    apply hx0
    have hv0 : v = 0 := Subtype.ext h0
    apply Subtype.ext
    rw [← hvx, hv0, map_zero]
    rfl
  have hxv : ∀ j, φ v j = (x : Fin N → ℝ) j := fun j => by rw [← hvx]; rfl
  rw [hnorm v]
  calc ∑ j, (φ v j) ^ 2 ≤ ∑ _j : Fin N, t ^ 2 := Finset.sum_le_sum fun j _ => by
        have := pow_le_pow_left₀ (abs_nonneg _) (hxj j) 2
        rwa [sq_abs, ← hxv j] at this
    _ = N * ((gram ℝ w).det / (I : ℝ) ^ 2) ^ (1 / (N : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hgram, ht, one_div]
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul hq, mul_comm, Real.rpow_mul hq, Real.rpow_natCast,
          div_pow, sq_abs]

end ReciprocityTheory.ChartRestriction.G.T0
