import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
open PositivityTheory.Rg.Tf.Geo
open MeasureTheory Topology
open scoped ENNReal Pointwise

namespace UpperTheory.ConvolutionTheory.G

/- English proof (translation)
Set `K : CompactExhaustion X` to `(CompactExhaustion.choice X).shiftr.shiftr`. Establish `hK0 : K 0 = ∅` using `rfl`. Establish `hK1 : K 1 = ∅` using `rfl`. Set `S : ℕ → Set X` to `fun m => (H : Set X) * K m`. Set `O : ℕ → Set X` to `fun m => (H : Set X) * interior (K m)`.

Establish `hSc : ∀ m, IsClosed (S m)` using `fun m => hH.mul_right_of_isCompact (K.isCompact m)`. Establish `hOo : ∀ m, IsOpen (O m)` using `fun m => isOpen_interior.mul_left`. Establish `hQ : ∀ m, IsCompact (K (m + 2) \ O (m + 1))` using `fun m => (K.isCompact _).diff (hOo _)`. Establish `hSO : ∀ m, S m ⊆ O (m + 1)` using `fun m => Set.mul_subset_mul_left (K.subset_interior_succ m)`. Establish `hd : ∀ m, Disjoint (K (m + 2) \ O (m + 1)) (S m)` using `fun m => Set.disjoint_left.2 fun x hx hxS => hx.2 (hSO m hxS)`.

Use `choose f hf1 hf0 hfc hfI using fun m => exists_continuous_one_zero_of_isCompact (hQ m) (hSc m) (hd m)`. Establish `hself : ∀ m, K m ⊆ S m` using `fun m x hx => ⟨1, H.one_mem, x, hx, one_mul x⟩`. Establish `hSmono : ∀ {a b : ℕ}, a ≤ b → S a ⊆ S b` using `fun hab => Set.mul_subset_mul_left (K.subset hab)`. Establish `hvan : ∀ {N m : ℕ}, N ≤ m → ∀ x ∈ S N, f m x = 0` using `fun hNm x hx => hf0 _ (hSmono hNm hx)`. Establish `hnn : ∀ m x, 0 ≤ f m x` using `fun m x => (hfI m x).1`.

Establish `hlf : LocallyFinite fun m => Function.support (f m)`. Introduce `x`. Take `⟨n, hn⟩` from `K.exists_mem x`. Use `⟨interior (K (n + 1)), isOpen_interior.mem_nhds (K.subset_interior_succ n hn), (Set.finite_lt_nat (n + 1)).subset ?_⟩` and prove the remaining obligations. Introduce and unpack `m ⟨y, hy, hyU⟩`.

Assume the negation of the conclusion as `hm`. Conclude with `hy (hvan (not_lt.1 hm) y (hself _ (interior_subset hyU)))`. Establish `hfin : ∀ x, (Function.support fun m => f m x).Finite`. Introduce `x`. Take `⟨n, hn⟩` from `K.exists_mem x`.

Use `(Set.finite_lt_nat n).subset ?_` and prove the remaining obligations. Introduce `m hm`. Assume the negation of the conclusion as `hmn`. Conclude with `hm (hvan (not_lt.1 hmn) x (hself _ hn))`. Use `⟨fun x => ∑ᶠ m, f m x, continuous_finsum (fun m => (f m).continuous) hlf, fun x => finsum_nonneg fun m => hnn m x, ?_, ?_⟩` and prove the remaining obligations.

Introduce `x`. Establish `hex : ∃ n, x ∈ O n`. Take `⟨n, hn⟩` from `K.exists_mem x`. Conclude with `⟨n + 1, 1, H.one_mem, x, K.subset_interior_succ n hn, one_mul x⟩`. Establish `hspec` using `Nat.find_spec hex`.

Establish `hmin : ∀ n, n < Nat.find hex → x ∉ O n` using `fun n hn => Nat.find_min hex hn`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m, Nat.find hex = m + 2 := by`. Break down `hN : Nat.find hex with _ | _ | m` into its components or cases. Rewrite `hspec` using `[hN]`. Take `⟨h, -, y, hy, -⟩` from `hspec`.

Simplify using `[hK0] at hy`. Rewrite `hspec` using `[hN]`. Take `⟨h, -, y, hy, -⟩` from `hspec`. Simplify using `[hK1] at hy`. Conclude with `⟨m, rfl⟩`.

Rewrite `hspec` using `[hm]`. Take `⟨h, hh, y, hy, rfl⟩` from `hspec`. Establish `hyQ : y ∈ K (m + 2) \ O (m + 1)`. Use `⟨interior_subset hy, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨h', hh', z, hz, rfl⟩`.

Use `hmin (m + 1) (by omega) ⟨h * h', H.mul_mem hh hh', z, hz, (mul_assoc _ _ _)⟩` and prove the remaining obligations. Use `⟨h⁻¹, H.inv_mem hh, ?_⟩` and prove the remaining obligations. Rewrite using `[inv_mul_cancel_left]`. Establish `h1 : f m y ≤ ∑ᶠ m, f m y` using `single_le_finsum m (hfin y) (fun j => hnn j y)`. Establish `h2 : f m y = 1` using `hf1 m hyQ`.

Introduce `h0`. Simplify using `only [h0, h2] at h1`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `C hC`. Take `⟨N, hN⟩` from `K.exists_superset_of_isCompact hC`.

Use `⟨⋃ m ∈ Finset.range N, tsupport (f m), (Finset.range N).isCompact_biUnion fun m _ => hfc m, ?_⟩` and prove the remaining obligations. Introduce `h hh x hx hne`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m, f m (h * x) ≠ 0 := by`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`.

Conclude with `hne (finsum_eq_zero_of_forall_eq_zero hall)`. Establish `hmN : m < N`. Assume the negation of the conclusion as `hmN`. Conclude with `hm (hvan (not_lt.1 hmN) _ ⟨h, hh, x, hN hx, rfl⟩)`. Conclude with `Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 hmN)) (subset_tsupport _ hm)`.
-/
private theorem exists_bump {X : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X]
    (H : Subgroup X) (hH : IsClosed (H : Set X)) :
    ∃ β : X → ℝ, Continuous β ∧ (∀ x, 0 ≤ β x) ∧ (∀ x, ∃ h ∈ H, β (h * x) ≠ 0) ∧
      ∀ C : Set X, IsCompact C → ∃ C' : Set X, IsCompact C' ∧
        ∀ h ∈ H, ∀ x ∈ C, β (h * x) ≠ 0 → h * x ∈ C' := by
  classical
  let K : CompactExhaustion X := (CompactExhaustion.choice X).shiftr.shiftr
  have hK0 : K 0 = ∅ := rfl
  have hK1 : K 1 = ∅ := rfl
  let S : ℕ → Set X := fun m => (H : Set X) * K m
  let O : ℕ → Set X := fun m => (H : Set X) * interior (K m)
  have hSc : ∀ m, IsClosed (S m) := fun m => hH.mul_right_of_isCompact (K.isCompact m)
  have hOo : ∀ m, IsOpen (O m) := fun m => isOpen_interior.mul_left
  have hQ : ∀ m, IsCompact (K (m + 2) \ O (m + 1)) := fun m => (K.isCompact _).diff (hOo _)
  have hSO : ∀ m, S m ⊆ O (m + 1) := fun m => Set.mul_subset_mul_left (K.subset_interior_succ m)
  have hd : ∀ m, Disjoint (K (m + 2) \ O (m + 1)) (S m) := fun m =>
    Set.disjoint_left.2 fun x hx hxS => hx.2 (hSO m hxS)
  choose f hf1 hf0 hfc hfI using fun m =>
    exists_continuous_one_zero_of_isCompact (hQ m) (hSc m) (hd m)
  have hself : ∀ m, K m ⊆ S m := fun m x hx => ⟨1, H.one_mem, x, hx, one_mul x⟩
  have hSmono : ∀ {a b : ℕ}, a ≤ b → S a ⊆ S b := fun hab =>
    Set.mul_subset_mul_left (K.subset hab)
  have hvan : ∀ {N m : ℕ}, N ≤ m → ∀ x ∈ S N, f m x = 0 := fun hNm x hx => hf0 _ (hSmono hNm hx)
  have hnn : ∀ m x, 0 ≤ f m x := fun m x => (hfI m x).1
  have hlf : LocallyFinite fun m => Function.support (f m) := by
    intro x
    obtain ⟨n, hn⟩ := K.exists_mem x
    refine ⟨interior (K (n + 1)), isOpen_interior.mem_nhds (K.subset_interior_succ n hn),
      (Set.finite_lt_nat (n + 1)).subset ?_⟩
    rintro m ⟨y, hy, hyU⟩
    by_contra hm
    exact hy (hvan (not_lt.1 hm) y (hself _ (interior_subset hyU)))
  have hfin : ∀ x, (Function.support fun m => f m x).Finite := by
    intro x
    obtain ⟨n, hn⟩ := K.exists_mem x
    refine (Set.finite_lt_nat n).subset ?_
    intro m hm
    by_contra hmn
    exact hm (hvan (not_lt.1 hmn) x (hself _ hn))
  refine ⟨fun x => ∑ᶠ m, f m x, continuous_finsum (fun m => (f m).continuous) hlf,
    fun x => finsum_nonneg fun m => hnn m x, ?_, ?_⟩
  · intro x
    have hex : ∃ n, x ∈ O n := by
      obtain ⟨n, hn⟩ := K.exists_mem x
      exact ⟨n + 1, 1, H.one_mem, x, K.subset_interior_succ n hn, one_mul x⟩
    have hspec := Nat.find_spec hex
    have hmin : ∀ n, n < Nat.find hex → x ∉ O n := fun n hn => Nat.find_min hex hn
    obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 2 := by
      rcases hN : Nat.find hex with _ | _ | m
      · rw [hN] at hspec
        obtain ⟨h, -, y, hy, -⟩ := hspec
        simp [hK0] at hy
      · rw [hN] at hspec
        obtain ⟨h, -, y, hy, -⟩ := hspec
        simp [hK1] at hy
      · exact ⟨m, rfl⟩
    rw [hm] at hspec
    obtain ⟨h, hh, y, hy, rfl⟩ := hspec
    have hyQ : y ∈ K (m + 2) \ O (m + 1) := by
      refine ⟨interior_subset hy, ?_⟩
      rintro ⟨h', hh', z, hz, rfl⟩
      refine hmin (m + 1) (by omega) ⟨h * h', H.mul_mem hh hh', z, hz, (mul_assoc _ _ _)⟩
    refine ⟨h⁻¹, H.inv_mem hh, ?_⟩
    rw [inv_mul_cancel_left]
    have h1 : f m y ≤ ∑ᶠ m, f m y := single_le_finsum m (hfin y) (fun j => hnn j y)
    have h2 : f m y = 1 := hf1 m hyQ
    intro h0
    simp only [h0, h2] at h1
    linarith
  · intro C hC
    obtain ⟨N, hN⟩ := K.exists_superset_of_isCompact hC
    refine ⟨⋃ m ∈ Finset.range N, tsupport (f m),
      (Finset.range N).isCompact_biUnion fun m _ => hfc m, ?_⟩
    intro h hh x hx hne
    obtain ⟨m, hm⟩ : ∃ m, f m (h * x) ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hne (finsum_eq_zero_of_forall_eq_zero hall)
    have hmN : m < N := by
      by_contra hmN
      exact hm (hvan (not_lt.1 hmN) _ ⟨h, hh, x, hN hx, rfl⟩)
    exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 hmN)) (subset_tsupport _ hm)

end UpperTheory.ConvolutionTheory.G

/- English proof (translation)
Introduce `X T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ν _ _ i hi`. Establish `hH : IsClosed ((i.range : Subgroup X) : Set X)`. Rewrite using `[MonoidHom.coe_range]`. Conclude with `hi.isClosed_range`. Take `⟨β, hβ, hβ0, hcov, hsupp⟩` from `UpperTheory.ConvolutionTheory.G.exists_bump i.range hH`.

Establish `hB : ∀ C : Set X, IsCompact C → ∃ B : Set T, IsCompact B ∧ ∀ t, ∀ x ∈ C, β (i t * x) ≠ 0 → t ∈ B`. Introduce `C hC`. Take `⟨C', hC', h⟩` from `hsupp C hC`. Use `⟨i ⁻¹' (C' * C⁻¹), hi.isCompact_preimage (hC'.mul hC.inv), fun t x hx hne => ?_⟩` and prove the remaining obligations. Conclude with `⟨i t * x, h _ ⟨t, rfl⟩ x hx hne, x⁻¹, Set.inv_mem_inv.2 hx, by simp⟩`.

Establish `hc : Continuous (Function.uncurry fun (x : X) (t : T) => β (i t * x))` using `hβ.comp ((hi.continuous.comp continuous_snd).mul continuous_fst)`. Establish `hcx : ∀ x, Continuous fun t => β (i t * x)` using `fun x => hβ.comp (hi.continuous.mul continuous_const)`. Establish `hcs : ∀ x, HasCompactSupport fun t => β (i t * x)`. Introduce `x`. Take `⟨B, hBc, hB'⟩` from `hB {x} isCompact_singleton`.

Use `HasCompactSupport.intro hBc fun t ht => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Conclude with `ht (hB' t x rfl hne)`. Set `D : X → ℝ` to `fun x => ∫ t, β (i t * x) ∂ν`. Establish `hDc : Continuous D`.

Rewrite using `[continuous_iff_continuousAt]`. Introduce `x₀`. Take `⟨N, hNc, hN⟩` from `exists_compact_mem_nhds x₀`. Take `⟨B, hBc, hB'⟩` from `hB N hNc`. Establish `h1 : Continuous fun x => ∫ t in B, β (i t * x) ∂ν` using `continuous_parametric_integral_of_continuous hc hBc`.

Use `h1.continuousAt.congr ?_` and prove the remaining obligations. Use `filter_upwards [hN] with x hx`. Use `setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Conclude with `ht (hB' t x hx hne)`.

Establish `hDpos : ∀ x, 0 < D x`. Introduce `x`. Take `⟨h, ⟨t₀, rfl⟩, hne⟩` from `hcov x`. Conclude with `(hcx x).integral_pos_of_hasCompactSupport_nonneg_nonzero (hcs x) (fun t => hβ0 _) hne`. Establish `hDinv : ∀ s x, D (i s * x) = D x`.

Introduce `s x`. Use `integral_mul_right_eq_self (μ := ν) (fun t => β (i t * x)) s` as an intermediate fact. Simplify `this` using `[D, mul_assoc]`. Use `⟨fun x => Real.toNNReal (β x / D x), continuous_real_toNNReal.comp (hβ.div hDc fun x => (hDpos x).ne'), ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `(ENNReal.continuous_coe.comp (continuous_real_toNNReal.comp (hβ.div hDc fun x => (hDpos x).ne'))).measurable`.

Introduce `x`. Establish `hint : Integrable (fun t => β (i t * x) / D x) ν` using `((hcx x).integrable_of_hasCompactSupport (hcs x)).div_const _`. Establish `h1 : ∫⁻ t, ((Real.toNNReal (β (i t * id x) / D (i t * id x)) : NNReal) : ℝ≥0∞) ∂ν = ∫⁻ t, ENNReal.ofReal (β (i t * x) / D x) ∂ν`. Use `lintegral_congr fun t => ?_` and prove the remaining obligations. Simplify using `only [id, hDinv]`.

Both sides reduce to the same expression. Rewrite using `[h1, ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun t => div_nonneg (hβ0 _) (hDpos x).le), integral_div]`. Express the relevant statement in the definitionally equal form `ENNReal.ofReal (D x / D x) = 1`. Rewrite using `[div_self (hDpos x).ne', ENNReal.ofReal_one]`. Introduce `C hC`.

Take `⟨C', hC', h⟩` from `hsupp C hC`. Use `⟨C', hC', fun t x hx hne => h _ ⟨t, rfl⟩ x hx fun h0 => hne ?_⟩` and prove the remaining obligations. Simplify using `[h0]`.
-/
theorem UpperTheory.ConvolutionTheory.G.closedSubgroup_cutoff_exists :
    Q2 := by
  intro X T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ν _ _ i hi
  have hH : IsClosed ((i.range : Subgroup X) : Set X) := by
    rw [MonoidHom.coe_range]; exact hi.isClosed_range
  obtain ⟨β, hβ, hβ0, hcov, hsupp⟩ := UpperTheory.ConvolutionTheory.G.exists_bump i.range hH
  have hB : ∀ C : Set X, IsCompact C → ∃ B : Set T, IsCompact B ∧
      ∀ t, ∀ x ∈ C, β (i t * x) ≠ 0 → t ∈ B := by
    intro C hC
    obtain ⟨C', hC', h⟩ := hsupp C hC
    refine ⟨i ⁻¹' (C' * C⁻¹), hi.isCompact_preimage (hC'.mul hC.inv), fun t x hx hne => ?_⟩
    exact ⟨i t * x, h _ ⟨t, rfl⟩ x hx hne, x⁻¹, Set.inv_mem_inv.2 hx, by simp⟩
  have hc : Continuous (Function.uncurry fun (x : X) (t : T) => β (i t * x)) :=
    hβ.comp ((hi.continuous.comp continuous_snd).mul continuous_fst)
  have hcx : ∀ x, Continuous fun t => β (i t * x) := fun x =>
    hβ.comp (hi.continuous.mul continuous_const)
  have hcs : ∀ x, HasCompactSupport fun t => β (i t * x) := by
    intro x
    obtain ⟨B, hBc, hB'⟩ := hB {x} isCompact_singleton
    refine HasCompactSupport.intro hBc fun t ht => ?_
    by_contra hne
    exact ht (hB' t x rfl hne)
  let D : X → ℝ := fun x => ∫ t, β (i t * x) ∂ν
  have hDc : Continuous D := by
    rw [continuous_iff_continuousAt]
    intro x₀
    obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds x₀
    obtain ⟨B, hBc, hB'⟩ := hB N hNc
    have h1 : Continuous fun x => ∫ t in B, β (i t * x) ∂ν :=
      continuous_parametric_integral_of_continuous hc hBc
    refine h1.continuousAt.congr ?_
    filter_upwards [hN] with x hx
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_
    by_contra hne
    exact ht (hB' t x hx hne)
  have hDpos : ∀ x, 0 < D x := by
    intro x
    obtain ⟨h, ⟨t₀, rfl⟩, hne⟩ := hcov x
    exact (hcx x).integral_pos_of_hasCompactSupport_nonneg_nonzero (hcs x)
      (fun t => hβ0 _) hne
  have hDinv : ∀ s x, D (i s * x) = D x := by
    intro s x
    have := integral_mul_right_eq_self (μ := ν) (fun t => β (i t * x)) s
    simpa [D, mul_assoc] using this
  refine ⟨fun x => Real.toNNReal (β x / D x),
    continuous_real_toNNReal.comp (hβ.div hDc fun x => (hDpos x).ne'), ⟨?_, ?_⟩, ?_⟩
  · exact (ENNReal.continuous_coe.comp
      (continuous_real_toNNReal.comp (hβ.div hDc fun x => (hDpos x).ne'))).measurable
  · intro x
    have hint : Integrable (fun t => β (i t * x) / D x) ν :=
      ((hcx x).integrable_of_hasCompactSupport (hcs x)).div_const _
    have h1 : ∫⁻ t, ((Real.toNNReal (β (i t * id x) / D (i t * id x)) : NNReal) : ℝ≥0∞) ∂ν =
        ∫⁻ t, ENNReal.ofReal (β (i t * x) / D x) ∂ν := by
      refine lintegral_congr fun t => ?_
      simp only [id, hDinv]
      rfl
    rw [h1, ← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun t => div_nonneg (hβ0 _) (hDpos x).le), integral_div]
    change ENNReal.ofReal (D x / D x) = 1
    rw [div_self (hDpos x).ne', ENNReal.ofReal_one]
  · intro C hC
    obtain ⟨C', hC', h⟩ := hsupp C hC
    refine ⟨C', hC', fun t x hx hne => h _ ⟨t, rfl⟩ x hx fun h0 => hne ?_⟩
    simp [h0]
