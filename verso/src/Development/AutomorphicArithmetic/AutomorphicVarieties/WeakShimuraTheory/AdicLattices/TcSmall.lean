import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicLattices.CompanionTheory
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.SmallExt

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Lat

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible B`. Take `⟨k, u, hdu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hϖ`. Establish `hm : maximalIdeal B = Ideal.span {ϖ}` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ`. Establish `hϖ0 : ϖ ≠ 0` using `hϖ.ne_zero`. Establish `hle : (maximalIdeal A).map g ≤ maximalIdeal B`.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `z hz`. Simplify using `only [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff] at hz ⊢`. Conclude with `fun h => hz (isUnit_of_map_unit g z h)`. Introduce `N`.

Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Establish `hA` using `(IsLocallyConstant.iff_eventually_eq _).1 (ha (N + k)) x`. Use `filter_upwards [hA] with y hy`. Rewrite `hy`, the goal using `[Ideal.Quotient.eq]`.

Establish `h1 : g (a y - a x) ∈ maximalIdeal B ^ (N + k)`. Establish `h2` using `Ideal.mem_map_of_mem g hy`. Rewrite `h2` using `[Ideal.map_pow]`. Conclude with `Ideal.pow_right_mono hle _ h2`. Establish `h3 : d * (b y - b x) = c * g (a y - a x)`.

Rewrite using `[mul_sub, h, h, map_sub, mul_sub]`. Establish `h5` using `Ideal.mul_mem_left _ c h1`. Rewrite `h5` using `[← h3, hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hdu]`. Rewrite using `[hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Establish `h4 : ϖ ^ N * ϖ ^ k ∣ (↑u * (b y - b x)) * ϖ ^ k`.

Rewrite using `[← pow_add]`. Use `h5 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Rewrite `h4` using `[mul_dvd_mul_iff_right (pow_ne_zero _ hϖ0)]`. Conclude with `(Units.dvd_mul_left).1 h4`.
-/
private theorem cont_div {Γ A B : Type} [TopologicalSpace Γ] [CommRing A] [IsLocalRing A] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] (g : A →+* B) [IsLocalHom g] (a : Γ → A) (b : Γ → B) (c d : B) (hd : d ≠ 0)
    (h : ∀ x, d * b x = c * g (a x)) (ha : AdicCont (maximalIdeal A) a) : AdicCont (maximalIdeal B) b := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨k, u, hdu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hϖ
  have hm : maximalIdeal B = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hle : (maximalIdeal A).map g ≤ maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap]
    intro z hz
    simp only [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff] at hz ⊢
    exact fun h => hz (isUnit_of_map_unit g z h)
  intro N
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hA := (IsLocallyConstant.iff_eventually_eq _).1 (ha (N + k)) x
  filter_upwards [hA] with y hy
  rw [Ideal.Quotient.eq] at hy ⊢
  have h1 : g (a y - a x) ∈ maximalIdeal B ^ (N + k) := by
    have h2 := Ideal.mem_map_of_mem g hy
    rw [Ideal.map_pow] at h2
    exact Ideal.pow_right_mono hle _ h2
  have h3 : d * (b y - b x) = c * g (a y - a x) := by
    rw [mul_sub, h, h, map_sub, mul_sub]
  have h5 := Ideal.mul_mem_left _ c h1
  rw [← h3, hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hdu] at h5
  rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have h4 : ϖ ^ N * ϖ ^ k ∣ (↑u * (b y - b x)) * ϖ ^ k := by
    rw [← pow_add]
    convert h5 using 1
    ring
  rw [mul_dvd_mul_iff_right (pow_ne_zero _ hϖ0)] at h4
  exact (Units.dvd_mul_left).1 h4

/- English proof (translation)
Introduce `l _ 𝔞 ι Γ _ _ t P P' hT hS`. Unfold `TConj at hT`. Unfold `Amb.Small at hS ⊢`. Take `⟨hr, hn⟩` from `hT`. Take `⟨A, _, _, _, f, P₁, hf, hc, rfl⟩` from `hS`.

Use `set U : Fin 4 → Fin 4 → 𝔞.K := fun i j => (wv t (wt i j) : 𝔞.K) with hU`. Establish `hU0 : ∀ i j, U i j ≠ 0` using `fun i j => Units.ne_zero _`. Establish `hr' : ∀ γ i j, 𝔞.toK (P'.r γ i j) = U i j * 𝔞.toK (f (P₁.r γ i j))` using `fun γ i j => congrFun (congrFun (hr γ) i) j`. Establish `hn' : ∀ v i j, 𝔞.toK (P'.n v i j) = U i j * 𝔞.toK (f (P₁.n v i j))` using `fun v i j => congrFun (congrFun (hn v) i) j`. Set `s : Finset 𝔞.K` to `Finset.univ.image (fun ij : Fin 4 × Fin 4 => U ij.1 ij.2) ∪ Finset.univ.image (fun ij : Fin 4 × Fin 4 => (U ij.1 ij.2)⁻¹)`.

Establish `hUs : ∀ i j, U i j ∈ s` using `fun i j => by simp [s]`. Establish `hUs' : ∀ i j, (U i j)⁻¹ ∈ s` using `fun i j => by simp [s]`. Take `⟨A', _, _, _, f', g, hf', hcomp, hcl⟩` from `smallExt 𝔞 A f hf s`. Establish `hinj : Function.Injective f'` using `hf'.inj`. Establish `hK : Function.Injective 𝔞.toK` using `Subtype.val_injective`.

Establish `hloc : IsLocalHom g`. Use `Amb.IsDvr.loc hf` as an intermediate fact. Use `⟨fun z hz => isUnit_of_map_unit f z ?_⟩` and prove the remaining obligations. Rewrite using `[← hcomp]`. Conclude with `hz.map f'`.

Establish `mem_cl : ∀ (x : 𝔞.V) (z : A) (i j : Fin 4), 𝔞.toK x = U i j * 𝔞.toK (f z) → x ∈ f'.range`. Introduce `x z i j hx`. Apply `hcl` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `𝔞.toK x ∈ _`. Rewrite using `[hx]`.

Apply `Subfield.mul_mem` to reduce the goal to its premises. Conclude with `Subfield.subset_closure (Or.inr (hUs i j))`. Conclude with `Subfield.subset_closure (Or.inl ⟨z, rfl⟩)`. Establish `frac : ∀ i j, ∃ c d : A', d ≠ 0 ∧ 𝔞.toK (f' d) * U i j = 𝔞.toK (f' c)`. Introduce `i j`.

Break down `𝔞.V.mem_or_inv_mem (U i j) with h | h` into its components or cases. Take `⟨c, hc'⟩` from `hcl ⟨U i j, h⟩ (Subfield.subset_closure (Or.inr (hUs i j)))`. Use `⟨c, 1, one_ne_zero, ?_⟩` and prove the remaining obligations. Rewrite using `[map_one, map_one, one_mul, hc']`. Both sides reduce to the same expression.

Take `⟨d, hd⟩` from `hcl ⟨(U i j)⁻¹, h⟩ (Subfield.subset_closure (Or.inr (hUs' i j)))`. Use `⟨1, d, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Rewrite `hd` using `[map_zero]`. Conclude with `inv_ne_zero (hU0 i j) (congrArg Subtype.val hd).symm`.

Rewrite using `[hd, map_one, map_one]`. Conclude with `inv_mul_cancel₀ (hU0 i j)`. Establish `hrR : ∀ γ i j, P'.r γ i j ∈ f'.range` using `fun γ i j => mem_cl _ _ i j (hr' γ i j)`. Establish `hnR : ∀ v i j, P'.n v i j ∈ f'.range` using `fun v i j => mem_cl _ _ i j (hn' v i j)`. Set `e : 𝔞.V → A'` to `Function.invFun f'`.

Establish `hE : ∀ γ i j, f' (e (P'.r γ i j)) = P'.r γ i j` using `fun γ i j => by`. Take `⟨y, hy⟩` from `hrR γ i j`. Conclude with `Function.invFun_eq ⟨y, hy⟩`. Establish `hEn : ∀ v i j, f' (e (P'.n v i j)) = P'.n v i j` using `fun v i j => by`. Take `⟨y, hy⟩` from `hnR v i j`.

Conclude with `Function.invFun_eq ⟨y, hy⟩`. Set `r₁ : Γ →* UpperTheory.V.GradeZeroInterpolatingElement.M4 A'` to `{ toFun := fun γ => (P'.r γ).map e map_one' := by`. Use extensionality with `i j`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[Matrix.map_apply, hE, map_one, Matrix.one_apply, Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Use the proof step `map_mul' := fun γ δ => by`. Use extensionality with `i j`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[Matrix.map_apply, hE, map_mul, Matrix.mul_apply, Matrix.mul_apply, map_sum]`.

Simplify using `only [Matrix.map_apply, map_mul, hE] }`. Set `P₁' : PD ι Γ A'` to `⟨r₁, fun v => (P'.n v).map e⟩`. Use `⟨A', inferInstance, inferInstance, inferInstance, f', P₁', hf', ?_, ?_⟩` and prove the remaining obligations. Unfold `PD.Cont`. Introduce `i j`.

Take `⟨c, d, hd, hcd⟩` from `frac i j`. Use `cont_div g (fun γ => P₁.r γ i j) (fun γ => P₁'.r γ i j) c d hd ?_ (hc i j)` and prove the remaining obligations. Introduce `γ`. Apply `hinj` to reduce the goal to its premises. Apply `hK` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `𝔞.toK (f' (d * e (P'.r γ i j))) = 𝔞.toK (f' (c * g (P₁.r γ i j)))`. Rewrite using `[map_mul, map_mul, hE, map_mul, map_mul, ← RingHom.comp_apply f' g, hcomp, ← hcd, hr', mul_assoc]`. Apply `PD.ext` to reduce the goal to its premises. Use extensionality with `γ i j`. Conclude with `congrArg Subtype.val (hE γ i j)`.

Use extensionality with `v i j`. Conclude with `congrArg Subtype.val (hEn v i j)`.
-/
theorem UpperTheory.V.Ws.Lat.tcSmall :
    ∀ {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) {ι Γ : Type} [Group Γ] [TopologicalSpace Γ] (t : 𝔞.Kˣ × 𝔞.Kˣ) (P P' : PD ι Γ 𝔞.V),
      TConj 𝔞.toK t P P' → 𝔞.Small P → 𝔞.Small P' := by
  classical
  intro l _ 𝔞 ι Γ _ _ t P P' hT hS
  unfold TConj at hT
  unfold Amb.Small at hS ⊢
  obtain ⟨hr, hn⟩ := hT
  obtain ⟨A, _, _, _, f, P₁, hf, hc, rfl⟩ := hS
  set U : Fin 4 → Fin 4 → 𝔞.K := fun i j => (wv t (wt i j) : 𝔞.K) with hU
  have hU0 : ∀ i j, U i j ≠ 0 := fun i j => Units.ne_zero _
  have hr' : ∀ γ i j, 𝔞.toK (P'.r γ i j) = U i j * 𝔞.toK (f (P₁.r γ i j)) :=
    fun γ i j => congrFun (congrFun (hr γ) i) j
  have hn' : ∀ v i j, 𝔞.toK (P'.n v i j) = U i j * 𝔞.toK (f (P₁.n v i j)) :=
    fun v i j => congrFun (congrFun (hn v) i) j
  let s : Finset 𝔞.K := Finset.univ.image (fun ij : Fin 4 × Fin 4 => U ij.1 ij.2) ∪
    Finset.univ.image (fun ij : Fin 4 × Fin 4 => (U ij.1 ij.2)⁻¹)
  have hUs : ∀ i j, U i j ∈ s := fun i j => by simp [s]
  have hUs' : ∀ i j, (U i j)⁻¹ ∈ s := fun i j => by simp [s]
  obtain ⟨A', _, _, _, f', g, hf', hcomp, hcl⟩ := smallExt 𝔞 A f hf s
  have hinj : Function.Injective f' := hf'.inj
  have hK : Function.Injective 𝔞.toK := Subtype.val_injective
  have hloc : IsLocalHom g := by
    have := Amb.IsDvr.loc hf
    refine ⟨fun z hz => isUnit_of_map_unit f z ?_⟩
    rw [← hcomp]
    exact hz.map f'
  have mem_cl : ∀ (x : 𝔞.V) (z : A) (i j : Fin 4), 𝔞.toK x = U i j * 𝔞.toK (f z) → x ∈ f'.range := by
    intro x z i j hx
    apply hcl
    change 𝔞.toK x ∈ _
    rw [hx]
    apply Subfield.mul_mem
    · exact Subfield.subset_closure (Or.inr (hUs i j))
    · exact Subfield.subset_closure (Or.inl ⟨z, rfl⟩)
  have frac : ∀ i j, ∃ c d : A', d ≠ 0 ∧ 𝔞.toK (f' d) * U i j = 𝔞.toK (f' c) := by
    intro i j
    rcases 𝔞.V.mem_or_inv_mem (U i j) with h | h
    · obtain ⟨c, hc'⟩ := hcl ⟨U i j, h⟩ (Subfield.subset_closure (Or.inr (hUs i j)))
      refine ⟨c, 1, one_ne_zero, ?_⟩
      rw [map_one, map_one, one_mul, hc']
      rfl
    · obtain ⟨d, hd⟩ := hcl ⟨(U i j)⁻¹, h⟩ (Subfield.subset_closure (Or.inr (hUs' i j)))
      refine ⟨1, d, ?_, ?_⟩
      · rintro rfl
        rw [map_zero] at hd
        exact inv_ne_zero (hU0 i j) (congrArg Subtype.val hd).symm
      · rw [hd, map_one, map_one]
        exact inv_mul_cancel₀ (hU0 i j)
  have hrR : ∀ γ i j, P'.r γ i j ∈ f'.range := fun γ i j => mem_cl _ _ i j (hr' γ i j)
  have hnR : ∀ v i j, P'.n v i j ∈ f'.range := fun v i j => mem_cl _ _ i j (hn' v i j)
  let e : 𝔞.V → A' := Function.invFun f'
  have hE : ∀ γ i j, f' (e (P'.r γ i j)) = P'.r γ i j := fun γ i j => by
    obtain ⟨y, hy⟩ := hrR γ i j
    exact Function.invFun_eq ⟨y, hy⟩
  have hEn : ∀ v i j, f' (e (P'.n v i j)) = P'.n v i j := fun v i j => by
    obtain ⟨y, hy⟩ := hnR v i j
    exact Function.invFun_eq ⟨y, hy⟩
  let r₁ : Γ →* UpperTheory.V.GradeZeroInterpolatingElement.M4 A' :=
    { toFun := fun γ => (P'.r γ).map e
      map_one' := by
        ext i j
        apply hinj
        rw [Matrix.map_apply, hE, map_one, Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      map_mul' := fun γ δ => by
        ext i j
        apply hinj
        rw [Matrix.map_apply, hE, map_mul, Matrix.mul_apply, Matrix.mul_apply, map_sum]
        simp only [Matrix.map_apply, map_mul, hE] }
  let P₁' : PD ι Γ A' := ⟨r₁, fun v => (P'.n v).map e⟩
  refine ⟨A', inferInstance, inferInstance, inferInstance, f', P₁', hf', ?_, ?_⟩
  · unfold PD.Cont
    intro i j
    obtain ⟨c, d, hd, hcd⟩ := frac i j
    refine cont_div g (fun γ => P₁.r γ i j) (fun γ => P₁'.r γ i j) c d hd ?_ (hc i j)
    intro γ
    apply hinj
    apply hK
    change 𝔞.toK (f' (d * e (P'.r γ i j))) = 𝔞.toK (f' (c * g (P₁.r γ i j)))
    rw [map_mul, map_mul, hE, map_mul, map_mul, ← RingHom.comp_apply f' g, hcomp, ← hcd, hr',
      mul_assoc]
  · apply PD.ext
    · ext γ i j
      exact congrArg Subtype.val (hE γ i j)
    · ext v i j
      exact congrArg Subtype.val (hEn v i j)
