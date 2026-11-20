import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LengthCommensurableMapIffOfInjective
universe u_1 u_2 u_3 u_4

namespace GlobalTheory.SignedLengthTower

/- English proof (translation)
Establish `hle : C.submoduleOf A ≤ B.submoduleOf A` using `Submodule.comap_mono hCB`. Rewrite using `[← relLength_submoduleOf hBA C, relLength_eq_length_map_mkQ (B.submoduleOf A), relLength_def, relLength_def]`. Use `Module.length_eq_add_of_exact (Submodule.subtype _) (Submodule.factor hle) (Submodule.injective_subtype _) (Submodule.factor_surjective _) ?_` and prove the remaining obligations. Introduce `y`. Take `⟨x, rfl⟩` from `Submodule.mkQ_surjective _ y`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hx : x ∈ B.submoduleOf A`. Simplify `h` using `[Submodule.factor_mk]`. Conclude with `⟨⟨_, x, hx, rfl⟩, rfl⟩`.

Introduce and unpack `⟨⟨_, z, hz, rfl⟩, h⟩`. Establish `h' : (C.submoduleOf A).mkQ z = (C.submoduleOf A).mkQ x` using `h`. Rewrite using `[← h']`. Simplify `hz` using `[Submodule.factor_mk]`.
-/
theorem relLength_tower {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    {A B C : Submodule R V} (hBA : B ≤ A) (hCB : C ≤ B) :
    relLength A C = relLength B C + relLength A B := by
  have hle : C.submoduleOf A ≤ B.submoduleOf A := Submodule.comap_mono hCB
  rw [← relLength_submoduleOf hBA C, relLength_eq_length_map_mkQ (B.submoduleOf A),
    relLength_def, relLength_def]
  refine Module.length_eq_add_of_exact (Submodule.subtype _) (Submodule.factor hle)
    (Submodule.injective_subtype _) (Submodule.factor_surjective _) ?_
  intro y
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
  constructor
  · intro h
    have hx : x ∈ B.submoduleOf A := by
      simpa [Submodule.factor_mk] using h
    exact ⟨⟨_, x, hx, rfl⟩, rfl⟩
  · rintro ⟨⟨_, z, hz, rfl⟩, h⟩
    have h' : (C.submoduleOf A).mkQ z = (C.submoduleOf A).mkQ x := h
    rw [← h']
    simpa [Submodule.factor_mk] using hz

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [Ring.ord_one]`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.prod_insert hi, Finset.sum_insert hi, Ring.ord_mul' R (mem_nonZeroDivisors_of_ne_zero (hd i)), ih]`.
-/
theorem ord_prod {R ι : Type*} [CommRing R] [IsDomain R] (s : Finset ι) (d : ι → R)
    (hd : ∀ i, d i ≠ 0) : Ring.ord R (∏ i ∈ s, d i) = ∑ i ∈ s, Ring.ord R (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Ring.ord_one]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      Ring.ord_mul' R (mem_nonZeroDivisors_of_ne_zero (hd i)), ih]

/- English proof (translation)
Establish `h : Module.finrank R (LinearMap.range f) = Module.finrank R (ι → R)` using `LinearMap.finrank_range_of_inj hf`. Use `set e := Pi.basisFun R ι`. Use `set d := Submodule.smithNormalFormCoeffs e h with hd`. Use `set top := Submodule.smithNormalFormTopBasis e h with htop`. Use `set bot := Submodule.smithNormalFormBotBasis e h with hbot`.

Establish `hass` using `LinearMap.associated_det_comp_equiv (LinearMap.range f).subtype (LinearEquiv.ofInjective f hf) (top.equiv bot (Equiv.refl ι))`. Establish `h1 : (LinearMap.range f).subtype ∘ₗ (LinearEquiv.ofInjective f hf).toLinearMap = f` using `by ext1 i ext1`. Both sides reduce to the same expression. Establish `h2 : LinearMap.det ((LinearMap.range f).subtype ∘ₗ (top.equiv bot (Equiv.refl ι)).toLinearMap) = ∏ i, d i`. Rewrite using `[← LinearMap.det_toMatrix top, ← Matrix.det_diagonal]`.

Use `congr 1`. Use extensionality with `i j`. Use `Submodule.smithNormalFormBotBasis_def e h j` as an intermediate fact. Rewrite `this` using `[← hd, ← htop, ← hbot]`. Rewrite using `[LinearMap.toMatrix_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply, Submodule.subtype_apply, this]`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hij, Finsupp.single_apply, Ne.symm hij]`. Rewrite `hass` using `[h1, h2]`.

Take `⟨v, hv⟩` from `hass.symm`. Rewrite using `[(Submodule.quotientEquivPiSpan _ e h).length_eq, Module.length_pi_of_fintype, ← hv, Ring.ord_mul R (v.isUnit.mem_nonZeroDivisors), Ring.ord_of_isUnit v.isUnit, add_zero, ord_prod _ _ (Submodule.smithNormalFormCoeffs_ne_zero e h)]`. Both sides reduce to the same expression.
-/
theorem length_coker {R ι : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Fintype ι] (f : (ι → R) →ₗ[R] (ι → R)) (hf : Function.Injective f) :
    Module.length R ((ι → R) ⧸ LinearMap.range f) = Ring.ord R (LinearMap.det f) := by
  classical
  have h : Module.finrank R (LinearMap.range f) = Module.finrank R (ι → R) :=
    LinearMap.finrank_range_of_inj hf
  set e := Pi.basisFun R ι
  set d := Submodule.smithNormalFormCoeffs e h with hd
  set top := Submodule.smithNormalFormTopBasis e h with htop
  set bot := Submodule.smithNormalFormBotBasis e h with hbot
  have hass := LinearMap.associated_det_comp_equiv (LinearMap.range f).subtype
    (LinearEquiv.ofInjective f hf) (top.equiv bot (Equiv.refl ι))
  have h1 : (LinearMap.range f).subtype ∘ₗ (LinearEquiv.ofInjective f hf).toLinearMap = f := by
    ext1 i
    ext1
    rfl
  have h2 : LinearMap.det ((LinearMap.range f).subtype ∘ₗ
      (top.equiv bot (Equiv.refl ι)).toLinearMap) = ∏ i, d i := by
    rw [← LinearMap.det_toMatrix top, ← Matrix.det_diagonal]
    congr 1
    ext i j
    have := Submodule.smithNormalFormBotBasis_def e h j
    rw [← hd, ← htop, ← hbot] at this
    rw [LinearMap.toMatrix_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Module.Basis.equiv_apply, Equiv.refl_apply, Submodule.subtype_apply, this]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Finsupp.single_apply, Ne.symm hij]
  rw [h1, h2] at hass
  obtain ⟨v, hv⟩ := hass.symm
  rw [(Submodule.quotientEquivPiSpan _ e h).length_eq, Module.length_pi_of_fintype, ← hv,
    Ring.ord_mul R (v.isUnit.mem_nonZeroDivisors), Ring.ord_of_isUnit v.isUnit, add_zero,
    ord_prod _ _ (Submodule.smithNormalFormCoeffs_ne_zero e h)]
  rfl

/- English proof (translation)
Set `φ` to `Fintype.linearCombination R a`. Establish `hφ : Function.Injective φ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Use function extensionality and compare the values at `i`.

Conclude with `Fintype.linearIndependent_iff.mp ha x (by simpa [φ, Fintype.linearCombination_apply] using hx) i`. Establish `hf : Function.Injective (Matrix.toLin' M)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Conclude with `Matrix.eq_zero_of_mulVec_eq_zero hM (by simpa using hx)`.

Establish `hA : Submodule.span R (Set.range a) = Submodule.map φ ⊤`. Rewrite using `[Submodule.map_top, Fintype.range_linearCombination]`. Establish `hC : Submodule.span R (Set.range c) = Submodule.map φ (LinearMap.range (Matrix.toLin' M))`. Rewrite using `[Matrix.range_toLin', Submodule.map_span, ← Set.range_comp]`. Use `congr 2`.

Use function extensionality and compare the values at `j`. Simplify using `[φ, Fintype.linearCombination_apply, hc]`. Rewrite using `[hA, hC, relLength_map_of_injective φ hφ, relLength_top_left, length_coker _ hf, LinearMap.det_toLin']`.
-/
theorem relLength_span_matrix {R V ι : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup V] [Module R V] [Fintype ι] [DecidableEq ι] {a c : ι → V}
    (ha : LinearIndependent R a) (M : Matrix ι ι R) (hM : M.det ≠ 0)
    (hc : ∀ j, c j = ∑ i, M i j • a i) :
    relLength (Submodule.span R (Set.range a)) (Submodule.span R (Set.range c)) =
      Ring.ord R M.det := by
  let φ := Fintype.linearCombination R a
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    funext i
    exact Fintype.linearIndependent_iff.mp ha x (by simpa [φ, Fintype.linearCombination_apply] using hx) i
  have hf : Function.Injective (Matrix.toLin' M) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact Matrix.eq_zero_of_mulVec_eq_zero hM (by simpa using hx)
  have hA : Submodule.span R (Set.range a) = Submodule.map φ ⊤ := by
    rw [Submodule.map_top, Fintype.range_linearCombination]
  have hC : Submodule.span R (Set.range c) =
      Submodule.map φ (LinearMap.range (Matrix.toLin' M)) := by
    rw [Matrix.range_toLin', Submodule.map_span, ← Set.range_comp]
    congr 2
    funext j
    simp [φ, Fintype.linearCombination_apply, hc]
  rw [hA, hC, relLength_map_of_injective φ hφ, relLength_top_left, length_coker _ hf,
    LinearMap.det_toLin']

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap R K)` using `IsFractionRing.injective R K`. Establish `hϖK : algebraMap R K ϖ ≠ 0` using `(map_ne_zero_iff _ hinj).mpr hϖ.ne_zero`. Establish `hg : g.det ≠ 0`. Rewrite using `[hdet]`. Conclude with `mul_ne_zero ((map_ne_zero_iff _ hinj).mpr u.ne_zero) (zpow_ne_zero _ hϖK)`.

Establish `hbK : LinearIndependent K b`. Rewrite `ha`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `x hx`. Establish `h0 : g.mulVec x = 0`. Use function extensionality and compare the values at `i`.

Use `ha (g.mulVec x) ?_ i` and prove the remaining obligations. Rewrite using `[← hx]`. Simplify using `only [hb, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [mul_comm]`.

Conclude with `congrFun (Matrix.eq_zero_of_mulVec_eq_zero hg h0)`. Establish `hres : ∀ {v : ι → V}, LinearIndependent K v → LinearIndependent R v` using `fun hv => hv.restrict_scalars (by simpa [← Algebra.algebraMap_eq_smul_one] using hinj)`. Take `⟨⟨t, ht⟩, hint⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) (fun p : ι × ι => g p.1 p.2)`. Use `choose m hm using hint`. Set `M : Matrix ι ι R` to `Matrix.of fun i j => m (i, j)`.

Establish `hM : (algebraMap R K).mapMatrix M = algebraMap R K t • g`. Use extensionality with `i j`. Simplify using `[M, hm, Algebra.smul_def]`. Set `D : Matrix ι ι R` to `Matrix.diagonal fun _ => t`. Establish `hD : D.det ≠ 0`.

Rewrite using `[Matrix.det_diagonal]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun _ _ => nonZeroDivisors.ne_zero ht`. Establish `hMD : algebraMap R K M.det = algebraMap R K D.det * g.det`. Rewrite using `[RingHom.map_det, hM, Matrix.det_smul, Matrix.det_diagonal]`. Simplify using the standard rewrite rules.

Establish `hM0 : M.det ≠ 0`. Rewrite using `[← map_ne_zero_iff _ hinj, hMD]`. Conclude with `mul_ne_zero ((map_ne_zero_iff _ hinj).mpr hD) hg`. Set `c : ι → V` to `fun j => t • b j`. Establish `hca : ∀ j, c j = ∑ i, M i j • a i`.

Introduce `j`. Simplify using `only [c, hb, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← smul_assoc, ← hm (i, j), algebraMap_smul]`. Both sides reduce to the same expression.

Establish `hcb : ∀ j, c j = ∑ i, D i j • b i`. Introduce `j`. Simplify using `[c, D, Matrix.diagonal_apply, ite_smul]`. Establish `hle : ∀ {v : ι → V} {N : Matrix ι ι R}, (∀ j, c j = ∑ i, N i j • v i) → Submodule.span R (Set.range c) ≤ Submodule.span R (Set.range v)`. Introduce `v N hN`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Rewrite using `[hN]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Establish `h1` using `relLength_span_matrix (hres ha) M hM0 hca`.

Establish `h2` using `relLength_span_matrix (hres hbK) D hD hcb`. Establish `hC` using `le_inf (hle hca) (hle hcb)`. Rewrite `h1` using `[relLength_tower inf_le_left hC, relLength_inf_right]`. Rewrite `h2` using `[relLength_tower inf_le_right hC, relLength_inf_right']`. Establish `hord : Ring.ord R ϖ = 1`.

Use `PrincipalIdealRing.isMaximal_of_irreducible hϖ` as an intermediate fact. Establish `h` using `relLength_top_of_isMaximal (Ideal.span {ϖ})`. Rewrite `h` using `[relLength_top_left]`. Conclude with `h`. Take `⟨p, q, rfl⟩ : ∃ p q : ℕ, n = (p : ℤ) - q` from `⟨n.toNat, (-n).toNat, by omega⟩`.

Establish `hR : M.det * ϖ ^ q = D.det * (u * ϖ ^ p)`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, map_mul, map_pow, map_pow, hMD, hdet, zpow_sub₀ hϖK, zpow_natCast, zpow_natCast]`. Clear the denominators using the available nonvanishing facts. Establish `hϖ0 : ϖ ∈ nonZeroDivisors R` using `mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero`.

Establish `hlen` using `congrArg (Ring.ord R) hR`. Rewrite `hlen` using `[Ring.ord_mul R (pow_mem hϖ0 q), Ring.ord_mul' R (mem_nonZeroDivisors_of_ne_zero hD), Ring.ord_mul R (pow_mem hϖ0 p), Ring.ord_of_isUnit u.isUnit, Ring.ord_pow hϖ0, Ring.ord_pow hϖ0, hord, ← h1, ← h2]`. Establish `f1` using `Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hM0)`. Establish `f2` using `Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hD)`. Rewrite `f1` using `[← h1]`.

Rewrite `f2` using `[← h2]`. Take `⟨x, hx⟩` from `ENat.ne_top_iff_exists.mp (WithTop.add_ne_top.mp f1).1`. Take `⟨y, hy⟩` from `ENat.ne_top_iff_exists.mp (WithTop.add_ne_top.mp f1).2`. Take `⟨z, hz⟩` from `ENat.ne_top_iff_exists.mp (WithTop.add_ne_top.mp f2).2`. Rewrite using `[signedLength_eq_of_relLength_eq hy.symm hz.symm]`.

Rewrite `hlen` using `[← hx, ← hy, ← hz, nsmul_one, nsmul_one, zero_add]`. Establish `: x + y + q = x + z + p` using `by exact_mod_cast hlen`. Use linear arithmetic over natural numbers and integers.
-/
theorem signedLength_span_eq {R : Type u_1} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type u_2} [Field K] [Algebra R K] [IsFractionRing R K]
    {V : Type u_3} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    {ι : Type u_4} [Fintype ι] [DecidableEq ι] {a b : ι → V} (ha : LinearIndependent K a)
    (g : Matrix ι ι K) (hb : ∀ j, b j = ∑ i, g i j • a i) {ϖ : R} (hϖ : Irreducible ϖ)
    (u : Rˣ) (n : ℤ) (hdet : g.det = algebraMap R K (u : R) * algebraMap R K ϖ ^ n) :
    signedLength (Submodule.span R (Set.range a)) (Submodule.span R (Set.range b)) = n := by
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hϖK : algebraMap R K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hϖ.ne_zero
  have hg : g.det ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero ((map_ne_zero_iff _ hinj).mpr u.ne_zero) (zpow_ne_zero _ hϖK)
  have hbK : LinearIndependent K b := by
    rw [Fintype.linearIndependent_iff] at ha ⊢
    intro x hx
    have h0 : g.mulVec x = 0 := by
      funext i
      refine ha (g.mulVec x) ?_ i
      rw [← hx]
      simp only [hb, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [mul_comm]
    exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hg h0)
  have hres : ∀ {v : ι → V}, LinearIndependent K v → LinearIndependent R v := fun hv =>
    hv.restrict_scalars (by simpa [← Algebra.algebraMap_eq_smul_one] using hinj)
  obtain ⟨⟨t, ht⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun p : ι × ι => g p.1 p.2)
  choose m hm using hint
  let M : Matrix ι ι R := Matrix.of fun i j => m (i, j)
  have hM : (algebraMap R K).mapMatrix M = algebraMap R K t • g := by
    ext i j
    simp [M, hm, Algebra.smul_def]
  let D : Matrix ι ι R := Matrix.diagonal fun _ => t
  have hD : D.det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => nonZeroDivisors.ne_zero ht
  have hMD : algebraMap R K M.det = algebraMap R K D.det * g.det := by
    rw [RingHom.map_det, hM, Matrix.det_smul, Matrix.det_diagonal]
    simp
  have hM0 : M.det ≠ 0 := by
    rw [← map_ne_zero_iff _ hinj, hMD]
    exact mul_ne_zero ((map_ne_zero_iff _ hinj).mpr hD) hg
  let c : ι → V := fun j => t • b j
  have hca : ∀ j, c j = ∑ i, M i j • a i := by
    intro j
    simp only [c, hb, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← smul_assoc, ← hm (i, j), algebraMap_smul]
    rfl
  have hcb : ∀ j, c j = ∑ i, D i j • b i := by
    intro j
    simp [c, D, Matrix.diagonal_apply, ite_smul]
  have hle : ∀ {v : ι → V} {N : Matrix ι ι R}, (∀ j, c j = ∑ i, N i j • v i) →
      Submodule.span R (Set.range c) ≤ Submodule.span R (Set.range v) := by
    intro v N hN
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [hN]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have h1 := relLength_span_matrix (hres ha) M hM0 hca
  have h2 := relLength_span_matrix (hres hbK) D hD hcb
  have hC := le_inf (hle hca) (hle hcb)
  rw [relLength_tower inf_le_left hC, relLength_inf_right] at h1
  rw [relLength_tower inf_le_right hC, relLength_inf_right'] at h2
  have hord : Ring.ord R ϖ = 1 := by
    have := PrincipalIdealRing.isMaximal_of_irreducible hϖ
    have h := relLength_top_of_isMaximal (Ideal.span {ϖ})
    rw [relLength_top_left] at h
    exact h
  obtain ⟨p, q, rfl⟩ : ∃ p q : ℕ, n = (p : ℤ) - q := ⟨n.toNat, (-n).toNat, by omega⟩
  have hR : M.det * ϖ ^ q = D.det * (u * ϖ ^ p) := by
    apply hinj
    rw [map_mul, map_mul, map_mul, map_pow, map_pow, hMD, hdet, zpow_sub₀ hϖK, zpow_natCast,
      zpow_natCast]
    field_simp
  have hϖ0 : ϖ ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero
  have hlen := congrArg (Ring.ord R) hR
  rw [Ring.ord_mul R (pow_mem hϖ0 q), Ring.ord_mul' R (mem_nonZeroDivisors_of_ne_zero hD),
    Ring.ord_mul R (pow_mem hϖ0 p), Ring.ord_of_isUnit u.isUnit, Ring.ord_pow hϖ0,
    Ring.ord_pow hϖ0, hord, ← h1, ← h2] at hlen
  have f1 := Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hM0)
  have f2 := Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hD)
  rw [← h1] at f1
  rw [← h2] at f2
  obtain ⟨x, hx⟩ := ENat.ne_top_iff_exists.mp (WithTop.add_ne_top.mp f1).1
  obtain ⟨y, hy⟩ := ENat.ne_top_iff_exists.mp (WithTop.add_ne_top.mp f1).2
  obtain ⟨z, hz⟩ := ENat.ne_top_iff_exists.mp (WithTop.add_ne_top.mp f2).2
  rw [signedLength_eq_of_relLength_eq hy.symm hz.symm]
  rw [← hx, ← hy, ← hz, nsmul_one, nsmul_one, zero_add] at hlen
  have : x + y + q = x + z + p := by exact_mod_cast hlen
  omega

end GlobalTheory.SignedLengthTower
