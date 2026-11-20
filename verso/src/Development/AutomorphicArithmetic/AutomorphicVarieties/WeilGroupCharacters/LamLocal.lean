import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Inertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
import GroundTheory.LocalFields.LocalArtinCompletion
import GroundTheory.LocalFields.PrincipalUnitsRank
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixingSubgroupEquivBicontinuous

open Topology Filter

/- English proof (translation)
Use `set F : A → Filter M := fun x => comap r (𝓝 x) with hF`. Establish `hne : ∀ x, (F x).NeBot` using `fun x => comap_neBot (fun t ht => by`. Take `⟨_, hy, m, rfl⟩` from `mem_closure_iff_nhds.mp (hr x) t ht`. Conclude with `⟨m, hy⟩)`. Establish `hrt : ∀ x, Tendsto r (F x) (𝓝 x)` using `fun x => tendsto_comap`.

Establish `hex : ∀ x, ∃ c, Tendsto φ (F x) (𝓝 c)`. Introduce `x`. Use `haveI := hne x`. Establish `h1 : Tendsto (fun p : M × M => p.2 / p.1) (F x ×ˢ F x) (comap r (𝓝 1))`. Rewrite using `[tendsto_comap_iff]`.

Use `((hrt x).comp tendsto_snd).div' ((hrt x).comp tendsto_fst)` as an intermediate fact. Simplify `this` using `[Function.comp_def, map_div]`. Establish `hc : Cauchy (map φ (F x))`. Use `⟨inferInstance, ?_⟩` and prove the remaining obligations. Rewrite using `[prod_map_map_eq, uniformity_eq_comap_nhds_one P, ← map_le_iff_le_comap, map_map]`.

Use `le_trans (le_of_eq ?_) (h.comp h1)` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `p`. Simplify using `[map_div]`. Conclude with `CompleteSpace.complete hc`.

Set `a : A → P` to `fun x => limUnder (F x) φ`. Establish `ha : ∀ x, Tendsto φ (F x) (𝓝 (a x))` using `fun x => tendsto_nhds_limUnder (hex x)`. Establish `hrm : ∀ m, a (r m) = φ m`. Introduce `m`. Use `haveI := hne (r m)`.

Use `tendsto_nhds_unique (ha (r m)) ?_` and prove the remaining obligations. Establish `h1 : Tendsto (fun n => m⁻¹ * n) (F (r m)) (comap r (𝓝 1))`. Rewrite using `[tendsto_comap_iff]`. Use `(hrt (r m)).const_mul (r m)⁻¹` as an intermediate fact. Simplify `this` using `[Function.comp_def, map_mul, map_inv]`.

Establish `h2` using `(h.comp h1).const_mul (φ m)`. Simplify `h2` using `[Function.comp_def, map_mul, map_inv]`. Establish `hmul : ∀ x y, a (x * y) = a x * a y`. Introduce `x y`. Use `haveI := hne x`.

Use `haveI := hne y`. Establish `h1 : Tendsto (fun p : M × M => p.1 * p.2) (F x ×ˢ F y) (F (x * y))`. Rewrite using `[hF, tendsto_comap_iff]`. Use `((hrt x).comp tendsto_fst).mul ((hrt y).comp tendsto_snd)` as an intermediate fact. Simplify `this` using `[Function.comp_def, map_mul]`.

Establish `h2` using `(ha (x * y)).comp h1`. Establish `h3` using `((ha x).comp tendsto_fst).mul ((ha y).comp tendsto_snd)`. Use `tendsto_nhds_unique h2 ?_` and prove the remaining obligations. Simplify `h3` using `[Function.comp_def, map_mul]`. Set `aH : A →* P` to `{ toFun := a map_one' := by simpa using hrm 1 map_mul' := hmul }`.

Use `⟨aH, ?_, hrm⟩` and prove the remaining obligations. Apply `continuous_of_continuousAt_one aH` to reduce the goal to its premises. Rewrite using `[ContinuousAt, map_one, (closed_nhds_basis (1 : P)).tendsto_right_iff]`. Introduce and unpack `V ⟨hV, hVc⟩`. Take `⟨U, hU, hUV⟩` from `mem_comap.mp (h hV)`.

Take `⟨W, hWU, hWo, hW1⟩` from `mem_nhds_iff.mp hU`. Use `filter_upwards [hWo.mem_nhds hW1] with x hx`. Use `haveI := hne x`. Conclude with `hVc.mem_of_tendsto (ha x) (Filter.mem_of_superset (preimage_mem_comap (hWo.mem_nhds hx)) (fun m hm => hUV (hWU hm)))`.
-/
private theorem ext_hom {M A P : Type} [CommGroup M] [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CommGroup P] [UniformSpace P] [IsUniformGroup P] [CompleteSpace P] [T2Space P]
    (r : M →* A) (hr : DenseRange r) (φ : M →* P) (h : Tendsto φ (comap r (𝓝 1)) (𝓝 1)) :
    ∃ a : A →* P, Continuous a ∧ ∀ x, a (r x) = φ x := by
  set F : A → Filter M := fun x => comap r (𝓝 x) with hF
  have hne : ∀ x, (F x).NeBot := fun x => comap_neBot (fun t ht => by
    obtain ⟨_, hy, m, rfl⟩ := mem_closure_iff_nhds.mp (hr x) t ht
    exact ⟨m, hy⟩)
  have hrt : ∀ x, Tendsto r (F x) (𝓝 x) := fun x => tendsto_comap
  have hex : ∀ x, ∃ c, Tendsto φ (F x) (𝓝 c) := by
    intro x
    haveI := hne x
    have h1 : Tendsto (fun p : M × M => p.2 / p.1) (F x ×ˢ F x) (comap r (𝓝 1)) := by
      rw [tendsto_comap_iff]
      have := ((hrt x).comp tendsto_snd).div' ((hrt x).comp tendsto_fst)
      simpa [Function.comp_def, map_div] using this
    have hc : Cauchy (map φ (F x)) := by
      refine ⟨inferInstance, ?_⟩
      rw [prod_map_map_eq, uniformity_eq_comap_nhds_one P, ← map_le_iff_le_comap, map_map]
      refine le_trans (le_of_eq ?_) (h.comp h1)
      congr 1
      funext p
      simp [map_div]
    exact CompleteSpace.complete hc
  let a : A → P := fun x => limUnder (F x) φ
  have ha : ∀ x, Tendsto φ (F x) (𝓝 (a x)) := fun x => tendsto_nhds_limUnder (hex x)
  have hrm : ∀ m, a (r m) = φ m := by
    intro m
    haveI := hne (r m)
    refine tendsto_nhds_unique (ha (r m)) ?_
    have h1 : Tendsto (fun n => m⁻¹ * n) (F (r m)) (comap r (𝓝 1)) := by
      rw [tendsto_comap_iff]
      have := (hrt (r m)).const_mul (r m)⁻¹
      simpa [Function.comp_def, map_mul, map_inv] using this
    have h2 := (h.comp h1).const_mul (φ m)
    simpa [Function.comp_def, map_mul, map_inv] using h2
  have hmul : ∀ x y, a (x * y) = a x * a y := by
    intro x y
    haveI := hne x
    haveI := hne y
    have h1 : Tendsto (fun p : M × M => p.1 * p.2) (F x ×ˢ F y) (F (x * y)) := by
      rw [hF, tendsto_comap_iff]
      have := ((hrt x).comp tendsto_fst).mul ((hrt y).comp tendsto_snd)
      simpa [Function.comp_def, map_mul] using this
    have h2 := (ha (x * y)).comp h1
    have h3 := ((ha x).comp tendsto_fst).mul ((ha y).comp tendsto_snd)
    refine tendsto_nhds_unique h2 ?_
    simpa [Function.comp_def, map_mul] using h3
  let aH : A →* P :=
    { toFun := a
      map_one' := by simpa using hrm 1
      map_mul' := hmul }
  refine ⟨aH, ?_, hrm⟩
  apply continuous_of_continuousAt_one aH
  rw [ContinuousAt, map_one, (closed_nhds_basis (1 : P)).tendsto_right_iff]
  rintro V ⟨hV, hVc⟩
  obtain ⟨U, hU, hUV⟩ := mem_comap.mp (h hV)
  obtain ⟨W, hWU, hWo, hW1⟩ := mem_nhds_iff.mp hU
  filter_upwards [hWo.mem_nhds hW1] with x hx
  haveI := hne x
  exact hVc.mem_of_tendsto (ha x)
    (Filter.mem_of_superset (preimage_mem_comap (hWo.mem_nhds hx)) (fun m hm => hUV (hWU hm)))

/- English proof (translation)
Set `T` to `Submodule.torsion ℤ_[l] N`. Use `haveI : Module.Free ℤ_[l] (N ⧸ T) := Module.Free.of_basis (Module.basisOfFiniteTypeTorsionFree' (R := ℤ_[l]) (M := N ⧸ T)).2`. Establish `hr : Module.finrank ℤ_[l] (N ⧸ T) = Module.finrank ℤ_[l] N` using `finrank_quotient_eq_of_le_torsion le_rfl`. Set `b` to `(Module.finBasis ℤ_[l] (N ⧸ T)).reindex (finCongr hr)`. Take `⟨s0, hs0⟩` from `Module.projective_lifting_property T.mkQ LinearMap.id T.mkQ_surjective`.

Take `⟨a, ha, ha0⟩` from `Submodule.annihilator_top_inter_nonZeroDivisors (R := ℤ_[l]) (M := T) (Submodule.torsion_isTorsion)`. Establish `hane : a ≠ 0` using `nonZeroDivisors.ne_zero ha0`. Use `⟨b.equivFun.toLinearMap ∘ₗ T.mkQ, s0 ∘ₗ b.equivFun.symm.toLinearMap, a.valuation, ?_, ?_⟩` and prove the remaining obligations. Introduce `y`. Establish `h` using `congrArg (fun g => g (b.equivFun.symm y)) hs0`.

Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply] at h`. Use `show b.equivFun (T.mkQ (s0 (b.equivFun.symm y))) = y`. Rewrite using `[h, LinearEquiv.apply_symm_apply]`. Introduce `n hn`. Establish `hq : T.mkQ n = 0` using `b.equivFun.injective (by simpa using hn)`.

Establish `hmem : n ∈ T` using `by simpa using hq`. Establish `hk : a • (⟨n, hmem⟩ : T) = 0` using `Submodule.mem_annihilator.mp (SetLike.mem_coe.mp ha) _ Submodule.mem_top`. Establish `hk' : a • n = 0` using `by simpa using congrArg Subtype.val hk`. Rewrite using `[← Nat.cast_smul_eq_nsmul ℤ_[l], Nat.cast_pow]`. Establish `h2 : ((PadicInt.unitCoeff hane : ℤ_[l]) * (l : ℤ_[l]) ^ a.valuation) • n = 0`.

Rewrite using `[← PadicInt.unitCoeff_spec hane]`. Conclude with `hk'`. Rewrite `h2` using `[mul_smul]`. Establish `h3` using `congrArg (fun m => (((PadicInt.unitCoeff hane)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • m) h2`. Simplify `h3` using `[smul_smul]`.
-/
private theorem mod_split (l : ℕ) [Fact l.Prime] (N : Type) [AddCommGroup N] [Module ℤ_[l] N] [Module.Finite ℤ_[l] N] :
    ∃ (f : N →ₗ[ℤ_[l]] (Fin (Module.finrank ℤ_[l] N) → ℤ_[l])) (s : (Fin (Module.finrank ℤ_[l] N) → ℤ_[l]) →ₗ[ℤ_[l]] N) (e : ℕ),
      (∀ y, f (s y) = y) ∧ ∀ n, f n = 0 → l ^ e • n = 0 := by
  classical
  let T := Submodule.torsion ℤ_[l] N
  haveI : Module.Free ℤ_[l] (N ⧸ T) :=
    Module.Free.of_basis (Module.basisOfFiniteTypeTorsionFree' (R := ℤ_[l]) (M := N ⧸ T)).2
  have hr : Module.finrank ℤ_[l] (N ⧸ T) = Module.finrank ℤ_[l] N :=
    finrank_quotient_eq_of_le_torsion le_rfl
  let b := (Module.finBasis ℤ_[l] (N ⧸ T)).reindex (finCongr hr)
  obtain ⟨s0, hs0⟩ := Module.projective_lifting_property T.mkQ LinearMap.id T.mkQ_surjective
  obtain ⟨a, ha, ha0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors (R := ℤ_[l]) (M := T)
    (Submodule.torsion_isTorsion)
  have hane : a ≠ 0 := nonZeroDivisors.ne_zero ha0
  refine ⟨b.equivFun.toLinearMap ∘ₗ T.mkQ, s0 ∘ₗ b.equivFun.symm.toLinearMap, a.valuation, ?_, ?_⟩
  · intro y
    have h := congrArg (fun g => g (b.equivFun.symm y)) hs0
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
    show b.equivFun (T.mkQ (s0 (b.equivFun.symm y))) = y
    rw [h, LinearEquiv.apply_symm_apply]
  · intro n hn
    have hq : T.mkQ n = 0 := b.equivFun.injective (by simpa using hn)
    have hmem : n ∈ T := by simpa using hq
    have hk : a • (⟨n, hmem⟩ : T) = 0 :=
      Submodule.mem_annihilator.mp (SetLike.mem_coe.mp ha) _ Submodule.mem_top
    have hk' : a • n = 0 := by simpa using congrArg Subtype.val hk
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l], Nat.cast_pow]
    have h2 : ((PadicInt.unitCoeff hane : ℤ_[l]) * (l : ℤ_[l]) ^ a.valuation) • n = 0 := by
      rw [← PadicInt.unitCoeff_spec hane]
      exact hk'
    rw [mul_smul] at h2
    have h3 := congrArg (fun m => (((PadicInt.unitCoeff hane)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • m) h2
    simpa [smul_smul] using h3

/- English proof (translation)
Take `⟨f, s, e, hfs, hker⟩` from `mod_split l (Additive U)`. Set `wf : M →* M` to `MonoidHom.mk' (fun x => x * π ^ (-(o x).toAdd)) (by`. Introduce `x y`. Simplify using `only [map_mul, toAdd_mul, neg_add, zpow_add]`. Rewrite using `[mul_mul_mul_comm])`.

Establish `hwo : ∀ x, o (wf x) = 1`. Introduce `x`. Use `show o (x * π ^ (-(o x).toAdd)) = 1`. Rewrite using `[map_mul, map_zpow, hπ, ← ofAdd_zsmul, ← ofAdd_toAdd (o x), ← ofAdd_add]`. Simplify using the standard rewrite rules.

Establish `hw1 : ∀ x, o x = 1 → wf x = x`. Introduce `x hx`. Use `show x * π ^ (-(o x).toAdd) = x`. Simplify using `[hx]`. Set `g : M →* U` to `MonoidHom.mk' (fun x => ⟨(wf x) ^ m, hmU _ (hwo x)⟩) (by`.

Introduce `x y`. Use `ext`. Simplify using `[mul_pow])`. Establish `hgU : ∀ v : U, g v = v ^ m`. Introduce `v`.

Use `ext`. Simplify using `[g, hw1 _ (hU v v.2)]`. Take `⟨u, hu⟩ : IsUnit (m : ℤ_[l])` from `PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr hm)`. Set `φ : M →* Multiplicative ((Fin (Module.finrank ℤ_[l] (Additive U)) → ℤ_[l]) × ℤ_[l])` to `MonoidHom.mk' (fun x => Multiplicative.ofAdd ((((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • f (Additive.ofMul (g x)), (((o x).toAdd : ℤ) : ℤ_[l])))) (by`. Introduce `x y`.

Rewrite using `[← ofAdd_add]`. Use `congr 1`. Apply the tactic sequence `ext <;> simp [smul_add, mul_add])`. Set `τ : Additive U →ₗ[ℤ_[l]] Additive U` to `LinearMap.id - s ∘ₗ f`. Establish `hτ : ∀ z, f (τ z) = 0` using `by intro z; simp [τ, hfs]`.

Establish `hττ : ∀ w, f w = 0 → τ w = w` using `by intro w hw; simp [τ, hw]`. Choose the witnesses or unpack the hypotheses as in `⟨a, b, hab⟩ : IsCoprime (m : ℤ) ((l : ℤ) ^ e) := by`. Use `Nat.isCoprime_iff_coprime.mpr (hm.symm.pow_right e)` as an intermediate fact. Simplify using `using this`. Establish `key : ∀ w : Additive U, f w = 0 → a • (m • w) = w`.

Introduce `w hw`. Establish `hl : ((l : ℤ) ^ e) • w = 0`. Rewrite using `[← Nat.cast_pow, natCast_zsmul, hker w hw]`. Combine the equalities or inequalities in the displayed calculation. Set `β : M →* M` to `MonoidHom.mk' (fun x => ((Additive.toMul (a • τ (Additive.ofMul (g x))) : U) : M)) (by`.

Introduce `x y`. Simplify using `[smul_add, toMul_add])`. Use `⟨φ, β, e, fun x => rfl, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `y`. Use `⟨((Additive.toMul (s y) : U) : M), hU _ (Additive.toMul (s y)).2, ?_⟩` and prove the remaining obligations.

Use `show ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • f (Additive.ofMul (g ((Additive.toMul (s y) : U) : M))) = y`. Rewrite using `[hgU, ofMul_pow, ofMul_toMul, map_nsmul, hfs, ← Nat.cast_smul_eq_nsmul ℤ_[l], ← hu, smul_smul, Units.inv_mul, one_smul]`. Introduce `x show ((Additive.toMul (a • τ (Additive.ofMul (g x))) : U) : M) ^ l ^ e = 1`. Rewrite using `[← SubmonoidClass.coe_pow, ← toMul_nsmul, smul_comm, hker _ (hτ _), smul_zero, toMul_zero, OneMemClass.coe_one]`. Introduce `x set w : Additive U := a • τ (Additive.ofMul (g x)) with hw`.

Establish `hfw : f w = 0` using `by simp [hw, hτ]`. Use `show ((Additive.toMul (a • τ (Additive.ofMul (g ((Additive.toMul w : U) : M)))) : U) : M) = ((Additive.toMul w : U) : M)`. Rewrite using `[hgU, ofMul_pow, ofMul_toMul, map_nsmul, hττ _ hfw, key _ hfw]`. Introduce and unpack `k x ⟨y, hy⟩ hb`. Establish `hb' : a • τ (Additive.ofMul (g x)) = 0`.

Establish `h1 : (Additive.toMul (a • τ (Additive.ofMul (g x))) : U) = 1` using `Subtype.ext hb`. Simplify using `using congrArg Additive.ofMul h1`. Establish `hτ0 : τ (Additive.ofMul (g x)) = 0`. Establish `h1` using `key (τ (Additive.ofMul (g x))) (hτ _)`. Rewrite using `[← h1, smul_comm, hb', smul_zero]`.

Establish `hz : Additive.ofMul (g x) = s (f (Additive.ofMul (g x)))`. Establish `h1` using `hτ0`. Simplify using `only [τ, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply] at h1`. Conclude with `sub_eq_zero.mp h1`. Establish `hy1 : ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • f (Additive.ofMul (g x)) = l ^ k • y.1` using `congrArg Prod.fst hy`.

Establish `hy2 : (((o x).toAdd : ℤ) : ℤ_[l]) = l ^ k • y.2` using `congrArg Prod.snd hy`. Establish `hfz : f (Additive.ofMul (g x)) = l ^ k • ((u : ℤ_[l]) • y.1)`. Rewrite using `[smul_comm, ← hy1, smul_smul, Units.mul_inv, one_smul]`. Set `v : U` to `Additive.toMul (s ((u : ℤ_[l]) • y.1))`. Establish `hgv : g x = v ^ (l ^ k)`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Rewrite using `[ofMul_pow, hz, hfz, map_nsmul]`. Both sides reduce to the same expression. Establish `hdiv : ((l : ℤ) ^ k) ∣ (o x).toAdd`. Rewrite using `[← PadicInt.norm_int_le_pow_iff_dvd, hy2, nsmul_eq_mul, norm_mul]`.

Establish `h1 : ‖((l ^ k : ℕ) : ℤ_[l])‖ = (l : ℝ) ^ (-k : ℤ)`. Simplify using `[PadicInt.norm_p_pow]`. Rewrite using `[h1]`. Conclude with `mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one _)`. Take `⟨n0, hn0⟩` from `hdiv`.

Choose the witnesses or unpack the hypotheses as in `⟨a', b', hab'⟩ : IsCoprime (m : ℤ) ((l : ℤ) ^ k) := by`. Use `Nat.isCoprime_iff_coprime.mpr (hm.symm.pow_right k)` as an intermediate fact. Simplify using `using this`. Establish `hwm : (wf x) ^ (m : ℤ) = ((v : M)) ^ ((l : ℤ) ^ k)`. Establish `h1` using `congrArg Subtype.val hgv`.

Simplify using `only [g, MonoidHom.mk'_apply, SubmonoidClass.coe_pow] at h1`. Rewrite using `[show ((l : ℤ) ^ k) = ((l ^ k : ℕ) : ℤ) by push_cast; rfl, zpow_natCast, zpow_natCast]`. Conclude with `h1`. Establish `hx : x = wf x * π ^ (o x).toAdd` using `by show x = x * π ^ (-(o x).toAdd) * π ^ (o x).toAdd`. Rewrite using `[mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]`.

Use `⟨(v : M) ^ a' * (wf x) ^ b' * π ^ n0, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hab', zpow_one, hn0]`. Use `_ = ((v : M) ^ a' * (wf x) ^ b' * π ^ n0) ^ ((l : ℤ) ^ k) := by`. Rewrite using `[zpow_add, mul_comm a' (m : ℤ), zpow_mul (wf x) (m : ℤ) a', hwm, mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul, mul_comm ((l : ℤ) ^ k) a', mul_comm ((l : ℤ) ^ k) n0]`.

Use `_ = ((v : M) ^ a' * (wf x) ^ b' * π ^ n0) ^ (l ^ k) := by`. Rewrite using `[← zpow_natCast]`. Use `push_cast`. Both sides reduce to the same expression.
-/
private theorem units_pack (l : ℕ) [Fact l.Prime] (M : Type) [CommGroup M] (o : M →* Multiplicative ℤ) (π : M)
    (hπ : o π = Multiplicative.ofAdd 1) (U : Subgroup M) (hU : ∀ u ∈ U, o u = 1) (m : ℕ) (hm : l.Coprime m)
    (hmU : ∀ x, o x = 1 → x ^ m ∈ U) [Module ℤ_[l] (Additive U)] [Module.Finite ℤ_[l] (Additive U)] :
    ∃ (φ : M →* Multiplicative ((Fin (Module.finrank ℤ_[l] (Additive U)) → ℤ_[l]) × ℤ_[l])) (β : M →* M) (e : ℕ),
      (∀ x, (φ x).toAdd.2 = ((o x).toAdd : ℤ)) ∧ (∀ y, ∃ x, o x = 1 ∧ (φ x).toAdd.1 = y) ∧ (∀ x, β x ^ l ^ e = 1) ∧
      (∀ x, β (β x) = β x) ∧
      ∀ (k : ℕ) x, (∃ y, (φ x).toAdd = l ^ k • y) → β x = 1 → ∃ z, x = z ^ l ^ k := by
  classical
  obtain ⟨f, s, e, hfs, hker⟩ := mod_split l (Additive U)
  let wf : M →* M := MonoidHom.mk' (fun x => x * π ^ (-(o x).toAdd)) (by
    intro x y
    simp only [map_mul, toAdd_mul, neg_add, zpow_add]
    rw [mul_mul_mul_comm])
  have hwo : ∀ x, o (wf x) = 1 := by
    intro x
    show o (x * π ^ (-(o x).toAdd)) = 1
    rw [map_mul, map_zpow, hπ, ← ofAdd_zsmul, ← ofAdd_toAdd (o x), ← ofAdd_add]
    simp
  have hw1 : ∀ x, o x = 1 → wf x = x := by
    intro x hx
    show x * π ^ (-(o x).toAdd) = x
    simp [hx]
  let g : M →* U := MonoidHom.mk' (fun x => ⟨(wf x) ^ m, hmU _ (hwo x)⟩) (by
    intro x y
    ext
    simp [mul_pow])
  have hgU : ∀ v : U, g v = v ^ m := by
    intro v
    ext
    simp [g, hw1 _ (hU v v.2)]
  obtain ⟨u, hu⟩ : IsUnit (m : ℤ_[l]) :=
    PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr hm)
  let φ : M →* Multiplicative ((Fin (Module.finrank ℤ_[l] (Additive U)) → ℤ_[l]) × ℤ_[l]) :=
    MonoidHom.mk' (fun x => Multiplicative.ofAdd
      ((((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • f (Additive.ofMul (g x)), (((o x).toAdd : ℤ) : ℤ_[l]))))
      (by
        intro x y
        rw [← ofAdd_add]
        congr 1
        ext <;> simp [smul_add, mul_add])
  let τ : Additive U →ₗ[ℤ_[l]] Additive U := LinearMap.id - s ∘ₗ f
  have hτ : ∀ z, f (τ z) = 0 := by intro z; simp [τ, hfs]
  have hττ : ∀ w, f w = 0 → τ w = w := by intro w hw; simp [τ, hw]
  obtain ⟨a, b, hab⟩ : IsCoprime (m : ℤ) ((l : ℤ) ^ e) := by
    have := Nat.isCoprime_iff_coprime.mpr (hm.symm.pow_right e)
    simpa using this
  have key : ∀ w : Additive U, f w = 0 → a • (m • w) = w := by
    intro w hw
    have hl : ((l : ℤ) ^ e) • w = 0 := by
      rw [← Nat.cast_pow, natCast_zsmul, hker w hw]
    calc a • (m • w) = (a * m) • w := by rw [← natCast_zsmul, smul_smul]
      _ = (1 - b * (l : ℤ) ^ e) • w := by rw [← hab]; ring_nf
      _ = w := by rw [sub_smul, one_smul, mul_smul, hl, smul_zero, sub_zero]
  let β : M →* M := MonoidHom.mk'
    (fun x => ((Additive.toMul (a • τ (Additive.ofMul (g x))) : U) : M)) (by
      intro x y
      simp [smul_add, toMul_add])
  refine ⟨φ, β, e, fun x => rfl, ?_, ?_, ?_, ?_⟩
  · intro y
    refine ⟨((Additive.toMul (s y) : U) : M), hU _ (Additive.toMul (s y)).2, ?_⟩
    show ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • f (Additive.ofMul (g ((Additive.toMul (s y) : U) : M))) = y
    rw [hgU, ofMul_pow, ofMul_toMul, map_nsmul, hfs, ← Nat.cast_smul_eq_nsmul ℤ_[l], ← hu,
      smul_smul, Units.inv_mul, one_smul]
  · intro x
    show ((Additive.toMul (a • τ (Additive.ofMul (g x))) : U) : M) ^ l ^ e = 1
    rw [← SubmonoidClass.coe_pow, ← toMul_nsmul, smul_comm, hker _ (hτ _), smul_zero, toMul_zero,
      OneMemClass.coe_one]
  · intro x
    set w : Additive U := a • τ (Additive.ofMul (g x)) with hw
    have hfw : f w = 0 := by simp [hw, hτ]
    show ((Additive.toMul (a • τ (Additive.ofMul (g ((Additive.toMul w : U) : M)))) : U) : M) =
      ((Additive.toMul w : U) : M)
    rw [hgU, ofMul_pow, ofMul_toMul, map_nsmul, hττ _ hfw, key _ hfw]
  · rintro k x ⟨y, hy⟩ hb
    have hb' : a • τ (Additive.ofMul (g x)) = 0 := by
      have h1 : (Additive.toMul (a • τ (Additive.ofMul (g x))) : U) = 1 := Subtype.ext hb
      simpa using congrArg Additive.ofMul h1
    have hτ0 : τ (Additive.ofMul (g x)) = 0 := by
      have h1 := key (τ (Additive.ofMul (g x))) (hτ _)
      rw [← h1, smul_comm, hb', smul_zero]
    have hz : Additive.ofMul (g x) = s (f (Additive.ofMul (g x))) := by
      have h1 := hτ0
      simp only [τ, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply] at h1
      exact sub_eq_zero.mp h1
    have hy1 : ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • f (Additive.ofMul (g x)) = l ^ k • y.1 :=
      congrArg Prod.fst hy
    have hy2 : (((o x).toAdd : ℤ) : ℤ_[l]) = l ^ k • y.2 := congrArg Prod.snd hy
    have hfz : f (Additive.ofMul (g x)) = l ^ k • ((u : ℤ_[l]) • y.1) := by
      rw [smul_comm, ← hy1, smul_smul, Units.mul_inv, one_smul]
    let v : U := Additive.toMul (s ((u : ℤ_[l]) • y.1))
    have hgv : g x = v ^ (l ^ k) := by
      apply Additive.ofMul.injective
      rw [ofMul_pow, hz, hfz, map_nsmul]
      rfl
    have hdiv : ((l : ℤ) ^ k) ∣ (o x).toAdd := by
      rw [← PadicInt.norm_int_le_pow_iff_dvd, hy2, nsmul_eq_mul, norm_mul]
      have h1 : ‖((l ^ k : ℕ) : ℤ_[l])‖ = (l : ℝ) ^ (-k : ℤ) := by
        simp [PadicInt.norm_p_pow]
      rw [h1]
      exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one _)
    obtain ⟨n0, hn0⟩ := hdiv
    obtain ⟨a', b', hab'⟩ : IsCoprime (m : ℤ) ((l : ℤ) ^ k) := by
      have := Nat.isCoprime_iff_coprime.mpr (hm.symm.pow_right k)
      simpa using this
    have hwm : (wf x) ^ (m : ℤ) = ((v : M)) ^ ((l : ℤ) ^ k) := by
      have h1 := congrArg Subtype.val hgv
      simp only [g, MonoidHom.mk'_apply, SubmonoidClass.coe_pow] at h1
      rw [show ((l : ℤ) ^ k) = ((l ^ k : ℕ) : ℤ) by push_cast; rfl, zpow_natCast, zpow_natCast]
      exact h1
    have hx : x = wf x * π ^ (o x).toAdd := by
      show x = x * π ^ (-(o x).toAdd) * π ^ (o x).toAdd
      rw [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
    refine ⟨(v : M) ^ a' * (wf x) ^ b' * π ^ n0, ?_⟩
    calc x = wf x * π ^ (o x).toAdd := hx
      _ = (wf x) ^ (a' * m + b' * (l : ℤ) ^ k) * π ^ ((l : ℤ) ^ k * n0) := by
          rw [hab', zpow_one, hn0]
      _ = ((v : M) ^ a' * (wf x) ^ b' * π ^ n0) ^ ((l : ℤ) ^ k) := by
          rw [zpow_add, mul_comm a' (m : ℤ), zpow_mul (wf x) (m : ℤ) a', hwm, mul_zpow, mul_zpow,
            ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul, mul_comm ((l : ℤ) ^ k) a',
            mul_comm ((l : ℤ) ^ k) n0]
      _ = ((v : M) ^ a' * (wf x) ^ b' * π ^ n0) ^ (l ^ k) := by
          rw [← zpow_natCast]
          push_cast
          rfl

/- English proof (translation)
Establish `hc : (0 : ℝ) ≤ (l : ℝ) ^ (-k : ℤ)` using `by positivity`. Establish `key : ∀ x : ℤ_[l], ‖x‖ ≤ (l : ℝ) ^ (-k : ℤ) ↔ ∃ w : ℤ_[l], x = l ^ k • w`. Introduce `x`. Rewrite using `[PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨w, rfl⟩`. Conclude with `⟨w, by rw [nsmul_eq_mul]; push_cast; ring⟩`. Introduce and unpack `⟨w, rfl⟩`. Conclude with `⟨w, by rw [nsmul_eq_mul]; push_cast; ring⟩`. Rewrite using `[norm_prod_le_iff, pi_norm_le_iff_of_nonneg hc]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩ choose w hw using fun i => (key _).mp (h1 i)`. Take `⟨w2, hw2⟩` from `(key _).mp h2`. Conclude with `⟨(w, w2), Prod.ext (funext fun i => by simp [hw i]) (by simp [hw2])⟩`. Introduce and unpack `⟨z, rfl⟩`.

Conclude with `⟨fun i => (key _).mpr ⟨z.1 i, by simp⟩, (key _).mpr ⟨z.2, by simp⟩⟩`.
-/
private theorem ball_pow (l d : ℕ) [Fact l.Prime] (k : ℕ) (y : (Fin d → ℤ_[l]) × ℤ_[l]) :
    ‖y‖ ≤ (l : ℝ) ^ (-k : ℤ) ↔ ∃ z, y = l ^ k • z := by
  have hc : (0 : ℝ) ≤ (l : ℝ) ^ (-k : ℤ) := by positivity
  have key : ∀ x : ℤ_[l], ‖x‖ ≤ (l : ℝ) ^ (-k : ℤ) ↔ ∃ w : ℤ_[l], x = l ^ k • w := by
    intro x
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w, by rw [nsmul_eq_mul]; push_cast; ring⟩
    · rintro ⟨w, rfl⟩
      exact ⟨w, by rw [nsmul_eq_mul]; push_cast; ring⟩
  rw [norm_prod_le_iff, pi_norm_le_iff_of_nonneg hc]
  constructor
  · rintro ⟨h1, h2⟩
    choose w hw using fun i => (key _).mp (h1 i)
    obtain ⟨w2, hw2⟩ := (key _).mp h2
    exact ⟨(w, w2), Prod.ext (funext fun i => by simp [hw i]) (by simp [hw2])⟩
  · rintro ⟨z, rfl⟩
    exact ⟨fun i => (key _).mpr ⟨z.1 i, by simp⟩, (key _).mpr ⟨z.2, by simp⟩⟩

/- English proof (translation)
The claim follows from `PadicInt.exists_pow_neg_lt l hε`.
-/
private theorem exists_zpow_lt (l : ℕ) [Fact l.Prime] {ε : ℝ} (hε : 0 < ε) : ∃ k : ℕ, (l : ℝ) ^ (-k : ℤ) < ε :=
  PadicInt.exists_pow_neg_lt l hε

/- English proof (translation)
Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective h`. Use `set N := (commutator G).topologicalClosure with hN`. Establish `hg : g ∉ N` using `fun hg => hh ((QuotientGroup.eq_one_iff g).mpr hg)`. Establish `hWo : IsOpen {w : G | g⁻¹ * w ∉ N}` using `(Subgroup.isClosed_topologicalClosure _).isOpen_compl.preimage (continuous_const.mul continuous_id)`. Establish `h1 : (1 : G) ∈ {w : G | g⁻¹ * w ∉ N}` using `by show g⁻¹ * 1 ∉ N`.

Rewrite using `[mul_one]`. Conclude with `fun h => hg (by simpa using N.inv_mem h)`. Take `⟨H, hH⟩` from `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hWo h1`. Use `⟨H.toSubgroup.map (QuotientGroup.mk' N), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.coe_map]`.

Conclude with `QuotientGroup.isOpenMap_coe _ H.isOpen`. Introduce `hm`. Take `⟨u, hu, he⟩` from `Subgroup.mem_map.mp hm`. Establish `hq` using `QuotientGroup.eq.mp he`. Conclude with `hH hu (by simpa [mul_inv_rev] using N.inv_mem hq)`.
-/
private theorem sep_open {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (h : TopologicalAbelianization G) (hh : h ≠ 1) :
    ∃ V : Subgroup (TopologicalAbelianization G), IsOpen (V : Set (TopologicalAbelianization G)) ∧ h ∉ V := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective h
  set N := (commutator G).topologicalClosure with hN
  have hg : g ∉ N := fun hg => hh ((QuotientGroup.eq_one_iff g).mpr hg)
  have hWo : IsOpen {w : G | g⁻¹ * w ∉ N} :=
    (Subgroup.isClosed_topologicalClosure _).isOpen_compl.preimage
      (continuous_const.mul continuous_id)
  have h1 : (1 : G) ∈ {w : G | g⁻¹ * w ∉ N} := by
    show g⁻¹ * 1 ∉ N
    rw [mul_one]
    exact fun h => hg (by simpa using N.inv_mem h)
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hWo h1
  refine ⟨H.toSubgroup.map (QuotientGroup.mk' N), ?_, ?_⟩
  · rw [Subgroup.coe_map]
    exact QuotientGroup.isOpenMap_coe _ H.isOpen
  · intro hm
    obtain ⟨u, hu, he⟩ := Subgroup.mem_map.mp hm
    have hq := QuotientGroup.eq.mp he
    exact hH hu (by simpa [mul_inv_rev] using N.inv_mem hq)

/- English proof (translation)
Establish `tf : ∀ (p : Multiplicative ((Fin d → ℤ_[l]) × ℤ_[l])) (j : ℕ), p ^ (l ^ j) = 1 → p = 1`. Introduce `p j hp`. Establish `h1 : (l ^ j : ℕ) • p.toAdd = 0`. Rewrite using `[← toAdd_pow, hp]`. Both sides reduce to the same expression.

Establish `hne : ((l : ℤ_[l]) ^ j) ≠ 0` using `pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)`. Rewrite `h1` using `[← Nat.cast_smul_eq_nsmul ℤ_[l], Nat.cast_pow, smul_eq_zero]`. Conclude with `toAdd_eq_zero.mp (h1.resolve_left hne)`. Establish `h0 : Tendsto (fun x => (φ x).toAdd) (Filter.comap r (𝓝 1)) (𝓝 0)`. Use `Metric.nhds_basis_closedBall.tendsto_right_iff.mpr fun ε hε => ?_` and prove the remaining obligations.

Take `⟨k, hk⟩` from `exists_zpow_lt l hε`. Take `⟨V, hV, hVx⟩` from `hopen k`. Use `filter_upwards [Filter.preimage_mem_comap hV] with x hx`. Take `⟨z, rfl⟩` from `hVx x hx`. Rewrite using `[Metric.mem_closedBall, dist_zero_right]`.

Use `((ball_pow l d k _).mpr ⟨(φ z).toAdd, ?_⟩).trans hk.le` and prove the remaining obligations. Rewrite using `[map_pow, toAdd_pow]`. Establish `htend : Tendsto φ (Filter.comap r (𝓝 1)) (𝓝 1)` using `(continuous_ofAdd.tendsto _).comp h0`. Take `⟨a, ha_cont, ha⟩` from `ext_hom r hr φ htend`. Use `letI : UniformSpace A := IsTopologicalGroup.rightUniformSpace A`.

Use `haveI : IsUniformGroup A := isUniformGroup_of_commGroup`. Use `haveI : CompleteSpace A := complete_of_compact`. Establish `htend2 : Tendsto (r.comp β) (Filter.comap r (𝓝 1)) (𝓝 1)`. Take `⟨V, hV, hVx⟩` from `hopen e`. Use `tendsto_const_nhds.congr' ?_` and prove the remaining obligations.

Use `filter_upwards [Filter.preimage_mem_comap hV] with x hx`. Take `⟨z, rfl⟩` from `hVx x hx`. Rewrite using `[MonoidHom.comp_apply, map_pow, hβe, map_one]`. Take `⟨b, hb_cont, hb⟩` from `ext_hom r hr (r.comp β) htend2`. Establish `hker : (b.ker : Set A) ∈ 𝓝 1`.

Take `⟨V, hV, hVx⟩` from `hopen e`. Establish `hsub : interior V ⊆ {h | b h = 1}`. Use `(hr.open_subset_closure_inter isOpen_interior).trans (closure_minimal ?_ (isClosed_eq hb_cont continuous_const))` and prove the remaining obligations. Introduce and unpack `_ ⟨hxV, x, rfl⟩`. Take `⟨z, rfl⟩` from `hVx _ (interior_subset hxV)`.

Use `show b (r _) = 1`. Rewrite using `[hb, MonoidHom.comp_apply, map_pow, hβe, map_one]`. Conclude with `Filter.mem_of_superset (interior_mem_nhds.mpr hV) (fun h hh => MonoidHom.mem_ker.mpr (hsub hh))`. Use `⟨a, b, ha_cont, ha, Subgroup.isOpen_of_mem_nhds _ hker, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g`.

Establish `heq` using `hr.equalizer (hb_cont.pow (l ^ e)) (continuous_const (y := (1 : A))) (funext fun x => by show b (r x) ^ l ^ e = 1`. Rewrite using `[hb, MonoidHom.comp_apply, ← map_pow, hβe, map_one])`. Conclude with `congrFun heq g`. Introduce `g`. Establish `heq` using `hr.equalizer (hb_cont.comp hb_cont) hb_cont (funext fun x => by show b (b (r x)) = b (r x)`.

Simplify using `only [hb, MonoidHom.comp_apply, hββ])`. Conclude with `congrFun heq g`. Introduce `j g hg`. Conclude with `tf (a g) j (by rw [← map_pow, hg, map_one])`. Introduce `k g hag hbg`.

Establish `hS : IsClosed (Set.range fun z : A => z ^ l ^ k)` using `(isCompact_range (continuous_pow (l ^ k))).isClosed`. Establish `hmem : g ∈ closure (Set.range fun z : A => z ^ l ^ k)`. Rewrite using `[mem_closure_iff_nhds]`. Introduce `U hU`. Establish `hF : Continuous fun h : A => h * (b h)⁻¹` using `continuous_id.mul hb_cont.inv`.

Establish `hFU : (fun h : A => h * (b h)⁻¹) ⁻¹' U ∈ 𝓝 g` using `hF.continuousAt.preimage_mem_nhds (by simpa [hbg] using hU)`. Establish `hpos : (0 : ℝ) < (l : ℝ) ^ (-k : ℤ)`. Establish `: (0 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).pos`. Check the signs of the components of the expression. Establish `hB : (fun h => (a h).toAdd) ⁻¹' Metric.closedBall 0 ((l : ℝ) ^ (-k : ℤ)) ∈ 𝓝 g` using `(continuous_toAdd.comp ha_cont).continuousAt.preimage_mem_nhds (by`.

Simplify using `only [Function.comp_apply, hag, toAdd_one]`. Conclude with `Metric.closedBall_mem_nhds _ hpos)`. Take `⟨_, ⟨x, rfl⟩, hx1, hx2⟩` from `hr.inter_nhds_nonempty (Filter.inter_mem hFU hB)`. Establish `hx2' : ‖(φ x).toAdd‖ ≤ (l : ℝ) ^ (-k : ℤ)`. Use `hx2` as an intermediate fact.

Simplify using `only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, ha] at this`. Conclude with `this`. Take `⟨y, hy⟩` from `(ball_pow l d k _).mp hx2'`. Establish `hβ' : β (x * (β x)⁻¹) = 1`. Rewrite using `[map_mul, map_inv, hββ, mul_inv_cancel]`.

Establish `hφ' : (φ (x * (β x)⁻¹)).toAdd = l ^ k • y`. Establish `h1 : φ (β x) = 1` using `tf _ e (by rw [← map_pow, hβe, map_one])`. Rewrite using `[map_mul, map_inv, h1, inv_one, mul_one, hy]`. Take `⟨z, hz⟩` from `hpow k _ ⟨y, hφ'⟩ hβ'`. Use `⟨r (x * (β x)⁻¹), ?_, r z, ?_⟩` and prove the remaining obligations.

Establish `h3 : r (x * (β x)⁻¹) = r x * (b (r x))⁻¹`. Rewrite using `[hb, map_mul, map_inv, MonoidHom.comp_apply]`. Rewrite using `[h3]`. Conclude with `hx1`. Use `show r z ^ l ^ k = r (x * (β x)⁻¹)`.

Rewrite using `[hz, map_pow]`. Take `⟨z, hz⟩` from `hS.closure_eq ▸ hmem`. Conclude with `⟨z, hz.symm⟩`.
-/
private theorem core_ab (l d : ℕ) [Fact l.Prime] {A M : Type} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [T2Space A] [CommGroup M] (r : M →* A) (hr : DenseRange r)
    (φ : M →* Multiplicative ((Fin d → ℤ_[l]) × ℤ_[l])) (β : M →* M) (e : ℕ)
    (hβe : ∀ x, β x ^ l ^ e = 1) (hββ : ∀ x, β (β x) = β x)
    (hpow : ∀ (k : ℕ) x, (∃ y, (φ x).toAdd = l ^ k • y) → β x = 1 → ∃ z, x = z ^ l ^ k)
    (hopen : ∀ k : ℕ, ∃ V ∈ 𝓝 (1 : A), ∀ x, r x ∈ V → ∃ z, x = z ^ l ^ k) :
    ∃ (a : A →* Multiplicative ((Fin d → ℤ_[l]) × ℤ_[l])) (b : A →* A), Continuous a ∧ (∀ x, a (r x) = φ x) ∧
      IsOpen (b.ker : Set A) ∧ (∀ g, b g ^ l ^ e = 1) ∧ (∀ g, b (b g) = b g) ∧
      (∀ (j : ℕ) g, g ^ l ^ j = 1 → a g = 1) ∧
      ∀ (k : ℕ) g, a g = 1 → b g = 1 → ∃ z, g = z ^ l ^ k := by
  have tf : ∀ (p : Multiplicative ((Fin d → ℤ_[l]) × ℤ_[l])) (j : ℕ), p ^ (l ^ j) = 1 → p = 1 := by
    intro p j hp
    have h1 : (l ^ j : ℕ) • p.toAdd = 0 := by
      rw [← toAdd_pow, hp]
      rfl
    have hne : ((l : ℤ_[l]) ^ j) ≠ 0 :=
      pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l], Nat.cast_pow, smul_eq_zero] at h1
    exact toAdd_eq_zero.mp (h1.resolve_left hne)
  have h0 : Tendsto (fun x => (φ x).toAdd) (Filter.comap r (𝓝 1)) (𝓝 0) := by
    refine Metric.nhds_basis_closedBall.tendsto_right_iff.mpr fun ε hε => ?_
    obtain ⟨k, hk⟩ := exists_zpow_lt l hε
    obtain ⟨V, hV, hVx⟩ := hopen k
    filter_upwards [Filter.preimage_mem_comap hV] with x hx
    obtain ⟨z, rfl⟩ := hVx x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    refine ((ball_pow l d k _).mpr ⟨(φ z).toAdd, ?_⟩).trans hk.le
    rw [map_pow, toAdd_pow]
  have htend : Tendsto φ (Filter.comap r (𝓝 1)) (𝓝 1) :=
    (continuous_ofAdd.tendsto _).comp h0
  obtain ⟨a, ha_cont, ha⟩ := ext_hom r hr φ htend
  letI : UniformSpace A := IsTopologicalGroup.rightUniformSpace A
  haveI : IsUniformGroup A := isUniformGroup_of_commGroup
  haveI : CompleteSpace A := complete_of_compact
  have htend2 : Tendsto (r.comp β) (Filter.comap r (𝓝 1)) (𝓝 1) := by
    obtain ⟨V, hV, hVx⟩ := hopen e
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.preimage_mem_comap hV] with x hx
    obtain ⟨z, rfl⟩ := hVx x hx
    rw [MonoidHom.comp_apply, map_pow, hβe, map_one]
  obtain ⟨b, hb_cont, hb⟩ := ext_hom r hr (r.comp β) htend2
  have hker : (b.ker : Set A) ∈ 𝓝 1 := by
    obtain ⟨V, hV, hVx⟩ := hopen e
    have hsub : interior V ⊆ {h | b h = 1} := by
      refine (hr.open_subset_closure_inter isOpen_interior).trans
        (closure_minimal ?_ (isClosed_eq hb_cont continuous_const))
      rintro _ ⟨hxV, x, rfl⟩
      obtain ⟨z, rfl⟩ := hVx _ (interior_subset hxV)
      show b (r _) = 1
      rw [hb, MonoidHom.comp_apply, map_pow, hβe, map_one]
    exact Filter.mem_of_superset (interior_mem_nhds.mpr hV)
      (fun h hh => MonoidHom.mem_ker.mpr (hsub hh))
  refine ⟨a, b, ha_cont, ha, Subgroup.isOpen_of_mem_nhds _ hker, ?_, ?_, ?_, ?_⟩
  · intro g
    have heq := hr.equalizer (hb_cont.pow (l ^ e)) (continuous_const (y := (1 : A)))
      (funext fun x => by
        show b (r x) ^ l ^ e = 1
        rw [hb, MonoidHom.comp_apply, ← map_pow, hβe, map_one])
    exact congrFun heq g
  · intro g
    have heq := hr.equalizer (hb_cont.comp hb_cont) hb_cont
      (funext fun x => by
        show b (b (r x)) = b (r x)
        simp only [hb, MonoidHom.comp_apply, hββ])
    exact congrFun heq g
  · intro j g hg
    exact tf (a g) j (by rw [← map_pow, hg, map_one])
  · intro k g hag hbg
    have hS : IsClosed (Set.range fun z : A => z ^ l ^ k) :=
      (isCompact_range (continuous_pow (l ^ k))).isClosed
    have hmem : g ∈ closure (Set.range fun z : A => z ^ l ^ k) := by
      rw [mem_closure_iff_nhds]
      intro U hU
      have hF : Continuous fun h : A => h * (b h)⁻¹ := continuous_id.mul hb_cont.inv
      have hFU : (fun h : A => h * (b h)⁻¹) ⁻¹' U ∈ 𝓝 g :=
        hF.continuousAt.preimage_mem_nhds (by simpa [hbg] using hU)
      have hpos : (0 : ℝ) < (l : ℝ) ^ (-k : ℤ) := by
        have : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
        positivity
      have hB : (fun h => (a h).toAdd) ⁻¹' Metric.closedBall 0 ((l : ℝ) ^ (-k : ℤ)) ∈ 𝓝 g :=
        (continuous_toAdd.comp ha_cont).continuousAt.preimage_mem_nhds (by
          simp only [Function.comp_apply, hag, toAdd_one]
          exact Metric.closedBall_mem_nhds _ hpos)
      obtain ⟨_, ⟨x, rfl⟩, hx1, hx2⟩ := hr.inter_nhds_nonempty (Filter.inter_mem hFU hB)
      have hx2' : ‖(φ x).toAdd‖ ≤ (l : ℝ) ^ (-k : ℤ) := by
        have := hx2
        simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, ha] at this
        exact this
      obtain ⟨y, hy⟩ := (ball_pow l d k _).mp hx2'
      have hβ' : β (x * (β x)⁻¹) = 1 := by
        rw [map_mul, map_inv, hββ, mul_inv_cancel]
      have hφ' : (φ (x * (β x)⁻¹)).toAdd = l ^ k • y := by
        have h1 : φ (β x) = 1 := tf _ e (by rw [← map_pow, hβe, map_one])
        rw [map_mul, map_inv, h1, inv_one, mul_one, hy]
      obtain ⟨z, hz⟩ := hpow k _ ⟨y, hφ'⟩ hβ'
      refine ⟨r (x * (β x)⁻¹), ?_, r z, ?_⟩
      · have h3 : r (x * (β x)⁻¹) = r x * (b (r x))⁻¹ := by
          rw [hb, map_mul, map_inv, MonoidHom.comp_apply]
        rw [h3]
        exact hx1
      · show r z ^ l ^ k = r (x * (β x)⁻¹)
        rw [hz, map_pow]
    obtain ⟨z, hz⟩ := hS.closure_eq ▸ hmem
    exact ⟨z, hz.symm⟩

open UpperTheory.V.W in
/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Use `haveI : IsClosed ((commutator G).topologicalClosure : Set G) := Subgroup.isClosed_topologicalClosure _`. Take `⟨a, b, ha, har, hbo, hbe, hbb, hator, hdiv⟩` from `core_ab l d r hr φ β e hβe hββ hpow hopen`. Set `q : G →* TopologicalAbelianization G` to `QuotientGroup.mk' (commutator G).topologicalClosure`. Establish `hq : Continuous q` using `continuous_quot_mk`.

Establish `hqs : Function.Surjective q` using `QuotientGroup.mk'_surjective _`. Establish `hfix : ∀ t : TopologicalAbelianization G, (∃ j : ℕ, t ^ l ^ j = 1) → b t = t`. Introduce and unpack `t ⟨j, hj⟩`. Use `set t' := t * (b t)⁻¹ with ht'`. Establish `hb' : b t' = 1` using `by simp [ht', hbb]`.

Establish `htor : t' ^ l ^ (j + e) = 1`. Rewrite using `[ht', mul_pow, inv_pow, pow_add, pow_mul, hj, one_pow, one_mul, mul_comm (l ^ j), pow_mul, hbe, one_pow, inv_one]`. Establish `ha' : a t' = 1` using `hator _ _ htor`. Assume the negation of the conclusion as `hne`. Establish `hne' : t' ≠ 1`.

Introduce `h`. Apply `hne` to reduce the goal to its premises. Rewrite `h` using `[ht', mul_inv_eq_one]`. Conclude with `h.symm`. Take `⟨V, hVo, hV⟩` from `sep_open t' hne'`.

Use `haveI : Finite (TopologicalAbelianization G ⧸ V) := Subgroup.quotient_finite_of_isOpen V hVo`. Use `haveI : V.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient`. Take `⟨s, m, hlm, hn⟩` from `Nat.exists_eq_pow_mul_and_not_dvd V.index_ne_zero_of_finite l hp.ne_one`. Take `⟨z, hz⟩` from `hdiv s t' ha' hb'`. Establish `h1 : t' ^ m ∈ V`.

Rewrite using `[hz, ← pow_mul, ← hn]`. Conclude with `V.pow_index_mem z`. Establish `h2 : t' ^ (l ^ (j + e)) ∈ V`. Rewrite using `[htor]`. Conclude with `V.one_mem`.

Establish `hcop : Nat.Coprime m (l ^ (j + e))` using `Nat.Coprime.symm (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hlm))`. Establish `key : t' = (t' ^ m) ^ (Nat.gcdA m (l ^ (j + e))) * (t' ^ (l ^ (j + e))) ^ (Nat.gcdB m (l ^ (j + e)))`. Rewrite using `[← zpow_natCast t' m, ← zpow_natCast t' (l ^ (j + e)), ← zpow_mul, ← zpow_mul, ← zpow_add, ← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one hcop, Nat.cast_one, zpow_one]`. Apply `hV` to reduce the goal to its premises. Rewrite using `[key]`.

Conclude with `V.mul_mem (V.zpow_mem h1 _) (V.zpow_mem h2 _)`. Establish `hbmem : ∀ g, (b.comp q) g ∈ CommGroup.primaryComponent (TopologicalAbelianization G) l` using `fun g => CommMonoid.mem_primaryComponent.mpr ⟨e, hbe _⟩`. Establish `hcl : IsClosed (a.range : Set (Multiplicative ((Fin d → ℤ_[l]) × ℤ_[l])))`. Rewrite using `[MonoidHom.coe_range]`. Conclude with `(isCompact_range ha).isClosed`.

Establish `hy0 : ∀ y, Multiplicative.ofAdd (y, (0 : ℤ_[l])) ∈ a.range`. Introduce `y`. Take `⟨x, hox, hx1⟩` from `hφs y`. Establish `hx : (φ x).toAdd = (y, 0)` using `Prod.ext hx1 (by simp [hφo x, hox])`. Conclude with `⟨r x, by rw [har, ← hx]; rfl⟩`.

Establish `h01 : Multiplicative.ofAdd ((0 : Fin d → ℤ_[l]), (1 : ℤ_[l])) ∈ a.range`. Establish `hπ2 : (φ π).toAdd.2 = 1` using `by simp [hφo π, hπ]`. Establish `hmem : φ π ∈ a.range` using `⟨r π, har π⟩`. Establish `heq : Multiplicative.ofAdd ((0 : Fin d → ℤ_[l]), (1 : ℤ_[l])) = φ π * (Multiplicative.ofAdd ((φ π).toAdd.1, (0 : ℤ_[l])))⁻¹`. Apply `Multiplicative.toAdd.injective` to reduce the goal to its premises.

Simplify using `only [toAdd_ofAdd, toAdd_mul, toAdd_inv]`. Use `ext`. Simplify using the standard rewrite rules. Simplify using `[hπ2]`. Rewrite using `[heq]`.

Conclude with `a.range.mul_mem hmem (a.range.inv_mem (hy0 _))`. Establish `hn : ∀ n : ℤ, Multiplicative.ofAdd ((0 : Fin d → ℤ_[l]), (n : ℤ_[l])) ∈ a.range`. Introduce `n`. Establish `: Multiplicative.ofAdd ((0 : Fin d → ℤ_[l]), (n : ℤ_[l])) = (Multiplicative.ofAdd ((0 : Fin d → ℤ_[l]), (1 : ℤ_[l]))) ^ n`. Rewrite using `[← ofAdd_zsmul]`.

Use `congr 1`. Apply the tactic sequence `ext <;> simp`. Rewrite using `[this]`. Conclude with `a.range.zpow_mem h01 n`. Establish `ht : ∀ t : ℤ_[l], Multiplicative.ofAdd ((0 : Fin d → ℤ_[l]), t) ∈ a.range`.

Introduce `t`. Use `PadicInt.denseRange_intCast.induction_on t ?_ hn` and prove the remaining obligations. Conclude with `hcl.preimage (continuous_ofAdd.comp (continuous_const.prodMk continuous_id))`. Establish `hsurj : Function.Surjective (a.comp q)`. Introduce `w`.

Establish `hw : w = Multiplicative.ofAdd ((Multiplicative.toAdd w).1, (0 : ℤ_[l])) * Multiplicative.ofAdd ((0 : Fin d → ℤ_[l]), (Multiplicative.toAdd w).2)`. Apply `Multiplicative.toAdd.injective` to reduce the goal to its premises. Simplify using the standard rewrite rules. Establish `: w ∈ a.range`. Rewrite using `[hw]`.

Conclude with `a.range.mul_mem (hy0 _) (ht _)`. Take `⟨h, hh⟩` from `this`. Take `⟨g, rfl⟩` from `hqs h`. Conclude with `⟨g, hh⟩`. Establish `hinert : ∀ x : (Fin d → ℤ_[l]) × ℤ_[l], (∃ g ∈ I, (a.comp q) g = Multiplicative.ofAdd x) ↔ x.2 = 0`.

Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hgI, hga⟩`. Establish `hk : ∀ k : ℕ, ‖x.2‖ ≤ (l : ℝ) ^ (-k : ℤ)`. Introduce `k`.

Take `⟨U, hUo, hIU, hUdiv⟩` from `hI2 k`. Set `f2 : TopologicalAbelianization G → ℤ_[l]` to `fun w => (Multiplicative.toAdd (a w)).2`. Establish `hf2 : Continuous f2` using `continuous_snd.comp (continuous_toAdd.comp ha)`. Set `O : Set (TopologicalAbelianization G)` to `(QuotientGroup.mk '' U) ∩ f2 ⁻¹' Metric.ball x.2 ((l : ℝ) ^ (-k : ℤ))`. Establish `hOo : IsOpen O` using `(QuotientGroup.isOpenMap_coe U hUo).inter (hf2.isOpen_preimage _ Metric.isOpen_ball)`.

Establish `hpos : (0 : ℝ) < (l : ℝ) ^ (-k : ℤ)` using `zpow_pos (by exact_mod_cast hp.pos) _`. Establish `hgO : q g ∈ O`. Use `⟨⟨g, hIU hgI, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `: f2 (q g) = x.2`. Simplify using `only [f2]`.

Establish `h' : a (q g) = Multiplicative.ofAdd x` using `hga`. Rewrite using `[h']`. Both sides reduce to the same expression. Use `show f2 (q g) ∈ Metric.ball x.2 _`. Rewrite using `[this]`.

Conclude with `Metric.mem_ball_self hpos`. Take `⟨m, hm⟩` from `hr.exists_mem_open hOo ⟨_, hgO⟩`. Take `⟨⟨g', hg'U, hg'eq⟩, hball⟩` from `hm`. Take `⟨c, hc⟩` from `hUdiv g' hg'U m hg'eq`. Establish `hf2m : f2 (r m) = (((o m).toAdd : ℤ) : ℤ_[l])`.

Simplify using `only [f2]`. Rewrite using `[har]`. Conclude with `hφo m`. Establish `hnm : ‖(((o m).toAdd : ℤ) : ℤ_[l])‖ ≤ (l : ℝ) ^ (-k : ℤ)`. Rewrite using `[hc]`.

Use `push_cast`. Rewrite using `[norm_mul, norm_pow, PadicInt.norm_p, zpow_neg, zpow_natCast, ← inv_pow]`. Conclude with `mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one _)`. Establish `hb : ‖f2 (r m) - x.2‖ < (l : ℝ) ^ (-k : ℤ)`. Use `hball` as an intermediate fact.

Simplify `this` using `[Metric.mem_ball, dist_eq_norm]`. Rewrite `hb` using `[hf2m]`. Establish `hsplit : x.2 = -((((o m).toAdd : ℤ) : ℤ_[l]) - x.2) + (((o m).toAdd : ℤ) : ℤ_[l])` using `by ring`. Rewrite using `[hsplit]`. Use `(PadicInt.nonarchimedean _ _).trans (max_le ?_ hnm)` and prove the remaining obligations.

Rewrite using `[norm_neg]`. Conclude with `hb.le`. Assume the negation of the conclusion as `hne`. Take `⟨k, hk'⟩` from `exists_zpow_lt l (norm_pos_iff.mpr hne)`. Conclude with `absurd (hk k) (not_le.mpr hk')`.

Introduce `hx2`. Take `⟨m, hom, hm1⟩` from `hφs x.1`. Take `⟨g, hgI, hgm⟩` from `hI1 m hom`. Use `⟨g, hgI, ?_⟩` and prove the remaining obligations. Establish `h1 : (a.comp q) g = φ m` using `by show a (q g) = φ m`.

Rewrite using `[← har]`. Use `congr 1`. Rewrite using `[h1]`. Apply `Multiplicative.toAdd.injective` to reduce the goal to its premises. Use `Prod.ext ?_ ?_` and prove the remaining obligations.

Conclude with `hm1`. Simplify using `[hφo m, hom, hx2]`. Establish `huniv : ∀ (C : Type) [CommGroup C] [Finite C], IsPGroup l C → ∀ (χ : G →* C), IsOpen (χ.ker : Set G) → muG l G ≤ χ.ker → (a.comp q).ker ≤ χ.ker`. Introduce `C _ _ hC χ hχo hμ g hg`. Rewrite `hg`, the goal using `[MonoidHom.mem_ker]`.

Establish `hkcl : IsClosed (χ.ker : Set G)` using `Subgroup.isClosed_of_isOpen _ hχo`. Establish `hN : (commutator G).topologicalClosure ≤ χ.ker` using `Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker χ) hkcl`. Set `χb` to `QuotientGroup.lift _ χ hN`. Establish `hχb : ∀ x, χb (q x) = χ x` using `fun x => rfl`. Take `⟨n, hn⟩` from `IsPGroup.exists_card_eq hC`.

Take `⟨g', hg'⟩` from `hqs (b (q g))`. Establish `hg'mu : g' ∈ muG l G` using `by show q g' ∈ CommGroup.primaryComponent (TopologicalAbelianization G) l`. Rewrite using `[hg']`. Conclude with `CommMonoid.mem_primaryComponent.mpr ⟨e, hbe _⟩`. Establish `hχt : χb (b (q g)) = 1`.

Rewrite using `[← hg', hχb]`. Conclude with `hμ hg'mu`. Establish `h' : a (q g * (b (q g))⁻¹) = 1`. Rewrite using `[map_mul, map_inv, show a (q g) = 1 from hg, hator e _ (hbe _), inv_one, one_mul]`. Establish `hb' : b (q g * (b (q g))⁻¹) = 1` using `by simp [hbb]`.

Take `⟨z, hz⟩` from `hdiv n _ h' hb'`. Establish `h1 : χb (q g * (b (q g))⁻¹) = 1`. Rewrite using `[hz, map_pow, ← hn, pow_card_eq_one']`. Rewrite using `[← hχb]`. Establish `: q g = q g * (b (q g))⁻¹ * b (q g)` using `by group`.

Rewrite using `[this, map_mul, h1, hχt, one_mul]`. Conclude with `⟨{ a := a.comp q cont := ha.comp hq surj := hsurj inertia := hinert univ := huniv b := (b.comp q).codRestrict _ hbmem b_open := by`. Rewrite using `[MonoidHom.ker_codRestrict, ← MonoidHom.comap_ker]`. Conclude with `hbo.preimage hq`. Use `b_mu := by`.

Introduce `g hg`. Take `⟨j, hj⟩` from `CommMonoid.mem_primaryComponent.mp hg`. Conclude with `hfix _ ⟨j, hj⟩ }⟩`.
-/
private theorem core (l d : ℕ) [Fact l.Prime] {G M : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (I : Subgroup G) [CommGroup M]
    (r : M →* TopologicalAbelianization G) (hr : DenseRange r) (o : M →* Multiplicative ℤ) (π : M)
    (hπ : o π = Multiplicative.ofAdd 1)
    (φ : M →* Multiplicative ((Fin d → ℤ_[l]) × ℤ_[l])) (β : M →* M) (e : ℕ)
    (hφo : ∀ x, (φ x).toAdd.2 = ((o x).toAdd : ℤ)) (hφs : ∀ y, ∃ x, o x = 1 ∧ (φ x).toAdd.1 = y)
    (hβe : ∀ x, β x ^ l ^ e = 1) (hββ : ∀ x, β (β x) = β x)
    (hpow : ∀ (k : ℕ) x, (∃ y, (φ x).toAdd = l ^ k • y) → β x = 1 → ∃ z, x = z ^ l ^ k)
    (hopen : ∀ k : ℕ, ∃ V ∈ 𝓝 (1 : TopologicalAbelianization G), ∀ x, r x ∈ V → ∃ z, x = z ^ l ^ k)
    (hI1 : ∀ x, o x = 1 → ∃ g ∈ I, (g : TopologicalAbelianization G) = r x)
    (hI2 : ∀ k : ℕ, ∃ U : Set G, IsOpen U ∧ (I : Set G) ⊆ U ∧
      ∀ g ∈ U, ∀ x, (g : TopologicalAbelianization G) = r x → (l : ℤ) ^ k ∣ (o x).toAdd) :
    Nonempty (LocAb l G I d) := by
  classical
  have hp : l.Prime := Fact.out
  haveI : IsClosed ((commutator G).topologicalClosure : Set G) :=
    Subgroup.isClosed_topologicalClosure _
  obtain ⟨a, b, ha, har, hbo, hbe, hbb, hator, hdiv⟩ :=
    core_ab l d r hr φ β e hβe hββ hpow hopen
  let q : G →* TopologicalAbelianization G := QuotientGroup.mk' (commutator G).topologicalClosure
  have hq : Continuous q := continuous_quot_mk
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hfix : ∀ t : TopologicalAbelianization G, (∃ j : ℕ, t ^ l ^ j = 1) → b t = t := by
    rintro t ⟨j, hj⟩
    set t' := t * (b t)⁻¹ with ht'
    have hb' : b t' = 1 := by simp [ht', hbb]
    have htor : t' ^ l ^ (j + e) = 1 := by
      rw [ht', mul_pow, inv_pow, pow_add, pow_mul, hj, one_pow, one_mul, mul_comm (l ^ j), pow_mul,
        hbe, one_pow, inv_one]
    have ha' : a t' = 1 := hator _ _ htor
    by_contra hne
    have hne' : t' ≠ 1 := by
      intro h
      apply hne
      rw [ht', mul_inv_eq_one] at h
      exact h.symm
    obtain ⟨V, hVo, hV⟩ := sep_open t' hne'
    haveI : Finite (TopologicalAbelianization G ⧸ V) := Subgroup.quotient_finite_of_isOpen V hVo
    haveI : V.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    obtain ⟨s, m, hlm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd V.index_ne_zero_of_finite l hp.ne_one
    obtain ⟨z, hz⟩ := hdiv s t' ha' hb'
    have h1 : t' ^ m ∈ V := by
      rw [hz, ← pow_mul, ← hn]
      exact V.pow_index_mem z
    have h2 : t' ^ (l ^ (j + e)) ∈ V := by
      rw [htor]
      exact V.one_mem
    have hcop : Nat.Coprime m (l ^ (j + e)) :=
      Nat.Coprime.symm (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hlm))
    have key : t' = (t' ^ m) ^ (Nat.gcdA m (l ^ (j + e))) *
        (t' ^ (l ^ (j + e))) ^ (Nat.gcdB m (l ^ (j + e))) := by
      rw [← zpow_natCast t' m, ← zpow_natCast t' (l ^ (j + e)), ← zpow_mul, ← zpow_mul, ← zpow_add,
        ← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one hcop, Nat.cast_one, zpow_one]
    apply hV
    rw [key]
    exact V.mul_mem (V.zpow_mem h1 _) (V.zpow_mem h2 _)
  have hbmem : ∀ g, (b.comp q) g ∈ CommGroup.primaryComponent (TopologicalAbelianization G) l :=
    fun g => CommMonoid.mem_primaryComponent.mpr ⟨e, hbe _⟩
  have hcl : IsClosed (a.range : Set (Multiplicative ((Fin d → ℤ_[l]) × ℤ_[l]))) := by
    rw [MonoidHom.coe_range]
    exact (isCompact_range ha).isClosed
  have hy0 : ∀ y, Multiplicative.ofAdd (y, (0 : ℤ_[l])) ∈ a.range := by
    intro y
    obtain ⟨x, hox, hx1⟩ := hφs y
    have hx : (φ x).toAdd = (y, 0) := Prod.ext hx1 (by simp [hφo x, hox])
    exact ⟨r x, by rw [har, ← hx]; rfl⟩
  have h01 : Multiplicative.ofAdd ((0 : Fin d → ℤ_[l]), (1 : ℤ_[l])) ∈ a.range := by
    have hπ2 : (φ π).toAdd.2 = 1 := by simp [hφo π, hπ]
    have hmem : φ π ∈ a.range := ⟨r π, har π⟩
    have heq : Multiplicative.ofAdd ((0 : Fin d → ℤ_[l]), (1 : ℤ_[l])) =
        φ π * (Multiplicative.ofAdd ((φ π).toAdd.1, (0 : ℤ_[l])))⁻¹ := by
      apply Multiplicative.toAdd.injective
      simp only [toAdd_ofAdd, toAdd_mul, toAdd_inv]
      ext
      · simp
      · simp [hπ2]
    rw [heq]
    exact a.range.mul_mem hmem (a.range.inv_mem (hy0 _))
  have hn : ∀ n : ℤ, Multiplicative.ofAdd ((0 : Fin d → ℤ_[l]), (n : ℤ_[l])) ∈ a.range := by
    intro n
    have : Multiplicative.ofAdd ((0 : Fin d → ℤ_[l]), (n : ℤ_[l])) =
        (Multiplicative.ofAdd ((0 : Fin d → ℤ_[l]), (1 : ℤ_[l]))) ^ n := by
      rw [← ofAdd_zsmul]
      congr 1
      ext <;> simp
    rw [this]
    exact a.range.zpow_mem h01 n
  have ht : ∀ t : ℤ_[l], Multiplicative.ofAdd ((0 : Fin d → ℤ_[l]), t) ∈ a.range := by
    intro t
    refine PadicInt.denseRange_intCast.induction_on t ?_ hn
    exact hcl.preimage (continuous_ofAdd.comp (continuous_const.prodMk continuous_id))
  have hsurj : Function.Surjective (a.comp q) := by
    intro w
    have hw : w = Multiplicative.ofAdd ((Multiplicative.toAdd w).1, (0 : ℤ_[l])) *
        Multiplicative.ofAdd ((0 : Fin d → ℤ_[l]), (Multiplicative.toAdd w).2) := by
      apply Multiplicative.toAdd.injective
      simp
    have : w ∈ a.range := by
      rw [hw]
      exact a.range.mul_mem (hy0 _) (ht _)
    obtain ⟨h, hh⟩ := this
    obtain ⟨g, rfl⟩ := hqs h
    exact ⟨g, hh⟩
  have hinert : ∀ x : (Fin d → ℤ_[l]) × ℤ_[l],
      (∃ g ∈ I, (a.comp q) g = Multiplicative.ofAdd x) ↔ x.2 = 0 := by
    intro x
    constructor
    · rintro ⟨g, hgI, hga⟩
      have hk : ∀ k : ℕ, ‖x.2‖ ≤ (l : ℝ) ^ (-k : ℤ) := by
        intro k
        obtain ⟨U, hUo, hIU, hUdiv⟩ := hI2 k
        let f2 : TopologicalAbelianization G → ℤ_[l] := fun w => (Multiplicative.toAdd (a w)).2
        have hf2 : Continuous f2 := continuous_snd.comp (continuous_toAdd.comp ha)
        let O : Set (TopologicalAbelianization G) :=
          (QuotientGroup.mk '' U) ∩ f2 ⁻¹' Metric.ball x.2 ((l : ℝ) ^ (-k : ℤ))
        have hOo : IsOpen O :=
          (QuotientGroup.isOpenMap_coe U hUo).inter (hf2.isOpen_preimage _ Metric.isOpen_ball)
        have hpos : (0 : ℝ) < (l : ℝ) ^ (-k : ℤ) := zpow_pos (by exact_mod_cast hp.pos) _
        have hgO : q g ∈ O := by
          refine ⟨⟨g, hIU hgI, rfl⟩, ?_⟩
          have : f2 (q g) = x.2 := by
            simp only [f2]
            have h' : a (q g) = Multiplicative.ofAdd x := hga
            rw [h']
            rfl
          show f2 (q g) ∈ Metric.ball x.2 _
          rw [this]
          exact Metric.mem_ball_self hpos
        obtain ⟨m, hm⟩ := hr.exists_mem_open hOo ⟨_, hgO⟩
        obtain ⟨⟨g', hg'U, hg'eq⟩, hball⟩ := hm
        obtain ⟨c, hc⟩ := hUdiv g' hg'U m hg'eq
        have hf2m : f2 (r m) = (((o m).toAdd : ℤ) : ℤ_[l]) := by
          simp only [f2]
          rw [har]
          exact hφo m
        have hnm : ‖(((o m).toAdd : ℤ) : ℤ_[l])‖ ≤ (l : ℝ) ^ (-k : ℤ) := by
          rw [hc]
          push_cast
          rw [norm_mul, norm_pow, PadicInt.norm_p, zpow_neg, zpow_natCast, ← inv_pow]
          exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one _)
        have hb : ‖f2 (r m) - x.2‖ < (l : ℝ) ^ (-k : ℤ) := by
          have := hball
          simpa [Metric.mem_ball, dist_eq_norm] using this
        rw [hf2m] at hb
        have hsplit : x.2 = -((((o m).toAdd : ℤ) : ℤ_[l]) - x.2) + (((o m).toAdd : ℤ) : ℤ_[l]) := by ring
        rw [hsplit]
        refine (PadicInt.nonarchimedean _ _).trans (max_le ?_ hnm)
        rw [norm_neg]
        exact hb.le
      by_contra hne
      obtain ⟨k, hk'⟩ := exists_zpow_lt l (norm_pos_iff.mpr hne)
      exact absurd (hk k) (not_le.mpr hk')
    · intro hx2
      obtain ⟨m, hom, hm1⟩ := hφs x.1
      obtain ⟨g, hgI, hgm⟩ := hI1 m hom
      refine ⟨g, hgI, ?_⟩
      have h1 : (a.comp q) g = φ m := by
        show a (q g) = φ m
        rw [← har]
        congr 1
      rw [h1]
      apply Multiplicative.toAdd.injective
      refine Prod.ext ?_ ?_
      · exact hm1
      · simp [hφo m, hom, hx2]
  have huniv : ∀ (C : Type) [CommGroup C] [Finite C], IsPGroup l C → ∀ (χ : G →* C),
      IsOpen (χ.ker : Set G) → muG l G ≤ χ.ker → (a.comp q).ker ≤ χ.ker := by
    intro C _ _ hC χ hχo hμ g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    have hkcl : IsClosed (χ.ker : Set G) := Subgroup.isClosed_of_isOpen _ hχo
    have hN : (commutator G).topologicalClosure ≤ χ.ker :=
      Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker χ) hkcl
    let χb := QuotientGroup.lift _ χ hN
    have hχb : ∀ x, χb (q x) = χ x := fun x => rfl
    obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq hC
    obtain ⟨g', hg'⟩ := hqs (b (q g))
    have hg'mu : g' ∈ muG l G := by
      show q g' ∈ CommGroup.primaryComponent (TopologicalAbelianization G) l
      rw [hg']
      exact CommMonoid.mem_primaryComponent.mpr ⟨e, hbe _⟩
    have hχt : χb (b (q g)) = 1 := by
      rw [← hg', hχb]
      exact hμ hg'mu
    have h' : a (q g * (b (q g))⁻¹) = 1 := by
      rw [map_mul, map_inv, show a (q g) = 1 from hg, hator e _ (hbe _), inv_one, one_mul]
    have hb' : b (q g * (b (q g))⁻¹) = 1 := by simp [hbb]
    obtain ⟨z, hz⟩ := hdiv n _ h' hb'
    have h1 : χb (q g * (b (q g))⁻¹) = 1 := by
      rw [hz, map_pow, ← hn, pow_card_eq_one']
    rw [← hχb]
    have : q g = q g * (b (q g))⁻¹ * b (q g) := by group
    rw [this, map_mul, h1, hχt, one_mul]
  exact ⟨{ a := a.comp q
           cont := ha.comp hq
           surj := hsurj
           inertia := hinert
           univ := huniv
           b := (b.comp q).codRestrict _ hbmem
           b_open := by
             rw [MonoidHom.ker_codRestrict, ← MonoidHom.comap_ker]
             exact hbo.preimage hq
           b_mu := by
             intro g hg
             obtain ⟨j, hj⟩ := CommMonoid.mem_primaryComponent.mp hg
             exact hfix _ ⟨j, hj⟩ }⟩

/- English proof (translation)
Establish `hle : (commutator G).topologicalClosure ≤ ((commutator G').topologicalClosure).comap f`. Apply `Subgroup.topologicalClosure_minimal` to reduce the goal to its premises. Rewrite using `[← Subgroup.map_le_iff_le_comap]`. Use `le_trans ?_ (Subgroup.le_topologicalClosure _)` and prove the remaining obligations. Rewrite using `[commutator_def, commutator_def, Subgroup.map_commutator]`.

Conclude with `Subgroup.commutator_mono le_top le_top`. Conclude with `(Subgroup.isClosed_topologicalClosure _).preimage hf`. Use `⟨QuotientGroup.map _ _ f hle, ?_, fun g => rfl⟩` and prove the remaining obligations. Apply `(QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr` to reduce the goal to its premises. Conclude with `continuous_quot_mk.comp hf`.
-/
private theorem ab_map {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] (f : G →* G') (hf : Continuous f) :
    ∃ F : TopologicalAbelianization G →* TopologicalAbelianization G', Continuous F ∧ ∀ g : G, F g = (f g : G') := by
  have hle : (commutator G).topologicalClosure ≤ ((commutator G').topologicalClosure).comap f := by
    apply Subgroup.topologicalClosure_minimal
    · rw [← Subgroup.map_le_iff_le_comap]
      refine le_trans ?_ (Subgroup.le_topologicalClosure _)
      rw [commutator_def, commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    · exact (Subgroup.isClosed_topologicalClosure _).preimage hf
  refine ⟨QuotientGroup.map _ _ f hle, ?_, fun g => rfl⟩
  apply (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
  exact continuous_quot_mk.comp hf

open UpperTheory.V.W GroundTheory.LocalField ValuativeRel GroundTheory.LocalField.Abstract in
/- English proof (translation)
Set `hom : G ≃ₜ (Ω ≃ₐ[K] Ω)` to `{ toEquiv := ε.toEquiv, continuous_toFun := hε, continuous_invFun := hε' }`. Use `haveI : CompactSpace G := hom.symm.compactSpace`. Use `haveI : TotallyDisconnectedSpace G := hom.symm.totallyDisconnectedSpace`. Take `⟨F, hFc, hF⟩` from `ab_map (ε.symm.toMonoidHom) hε'`. Take `⟨F', hF'c, hF'⟩` from `ab_map (ε.toMonoidHom) hε`.

Establish `hF'F : ∀ y, F' (F y) = y`. Introduce `y`. Take `⟨σ, rfl⟩` from `QuotientGroup.mk_surjective y`. Establish `h1` using `hF σ`. Establish `h2` using `hF' (ε.symm σ)`.

Simplify using `only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at h1 h2`. Rewrite using `[h1, h2]`. Establish `hFsurj : Function.Surjective F`. Introduce `y`. Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective y`.

Use `⟨QuotientGroup.mk (ε g), ?_⟩` and prove the remaining obligations. Establish `h1` using `hF (ε g)`. Simplify using `only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h1`. Conclude with `h1`. Set `r : Kˣ →* TopologicalAbelianization G` to `F.comp (localReciprocityLimit K Ω)`.

Establish `hr : DenseRange r` using `hFsurj.denseRange.comp denseRange_localReciprocityLimit hFc`. Set `o : Kˣ →* Multiplicative ℤ` to `{ toFun := fun x => Multiplicative.ofAdd (ord (x : K)) map_one' := by`. Use `ord_unit (K := K) 1` as an intermediate fact. Simplify using `using this`. Use the proof step `map_mul' := fun x y => by`.

Simplify using `only [Units.val_mul, ord_mul x.ne_zero y.ne_zero, ofAdd_add] }`. Establish `ho : ∀ x : Kˣ, o x = Multiplicative.ofAdd (ord (x : K))` using `fun _ => rfl`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible (ValuativeRel.valuation K).integer`. Establish `hπ : o (uniformizerUnit hϖ) = Multiplicative.ofAdd 1`. Rewrite using `[ho, uniformizerUnit, Units.val_mk0, ord_uniformizer hϖ]`.

Use `haveI : Module.Finite ℤ_[l] (Additive (unitFiltrationUnits K 1)) := finite_principalUnits l`. Establish `hunit : ∀ x : Kˣ, o x = 1 ↔ x ∈ (unitsIncl K).range`. Introduce `x`. Rewrite using `[mem_range_unitsIncl_iff, normalizedValuation_eq_exp_ord x.ne_zero, ho]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `h' : ord (x : K) = 0` using `by simpa using h`. Simplify using `[h']`. Introduce `h`. Establish `h' : ord (x : K) = 0` using `by simpa using h`.

Simplify using `[h']`. Establish `hU : ∀ u ∈ unitFiltrationUnits K 1, o u = 1`. Introduce `u hu`. Take `⟨v, -, rfl⟩` from `Subgroup.mem_map.mp hu`. Conclude with `(hunit _).mpr ⟨v, rfl⟩`.

Establish `hm : l.Coprime (Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) - 1)`. Establish `h0` using `natCast_card_residueField_sub_one_ne_zero K`. Use `(Nat.Prime.coprime_iff_not_dvd Fact.out).mpr fun hd => h0 ?_` and prove the remaining obligations. Conclude with `(CharP.cast_eq_zero_iff _ l _).mpr hd`. Establish `hmU : ∀ x : Kˣ, o x = 1 → x ^ (Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) - 1) ∈ unitFiltrationUnits K 1`.

Introduce `x hx`. Take `⟨v, rfl⟩` from `(hunit x).mp hx`. Establish `hv : v ^ (unitFiltration K 1).index ∈ unitFiltration K 1` using `Subgroup.pow_index_mem _ v`. Rewrite `hv` using `[index_unitFiltration_one]`. Conclude with `⟨_, hv, map_pow _ _ _⟩`.

Take `⟨φ, β, e, hφo, hφs, hβe, hββ, hpow⟩` from `units_pack l Kˣ o (uniformizerUnit hϖ) hπ (unitFiltrationUnits K 1) hU _ hm hmU`. Establish `hrx : ∀ x : Kˣ, F' (r x) = localReciprocityLimit K Ω x` using `fun x => hF'F _`. Establish `hopen : ∀ k : ℕ, ∃ V ∈ 𝓝 (1 : TopologicalAbelianization G), ∀ x, r x ∈ V → ∃ z, x = z ^ l ^ k`. Introduce `k`. Establish `hk : l ^ k ≠ 0` using `pow_ne_zero _ (Fact.out : l.Prime).ne_zero`.

Establish `hk0 : ((l ^ k : ℕ) : K) ≠ 0` using `Nat.cast_ne_zero.mpr hk`. Set `H : Subgroup Kˣ` to `(powMonoidHom (l ^ k)).range`. Establish `hHo : IsOpen (H : Set Kˣ)` using `isOpen_range_pow hk0`. Use `haveI : Finite (Kˣ ⧸ H) := finite_quotient_range_pow_of_charZero hk`. Establish `hHmem : H ∈ openFiniteIndex Kˣ` using `⟨hHo, Subgroup.finiteIndex_of_finite_quotient⟩`.

Use `haveI := openCompletion.discreteTopology_quotient (⟨H, hHmem⟩ : openFiniteIndex Kˣ)`. Set `Ψ : TopologicalAbelianization G →* Kˣ ⧸ H` to `(artinCoord K Ω ⟨H, hHmem⟩).comp ((topologicalAbelianizationEquiv K Ω).toMulEquiv.toMonoidHom.comp F')`. Establish `hΨc : Continuous Ψ` using `(continuous_artinCoord _).comp ((topologicalAbelianizationEquiv K Ω).continuous.comp hF'c)`. Establish `hΨr : ∀ x : Kˣ, Ψ (r x) = (x : Kˣ ⧸ H)`. Introduce `x`.

Establish `h1` using `artinCoord_localArtinMap (Ω := Ω) (⟨H, hHmem⟩ : openFiniteIndex Kˣ) x`. Rewrite `h1` using `[localArtinMap_apply]`. Simplify using `only [Ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hrx]`. Conclude with `h1`. Use `⟨Ψ ⁻¹' {1}, ((isOpen_discrete _).preimage hΨc).mem_nhds (by simp), ?_⟩` and prove the remaining obligations.

Introduce `x hx`. Establish `h1 : (x : Kˣ ⧸ H) = 1`. Rewrite using `[← hΨr]`. Conclude with `hx`. Take `⟨z, hz⟩` from `(QuotientGroup.eq_one_iff x).mp h1`.

Conclude with `⟨z, by rw [← hz]; rfl⟩`. Establish `hI1 : ∀ x, o x = 1 → ∃ g ∈ I, (g : TopologicalAbelianization G) = r x`. Introduce `x hx`. Take `⟨σ, hσ⟩` from `QuotientGroup.mk_surjective (localReciprocityLimit K Ω x)`. Use `⟨ε.symm σ, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hI, MulEquiv.apply_symm_apply, unramifiedDegree_of_mk_eq_localReciprocityLimit hσ]`. Establish `h' : ord (x : K) = 0` using `by simpa [ho] using hx`. Simplify using `[h']`. Establish `h1` using `hF σ`. Simplify using `only [MulEquiv.coe_toMonoidHom] at h1`.

Rewrite using `[← h1, hσ]`. Both sides reduce to the same expression. Establish `hI2 : ∀ k : ℕ, ∃ U : Set G, IsOpen U ∧ (I : Set G) ⊆ U ∧ ∀ g ∈ U, ∀ x, (g : TopologicalAbelianization G) = r x → (l : ℤ) ^ k ∣ (o x).toAdd`. Introduce `k`. Set `n : ℕ+` to `⟨l ^ k, pow_pos (Fact.out : l.Prime).pos _⟩`.

Use `⟨{g | unramifiedCoord K (ε g) n = 0}, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(isOpen_discrete ({0} : Set (ZMod n))).preimage ((continuous_unramifiedCoord (K := K) (Ω := Ω) n).comp hε)`. Introduce `g hg`. Establish `h1` using `(hI g).mp hg`. Use `show unramifiedCoord K (ε g) n = 0`.

Rewrite using `[← proj_toAdd_unramifiedDegree, h1]`. Simplify using the standard rewrite rules. Introduce `g hg x hgx`. Establish `hσ : ((ε g : Ω ≃ₐ[K] Ω) : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) = localReciprocityLimit K Ω x`. Establish `h1` using `hF' g`.

Simplify using `only [MulEquiv.coe_toMonoidHom] at h1`. Rewrite using `[← h1, hgx, hrx]`. Establish `h2` using `unramifiedDegree_of_mk_eq_localReciprocityLimit hσ`. Establish `h3 : unramifiedCoord K (ε g) n = 0` using `hg`. Rewrite `h3` using `[← proj_toAdd_unramifiedDegree, h2]`.

Simplify using `only [toAdd_ofAdd, map_intCast] at h3`. Establish `h4` using `(ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp h3`. Simplify `h4` using `[ho, n]`. Conclude with `core l _ I r hr o (uniformizerUnit hϖ) hπ φ β e hφo hφs hβe hββ hpow hopen hI1 hI2`.
-/
private theorem loc_field (l : ℕ) [Fact l.Prime] (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharP 𝓀[K] l] [CharZero K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (I : Subgroup G) (ε : G ≃* (Ω ≃ₐ[K] Ω))
    (hε : Continuous ε) (hε' : Continuous ε.symm) (hI : ∀ g, g ∈ I ↔ unramifiedDegree K Ω (ε g) = 1) :
    Nonempty (LocAb l G I (Module.finrank ℤ_[l] (Additive (unitFiltrationUnits K 1)))) := by
  classical
  let hom : G ≃ₜ (Ω ≃ₐ[K] Ω) :=
    { toEquiv := ε.toEquiv, continuous_toFun := hε, continuous_invFun := hε' }
  haveI : CompactSpace G := hom.symm.compactSpace
  haveI : TotallyDisconnectedSpace G := hom.symm.totallyDisconnectedSpace
  obtain ⟨F, hFc, hF⟩ := ab_map (ε.symm.toMonoidHom) hε'
  obtain ⟨F', hF'c, hF'⟩ := ab_map (ε.toMonoidHom) hε
  have hF'F : ∀ y, F' (F y) = y := by
    intro y
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective y
    have h1 := hF σ
    have h2 := hF' (ε.symm σ)
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at h1 h2
    rw [h1, h2]
  have hFsurj : Function.Surjective F := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    refine ⟨QuotientGroup.mk (ε g), ?_⟩
    have h1 := hF (ε g)
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h1
    exact h1
  let r : Kˣ →* TopologicalAbelianization G := F.comp (localReciprocityLimit K Ω)
  have hr : DenseRange r := hFsurj.denseRange.comp denseRange_localReciprocityLimit hFc
  let o : Kˣ →* Multiplicative ℤ :=
    { toFun := fun x => Multiplicative.ofAdd (ord (x : K))
      map_one' := by
        have := ord_unit (K := K) 1
        simpa using this
      map_mul' := fun x y => by
        simp only [Units.val_mul, ord_mul x.ne_zero y.ne_zero, ofAdd_add] }
  have ho : ∀ x : Kˣ, o x = Multiplicative.ofAdd (ord (x : K)) := fun _ => rfl
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (ValuativeRel.valuation K).integer
  have hπ : o (uniformizerUnit hϖ) = Multiplicative.ofAdd 1 := by
    rw [ho, uniformizerUnit, Units.val_mk0, ord_uniformizer hϖ]
  haveI : Module.Finite ℤ_[l] (Additive (unitFiltrationUnits K 1)) := finite_principalUnits l
  have hunit : ∀ x : Kˣ, o x = 1 ↔ x ∈ (unitsIncl K).range := by
    intro x
    rw [mem_range_unitsIncl_iff, normalizedValuation_eq_exp_ord x.ne_zero, ho]
    constructor
    · intro h
      have h' : ord (x : K) = 0 := by simpa using h
      simp [h']
    · intro h
      have h' : ord (x : K) = 0 := by simpa using h
      simp [h']
  have hU : ∀ u ∈ unitFiltrationUnits K 1, o u = 1 := by
    intro u hu
    obtain ⟨v, -, rfl⟩ := Subgroup.mem_map.mp hu
    exact (hunit _).mpr ⟨v, rfl⟩
  have hm : l.Coprime (Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) - 1) := by
    have h0 := natCast_card_residueField_sub_one_ne_zero K
    refine (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr fun hd => h0 ?_
    exact (CharP.cast_eq_zero_iff _ l _).mpr hd
  have hmU : ∀ x : Kˣ, o x = 1 →
      x ^ (Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) - 1) ∈
        unitFiltrationUnits K 1 := by
    intro x hx
    obtain ⟨v, rfl⟩ := (hunit x).mp hx
    have hv : v ^ (unitFiltration K 1).index ∈ unitFiltration K 1 := Subgroup.pow_index_mem _ v
    rw [index_unitFiltration_one] at hv
    exact ⟨_, hv, map_pow _ _ _⟩
  obtain ⟨φ, β, e, hφo, hφs, hβe, hββ, hpow⟩ :=
    units_pack l Kˣ o (uniformizerUnit hϖ) hπ (unitFiltrationUnits K 1) hU _ hm hmU
  have hrx : ∀ x : Kˣ, F' (r x) = localReciprocityLimit K Ω x := fun x => hF'F _
  have hopen : ∀ k : ℕ, ∃ V ∈ 𝓝 (1 : TopologicalAbelianization G), ∀ x, r x ∈ V → ∃ z, x = z ^ l ^ k := by
    intro k
    have hk : l ^ k ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
    have hk0 : ((l ^ k : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr hk
    let H : Subgroup Kˣ := (powMonoidHom (l ^ k)).range
    have hHo : IsOpen (H : Set Kˣ) := isOpen_range_pow hk0
    haveI : Finite (Kˣ ⧸ H) := finite_quotient_range_pow_of_charZero hk
    have hHmem : H ∈ openFiniteIndex Kˣ := ⟨hHo, Subgroup.finiteIndex_of_finite_quotient⟩
    haveI := openCompletion.discreteTopology_quotient (⟨H, hHmem⟩ : openFiniteIndex Kˣ)
    let Ψ : TopologicalAbelianization G →* Kˣ ⧸ H :=
      (artinCoord K Ω ⟨H, hHmem⟩).comp
        ((topologicalAbelianizationEquiv K Ω).toMulEquiv.toMonoidHom.comp F')
    have hΨc : Continuous Ψ :=
      (continuous_artinCoord _).comp ((topologicalAbelianizationEquiv K Ω).continuous.comp hF'c)
    have hΨr : ∀ x : Kˣ, Ψ (r x) = (x : Kˣ ⧸ H) := by
      intro x
      have h1 := artinCoord_localArtinMap (Ω := Ω) (⟨H, hHmem⟩ : openFiniteIndex Kˣ) x
      rw [localArtinMap_apply] at h1
      simp only [Ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hrx]
      exact h1
    refine ⟨Ψ ⁻¹' {1}, ((isOpen_discrete _).preimage hΨc).mem_nhds (by simp), ?_⟩
    intro x hx
    have h1 : (x : Kˣ ⧸ H) = 1 := by
      rw [← hΨr]
      exact hx
    obtain ⟨z, hz⟩ := (QuotientGroup.eq_one_iff x).mp h1
    exact ⟨z, by rw [← hz]; rfl⟩
  have hI1 : ∀ x, o x = 1 → ∃ g ∈ I, (g : TopologicalAbelianization G) = r x := by
    intro x hx
    obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (localReciprocityLimit K Ω x)
    refine ⟨ε.symm σ, ?_, ?_⟩
    · rw [hI, MulEquiv.apply_symm_apply,
        unramifiedDegree_of_mk_eq_localReciprocityLimit hσ]
      have h' : ord (x : K) = 0 := by simpa [ho] using hx
      simp [h']
    · have h1 := hF σ
      simp only [MulEquiv.coe_toMonoidHom] at h1
      rw [← h1, hσ]
      rfl
  have hI2 : ∀ k : ℕ, ∃ U : Set G, IsOpen U ∧ (I : Set G) ⊆ U ∧
      ∀ g ∈ U, ∀ x, (g : TopologicalAbelianization G) = r x → (l : ℤ) ^ k ∣ (o x).toAdd := by
    intro k
    let n : ℕ+ := ⟨l ^ k, pow_pos (Fact.out : l.Prime).pos _⟩
    refine ⟨{g | unramifiedCoord K (ε g) n = 0}, ?_, ?_, ?_⟩
    · exact (isOpen_discrete ({0} : Set (ZMod n))).preimage
        ((continuous_unramifiedCoord (K := K) (Ω := Ω) n).comp hε)
    · intro g hg
      have h1 := (hI g).mp hg
      show unramifiedCoord K (ε g) n = 0
      rw [← proj_toAdd_unramifiedDegree, h1]
      simp
    · intro g hg x hgx
      have hσ : ((ε g : Ω ≃ₐ[K] Ω) : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) =
          localReciprocityLimit K Ω x := by
        have h1 := hF' g
        simp only [MulEquiv.coe_toMonoidHom] at h1
        rw [← h1, hgx, hrx]
      have h2 := unramifiedDegree_of_mk_eq_localReciprocityLimit hσ
      have h3 : unramifiedCoord K (ε g) n = 0 := hg
      rw [← proj_toAdd_unramifiedDegree, h2] at h3
      simp only [toAdd_ofAdd, map_intCast] at h3
      have h4 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp h3
      simpa [ho, n] using h4
  exact core l _ I r hr o (uniformizerUnit hϖ) hπ φ β e hφo hφs hβe hββ hpow hopen hI1 hI2

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc

open GroundTheory.LocalField ValuativeRel in
/- English proof (translation)
Introduce `l _ K`. Use `haveI : FiniteDimensional ℚ_[l] K.1 := K.2`. Take `⟨v, t, hloc, hext⟩` from `GroundTheory.LocalField.exists_isNonarchimedeanLocalField_valuativeExtension ℚ_[l] K.1`. Use `letI := v`. Use `letI := t`.

Use `haveI := hloc`. Use `haveI := hext`. Establish `hunit : ¬ IsUnit ((l : (ValuativeRel.valuation K.1).integer))`. Introduce and unpack `⟨u, hu⟩`. Establish `h1 : ((u : (ValuativeRel.valuation K.1).integer) : K.1) * ((↑u⁻¹ : (ValuativeRel.valuation K.1).integer) : K.1) = 1` using `congrArg Subtype.val u.mul_inv`.

Rewrite `h1` using `[hu]`. Move the coercions through the operations in `at h1`. Establish `h2 : ((↑u⁻¹ : (ValuativeRel.valuation K.1).integer) : K.1) = algebraMap ℚ_[l] K.1 ((l : ℚ_[l])⁻¹)`. Rewrite using `[map_inv₀, map_natCast]`. Conclude with `eq_inv_of_mul_eq_one_right h1`.

Establish `h3` using `(↑u⁻¹ : (ValuativeRel.valuation K.1).integer).2`. Rewrite `h3` using `[h2, GroundTheory.LocalField.algebraMap_mem_integer_iff, GroundTheory.LocalField.PadicRank.mem_integer_padic_iff, norm_inv, Padic.norm_p, inv_inv]`. Establish `: (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Combine the linear equalities and inequalities to obtain the conclusion. Use `haveI hchar : CharP 𝓀[K.1] l := by`.

Rewrite using `[CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime), ← map_natCast (IsLocalRing.residue (ValuativeRel.valuation K.1).integer) l, IsLocalRing.residue_eq_zero_iff]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hunit)`. Use `haveI : Algebra.IsAlgebraic K.1 (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) K.1`. Use `haveI : IsAlgClosure K.1 (Om l) := ⟨inferInstance, inferInstance⟩`. Use `haveI : IsSepClosure K.1 (Om l) := IsSepClosure.of_isAlgClosure_of_perfectField _ _`.

Take `⟨hc, hc'⟩` from `GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) K.1`. Establish `hm : ∀ m : ℕ, ((m : 𝓀[K.1]) ≠ 0 ↔ 0 < m ∧ ¬ l ∣ m)`. Introduce `m`. Rewrite using `[Ne, CharP.cast_eq_zero_iff 𝓀[K.1] l]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `⟨Nat.pos_of_ne_zero (fun h0 => h (h0 ▸ dvd_zero l)), h⟩`. Conclude with `fun h => h.2`. Establish `hI : ∀ g, g ∈ (UpperTheory.V.Loc.Iq l).comap (GK K).subtype ↔ unramifiedDegree K.1 (Om l) (K.1.fixingSubgroupEquiv g) = 1`. Introduce `g`.

Rewrite using `[Subgroup.mem_comap, UpperTheory.V.Loc.Iq, Formalism.BasicNotions.Loc.MaximalUnramifiedExtension, GroundTheory.LocalField.mem_fixingSubgroup_adjoin_iff, GroundTheory.LocalField.unramifiedDegree_eq_one_iff]`. Use `forall_congr' fun ξ => ?_` and prove the remaining obligations. Rewrite using `[GroundTheory.LocalField.mem_unramifiedRoots_iff]`. Simplify using `only [Set.mem_setOf_eq, hm, and_assoc]`. Both sides reduce to the same expression.

Establish `h` using `loc_field l K.1 (Om l) ((UpperTheory.V.Loc.Iq l).comap (GK K).subtype) K.1.fixingSubgroupEquiv hc hc' hI`. Rewrite `h` using `[GroundTheory.LocalField.finrank_principalUnits l]`. Establish `hdense : DenseRange ((↑) : ℚ → ℚ_[l])`. Rewrite using `[Metric.denseRange_iff]`. Introduce `x r hr`.

Take `⟨q, hq⟩` from `Padic.rat_dense l x hr`. Conclude with `⟨q, by rwa [dist_eq_norm]⟩`. Establish `heq : (GroundTheory.LocalField.CharZero.padicHom K.1 l : ℚ_[l] → K.1) = algebraMap ℚ_[l] K.1`. Use `hdense.equalizer (GroundTheory.LocalField.CharZero.continuous_padicHom K.1 l) (GroundTheory.LocalField.continuous_algebraMap ℚ_[l] K.1) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `q`.

Simplify using the standard rewrite rules. Use `h using 4` and compare the differences between its conclusion and the goal. Apply `Module.ext'` to reduce the goal to its premises. Introduce `r m`. Rewrite using `[Algebra.smul_def]`.

Simplify using `only [HSMul.hSMul, SMul.smul]`. Rewrite using `[← heq]`.
-/
theorem UpperTheory.V.W.lam_local :
    ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), Nonempty (LocAb l (GK K) ((UpperTheory.V.Loc.Iq l).comap (GK K).subtype) (Module.finrank ℚ_[l] K.1)) := by
  intro l _ K
  haveI : FiniteDimensional ℚ_[l] K.1 := K.2
  obtain ⟨v, t, hloc, hext⟩ :=
    GroundTheory.LocalField.exists_isNonarchimedeanLocalField_valuativeExtension ℚ_[l] K.1
  letI := v
  letI := t
  haveI := hloc
  haveI := hext
  have hunit : ¬ IsUnit ((l : (ValuativeRel.valuation K.1).integer)) := by
    rintro ⟨u, hu⟩
    have h1 : ((u : (ValuativeRel.valuation K.1).integer) : K.1) *
        ((↑u⁻¹ : (ValuativeRel.valuation K.1).integer) : K.1) = 1 :=
      congrArg Subtype.val u.mul_inv
    rw [hu] at h1
    push_cast at h1
    have h2 : ((↑u⁻¹ : (ValuativeRel.valuation K.1).integer) : K.1) =
        algebraMap ℚ_[l] K.1 ((l : ℚ_[l])⁻¹) := by
      rw [map_inv₀, map_natCast]
      exact eq_inv_of_mul_eq_one_right h1
    have h3 := (↑u⁻¹ : (ValuativeRel.valuation K.1).integer).2
    rw [h2, GroundTheory.LocalField.algebraMap_mem_integer_iff,
      GroundTheory.LocalField.PadicRank.mem_integer_padic_iff, norm_inv, Padic.norm_p, inv_inv] at h3
    have : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    linarith
  haveI hchar : CharP 𝓀[K.1] l := by
    rw [CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime),
      ← map_natCast (IsLocalRing.residue (ValuativeRel.valuation K.1).integer) l,
      IsLocalRing.residue_eq_zero_iff]
    exact (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hunit)
  haveI : Algebra.IsAlgebraic K.1 (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) K.1
  haveI : IsAlgClosure K.1 (Om l) := ⟨inferInstance, inferInstance⟩
  haveI : IsSepClosure K.1 (Om l) := IsSepClosure.of_isAlgClosure_of_perfectField _ _
  obtain ⟨hc, hc'⟩ := GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) K.1
  have hm : ∀ m : ℕ, ((m : 𝓀[K.1]) ≠ 0 ↔ 0 < m ∧ ¬ l ∣ m) := by
    intro m
    rw [Ne, CharP.cast_eq_zero_iff 𝓀[K.1] l]
    constructor
    · intro h
      exact ⟨Nat.pos_of_ne_zero (fun h0 => h (h0 ▸ dvd_zero l)), h⟩
    · exact fun h => h.2
  have hI : ∀ g, g ∈ (UpperTheory.V.Loc.Iq l).comap (GK K).subtype ↔
      unramifiedDegree K.1 (Om l) (K.1.fixingSubgroupEquiv g) = 1 := by
    intro g
    rw [Subgroup.mem_comap, UpperTheory.V.Loc.Iq, Formalism.BasicNotions.Loc.MaximalUnramifiedExtension,
      GroundTheory.LocalField.mem_fixingSubgroup_adjoin_iff, GroundTheory.LocalField.unramifiedDegree_eq_one_iff]
    refine forall_congr' fun ξ => ?_
    rw [GroundTheory.LocalField.mem_unramifiedRoots_iff]
    simp only [Set.mem_setOf_eq, hm, and_assoc]
    rfl
  have h := loc_field l K.1 (Om l) ((UpperTheory.V.Loc.Iq l).comap (GK K).subtype)
    K.1.fixingSubgroupEquiv hc hc' hI
  rw [GroundTheory.LocalField.finrank_principalUnits l] at h
  have hdense : DenseRange ((↑) : ℚ → ℚ_[l]) := by
    rw [Metric.denseRange_iff]
    intro x r hr
    obtain ⟨q, hq⟩ := Padic.rat_dense l x hr
    exact ⟨q, by rwa [dist_eq_norm]⟩
  have heq : (GroundTheory.LocalField.CharZero.padicHom K.1 l : ℚ_[l] → K.1) = algebraMap ℚ_[l] K.1 := by
    refine hdense.equalizer (GroundTheory.LocalField.CharZero.continuous_padicHom K.1 l)
      (GroundTheory.LocalField.continuous_algebraMap ℚ_[l] K.1) ?_
    funext q
    simp
  convert h using 4
  apply Module.ext'
  intro r m
  rw [Algebra.smul_def]
  simp only [HSMul.hSMul, SMul.smul]
  rw [← heq]
