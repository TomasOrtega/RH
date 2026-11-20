import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.KappaZeroD

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

/- English proof (translation)
Rewrite `ht` using `[KD, Subgroup.mem_subgroupOf, MonoidHom.mem_range]`. Take `⟨N, hN⟩` from `ht`. Rewrite using `[← hN, Matrix.GeneralLinearGroup.map_apply]`. Conclude with `(N.1 0 0).2`.
-/
private theorem isIntegral_entry_zero_zero_of_mem_kd {O K : Type} [CommRing O] [Field K] [Algebra O K] {Δ : K} {t : DX Δ}
    (ht : t ∈ KD Δ O) :
    IsIntegral O (((t : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 0 0) := by
  rw [KD, Subgroup.mem_subgroupOf, MonoidHom.mem_range] at ht
  obtain ⟨N, hN⟩ := ht
  rw [← hN, Matrix.GeneralLinearGroup.map_apply]
  exact (N.1 0 0).2

/- English proof (translation)
Establish `e : s = s' * (s'⁻¹ * s)` using `by group`. Establish `hmat : Glob.mt s = Glob.mt s' * Glob.mt (s'⁻¹ * s)` using `by conv_lhs => rw [e]`. Both sides reduce to the same expression. Unfold `IsScal at hs hs'`. Rewrite `hmat` using `[hs, hs']`.

Establish `e2` using `congrFun (congrFun hmat 0) 0`. Simplify using `only [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.diagonal_apply_eq] at e2`. Use `show Glob.mt (s'⁻¹ * s) 0 0 = _`. Use `set M := Glob.mt (s'⁻¹ * s) 0 0`. Establish `h1 : algebraMap K (Lsq K Δ) (z' : K)⁻¹ * algebraMap K (Lsq K Δ) (z' : K) = 1`.

Rewrite using `[← map_mul, inv_mul_cancel₀ z'.ne_zero, map_one]`. Rewrite using `[map_mul]`. Take the linear combination `(-(algebraMap K (Lsq K Δ) (z' : K)⁻¹)) * e2 + (-M) * h1`.
-/
private theorem inv_mul_scal_entry_zero_zero_eq {K : Type} [Field K] {Δ : K} {z z' : Kˣ} {s s' : DX Δ}
    (hs : IsScal z s) (hs' : IsScal z' s') :
    (((s'⁻¹ * s : DX Δ) : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 0 0
      = algebraMap K (Lsq K Δ) ((z' : K)⁻¹ * z) := by
  have e : s = s' * (s'⁻¹ * s) := by group
  have hmat : Glob.mt s = Glob.mt s' * Glob.mt (s'⁻¹ * s) := by
    conv_lhs => rw [e]
    rfl
  unfold IsScal at hs hs'
  rw [hs, hs'] at hmat
  have e2 := congrFun (congrFun hmat 0) 0
  simp only [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.diagonal_apply_eq] at e2
  show Glob.mt (s'⁻¹ * s) 0 0 = _
  set M := Glob.mt (s'⁻¹ * s) 0 0
  have h1 : algebraMap K (Lsq K Δ) (z' : K)⁻¹ * algebraMap K (Lsq K Δ) (z' : K) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ z'.ne_zero, map_one]
  rw [map_mul]
  linear_combination (-(algebraMap K (Lsq K Δ) (z' : K)⁻¹)) * e2 + (-M) * h1

/- English proof (translation)
Introduce `O K _ _ _ _ _ Δ hL χ hχ`. Use `haveI := hL.frac`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `g hg`. Rewrite using `[fZD, dif_neg]`.

Introduce and unpack `⟨z, s, hs, hk⟩`. Apply `hg` to reduce the goal to its premises. Establish `hsZ : s ∈ ZD Δ`. Rewrite using `[ZD, Subgroup.mem_subgroupOf, MonoidHom.mem_range]`. Use `⟨z, Matrix.GeneralLinearGroup.ext fun i j => ?_⟩` and prove the remaining obligations.

Establish `h` using `congrFun (congrFun hs i) j`. Rewrite using `[show (((s : DX Δ) : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) i j = Glob.mt s i j from rfl, h]`. Simplify using `[Matrix.scalar_apply]`. Establish `e : g = s * (s⁻¹ * g)` using `by group`. Rewrite using `[e]`.

Conclude with `Subgroup.mul_mem_sup hsZ hk`. Introduce `z s k hs hk`. Establish `hex : ∃ z s', IsScal z s' ∧ s'⁻¹ * (s * k) ∈ KD Δ O` using `⟨z, s, hs, by rwa [inv_mul_cancel_left]⟩`. Rewrite using `[fZD, dif_pos hex]`. Take `⟨hs', hk'⟩` from `hex.choose_spec.choose_spec`.

Use `set z' := hex.choose`. Use `set s' := hex.choose_spec.choose`. Establish `ht : s'⁻¹ * s ∈ KD Δ O`. Establish `e : s'⁻¹ * s = (s'⁻¹ * (s * k)) * k⁻¹` using `by group`. Rewrite using `[e]`.

Conclude with `mul_mem hk' (inv_mem hk)`. Establish `ht' : s⁻¹ * s' ∈ KD Δ O`. Establish `e : s⁻¹ * s' = (s'⁻¹ * s)⁻¹` using `by group`. Rewrite using `[e]`. Conclude with `inv_mem ht`.

Establish `i1` using `isIntegral_entry_zero_zero_of_mem_kd ht`. Rewrite `i1` using `[inv_mul_scal_entry_zero_zero_eq hs hs']`. Establish `i2` using `isIntegral_entry_zero_zero_of_mem_kd ht'`. Rewrite `i2` using `[inv_mul_scal_entry_zero_zero_eq hs' hs]`. Set `f : K →ₐ[O] Lsq K Δ` to `IsScalarTower.toAlgHom O K (Lsq K Δ)`.

Establish `hf : Function.Injective f` using `(algebraMap K (Lsq K Δ)).injective`. Rewrite `i1` using `[show algebraMap K (Lsq K Δ) ((z' : K)⁻¹ * z) = f ((z' : K)⁻¹ * z) from rfl, isIntegral_algHom_iff f hf, IsIntegrallyClosed.isIntegral_iff (K := K)]`. Rewrite `i2` using `[show algebraMap K (Lsq K Δ) ((z : K)⁻¹ * z') = f ((z : K)⁻¹ * z') from rfl, isIntegral_algHom_iff f hf, IsIntegrallyClosed.isIntegral_iff (K := K)]`. Take `⟨a, ha⟩` from `i1`. Take `⟨b, hb⟩` from `i2`.

Establish `hab : a * b = 1`. Apply `IsFractionRing.injective O K` to reduce the goal to its premises. Rewrite using `[map_mul, ha, hb, map_one]`. Clear the denominators using the available nonvanishing facts. Establish `hu` using `hχ ⟨a, b, hab, by rw [mul_comm]; exact hab⟩`.

Establish `hmap : (Units.map (algebraMap O K : O →* K)) ⟨a, b, hab, by rw [mul_comm]; exact hab⟩ = z'⁻¹ * z` using `Units.ext (by simp [ha])`. Rewrite `hu` using `[hmap, map_mul, map_inv, inv_mul_eq_one]`. Rewrite using `[hu]`.
-/
theorem UpperTheory.V.Z.Sym.Loc.fzdLaw : UpperTheory.V.Z.Sym.Loc.FzdLaw := by
  intro O K _ _ _ _ _ Δ hL χ hχ
  haveI := hL.frac
  refine ⟨?_, ?_⟩
  · intro g hg
    rw [fZD, dif_neg]
    rintro ⟨z, s, hs, hk⟩
    apply hg
    have hsZ : s ∈ ZD Δ := by
      rw [ZD, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
      refine ⟨z, Matrix.GeneralLinearGroup.ext fun i j => ?_⟩
      have h := congrFun (congrFun hs i) j
      rw [show (((s : DX Δ) : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) i j
        = Glob.mt s i j from rfl, h]
      simp [Matrix.scalar_apply]
    have e : g = s * (s⁻¹ * g) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hsZ hk
  · intro z s k hs hk
    have hex : ∃ z s', IsScal z s' ∧ s'⁻¹ * (s * k) ∈ KD Δ O :=
      ⟨z, s, hs, by rwa [inv_mul_cancel_left]⟩
    rw [fZD, dif_pos hex]
    obtain ⟨hs', hk'⟩ := hex.choose_spec.choose_spec
    set z' := hex.choose
    set s' := hex.choose_spec.choose
    have ht : s'⁻¹ * s ∈ KD Δ O := by
      have e : s'⁻¹ * s = (s'⁻¹ * (s * k)) * k⁻¹ := by group
      rw [e]
      exact mul_mem hk' (inv_mem hk)
    have ht' : s⁻¹ * s' ∈ KD Δ O := by
      have e : s⁻¹ * s' = (s'⁻¹ * s)⁻¹ := by group
      rw [e]
      exact inv_mem ht
    have i1 := isIntegral_entry_zero_zero_of_mem_kd ht
    rw [inv_mul_scal_entry_zero_zero_eq hs hs'] at i1
    have i2 := isIntegral_entry_zero_zero_of_mem_kd ht'
    rw [inv_mul_scal_entry_zero_zero_eq hs' hs] at i2
    let f : K →ₐ[O] Lsq K Δ := IsScalarTower.toAlgHom O K (Lsq K Δ)
    have hf : Function.Injective f := (algebraMap K (Lsq K Δ)).injective
    rw [show algebraMap K (Lsq K Δ) ((z' : K)⁻¹ * z) = f ((z' : K)⁻¹ * z) from rfl,
      isIntegral_algHom_iff f hf, IsIntegrallyClosed.isIntegral_iff (K := K)] at i1
    rw [show algebraMap K (Lsq K Δ) ((z : K)⁻¹ * z') = f ((z : K)⁻¹ * z') from rfl,
      isIntegral_algHom_iff f hf, IsIntegrallyClosed.isIntegral_iff (K := K)] at i2
    obtain ⟨a, ha⟩ := i1
    obtain ⟨b, hb⟩ := i2
    have hab : a * b = 1 := by
      apply IsFractionRing.injective O K
      rw [map_mul, ha, hb, map_one]
      field_simp
    have hu := hχ ⟨a, b, hab, by rw [mul_comm]; exact hab⟩
    have hmap : (Units.map (algebraMap O K : O →* K)) ⟨a, b, hab, by rw [mul_comm]; exact hab⟩
        = z'⁻¹ * z := Units.ext (by simp [ha])
    rw [hmap, map_mul, map_inv, inv_mul_eq_one] at hu
    rw [hu]
