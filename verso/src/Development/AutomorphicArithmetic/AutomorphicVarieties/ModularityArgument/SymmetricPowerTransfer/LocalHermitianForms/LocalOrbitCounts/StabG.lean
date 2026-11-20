import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.CintIdx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ExistsOfGOrbNe

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Use extensionality with `a b`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp [Matrix.one_apply] <;> rw [Algebra.smul_def]`.
-/
private theorem map_two_add_smul_eq (O K : Type) [CommRing O] [Field K] [Algebra O K] (π : O)
    (X : Matrix (Fin 2) (Fin 2) O) :
    (1 + 1 + π • X).map (algebraMap O K) = 1 + 1 + algebraMap O K π • X.map (algebraMap O K) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.one_apply] <;> rw [Algebra.smul_def]

/- English proof (translation)
Introduce `O K _ _ _ _ _ Δ τ L hτ j hj y`. Use `haveI := L.frac`. Use `set H := Subgroup.comap (jU j) (Subgroup.comap (MulEquiv.toMonoidHom (MulAut.conj y⁻¹)) (ZK O K)) with hH`. Establish `memH : ∀ z, z ∈ H ↔ y⁻¹ * jU j z * y ∈ ZK O K`. Introduce `z`.

Simplify using `[hH]`. Establish `Q : ∀ z : (Etau K τ)ˣ, trace (quo z) = trace (z : Etau K τ) ^ 2 * norm (↑z⁻¹ : Etau K τ) - 2 ∧ norm (quo z) = 1 ∧ norm (z : Etau K τ) * norm (↑z⁻¹ : Etau K τ) = 1`. Introduce `z`. Establish `hzw : (z : Etau K τ) * ↑z⁻¹ = 1` using `z.mul_inv`. Establish `hn : norm (z : Etau K τ) * norm (↑z⁻¹ : Etau K τ) = 1` using `by rw [← map_mul, hzw, map_one]`.

Establish `h1 : quo z = algebraMap K (Etau K τ) (trace (↑z⁻¹ : Etau K τ)) * z - 1`. Rewrite using `[quo, star_eq (↑z⁻¹ : Etau K τ), mul_sub, hzw, mul_comm]`. Establish `h2 : trace (z : Etau K τ) = norm (z : Etau K τ) * trace (↑z⁻¹ : Etau K τ)`. Establish `e : algebraMap K (Etau K τ) (norm (z : Etau K τ)) * ↑z⁻¹ = star (z : Etau K τ)`. Rewrite using `[algebraMap_norm_eq_mul_star, mul_comm (z : Etau K τ), mul_assoc, hzw, mul_one]`.

Use `congrArg trace e` as an intermediate fact. Rewrite `this` using `[← Algebra.smul_def, map_smul, smul_eq_mul, trace_star]`. Conclude with `this.symm`. Use `⟨?_, ?_, hn⟩` and prove the remaining obligations. Rewrite using `[h1, map_sub, ← Algebra.smul_def, map_smul, smul_eq_mul, trace_one]`.

Take the linear combination `(-(trace (z : Etau K τ)) * trace (↑z⁻¹ : Etau K τ)) * hn + (-(trace (z : Etau K τ)) * norm (↑z⁻¹ : Etau K τ)) * h2`. Rewrite using `[quo, map_mul, QuadraticAlgebra.norm_star, hn]`. Establish `P1 : ∀ z ∈ H, IsIntegral O (quo z)`. Introduce `z hz`. Rewrite `hz` using `[memH]`.

Take `⟨c, k, hck⟩` from `mem_ZK.mp hz`. Establish `hM` using `congrArg Units.val hck`. Rewrite `hM` using `[Units.val_mul, Units.val_mul, Units.val_mul]`. Establish `e0 : ((jU j z : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = j ↑z` using `rfl`. Rewrite `hM` using `[e0]`.

Establish `htr : trace (z : Etau K τ) = c * algebraMap O K (Matrix.trace (k : Matrix (Fin 2) (Fin 2) O))`. Rewrite using `[← j_trace j hj, ← Matrix.trace_units_conj' y (j z), hM]`. Apply the tactic sequence `simp [Matrix.trace_fin_two, Matrix.GeneralLinearGroup.map_apply] <;> ring`. Establish `hdet : norm (z : Etau K τ) = c ^ 2 * algebraMap O K (Matrix.det (k : Matrix (Fin 2) (Fin 2) O))`. Rewrite using `[← j_det j hj, ← Matrix.det_units_conj' y (j z), hM]`.

Apply the tactic sequence `simp [Matrix.det_fin_two, Matrix.GeneralLinearGroup.map_apply] <;> ring`. Take `⟨u, hu⟩` from `(Matrix.isUnit_iff_isUnit_det _).mp k.isUnit`. Establish `hunit : algebraMap O K ↑u⁻¹ * algebraMap O K ↑u = 1`. Rewrite using `[← map_mul]`. Simplify using the standard rewrite rules.

Establish `hn'` using `(Q z).2.2`. Rewrite `hn'` using `[hdet, ← hu]`. Use `isIntegral_of_trace_norm (x := quo z) ((k : Matrix (Fin 2) (Fin 2) O).trace ^ 2 * ↑u⁻¹ - 2) 1 ?_ ?_` and prove the remaining obligations. Rewrite using `[(Q z).1, htr]`. Simplify using `only [map_sub, map_mul, map_pow, map_ofNat]`.

Take the linear combination `(algebraMap O K (k : Matrix (Fin 2) (Fin 2) O).trace) ^ 2 * (-((c : K) ^ 2 * norm (↑z⁻¹ : Etau K τ)) * hunit + algebraMap O K ↑u⁻¹ * hn')`. Rewrite using `[(Q z).2.1, map_one]`. Use `⟨fun z hz => ⟨P1 z hz, P1 _ (H.inv_mem hz)⟩, ?_⟩` and prove the remaining obligations. Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨s, hs⟩` from `intE_fg L hτ`.

Take `⟨d, hd⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O) (s.biUnion fun g => Finset.univ.image fun p : Fin 2 × Fin 2 => (((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j g * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) p.1 p.2)`. Establish `hint : ∀ x ∈ Submodule.span O (s : Set (Etau K τ)), ∀ a b, IsLocalization.IsInteger O ((d : O) • (((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j x * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) a b)`. Introduce `x hx a b`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem g hg`.

Conclude with `hd _ (Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_image.mpr ⟨(a, b), Finset.mem_univ _, rfl⟩⟩)`. Consider the case `zero => simpa using IsLocalization.isInteger_zero`. Consider the case `add x x' _ _ h1 h2`. Rewrite using `[map_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, smul_add]`. Conclude with `IsLocalization.isInteger_add h1 h2`.

Consider the case `smul o x _ h`. Rewrite using `[← algebraMap_smul K o x, map_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, algebraMap_smul, smul_comm]`. Conclude with `IsLocalization.isInteger_smul h`. Establish `hπ0 : π ≠ 0` using `hπ.ne_zero`. Establish `hd0 : (d : O) ≠ 0` using `nonZeroDivisors.coe_ne_zero d`.

Establish `hm : π * (d : O) ≠ 0` using `mul_ne_zero hπ0 hd0`. Use `cint_relIndex_ne_zero L hτ hm H ?_` and prove the remaining obligations. Introduce `z _ r hr hq`. Establish `hrs : r ∈ Submodule.span O (s : Set (Etau K τ))`. Rewrite using `[hs, Subalgebra.mem_toSubmodule, mem_integralClosure_iff]`.

Conclude with `hr`. Set `X : Matrix (Fin 2) (Fin 2) O` to `Matrix.of fun a b => (hint r hrs a b).choose`. Establish `hX : ∀ a b, algebraMap O K (X a b) = (d : O) • (((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j r * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) a b` using `fun a b => (hint r hrs a b).choose_spec`. Establish `hzw : (z : Etau K τ) * ↑z⁻¹ = 1` using `z.mul_inv`. Establish `hn : norm (z : Etau K τ) * norm (↑z⁻¹ : Etau K τ) = 1` using `by rw [← map_mul, hzw, map_one]`.

Establish `hN0 : norm (z : Etau K τ) ≠ 0` using `left_ne_zero_of_mul_eq_one hn`. Establish `hsw : star (z : Etau K τ) * star (↑z⁻¹ : Etau K τ) = 1`. Rewrite using `[← star_mul, z.inv_mul, star_one]`. Establish `hkey : algebraMap K (Etau K τ) (trace (z : Etau K τ)) * z = algebraMap K (Etau K τ) (norm (z : Etau K τ)) * (1 + quo z)`. Rewrite using `[algebraMap_trace_eq_add_star, algebraMap_norm_eq_mul_star, quo]`.

Take the linear combination `(-((z : Etau K τ) * z)) * hsw`. Establish `h2 : IsUnit (2 : O)` using `L.two`. Establish `hm' : algebraMap O K (π * d) ≠ 0`. Rewrite using `[Ne, map_eq_zero_iff _ (IsFractionRing.injective O K)]`. Conclude with `hm`.

Establish `htr0 : trace (z : Etau K τ) ≠ 0`. Introduce `h0`. Rewrite `hkey` using `[h0, map_zero, zero_mul]`. Establish `hu : algebraMap K (Etau K τ) (norm (z : Etau K τ)) * algebraMap K (Etau K τ) (norm (↑z⁻¹ : Etau K τ)) = 1`. Rewrite using `[← map_mul, hn, map_one]`.

Establish `h1q : (1 : Etau K τ) + quo z = 0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, mul_comm (algebraMap K (Etau K τ) (norm (↑z⁻¹ : Etau K τ))), hu, one_mul]`. Use `_ = 0 := by rw [← hkey, mul_zero]`. Rewrite `h1q` using `[hq]`.

Establish `e : algebraMap O K (π * d) • r = algebraMap K (Etau K τ) (-2)`. Rewrite using `[map_neg, map_ofNat]`. Take the linear combination `h1q`. Establish `hr' : r = algebraMap K (Etau K τ) (-2 / algebraMap O K (π * d))`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[smul_smul, inv_mul_cancel₀ hm', one_smul]`. Use `_ = _ := by rw [e, Algebra.smul_def, ← map_mul, div_eq_inv_mul]`. Rewrite `hr` using `[hr']`. Establish `hI : IsIntegral O (-2 / algebraMap O K (π * d))` using `(isIntegral_algebraMap_iff (algebraMap K (Etau K τ)).injective).mp hr`. Take `⟨o, ho⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hI`.

Establish `h4 : (-2 : O) = π * d * o`. Apply `IsFractionRing.injective O K` to reduce the goal to its premises. Rewrite using `[map_mul (algebraMap O K) (π * d) o, ho, mul_div_assoc', mul_comm, mul_div_assoc, div_self hm', mul_one, map_neg, map_ofNat]`. Conclude with `hπ.not_isUnit (isUnit_of_mul_isUnit_left (x := π) (y := (d : O) * o) (by rw [← mul_assoc, ← h4]; exact h2.neg))`. Establish `ha : norm (z : Etau K τ) / trace (z : Etau K τ) ≠ 0` using `div_ne_zero hN0 htr0`.

Establish `hz_eq : (z : Etau K τ) = algebraMap K (Etau K τ) (norm (z : Etau K τ) / trace (z : Etau K τ)) * (1 + (1 + algebraMap O K (π * d) • r))`. Rewrite using `[← hq]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, ← map_mul, inv_mul_cancel₀ htr0, map_one, one_mul]`. Use `_ = _ := by rw [hkey, ← mul_assoc, ← map_mul, div_eq_mul_inv, mul_comm (trace (z : Etau K τ))⁻¹]`.

Establish `hYY : ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1` using `by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]`. Establish `φmul : ∀ (b : K) (x : Etau K τ), ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j (algebraMap K (Etau K τ) b * x) * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = b • (((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j x * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K …`. Introduce `b x`. Rewrite using `[map_mul, j.commutes, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, Matrix.mul_smul, Matrix.smul_mul]`. Establish `φadd : ∀ x x' : Etau K τ, ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j (x + x') * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j x * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) + ((y⁻¹ : GL (Fin 2) K) : Matrix …`.

Introduce `x x'`. Rewrite using `[map_add, Matrix.mul_add, Matrix.add_mul]`. Establish `φone : ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j 1 * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1` using `by rw [map_one, Matrix.mul_one, hYY]`. Establish `φsmul : ∀ (b : K) (x : Etau K τ), ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j (b • x) * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = b • (((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j x * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))`. Introduce `b x`.

Rewrite using `[map_smul, Matrix.mul_smul, Matrix.smul_mul]`. Establish `hXm : X.map (algebraMap O K) = algebraMap O K d • (((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j r * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))`. Use extensionality with `a b`. Rewrite using `[Matrix.map_apply, hX, Matrix.smul_apply, Algebra.smul_def, smul_eq_mul]`. Set `km : Matrix (Fin 2) (Fin 2) O` to `1 + 1 + π • X`.

Establish `hkm : km.map (algebraMap O K) = 1 + 1 + algebraMap O K π • X.map (algebraMap O K)`. Conclude with `map_two_add_smul_eq O K π X`. Establish `hdet : km.det = 4 + π * (2 * X 0 0 + 2 * X 1 1 + π * (X 0 0 * X 1 1 - X 0 1 * X 1 0))`. Simplify using `[km, Matrix.det_fin_two, Matrix.one_apply]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hdu : IsUnit km.det`. Assume the negation of the conclusion as `hnu`. Establish `hπm : π ∈ IsLocalRing.maximalIdeal O` using `(IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hπ.not_isUnit)`. Establish `hdm : km.det ∈ IsLocalRing.maximalIdeal O` using `(IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)`. Establish `h4m : (4 : O) ∈ IsLocalRing.maximalIdeal O`.

Use `Ideal.sub_mem _ hdm (Ideal.mul_mem_right (2 * X 0 0 + 2 * X 1 1 + π * (X 0 0 * X 1 1 - X 0 1 * X 1 0)) _ hπm)` as an intermediate fact. Rewrite `this` using `[hdet, add_sub_cancel_right]`. Then use the resulting hypothesis. Apply `mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp h4m)` to reduce the goal to its premises. Rewrite using `[show (4 : O) = 2 * 2 by norm_num]`. Conclude with `h2.mul h2`.

Set `kk : GL (Fin 2) O` to `((Matrix.isUnit_iff_isUnit_det _).mpr hdu).unit`. Establish `hA : ((Matrix.GeneralLinearGroup.map (algebraMap O K) kk : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = km.map (algebraMap O K)`. Use extensionality with `a b`. Rewrite using `[Matrix.GeneralLinearGroup.map_apply]`. Both sides reduce to the same expression.

Rewrite using `[memH]`. Apply `mem_ZK.mpr` to reduce the goal to its premises. Use `⟨Units.mk0 _ ha, kk, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, Units.val_mul, Units.val_mul]`.

Express the relevant statement in the definitionally equal form `((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j z * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = _`. Rewrite using `[Matrix.GeneralLinearGroup.coe_scalar, hA, hkm, hXm, Units.val_mk0, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]`. Use `conv_lhs => rw [hz_eq]`. Rewrite using `[φmul, φadd, φone, φadd, φone, φsmul, map_mul, smul_smul, add_assoc]`.
-/
theorem UpperTheory.V.Z.Sym.Loc.stabG : UpperTheory.V.Z.Sym.Loc.StabG := by
  classical
  intro O K _ _ _ _ _ Δ τ L hτ j hj y
  haveI := L.frac
  set H := Subgroup.comap (jU j) (Subgroup.comap (MulEquiv.toMonoidHom (MulAut.conj y⁻¹)) (ZK O K)) with hH
  have memH : ∀ z, z ∈ H ↔ y⁻¹ * jU j z * y ∈ ZK O K := by
    intro z
    simp [hH]
  have Q : ∀ z : (Etau K τ)ˣ, trace (quo z) = trace (z : Etau K τ) ^ 2 * norm (↑z⁻¹ : Etau K τ) - 2 ∧
      norm (quo z) = 1 ∧ norm (z : Etau K τ) * norm (↑z⁻¹ : Etau K τ) = 1 := by
    intro z
    have hzw : (z : Etau K τ) * ↑z⁻¹ = 1 := z.mul_inv
    have hn : norm (z : Etau K τ) * norm (↑z⁻¹ : Etau K τ) = 1 := by rw [← map_mul, hzw, map_one]
    have h1 : quo z = algebraMap K (Etau K τ) (trace (↑z⁻¹ : Etau K τ)) * z - 1 := by
      rw [quo, star_eq (↑z⁻¹ : Etau K τ), mul_sub, hzw, mul_comm]
    have h2 : trace (z : Etau K τ) = norm (z : Etau K τ) * trace (↑z⁻¹ : Etau K τ) := by
      have e : algebraMap K (Etau K τ) (norm (z : Etau K τ)) * ↑z⁻¹ = star (z : Etau K τ) := by
        rw [algebraMap_norm_eq_mul_star, mul_comm (z : Etau K τ), mul_assoc, hzw, mul_one]
      have := congrArg trace e
      rw [← Algebra.smul_def, map_smul, smul_eq_mul, trace_star] at this
      exact this.symm
    refine ⟨?_, ?_, hn⟩
    · rw [h1, map_sub, ← Algebra.smul_def, map_smul, smul_eq_mul, trace_one]
      linear_combination (-(trace (z : Etau K τ)) * trace (↑z⁻¹ : Etau K τ)) * hn +
        (-(trace (z : Etau K τ)) * norm (↑z⁻¹ : Etau K τ)) * h2
    · rw [quo, map_mul, QuadraticAlgebra.norm_star, hn]
  have P1 : ∀ z ∈ H, IsIntegral O (quo z) := by
    intro z hz
    rw [memH] at hz
    obtain ⟨c, k, hck⟩ := mem_ZK.mp hz
    have hM := congrArg Units.val hck
    rw [Units.val_mul, Units.val_mul, Units.val_mul] at hM
    have e0 : ((jU j z : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = j ↑z := rfl
    rw [e0] at hM
    have htr : trace (z : Etau K τ) = c * algebraMap O K (Matrix.trace (k : Matrix (Fin 2) (Fin 2) O)) := by
      rw [← j_trace j hj, ← Matrix.trace_units_conj' y (j z), hM]
      simp [Matrix.trace_fin_two, Matrix.GeneralLinearGroup.map_apply] <;> ring
    have hdet : norm (z : Etau K τ) = c ^ 2 * algebraMap O K (Matrix.det (k : Matrix (Fin 2) (Fin 2) O)) := by
      rw [← j_det j hj, ← Matrix.det_units_conj' y (j z), hM]
      simp [Matrix.det_fin_two, Matrix.GeneralLinearGroup.map_apply] <;> ring
    obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).mp k.isUnit
    have hunit : algebraMap O K ↑u⁻¹ * algebraMap O K ↑u = 1 := by
      rw [← map_mul]
      simp
    have hn' := (Q z).2.2
    rw [hdet, ← hu] at hn'
    refine isIntegral_of_trace_norm (x := quo z) ((k : Matrix (Fin 2) (Fin 2) O).trace ^ 2 * ↑u⁻¹ - 2) 1 ?_ ?_
    · rw [(Q z).1, htr]
      simp only [map_sub, map_mul, map_pow, map_ofNat]
      linear_combination (algebraMap O K (k : Matrix (Fin 2) (Fin 2) O).trace) ^ 2 *
        (-((c : K) ^ 2 * norm (↑z⁻¹ : Etau K τ)) * hunit + algebraMap O K ↑u⁻¹ * hn')
    · rw [(Q z).2.1, map_one]
  refine ⟨fun z hz => ⟨P1 z hz, P1 _ (H.inv_mem hz)⟩, ?_⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨s, hs⟩ := intE_fg L hτ
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O)
    (s.biUnion fun g => Finset.univ.image fun p : Fin 2 × Fin 2 =>
      (((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j g * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) p.1 p.2)
  have hint : ∀ x ∈ Submodule.span O (s : Set (Etau K τ)), ∀ a b,
      IsLocalization.IsInteger O ((d : O) • (((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j x * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) a b) := by
    intro x hx a b
    induction hx using Submodule.span_induction with
    | mem g hg =>
      exact hd _ (Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_image.mpr ⟨(a, b), Finset.mem_univ _, rfl⟩⟩)
    | zero => simpa using IsLocalization.isInteger_zero
    | add x x' _ _ h1 h2 =>
      rw [map_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, smul_add]
      exact IsLocalization.isInteger_add h1 h2
    | smul o x _ h =>
      rw [← algebraMap_smul K o x, map_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,
        algebraMap_smul, smul_comm]
      exact IsLocalization.isInteger_smul h
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hd0 : (d : O) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hm : π * (d : O) ≠ 0 := mul_ne_zero hπ0 hd0
  refine cint_relIndex_ne_zero L hτ hm H ?_
  intro z _ r hr hq
  have hrs : r ∈ Submodule.span O (s : Set (Etau K τ)) := by
    rw [hs, Subalgebra.mem_toSubmodule, mem_integralClosure_iff]
    exact hr
  let X : Matrix (Fin 2) (Fin 2) O := Matrix.of fun a b => (hint r hrs a b).choose
  have hX : ∀ a b, algebraMap O K (X a b) = (d : O) • (((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j r * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) a b :=
    fun a b => (hint r hrs a b).choose_spec
  have hzw : (z : Etau K τ) * ↑z⁻¹ = 1 := z.mul_inv
  have hn : norm (z : Etau K τ) * norm (↑z⁻¹ : Etau K τ) = 1 := by rw [← map_mul, hzw, map_one]
  have hN0 : norm (z : Etau K τ) ≠ 0 := left_ne_zero_of_mul_eq_one hn
  have hsw : star (z : Etau K τ) * star (↑z⁻¹ : Etau K τ) = 1 := by
    rw [← star_mul, z.inv_mul, star_one]
  have hkey : algebraMap K (Etau K τ) (trace (z : Etau K τ)) * z =
      algebraMap K (Etau K τ) (norm (z : Etau K τ)) * (1 + quo z) := by
    rw [algebraMap_trace_eq_add_star, algebraMap_norm_eq_mul_star, quo]
    linear_combination (-((z : Etau K τ) * z)) * hsw
  have h2 : IsUnit (2 : O) := L.two
  have hm' : algebraMap O K (π * d) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective O K)]
    exact hm
  have htr0 : trace (z : Etau K τ) ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at hkey
    have hu : algebraMap K (Etau K τ) (norm (z : Etau K τ)) * algebraMap K (Etau K τ) (norm (↑z⁻¹ : Etau K τ)) = 1 := by
      rw [← map_mul, hn, map_one]
    have h1q : (1 : Etau K τ) + quo z = 0 := by
      calc (1 : Etau K τ) + quo z = algebraMap K (Etau K τ) (norm (↑z⁻¹ : Etau K τ)) *
            (algebraMap K (Etau K τ) (norm (z : Etau K τ)) * (1 + quo z)) := by
            rw [← mul_assoc, mul_comm (algebraMap K (Etau K τ) (norm (↑z⁻¹ : Etau K τ))), hu, one_mul]
        _ = 0 := by rw [← hkey, mul_zero]
    rw [hq] at h1q
    have e : algebraMap O K (π * d) • r = algebraMap K (Etau K τ) (-2) := by
      rw [map_neg, map_ofNat]
      linear_combination h1q
    have hr' : r = algebraMap K (Etau K τ) (-2 / algebraMap O K (π * d)) := by
      calc r = (algebraMap O K (π * d))⁻¹ • (algebraMap O K (π * d) • r) := by
            rw [smul_smul, inv_mul_cancel₀ hm', one_smul]
        _ = _ := by rw [e, Algebra.smul_def, ← map_mul, div_eq_inv_mul]
    rw [hr'] at hr
    have hI : IsIntegral O (-2 / algebraMap O K (π * d)) :=
      (isIntegral_algebraMap_iff (algebraMap K (Etau K τ)).injective).mp hr
    obtain ⟨o, ho⟩ := IsIntegrallyClosed.isIntegral_iff.mp hI
    have h4 : (-2 : O) = π * d * o := by
      apply IsFractionRing.injective O K
      rw [map_mul (algebraMap O K) (π * d) o, ho, mul_div_assoc', mul_comm, mul_div_assoc, div_self hm',
        mul_one, map_neg, map_ofNat]
    exact hπ.not_isUnit (isUnit_of_mul_isUnit_left (x := π) (y := (d : O) * o)
      (by rw [← mul_assoc, ← h4]; exact h2.neg))
  have ha : norm (z : Etau K τ) / trace (z : Etau K τ) ≠ 0 := div_ne_zero hN0 htr0
  have hz_eq : (z : Etau K τ) = algebraMap K (Etau K τ) (norm (z : Etau K τ) / trace (z : Etau K τ)) *
      (1 + (1 + algebraMap O K (π * d) • r)) := by
    rw [← hq]
    calc (z : Etau K τ) = algebraMap K (Etau K τ) (trace (z : Etau K τ))⁻¹ *
          (algebraMap K (Etau K τ) (trace (z : Etau K τ)) * z) := by
          rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ htr0, map_one, one_mul]
      _ = _ := by rw [hkey, ← mul_assoc, ← map_mul, div_eq_mul_inv, mul_comm (trace (z : Etau K τ))⁻¹]
  have hYY : ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have φmul : ∀ (b : K) (x : Etau K τ), ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j (algebraMap K (Etau K τ) b * x) * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = b • (((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j x * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
    intro b x
    rw [map_mul, j.commutes, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  have φadd : ∀ x x' : Etau K τ, ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j (x + x') * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j x * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) + ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j x' * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    intro x x'
    rw [map_add, Matrix.mul_add, Matrix.add_mul]
  have φone : ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j 1 * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by rw [map_one, Matrix.mul_one, hYY]
  have φsmul : ∀ (b : K) (x : Etau K τ), ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j (b • x) * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = b • (((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j x * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
    intro b x
    rw [map_smul, Matrix.mul_smul, Matrix.smul_mul]
  have hXm : X.map (algebraMap O K) = algebraMap O K d • (((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j r * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
    ext a b
    rw [Matrix.map_apply, hX, Matrix.smul_apply, Algebra.smul_def, smul_eq_mul]
  let km : Matrix (Fin 2) (Fin 2) O := 1 + 1 + π • X
  have hkm : km.map (algebraMap O K) = 1 + 1 + algebraMap O K π • X.map (algebraMap O K) := by
    exact map_two_add_smul_eq O K π X
  have hdet : km.det = 4 + π * (2 * X 0 0 + 2 * X 1 1 + π * (X 0 0 * X 1 1 - X 0 1 * X 1 0)) := by
    simp [km, Matrix.det_fin_two, Matrix.one_apply]
    ring
  have hdu : IsUnit km.det := by
    by_contra hnu
    have hπm : π ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hπ.not_isUnit)
    have hdm : km.det ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
    have h4m : (4 : O) ∈ IsLocalRing.maximalIdeal O := by
      have := Ideal.sub_mem _ hdm (Ideal.mul_mem_right (2 * X 0 0 + 2 * X 1 1 + π * (X 0 0 * X 1 1 - X 0 1 * X 1 0)) _ hπm)
      rwa [hdet, add_sub_cancel_right] at this
    apply mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp h4m)
    rw [show (4 : O) = 2 * 2 by norm_num]
    exact h2.mul h2
  let kk : GL (Fin 2) O := ((Matrix.isUnit_iff_isUnit_det _).mpr hdu).unit
  have hA : ((Matrix.GeneralLinearGroup.map (algebraMap O K) kk : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      km.map (algebraMap O K) := by
    ext a b
    rw [Matrix.GeneralLinearGroup.map_apply]
    rfl
  rw [memH]
  apply mem_ZK.mpr
  refine ⟨Units.mk0 _ ha, kk, ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul]
  change ((y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j z * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = _
  rw [Matrix.GeneralLinearGroup.coe_scalar, hA, hkm, hXm, Units.val_mk0, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul]
  conv_lhs => rw [hz_eq]
  rw [φmul, φadd, φone, φadd, φone, φsmul, map_mul, smul_smul, add_assoc]
