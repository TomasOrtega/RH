import Formalism.SatakeDualWeyl.DefsCS

noncomputable section
open Module NumberField Matrix

namespace Formalism.UG.P

/- English proof (translation)
Set `b₀` to `(EuclideanSpace.basisFun (Fin N) ℝ).toBasis`. Establish `hc` using `ZLattice.covolume_eq_det_mul_measureReal L MeasureTheory.volume b b₀`. Establish `hvol : MeasureTheory.volume.real (ZSpan.fundamentalDomain b₀) = 1`. Rewrite using `[MeasureTheory.measureReal_def, MeasureTheory.measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped b₀ MeasureTheory.volume)]`. Rewrite using `[OrthonormalBasis.coe_toBasis, OrthonormalBasis.volume_parallelepiped]`.

Simplify using the standard rewrite rules. Rewrite using `[hc, hvol, mul_one, sq_abs, Module.Basis.det_apply]`. Establish `hG : (Matrix.of fun i j : Fin N => inner ℝ ((b i : EuclideanSpace ℝ (Fin N))) (b j)) = (b₀.toMatrix (Subtype.val ∘ b))ᵀ * b₀.toMatrix (Subtype.val ∘ b)`. Use extensionality with `i j`. Simplify using `[b₀, Matrix.mul_apply, Module.Basis.toMatrix_apply, PiLp.inner_apply, mul_comm]`.

Rewrite using `[hG, Matrix.det_mul, Matrix.det_transpose, sq]`.
-/
theorem csCovol_sq_eq_det_gram {N : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin N)))
    [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis (Fin N) ℤ L) :
    ZLattice.covolume L ^ 2 =
      (Matrix.of fun i j : Fin N => inner ℝ ((b i : EuclideanSpace ℝ (Fin N))) (b j)).det := by
  classical
  let b₀ := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
  have hc := ZLattice.covolume_eq_det_mul_measureReal L MeasureTheory.volume b b₀
  have hvol : MeasureTheory.volume.real (ZSpan.fundamentalDomain b₀) = 1 := by
    rw [MeasureTheory.measureReal_def,
      MeasureTheory.measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped b₀ MeasureTheory.volume)]
    rw [OrthonormalBasis.coe_toBasis, OrthonormalBasis.volume_parallelepiped]
    simp
  rw [hc, hvol, mul_one, sq_abs, Module.Basis.det_apply]
  have hG : (Matrix.of fun i j : Fin N => inner ℝ ((b i : EuclideanSpace ℝ (Fin N))) (b j)) =
      (b₀.toMatrix (Subtype.val ∘ b))ᵀ * b₀.toMatrix (Subtype.val ∘ b) := by
    ext i j
    simp [b₀, Matrix.mul_apply, Module.Basis.toMatrix_apply, PiLp.inner_apply, mul_comm]
  rw [hG, Matrix.det_mul, Matrix.det_transpose, sq]

/- English proof (translation)
Establish `hdet` using `congrArg Matrix.det hP`. Rewrite `hdet` using `[Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]`. Establish `hPd : ((P.det : ℤ) : ℚ) = (P.map (Int.cast : ℤ → ℚ)).det` using `(Int.castRingHom ℚ).map_det P`. Rewrite `hdet` using `[← hPd]`. Establish `hP0 : P.det ≠ 0`.

Introduce `h0`. Rewrite `hdet` using `[h0, Int.cast_zero, mul_zero]`. Conclude with `pow_ne_zero N (Int.cast_ne_zero.mpr hD0) hdet.symm`. Establish `h1 : (1 : ℚ) ≤ |(P.det : ℚ)|`. Establish `: (1 : ℤ) ≤ |P.det|` using `Int.one_le_abs hP0`.

Conclude with `this` after adjusting the coercions. Establish `habs` using `congrArg abs hdet`. Rewrite `habs` using `[abs_mul, abs_of_pos hG, abs_pow]`. Establish `key : G.det ≤ |(D : ℚ)| ^ N`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `using key`.
-/
theorem csCovol_det_le {N : ℕ} (G : Matrix (Fin N) (Fin N) ℚ) (hG : 0 < G.det) (D : ℤ) (hD0 : D ≠ 0)
    (P : Matrix (Fin N) (Fin N) ℤ) (hP : G * P.map (Int.cast : ℤ → ℚ) = (D : ℚ) • 1) :
    G.det ≤ (|D| : ℚ) ^ N := by
  have hdet := congrArg Matrix.det hP
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
  have hPd : ((P.det : ℤ) : ℚ) = (P.map (Int.cast : ℤ → ℚ)).det := (Int.castRingHom ℚ).map_det P
  rw [← hPd] at hdet
  have hP0 : P.det ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero, mul_zero] at hdet
    exact pow_ne_zero N (Int.cast_ne_zero.mpr hD0) hdet.symm
  have h1 : (1 : ℚ) ≤ |(P.det : ℚ)| := by
    have : (1 : ℤ) ≤ |P.det| := Int.one_le_abs hP0
    exact_mod_cast this
  have habs := congrArg abs hdet
  rw [abs_mul, abs_of_pos hG, abs_pow] at habs
  have key : G.det ≤ |(D : ℚ)| ^ N :=
    calc G.det = G.det * 1 := (mul_one _).symm
      _ ≤ G.det * |(P.det : ℚ)| := mul_le_mul_of_nonneg_left h1 hG.le
      _ = |(D : ℚ)| ^ N := habs
  simpa using key

/- English proof (translation)
Take `⟨c, hc⟩` from `Algebra.dvd_algebraMap_intNorm_self ℤ (𝓞 K) e`. Use `⟨Algebra.intNorm ℤ (𝓞 K) e, ?_, c, by rw [hc, mul_comm]⟩` and prove the remaining obligations. Use `first`. Consider the case `exact Algebra.intNorm_ne_zero.mpr he`. Consider the case `exact (Algebra.intNorm_eq_zero.not).mpr he`.

Consider the case `simpa using he`.
-/
theorem csCovol_int_mult {K : Type} [Field K] [NumberField K] (e : 𝓞 K) (he : e ≠ 0) :
    ∃ n : ℤ, n ≠ 0 ∧ ∃ c : 𝓞 K, (algebraMap ℤ (𝓞 K) n) = c * e := by
  obtain ⟨c, hc⟩ := Algebra.dvd_algebraMap_intNorm_self ℤ (𝓞 K) e
  refine ⟨Algebra.intNorm ℤ (𝓞 K) e, ?_, c, by rw [hc, mul_comm]⟩
  first
  | exact Algebra.intNorm_ne_zero.mpr he
  | exact (Algebra.intNorm_eq_zero.not).mpr he
  | simpa using he

/- English proof (translation)
Establish `hmem : z ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 K) K)`. Rewrite using `[Submodule.mem_traceDual]`. Introduce `a ha`. Take `⟨a', rfl⟩` from `Submodule.mem_one.mp ha`. Rewrite using `[Algebra.traceForm_apply, mul_comm]`.

Take `⟨n, hn⟩` from `hz a'`. Conclude with `⟨n, hn⟩`. Establish `hone : (1 : K) ∈ (1 : Submodule (𝓞 K) K)` using `Submodule.mem_one.mpr ⟨1, map_one _⟩`. Establish `hint` using `isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ) (L := K) (B := 𝓞 K) (1 : Submodule (𝓞 K) K) (b := NumberField.integralBasis K) (fun i => by`. Rewrite using `[NumberField.integralBasis_apply]`.

Conclude with `NumberField.RingOfIntegers.isIntegral_coe _) hone hmem`. Rewrite `hint` using `[← NumberField.coe_discr, Algebra.smul_def, mul_one]`. Use `⟨⟨_, hint⟩, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem csCovol_discr_mul {K : Type} [Field K] [NumberField K] (z : K)
    (hz : ∀ a : 𝓞 K, Algebra.trace ℚ K ((a : K) * z) ∈ Set.range (algebraMap ℤ ℚ)) :
    ((discr K : ℚ) : K) * z ∈ Set.range (algebraMap (𝓞 K) K) := by
  have hmem : z ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 K) K) := by
    rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨a', rfl⟩ := Submodule.mem_one.mp ha
    rw [Algebra.traceForm_apply, mul_comm]
    obtain ⟨n, hn⟩ := hz a'
    exact ⟨n, hn⟩
  have hone : (1 : K) ∈ (1 : Submodule (𝓞 K) K) := Submodule.mem_one.mpr ⟨1, map_one _⟩
  have hint := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ) (L := K) (B := 𝓞 K)
    (1 : Submodule (𝓞 K) K) (b := NumberField.integralBasis K)
    (fun i => by
      rw [NumberField.integralBasis_apply]
      exact NumberField.RingOfIntegers.isIntegral_coe _) hone hmem
  rw [← NumberField.coe_discr, Algebra.smul_def, mul_one] at hint
  refine ⟨⟨_, hint⟩, ?_⟩
  simp

section Main

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) {N : ℕ}
  (ι : V →+ EuclideanSpace ℝ (Fin N))

/- English proof (translation)
Use `first`. Consider the case `exact Iff.rfl`. Consider the case `simp [Formalism.HermitianLatticesTheory.zmap, AddSubgroup.mem_map]`. Consider the case `(unfold Formalism.HermitianLatticesTheory.zmap; rw [AddSubgroup.mem_toIntSubmodule, AddSubgroup.mem_map]; rfl)`.
-/
theorem csCovol_mem_zmap (M : Submodule (𝓞 K) V) (v : EuclideanSpace ℝ (Fin N)) :
    v ∈ Formalism.HermitianLatticesTheory.zmap ι M ↔ ∃ y ∈ M, ι y = v := by
  first
  | exact Iff.rfl
  | simp [Formalism.HermitianLatticesTheory.zmap, AddSubgroup.mem_map]
  | (unfold Formalism.HermitianLatticesTheory.zmap; rw [AddSubgroup.mem_toIntSubmodule, AddSubgroup.mem_map]; rfl)

/- English proof (translation)
Establish `hz' : ι z ∈ Formalism.HermitianLatticesTheory.zmap ι M` using `(csCovol_mem_zmap ι M (ι z)).mpr ⟨z, hz, rfl⟩`. Establish `h1 : (⟨ι z, hz'⟩ : Formalism.HermitianLatticesTheory.zmap ι M) = ∑ j, b.repr ⟨ι z, hz'⟩ j • b j` using `(b.sum_repr _).symm`. Establish `h2` using `congrArg Subtype.val h1`. Simplify using `only [Submodule.coe_sum, SetLike.val_smul, ← hm] at h2`. Use `⟨fun j => b.repr ⟨ι z, hz'⟩ j, fun w => ?_, fun w => ?_⟩` and prove the remaining obligations.

Establish `e1` using `hι w z`. Rewrite `e1` using `[h2, inner_sum]`. Simplify using `only [← Int.cast_smul_eq_zsmul ℝ, inner_smul_right, hι] at e1`. Establish `e2 : ((Algebra.trace ℚ K (h w z) : ℚ) : ℝ) = ((∑ j, ((b.repr ⟨ι z, hz'⟩ j : ℤ) : ℚ) * Algebra.trace ℚ K (h w (m j)) : ℚ) : ℝ)`. Use `push_cast`.

Apply the tactic sequence `first | exact e1 | exact e1.symm`. Conclude with `e2` after adjusting the coercions. Establish `e1` using `hι z w`. Rewrite `e1` using `[h2, sum_inner]`. Simplify using `only [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hι] at e1`.

Establish `e2 : ((Algebra.trace ℚ K (h z w) : ℚ) : ℝ) = ((∑ j, ((b.repr ⟨ι z, hz'⟩ j : ℤ) : ℚ) * Algebra.trace ℚ K (h (m j) w) : ℚ) : ℝ)`. Use `push_cast`. Apply the tactic sequence `first | exact e1 | exact e1.symm`. Conclude with `e2` after adjusting the coercions.
-/
theorem csCovol_expand
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (M : Submodule (𝓞 K) V) (b : Basis (Fin N) ℤ (Formalism.HermitianLatticesTheory.zmap ι M)) (m : Fin N → V)
    (hm : ∀ i, ι (m i) = b i) (z : V) (hz : z ∈ M) :
    ∃ a : Fin N → ℤ, (∀ w : V, Algebra.trace ℚ K (h w z) =
        ∑ j, (a j : ℚ) * Algebra.trace ℚ K (h w (m j))) ∧
      (∀ w : V, Algebra.trace ℚ K (h z w) = ∑ j, (a j : ℚ) * Algebra.trace ℚ K (h (m j) w)) := by
  have hz' : ι z ∈ Formalism.HermitianLatticesTheory.zmap ι M := (csCovol_mem_zmap ι M (ι z)).mpr ⟨z, hz, rfl⟩
  have h1 : (⟨ι z, hz'⟩ : Formalism.HermitianLatticesTheory.zmap ι M) = ∑ j, b.repr ⟨ι z, hz'⟩ j • b j := (b.sum_repr _).symm
  have h2 := congrArg Subtype.val h1
  simp only [Submodule.coe_sum, SetLike.val_smul, ← hm] at h2
  refine ⟨fun j => b.repr ⟨ι z, hz'⟩ j, fun w => ?_, fun w => ?_⟩
  · have e1 := hι w z
    rw [h2, inner_sum] at e1
    simp only [← Int.cast_smul_eq_zsmul ℝ, inner_smul_right, hι] at e1
    have e2 : ((Algebra.trace ℚ K (h w z) : ℚ) : ℝ) =
        ((∑ j, ((b.repr ⟨ι z, hz'⟩ j : ℤ) : ℚ) * Algebra.trace ℚ K (h w (m j)) : ℚ) : ℝ) := by
      push_cast
      first | exact e1 | exact e1.symm
    exact_mod_cast e2
  · have e1 := hι z w
    rw [h2, sum_inner] at e1
    simp only [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hι] at e1
    have e2 : ((Algebra.trace ℚ K (h z w) : ℚ) : ℝ) =
        ((∑ j, ((b.repr ⟨ι z, hz'⟩ j : ℤ) : ℚ) * Algebra.trace ℚ K (h (m j) w) : ℚ) : ℝ) := by
      push_cast
      first | exact e1 | exact e1.symm
    exact_mod_cast e2

/- English proof (translation)
Use `set G : Matrix (Fin N) (Fin N) ℚ := Matrix.of fun i k => Algebra.trace ℚ K (h (m i) (m k)) with hGdef`. Establish `htr : ∀ (q : ℚ) (y : K), Algebra.trace ℚ K ((q : K) * y) = q * Algebra.trace ℚ K y`. Introduce `q y`. Rewrite using `[← Rat.smul_def, map_smul, smul_eq_mul]`. Establish `hunit : IsUnit G.det` using `isUnit_iff_ne_zero.mpr hG`.

Use `set cc : Fin N → ℚ := G⁻¹ *ᵥ Pi.single j (1 : ℚ) with hcc`. Establish `hGc : G *ᵥ cc = Pi.single j (1 : ℚ)`. Rewrite using `[hcc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G hunit, Matrix.one_mulVec]`. Use `set x : V := ∑ k, ((cc k : ℚ) : K) • m k with hx`. Establish `hmx : ∀ i, Algebra.trace ℚ K (h (m i) x) = (Pi.single j (1 : ℚ) : Fin N → ℚ) i`.

Introduce `i`. Rewrite using `[← hGc, hx, map_sum, map_sum]`. Simplify using `only [map_smul, smul_eq_mul, htr]`. Simplify using `only [Matrix.mulVec, dotProduct, hGdef, Matrix.of_apply]`. Conclude with `Finset.sum_congr rfl (fun k _ => mul_comm _ _)`.

Establish `hloc : ∀ w ∈ M, ((discr K : ℚ) : K) * h w x ∈ Set.range (algebraMap (𝓞 K) K)`. Introduce `w hw`. Apply `csCovol_discr_mul` to reduce the goal to its premises. Introduce `a`. Establish `hai : IsIntegral ℤ (star (a : K))` using `(NumberField.RingOfIntegers.isIntegral_coe a).map (starRingEnd K).toIntAlgHom`.

Use `set a' : 𝓞 K := ⟨star (a : K), hai⟩ with ha'`. Establish `hw' : a' • w ∈ M` using `M.smul_mem a' hw`. Take `⟨aa, -, haa⟩` from `csCovol_expand h ι hι M b m hm (a' • w) hw'`. Establish `e1` using `haa x`. Simplify using `only [hmx] at e1`.

Establish `hsmul : a' • w = (star (a : K)) • w`. Rewrite using `[← algebraMap_smul K a' w]`. Both sides reduce to the same expression. Rewrite `e1` using `[hsmul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul]`. Use `⟨aa j, ?_⟩` and prove the remaining obligations.

Rewrite using `[e1]`. Simplify using `[Pi.single_apply]`. Establish `hdx : ((discr K : ℚ) : K) • x ∈ Formalism.HermitianLatticesTheory.dual h M`. Simplify using `only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]`. Introduce `w hw`.

Rewrite using `[map_smul, smul_eq_mul]`. Take `⟨r, hr⟩` from `hloc w hw`. Conclude with `Submodule.mem_one.mpr ⟨r, hr⟩`. Establish `hy : (((n * discr K : ℤ) : ℚ) : K) • x ∈ M`. Establish `h1` using `hdual _ hdx`.

Establish `h2` using `M.smul_mem c h1`. Establish `hcK : ((n : ℤ) : K) = (c : K) * (e : K)`. Use `congrArg (fun t : 𝓞 K => (t : K)) hc` as an intermediate fact. Simplify using `using this`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[← algebraMap_smul K c, smul_smul, smul_smul]`. Use `congr 1`. Use `push_cast`. Rewrite using `[hcK]`. Apply the tactic sequence `try simp only [algebraMap_smul, RingOfIntegers.coe_eq_algebraMap]`.

Apply the tactic sequence `try ring`. Take `⟨aa, haa, -⟩` from `csCovol_expand h ι hι M b m hm _ hy`. Use `⟨aa, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Establish `e1` using `haa (m i)`.

Rewrite `e1` using `[map_smul, smul_eq_mul, htr, hmx]`. Simplify using `only [Matrix.mulVec, dotProduct, hGdef, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[e1]`. Conclude with `Finset.sum_congr rfl (fun k _ => mul_comm _ _)`.
-/
theorem csCovol_column
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (M : Submodule (𝓞 K) V) (b : Basis (Fin N) ℤ (Formalism.HermitianLatticesTheory.zmap ι M)) (m : Fin N → V)
    (hm : ∀ i, ι (m i) = b i) (e : 𝓞 K)
    (hdual : ∀ x ∈ Formalism.HermitianLatticesTheory.dual h M, (e : K) • x ∈ M) (n : ℤ) (c : 𝓞 K)
    (hc : algebraMap ℤ (𝓞 K) n = c * e)
    (hG : (Matrix.of fun i k => Algebra.trace ℚ K (h (m i) (m k))).det ≠ 0) (j : Fin N) :
    ∃ a : Fin N → ℤ,
      (Matrix.of fun i k => Algebra.trace ℚ K (h (m i) (m k))) *ᵥ (fun k => (a k : ℚ)) =
        ((n * discr K : ℤ) : ℚ) • Pi.single j (1 : ℚ) := by
  classical
  set G : Matrix (Fin N) (Fin N) ℚ := Matrix.of fun i k => Algebra.trace ℚ K (h (m i) (m k)) with hGdef
  have htr : ∀ (q : ℚ) (y : K), Algebra.trace ℚ K ((q : K) * y) = q * Algebra.trace ℚ K y := by
    intro q y
    rw [← Rat.smul_def, map_smul, smul_eq_mul]
  have hunit : IsUnit G.det := isUnit_iff_ne_zero.mpr hG
  set cc : Fin N → ℚ := G⁻¹ *ᵥ Pi.single j (1 : ℚ) with hcc
  have hGc : G *ᵥ cc = Pi.single j (1 : ℚ) := by
    rw [hcc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G hunit, Matrix.one_mulVec]
  set x : V := ∑ k, ((cc k : ℚ) : K) • m k with hx
  have hmx : ∀ i, Algebra.trace ℚ K (h (m i) x) = (Pi.single j (1 : ℚ) : Fin N → ℚ) i := by
    intro i
    rw [← hGc, hx, map_sum, map_sum]
    simp only [map_smul, smul_eq_mul, htr]
    simp only [Matrix.mulVec, dotProduct, hGdef, Matrix.of_apply]
    exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  have hloc : ∀ w ∈ M, ((discr K : ℚ) : K) * h w x ∈ Set.range (algebraMap (𝓞 K) K) := by
    intro w hw
    apply csCovol_discr_mul
    intro a
    have hai : IsIntegral ℤ (star (a : K)) :=
      (NumberField.RingOfIntegers.isIntegral_coe a).map (starRingEnd K).toIntAlgHom
    set a' : 𝓞 K := ⟨star (a : K), hai⟩ with ha'
    have hw' : a' • w ∈ M := M.smul_mem a' hw
    obtain ⟨aa, -, haa⟩ := csCovol_expand h ι hι M b m hm (a' • w) hw'
    have e1 := haa x
    simp only [hmx] at e1
    have hsmul : a' • w = (star (a : K)) • w := by
      rw [← algebraMap_smul K a' w]
      rfl
    rw [hsmul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul] at e1
    refine ⟨aa j, ?_⟩
    rw [e1]
    simp [Pi.single_apply]
  have hdx : ((discr K : ℚ) : K) • x ∈ Formalism.HermitianLatticesTheory.dual h M := by
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply]
    intro w hw
    rw [map_smul, smul_eq_mul]
    obtain ⟨r, hr⟩ := hloc w hw
    exact Submodule.mem_one.mpr ⟨r, hr⟩
  have hy : (((n * discr K : ℤ) : ℚ) : K) • x ∈ M := by
    have h1 := hdual _ hdx
    have h2 := M.smul_mem c h1
    have hcK : ((n : ℤ) : K) = (c : K) * (e : K) := by
      have := congrArg (fun t : 𝓞 K => (t : K)) hc
      simpa using this
    convert h2 using 1
    rw [← algebraMap_smul K c, smul_smul, smul_smul]
    congr 1
    push_cast
    rw [hcK]
    try simp only [algebraMap_smul, RingOfIntegers.coe_eq_algebraMap]
    try ring
  obtain ⟨aa, haa, -⟩ := csCovol_expand h ι hι M b m hm _ hy
  refine ⟨aa, ?_⟩
  funext i
  have e1 := haa (m i)
  rw [map_smul, smul_eq_mul, htr, hmx] at e1
  simp only [Matrix.mulVec, dotProduct, hGdef, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  rw [e1]
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

end Main

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ _ _ h _ _ N ι hι e he`. Take `⟨n, hn0, c, hc⟩` from `csCovol_int_mult e he`. Use `set D : ℤ := n * discr K with hD`. Establish `hD0 : D ≠ 0` using `mul_ne_zero hn0 (NumberField.discr_ne_zero K)`. Use `⟨|(D : ℝ)| ^ N, ?_⟩` and prove the remaining obligations.

Introduce `M _ hdual _ _`. Establish `hrank : Module.finrank ℤ (Formalism.HermitianLatticesTheory.zmap ι M) = N`. Rewrite using `[ZLattice.rank ℝ, finrank_euclideanSpace_fin]`. Set `b` to `Module.finBasisOfFinrankEq ℤ (Formalism.HermitianLatticesTheory.zmap ι M) hrank`. Establish `hm' : ∀ i, ∃ y ∈ M, ι y = b i` using `fun i => (csCovol_mem_zmap ι M _).mp (b i).2`.

Use `choose m _ hm using hm'`. Use `set G : Matrix (Fin N) (Fin N) ℚ := Matrix.of fun i k => Algebra.trace ℚ K (h (m i) (m k)) with hGdef`. Establish `hsq` using `csCovol_sq_eq_det_gram _ b`. Establish `hGR : (Matrix.of fun i j : Fin N => inner ℝ ((b i : EuclideanSpace ℝ (Fin N))) (b j)) = (Rat.castHom ℝ).mapMatrix G`. Use extensionality with `i k`.

Simplify using `only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, hGdef]`. Rewrite using `[← hm, ← hm, hι]`. Both sides reduce to the same expression. Establish `hsq' : ZLattice.covolume (Formalism.HermitianLatticesTheory.zmap ι M) ^ 2 = (G.det : ℝ)`. Rewrite using `[hsq, hGR, ← RingHom.map_det]`.

Both sides reduce to the same expression. Use `clear hsq`. Establish `hsq` using `hsq'`. Establish `hcov : 0 < ZLattice.covolume (Formalism.HermitianLatticesTheory.zmap ι M)` using `ZLattice.covolume_pos _ _`. Establish `hGpos : 0 < G.det`.

Establish `: (0 : ℝ) < (G.det : ℝ)` using `by rw [← hsq]; positivity`. Conclude with `this` after adjusting the coercions. Establish `hcol` using `fun j => csCovol_column h ι hι M b m hm e hdual n c hc hGpos.ne' j`. Use `choose aa haa using hcol`. Set `P : Matrix (Fin N) (Fin N) ℤ` to `Matrix.of fun k j => aa j k`.

Establish `hP : G * P.map (Int.cast : ℤ → ℚ) = (D : ℚ) • 1`. Use extensionality with `i j`. Use `congrFun (haa j) i` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this`. Simplify using `only [Matrix.mul_apply, Matrix.map_apply, P, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]`.

Rewrite using `[this, hD]`. Simplify using `[Pi.single_apply, eq_comm]`. Establish `hle` using `csCovol_det_le G hGpos D hD0 P hP`. Establish `hleR : ZLattice.covolume (Formalism.HermitianLatticesTheory.zmap ι M) ^ 2 ≤ |(D : ℝ)| ^ N`. Rewrite using `[hsq]`.

Establish `: ((G.det : ℚ) : ℝ) ≤ (((|D| : ℚ) ^ N : ℚ) : ℝ)` using `by exact_mod_cast hle`. Simplify using `using this`. Establish `hD1 : (1 : ℝ) ≤ |(D : ℝ)| ^ N`. Apply `one_le_pow₀` to reduce the goal to its premises. Establish `: (1 : ℤ) ≤ |D|` using `Int.one_le_abs hD0`.

Conclude with `this` after adjusting the coercions. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem covolume_of_dual_holds : Formalism.UG.CS.CovolOfDual := by
  intro K V _ _ _ _ _ _ _ _ h _ _ N ι hι e he
  obtain ⟨n, hn0, c, hc⟩ := csCovol_int_mult e he
  set D : ℤ := n * discr K with hD
  have hD0 : D ≠ 0 := mul_ne_zero hn0 (NumberField.discr_ne_zero K)
  refine ⟨|(D : ℝ)| ^ N, ?_⟩
  intro M _ hdual _ _
  classical
  have hrank : Module.finrank ℤ (Formalism.HermitianLatticesTheory.zmap ι M) = N := by
    rw [ZLattice.rank ℝ, finrank_euclideanSpace_fin]
  let b := Module.finBasisOfFinrankEq ℤ (Formalism.HermitianLatticesTheory.zmap ι M) hrank
  have hm' : ∀ i, ∃ y ∈ M, ι y = b i := fun i => (csCovol_mem_zmap ι M _).mp (b i).2
  choose m _ hm using hm'
  set G : Matrix (Fin N) (Fin N) ℚ := Matrix.of fun i k => Algebra.trace ℚ K (h (m i) (m k)) with hGdef
  have hsq := csCovol_sq_eq_det_gram _ b
  have hGR : (Matrix.of fun i j : Fin N => inner ℝ ((b i : EuclideanSpace ℝ (Fin N))) (b j)) =
      (Rat.castHom ℝ).mapMatrix G := by
    ext i k
    simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, hGdef]
    rw [← hm, ← hm, hι]
    rfl
  have hsq' : ZLattice.covolume (Formalism.HermitianLatticesTheory.zmap ι M) ^ 2 = (G.det : ℝ) := by
    rw [hsq, hGR, ← RingHom.map_det]
    rfl
  clear hsq
  have hsq := hsq'
  have hcov : 0 < ZLattice.covolume (Formalism.HermitianLatticesTheory.zmap ι M) := ZLattice.covolume_pos _ _
  have hGpos : 0 < G.det := by
    have : (0 : ℝ) < (G.det : ℝ) := by rw [← hsq]; positivity
    exact_mod_cast this
  have hcol := fun j => csCovol_column h ι hι M b m hm e hdual n c hc hGpos.ne' j
  choose aa haa using hcol
  let P : Matrix (Fin N) (Fin N) ℤ := Matrix.of fun k j => aa j k
  have hP : G * P.map (Int.cast : ℤ → ℚ) = (D : ℚ) • 1 := by
    ext i j
    have := congrFun (haa j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mul_apply, Matrix.map_apply, P, Matrix.of_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
    rw [this, hD]
    simp [Pi.single_apply, eq_comm]
  have hle := csCovol_det_le G hGpos D hD0 P hP
  have hleR : ZLattice.covolume (Formalism.HermitianLatticesTheory.zmap ι M) ^ 2 ≤ |(D : ℝ)| ^ N := by
    rw [hsq]
    have : ((G.det : ℚ) : ℝ) ≤ (((|D| : ℚ) ^ N : ℚ) : ℝ) := by exact_mod_cast hle
    simpa using this
  have hD1 : (1 : ℝ) ≤ |(D : ℝ)| ^ N := by
    apply one_le_pow₀
    have : (1 : ℤ) ≤ |D| := Int.one_le_abs hD0
    exact_mod_cast this
  nlinarith

end Formalism.UG.P
