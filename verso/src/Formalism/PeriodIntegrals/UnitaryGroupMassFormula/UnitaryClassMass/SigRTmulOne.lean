import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PsiInclR

open NumberField PI.UJClassFin PI.UnitaryGroupMassFormula.UJClassFin IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {M : ℕ}

/- English proof (translation)
Use `choose o ho hoe using hY`. Establish `hYy : Y.mulVec y = y + (Y - 1).mulVec y`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec]`. Normalize the expressions using the abelian group laws. Establish `e1 : (a ⊗ₜ[F] (1 : E)) • (Y - 1).mulVec y = k • fun i => ∑ j, o i j * (u • y j)`.

Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, hoe i j]`. Simplify using `only [nsmul_eq_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hYy, smul_add, e1]`. Conclude with `add_mem (latHat_smul L ha hy) (low_vec L hk fun i => AddSubgroup.sum_mem _ fun j _ => Oh_mul (ho i j) (up_Oh L hu hy j))`.
-/
theorem stabT (L : Set (Fin M → E)) {u k : ℕ} (hu : ∀ x ∈ L, ∀ i, IsIntegral ℤ ((u : F) • x i))
    (hk : ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((k : F) • e) ∈ L) {a : Af F} (ha : a ∈ intAf F)
    (Y : Matrix (Fin M) (Fin M) (Af F ⊗[F] E))
    (hY : ∀ i j, ∃ o ∈ Oh F E, (a ⊗ₜ[F] (1 : E)) * (Y - 1) i j = (u * k) • o)
    {y : Fin M → Af F ⊗[F] E} (hy : y ∈ latHat F E L) :
    (a ⊗ₜ[F] (1 : E)) • Y.mulVec y ∈ latHat F E L := by
  choose o ho hoe using hY
  have hYy : Y.mulVec y = y + (Y - 1).mulVec y := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  have e1 : (a ⊗ₜ[F] (1 : E)) • (Y - 1).mulVec y = k • fun i => ∑ j, o i j * (u • y j) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, hoe i j]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  rw [hYy, smul_add, e1]
  exact add_mem (latHat_smul L ha hy)
    (low_vec L hk fun i => AddSubgroup.sum_mem _ fun j _ => Oh_mul (ho i j) (up_Oh L hu hy j))

/- English proof (translation)
Use `set z := (finMat σ J g2⁻¹).mulVec (vinc (F := F) x) with hz`. Establish `hzC : (evT T ⊗ₜ[F] (1 : E)) • z ∈ latHat F E L`. Establish `: z = (finMat σ J (g2⁻¹ * g1)).mulVec ((finMat σ J g1⁻¹).mulVec (vinc (F` using `F) x)) := by`. Rewrite using `[Matrix.mulVec_mulVec, ← finMat_mul, mul_assoc, mul_inv_cancel, mul_one]`. Rewrite using `[this]`.

Conclude with `hC _ hx`. Establish `hden : ∃ m : ℕ, 0 < m ∧ m • z ∈ latHat F E L` using `by choose mf hmf hmO using fun i => den (F := F) (E := E) (z i)`. Use `⟨k * ∏ i, mf i, Nat.mul_pos hkpos (Finset.prod_pos fun i _ => hmf i), ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul]`. Apply `low_vec L hk` to reduce the goal to its premises.

Introduce `i`. Take `⟨q, hq⟩` from `Finset.dvd_prod_of_mem mf (Finset.mem_univ i)`. Use `show (∏ i, mf i) • z i ∈ Oh F E`. Rewrite using `[hq, mul_comm, mul_smul]`. Conclude with `AddSubgroup.nsmul_mem _ (hmO i) _`.

Take `⟨m, hm, hmz⟩` from `hden`. Take `⟨a, m2, hm2, hmeq⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hm.ne' p hp`. Use `⟨m2, hm2, ?_⟩` and prove the remaining obligations. Use `show (finMat σ J g2⁻¹).mulVec (vinc (F := F) ((m2 : E) • x)) ∈ latHat F E L`. Establish `e2 : (finMat σ J g2⁻¹).mulVec (vinc (F` using `F) ((m2 : E) • x)) = m2 • z := by`.

Rewrite using `[Nat.cast_smul_eq_nsmul, hz]`. Establish `: vinc (F` using `F) (m2 • x) = m2 • vinc (F := F) x := by funext i; simp [vinc]`. Rewrite using `[this, Matrix.mulVec_smul]`. Rewrite using `[e2]`. Use `set c : Af F := (1 - evT T) * algebraMap F (Af F) ((algebraMap (𝓞 F) F ((p : 𝓞 F) ^ a))⁻¹) with hc`.

Establish `hcI : c ∈ intAf F` using `one_sub_evT_inv_int T ((p : 𝓞 F) ^ a) (fun w hw hpw => hpT w hw (w.isPrime.mem_of_pow_mem a hpw))`. Establish `hpa : algebraMap (𝓞 F) F ((p : 𝓞 F) ^ a) ≠ 0`. Rewrite using `[map_pow, map_natCast]; exact pow_ne_zero _ (by exact_mod_cast hp0)`. Establish `hA : algebraMap F (Af F) ((algebraMap (𝓞 F) F ((p : 𝓞 F) ^ a))⁻¹) * ((p : Af F) ^ a) = 1`. Rewrite using `[show ((p : Af F) ^ a) = algebraMap F (Af F) (algebraMap (𝓞 F) F ((p : 𝓞 F) ^ a)) by simp, ← map_mul, inv_mul_cancel₀ hpa, map_one]`.

Establish `hsc : (m2 : Af F) = m2 * evT T + c * (m : Af F)`. Rewrite using `[hmeq, hc]`. Move the coercions through the operations in `at hA ⊢`. Take the linear combination `(-(1 - evT T) * (m2 : Af F)) * hA`. Establish `e3 : m2 • z = m2 • ((evT T ⊗ₜ[F] (1 : E)) • z) + (c ⊗ₜ[F] (1 : E)) • (m • z)`.

Establish `hι` using `congrArg (Algebra.TensorProduct.includeLeftRingHom : Af F →+* Af F ⊗[F] E) hsc`. Simplify using `only [map_add, map_mul, map_natCast] at hι`. Rewrite using `[← Nat.cast_smul_eq_nsmul (Af F ⊗[F] E) m2 z, ← Nat.cast_smul_eq_nsmul (Af F ⊗[F] E) m2, ← Nat.cast_smul_eq_nsmul (Af F ⊗[F] E) m z, smul_smul, smul_smul, ← add_smul]`. Use `congr 1`. Rewrite using `[e3]`.

Conclude with `add_mem (AddSubgroup.nsmul_mem _ hzC _) (latHat_smul L hcI hmz)`.
-/
theorem locCmpT (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (L : Set (Fin M → E)) {k : ℕ} (hkpos : 0 < k)
    (hk : ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((k : F) • e) ∈ L)
    (T : Set (HeightOneSpectrum (𝓞 F))) (p : ℕ) (hp0 : p ≠ 0) (hp : p ≠ 1)
    (hpT : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ T → (p : 𝓞 F) ∉ w.asIdeal) (g1 g2 : HA (AF F) σ J)
    (hC : ∀ y ∈ latHat F E L, (evT T ⊗ₜ[F] (1 : E)) • (finMat σ J (g2⁻¹ * g1)).mulVec y ∈ latHat F E L)
    {x : Fin M → E} (hx : x ∈ abelian₂ σ J L g1) : ∃ m2 : ℕ, ¬ p ∣ m2 ∧ (m2 : E) • x ∈ abelian₂ σ J L g2 := by
  classical
  set z := (finMat σ J g2⁻¹).mulVec (vinc (F := F) x) with hz
  have hzC : (evT T ⊗ₜ[F] (1 : E)) • z ∈ latHat F E L := by
    have : z = (finMat σ J (g2⁻¹ * g1)).mulVec ((finMat σ J g1⁻¹).mulVec (vinc (F := F) x)) := by
      rw [Matrix.mulVec_mulVec, ← finMat_mul, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]; exact hC _ hx
  have hden : ∃ m : ℕ, 0 < m ∧ m • z ∈ latHat F E L := by
    choose mf hmf hmO using fun i => den (F := F) (E := E) (z i)
    refine ⟨k * ∏ i, mf i, Nat.mul_pos hkpos (Finset.prod_pos fun i _ => hmf i), ?_⟩
    rw [mul_smul]
    apply low_vec L hk
    intro i
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem mf (Finset.mem_univ i)
    show (∏ i, mf i) • z i ∈ Oh F E
    rw [hq, mul_comm, mul_smul]
    exact AddSubgroup.nsmul_mem _ (hmO i) _
  obtain ⟨m, hm, hmz⟩ := hden
  obtain ⟨a, m2, hm2, hmeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' p hp
  refine ⟨m2, hm2, ?_⟩
  show (finMat σ J g2⁻¹).mulVec (vinc (F := F) ((m2 : E) • x)) ∈ latHat F E L
  have e2 : (finMat σ J g2⁻¹).mulVec (vinc (F := F) ((m2 : E) • x)) = m2 • z := by
    rw [Nat.cast_smul_eq_nsmul, hz]
    have : vinc (F := F) (m2 • x) = m2 • vinc (F := F) x := by funext i; simp [vinc]
    rw [this, Matrix.mulVec_smul]
  rw [e2]
  set c : Af F := (1 - evT T) * algebraMap F (Af F) ((algebraMap (𝓞 F) F ((p : 𝓞 F) ^ a))⁻¹) with hc
  have hcI : c ∈ intAf F := one_sub_evT_inv_int T ((p : 𝓞 F) ^ a)
    (fun w hw hpw => hpT w hw (w.isPrime.mem_of_pow_mem a hpw))
  have hpa : algebraMap (𝓞 F) F ((p : 𝓞 F) ^ a) ≠ 0 := by
    rw [map_pow, map_natCast]; exact pow_ne_zero _ (by exact_mod_cast hp0)
  have hA : algebraMap F (Af F) ((algebraMap (𝓞 F) F ((p : 𝓞 F) ^ a))⁻¹) * ((p : Af F) ^ a) = 1 := by
    rw [show ((p : Af F) ^ a) = algebraMap F (Af F) (algebraMap (𝓞 F) F ((p : 𝓞 F) ^ a)) by simp,
      ← map_mul, inv_mul_cancel₀ hpa, map_one]
  have hsc : (m2 : Af F) = m2 * evT T + c * (m : Af F) := by
    rw [hmeq, hc]; push_cast at hA ⊢
    linear_combination (-(1 - evT T) * (m2 : Af F)) * hA
  have e3 : m2 • z = m2 • ((evT T ⊗ₜ[F] (1 : E)) • z) + (c ⊗ₜ[F] (1 : E)) • (m • z) := by
    have hι := congrArg (Algebra.TensorProduct.includeLeftRingHom : Af F →+* Af F ⊗[F] E) hsc
    simp only [map_add, map_mul, map_natCast] at hι
    rw [← Nat.cast_smul_eq_nsmul (Af F ⊗[F] E) m2 z, ← Nat.cast_smul_eq_nsmul (Af F ⊗[F] E) m2,
      ← Nat.cast_smul_eq_nsmul (Af F ⊗[F] E) m z, smul_smul, smul_smul, ← add_smul]
    congr 1
  rw [e3]
  exact add_mem (AddSubgroup.nsmul_mem _ hzC _) (latHat_smul L hcI hmz)

/- English proof (translation)
Simplify using `[PI.UJClassFin.sigR]`.
-/
theorem sigR_tmul_one (σ : E →ₐ[F] E) (e : Af F) :
    PI.UJClassFin.sigR (Af F) σ (e ⊗ₜ[F] (1 : E)) = e ⊗ₜ[F] (1 : E) := by
  simp [PI.UJClassFin.sigR]

/- English proof (translation)
Use `choose o ho hoe using h`. Use `set U := finMat σ J kk with hUd`. Use `set W := finMat σ J kk⁻¹ with hWd`. Use `set JI := (J⁻¹).map (inclR (F := F) (Af F)) with hJId`. Use `set JA := JR (F := F) (Af F) J with hJAd`.

Use `set sg := PI.UJClassFin.sigR (Af F) σ with hsg`. Establish `hJI : JI * JA = 1`. Rewrite using `[hJId, hJAd, JR, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hJ), Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hWU : W * U = 1` using `by rw [hWd, hUd, ← finMat_mul, inv_mul_cancel, finMat_one]`. Establish `hunit : PI.UJClassFin.cT sg W * JA * W = JA` using `finMat_unitary σ J kk⁻¹`.

Establish `hU : U = JI * PI.UJClassFin.cT sg W * JA`. Combine the equalities or inequalities in the displayed calculation. Establish `hcs : PI.UJClassFin.cT sg (W - 1) = PI.UJClassFin.cT sg W - 1`. Establish `h1` using `PI.UJClassFin.cT_one (n := Fin M) sg`. Unfold `PI.UJClassFin.cT at h1 ⊢`.

Rewrite using `[Matrix.map_sub _ (map_sub _), Matrix.transpose_sub, h1]`. Establish `hU1 : U - 1 = JI * PI.UJClassFin.cT sg (W - 1) * JA`. Rewrite using `[hU, hcs, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hJI]`. Establish `key : ∀ a b, (e ⊗ₜ[F] (1 : E)) * sg ((W - 1) b a) = (dI * dJ * N) • sg (o b a)`. Introduce `a b`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hsg, sigR_tmul_one]`. Use `_ = sg ((e ⊗ₜ[F] (1 : E)) * (W - 1) b a) := (map_mul _ _ _).symm`. Use `_ = sg ((dI * dJ * N) • o b a) := by rw [hoe b a]`. Use `_ = (dI * dJ * N) • sg (o b a) := map_nsmul _ _ _`.

Introduce `i j`. Use `⟨∑ a, ∑ b, inclR (F := F) (Af F) ((dI : E) * J⁻¹ i a) * sg (o b a) * inclR (F := F) (Af F) ((dJ : E) * J b j), AddSubgroup.sum_mem _ fun a _ => AddSubgroup.sum_mem _ fun b _ => Oh_mul (Oh_mul (incl_mem_Oh (hdI i a)) (sigR_Oh σ (ho b a))) (incl_mem_Oh (hdJ b j)), ?_⟩` and prove the remaining obligations. Rewrite using `[hU1]`. Simplify using `only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]`. Use `conv_lhs => rw [Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Establish `hk` using `key a b`. Establish `hX : PI.UJClassFin.cT sg (W - 1) a b = sg ((W - 1) b a)` using `rfl`. Establish `hJI' : JI i a = inclR (F` using `F) (Af F) (J⁻¹ i a) := rfl`. Establish `hJA' : JA b j = inclR (F` using `F) (Af F) (J b j) := rfl`.

Rewrite using `[hX, hJI', hJA', map_mul, map_mul, map_natCast, map_natCast]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hk]`. Simplify using `only [nsmul_eq_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem invSmall (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0) {dI dJ : ℕ}
    (hdI : ∀ i j, IsIntegral ℤ ((dI : E) * J⁻¹ i j)) (hdJ : ∀ i j, IsIntegral ℤ ((dJ : E) * J i j))
    (e : Af F) (kk : HA (AF F) σ J) (N : ℕ)
    (h : ∀ i j, ∃ o ∈ Oh F E, (e ⊗ₜ[F] (1 : E)) * (finMat σ J kk⁻¹ - 1) i j = (dI * dJ * N) • o) :
    ∀ i j, ∃ o ∈ Oh F E, (e ⊗ₜ[F] (1 : E)) * (finMat σ J kk - 1) i j = N • o := by
  choose o ho hoe using h
  set U := finMat σ J kk with hUd
  set W := finMat σ J kk⁻¹ with hWd
  set JI := (J⁻¹).map (inclR (F := F) (Af F)) with hJId
  set JA := JR (F := F) (Af F) J with hJAd
  set sg := PI.UJClassFin.sigR (Af F) σ with hsg
  have hJI : JI * JA = 1 := by
    rw [hJId, hJAd, JR, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hJ), Matrix.map_one _ (map_zero _) (map_one _)]
  have hWU : W * U = 1 := by rw [hWd, hUd, ← finMat_mul, inv_mul_cancel, finMat_one]
  have hunit : PI.UJClassFin.cT sg W * JA * W = JA := finMat_unitary σ J kk⁻¹
  have hU : U = JI * PI.UJClassFin.cT sg W * JA := by
    calc U = JI * JA * U := by rw [hJI, Matrix.one_mul]
      _ = JI * (PI.UJClassFin.cT sg W * JA * W) * U := by rw [hunit]
      _ = JI * PI.UJClassFin.cT sg W * JA * (W * U) := by simp only [Matrix.mul_assoc]
      _ = JI * PI.UJClassFin.cT sg W * JA := by rw [hWU, Matrix.mul_one]
  have hcs : PI.UJClassFin.cT sg (W - 1) = PI.UJClassFin.cT sg W - 1 := by
    have h1 := PI.UJClassFin.cT_one (n := Fin M) sg
    unfold PI.UJClassFin.cT at h1 ⊢
    rw [Matrix.map_sub _ (map_sub _), Matrix.transpose_sub, h1]
  have hU1 : U - 1 = JI * PI.UJClassFin.cT sg (W - 1) * JA := by
    rw [hU, hcs, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hJI]
  have key : ∀ a b, (e ⊗ₜ[F] (1 : E)) * sg ((W - 1) b a) = (dI * dJ * N) • sg (o b a) := by
    intro a b
    calc (e ⊗ₜ[F] (1 : E)) * sg ((W - 1) b a) = sg (e ⊗ₜ[F] (1 : E)) * sg ((W - 1) b a) := by
          rw [hsg, sigR_tmul_one]
      _ = sg ((e ⊗ₜ[F] (1 : E)) * (W - 1) b a) := (map_mul _ _ _).symm
      _ = sg ((dI * dJ * N) • o b a) := by rw [hoe b a]
      _ = (dI * dJ * N) • sg (o b a) := map_nsmul _ _ _
  intro i j
  refine ⟨∑ a, ∑ b, inclR (F := F) (Af F) ((dI : E) * J⁻¹ i a) * sg (o b a) *
      inclR (F := F) (Af F) ((dJ : E) * J b j),
    AddSubgroup.sum_mem _ fun a _ => AddSubgroup.sum_mem _ fun b _ =>
      Oh_mul (Oh_mul (incl_mem_Oh (hdI i a)) (sigR_Oh σ (ho b a))) (incl_mem_Oh (hdJ b j)), ?_⟩
  rw [hU1]
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hk := key a b
  have hX : PI.UJClassFin.cT sg (W - 1) a b = sg ((W - 1) b a) := rfl
  have hJI' : JI i a = inclR (F := F) (Af F) (J⁻¹ i a) := rfl
  have hJA' : JA b j = inclR (F := F) (Af F) (J b j) := rfl
  rw [hX, hJI', hJA', map_mul, map_mul, map_natCast, map_natCast]
  calc (e ⊗ₜ[F] (1 : E)) * (inclR (F := F) (Af F) (J⁻¹ i a) * sg ((W - 1) b a) * inclR (F := F) (Af F) (J b j))
      = inclR (F := F) (Af F) (J⁻¹ i a) * ((e ⊗ₜ[F] (1 : E)) * sg ((W - 1) b a)) *
          inclR (F := F) (Af F) (J b j) := by ring
    _ = _ := by
      rw [hk]
      simp only [nsmul_eq_mul]
      push_cast
      ring

end Loc

end PI.UnitaryGroupMassFormula.UJClassMass
