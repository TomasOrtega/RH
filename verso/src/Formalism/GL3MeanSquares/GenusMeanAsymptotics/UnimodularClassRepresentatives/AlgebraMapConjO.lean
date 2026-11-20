import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSqAbsNormOfInert

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallB

section Gram

variable {K V ι : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [Fintype ι]
  [DecidableEq ι]

/- English proof (translation)
Establish `hm : (Matrix.of fun i j => h (u i) (w j)) = (b.toMatrix u).conjTranspose * (Matrix.of fun i j => h (b i) (b j)) * b.toMatrix w`. Use extensionality with `i j`. Rewrite using `[Matrix.of_apply]`. Use `conv_lhs => rw [← b.sum_repr (u i), ← b.sum_repr (w j)]`. Simplify using `only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Basis.toMatrix_apply, Matrix.of_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, starRingEnd_apply, RingHom.id_apply]`.

Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hm, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Basis.det_apply, Basis.det_apply]`.
-/
theorem gram_det_eq (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis ι K V) (u w : ι → V) :
    (Matrix.of fun i j => h (u i) (w j)).det =
      star (b.det u) * (Matrix.of fun i j => h (b i) (b j)).det * b.det w := by
  have hm : (Matrix.of fun i j => h (u i) (w j)) =
      (b.toMatrix u).conjTranspose * (Matrix.of fun i j => h (b i) (b j)) * b.toMatrix w := by
    ext i j
    rw [Matrix.of_apply]
    conv_lhs => rw [← b.sum_repr (u i), ← b.sum_repr (w j)]
    simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Basis.toMatrix_apply, Matrix.of_apply, smul_eq_mul,
      Finset.sum_mul, Finset.mul_sum, starRingEnd_apply, RingHom.id_apply]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hm, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Basis.det_apply,
    Basis.det_apply]

end Gram

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def gdet (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis (Fin (finrank K V)) K V) : K :=
  (Matrix.of fun i j => h (b i) (b j)).det

/- English proof (translation)
The claim follows from `Ideal.subset_span ⟨x, hx, by rw [hz, gram_det_eq h b]; rfl⟩`.
-/
theorem mem_discrIdeal {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (b : Basis (Fin (finrank K V)) K V) {x : Fin (finrank K V) → V} (hx : ∀ i, x i ∈ L) {z : 𝓞 K}
    (hz : algebraMap (𝓞 K) K z = star (b.det x) * gdet h b * b.det x) : z ∈ discrIdeal h L :=
  Ideal.subset_span ⟨x, hx, by rw [hz, gram_det_eq h b]; rfl⟩

/- English proof (translation)
Use `Ideal.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `z ⟨x, hx, hz⟩`. Conclude with `hI x hx z (by rw [hz, gram_det_eq h b]; rfl)`.
-/
theorem discrIdeal_le {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (b : Basis (Fin (finrank K V)) K V) {I : Ideal (𝓞 K)}
    (hI : ∀ x : Fin (finrank K V) → V, (∀ i, x i ∈ L) → ∀ z : 𝓞 K,
      algebraMap (𝓞 K) K z = star (b.det x) * gdet h b * b.det x → z ∈ I) : discrIdeal h L ≤ I := by
  refine Ideal.span_le.2 ?_
  rintro z ⟨x, hx, hz⟩
  exact hI x hx z (by rw [hz, gram_det_eq h b]; rfl)

/- English proof (translation)
Use `choose g hg using fun i j => Submodule.mem_one.mp (hLi (u i) (hu i) (w j) (hw j))`. Use `⟨(Matrix.of g).det, ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.map_det, gdet, ← gram_det_eq h b]`. Use `congr 1`. Use extensionality with `i j`.

Conclude with `hg i j`.
-/
theorem exists_mixed {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (b : Basis (Fin (finrank K V)) K V)
    {u w : Fin (finrank K V) → V} (hu : ∀ i, u i ∈ L) (hw : ∀ i, w i ∈ L) :
    ∃ z : 𝓞 K, algebraMap (𝓞 K) K z = star (b.det u) * gdet h b * b.det w := by
  choose g hg using fun i j => Submodule.mem_one.mp (hLi (u i) (hu i) (w j) (hw j))
  refine ⟨(Matrix.of g).det, ?_⟩
  rw [RingHom.map_det, gdet, ← gram_det_eq h b]
  congr 1
  ext i j
  exact hg i j

/- English proof (translation)
Introduce `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Rewrite using `[Function.update_self]` and apply the resulting hypothesis. Rewrite using `[Function.update_of_ne hk]`.

Conclude with `hx k hk`.
-/
theorem update_mem {L : Submodule (𝓞 K) V} {n : ℕ} {x : Fin n → V} {i : Fin n}
    (hx : ∀ k, k ≠ i → x k ∈ L) {y : V} (hy : y ∈ L) : ∀ k, Function.update x i y k ∈ L := by
  intro k
  by_cases hk : k = i
  · subst hk; rwa [Function.update_self]
  · rw [Function.update_of_ne hk]; exact hx k hk

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem algebraMap_conjO (x : 𝓞 K) :
    algebraMap (𝓞 K) K (conjO K x) = star (algebraMap (𝓞 K) K x) := rfl

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Set `J : Ideal (𝓞 K)` to `{ carrier := {c | c * z ∈ I} add_mem' := fun {a c} ha hc => by`. Express the relevant statement in the definitionally equal form `(a + c) * z ∈ I`. Rewrite using `[add_mul]`. Conclude with `I.add_mem ha hc`.

Use the proof step `zero_mem' := by change (0 : 𝓞 K) * z ∈ I; rw [zero_mul]; exact I.zero_mem`. Use the proof step `smul_mem' := fun c a ha => by`. Express the relevant statement in the definitionally equal form `(c • a) * z ∈ I`. Rewrite using `[smul_eq_mul, mul_assoc]`. Conclude with `I.mul_mem_left c ha }`.

Establish `hJ : J ≠ ⊤`. Introduce `hJ`. Establish `h1 : (1 : 𝓞 K) ∈ J` using `hJ ▸ Submodule.mem_top`. Establish `h2 : (1 : 𝓞 K) * z ∈ I` using `h1`. Rewrite `h2` using `[one_mul]`.

Conclude with `hn h2`. Take `⟨P, hP, hJP⟩` from `Ideal.exists_le_maximal J hJ`. Take `⟨θ, hθ⟩` from `exists_sub_conjO_notMem hK hP`. Conclude with `hθ (hJP (hz θ))`.
-/
theorem mem_of_unram (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {I : Ideal (𝓞 K)} {z : 𝓞 K}
    (hz : ∀ θ : 𝓞 K, (θ - conjO K θ) * z ∈ I) : z ∈ I := by
  by_contra hn
  let J : Ideal (𝓞 K) :=
    { carrier := {c | c * z ∈ I}
      add_mem' := fun {a c} ha hc => by
        change (a + c) * z ∈ I
        rw [add_mul]; exact I.add_mem ha hc
      zero_mem' := by change (0 : 𝓞 K) * z ∈ I; rw [zero_mul]; exact I.zero_mem
      smul_mem' := fun c a ha => by
        change (c • a) * z ∈ I
        rw [smul_eq_mul, mul_assoc]; exact I.mul_mem_left c ha }
  have hJ : J ≠ ⊤ := by
    intro hJ
    have h1 : (1 : 𝓞 K) ∈ J := hJ ▸ Submodule.mem_top
    have h2 : (1 : 𝓞 K) * z ∈ I := h1
    rw [one_mul] at h2
    exact hn h2
  obtain ⟨P, hP, hJP⟩ := Ideal.exists_le_maximal J hJ
  obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
  exact hθ (hJP (hz θ))

/- English proof (translation)
Establish `hu` using `update_mem hx hy`. Establish `hu'` using `update_mem hx hy'`. Take `⟨z11, h11⟩` from `exists_mixed hLi b hu hu`. Take `⟨z22, h22⟩` from `exists_mixed hLi b hu' hu'`. Take `⟨z21, h21⟩` from `exists_mixed hLi b hu' hu`.

Establish `m11` using `mem_discrIdeal b hu h11`. Establish `m22` using `mem_discrIdeal b hu' h22`. Establish `key : ∀ θ : 𝓞 K, θ * z + conjO K θ * z21 ∈ discrIdeal h L`. Introduce `θ`. Establish `hd : b.det (Function.update x i (y + θ • y')) = b.det (Function.update x i y) + algebraMap (𝓞 K) K θ * b.det (Function.update x i y')`.

Rewrite using `[← algebraMap_smul K θ y', AlternatingMap.map_update_add, AlternatingMap.map_update_smul, smul_eq_mul]`. Establish `hw : z11 + conjO K θ * θ * z22 + θ * z + conjO K θ * z21 ∈ discrIdeal h L`. Use `mem_discrIdeal b (update_mem hx (L.add_mem hy (L.smul_mem θ hy'))) ?_` and prove the remaining obligations. Rewrite using `[hd]`. Simplify using `only [map_add, map_mul, h11, h22, h21, hz, algebraMap_conjO, star_add, star_mul']`.

Expand and normalize the polynomial expressions, which then agree. Establish `he : θ * z + conjO K θ * z21 = (z11 + conjO K θ * θ * z22 + θ * z + conjO K θ * z21) - z11 - conjO K θ * θ * z22`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[he]`. Conclude with `Ideal.sub_mem _ (Ideal.sub_mem _ hw m11) (Ideal.mul_mem_left _ _ m22)`.

Use `mem_of_unram hK fun θ => ?_` and prove the remaining obligations. Establish `h1` using `key 1`. Rewrite `h1` using `[map_one, one_mul, one_mul]`. Establish `he : (θ - conjO K θ) * z = (θ * z + conjO K θ * z21) - conjO K θ * (z + z21)` using `by ring`. Rewrite using `[he]`.

Conclude with `Ideal.sub_mem _ (key θ) (Ideal.mul_mem_left _ _ h1)`.
-/
theorem mixed_mem (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (b : Basis (Fin (finrank K V)) K V)
    {x : Fin (finrank K V) → V} {i : Fin (finrank K V)} (hx : ∀ k, k ≠ i → x k ∈ L) {y y' : V}
    (hy : y ∈ L) (hy' : y' ∈ L) {z : 𝓞 K}
    (hz : algebraMap (𝓞 K) K z = star (b.det (Function.update x i y)) * gdet h b *
      b.det (Function.update x i y')) : z ∈ discrIdeal h L := by
  have hu := update_mem hx hy
  have hu' := update_mem hx hy'
  obtain ⟨z11, h11⟩ := exists_mixed hLi b hu hu
  obtain ⟨z22, h22⟩ := exists_mixed hLi b hu' hu'
  obtain ⟨z21, h21⟩ := exists_mixed hLi b hu' hu
  have m11 := mem_discrIdeal b hu h11
  have m22 := mem_discrIdeal b hu' h22
  have key : ∀ θ : 𝓞 K, θ * z + conjO K θ * z21 ∈ discrIdeal h L := by
    intro θ
    have hd : b.det (Function.update x i (y + θ • y')) =
        b.det (Function.update x i y) + algebraMap (𝓞 K) K θ * b.det (Function.update x i y') := by
      rw [← algebraMap_smul K θ y', AlternatingMap.map_update_add, AlternatingMap.map_update_smul,
        smul_eq_mul]
    have hw : z11 + conjO K θ * θ * z22 + θ * z + conjO K θ * z21 ∈ discrIdeal h L := by
      refine mem_discrIdeal b (update_mem hx (L.add_mem hy (L.smul_mem θ hy'))) ?_
      rw [hd]
      simp only [map_add, map_mul, h11, h22, h21, hz, algebraMap_conjO, star_add, star_mul']
      ring
    have he : θ * z + conjO K θ * z21 =
        (z11 + conjO K θ * θ * z22 + θ * z + conjO K θ * z21) - z11 - conjO K θ * θ * z22 := by
      ring
    rw [he]
    exact Ideal.sub_mem _ (Ideal.sub_mem _ hw m11) (Ideal.mul_mem_left _ _ m22)
  refine mem_of_unram hK fun θ => ?_
  have h1 := key 1
  rw [map_one, one_mul, one_mul] at h1
  have he : (θ - conjO K θ) * z = (θ * z + conjO K θ * z21) - conjO K θ * (z + z21) := by ring
  rw [he]
  exact Ideal.sub_mem _ (key θ) (Ideal.mul_mem_left _ _ h1)

omit [StarRing K] in

/- English proof (translation)
Take `⟨N, hN⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K)) a`. Use `choose e he using hN`. Establish `hN0 : algebraMap (𝓞 K) K (N : 𝓞 K) ≠ 0`. Rewrite using `[Ne, FaithfulSMul.algebraMap_eq_zero_iff]`. Conclude with `nonZeroDivisors.coe_ne_zero N`.

Establish `he' : ∀ j, algebraMap (𝓞 K) K (e j) = algebraMap (𝓞 K) K (N : 𝓞 K) * a j`. Introduce `j`. Rewrite using `[he j, Algebra.smul_def]`. Establish `hβ : e j₀ ≠ 0`. Introduce `h0`.

Use `he' j₀` as an intermediate fact. Rewrite `this` using `[h0, map_zero]`. Conclude with `(mul_ne_zero hN0 ha) this.symm`. Establish `hβK : algebraMap (𝓞 K) K (e j₀) ≠ 0`. Rewrite using `[Ne, FaithfulSMul.algebraMap_eq_zero_iff]` and apply the resulting hypothesis.

Take `⟨C, hC⟩ : Ideal.span (Set.range e) ∣ Ideal.span {e j₀}` from `Ideal.dvd_iff_le.2 (Ideal.span_le.2 (by`. Introduce and unpack `_ rfl`. Conclude with `Ideal.subset_span ⟨j₀, rfl⟩))`. Establish `hex : ∃ γ ∈ C, ∃ j, γ * e j ∉ P * Ideal.span {e j₀}`. Assume the negation of the conclusion as `hcon`.

Use `push Not at hcon`. Establish `hle : Ideal.span {e j₀} ≤ P * Ideal.span {e j₀}` using `by conv_lhs => rw [hC]`. Rewrite using `[mul_comm, Ideal.mul_le]`. Introduce `γ hγ r hr`. Proceed by induction on `hr using Submodule.span_induction with`.

Consider the case `mem r hr => obtain ⟨j, rfl⟩ := hr`. Conclude with `hcon γ hγ j`. Consider the case `zero => rw [mul_zero]`. Conclude with `Ideal.zero_mem _`. Consider the case `add r s _ _ hr hs => rw [mul_add]`.

Conclude with `Ideal.add_mem _ hr hs`. Consider the case `smul c r _ hr => rw [smul_eq_mul, mul_left_comm]`. Conclude with `Ideal.mul_mem_left _ _ hr`. Establish `heq : P * Ideal.span {e j₀} = 1 * Ideal.span {e j₀}`. Rewrite using `[one_mul]`.

Conclude with `le_antisymm Ideal.mul_le_right hle`. Establish `hs0 : Ideal.span {e j₀} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hβ`. Conclude with `hP (by rw [mul_right_cancel₀ hs0 heq, Ideal.one_eq_top])`.

Take `⟨γ, hγ, j₁, hj₁⟩` from `hex`. Establish `hmem : ∀ j, γ * e j ∈ Ideal.span {e j₀}`. Introduce `j`. Rewrite using `[hC, mul_comm γ]`. Conclude with `Ideal.mul_mem_mul (Ideal.subset_span ⟨j, rfl⟩) hγ`.

Use `choose c hc using fun j => Ideal.mem_span_singleton'.1 (hmem j)`. Use `⟨algebraMap (𝓞 K) K γ * algebraMap (𝓞 K) K (N : 𝓞 K) / algebraMap (𝓞 K) K (e j₀), c, fun j => ?_, j₁, fun hcP => hj₁ ?_⟩` and prove the remaining obligations. Use `congrArg (algebraMap (𝓞 K) K) (hc j)` as an intermediate fact. Rewrite `this` using `[map_mul, map_mul, he' j]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← hc j₁]`. Conclude with `Ideal.mul_mem_mul hcP (Ideal.mem_span_singleton_self _)`.
-/
theorem exists_prim {J : Type*} [Finite J] (a : J → K) {j₀ : J} (ha : a j₀ ≠ 0) {P : Ideal (𝓞 K)}
    (hP : P ≠ ⊤) :
    ∃ (t : K) (c : J → 𝓞 K), (∀ j, algebraMap (𝓞 K) K (c j) = t * a j) ∧ ∃ j, c j ∉ P := by
  obtain ⟨N, hN⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K)) a
  choose e he using hN
  have hN0 : algebraMap (𝓞 K) K (N : 𝓞 K) ≠ 0 := by
    rw [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
    exact nonZeroDivisors.coe_ne_zero N
  have he' : ∀ j, algebraMap (𝓞 K) K (e j) = algebraMap (𝓞 K) K (N : 𝓞 K) * a j := by
    intro j
    rw [he j, Algebra.smul_def]
  have hβ : e j₀ ≠ 0 := by
    intro h0
    have := he' j₀
    rw [h0, map_zero] at this
    exact (mul_ne_zero hN0 ha) this.symm
  have hβK : algebraMap (𝓞 K) K (e j₀) ≠ 0 := by
    rwa [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
  obtain ⟨C, hC⟩ : Ideal.span (Set.range e) ∣ Ideal.span {e j₀} :=
    Ideal.dvd_iff_le.2 (Ideal.span_le.2 (by
      rintro _ rfl
      exact Ideal.subset_span ⟨j₀, rfl⟩))
  have hex : ∃ γ ∈ C, ∃ j, γ * e j ∉ P * Ideal.span {e j₀} := by
    by_contra hcon
    push Not at hcon
    have hle : Ideal.span {e j₀} ≤ P * Ideal.span {e j₀} := by
      conv_lhs => rw [hC]
      rw [mul_comm, Ideal.mul_le]
      intro γ hγ r hr
      induction hr using Submodule.span_induction with
      | mem r hr => obtain ⟨j, rfl⟩ := hr; exact hcon γ hγ j
      | zero => rw [mul_zero]; exact Ideal.zero_mem _
      | add r s _ _ hr hs => rw [mul_add]; exact Ideal.add_mem _ hr hs
      | smul c r _ hr => rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ hr
    have heq : P * Ideal.span {e j₀} = 1 * Ideal.span {e j₀} := by
      rw [one_mul]; exact le_antisymm Ideal.mul_le_right hle
    have hs0 : Ideal.span {e j₀} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hβ
    exact hP (by rw [mul_right_cancel₀ hs0 heq, Ideal.one_eq_top])
  obtain ⟨γ, hγ, j₁, hj₁⟩ := hex
  have hmem : ∀ j, γ * e j ∈ Ideal.span {e j₀} := by
    intro j
    rw [hC, mul_comm γ]
    exact Ideal.mul_mem_mul (Ideal.subset_span ⟨j, rfl⟩) hγ
  choose c hc using fun j => Ideal.mem_span_singleton'.1 (hmem j)
  refine ⟨algebraMap (𝓞 K) K γ * algebraMap (𝓞 K) K (N : 𝓞 K) / algebraMap (𝓞 K) K (e j₀), c,
    fun j => ?_, j₁, fun hcP => hj₁ ?_⟩
  · have := congrArg (algebraMap (𝓞 K) K) (hc j)
    rw [map_mul, map_mul, he' j] at this
    field_simp
    rw [this]; ring
  · rw [← hc j₁]
    exact Ideal.mul_mem_mul hcP (Ideal.mem_span_singleton_self _)

end Formalism.HermitianLattices.Ext.L3.BallB
