import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AbsNormDiscrIdealOfLe

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallB

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [StarRing K] in
/- English proof (translation)
Use `choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 (hx j)`. Establish `hrepr : ∀ j i, b.repr (x j) i = algebraMap (𝓞 K) K (c j i)`. Introduce `j i`. Rewrite using `[← hc j]`. Simplify using `[← algebraMap_smul K, map_sum, Finsupp.single_apply]`.

Use `⟨(Matrix.of fun i j => c j i).det, ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.map_det, Basis.det_apply]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `[Basis.toMatrix_apply, hrepr]`.
-/
theorem exists_det_span (b : Basis (Fin (finrank K V)) K V) {x : Fin (finrank K V) → V}
    (hx : ∀ i, x i ∈ Submodule.span (𝓞 K) (Set.range b)) :
    ∃ d : 𝓞 K, algebraMap (𝓞 K) K d = b.det x := by
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 (hx j)
  have hrepr : ∀ j i, b.repr (x j) i = algebraMap (𝓞 K) K (c j i) := by
    intro j i
    rw [← hc j]
    simp [← algebraMap_smul K, map_sum, Finsupp.single_apply]
  refine ⟨(Matrix.of fun i j => c j i).det, ?_⟩
  rw [RingHom.map_det, Basis.det_apply]
  congr 1
  ext i j
  simp [Basis.toMatrix_apply, hrepr]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `discrIdeal_le b ?_` and prove the remaining obligations. Introduce `x hx z hz`. Take `⟨d, hd⟩` from `exists_det_span b hx`. Establish `hz' : z = conjO K d * g₀ * d`.

Apply `IsFractionRing.injective (𝓞 K) K` to reduce the goal to its premises. Apply the tactic sequence `have e1 : algebraMap (𝓞 K) K (conjO K d) = star (algebraMap (𝓞 K) K d) := by first | rfl | simp [conjO]`. Rewrite using `[hz, map_mul, map_mul, e1, hd, hg]`. Rewrite using `[hz', Ideal.mem_span_singleton]`. Conclude with `⟨conjO K d * d, by ring⟩`.

Rewrite using `[Ideal.span_singleton_le_iff_mem]`. Use `mem_discrIdeal b (fun i => Submodule.subset_span (Set.mem_range_self i)) ?_` and prove the remaining obligations. Rewrite using `[Basis.det_self, hg]`. Simplify using the standard rewrite rules.
-/
theorem discrIdeal_span {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis (Fin (finrank K V)) K V) {g₀ : 𝓞 K}
    (hg : algebraMap (𝓞 K) K g₀ = gdet h b) :
    discrIdeal h (Submodule.span (𝓞 K) (Set.range b)) = Ideal.span {g₀} := by
  apply le_antisymm
  · refine discrIdeal_le b ?_
    intro x hx z hz
    obtain ⟨d, hd⟩ := exists_det_span b hx
    have hz' : z = conjO K d * g₀ * d := by
      apply IsFractionRing.injective (𝓞 K) K
      have e1 : algebraMap (𝓞 K) K (conjO K d) = star (algebraMap (𝓞 K) K d) := by
        first | rfl | simp [conjO]
      rw [hz, map_mul, map_mul, e1, hd, hg]
    rw [hz', Ideal.mem_span_singleton]
    exact ⟨conjO K d * d, by ring⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    refine mem_discrIdeal b (fun i => Submodule.subset_span (Set.mem_range_self i)) ?_
    rw [Basis.det_self, hg]
    simp

omit [StarRing K] in
/- English proof (translation)
Establish `hm : ∀ w : InfinitePlace K, w.mult = 2`. Introduce `w`. Establish `hw : ¬ w.IsReal`. Rewrite using `[InfinitePlace.not_isReal_iff_isComplex]`. Conclude with `IsTotallyComplex.isComplex w`.

Simplify using `[InfinitePlace.mult, hw]`. Establish `hp` using `InfinitePlace.prod_eq_abs_norm (algebraMap (𝓞 K) K g₀)`. Simplify using `only [hm] at hp`. Rewrite using `[Ideal.absNorm_span_singleton, ← Finset.prod_pow, hp, Nat.cast_natAbs]`. Establish `h3` using `Algebra.coe_norm_int g₀`.

Rewrite using `[← h3]`. Use `norm_cast`.
-/
theorem absNorm_span_singleton_eq [IsTotallyComplex K] (g₀ : 𝓞 K) :
    (Ideal.absNorm (Ideal.span {g₀}) : ℝ) =
      (∏ w : InfinitePlace K, w (algebraMap (𝓞 K) K g₀)) ^ 2 := by
  have hm : ∀ w : InfinitePlace K, w.mult = 2 := by
    intro w
    have hw : ¬ w.IsReal := by
      rw [InfinitePlace.not_isReal_iff_isComplex]
      exact IsTotallyComplex.isComplex w
    simp [InfinitePlace.mult, hw]
  have hp := InfinitePlace.prod_eq_abs_norm (algebraMap (𝓞 K) K g₀)
  simp only [hm] at hp
  rw [Ideal.absNorm_span_singleton, ← Finset.prod_pow, hp, Nat.cast_natAbs]
  have h3 := Algebra.coe_norm_int g₀
  rw [← h3]
  norm_cast

/- English proof (translation)
Use `haveI : IsTotallyComplex K := hK.1`. Establish `hint : ∀ i j, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = h (b i) (b j)` using `fun i j => Submodule.mem_one.1 (hLi _ (hb i) _ (hb j))`. Use `choose c hc using hint`. Establish `hg : algebraMap (𝓞 K) K (Matrix.of fun i j => c i j).det = gdet h b`. Rewrite using `[RingHom.map_det]`.

Unfold `gdet`. Use `congr 1`. Use extensionality with `i j`. Simplify using `[hc]`. Establish `hle : Submodule.span (𝓞 K) (Set.range b) ≤ L` using `Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hb i)`.

Take `⟨n, hn⟩ : ∃ n, (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup = n` from `⟨_, rfl⟩`. Rewrite `hidx`, the goal using `[hn]`. Establish `hN` using `absNorm_discrIdeal_of_le hK hLi b n (Submodule.span (𝓞 K) (Set.range b)) hle hn hidx`. Rewrite `hN` using `[discrIdeal_span b hg]`. Establish `hS` using `absNorm_span_singleton_eq (Matrix.of fun i j => c i j).det`.

Rewrite `hS` using `[hg]`. Establish `hprod : (0 : ℝ) ≤ ∏ w : InfinitePlace K, w (gdet h b)` using `Finset.prod_nonneg (fun w _ => w.1.nonneg _)`. Establish `key : ((n : ℝ) * Real.sqrt (Ideal.absNorm (discrIdeal h L) : ℝ)) ^ 2 = (∏ w : InfinitePlace K, w (gdet h b)) ^ 2`. Rewrite using `[mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), ← hS, hN]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Unfold `normD`. Rewrite using `[← Real.sqrt_sq hprod, ← key, Real.sqrt_sq (by positivity)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem normD_mul_relIndex (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    {L : Submodule (𝓞 K) V} (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (b : Basis (Fin (finrank K V)) K V)
    (hb : ∀ i, b i ∈ L)
    (hidx : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0) :
    normD h L * ((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) =
      ∏ w : InfinitePlace K, w (gdet h b) := by
  haveI : IsTotallyComplex K := hK.1
  have hint : ∀ i j, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = h (b i) (b j) := fun i j =>
    Submodule.mem_one.1 (hLi _ (hb i) _ (hb j))
  choose c hc using hint
  have hg : algebraMap (𝓞 K) K (Matrix.of fun i j => c i j).det = gdet h b := by
    rw [RingHom.map_det]
    unfold gdet
    congr 1
    ext i j
    simp [hc]
  have hle : Submodule.span (𝓞 K) (Set.range b) ≤ L :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hb i)
  obtain ⟨n, hn⟩ : ∃ n, (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup = n :=
    ⟨_, rfl⟩
  rw [hn] at hidx ⊢
  have hN := absNorm_discrIdeal_of_le hK hLi b n (Submodule.span (𝓞 K) (Set.range b)) hle hn hidx
  rw [discrIdeal_span b hg] at hN
  have hS := absNorm_span_singleton_eq (Matrix.of fun i j => c i j).det
  rw [hg] at hS
  have hprod : (0 : ℝ) ≤ ∏ w : InfinitePlace K, w (gdet h b) :=
    Finset.prod_nonneg (fun w _ => w.1.nonneg _)
  have key : ((n : ℝ) * Real.sqrt (Ideal.absNorm (discrIdeal h L) : ℝ)) ^ 2 =
      (∏ w : InfinitePlace K, w (gdet h b)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), ← hS, hN]
    push_cast
    ring
  unfold normD
  rw [← Real.sqrt_sq hprod, ← key, Real.sqrt_sq (by positivity)]
  ring

end Formalism.HermitianLattices.Ext.L3.BallB
