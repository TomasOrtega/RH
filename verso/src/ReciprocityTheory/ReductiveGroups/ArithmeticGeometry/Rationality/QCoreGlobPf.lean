import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QCoreH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.GlobQuotPf

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open NumberField IsDedekindDomain
open scoped TensorProduct

section Mean

variable {K K₁ : Type*} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]

/- English proof (translation)
Rewrite using `[← Finset.sum_fiberwise Finset.univ (fun φ : K₁ →+* ℂ => φ.comp (algebraMap K K₁)), Finset.mul_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_congr rfl (fun φ hφ => by rw [(Finset.mem_filter.mp hφ).2]), Finset.sum_const, nsmul_eq_mul]`. Use `congr 1`. Use `norm_cast`.

Use `letI : Algebra K ℂ := τ.toAlgebra`. Set `eqv : {φ : K₁ →+* ℂ // φ.comp (algebraMap K K₁) = τ} ≃ (K₁ →ₐ[K] ℂ)` to `{ toFun := fun φ => { φ.1 with commutes' := fun r => RingHom.congr_fun φ.2 r } invFun := fun ψ => ⟨ψ.toRingHom, RingHom.ext fun r => ψ.commutes r⟩ left_inv := fun φ => rfl right_inv := fun ψ => rfl }`. Rewrite using `[← Fintype.card_subtype, Fintype.card_congr eqv, AlgHom.card]`.
-/
theorem sum_embeddings_restrict (g : (K →+* ℂ) → ℝ) :
    ∑ φ : K₁ →+* ℂ, g (φ.comp (algebraMap K K₁)) =
      (Module.finrank K K₁ : ℝ) * ∑ τ : K →+* ℂ, g τ := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun φ : K₁ →+* ℂ => φ.comp (algebraMap K K₁)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_congr rfl (fun φ hφ => by rw [(Finset.mem_filter.mp hφ).2]), Finset.sum_const,
    nsmul_eq_mul]
  congr 1
  norm_cast
  letI : Algebra K ℂ := τ.toAlgebra
  let eqv : {φ : K₁ →+* ℂ // φ.comp (algebraMap K K₁) = τ} ≃ (K₁ →ₐ[K] ℂ) :=
    { toFun := fun φ => { φ.1 with commutes' := fun r => RingHom.congr_fun φ.2 r }
      invFun := fun ψ => ⟨ψ.toRingHom, RingHom.ext fun r => ψ.commutes r⟩
      left_inv := fun φ => rfl
      right_inv := fun ψ => rfl }
  rw [← Fintype.card_subtype, Fintype.card_congr eqv, AlgHom.card]

/- English proof (translation)
Rewrite using `[← sum_embeddings_restrict g]`. Rewrite using `[← Finset.sum_fiberwise Finset.univ (fun φ : K₁ →+* ℂ => InfinitePlace.mk φ)]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Establish `hc : ∀ φ ∈ Finset.univ.filter (fun φ : K₁ →+* ℂ => InfinitePlace.mk φ = σ), g (φ.comp (algebraMap K K₁)) = g (σ.embedding.comp (algebraMap K K₁))`. Introduce `φ hφ`.

Establish `h1` using `(Finset.mem_filter.mp hφ).2`. Rewrite `h1` using `[← InfinitePlace.mk_embedding σ, InfinitePlace.mk_eq_iff]`. Break down `h1 with h1 | h1` into its components or cases. Rewrite using `[h1]`. Rewrite using `[← h1]`.

Establish `h2 : (ComplexEmbedding.conjugate φ).comp (algebraMap K K₁) = (starRingEnd ℂ).comp (φ.comp (algebraMap K K₁))` using `RingHom.ext fun x => rfl`. Rewrite using `[h2, hg]`. Rewrite using `[Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul, InfinitePlace.card_filter_mk_eq]`.
-/
theorem sum_places_restrict (g : (K →+* ℂ) → ℝ) (hg : ∀ τ, g ((starRingEnd ℂ).comp τ) = g τ) :
    ∑ σ : InfinitePlace K₁, (σ.mult : ℝ) * g (σ.embedding.comp (algebraMap K K₁)) =
      (Module.finrank K K₁ : ℝ) * ∑ τ : K →+* ℂ, g τ := by
  rw [← sum_embeddings_restrict g]
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun φ : K₁ →+* ℂ => InfinitePlace.mk φ)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hc : ∀ φ ∈ Finset.univ.filter (fun φ : K₁ →+* ℂ => InfinitePlace.mk φ = σ),
      g (φ.comp (algebraMap K K₁)) = g (σ.embedding.comp (algebraMap K K₁)) := by
    intro φ hφ
    have h1 := (Finset.mem_filter.mp hφ).2
    rw [← InfinitePlace.mk_embedding σ, InfinitePlace.mk_eq_iff] at h1
    rcases h1 with h1 | h1
    · rw [h1]
    · rw [← h1]
      have h2 : (ComplexEmbedding.conjugate φ).comp (algebraMap K K₁)
          = (starRingEnd ℂ).comp (φ.comp (algebraMap K K₁)) := RingHom.ext fun x => rfl
      rw [h2, hg]
  rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul, InfinitePlace.card_filter_mk_eq]

end Mean

section Regroup

variable {K K₁ : Type*} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]

noncomputable def under (w : HeightOneSpectrum (𝓞 K₁)) : HeightOneSpectrum (𝓞 K) where
  asIdeal := w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 K₁))
  isPrime := Ideal.IsPrime.comap _
  ne_bot := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)

/- English proof (translation)
Unfold `LiesOver`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `HeightOneSpectrum.ext h`. Introduce `h`.

Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem liesOver_iff_under (w : HeightOneSpectrum (𝓞 K₁)) (la : HeightOneSpectrum (𝓞 K)) :
    LiesOver w la ↔ under (K := K) w = la := by
  unfold LiesOver
  constructor
  · intro h
    exact HeightOneSpectrum.ext h
  · intro h
    subst h
    rfl

/- English proof (translation)
Establish `: w.asIdeal.LiesOver la.asIdeal` using `⟨by rw [Ideal.under_def]; exact h.symm⟩`. Establish `hn` using `Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal la.asIdeal la.isPrime la.ne_bot`. Rewrite `hn` using `[Ideal.inertiaDeg'_eq_inertiaDeg]`. Simplify using `only [logN, hn, Nat.cast_pow, Real.log_pow]`.
-/
theorem logN_of_liesOver {w : HeightOneSpectrum (𝓞 K₁)} {la : HeightOneSpectrum (𝓞 K)}
    (h : LiesOver w la) : logN w = (w.asIdeal.inertiaDeg (𝓞 K) : ℝ) * logN la := by
  have : w.asIdeal.LiesOver la.asIdeal := ⟨by rw [Ideal.under_def]; exact h.symm⟩
  have hn := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal la.asIdeal la.isPrime la.ne_bot
  rw [Ideal.inertiaDeg'_eq_inertiaDeg] at hn
  simp only [logN, hn, Nat.cast_pow, Real.log_pow]

/- English proof (translation)
Use `set S := hF.toFinset`. Use `set T : Finset (HeightOneSpectrum (𝓞 K)) := S.image under`. Establish `hinner : ∀ la : HeightOneSpectrum (𝓞 K), ∑ᶠ w : {w // LiesOver w la}, (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w.1 = ∑ w ∈ S.filter (fun w => under (K` using `K) w = la), (w.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w := by`. Introduce `la`. Rewrite using `[finsum_eq_sum_of_support_subset _ (s := S.subtype (fun w => LiesOver w la)) ?_, Finset.sum_subtype_eq_sum_filter (fun w : HeightOneSpectrum (𝓞 K₁) => (w.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w)]`.

Use `Finset.sum_congr ?_ fun _ _ => rfl` and prove the remaining obligations. Use extensionality with `w`. Simplify using `[liesOver_iff_under]`. Introduce `w hw`. Rewrite using `[Finset.mem_coe, Finset.mem_subtype, Set.Finite.mem_toFinset, Function.mem_support]`.

Introduce `h0`. Conclude with `hw (by simp [h0])`. Establish `hsupp : (Function.support fun la : HeightOneSpectrum (𝓞 K) => ∑ᶠ w : {w // LiesOver w la}, (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w.1) ⊆ T`. Introduce `la hla`. Rewrite `hla` using `[Function.mem_support, hinner]`.

Take `⟨w, hw, -⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hla`. Rewrite `hw` using `[Finset.mem_filter]`. Conclude with `Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨w, hw.1, hw.2⟩)`. Use `⟨T.finite_toSet.subset hsupp, ?_⟩` and prove the remaining obligations. Rewrite using `[finsum_eq_sum_of_support_subset _ (s := T) (fun la hla => hsupp (by`.

Introduce `h`. Apply `hla` to reduce the goal to its premises. Simplify using `[h])),`. Use `finsum_eq_sum_of_support_subset _ (s := S) (fun w hw => by`. Simplify using `only [Finset.mem_coe, Set.Finite.mem_toFinset, S]`.

Introduce `h`. Apply `hw` to reduce the goal to its premises. Simplify using `[h])]`. Repeatedly rewrite using `[hinner, Finset.sum_mul]`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (s := S) (t := T) (g := under) (fun w hw => Finset.mem_image_of_mem _ hw)]`.

Use `Finset.sum_congr rfl fun la _ => Finset.sum_congr rfl fun w hw => ?_` and prove the remaining obligations. Rewrite `hw` using `[Finset.mem_filter]`. Rewrite using `[logN_of_liesOver ((liesOver_iff_under w la).mpr hw.2)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finsum_regroup (F : HeightOneSpectrum (𝓞 K₁) → ℝ) (hF : (Function.support F).Finite) :
    (Function.support fun la : HeightOneSpectrum (𝓞 K) =>
        ∑ᶠ w : {w // LiesOver w la}, (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w.1).Finite ∧
    ∑ᶠ la : HeightOneSpectrum (𝓞 K),
        (∑ᶠ w : {w // LiesOver w la}, (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w.1) * logN la =
      ∑ᶠ w, F w * logN w := by
  classical
  set S := hF.toFinset
  set T : Finset (HeightOneSpectrum (𝓞 K)) := S.image under
  have hinner : ∀ la : HeightOneSpectrum (𝓞 K),
      ∑ᶠ w : {w // LiesOver w la}, (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w.1 =
        ∑ w ∈ S.filter (fun w => under (K := K) w = la),
          (w.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w := by
    intro la
    rw [finsum_eq_sum_of_support_subset _ (s := S.subtype (fun w => LiesOver w la)) ?_,
      Finset.sum_subtype_eq_sum_filter
        (fun w : HeightOneSpectrum (𝓞 K₁) => (w.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w)]
    · refine Finset.sum_congr ?_ fun _ _ => rfl
      ext w; simp [liesOver_iff_under]
    · intro w hw
      rw [Finset.mem_coe, Finset.mem_subtype, Set.Finite.mem_toFinset, Function.mem_support]
      intro h0
      exact hw (by simp [h0])
  have hsupp : (Function.support fun la : HeightOneSpectrum (𝓞 K) =>
      ∑ᶠ w : {w // LiesOver w la}, (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w.1) ⊆ T := by
    intro la hla
    rw [Function.mem_support, hinner] at hla
    obtain ⟨w, hw, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hla
    rw [Finset.mem_filter] at hw
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨w, hw.1, hw.2⟩)
  refine ⟨T.finite_toSet.subset hsupp, ?_⟩
  rw [finsum_eq_sum_of_support_subset _ (s := T) (fun la hla => hsupp (by
      intro h; apply hla; simp [h])),
    finsum_eq_sum_of_support_subset _ (s := S) (fun w hw => by
      simp only [Finset.mem_coe, Set.Finite.mem_toFinset, S]
      intro h; apply hw; simp [h])]
  simp_rw [hinner, Finset.sum_mul]
  rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := T) (g := under)
    (fun w hw => Finset.mem_image_of_mem _ hw)]
  refine Finset.sum_congr rfl fun la _ => Finset.sum_congr rfl fun w hw => ?_
  rw [Finset.mem_filter] at hw
  rw [logN_of_liesOver ((liesOver_iff_under w la).mpr hw.2)]
  ring

end Regroup

/- English proof (translation)
Introduce `K K₁ V _ _ _ _ _ _ _ _ M ρ θ c hD s hs supN a Bθ Carch Bdeg hconj hmean harch hdeg`. Use `set D := detCT c θ with hDdef`. Set `F : HeightOneSpectrum (𝓞 K₁) → ℝ` to `fun w => (ordAt w D : ℝ) + ∑ i, s i w`. Establish `hordfin : (Function.support fun w : HeightOneSpectrum (𝓞 K₁) => (ordAt w D : ℝ)).Finite`. Use `(finite_ordAt hD).subset fun w hw => ?_` and prove the remaining obligations.

Establish `hpos : (0 : ℝ) < logN w` using `Real.log_pos (one_lt_absNorm_real w)`. Simplify using `only [Function.mem_support] at hw ⊢`. Conclude with `mul_ne_zero hw hpos.ne'`. Establish `hFfin : (Function.support F).Finite`. Use `(hordfin.union (Set.finite_iUnion fun i => hs i)).subset fun w hw => ?_` and prove the remaining obligations.

Assume the negation of the conclusion as `hnot`. Simplify using `only [Set.mem_union, Set.mem_iUnion, Function.mem_support, not_or, not_exists, not_not] at hnot`. Apply `hw` to reduce the goal to its premises. Simplify using `[F, hnot.1, hnot.2]`. Take `⟨hfinsupp, hregroup⟩` from `finsum_regroup (K := K) F hFfin`.

Establish `hnn : ∀ la, nnFun (K` using `K) D s la = (∑ᶠ w : {w // LiesOver w la}, (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w.1) / (Module.finrank K K₁ : ℝ) := fun la => rfl`. Establish `hK₁K : (0 : ℝ) < Module.finrank K K₁`. Establish `: Module.Finite K K₁` using `Module.Finite.of_restrictScalars_finite ℚ K K₁`. Conclude with `Module.finrank_pos` after adjusting the coercions. Establish `hKQ : (0 : ℝ) < Module.finrank ℚ K` using `by exact_mod_cast Module.finrank_pos`.

Establish `htower : (Module.finrank ℚ K₁ : ℝ) = Module.finrank ℚ K * Module.finrank K K₁`. Conclude with `(Module.finrank_mul_finrank ℚ K K₁).symm` after adjusting the coercions. Use `⟨hfinsupp.subset fun la hla => by` and prove the remaining obligations. Rewrite `hla` using `[Function.mem_support, hnn]`. Introduce `h`.

Apply `hla` to reduce the goal to its premises. Simplify using `[h], ?_⟩`. Establish `hsum : (∑ᶠ la : HeightOneSpectrum (𝓞 K), nnFun (K` using `K) D s la * logN la) = (∑ᶠ w, F w * logN w) / (Module.finrank K K₁ : ℝ) := by`. Establish `hfin2 : (Function.support fun la : HeightOneSpectrum (𝓞 K) => (∑ᶠ w : {w // LiesOver w la}, (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w.1) * logN la).Finite` using `hfinsupp.subset fun la hla => by`. Rewrite `hla`, the goal using `[Function.mem_support]`.

Introduce `h`. Apply `hla` to reduce the goal to its premises. Rewrite using `[h, zero_mul]`. Rewrite using `[← hregroup, div_eq_mul_inv, finsum_mul]`. Use `finsum_congr fun la => ?_` and prove the remaining obligations.

Rewrite using `[hnn]`. Expand and normalize the polynomial expressions, which then agree. Set `m : Matrix (Fin ρ) (Fin ρ) K₁` to `Matrix.of fun i j => c i ((1 : K₁) ⊗ₜ[K] ((θ j : M) : V))`. Establish `hmD : m.det = D` using `rfl`. Set `b : Fin ρ → InfinitePlace K₁ → ℝ` to `fun j σ => Real.log (supN (σ.embedding.comp (algebraMap K K₁)) ((θ j : M) : V)) + Carch`.

Establish `hG` using `globalQuot_holds K₁ ρ m (by rw [hmD]; exact hD) s (fun _ => 0) a b (fun _ => Bdeg) 0 hs (by simp) (fun σ i j hij => harch σ i j hij) hdeg (by simp)`. Establish `hLHS : (∑ᶠ w, ((ordAt w m.det : ℝ) + ∑ i, s i w + (ρ : ℝ) * (fun _ => (0 : ℝ)) w) * logN w) = ∑ᶠ w, F w * logN w` using `finsum_congr fun w => by simp [F, hmD]`. Rewrite `hG` using `[hLHS]`. Establish `hKQc : (Fintype.card (K →+* ℂ) : ℝ) = Module.finrank ℚ K`. Conclude with `Embeddings.card K ℂ` after adjusting the coercions.

Establish `hbj : ∀ j, (∑ σ : InfinitePlace K₁, (σ.mult : ℝ) * b j σ) / (Module.finrank ℚ K₁ : ℝ) ≤ Bθ + Carch`. Introduce `j`. Establish `e0 : ∀ σ : InfinitePlace K₁, (σ.mult : ℝ) * b j σ = (σ.mult : ℝ) * Real.log (supN (σ.embedding.comp (algebraMap K K₁)) ((θ j : M) : V)) + Carch * (σ.mult : ℝ)` using `fun σ => by simp only [b]; ring`. Establish `e2` using `sum_places_restrict (K := K) (K₁ := K₁) (fun τ => Real.log (supN τ ((θ j : M) : V))) (fun τ => by rw [hconj])`. Establish `e3 : (∑ σ : InfinitePlace K₁, (σ.mult : ℝ)) = Module.finrank ℚ K₁`.

Conclude with `InfinitePlace.sum_mult_eq` after adjusting the coercions. Rewrite using `[Finset.sum_congr rfl (fun σ _ => e0 σ), Finset.sum_add_distrib, ← Finset.mul_sum, e2, e3]`. Establish `hm` using `hmean j`. Rewrite `hm` using `[hKQc]`. Establish `hsplit : ((Module.finrank K K₁ : ℝ) * ∑ τ : K →+* ℂ, Real.log (supN τ ((θ j : M) : V)) + Carch * (Module.finrank ℚ K₁ : ℝ)) / (Module.finrank ℚ K₁ : ℝ) = (∑ τ : K →+* ℂ, Real.log (supN τ ((θ j : M) : V))) / (Module.finrank ℚ K : ℝ) + Carch`.

Rewrite using `[htower]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hsplit]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsumj : ∑ j : Fin ρ, (∑ σ : InfinitePlace K₁, (σ.mult : ℝ) * b j σ) / (Module.finrank ℚ K₁ : ℝ) ≤ (ρ : ℝ) * (Bθ + Carch)`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Establish `hBdeg : ∑ _i : Fin ρ, Bdeg = (ρ : ℝ) * Bdeg`. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Rewrite `hG` using `[hBdeg]`.

Rewrite using `[hsum, div_div, mul_comm (Module.finrank K K₁ : ℝ), ← htower]`. Use polynomial arithmetic with `[hG, hsumj]`.
-/
theorem qcoreGlobal_holds : QCoreGlobalStatement := by
  intro K K₁ V _ _ _ _ _ _ _ _ M ρ θ c hD s hs supN a Bθ Carch Bdeg hconj hmean harch hdeg
  classical
  set D := detCT c θ with hDdef
  let F : HeightOneSpectrum (𝓞 K₁) → ℝ := fun w => (ordAt w D : ℝ) + ∑ i, s i w
  have hordfin : (Function.support fun w : HeightOneSpectrum (𝓞 K₁) => (ordAt w D : ℝ)).Finite := by
    refine (finite_ordAt hD).subset fun w hw => ?_
    have hpos : (0 : ℝ) < logN w := Real.log_pos (one_lt_absNorm_real w)
    simp only [Function.mem_support] at hw ⊢
    exact mul_ne_zero hw hpos.ne'
  have hFfin : (Function.support F).Finite := by
    refine (hordfin.union (Set.finite_iUnion fun i => hs i)).subset fun w hw => ?_
    by_contra hnot
    simp only [Set.mem_union, Set.mem_iUnion, Function.mem_support, not_or, not_exists,
      not_not] at hnot
    apply hw
    simp [F, hnot.1, hnot.2]
  obtain ⟨hfinsupp, hregroup⟩ := finsum_regroup (K := K) F hFfin
  have hnn : ∀ la, nnFun (K := K) D s la =
      (∑ᶠ w : {w // LiesOver w la}, (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w.1) /
        (Module.finrank K K₁ : ℝ) := fun la => rfl
  have hK₁K : (0 : ℝ) < Module.finrank K K₁ := by
    have : Module.Finite K K₁ := Module.Finite.of_restrictScalars_finite ℚ K K₁
    exact_mod_cast Module.finrank_pos
  have hKQ : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have htower : (Module.finrank ℚ K₁ : ℝ) = Module.finrank ℚ K * Module.finrank K K₁ := by
    exact_mod_cast (Module.finrank_mul_finrank ℚ K K₁).symm
  refine ⟨hfinsupp.subset fun la hla => by
    rw [Function.mem_support, hnn] at hla
    intro h; apply hla; simp [h], ?_⟩

  have hsum : (∑ᶠ la : HeightOneSpectrum (𝓞 K), nnFun (K := K) D s la * logN la) =
      (∑ᶠ w, F w * logN w) / (Module.finrank K K₁ : ℝ) := by
    have hfin2 : (Function.support fun la : HeightOneSpectrum (𝓞 K) =>
        (∑ᶠ w : {w // LiesOver w la}, (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w.1) * logN la).Finite :=
      hfinsupp.subset fun la hla => by
        rw [Function.mem_support] at hla ⊢
        intro h; apply hla; rw [h, zero_mul]
    rw [← hregroup, div_eq_mul_inv, finsum_mul]
    refine finsum_congr fun la => ?_
    rw [hnn]; ring

  let m : Matrix (Fin ρ) (Fin ρ) K₁ := Matrix.of fun i j => c i ((1 : K₁) ⊗ₜ[K] ((θ j : M) : V))
  have hmD : m.det = D := rfl
  let b : Fin ρ → InfinitePlace K₁ → ℝ := fun j σ =>
    Real.log (supN (σ.embedding.comp (algebraMap K K₁)) ((θ j : M) : V)) + Carch
  have hG := globalQuot_holds K₁ ρ m (by rw [hmD]; exact hD) s (fun _ => 0) a b (fun _ => Bdeg) 0 hs
    (by simp) (fun σ i j hij => harch σ i j hij) hdeg (by simp)
  have hLHS : (∑ᶠ w, ((ordAt w m.det : ℝ) + ∑ i, s i w + (ρ : ℝ) * (fun _ => (0 : ℝ)) w) * logN w) =
      ∑ᶠ w, F w * logN w := finsum_congr fun w => by simp [F, hmD]
  rw [hLHS] at hG
  have hKQc : (Fintype.card (K →+* ℂ) : ℝ) = Module.finrank ℚ K := by
    exact_mod_cast Embeddings.card K ℂ
  have hbj : ∀ j, (∑ σ : InfinitePlace K₁, (σ.mult : ℝ) * b j σ) / (Module.finrank ℚ K₁ : ℝ) ≤
      Bθ + Carch := by
    intro j
    have e0 : ∀ σ : InfinitePlace K₁, (σ.mult : ℝ) * b j σ =
        (σ.mult : ℝ) * Real.log (supN (σ.embedding.comp (algebraMap K K₁)) ((θ j : M) : V)) +
          Carch * (σ.mult : ℝ) := fun σ => by simp only [b]; ring
    have e2 := sum_places_restrict (K := K) (K₁ := K₁)
      (fun τ => Real.log (supN τ ((θ j : M) : V))) (fun τ => by rw [hconj])
    have e3 : (∑ σ : InfinitePlace K₁, (σ.mult : ℝ)) = Module.finrank ℚ K₁ := by
      exact_mod_cast InfinitePlace.sum_mult_eq
    rw [Finset.sum_congr rfl (fun σ _ => e0 σ), Finset.sum_add_distrib, ← Finset.mul_sum, e2, e3]
    have hm := hmean j
    rw [hKQc] at hm
    have hsplit : ((Module.finrank K K₁ : ℝ) * ∑ τ : K →+* ℂ, Real.log (supN τ ((θ j : M) : V)) +
        Carch * (Module.finrank ℚ K₁ : ℝ)) / (Module.finrank ℚ K₁ : ℝ) =
        (∑ τ : K →+* ℂ, Real.log (supN τ ((θ j : M) : V))) / (Module.finrank ℚ K : ℝ) + Carch := by
      rw [htower]; field_simp
    rw [hsplit]; linarith
  have hsumj : ∑ j : Fin ρ, (∑ σ : InfinitePlace K₁, (σ.mult : ℝ) * b j σ) /
      (Module.finrank ℚ K₁ : ℝ) ≤ (ρ : ℝ) * (Bθ + Carch) := by
    calc _ ≤ ∑ _j : Fin ρ, (Bθ + Carch) := Finset.sum_le_sum fun j _ => hbj j
      _ = (ρ : ℝ) * (Bθ + Carch) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hBdeg : ∑ _i : Fin ρ, Bdeg = (ρ : ℝ) * Bdeg := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hBdeg] at hG
  rw [hsum, div_div, mul_comm (Module.finrank K K₁ : ℝ), ← htower]
  nlinarith [hG, hsumj]

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
