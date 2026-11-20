import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingOfBall

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical nonZeroDivisors

noncomputable section

namespace GlobalTheory.IdealFund

open GlobalTheory.HomCovolume

/- English proof (translation)
Take `⟨L, hL, hcov⟩` from `exists_idealLat K hK a ha`. Set `g : ι ≃ InfinitePlace K` to `Equiv.ofBijective (fun v => InfinitePlace.mk (σ v)) ((Function.bijective_iff_existsUnique _).2 hσ)`. Establish `hg : ∀ w, InfinitePlace.mk (σ (g.symm w)) = w` using `fun w => g.apply_symm_apply w`. Establish `hκ : ∀ w : InfinitePlace K, ∃ κ : ℂ ≃ₗᵢ[ℝ] ℂ, ∀ t, κ (σ (g.symm w) t) = w.embedding t`. Introduce `w`.

Establish `h1 : InfinitePlace.mk (σ (g.symm w)) = InfinitePlace.mk w.embedding`. Rewrite using `[hg, InfinitePlace.mk_embedding]`. Break down `InfinitePlace.mk_eq_iff.1 h1 with h | h` into its components or cases. Conclude with `⟨LinearIsometryEquiv.refl _ _, fun t => by rw [← h]; rfl⟩`. Conclude with `⟨Complex.conjLIE, fun t => by rw [← h]; rfl⟩`.

Use `choose κ hκ using hκ`. Set `e₀ : (ι → ℂ) ≃ₗ[ℝ] (InfinitePlace K → ℂ)` to `{ toFun := fun z w => κ w (z (g.symm w)), invFun := fun x v => (κ (g v)).symm (x (g v)) map_add' := fun _ _ => funext fun w => by simp map_smul' := fun _ _ => funext fun w => by simp only [Pi.smul_apply, map_smul, RingHom.id_apply] left_inv := fun _ => funext fun v => by simp rig …`. Establish `hcard : Fintype.card ι = Fintype.card (InfinitePlace K)` using `Fintype.card_congr g`. Establish `hmp : MeasurePreserving e₀.toContinuousLinearEquiv volume volume`. Use `measurePreserving_of_ball _ _ _ (fun x => ?_) ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `‖fun w => κ w (x (g.symm w))‖ ≤ 1 ↔ _`. Simplify using `only [pi_norm_le_iff_of_nonneg zero_le_one, LinearIsometryEquiv.norm_map]`. Conclude with `⟨fun h v => by simpa using h (g v), fun h w => h _⟩`. Simplify using `[volume_pi_closedBall _ zero_le_one, hcard]`. Use `⟨ZLattice.comap ℝ L e₀.toContinuousLinearEquiv.toLinearMap, fun z => ?_, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `e₀ z ∈ L ↔ _`. Rewrite using `[hL]`. Use `exists_congr fun y => and_congr Iff.rfl ⟨fun h v => ?_, fun h w => ?_⟩` and prove the remaining obligations. Establish `h1 : κ (g v) (z (g.symm (g v))) = (g v).embedding y` using `h (g v)`. Rewrite `h1` using `[← hκ]`.

Simplify using `using h1`. Express the relevant statement in the definitionally equal form `κ w (z (g.symm w)) = _`. Rewrite using `[h, hκ]`. Rewrite using `[hcard]`. Conclude with `HasCov.of_measurePreserving _ hmp (fun _ => Iff.rfl) hcov`.
-/
theorem exists_lat (K : Type) [Field K] [NumberField K] (hK : IsTotallyComplex K) (ι : Type) [Fintype ι]
    (σ : ι → (K →+* ℂ)) (hσ : ∀ w : InfinitePlace K, ∃! v, InfinitePlace.mk (σ v) = w)
    (a : FractionalIdeal (𝓞 K)⁰ K) (ha : a ≠ 0) :
    ∃ L : Submodule ℤ (ι → ℂ), (∀ z, z ∈ L ↔ ∃ y ∈ a, ∀ v, z v = σ v y) ∧
      HasCov volume L ((FractionalIdeal.absNorm a : ℝ) * Formalism.HermitianLatticesTheory.vInv K ^ Fintype.card ι) := by
  obtain ⟨L, hL, hcov⟩ := exists_idealLat K hK a ha
  let g : ι ≃ InfinitePlace K := Equiv.ofBijective (fun v => InfinitePlace.mk (σ v))
    ((Function.bijective_iff_existsUnique _).2 hσ)
  have hg : ∀ w, InfinitePlace.mk (σ (g.symm w)) = w := fun w => g.apply_symm_apply w
  have hκ : ∀ w : InfinitePlace K, ∃ κ : ℂ ≃ₗᵢ[ℝ] ℂ, ∀ t, κ (σ (g.symm w) t) = w.embedding t := by
    intro w
    have h1 : InfinitePlace.mk (σ (g.symm w)) = InfinitePlace.mk w.embedding := by
      rw [hg, InfinitePlace.mk_embedding]
    rcases InfinitePlace.mk_eq_iff.1 h1 with h | h
    · exact ⟨LinearIsometryEquiv.refl _ _, fun t => by rw [← h]; rfl⟩
    · exact ⟨Complex.conjLIE, fun t => by rw [← h]; rfl⟩
  choose κ hκ using hκ
  let e₀ : (ι → ℂ) ≃ₗ[ℝ] (InfinitePlace K → ℂ) :=
    { toFun := fun z w => κ w (z (g.symm w)), invFun := fun x v => (κ (g v)).symm (x (g v))
      map_add' := fun _ _ => funext fun w => by simp
      map_smul' := fun _ _ => funext fun w => by simp only [Pi.smul_apply, map_smul, RingHom.id_apply]
      left_inv := fun _ => funext fun v => by simp
      right_inv := fun _ => funext fun w => by simp }
  have hcard : Fintype.card ι = Fintype.card (InfinitePlace K) := Fintype.card_congr g
  have hmp : MeasurePreserving e₀.toContinuousLinearEquiv volume volume := by
    refine measurePreserving_of_ball _ _ _ (fun x => ?_) ?_
    · change ‖fun w => κ w (x (g.symm w))‖ ≤ 1 ↔ _
      simp only [pi_norm_le_iff_of_nonneg zero_le_one, LinearIsometryEquiv.norm_map]
      exact ⟨fun h v => by simpa using h (g v), fun h w => h _⟩
    · simp [volume_pi_closedBall _ zero_le_one, hcard]
  refine ⟨ZLattice.comap ℝ L e₀.toContinuousLinearEquiv.toLinearMap, fun z => ?_, ?_⟩
  · change e₀ z ∈ L ↔ _
    rw [hL]
    refine exists_congr fun y => and_congr Iff.rfl ⟨fun h v => ?_, fun h w => ?_⟩
    · have h1 : κ (g v) (z (g.symm (g v))) = (g v).embedding y := h (g v)
      rw [← hκ] at h1
      simpa using h1
    · change κ w (z (g.symm w)) = _
      rw [h, hκ]
  · rw [hcard]
    exact HasCov.of_measurePreserving _ hmp (fun _ => Iff.rfl) hcov

/- English proof (translation)
Introduce `K _ _ _ hK ι _ σ hσ 𝔡 n c h𝔡 hc`. Establish `h0 : (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.2 h𝔡`. Take `⟨L₀, hL₀, hcov⟩` from `exists_lat K hK.1 ι σ hσ.2 _ (zpow_ne_zero n h0)`. Set `f : (ι → ℂ) →ₗ[ℝ] (ι → ℂ)` to `LinearMap.pi fun v => (Algebra.lmul ℝ ℂ (c v)⁻¹).comp (LinearMap.proj v)`. Establish `hf : ∀ z v, f z v = (c v)⁻¹ * z v` using `fun _ _ => rfl`.

Establish `hdet : LinearMap.det f = (∏ v, ‖c v‖ ^ 2)⁻¹`. Rewrite using `[LinearMap.det_pi, ← Finset.prod_inv_distrib]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, norm_inv, inv_pow]`. Establish `hpos : 0 < ∏ v, ‖c v‖ ^ 2` using `Finset.prod_pos fun v _ => pow_pos (norm_pos_iff.2 (hc v)) _`.

Set `L : Submodule ℤ (ι → ℂ)` to `L₀.comap (f.restrictScalars ℤ)`. Take `⟨_, _, h⟩` from `HasCov.of_det f (L := L) (by rw [hdet]; exact (inv_pos.2 hpos).ne') (fun _ => Iff.rfl) hcov`. Establish `hL : ∀ z, z ∈ L ↔ ∃ t ∈ ipow 𝔡 n, z = fun v => c v * σ v t`. Introduce `z`. Express the relevant statement in the definitionally equal form `f z ∈ L₀ ↔ _`.

Rewrite using `[hL₀]`. Use `exists_congr fun y => and_congr Iff.rfl ⟨fun h => funext fun v => ?_, fun h v => ?_⟩` and prove the remaining obligations. Rewrite using `[← h, hf, mul_inv_cancel_left₀ (hc v)]`. Rewrite using `[hf, h, inv_mul_cancel_left₀ (hc v)]`. Take `⟨v₀, -⟩` from `(hσ.2 (Classical.arbitrary _)).exists`.

Use `⟨latticeDomain L, measurableSet_latticeDomain L, fun a => ?_, ?_⟩` and prove the remaining obligations. Take `⟨z, hz, hu⟩` from `existsUnique_add_mem_latticeDomain L a`. Take `⟨t, ht, hzt⟩` from `(hL z).1 z.2`. Use `⟨t, ⟨ht, by rw [← hzt, add_comm]; exact hz⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `t' ⟨ht', h'⟩`.

Establish `h1` using `hu ⟨_, (hL _).2 ⟨t', ht', rfl⟩⟩ (by rw [add_comm] at h'; exact h')`. Establish `h2` using `congrFun ((congrArg Subtype.val h1).trans hzt) v₀`. Conclude with `(σ v₀).injective (mul_left_cancel₀ (hc v₀) h2)`. Rewrite `h` using `[ZLattice.covolume_eq_measure_fundamentalDomain _ _ (isAddFundamentalDomain_latticeDomain _ _), measureReal_def, hdet, abs_of_pos (inv_pos.2 hpos), div_inv_eq_mul, map_zpow₀, FractionalIdeal.coeIdeal_absNorm]`. Establish `hfin : volume (latticeDomain L) ≠ ⊤` using `(ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne`.

Rewrite using `[← ENNReal.ofReal_toReal hfin, h]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_fund_ipow : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (ι : Type) [Fintype ι] (σ : ι → (K →+* ℂ)), IsPlaces σ → ∀ (𝔡 : Ideal (𝓞 K)) (n : ℤ) (c : ι → ℂ), 𝔡 ≠ ⊥ → (∀ v, c v ≠ 0) → ∃ F : Set (ι → ℂ), MeasurableSet F ∧ (∀ a : ι → ℂ, ∃! t : K, t ∈ ipow 𝔡 n ∧ ((fun v => c v * σ v t) + a) ∈ F) ∧ volume F = ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv K ^ Fintype.card ι * (Ideal.absNorm 𝔡 : ℝ) ^ n * ∏ v, ‖c v‖ ^ 2) := by
  intro K _ _ _ hK ι _ σ hσ 𝔡 n c h𝔡 hc
  have h0 : (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔡
  obtain ⟨L₀, hL₀, hcov⟩ := exists_lat K hK.1 ι σ hσ.2 _ (zpow_ne_zero n h0)
  let f : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) :=
    LinearMap.pi fun v => (Algebra.lmul ℝ ℂ (c v)⁻¹).comp (LinearMap.proj v)
  have hf : ∀ z v, f z v = (c v)⁻¹ * z v := fun _ _ => rfl
  have hdet : LinearMap.det f = (∏ v, ‖c v‖ ^ 2)⁻¹ := by
    rw [LinearMap.det_pi, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, norm_inv, inv_pow]
  have hpos : 0 < ∏ v, ‖c v‖ ^ 2 := Finset.prod_pos fun v _ => pow_pos (norm_pos_iff.2 (hc v)) _
  let L : Submodule ℤ (ι → ℂ) := L₀.comap (f.restrictScalars ℤ)
  obtain ⟨_, _, h⟩ := HasCov.of_det f (L := L) (by rw [hdet]; exact (inv_pos.2 hpos).ne')
    (fun _ => Iff.rfl) hcov
  have hL : ∀ z, z ∈ L ↔ ∃ t ∈ ipow 𝔡 n, z = fun v => c v * σ v t := by
    intro z
    change f z ∈ L₀ ↔ _
    rw [hL₀]
    refine exists_congr fun y => and_congr Iff.rfl ⟨fun h => funext fun v => ?_, fun h v => ?_⟩
    · rw [← h, hf, mul_inv_cancel_left₀ (hc v)]
    · rw [hf, h, inv_mul_cancel_left₀ (hc v)]
  obtain ⟨v₀, -⟩ := (hσ.2 (Classical.arbitrary _)).exists
  refine ⟨latticeDomain L, measurableSet_latticeDomain L, fun a => ?_, ?_⟩
  · obtain ⟨z, hz, hu⟩ := existsUnique_add_mem_latticeDomain L a
    obtain ⟨t, ht, hzt⟩ := (hL z).1 z.2
    refine ⟨t, ⟨ht, by rw [← hzt, add_comm]; exact hz⟩, ?_⟩
    rintro t' ⟨ht', h'⟩
    have h1 := hu ⟨_, (hL _).2 ⟨t', ht', rfl⟩⟩ (by rw [add_comm] at h'; exact h')
    have h2 := congrFun ((congrArg Subtype.val h1).trans hzt) v₀
    exact (σ v₀).injective (mul_left_cancel₀ (hc v₀) h2)
  · rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _
      (isAddFundamentalDomain_latticeDomain _ _), measureReal_def, hdet, abs_of_pos (inv_pos.2 hpos),
      div_inv_eq_mul, map_zpow₀, FractionalIdeal.coeIdeal_absNorm] at h
    have hfin : volume (latticeDomain L) ≠ ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
    rw [← ENNReal.ofReal_toReal hfin, h]
    congr 1
    push_cast
    ring

end GlobalTheory.IdealFund
