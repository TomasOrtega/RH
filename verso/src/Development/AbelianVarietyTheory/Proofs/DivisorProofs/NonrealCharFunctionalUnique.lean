import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFullRankModuloTranslates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatSumSplitTensor
open GlobalTheory.WeilM GlobalTheory.SplitFlip
open scoped Matrix

noncomputable section
namespace GlobalTheory.LineZeroForm

open Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a b : ℕ}

def fstT (Y : Matrix (Fin a) (Fin (a + b)) k) : Matrix (Fin a) (Fin a) k :=
  (toCols₁ (Y.submatrix id finSumFinEquiv))ᵀ

def snd (Y : Matrix (Fin a) (Fin (a + b)) k) : Matrix (Fin a) (Fin b) k :=
  toCols₂ (Y.submatrix id finSumFinEquiv)

def glue (q : Matrix (Fin a) (Fin a) k × Matrix (Fin a) (Fin b) k) : Matrix (Fin a) (Fin (a + b)) k :=
  (fromCols q.1ᵀ q.2).submatrix id finSumFinEquiv.symm

/- English proof (translation)
Simplify using `[glue, fstT, snd, fromCols_toCols, submatrix_submatrix]`.
-/
theorem glue_fstT_snd (Y : Matrix (Fin a) (Fin (a + b)) k) : glue (fstT Y, snd Y) = Y := by
  simp [glue, fstT, snd, fromCols_toCols, submatrix_submatrix]

/- English proof (translation)
Simplify using `[glue, fstT, submatrix_submatrix]`.
-/
theorem fstT_glue (q : Matrix (Fin a) (Fin a) k × Matrix (Fin a) (Fin b) k) : fstT (glue q) = q.1 := by
  simp [glue, fstT, submatrix_submatrix]

/- English proof (translation)
Simplify using `[glue, snd, submatrix_submatrix]`.
-/
theorem snd_glue (q : Matrix (Fin a) (Fin a) k × Matrix (Fin a) (Fin b) k) : snd (glue q) = q.2 := by
  simp [glue, snd, submatrix_submatrix]

/- English proof (translation)
Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Simplify using `only [glue, submatrix_apply, id, fromCols, of_apply]`. Apply the tactic sequence `cases finSumFinEquiv.symm j <;> simp <;> fun_prop`.
-/
theorem continuous_glue : Continuous (glue (k := k) (a := a) (b := b)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [glue, submatrix_apply, id, fromCols, of_apply]
  cases finSumFinEquiv.symm j <;> simp <;> fun_prop

/- English proof (translation)
Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Simplify using `only [fstT, transpose_apply, toCols₁, of_apply, submatrix_apply, id]`. Use `fun_prop`.
-/
theorem continuous_fstT : Continuous (fstT (k := k) (a := a) (b := b)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [fstT, transpose_apply, toCols₁, of_apply, submatrix_apply, id]
  fun_prop

/- English proof (translation)
Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Simplify using `only [snd, toCols₂, of_apply, submatrix_apply, id]`. Use `fun_prop`.
-/
theorem continuous_snd : Continuous (snd (k := k) (a := a) (b := b)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [snd, toCols₂, of_apply, submatrix_apply, id]
  fun_prop

def box (φ : Matrix (Fin a) (Fin a) k → ℂ) (φ' : Matrix (Fin a) (Fin b) k → ℂ) :
    Matrix (Fin a) (Fin (a + b)) k → ℂ :=
  fun Y => φ (fstT Y) * φ' (snd Y)

/- English proof (translation)
Use `GlobalTheory.SBBlocks.mem_SB_of_support_subset ((h.1.comp_continuous continuous_fstT).mul (h'.1.comp_continuous continuous_snd)) ((h.2.isCompact.prod h'.2.isCompact).image continuous_glue) ?_` and prove the remaining obligations. Introduce `Y hY`. Use `⟨(fstT Y, snd Y), ⟨?_, ?_⟩, glue_fstT_snd Y⟩` and prove the remaining obligations. Conclude with `subset_tsupport _ (left_ne_zero_of_mul hY)`. Conclude with `subset_tsupport _ (right_ne_zero_of_mul hY)`.
-/
theorem box_mem {φ : Matrix (Fin a) (Fin a) k → ℂ} {φ' : Matrix (Fin a) (Fin b) k → ℂ}
    (h : φ ∈ SB (Matrix (Fin a) (Fin a) k)) (h' : φ' ∈ SB (Matrix (Fin a) (Fin b) k)) :
    box φ φ' ∈ SB (Matrix (Fin a) (Fin (a + b)) k) := by
  refine GlobalTheory.SBBlocks.mem_SB_of_support_subset
    ((h.1.comp_continuous continuous_fstT).mul (h'.1.comp_continuous continuous_snd))
    ((h.2.isCompact.prod h'.2.isCompact).image continuous_glue) ?_
  intro Y hY
  refine ⟨(fstT Y, snd Y), ⟨?_, ?_⟩, glue_fstT_snd Y⟩
  · exact subset_tsupport _ (left_ne_zero_of_mul hY)
  · exact subset_tsupport _ (right_ne_zero_of_mul hY)

/- English proof (translation)
Establish `hh : (Ψ ∘ glue) ∈ SB (Matrix (Fin a) (Fin a) k × Matrix (Fin a) (Fin b) k)`. Use `GlobalTheory.SBBlocks.mem_SB_of_support_subset (hΨ.1.comp_continuous continuous_glue) (hΨ.2.isCompact.image (continuous_fstT.prodMk continuous_snd)) ?_` and prove the remaining obligations. Introduce `q hq`. Conclude with `⟨glue q, subset_tsupport _ hq, Prod.ext (fstT_glue q) (snd_glue q)⟩`. Take `⟨m, p, q, hp, hq, he⟩` from `GlobalTheory.SBBlocks.prod_decomp _ hh`.

Use `⟨m, p, q, hp, hq, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `Y`. Rewrite using `[Finset.sum_apply]`. Use `he (fstT Y) (snd Y)` as an intermediate fact. Simplify `this` using `[glue_fstT_snd, box]`.
-/
theorem exists_sum_box (Ψ : Matrix (Fin a) (Fin (a + b)) k → ℂ) (hΨ : Ψ ∈ SB (Matrix (Fin a) (Fin (a + b)) k)) :
    ∃ (m : ℕ) (p : Fin m → Matrix (Fin a) (Fin a) k → ℂ) (q : Fin m → Matrix (Fin a) (Fin b) k → ℂ),
      (∀ j, p j ∈ SB (Matrix (Fin a) (Fin a) k)) ∧ (∀ j, q j ∈ SB (Matrix (Fin a) (Fin b) k)) ∧
      Ψ = ∑ j, box (p j) (q j) := by
  have hh : (Ψ ∘ glue) ∈ SB (Matrix (Fin a) (Fin a) k × Matrix (Fin a) (Fin b) k) := by
    refine GlobalTheory.SBBlocks.mem_SB_of_support_subset (hΨ.1.comp_continuous continuous_glue)
      (hΨ.2.isCompact.image (continuous_fstT.prodMk continuous_snd)) ?_
    intro q hq
    exact ⟨glue q, subset_tsupport _ hq, Prod.ext (fstT_glue q) (snd_glue q)⟩
  obtain ⟨m, p, q, hp, hq, he⟩ := GlobalTheory.SBBlocks.prod_decomp _ hh
  refine ⟨m, p, q, hp, hq, ?_⟩
  funext Y
  rw [Finset.sum_apply]
  have := he (fstT Y) (snd Y)
  simpa [glue_fstT_snd, box] using this

abbrev diagR (g : GL (Fin a) k) : Matrix (Fin (a + b)) (Fin (a + b)) k :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g.1 0 0 (1 : Matrix (Fin b) (Fin b) k))

/- English proof (translation)
Rewrite using `[show (Y * diagR g : Matrix (Fin a) (Fin (a + b)) k) = @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid Y (diagR g) from rfl]`. Rewrite using `[Matrix.submatrix_mul _ _ _ finSumFinEquiv _ finSumFinEquiv.bijective]`. Establish `hR : (diagR g).submatrix finSumFinEquiv finSumFinEquiv = fromBlocks g.1 0 0 (1 : Matrix (Fin b) (Fin b) k)`. Simplify using `[diagR, reindex_apply, submatrix_submatrix]`. Rewrite using `[hR]`.

Use `conv_lhs => rw [← fromCols_toCols (Y.submatrix id finSumFinEquiv)]`. Rewrite using `[fromCols_mul_fromBlocks]`. Simplify using `only [Matrix.mul_zero, Matrix.mul_one, add_zero, zero_add]`.
-/
theorem submatrix_mul_diagR (Y : Matrix (Fin a) (Fin (a + b)) k) (g : GL (Fin a) k) :
    (Y * diagR g : Matrix (Fin a) (Fin (a + b)) k).submatrix id finSumFinEquiv =
      fromCols (toCols₁ (Y.submatrix id finSumFinEquiv) * g.1) (toCols₂ (Y.submatrix id finSumFinEquiv)) := by
  rw [show (Y * diagR g : Matrix (Fin a) (Fin (a + b)) k) =
      @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid Y (diagR g) from rfl]
  rw [Matrix.submatrix_mul _ _ _ finSumFinEquiv _ finSumFinEquiv.bijective]
  have hR : (diagR g).submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks g.1 0 0 (1 : Matrix (Fin b) (Fin b) k) := by
    simp [diagR, reindex_apply, submatrix_submatrix]
  rw [hR]
  conv_lhs => rw [← fromCols_toCols (Y.submatrix id finSumFinEquiv)]
  rw [fromCols_mul_fromBlocks]
  simp only [Matrix.mul_zero, Matrix.mul_one, add_zero, zero_add]

/- English proof (translation)
Rewrite using `[fstT, submatrix_mul_diagR, toCols₁_fromCols, transpose_mul, fstT]`.
-/
theorem fstT_mul (Y : Matrix (Fin a) (Fin (a + b)) k) (g : GL (Fin a) k) :
    fstT (Y * diagR g) = g.1ᵀ * fstT Y := by
  rw [fstT, submatrix_mul_diagR, toCols₁_fromCols, transpose_mul, fstT]

/- English proof (translation)
Rewrite using `[snd, submatrix_mul_diagR, toCols₂_fromCols, snd]`.
-/
theorem snd_mul (Y : Matrix (Fin a) (Fin (a + b)) k) (g : GL (Fin a) k) :
    snd (Y * diagR g) = snd Y := by
  rw [snd, submatrix_mul_diagR, toCols₂_fromCols, snd]

end GlobalTheory.LineZeroForm

noncomputable section
namespace GlobalTheory.LineZeroForm

open Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def absChar (w : ℝ) : kˣ →* ℂˣ where
  toFun x := Units.mk0 (apow x (w : ℂ)) (apow_ne_zero x _)
  map_one' := Units.ext (by simp)
  map_mul' x y := Units.ext (by simp [apow_mul])

/- English proof (translation)
Use `⟨_, ?_, (Complex.ofReal_cpow (le_of_lt (by exact_mod_cast GlobalTheory.SplitWeil.nabs_pos k x)) w).symm⟩` and prove the remaining obligations. Conclude with `(Real.rpow_pos_of_pos (by exact_mod_cast GlobalTheory.SplitWeil.nabs_pos k x) w).ne'`.
-/
theorem apow_eq_ofReal (x : kˣ) (w : ℝ) : ∃ t : ℝ, t ≠ 0 ∧ apow x (w : ℂ) = (t : ℂ) := by
  refine ⟨_, ?_, (Complex.ofReal_cpow (le_of_lt (by exact_mod_cast GlobalTheory.SplitWeil.nabs_pos k x)) w).symm⟩
  exact (Real.rpow_pos_of_pos (by exact_mod_cast GlobalTheory.SplitWeil.nabs_pos k x) w).ne'

/- English proof (translation)
Take `⟨t, -, ht⟩` from `apow_eq_ofReal x w`. Rewrite using `[ht, Complex.conj_ofReal]`.
-/
theorem conj_apow (x : kˣ) (w : ℝ) : starRingEnd ℂ (apow x (w : ℂ)) = apow x (w : ℂ) := by
  obtain ⟨t, -, ht⟩ := apow_eq_ofReal x w
  rw [ht, Complex.conj_ofReal]

def twist (χ : kˣ →* ℂˣ) (w : ℝ) : kˣ →* ℂˣ :=
  ((Units.map (starRingEnd ℂ).toMonoidHom).comp (χ * absChar w))⁻¹

/- English proof (translation)
Simplify using `[twist, absChar]`.
-/
theorem twist_val (χ : kˣ →* ℂˣ) (w : ℝ) (x : kˣ) :
    ((twist χ w x : ℂˣ) : ℂ) = (starRingEnd ℂ ((χ x : ℂ) * apow x (w : ℂ)))⁻¹ := by
  simp [twist, absChar]

/- English proof (translation)
Introduce `m hm r hr`. Take `⟨t, ht0, ht⟩` from `apow_eq_ofReal ϖ w`. Establish `hu : ((χ ϖ : ℂ)) ≠ 0` using `Units.ne_zero _`. Rewrite `hr` using `[twist_val, ht]`. Establish `hr'` using `congrArg (starRingEnd ℂ) hr`.

Simplify using `only [map_pow, map_inv₀, map_mul, Complex.conj_conj, Complex.conj_ofReal] at hr'`. Establish `hr0 : (r : ℂ) ≠ 0` using `by rw [← hr']; exact pow_ne_zero _ (inv_ne_zero (mul_ne_zero hu (by exact_mod_cast ht0)))`. Apply `hχ m hm ((r * t ^ m)⁻¹)` to reduce the goal to its premises. Use `push_cast`. Rewrite using `[← hr', inv_pow, mul_pow]`.

Establish `ht' : (t : ℂ) ≠ 0` using `by exact_mod_cast ht0`. Clear the denominators using the available nonvanishing facts.
-/
theorem twist_pow_ne_real (χ : kˣ →* ℂˣ) (w : ℝ) (ϖ : kˣ)
    (hχ : ∀ m : ℕ, 0 < m → ∀ r : ℝ, ((χ ϖ : ℂ)) ^ m ≠ (r : ℂ)) :
    ∀ m : ℕ, 0 < m → ∀ r : ℝ, ((twist χ w ϖ : ℂ)) ^ m ≠ (r : ℂ) := by
  intro m hm r hr
  obtain ⟨t, ht0, ht⟩ := apow_eq_ofReal ϖ w
  have hu : ((χ ϖ : ℂ)) ≠ 0 := Units.ne_zero _
  rw [twist_val, ht] at hr
  have hr' := congrArg (starRingEnd ℂ) hr
  simp only [map_pow, map_inv₀, map_mul, Complex.conj_conj, Complex.conj_ofReal] at hr'
  have hr0 : (r : ℂ) ≠ 0 := by rw [← hr']; exact pow_ne_zero _ (inv_ne_zero (mul_ne_zero hu (by exact_mod_cast ht0)))
  apply hχ m hm ((r * t ^ m)⁻¹)
  push_cast
  rw [← hr', inv_pow, mul_pow]
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
  field_simp

end GlobalTheory.LineZeroForm

namespace GlobalTheory.LineZeroForm
open Matrix

/- English proof (translation)
Introduce `hr`. Establish `hv : (fstT Y) *ᵥ ℓ = 0`. Use function extensionality and compare the values at `i`. Use `congrFun hY (finSumFinEquiv (Sum.inl i))` as an intermediate fact. Simplify `this` using `[fstT, Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm, toCols₁]`.

Establish `hk : LinearMap.ker (fstT Y).mulVecLin ≠ ⊥`. Introduce `h`. Apply `hℓ` to reduce the goal to its premises. Use `LinearMap.ker_eq_bot.1 h` as an intermediate fact. Apply `this` to reduce the goal to its premises.

Simplify using `[Matrix.mulVecLin_apply, hv]`. Establish `h1` using `LinearMap.finrank_range_add_finrank_ker (fstT Y).mulVecLin`. Establish `h2 : 0 < Module.finrank k (LinearMap.ker (fstT Y).mulVecLin)` using `Nat.pos_of_ne_zero (mt Submodule.finrank_eq_zero.1 hk)`. Establish `h3 : (fstT Y).rank = Module.finrank k (LinearMap.range (fstT Y).mulVecLin)` using `rfl`. Rewrite `h1` using `[Module.finrank_fin_fun]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem rank_fstT_ne {k : Type} [Field k] {a b : ℕ} (ℓ : Fin a → k) (hℓ : ℓ ≠ 0)
    (Y : Matrix (Fin a) (Fin (a + b)) k) (hY : Matrix.vecMul ℓ Y = 0) : (fstT Y).rank ≠ a := by
  intro hr
  have hv : (fstT Y) *ᵥ ℓ = 0 := by
    funext i
    have := congrFun hY (finSumFinEquiv (Sum.inl i))
    simpa [fstT, Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm, toCols₁] using this
  have hk : LinearMap.ker (fstT Y).mulVecLin ≠ ⊥ := by
    intro h
    apply hℓ
    have := LinearMap.ker_eq_bot.1 h
    apply this
    simp [Matrix.mulVecLin_apply, hv]
  have h1 := LinearMap.finrank_range_add_finrank_ker (fstT Y).mulVecLin
  have h2 : 0 < Module.finrank k (LinearMap.ker (fstT Y).mulVecLin) :=
    Nat.pos_of_ne_zero (mt Submodule.finrank_eq_zero.1 hk)
  have h3 : (fstT Y).rank = Module.finrank k (LinearMap.range (fstT Y).mulVecLin) := rfl
  rw [Module.finrank_fin_fun] at h1
  omega

/- English proof (translation)
Introduce `k _ _ _ _ a b χ ϖ hϖ _ hχ s ℓ hℓ L hZ hL`. Set `w : ℝ` to `s + (a : ℝ) / 2`. Set `ν` to `twist χ w`. Establish `hν` using `twist_pow_ne_real χ w ϖ hχ`. Establish `key : ∀ φ' (hφ' : φ' ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin b) k)) φ (hφ : φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin a) k)), L ⟨box φ φ', box_mem hφ hφ'⟩ = 0`.

Introduce `φ' hφ'`. Set `T : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin a) k) →ₗ[ℂ] GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k)` to `{ toFun := fun φ => ⟨box φ.1 φ', box_mem φ.2 hφ'⟩ map_add' := fun x y => Subtype.ext (funext fun Y => by simp [box, add_mul]) map_smul' := fun c x => Subtype.ext (funext fun Y => by simp [box, mul_assoc]) }`. Set `μ` to `L.comp T`. Establish `hN : GlobalTheory.RankStrata.Nsp k (Fin a) (Fin a) ν ≤ (LinearMap.ker μ).map (GlobalTheory.WeilM.SB _).subtype`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨g, Ψ', hΨ', rfl⟩`. Use `⟨⟨_, omB_mem_SB ν ν g 1 hΨ'⟩ - ⟨Ψ', hΨ'⟩, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, LinearMap.mem_ker, map_sub, sub_eq_zero]`. Establish `hmem : (fun Y => box Ψ' φ' (Y * diagR g)) ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k)`. Establish `: (fun Y => box Ψ' φ' (Y * diagR g)) = box (fun X => Ψ' ((g.1)ᵀ * X)) φ'`.

Use function extensionality and compare the values at `Y`. Simplify using `only [box]`. Rewrite using `[fstT_mul, snd_mul]`. Rewrite using `[this]`. Use `box_mem ?_ hφ'` and prove the remaining obligations.

Use `comp_mul_mem_SB (invT g)⁻¹ (1 : GL (Fin a) k) hΨ'` as an intermediate fact. Rewrite `this` using `[invT_inv_val]`. Simplify using `only [Units.val_one, Matrix.mul_one] at this`. Conclude with `this`. Establish `h1` using `hL g (T ⟨Ψ', hΨ'⟩) ⟨_, hmem⟩ rfl`.

Establish `h2 : T ⟨_, omB_mem_SB ν ν g 1 hΨ'⟩ = (((ν (gdet g) : ℂ) * apow (gdet g) ((a : ℂ) / 2)) • (⟨_, hmem⟩ : GlobalTheory.WeilM.SB _))`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `Y`. Use `show omB ν ν g 1 Ψ' (fstT Y) * φ' (snd Y) = ((ν (gdet g) : ℂ) * apow (gdet g) ((a : ℂ) / 2)) * (Ψ' (fstT (Y * diagR g)) * φ' (snd (Y * diagR g)))`. Rewrite using `[fstT_mul, snd_mul]`.

Simplify using `[omB, gdet]`. Expand and normalize the polynomial expressions, which then agree. Use `show L (T _) = L (T _)`. Rewrite using `[h2, LinearMap.map_smulₛₗ, h1, smul_eq_mul, ← mul_assoc, ← mul_assoc]`. Use `conv_rhs => rw [← one_mul (L (T _))]`.

Use `congr 1`. Establish `hc : ∀ x : kˣ, starRingEnd ℂ ((ν x : ℂ) * apow x ((a : ℂ) / 2)) * (χ x : ℂ) * apow x (s : ℂ) = 1`. Introduce `x`. Establish `e1 : ((a : ℂ) / 2) = (((a : ℝ) / 2 : ℝ) : ℂ)` using `by push_cast; ring`. Establish `e2 : apow x (w : ℂ) = apow x (s : ℂ) * apow x ((a : ℂ) / 2)`.

Rewrite using `[← apow_add]`. Use `congr 1`. Simplify using `[w]`. Rewrite using `[map_mul, twist_val, map_inv₀, Complex.conj_conj, e1, conj_apow, ← e1, e2]`. Use `apow_ne_zero x (s : ℂ)` as an intermediate fact.

Use `apow_ne_zero x ((a : ℂ) / 2)` as an intermediate fact. Establish `: (χ x : ℂ) ≠ 0` using `Units.ne_zero _`. Clear the denominators using the available nonvanishing facts. Conclude with `hc _`. Introduce `φ hφ`.

Take `⟨Ψ₀, h0SB, h0rk, hdiff⟩` from `GlobalTheory.RankStrata.exists_fullRank_sub_mem_span k a a ν ϖ hϖ hν φ hφ`. Take `⟨z, hz, hzeq⟩` from `hN hdiff`. Establish `hz' : z = ⟨φ, hφ⟩ - ⟨Ψ₀, h0SB⟩` using `Subtype.ext hzeq`. Establish `hμ0 : μ ⟨Ψ₀, h0SB⟩ = 0`. Apply `hZ` to reduce the goal to its premises.

Introduce `Y hY`. Use `show Ψ₀ (fstT Y) * φ' (snd Y) = 0`. Rewrite using `[h0rk _ (rank_fstT_ne ℓ hℓ Y hY), zero_mul]`. Rewrite `hz` using `[SetLike.mem_coe, LinearMap.mem_ker, hz', map_sub, hμ0, sub_zero]`. Conclude with `hz`.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce and unpack `⟨Ψ, hΨ⟩`. Take `⟨m, p, q, hp, hq, he⟩` from `exists_sum_box Ψ hΨ`. Establish `: (⟨Ψ, hΨ⟩ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k)) = ∑ j, ⟨box (p j) (q j), box_mem (hp j) (hq j)⟩`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[Submodule.coe_sum]`. Conclude with `he`. Rewrite using `[this, map_sum]`. Simplify using `[key _ (hq _) _ (hp _)]`.
-/
theorem conjForm_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → GlobalTheory.SmGL.IsSmoothChar χ →
    (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((χ ϖ : ℂ)) ^ m ≠ (r : ℂ)) → ∀ (s : ℝ) (ℓ : Fin a → k), ℓ ≠ 0 →
    ∀ L : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) →ₗ⋆[ℂ] ℂ,
      (∀ Ψ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k), (∀ Y : Matrix (Fin a) (Fin (a + b)) k, Matrix.vecMul ℓ Y = 0 → Ψ.1 Y = 0) → L Ψ = 0) →
      (∀ (g : GL (Fin a) k) (Ψ Ψ' : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k)),
        Ψ'.1 = (fun Y => Ψ.1 (Y * (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g.1 0 0 (1 : Matrix (Fin b) (Fin b) k))))) →
        L Ψ' = ((χ (Matrix.GeneralLinearGroup.det g) : ℂ) * GlobalTheory.SplitFlip.apow (Matrix.GeneralLinearGroup.det g) (s : ℂ)) * L Ψ) →
      L = 0 := by
  intro k _ _ _ _ a b χ ϖ hϖ _ hχ s ℓ hℓ L hZ hL
  classical
  let w : ℝ := s + (a : ℝ) / 2
  let ν := twist χ w
  have hν := twist_pow_ne_real χ w ϖ hχ
  have key : ∀ φ' (hφ' : φ' ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin b) k)) φ (hφ : φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin a) k)),
      L ⟨box φ φ', box_mem hφ hφ'⟩ = 0 := by
    intro φ' hφ'
    let T : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin a) k) →ₗ[ℂ] GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) :=
      { toFun := fun φ => ⟨box φ.1 φ', box_mem φ.2 hφ'⟩
        map_add' := fun x y => Subtype.ext (funext fun Y => by simp [box, add_mul])
        map_smul' := fun c x => Subtype.ext (funext fun Y => by simp [box, mul_assoc]) }
    let μ := L.comp T
    have hN : GlobalTheory.RankStrata.Nsp k (Fin a) (Fin a) ν ≤ (LinearMap.ker μ).map (GlobalTheory.WeilM.SB _).subtype := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, Ψ', hΨ', rfl⟩
      refine ⟨⟨_, omB_mem_SB ν ν g 1 hΨ'⟩ - ⟨Ψ', hΨ'⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, sub_eq_zero]
      have hmem : (fun Y => box Ψ' φ' (Y * diagR g)) ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) := by
        have : (fun Y => box Ψ' φ' (Y * diagR g)) =
            box (fun X => Ψ' ((g.1)ᵀ * X)) φ' := by
          funext Y; simp only [box]; rw [fstT_mul, snd_mul]
        rw [this]
        refine box_mem ?_ hφ'
        have := comp_mul_mem_SB (invT g)⁻¹ (1 : GL (Fin a) k) hΨ'
        rw [invT_inv_val] at this
        simp only [Units.val_one, Matrix.mul_one] at this
        exact this
      have h1 := hL g (T ⟨Ψ', hΨ'⟩) ⟨_, hmem⟩ rfl
      have h2 : T ⟨_, omB_mem_SB ν ν g 1 hΨ'⟩ =
          (((ν (gdet g) : ℂ) * apow (gdet g) ((a : ℂ) / 2)) • (⟨_, hmem⟩ : GlobalTheory.WeilM.SB _)) := by
        apply Subtype.ext
        funext Y
        show omB ν ν g 1 Ψ' (fstT Y) * φ' (snd Y) =
          ((ν (gdet g) : ℂ) * apow (gdet g) ((a : ℂ) / 2)) * (Ψ' (fstT (Y * diagR g)) * φ' (snd (Y * diagR g)))
        rw [fstT_mul, snd_mul]
        simp [omB, gdet]
        ring
      show L (T _) = L (T _)
      rw [h2, LinearMap.map_smulₛₗ, h1, smul_eq_mul, ← mul_assoc, ← mul_assoc]
      conv_rhs => rw [← one_mul (L (T _))]
      congr 1
      have hc : ∀ x : kˣ, starRingEnd ℂ ((ν x : ℂ) * apow x ((a : ℂ) / 2)) * (χ x : ℂ) * apow x (s : ℂ) = 1 := by
        intro x
        have e1 : ((a : ℂ) / 2) = (((a : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
        have e2 : apow x (w : ℂ) = apow x (s : ℂ) * apow x ((a : ℂ) / 2) := by
          rw [← apow_add]; congr 1; simp [w]
        rw [map_mul, twist_val, map_inv₀, Complex.conj_conj, e1, conj_apow, ← e1, e2]
        have := apow_ne_zero x (s : ℂ)
        have := apow_ne_zero x ((a : ℂ) / 2)
        have : (χ x : ℂ) ≠ 0 := Units.ne_zero _
        field_simp
      exact hc _
    intro φ hφ
    obtain ⟨Ψ₀, h0SB, h0rk, hdiff⟩ := GlobalTheory.RankStrata.exists_fullRank_sub_mem_span k a a ν ϖ hϖ hν φ hφ
    obtain ⟨z, hz, hzeq⟩ := hN hdiff
    have hz' : z = ⟨φ, hφ⟩ - ⟨Ψ₀, h0SB⟩ := Subtype.ext hzeq
    have hμ0 : μ ⟨Ψ₀, h0SB⟩ = 0 := by
      apply hZ
      intro Y hY
      show Ψ₀ (fstT Y) * φ' (snd Y) = 0
      rw [h0rk _ (rank_fstT_ne ℓ hℓ Y hY), zero_mul]
    rw [SetLike.mem_coe, LinearMap.mem_ker, hz', map_sub, hμ0, sub_zero] at hz
    exact hz
  apply LinearMap.ext
  rintro ⟨Ψ, hΨ⟩
  obtain ⟨m, p, q, hp, hq, he⟩ := exists_sum_box Ψ hΨ
  have : (⟨Ψ, hΨ⟩ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k)) =
      ∑ j, ⟨box (p j) (q j), box_mem (hp j) (hq j)⟩ := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact he
  rw [this, map_sum]
  simp [key _ (hq _) _ (hp _)]

end GlobalTheory.LineZeroForm
