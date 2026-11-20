import Mathlib
import GroundTheory.AutomorphicForms.ReductionFinite
import GroundTheory.AutomorphicForms.ReductionIwasawa
import GroundTheory.AutomorphicForms.ReductionBlock
import GroundTheory.AutomorphicForms.ReductionDirichlet

open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GroundTheory.Automorphic

noncomputable section

namespace Reduction

variable {K : Type*} [Field K] [NumberField K]

def adeleAbs (a : 𝔸[K]) : ℝ :=
  (∏ w : InfinitePlace K, ‖a.1 w‖ ^ w.mult) * ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖a.2 v‖

/- English proof (translation)
The claim follows from `(ideleModule_eq u).symm`.
-/
theorem adeleAbs_units (u : IdeleGroup K) : adeleAbs (u : 𝔸[K]) = ideleModule K u :=
  (ideleModule_eq u).symm

section Two

variable {E : Type*} [NormedField E] {n : ℕ}

/- English proof (translation)
Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using `[h]`. Distinguish the cases in `hk' : k = i'`. Substitute `hk'` using the available equality.

Simplify using `[hk]`. Simplify using `[hk, hk']`.
-/
theorem single_add_single_apply_norm_sq {i i' : Fin n} (h : i ≠ i') (x y : E) (k : Fin n) :
    ‖(Pi.single i x + Pi.single i' y : Fin n → E) k‖ ^ 2 =
      (Pi.single i (‖x‖ ^ 2) : Fin n → ℝ) k + (Pi.single i' (‖y‖ ^ 2) : Fin n → ℝ) k := by
  by_cases hk : k = i
  · subst hk
    simp [h]
  · by_cases hk' : k = i'
    · subst hk'
      simp [hk]
    · simp [hk, hk']

/- English proof (translation)
Rewrite using `[euclidNorm, euclidNorm]`. Use `congr 1`. Repeatedly rewrite using `[single_add_single_apply_norm_sq h]`. Rewrite using `[Finset.sum_add_distrib, Finset.sum_pi_single', Finset.sum_pi_single', Fin.sum_univ_two]`. Simplify using the standard rewrite rules.
-/
theorem euclidNorm_single_add_single {i i' : Fin n} (h : i ≠ i') (x y : E) :
    euclidNorm (Pi.single i x + Pi.single i' y : Fin n → E) = euclidNorm ![x, y] := by
  rw [euclidNorm, euclidNorm]
  congr 1
  simp_rw [single_add_single_apply_norm_sq h]
  rw [Finset.sum_add_distrib, Finset.sum_pi_single', Finset.sum_pi_single', Fin.sum_univ_two]
  simp

/- English proof (translation)
Establish `h2 : ‖![x, y]‖ = max ‖x‖ ‖y‖`. Use `le_antisymm ((pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).2 fun j => ?_) (max_le (norm_le_pi_norm ![x, y] 0) (norm_le_pi_norm ![x, y] 1))` and prove the remaining obligations. Use `fin_cases j`. Conclude with `le_max_left _ _`. Conclude with `le_max_right _ _`.

Rewrite using `[h2]`. Use `le_antisymm ((pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).2 fun k => ?_) (max_le ?_ ?_)` and prove the remaining obligations. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using `[h]`.

Distinguish the cases in `hk' : k = i'`. Substitute `hk'` using the available equality. Simplify using `[hk]`. Simplify using `[hk, hk']`. Use `norm_le_pi_norm (Pi.single i x + Pi.single i' y : Fin n → E) i` as an intermediate fact.

Simplify `this` using `[Pi.single_apply, h]`. Use `norm_le_pi_norm (Pi.single i x + Pi.single i' y : Fin n → E) i'` as an intermediate fact. Simplify `this` using `[Pi.single_apply, h.symm]`.
-/
theorem norm_single_add_single {i i' : Fin n} (h : i ≠ i') (x y : E) :
    ‖(Pi.single i x + Pi.single i' y : Fin n → E)‖ = ‖![x, y]‖ := by
  have h2 : ‖![x, y]‖ = max ‖x‖ ‖y‖ := by
    refine le_antisymm ((pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).2
      fun j => ?_) (max_le (norm_le_pi_norm ![x, y] 0) (norm_le_pi_norm ![x, y] 1))
    fin_cases j
    · exact le_max_left _ _
    · exact le_max_right _ _
  rw [h2]
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).2
    fun k => ?_) (max_le ?_ ?_)
  · by_cases hk : k = i
    · subst hk; simp [h]
    · by_cases hk' : k = i'
      · subst hk'; simp [hk]
      · simp [hk, hk']
  · have := norm_le_pi_norm (Pi.single i x + Pi.single i' y : Fin n → E) i
    simpa [Pi.single_apply, h] using this
  · have := norm_le_pi_norm (Pi.single i x + Pi.single i' y : Fin n → E) i'
    simpa [Pi.single_apply, h.symm] using this

end Two

/- English proof (translation)
Establish `hinf : ∀ w : InfinitePlace K, infComp w (Pi.single i a + Pi.single i' c : Fin n → 𝔸[K]) = Pi.single i (a.1 w) + Pi.single i' (c.1 w)` using `fun w => by`. Use extensionality with `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using `[infComp, h]`.

Distinguish the cases in `hk' : k = i'`. Substitute `hk'` using the available equality. Simplify using `[infComp, hk]`. Simplify using `only [infComp, Pi.add_apply, Pi.single_eq_of_ne hk, Pi.single_eq_of_ne hk', add_zero]`. Both sides reduce to the same expression.

Establish `hfin : ∀ v : HeightOneSpectrum (𝓞 K), finComp v (Pi.single i a + Pi.single i' c : Fin n → 𝔸[K]) = Pi.single i (a.2 v) + Pi.single i' (c.2 v)` using `fun v => by`. Use extensionality with `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using `[finComp, h]`.

Distinguish the cases in `hk' : k = i'`. Substitute `hk'` using the available equality. Simplify using `[finComp, hk]`. Simplify using `only [finComp, Pi.add_apply, Pi.single_eq_of_ne hk, Pi.single_eq_of_ne hk', add_zero]`. Both sides reduce to the same expression.

Establish `hinf2 : ∀ w : InfinitePlace K, infComp w ![a, c] = ![a.1 w, c.1 w]` using `fun w => by`. Apply the tactic sequence `ext j; fin_cases j <;> rfl`. Establish `hfin2 : ∀ v : HeightOneSpectrum (𝓞 K), finComp v ![a, c] = ![a.2 v, c.2 v]` using `fun v => by`. Apply the tactic sequence `ext j; fin_cases j <;> rfl`. Rewrite using `[adelicNorm, adelicNorm]`.

Repeatedly rewrite using `[hinf, hfin, hinf2, hfin2, euclidNorm_single_add_single h, norm_single_add_single h]`.
-/
theorem adelicNorm_single_add_single {n : ℕ} {i i' : Fin n} (h : i ≠ i') (a c : 𝔸[K]) :
    adelicNorm (Pi.single i a + Pi.single i' c : Fin n → 𝔸[K]) = adelicNorm ![a, c] := by
  have hinf : ∀ w : InfinitePlace K, infComp w (Pi.single i a + Pi.single i' c : Fin n → 𝔸[K]) =
      Pi.single i (a.1 w) + Pi.single i' (c.1 w) := fun w => by
    ext k
    by_cases hk : k = i
    · subst hk; simp [infComp, h]
    · by_cases hk' : k = i'
      · subst hk'; simp [infComp, hk]
      · simp only [infComp, Pi.add_apply, Pi.single_eq_of_ne hk, Pi.single_eq_of_ne hk', add_zero]
        rfl
  have hfin : ∀ v : HeightOneSpectrum (𝓞 K),
      finComp v (Pi.single i a + Pi.single i' c : Fin n → 𝔸[K]) =
      Pi.single i (a.2 v) + Pi.single i' (c.2 v) := fun v => by
    ext k
    by_cases hk : k = i
    · subst hk; simp [finComp, h]
    · by_cases hk' : k = i'
      · subst hk'; simp [finComp, hk]
      · simp only [finComp, Pi.add_apply, Pi.single_eq_of_ne hk, Pi.single_eq_of_ne hk', add_zero]
        rfl
  have hinf2 : ∀ w : InfinitePlace K, infComp w ![a, c] = ![a.1 w, c.1 w] := fun w => by
    ext j; fin_cases j <;> rfl
  have hfin2 : ∀ v : HeightOneSpectrum (𝓞 K), finComp v ![a, c] = ![a.2 v, c.2 v] := fun v => by
    ext j; fin_cases j <;> rfl
  rw [adelicNorm, adelicNorm]
  simp_rw [hinf, hfin, hinf2, hfin2, euclidNorm_single_add_single h, norm_single_add_single h]

/- English proof (translation)
Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Conclude with `congrArg (fun N => N i j) (blockOne_map (algebraMap K 𝔸[K]) (γ : Matrix (Fin m) (Fin m) K))`.
-/
theorem diagonal_blockOneHom {m : ℕ} (γ : GL (Fin m) K) :
    AdelicGLn.diagonal K (m + 1) (blockOneHom γ) = blockOneHom (AdelicGLn.diagonal K m γ) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact congrArg (fun N => N i j) (blockOne_map (algebraMap K 𝔸[K]) (γ : Matrix (Fin m) (Fin m) K))

/- English proof (translation)
Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Conclude with `congrArg (fun N => N i j) (blockOne_map (infEval w) (k : Matrix (Fin m) (Fin m) 𝔸[K]))`.
-/
theorem infAt_blockOneHom {m : ℕ} (w : InfinitePlace K) (k : AdelicGLn.AdelicGL K m) :
    infAt w (blockOneHom k) = blockOneHom (infAt w k) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact congrArg (fun N => N i j) (blockOne_map (infEval w) (k : Matrix (Fin m) (Fin m) 𝔸[K]))

/- English proof (translation)
Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Conclude with `congrArg (fun N => N i j) (blockOne_map (finEval v) (k : Matrix (Fin m) (Fin m) 𝔸[K]))`.
-/
theorem finAt_blockOneHom {m : ℕ} (v : HeightOneSpectrum (𝓞 K)) (k : AdelicGLn.AdelicGL K m) :
    finAt v (blockOneHom k) = blockOneHom (finAt v k) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact congrArg (fun N => N i j) (blockOne_map (finEval v) (k : Matrix (Fin m) (Fin m) 𝔸[K]))

/- English proof (translation)
The claim follows from `Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)`.
-/
theorem euclidNorm_sq {E : Type*} [NormedField E] {n : ℕ} (y : Fin n → E) :
    euclidNorm y ^ 2 = ∑ i, ‖y i‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

omit [NumberField K] in
/- English proof (translation)
Introduce `y`. Rewrite using `[coe_blockOneHom]`. Establish `h1` using `hk (Fin.init y)`. Establish `key : euclidNorm (y ᵥ* blockOne (k : Matrix (Fin m) (Fin m) w.Completion)) ^ 2 = euclidNorm y ^ 2`. Rewrite using `[euclidNorm_sq, euclidNorm_sq, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]`.

Repeatedly rewrite using `[vecMul_blockOne_castSucc, vecMul_blockOne_last]`. Establish `h2` using `congrArg (· ^ 2) h1`. Simplify using `only [euclidNorm_sq] at h2`. Rewrite using `[h2]`. Both sides reduce to the same expression.

Conclude with `(sq_eq_sq₀ (euclidNorm_nonneg _) (euclidNorm_nonneg _)).1 key`.
-/
theorem blockOneHom_mem_archCompact {m : ℕ} (w : InfinitePlace K) {k : GL (Fin m) w.Completion}
    (hk : k ∈ archCompact w) : blockOneHom k ∈ archCompact (n := m + 1) w := by
  intro y
  rw [coe_blockOneHom]
  have h1 := hk (Fin.init y)
  have key : euclidNorm (y ᵥ* blockOne (k : Matrix (Fin m) (Fin m) w.Completion)) ^ 2 =
      euclidNorm y ^ 2 := by
    rw [euclidNorm_sq, euclidNorm_sq, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp_rw [vecMul_blockOne_castSucc, vecMul_blockOne_last]
    have h2 := congrArg (· ^ 2) h1
    simp only [euclidNorm_sq] at h2
    rw [h2]
    rfl
  exact (sq_eq_sq₀ (euclidNorm_nonneg _) (euclidNorm_nonneg _)).1 key

/- English proof (translation)
Rewrite `hk`, the goal using `[GLnLocal.mem_integralGL_iff]`. Establish `h2 : ∀ i j, (k : Matrix (Fin m) (Fin m) (v.adicCompletion K))⁻¹ i j ∈ (ValuativeRel.valuation (v.adicCompletion K)).integer`. Simplify `hk.2` using `[Matrix.coe_units_inv]`. Rewrite using `[← map_inv]`. Apply the tactic sequence `refine ⟨fun i j => ?_, fun i j => ?_⟩ <;>`.

Rewrite using `[coe_blockOneHom]`. Apply the tactic sequence `induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>`. Simplify using `[hk.1, h2]`.
-/
theorem blockOneHom_mem_integralGL {m : ℕ} (v : HeightOneSpectrum (𝓞 K))
    {k : GL (Fin m) (v.adicCompletion K)} (hk : k ∈ GLnLocal.integralGL (v.adicCompletion K) m) :
    blockOneHom k ∈ GLnLocal.integralGL (v.adicCompletion K) (m + 1) := by
  rw [GLnLocal.mem_integralGL_iff] at hk ⊢
  have h2 : ∀ i j, (k : Matrix (Fin m) (Fin m) (v.adicCompletion K))⁻¹ i j ∈
      (ValuativeRel.valuation (v.adicCompletion K)).integer := by
    simpa [Matrix.coe_units_inv] using hk.2
  rw [← map_inv]
  refine ⟨fun i j => ?_, fun i j => ?_⟩ <;>
  · rw [coe_blockOneHom]
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp [hk.1, h2]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun w => by rw [infAt_blockOneHom]; exact blockOneHom_mem_archCompact w (hk.1 w), fun v => by rw [finAt_blockOneHom]; exact blockOneHom_mem_integralGL v (hk.2 v)⟩`.
-/
theorem blockOneHom_mem_maxCompact {m : ℕ} {k : AdelicGLn.AdelicGL K m} (hk : k ∈ maxCompact) :
    blockOneHom k ∈ maxCompact (n := m + 1) :=
  ⟨fun w => by rw [infAt_blockOneHom]; exact blockOneHom_mem_archCompact w (hk.1 w),
    fun v => by rw [finAt_blockOneHom]; exact blockOneHom_mem_integralGL v (hk.2 v)⟩

/- English proof (translation)
Establish `hinf : ∀ w : InfinitePlace K, infComp w (Pi.single i (1 : 𝔸[K]) : Fin n → 𝔸[K]) = Pi.single i 1` using `fun w => by`. Use extensionality with `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using `[infComp]`.

Simplify using `only [infComp, Pi.single_eq_of_ne hk]`. Both sides reduce to the same expression. Establish `hfin : ∀ v : HeightOneSpectrum (𝓞 K), finComp v (Pi.single i (1 : 𝔸[K]) : Fin n → 𝔸[K]) = Pi.single i 1` using `fun v => by`. Use extensionality with `k`. Distinguish the cases in `hk : k = i`.

Substitute `hk` using the available equality. Simplify using `[finComp]`. Simplify using `only [finComp, Pi.single_eq_of_ne hk]`. Both sides reduce to the same expression. Establish `he : ∀ (E : Type _) [NormedField E], euclidNorm (Pi.single i (1 : E) : Fin n → E) = 1`.

Introduce `E _`. Rewrite using `[euclidNorm, Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]`. Simplify using the standard rewrite rules. Establish `hs : ∀ (E : Type _) [NormedField E], ‖(Pi.single i (1 : E) : Fin n → E)‖ = 1`. Introduce `E _`.

Use `le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_) ?_` and prove the remaining obligations. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne hj]`.

Use `norm_le_pi_norm (Pi.single i (1 : E) : Fin n → E) i` as an intermediate fact. Simplify using `using this`. Establish `heW : ∀ w : InfinitePlace K, euclidNorm (Pi.single i (1 : w.Completion) : Fin n → _) = 1` using `fun w => he _`. Establish `hsV : ∀ v : HeightOneSpectrum (𝓞 K), ‖(Pi.single i (1 : v.adicCompletion K) : Fin n → _)‖ = 1` using `fun v => hs _`. Rewrite using `[adelicNorm]`.

Simplify using `only [hinf, hfin, heW, hsV, one_pow, Finset.prod_const_one, finprod_one, mul_one]`.
-/
theorem adelicNorm_single_one {n : ℕ} (i : Fin n) :
    adelicNorm (Pi.single i (1 : 𝔸[K]) : Fin n → 𝔸[K]) = 1 := by
  classical
  have hinf : ∀ w : InfinitePlace K, infComp w (Pi.single i (1 : 𝔸[K]) : Fin n → 𝔸[K]) =
      Pi.single i 1 := fun w => by
    ext k
    by_cases hk : k = i
    · subst hk; simp [infComp]
    · simp only [infComp, Pi.single_eq_of_ne hk]; rfl
  have hfin : ∀ v : HeightOneSpectrum (𝓞 K), finComp v (Pi.single i (1 : 𝔸[K]) : Fin n → 𝔸[K]) =
      Pi.single i 1 := fun v => by
    ext k
    by_cases hk : k = i
    · subst hk; simp [finComp]
    · simp only [finComp, Pi.single_eq_of_ne hk]; rfl
  have he : ∀ (E : Type _) [NormedField E], euclidNorm (Pi.single i (1 : E) : Fin n → E) = 1 := by
    intro E _
    rw [euclidNorm, Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
    simp
  have hs : ∀ (E : Type _) [NormedField E], ‖(Pi.single i (1 : E) : Fin n → E)‖ = 1 := by
    intro E _
    refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_) ?_
    · by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_eq_of_ne hj]
    · have := norm_le_pi_norm (Pi.single i (1 : E) : Fin n → E) i
      simpa using this
  have heW : ∀ w : InfinitePlace K, euclidNorm (Pi.single i (1 : w.Completion) : Fin n → _) = 1 :=
    fun w => he _
  have hsV : ∀ v : HeightOneSpectrum (𝓞 K),
      ‖(Pi.single i (1 : v.adicCompletion K) : Fin n → _)‖ = 1 := fun v => hs _
  rw [adelicNorm]
  simp only [hinf, hfin, heW, hsV, one_pow, Finset.prod_const_one, finprod_one, mul_one]

/- English proof (translation)
Use `Filter.Eventually.of_forall fun v => ?_` and prove the remaining obligations. Establish `hfin : finComp v (Pi.single i (1 : 𝔸[K]) : Fin n → 𝔸[K]) = Pi.single i 1`. Use extensionality with `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality.

Simplify using `[finComp]`. Simplify using `only [finComp, Pi.single_eq_of_ne hk]`. Both sides reduce to the same expression. Rewrite using `[hfin]`. Use `le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_) ?_` and prove the remaining obligations.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne hj]`. Use `norm_le_pi_norm (Pi.single i (1 : v.adicCompletion K) : Fin n → _) i` as an intermediate fact.

Simplify using `using this`.
-/
theorem hasFiniteContent_single_one {n : ℕ} (i : Fin n) :
    HasFiniteContent (Pi.single i (1 : 𝔸[K]) : Fin n → 𝔸[K]) := by
  refine Filter.Eventually.of_forall fun v => ?_
  have hfin : finComp v (Pi.single i (1 : 𝔸[K]) : Fin n → 𝔸[K]) = Pi.single i 1 := by
    ext k
    by_cases hk : k = i
    · subst hk; simp [finComp]
    · simp only [finComp, Pi.single_eq_of_ne hk]; rfl
  rw [hfin]
  refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_) ?_
  · by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj]
  · have := norm_le_pi_norm (Pi.single i (1 : v.adicCompletion K) : Fin n → _) i
    simpa using this

/- English proof (translation)
Establish `: (Pi.single i (s : 𝔸[K]) : Fin n → 𝔸[K]) = (s : 𝔸[K]) • Pi.single i 1`. Use extensionality with `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Pi.single_eq_of_ne hj]`. Rewrite using `[this, adelicNorm_smul (hasFiniteContent_single_one i), adelicNorm_single_one, mul_one]`.
-/
theorem adelicNorm_single_units {n : ℕ} (i : Fin n) (s : IdeleGroup K) :
    adelicNorm (Pi.single i (s : 𝔸[K]) : Fin n → 𝔸[K]) = ideleModule K s := by
  have : (Pi.single i (s : 𝔸[K]) : Fin n → 𝔸[K]) = (s : 𝔸[K]) • Pi.single i 1 := by
    ext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj]
  rw [this, adelicNorm_smul (hasFiniteContent_single_one i), adelicNorm_single_one, mul_one]

/- English proof (translation)
Use extensionality with `j`. Apply the tactic sequence `fin_cases j <;> simp [vecMul, dotProduct, Fin.sum_univ_two, ratVec]`.
-/
theorem ratVec_vecMul_two (x : Fin 2 → K) (α u β : 𝔸[K]) :
    ratVec x ᵥ* !![α, u; 0, β] =
      ![algebraMap K 𝔸[K] (x 0) * α, algebraMap K 𝔸[K] (x 0) * u + algebraMap K 𝔸[K] (x 1) * β] := by
  ext j
  fin_cases j <;> simp [vecMul, dotProduct, Fin.sum_univ_two, ratVec]

/- English proof (translation)
Use extensionality with `k`. Simplify using `only [ratVec, Pi.add_apply, map_add]`. Apply the tactic sequence `by_cases h1 : k = i <;> by_cases h2 : k = i' <;>`. Simplify using `[Pi.single_apply, h1, h2, apply_ite (algebraMap K 𝔸[K])]`.
-/
theorem ratVec_single_add_single {n : ℕ} (i i' : Fin n) (a c : K) :
    ratVec (Pi.single i a + Pi.single i' c : Fin n → K) =
      Pi.single i (algebraMap K 𝔸[K] a) + Pi.single i' (algebraMap K 𝔸[K] c) := by
  ext k
  simp only [ratVec, Pi.add_apply, map_add]
  by_cases h1 : k = i <;> by_cases h2 : k = i' <;>
    simp [Pi.single_apply, h1, h2, apply_ite (algebraMap K 𝔸[K])]

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `g`. Take `⟨b, hb, k, hk, hbk⟩` from `exists_adelicBorel_mul_maxCompact g`.

Conclude with `⟨1, b, hb, k, hk, by rw [map_one, one_mul, hbk], fun i => i.elim0⟩`. Consider the case `succ m ih`. Introduce `g`. Take `⟨x₀, hx₀, hmin⟩` from `exists_height_min (Nat.succ_pos m) g`. Take `⟨γ₁, hγ₁⟩` from `exists_lastRow_eq hx₀`.

Take `⟨b, hb, k, hk, hbk⟩` from `exists_adelicBorel_mul_maxCompact (AdelicGLn.diagonal K _ γ₁ * g)`. Use `set B : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔸[K] := (b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔸[K]) with hB`. Establish `hBup : ∀ i j : Fin (m + 1), j < i → B i j = 0` using `fun i j hij => hb hij`. Use `set b' : Matrix (Fin m) (Fin m) 𝔸[K] := Matrix.of fun i j => B i.castSucc j.castSucc with hb'`. Establish `hb'up : b'.IsUpperTriangular` using `fun i j hij => hBup _ _ (Fin.castSucc_lt_castSucc_iff.2 hij)`.

Establish `hb'det : IsUnit b'.det`. Rewrite using `[Matrix.det_of_isUpperTriangular hb'up]`. Conclude with `Finset.prod_induction _ IsUnit (fun a c ha hc => ha.mul hc) isUnit_one (fun i _ => isUnit_apply_self_of_mem_adelicBorel hb i.castSucc)`. Use `set b'GL : AdelicGLn.AdelicGL K m := ((Matrix.isUnit_iff_isUnit_det b').2 hb'det).unit with hb'GL`. Take `⟨γ', bb, hbb, k', hk', hγ'eq, hratio⟩` from `ih b'GL`.

Use `set G' : Matrix (Fin m) (Fin m) 𝔸[K] := ((AdelicGLn.diagonal K m γ' : AdelicGLn.AdelicGL K m) : Matrix (Fin m) (Fin m) 𝔸[K]) with hG'`. Use `set BB : Matrix (Fin m) (Fin m) 𝔸[K] := (bb : Matrix (Fin m) (Fin m) 𝔸[K]) with hBB`. Use `set K' : Matrix (Fin m) (Fin m) 𝔸[K] := (k' : Matrix (Fin m) (Fin m) 𝔸[K]) with hK'`. Establish `hIH : G' * b' = BB * K'`. Use `congrArg (fun x : AdelicGLn.AdelicGL K m => (x : Matrix (Fin m) (Fin m) 𝔸[K])) hγ'eq` as an intermediate fact.

Simplify `this` using `[hb'GL]`. Use `set u : Fin m → 𝔸[K] := fun i => B i.castSucc (Fin.last m) with hu`. Use `set β : 𝔸[K] := B (Fin.last m) (Fin.last m) with hβ`. Use `set Bn : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔸[K] := Matrix.of fun i j => Fin.lastCases (Fin.lastCases β (fun _ => 0) j) (fun i' => Fin.lastCases ((G' *ᵥ u) i') (fun j' => BB i' j') j) i with hBn`. Establish `hBn_ll : Bn (Fin.last m) (Fin.last m) = β` using `by simp [hBn]`.

Establish `hBn_lc : ∀ j : Fin m, Bn (Fin.last m) j.castSucc = 0` using `fun j => by simp [hBn]`. Establish `hBn_cl : ∀ i : Fin m, Bn i.castSucc (Fin.last m) = (G' *ᵥ u) i` using `fun i => by simp [hBn]`. Establish `hBn_cc : ∀ i j : Fin m, Bn i.castSucc j.castSucc = BB i j` using `fun i j => by simp [hBn]`. Establish `hblock : blockOne G' * B = Bn * blockOne K'`. Use extensionality with `i j`.

Proceed by induction on `i using Fin.lastCases with`. Consider the case `last`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => simp [Matrix.mul_apply, Fin.sum_univ_castSucc, hBn_ll, hBn_lc, hβ]`. Consider the case `cast j`.

Simplify using `[Matrix.mul_apply, Fin.sum_univ_castSucc, hBn_ll, hBn_lc, hBup _ _ (Fin.castSucc_lt_last j)]`. Consider the case `cast i`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => simp [Matrix.mul_apply, Fin.sum_univ_castSucc, hBn_cl, hBn_cc, mulVec, dotProduct, hu]`. Consider the case `cast j`.

Use `congrArg (fun N : Matrix (Fin m) (Fin m) 𝔸[K] => N i j) hIH` as an intermediate fact. Simplify using `only [Matrix.mul_apply] at this`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_castSucc, hBn_cl, hBn_cc]`. Conclude with `this`. Use `set γ : GL (Fin (m + 1)) K := blockOneHom γ' * γ₁ with hγ`.

Use `set kn : AdelicGLn.AdelicGL K (m + 1) := blockOneHom k' * k with hkn`. Establish `hkn_mem : kn ∈ maxCompact` using `mul_mem (blockOneHom_mem_maxCompact hk') hk`. Use `set bn : AdelicGLn.AdelicGL K (m + 1) := AdelicGLn.diagonal K _ γ * g * kn⁻¹ with hbn`. Establish `hdg : AdelicGLn.diagonal K _ γ * g = bn * kn` using `by rw [hbn, inv_mul_cancel_right]`. Establish `hbnmat : (bn : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔸[K]) = Bn`.

Establish `h1 : ((AdelicGLn.diagonal K _ γ * g : AdelicGLn.AdelicGL K (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔸[K]) = Bn * (kn : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔸[K])`. Rewrite using `[hγ, map_mul, mul_assoc, hbk, diagonal_blockOneHom, hkn]`. Simplify using `only [Units.val_mul, coe_blockOneHom]`. Rewrite using `[← mul_assoc, hblock, mul_assoc]`. Rewrite using `[hbn, Units.val_mul, h1, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]`.

Establish `hbn_mem : bn ∈ adelicBorel`. Rewrite using `[mem_adelicBorel, hbnmat]`. Introduce `i j hij`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last`.

Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => exact absurd hij (lt_irrefl _)`. Consider the case `cast j => exact hBn_lc j`. Consider the case `cast i`. Proceed by induction on `j using Fin.lastCases with`.

Consider the case `last => exact absurd hij (not_lt.2 (Fin.castSucc_lt_last i).le)`. Consider the case `cast j`. Rewrite using `[hBn_cc]`. Conclude with `hbb (Fin.castSucc_lt_castSucc_iff.1 hij)`. Use `⟨γ, bn, hbn_mem, kn, hkn_mem, hdg, ?_⟩` and prove the remaining obligations.

Rewrite using `[hbnmat]`. Introduce `i j hij`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `cast j`. Proceed by induction on `i using Fin.lastCases with`.

Consider the case `last`. It suffices to derive a contradiction. Use `j.isLt` as an intermediate fact. Simplify using `only [Fin.coe_castSucc, Fin.val_last] at hij`. Use linear arithmetic over natural numbers and integers.

Consider the case `cast i`. Rewrite using `[hBn_cc, hBn_cc]`. Conclude with `hratio i j (by simpa using hij)`. Consider the case `last`. Proceed by induction on `i using Fin.lastCases with`.

Consider the case `last`. It suffices to derive a contradiction. Simplify using `only [Fin.val_last] at hij`. Use linear arithmetic over natural numbers and integers. Consider the case `cast i`.

Establish `hi : (i : ℕ) + 1 = m` using `by simpa using hij.symm`. Rewrite using `[hBn_ll, hBn_cc]`. Establish `hα : IsUnit (BB i i)` using `isUnit_apply_self_of_mem_adelicBorel hbb i`. Establish `hβu : IsUnit β` using `isUnit_apply_self_of_mem_adelicBorel hb (Fin.last m)`. Take `⟨x, hx0, hxle⟩` from `hD hα.unit hβu.unit ((G' *ᵥ u) i)`.

Rewrite `hxle` using `[IsUnit.unit_spec, IsUnit.unit_spec]`. Establish `hil : i.castSucc ≠ Fin.last m` using `Fin.castSucc_ne_last i`. Use `set z : Fin (m + 1) → K := Pi.single i.castSucc (x 0) + Pi.single (Fin.last m) (x 1) with hz`. Establish `hz0 : z ≠ 0`. Introduce `h`.

Apply `hx0` to reduce the goal to its premises. Use extensionality with `l`. Use `fin_cases l`. Use `congrFun h i.castSucc` as an intermediate fact. Simplify `this` using `[hz, Pi.single_apply, hil]`.

Use `congrFun h (Fin.last m)` as an intermediate fact. Simplify `this` using `[hz, Pi.single_apply, hil.symm]`. Establish `hrow : ratVec z ᵥ* Bn = Pi.single i.castSucc (algebraMap K 𝔸[K] (x 0) * BB i i) + Pi.single (Fin.last m) (algebraMap K 𝔸[K] (x 0) * (G' *ᵥ u) i + algebraMap K 𝔸[K] (x 1) * β)`. Rewrite using `[hz, ratVec_single_add_single, add_vecMul, single_vecMul, single_vecMul]`. Use extensionality with `l`.

Proceed by induction on `l using Fin.lastCases with`. Consider the case `last => simp [Matrix.row, hBn_cl, hBn_ll, hil, Algebra.smul_def]`. Consider the case `cast l`. Distinguish the cases in `hl : l = i`. Substitute `hl` using the available equality.

Simplify using `[Matrix.row, hBn_cc, hBn_lc, Fin.castSucc_ne_last, Algebra.smul_def]`. Establish `hli : l < i` using `lt_of_le_of_ne (Fin.le_iff_val_le_val.2 (by omega)) hl`. Establish `hBB0 : BB i l = 0` using `hbb hli`. Simplify using `[Matrix.row, hBn_cc, hBn_lc, hBB0, Fin.castSucc_ne_last, hl, Algebra.smul_def]`. Establish `hlast : ratVec (Pi.single (Fin.last m) (1 : K)) ᵥ* Bn = Pi.single (Fin.last m) β`.

Establish `: ratVec (Pi.single (Fin.last m) (1 : K)) = Pi.single (Fin.last m) (1 : 𝔸[K])`. Use extensionality with `l`. Distinguish the cases in `hl : l = Fin.last m`. Substitute `hl` using the available equality. Simplify using `[ratVec]`.

Simplify using `[ratVec, Pi.single_eq_of_ne hl]`. Rewrite using `[this, single_one_vecMul]`. Use extensionality with `l`. Proceed by induction on `l using Fin.lastCases with`. Consider the case `last => simp [Matrix.row, hBn_ll]`.

Consider the case `cast l => simp [Matrix.row, hBn_lc, Fin.castSucc_ne_last]`. Establish `hzγ : z ᵥ* (γ : Matrix (Fin (m + 1)) (Fin (m + 1)) K) ≠ 0`. Introduce `h`. Apply `hz0` to reduce the goal to its premises. Use `congrArg (fun y => y ᵥ* ((γ⁻¹ : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) h` as an intermediate fact.

Simplify `this` using `[vecMul_vecMul, ← Units.val_mul]`. Establish `hx₀γ : x₀ = Pi.single (Fin.last m) 1 ᵥ* (γ : Matrix (Fin (m + 1)) (Fin (m + 1)) K)`. Rewrite using `[hγ, Units.val_mul, coe_blockOneHom, ← vecMul_vecMul, single_last_vecMul_blockOne, hγ₁]`. Establish `h1` using `hmin _ hzγ`. Rewrite `h1` using `[hx₀γ, ← height_diagonal_mul, ← height_diagonal_mul, hdg, height_mul_maxCompact _ hkn_mem, height_mul_maxCompact _ hkn_mem, height, height, hbnmat, hlast, hrow, adelicNorm_single_add_single hil]`.

Establish `h2 : adelicNorm (Pi.single (Fin.last m) β : Fin (m + 1) → 𝔸[K]) = ideleModule K hβu.unit`. Rewrite using `[← adelicNorm_single_units (Fin.last m) hβu.unit, IsUnit.unit_spec]`. Rewrite `h1` using `[h2, ← ratVec_vecMul_two]`. Establish `h3` using `h1.trans hxle`. Rewrite `h3` using `[map_mul, Positive.val_mul]`.

Rewrite using `[← IsUnit.unit_spec hβu, ← IsUnit.unit_spec hα, adeleAbs_units, adeleAbs_units]`. Use `set a : ℝ := (ideleModule K hα.unit : ℝ)`. Use `set c : ℝ := (ideleModule K hβu.unit : ℝ)`. Establish `ha : 0 < a` using `(ideleModule K hα.unit).2`. Establish `hc : 0 < c` using `(ideleModule K hβu.unit).2`.

Establish `h4 : c ^ 2 ≤ C ^ 2 * (a * c)`. Combine the equalities or inequalities in the displayed calculation. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem exists_reduced_of {C : ℝ} (hC : 0 < C)
    (hD : ∀ (α δ : IdeleGroup K) (u : 𝔸[K]), ∃ x : Fin 2 → K, x ≠ 0 ∧
      adelicNorm (ratVec x ᵥ* !![(α : 𝔸[K]), u; 0, (δ : 𝔸[K])]) ≤
        C * √(ideleModule K (α * δ) : ℝ)) :
    ∀ (n : ℕ) (g : AdelicGLn.AdelicGL K n), ∃ γ : GL (Fin n) K, ∃ b ∈ adelicBorel, ∃ k ∈ maxCompact,
      AdelicGLn.diagonal K n γ * g = b * k ∧ ∀ i j : Fin n, (j : ℕ) = i + 1 →
        adeleAbs ((b : Matrix (Fin n) (Fin n) 𝔸[K]) j j) ≤
          C ^ 2 * adeleAbs ((b : Matrix (Fin n) (Fin n) 𝔸[K]) i i) := by
  classical
  intro n
  induction n with
  | zero =>
    intro g
    obtain ⟨b, hb, k, hk, hbk⟩ := exists_adelicBorel_mul_maxCompact g
    exact ⟨1, b, hb, k, hk, by rw [map_one, one_mul, hbk], fun i => i.elim0⟩
  | succ m ih =>
    intro g
    obtain ⟨x₀, hx₀, hmin⟩ := exists_height_min (Nat.succ_pos m) g
    obtain ⟨γ₁, hγ₁⟩ := exists_lastRow_eq hx₀
    obtain ⟨b, hb, k, hk, hbk⟩ :=
      exists_adelicBorel_mul_maxCompact (AdelicGLn.diagonal K _ γ₁ * g)
    set B : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔸[K] := (b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔸[K])
      with hB
    have hBup : ∀ i j : Fin (m + 1), j < i → B i j = 0 := fun i j hij => hb hij

    set b' : Matrix (Fin m) (Fin m) 𝔸[K] := Matrix.of fun i j => B i.castSucc j.castSucc with hb'
    have hb'up : b'.IsUpperTriangular := fun i j hij =>
      hBup _ _ (Fin.castSucc_lt_castSucc_iff.2 hij)
    have hb'det : IsUnit b'.det := by
      rw [Matrix.det_of_isUpperTriangular hb'up]
      exact Finset.prod_induction _ IsUnit (fun a c ha hc => ha.mul hc) isUnit_one
        (fun i _ => isUnit_apply_self_of_mem_adelicBorel hb i.castSucc)
    set b'GL : AdelicGLn.AdelicGL K m := ((Matrix.isUnit_iff_isUnit_det b').2 hb'det).unit
      with hb'GL
    obtain ⟨γ', bb, hbb, k', hk', hγ'eq, hratio⟩ := ih b'GL
    set G' : Matrix (Fin m) (Fin m) 𝔸[K] :=
      ((AdelicGLn.diagonal K m γ' : AdelicGLn.AdelicGL K m) : Matrix (Fin m) (Fin m) 𝔸[K]) with hG'
    set BB : Matrix (Fin m) (Fin m) 𝔸[K] := (bb : Matrix (Fin m) (Fin m) 𝔸[K]) with hBB
    set K' : Matrix (Fin m) (Fin m) 𝔸[K] := (k' : Matrix (Fin m) (Fin m) 𝔸[K]) with hK'
    have hIH : G' * b' = BB * K' := by
      have := congrArg (fun x : AdelicGLn.AdelicGL K m => (x : Matrix (Fin m) (Fin m) 𝔸[K])) hγ'eq
      simpa [hb'GL] using this
    set u : Fin m → 𝔸[K] := fun i => B i.castSucc (Fin.last m) with hu
    set β : 𝔸[K] := B (Fin.last m) (Fin.last m) with hβ
    set Bn : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔸[K] := Matrix.of fun i j =>
      Fin.lastCases (Fin.lastCases β (fun _ => 0) j)
        (fun i' => Fin.lastCases ((G' *ᵥ u) i') (fun j' => BB i' j') j) i with hBn
    have hBn_ll : Bn (Fin.last m) (Fin.last m) = β := by simp [hBn]
    have hBn_lc : ∀ j : Fin m, Bn (Fin.last m) j.castSucc = 0 := fun j => by simp [hBn]
    have hBn_cl : ∀ i : Fin m, Bn i.castSucc (Fin.last m) = (G' *ᵥ u) i := fun i => by simp [hBn]
    have hBn_cc : ∀ i j : Fin m, Bn i.castSucc j.castSucc = BB i j := fun i j => by simp [hBn]
    have hblock : blockOne G' * B = Bn * blockOne K' := by
      ext i j
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => simp [Matrix.mul_apply, Fin.sum_univ_castSucc, hBn_ll, hBn_lc, hβ]
        | cast j =>
          simp [Matrix.mul_apply, Fin.sum_univ_castSucc, hBn_ll, hBn_lc,
            hBup _ _ (Fin.castSucc_lt_last j)]
      | cast i =>
        induction j using Fin.lastCases with
        | last => simp [Matrix.mul_apply, Fin.sum_univ_castSucc, hBn_cl, hBn_cc, mulVec, dotProduct, hu]
        | cast j =>
          have := congrArg (fun N : Matrix (Fin m) (Fin m) 𝔸[K] => N i j) hIH
          simp only [Matrix.mul_apply] at this
          simp [Matrix.mul_apply, Fin.sum_univ_castSucc, hBn_cl, hBn_cc]
          exact this
    set γ : GL (Fin (m + 1)) K := blockOneHom γ' * γ₁ with hγ
    set kn : AdelicGLn.AdelicGL K (m + 1) := blockOneHom k' * k with hkn
    have hkn_mem : kn ∈ maxCompact := mul_mem (blockOneHom_mem_maxCompact hk') hk
    set bn : AdelicGLn.AdelicGL K (m + 1) := AdelicGLn.diagonal K _ γ * g * kn⁻¹ with hbn
    have hdg : AdelicGLn.diagonal K _ γ * g = bn * kn := by rw [hbn, inv_mul_cancel_right]
    have hbnmat : (bn : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔸[K]) = Bn := by
      have h1 : ((AdelicGLn.diagonal K _ γ * g : AdelicGLn.AdelicGL K (m + 1)) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔸[K]) = Bn * (kn : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔸[K]) := by
        rw [hγ, map_mul, mul_assoc, hbk, diagonal_blockOneHom, hkn]
        simp only [Units.val_mul, coe_blockOneHom]
        rw [← mul_assoc, hblock, mul_assoc]
      rw [hbn, Units.val_mul, h1, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
    have hbn_mem : bn ∈ adelicBorel := by
      rw [mem_adelicBorel, hbnmat]
      intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (lt_irrefl _)
        | cast j => exact hBn_lc j
      | cast i =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (not_lt.2 (Fin.castSucc_lt_last i).le)
        | cast j =>
          rw [hBn_cc]
          exact hbb (Fin.castSucc_lt_castSucc_iff.1 hij)
    refine ⟨γ, bn, hbn_mem, kn, hkn_mem, hdg, ?_⟩
    rw [hbnmat]
    intro i j hij
    induction j using Fin.lastCases with
    | cast j =>
      induction i using Fin.lastCases with
      | last =>
        exfalso
        have := j.isLt
        simp only [Fin.coe_castSucc, Fin.val_last] at hij
        omega
      | cast i =>
        rw [hBn_cc, hBn_cc]
        exact hratio i j (by simpa using hij)
    | last =>
      induction i using Fin.lastCases with
      | last =>
        exfalso
        simp only [Fin.val_last] at hij
        omega
      | cast i =>
        have hi : (i : ℕ) + 1 = m := by simpa using hij.symm
        rw [hBn_ll, hBn_cc]
        have hα : IsUnit (BB i i) := isUnit_apply_self_of_mem_adelicBorel hbb i
        have hβu : IsUnit β := isUnit_apply_self_of_mem_adelicBorel hb (Fin.last m)
        obtain ⟨x, hx0, hxle⟩ := hD hα.unit hβu.unit ((G' *ᵥ u) i)
        rw [IsUnit.unit_spec, IsUnit.unit_spec] at hxle
        have hil : i.castSucc ≠ Fin.last m := Fin.castSucc_ne_last i
        set z : Fin (m + 1) → K := Pi.single i.castSucc (x 0) + Pi.single (Fin.last m) (x 1) with hz
        have hz0 : z ≠ 0 := by
          intro h
          apply hx0
          ext l
          fin_cases l
          · have := congrFun h i.castSucc
            simpa [hz, Pi.single_apply, hil] using this
          · have := congrFun h (Fin.last m)
            simpa [hz, Pi.single_apply, hil.symm] using this
        have hrow : ratVec z ᵥ* Bn = Pi.single i.castSucc (algebraMap K 𝔸[K] (x 0) * BB i i) +
            Pi.single (Fin.last m) (algebraMap K 𝔸[K] (x 0) * (G' *ᵥ u) i +
              algebraMap K 𝔸[K] (x 1) * β) := by
          rw [hz, ratVec_single_add_single, add_vecMul, single_vecMul, single_vecMul]
          ext l
          induction l using Fin.lastCases with
          | last => simp [Matrix.row, hBn_cl, hBn_ll, hil, Algebra.smul_def]
          | cast l =>
            by_cases hl : l = i
            · subst hl
              simp [Matrix.row, hBn_cc, hBn_lc, Fin.castSucc_ne_last, Algebra.smul_def]
            · have hli : l < i := lt_of_le_of_ne (Fin.le_iff_val_le_val.2 (by omega)) hl
              have hBB0 : BB i l = 0 := hbb hli
              simp [Matrix.row, hBn_cc, hBn_lc, hBB0, Fin.castSucc_ne_last, hl, Algebra.smul_def]
        have hlast : ratVec (Pi.single (Fin.last m) (1 : K)) ᵥ* Bn = Pi.single (Fin.last m) β := by
          have : ratVec (Pi.single (Fin.last m) (1 : K)) = Pi.single (Fin.last m) (1 : 𝔸[K]) := by
            ext l
            by_cases hl : l = Fin.last m
            · subst hl; simp [ratVec]
            · simp [ratVec, Pi.single_eq_of_ne hl]
          rw [this, single_one_vecMul]
          ext l
          induction l using Fin.lastCases with
          | last => simp [Matrix.row, hBn_ll]
          | cast l => simp [Matrix.row, hBn_lc, Fin.castSucc_ne_last]
        have hzγ : z ᵥ* (γ : Matrix (Fin (m + 1)) (Fin (m + 1)) K) ≠ 0 := by
          intro h
          apply hz0
          have := congrArg (fun y => y ᵥ* ((γ⁻¹ : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) h
          simpa [vecMul_vecMul, ← Units.val_mul] using this
        have hx₀γ : x₀ = Pi.single (Fin.last m) 1 ᵥ* (γ : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
          rw [hγ, Units.val_mul, coe_blockOneHom, ← vecMul_vecMul, single_last_vecMul_blockOne, hγ₁]
        have h1 := hmin _ hzγ
        rw [hx₀γ, ← height_diagonal_mul, ← height_diagonal_mul, hdg, height_mul_maxCompact _ hkn_mem,
          height_mul_maxCompact _ hkn_mem, height, height, hbnmat, hlast, hrow,
          adelicNorm_single_add_single hil] at h1
        have h2 : adelicNorm (Pi.single (Fin.last m) β : Fin (m + 1) → 𝔸[K]) =
            ideleModule K hβu.unit := by
          rw [← adelicNorm_single_units (Fin.last m) hβu.unit, IsUnit.unit_spec]
        rw [h2, ← ratVec_vecMul_two] at h1
        have h3 := h1.trans hxle
        rw [map_mul, Positive.val_mul] at h3
        rw [← IsUnit.unit_spec hβu, ← IsUnit.unit_spec hα, adeleAbs_units, adeleAbs_units]
        set a : ℝ := (ideleModule K hα.unit : ℝ)
        set c : ℝ := (ideleModule K hβu.unit : ℝ)
        have ha : 0 < a := (ideleModule K hα.unit).2
        have hc : 0 < c := (ideleModule K hβu.unit).2
        have h4 : c ^ 2 ≤ C ^ 2 * (a * c) := by
          calc c ^ 2 ≤ (C * √(a * c)) ^ 2 := pow_le_pow_left₀ hc.le h3 2
            _ = C ^ 2 * (a * c) := by rw [mul_pow, Real.sq_sqrt (mul_nonneg ha.le hc.le)]
        nlinarith

/- English proof (translation)
Take `⟨C, hC, hD⟩` from `exists_adelicNorm_vecMul_le (K := K)`. Establish `hC2 : 0 < C ^ 2` using `pow_pos hC 2`. Use `⟨(C ^ 2)⁻¹, inv_pos.2 hC2, fun n g => ?_⟩` and prove the remaining obligations. Take `⟨γ, b, hb, k, hk, heq, hr⟩` from `exists_reduced_of hC hD n g`. Use `⟨γ, b, hb, k, hk, heq, fun i j hij => ?_⟩` and prove the remaining obligations.

Rewrite using `[inv_mul_le_iff₀ hC2]`. Conclude with `hr i j hij`.
-/
theorem exists_reduced : ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ (n : ℕ) (g : AdelicGLn.AdelicGL K n),
    ∃ γ : GL (Fin n) K, ∃ b ∈ adelicBorel, ∃ k ∈ maxCompact,
      AdelicGLn.diagonal K n γ * g = b * k ∧ ∀ i j : Fin n, (j : ℕ) = i + 1 →
        t₀ * adeleAbs ((b : Matrix (Fin n) (Fin n) 𝔸[K]) j j) ≤
          adeleAbs ((b : Matrix (Fin n) (Fin n) 𝔸[K]) i i) := by
  obtain ⟨C, hC, hD⟩ := exists_adelicNorm_vecMul_le (K := K)
  have hC2 : 0 < C ^ 2 := pow_pos hC 2
  refine ⟨(C ^ 2)⁻¹, inv_pos.2 hC2, fun n g => ?_⟩
  obtain ⟨γ, b, hb, k, hk, heq, hr⟩ := exists_reduced_of hC hD n g
  refine ⟨γ, b, hb, k, hk, heq, fun i j hij => ?_⟩
  rw [inv_mul_le_iff₀ hC2]
  exact hr i j hij

end Reduction

end

end GroundTheory.Automorphic
