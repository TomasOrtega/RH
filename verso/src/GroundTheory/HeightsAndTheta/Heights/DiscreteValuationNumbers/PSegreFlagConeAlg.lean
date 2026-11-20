import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagConeAlg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairConeAlg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureModel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace SegreFlagConeAlg

/- English proof (translation)
Use `symm`. Use `Fintype.sum_of_injective (Fin.castLE hkN) (Fin.castLE_injective hkN) _ _ (fun j hj => hs j ?_) (fun _ => rfl)` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `hj ⟨⟨j, by omega⟩, Fin.ext rfl⟩`.
-/
theorem sum_castLE {M : Type*} [AddCommMonoid M] {N k : ℕ} (hkN : k ≤ N) (s : Fin N → M)
    (hs : ∀ j : Fin N, k ≤ (j : ℕ) → s j = 0) : ∑ j, s j = ∑ j : Fin k, s (Fin.castLE hkN j) := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE hkN) (Fin.castLE_injective hkN) _ _ (fun j hj => hs j ?_)
    (fun _ => rfl)
  by_contra h
  exact hj ⟨⟨j, by omega⟩, Fin.ext rfl⟩

/- English proof (translation)
Use `conv_lhs => rw [← w.sum_repr v]`. Rewrite using `[map_sum]`. Simplify using `only [map_smul, smul_eq_mul]`. Conclude with `sum_castLE hkN _ fun j hj => by rw [hv j hj, zero_mul]`.
-/
theorem apply_castLE {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {N k : ℕ} (hkN : k ≤ N)
    (w : Module.Basis (Fin N) Ω E) (v : E) (hv : ∀ j : Fin N, k ≤ (j : ℕ) → w.repr v j = 0)
    (ψ : Module.Dual Ω E) :
    ψ v = ∑ j : Fin k, w.repr v (Fin.castLE hkN j) * ψ (w (Fin.castLE hkN j)) := by
  conv_lhs => rw [← w.sum_repr v]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  exact sum_castLE hkN _ fun j hj => by rw [hv j hj, zero_mul]

/- English proof (translation)
Use `set T : Matrix (Fin k) (Fin k) Ω := Matrix.of fun q j : Fin k => w.repr (u q) (Fin.castLE hkN j) with hT`. Set `TΦ : Matrix (Fin k) (Fin k) Φ` to `(algebraMap Ω Φ).mapMatrix T`. Establish `hTΦ : IsUnit TΦ.det`. Rewrite using `[← RingHom.map_det]`. Conclude with `isUnit_iff_ne_zero.2 ((map_ne_zero _).2 hdet)`.

Set `sk : Fin k → Φ` to `fun j => s (Fin.castLE hkN j)`. Use `⟨Matrix.vecMul sk TΦ⁻¹, fun ψ => ?_⟩` and prove the remaining obligations. Establish `hsk : Matrix.vecMul (Matrix.vecMul sk TΦ⁻¹) TΦ = sk`. Rewrite using `[Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hTΦ, Matrix.vecMul_one]`. Rewrite using `[sum_castLE hkN _ fun j hj => by rw [hs j hj, zero_mul]]`.

Repeatedly rewrite using `[apply_castLE hkN w (u _) (hu _) ψ, map_sum, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `h` using `congrFun hsk j`. Simplify using `only [Matrix.vecMul, dotProduct] at h`.

Use `show sk j * _ = _`. Rewrite using `[← h, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Simplify using `only [TΦ, RingHom.mapMatrix_apply, Matrix.map_apply, hT, Matrix.of_apply, map_mul, Matrix.vecMul, dotProduct]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_coords {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ]
    [Algebra Ω Φ] {N k : ℕ} (hkN : k ≤ N) (w : Module.Basis (Fin N) Ω E) (u : Fin k → E)
    (hu : ∀ q (j : Fin N), k ≤ (j : ℕ) → w.repr (u q) j = 0)
    (hdet : (Matrix.of fun q j : Fin k => w.repr (u q) (Fin.castLE hkN j)).det ≠ 0)
    (s : Fin N → Φ) (hs : ∀ j : Fin N, k ≤ (j : ℕ) → s j = 0) :
    ∃ s' : Fin k → Φ, ∀ ψ : Module.Dual Ω E,
      ∑ j, s j * algebraMap Ω Φ (ψ (w j)) = ∑ q, s' q * algebraMap Ω Φ (ψ (u q)) := by
  classical
  set T : Matrix (Fin k) (Fin k) Ω := Matrix.of fun q j : Fin k => w.repr (u q) (Fin.castLE hkN j) with hT
  let TΦ : Matrix (Fin k) (Fin k) Φ := (algebraMap Ω Φ).mapMatrix T
  have hTΦ : IsUnit TΦ.det := by
    rw [← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 hdet)
  let sk : Fin k → Φ := fun j => s (Fin.castLE hkN j)
  refine ⟨Matrix.vecMul sk TΦ⁻¹, fun ψ => ?_⟩
  have hsk : Matrix.vecMul (Matrix.vecMul sk TΦ⁻¹) TΦ = sk := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hTΦ, Matrix.vecMul_one]
  rw [sum_castLE hkN _ fun j hj => by rw [hs j hj, zero_mul]]
  simp_rw [apply_castLE hkN w (u _) (hu _) ψ, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := congrFun hsk j
  simp only [Matrix.vecMul, dotProduct] at h
  show sk j * _ = _
  rw [← h, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [TΦ, RingHom.mapMatrix_apply, Matrix.map_apply, hT, Matrix.of_apply, map_mul, Matrix.vecMul, dotProduct]
  ring

/- English proof (translation)
Rewrite using `[hV, Finset.mul_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← map_mul]`. Use `congr 2`. Simplify using `only [map_div₀]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem expand_coords {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ]
    [Algebra Ω Φ] {n : ℕ} {σ : Type*} (u : Fin n → E) (s' : Fin n → Φ) (ψ : Module.Dual Ω E) (V : Φ)
    (hV : V = ∑ q, s' q * algebraMap Ω Φ (ψ (u q))) (Y Z : Ω) (o : σ) :
    ∑ q, C (algebraMap Ω Φ (ψ (u q) / Z)) * (C (algebraMap Ω Φ Y * s' q) * (X o : MvPolynomial σ Φ)) =
      C (algebraMap Ω Φ (Y / Z) * V) * X o := by
  rw [hV, Finset.mul_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← mul_assoc, ← map_mul]
  congr 2
  simp only [map_div₀]
  ring

end SegreFlagConeAlg

open PairConeAlg SegreFlagConeAlg SegreFlagClosureModel GenericProjClosureDim in

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _ e t ht k hk hkN`. Establish `hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0` using `fun k => by`. Take `⟨j, hj⟩` from `hV.multiProj.relevant k`. Use `⟨j, fun h0 => hj ?_⟩` and prove the remaining obligations. Rewrite using `[pointIdeal, RingHom.mem_ker]`.

Simplify using `[pointConeMap, h0]`. Use `choose c hc using hne`. Establish `hyc : segreVec y c ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => hc k`. Establish `hli` using `ht.linearIndependent`. Establish `hspan` using `TwistedDualGensSpan.proof O Ω K ι y N E B a₀ M φ hφ c hyc`.

Establish `hspan'` using `TwistedDualGensSpan.proof O Ω K ι y N E B' a₀' M' φ' hφ' c hyc`. Set `R : Module.Dual Ω E →ₗ[Ω] (Fin k → Ω)` to `LinearMap.pi fun j => Module.Dual.eval Ω E (w (Fin.castLE hkN j))`. Establish `hR : ∀ ψ j, R ψ j = ψ (w (Fin.castLE hkN j))` using `fun _ _ => rfl`. Establish `hRsurj : Function.Surjective R`. Introduce `a`.

Use `⟨∑ j, a j • w.coord (Fin.castLE hkN j), funext fun j' => ?_⟩` and prove the remaining obligations. Rewrite using `[hR, LinearMap.sum_apply, Finset.sum_eq_single j']`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Simplify using `[(Fin.castLE_injective hkN).ne hj]`.

Simplify using the standard rewrite rules. Choose the witnesses or unpack the hypotheses as in `⟨l, hl⟩ : ∃ l : Fin k → Fin M, LinearIndependent Ω (fun i : Fin k => fun j : Fin k => φ (l i) (w (Fin.castLE hkN j))) := by`. Take `⟨κ, a, ha, hsp, hind⟩` from `exists_linearIndependent' Ω (R ∘ φ)`. Establish `: Finite κ` using `Finite.of_injective a ha`. Use `Fintype.ofFinite κ` as an intermediate fact.

Establish `hcard : Fintype.card κ = k`. Rewrite using `[← finrank_span_eq_card hind, hsp, Set.range_comp, Submodule.span_image, hspan, Submodule.map_top, LinearMap.range_eq_top.2 hRsurj, finrank_top, Module.finrank_fin_fun]`. Set `σ` to `Fintype.equivFinOfCardEq hcard`. Conclude with `⟨a ∘ σ.symm, hind.comp σ.symm σ.symm.injective⟩`. Take `⟨m', hm'⟩` from `exists_flag_ne_zero w e hli φ' hspan' hk hkN`.

Establish `hϖ0 : algebraMap O Ω ϖ ≠ 0`. Introduce `h0`. Establish `hmem : ϖ ∈ (pointIdeal O y).comap (C : O →+* MRing ι O)`. Rewrite using `[Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, h0, map_zero]`. Rewrite `hmem` using `[hV.noTorsion]`.

Conclude with `hϖ.ne_zero (Ideal.mem_bot.1 hmem)`. Establish `hsec : ∀ q : Fin k, ∃ v ∈ B.lat c, (∀ j, Fin.castLE hkN q < j → w.repr v j = 0) ∧ w.repr v (Fin.castLE hkN q) = 1 * ∏ k', y ⟨k', c k'⟩ ^ x (Fin.castLE hkN q) k'`. Introduce `q`. Establish `hmem : (1 * ∏ k', y ⟨k', c k'⟩ ^ x (Fin.castLE hkN q) k' : Ω) ∈ degLat O y (x (Fin.castLE hkN q)) c` using `⟨1, Subalgebra.one_mem _, rfl⟩`. Rewrite `hmem` using `[← hfl.flag.graded c hyc (Fin.castLE hkN q)]`.

Conclude with `hmem`. Use `choose u hu hup hud using hsec`. Establish `hlt : ∀ (q : Fin k) (j : Fin N), (q : ℕ) < (j : ℕ) → w.repr (u q) j = 0` using `fun q j h => hup q j (by rw [Fin.lt_def, Fin.val_castLE]; exact h)`. Establish `hhi : ∀ (q : Fin k) (j : Fin N), k ≤ (j : ℕ) → w.repr (u q) j = 0` using `fun q j h => hlt q j (by omega)`. Use `set T : Matrix (Fin k) (Fin k) Ω := Matrix.of fun q j : Fin k => w.repr (u q) (Fin.castLE hkN j) with hT`.

Establish `hTdet : T.det ≠ 0`. Establish `hlow : T.IsLowerTriangular`. Introduce `i j hij`. Conclude with `hlt i _ (by rw [Fin.val_castLE]; exact Fin.lt_def.1 (show i < j from hij))`. Rewrite using `[Matrix.det_of_isLowerTriangular T hlow]`.

Use `Finset.prod_ne_zero_iff.2 fun q _ => ?_` and prove the remaining obligations. Rewrite using `[hT, Matrix.of_apply, hud q, one_mul]`. Conclude with `Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (hc k')`. Take `⟨s', hs'⟩` from `exists_coords hkN w u hhi hTdet (flagCoord w e t k) (fun j hj => by`. Simplify using `only [flagCoord]`.

Rewrite using `[if_neg (not_lt.2 hj)])`. Use `set Y : Ω := ∏ k, y ⟨k, c k⟩ ^ a₀ k with hYdef`. Use `set Y' : Ω := ∏ k, y ⟨k, c k⟩ ^ a₀' k with hY'def`. Establish `hY : Y ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k)`. Establish `hY' : Y' ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k)`.

Set `Rows : Matrix (Fin k) (Fin k) Ω` to `Matrix.of fun i j : Fin k => φ (l i) (w (Fin.castLE hkN j))`. Establish `hRows : Rows.det ≠ 0`. Establish `hu : IsUnit Rows` using `Matrix.linearIndependent_rows_iff_isUnit.1 hl`. Conclude with `((Matrix.isUnit_iff_isUnit_det Rows).1 hu).ne_zero`. Set `Gm : Matrix (Fin k) (Fin k) Ω` to `fun i q => φ (l i) (u q) / Y`.

Establish `hGm : Gm = Y⁻¹ • (Rows * T.transpose)`. Use extensionality with `i q`. Rewrite using `[Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]`. Use `show φ (l i) (u q) / Y = _`. Rewrite using `[apply_castLE hkN w (u q) (hhi q) (φ (l i)), div_eq_inv_mul]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [Rows, hT, Matrix.of_apply, Matrix.transpose_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `hdet : Gm.det ≠ 0`.

Rewrite using `[hGm, Matrix.det_smul, Matrix.det_mul, Matrix.det_transpose]`. Conclude with `mul_ne_zero (pow_ne_zero _ (inv_ne_zero hY)) (mul_ne_zero hRows hTdet)`. Establish `key : ∀ A1 : Subalgebra O (MvPolynomial (Option (Option K)) Φ), (∀ q : Σ k, ι k, C (algebraMap Ω Φ (y q)) * X (some (some q.1)) ∈ A1) → (∀ i, C (flagClosurePt y w e φ φ' t k ⟨some none, l i⟩) * X (some none) ∈ A1) → C (flagClosurePt y w e φ φ' t k ⟨none, m'⟩) * X none ∈ A1 → ∀ p …`. Introduce `A1 h1 h2 h3`. Set `AC` to `Subalgebra.algebraicClosure A1 (MvPolynomial (Option (Option K)) Φ)`.

Establish `hA : ∀ x ∈ A1, x ∈ AC` using `fun x hx => isAlgebraic_algebraMap (⟨x, hx⟩ : A1)`. Set `ψ : Ω →+* MvPolynomial (Option (Option K)) Φ` to `(C : Φ →+* _).comp (algebraMap Ω Φ)`. Establish `hψ : ∀ a, ψ a = C (algebraMap Ω Φ a)` using `fun _ => rfl`. Set `G : Subalgebra O Ω` to `{ carrier := {a | ψ a ∈ AC} mul_mem' := fun {a b} ha hb => by show ψ (a * b) ∈ AC`. Rewrite using `[map_mul]`.

Conclude with `AC.mul_mem ha hb`. Use the proof step `add_mem' := fun {a b} ha hb => by show ψ (a + b) ∈ AC`. Rewrite using `[map_add]`. Conclude with `AC.add_mem ha hb`. Use the proof step `algebraMap_mem' := fun r => by show ψ (algebraMap O Ω r) ∈ AC`.

Establish `: ψ (algebraMap O Ω r) = algebraMap O (MvPolynomial (Option (Option K)) Φ) r`. Rewrite using `[hψ, ← IsScalarTower.algebraMap_apply, MvPolynomial.algebraMap_apply]`. Rewrite using `[this]`. Conclude with `hA _ (A1.algebraMap_mem r) }`. Establish `hratio : ∀ k j, ψ (y ⟨k, j⟩ / y ⟨k, c k⟩) ∈ AC`.

Introduce `k j`. Establish `h0 : C (algebraMap Ω Φ (y ⟨k, c k⟩)) * X (some (some k)) ∈ nonZeroDivisors (MvPolynomial (Option (Option K)) Φ)` using `mem_nonZeroDivisors_of_ne_zero (mul_ne_zero (by rw [← hψ]; exact (map_ne_zero ψ).2 (hc k)) (X_ne_zero _))`. Use `IsAlgebraic.of_mul h0 (hA _ (h1 ⟨k, c k⟩)) ?_` and prove the remaining obligations. Establish `: C (algebraMap Ω Φ (y ⟨k, c k⟩)) * X (some (some k)) * ψ (y ⟨k, j⟩ / y ⟨k, c k⟩) = C (algebraMap Ω Φ (y ⟨k, j⟩)) * X (some (some k))`. Rewrite using `[hψ, mul_right_comm, ← map_mul, ← map_mul, mul_div_cancel₀ _ (hc k)]`.

Rewrite using `[this]`. Conclude with `hA _ (h1 ⟨k, j⟩)`. Establish `hchart : chartRing O (segreVec y) c ≤ G`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`.

Use `show ψ (segreVec y j / segreVec y c) ∈ AC`. Rewrite using `[segreVec, segreVec, ← Finset.prod_div_distrib, map_prod]`. Conclude with `Subalgebra.prod_mem AC fun k _ => hratio k (j k)`. Establish `hϖG : ψ (algebraMap O Ω ϖ) ∈ AC` using `G.algebraMap_mem ϖ`. Establish `hg : ∀ l q, ψ (φ l (u q) / Y) ∈ AC`.

Introduce `l q`. Take `⟨a, ha, hrep⟩` from `hφ.sections c hyc l (u q) (hu q)`. Establish `: φ l (u q) / Y = a` using `by rw [hrep, mul_div_cancel_right₀ _ hY]`. Rewrite using `[this]`. Conclude with `hchart ha`.

Establish `hg' : ∀ l q, ψ (φ' l (u q) / Y') ∈ AC`. Introduce `l q`. Take `⟨m, hm⟩` from `(hB c hyc).1 (u q) (hu q)`. Take `⟨a, ha, hrep⟩` from `hφ'.sections c hyc l _ hm`. Rewrite `hrep` using `[map_smul, smul_eq_mul]`.

Establish `h0 : ψ (algebraMap O Ω ϖ ^ m) ∈ nonZeroDivisors (MvPolynomial (Option (Option K)) Φ)` using `mem_nonZeroDivisors_of_ne_zero ((map_ne_zero ψ).2 (pow_ne_zero _ hϖ0))`. Establish `hpow : ψ (algebraMap O Ω ϖ ^ m) ∈ AC`. Rewrite using `[map_pow]`. Conclude with `AC.pow_mem hϖG m`. Use `IsAlgebraic.of_mul h0 hpow ?_` and prove the remaining obligations.

Rewrite using `[← map_mul, mul_div_assoc', hrep, mul_div_cancel_right₀ _ hY']`. Conclude with `hchart ha`. Set `W : Fin k → MvPolynomial (Option (Option K)) Φ` to `fun q => C (algebraMap Ω Φ Y * s' q) * X (some none)`. Establish `hx : ∀ lφ, C (flagClosurePt y w e φ φ' t k ⟨some none, lφ⟩) * X (some none) = ∑ q, ψ (φ lφ (u q) / Y) * W q`. Introduce `lφ`.

Use `expand_coords u s' (φ lφ) _ (hs' (φ lφ)) Y Y (some none : Option (Option K))` as an intermediate fact. Rewrite `this` using `[div_self hY, map_one, one_mul]`. Conclude with `this.symm`. Establish `hW : ∀ q, W q ∈ AC`. Introduce `q`.

Use `isAlgebraic_of_mulVec (Gm.map ψ) W (fun i j => hg _ _) (fun i => ?_) ?_ q` and prove the remaining obligations. Establish `: ((Gm.map ψ).mulVec W) i = ∑ q, ψ (φ (l i) (u q) / Y) * W q` using `rfl`. Rewrite using `[this, ← hx (l i)]`. Conclude with `hA _ (h2 i)`. Use `show (ψ.mapMatrix Gm).det ≠ 0`.

Rewrite using `[← RingHom.map_det]`. Conclude with `(map_ne_zero ψ).2 hdet`. Introduce and unpack `⟨(_ | _ | k'), j⟩`. Set `P : Fin M' → MvPolynomial (Option (Option K)) Φ` to `fun l' => ∑ q, ψ (φ' l' (u q) / Y') * W q`. Establish `hP : ∀ l', P l' = C (algebraMap Ω Φ (Y / Y') * flagClosurePt y w e φ φ' t k ⟨none, l'⟩) * X (some none)` using `fun l' => expand_coords u s' (φ' l') _ (hs' (φ' l')) Y Y' (some none : Option (Option K))`.

Establish `hPA : ∀ l', P l' ∈ AC` using `fun l' => Subalgebra.sum_mem AC fun q _ => AC.mul_mem (hg' l' q) (hW q)`. Establish `hP0 : P m' ∈ nonZeroDivisors (MvPolynomial (Option (Option K)) Φ)`. Rewrite using `[hP]`. Use `mem_nonZeroDivisors_of_ne_zero (mul_ne_zero ?_ (X_ne_zero _))` and prove the remaining obligations. Rewrite using `[Ne, C_eq_zero]`.

Conclude with `mul_ne_zero ((map_ne_zero _).2 (div_ne_zero hY hY')) hm'`. Use `IsAlgebraic.of_mul hP0 (hPA m') ?_` and prove the remaining obligations. Establish `: P m' * (C (flagClosurePt y w e φ φ' t k ⟨none, j⟩) * X none) = P j * (C (flagClosurePt y w e φ φ' t k ⟨none, m'⟩) * X none)`. Rewrite using `[hP m', hP j]`. Simplify using `only [map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `AC.mul_mem (hPA j) (hA _ h3)`. Use `show C (flagClosurePt y w e φ φ' t k ⟨some none, j⟩) * X (some none) ∈ AC`. Rewrite using `[hx]`.

Conclude with `Subalgebra.sum_mem AC fun q _ => AC.mul_mem (hg j q) (hW q)`. Conclude with `hA _ (h1 ⟨k', j⟩)`. Conclude with `⟨l, m', hl, hm', key _ (fun q => Algebra.subset_adjoin (Or.inl ⟨q, rfl⟩)) (fun i => Algebra.subset_adjoin (Or.inr ⟨Sum.inl i, rfl⟩)) (Algebra.subset_adjoin (Or.inr ⟨Sum.inr (), rfl⟩))⟩`.
-/
theorem SegreFlagConeAlg.proof : SegreFlagConeAlg.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk hkN
  classical

  have hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0 := fun k => by
    obtain ⟨j, hj⟩ := hV.multiProj.relevant k
    refine ⟨j, fun h0 => hj ?_⟩
    rw [pointIdeal, RingHom.mem_ker]
    simp [pointConeMap, h0]
  choose c hc using hne
  have hyc : segreVec y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hli := ht.linearIndependent
  have hspan := TwistedDualGensSpan.proof O Ω K ι y N E B a₀ M φ hφ c hyc
  have hspan' := TwistedDualGensSpan.proof O Ω K ι y N E B' a₀' M' φ' hφ' c hyc

  let R : Module.Dual Ω E →ₗ[Ω] (Fin k → Ω) :=
    LinearMap.pi fun j => Module.Dual.eval Ω E (w (Fin.castLE hkN j))
  have hR : ∀ ψ j, R ψ j = ψ (w (Fin.castLE hkN j)) := fun _ _ => rfl
  have hRsurj : Function.Surjective R := by
    intro a
    refine ⟨∑ j, a j • w.coord (Fin.castLE hkN j), funext fun j' => ?_⟩
    rw [hR, LinearMap.sum_apply, Finset.sum_eq_single j']
    · simp
    · intro j _ hj
      simp [(Fin.castLE_injective hkN).ne hj]
    · simp

  obtain ⟨l, hl⟩ : ∃ l : Fin k → Fin M,
      LinearIndependent Ω (fun i : Fin k => fun j : Fin k => φ (l i) (w (Fin.castLE hkN j))) := by
    obtain ⟨κ, a, ha, hsp, hind⟩ := exists_linearIndependent' Ω (R ∘ φ)
    have : Finite κ := Finite.of_injective a ha
    have := Fintype.ofFinite κ
    have hcard : Fintype.card κ = k := by
      rw [← finrank_span_eq_card hind, hsp, Set.range_comp, Submodule.span_image, hspan, Submodule.map_top,
        LinearMap.range_eq_top.2 hRsurj, finrank_top, Module.finrank_fin_fun]
    let σ := Fintype.equivFinOfCardEq hcard
    exact ⟨a ∘ σ.symm, hind.comp σ.symm σ.symm.injective⟩
  obtain ⟨m', hm'⟩ := exists_flag_ne_zero w e hli φ' hspan' hk hkN

  have hϖ0 : algebraMap O Ω ϖ ≠ 0 := by
    intro h0
    have hmem : ϖ ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := by
      rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, h0,
        map_zero]
    rw [hV.noTorsion] at hmem
    exact hϖ.ne_zero (Ideal.mem_bot.1 hmem)

  have hsec : ∀ q : Fin k, ∃ v ∈ B.lat c, (∀ j, Fin.castLE hkN q < j → w.repr v j = 0) ∧
      w.repr v (Fin.castLE hkN q) = 1 * ∏ k', y ⟨k', c k'⟩ ^ x (Fin.castLE hkN q) k' := by
    intro q
    have hmem : (1 * ∏ k', y ⟨k', c k'⟩ ^ x (Fin.castLE hkN q) k' : Ω) ∈
        degLat O y (x (Fin.castLE hkN q)) c := ⟨1, Subalgebra.one_mem _, rfl⟩
    rw [← hfl.flag.graded c hyc (Fin.castLE hkN q)] at hmem
    exact hmem
  choose u hu hup hud using hsec
  have hlt : ∀ (q : Fin k) (j : Fin N), (q : ℕ) < (j : ℕ) → w.repr (u q) j = 0 := fun q j h =>
    hup q j (by rw [Fin.lt_def, Fin.val_castLE]; exact h)
  have hhi : ∀ (q : Fin k) (j : Fin N), k ≤ (j : ℕ) → w.repr (u q) j = 0 := fun q j h => hlt q j (by omega)

  set T : Matrix (Fin k) (Fin k) Ω := Matrix.of fun q j : Fin k => w.repr (u q) (Fin.castLE hkN j) with hT
  have hTdet : T.det ≠ 0 := by
    have hlow : T.IsLowerTriangular := by
      intro i j hij
      exact hlt i _ (by rw [Fin.val_castLE]; exact Fin.lt_def.1 (show i < j from hij))
    rw [Matrix.det_of_isLowerTriangular T hlow]
    refine Finset.prod_ne_zero_iff.2 fun q _ => ?_
    rw [hT, Matrix.of_apply, hud q, one_mul]
    exact Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (hc k')
  obtain ⟨s', hs'⟩ := exists_coords hkN w u hhi hTdet (flagCoord w e t k) (fun j hj => by
    simp only [flagCoord]
    rw [if_neg (not_lt.2 hj)])
  set Y : Ω := ∏ k, y ⟨k, c k⟩ ^ a₀ k with hYdef
  set Y' : Ω := ∏ k, y ⟨k, c k⟩ ^ a₀' k with hY'def
  have hY : Y ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k)
  have hY' : Y' ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k)

  let Rows : Matrix (Fin k) (Fin k) Ω := Matrix.of fun i j : Fin k => φ (l i) (w (Fin.castLE hkN j))
  have hRows : Rows.det ≠ 0 := by
    have hu : IsUnit Rows := Matrix.linearIndependent_rows_iff_isUnit.1 hl
    exact ((Matrix.isUnit_iff_isUnit_det Rows).1 hu).ne_zero
  let Gm : Matrix (Fin k) (Fin k) Ω := fun i q => φ (l i) (u q) / Y
  have hGm : Gm = Y⁻¹ • (Rows * T.transpose) := by
    ext i q
    rw [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
    show φ (l i) (u q) / Y = _
    rw [apply_castLE hkN w (u q) (hhi q) (φ (l i)), div_eq_inv_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Rows, hT, Matrix.of_apply, Matrix.transpose_apply]
    ring
  have hdet : Gm.det ≠ 0 := by
    rw [hGm, Matrix.det_smul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hY)) (mul_ne_zero hRows hTdet)

  have key : ∀ A1 : Subalgebra O (MvPolynomial (Option (Option K)) Φ),
      (∀ q : Σ k, ι k, C (algebraMap Ω Φ (y q)) * X (some (some q.1)) ∈ A1) →
      (∀ i, C (flagClosurePt y w e φ φ' t k ⟨some none, l i⟩) * X (some none) ∈ A1) →
      C (flagClosurePt y w e φ φ' t k ⟨none, m'⟩) * X none ∈ A1 →
      ∀ p : Σ o, bundleIdx (bundleIdx ι M) M' o,
        IsAlgebraic A1 (C (flagClosurePt y w e φ φ' t k p) * X p.1) := by
    intro A1 h1 h2 h3
    let AC := Subalgebra.algebraicClosure A1 (MvPolynomial (Option (Option K)) Φ)
    have hA : ∀ x ∈ A1, x ∈ AC := fun x hx => isAlgebraic_algebraMap (⟨x, hx⟩ : A1)
    let ψ : Ω →+* MvPolynomial (Option (Option K)) Φ := (C : Φ →+* _).comp (algebraMap Ω Φ)
    have hψ : ∀ a, ψ a = C (algebraMap Ω Φ a) := fun _ => rfl

    let G : Subalgebra O Ω :=
      { carrier := {a | ψ a ∈ AC}
        mul_mem' := fun {a b} ha hb => by
          show ψ (a * b) ∈ AC
          rw [map_mul]
          exact AC.mul_mem ha hb
        add_mem' := fun {a b} ha hb => by
          show ψ (a + b) ∈ AC
          rw [map_add]
          exact AC.add_mem ha hb
        algebraMap_mem' := fun r => by
          show ψ (algebraMap O Ω r) ∈ AC
          have : ψ (algebraMap O Ω r) = algebraMap O (MvPolynomial (Option (Option K)) Φ) r := by
            rw [hψ, ← IsScalarTower.algebraMap_apply, MvPolynomial.algebraMap_apply]
          rw [this]
          exact hA _ (A1.algebraMap_mem r) }
    have hratio : ∀ k j, ψ (y ⟨k, j⟩ / y ⟨k, c k⟩) ∈ AC := by
      intro k j
      have h0 : C (algebraMap Ω Φ (y ⟨k, c k⟩)) * X (some (some k)) ∈
          nonZeroDivisors (MvPolynomial (Option (Option K)) Φ) :=
        mem_nonZeroDivisors_of_ne_zero (mul_ne_zero (by rw [← hψ]; exact (map_ne_zero ψ).2 (hc k)) (X_ne_zero _))
      refine IsAlgebraic.of_mul h0 (hA _ (h1 ⟨k, c k⟩)) ?_
      have : C (algebraMap Ω Φ (y ⟨k, c k⟩)) * X (some (some k)) * ψ (y ⟨k, j⟩ / y ⟨k, c k⟩) =
          C (algebraMap Ω Φ (y ⟨k, j⟩)) * X (some (some k)) := by
        rw [hψ, mul_right_comm, ← map_mul, ← map_mul, mul_div_cancel₀ _ (hc k)]
      rw [this]
      exact hA _ (h1 ⟨k, j⟩)
    have hchart : chartRing O (segreVec y) c ≤ G := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨j, rfl⟩
      show ψ (segreVec y j / segreVec y c) ∈ AC
      rw [segreVec, segreVec, ← Finset.prod_div_distrib, map_prod]
      exact Subalgebra.prod_mem AC fun k _ => hratio k (j k)
    have hϖG : ψ (algebraMap O Ω ϖ) ∈ AC := G.algebraMap_mem ϖ

    have hg : ∀ l q, ψ (φ l (u q) / Y) ∈ AC := by
      intro l q
      obtain ⟨a, ha, hrep⟩ := hφ.sections c hyc l (u q) (hu q)
      have : φ l (u q) / Y = a := by rw [hrep, mul_div_cancel_right₀ _ hY]
      rw [this]
      exact hchart ha
    have hg' : ∀ l q, ψ (φ' l (u q) / Y') ∈ AC := by
      intro l q
      obtain ⟨m, hm⟩ := (hB c hyc).1 (u q) (hu q)
      obtain ⟨a, ha, hrep⟩ := hφ'.sections c hyc l _ hm
      rw [map_smul, smul_eq_mul] at hrep
      have h0 : ψ (algebraMap O Ω ϖ ^ m) ∈ nonZeroDivisors (MvPolynomial (Option (Option K)) Φ) :=
        mem_nonZeroDivisors_of_ne_zero ((map_ne_zero ψ).2 (pow_ne_zero _ hϖ0))
      have hpow : ψ (algebraMap O Ω ϖ ^ m) ∈ AC := by
        rw [map_pow]
        exact AC.pow_mem hϖG m
      refine IsAlgebraic.of_mul h0 hpow ?_
      rw [← map_mul, mul_div_assoc', hrep, mul_div_cancel_right₀ _ hY']
      exact hchart ha

    let W : Fin k → MvPolynomial (Option (Option K)) Φ := fun q =>
      C (algebraMap Ω Φ Y * s' q) * X (some none)
    have hx : ∀ lφ, C (flagClosurePt y w e φ φ' t k ⟨some none, lφ⟩) * X (some none) =
        ∑ q, ψ (φ lφ (u q) / Y) * W q := by
      intro lφ
      have := expand_coords u s' (φ lφ) _ (hs' (φ lφ)) Y Y (some none : Option (Option K))
      rw [div_self hY, map_one, one_mul] at this
      exact this.symm
    have hW : ∀ q, W q ∈ AC := by
      intro q
      refine isAlgebraic_of_mulVec (Gm.map ψ) W (fun i j => hg _ _) (fun i => ?_) ?_ q
      · have : ((Gm.map ψ).mulVec W) i = ∑ q, ψ (φ (l i) (u q) / Y) * W q := rfl
        rw [this, ← hx (l i)]
        exact hA _ (h2 i)
      · show (ψ.mapMatrix Gm).det ≠ 0
        rw [← RingHom.map_det]
        exact (map_ne_zero ψ).2 hdet
    rintro ⟨(_ | _ | k'), j⟩
    ·
      let P : Fin M' → MvPolynomial (Option (Option K)) Φ := fun l' => ∑ q, ψ (φ' l' (u q) / Y') * W q
      have hP : ∀ l', P l' =
          C (algebraMap Ω Φ (Y / Y') * flagClosurePt y w e φ φ' t k ⟨none, l'⟩) * X (some none) :=
        fun l' => expand_coords u s' (φ' l') _ (hs' (φ' l')) Y Y' (some none : Option (Option K))
      have hPA : ∀ l', P l' ∈ AC := fun l' => Subalgebra.sum_mem AC fun q _ => AC.mul_mem (hg' l' q) (hW q)
      have hP0 : P m' ∈ nonZeroDivisors (MvPolynomial (Option (Option K)) Φ) := by
        rw [hP]
        refine mem_nonZeroDivisors_of_ne_zero (mul_ne_zero ?_ (X_ne_zero _))
        rw [Ne, C_eq_zero]
        exact mul_ne_zero ((map_ne_zero _).2 (div_ne_zero hY hY')) hm'
      refine IsAlgebraic.of_mul hP0 (hPA m') ?_
      have : P m' * (C (flagClosurePt y w e φ φ' t k ⟨none, j⟩) * X none) =
          P j * (C (flagClosurePt y w e φ φ' t k ⟨none, m'⟩) * X none) := by
        rw [hP m', hP j]
        simp only [map_mul]
        ring
      rw [this]
      exact AC.mul_mem (hPA j) (hA _ h3)
    ·
      show C (flagClosurePt y w e φ φ' t k ⟨some none, j⟩) * X (some none) ∈ AC
      rw [hx]
      exact Subalgebra.sum_mem AC fun q _ => AC.mul_mem (hg j q) (hW q)
    ·
      exact hA _ (h1 ⟨k', j⟩)
  exact ⟨l, m', hl, hm', key _ (fun q => Algebra.subset_adjoin (Or.inl ⟨q, rfl⟩))
    (fun i => Algebra.subset_adjoin (Or.inr ⟨Sum.inl i, rfl⟩))
    (Algebra.subset_adjoin (Or.inr ⟨Sum.inr (), rfl⟩))⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
