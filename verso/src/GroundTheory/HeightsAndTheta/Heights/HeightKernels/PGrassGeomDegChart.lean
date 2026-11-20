import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassGeomDegChart
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGrassLeRoot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheetA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Matrix

noncomputable section

namespace GrassmannianGeometricDegreeChart

variable {n : ℕ}

def single1 (c : Fin (1 + n)) : PlIdx 1 n := ⟨{c}, Finset.card_singleton c⟩

/- English proof (translation)
Take `⟨c, hc⟩` from `Finset.card_eq_one.mp I.2`. Establish `h2 : ∀ x ∈ I.1, x = c` using `fun x hx => by rw [hc] at hx; exact Finset.mem_singleton.mp hx`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[h2 _ (Finset.orderEmbOfFin_mem I.1 I.2 0)]`. Conclude with `hc`.
-/
theorem eq_single1 (I : PlIdx 1 n) : I = single1 (I.1.orderEmbOfFin I.2 0) := by
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp I.2
  have h2 : ∀ x ∈ I.1, x = c := fun x hx => by rw [hc] at hx; exact Finset.mem_singleton.mp hx
  apply Subtype.ext
  rw [h2 _ (Finset.orderEmbOfFin_mem I.1 I.2 0)]
  exact hc

/- English proof (translation)
The claim follows from `funext fun k => congrArg i (Subsingleton.elim 0 k)`.
-/
theorem fin_one_fun_eq_const {α : Type*} (i : Fin 1 → α) : (fun _ => i 0) = i :=
  funext fun k => congrArg i (Subsingleton.elim 0 k)

def a0 : Σ _ : Fin 1, PlIdx 1 n := ⟨0, single1 (Fin.castAdd n 0)⟩

def chartPt (z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ) : Fin 1 → Matrix (Fin 1) (Fin n) ℂ :=
  fun _ _ b => z ⟨0, single1 (Fin.natAdd 1 b)⟩ / z a0

/- English proof (translation)
Use function extensionality and compare the values at `p`. Take `⟨k, I⟩` from `p`. Take `rfl : k = 0` from `Subsingleton.elim _ _`. Use `conv_rhs => rw [eq_single1 I]`. Simplify using `only [rootCoord, colsOf, onePipe, Matrix.det_unique, Matrix.submatrix_apply, Matrix.of_apply, id]`.

Generalize the expression as in `I.1.orderEmbOfFin I.2 0 = c`. Use `Fin.addCases (fun a => ?_) (fun b => ?_) c` and prove the remaining obligations. Take `rfl : a = 0` from `Subsingleton.elim _ _`. Simplify using `only [Fin.append_left]`. Rewrite using `[show (default : Fin 1) = 0 from rfl, Matrix.one_apply_eq, one_mul]`.

Both sides reduce to the same expression. Simplify using `only [Fin.append_right, chartPt]`. Conclude with `div_mul_cancel₀ _ ht`.
-/
theorem rootCoord_mul (z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ) (ht : z a0 ≠ 0) :
    (fun p => rootCoord (chartPt z) p * z a0) = z := by
  funext p
  obtain ⟨k, I⟩ := p
  obtain rfl : k = 0 := Subsingleton.elim _ _
  conv_rhs => rw [eq_single1 I]
  simp only [rootCoord, colsOf, onePipe, Matrix.det_unique, Matrix.submatrix_apply, Matrix.of_apply, id]
  generalize I.1.orderEmbOfFin I.2 0 = c
  refine Fin.addCases (fun a => ?_) (fun b => ?_) c
  · obtain rfl : a = 0 := Subsingleton.elim _ _
    simp only [Fin.append_left]
    rw [show (default : Fin 1) = 0 from rfl, Matrix.one_apply_eq, one_mul]
    rfl
  · simp only [Fin.append_right, chartPt]
    exact div_mul_cancel₀ _ ht

/- English proof (translation)
Establish `key : ∀ z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ, z a0 ≠ 0 → MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) g) = 0`. Introduce `z hz`. Establish `h0 : mConeMap (rootCoord (chartPt z)) g = 0` using `GrassLeRoot.proof 1 1 n _ hg`. Establish `h1` using `congrArg ((MvPolynomial.aeval fun _ : Fin 1 => z a0).restrictScalars ℤ) h0`. Rewrite `h1` using `[map_zero, mConeMap]`.

Rewrite `h1` using `[show ((MvPolynomial.aeval fun _ : Fin 1 => z a0).restrictScalars ℤ) ((MvPolynomial.aeval fun p => MvPolynomial.C (rootCoord (chartPt z) p) * MvPolynomial.X p.1) g) = (((MvPolynomial.aeval fun _ : Fin 1 => z a0).restrictScalars ℤ).comp (MvPolynomial.aeval fun p => MvPolynomial.C …`. Simplify using `only [AlgHom.restrictScalars_apply, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Algebra.algebraMap_self, RingHom.id_apply] at h1`. Rewrite `h1` using `[rootCoord_mul z hz]`. Rewrite using `[MvPolynomial.eval_map, ← h1, MvPolynomial.aeval_def]`. Both sides reduce to the same expression.

Establish `hq : MvPolynomial.map (Int.castRingHom ℂ) g * MvPolynomial.X a0 = 0`. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `z`. Rewrite using `[map_mul, MvPolynomial.eval_X, map_zero]`. Distinguish the cases in `hz : z a0 = 0`.

Rewrite using `[hz, mul_zero]`. Rewrite using `[key z hz, zero_mul]`. Break down `mul_eq_zero.mp hq with h | h` into its components or cases. Rewrite using `[h, map_zero]`. Conclude with `absurd h (MvPolynomial.X_ne_zero a0)`.
-/
theorem eval_eq_zero {g : MRing (plBlocks 1 1 n)} (hg : g ∈ grassIdeal 1 1 n) (z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ) :
    MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) g) = 0 := by
  have key : ∀ z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ, z a0 ≠ 0 →
      MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) g) = 0 := by
    intro z hz
    have h0 : mConeMap (rootCoord (chartPt z)) g = 0 := GrassLeRoot.proof 1 1 n _ hg
    have h1 := congrArg ((MvPolynomial.aeval fun _ : Fin 1 => z a0).restrictScalars ℤ) h0
    rw [map_zero, mConeMap] at h1
    rw [show ((MvPolynomial.aeval fun _ : Fin 1 => z a0).restrictScalars ℤ)
        ((MvPolynomial.aeval fun p => MvPolynomial.C (rootCoord (chartPt z) p) * MvPolynomial.X p.1) g) =
        (((MvPolynomial.aeval fun _ : Fin 1 => z a0).restrictScalars ℤ).comp
          (MvPolynomial.aeval fun p => MvPolynomial.C (rootCoord (chartPt z) p) * MvPolynomial.X p.1)) g from rfl,
      MvPolynomial.comp_aeval] at h1
    simp only [AlgHom.restrictScalars_apply, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Algebra.algebraMap_self, RingHom.id_apply] at h1
    rw [rootCoord_mul z hz] at h1
    rw [MvPolynomial.eval_map, ← h1, MvPolynomial.aeval_def]
    rfl
  have hq : MvPolynomial.map (Int.castRingHom ℂ) g * MvPolynomial.X a0 = 0 := by
    apply MvPolynomial.funext
    intro z
    rw [map_mul, MvPolynomial.eval_X, map_zero]
    by_cases hz : z a0 = 0
    · rw [hz, mul_zero]
    · rw [key z hz, zero_mul]
  rcases mul_eq_zero.mp hq with h | h
  · rw [h, map_zero]
  · exact absurd h (MvPolynomial.X_ne_zero a0)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => h.1, fun h => ⟨h, fun _ hf => eval_eq_zero hf z⟩⟩`.
-/
theorem mem_mcPts (z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ) :
    z ∈ mcPts (grassIdeal 1 1 n) ↔ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ hf => eval_eq_zero hf z⟩⟩

/- English proof (translation)
Simplify using `[segre]`.
-/
theorem segre_eq (z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ) (i : Fin 1 → PlIdx 1 n) :
    segre (ι := plBlocks 1 1 n) z i = z ⟨0, i 0⟩ := by
  simp [segre]

/- English proof (translation)
Take `⟨k, I⟩` from `p`. Take `rfl : k = 0` from `Subsingleton.elim _ _`. Rewrite using `[segre_eq]`.
-/
theorem apply_eq_segre (z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ) (p : Σ _ : Fin 1, PlIdx 1 n) :
    z p = segre (ι := plBlocks 1 1 n) z (fun _ => p.2) := by
  obtain ⟨k, I⟩ := p
  obtain rfl : k = 0 := Subsingleton.elim _ _
  rw [segre_eq]

def blockLift (x : PlIdx 1 n → ℂ) : (Σ _ : Fin 1, PlIdx 1 n) → ℂ := fun p => x p.2

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[segre_eq]`. Both sides reduce to the same expression.
-/
theorem segre_blockLift (x : PlIdx 1 n → ℂ) :
    segre (ι := plBlocks 1 1 n) (blockLift x) = fun i => x (i 0) := by
  funext i
  rw [segre_eq]
  rfl

/- English proof (translation)
Simplify using `[PlIdx, Fintype.card_subtype, Finset.card_powersetCard, add_comm]`.
-/
theorem card_seg : Fintype.card (Fin 1 → PlIdx 1 n) = n + 1 := by
  simp [PlIdx, Fintype.card_subtype, Finset.card_powersetCard, add_comm]

/- English proof (translation)
Take `⟨i, hi⟩` from `Function.ne_iff.mp hw`. Use `⟨(mem_mcPts _).2 fun _ => ⟨i 0, ?_⟩, ?_⟩` and prove the remaining obligations. Simplify `hi` using `[blockLift, fin_one_fun_eq_const]`. Rewrite using `[segre_blockLift]`. Use function extensionality and compare the values at `i'`.

Simplify using `only [fin_one_fun_eq_const]`.
-/
theorem exists_of_ne_zero {w : (Fin 1 → PlIdx 1 n) → ℂ} (hw : w ≠ 0) :
    blockLift (fun I => w fun _ => I) ∈ mcPts (grassIdeal 1 1 n) ∧
      segre (ι := plBlocks 1 1 n) (blockLift fun I => w fun _ => I) = w := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  refine ⟨(mem_mcPts _).2 fun _ => ⟨i 0, ?_⟩, ?_⟩
  · simpa [blockLift, fin_one_fun_eq_const] using hi
  · rw [segre_blockLift]
    funext i'
    simp only [fin_one_fun_eq_const]

/- English proof (translation)
Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `w hw`. Assume the negation of the conclusion as `hne`. Take `⟨hm, hs⟩` from `exists_of_ne_zero hne`. Conclude with `hΨ _ hm (by rw [hs]; exact hw)`.
-/
theorem injective_of_good {Ψ : (((k : Fin 1) → plBlocks 1 1 n k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)}
    (hΨ : IsGoodProj (grassIdeal 1 1 n) Ψ) : Function.Injective Ψ := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  by_contra hne
  obtain ⟨hm, hs⟩ := exists_of_ne_zero hne
  exact hΨ _ hm (by rw [hs]; exact hw)

/- English proof (translation)
Set `Ψ0` to `LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFinOfCardEq (card_seg (n := n))).symm`. Use `⟨Ψ0.toLinearMap, fun z hz h0 => ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `hz.1 0`. Establish `hs : segre (ι` using `plBlocks 1 1 n) z = 0 := Ψ0.map_eq_zero_iff.mp h0`. Conclude with `hi (by rw [apply_eq_segre z ⟨0, i⟩, hs]; rfl)`.
-/
theorem exists_good (n : ℕ) :
    ∃ Ψ : (((k : Fin 1) → plBlocks 1 1 n k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ), IsGoodProj (grassIdeal 1 1 n) Ψ := by
  let Ψ0 := LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFinOfCardEq (card_seg (n := n))).symm
  refine ⟨Ψ0.toLinearMap, fun z hz h0 => ?_⟩
  obtain ⟨i, hi⟩ := hz.1 0
  have hs : segre (ι := plBlocks 1 1 n) z = 0 := Ψ0.map_eq_zero_iff.mp h0
  exact hi (by rw [apply_eq_segre z ⟨0, i⟩, hs]; rfl)

/- English proof (translation)
Establish `hinj` using `injective_of_good hΨ`. Establish `hrank : Module.finrank ℂ ((Fin 1 → PlIdx 1 n) → ℂ) = Module.finrank ℂ (Fin (n + 1) → ℂ)`. Rewrite using `[Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, card_seg, Fintype.card_fin]`. Establish `hsurj` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj`. Use `set L := (LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩).symm with hL`.

Establish `hΨL : ∀ v, Ψ (L v) = v` using `(LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩).apply_symm_apply`. Establish `hLΨ : ∀ w, L (Ψ w) = w` using `(LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩).symm_apply_apply`. Use `set M := L.trans (LinearEquiv.funCongrLeft ℂ ℂ (Equiv.funUnique (Fin 1) (PlIdx 1 n))).symm with hM`. Use `set B := LinearMap.toMatrix' M.toLinearMap with hB`. Establish `hmv : ∀ v, B *ᵥ v = M v` using `fun v => LinearMap.toMatrix'_mulVec _ _`.

Establish `hMapp : ∀ v I, M v I = L v fun _ => I` using `fun v I => rfl`. Use `⟨B, ?_, ?_⟩` and prove the remaining obligations. Use `M.bijective using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `v`. Conclude with `hmv v`.

Establish `hseg : ∀ v, segre (ι` using `plBlocks 1 1 n) (blockLift (M v)) = L v := by`. Introduce `v`. Rewrite using `[segre_blockLift]`. Use function extensionality and compare the values at `i`. Rewrite using `[hMapp, fin_one_fun_eq_const]`.

Establish `hMdiff : Differentiable ℂ fun v => M v` using `(LinearMap.toContinuousLinearMap M.toLinearMap).differentiable`. Establish `hcons : Differentiable ℂ fun y' : Fin n → ℂ => (Fin.cons 1 y' : Fin (n + 1) → ℂ)`. Rewrite using `[differentiable_pi]`. Introduce `c`. Use `Fin.cases ?_ (fun i => ?_) c` and prove the remaining obligations.

Simplify using `only [Fin.cons_zero]`. Conclude with `differentiable_const _`. Simplify using `only [Fin.cons_succ]`. Conclude with `differentiable_apply i`. Use `set γ0 : (Fin n → ℂ) → (Σ _ : Fin 1, PlIdx 1 n) → ℂ := fun y' => blockLift (M (Fin.cons 1 y')) with hγ0`.

Establish `hγ0d : ∀ y', DifferentiableAt ℂ γ0 y'`. Introduce `y'`. Rewrite using `[differentiableAt_pi]`. Introduce `p`. Conclude with `((differentiable_apply p.2).comp (hMdiff.comp hcons)) y'`.

Establish `hγ0mem : ∀ y', γ0 y' ∈ mcPts (grassIdeal 1 1 n)`. Introduce `y'`. Establish `hv : (Fin.cons 1 y' : Fin (n + 1) → ℂ) ≠ 0` using `fun h => one_ne_zero (congrFun h 0)`. Take `⟨I, hI⟩` from `Function.ne_iff.mp ((M.map_ne_zero_iff).mpr hv)`. Conclude with `(mem_mcPts _).2 fun _ => ⟨I, hI⟩`.

Establish `hpot : ∀ y', Real.log ((fsMulti (plBlocks 1 1 n)).h (γ0 y')) = hermChartPot (Bᴴ * B) y'`. Introduce `y'`. Use `set v : Fin (n + 1) → ℂ := Fin.cons 1 y'`. Establish `h1 : (fsMulti (plBlocks 1 1 n)).h (γ0 y') = ‖WithLp.toLp 2 (B *ᵥ v)‖`. Rewrite using `[hmv]`.

Simplify using `[fsMulti, HermLine.ofMetrics, fsMetric, hγ0, blockLift, v]`. Establish `h2 : (star v ⬝ᵥ ((Bᴴ * B) *ᵥ v)).re = ∑ I, ‖(B *ᵥ v) I‖ ^ 2`. Rewrite using `[← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]`. Simplify using `[dotProduct, Complex.re_sum, Complex.conj_mul']`. Use `norm_cast`.

Rewrite using `[hermChartPot, h1, h2, EuclideanSpace.norm_eq]`. Unfold `ptsIntegralAt chartMass`. Use `congr 1`. Use function extensionality and compare the values at `y`. Establish `hfib : fibre (grassIdeal 1 1 n) Ψ y = {L (Fin.cons 1 y)}`.

Use extensionality with `w`. Simplify using `only [fibre, Set.mem_ofPred_eq, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, -, -, hw⟩`. Rewrite using `[← hw, hLΨ]`.

Introduce and unpack `rfl`. Conclude with `⟨γ0 y, hγ0mem y, hseg _, hΨL _⟩`. Establish `hsheet : IsSheet (grassIdeal 1 1 n) Ψ y (L (Fin.cons 1 y)) γ0` using `⟨hseg _, Eventually.of_forall fun y' => ⟨hγ0d y', hγ0mem y', by rw [hseg, hΨL]⟩⟩`. Rewrite using `[hfib, finsum_mem_singleton]`. Unfold `sheetDensity`.

Use `split_ifs with hγ`. Establish `hev : (fun y' => Real.log ((fsMulti (plBlocks 1 1 n)).h (hγ.choose y'))) =ᶠ[𝓝 y] hermChartPot (Bᴴ * B)` using `by filter_upwards [hγ.choose_spec.2] with y' hy'`. Establish `hs : segre (ι` using `plBlocks 1 1 n) (hγ.choose y') = segre (ι := plBlocks 1 1 n) (γ0 y') := by`. Rewrite using `[hseg, ← hy'.2.2, hLΨ]`. Establish `he : hγ.choose y' = γ0 y'`.

Use function extensionality and compare the values at `p`. Rewrite using `[apply_eq_segre (hγ.choose y') p, apply_eq_segre (γ0 y') p, hs]`. Rewrite using `[he, hpot]`. Simplify using `only [one_mul, maDensity, cxHessian_congr hev]`. Conclude with `absurd ⟨γ0, hsheet⟩ hγ`.
-/
theorem ptsIntegralAt_eq {Ψ : (((k : Fin 1) → plBlocks 1 1 n k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)}
    (hΨ : IsGoodProj (grassIdeal 1 1 n) Ψ) :
    ∃ B : Matrix (PlIdx 1 n) (Fin (n + 1)) ℂ, Function.Bijective B.mulVec ∧
      ptsIntegralAt (grassIdeal 1 1 n) Ψ (fun _ z => Real.log ((fsMulti (plBlocks 1 1 n)).h z)) (fun _ => 1) =
        chartMass (Bᴴ * B) := by
  have hinj := injective_of_good hΨ
  have hrank : Module.finrank ℂ ((Fin 1 → PlIdx 1 n) → ℂ) = Module.finrank ℂ (Fin (n + 1) → ℂ) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, card_seg, Fintype.card_fin]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj
  set L := (LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩).symm with hL
  have hΨL : ∀ v, Ψ (L v) = v := (LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩).apply_symm_apply
  have hLΨ : ∀ w, L (Ψ w) = w := (LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩).symm_apply_apply
  set M := L.trans (LinearEquiv.funCongrLeft ℂ ℂ (Equiv.funUnique (Fin 1) (PlIdx 1 n))).symm with hM
  set B := LinearMap.toMatrix' M.toLinearMap with hB
  have hmv : ∀ v, B *ᵥ v = M v := fun v => LinearMap.toMatrix'_mulVec _ _
  have hMapp : ∀ v I, M v I = L v fun _ => I := fun v I => rfl
  refine ⟨B, ?_, ?_⟩
  · convert M.bijective using 1
    funext v
    exact hmv v
  have hseg : ∀ v, segre (ι := plBlocks 1 1 n) (blockLift (M v)) = L v := by
    intro v
    rw [segre_blockLift]
    funext i
    rw [hMapp, fin_one_fun_eq_const]
  have hMdiff : Differentiable ℂ fun v => M v := (LinearMap.toContinuousLinearMap M.toLinearMap).differentiable
  have hcons : Differentiable ℂ fun y' : Fin n → ℂ => (Fin.cons 1 y' : Fin (n + 1) → ℂ) := by
    rw [differentiable_pi]
    intro c
    refine Fin.cases ?_ (fun i => ?_) c
    · simp only [Fin.cons_zero]
      exact differentiable_const _
    · simp only [Fin.cons_succ]
      exact differentiable_apply i
  set γ0 : (Fin n → ℂ) → (Σ _ : Fin 1, PlIdx 1 n) → ℂ := fun y' => blockLift (M (Fin.cons 1 y')) with hγ0
  have hγ0d : ∀ y', DifferentiableAt ℂ γ0 y' := by
    intro y'
    rw [differentiableAt_pi]
    intro p
    exact ((differentiable_apply p.2).comp (hMdiff.comp hcons)) y'
  have hγ0mem : ∀ y', γ0 y' ∈ mcPts (grassIdeal 1 1 n) := by
    intro y'
    have hv : (Fin.cons 1 y' : Fin (n + 1) → ℂ) ≠ 0 := fun h => one_ne_zero (congrFun h 0)
    obtain ⟨I, hI⟩ := Function.ne_iff.mp ((M.map_ne_zero_iff).mpr hv)
    exact (mem_mcPts _).2 fun _ => ⟨I, hI⟩
  have hpot : ∀ y', Real.log ((fsMulti (plBlocks 1 1 n)).h (γ0 y')) = hermChartPot (Bᴴ * B) y' := by
    intro y'
    set v : Fin (n + 1) → ℂ := Fin.cons 1 y'
    have h1 : (fsMulti (plBlocks 1 1 n)).h (γ0 y') = ‖WithLp.toLp 2 (B *ᵥ v)‖ := by
      rw [hmv]
      simp [fsMulti, HermLine.ofMetrics, fsMetric, hγ0, blockLift, v]
    have h2 : (star v ⬝ᵥ ((Bᴴ * B) *ᵥ v)).re = ∑ I, ‖(B *ᵥ v) I‖ ^ 2 := by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
      simp [dotProduct, Complex.re_sum, Complex.conj_mul']
      norm_cast
    rw [hermChartPot, h1, h2, EuclideanSpace.norm_eq]
  unfold ptsIntegralAt chartMass
  congr 1
  funext y
  have hfib : fibre (grassIdeal 1 1 n) Ψ y = {L (Fin.cons 1 y)} := by
    ext w
    simp only [fibre, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, -, -, hw⟩
      rw [← hw, hLΨ]
    · rintro rfl
      exact ⟨γ0 y, hγ0mem y, hseg _, hΨL _⟩
  have hsheet : IsSheet (grassIdeal 1 1 n) Ψ y (L (Fin.cons 1 y)) γ0 :=
    ⟨hseg _, Eventually.of_forall fun y' => ⟨hγ0d y', hγ0mem y', by rw [hseg, hΨL]⟩⟩
  rw [hfib, finsum_mem_singleton]
  unfold sheetDensity
  split_ifs with hγ
  · have hev : (fun y' => Real.log ((fsMulti (plBlocks 1 1 n)).h (hγ.choose y'))) =ᶠ[𝓝 y]
        hermChartPot (Bᴴ * B) := by
      filter_upwards [hγ.choose_spec.2] with y' hy'
      have hs : segre (ι := plBlocks 1 1 n) (hγ.choose y') = segre (ι := plBlocks 1 1 n) (γ0 y') := by
        rw [hseg, ← hy'.2.2, hLΨ]
      have he : hγ.choose y' = γ0 y' := by
        funext p
        rw [apply_eq_segre (hγ.choose y') p, apply_eq_segre (γ0 y') p, hs]
      rw [he, hpot]
    simp only [one_mul, maDensity, cxHessian_congr hev]
  · exact absurd ⟨γ0, hsheet⟩ hγ

end GrassmannianGeometricDegreeChart

open GrassmannianGeometricDegreeChart in

/- English proof (translation)
Introduce `n`. Establish `hex` using `exists_good n`. Take `⟨B, hB, hval⟩` from `ptsIntegralAt_eq hex.choose_spec`. Use `⟨B, hB, ?_⟩` and prove the remaining obligations. Unfold `geomDeg ptsIntegral`.

Rewrite using `[dif_pos hex]`. Conclude with `hval`.
-/
theorem GrassGeomDegChart.proof : GrassGeomDegChart.Statement := by
  intro n
  have hex := exists_good n
  obtain ⟨B, hB, hval⟩ := ptsIntegralAt_eq hex.choose_spec
  refine ⟨B, hB, ?_⟩
  unfold geomDeg ptsIntegral
  rw [dif_pos hex]
  exact hval

end

end GroundTheory.Heights₂.Heights
