import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TransPtBase
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph.GenIdeal

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def coneOver {A : Type} [CommRing A] (Y : (Σ k, ι k) → A) : MRing ι →ₐ[ℤ] MvPolynomial K A :=
  aeval fun p => C (Y p) * X p.1

def scaleBy {F : Type} [Field F] (c : K → F) : MvPolynomial K F →ₐ[F] MvPolynomial K F :=
  aeval fun k => C (c k) * X k

omit [Fintype K] in
/- English proof (translation)
Establish `h : (scaleBy fun k => (c k)⁻¹).comp (scaleBy c) = AlgHom.id F _`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `k`. Simplify using `only [scaleBy, AlgHom.comp_apply, aeval_X, map_mul, algHom_C, AlgHom.id_apply]`. Rewrite using `[← mul_assoc, algebraMap_eq, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]`.

Conclude with `Function.LeftInverse.injective (g := scaleBy fun k => (c k)⁻¹) fun f => DFunLike.congr_fun h f`.
-/
theorem scaleBy_injective {F : Type} [Field F] (c : K → F) (hc : ∀ k, c k ≠ 0) :
    Function.Injective (scaleBy c) := by
  have h : (scaleBy fun k => (c k)⁻¹).comp (scaleBy c) = AlgHom.id F _ := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [scaleBy, AlgHom.comp_apply, aeval_X, map_mul, algHom_C, AlgHom.id_apply]
    rw [← mul_assoc, algebraMap_eq, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]
  exact Function.LeftInverse.injective (g := scaleBy fun k => (c k)⁻¹) fun f => DFunLike.congr_fun h f

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simp [mConeMap, coneOver]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p q hp`. Rewrite using `[map_mul, map_mul, map_mul, map_mul, hp]`.

Use `congr 1`. Simplify using `only [mConeMap, coneOver, aeval_X, scaleBy, map_mul, map_C, map_X, algHom_C, algebraMap_eq, hz q]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mConeMap_eq {A F : Type} [CommRing A] [Field F] (f : A →+* F) (Y : (Σ k, ι k) → A) (z : (Σ k, ι k) → F)
    (c : K → F) (hz : ∀ q, z q = c q.1 * f (Y q)) (p : MRing ι) :
    mConeMap z p = scaleBy c (MvPolynomial.map f (coneOver Y p)) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [mConeMap, coneOver]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p q hp =>
    rw [map_mul, map_mul, map_mul, map_mul, hp]
    congr 1
    simp only [mConeMap, coneOver, aeval_X, scaleBy, map_mul, map_C, map_X, algHom_C, algebraMap_eq, hz q]
    ring

/- English proof (translation)
Use extensionality with `p`. Rewrite using `[mCoordIdeal, RingHom.mem_ker, RingHom.mem_ker, mConeMap_eq f Y z c hz]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1 : MvPolynomial.map f (coneOver Y p) = 0` using `scaleBy_injective c hc (by rw [h, map_zero])`.

Conclude with `MvPolynomial.map_injective f hf (by rw [h1, map_zero])`. Introduce `h`. Rewrite using `[h, map_zero, map_zero]`.
-/
theorem mCoordIdeal_eq {A F : Type} [CommRing A] [Field F] (f : A →+* F) (hf : Function.Injective f)
    (Y : (Σ k, ι k) → A) (z : (Σ k, ι k) → F) (c : K → F) (hc : ∀ k, c k ≠ 0)
    (hz : ∀ q, z q = c q.1 * f (Y q)) : mCoordIdeal z = RingHom.ker (coneOver Y) := by
  ext p
  rw [mCoordIdeal, RingHom.mem_ker, RingHom.mem_ker, mConeMap_eq f Y z c hz]
  constructor
  · intro h
    have h1 : MvPolynomial.map f (coneOver Y p) = 0 := scaleBy_injective c hc (by rw [h, map_zero])
    exact MvPolynomial.map_injective f hf (by rw [h1, map_zero])
  · intro h
    rw [h, map_zero, map_zero]

/- English proof (translation)
Unfold `minorIJ`. Use `split_ifs with e`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression. Conclude with `map_zero f`.
-/
theorem map_minorIJ {R S : Type} [CommRing R] [CommRing S] {N : ℕ} (f : R →+* S) (h : Matrix (Fin N) (Fin N) R)
    (I J : Finset (Fin N)) : f (minorIJ h I J) = minorIJ (h.map f) I J := by
  unfold minorIJ
  split_ifs with e
  · rw [RingHom.map_det]
    rfl
  · exact map_zero f

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ}

def polyPt (M : FlagModel y Ψ N j) : (Σ k, ι k) → MvPolynomial (LowIdx Ψ N j) M.Ω := fun q =>
  if h : ∀ p, M.blk p ≠ some q.1 then C (M.x ⟨⟨q.1, h⟩, q.2⟩)
  else ∑ I, C (M.coef q I) * minorIJ (genLow M.Ω N j (stepOf M q.1 h).1) I (stepCols N j (stepOf M q.1 h).2)

/- English proof (translation)
Establish `hmap : ∀ τ, (genLow M.Ω N j τ).map f = G τ * B τ` using `genLow_map f (H := fun τ => G τ * B τ) (fun τ => ⟨(hG τ).mul (hB τ).1, (hB τ).2.2⟩) hf`. Establish `hdiag : ∀ τ c, B τ c c ≠ 0` using `fun τ c h0 => by`. Establish `h1 : (G τ).det * (B τ).det = 1` using `by rw [← det_mul, (hB τ).2.2.det]`. Establish `h2 : ∏ i, B τ i i = 0` using `Finset.prod_eq_zero (Finset.mem_univ c) h0`. Rewrite `h1` using `[det_of_upperTriangular (hB τ).2.1, h2, mul_zero]`.

Conclude with `zero_ne_one h1`. Set `s : Ψ × Fin N → F` to `fun p => ∏ c ∈ stepCols N j p.2, B p.1 c c`. Establish `hs : ∀ p, s p ≠ 0` using `fun p => Finset.prod_ne_zero_iff.2 fun c _ => hdiag p.1 c`. Establish `gen : ∀ a b t : F, t ≠ 0 → a * b = t⁻¹ * (a * (b * t))` using `fun a b t ht => by field_simp`. Use `⟨fun k => if h : ∀ p, M.blk p ≠ some k then 1 else (s (stepOf M k h))⁻¹, fun k => ?_, ?_⟩` and prove the remaining obligations.

Simplify using `only split_ifs with h`. Conclude with `one_ne_zero`. Conclude with `inv_ne_zero (hs _)`. Introduce and unpack `⟨k, m⟩`. Distinguish the cases in `h : ∀ p, M.blk p ≠ some k`.

Establish `e` using `hbase ⟨⟨k, h⟩, m⟩`. Simplify using `only [polyPt, dif_pos h, one_mul, hfC]`. Conclude with `e`. Simplify using `only [polyPt, dif_neg h, map_sum, map_mul, hfC, map_minorIJ, hmap]`. Rewrite using `[hstep _ k (blk_stepOf M k h) m, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun I _ => ?_` and prove the remaining obligations. Rewrite using `[(GlobalTheory.T.block_diagonal_minor_vanishing F N j (stepOf M k h).2 M.j_le).2.2.1 _ _ I (hB _).1 (hB _).2.1]`. Conclude with `gen _ _ _ (hs _)`.
-/
theorem exists_scale (M : FlagModel y Ψ N j) {F : Type} [Field F] (f : MvPolynomial (LowIdx Ψ N j) M.Ω →+* F)
    (ψ : M.Ω →+* F) (hfC : ∀ a, f (C a) = ψ a) (G B : Ψ → Matrix (Fin N) (Fin N) F)
    (hG : ∀ τ, IsBlockDiag j (G τ))
    (hB : ∀ τ, IsBlockDiag j (B τ) ∧ (B τ).BlockTriangular id ∧ IsLowerUni (G τ * B τ))
    (hf : ∀ q : LowIdx Ψ N j, f (X q) = (G q.1.1 * B q.1.1) q.1.2.1 q.1.2.2)
    (z : (Σ k, ι k) → F)
    (hbase : ∀ q : Σ k, baseIdx ι M.blk k, z ⟨q.1.1, q.2⟩ = ψ (M.x q))
    (hstep : ∀ p k, M.blk p = some k → ∀ m : ι k,
      z ⟨k, m⟩ = ∑ I, ψ (M.coef ⟨k, m⟩ I) * minorIJ (G p.1) I (stepCols N j p.2)) :
    ∃ c : K → F, (∀ k, c k ≠ 0) ∧ ∀ q, z q = c q.1 * f (polyPt M q) := by
  have hmap : ∀ τ, (genLow M.Ω N j τ).map f = G τ * B τ :=
    genLow_map f (H := fun τ => G τ * B τ) (fun τ => ⟨(hG τ).mul (hB τ).1, (hB τ).2.2⟩) hf
  have hdiag : ∀ τ c, B τ c c ≠ 0 := fun τ c h0 => by
    have h1 : (G τ).det * (B τ).det = 1 := by rw [← det_mul, (hB τ).2.2.det]
    have h2 : ∏ i, B τ i i = 0 := Finset.prod_eq_zero (Finset.mem_univ c) h0
    rw [det_of_upperTriangular (hB τ).2.1, h2, mul_zero] at h1
    exact zero_ne_one h1
  let s : Ψ × Fin N → F := fun p => ∏ c ∈ stepCols N j p.2, B p.1 c c
  have hs : ∀ p, s p ≠ 0 := fun p => Finset.prod_ne_zero_iff.2 fun c _ => hdiag p.1 c
  have gen : ∀ a b t : F, t ≠ 0 → a * b = t⁻¹ * (a * (b * t)) := fun a b t ht => by field_simp
  refine ⟨fun k => if h : ∀ p, M.blk p ≠ some k then 1 else (s (stepOf M k h))⁻¹, fun k => ?_, ?_⟩
  · dsimp only
    split_ifs with h
    · exact one_ne_zero
    · exact inv_ne_zero (hs _)
  · rintro ⟨k, m⟩
    by_cases h : ∀ p, M.blk p ≠ some k
    · have e := hbase ⟨⟨k, h⟩, m⟩
      simp only [polyPt, dif_pos h, one_mul, hfC]
      exact e
    · simp only [polyPt, dif_neg h, map_sum, map_mul, hfC, map_minorIJ, hmap]
      rw [hstep _ k (blk_stepOf M k h) m, Finset.mul_sum]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [(GlobalTheory.T.block_diagonal_minor_vanishing F N j (stepOf M k h).2 M.j_le).2.2.1 _ _ I (hB _).1 (hB _).2.1]
      exact gen _ _ _ (hs _)

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph.GenIdeal

open GlobalTheory.CompanionTheory.Ar.PB.CovGraph.GenIdeal in

/- English proof (translation)
Introduce `K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv`. Take `⟨B, hB, hind⟩` from `M.g_indep`. Take `⟨B', hB', hind'⟩` from `M'.g_indep`. Set `ev : MvPolynomial (LowIdx Ψ N j) M.Ω →ₐ[M.Ω] Φ` to `aeval fun q => (M.g q.1.1 * B q.1.1) q.1.2.1 q.1.2.2`. Set `ev₀ : MvPolynomial (LowIdx Ψ N j) M'.Ω →ₐ[M'.Ω] Φ'` to `aeval fun q => (M'.g q.1.1 * B' q.1.1) q.1.2.1 q.1.2.2`.

Set `ev' : MvPolynomial (LowIdx Ψ N j) M.Ω →+* Φ'` to `ev₀.toRingHom.comp (MvPolynomial.map Cv.φ)`. Establish `hev' : Function.Injective ev'` using `(show Function.Injective ev₀ from hind').comp (MvPolynomial.map_injective Cv.φ Cv.φ.injective)`. Take `⟨c, hc, hz⟩` from `exists_scale M ev.toRingHom (algebraMap M.Ω Φ) (fun a => aeval_C _ a) M.g B M.g_block hB (fun q => aeval_X _ q) y M.y_base M.y_step`. Take `⟨c', hc', hz'⟩` from `exists_scale M ev' ((algebraMap M'.Ω Φ').comp Cv.φ) (fun a => by simp [ev', ev₀]) M'.g B' M'.g_block hB' (fun q => by simp [ev', ev₀]) (transPt Cv) (transPt_base Cv) (fun p k hp m => transPt_step Cv p k hp m)`. Rewrite using `[mCoordIdeal_eq ev' hev' _ _ c' hc' hz', mCoordIdeal_eq ev.toRingHom hind _ _ c hc hz]`.
-/
theorem GlobalTheory.CompanionTheory.Ar.PB.CovGraph.mCoordIdeal_transPt : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M), mCoordIdeal (transPt Cv) = mCoordIdeal y := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv
  obtain ⟨B, hB, hind⟩ := M.g_indep
  obtain ⟨B', hB', hind'⟩ := M'.g_indep
  let ev : MvPolynomial (LowIdx Ψ N j) M.Ω →ₐ[M.Ω] Φ := aeval fun q => (M.g q.1.1 * B q.1.1) q.1.2.1 q.1.2.2
  let ev₀ : MvPolynomial (LowIdx Ψ N j) M'.Ω →ₐ[M'.Ω] Φ' := aeval fun q => (M'.g q.1.1 * B' q.1.1) q.1.2.1 q.1.2.2
  let ev' : MvPolynomial (LowIdx Ψ N j) M.Ω →+* Φ' := ev₀.toRingHom.comp (MvPolynomial.map Cv.φ)
  have hev' : Function.Injective ev' :=
    (show Function.Injective ev₀ from hind').comp (MvPolynomial.map_injective Cv.φ Cv.φ.injective)
  obtain ⟨c, hc, hz⟩ := exists_scale M ev.toRingHom (algebraMap M.Ω Φ) (fun a => aeval_C _ a) M.g B M.g_block hB
    (fun q => aeval_X _ q) y M.y_base M.y_step
  obtain ⟨c', hc', hz'⟩ := exists_scale M ev' ((algebraMap M'.Ω Φ').comp Cv.φ)
    (fun a => by simp [ev', ev₀]) M'.g B' M'.g_block hB' (fun q => by simp [ev', ev₀]) (transPt Cv)
    (transPt_base Cv) (fun p k hp m => transPt_step Cv p k hp m)
  rw [mCoordIdeal_eq ev' hev' _ _ c' hc' hz', mCoordIdeal_eq ev.toRingHom hind _ _ c hc hz]
