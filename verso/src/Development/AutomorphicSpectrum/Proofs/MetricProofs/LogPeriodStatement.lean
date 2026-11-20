import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentSwapVarietiesArithmeticStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishingStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorSumIdentityBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProportionalMinorsBlockTriangularStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryFactorizationOfNearTriangularStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.NearTriangularOfStepConditionsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryFactorCommutationStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericFlagElementaryTwistStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Pts
open GlobalTheory.CompanionTheory.Ar.PB.CPts GlobalTheory.CompanionTheory.Ar.PB.ValRing

section Sides

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Use `⟨Option.some_injective _, ?_, fun _ => rfl, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨k, i⟩ ⟨k', i'⟩ h`. Simplify using `only [v₀, Sigma.mk.injEq, Option.some.injEq] at h`. Take `⟨rfl, h⟩` from `h`. Simplify using `only [Option.getD_some, heq_eq_eq] at h`.

Substitute `h` using the available equality. Both sides reduce to the same expression. Introduce and unpack `⟨o, i⟩ ⟨k, hk⟩`. Take `rfl : o = some k` from `hk.symm`. Conclude with `⟨⟨k, i⟩, rfl⟩`.
-/
theorem isBlockMap_v₀ (k₀ : K) : IsBlockMap (ι := ι) (ι' := fun o : Option K => ι (o.getD k₀)) some (v₀ k₀) := by
  refine ⟨Option.some_injective _, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, i⟩ ⟨k', i'⟩ h
    simp only [v₀, Sigma.mk.injEq, Option.some.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [Option.getD_some, heq_eq_eq] at h
    subst h
    rfl
  · rintro ⟨o, i⟩ ⟨k, hk⟩
    obtain rfl : o = some k := hk.symm
    exact ⟨⟨k, i⟩, rfl⟩

/- English proof (translation)
Use `⟨fun k => ?_, fun f hf => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hk : k = k₀`. Substitute `hk` using the available equality. Take `⟨i, hi⟩` from `hz.1 none`. Conclude with `⟨i, by simpa [sndPt, Function.comp, v₁_self] using hi⟩`.

Take `⟨i, hi⟩` from `hz.1 (some k)`. Conclude with `⟨i, by simpa [sndPt, Function.comp, v₁_ne (p := ⟨k, i⟩) hk] using hi⟩`. Rewrite `hf` using `[← hI]`. Establish `h0` using `hz.2 _ hf`. Establish `h1 : eval z (map (Int.castRingHom ℂ) (rename (v₁ k₀) f)) = 0` using `h0`.

Rewrite `h1` using `[eval_rename_block]`. Conclude with `h1`.
-/
theorem snd_mem {k₀ : K} {P' : Ideal (MRing (fun o : Option K => ι (o.getD k₀)))} {P : Ideal (MRing ι)}
    (hI : imageZ (v₁ k₀) P' = P) {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (hz : z ∈ mcPts P') : sndPt k₀ z ∈ mcPts P := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · by_cases hk : k = k₀
    · subst hk
      obtain ⟨i, hi⟩ := hz.1 none
      exact ⟨i, by simpa [sndPt, Function.comp, v₁_self] using hi⟩
    · obtain ⟨i, hi⟩ := hz.1 (some k)
      exact ⟨i, by simpa [sndPt, Function.comp, v₁_ne (p := ⟨k, i⟩) hk] using hi⟩
  · rw [← hI] at hf
    have h0 := hz.2 _ hf
    have h1 : eval z (map (Int.castRingHom ℂ) (rename (v₁ k₀) f)) = 0 := h0
    rw [eval_rename_block] at h1
    exact h1

/- English proof (translation)
Use `show z (v₁ k₀ ⟨k, m⟩) = z (v₀ k₀ ⟨k, m⟩)`. Rewrite using `[v₁_ne (p := ⟨k, m⟩) hk]`. Both sides reduce to the same expression.
-/
theorem snd_fst_ne {k₀ k : K} (hk : k ≠ k₀) (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) (m : ι k) :
    sndPt k₀ z ⟨k, m⟩ = fstPt k₀ z ⟨k, m⟩ := by
  show z (v₁ k₀ ⟨k, m⟩) = z (v₀ k₀ ⟨k, m⟩)
  rw [v₁_ne (p := ⟨k, m⟩) hk]
  rfl

/- English proof (translation)
Use `show z (v₁ k₀ ⟨k₀, m⟩) = _`. Rewrite using `[v₁_self]`.
-/
theorem snd_self {k₀ : K} (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) (m : ι k₀) :
    sndPt k₀ z ⟨k₀, m⟩ = z ⟨none, m⟩ := by
  show z (v₁ k₀ ⟨k₀, m⟩) = _
  rw [v₁_self]

end Sides

section Mat

variable {N j : ℕ}

/- English proof (translation)
Use `a.2` as an intermediate fact. Use `b.2` as an intermediate fact. Use `cb.2` as an intermediate fact. Unfold `lastCol at hca`. Apply the tactic sequence `split_ifs at hca <;> omega`.
-/
theorem same_summand {a b ca cb : Fin N} (hb : (b : ℕ) = a + 1) (hab : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) : ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) := by
  have := a.2
  have := b.2
  have := cb.2
  unfold lastCol at hca
  split_ifs at hca <;> omega

/- English proof (translation)
Introduce `r c h` and use `by rw [Matrix.add_apply, isBlockDiag_one r c h, zero_add, Matrix.single_apply_of_ne] rintro ⟨rfl, rfl⟩ exact h hS.symm`.
-/
theorem transv_block {R : Type} [CommRing R] {ca cb : Fin N} (hS : ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j)) (t : R) :
    IsBlockDiag j (1 + Matrix.single cb ca t) := fun r c h => by
  rw [Matrix.add_apply, isBlockDiag_one r c h, zero_add, Matrix.single_apply_of_ne]
  rintro ⟨rfl, rfl⟩
  exact h hS.symm

/- English proof (translation)
Establish `hne : ca ≠ cb` using `fun e => by rw [e] at hc; omega`. Establish `hlt : ca < cb` using `by rw [Fin.lt_def]; omega`. Rewrite using `[Matrix.det_of_lowerTriangular _ fun r c h => ?_]`. Use `Finset.prod_eq_one fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply_of_ne, add_zero]`.

Introduce and unpack `⟨rfl, e⟩`. Conclude with `hne e`. Establish `h' : r < c` using `h`. Rewrite using `[Matrix.add_apply, Matrix.one_apply_ne h'.ne, Matrix.single_apply_of_ne, add_zero]`. Introduce and unpack `⟨rfl, rfl⟩`.

Conclude with `lt_asymm h' hlt`.
-/
theorem transv_det {R : Type} [CommRing R] {ca cb : Fin N} (hc : (cb : ℕ) = ca + 1) (t : R) :
    (1 + Matrix.single cb ca t).det = 1 := by
  have hne : ca ≠ cb := fun e => by rw [e] at hc; omega
  have hlt : ca < cb := by rw [Fin.lt_def]; omega
  rw [Matrix.det_of_lowerTriangular _ fun r c h => ?_]
  · refine Finset.prod_eq_one fun c _ => ?_
    rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply_of_ne, add_zero]
    rintro ⟨rfl, e⟩
    exact hne e
  · have h' : r < c := h
    rw [Matrix.add_apply, Matrix.one_apply_ne h'.ne, Matrix.single_apply_of_ne, add_zero]
    rintro ⟨rfl, rfl⟩
    exact lt_asymm h' hlt

/- English proof (translation)
Use extensionality with `r c`. Rewrite using `[Matrix.map_apply, Matrix.add_apply, Matrix.add_apply, map_add, Matrix.one_apply, Matrix.one_apply, apply_ite f, map_one, map_zero, Matrix.single_apply, Matrix.single_apply, apply_ite f, map_zero]`.
-/
theorem transv_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (ca cb : Fin N) (t : R) :
    (1 + Matrix.single cb ca t).map f = 1 + Matrix.single cb ca (f t) := by
  ext r c
  rw [Matrix.map_apply, Matrix.add_apply, Matrix.add_apply, map_add, Matrix.one_apply, Matrix.one_apply, apply_ite f,
    map_one, map_zero, Matrix.single_apply, Matrix.single_apply, apply_ite f, map_zero]

/- English proof (translation)
Establish `hP : (∏ c ∈ stepCols N j i, U c c) ≠ 0` using `Finset.prod_ne_zero_iff.2 hd`. Establish `e : ∀ m, ∑ I, v m I * minorIJ (A * U) I (stepCols N j i) = (∏ c ∈ stepCols N j i, U c c) * ∑ I, v m I * minorIJ A I (stepCols N j i)` using `fun m => by`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun I _ => ?_` and prove the remaining obligations. Rewrite using `[(GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j i hj).2.2.1 A U I hU hUt]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [e]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨α, hα, h⟩`. Conclude with `⟨α * ∏ c ∈ stepCols N j i, U c c, mul_ne_zero hα hP, fun m => by rw [h m, mul_assoc]⟩`.

Introduce and unpack `⟨α, hα, h⟩`. Conclude with `⟨α / ∏ c ∈ stepCols N j i, U c c, div_ne_zero hα hP, fun m => by rw [h m]; field_simp⟩`.
-/
theorem step_mul_right (hj : j ≤ N) (i : Fin N) {A U : Matrix (Fin N) (Fin N) ℂ} (hU : IsBlockDiag j U)
    (hUt : U.BlockTriangular id) (hd : ∀ c, c ∈ stepCols N j i → U c c ≠ 0) {κ : Type} (w : κ → ℂ)
    (v : κ → Finset (Fin N) → ℂ) :
    (∃ α : ℂ, α ≠ 0 ∧ ∀ m, w m = α * ∑ I, v m I * minorIJ (A * U) I (stepCols N j i)) ↔
      ∃ α : ℂ, α ≠ 0 ∧ ∀ m, w m = α * ∑ I, v m I * minorIJ A I (stepCols N j i) := by
  have hP : (∏ c ∈ stepCols N j i, U c c) ≠ 0 := Finset.prod_ne_zero_iff.2 hd
  have e : ∀ m, ∑ I, v m I * minorIJ (A * U) I (stepCols N j i) =
      (∏ c ∈ stepCols N j i, U c c) * ∑ I, v m I * minorIJ A I (stepCols N j i) := fun m => by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [(GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j i hj).2.2.1 A U I hU hUt]
    ring
  simp only [e]
  constructor
  · rintro ⟨α, hα, h⟩
    exact ⟨α * ∏ c ∈ stepCols N j i, U c c, mul_ne_zero hα hP, fun m => by rw [h m, mul_assoc]⟩
  · rintro ⟨α, hα, h⟩
    exact ⟨α / ∏ c ∈ stepCols N j i, U c c, div_ne_zero hα hP, fun m => by rw [h m]; field_simp⟩

end Mat

section Flags

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} (M : FlagModel y Ψ N j)

/- English proof (translation)
Use function extensionality and compare the values at `q`. Take `⟨⟨k, hb⟩, i⟩` from `q`. Conclude with `snd_fst_ne (fun e => hb (τ, a) (hk.trans (congrArg some e.symm))) z i`.
-/
theorem basePart_snd {k₀ : K} {τ : Ψ} {a : Fin N} (hk : M.blk (τ, a) = some k₀)
    (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) : basePart M.blk (sndPt k₀ z) = basePart M.blk (fstPt k₀ z) := by
  funext q
  obtain ⟨⟨k, hb⟩, i⟩ := q
  exact snd_fst_ne (fun e => hb (τ, a) (hk.trans (congrArg some e.symm))) z i

/- English proof (translation)
Set `val` to `regVal hzb`. Set `uA : (Σ k, ι k) → Finset (Fin N) → regRing M.x zb` to `fun q I => ⟨F.u q I, exists_isValueAt hzb (hG.2.1 q I).1⟩`. Set `vA : Finset (Fin N) → (Σ k, ι k) → regRing M.x zb` to `fun I q => ⟨F.u' I q, exists_isValueAt hzb (hG.2.1 q I).2⟩`. Establish `rel : ∀ I', IsStepRows N j p.2 I' → ∑ m : ι k, val (vA I₀ ⟨k, m⟩) * val (uA ⟨k, m⟩ I') = if I₀ = I' then 1 else 0` using `fun I' hI' => by`. Establish `e : ∑ m : ι k, vA I₀ ⟨k, m⟩ * uA ⟨k, m⟩ I' = if I₀ = I' then 1 else 0`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `hF.2.2.1 p k hp I₀ I' hI₀ hI'` as an intermediate fact. Apply the tactic sequence `split_ifs at this ⊢ <;> simpa [uA, vA] using this`. Establish `e'` using `congrArg val e`. Rewrite `e'` using `[map_sum]`.

Simplify using `only [map_mul] at e'`. Rewrite using `[e']`. Apply the tactic sequence `split_ifs <;> simp`. Establish `read : ∀ A : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j A → ∑ m : ι k, val (vA I₀ ⟨k, m⟩) * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ A I (stepCols N j p.2) = minorIJ A I₀ (stepCols N j p.2)` using `fun A hA => by`. Establish `off : ∀ I, ¬ IsStepRows N j p.2 I → minorIJ A I (stepCols N j p.2) = 0` using `fun I hI => ((GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le).2.1 A I hA hI).resolve_right (Finset.nonempty_iff_ne_empty.1 (stepCols_nonempty M.j_le p.2))`.

Establish `key : ∀ I, (∑ m : ι k, val (vA I₀ ⟨k, m⟩) * val (uA ⟨k, m⟩ I)) * minorIJ A I (stepCols N j p.2) = if I = I₀ then minorIJ A I₀ (stepCols N j p.2) else 0` using `fun I => by`. Distinguish the cases in `hI : IsStepRows N j p.2 I`. Rewrite using `[rel I hI]`. Distinguish the cases in `e : I = I₀`. Substitute `e` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[e, Ne.symm e]`. Establish `e : I ≠ I₀` using `fun e => hI (e ▸ hI₀)`. Rewrite using `[off I hI, if_neg e, mul_zero]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Both sides reduce to the same expression.

Use `_ = _ := by simp only [key]; simp`. Rewrite using `[← read A hA, ← read B hB, Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[mul_left_comm, h m, mul_left_comm]`.
-/
theorem step_pl {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) {zb : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hzb : zb ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal zb)) {p : Ψ × Fin N} {k : K}
    (hp : M.blk p = some k) {A B : Matrix (Fin N) (Fin N) ℂ} (hA : IsBlockDiag j A) (hB : IsBlockDiag j B) {α β : ℂ}
    (h : ∀ m : ι k, α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ A I (stepCols N j p.2) =
      β * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ B I (stepCols N j p.2))
    (I₀ : Finset (Fin N)) (hI₀ : IsStepRows N j p.2 I₀) :
    α * minorIJ A I₀ (stepCols N j p.2) = β * minorIJ B I₀ (stepCols N j p.2) := by
  let val := regVal hzb
  let uA : (Σ k, ι k) → Finset (Fin N) → regRing M.x zb :=
    fun q I => ⟨F.u q I, exists_isValueAt hzb (hG.2.1 q I).1⟩
  let vA : Finset (Fin N) → (Σ k, ι k) → regRing M.x zb :=
    fun I q => ⟨F.u' I q, exists_isValueAt hzb (hG.2.1 q I).2⟩
  have rel : ∀ I', IsStepRows N j p.2 I' →
      ∑ m : ι k, val (vA I₀ ⟨k, m⟩) * val (uA ⟨k, m⟩ I') = if I₀ = I' then 1 else 0 := fun I' hI' => by
    have e : ∑ m : ι k, vA I₀ ⟨k, m⟩ * uA ⟨k, m⟩ I' = if I₀ = I' then 1 else 0 := by
      apply Subtype.ext
      have := hF.2.2.1 p k hp I₀ I' hI₀ hI'
      split_ifs at this ⊢ <;> simpa [uA, vA] using this
    have e' := congrArg val e
    rw [map_sum] at e'
    simp only [map_mul] at e'
    rw [e']
    split_ifs <;> simp
  have read : ∀ A : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j A →
      ∑ m : ι k, val (vA I₀ ⟨k, m⟩) * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ A I (stepCols N j p.2) =
        minorIJ A I₀ (stepCols N j p.2) := fun A hA => by
    have off : ∀ I, ¬ IsStepRows N j p.2 I → minorIJ A I (stepCols N j p.2) = 0 := fun I hI =>
      ((GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le).2.1 A I hA hI).resolve_right
        (Finset.nonempty_iff_ne_empty.1 (stepCols_nonempty M.j_le p.2))
    have key : ∀ I, (∑ m : ι k, val (vA I₀ ⟨k, m⟩) * val (uA ⟨k, m⟩ I)) * minorIJ A I (stepCols N j p.2) =
        if I = I₀ then minorIJ A I₀ (stepCols N j p.2) else 0 := fun I => by
      by_cases hI : IsStepRows N j p.2 I
      · rw [rel I hI]
        by_cases e : I = I₀
        · subst e; simp
        · simp [e, Ne.symm e]
      · have e : I ≠ I₀ := fun e => hI (e ▸ hI₀)
        rw [off I hI, if_neg e, mul_zero]
    calc _ = ∑ I, (∑ m : ι k, val (vA I₀ ⟨k, m⟩) * val (uA ⟨k, m⟩ I)) * minorIJ A I (stepCols N j p.2) := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun m _ => ?_
          rw [mul_assoc]
          rfl
      _ = _ := by simp only [key]; simp
  rw [← read A hA, ← read B hB, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_left_comm, h m, mul_left_comm]

/- English proof (translation)
Establish `hS` using `same_summand hb hab hca hcb`. Establish `hsnd` using `basePart_snd M hk z`. Establish `hd : IsUnit (h τ).det` using `(H.2.1 τ).2.isUnit`. Set `C` to `(h τ)⁻¹ * h' τ`. Establish `hCb : IsBlockDiag j C` using `((H.2.1 τ).1.inv hd).mul (H'.2.1 τ).1`.

Establish `hCd : C.det ≠ 0`. Rewrite using `[Matrix.det_mul]`. Use `mul_ne_zero (fun h0 => ?_) (H'.2.1 τ).2` and prove the remaining obligations. Establish `h1` using `Matrix.det_nonsing_inv_mul_det (h τ) hd`. Rewrite `h1` using `[h0, zero_mul]`.

Conclude with `zero_ne_one h1`. Establish `vanish : ∀ i, IsProperStep N j i → i ≠ a → ∀ r c, c ∈ stepCols N j i → r ∉ stepCols N j i → C r c = 0`. Introduce `i hi hia`. Take `⟨k, hp⟩ : ∃ k, M.blk (τ, i) = some k` from `Option.ne_none_iff_exists'.1 fun e => (M.blk_none _).1 e hi`. Establish `hkk : k ≠ k₀` using `fun e => hia (Prod.ext_iff.1 (M.blk_inj _ _ k₀ (e ▸ hp) hk)).2`.

Take `⟨α, hα, hz⟩` from `H.2.2 (τ, i) k hp`. Take `⟨β, hβ, hz'⟩` from `H'.2.2 (τ, i) k hp`. Rewrite `hz'` using `[hsnd]`. Conclude with `GlobalTheory.T.proportional_minors_block_triangular N j i (h τ) (h' τ) α β M.j_le (H.2.1 τ).1 (H'.2.1 τ).1 (H.2.1 τ).2 hα hβ (step_pl M hF hzb hG hp (H.2.1 τ).1 (H'.2.1 τ).1 fun m => by rw [← hz m, ← hz' m, snd_fst_ne hkk])`. Take `⟨B, U, t, hB, hBt, hBd, hU, hUt, hUd, hC⟩` from `GlobalTheory.T.elementary_factorization_of_near_triangular N j ca cb C hcb hS hCb hCd (GlobalTheory.T.near_triangular_of_step_conditions N j a b ca cb C M.j_le hb hab hca hcb hCb vanish)`.

Establish `hBc : ∀ c, B c c ≠ 0` using `fun c => by`. Rewrite `hBd` using `[Matrix.det_of_upperTriangular hBt]`. Conclude with `Finset.prod_ne_zero_iff.1 hBd c (Finset.mem_univ c)`. Establish `hh' : h' τ = h τ * B * (1 + Matrix.single cb ca t) * U`. Establish `: h τ * C = h' τ` using `Matrix.mul_nonsing_inv_cancel_left _ _ hd`.

Rewrite using `[← this, hC]`. Simplify using `only [Matrix.mul_assoc]`. Establish `hE` using `transv_block (j := j) hS t`. Establish `hEd` using `transv_det hcb t`. Use `⟨Function.update h τ (h τ * B), t, ⟨H.1, fun τ' => ?_, fun p k hp => ?_⟩, ⟨H'.1, fun τ' => ?_, fun p k hp => ?_⟩⟩` and prove the remaining obligations.

Distinguish the cases in `e : τ' = τ`. Substitute `e` using the available equality. Rewrite using `[Function.update_self]`. Conclude with `⟨(H.2.1 τ').1.mul hB, by rw [Matrix.det_mul]; exact mul_ne_zero (H.2.1 τ').2 hBd⟩`. Rewrite using `[Function.update_of_ne e]`.

Conclude with `H.2.1 τ'`. Distinguish the cases in `e : p.1 = τ`. Rewrite using `[e, Function.update_self]`. Use `H.2.2 p k hp` as an intermediate fact. Rewrite `this` using `[e]`.

Conclude with `(step_mul_right M.j_le p.2 hB hBt (fun c _ => hBc c) _ _).2 this`. Rewrite using `[Function.update_of_ne e]`. Conclude with `H.2.2 p k hp`. Distinguish the cases in `e : τ' = τ`. Substitute `e` using the available equality.

Rewrite using `[Function.update_self, Function.update_self]`. Conclude with `⟨((H.2.1 τ').1.mul hB).mul hE, by`. Rewrite using `[Matrix.det_mul, Matrix.det_mul, hEd, mul_one]`. Conclude with `mul_ne_zero (H.2.1 τ').2 hBd⟩`. Rewrite using `[Function.update_of_ne e, Function.update_of_ne e]`.

Conclude with `H.2.1 τ'`. Distinguish the cases in `e : p.1 = τ`. Rewrite using `[e, Function.update_self, Function.update_self]`. Use `H'.2.2 p k hp` as an intermediate fact. Rewrite `this` using `[e, hh']`.

Conclude with `(step_mul_right M.j_le p.2 hU hUt (fun c _ => hUd c) _ _).1 this`. Rewrite using `[Function.update_of_ne e, Function.update_of_ne e]`. Establish `hkk : k ≠ k₀` using `fun e' => e (Prod.ext_iff.1 (M.blk_inj _ _ k₀ (e' ▸ hp) hk)).1`. Take `⟨α, hα, hz⟩` from `H.2.2 p k hp`. Conclude with `⟨α, hα, fun m => by rw [snd_fst_ne hkk, hsnd]; exact hz m⟩`.
-/
theorem fwd_flags {τ : Ψ} {a b ca cb : Fin N} {k₀ : K} (hb : (b : ℕ) = a + 1) (hab : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hk : M.blk (τ, a) = some k₀) (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1)
    {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ}
    (hzb : basePart M.blk (fstPt k₀ z) ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal (basePart M.blk (fstPt k₀ z))))
    {h h' : Ψ → Matrix (Fin N) (Fin N) ℂ} (H : M.IsFlagOf F (fstPt k₀ z) h) (H' : M.IsFlagOf F (sndPt k₀ z) h') :
    ∃ (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (t : ℂ), M.IsFlagOf F (fstPt k₀ z) h ∧
      M.IsFlagOf F (sndPt k₀ z) (Function.update h τ (h τ * (1 + Matrix.single cb ca t))) := by
  have hS := same_summand hb hab hca hcb
  have hsnd := basePart_snd M hk z
  have hd : IsUnit (h τ).det := (H.2.1 τ).2.isUnit
  let C := (h τ)⁻¹ * h' τ
  have hCb : IsBlockDiag j C := ((H.2.1 τ).1.inv hd).mul (H'.2.1 τ).1
  have hCd : C.det ≠ 0 := by
    rw [Matrix.det_mul]
    refine mul_ne_zero (fun h0 => ?_) (H'.2.1 τ).2
    have h1 := Matrix.det_nonsing_inv_mul_det (h τ) hd
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have vanish : ∀ i, IsProperStep N j i → i ≠ a → ∀ r c, c ∈ stepCols N j i → r ∉ stepCols N j i → C r c = 0 := by
    intro i hi hia
    obtain ⟨k, hp⟩ : ∃ k, M.blk (τ, i) = some k := Option.ne_none_iff_exists'.1 fun e => (M.blk_none _).1 e hi
    have hkk : k ≠ k₀ := fun e => hia (Prod.ext_iff.1 (M.blk_inj _ _ k₀ (e ▸ hp) hk)).2
    obtain ⟨α, hα, hz⟩ := H.2.2 (τ, i) k hp
    obtain ⟨β, hβ, hz'⟩ := H'.2.2 (τ, i) k hp
    rw [hsnd] at hz'
    exact GlobalTheory.T.proportional_minors_block_triangular N j i (h τ) (h' τ) α β M.j_le (H.2.1 τ).1 (H'.2.1 τ).1 (H.2.1 τ).2 hα hβ
      (step_pl M hF hzb hG hp (H.2.1 τ).1 (H'.2.1 τ).1 fun m => by rw [← hz m, ← hz' m, snd_fst_ne hkk])
  obtain ⟨B, U, t, hB, hBt, hBd, hU, hUt, hUd, hC⟩ := GlobalTheory.T.elementary_factorization_of_near_triangular N j ca cb C hcb hS hCb hCd
    (GlobalTheory.T.near_triangular_of_step_conditions N j a b ca cb C M.j_le hb hab hca hcb hCb vanish)
  have hBc : ∀ c, B c c ≠ 0 := fun c => by
    rw [Matrix.det_of_upperTriangular hBt] at hBd
    exact Finset.prod_ne_zero_iff.1 hBd c (Finset.mem_univ c)
  have hh' : h' τ = h τ * B * (1 + Matrix.single cb ca t) * U := by
    have : h τ * C = h' τ := Matrix.mul_nonsing_inv_cancel_left _ _ hd
    rw [← this, hC]
    simp only [Matrix.mul_assoc]
  have hE := transv_block (j := j) hS t
  have hEd := transv_det hcb t
  refine ⟨Function.update h τ (h τ * B), t, ⟨H.1, fun τ' => ?_, fun p k hp => ?_⟩, ⟨H'.1, fun τ' => ?_, fun p k hp => ?_⟩⟩
  · by_cases e : τ' = τ
    · subst e
      rw [Function.update_self]
      exact ⟨(H.2.1 τ').1.mul hB, by rw [Matrix.det_mul]; exact mul_ne_zero (H.2.1 τ').2 hBd⟩
    · rw [Function.update_of_ne e]
      exact H.2.1 τ'
  · by_cases e : p.1 = τ
    · rw [e, Function.update_self]
      have := H.2.2 p k hp
      rw [e] at this
      exact (step_mul_right M.j_le p.2 hB hBt (fun c _ => hBc c) _ _).2 this
    · rw [Function.update_of_ne e]
      exact H.2.2 p k hp
  · by_cases e : τ' = τ
    · subst e
      rw [Function.update_self, Function.update_self]
      exact ⟨((H.2.1 τ').1.mul hB).mul hE, by
        rw [Matrix.det_mul, Matrix.det_mul, hEd, mul_one]; exact mul_ne_zero (H.2.1 τ').2 hBd⟩
    · rw [Function.update_of_ne e, Function.update_of_ne e]
      exact H.2.1 τ'
  · by_cases e : p.1 = τ
    · rw [e, Function.update_self, Function.update_self]
      have := H'.2.2 p k hp
      rw [e, hh'] at this
      exact (step_mul_right M.j_le p.2 hU hUt (fun c _ => hUd c) _ _).1 this
    · rw [Function.update_of_ne e, Function.update_of_ne e]
      have hkk : k ≠ k₀ := fun e' => e (Prod.ext_iff.1 (M.blk_inj _ _ k₀ (e' ▸ hp) hk)).1
      obtain ⟨α, hα, hz⟩ := H.2.2 p k hp
      exact ⟨α, hα, fun m => by rw [snd_fst_ne hkk, hsnd]; exact hz m⟩

/- English proof (translation)
Use `haveI : Infinite M.Ω := Infinite.of_injective (Nat.cast : ℕ → M.Ω) Nat.cast_injective`. Use `letI : Algebra M.Ω S := f.toAlgebra`. Establish `h1` using `GlobalTheory.T.minor_sum_identity_base_change M.Ω N j (F.T p.1) _ _ (M.coef ⟨k, m⟩) (F.u ⟨k, m⟩) (stepCols N j p.2) (hF.2.1 p k hp m) S G hG`. Establish `e' : (F.T p.1).map (algebraMap M.Ω S) * G = gg * bb` using `e`. Rewrite `h1` using `[e']`.

Establish `h2 : ∀ I, minorIJ (gg * bb) I (stepCols N j p.2) = minorIJ gg I (stepCols N j p.2) * ∏ c ∈ stepCols N j p.2, bb c c` using `fun I => (GlobalTheory.T.block_diagonal_minor_vanishing S N j p.2 M.j_le).2.2.1 gg bb I hbb hbt`. Simplify using `only [h2] at h1`. Use `Eq.trans ?_ h1` and prove the remaining obligations. Rewrite using `[mul_assoc, Finset.mul_sum (a := ∏ c ∈ stepCols N j p.2, bb c c)]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun I _ => ?_` and prove the remaining obligations. Use `show _ = f _ * _`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem frame_any {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) {S : Type} [CommRing S] (f : M.Ω →+* S)
    {p : Ψ × Fin N} {k : K} (hp : M.blk p = some k) (m : ι k) {G bb gg : Matrix (Fin N) (Fin N) S}
    (hG : IsBlockDiag j G) (hbb : IsBlockDiag j bb) (hbt : bb.BlockTriangular id)
    (e : (F.T p.1).map f * G = gg * bb) :
    f (detFac j p.2 (F.T p.1)) * (∏ c ∈ stepCols N j p.2, bb c c) *
        ∑ I, f (M.coef ⟨k, m⟩ I) * minorIJ gg I (stepCols N j p.2) =
      f (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') * ∑ I, f (F.u ⟨k, m⟩ I) * minorIJ G I (stepCols N j p.2) := by
  haveI : Infinite M.Ω := Infinite.of_injective (Nat.cast : ℕ → M.Ω) Nat.cast_injective
  letI : Algebra M.Ω S := f.toAlgebra
  have h1 := GlobalTheory.T.minor_sum_identity_base_change M.Ω N j (F.T p.1) _ _ (M.coef ⟨k, m⟩) (F.u ⟨k, m⟩) (stepCols N j p.2)
    (hF.2.1 p k hp m) S G hG
  have e' : (F.T p.1).map (algebraMap M.Ω S) * G = gg * bb := e
  rw [e'] at h1
  have h2 : ∀ I, minorIJ (gg * bb) I (stepCols N j p.2) =
      minorIJ gg I (stepCols N j p.2) * ∏ c ∈ stepCols N j p.2, bb c c := fun I =>
    (GlobalTheory.T.block_diagonal_minor_vanishing S N j p.2 M.j_le).2.2.1 gg bb I hbb hbt
  simp only [h2] at h1
  refine Eq.trans ?_ h1
  rw [mul_assoc, Finset.mul_sum (a := ∏ c ∈ stepCols N j p.2, bb c c)]
  congr 1
  refine Finset.sum_congr rfl fun I _ => ?_
  show _ = f _ * _
  ring

/- English proof (translation)
Establish `hS` using `same_summand hb hab hca hcb`. Establish `hsnd` using `basePart_snd M hk z`. Establish `hnz : ∀ o : Option K, ∃ i, z ⟨o, i⟩ ≠ 0`. Introduce `o`. Consider the cases of `o with`.

Consider the case `some k => exact flag_nonzero M hF hzb hG H k`. Consider the case `none`. Take `⟨i, hi⟩` from `flag_nonzero M hF (hsnd ▸ hzb) (hsnd ▸ hG) H' k₀`. Conclude with `⟨i, by rwa [snd_self] at hi⟩`. Set `zb` to `basePart M.blk (fstPt k₀ z)`.

Set `A` to `regRing M.x zb`. Set `val : A →+* ℂ` to `regVal hzb`. Take `⟨L, R, _, _, φ, θ, U, s, i, ρ, cA, B, sR, hi, hθ, hU, hU0, hθX, hic, hρc, hBb, hBi, hBρ, his, hρs⟩` from `GlobalTheory.T.generic_flag_elementary_twist M.Ω Φ Ψ N j M.g F.T A val h t τ ca cb hcb hS M.g_block M.g_indep hF.1 fun τ => (H.2.1 τ).1`. Set `am` to `algebraMap M.Ω Φ`. Set `φΩ : M.Ω →+* L` to `φ.comp am`.

Set `uA : (Σ k, ι k) → Finset (Fin N) → A` to `fun q I => ⟨F.u q I, exists_isValueAt hzb (hG.2.1 q I).1⟩`. Establish `hxp : ∀ p, φΩ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') ≠ 0` using `fun p => (map_ne_zero _).2 (Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (M.x_chart_ne (mCoordIdeal_le hzb) hG k'))`. Establish `hdt : ∀ p : Ψ × Fin N, φΩ (detFac j p.2 (F.T p.1)) ≠ 0` using `fun p => (map_ne_zero _).2 (detFac_ne_zero M.j_le p.2 (hF.1 p.1).1 (hF.1 p.1).2)`. Establish `hTg : ∀ τ', (F.T τ').map φΩ * (B τ').map i = (M.g τ').map φ * U τ'` using `fun τ' => by`. Rewrite using `[hBi]`.

Conclude with `map_mul_inv_map _ (hF.1 τ').2 _`. Establish `hstep : ∀ (i₀ : Fin N) (k : K) (D : Matrix (Fin N) (Fin N) R) (c₀ c₁ : L) (W : ι k → L) (α : ℂ) (zz : ι k → ℂ), c₀ ≠ 0 → c₁ ≠ 0 → α ≠ 0 → (∀ m, c₀ * W m = c₁ * ∑ I, φΩ (F.u ⟨k, m⟩ I) * minorIJ (D.map i) I (stepCols N j i₀)) → (∀ m, zz m = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * mi …`. Introduce `i₀ k D c₀ c₁ W α zz h0 h1 hα hW hz`. Use `⟨c₁ / c₀, α⁻¹, fun m => ∑ I, cA (uA ⟨k, m⟩ I) * minorIJ D I (stepCols N j i₀), div_ne_zero h1 h0, inv_ne_zero hα, fun m => ?_, fun m => ?_⟩` and prove the remaining obligations. Establish `e1 : i (∑ I, cA (uA ⟨k, m⟩ I) * minorIJ D I (stepCols N j i₀)) = ∑ I, φΩ (F.u ⟨k, m⟩ I) * minorIJ (D.map i) I (stepCols N j i₀)`.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun I _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hic, minorIJ_map]`. Both sides reduce to the same expression. Rewrite using `[e1, div_mul_eq_mul_div, ← hW m]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[map_sum, hz m, inv_mul_cancel_left₀ hα]`. Use `Finset.sum_congr rfl fun I _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hρc, ← minorIJ_map]`. Both sides reduce to the same expression.

Establish `key : ∀ o : Option K, ∃ (e : L) (t' : ℂ) (sv : ι (o.getD k₀) → R), e ≠ 0 ∧ t' ≠ 0 ∧ (∀ m, θ (M.wCo (τ, a) k₀ ca cb RatFunc.X ⟨o, m⟩) = e * i (sv m)) ∧ ∀ m, ρ (sv m) = t' * z ⟨o, m⟩`. Introduce `o`. Consider the cases of `o with`. Consider the case `some k => show ∃ (e : L) (t' : ℂ) (sv : ι k → R), e ≠ 0 ∧ t' ≠ 0 ∧ (∀ m, θ (algebraMap Φ (RatFunc Φ) (y ⟨k, m⟩)) = e * i (sv m)) ∧ ∀ m, ρ (sv m) = t' * fstPt k₀ z ⟨k, m⟩`. Simplify using `only [hθ]`.

Distinguish the cases in `hkb : ∀ p, M.blk p ≠ some k`. Set `kb : NonPluckerBlocks M.blk` to `⟨k, hkb⟩`. Establish `hxc : M.x ⟨kb, F.c kb⟩ ≠ 0` using `M.x_chart_ne (mCoordIdeal_le hzb) hG kb`. Establish `hzc : zb ⟨kb, F.c kb⟩ = 1` using `H.1 kb`. Establish `hv : ∀ m : ι k, IsValueAt M.x (M.x ⟨kb, m⟩ / M.x ⟨kb, F.c kb⟩) zb (zb ⟨kb, m⟩ / zb ⟨kb, F.c kb⟩)` using `fun m => isValueAt_ratio hxc (by rw [hzc]; exact one_ne_zero)`.

Use `⟨φΩ (M.x ⟨kb, F.c kb⟩), 1, fun m => cA ⟨_, _, hv m⟩, (map_ne_zero _).2 hxc, one_ne_zero, fun m => ?_, fun m => ?_⟩` and prove the remaining obligations. Rewrite using `[hic, show y ⟨k, m⟩ = am (M.x ⟨kb, m⟩) from M.y_base ⟨kb, m⟩] show φ (am _) = φ (am _) * φ (am _)`. Rewrite using `[← map_mul, ← map_mul]`. Use `congr 2`. Conclude with `(mul_div_cancel₀ _ hxc).symm`.

Rewrite using `[hρc, show val ⟨_, _, hv m⟩ = _ from regVal_eq hzb _ (hv m), hzc, div_one, one_mul]`. Both sides reduce to the same expression. Use `push_neg at hkb`. Take `⟨p, hp⟩` from `hkb`. Take `⟨α, hα, hz⟩` from `H.2.2 p k hp`.

Establish `hUp : (∏ c ∈ stepCols N j p.2, U p.1 c c) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun c _ => (hU p.1).2.2 c`. Use `hstep p.2 k (B p.1) (φΩ (detFac j p.2 (F.T p.1)) * ∏ c ∈ stepCols N j p.2, U p.1 c c) (φΩ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k')) _ α _ (mul_ne_zero (hdt p) hUp) (hxp p) hα (fun m => ?_) (fun m => ?_)` and prove the remaining obligations. Conclude with `frame_gen M hF φ hp m ((hBb p.1).map i) (hU p.1).1 (hU p.1).2.1 (hTg p.1)`. Rewrite using `[hBρ]`. Conclude with `hz m`.

Consider the case `none => show ∃ (e : L) (t' : ℂ) (sv : ι k₀ → R), e ≠ 0 ∧ t' ≠ 0 ∧ (∀ m, θ (M.wCo (τ, a) k₀ ca cb RatFunc.X ⟨none, m⟩) = e * i (sv m)) ∧ ∀ m, ρ (sv m) = t' * z ⟨none, m⟩`. Take `⟨V, hVb, hVt, hVd, hV⟩` from `GlobalTheory.T.elementary_factor_commutation L N j ca cb (U τ) (θ RatFunc.X) s hcb hS (hU τ).1 (hU τ).2.1 (hU τ).2.2 hU0 hθX`. Establish `hcbS : cb ∉ stepCols N j a`. Simplify using `only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]`. Unfold `lastCol at hca`.

Apply the tactic sequence `split_ifs at hca ⊢ <;> omega`. Establish `hVp : (∏ c ∈ stepCols N j a, V c c) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun c hc => hVd c fun e => hcbS (e ▸ hc)`. Take `⟨α, hα, hz⟩` from `H'.2.2 (τ, a) k₀ hk`. Rewrite `hz` using `[hsnd, Function.update_self]`. Establish `hEi : (1 + Matrix.single cb ca sR).map i = 1 + Matrix.single cb ca s`.

Rewrite using `[transv_map, his]`. Establish `hEρ : (1 + Matrix.single cb ca sR).map ρ = 1 + Matrix.single cb ca t`. Rewrite using `[transv_map, hρs]`. Establish `hEθ : ((M.g τ).map (algebraMap Φ (RatFunc Φ)) * (1 + Matrix.single cb ca RatFunc.X)).map θ = (M.g τ).map φ * (1 + Matrix.single cb ca (θ RatFunc.X))`. Rewrite using `[Matrix.map_mul, transv_map]`.

Use `congr 1`. Use extensionality with `r c`. Conclude with `hθ _`. Use `hstep a k₀ (B τ * (1 + Matrix.single cb ca sR)) (φΩ (detFac j a (F.T τ)) * ∏ c ∈ stepCols N j a, V c c) (φΩ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b (τ, a) k')) _ α _ (mul_ne_zero (hdt (τ, a)) hVp) (hxp (τ, a)) hα (fun m => ?_) (fun m => ?_)` and prove the remaining obligations. Establish `e1 : θ (M.wCo (τ, a) k₀ ca cb RatFunc.X ⟨none, m⟩) = ∑ I, φΩ (M.coef ⟨k₀, m⟩ I) * minorIJ ((M.g τ).map φ * (1 + Matrix.single cb ca (θ RatFunc.X))) I (stepCols N j a)` using `by show θ (∑ I, _) = _`.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun I _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hθ, ← hEθ, minorIJ_map]`. Both sides reduce to the same expression. Rewrite using `[e1]`.

Use `frame_any M hF φΩ (p := (τ, a)) hk m (G := (B τ * (1 + Matrix.single cb ca sR)).map i) (bb := V) (gg := (M.g τ).map φ * (1 + Matrix.single cb ca (θ RatFunc.X))) ((hBb τ).mul (transv_block hS sR) |>.map i) hVb hVt (by` as an intermediate fact. Rewrite using `[Matrix.map_mul, hEi]`. Use `show (F.T τ).map φΩ * ((B τ).map i * _) = _`. Rewrite using `[← Matrix.mul_assoc, hTg, Matrix.mul_assoc, ← hV, Matrix.mul_assoc])`. Conclude with `this`.

Rewrite using `[Matrix.map_mul, hBρ, hEρ, ← snd_self z m]`. Conclude with `hz m`. Use `choose e t' sv he ht has hv using key`. Establish `hz' : z ∈ mcPts (mCoordIdeal (fun q : Σ o : Option K, ι (o.getD k₀) => θ (M.wCo (τ, a) k₀ ca cb RatFunc.X q)))` using `mem_mcPts_of_ringHom i hi ρ _ (fun q => sv q.1 q.2) e t' z hnz he ht (fun q => has q.1 q.2) fun q => hv q.1 q.2`. Use `⟨hnz, fun f hf => hz'.2 f ?_⟩` and prove the remaining obligations.

Establish `h0 : mConeMap (M.wCo (τ, a) k₀ ca cb RatFunc.X) f = 0` using `hf`. Use `show mConeMap (θ ∘ M.wCo (τ, a) k₀ ca cb RatFunc.X) f = 0`. Rewrite using `[mConeMap_comp, h0, map_zero]`.
-/
theorem back {τ : Ψ} {a b ca cb : Fin N} {k₀ : K} (hb : (b : ℕ) = a + 1) (hab : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hk : M.blk (τ, a) = some k₀) (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1)
    {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ}
    (hzb : basePart M.blk (fstPt k₀ z) ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal (basePart M.blk (fstPt k₀ z))))
    {h : Ψ → Matrix (Fin N) (Fin N) ℂ} {t : ℂ} (H : M.IsFlagOf F (fstPt k₀ z) h)
    (H' : M.IsFlagOf F (sndPt k₀ z) (Function.update h τ (h τ * (1 + Matrix.single cb ca t)))) :
    z ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) := by
  have hS := same_summand hb hab hca hcb
  have hsnd := basePart_snd M hk z
  have hnz : ∀ o : Option K, ∃ i, z ⟨o, i⟩ ≠ 0 := by
    intro o
    cases o with
    | some k => exact flag_nonzero M hF hzb hG H k
    | none =>
      obtain ⟨i, hi⟩ := flag_nonzero M hF (hsnd ▸ hzb) (hsnd ▸ hG) H' k₀
      exact ⟨i, by rwa [snd_self] at hi⟩
  let zb := basePart M.blk (fstPt k₀ z)
  let A := regRing M.x zb
  let val : A →+* ℂ := regVal hzb
  obtain ⟨L, R, _, _, φ, θ, U, s, i, ρ, cA, B, sR, hi, hθ, hU, hU0, hθX, hic, hρc, hBb, hBi, hBρ, his, hρs⟩ :=
    GlobalTheory.T.generic_flag_elementary_twist M.Ω Φ Ψ N j M.g F.T A val h t τ ca cb hcb hS M.g_block M.g_indep hF.1 fun τ => (H.2.1 τ).1
  let am := algebraMap M.Ω Φ
  let φΩ : M.Ω →+* L := φ.comp am
  let uA : (Σ k, ι k) → Finset (Fin N) → A := fun q I => ⟨F.u q I, exists_isValueAt hzb (hG.2.1 q I).1⟩
  have hxp : ∀ p, φΩ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') ≠ 0 := fun p => (map_ne_zero _).2
    (Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (M.x_chart_ne (mCoordIdeal_le hzb) hG k'))
  have hdt : ∀ p : Ψ × Fin N, φΩ (detFac j p.2 (F.T p.1)) ≠ 0 := fun p => (map_ne_zero _).2
    (detFac_ne_zero M.j_le p.2 (hF.1 p.1).1 (hF.1 p.1).2)
  have hTg : ∀ τ', (F.T τ').map φΩ * (B τ').map i = (M.g τ').map φ * U τ' := fun τ' => by
    rw [hBi]
    exact map_mul_inv_map _ (hF.1 τ').2 _
  have hstep : ∀ (i₀ : Fin N) (k : K) (D : Matrix (Fin N) (Fin N) R) (c₀ c₁ : L) (W : ι k → L) (α : ℂ) (zz : ι k → ℂ),
      c₀ ≠ 0 → c₁ ≠ 0 → α ≠ 0 →
      (∀ m, c₀ * W m = c₁ * ∑ I, φΩ (F.u ⟨k, m⟩ I) * minorIJ (D.map i) I (stepCols N j i₀)) →
      (∀ m, zz m = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ (D.map ρ) I (stepCols N j i₀)) →
      ∃ (e : L) (t' : ℂ) (sv : ι k → R), e ≠ 0 ∧ t' ≠ 0 ∧ (∀ m, W m = e * i (sv m)) ∧ ∀ m, ρ (sv m) = t' * zz m := by
    intro i₀ k D c₀ c₁ W α zz h0 h1 hα hW hz
    refine ⟨c₁ / c₀, α⁻¹, fun m => ∑ I, cA (uA ⟨k, m⟩ I) * minorIJ D I (stepCols N j i₀),
      div_ne_zero h1 h0, inv_ne_zero hα, fun m => ?_, fun m => ?_⟩
    · have e1 : i (∑ I, cA (uA ⟨k, m⟩ I) * minorIJ D I (stepCols N j i₀)) =
          ∑ I, φΩ (F.u ⟨k, m⟩ I) * minorIJ (D.map i) I (stepCols N j i₀) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [map_mul, hic, minorIJ_map]
        rfl
      rw [e1, div_mul_eq_mul_div, ← hW m]
      field_simp
    · rw [map_sum, hz m, inv_mul_cancel_left₀ hα]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [map_mul, hρc, ← minorIJ_map]
      rfl
  have key : ∀ o : Option K, ∃ (e : L) (t' : ℂ) (sv : ι (o.getD k₀) → R), e ≠ 0 ∧ t' ≠ 0 ∧
      (∀ m, θ (M.wCo (τ, a) k₀ ca cb RatFunc.X ⟨o, m⟩) = e * i (sv m)) ∧ ∀ m, ρ (sv m) = t' * z ⟨o, m⟩ := by
    intro o
    cases o with
    | some k =>
      show ∃ (e : L) (t' : ℂ) (sv : ι k → R), e ≠ 0 ∧ t' ≠ 0 ∧
        (∀ m, θ (algebraMap Φ (RatFunc Φ) (y ⟨k, m⟩)) = e * i (sv m)) ∧ ∀ m, ρ (sv m) = t' * fstPt k₀ z ⟨k, m⟩
      simp only [hθ]
      by_cases hkb : ∀ p, M.blk p ≠ some k
      · let kb : NonPluckerBlocks M.blk := ⟨k, hkb⟩
        have hxc : M.x ⟨kb, F.c kb⟩ ≠ 0 := M.x_chart_ne (mCoordIdeal_le hzb) hG kb
        have hzc : zb ⟨kb, F.c kb⟩ = 1 := H.1 kb
        have hv : ∀ m : ι k, IsValueAt M.x (M.x ⟨kb, m⟩ / M.x ⟨kb, F.c kb⟩) zb (zb ⟨kb, m⟩ / zb ⟨kb, F.c kb⟩) := fun m =>
          isValueAt_ratio hxc (by rw [hzc]; exact one_ne_zero)
        refine ⟨φΩ (M.x ⟨kb, F.c kb⟩), 1, fun m => cA ⟨_, _, hv m⟩, (map_ne_zero _).2 hxc, one_ne_zero, fun m => ?_, fun m => ?_⟩
        · rw [hic, show y ⟨k, m⟩ = am (M.x ⟨kb, m⟩) from M.y_base ⟨kb, m⟩]
          show φ (am _) = φ (am _) * φ (am _)
          rw [← map_mul, ← map_mul]
          congr 2
          exact (mul_div_cancel₀ _ hxc).symm
        · rw [hρc, show val ⟨_, _, hv m⟩ = _ from regVal_eq hzb _ (hv m), hzc, div_one, one_mul]
          rfl
      · push_neg at hkb
        obtain ⟨p, hp⟩ := hkb
        obtain ⟨α, hα, hz⟩ := H.2.2 p k hp
        have hUp : (∏ c ∈ stepCols N j p.2, U p.1 c c) ≠ 0 := Finset.prod_ne_zero_iff.2 fun c _ => (hU p.1).2.2 c
        refine hstep p.2 k (B p.1) (φΩ (detFac j p.2 (F.T p.1)) * ∏ c ∈ stepCols N j p.2, U p.1 c c)
          (φΩ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k')) _ α _ (mul_ne_zero (hdt p) hUp) (hxp p) hα (fun m => ?_) (fun m => ?_)
        · exact frame_gen M hF φ hp m ((hBb p.1).map i) (hU p.1).1 (hU p.1).2.1 (hTg p.1)
        · rw [hBρ]
          exact hz m
    | none =>
      show ∃ (e : L) (t' : ℂ) (sv : ι k₀ → R), e ≠ 0 ∧ t' ≠ 0 ∧
        (∀ m, θ (M.wCo (τ, a) k₀ ca cb RatFunc.X ⟨none, m⟩) = e * i (sv m)) ∧ ∀ m, ρ (sv m) = t' * z ⟨none, m⟩
      obtain ⟨V, hVb, hVt, hVd, hV⟩ := GlobalTheory.T.elementary_factor_commutation L N j ca cb (U τ) (θ RatFunc.X) s hcb hS (hU τ).1 (hU τ).2.1
        (hU τ).2.2 hU0 hθX
      have hcbS : cb ∉ stepCols N j a := by
        simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        unfold lastCol at hca
        split_ifs at hca ⊢ <;> omega
      have hVp : (∏ c ∈ stepCols N j a, V c c) ≠ 0 := Finset.prod_ne_zero_iff.2 fun c hc =>
        hVd c fun e => hcbS (e ▸ hc)
      obtain ⟨α, hα, hz⟩ := H'.2.2 (τ, a) k₀ hk
      rw [hsnd, Function.update_self] at hz
      have hEi : (1 + Matrix.single cb ca sR).map i = 1 + Matrix.single cb ca s := by
        rw [transv_map, his]
      have hEρ : (1 + Matrix.single cb ca sR).map ρ = 1 + Matrix.single cb ca t := by
        rw [transv_map, hρs]
      have hEθ : ((M.g τ).map (algebraMap Φ (RatFunc Φ)) * (1 + Matrix.single cb ca RatFunc.X)).map θ =
          (M.g τ).map φ * (1 + Matrix.single cb ca (θ RatFunc.X)) := by
        rw [Matrix.map_mul, transv_map]
        congr 1
        ext r c
        exact hθ _
      refine hstep a k₀ (B τ * (1 + Matrix.single cb ca sR)) (φΩ (detFac j a (F.T τ)) * ∏ c ∈ stepCols N j a, V c c)
        (φΩ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b (τ, a) k')) _ α _ (mul_ne_zero (hdt (τ, a)) hVp) (hxp (τ, a)) hα (fun m => ?_) (fun m => ?_)
      · have e1 : θ (M.wCo (τ, a) k₀ ca cb RatFunc.X ⟨none, m⟩) = ∑ I, φΩ (M.coef ⟨k₀, m⟩ I) *
            minorIJ ((M.g τ).map φ * (1 + Matrix.single cb ca (θ RatFunc.X))) I (stepCols N j a) := by
          show θ (∑ I, _) = _
          rw [map_sum]
          refine Finset.sum_congr rfl fun I _ => ?_
          rw [map_mul, hθ, ← hEθ, minorIJ_map]
          rfl
        rw [e1]
        have := frame_any M hF φΩ (p := (τ, a)) hk m (G := (B τ * (1 + Matrix.single cb ca sR)).map i)
          (bb := V) (gg := (M.g τ).map φ * (1 + Matrix.single cb ca (θ RatFunc.X))) ((hBb τ).mul (transv_block hS sR) |>.map i)
          hVb hVt (by
            rw [Matrix.map_mul, hEi]
            show (F.T τ).map φΩ * ((B τ).map i * _) = _
            rw [← Matrix.mul_assoc, hTg, Matrix.mul_assoc, ← hV, Matrix.mul_assoc])
        exact this
      · rw [Matrix.map_mul, hBρ, hEρ, ← snd_self z m]
        exact hz m
  choose e t' sv he ht has hv using key
  have hz' : z ∈ mcPts (mCoordIdeal (fun q : Σ o : Option K, ι (o.getD k₀) => θ (M.wCo (τ, a) k₀ ca cb RatFunc.X q))) :=
    mem_mcPts_of_ringHom i hi ρ _ (fun q => sv q.1 q.2) e t' z hnz he ht (fun q => has q.1 q.2) fun q => hv q.1 q.2
  refine ⟨hnz, fun f hf => hz'.2 f ?_⟩
  have h0 : mConeMap (M.wCo (τ, a) k₀ ca cb RatFunc.X) f = 0 := hf
  show mConeMap (θ ∘ M.wCo (τ, a) k₀ ca cb RatFunc.X) f = 0
  rw [mConeMap_comp, h0, map_zero]

end Flags

/- English proof (translation)
Introduce `K _ ι _ Φ _ y Ψ _ _ N j M d τ a b k₀ ca cb hb hab hk hca hcb hy F z hF hzb hG hc`. Use `⟨fun hz => ?_, fun ⟨h, t, H, H'⟩ => back M hb hab hk hca hcb hF hzb hG H H'⟩` and prove the remaining obligations. Establish `hI` using `(GlobalTheory.T.flag_adjacent_swap_varieties_arithmetic K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk hca hcb hy).2.2.2.2 (v₁ k₀) (fun p hp => v₁_ne hp) (v₁_self k₀)`. Establish `hsnd` using `basePart_snd M hk z`. Establish `z₀ : fstPt k₀ z ∈ mcPts (mCoordIdeal y)` using `comp_mem_mcPts (isBlockMap_v₀ k₀) (algebraMap Φ (RatFunc Φ)) (funext fun _ => rfl) hz`.

Establish `z₁ : sndPt k₀ z ∈ mcPts (mCoordIdeal y)` using `snd_mem hI hz`. Take `⟨h, H⟩` from `flag_fwd M hF z₀ hG hc`. Take `⟨h', H'⟩` from `flag_fwd M hF z₁ (hsnd ▸ hG) (hsnd ▸ hc)`. Conclude with `fwd_flags M hb hab hk hca hcb hF hzb hG H H'`.
-/
theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (d : ℕ) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → ∀ (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ), M.IsFrame F → basePart M.blk (fstPt k₀ z) ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal (basePart M.blk (fstPt k₀ z))) → (∀ k, basePart M.blk (fstPt k₀ z) ⟨k, F.c k⟩ = 1) → (z ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ↔ ∃ (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (t : ℂ), M.IsFlagOf F (fstPt k₀ z) h ∧ M.IsFlagOf F (sndPt k₀ z) (Function.update h τ (h τ * (1 + Matrix.single cb ca t)))) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M d τ a b k₀ ca cb hb hab hk hca hcb hy F z hF hzb hG hc
  refine ⟨fun hz => ?_, fun ⟨h, t, H, H'⟩ => back M hb hab hk hca hcb hF hzb hG H H'⟩
  have hI := (GlobalTheory.T.flag_adjacent_swap_varieties_arithmetic K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk hca hcb hy).2.2.2.2 (v₁ k₀)
    (fun p hp => v₁_ne hp) (v₁_self k₀)
  have hsnd := basePart_snd M hk z
  have z₀ : fstPt k₀ z ∈ mcPts (mCoordIdeal y) :=
    comp_mem_mcPts (isBlockMap_v₀ k₀) (algebraMap Φ (RatFunc Φ)) (funext fun _ => rfl) hz
  have z₁ : sndPt k₀ z ∈ mcPts (mCoordIdeal y) := snd_mem hI hz
  obtain ⟨h, H⟩ := flag_fwd M hF z₀ hG hc
  obtain ⟨h', H'⟩ := flag_fwd M hF z₁ (hsnd ▸ hG) (hsnd ▸ hc)
  exact fwd_flags M hb hab hk hca hcb hF hzb hG H H'

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Pts
