import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.SharpRestriction.Divisibility.ChainOperators.ClosedPartStatementHolds

noncomputable section

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.PrimeDegreeVariant

namespace Formalism.MainNotions.DIV.Proofs.ScaledLatticeNorms

section Norms

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt`. Establish `: (fun i => v.embedding (b.repr (k • x) i)) = v.embedding k • (fun i => v.embedding (b.repr x i))`. Use function extensionality and compare the values at `i`. Simplify using `[map_smul, smul_eq_mul]`. Rewrite using `[this, Matrix.mulVec_smul]`.
-/
theorem fcoord_smul (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (k : K) (x : V) :
    Formalism.HermitianLatticesTheory.fcoord b X v (k • x) = v.embedding k • Formalism.HermitianLatticesTheory.fcoord b X v x := by
  unfold Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
  have : (fun i => v.embedding (b.repr (k • x) i)) = v.embedding k • (fun i => v.embedding (b.repr x i)) := by
    funext i; simp [map_smul, smul_eq_mul]
  rw [this, Matrix.mulVec_smul]

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.cnorm`. Simplify using `only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]`. Rewrite using `[← Finset.mul_sum, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]`.
-/
theorem cnorm_smul (a : ℂ) (u : ι → ℂ) : Formalism.HermitianLatticesTheory.cnorm (a • u) = ‖a‖ * Formalism.HermitianLatticesTheory.cnorm u := by
  unfold Formalism.HermitianLatticesTheory.cnorm
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.normAt`. Rewrite using `[fcoord_smul, cnorm_smul]`.
-/
theorem normAt_smul (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (k : K) (x : V) :
    Formalism.HermitianLatticesTheory.normAt b X v (k • x) = ‖v.embedding k‖ * Formalism.HermitianLatticesTheory.normAt b X v x := by
  unfold Formalism.HermitianLatticesTheory.normAt
  rw [fcoord_smul, cnorm_smul]

/- English proof (translation)
The claim follows from `Real.sqrt_nonneg _`.
-/
theorem normAt_nonneg (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x : V) :
    0 ≤ Formalism.HermitianLatticesTheory.normAt b X v x := Real.sqrt_nonneg _

/- English proof (translation)
Establish `ha' : ((a : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast ha`. Establish `hinv : (((a : ℝ) : ℂ) • X v)⁻¹ = ((a : ℝ) : ℂ)⁻¹ • (X v)⁻¹`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ ha', one_smul, Matrix.nonsing_inv_mul _ hX]`. Unfold `Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord`.

Simplify using `only []`. Rewrite using `[hinv]`. Establish `hmv : (((a : ℝ) : ℂ)⁻¹ • (X v)⁻¹).mulVec (Formalism.HermitianLatticesTheory.vecAt b v x) = ((a : ℝ) : ℂ)⁻¹ • ((X v)⁻¹.mulVec (Formalism.HermitianLatticesTheory.vecAt b v x))`. Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]`.

Rewrite using `[hmv, cnorm_smul]`. Use `congr 1`. Simplify using `[norm_inv, Complex.norm_real, Real.norm_eq_abs]`.
-/
theorem normAt_frame_smul (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (hX : IsUnit (X v).det) (a : ℝ) (ha : a ≠ 0) (x : V) :
    Formalism.HermitianLatticesTheory.normAt b (fun w => ((a : ℝ) : ℂ) • X w) v x = |a|⁻¹ * Formalism.HermitianLatticesTheory.normAt b X v x := by
  have ha' : ((a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha
  have hinv : (((a : ℝ) : ℂ) • X v)⁻¹ = ((a : ℝ) : ℂ)⁻¹ • (X v)⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ ha', one_smul,
      Matrix.nonsing_inv_mul _ hX]
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord
  simp only []
  rw [hinv]
  have hmv : (((a : ℝ) : ℂ)⁻¹ • (X v)⁻¹).mulVec (Formalism.HermitianLatticesTheory.vecAt b v x) =
      ((a : ℝ) : ℂ)⁻¹ • ((X v)⁻¹.mulVec (Formalism.HermitianLatticesTheory.vecAt b v x)) := by
    ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [hmv, cnorm_smul]
  congr 1
  simp [norm_inv, Complex.norm_real, Real.norm_eq_abs]

end Norms

section Lat

variable {K : Type} [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
  {W κ : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
  [Fintype κ] [DecidableEq κ]

/- English proof (translation)
Unfold `Formalism.HN.nPl`. Conclude with `Fintype.card_pos` after adjusting the coercions.
-/
theorem nPl_pos : 0 < (Formalism.HN.nPl K : ℝ) := by
  unfold Formalism.HN.nPl
  exact_mod_cast Fintype.card_pos

/- English proof (translation)
Unfold `Formalism.HN.rkK`. Rewrite using `[Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image]`. Conclude with `(LinearEquiv.finrank_eq (Submodule.equivMapOfInjective ψ hψ _)).symm`.
-/
theorem rkK_map (ψ : V →ₗ[K] W) (hψ : Function.Injective ψ) (M : Submodule (𝓞 K) V) :
    Formalism.HN.rkK (M.map (ψ.restrictScalars (𝓞 K))) = Formalism.HN.rkK M := by
  unfold Formalism.HN.rkK
  rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective ψ hψ _)).symm

/- English proof (translation)
The claim follows from `Submodule.finrank_mono (Submodule.span_mono h)`.
-/
theorem rkK_mono [FiniteDimensional K V] {M N : Submodule (𝓞 K) V} (h : M ≤ N) :
    Formalism.HN.rkK M ≤ Formalism.HN.rkK N :=
  Submodule.finrank_mono (Submodule.span_mono h)

/- English proof (translation)
Introduce and unpack `rfl`. Unfold `Formalism.HN.rkK at h`. Rewrite `h` using `[Submodule.bot_coe, Submodule.span_singleton_eq_bot.2 rfl, finrank_bot]`. Conclude with `lt_irrefl _ h`.
-/
theorem ne_bot_of_rkK_pos {M : Submodule (𝓞 K) V} (h : 0 < Formalism.HN.rkK M) : M ≠ ⊥ := by
  rintro rfl
  unfold Formalism.HN.rkK at h
  rw [Submodule.bot_coe, Submodule.span_singleton_eq_bot.2 rfl, finrank_bot] at h
  exact lt_irrefl _ h

/- English proof (translation)
Establish `: IsNoetherian (𝓞 K) N` using `isNoetherian_of_fg_of_noetherian N hN`. Establish `hc : (M.comap N.subtype).FG` using `IsNoetherian.noetherian _`. Use `hc.map N.subtype` as an intermediate fact. Rewrite `this` using `[Submodule.map_comap_subtype, inf_eq_right.2 h]`. Then use the resulting hypothesis.
-/
theorem fg_of_le_fg {M N : Submodule (𝓞 K) V} (hN : N.FG) (h : M ≤ N) : M.FG := by
  have : IsNoetherian (𝓞 K) N := isNoetherian_of_fg_of_noetherian N hN
  have hc : (M.comap N.subtype).FG := IsNoetherian.noetherian _
  have := hc.map N.subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.2 h] at this

/- English proof (translation)
Establish `hs : 0 < Real.sqrt c` using `Real.sqrt_pos.2 hc`. Use `set a : ℝ := (Real.sqrt c)⁻¹ with ha`. Establish `ha0 : 0 < a` using `inv_pos.2 hs`. Use `set X'' : InfinitePlace K → Matrix ι ι ℂ := fun v => ((a : ℝ) : ℂ) • X v with hX''`. Establish `hX''u : ∀ v, IsUnit (X'' v).det`.

Introduce `v`. Simplify using `only [hX'', Matrix.det_smul]`. Conclude with `(IsUnit.pow _ (isUnit_iff_ne_zero.2 (by exact_mod_cast ha0.ne'))).mul (hX v)`. Establish `hnorm : ∀ v x, Formalism.HermitianLatticesTheory.normAt b' X' v (ψ x) = Formalism.HermitianLatticesTheory.normAt b X'' v x`. Introduce `v x`.

Rewrite using `[hX'', normAt_frame_smul b X v (hX v) a ha0.ne' x, abs_of_pos ha0, ha, inv_inv]`. Rewrite using `[← Real.sqrt_sq (normAt_nonneg b' X' v (ψ x)), hn v x, Real.sqrt_mul hc.le, Real.sqrt_sq (normAt_nonneg b X v x)]`. Take `⟨-, -, hsl, hmx, -⟩` from `Formalism.HN.rerealize K V ι W κ b X'' b' X' ψ hX''u hX' hψ hnorm M hM`. Take `⟨-, -, h3, -⟩` from `Formalism.HN.twist K V ι b X (fun _ => a) hX (fun _ => ha0) M hM`. Take `⟨hmu, hmax, -⟩` from `h3 hM0`.

Establish `ht : (1 / (Formalism.HN.nPl K : ℝ)) * ∑ _v : InfinitePlace K, Real.log a = -(1 / 2) * Real.log c`. Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Establish `hf` using `(nPl_pos (K := K)).ne'`. Unfold `Formalism.HN.nPl at hf ⊢`. Rewrite using `[ha, Real.log_inv, Real.log_sqrt hc.le]`.

Clear the denominators using the available nonvanishing facts. Establish `e1 : Formalism.HN.muDef b X'' M = Formalism.HN.muDef b X M - Real.log c`. Rewrite using `[show Formalism.HN.muDef b X'' M = _ from hmu, ht]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : Formalism.HN.muMaxDef b X'' M = Formalism.HN.muMaxDef b X M - Real.log c`.

Rewrite using `[show Formalism.HN.muMaxDef b X'' M = _ from hmax, ht]`. Expand and normalize the polynomial expressions, which then agree. Prove the components needed by the constructor for the conclusion. Rewrite using `[← e1]`. Unfold `Formalism.HN.muDef`.

Rewrite using `[hsl]`. Rewrite using `[← e2]`. Unfold `Formalism.HN.muMaxDef`. Rewrite using `[hmx]`.
-/
theorem scale_map (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (hX' : ∀ v, IsUnit (X' v).det)
    (ψ : V →ₗ[K] W) (hψ : Function.Injective ψ) (c : ℝ) (hc : 0 < c)
    (hn : ∀ v x, Formalism.HermitianLatticesTheory.normAt b' X' v (ψ x) ^ 2 = c * Formalism.HermitianLatticesTheory.normAt b X v x ^ 2)
    (M : Submodule (𝓞 K) V) (hM : M.FG) (hM0 : M ≠ ⊥) :
    Formalism.HN.muDef b' X' (M.map (ψ.restrictScalars (𝓞 K))) = Formalism.HN.muDef b X M - Real.log c ∧
    Formalism.HN.muMaxDef b' X' (M.map (ψ.restrictScalars (𝓞 K))) = Formalism.HN.muMaxDef b X M - Real.log c := by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  set a : ℝ := (Real.sqrt c)⁻¹ with ha
  have ha0 : 0 < a := inv_pos.2 hs
  set X'' : InfinitePlace K → Matrix ι ι ℂ := fun v => ((a : ℝ) : ℂ) • X v with hX''
  have hX''u : ∀ v, IsUnit (X'' v).det := by
    intro v
    simp only [hX'', Matrix.det_smul]
    exact (IsUnit.pow _ (isUnit_iff_ne_zero.2 (by exact_mod_cast ha0.ne'))).mul (hX v)
  have hnorm : ∀ v x, Formalism.HermitianLatticesTheory.normAt b' X' v (ψ x) = Formalism.HermitianLatticesTheory.normAt b X'' v x := by
    intro v x
    rw [hX'', normAt_frame_smul b X v (hX v) a ha0.ne' x, abs_of_pos ha0, ha, inv_inv]
    rw [← Real.sqrt_sq (normAt_nonneg b' X' v (ψ x)), hn v x, Real.sqrt_mul hc.le,
      Real.sqrt_sq (normAt_nonneg b X v x)]
  obtain ⟨-, -, hsl, hmx, -⟩ := Formalism.HN.rerealize K V ι W κ b X'' b' X' ψ hX''u hX' hψ hnorm M hM
  obtain ⟨-, -, h3, -⟩ := Formalism.HN.twist K V ι b X (fun _ => a) hX (fun _ => ha0) M hM
  obtain ⟨hmu, hmax, -⟩ := h3 hM0
  have ht : (1 / (Formalism.HN.nPl K : ℝ)) * ∑ _v : InfinitePlace K, Real.log a = -(1 / 2) * Real.log c := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hf := (nPl_pos (K := K)).ne'
    unfold Formalism.HN.nPl at hf ⊢
    rw [ha, Real.log_inv, Real.log_sqrt hc.le]
    field_simp
  have e1 : Formalism.HN.muDef b X'' M = Formalism.HN.muDef b X M - Real.log c := by
    rw [show Formalism.HN.muDef b X'' M = _ from hmu, ht]; ring
  have e2 : Formalism.HN.muMaxDef b X'' M = Formalism.HN.muMaxDef b X M - Real.log c := by
    rw [show Formalism.HN.muMaxDef b X'' M = _ from hmax, ht]; ring
  constructor
  · rw [← e1]; unfold Formalism.HN.muDef; rw [hsl]
  · rw [← e2]; unfold Formalism.HN.muMaxDef; rw [hmx]

/- English proof (translation)
Establish `hL` using `(Formalism.HN.plLat K V ι b X hX M hM).1`. Use `(Formalism.HN.muChar (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) M hL hM0).2.2.2.2` as an intermediate fact. Unfold `Formalism.HN.muDef Formalism.HN.muMaxDef`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem mu_le_muMax (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    (M : Submodule (𝓞 K) V) (hM : M.FG) (hM0 : M ≠ ⊥) :
    Formalism.HN.muDef b X M ≤ Formalism.HN.muMaxDef b X M := by
  have hL := (Formalism.HN.plLat K V ι b X hX M hM).1
  have := (Formalism.HN.muChar (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) M hL hM0).2.2.2.2
  unfold Formalism.HN.muDef Formalism.HN.muMaxDef; linarith

/- English proof (translation)
Establish `hN0 : N ≠ ⊥` using `fun h => hM0 (eq_bot_iff.2 (h ▸ hMN))`. Establish `hLN` using `(Formalism.HN.plLat K V ι b X hX N hN).1`. Establish `hLM` using `(Formalism.HN.plLat K V ι b X hX M hM).1`. Establish `h1` using `((Formalism.HN.muChar (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) N hLN hN0).1 _).1 le_rfl`. Establish `h2` using `((Formalism.HN.muChar (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) M hLM hM0).1 (Formalism.HN.muMax (Formalism.HermitianLatticesTheory.realize b X) N)).2 (fun N' hN' => h1 N' (hN'.trans hMN))`.

Unfold `Formalism.HN.muMaxDef`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem muMax_mono (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    {M N : Submodule (𝓞 K) V} (hMN : M ≤ N) (hM : M.FG) (hN : N.FG) (hM0 : M ≠ ⊥) :
    Formalism.HN.muMaxDef b X M ≤ Formalism.HN.muMaxDef b X N := by
  have hN0 : N ≠ ⊥ := fun h => hM0 (eq_bot_iff.2 (h ▸ hMN))
  have hLN := (Formalism.HN.plLat K V ι b X hX N hN).1
  have hLM := (Formalism.HN.plLat K V ι b X hX M hM).1
  have h1 := ((Formalism.HN.muChar (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) N hLN hN0).1 _).1 le_rfl
  have h2 := ((Formalism.HN.muChar (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) M hLM hM0).1
    (Formalism.HN.muMax (Formalism.HermitianLatticesTheory.realize b X) N)).2 (fun N' hN' => h1 N' (hN'.trans hMN))
  unfold Formalism.HN.muMaxDef; linarith

/- English proof (translation)
Establish `hN0 : N ≠ ⊥` using `fun h => hM0 (eq_bot_iff.2 (h ▸ hMN))`. Take `⟨-, hmM, -, -, -, hle⟩` from `Formalism.HN.sizeMu K V ι b X hX M hM hM0`. Take `⟨-, hmN, -, -, -, -⟩` from `Formalism.HN.sizeMu K V ι b X hX N hN hN0`. Establish `hhtN` using `(Formalism.HN.plLat K V ι b X hX N hN).2.2`. Establish `hhtM` using `(Formalism.HN.plLat K V ι b X hX M hM).2.2`.

Establish `h` using `hle N hMN hN hrk`. Rewrite using `[hmM, hmN]`. Unfold `Formalism.HN.size`. Rewrite using `[hrk, Real.log_rpow hhtN, Real.log_rpow hhtM]`. Establish `hl : Real.log (Formalism.HN.ht b X N) ≤ Real.log (Formalism.HN.ht b X M)` using `Real.log_le_log hhtN h`.

Establish `hp : 0 ≤ (1 : ℝ) / (2 * (Formalism.HN.nPl K : ℝ) * (Formalism.HN.rkK M : ℝ))` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem mu_mono (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    {M N : Submodule (𝓞 K) V} (hMN : M ≤ N) (hM : M.FG) (hN : N.FG) (hM0 : M ≠ ⊥)
    (hrk : Formalism.HN.rkK N = Formalism.HN.rkK M) :
    Formalism.HN.muDef b X M ≤ Formalism.HN.muDef b X N := by
  have hN0 : N ≠ ⊥ := fun h => hM0 (eq_bot_iff.2 (h ▸ hMN))
  obtain ⟨-, hmM, -, -, -, hle⟩ := Formalism.HN.sizeMu K V ι b X hX M hM hM0
  obtain ⟨-, hmN, -, -, -, -⟩ := Formalism.HN.sizeMu K V ι b X hX N hN hN0
  have hhtN := (Formalism.HN.plLat K V ι b X hX N hN).2.2
  have hhtM := (Formalism.HN.plLat K V ι b X hX M hM).2.2
  have h := hle N hMN hN hrk
  rw [hmM, hmN]
  unfold Formalism.HN.size
  rw [hrk, Real.log_rpow hhtN, Real.log_rpow hhtM]
  have hl : Real.log (Formalism.HN.ht b X N) ≤ Real.log (Formalism.HN.ht b X M) := Real.log_le_log hhtN h
  have hp : 0 ≤ (1 : ℝ) / (2 * (Formalism.HN.nPl K : ℝ) * (Formalism.HN.rkK M : ℝ)) := by positivity
  nlinarith

end Lat

section Level

variable {K : Type} [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]

/- English proof (translation)
Take `⟨y, hy, hy0⟩` from `(Submodule.ne_bot_iff M).1 hM`. Conclude with `(Submodule.ne_bot_iff _).2 ⟨ψ y, ⟨y, hy, rfl⟩, fun h => hy0 (hψ (h.trans (map_zero ψ).symm))⟩`.
-/
theorem map_ne_bot {V W : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (ψ : V →ₗ[K] W) (hψ : Function.Injective ψ) {M : Submodule (𝓞 K) V} (hM : M ≠ ⊥) :
    M.map (ψ.restrictScalars (𝓞 K)) ≠ ⊥ := by
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff M).1 hM
  exact (Submodule.ne_bot_iff _).2 ⟨ψ y, ⟨y, hy, rfl⟩, fun h => hy0 (hψ (h.trans (map_zero ψ).symm))⟩

/- English proof (translation)
Introduce and unpack `_ ⟨x, hx, rfl⟩`. Use `⟨hjL x hx, ?_⟩` and prove the remaining obligations. Use `show j x ∈ LinearMap.range e`. Rewrite using `[← hrange]`. Conclude with `LinearMap.mem_range_self j x`.
-/
theorem map_le_cutE (A RP : HLat K) (e : Module.End K A.V) (j : RP.V →ₗ[K] A.V)
    (hrange : LinearMap.range j = LinearMap.range e) (hjL : ∀ x ∈ RP.L, j x ∈ A.L) :
    RP.L.map (j.restrictScalars (𝓞 K)) ≤ cutE A e A.L := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨hjL x hx, ?_⟩
  show j x ∈ LinearMap.range e
  rw [← hrange]; exact LinearMap.mem_range_self j x

/- English proof (translation)
Establish `: FiniteDimensional K A.V` using `Module.Finite.of_basis A.b`. Use `set Cut := cutE A e A.L with hCut`. Establish `hCutFG : Cut.FG` using `fg_of_le_fg hAL inf_le_left`. Use `set J := RP.L.map (j.restrictScalars (𝓞 K)) with hJ`. Establish `hJle : J ≤ Cut` using `map_le_cutE A RP e j hrange hjL`.

Establish `hJFG : J.FG` using `fg_of_le_fg hCutFG hJle`. Establish `hRPFG : RP.L.FG` using `Submodule.fg_of_fg_map_injective (j.restrictScalars (𝓞 K)) hj hJFG`. Establish `hnK : ((n : ℕ) : K) ≠ 0` using `by exact_mod_cast hn0`. Use `set φ : A.V →ₗ[K] A.V := ((n : ℕ) : K) • LinearMap.id with hφ`. Establish `hφi : Function.Injective φ` using `fun a b h => by`.

Simplify `h` using `[hφ, smul_right_inj hnK]`. Use `set nC := Cut.map (φ.restrictScalars (𝓞 K)) with hnC`. Establish `hnle : nC ≤ J`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Take `⟨x, hx, hxe⟩` from `hn y hy`.

Conclude with `⟨x, hx, by simp [hφ, hxe]⟩`. Establish `hnC0 : nC ≠ ⊥` using `map_ne_bot φ hφi hcut`. Establish `hJ0 : J ≠ ⊥` using `fun h => hnC0 (eq_bot_iff.2 (h ▸ hnle))`. Establish `hRP0 : RP.L ≠ ⊥`. Introduce `h`.

Apply `hJ0` to reduce the goal to its premises. Rewrite using `[hJ, h, Submodule.map_bot]`. Establish `hrJ : Formalism.HN.rkK J = Formalism.HN.rkK RP.L` using `rkK_map j hj RP.L`. Establish `hrn : Formalism.HN.rkK nC = Formalism.HN.rkK Cut` using `rkK_map φ hφi Cut`. Establish `hr1` using `rkK_mono hnle`.

Establish `hr2` using `rkK_mono hJle`. Establish `hrJC : Formalism.HN.rkK J = Formalism.HN.rkK Cut` using `le_antisymm hr2 (hrn ▸ hr1)`. Establish `hnCFG : nC.FG` using `hCutFG.map _`. Establish `hc0 : 0 < c` using `lt_of_lt_of_le one_pos hc1`. Take `⟨sJ, sJm⟩` from `scale_map RP.b RP.X hRX A.b A.X hAX j hj c hc0 hcn RP.L hRPFG hRP0`.

Establish `hnn : ∀ v x, Formalism.HermitianLatticesTheory.normAt A.b A.X v (φ x) ^ 2 = ((n : ℝ) ^ 2) * Formalism.HermitianLatticesTheory.normAt A.b A.X v x ^ 2`. Introduce `v x`. Simplify using `only [hφ, LinearMap.smul_apply, LinearMap.id_apply]`. Rewrite using `[normAt_smul, mul_pow]`. Use `congr 1`.

Simplify using the standard rewrite rules. Establish `hn2 : (0 : ℝ) < (n : ℝ) ^ 2` using `by positivity`. Take `⟨sn, snm⟩` from `scale_map A.b A.X hAX A.b A.X hAX φ hφi _ hn2 hnn Cut hCutFG hcut`. Establish `hlogn : Real.log ((n : ℝ) ^ 2) = 2 * Real.log n` using `by rw [Real.log_pow]; push_cast; ring`. Rewrite `sn`, `snm` using `[hlogn]`.

Establish `m1` using `muMax_mono A.b A.X hAX hJle hJFG hCutFG hJ0`. Establish `m2` using `muMax_mono A.b A.X hAX hnle hnCFG hJFG hnC0`. Establish `m3` using `mu_mono A.b A.X hAX hJle hJFG hCutFG hJ0 hrJC.symm`. Establish `m4` using `mu_mono A.b A.X hAX hnle hnCFG hJFG hnC0 (hrJC.trans hrn.symm)`. Establish `hlc : 0 ≤ Real.log c` using `Real.log_nonneg hc1`.

Use `⟨hRPFG, hRP0, hrJ.symm.trans hrJC, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show Formalism.HN.muMaxDef RP.b RP.X RP.L ≤ _`. Combine the linear equalities and inequalities to obtain the conclusion. Use `show _ ≤ Formalism.HN.muMaxDef RP.b RP.X RP.L + _ - _`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `show _ ≤ Formalism.HN.muDef RP.b RP.X RP.L`. Combine the linear equalities and inequalities to obtain the conclusion. Use `show Formalism.HN.muDef RP.b RP.X RP.L ≤ _`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem level (A RP : HLat K) (hAX : ∀ v, IsUnit (A.X v).det) (hAL : A.L.FG)
    (hRX : ∀ v, IsUnit (RP.X v).det) (e : Module.End K A.V) (j : RP.V →ₗ[K] A.V)
    (hj : Function.Injective j) (hrange : LinearMap.range j = LinearMap.range e)
    (hjL : ∀ x ∈ RP.L, j x ∈ A.L) (n : ℕ) (hn0 : n ≠ 0)
    (hn : ∀ y ∈ cutE A e A.L, ∃ x ∈ RP.L, j x = ((n : ℕ) : K) • y)
    (c : ℝ) (hc1 : 1 ≤ c)
    (hcn : ∀ v x, Formalism.HermitianLatticesTheory.normAt A.b A.X v (j x) ^ 2 = c * Formalism.HermitianLatticesTheory.normAt RP.b RP.X v x ^ 2)
    (hcut : cutE A e A.L ≠ ⊥) :
    RP.L.FG ∧ RP.L ≠ ⊥ ∧ Formalism.HN.rkK RP.L = Formalism.HN.rkK (cutE A e A.L) ∧
    RP.muMax ≤ Formalism.HN.muMaxDef A.b A.X (cutE A e A.L) + Real.log c ∧
    Formalism.HN.muMaxDef A.b A.X (cutE A e A.L) ≤ RP.muMax + 2 * Real.log n - Real.log c ∧
    Formalism.HN.muDef A.b A.X (cutE A e A.L) - 2 * Real.log n + Real.log c ≤ RP.mu ∧
    RP.mu ≤ Formalism.HN.muDef A.b A.X (cutE A e A.L) + Real.log c := by
  have : FiniteDimensional K A.V := Module.Finite.of_basis A.b
  set Cut := cutE A e A.L with hCut
  have hCutFG : Cut.FG := fg_of_le_fg hAL inf_le_left
  set J := RP.L.map (j.restrictScalars (𝓞 K)) with hJ
  have hJle : J ≤ Cut := map_le_cutE A RP e j hrange hjL
  have hJFG : J.FG := fg_of_le_fg hCutFG hJle
  have hRPFG : RP.L.FG := Submodule.fg_of_fg_map_injective (j.restrictScalars (𝓞 K)) hj hJFG
  have hnK : ((n : ℕ) : K) ≠ 0 := by exact_mod_cast hn0
  set φ : A.V →ₗ[K] A.V := ((n : ℕ) : K) • LinearMap.id with hφ
  have hφi : Function.Injective φ := fun a b h => by
    simpa [hφ, smul_right_inj hnK] using h
  set nC := Cut.map (φ.restrictScalars (𝓞 K)) with hnC
  have hnle : nC ≤ J := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxe⟩ := hn y hy
    exact ⟨x, hx, by simp [hφ, hxe]⟩
  have hnC0 : nC ≠ ⊥ := map_ne_bot φ hφi hcut
  have hJ0 : J ≠ ⊥ := fun h => hnC0 (eq_bot_iff.2 (h ▸ hnle))
  have hRP0 : RP.L ≠ ⊥ := by
    intro h; apply hJ0; rw [hJ, h, Submodule.map_bot]
  have hrJ : Formalism.HN.rkK J = Formalism.HN.rkK RP.L := rkK_map j hj RP.L
  have hrn : Formalism.HN.rkK nC = Formalism.HN.rkK Cut := rkK_map φ hφi Cut
  have hr1 := rkK_mono hnle
  have hr2 := rkK_mono hJle
  have hrJC : Formalism.HN.rkK J = Formalism.HN.rkK Cut := le_antisymm hr2 (hrn ▸ hr1)
  have hnCFG : nC.FG := hCutFG.map _
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  obtain ⟨sJ, sJm⟩ := scale_map RP.b RP.X hRX A.b A.X hAX j hj c hc0 hcn RP.L hRPFG hRP0
  have hnn : ∀ v x, Formalism.HermitianLatticesTheory.normAt A.b A.X v (φ x) ^ 2 = ((n : ℝ) ^ 2) * Formalism.HermitianLatticesTheory.normAt A.b A.X v x ^ 2 := by
    intro v x
    simp only [hφ, LinearMap.smul_apply, LinearMap.id_apply]
    rw [normAt_smul, mul_pow]
    congr 1
    simp
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  obtain ⟨sn, snm⟩ := scale_map A.b A.X hAX A.b A.X hAX φ hφi _ hn2 hnn Cut hCutFG hcut
  have hlogn : Real.log ((n : ℝ) ^ 2) = 2 * Real.log n := by rw [Real.log_pow]; push_cast; ring
  rw [hlogn] at sn snm
  have m1 := muMax_mono A.b A.X hAX hJle hJFG hCutFG hJ0
  have m2 := muMax_mono A.b A.X hAX hnle hnCFG hJFG hnC0
  have m3 := mu_mono A.b A.X hAX hJle hJFG hCutFG hJ0 hrJC.symm
  have m4 := mu_mono A.b A.X hAX hnle hnCFG hJFG hnC0 (hrJC.trans hrn.symm)
  have hlc : 0 ≤ Real.log c := Real.log_nonneg hc1
  refine ⟨hRPFG, hRP0, hrJ.symm.trans hrJC, ?_, ?_, ?_, ?_⟩
  · show Formalism.HN.muMaxDef RP.b RP.X RP.L ≤ _; linarith
  · show _ ≤ Formalism.HN.muMaxDef RP.b RP.X RP.L + _ - _; linarith
  · show _ ≤ Formalism.HN.muDef RP.b RP.X RP.L; linarith
  · show Formalism.HN.muDef RP.b RP.X RP.L ≤ _; linarith

/- English proof (translation)
Establish `hnK : ((n : ℕ) : K) ≠ 0` using `by exact_mod_cast hn0`. Establish `h1 : LinearMap.range e ≤ (Submodule.span K (RP.L : Set RP.V)).map j`. Rewrite using `[← hspan, Submodule.span_le]`. Introduce `y hy`. Take `⟨x, hx, hxe⟩` from `hn y hy`.

Establish `: y = ((n : ℕ) : K)⁻¹ • j x` using `by rw [hxe, smul_smul, inv_mul_cancel₀ hnK, one_smul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ ⟨x, Submodule.subset_span hx, rfl⟩`. Rewrite `h1` using `[← hrange, LinearMap.range_eq_map]`. Conclude with `eq_top_iff.2 ((Submodule.map_le_map_iff_of_injective hj _ _).1 h1)`.
-/
theorem span_top (A RP : HLat K) (e : Module.End K A.V) (j : RP.V →ₗ[K] A.V)
    (hj : Function.Injective j) (hrange : LinearMap.range j = LinearMap.range e)
    (n : ℕ) (hn0 : n ≠ 0)
    (hn : ∀ y ∈ cutE A e A.L, ∃ x ∈ RP.L, j x = ((n : ℕ) : K) • y)
    (hspan : Submodule.span K (cutE A e A.L : Set A.V) = LinearMap.range e) :
    Submodule.span K (RP.L : Set RP.V) = ⊤ := by
  have hnK : ((n : ℕ) : K) ≠ 0 := by exact_mod_cast hn0
  have h1 : LinearMap.range e ≤ (Submodule.span K (RP.L : Set RP.V)).map j := by
    rw [← hspan, Submodule.span_le]
    intro y hy
    obtain ⟨x, hx, hxe⟩ := hn y hy
    have : y = ((n : ℕ) : K)⁻¹ • j x := by rw [hxe, smul_smul, inv_mul_cancel₀ hnK, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ ⟨x, Submodule.subset_span hx, rfl⟩
  rw [← hrange, LinearMap.range_eq_map] at h1
  exact eq_top_iff.2 ((Submodule.map_le_map_iff_of_injective hj _ _).1 h1)

/- English proof (translation)
Use `set e := ρ.asAlgebraHom (eps P) with he`. Establish `hHpos : 0 < Nat.card P.H` using `Nat.card_pos`. Establish `hm : ((Nat.card P.H : ℕ) : K) ≠ 0` using `by exact_mod_cast hHpos.ne'`. Establish `hu : ∀ (h : P.H) (y : A.V), y ∈ A.L → (((P.chi h)⁻¹ : Kˣ) : K) • y ∈ A.L`. Introduce `h y hy`.

Establish `h1 : ((P.chi h)⁻¹ : Kˣ) ^ Nat.card P.H = 1`. Rewrite using `[inv_pow, ← map_pow, pow_card_eq_one', map_one, inv_one]`. Establish `hpow : (((P.chi h)⁻¹ : Kˣ) : K) ^ Nat.card P.H = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, h1, Units.val_one]`. Establish `hui : IsIntegral ℤ (((P.chi h)⁻¹ : Kˣ) : K)` using `IsIntegral.of_pow hHpos (by rw [hpow]; exact isIntegral_one)`.

Take `⟨o, ho⟩` from `(IsIntegralClosure.isIntegral_iff (A := 𝓞 K)).1 hui`. Rewrite using `[← ho, algebraMap_smul]`. Conclude with `A.L.smul_mem o hy`. Establish `hint : ∀ x ∈ A.L, ((Nat.card P.H : ℕ) : K) • e x ∈ A.L`. Introduce `x hx`.

Rewrite using `[he, eps, map_smul, LinearMap.smul_apply, smul_smul, mul_inv_cancel₀ hm, one_smul, map_sum, LinearMap.sum_apply]`. Use `Submodule.sum_mem _ (fun g _ => ?_)` and prove the remaining obligations. Use `split`. Name the introduced variables `h`. Rewrite using `[map_smul, MonoidAlgebra.of_apply, Representation.asAlgebraHom_single, one_smul, LinearMap.smul_apply]`.

Conclude with `hu _ _ (hG.2.1 g x hx)`. Rewrite using `[map_zero, LinearMap.zero_apply]`. Conclude with `A.L.zero_mem`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`.

Introduce `y hy`. Conclude with `hy.2`. Introduce and unpack `_ ⟨w, rfl⟩`. Establish `hw : w ∈ Submodule.span K (A.L : Set A.V)` using `by rw [hG.1.2.2]; trivial`. Proceed by induction on `hw using Submodule.span_induction with`.

Consider the case `mem x hx`. Establish `hmem : ((Nat.card P.H : ℕ) : K) • e x ∈ cut A ρ (eps P) A.L` using `⟨hint x hx, ⟨((Nat.card P.H : ℕ) : K) • x, by rw [map_smul]⟩⟩`. Establish `: e x = ((Nat.card P.H : ℕ) : K)⁻¹ • (((Nat.card P.H : ℕ) : K) • e x)`. Rewrite using `[smul_smul, inv_mul_cancel₀ hm, one_smul]`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hmem)`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`.

Consider the case `smul a x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem span_cut {G : Type} [Group G] [Fintype G] (A : HLat K) (ρ : Representation K G A.V)
    (hG : IsGLat A ρ) (P : Pair K G) :
    Submodule.span K ((cut A ρ (eps P) A.L : Submodule (𝓞 K) A.V) : Set A.V) =
      LinearMap.range (ρ.asAlgebraHom (eps P)) := by
  set e := ρ.asAlgebraHom (eps P) with he
  have hHpos : 0 < Nat.card P.H := Nat.card_pos
  have hm : ((Nat.card P.H : ℕ) : K) ≠ 0 := by exact_mod_cast hHpos.ne'
  have hu : ∀ (h : P.H) (y : A.V), y ∈ A.L → (((P.chi h)⁻¹ : Kˣ) : K) • y ∈ A.L := by
    intro h y hy
    have h1 : ((P.chi h)⁻¹ : Kˣ) ^ Nat.card P.H = 1 := by
      rw [inv_pow, ← map_pow, pow_card_eq_one', map_one, inv_one]
    have hpow : (((P.chi h)⁻¹ : Kˣ) : K) ^ Nat.card P.H = 1 := by
      rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    have hui : IsIntegral ℤ (((P.chi h)⁻¹ : Kˣ) : K) :=
      IsIntegral.of_pow hHpos (by rw [hpow]; exact isIntegral_one)
    obtain ⟨o, ho⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 K)).1 hui
    rw [← ho, algebraMap_smul]
    exact A.L.smul_mem o hy
  have hint : ∀ x ∈ A.L, ((Nat.card P.H : ℕ) : K) • e x ∈ A.L := by
    intro x hx
    rw [he, eps, map_smul, LinearMap.smul_apply, smul_smul, mul_inv_cancel₀ hm, one_smul, map_sum,
      LinearMap.sum_apply]
    refine Submodule.sum_mem _ (fun g _ => ?_)
    split
    · rename_i h
      rw [map_smul, MonoidAlgebra.of_apply, Representation.asAlgebraHom_single, one_smul,
        LinearMap.smul_apply]
      exact hu _ _ (hG.2.1 g x hx)
    · rw [map_zero, LinearMap.zero_apply]; exact A.L.zero_mem
  apply le_antisymm
  · rw [Submodule.span_le]; intro y hy; exact hy.2
  · rintro _ ⟨w, rfl⟩
    have hw : w ∈ Submodule.span K (A.L : Set A.V) := by rw [hG.1.2.2]; trivial
    induction hw using Submodule.span_induction with
    | mem x hx =>
        have hmem : ((Nat.card P.H : ℕ) : K) • e x ∈ cut A ρ (eps P) A.L :=
          ⟨hint x hx, ⟨((Nat.card P.H : ℕ) : K) • x, by rw [map_smul]⟩⟩
        have : e x = ((Nat.card P.H : ℕ) : K)⁻¹ • (((Nat.card P.H : ℕ) : K) • e x) := by
          rw [smul_smul, inv_mul_cancel₀ hm, one_smul]
        rw [this]; exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Take `⟨hdF, hdS, -, hsz, -⟩` from `Formalism.HN.dualPl K A.V A.ι A.b A.X hX A.L hF hS`. Establish `hdX : ∀ v, IsUnit (Formalism.HN.dualFrame A.X v).det`. Introduce `v`. Unfold `Formalism.HN.dualFrame`. Conclude with `Matrix.isUnit_nonsing_inv_det _ (by rw [Matrix.det_transpose]; exact hX v)`.

Establish `hd0 : Formalism.HN.dualLat A.L ≠ ⊥`. Introduce `hb`. Take `⟨y, hy, hy0⟩` from `(Submodule.ne_bot_iff _).1 h0`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, A.b.repr y i ≠ 0 := by`. Assume the negation of the conclusion as `hc`.

Use `push Not at hc`. Conclude with `hy0 (A.b.repr.injective (by ext i; simp [hc i]))`. Establish `hmem : A.b.coord i ∈ Submodule.span K (Formalism.HN.dualLat A.L : Set (Module.Dual K A.V))`. Rewrite using `[hdS]`. Discharge the goal by the elementary cases of `trivial`.

Establish `hz : A.b.coord i = 0` using `by simpa [hb] using hmem`. Conclude with `hi (by simpa using congrArg (fun f => f y) hz)`. Take `⟨-, hmuD, -⟩` from `Formalism.HN.sizeMu K (Module.Dual K A.V) A.ι A.b.dualBasis (Formalism.HN.dualFrame A.X) hdX _ hdF hd0`. Take `⟨-, hmu, -⟩` from `Formalism.HN.sizeMu K A.V A.ι A.b A.X hX A.L hF h0`. Use `show Formalism.HN.muDef A.b.dualBasis (Formalism.HN.dualFrame A.X) (Formalism.HN.dualLat A.L) = - Formalism.HN.muDef A.b A.X A.L`.

Rewrite using `[hmuD, hmu, hsz, Real.log_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem muDual_eq (A : HLat K) (hX : ∀ v, IsUnit (A.X v).det) (hF : A.L.FG)
    (hS : Submodule.span K (A.L : Set A.V) = ⊤) (h0 : A.L ≠ ⊥) : A.muDual = - A.mu := by
  obtain ⟨hdF, hdS, -, hsz, -⟩ := Formalism.HN.dualPl K A.V A.ι A.b A.X hX A.L hF hS
  have hdX : ∀ v, IsUnit (Formalism.HN.dualFrame A.X v).det := by
    intro v
    unfold Formalism.HN.dualFrame
    exact Matrix.isUnit_nonsing_inv_det _ (by rw [Matrix.det_transpose]; exact hX v)
  have hd0 : Formalism.HN.dualLat A.L ≠ ⊥ := by
    intro hb
    obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 h0
    obtain ⟨i, hi⟩ : ∃ i, A.b.repr y i ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hy0 (A.b.repr.injective (by ext i; simp [hc i]))
    have hmem : A.b.coord i ∈ Submodule.span K (Formalism.HN.dualLat A.L : Set (Module.Dual K A.V)) := by
      rw [hdS]; trivial
    have hz : A.b.coord i = 0 := by simpa [hb] using hmem
    exact hi (by simpa using congrArg (fun f => f y) hz)
  obtain ⟨-, hmuD, -⟩ := Formalism.HN.sizeMu K (Module.Dual K A.V) A.ι A.b.dualBasis (Formalism.HN.dualFrame A.X) hdX _ hdF hd0
  obtain ⟨-, hmu, -⟩ := Formalism.HN.sizeMu K A.V A.ι A.b A.X hX A.L hF h0
  show Formalism.HN.muDef A.b.dualBasis (Formalism.HN.dualFrame A.X) (Formalism.HN.dualLat A.L) = - Formalism.HN.muDef A.b A.X A.L
  rw [hmuD, hmu, hsz, Real.log_inv]; ring

/- English proof (translation)
Unfold `cut`. Rewrite using `[map_mul, hb, mul_one]`.
-/
theorem cut_mul_one {G : Type} [Group G] (A : HLat K) (ρ : Representation K G A.V)
    (a b : MonoidAlgebra K G) (hb : ρ.asAlgebraHom b = 1) (M : Submodule (𝓞 K) A.V) :
    cut A ρ (a * b) M = cut A ρ a M := by
  unfold cut; rw [map_mul, hb, mul_one]

/- English proof (translation)
Unfold `cut cutE`. Rewrite using `[map_mul]`. Use `inf_le_inf_left _ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `⟨ρ.asAlgebraHom b y, rfl⟩`.
-/
theorem cut_mul_le {G : Type} [Group G] (A : HLat K) (ρ : Representation K G A.V)
    (a b : MonoidAlgebra K G) (M : Submodule (𝓞 K) A.V) :
    cut A ρ (a * b) M ≤ cut A ρ a M := by
  unfold cut cutE
  rw [map_mul]
  refine inf_le_inf_left _ ?_
  rintro _ ⟨y, rfl⟩
  exact ⟨ρ.asAlgebraHom b y, rfl⟩

end Level

section Reals

/- English proof (translation)
Use `set R := ∑ s, r s with hRdef`. Use `set U := ∑ s, (r s * H - d s) with hUdef`. Establish `hU : 0 ≤ U` using `Finset.sum_nonneg (fun s _ => by linarith [hd s])`. Establish `hNlo : ∀ s, nb * (1 - δ) ≤ N s` using `fun s => by`. Use `(abs_le.1 (hN s)).1` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Establish `hNhi : ∀ s, N s ≤ nb * (1 + δ)` using `fun s => by`. Use `(abs_le.1 (hN s)).2` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `h1δ : 0 < 1 - δ` using `by linarith`.

Establish `hN0 : ∀ s, 0 ≤ N s` using `fun s => le_trans (by positivity) (hNlo s)`. Establish `hNr : nb * (1 - δ) * R ≤ ∑ s, N s * r s`. Rewrite using `[hRdef, Finset.mul_sum]`. Conclude with `Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_right (hNlo s) (hr s))`. Establish `hNu : ∑ s, N s * (r s * H - d s) ≤ nb * (1 + δ) * U`.

Rewrite using `[hUdef, Finset.mul_sum]`. Conclude with `Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_right (hNhi s) (by linarith [hd s]))`. Establish `hNu0 : 0 ≤ ∑ s, N s * (r s * H - d s)` using `Finset.sum_nonneg (fun s _ => mul_nonneg (hN0 s) (by linarith [hd s]))`. Establish `hpos : 0 < nb * (1 - δ) * R` using `by positivity`. Establish `hD : 0 < ∑ s, N s * r s` using `lt_of_lt_of_le hpos hNr`.

Establish `hs1 : ∑ s, N s * (r s * H - d s) = H * ∑ s, N s * r s - ∑ s, N s * d s`. Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl (fun s _ => by ring)`. Establish `hs2 : U = H * R - ∑ s, d s`. Rewrite using `[hUdef, hRdef, Finset.mul_sum, ← Finset.sum_sub_distrib]`.

Conclude with `Finset.sum_congr rfl (fun s _ => by ring)`. Establish `hq : (∑ s, N s * (r s * H - d s)) / (∑ s, N s * r s) ≤ (1 + 3 * δ) * (U / R)`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_right _ (div_nonneg hU hR.le)` to reduce the goal to its premises. Rewrite using `[div_le_iff₀ h1δ]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hl : -(∑ s, N s * d s) / (∑ s, N s * r s) = (∑ s, N s * (r s * H - d s)) / (∑ s, N s * r s) - H`. Rewrite using `[hs1]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `hr' : U / R = H + -(∑ s, d s) / R` using `by rw [hs2]; field_simp; ring`. Rewrite using `[hl]`. Rewrite `hq` using `[hr']`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem key_ineq {S : Type} [Fintype S] (N r d : S → ℝ) (nb δ H : ℝ) (hnb : 0 < nb) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / 3) (hN : ∀ s, |N s - nb| ≤ δ * nb) (hr : ∀ s, 0 ≤ r s) (hd : ∀ s, d s ≤ r s * H)
    (hR : 0 < ∑ s, r s) :
    -(∑ s, N s * d s) / (∑ s, N s * r s) ≤
      -(∑ s, d s) / (∑ s, r s) + 3 * δ * (-(∑ s, d s) / (∑ s, r s) + H) := by
  set R := ∑ s, r s with hRdef
  set U := ∑ s, (r s * H - d s) with hUdef
  have hU : 0 ≤ U := Finset.sum_nonneg (fun s _ => by linarith [hd s])
  have hNlo : ∀ s, nb * (1 - δ) ≤ N s := fun s => by
    have := (abs_le.1 (hN s)).1; nlinarith
  have hNhi : ∀ s, N s ≤ nb * (1 + δ) := fun s => by
    have := (abs_le.1 (hN s)).2; nlinarith
  have h1δ : 0 < 1 - δ := by linarith
  have hN0 : ∀ s, 0 ≤ N s := fun s => le_trans (by positivity) (hNlo s)
  have hNr : nb * (1 - δ) * R ≤ ∑ s, N s * r s := by
    rw [hRdef, Finset.mul_sum]
    exact Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_right (hNlo s) (hr s))
  have hNu : ∑ s, N s * (r s * H - d s) ≤ nb * (1 + δ) * U := by
    rw [hUdef, Finset.mul_sum]
    exact Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_right (hNhi s) (by linarith [hd s]))
  have hNu0 : 0 ≤ ∑ s, N s * (r s * H - d s) :=
    Finset.sum_nonneg (fun s _ => mul_nonneg (hN0 s) (by linarith [hd s]))
  have hpos : 0 < nb * (1 - δ) * R := by positivity
  have hD : 0 < ∑ s, N s * r s := lt_of_lt_of_le hpos hNr
  have hs1 : ∑ s, N s * (r s * H - d s) = H * ∑ s, N s * r s - ∑ s, N s * d s := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun s _ => by ring)
  have hs2 : U = H * R - ∑ s, d s := by
    rw [hUdef, hRdef, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun s _ => by ring)
  have hq : (∑ s, N s * (r s * H - d s)) / (∑ s, N s * r s) ≤ (1 + 3 * δ) * (U / R) := by
    calc (∑ s, N s * (r s * H - d s)) / (∑ s, N s * r s) ≤ nb * (1 + δ) * U / (nb * (1 - δ) * R) :=
          div_le_div₀ (by positivity) hNu hpos hNr
      _ = (1 + δ) / (1 - δ) * (U / R) := by field_simp
      _ ≤ (1 + 3 * δ) * (U / R) := by
          apply mul_le_mul_of_nonneg_right _ (div_nonneg hU hR.le)
          rw [div_le_iff₀ h1δ]; nlinarith
  have hl : -(∑ s, N s * d s) / (∑ s, N s * r s) = (∑ s, N s * (r s * H - d s)) / (∑ s, N s * r s) - H := by
    rw [hs1]; field_simp; ring
  have hr' : U / R = H + -(∑ s, d s) / R := by rw [hs2]; field_simp; ring
  rw [hl]
  rw [hr'] at hq
  nlinarith

end Reals

section Zero

/- English proof (translation)
Establish `: ∀ k, NeZero (D.host.g k)` using `fun k => ⟨(D.host.g_prime k).ne_zero⟩`. Introduce `Y hY`. Unfold `Formalism.BasicNotions.lam0`. Rewrite using `[D.nd.restN_card_levelGroup_eq]`. Establish `hNpos : ∀ k, 0 < Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k)))` using `fun k => Nat.card_pos`.

Establish `hNle : ∀ k, Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) ≤ D.host.g k ^ (D.R.r * D.R.r)`. Introduce `k`. Establish `h1 : Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) ≤ Nat.card (Fin D.R.r → Fin D.R.r → ZMod (D.host.g k))` using `Nat.card_le_card_of_injective (fun u : GL (Fin D.R.r) (ZMod (D.host.g k)) => ((u : Matrix _ _ _) : Fin D.R.r → Fin D.R.r → ZMod (D.host.g k))) (fun a b h => Units.ext h)`. Establish `h2 : Nat.card (Fin D.R.r → Fin D.R.r → ZMod (D.host.g k)) = D.host.g k ^ (D.R.r * D.R.r)`. Rewrite using `[Nat.card_fun, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul]`.

Conclude with `h2 ▸ h1`. Establish `hg2 : ∀ k, (2 : ℝ) ≤ D.host.g k` using `fun k => by exact_mod_cast (D.host.g_prime k).two_le`. Establish `hk : ∀ k, Real.log (Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) : ℝ) ≤ (D.R.r : ℝ) ^ 2 * Real.log (2 * Y)`. Introduce `k`. Establish `hNr : (Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) : ℝ) ≤ (D.host.g k : ℝ) ^ (D.R.r * D.R.r)`.

Conclude with `hNle k` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation. Use `push_cast`. Rewrite using `[Real.log_prod (fun k _ => by have := hNpos k; positivity), Fin.sum_univ_two, Real.log_pow, Real.log_pow]`. Establish `hf : (0 : ℝ) ≤ D.R.f` using `Nat.cast_nonneg _`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left (hk 0) hf, mul_le_mul_of_nonneg_left (hk 1) hf]`.
-/
theorem scaled_lattice_nonzero_holds (D : D7) : Formalism.MainNotions.PrimeDegreeVariant.Conclusion0 D := by
  have : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  intro Y hY
  unfold Formalism.BasicNotions.lam0
  rw [D.nd.restN_card_levelGroup_eq]
  have hNpos : ∀ k, 0 < Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) := fun k => Nat.card_pos
  have hNle : ∀ k, Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) ≤ D.host.g k ^ (D.R.r * D.R.r) := by
    intro k
    have h1 : Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) ≤
        Nat.card (Fin D.R.r → Fin D.R.r → ZMod (D.host.g k)) :=
      Nat.card_le_card_of_injective (fun u : GL (Fin D.R.r) (ZMod (D.host.g k)) => ((u : Matrix _ _ _) :
        Fin D.R.r → Fin D.R.r → ZMod (D.host.g k))) (fun a b h => Units.ext h)
    have h2 : Nat.card (Fin D.R.r → Fin D.R.r → ZMod (D.host.g k)) = D.host.g k ^ (D.R.r * D.R.r) := by
      rw [Nat.card_fun, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul]
    exact h2 ▸ h1
  have hg2 : ∀ k, (2 : ℝ) ≤ D.host.g k := fun k => by exact_mod_cast (D.host.g_prime k).two_le
  have hk : ∀ k, Real.log (Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) : ℝ) ≤
      (D.R.r : ℝ) ^ 2 * Real.log (2 * Y) := by
    intro k
    have hNr : (Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) : ℝ) ≤ (D.host.g k : ℝ) ^ (D.R.r * D.R.r) := by
      exact_mod_cast hNle k
    calc Real.log (Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) : ℝ)
          ≤ Real.log ((D.host.g k : ℝ) ^ (D.R.r * D.R.r)) :=
          Real.log_le_log (by exact_mod_cast hNpos k) hNr
      _ = (D.R.r : ℝ) ^ 2 * Real.log (D.host.g k) := by rw [Real.log_pow]; push_cast; ring
      _ ≤ (D.R.r : ℝ) ^ 2 * Real.log (2 * Y) :=
          mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith [hg2 k]) (hY k)) (by positivity)
  push_cast
  rw [Real.log_prod (fun k _ => by have := hNpos k; positivity), Fin.sum_univ_two, Real.log_pow,
    Real.log_pow]
  have hf : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left (hk 0) hf, mul_le_mul_of_nonneg_left (hk 1) hf]

end Zero

section Main

attribute [local instance] Formalism.MainNotions.PrimeDegreeVariant.finiteLevelGroupFintype

variable {D : D7} {X : BaseLevelRowSide D}

/- English proof (translation)
Introduce `h0 h51 hTT h3 h4`. Unfold `Conclusion5 Formalism.BasicNotions.LemmaT`. Introduce `hδ HH0 hH`. Establish `hfrg : frg D = (D.R.f : ℝ) * D.R.r / (min (D.host.g 0) (D.host.g 1) : ℕ)` using `rfl`. Rewrite `hδ`, the goal using `[← hfrg]`.

Take `⟨hGL, -, heG, hL0, hLs⟩` from `h51`. Take `⟨lab, hlab, hgood⟩` from `hTT`. Establish `hAX : ∀ v, IsUnit (Y.RK.X v).det` using `hGL.1.1`. Establish `hAL : Y.RK.L.FG` using `hGL.1.2.1`. Establish `hM1 : M1 Y.T Y.P0` using `fun s => (h3 lab hlab s (hgood s)).1`.

Establish `hM1' : ∀ s, nS Y.T Y.P0 s = 1` using `hM1`. Establish `hNs : ∀ s, |(nS Y.T Y.Ps s : ℝ) - nbar D| ≤ C * frg D * nbar D` using `fun s => (h3 lab hlab s (hgood s)).2`. Take `⟨hrkS, hdegS, hmaxS⟩` from `h4 D.what₂.LL (G0g D.nd) Y.T Y.P0 Y.Ps hM1 Y.RK Y.rho hGL`. Take `⟨hrk0, hdeg0, -⟩` from `h4 D.what₂.LL (G0g D.nd) Y.T Y.P0 Y.P0 hM1 Y.RK Y.rho hGL`. Simplify using `only [cut_mul_one Y.RK Y.rho _ _ heG] at hrkS hdegS hmaxS hrk0 hdeg0`.

Establish `hcard1 : (1 : ℝ) ≤ Fintype.card (G0g D.nd)` using `by exact_mod_cast Fintype.card_pos`. Establish `hlam : laG (G0g D.nd) = lam0 D` using `by unfold laG Formalism.BasicNotions.lam0; rw [card_tie]`. Establish `hlam0 : 0 ≤ lam0 D` using `by rw [← hlam]; exact Real.log_nonneg hcard1`. Establish `hlogn : ∀ n : ℕ, n ∣ Fintype.card (G0g D.nd) → Real.log n ≤ lam0 D ∧ n ≠ 0`. Introduce `n hd`.

Establish `hn : 0 < n` using `Nat.pos_of_dvd_of_pos hd Fintype.card_pos`. Use `⟨?_, hn.ne'⟩` and prove the remaining obligations. Rewrite using `[← hlam]`. Unfold `laG`. Conclude with `Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast Nat.le_of_dvd Fintype.card_pos hd)`.

Establish `hlogc : ∀ c : ℝ, 1 ≤ c → c ≤ Fintype.card (G0g D.nd) → Real.log c ≤ lam0 D ∧ 0 ≤ Real.log c`. Introduce `c h1 h2`. Conclude with `⟨by rw [← hlam]; exact Real.log_le_log (by linarith) h2, Real.log_nonneg h1⟩`. Take `⟨hj0, hr0, hjL0, ⟨n0, hn0d, hn0⟩, ⟨c0, hc01, hc0c, hcn0⟩⟩` from `hL0`. Take `⟨hjs, hrs, hjLs, ⟨ns, hnsd, hns⟩, ⟨cs, hcs1, hcsc, hcns⟩⟩` from `hLs`.

Take `⟨hln0, hn00⟩` from `hlogn n0 hn0d`. Take `⟨hlns, hns0⟩` from `hlogn ns hnsd`. Take `⟨hlc0, hlc00⟩` from `hlogc c0 hc01 hc0c`. Take `⟨hlcs, hlcs0⟩` from `hlogc cs hcs1 hcsc`. Establish `ec0 : cut Y.RK Y.rho (eps Y.P0) Y.RK.L = cutE Y.RK (Y.rho.asAlgebraHom (eps Y.P0)) Y.RK.L` using `rfl`.

Establish `ecs : cut Y.RK Y.rho (eps Y.Ps) Y.RK.L = cutE Y.RK (Y.rho.asAlgebraHom (eps Y.Ps)) Y.RK.L` using `rfl`. Establish `hR0 : X.principalHermitianLattice.L ≠ ⊥` using `ne_bot_of_rkK_pos h0`. Establish `hcut0 : cutE Y.RK (Y.rho.asAlgebraHom (eps Y.P0)) Y.RK.L ≠ ⊥`. Introduce `hb`. Conclude with `map_ne_bot Y.j0 hj0 hR0 (eq_bot_iff.2 (hb ▸ map_le_cutE Y.RK X.principalHermitianLattice _ Y.j0 hr0 hjL0))`.

Take `⟨hF0, hne0, hrkeq0, a1, a2, a3, a4⟩` from `level Y.RK X.principalHermitianLattice hAX hAL X.s.RR_frames _ Y.j0 hj0 hr0 hjL0 n0 hn00 hn0 c0 hc01 hcn0 hcut0`. Establish `hrk0' : rkL Y.RK (cut Y.RK Y.rho (eps Y.P0) Y.RK.L) = ∑ s, rS Y.T Y.P0 Y.RK Y.rho s`. Rewrite using `[hrk0]`. Unfold `rkT`. Simplify using `only [hM1', one_mul]`.

Establish `hRn : 0 < ∑ s, rS Y.T Y.P0 Y.RK Y.rho s`. Rewrite using `[← hrk0']`. Use `show 0 < Formalism.HN.rkK _`. Rewrite using `[ec0, ← hrkeq0]`. Conclude with `h0`.

Establish `hR : (0 : ℝ) < ∑ s, (rS Y.T Y.P0 Y.RK Y.rho s : ℝ)` using `by exact_mod_cast hRn`. Take `⟨s0, -, hs0⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hRn.ne'`. Establish `hnb` using `nbar_pos D`. Establish `hδ0 : 0 ≤ C * frg D`. Assume the negation of the conclusion as `hneg`.

Use `push Not at hneg`. Use `hNs s0` as an intermediate fact. Establish `: C * frg D * nbar D < 0` using `mul_neg_of_neg_of_pos hneg hnb`. Combine the linear relations using `[abs_nonneg ((nS Y.T Y.Ps s0 : ℝ) - nbar D)]`. Establish `hNpos : ∀ s, 0 < nS Y.T Y.Ps s`.

Introduce `s`. Establish `h1` using `(abs_le.1 (hNs s)).1`. Establish `: (0 : ℝ) < nS Y.T Y.Ps s` using `by nlinarith`. Conclude with `this` after adjusting the coercions. Establish `hrkSpos : 0 < rkT Y.T Y.P0 Y.Ps Y.RK Y.rho`.

Unfold `rkT`. Conclude with `lt_of_lt_of_le (Nat.mul_pos (hNpos s0) (Nat.pos_of_ne_zero hs0)) (Finset.single_le_sum (f := fun s => nS Y.T Y.Ps s * rS Y.T Y.P0 Y.RK Y.rho s) (fun _ _ => Nat.zero_le _) (Finset.mem_univ s0))`. Establish `hcuts : cutE Y.RK (Y.rho.asAlgebraHom (eps Y.Ps)) Y.RK.L ≠ ⊥` using `ne_bot_of_rkK_pos (by rw [← ecs]; show 0 < rkL _ _; rw [hrkS]; exact hrkSpos)`. Take `⟨hFs, hnes, hrkeqs, b1, b2, b3, b4⟩` from `level Y.RK D.div.RR hAX hAL D.div_good.1 _ Y.js hjs hrs hjLs ns hns0 hns cs hcs1 hcns hcuts`. Establish `hS0` using `span_top Y.RK X.principalHermitianLattice _ Y.j0 hj0 hr0 n0 hn00 hn0 (span_cut Y.RK Y.rho hGL Y.P0)`.

Establish `hSs` using `span_top Y.RK D.div.RR _ Y.js hjs hrs ns hns0 hns (span_cut Y.RK Y.rho hGL Y.Ps)`. Establish `hD0 : X.principalHermitianLattice.muDual = - X.principalHermitianLattice.mu` using `muDual_eq X.principalHermitianLattice X.s.RR_frames hF0 hS0 hne0`. Establish `hDs : D.div.RR.muDual = - D.div.RR.mu` using `muDual_eq D.div.RR D.div_good.1 hFs hSs hnes`. Establish `hFG0 : (cut Y.RK Y.rho (eps Y.P0) Y.RK.L).FG` using `fg_of_le_fg hAL inf_le_left`. Establish `hd : ∀ s, degL Y.RK (cut Y.RK Y.rho (eps Y.P0 * eS Y.T s) Y.RK.L) ≤ (rS Y.T Y.P0 Y.RK Y.rho s : ℝ) * Formalism.HN.muMaxDef Y.RK.b Y.RK.X (cut Y.RK Y.rho (eps Y.P0) Y.RK.L)`.

Introduce `s`. Use `show (Formalism.HN.rkK (cut Y.RK Y.rho (eps Y.P0 * eS Y.T s) Y.RK.L) : ℝ) * Formalism.HN.muDef Y.RK.b Y.RK.X (cut Y.RK Y.rho (eps Y.P0 * eS Y.T s) Y.RK.L) ≤ (Formalism.HN.rkK (cut Y.RK Y.rho (eps Y.P0 * eS Y.T s) Y.RK.L) : ℝ) * Formalism.HN.muMaxDef Y.RK.b Y.RK.X (cut Y.RK Y.rho …`. Distinguish the cases in `hs : Formalism.HN.rkK (cut Y.RK Y.rho (eps Y.P0 * eS Y.T s) Y.RK.L) = 0`. Rewrite using `[hs]`. Simplify using the standard rewrite rules.

Establish `hle` using `cut_mul_le Y.RK Y.rho (eps Y.P0) (eS Y.T s) Y.RK.L`. Establish `hFGs` using `fg_of_le_fg hFG0 hle`. Establish `hne` using `ne_bot_of_rkK_pos (Nat.pos_of_ne_zero hs)`. Conclude with `mul_le_mul_of_nonneg_left ((mu_le_muMax Y.RK.b Y.RK.X hAX _ hFGs hne).trans (muMax_mono Y.RK.b Y.RK.X hAX hle hFGs hFG0 hne)) (Nat.cast_nonneg _)`. Establish `hrkr : ((rkT Y.T Y.P0 Y.Ps Y.RK Y.rho : ℕ) : ℝ) = ∑ s, (nS Y.T Y.Ps s : ℝ) * (rS Y.T Y.P0 Y.RK Y.rho s : ℝ)`.

Unfold `rkT`. Use `push_cast`. Both sides reduce to the same expression. Establish `hrkrpos : (0 : ℝ) < ∑ s, (nS Y.T Y.Ps s : ℝ) * (rS Y.T Y.P0 Y.RK Y.rho s : ℝ)`. Rewrite using `[← hrkr]`.

Conclude with `hrkSpos` after adjusting the coercions. Establish `hmuS : -(Formalism.HN.muDef Y.RK.b Y.RK.X (cut Y.RK Y.rho (eps Y.Ps) Y.RK.L)) ≤ -(∑ s, (nS Y.T Y.Ps s : ℝ) * degL Y.RK (cut Y.RK Y.rho (eps Y.P0 * eS Y.T s) Y.RK.L)) / (∑ s, (nS Y.T Y.Ps s : ℝ) * (rS Y.T Y.P0 Y.RK Y.rho s : ℝ)) + 10 * lam0 D`. Establish `h1` using `(abs_le.1 hdegS).1`. Rewrite `h1` using `[hlam, hrkr]`. Establish `h2 : degL Y.RK (cut Y.RK Y.rho (eps Y.Ps) Y.RK.L) = (∑ s, (nS Y.T Y.Ps s : ℝ) * (rS Y.T Y.P0 Y.RK Y.rho s : ℝ)) * Formalism.HN.muDef Y.RK.b Y.RK.X (cut Y.RK Y.rho (eps Y.Ps) Y.RK.L)`.

Rewrite using `[← hrkr, ← hrkS]`. Both sides reduce to the same expression. Establish `h3 : (∑ s, (nS Y.T Y.Ps s : ℝ) * degL Y.RK (cut Y.RK Y.rho (eps Y.P0 * eS Y.T s) Y.RK.L)) / (∑ s, (nS Y.T Y.Ps s : ℝ) * (rS Y.T Y.P0 Y.RK Y.rho s : ℝ)) ≤ Formalism.HN.muDef Y.RK.b Y.RK.X (cut Y.RK Y.rho (eps Y.Ps) Y.RK.L) + 10 * lam0 D`. Rewrite using `[div_le_iff₀ hrkrpos]`. Use the polynomial consequences of the given equalities and inequalities.

Rewrite using `[neg_div]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmu0 : -(∑ s, degL Y.RK (cut Y.RK Y.rho (eps Y.P0 * eS Y.T s) Y.RK.L)) / (∑ s, (rS Y.T Y.P0 Y.RK Y.rho s : ℝ)) ≤ -(Formalism.HN.muDef Y.RK.b Y.RK.X (cut Y.RK Y.rho (eps Y.P0) Y.RK.L)) + 10 * lam0 D`. Establish `h1` using `(abs_le.1 hdeg0).2`. Simplify using `only [hM1', Nat.cast_one, one_mul] at h1`.

Establish `hr : ((rkT Y.T Y.P0 Y.P0 Y.RK Y.rho : ℕ) : ℝ) = ∑ s, (rS Y.T Y.P0 Y.RK Y.rho s : ℝ)`. Unfold `rkT`. Simplify using `only [hM1', one_mul]`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite `h1` using `[hlam, hr]`. Establish `h2 : degL Y.RK (cut Y.RK Y.rho (eps Y.P0) Y.RK.L) = (∑ s, (rS Y.T Y.P0 Y.RK Y.rho s : ℝ)) * Formalism.HN.muDef Y.RK.b Y.RK.X (cut Y.RK Y.rho (eps Y.P0) Y.RK.L)`. Rewrite using `[← hr, ← hrk0]`. Both sides reduce to the same expression. Establish `h3 : Formalism.HN.muDef Y.RK.b Y.RK.X (cut Y.RK Y.rho (eps Y.P0) Y.RK.L) - 10 * lam0 D ≤ (∑ s, degL Y.RK (cut Y.RK Y.rho (eps Y.P0 * eS Y.T s) Y.RK.L)) / (∑ s, (rS Y.T Y.P0 Y.RK Y.rho s : ℝ))`.

Rewrite using `[le_div_iff₀ hR]`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[neg_div]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `key : -(∑ s, (nS Y.T Y.Ps s : ℝ) * degL Y.RK (cut Y.RK Y.rho (eps Y.P0 * eS Y.T s) Y.RK.L)) / (∑ s, (nS Y.T Y.Ps s : ℝ) * (rS Y.T Y.P0 Y.RK Y.rho s : ℝ)) ≤ -(∑ s, degL Y.RK (cut Y.RK Y.rho (eps Y.P0 * eS Y.T s) Y.RK.L)) / (∑ s, (rS Y.T Y.P0 Y.RK Y.rho s : ℝ)) + 3 * (C * frg D) * …` using `key_ineq (fun s => (nS Y.T Y.Ps s : ℝ)) (fun s => (rS Y.T Y.P0 Y.RK Y.rho s : ℝ)) (fun s => degL Y.RK (cut Y.RK Y.rho (eps Y.P0 * eS Y.T s) Y.RK.L)) (nbar D) (C * frg D) _ hnb hδ0 hδ hNs (fun s => Nat.cast_nonneg _) hd hR`.

Establish `hmx` using `hmaxS hrkSpos`. Express the relevant statement in the definitionally equal form `Formalism.HN.muMaxDef Y.RK.b Y.RK.X (cut Y.RK Y.rho (eps Y.Ps) Y.RK.L) ≤ Formalism.HN.muMaxDef Y.RK.b Y.RK.X (cut Y.RK Y.rho (eps Y.P0) Y.RK.L) + 10 * laG (G0g D.nd) at hmx`. Rewrite `hmx` using `[hlam]`. Rewrite `a1`, `a2`, `a3`, `a4` using `[← ec0]`. Rewrite `b1`, `b2`, `b3`, `b4` using `[← ecs]`.

Use `⟨by linarith, ?_⟩` and prove the remaining obligations. Establish `hxM : -(∑ s, degL Y.RK (cut Y.RK Y.rho (eps Y.P0 * eS Y.T s) Y.RK.L)) / (∑ s, (rS Y.T Y.P0 Y.RK Y.rho s : ℝ)) + Formalism.HN.muMaxDef Y.RK.b Y.RK.X (cut Y.RK Y.rho (eps Y.P0) Y.RK.L) ≤ X.principalHermitianLattice.muDual + HH0 + 13 * lam0 D` using `by linarith`. Establish `h3δ : (0 : ℝ) ≤ 3 * (C * frg D)` using `by linarith`. Establish `hmul` using `mul_le_mul_of_nonneg_left hxM h3δ`. Establish `hdl : 0 ≤ C * frg D * lam0 D` using `mul_nonneg hδ0 hlam0`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem scaled_lattice_bound_holds (Y : Prov D X) (C : ℝ) : GGFromIrreducibility Y C := by
  intro h0 h51 hTT h3 h4
  unfold Conclusion5 Formalism.BasicNotions.LemmaT
  intro hδ HH0 hH
  have hfrg : frg D = (D.R.f : ℝ) * D.R.r / (min (D.host.g 0) (D.host.g 1) : ℕ) := rfl
  rw [← hfrg] at hδ ⊢
  obtain ⟨hGL, -, heG, hL0, hLs⟩ := h51
  obtain ⟨lab, hlab, hgood⟩ := hTT
  have hAX : ∀ v, IsUnit (Y.RK.X v).det := hGL.1.1
  have hAL : Y.RK.L.FG := hGL.1.2.1
  have hM1 : M1 Y.T Y.P0 := fun s => (h3 lab hlab s (hgood s)).1
  have hM1' : ∀ s, nS Y.T Y.P0 s = 1 := hM1
  have hNs : ∀ s, |(nS Y.T Y.Ps s : ℝ) - nbar D| ≤ C * frg D * nbar D :=
    fun s => (h3 lab hlab s (hgood s)).2
  obtain ⟨hrkS, hdegS, hmaxS⟩ := h4 D.what₂.LL (G0g D.nd) Y.T Y.P0 Y.Ps hM1 Y.RK Y.rho hGL
  obtain ⟨hrk0, hdeg0, -⟩ := h4 D.what₂.LL (G0g D.nd) Y.T Y.P0 Y.P0 hM1 Y.RK Y.rho hGL
  simp only [cut_mul_one Y.RK Y.rho _ _ heG] at hrkS hdegS hmaxS hrk0 hdeg0

  have hcard1 : (1 : ℝ) ≤ Fintype.card (G0g D.nd) := by exact_mod_cast Fintype.card_pos
  have hlam : laG (G0g D.nd) = lam0 D := by unfold laG Formalism.BasicNotions.lam0; rw [card_tie]
  have hlam0 : 0 ≤ lam0 D := by rw [← hlam]; exact Real.log_nonneg hcard1
  have hlogn : ∀ n : ℕ, n ∣ Fintype.card (G0g D.nd) → Real.log n ≤ lam0 D ∧ n ≠ 0 := by
    intro n hd
    have hn : 0 < n := Nat.pos_of_dvd_of_pos hd Fintype.card_pos
    refine ⟨?_, hn.ne'⟩
    rw [← hlam]; unfold laG
    exact Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast Nat.le_of_dvd Fintype.card_pos hd)
  have hlogc : ∀ c : ℝ, 1 ≤ c → c ≤ Fintype.card (G0g D.nd) → Real.log c ≤ lam0 D ∧ 0 ≤ Real.log c := by
    intro c h1 h2
    exact ⟨by rw [← hlam]; exact Real.log_le_log (by linarith) h2, Real.log_nonneg h1⟩

  obtain ⟨hj0, hr0, hjL0, ⟨n0, hn0d, hn0⟩, ⟨c0, hc01, hc0c, hcn0⟩⟩ := hL0
  obtain ⟨hjs, hrs, hjLs, ⟨ns, hnsd, hns⟩, ⟨cs, hcs1, hcsc, hcns⟩⟩ := hLs
  obtain ⟨hln0, hn00⟩ := hlogn n0 hn0d
  obtain ⟨hlns, hns0⟩ := hlogn ns hnsd
  obtain ⟨hlc0, hlc00⟩ := hlogc c0 hc01 hc0c
  obtain ⟨hlcs, hlcs0⟩ := hlogc cs hcs1 hcsc
  have ec0 : cut Y.RK Y.rho (eps Y.P0) Y.RK.L = cutE Y.RK (Y.rho.asAlgebraHom (eps Y.P0)) Y.RK.L := rfl
  have ecs : cut Y.RK Y.rho (eps Y.Ps) Y.RK.L = cutE Y.RK (Y.rho.asAlgebraHom (eps Y.Ps)) Y.RK.L := rfl
  have hR0 : X.principalHermitianLattice.L ≠ ⊥ := ne_bot_of_rkK_pos h0
  have hcut0 : cutE Y.RK (Y.rho.asAlgebraHom (eps Y.P0)) Y.RK.L ≠ ⊥ := by
    intro hb
    exact map_ne_bot Y.j0 hj0 hR0 (eq_bot_iff.2 (hb ▸ map_le_cutE Y.RK X.principalHermitianLattice _ Y.j0 hr0 hjL0))
  obtain ⟨hF0, hne0, hrkeq0, a1, a2, a3, a4⟩ :=
    level Y.RK X.principalHermitianLattice hAX hAL X.s.RR_frames _ Y.j0 hj0 hr0 hjL0 n0 hn00 hn0 c0 hc01 hcn0 hcut0

  have hrk0' : rkL Y.RK (cut Y.RK Y.rho (eps Y.P0) Y.RK.L) = ∑ s, rS Y.T Y.P0 Y.RK Y.rho s := by
    rw [hrk0]; unfold rkT; simp only [hM1', one_mul]
  have hRn : 0 < ∑ s, rS Y.T Y.P0 Y.RK Y.rho s := by
    rw [← hrk0']; show 0 < Formalism.HN.rkK _; rw [ec0, ← hrkeq0]; exact h0
  have hR : (0 : ℝ) < ∑ s, (rS Y.T Y.P0 Y.RK Y.rho s : ℝ) := by exact_mod_cast hRn
  obtain ⟨s0, -, hs0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hRn.ne'
  have hnb := nbar_pos D
  have hδ0 : 0 ≤ C * frg D := by
    by_contra hneg
    push Not at hneg
    have := hNs s0
    have : C * frg D * nbar D < 0 := mul_neg_of_neg_of_pos hneg hnb
    linarith [abs_nonneg ((nS Y.T Y.Ps s0 : ℝ) - nbar D)]
  have hNpos : ∀ s, 0 < nS Y.T Y.Ps s := by
    intro s
    have h1 := (abs_le.1 (hNs s)).1
    have : (0 : ℝ) < nS Y.T Y.Ps s := by nlinarith
    exact_mod_cast this
  have hrkSpos : 0 < rkT Y.T Y.P0 Y.Ps Y.RK Y.rho := by
    unfold rkT
    exact lt_of_lt_of_le (Nat.mul_pos (hNpos s0) (Nat.pos_of_ne_zero hs0))
      (Finset.single_le_sum (f := fun s => nS Y.T Y.Ps s * rS Y.T Y.P0 Y.RK Y.rho s)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ s0))
  have hcuts : cutE Y.RK (Y.rho.asAlgebraHom (eps Y.Ps)) Y.RK.L ≠ ⊥ :=
    ne_bot_of_rkK_pos (by rw [← ecs]; show 0 < rkL _ _; rw [hrkS]; exact hrkSpos)
  obtain ⟨hFs, hnes, hrkeqs, b1, b2, b3, b4⟩ :=
    level Y.RK D.div.RR hAX hAL D.div_good.1 _ Y.js hjs hrs hjLs ns hns0 hns cs hcs1 hcns hcuts

  have hS0 := span_top Y.RK X.principalHermitianLattice _ Y.j0 hj0 hr0 n0 hn00 hn0 (span_cut Y.RK Y.rho hGL Y.P0)
  have hSs := span_top Y.RK D.div.RR _ Y.js hjs hrs ns hns0 hns (span_cut Y.RK Y.rho hGL Y.Ps)
  have hD0 : X.principalHermitianLattice.muDual = - X.principalHermitianLattice.mu := muDual_eq X.principalHermitianLattice X.s.RR_frames hF0 hS0 hne0
  have hDs : D.div.RR.muDual = - D.div.RR.mu := muDual_eq D.div.RR D.div_good.1 hFs hSs hnes

  have hFG0 : (cut Y.RK Y.rho (eps Y.P0) Y.RK.L).FG := fg_of_le_fg hAL inf_le_left
  have hd : ∀ s, degL Y.RK (cut Y.RK Y.rho (eps Y.P0 * eS Y.T s) Y.RK.L) ≤
      (rS Y.T Y.P0 Y.RK Y.rho s : ℝ) * Formalism.HN.muMaxDef Y.RK.b Y.RK.X (cut Y.RK Y.rho (eps Y.P0) Y.RK.L) := by
    intro s
    show (Formalism.HN.rkK (cut Y.RK Y.rho (eps Y.P0 * eS Y.T s) Y.RK.L) : ℝ) *
        Formalism.HN.muDef Y.RK.b Y.RK.X (cut Y.RK Y.rho (eps Y.P0 * eS Y.T s) Y.RK.L) ≤
      (Formalism.HN.rkK (cut Y.RK Y.rho (eps Y.P0 * eS Y.T s) Y.RK.L) : ℝ) *
        Formalism.HN.muMaxDef Y.RK.b Y.RK.X (cut Y.RK Y.rho (eps Y.P0) Y.RK.L)
    by_cases hs : Formalism.HN.rkK (cut Y.RK Y.rho (eps Y.P0 * eS Y.T s) Y.RK.L) = 0
    · rw [hs]; simp
    · have hle := cut_mul_le Y.RK Y.rho (eps Y.P0) (eS Y.T s) Y.RK.L
      have hFGs := fg_of_le_fg hFG0 hle
      have hne := ne_bot_of_rkK_pos (Nat.pos_of_ne_zero hs)
      exact mul_le_mul_of_nonneg_left ((mu_le_muMax Y.RK.b Y.RK.X hAX _ hFGs hne).trans
        (muMax_mono Y.RK.b Y.RK.X hAX hle hFGs hFG0 hne)) (Nat.cast_nonneg _)

  have hrkr : ((rkT Y.T Y.P0 Y.Ps Y.RK Y.rho : ℕ) : ℝ) =
      ∑ s, (nS Y.T Y.Ps s : ℝ) * (rS Y.T Y.P0 Y.RK Y.rho s : ℝ) := by
    unfold rkT; push_cast; rfl
  have hrkrpos : (0 : ℝ) < ∑ s, (nS Y.T Y.Ps s : ℝ) * (rS Y.T Y.P0 Y.RK Y.rho s : ℝ) := by
    rw [← hrkr]; exact_mod_cast hrkSpos
  have hmuS : -(Formalism.HN.muDef Y.RK.b Y.RK.X (cut Y.RK Y.rho (eps Y.Ps) Y.RK.L)) ≤
      -(∑ s, (nS Y.T Y.Ps s : ℝ) * degL Y.RK (cut Y.RK Y.rho (eps Y.P0 * eS Y.T s) Y.RK.L)) /
        (∑ s, (nS Y.T Y.Ps s : ℝ) * (rS Y.T Y.P0 Y.RK Y.rho s : ℝ)) + 10 * lam0 D := by
    have h1 := (abs_le.1 hdegS).1
    rw [hlam, hrkr] at h1
    have h2 : degL Y.RK (cut Y.RK Y.rho (eps Y.Ps) Y.RK.L) =
        (∑ s, (nS Y.T Y.Ps s : ℝ) * (rS Y.T Y.P0 Y.RK Y.rho s : ℝ)) *
          Formalism.HN.muDef Y.RK.b Y.RK.X (cut Y.RK Y.rho (eps Y.Ps) Y.RK.L) := by
      rw [← hrkr, ← hrkS]; rfl
    have h3 : (∑ s, (nS Y.T Y.Ps s : ℝ) * degL Y.RK (cut Y.RK Y.rho (eps Y.P0 * eS Y.T s) Y.RK.L)) /
        (∑ s, (nS Y.T Y.Ps s : ℝ) * (rS Y.T Y.P0 Y.RK Y.rho s : ℝ)) ≤
        Formalism.HN.muDef Y.RK.b Y.RK.X (cut Y.RK Y.rho (eps Y.Ps) Y.RK.L) + 10 * lam0 D := by
      rw [div_le_iff₀ hrkrpos]; nlinarith
    rw [neg_div]; linarith

  have hmu0 : -(∑ s, degL Y.RK (cut Y.RK Y.rho (eps Y.P0 * eS Y.T s) Y.RK.L)) /
      (∑ s, (rS Y.T Y.P0 Y.RK Y.rho s : ℝ)) ≤
      -(Formalism.HN.muDef Y.RK.b Y.RK.X (cut Y.RK Y.rho (eps Y.P0) Y.RK.L)) + 10 * lam0 D := by
    have h1 := (abs_le.1 hdeg0).2
    simp only [hM1', Nat.cast_one, one_mul] at h1
    have hr : ((rkT Y.T Y.P0 Y.P0 Y.RK Y.rho : ℕ) : ℝ) = ∑ s, (rS Y.T Y.P0 Y.RK Y.rho s : ℝ) := by
      unfold rkT; simp only [hM1', one_mul]; push_cast; rfl
    rw [hlam, hr] at h1
    have h2 : degL Y.RK (cut Y.RK Y.rho (eps Y.P0) Y.RK.L) =
        (∑ s, (rS Y.T Y.P0 Y.RK Y.rho s : ℝ)) * Formalism.HN.muDef Y.RK.b Y.RK.X (cut Y.RK Y.rho (eps Y.P0) Y.RK.L) := by
      rw [← hr, ← hrk0]; rfl
    have h3 : Formalism.HN.muDef Y.RK.b Y.RK.X (cut Y.RK Y.rho (eps Y.P0) Y.RK.L) - 10 * lam0 D ≤
        (∑ s, degL Y.RK (cut Y.RK Y.rho (eps Y.P0 * eS Y.T s) Y.RK.L)) / (∑ s, (rS Y.T Y.P0 Y.RK Y.rho s : ℝ)) := by
      rw [le_div_iff₀ hR]; nlinarith
    rw [neg_div]; linarith
  have key : -(∑ s, (nS Y.T Y.Ps s : ℝ) * degL Y.RK (cut Y.RK Y.rho (eps Y.P0 * eS Y.T s) Y.RK.L)) /
      (∑ s, (nS Y.T Y.Ps s : ℝ) * (rS Y.T Y.P0 Y.RK Y.rho s : ℝ)) ≤
      -(∑ s, degL Y.RK (cut Y.RK Y.rho (eps Y.P0 * eS Y.T s) Y.RK.L)) / (∑ s, (rS Y.T Y.P0 Y.RK Y.rho s : ℝ)) +
      3 * (C * frg D) * (-(∑ s, degL Y.RK (cut Y.RK Y.rho (eps Y.P0 * eS Y.T s) Y.RK.L)) /
        (∑ s, (rS Y.T Y.P0 Y.RK Y.rho s : ℝ)) +
        Formalism.HN.muMaxDef Y.RK.b Y.RK.X (cut Y.RK Y.rho (eps Y.P0) Y.RK.L)) :=
    key_ineq (fun s => (nS Y.T Y.Ps s : ℝ)) (fun s => (rS Y.T Y.P0 Y.RK Y.rho s : ℝ))
      (fun s => degL Y.RK (cut Y.RK Y.rho (eps Y.P0 * eS Y.T s) Y.RK.L)) (nbar D) (C * frg D) _ hnb hδ0 hδ
      hNs (fun s => Nat.cast_nonneg _) hd hR
  have hmx := hmaxS hrkSpos
  change Formalism.HN.muMaxDef Y.RK.b Y.RK.X (cut Y.RK Y.rho (eps Y.Ps) Y.RK.L) ≤
    Formalism.HN.muMaxDef Y.RK.b Y.RK.X (cut Y.RK Y.rho (eps Y.P0) Y.RK.L) + 10 * laG (G0g D.nd) at hmx
  rw [hlam] at hmx
  rw [← ec0] at a1 a2 a3 a4
  rw [← ecs] at b1 b2 b3 b4
  refine ⟨by linarith, ?_⟩
  have hxM : -(∑ s, degL Y.RK (cut Y.RK Y.rho (eps Y.P0 * eS Y.T s) Y.RK.L)) /
        (∑ s, (rS Y.T Y.P0 Y.RK Y.rho s : ℝ)) +
        Formalism.HN.muMaxDef Y.RK.b Y.RK.X (cut Y.RK Y.rho (eps Y.P0) Y.RK.L) ≤
      X.principalHermitianLattice.muDual + HH0 + 13 * lam0 D := by linarith
  have h3δ : (0 : ℝ) ≤ 3 * (C * frg D) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hxM h3δ
  have hdl : 0 ≤ C * frg D * lam0 D := mul_nonneg hδ0 hlam0
  linarith

end Main

end Formalism.MainNotions.DIV.Proofs.ScaledLatticeNorms

namespace Formalism.MainNotions.DIV.Proofs

open Formalism.MainNotions

/- English proof (translation)
The claim follows from `PrimeDegreeVariant.stmtAtB_ofC Fm YF Formalism.MainNotions.DIV.closed_part_statement_holds (fun x i => ScaledLatticeNorms.scaled_lattice_nonzero_holds (Fm.D x i)) (fun x hx i C => ScaledLatticeNorms.scaled_lattice_bound_holds (YF x hx i) C)`.
-/
theorem family_statement_of_scaled_lemmas {ε : ℝ} (Fm : FamP ε) (YF : PrimeDegreeVariant.ProvF Fm) : PrimeDegreeVariant.FamilyPartBImplication Fm YF :=
  PrimeDegreeVariant.stmtAtB_ofC Fm YF Formalism.MainNotions.DIV.closed_part_statement_holds
    (fun x i => ScaledLatticeNorms.scaled_lattice_nonzero_holds (Fm.D x i))
    (fun x hx i C => ScaledLatticeNorms.scaled_lattice_bound_holds (YF x hx i) C)

end Formalism.MainNotions.DIV.Proofs
