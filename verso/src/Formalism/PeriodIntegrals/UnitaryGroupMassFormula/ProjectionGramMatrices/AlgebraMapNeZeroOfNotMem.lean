import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.PeriodIntegrals.IdxCalc
import Formalism.HermitianLattices.HermitianLatticesProofs.IndexBasic

noncomputable section

namespace PI.Dv.ProjGramW

open NumberField IsDedekindDomain Formalism.BasicNotions

def IdxDet : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (w : HeightOneSpectrum (𝓞 K)) (d : ℕ) (b : Fin d → V),
    LinearIndependent K b → ∀ C : Matrix (Fin d) (Fin d) K, C.det ≠ 0 →
    idxAt w (Submodule.span (𝓞 K) (Set.range b))
      (Submodule.span (𝓞 K) (Set.range fun j => ∑ i, C i j • b i)) = vAdd w C.det

section Gen

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Unfold `PI.Dv.idxAt`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma idxAt_antisymm (w : HeightOneSpectrum (𝓞 K)) (M N : Submodule (𝓞 K) V) :
    idxAt w M N = - idxAt w N M := by
  unfold PI.Dv.idxAt
  ring

/- English proof (translation)
Unfold `PI.Dv.LocLe`. Simplify using `only [pow_zero, Ideal.one_eq_top, Submodule.top_smul]`.
-/
lemma locLe_zero_iff (w : HeightOneSpectrum (𝓞 K)) (X Y : Submodule (𝓞 K) V) :
    LocLe w 0 X Y ↔ ∀ x ∈ X, ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ Y := by
  unfold PI.Dv.LocLe
  simp only [pow_zero, Ideal.one_eq_top, Submodule.top_smul]

/- English proof (translation)
Introduce `h0`. Apply `hs` to reduce the goal to its premises. Establish `: s = 0` using `(IsFractionRing.injective (𝓞 K) K) (h0.trans (map_zero _).symm)`. Rewrite using `[this]`. Conclude with `w.asIdeal.zero_mem`.
-/
lemma algebraMap_ne_zero_of_not_mem (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K} (hs : s ∉ w.asIdeal) :
    algebraMap (𝓞 K) K s ≠ 0 := by
  intro h0
  apply hs
  have : s = 0 := (IsFractionRing.injective (𝓞 K) K) (h0.trans (map_zero _).symm)
  rw [this]
  exact w.asIdeal.zero_mem

/- English proof (translation)
Rewrite using `[Submodule.span_le]`. Introduce `x hx`. Take `⟨s, hs, hsx⟩` from `(locLe_zero_iff w X Y).mp h x hx`. Establish `hs0` using `algebraMap_ne_zero_of_not_mem w hs`. Establish `h1 : (algebraMap (𝓞 K) K s) • x ∈ Submodule.span K (Y : Set V)`.

Rewrite using `[algebraMap_smul]`. Conclude with `Submodule.subset_span hsx`. Establish `h2` using `Submodule.smul_mem (Submodule.span K (Y : Set V)) (algebraMap (𝓞 K) K s)⁻¹ h1`. Rewrite `h2` using `[smul_smul, inv_mul_cancel₀ hs0, one_smul]`. Then use the resulting hypothesis.
-/
lemma span_le_of_locLe (w : HeightOneSpectrum (𝓞 K)) {X Y : Submodule (𝓞 K) V} (h : LocLe w 0 X Y) :
    Submodule.span K (X : Set V) ≤ Submodule.span K (Y : Set V) := by
  rw [Submodule.span_le]
  intro x hx
  obtain ⟨s, hs, hsx⟩ := (locLe_zero_iff w X Y).mp h x hx
  have hs0 := algebraMap_ne_zero_of_not_mem w hs
  have h1 : (algebraMap (𝓞 K) K s) • x ∈ Submodule.span K (Y : Set V) := by
    rw [algebraMap_smul]
    exact Submodule.subset_span hsx
  have h2 := Submodule.smul_mem (Submodule.span K (Y : Set V)) (algebraMap (𝓞 K) K s)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hs0, one_smul] at h2

/- English proof (translation)
Establish `hs : Submodule.span K (X : Set V) = Submodule.span K (Y : Set V)` using `le_antisymm (span_le_of_locLe w hXY) (span_le_of_locLe w hYX)`. Establish `h1` using `(hI K V w Y X hY hX hs.symm).2.2.2.1 0 hXY`. Establish `h2` using `(hI K V w X Y hX hY hs).2.2.2.1 0 hYX`. Establish `h3` using `idxAt_antisymm w Y X`. Simplify using `only [Nat.cast_zero, zero_mul] at h1 h2`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma idx_eq_zero_of_loc (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {X Y : Submodule (𝓞 K) V}
    (hX : X.FG) (hY : Y.FG) (hXY : LocLe w 0 X Y) (hYX : LocLe w 0 Y X) : idxAt w X Y = 0 := by
  have hs : Submodule.span K (X : Set V) = Submodule.span K (Y : Set V) :=
    le_antisymm (span_le_of_locLe w hXY) (span_le_of_locLe w hYX)
  have h1 := (hI K V w Y X hY hX hs.symm).2.2.2.1 0 hXY
  have h2 := (hI K V w X Y hX hY hs).2.2.2.1 0 hYX
  have h3 := idxAt_antisymm w Y X
  simp only [Nat.cast_zero, zero_mul] at h1 h2
  linarith

/- English proof (translation)
Establish `h1` using `(hI K V w Y X hY hX hs.symm).2.2.2.1 0 hXY`. Establish `h3` using `idxAt_antisymm w Y X`. Simplify using `only [Nat.cast_zero, zero_mul] at h1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma idx_nonpos_of_loc (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {X Y : Submodule (𝓞 K) V}
    (hX : X.FG) (hY : Y.FG) (hs : Submodule.span K (X : Set V) = Submodule.span K (Y : Set V))
    (hXY : LocLe w 0 X Y) : idxAt w X Y ≤ 0 := by
  have h1 := (hI K V w Y X hY hX hs.symm).2.2.2.1 0 hXY
  have h3 := idxAt_antisymm w Y X
  simp only [Nat.cast_zero, zero_mul] at h1
  linarith

/- English proof (translation)
Simplify using `[Formalism.BasicNotions.vAdd]`.
-/
lemma vAdd_zero' (w : HeightOneSpectrum (𝓞 K)) : vAdd w (0 : K) = 0 := by
  simp [Formalism.BasicNotions.vAdd]

/- English proof (translation)
Unfold `Formalism.BasicNotions.vAdd`. Establish `h1 : w.valuation K (algebraMap (𝓞 K) K r) ≤ 1` using `w.valuation_le_one r`. Distinguish the cases in `h0 : w.valuation K (algebraMap (𝓞 K) K r) = 0`. Rewrite using `[h0, WithZero.log_zero]`. Simplify using the standard rewrite rules.

Establish `h2 : WithZero.exp (WithZero.log (w.valuation K (algebraMap (𝓞 K) K r))) ≤ WithZero.exp 0`. Rewrite using `[WithZero.exp_log h0, WithZero.exp_zero]`. Conclude with `h1`. Rewrite `h2` using `[WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
lemma vAdd_algebraMap_nonneg (w : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) :
    0 ≤ vAdd w (algebraMap (𝓞 K) K r) := by
  unfold Formalism.BasicNotions.vAdd
  have h1 : w.valuation K (algebraMap (𝓞 K) K r) ≤ 1 := w.valuation_le_one r
  by_cases h0 : w.valuation K (algebraMap (𝓞 K) K r) = 0
  · rw [h0, WithZero.log_zero]
    simp
  · have h2 : WithZero.exp (WithZero.log (w.valuation K (algebraMap (𝓞 K) K r))) ≤ WithZero.exp 0 := by
      rw [WithZero.exp_log h0, WithZero.exp_zero]
      exact h1
    rw [WithZero.exp_le_exp] at h2
    omega

/- English proof (translation)
Use `vAdd_algebraMap_nonneg w (n : 𝓞 K)` as an intermediate fact. Simplify using `using this`.
-/
lemma vAdd_natCast_nonneg (w : HeightOneSpectrum (𝓞 K)) (n : ℕ) : 0 ≤ vAdd w ((n : ℕ) : K) := by
  have := vAdd_algebraMap_nonneg w (n : 𝓞 K)
  simpa using this

/- English proof (translation)
Unfold `Formalism.BasicNotions.vAdd`. Establish `hne : w.valuation K (algebraMap (𝓞 K) K s) ≠ 0`. Rewrite using `[Valuation.ne_zero_iff]`. Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hs0`. Establish `hle : w.valuation K (algebraMap (𝓞 K) K s) ≤ 1` using `w.valuation_le_one s`.

Rewrite using `[neg_eq_zero, ← (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) w s).not, not_lt]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[← WithZero.exp_log hne, h, WithZero.exp_zero]`. Introduce `h`.

Rewrite using `[le_antisymm hle h, WithZero.log_one]`.
-/
lemma vAdd_eq_zero_iff (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K} (hs0 : s ≠ 0) :
    vAdd w (algebraMap (𝓞 K) K s) = 0 ↔ s ∉ w.asIdeal := by
  unfold Formalism.BasicNotions.vAdd
  have hne : w.valuation K (algebraMap (𝓞 K) K s) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hs0
  have hle : w.valuation K (algebraMap (𝓞 K) K s) ≤ 1 := w.valuation_le_one s
  rw [neg_eq_zero, ← (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) w s).not, not_lt]
  constructor
  · intro h
    rw [← WithZero.exp_log hne, h, WithZero.exp_zero]
  · intro h
    rw [le_antisymm hle h, WithZero.log_one]

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Establish `h1 : ∑ i, (∑ j, C i j * g j) • b i = 0`. Rewrite using `[← hg]`. Simplify using `only [Finset.smul_sum, smul_smul, Finset.sum_smul]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Establish `h2` using `(Fintype.linearIndependent_iff.mp hb) _ h1`. Establish `h3 : Matrix.mulVec C g = 0`.

Use function extensionality and compare the values at `i`. Simplify `h2 i` using `[Matrix.mulVec, dotProduct]`. Establish `h4` using `Matrix.eq_zero_of_mulVec_eq_zero hC h3`. Introduce `j`. Simplify using `using congrFun h4 j`.
-/
lemma linIndep_mat {d : ℕ} {b : Fin d → V} (hb : LinearIndependent K b) (C : Matrix (Fin d) (Fin d) K)
    (hC : C.det ≠ 0) : LinearIndependent K (fun j => ∑ i, C i j • b i) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h1 : ∑ i, (∑ j, C i j * g j) • b i = 0 := by
    rw [← hg]
    simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
  have h2 := (Fintype.linearIndependent_iff.mp hb) _ h1
  have h3 : Matrix.mulVec C g = 0 := by
    funext i
    simpa [Matrix.mulVec, dotProduct] using h2 i
  have h4 := Matrix.eq_zero_of_mulVec_eq_zero hC h3
  intro j
  simpa using congrFun h4 j

end Gen

section Herm

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Set `G : Matrix A.ι A.ι K` to `fun i j => h (A.b i) (A.b j)`. Establish `hsum : ∀ (c : A.ι → K) (j : A.ι), h (∑ i, star (c i) • A.b i) (A.b j) = Matrix.vecMul c G j`. Introduce `c j`. Simplify using `only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul, Matrix.vecMul, dotProduct, G]`. Establish `key : ∀ c : A.ι → K, Matrix.vecMul c G = 0 → c = 0`.

Introduce `c hc`. Establish `hu : h (∑ i, star (c i) • A.b i) = 0` using `A.b.ext fun j => by`. Rewrite using `[hsum c j, hc]`. Both sides reduce to the same expression. Establish `hu0` using `hnd (∑ i, star (c i) • A.b i) (fun y => by rw [hu]; rfl)`.

Establish `h0` using `(Fintype.linearIndependent_iff.mp A.b.linearIndependent) (fun i => star (c i)) hu0`. Use function extensionality and compare the values at `i`. Conclude with `star_eq_zero.mp (h0 i)`. Establish `hinj : Function.Injective (fun c : A.ι → K => Matrix.vecMul c G)`. Introduce `c c' hcc`.

Use `key (c - c') (by rw [Matrix.sub_vecMul]; exact sub_eq_zero.mpr hcc)` as an intermediate fact. Conclude with `sub_eq_zero.mp this`. Establish `hsurj : Function.Surjective (fun c : A.ι → K => Matrix.vecMul c G)` using `Matrix.vecMul_surjective_iff_isUnit.mpr (Matrix.vecMul_injective_iff_isUnit.mp hinj)`. Take `⟨c, hc⟩` from `hsurj (fun j => φ (A.b j))`. Use `⟨∑ i, star (c i) • A.b i, A.b.ext fun j => ?_⟩` and prove the remaining obligations.

Rewrite using `[hsum c j]`. Conclude with `congrFun hc j`.
-/
lemma exists_rep (A : HLat K) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) (hnd : ∀ x, (∀ y, h x y = 0) → x = 0)
    (φ : Module.Dual K A.V) : ∃ u, h u = φ := by
  classical
  let G : Matrix A.ι A.ι K := fun i j => h (A.b i) (A.b j)
  have hsum : ∀ (c : A.ι → K) (j : A.ι), h (∑ i, star (c i) • A.b i) (A.b j) = Matrix.vecMul c G j := by
    intro c j
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, starRingEnd_apply, star_star,
      smul_eq_mul, Matrix.vecMul, dotProduct, G]
  have key : ∀ c : A.ι → K, Matrix.vecMul c G = 0 → c = 0 := by
    intro c hc
    have hu : h (∑ i, star (c i) • A.b i) = 0 := A.b.ext fun j => by
      rw [hsum c j, hc]
      rfl
    have hu0 := hnd (∑ i, star (c i) • A.b i) (fun y => by rw [hu]; rfl)
    have h0 := (Fintype.linearIndependent_iff.mp A.b.linearIndependent) (fun i => star (c i)) hu0
    funext i
    exact star_eq_zero.mp (h0 i)
  have hinj : Function.Injective (fun c : A.ι → K => Matrix.vecMul c G) := by
    intro c c' hcc
    have := key (c - c') (by rw [Matrix.sub_vecMul]; exact sub_eq_zero.mpr hcc)
    exact sub_eq_zero.mp this
  have hsurj : Function.Surjective (fun c : A.ι → K => Matrix.vecMul c G) :=
    Matrix.vecMul_surjective_iff_isUnit.mpr (Matrix.vecMul_injective_iff_isUnit.mp hinj)
  obtain ⟨c, hc⟩ := hsurj (fun j => φ (A.b j))
  refine ⟨∑ i, star (c i) • A.b i, A.b.ext fun j => ?_⟩
  rw [hsum c j]
  exact congrFun hc j

end Herm

end PI.Dv.ProjGramW
