import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BesselChar

section Alg

variable {R : Type} [CommRing R] {n ρ : ℕ}

def StrictUp (T : Matrix (Fin ρ) (Fin ρ) R) : Prop := ∀ j i, i ≤ j → T j i = 0

def Unip (E : Matrix (Fin n) (Fin ρ) R) (K : Matrix (Fin ρ) (Fin n) R) (M : Matrix (Fin n) (Fin n) R) : Prop :=
  (∃ T : Matrix (Fin ρ) (Fin ρ) R, StrictUp T ∧ M * E = E + E * T) ∧ ∀ y, K *ᵥ y = 0 → ∃ a, M *ᵥ y = y + E *ᵥ a

/- English proof (translation)
Introduce `j i hij`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Break down `lt_or_ge k j with h | h` into its components or cases. Rewrite using `[hU (show id k < id j from h), zero_mul]`.

Rewrite using `[hT k i (hij.trans h), mul_zero]`.
-/
theorem StrictUp.mul_left {U T : Matrix (Fin ρ) (Fin ρ) R} (hU : U.BlockTriangular id) (hT : StrictUp T) :
    StrictUp (U * T) := by
  intro j i hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge k j with h | h
  · rw [hU (show id k < id j from h), zero_mul]
  · rw [hT k i (hij.trans h), mul_zero]

/- English proof (translation)
Introduce `_ _ h` and use `hT _ _ (le_of_lt h)`.
-/
theorem StrictUp.tri {T : Matrix (Fin ρ) (Fin ρ) R} (hT : StrictUp T) : T.BlockTriangular id :=
  fun _ _ h => hT _ _ (le_of_lt h)

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨0, fun _ _ _ => rfl, by simp⟩, fun y _ => ⟨0, by simp⟩⟩`.
-/
theorem unip_one (E : Matrix (Fin n) (Fin ρ) R) (K : Matrix (Fin ρ) (Fin n) R) : Unip E K 1 :=
  ⟨⟨0, fun _ _ _ => rfl, by simp⟩, fun y _ => ⟨0, by simp⟩⟩

/- English proof (translation)
Rewrite using `[Matrix.mul_assoc, h', Matrix.mul_add, ← Matrix.mul_assoc, h, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws.
-/
theorem mul_cols {E : Matrix (Fin n) (Fin ρ) R} {M M' : Matrix (Fin n) (Fin n) R} {T T' : Matrix (Fin ρ) (Fin ρ) R}
    (h : M * E = E + E * T) (h' : M' * E = E + E * T') : M * M' * E = E + E * (T + T' + T * T') := by
  rw [Matrix.mul_assoc, h', Matrix.mul_add, ← Matrix.mul_assoc, h, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    Matrix.mul_assoc]
  abel

/- English proof (translation)
Rewrite using `[← Matrix.mulVec_mulVec, ha', Matrix.mulVec_add, ha, Matrix.mulVec_mulVec, h, Matrix.add_mulVec, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_mulVec]`. Normalize the expressions using the abelian group laws.
-/
theorem mul_vec {E : Matrix (Fin n) (Fin ρ) R} {M M' : Matrix (Fin n) (Fin n) R} {T : Matrix (Fin ρ) (Fin ρ) R}
    {y : Fin n → R} {a a' : Fin ρ → R}
    (h : M * E = E + E * T) (ha : M *ᵥ y = y + E *ᵥ a) (ha' : M' *ᵥ y = y + E *ᵥ a') :
    (M * M') *ᵥ y = y + E *ᵥ (a + a' + T *ᵥ a') := by
  rw [← Matrix.mulVec_mulVec, ha', Matrix.mulVec_add, ha, Matrix.mulVec_mulVec, h, Matrix.add_mulVec,
    Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_mulVec]
  abel

/- English proof (translation)
Take `⟨⟨T, hT, e⟩, h2⟩` from `h`. Take `⟨⟨T', hT', e'⟩, h2'⟩` from `h'`. Use `⟨⟨_, ?_, mul_cols e e'⟩, fun y hy => ?_⟩` and prove the remaining obligations. Introduce `j i hij`. Rewrite using `[Matrix.add_apply, Matrix.add_apply, hT j i hij, hT' j i hij, hT'.mul_left hT.tri j i hij]`.

Simplify using the standard rewrite rules. Take `⟨a, ha⟩` from `h2 y hy`. Take `⟨a', ha'⟩` from `h2' y hy`. Conclude with `⟨_, mul_vec e ha ha'⟩`.
-/
theorem Unip.mul {E : Matrix (Fin n) (Fin ρ) R} {K : Matrix (Fin ρ) (Fin n) R} {M M' : Matrix (Fin n) (Fin n) R}
    (h : Unip E K M) (h' : Unip E K M') : Unip E K (M * M') := by
  obtain ⟨⟨T, hT, e⟩, h2⟩ := h
  obtain ⟨⟨T', hT', e'⟩, h2'⟩ := h'
  refine ⟨⟨_, ?_, mul_cols e e'⟩, fun y hy => ?_⟩
  · intro j i hij
    rw [Matrix.add_apply, Matrix.add_apply, hT j i hij, hT' j i hij, hT'.mul_left hT.tri j i hij]
    simp
  · obtain ⟨a, ha⟩ := h2 y hy
    obtain ⟨a', ha'⟩ := h2' y hy
    exact ⟨_, mul_vec e ha ha'⟩

/- English proof (translation)
Take `⟨⟨T, hT, e⟩, h2⟩` from `h`. Establish `hU : (1 + T).BlockTriangular id` using `Matrix.blockTriangular_one.add hT.tri`. Establish `hdet : (1 + T).det = 1`. Rewrite using `[Matrix.det_of_isUpperTriangular hU]`. Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.add_apply, hT i i le_rfl]`. Simplify using the standard rewrite rules. Establish `hu : IsUnit (1 + T).det` using `by rw [hdet]; exact isUnit_one`. Establish `: Invertible (1 + T)` using `Matrix.invertibleOfIsUnitDet _ hu`. Establish `hV : (1 + T)⁻¹.BlockTriangular id` using `Matrix.blockTriangular_inv_of_blockTriangular hU`.

Establish `e1 : M' * E = E * (1 + T)⁻¹`. Establish `: M' * E * (1 + T) = E`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_add, Matrix.mul_one, ← e, ← Matrix.mul_assoc, hM, Matrix.one_mul]`. Use `conv_rhs => rw [← this]`. Rewrite using `[Matrix.mul_assoc _ (1 + T), Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]`.

Establish `e2 : (1 + T)⁻¹ = 1 + -((1 + T)⁻¹ * T)`. Use `Matrix.nonsing_inv_mul _ hu` as an intermediate fact. Rewrite `this` using `[Matrix.mul_add, Matrix.mul_one]`. Rewrite using `[← sub_eq_add_neg, eq_sub_iff_add_eq, this]`. Use `⟨⟨-((1 + T)⁻¹ * T), ?_, ?_⟩, fun y hy => ?_⟩` and prove the remaining obligations.

Introduce `j i hij`. Rewrite using `[Matrix.neg_apply, hT.mul_left hV j i hij, neg_zero]`. Rewrite using `[e1] conv_lhs => rw [e2]`. Rewrite using `[Matrix.mul_add, Matrix.mul_one]`. Take `⟨a, ha⟩` from `h2 y hy`.

Use `⟨-((1 + T)⁻¹ *ᵥ a), ?_⟩` and prove the remaining obligations. Establish `: M' *ᵥ (M *ᵥ y) = y` using `by rw [Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]`. Rewrite `this` using `[ha, Matrix.mulVec_add, Matrix.mulVec_mulVec, e1, ← Matrix.mulVec_mulVec]`. Rewrite using `[Matrix.mulVec_neg, ← sub_eq_add_neg, eq_sub_iff_add_eq, this]`.
-/
theorem Unip.inv {E : Matrix (Fin n) (Fin ρ) R} {K : Matrix (Fin ρ) (Fin n) R} {M M' : Matrix (Fin n) (Fin n) R}
    (h : Unip E K M) (hM : M' * M = 1) : Unip E K M' := by
  obtain ⟨⟨T, hT, e⟩, h2⟩ := h
  have hU : (1 + T).BlockTriangular id := Matrix.blockTriangular_one.add hT.tri
  have hdet : (1 + T).det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hU]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [Matrix.add_apply, hT i i le_rfl]; simp
  have hu : IsUnit (1 + T).det := by rw [hdet]; exact isUnit_one
  have : Invertible (1 + T) := Matrix.invertibleOfIsUnitDet _ hu
  have hV : (1 + T)⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hU
  have e1 : M' * E = E * (1 + T)⁻¹ := by
    have : M' * E * (1 + T) = E := by
      rw [Matrix.mul_assoc, Matrix.mul_add, Matrix.mul_one, ← e, ← Matrix.mul_assoc, hM, Matrix.one_mul]
    conv_rhs => rw [← this]
    rw [Matrix.mul_assoc _ (1 + T), Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  have e2 : (1 + T)⁻¹ = 1 + -((1 + T)⁻¹ * T) := by
    have := Matrix.nonsing_inv_mul _ hu
    rw [Matrix.mul_add, Matrix.mul_one] at this
    rw [← sub_eq_add_neg, eq_sub_iff_add_eq, this]
  refine ⟨⟨-((1 + T)⁻¹ * T), ?_, ?_⟩, fun y hy => ?_⟩
  · intro j i hij
    rw [Matrix.neg_apply, hT.mul_left hV j i hij, neg_zero]
  · rw [e1]
    conv_lhs => rw [e2]
    rw [Matrix.mul_add, Matrix.mul_one]
  · obtain ⟨a, ha⟩ := h2 y hy
    refine ⟨-((1 + T)⁻¹ *ᵥ a), ?_⟩
    have : M' *ᵥ (M *ᵥ y) = y := by rw [Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]
    rw [ha, Matrix.mulVec_add, Matrix.mulVec_mulVec, e1, ← Matrix.mulVec_mulVec] at this
    rw [Matrix.mulVec_neg, ← sub_eq_add_neg, eq_sub_iff_add_eq, this]

/- English proof (translation)
Rewrite using `[Matrix.mul_assoc, hG', Matrix.mul_assoc, h, Matrix.mul_add, ← Matrix.mul_assoc, hG]`.
-/
theorem conj_cols {E : Matrix (Fin n) (Fin ρ) R} {M G G' : Matrix (Fin n) (Fin n) R} {T : Matrix (Fin ρ) (Fin ρ) R}
    (hG : G * E = E) (hG' : G' * E = E) (h : M * E = E + E * T) : G * M * G' * E = E + E * T := by
  rw [Matrix.mul_assoc, hG', Matrix.mul_assoc, h, Matrix.mul_add, ← Matrix.mul_assoc, hG]

/- English proof (translation)
Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hG, hGG, Matrix.one_mulVec]`.
-/
theorem conj_vec {E : Matrix (Fin n) (Fin ρ) R} {M G G' : Matrix (Fin n) (Fin n) R} {y : Fin n → R} {a : Fin ρ → R}
    (hG : G * E = E) (hGG : G * G' = 1) (h : M *ᵥ (G' *ᵥ y) = G' *ᵥ y + E *ᵥ a) :
    (G * M * G') *ᵥ y = y + E *ᵥ a := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_add, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hG, hGG, Matrix.one_mulVec]

/- English proof (translation)
Take `⟨⟨T, hT, e⟩, h2⟩` from `h`. Use `⟨⟨T, hT, conj_cols hG hG' e⟩, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `h2 (G' *ᵥ y) (by rw [Matrix.mulVec_mulVec, hK, hy])`. Conclude with `⟨a, conj_vec hG hGG ha⟩`.
-/
theorem Unip.conj {E : Matrix (Fin n) (Fin ρ) R} {K : Matrix (Fin ρ) (Fin n) R} {M G G' : Matrix (Fin n) (Fin n) R}
    (h : Unip E K M) (hG : G * E = E) (hG' : G' * E = E) (hGG : G * G' = 1) (hK : K * G' = K) :
    Unip E K (G * M * G') := by
  obtain ⟨⟨T, hT, e⟩, h2⟩ := h
  refine ⟨⟨T, hT, conj_cols hG hG' e⟩, fun y hy => ?_⟩
  obtain ⟨a, ha⟩ := h2 (G' *ᵥ y) (by rw [Matrix.mulVec_mulVec, hK, hy])
  exact ⟨a, conj_vec hG hGG ha⟩

def superSum (c : Fin ρ → R) (T : Matrix (Fin ρ) (Fin ρ) R) (b : Fin ρ → R) : R :=
  (∑ i : Fin ρ, ∑ j : Fin ρ, if j.1 = i.1 + 1 then c i * T i j else 0) +
    ∑ i : Fin ρ, if i.1 + 1 = ρ then c i * b i else 0

/- English proof (translation)
Unfold `superSum`. Rewrite using `[add_add_add_comm]`. Use `congr 1`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Establish `: (T * T') i j = 0`. Rewrite using `[Matrix.mul_apply]`.

Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Break down `le_or_gt k i with hk | hk` into its components or cases. Rewrite using `[hT i k hk, zero_mul]`. Rewrite using `[hT' k j (by rw [Fin.le_def]; rw [Fin.lt_def] at hk; omega), mul_zero]`. Rewrite using `[Matrix.add_apply, Matrix.add_apply, this]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `split_ifs with h`.

Establish `: (T *ᵥ b') i = 0` using `by show ∑ k, T i k * b' k = 0`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Use `k.2` as an intermediate fact. Rewrite using `[hT i k (by rw [Fin.le_def]; omega), zero_mul]`. Rewrite using `[Pi.add_apply, Pi.add_apply, this]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
theorem superSum_mul (c : Fin ρ → R) {T T' : Matrix (Fin ρ) (Fin ρ) R} (hT : StrictUp T) (hT' : StrictUp T')
    (b b' : Fin ρ → R) :
    superSum c (T + T' + T * T') (b + b' + T *ᵥ b') = superSum c T b + superSum c T' b' := by
  unfold superSum
  rw [add_add_add_comm]
  congr 1
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · have : (T * T') i j = 0 := by
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_zero fun k _ => ?_
        rcases le_or_gt k i with hk | hk
        · rw [hT i k hk, zero_mul]
        · rw [hT' k j (by rw [Fin.le_def]; rw [Fin.lt_def] at hk; omega), mul_zero]
      rw [Matrix.add_apply, Matrix.add_apply, this]; ring
    · simp
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · have : (T *ᵥ b') i = 0 := by
        show ∑ k, T i k * b' k = 0
        refine Finset.sum_eq_zero fun k _ => ?_
        have := k.2
        rw [hT i k (by rw [Fin.le_def]; omega), zero_mul]
      rw [Pi.add_apply, Pi.add_apply, this]; ring
    · simp

/- English proof (translation)
Simplify using `only [superSum, map_add, map_sum, apply_ite φ, map_mul, map_zero, Matrix.map_apply]`.
-/
theorem superSum_map {S : Type} [CommRing S] (φ : R →+* S) (c : Fin ρ → R) (T : Matrix (Fin ρ) (Fin ρ) R)
    (b : Fin ρ → R) : superSum (fun i => φ (c i)) (T.map φ) (fun i => φ (b i)) = φ (superSum c T b) := by
  simp only [superSum, map_add, map_sum, apply_ite φ, map_mul, map_zero, Matrix.map_apply]

/- English proof (translation)
Unfold `superSum`. Use `Continuous.add (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_) (continuous_finsetSum _ fun i _ => ?_)` and prove the remaining obligations. Use `split_ifs`. Conclude with `continuous_const.mul (hT.matrix_elem i j)`. Conclude with `continuous_const`.

Use `split_ifs`. Conclude with `continuous_const.mul ((continuous_apply i).comp hb)`. Conclude with `continuous_const`.
-/
theorem continuous_superSum [TopologicalSpace R] [IsTopologicalRing R] {X : Type} [TopologicalSpace X]
    (c : Fin ρ → R) {T : X → Matrix (Fin ρ) (Fin ρ) R} {b : X → Fin ρ → R} (hT : Continuous T) (hb : Continuous b) :
    Continuous fun x => superSum c (T x) (b x) := by
  unfold superSum
  refine Continuous.add (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_)
    (continuous_finsetSum _ fun i _ => ?_)
  · split_ifs
    · exact continuous_const.mul (hT.matrix_elem i j)
    · exact continuous_const
  · split_ifs
    · exact continuous_const.mul ((continuous_apply i).comp hb)
    · exact continuous_const

/- English proof (translation)
Establish `hi : Function.Injective e.mulVec` using `Matrix.mulVec_injective_iff.2 h`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective (Matrix.toLin' e) (LinearMap.ker_eq_bot.2 hi)`. Use `⟨LinearMap.toMatrix' g, ?_⟩` and prove the remaining obligations. Use `congrArg LinearMap.toMatrix' hg` as an intermediate fact. Rewrite `this` using `[LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id]`. Then use the resulting hypothesis.
-/
theorem exists_leftInv {E : Type} [Field E] (e : Matrix (Fin n) (Fin ρ) E) (h : LinearIndependent E e.transpose) :
    ∃ L : Matrix (Fin ρ) (Fin n) E, L * e = 1 := by
  have hi : Function.Injective e.mulVec := Matrix.mulVec_injective_iff.2 h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' e) (LinearMap.ker_eq_bot.2 hi)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this

/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `(RingHom.map_mulVec φ P x i).symm`.
-/
theorem mulVec_map {E : Type} [CommRing E] (φ : E →+* R) {m : ℕ} (P : Matrix (Fin m) (Fin n) E) (x : Fin n → E) :
    P.map φ *ᵥ (fun i => φ (x i)) = fun i => φ ((P *ᵥ x) i) := by
  funext i
  exact (RingHom.map_mulVec φ P x i).symm

/- English proof (translation)
Establish `hP : K * (1 - G * K) = 0`. Rewrite using `[Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hG, Matrix.one_mul, sub_self]`. Use `choose a ha using fun j => h (fun k => (1 - G * K : Matrix (Fin n) (Fin n) E) k j) (by funext k; exact congr_fun (congr_fun hP k) j)`. Establish `e1 : M * (1 - G * K).map φ = X * (Matrix.of a)ᵀ`. Use extensionality with `i j`.

Conclude with `congr_fun (ha j) i`. Establish `e2 : (1 - G * K).map φ *ᵥ y = y`. Rewrite using `[Matrix.map_sub _ (map_sub φ), Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.map_mul, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_zero, Matrix.one_mulVec, sub_zero]`. Use `⟨(Matrix.of a)ᵀ *ᵥ y, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_mulVec, ← e1, ← Matrix.mulVec_mulVec, e2]`.
-/
theorem ker_baseChange {E : Type} [CommRing E] (φ : E →+* R) (K : Matrix (Fin ρ) (Fin n) E) (G : Matrix (Fin n) (Fin ρ) E)
    (hG : K * G = 1) (X : Matrix (Fin n) (Fin ρ) R) (M : Matrix (Fin n) (Fin n) R)
    (h : ∀ x, K *ᵥ x = 0 → ∃ a, M *ᵥ (fun i => φ (x i)) = X *ᵥ a) (y : Fin n → R) (hy : K.map φ *ᵥ y = 0) :
    ∃ a, M *ᵥ y = X *ᵥ a := by
  have hP : K * (1 - G * K) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hG, Matrix.one_mul, sub_self]
  choose a ha using fun j => h (fun k => (1 - G * K : Matrix (Fin n) (Fin n) E) k j)
    (by funext k; exact congr_fun (congr_fun hP k) j)
  have e1 : M * (1 - G * K).map φ = X * (Matrix.of a)ᵀ := by
    ext i j
    exact congr_fun (ha j) i
  have e2 : (1 - G * K).map φ *ᵥ y = y := by
    rw [Matrix.map_sub _ (map_sub φ), Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.map_mul, Matrix.sub_mulVec,
      ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_zero, Matrix.one_mulVec, sub_zero]
  refine ⟨(Matrix.of a)ᵀ *ᵥ y, ?_⟩
  rw [Matrix.mulVec_mulVec, ← e1, ← Matrix.mulVec_mulVec, e2]

def coordSum (c : Fin ρ → R) (L : Matrix (Fin ρ) (Fin n) R) (E : Matrix (Fin n) (Fin ρ) R) (z : Fin n → R)
    (M : Matrix (Fin n) (Fin n) R) : R :=
  superSum c (L * (M - 1) * E) ((L * (M - 1)) *ᵥ z)

/- English proof (translation)
Establish `e1 : L * (M - 1) * E = T`. Rewrite using `[Matrix.mul_assoc, Matrix.sub_mul, h1, Matrix.one_mul, add_sub_cancel_left, ← Matrix.mul_assoc, hL, Matrix.one_mul]`. Establish `e2 : (L * (M - 1)) *ᵥ z = b`. Rewrite using `[← Matrix.mulVec_mulVec, Matrix.sub_mulVec, h2, Matrix.one_mulVec, add_sub_cancel_left, Matrix.mulVec_mulVec, hL, Matrix.one_mulVec]`. Rewrite using `[coordSum, e1, e2]`.
-/
theorem coordSum_eq (c : Fin ρ → R) {L : Matrix (Fin ρ) (Fin n) R} {E : Matrix (Fin n) (Fin ρ) R} {z : Fin n → R}
    {M : Matrix (Fin n) (Fin n) R} {T : Matrix (Fin ρ) (Fin ρ) R} {b : Fin ρ → R} (hL : L * E = 1)
    (h1 : M * E = E + E * T) (h2 : M *ᵥ z = z + E *ᵥ b) : coordSum c L E z M = superSum c T b := by
  have e1 : L * (M - 1) * E = T := by
    rw [Matrix.mul_assoc, Matrix.sub_mul, h1, Matrix.one_mul, add_sub_cancel_left, ← Matrix.mul_assoc, hL,
      Matrix.one_mul]
  have e2 : (L * (M - 1)) *ᵥ z = b := by
    rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, h2, Matrix.one_mulVec, add_sub_cancel_left, Matrix.mulVec_mulVec,
      hL, Matrix.one_mulVec]
  rw [coordSum, e1, e2]

/- English proof (translation)
Establish `hm : M.map φ - 1 = (M - 1).map φ`. Rewrite using `[Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]`. Unfold `coordSum`. Rewrite using `[hm, ← Matrix.map_mul, ← Matrix.map_mul, mulVec_map, superSum_map]`.
-/
theorem coordSum_map {S : Type} [CommRing S] (φ : R →+* S) (c : Fin ρ → R) (L : Matrix (Fin ρ) (Fin n) R)
    (E : Matrix (Fin n) (Fin ρ) R) (z : Fin n → R) (M : Matrix (Fin n) (Fin n) R) :
    coordSum (fun i => φ (c i)) (L.map φ) (E.map φ) (fun i => φ (z i)) (M.map φ) = φ (coordSum c L E z M) := by
  have hm : M.map φ - 1 = (M - 1).map φ := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
  unfold coordSum
  rw [hm, ← Matrix.map_mul, ← Matrix.map_mul, mulVec_map, superSum_map]

/- English proof (translation)
Establish `hm : Continuous fun M : Matrix (Fin n) (Fin n) R => L * (M - 1)` using `continuous_const.matrix_mul (continuous_id.sub continuous_const)`. Conclude with `continuous_superSum c (hm.matrix_mul continuous_const) (hm.matrix_mulVec continuous_const)`.
-/
theorem continuous_coordSum [TopologicalSpace R] [IsTopologicalRing R] (c : Fin ρ → R) (L : Matrix (Fin ρ) (Fin n) R)
    (E : Matrix (Fin n) (Fin ρ) R) (z : Fin n → R) : Continuous (coordSum c L E z) := by
  have hm : Continuous fun M : Matrix (Fin n) (Fin n) R => L * (M - 1) :=
    continuous_const.matrix_mul (continuous_id.sub continuous_const)
  exact continuous_superSum c (hm.matrix_mul continuous_const) (hm.matrix_mulVec continuous_const)

/- English proof (translation)
Rewrite using `[← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem map_leftInv {S : Type} [CommRing S] (φ : R →+* S) {e : Matrix (Fin n) (Fin ρ) R} {L : Matrix (Fin ρ) (Fin n) R}
    (hL : L * e = 1) : L.map φ * e.map φ = 1 := by
  rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]

/- English proof (translation)
Establish `h1` using `congrArg (Formalism.UG.cT σ) h`. Rewrite `h1` using `[Formalism.UG.cT_mul]`. Use `conv_lhs => rw [← h1]`. Rewrite using `[Matrix.mul_assoc (Formalism.UG.cT σ E), Matrix.mul_assoc, hu]`.
-/
theorem perp_fixed_gen (σ : R →+* R) {E : Matrix (Fin n) (Fin ρ) R} {J M : Matrix (Fin n) (Fin n) R}
    (hu : Formalism.UG.cT σ M * J * M = J) (h : M * E = E) : Formalism.UG.cT σ E * J * M = Formalism.UG.cT σ E * J := by
  have h1 := congrArg (Formalism.UG.cT σ) h
  rw [Formalism.UG.cT_mul] at h1
  conv_lhs => rw [← h1]
  rw [Matrix.mul_assoc (Formalism.UG.cT σ E), Matrix.mul_assoc, hu]

/- English proof (translation)
Use `conv_lhs => rw [← h]`. Rewrite using `[← Matrix.mul_assoc, hM, Matrix.one_mul]`.
-/
theorem inv_fix_cols {E : Matrix (Fin n) (Fin ρ) R} {M M' : Matrix (Fin n) (Fin n) R} (hM : M' * M = 1)
    (h : M * E = E) : M' * E = E := by
  conv_lhs => rw [← h]
  rw [← Matrix.mul_assoc, hM, Matrix.one_mul]

/- English proof (translation)
Use `conv_lhs => rw [← h]`. Rewrite using `[Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]`.
-/
theorem inv_fix_vec {z : Fin n → R} {M M' : Matrix (Fin n) (Fin n) R} (hM : M' * M = 1)
    (h : M *ᵥ z = z) : M' *ᵥ z = z := by
  conv_lhs => rw [← h]
  rw [Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]

end Alg

section Adelic

variable {D : D7}

local infixl:70 " *ₘ " => HMul.hMul

/- English proof (translation)
Simplify using `[Formalism.L2.Theta.mt]`.
-/
theorem mt_mul (B : HSp D) (g h : GA D B) : Formalism.L2.Theta.mt B (g * h) = Formalism.L2.Theta.mt B g * Formalism.L2.Theta.mt B h := by
  simp [Formalism.L2.Theta.mt]

/- English proof (translation)
Simplify using `[Formalism.L2.Theta.mt]`.
-/
theorem mt_one (B : HSp D) : Formalism.L2.Theta.mt B 1 = 1 := by simp [Formalism.L2.Theta.mt]

/- English proof (translation)
Rewrite using `[← mt_mul, inv_mul_cancel, mt_one]`.
-/
theorem mt_inv_mul (B : HSp D) (g : GA D B) : Formalism.L2.Theta.mt B g⁻¹ * Formalism.L2.Theta.mt B g = 1 := by
  rw [← mt_mul, inv_mul_cancel, mt_one]

/- English proof (translation)
Rewrite using `[← mt_mul, mul_inv_cancel, mt_one]`.
-/
theorem mt_mul_inv (B : HSp D) (g : GA D B) : Formalism.L2.Theta.mt B g * Formalism.L2.Theta.mt B g⁻¹ = 1 := by
  rw [← mt_mul, mul_inv_cancel, mt_one]

/- English proof (translation)
Unfold `subOne`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_iff_eq_add']`. Both sides reduce to the same expression.
-/
theorem subOne_vec (B : HSp D) (g : GA D B) (y w : Fin B.rank → AE D) :
    subOne B g *ᵥ y = w ↔ Formalism.L2.Theta.mt B g *ᵥ y = y + w := by
  unfold subOne
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_iff_eq_add']
  rfl

/- English proof (translation)
Simplify using `only [subOne_vec]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `k i`. Conclude with `congr_fun (h i) k`.

Introduce `h i`. Use function extensionality and compare the values at `k`. Conclude with `congr_fun (congr_fun h k) i`.
-/
theorem subOne_cols (B : HSp D) {ρ : ℕ} (e : Matrix (Fin B.rank) (Fin ρ) D.host.E) (g : GA D B)
    (a : Fin ρ → Fin ρ → AE D) :
    (∀ i, subOne B g *ᵥ (ratV fun k => e k i) = e.map (incA D) *ᵥ a i) ↔
      Formalism.L2.Theta.mt B g *ₘ e.map (incA D) = e.map (incA D) + e.map (incA D) *ₘ (Matrix.of a)ᵀ := by
  simp only [subOne_vec]
  constructor
  · intro h
    ext k i
    exact congr_fun (h i) k
  · intro h i
    funext k
    exact congr_fun (congr_fun h k) i

abbrev perpMat (B : HSp D) {ρ : ℕ} (e : Matrix (Fin B.rank) (Fin ρ) D.host.E) : Matrix (Fin ρ) (Fin B.rank) D.host.E :=
  Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e * B.gram

/- English proof (translation)
Take `⟨L, hL⟩` from `exists_leftInv e he`. Establish `hu : IsUnit B.gram.det` using `(GlobalTheory.AutFunCounterexample.gram_det_ne B).isUnit`. Use `⟨B.gram⁻¹ * Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) L, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc B.gram, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, ← Formalism.UG.cT_mul, hL, Formalism.UG.cT_one]`.
-/
theorem perpMat_rightInv (B : HSp D) {ρ : ℕ} (e : Matrix (Fin B.rank) (Fin ρ) D.host.E)
    (he : LinearIndependent D.host.E e.transpose) :
    ∃ G : Matrix (Fin B.rank) (Fin ρ) D.host.E, perpMat B e * G = 1 := by
  obtain ⟨L, hL⟩ := exists_leftInv e he
  have hu : IsUnit B.gram.det := (GlobalTheory.AutFunCounterexample.gram_det_ne B).isUnit
  refine ⟨B.gram⁻¹ * Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) L, ?_⟩
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc B.gram, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, ← Formalism.UG.cT_mul, hL,
    Formalism.UG.cT_one]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hg`. Unfold `NFlag at hg`. Proceed by induction on `hg using Subgroup.closure_induction with`. Consider the case `mem g hg`.

Take `⟨h1, h2⟩` from `hg`. Use `choose a ha0 ha using h1`. Take `⟨G, hG⟩` from `perpMat_rightInv B e he`. Use `⟨⟨(Matrix.of a)ᵀ, fun j i hij => ha0 i j hij, (subOne_cols B e g a).1 ha⟩, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `ker_baseChange (incA D) (perpMat B e) G hG (e.map (incA D)) (subOne B g) h2 y hy`.

Conclude with `⟨c, (subOne_vec B g y _).1 hc⟩`. Consider the case `one => rw [mt_one]`. Conclude with `unip_one _ _`. Consider the case `mul g h _ _ hg hh => rw [mt_mul]`. Conclude with `hg.mul hh`.

Consider the case `inv g _ hg => exact hg.inv (mt_inv_mul B g)`. Introduce and unpack `⟨⟨T, hT, h1⟩, h2⟩`. Use `Subgroup.subset_closure ⟨fun i => ⟨fun j => T j i, fun j hij => hT j i hij, ?_⟩, fun x hx => ?_⟩` and prove the remaining obligations. Conclude with `(subOne_cols B e g (fun i j => T j i)).2 h1 i`. Take `⟨a, ha⟩` from `h2 (ratV x) (by`.

Use `mulVec_map (incA D) (perpMat B e) x` as an intermediate fact. Rewrite `this` using `[hx]`. Use `this.trans ?_` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Conclude with `map_zero _)`.

Conclude with `⟨a, (subOne_vec B g _ _).2 ha⟩`.
-/
theorem mem_NFlag_iff (B : HSp D) {ρ : ℕ} (e : Matrix (Fin B.rank) (Fin ρ) D.host.E)
    (he : LinearIndependent D.host.E e.transpose) (g : GA D B) :
    g ∈ NFlag B e ↔ Unip (e.map (incA D)) ((perpMat B e).map (incA D)) (Formalism.L2.Theta.mt B g) := by
  constructor
  · intro hg
    unfold NFlag at hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨h1, h2⟩ := hg
      choose a ha0 ha using h1
      obtain ⟨G, hG⟩ := perpMat_rightInv B e he
      refine ⟨⟨(Matrix.of a)ᵀ, fun j i hij => ha0 i j hij, (subOne_cols B e g a).1 ha⟩, fun y hy => ?_⟩
      obtain ⟨c, hc⟩ := ker_baseChange (incA D) (perpMat B e) G hG (e.map (incA D)) (subOne B g) h2 y hy
      exact ⟨c, (subOne_vec B g y _).1 hc⟩
    | one => rw [mt_one]; exact unip_one _ _
    | mul g h _ _ hg hh => rw [mt_mul]; exact hg.mul hh
    | inv g _ hg => exact hg.inv (mt_inv_mul B g)
  · rintro ⟨⟨T, hT, h1⟩, h2⟩
    refine Subgroup.subset_closure ⟨fun i => ⟨fun j => T j i, fun j hij => hT j i hij, ?_⟩, fun x hx => ?_⟩
    · exact (subOne_cols B e g (fun i j => T j i)).2 h1 i
    · obtain ⟨a, ha⟩ := h2 (ratV x) (by
        have := mulVec_map (incA D) (perpMat B e) x
        rw [hx] at this
        refine this.trans ?_
        funext i
        exact map_zero _)
      exact ⟨a, (subOne_vec B g _ _).2 ha⟩

variable {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

/- English proof (translation)
Take `⟨L, hL⟩` from `exists_leftInv d.e d.e_iso.1`. Establish `hL'` using `map_leftInv (incA D) hL`. Establish `hex : ∃ v, IsBesVal ψ d g v` using `⟨_, fun i j => T j i, b, (subOne_cols B d.e g (fun i j => T j i)).2 hT, (subOne_vec B g _ _).2 hb, rfl⟩`. Unfold `besChar`. Rewrite using `[dif_pos hex]`.

Take `⟨a, b', h1, h2, h3⟩` from `hex.choose_spec`. Establish `e1` using `(subOne_cols B d.e g a).1 h1`. Establish `e2` using `(subOne_vec B g _ _).1 h2`. Rewrite using `[h3, ← coordSum_eq _ hL' hT hb, coordSum_eq _ hL' e1 e2]`. Both sides reduce to the same expression.
-/
theorem besChar_eq (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (g : GA D B)
    (T : Matrix (Fin d.ρ) (Fin d.ρ) (AE D)) (b : Fin d.ρ → AE D)
    (hT : Formalism.L2.Theta.mt B g *ₘ d.e.map (incA D) = d.e.map (incA D) + d.e.map (incA D) *ₘ T)
    (hb : Formalism.L2.Theta.mt B g *ᵥ ratV d.z = ratV d.z + d.e.map (incA D) *ᵥ b) :
    besChar ψ d g = ψ (Algebra.trace (AF D.host.F) (AE D) (superSum (fun i => incA D (d.c i)) T b)) := by
  obtain ⟨L, hL⟩ := exists_leftInv d.e d.e_iso.1
  have hL' := map_leftInv (incA D) hL
  have hex : ∃ v, IsBesVal ψ d g v :=
    ⟨_, fun i j => T j i, b, (subOne_cols B d.e g (fun i j => T j i)).2 hT, (subOne_vec B g _ _).2 hb, rfl⟩
  unfold besChar
  rw [dif_pos hex]
  obtain ⟨a, b', h1, h2, h3⟩ := hex.choose_spec
  have e1 := (subOne_cols B d.e g a).1 h1
  have e2 := (subOne_vec B g _ _).1 h2
  rw [h3, ← coordSum_eq _ hL' hT hb, coordSum_eq _ hL' e1 e2]
  rfl

/- English proof (translation)
Use `mulVec_map (incA D) (perpMat B d.e) d.z` as an intermediate fact. Rewrite `this` using `[d.z_perpE]`. Use `this.trans ?_` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Conclude with `map_zero _`.
-/
theorem flagOrthogonalComplementEquations_mulVec_bessel_eq_zero (d : BesDat A B ι) : (perpMat B d.e).map (incA D) *ᵥ ratV d.z = 0 := by
  have := mulVec_map (incA D) (perpMat B d.e) d.z
  rw [d.z_perpE] at this
  refine this.trans ?_
  funext i
  exact map_zero _

/- English proof (translation)
Take `⟨⟨T, hT, h1⟩, h2⟩` from `(mem_NFlag_iff B d.e d.e_iso.1 g).1 hg`. Take `⟨b, hb⟩` from `h2 _ (flagOrthogonalComplementEquations_mulVec_bessel_eq_zero d)`. Conclude with `⟨T, b, hT, h1, hb⟩`.
-/
theorem exists_coords (d : BesDat A B ι) (g : GA D B) (hg : g ∈ NFlag B d.e) :
    ∃ (T : Matrix (Fin d.ρ) (Fin d.ρ) (AE D)) (b : Fin d.ρ → AE D), StrictUp T ∧
      Formalism.L2.Theta.mt B g *ₘ d.e.map (incA D) = d.e.map (incA D) + d.e.map (incA D) *ₘ T ∧
      Formalism.L2.Theta.mt B g *ᵥ ratV d.z = ratV d.z + d.e.map (incA D) *ᵥ b := by
  obtain ⟨⟨T, hT, h1⟩, h2⟩ := (mem_NFlag_iff B d.e d.e_iso.1 g).1 hg
  obtain ⟨b, hb⟩ := h2 _ (flagOrthogonalComplementEquations_mulVec_bessel_eq_zero d)
  exact ⟨T, b, hT, h1, hb⟩

/- English proof (translation)
Take `⟨T, b, -, h1, h2⟩` from `exists_coords d g hg`. Rewrite using `[coordSum_eq _ (map_leftInv (incA D) hL) h1 h2]`. Conclude with `besChar_eq ψ d g T b h1 h2`.
-/
theorem besChar_formula (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (L : Matrix (Fin d.ρ) (Fin B.rank) D.host.E)
    (hL : L * d.e = 1) (g : GA D B) (hg : g ∈ NFlag B d.e) :
    besChar ψ d g = ψ (Algebra.trace (AF D.host.F) (AE D) (coordSum (fun i => incA D (d.c i))
      (L.map (incA D)) (d.e.map (incA D)) (ratV d.z) (Formalism.L2.Theta.mt B g))) := by
  obtain ⟨T, b, -, h1, h2⟩ := exists_coords d g hg
  rw [coordSum_eq _ (map_leftInv (incA D) hL) h1 h2]
  exact besChar_eq ψ d g T b h1 h2

/- English proof (translation)
Take `⟨T, b, hT, h1, h2⟩` from `exists_coords d g hg`. Take `⟨T', b', hT', h1', h2'⟩` from `exists_coords d h hh`. Rewrite using `[besChar_eq ψ d g T b h1 h2, besChar_eq ψ d h T' b' h1' h2', besChar_eq ψ d (g * h) (T + T' + T * T') (b + b' + T *ᵥ b') (by rw [mt_mul]; exact mul_cols h1 h1') (by rw [mt_mul]; exact mul_vec h1 h2 h2'), superSum_mul _ hT hT', map_add, AddChar.map_add_eq_mul]`.
-/
theorem besChar_mul (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (g h : GA D B) (hg : g ∈ NFlag B d.e)
    (hh : h ∈ NFlag B d.e) : besChar ψ d (g * h) = besChar ψ d g * besChar ψ d h := by
  obtain ⟨T, b, hT, h1, h2⟩ := exists_coords d g hg
  obtain ⟨T', b', hT', h1', h2'⟩ := exists_coords d h hh
  rw [besChar_eq ψ d g T b h1 h2, besChar_eq ψ d h T' b' h1' h2',
    besChar_eq ψ d (g * h) (T + T' + T * T') (b + b' + T *ᵥ b') (by rw [mt_mul]; exact mul_cols h1 h1')
      (by rw [mt_mul]; exact mul_vec h1 h2 h2'),
    superSum_mul _ hT hT', map_add, AddChar.map_add_eq_mul]

/- English proof (translation)
Use `show Algebra.trace (AF D.host.F) (AE D) ((1 : AF D.host.F) ⊗ₜ[D.host.F] x) = _`. Rewrite using `[Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]`.
-/
theorem trace_incA (x : D.host.E) : Algebra.trace (AF D.host.F) (AE D) (incA D x) =
    algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E x) := by
  show Algebra.trace (AF D.host.F) (AE D) ((1 : AF D.host.F) ⊗ₜ[D.host.F] x) = _
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

/- English proof (translation)
Take `⟨L, hL⟩` from `exists_leftInv d.e d.e_iso.1`. Take `⟨γ, -, hγ⟩` from `hq`. Establish `hm : Formalism.L2.Theta.mt B g = (γ : Matrix (Fin B.rank) (Fin B.rank) D.host.E).map (incA D)` using `(congrArg Units.val hγ).symm`. Rewrite using `[besChar_formula ψ d L hL g hg, hm]`. Unfold `ratV`.

Rewrite using `[coordSum_map, trace_incA]`. Conclude with `hψ.2.2.1 _`.
-/
theorem besChar_rat (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (d : BesDat A B ι) (g : GA D B)
    (hg : g ∈ NFlag B d.e) (hq : g ∈ GQ B) : besChar ψ d g = 1 := by
  obtain ⟨L, hL⟩ := exists_leftInv d.e d.e_iso.1
  obtain ⟨γ, -, hγ⟩ := hq
  have hm : Formalism.L2.Theta.mt B g = (γ : Matrix (Fin B.rank) (Fin B.rank) D.host.E).map (incA D) :=
    (congrArg Units.val hγ).symm
  rw [besChar_formula ψ d L hL g hg, hm]
  unfold ratV
  rw [coordSum_map, trace_incA]
  exact hψ.2.2.1 _

/- English proof (translation)
Take `⟨L, hL⟩` from `exists_leftInv d.e d.e_iso.1`. Establish `: IsTopologicalRing (AE D)` using `IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)`. Establish `ht : Continuous (Algebra.trace (AF D.host.F) (AE D))` using `IsModuleTopology.continuous_of_linearMap _`. Establish `hm0 : Continuous (fun k : GA D B => Formalism.L2.Theta.mt B k)` using `Units.continuous_val.comp continuous_subtype_val`. Use `hψ.1.comp (ht.comp ((continuous_coordSum (fun i => incA D (d.c i)) (L.map (incA D)) (d.e.map (incA D)) (ratV d.z)).comp (hm0.comp (continuous_subtype_val (p := (· ∈ NFlag B d.e))))))` as an intermediate fact.

Conclude with `this.congr fun n => (besChar_formula ψ d L hL n n.2).symm`.
-/
theorem besChar_continuous (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (d : BesDat A B ι) :
    Continuous fun n : NFlag B d.e => besChar ψ d (n : GA D B) := by
  obtain ⟨L, hL⟩ := exists_leftInv d.e d.e_iso.1
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  have hm0 : Continuous (fun k : GA D B => Formalism.L2.Theta.mt B k) := Units.continuous_val.comp continuous_subtype_val
  have := hψ.1.comp (ht.comp ((continuous_coordSum (fun i => incA D (d.c i))
    (L.map (incA D)) (d.e.map (incA D)) (ratV d.z)).comp (hm0.comp (continuous_subtype_val (p := (· ∈ NFlag B d.e))))))
  exact this.congr fun n => (besChar_formula ψ d L hL n n.2).symm

/- English proof (translation)
Establish `h2 : (perpMat B e).map (incA D) = Formalism.UG.cT (cA D) (e.map (incA D)) *ₘ B.gram.map (incA D)`. Rewrite using `[Matrix.map_mul, GlobalTheory.AutFunCounterexample.cT_map_gen]`. Rewrite using `[h2]`. Conclude with `perp_fixed_gen (cA D) g.2 hg`.
-/
theorem perp_fixed {ρ : ℕ} (e : Matrix (Fin B.rank) (Fin ρ) D.host.E) (g : GA D B)
    (hg : Formalism.L2.Theta.mt B g *ₘ e.map (incA D) = e.map (incA D)) :
    (perpMat B e).map (incA D) *ₘ Formalism.L2.Theta.mt B g = (perpMat B e).map (incA D) := by
  have h2 : (perpMat B e).map (incA D) = Formalism.UG.cT (cA D) (e.map (incA D)) *ₘ B.gram.map (incA D) := by
    rw [Matrix.map_mul, GlobalTheory.AutFunCounterexample.cT_map_gen]
  rw [h2]
  exact perp_fixed_gen (cA D) g.2 hg

/- English proof (translation)
Establish `he : Formalism.L2.Theta.mt B g *ₘ d.e.map (incA D) = d.e.map (incA D)`. Use extensionality with `k i`. Conclude with `congr_fun (hg.2 (fun k => d.e k i) (by funext k; exact congr_fun (congr_fun d.e_perp k) i)) k`. Establish `hz : Formalism.L2.Theta.mt B g *ᵥ ratV d.z = ratV d.z` using `hg.2 d.z d.z_perpA`. Establish `he'` using `inv_fix_cols (mt_inv_mul B g) he`.

Establish `hz'` using `inv_fix_vec (mt_inv_mul B g) hz`. Prove the components needed by the constructor for the conclusion. Rewrite `hn`, the goal using `[mem_NFlag_iff B d.e d.e_iso.1]`. Rewrite using `[mt_mul, mt_mul]`. Conclude with `hn.conj he he' (mt_mul_inv B g) (perp_fixed d.e g⁻¹ he')`.

Take `⟨T, b, -, h1, h2⟩` from `exists_coords d n hn`. Rewrite using `[besChar_eq ψ d n T b h1 h2]`. Use `besChar_eq ψ d _ T b ?_ ?_` and prove the remaining obligations. Rewrite using `[mt_mul, mt_mul]`. Conclude with `conj_cols he he' h1`.

Rewrite using `[mt_mul, mt_mul]; exact conj_vec he (mt_mul_inv B g) (by rw [hz', h2])`.
-/
theorem besChar_conj (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (g : GA D B) (h : GA D A)
    (hg : EmbRel B A ι g h) (n : GA D B) (hn : n ∈ NFlag B d.e) :
    g * n * g⁻¹ ∈ NFlag B d.e ∧ besChar ψ d (g * n * g⁻¹) = besChar ψ d n := by
  have he : Formalism.L2.Theta.mt B g *ₘ d.e.map (incA D) = d.e.map (incA D) := by
    ext k i
    exact congr_fun (hg.2 (fun k => d.e k i) (by funext k; exact congr_fun (congr_fun d.e_perp k) i)) k
  have hz : Formalism.L2.Theta.mt B g *ᵥ ratV d.z = ratV d.z := hg.2 d.z d.z_perpA
  have he' := inv_fix_cols (mt_inv_mul B g) he
  have hz' := inv_fix_vec (mt_inv_mul B g) hz
  constructor
  · rw [mem_NFlag_iff B d.e d.e_iso.1] at hn ⊢
    rw [mt_mul, mt_mul]
    exact hn.conj he he' (mt_mul_inv B g) (perp_fixed d.e g⁻¹ he')
  · obtain ⟨T, b, -, h1, h2⟩ := exists_coords d n hn
    rw [besChar_eq ψ d n T b h1 h2]
    refine besChar_eq ψ d _ T b ?_ ?_
    · rw [mt_mul, mt_mul]; exact conj_cols he he' h1
    · rw [mt_mul, mt_mul]; exact conj_vec he (mt_mul_inv B g) (by rw [hz', h2])

end Adelic

/- English proof (translation)
Introduce `_ ψ hψ _ _ _ _ d` and use `⟨fun n n' => besChar_mul ψ d n n' n.2 n'.2, fun γ hγ => besChar_rat ψ hψ.1 d γ γ.2 hγ, besChar_continuous ψ hψ.1 d, fun g h hg n hn => besChar_conj ψ d g h hg n hn⟩`.
-/
theorem besChar_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V), HSpace.IsIsomEmb A B ι → ∀ d : BesDat A B ι, (∀ n n' : NFlag B d.e, besChar ψ d ((n * n' : NFlag B d.e) : GA D B) = besChar ψ d (n : GA D B) * besChar ψ d (n' : GA D B)) ∧ (∀ γ ∈ NFlagQ B d.e, besChar ψ d (γ : GA D B) = 1) ∧ (Continuous fun n : NFlag B d.e => besChar ψ d (n : GA D B)) ∧ ∀ g h, EmbRel B A ι g h → ∀ n ∈ NFlag B d.e, g * n * g⁻¹ ∈ NFlag B d.e ∧ besChar ψ d (g * n * g⁻¹) = besChar ψ d n :=
  fun _ ψ hψ _ _ _ _ d =>
    ⟨fun n n' => besChar_mul ψ d n n' n.2 n'.2, fun γ hγ => besChar_rat ψ hψ.1 d γ γ.2 hγ,
      besChar_continuous ψ hψ.1 d, fun g h hg n hn => besChar_conj ψ d g h hg n hn⟩

end GlobalTheory.BesselChar

end
