import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryOfSabMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculus
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsUnitGramFrameBorelChange
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOne
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.UnitFramesGeneratorRatioModulusOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.BlockTriangularOfMulEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix ComplexConjugate

noncomputable section

namespace GlobalTheory.PeriodBorel

open GlobalTheory.FramePeriod

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Establish `h0 : f 0 = 0`. Use `hadd 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Take the linear combination `-this`. Establish `hE : ∀ v : Fin r → E, f (Data.emb τ v) = 0`.

Introduce `v`. Establish `hv : v ∈ Submodule.span E (X.Λ : Set (Fin r → E))` using `by rw [X.Λ_span]; trivial`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem v hv => exact h v hv`. Consider the case `zero`.

Establish `: Data.emb τ (0 : Fin r → E) = 0` using `by funext a; simp [Data.emb]`. Rewrite using `[this, h0]`. Consider the case `add v w _ _ hv hw`. Establish `: Data.emb τ (v + w) = Data.emb τ v + Data.emb τ w` using `by funext a; simp [Data.emb]`. Rewrite using `[this, hadd, hv, hw, add_zero]`.

Consider the case `smul c v _ hv`. Establish `: Data.emb τ (c • v) = τ c • Data.emb τ v` using `by funext a; simp [Data.emb]`. Rewrite using `[this, hsm, hv, mul_zero]`. Set `F : (Fin r → ℂ) →+ ℂ` to `⟨⟨f, h0⟩, hadd⟩`. Establish `hu : u = ∑ k, u k • Data.emb τ (Pi.single k (1 : E))`.

Use function extensionality and compare the values at `a`. Simplify using `[Data.emb, Finset.sum_apply, Pi.single_apply, apply_ite]`. Use `show F u = 0`. Rewrite using `[hu, map_sum]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations.

Use `show f _ = 0`. Rewrite using `[hsm, hE, mul_zero]`.
-/
theorem eq_zero_of_lattice (X : Data E r) (τ : E →+* ℂ) (f : (Fin r → ℂ) → ℂ) (φ : ℂ → ℂ)
    (hadd : ∀ u w, f (u + w) = f u + f w) (hsm : ∀ (c : ℂ) u, f (c • u) = φ c * f u)
    (h : ∀ v ∈ X.Λ, f (Data.emb τ v) = 0) (u : Fin r → ℂ) : f u = 0 := by
  classical
  have h0 : f 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    linear_combination -this
  have hE : ∀ v : Fin r → E, f (Data.emb τ v) = 0 := by
    intro v
    have hv : v ∈ Submodule.span E (X.Λ : Set (Fin r → E)) := by rw [X.Λ_span]; trivial
    induction hv using Submodule.span_induction with
    | mem v hv => exact h v hv
    | zero =>
      have : Data.emb τ (0 : Fin r → E) = 0 := by funext a; simp [Data.emb]
      rw [this, h0]
    | add v w _ _ hv hw =>
      have : Data.emb τ (v + w) = Data.emb τ v + Data.emb τ w := by funext a; simp [Data.emb]
      rw [this, hadd, hv, hw, add_zero]
    | smul c v _ hv =>
      have : Data.emb τ (c • v) = τ c • Data.emb τ v := by funext a; simp [Data.emb]
      rw [this, hsm, hv, mul_zero]
  let F : (Fin r → ℂ) →+ ℂ := ⟨⟨f, h0⟩, hadd⟩
  have hu : u = ∑ k, u k • Data.emb τ (Pi.single k (1 : E)) := by
    funext a
    simp [Data.emb, Finset.sum_apply, Pi.single_apply, apply_ite]
  show F u = 0
  rw [hu, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  show f _ = 0
  rw [hsm, hE, mul_zero]

def natPer (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (q : ℕ) (M : Matrix (Fin r) (Fin r) ℂ)
    (u : Fin r → ℂ) (n : ℕ) : ℂ :=
  if h : n < r then locPer τ G q M u ⟨n, h⟩ else 0

/- English proof (translation)
Unfold `Formalism.L2.PjFree.perFr natPer`. Rewrite using `[dif_pos h]`. Use `split_ifs with hi`. Rewrite using `[locPer_apply, if_neg (by simp)]`. Both sides reduce to the same expression.
-/
theorem perFr_mem (X : Data E r) (x : Frame X.Ψ r) (v : Fin r → E) (τ : E →+* ℂ) (h : τ ∈ X.Ψ) (i : ℕ) :
    Formalism.L2.PjFree.perFr X x v τ i = natPer τ X.Gm X.p0 (mat x ⟨τ, h⟩) (Data.emb τ v) (X.p0 + i) := by
  unfold Formalism.L2.PjFree.perFr natPer
  rw [dif_pos h]
  split_ifs with hi
  · rw [locPer_apply, if_neg (by simp)]
  · rfl

/- English proof (translation)
Use extensionality with `x`. Simplify using `[conjEmb]`.
-/
theorem conjEmb_conjEmb (τ : E →+* ℂ) : conjEmb (conjEmb τ) = τ := by
  ext x; simp [conjEmb]

/- English proof (translation)
The claim follows from `(X.cmType τ).1 h`.
-/
theorem conjEmb_not_mem (X : Data E r) {τ : E →+* ℂ} (h : τ ∈ X.Ψ) : conjEmb τ ∉ X.Ψ :=
  (X.cmType τ).1 h

/- English proof (translation)
Assume the negation of the conclusion as `h'`. Conclude with `h ((X.cmType τ).2 h')`.
-/
theorem conjEmb_mem (X : Data E r) {τ : E →+* ℂ} (h : τ ∉ X.Ψ) : conjEmb τ ∈ X.Ψ := by
  by_contra h'
  exact h ((X.cmType τ).2 h')

/- English proof (translation)
Establish `hn` using `conjEmb_not_mem X h`. Establish `e` using `conjEmb_conjEmb τ`. Generalize the expression as in `conjEmb τ = σ at hn e`. Substitute `e` using the available equality. Unfold `Formalism.L2.PjFree.perFr natPer`.

Rewrite using `[dif_neg hn, dif_pos h]`. Use `split_ifs with hj`. Rewrite using `[locPer_apply, if_pos (by simp only; omega)]`. Both sides reduce to the same expression.
-/
theorem perFr_conj (X : Data E r) (x : Frame X.Ψ r) (v : Fin r → E) (τ : E →+* ℂ) (h : τ ∈ X.Ψ) (i : ℕ)
    (hi : i < X.p0) :
    Formalism.L2.PjFree.perFr X x v (conjEmb τ) i =
      natPer τ X.Gm X.p0 (mat x ⟨τ, h⟩) (Data.emb τ v) (X.p0 - 1 - i) := by
  have hn := conjEmb_not_mem X h
  have e := conjEmb_conjEmb τ
  generalize conjEmb τ = σ at hn e
  subst e
  unfold Formalism.L2.PjFree.perFr natPer
  rw [dif_neg hn, dif_pos h]
  split_ifs with hj
  · rw [locPer_apply, if_pos (by simp only; omega)]
  · rfl

/- English proof (translation)
Establish `he : Data.emb τ ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = (a : Matrix (Fin r) (Fin r) E).map τ *ᵥ Data.emb τ v`. Use function extensionality and compare the values at `k`. Simplify using `[Data.emb, Matrix.mulVec, dotProduct, map_sum, map_mul]`. Establish `hu : IsUnit ((a : Matrix (Fin r) (Fin r) E).map τ).det`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`.

Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 a.isUnit).map τ`. Unfold `natPer`. Use `split_ifs with hn`. Rewrite using `[he, locPer_apply, locPer_apply] split_ifs`. Conclude with `h.hermC_eq τ (col M ⟨n, hn⟩) _`.

Rewrite using `[Matrix.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul_cancel_right _ _ hu]`. Both sides reduce to the same expression.
-/
theorem natPer_move {X X' : Data E r} {a : GL (Fin r) E} (h : IsMatch X X' a) (τ : E →+* ℂ) (q : ℕ)
    (M : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → E) (n : ℕ) :
    natPer τ X'.Gm q ((a : Matrix (Fin r) (Fin r) E).map τ * M)
      (Data.emb τ ((a : Matrix (Fin r) (Fin r) E) *ᵥ v)) n = natPer τ X.Gm q M (Data.emb τ v) n := by
  have he : Data.emb τ ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      (a : Matrix (Fin r) (Fin r) E).map τ *ᵥ Data.emb τ v := by
    funext k; simp [Data.emb, Matrix.mulVec, dotProduct, map_sum, map_mul]
  have hu : IsUnit ((a : Matrix (Fin r) (Fin r) E).map τ).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 a.isUnit).map τ
  unfold natPer
  split_ifs with hn
  · rw [he, locPer_apply, locPer_apply]
    split_ifs
    · exact h.hermC_eq τ (col M ⟨n, hn⟩) _
    · rw [Matrix.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul_cancel_right _ _ hu]
  · rfl

/- English proof (translation)
Establish `hq` using `X.p0_le`. Use `set q := X.p0 with hqd`. Set `K0 : ℕ → ℕ → ℂ` to `fun a c => if a < q then (if c < q then A' (q - 1 - a) (q - 1 - c) else 0) else (if c < q then 0 else A (a - q) (c - q))`. Set `K : Matrix (Fin r) (Fin r) ℂ` to `Matrix.of fun a c => K0 a c`. Establish `hK0 : ∀ a c : Fin r, ¬ ((a : ℕ) < q ↔ (c : ℕ) < q) → K a c = 0`.

Introduce `a c hac`. Simplify using `only [K, K0, Matrix.of_apply]`. Apply the tactic sequence `split_ifs <;> tauto`. Establish `hlat : ∀ v ∈ X.Λ, ∀ a, locPer τ X.Gm q M' (Data.emb τ v) a = (K *ᵥ locPer τ X.Gm q M (Data.emb τ v)) a`. Introduce `v hv a`.

Establish `e1 : (K *ᵥ locPer τ X.Gm q M (Data.emb τ v)) a = ∑ n ∈ Finset.range (q + (r - q)), K0 a n * natPer τ X.Gm q M (Data.emb τ v) n`. Rewrite using `[Nat.add_sub_cancel' hq, ← Fin.sum_univ_eq_sum_range (fun n => K0 a n * natPer τ X.Gm q M (Data.emb τ v) n)]`. Rewrite using `[Matrix.mulVec, dotProduct]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Simplify using `[natPer, K]`.

Establish `e2 : locPer τ X.Gm q M' (Data.emb τ v) a = natPer τ X.Gm q M' (Data.emb τ v) a` using `by simp [natPer]`. Rewrite using `[e1, e2, Finset.sum_range_add]`. Distinguish the cases in `ha : (a : ℕ) < q`. Use `h2 (q - 1 - a) (by omega) v hv` as an intermediate fact. Rewrite `this` using `[show q - 1 - (q - 1 - a) = a by omega]`.

Establish `z0 : ∑ j ∈ Finset.range (r - q), K0 a (q + j) * natPer τ X.Gm q M (Data.emb τ v) (q + j) = 0` using `Finset.sum_eq_zero fun j _ => by simp [K0, ha]`. Rewrite using `[this, ← Finset.sum_range_reflect, z0, add_zero]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite `hj` using `[Finset.mem_range]`. Rewrite using `[show q - 1 - (q - 1 - j) = j by omega]`.

Simplify using `[K0, ha, hj]`. Use `h1 (a - q) (by omega) v hv` as an intermediate fact. Rewrite `this` using `[show q + (a - q) = a by omega]`. Establish `z0 : ∑ j ∈ Finset.range q, K0 a j * natPer τ X.Gm q M (Data.emb τ v) j = 0` using `Finset.sum_eq_zero fun j hj => by simp [K0, ha, Finset.mem_range.1 hj]`. Rewrite using `[this, z0, zero_add]`.

Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Simplify using `[K0, ha]`. Establish `hall : ∀ u, locPer τ X.Gm q M' u = K *ᵥ locPer τ X.Gm q M u`. Introduce `u`. Use function extensionality and compare the values at `a`.

Rewrite using `[← sub_eq_zero]`. Use `eq_zero_of_lattice X τ (fun u => locPer τ X.Gm q M' u a - (K *ᵥ locPer τ X.Gm q M u) a) (fun c => if (a : ℕ) < q then conj c else c) (fun u w => ?_) (fun c u => ?_) (fun v hv => sub_eq_zero.2 (hlat v hv a)) u` and prove the remaining obligations. Simplify using `only [map_add, Matrix.mulVec_add, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `hs : ∀ (N : Matrix (Fin r) (Fin r) ℂ) (e : Fin r), locPer τ X.Gm q N (c • u) e = (if (e : ℕ) < q then conj c else c) * locPer τ X.Gm q N u e`.

Introduce `N e`. Rewrite using `[locPer_apply, locPer_apply]`. Use `split_ifs`. Rewrite using `[FD.hermC_smul_right]`. Rewrite using `[Matrix.mulVec_smul]`.

Both sides reduce to the same expression. Simplify using `only [mul_sub, hs, Matrix.mulVec, dotProduct, Finset.mul_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Distinguish the cases in `hae : ((a : ℕ) < q ↔ (e : ℕ) < q)`.

Simplify using `only [hae]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hK0 a e hae]`. Simplify using the standard rewrite rules. Take `⟨c1, c2⟩` from `loc_compare τ X.Gm X.Gm_det q M M' K hM hM' hK0 hall`.

Use `set B := M⁻¹ * M' with hB`. Establish `hBd : B.det ≠ 0`. Rewrite using `[hB, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']`. Conclude with `mul_ne_zero (inv_ne_zero hM) hM'`. Establish `hup : ∀ a c : Fin r, c < a → B a c = 0`.

Use `GlobalTheory.FibreFlag.upper_of_blocks q B hBd (fun a c hc hca => ?_) (fun a c hc hca => ?_)` and prove the remaining obligations. Rewrite using `[← c1 c a hc]`. Rewrite `hca` using `[Fin.lt_def]`. Simplify using `only [K, K0, Matrix.of_apply, if_pos hc]`. Use `split_ifs`.

Conclude with `hA' _ _ (by omega)`. Both sides reduce to the same expression. Rewrite `hca` using `[Fin.lt_def]`. Rewrite using `[← c2 a c (by omega)]`. Simplify using `only [K, K0, Matrix.of_apply]`.

Rewrite using `[if_neg (by omega), if_neg (by omega)]`. Conclude with `hA _ _ (by omega)`. Use `⟨hup, fun hd => ⟨fun i hi => ?_, fun i hi => ?_⟩⟩` and prove the remaining obligations. Set `a : Fin r` to `⟨q + i, by omega⟩`. Establish `hBu : IsUnit B.det` using `isUnit_iff_ne_zero.2 hBd`.

Establish `hinv : B⁻¹.BlockTriangular id`. Use `Matrix.invertibleOfIsUnitDet _ hBu` as an intermediate fact. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular (fun a c h => hup a c h)`. Establish `e1 : B⁻¹ a a * B a a = 1`. Use `congrFun (congrFun (Matrix.nonsing_inv_mul B hBu) a) a` as an intermediate fact.

Rewrite `this` using `[Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single a]`. Conclude with `this`. Introduce `c _ hc`. Break down `lt_or_gt_of_ne hc with h | h` into its components or cases. Rewrite using `[hinv h, zero_mul]`.

Rewrite using `[hup _ _ h, mul_zero]`. Simplify using the standard rewrite rules. Establish `e2` using `congrArg norm e1`. Rewrite `e2` using `[norm_mul, hd, mul_one, norm_one, ← c2 a a (by simp [a])]`. Simplify `e2` using `[K, K0, a]`.

Set `a : Fin r` to `⟨q - 1 - i, by omega⟩`. Establish `ha : (a : ℕ) < q` using `by simp only [a]; omega`. Establish `e2` using `hd a`. Rewrite `e2` using `[← c1 a a ha]`. Simplify using `only [K, K0, Matrix.of_apply, if_pos ha] at e2`.

Rewrite `e2` using `[show q - 1 - (a : ℕ) = i by simp only [a]; omega]`. Then use the resulting hypothesis.
-/
theorem loc_borel (X : Data E r) (τ : E →+* ℂ) (M M' : Matrix (Fin r) (Fin r) ℂ) (hM : M.det ≠ 0)
    (hM' : M'.det ≠ 0) (A A' : ℕ → ℕ → ℂ) (hA : ∀ i j, j < i → A i j = 0) (hA' : ∀ i j, j < i → A' i j = 0)
    (h1 : ∀ i < r - X.p0, ∀ v ∈ X.Λ, natPer τ X.Gm X.p0 M' (Data.emb τ v) (X.p0 + i) =
      ∑ j ∈ Finset.range (r - X.p0), A i j * natPer τ X.Gm X.p0 M (Data.emb τ v) (X.p0 + j))
    (h2 : ∀ i < X.p0, ∀ v ∈ X.Λ, natPer τ X.Gm X.p0 M' (Data.emb τ v) (X.p0 - 1 - i) =
      ∑ j ∈ Finset.range X.p0, A' i j * natPer τ X.Gm X.p0 M (Data.emb τ v) (X.p0 - 1 - j)) :
    (∀ a c : Fin r, c < a → (M⁻¹ * M') a c = 0) ∧
      ((∀ a, ‖(M⁻¹ * M') a a‖ = 1) → (∀ i < r - X.p0, ‖A i i‖ = 1) ∧ ∀ i < X.p0, ‖A' i i‖ = 1) := by
  classical
  have hq := X.p0_le
  set q := X.p0 with hqd
  let K0 : ℕ → ℕ → ℂ := fun a c =>
    if a < q then (if c < q then A' (q - 1 - a) (q - 1 - c) else 0) else (if c < q then 0 else A (a - q) (c - q))
  let K : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a c => K0 a c
  have hK0 : ∀ a c : Fin r, ¬ ((a : ℕ) < q ↔ (c : ℕ) < q) → K a c = 0 := by
    intro a c hac
    simp only [K, K0, Matrix.of_apply]
    split_ifs <;> tauto
  have hlat : ∀ v ∈ X.Λ, ∀ a, locPer τ X.Gm q M' (Data.emb τ v) a =
      (K *ᵥ locPer τ X.Gm q M (Data.emb τ v)) a := by
    intro v hv a
    have e1 : (K *ᵥ locPer τ X.Gm q M (Data.emb τ v)) a =
        ∑ n ∈ Finset.range (q + (r - q)), K0 a n * natPer τ X.Gm q M (Data.emb τ v) n := by
      rw [Nat.add_sub_cancel' hq, ← Fin.sum_univ_eq_sum_range (fun n => K0 a n * natPer τ X.Gm q M (Data.emb τ v) n)]
      rw [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp [natPer, K]
    have e2 : locPer τ X.Gm q M' (Data.emb τ v) a = natPer τ X.Gm q M' (Data.emb τ v) a := by simp [natPer]
    rw [e1, e2, Finset.sum_range_add]
    by_cases ha : (a : ℕ) < q
    · have := h2 (q - 1 - a) (by omega) v hv
      rw [show q - 1 - (q - 1 - a) = a by omega] at this
      have z0 : ∑ j ∈ Finset.range (r - q), K0 a (q + j) * natPer τ X.Gm q M (Data.emb τ v) (q + j) = 0 :=
        Finset.sum_eq_zero fun j _ => by simp [K0, ha]
      rw [this, ← Finset.sum_range_reflect, z0, add_zero]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      rw [show q - 1 - (q - 1 - j) = j by omega]
      simp [K0, ha, hj]
    · have := h1 (a - q) (by omega) v hv
      rw [show q + (a - q) = a by omega] at this
      have z0 : ∑ j ∈ Finset.range q, K0 a j * natPer τ X.Gm q M (Data.emb τ v) j = 0 :=
        Finset.sum_eq_zero fun j hj => by simp [K0, ha, Finset.mem_range.1 hj]
      rw [this, z0, zero_add]
      refine Finset.sum_congr rfl fun j hj => ?_
      simp [K0, ha]
  have hall : ∀ u, locPer τ X.Gm q M' u = K *ᵥ locPer τ X.Gm q M u := by
    intro u
    funext a
    rw [← sub_eq_zero]
    refine eq_zero_of_lattice X τ (fun u => locPer τ X.Gm q M' u a - (K *ᵥ locPer τ X.Gm q M u) a)
      (fun c => if (a : ℕ) < q then conj c else c) (fun u w => ?_) (fun c u => ?_)
      (fun v hv => sub_eq_zero.2 (hlat v hv a)) u
    · simp only [map_add, Matrix.mulVec_add, Pi.add_apply]; ring
    · have hs : ∀ (N : Matrix (Fin r) (Fin r) ℂ) (e : Fin r), locPer τ X.Gm q N (c • u) e =
          (if (e : ℕ) < q then conj c else c) * locPer τ X.Gm q N u e := by
        intro N e
        rw [locPer_apply, locPer_apply]
        split_ifs
        · rw [FD.hermC_smul_right]
        · rw [Matrix.mulVec_smul]; rfl
      simp only [mul_sub, hs, Matrix.mulVec, dotProduct, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases hae : ((a : ℕ) < q ↔ (e : ℕ) < q)
      · simp only [hae]; ring
      · rw [hK0 a e hae]; simp
  obtain ⟨c1, c2⟩ := loc_compare τ X.Gm X.Gm_det q M M' K hM hM' hK0 hall
  set B := M⁻¹ * M' with hB
  have hBd : B.det ≠ 0 := by
    rw [hB, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero (inv_ne_zero hM) hM'
  have hup : ∀ a c : Fin r, c < a → B a c = 0 := by
    refine GlobalTheory.FibreFlag.upper_of_blocks q B hBd (fun a c hc hca => ?_) (fun a c hc hca => ?_)
    · rw [← c1 c a hc]
      rw [Fin.lt_def] at hca
      simp only [K, K0, Matrix.of_apply, if_pos hc]
      split_ifs
      · exact hA' _ _ (by omega)
      · rfl
    · rw [Fin.lt_def] at hca
      rw [← c2 a c (by omega)]
      simp only [K, K0, Matrix.of_apply]
      rw [if_neg (by omega), if_neg (by omega)]
      exact hA _ _ (by omega)
  refine ⟨hup, fun hd => ⟨fun i hi => ?_, fun i hi => ?_⟩⟩
  · let a : Fin r := ⟨q + i, by omega⟩
    have hBu : IsUnit B.det := isUnit_iff_ne_zero.2 hBd
    have hinv : B⁻¹.BlockTriangular id := by
      have := Matrix.invertibleOfIsUnitDet _ hBu
      exact Matrix.blockTriangular_inv_of_blockTriangular (fun a c h => hup a c h)
    have e1 : B⁻¹ a a * B a a = 1 := by
      have := congrFun (congrFun (Matrix.nonsing_inv_mul B hBu) a) a
      rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single a] at this
      · exact this
      · intro c _ hc
        rcases lt_or_gt_of_ne hc with h | h
        · rw [hinv h, zero_mul]
        · rw [hup _ _ h, mul_zero]
      · simp
    have e2 := congrArg norm e1
    rw [norm_mul, hd, mul_one, norm_one, ← c2 a a (by simp [a])] at e2
    simpa [K, K0, a] using e2
  · let a : Fin r := ⟨q - 1 - i, by omega⟩
    have ha : (a : ℕ) < q := by simp only [a]; omega
    have e2 := hd a
    rw [← c1 a a ha] at e2
    simp only [K, K0, Matrix.of_apply, if_pos ha] at e2
    rwa [show q - 1 - (a : ℕ) = i by simp only [a]; omega] at e2

/- English proof (translation)
Introduce `E _ _ _ r X X' a h m hm1 hm2 x hx x' hx' A hA hper`. Establish `hz` using `h.mem_dom hx`. Use `set z := lact a (castFr h.psi x) with hzd`. Establish `hlat : ∀ w ∈ X'.Λ, ∃ v ∈ X.Λ, (a : Matrix (Fin r) (Fin r) E) *ᵥ v = w`. Introduce `w hw`.

Establish `e : (a : Matrix (Fin r) (Fin r) E) *ᵥ (((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w) = w`. Rewrite using `[Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Conclude with `⟨_, (h.lat _).2 (by rw [e]; exact hw), e⟩`. Establish `hloc` using `fun τ : X'.Ψ => loc_borel X' τ.1 (mat z τ) (mat x' τ) (hz τ).1 (hx' τ).1 (A τ.1) (A (conjEmb τ.1)) (hA _) (hA _) (fun i hi w hw => by`. Take `⟨v, hv, rfl⟩` from `hlat w hw`.

Establish `hm` using `hm1 τ.1 (h.mem τ)`. Rewrite `hm` using `[h.p0]`. Rewrite using `[← perFr_mem X' x' _ τ.1 τ.2, hper τ.1 i (hm ▸ hi) v hv, hm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[perFr_mem X x v τ.1 (h.mem τ), ← natPer_move h, h.p0]`.

Use the proof step `rfl)`. Use the proof step `(fun i hi w hw => by`. Take `⟨v, hv, rfl⟩` from `hlat w hw`. Establish `hm` using `hm2 _ (conjEmb_not_mem X (h.mem τ))`. Rewrite `hm` using `[h.p0]`.

Rewrite using `[← perFr_conj X' x' _ τ.1 τ.2 i hi, hper _ i (hm ▸ hi) v hv, hm]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite using `[perFr_conj X x v τ.1 (h.mem τ) j (h.p0 ▸ Finset.mem_range.1 hj), ← natPer_move h, h.p0]`. Use the proof step `rfl)`. Set `b : Frame X'.Ψ r` to `fun τ => ((mat z τ)⁻¹ * mat x' τ : Matrix (Fin r) (Fin r) ℂ)`.

Establish `hb : b ∈ Bor X'.Ψ r` using `fun τ => by`. Use `⟨?_, (hloc τ).1⟩` and prove the remaining obligations. Use `show ((mat z τ)⁻¹ * mat x' τ).det ≠ 0`. Rewrite using `[Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']`. Conclude with `mul_ne_zero (inv_ne_zero (hz τ).1) (hx' τ).1`.

Establish `hxb : x' = rmul z b`. Use function extensionality and compare the values at `τ`. Conclude with `(Matrix.mul_nonsing_inv_cancel_left (mat z τ) (mat x' τ) (isUnit_iff_ne_zero.2 (hz τ).1)).symm`. Use `⟨b, hb, hxb, fun hu hu' => ?_⟩` and prove the remaining obligations. Establish `hbd : ∀ τ i, ‖b τ i i‖ = 1`.

Introduce `τ i`. Establish `e` using `FrameDegreeData.ratio_rmul X' z hz hb τ i`. Rewrite `e` using `[← hxb, norm_div, norm_div, hu', hu', hzd, h.dmin_eq, h.dmin_eq, hu, hu, div_one, mul_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 e.symm`. Use `⟨hbd, fun τ i hi => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hτ : τ ∈ X.Ψ`. Rewrite `hi` using `[hm1 τ hτ, h.p0]`. Conclude with `((hloc ⟨τ, h.psi ▸ hτ⟩).2 (hbd _)).1 i hi`. Rewrite `hi` using `[hm2 τ hτ, h.p0]`. Use `((hloc ⟨conjEmb τ, h.psi ▸ conjEmb_mem X hτ⟩).2 (hbd _)).2 i hi` as an intermediate fact.

Rewrite `this` using `[conjEmb_conjEmb]`. Then use the resulting hypothesis.
-/
theorem borel_of_periods : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (a : GL (Fin r) E) (h : IsMatch X X' a), ∀ (m : (E →+* ℂ) → ℕ), (∀ τ ∈ X.Ψ, m τ = r - X.p0) → (∀ τ ∉ X.Ψ, m τ = X.p0) → ∀ x ∈ X.dom, ∀ x' ∈ X'.dom, ∀ (A : (E →+* ℂ) → ℕ → ℕ → ℂ), (∀ τ i j, j < i → A τ i j = 0) → (∀ τ, ∀ i < m τ, ∀ v ∈ X.Λ, Formalism.L2.PjFree.perFr X' x' ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i = ∑ j ∈ Finset.range (m τ), A τ i j * Formalism.L2.PjFree.perFr X x v τ j) → ∃ b ∈ Bor X'.Ψ r, x' = rmul (lact a (castFr h.psi x)) b ∧ (IsUnitFr X x → IsUnitFr X' x' → (∀ τ i, ‖b τ i i‖ = 1) ∧ ∀ τ, ∀ i < m τ, ‖A τ i i‖ = 1) := by
  intro E _ _ _ r X X' a h m hm1 hm2 x hx x' hx' A hA hper
  have hz := h.mem_dom hx
  set z := lact a (castFr h.psi x) with hzd
  have hlat : ∀ w ∈ X'.Λ, ∃ v ∈ X.Λ, (a : Matrix (Fin r) (Fin r) E) *ᵥ v = w := by
    intro w hw
    have e : (a : Matrix (Fin r) (Fin r) E) *ᵥ (((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    exact ⟨_, (h.lat _).2 (by rw [e]; exact hw), e⟩
  have hloc := fun τ : X'.Ψ => loc_borel X' τ.1 (mat z τ) (mat x' τ) (hz τ).1 (hx' τ).1 (A τ.1) (A (conjEmb τ.1))
    (hA _) (hA _)
    (fun i hi w hw => by
      obtain ⟨v, hv, rfl⟩ := hlat w hw
      have hm := hm1 τ.1 (h.mem τ)
      rw [h.p0] at hm
      rw [← perFr_mem X' x' _ τ.1 τ.2, hper τ.1 i (hm ▸ hi) v hv, hm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [perFr_mem X x v τ.1 (h.mem τ), ← natPer_move h, h.p0]
      rfl)
    (fun i hi w hw => by
      obtain ⟨v, hv, rfl⟩ := hlat w hw
      have hm := hm2 _ (conjEmb_not_mem X (h.mem τ))
      rw [h.p0] at hm
      rw [← perFr_conj X' x' _ τ.1 τ.2 i hi, hper _ i (hm ▸ hi) v hv, hm]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [perFr_conj X x v τ.1 (h.mem τ) j (h.p0 ▸ Finset.mem_range.1 hj), ← natPer_move h, h.p0]
      rfl)
  let b : Frame X'.Ψ r := fun τ => ((mat z τ)⁻¹ * mat x' τ : Matrix (Fin r) (Fin r) ℂ)
  have hb : b ∈ Bor X'.Ψ r := fun τ => by
    refine ⟨?_, (hloc τ).1⟩
    show ((mat z τ)⁻¹ * mat x' τ).det ≠ 0
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero (inv_ne_zero (hz τ).1) (hx' τ).1
  have hxb : x' = rmul z b := by
    funext τ
    exact (Matrix.mul_nonsing_inv_cancel_left (mat z τ) (mat x' τ) (isUnit_iff_ne_zero.2 (hz τ).1)).symm
  refine ⟨b, hb, hxb, fun hu hu' => ?_⟩
  have hbd : ∀ τ i, ‖b τ i i‖ = 1 := by
    intro τ i
    have e := FrameDegreeData.ratio_rmul X' z hz hb τ i
    rw [← hxb, norm_div, norm_div, hu', hu', hzd, h.dmin_eq, h.dmin_eq, hu, hu, div_one, mul_one] at e
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 e.symm
  refine ⟨hbd, fun τ i hi => ?_⟩
  by_cases hτ : τ ∈ X.Ψ
  · rw [hm1 τ hτ, h.p0] at hi
    exact ((hloc ⟨τ, h.psi ▸ hτ⟩).2 (hbd _)).1 i hi
  · rw [hm2 τ hτ, h.p0] at hi
    have := ((hloc ⟨conjEmb τ, h.psi ▸ conjEmb_mem X hτ⟩).2 (hbd _)).2 i hi
    rwa [conjEmb_conjEmb] at this

end GlobalTheory.PeriodBorel
