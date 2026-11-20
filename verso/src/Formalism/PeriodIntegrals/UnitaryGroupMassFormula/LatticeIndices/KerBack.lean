import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondSplitSmul

noncomputable section

namespace MassDataIdxCore

open Matrix

variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (O : ValuationSubring K) {n : Type} [Fintype n]
  [DecidableEq n] {θ : T ≃ₐ[K] K × K} {s : T →+* T} (hs : ∀ t, θ (s t) = (θ t).swap) (J : Matrix n n T)
  (P : GL n K)

/- English proof (translation)
Conclude with `P.inv_mul`.
-/
theorem pinv_p : ((P⁻¹ : GL n K) : Matrix n n K) * (P : Matrix n n K) = 1 := by
  exact P.inv_mul

/- English proof (translation)
Conclude with `P.mul_inv`.
-/
theorem p_pinv : (P : Matrix n n K) * ((P⁻¹ : GL n K) : Matrix n n K) = 1 := by
  exact P.mul_inv

/- English proof (translation)
Rewrite using `[← Matrix.map_mul, g.mul_inv, Matrix.map_one _ (map_zero f) (map_one f)]`.
-/
theorem map_mul_inv (f : T →+* K) (g : GL n T) :
    (g : Matrix n n T).map f * ((g⁻¹ : GL n T) : Matrix n n T).map f = 1 := by
  rw [← Matrix.map_mul, g.mul_inv, Matrix.map_one _ (map_zero f) (map_one f)]

include hs in

/- English proof (translation)
Establish `ht : ∀ x, t1 θ (s x) = t2 θ x` using `fun x => by simp [t1, t2, hs]`. Establish `hg' : Formalism.UG.cT s (g : Matrix n n T) * J * (g : Matrix n n T) = J` using `hg`. Establish `h1` using `congrArg (fun M : Matrix n n T => M.map (t1 θ)) hg'`. Simplify using `only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_map, Matrix.map_map] at h1`. Establish `hcomp : (⇑(t1 θ) ∘ ⇑s) = ⇑(t2 θ)` using `funext ht`.

Rewrite `h1` using `[hcomp]`. Establish `h2` using `congrArg Matrix.transpose h1`. Simplify using `only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] at h2`. Establish `hinv : (((g⁻¹ : GL n T) : Matrix n n T).map (t1 θ))ᵀ * ((g : Matrix n n T).map (t1 θ))ᵀ = 1`. Rewrite using `[← Matrix.transpose_mul, MassDataIdxCore.map_mul_inv, Matrix.transpose_one]`.

Establish `key : (J.map (t1 θ))ᵀ * (g : Matrix n n T).map (t2 θ) = (((g⁻¹ : GL n T) : Matrix n n T).map (t1 θ))ᵀ * (J.map (t1 θ))ᵀ`. Combine the equalities or inequalities in the displayed calculation. Establish `hPP : ((P⁻¹ : GL n K) : Matrix n n K)ᵀ * (P : Matrix n n K)ᵀ = 1`. Rewrite using `[← Matrix.transpose_mul, p_pinv P, Matrix.transpose_one]`. Unfold `conjPrime₂`.

Rewrite using `[Matrix.transpose_mul, Matrix.transpose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (((P⁻¹ : GL n K) : Matrix n n K)ᵀ), hPP, Matrix.one_mul, key]`.
-/
theorem key_I (g : GL n T) (hg : g ∈ Formalism.UG.UJ s J) :
    ((P : Matrix n n K)ᵀ * (J.map (t1 θ))ᵀ) * (g : Matrix n n T).map (t2 θ) =
      (conjPrime₂ θ P g⁻¹)ᵀ * ((P : Matrix n n K)ᵀ * (J.map (t1 θ))ᵀ) := by
  have ht : ∀ x, t1 θ (s x) = t2 θ x := fun x => by simp [t1, t2, hs]
  have hg' : Formalism.UG.cT s (g : Matrix n n T) * J * (g : Matrix n n T) = J := hg
  have h1 := congrArg (fun M : Matrix n n T => M.map (t1 θ)) hg'
  simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_map, Matrix.map_map] at h1
  have hcomp : (⇑(t1 θ) ∘ ⇑s) = ⇑(t2 θ) := funext ht
  rw [hcomp] at h1
  have h2 := congrArg Matrix.transpose h1
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] at h2
  have hinv : (((g⁻¹ : GL n T) : Matrix n n T).map (t1 θ))ᵀ * ((g : Matrix n n T).map (t1 θ))ᵀ = 1 := by
    rw [← Matrix.transpose_mul, MassDataIdxCore.map_mul_inv, Matrix.transpose_one]
  have key : (J.map (t1 θ))ᵀ * (g : Matrix n n T).map (t2 θ) =
      (((g⁻¹ : GL n T) : Matrix n n T).map (t1 θ))ᵀ * (J.map (t1 θ))ᵀ := by
    calc (J.map (t1 θ))ᵀ * (g : Matrix n n T).map (t2 θ)
        = ((((g⁻¹ : GL n T) : Matrix n n T).map (t1 θ))ᵀ * ((g : Matrix n n T).map (t1 θ))ᵀ) *
          ((J.map (t1 θ))ᵀ * (g : Matrix n n T).map (t2 θ)) := by rw [hinv, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, h2]
  have hPP : ((P⁻¹ : GL n K) : Matrix n n K)ᵀ * (P : Matrix n n K)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, p_pinv P, Matrix.transpose_one]
  unfold conjPrime₂
  rw [Matrix.transpose_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (((P⁻¹ : GL n K) : Matrix n n K)ᵀ), hPP, Matrix.one_mul, key]

include hs in
/- English proof (translation)
Introduce `c g hg hL hc y hy`. Establish `hsm : ∀ (a : K) (t : T), t1 θ (a • t) = a * t1 θ t` using `fun a t => by simp [t1]`. Establish `hsm2 : ∀ (a : K) (t : T), t2 θ (a • t) = a * t2 θ t` using `fun a t => by simp [t2]`. Establish `hint : ∀ W : Matrix n n K, (∀ i j, W i j ∈ O) → ∀ v : n → K, IntV O v → IntV O (W *ᵥ v)`. Introduce `W hW v hv i`.

Conclude with `sum_mem (fun j _ => mul_mem (hW i j) (hv j))`. Establish `m1 : ∀ (A : Matrix n n T) (x : n → T), (fun j => t1 θ ((A *ᵥ x) j)) = A.map (t1 θ) *ᵥ fun j => t1 θ (x j)`. Introduce `A x`. Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec _ _ _ i`.

Establish `m2 : ∀ (A : Matrix n n T) (x : n → T), (fun j => t2 θ ((A *ᵥ x) j)) = A.map (t2 θ) *ᵥ fun j => t2 θ (x j)`. Introduce `A x`. Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec _ _ _ i`. Establish `lat_sub : ∀ x x', x ∈ Lat O θ J P → x' ∈ Lat O θ J P → x - x' ∈ Lat O θ J P`.

Introduce `x x' hx hx'`. Unfold `Lat at hx hx' ⊢`. Simplify using `only [Set.mem_setOf_eq] at hx hx' ⊢`. Prove the components needed by the constructor for the conclusion. Establish `e : (fun j => t1 θ ((x - x') j)) = (fun j => t1 θ (x j)) - fun j => t1 θ (x' j)`.

Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules. Rewrite using `[e, Matrix.mulVec_sub]`. Conclude with `fun i => sub_mem (hx.1 i) (hx'.1 i)`. Establish `e : (fun j => t2 θ ((x - x') j)) = (fun j => t2 θ (x j)) - fun j => t2 θ (x' j)`.

Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules. Rewrite using `[e, Matrix.mulVec_sub]`. Conclude with `fun i => sub_mem (hx.2 i) (hx'.2 i)`. Establish `hy'` using `hy`.

Unfold `Lat at hy'`. Simplify using `only [Set.mem_setOf_eq] at hy'`. Establish `hginv : ∀ x ∈ Lat O θ J P, ((g⁻¹ : GL n T) : Matrix n n T) *ᵥ x ∈ Lat O θ J P`. Introduce `x hx`. Apply `(hL _).mpr` to reduce the goal to its premises.

Rewrite using `[Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Conclude with `hx`. Establish `hVint` using `ker_fwd (O := O) (θ := θ) (J := J) (P := P) 1 g⁻¹ (fun x hx => ⟨((g⁻¹ : GL n T) : Matrix n n T) *ᵥ x - x, lat_sub _ _ (hginv x hx) hx, by`. Rewrite using `[one_smul, Matrix.sub_mulVec, Matrix.one_mulVec]⟩)`. Establish `hV : ∀ i j, conjPrime₂ θ P g⁻¹ i j ∈ O`.

Introduce `i j`. Take `⟨w, hw, e⟩` from `hVint i j`. Establish `e2 : conjPrime₂ θ P g⁻¹ i j = (1 : Matrix n n K) i j + w`. Rewrite using `[← one_mul w, ← e]`. Simplify using the standard rewrite rules.

Rewrite using `[e2]`. Use `add_mem ?_ hw` and prove the remaining obligations. Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Conclude with `one_mem O`.

Conclude with `zero_mem O`. Use `choose W hWO hW using hc`. Establish `hWm : conjPrime₂ θ P g - 1 = c • Matrix.of W`. Use extensionality with `i j`. Simplify using `[hW i j]`.

Establish `hV1 : conjPrime₂ θ P g⁻¹ * conjPrime₂ θ P g = 1`. Rewrite using `[← conjP_mul, inv_mul_cancel, conjP_one]`. Establish `hW'm : conjPrime₂ θ P g⁻¹ - 1 = c • (-(conjPrime₂ θ P g⁻¹ * Matrix.of W))`. Rewrite using `[smul_neg, ← Matrix.mul_smul, ← hWm, Matrix.mul_sub, hV1, Matrix.mul_one]`. Normalize the expressions using the abelian group laws.

Establish `hW'O : ∀ i j, (-(conjPrime₂ θ P g⁻¹ * Matrix.of W)) i j ∈ O`. Introduce `i j`. Simplify using `only [Matrix.neg_apply, Matrix.mul_apply, Matrix.of_apply]`. Conclude with `neg_mem (sum_mem (fun k _ => mul_mem (hV i k) (hWO k j)))`. Establish `E1m : ((P⁻¹ : GL n K) : Matrix n n K) * ((g : Matrix n n T) - 1).map (t1 θ) = (conjPrime₂ θ P g - 1) * ((P⁻¹ : GL n K) : Matrix n n K)`.

Unfold `conjPrime₂`. Rewrite using `[Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]`. Simplify using `only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, p_pinv P]`. Establish `E2m : ((P : Matrix n n K)ᵀ * (J.map (t1 θ))ᵀ) * ((g : Matrix n n T) - 1).map (t2 θ) = (conjPrime₂ θ P g⁻¹ - 1)ᵀ * ((P : Matrix n n K)ᵀ * (J.map (t1 θ))ᵀ)`. Rewrite using `[Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_sub, key_I hs J P g hg, Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]`.

Establish `hv1 : ((P⁻¹ : GL n K) : Matrix n n K) *ᵥ (fun j => t1 θ ((((g : Matrix n n T) - 1) *ᵥ y) j)) = (conjPrime₂ θ P g - 1) *ᵥ (((P⁻¹ : GL n K) : Matrix n n K) *ᵥ fun j => t1 θ (y j))`. Rewrite using `[m1, Matrix.mulVec_mulVec, E1m, ← Matrix.mulVec_mulVec]`. Establish `hv2 : ((P : Matrix n n K)ᵀ * (J.map (t1 θ))ᵀ) *ᵥ (fun j => t2 θ ((((g : Matrix n n T) - 1) *ᵥ y) j)) = (conjPrime₂ θ P g⁻¹ - 1)ᵀ *ᵥ (((P : Matrix n n K)ᵀ * (J.map (t1 θ))ᵀ) *ᵥ fun j => t2 θ (y j))`. Rewrite using `[m2, Matrix.mulVec_mulVec, E2m, ← Matrix.mulVec_mulVec]`. Distinguish the cases in `hc0 : c = 0`.

Substitute `hc0` using the available equality. Establish `hM : IsUnit ((P : Matrix n n K)ᵀ * (J.map (t1 θ))ᵀ).det`. Establish `hJ1 : (J.map (t1 θ)).det = t1 θ J.det` using `(RingHom.map_det (t1 θ) J).symm`. Rewrite using `[Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose, hJ1]`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).mp P.isUnit).mul (hJu.map _)`.

Establish `a1z : (fun j => t1 θ ((((g : Matrix n n T) - 1) *ᵥ y) j)) = 0`. Establish `h0 : ((P⁻¹ : GL n K) : Matrix n n K) *ᵥ (fun j => t1 θ ((((g : Matrix n n T) - 1) *ᵥ y) j)) = 0`. Rewrite using `[hv1, hWm, zero_smul, Matrix.zero_mulVec]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[p_pinv P, Matrix.one_mulVec]`.

Use `_ = 0 := by rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]`. Establish `a2z : (fun j => t2 θ ((((g : Matrix n n T) - 1) *ᵥ y) j)) = 0`. Establish `h0 : ((P : Matrix n n K)ᵀ * (J.map (t1 θ))ᵀ) *ᵥ (fun j => t2 θ ((((g : Matrix n n T) - 1) *ᵥ y) j)) = 0`. Rewrite using `[hv2, hW'm, zero_smul, Matrix.transpose_zero, Matrix.zero_mulVec]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.nonsing_inv_mul _ hM, Matrix.one_mulVec]`. Use `_ = 0 := by rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]`. Establish `hv0 : ((g : Matrix n n T) - 1) *ᵥ y = 0`. Use function extensionality and compare the values at `j`. Apply `θ.injective` to reduce the goal to its premises.

Establish `e1` using `congrFun a1z j`. Establish `e2` using `congrFun a2z j`. Simplify using `only [t1, t2, Pi.zero_apply, RingHom.comp_apply, RingHom.coe_fst, RingHom.coe_snd, AlgEquiv.toAlgHom_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.coe_coe] at e1 e2`. Use `ext`. Simplify using `using e1`.

Simplify using `using e2`. Conclude with `⟨0, by simpa using lat_sub y y hy hy, by rw [hv0, smul_zero]⟩`. Use `⟨c⁻¹ • (((g : Matrix n n T) - 1) *ᵥ y), ?_, by` and prove the remaining obligations. Rewrite using `[smul_smul, mul_inv_cancel₀ hc0, one_smul]⟩`. Establish `s1 : (fun j => t1 θ ((c⁻¹ • (((g : Matrix n n T) - 1) *ᵥ y)) j)) = c⁻¹ • fun j => t1 θ ((((g : Matrix n n T) - 1) *ᵥ y) j)`.

Use function extensionality and compare the values at `j`. Simplify using `only [Pi.smul_apply, hsm, smul_eq_mul]`. Establish `s2 : (fun j => t2 θ ((c⁻¹ • (((g : Matrix n n T) - 1) *ᵥ y)) j)) = c⁻¹ • fun j => t2 θ ((((g : Matrix n n T) - 1) *ᵥ y) j)`. Use function extensionality and compare the values at `j`. Simplify using `only [Pi.smul_apply, hsm2, smul_eq_mul]`.

Unfold `Lat`. Simplify using `only [Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[s1, Matrix.mulVec_smul, hv1, hWm, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ hc0, one_smul]`. Conclude with `hint _ hWO _ hy'.1`.

Rewrite using `[s2, Matrix.mulVec_smul, hv2, hW'm, Matrix.transpose_smul, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ hc0, one_smul]`. Conclude with `hint _ (fun i j => hW'O j i) _ hy'.2`.
-/
theorem kerBack (hJu : IsUnit J.det) : KerBack O θ s J P := by
  intro c g hg hL hc y hy
  have hsm : ∀ (a : K) (t : T), t1 θ (a • t) = a * t1 θ t := fun a t => by simp [t1]
  have hsm2 : ∀ (a : K) (t : T), t2 θ (a • t) = a * t2 θ t := fun a t => by simp [t2]
  have hint : ∀ W : Matrix n n K, (∀ i j, W i j ∈ O) → ∀ v : n → K, IntV O v →
      IntV O (W *ᵥ v) := by
    intro W hW v hv i
    exact sum_mem (fun j _ => mul_mem (hW i j) (hv j))
  have m1 : ∀ (A : Matrix n n T) (x : n → T),
      (fun j => t1 θ ((A *ᵥ x) j)) = A.map (t1 θ) *ᵥ fun j => t1 θ (x j) := by
    intro A x
    funext i
    exact RingHom.map_mulVec _ _ _ i
  have m2 : ∀ (A : Matrix n n T) (x : n → T),
      (fun j => t2 θ ((A *ᵥ x) j)) = A.map (t2 θ) *ᵥ fun j => t2 θ (x j) := by
    intro A x
    funext i
    exact RingHom.map_mulVec _ _ _ i
  have lat_sub : ∀ x x', x ∈ Lat O θ J P → x' ∈ Lat O θ J P → x - x' ∈ Lat O θ J P := by
    intro x x' hx hx'
    unfold Lat at hx hx' ⊢
    simp only [Set.mem_setOf_eq] at hx hx' ⊢
    constructor
    · have e : (fun j => t1 θ ((x - x') j)) = (fun j => t1 θ (x j)) - fun j => t1 θ (x' j) := by
        funext j
        simp
      rw [e, Matrix.mulVec_sub]
      exact fun i => sub_mem (hx.1 i) (hx'.1 i)
    · have e : (fun j => t2 θ ((x - x') j)) = (fun j => t2 θ (x j)) - fun j => t2 θ (x' j) := by
        funext j
        simp
      rw [e, Matrix.mulVec_sub]
      exact fun i => sub_mem (hx.2 i) (hx'.2 i)
  have hy' := hy
  unfold Lat at hy'
  simp only [Set.mem_setOf_eq] at hy'
  have hginv : ∀ x ∈ Lat O θ J P, ((g⁻¹ : GL n T) : Matrix n n T) *ᵥ x ∈ Lat O θ J P := by
    intro x hx
    apply (hL _).mpr
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    exact hx
  have hVint := ker_fwd (O := O) (θ := θ) (J := J) (P := P) 1 g⁻¹ (fun x hx =>
    ⟨((g⁻¹ : GL n T) : Matrix n n T) *ᵥ x - x, lat_sub _ _ (hginv x hx) hx, by
      rw [one_smul, Matrix.sub_mulVec, Matrix.one_mulVec]⟩)
  have hV : ∀ i j, conjPrime₂ θ P g⁻¹ i j ∈ O := by
    intro i j
    obtain ⟨w, hw, e⟩ := hVint i j
    have e2 : conjPrime₂ θ P g⁻¹ i j = (1 : Matrix n n K) i j + w := by
      rw [← one_mul w, ← e]
      simp
    rw [e2]
    refine add_mem ?_ hw
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem O
    · exact zero_mem O
  choose W hWO hW using hc
  have hWm : conjPrime₂ θ P g - 1 = c • Matrix.of W := by
    ext i j
    simp [hW i j]
  have hV1 : conjPrime₂ θ P g⁻¹ * conjPrime₂ θ P g = 1 := by
    rw [← conjP_mul, inv_mul_cancel, conjP_one]
  have hW'm : conjPrime₂ θ P g⁻¹ - 1 = c • (-(conjPrime₂ θ P g⁻¹ * Matrix.of W)) := by
    rw [smul_neg, ← Matrix.mul_smul, ← hWm, Matrix.mul_sub, hV1, Matrix.mul_one]
    abel
  have hW'O : ∀ i j, (-(conjPrime₂ θ P g⁻¹ * Matrix.of W)) i j ∈ O := by
    intro i j
    simp only [Matrix.neg_apply, Matrix.mul_apply, Matrix.of_apply]
    exact neg_mem (sum_mem (fun k _ => mul_mem (hV i k) (hWO k j)))
  have E1m : ((P⁻¹ : GL n K) : Matrix n n K) * ((g : Matrix n n T) - 1).map (t1 θ) = (conjPrime₂ θ P g - 1) * ((P⁻¹ : GL n K) : Matrix n n K) := by
    unfold conjPrime₂
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc,
      p_pinv P]
  have E2m : ((P : Matrix n n K)ᵀ * (J.map (t1 θ))ᵀ) * ((g : Matrix n n T) - 1).map (t2 θ) =
      (conjPrime₂ θ P g⁻¹ - 1)ᵀ * ((P : Matrix n n K)ᵀ * (J.map (t1 θ))ᵀ) := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_sub, key_I hs J P g hg,
      Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
  have hv1 : ((P⁻¹ : GL n K) : Matrix n n K) *ᵥ (fun j => t1 θ ((((g : Matrix n n T) - 1) *ᵥ y) j)) =
      (conjPrime₂ θ P g - 1) *ᵥ (((P⁻¹ : GL n K) : Matrix n n K) *ᵥ fun j => t1 θ (y j)) := by
    rw [m1, Matrix.mulVec_mulVec, E1m, ← Matrix.mulVec_mulVec]
  have hv2 : ((P : Matrix n n K)ᵀ * (J.map (t1 θ))ᵀ) *ᵥ (fun j => t2 θ ((((g : Matrix n n T) - 1) *ᵥ y) j)) =
      (conjPrime₂ θ P g⁻¹ - 1)ᵀ *ᵥ (((P : Matrix n n K)ᵀ * (J.map (t1 θ))ᵀ) *ᵥ fun j => t2 θ (y j)) := by
    rw [m2, Matrix.mulVec_mulVec, E2m, ← Matrix.mulVec_mulVec]
  by_cases hc0 : c = 0
  · subst hc0
    have hM : IsUnit ((P : Matrix n n K)ᵀ * (J.map (t1 θ))ᵀ).det := by
      have hJ1 : (J.map (t1 θ)).det = t1 θ J.det := (RingHom.map_det (t1 θ) J).symm
      rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose, hJ1]
      exact ((Matrix.isUnit_iff_isUnit_det _).mp P.isUnit).mul (hJu.map _)
    have a1z : (fun j => t1 θ ((((g : Matrix n n T) - 1) *ᵥ y) j)) = 0 := by
      have h0 : ((P⁻¹ : GL n K) : Matrix n n K) *ᵥ (fun j => t1 θ ((((g : Matrix n n T) - 1) *ᵥ y) j)) = 0 := by
        rw [hv1, hWm, zero_smul, Matrix.zero_mulVec]
      calc _ = ((P : Matrix n n K) * ((P⁻¹ : GL n K) : Matrix n n K)) *ᵥ
            (fun j => t1 θ ((((g : Matrix n n T) - 1) *ᵥ y) j)) := by
            rw [p_pinv P, Matrix.one_mulVec]
        _ = 0 := by rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
    have a2z : (fun j => t2 θ ((((g : Matrix n n T) - 1) *ᵥ y) j)) = 0 := by
      have h0 : ((P : Matrix n n K)ᵀ * (J.map (t1 θ))ᵀ) *ᵥ (fun j => t2 θ ((((g : Matrix n n T) - 1) *ᵥ y) j)) = 0 := by
        rw [hv2, hW'm, zero_smul, Matrix.transpose_zero, Matrix.zero_mulVec]
      calc _ = (((P : Matrix n n K)ᵀ * (J.map (t1 θ))ᵀ)⁻¹ * ((P : Matrix n n K)ᵀ * (J.map (t1 θ))ᵀ)) *ᵥ
            (fun j => t2 θ ((((g : Matrix n n T) - 1) *ᵥ y) j)) := by
            rw [Matrix.nonsing_inv_mul _ hM, Matrix.one_mulVec]
        _ = 0 := by rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
    have hv0 : ((g : Matrix n n T) - 1) *ᵥ y = 0 := by
      funext j
      apply θ.injective
      have e1 := congrFun a1z j
      have e2 := congrFun a2z j
      simp only [t1, t2, Pi.zero_apply, RingHom.comp_apply, RingHom.coe_fst, RingHom.coe_snd,
        AlgEquiv.toAlgHom_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.coe_coe] at e1 e2
      ext
      · simpa using e1
      · simpa using e2
    exact ⟨0, by simpa using lat_sub y y hy hy, by rw [hv0, smul_zero]⟩
  · refine ⟨c⁻¹ • (((g : Matrix n n T) - 1) *ᵥ y), ?_, by
      rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]⟩
    have s1 : (fun j => t1 θ ((c⁻¹ • (((g : Matrix n n T) - 1) *ᵥ y)) j)) =
        c⁻¹ • fun j => t1 θ ((((g : Matrix n n T) - 1) *ᵥ y) j) := by
      funext j
      simp only [Pi.smul_apply, hsm, smul_eq_mul]
    have s2 : (fun j => t2 θ ((c⁻¹ • (((g : Matrix n n T) - 1) *ᵥ y)) j)) =
        c⁻¹ • fun j => t2 θ ((((g : Matrix n n T) - 1) *ᵥ y) j) := by
      funext j
      simp only [Pi.smul_apply, hsm2, smul_eq_mul]
    unfold Lat
    simp only [Set.mem_setOf_eq]
    constructor
    · rw [s1, Matrix.mulVec_smul, hv1, hWm, Matrix.smul_mulVec, smul_smul,
        inv_mul_cancel₀ hc0, one_smul]
      exact hint _ hWO _ hy'.1
    · rw [s2, Matrix.mulVec_smul, hv2, hW'm, Matrix.transpose_smul, Matrix.smul_mulVec,
        smul_smul, inv_mul_cancel₀ hc0, one_smul]
      exact hint _ (fun i j => hW'O j i) _ hy'.2

end MassDataIdxCore
