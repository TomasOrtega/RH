import ReciprocityTheory.DualLattices.LiftMonomialDeterminantStatement
import ReciprocityTheory.DualLattices.PowMemCarrier
import ReciprocityTheory.DualLattices.HasLenCokerDet

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section FrobA

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}

/- English proof (translation)
Take `⟨m, c, ⟨φ⟩, hx⟩` from `h`. Conclude with `⟨m, c, ⟨e.trans φ⟩, hx⟩`.
-/
private theorem hasLen_of_linearEquiv {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    {x : NNReal} (e : M ≃ₗ[R] M') (h : HasLen v R M' x) : HasLen v R M x := by
  obtain ⟨m, c, ⟨φ⟩, hx⟩ := h
  exact ⟨m, c, ⟨e.trans φ⟩, hx⟩

/- English proof (translation)
Rewrite `hf` using `[hbasis]`. Take `⟨r, hr⟩` from `(Submodule.mem_span_range_iff_exists_fun R).mp hf`. Use `⟨r, ?_⟩` and prove the remaining obligations. Establish `hfv : f = valM D *ᵥ (algebraMap R C ∘ r)`. Rewrite using `[← hr]`.

Use function extensionality and compare the values at `y`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, valM, Matrix.of_apply, Function.comp_apply, monX, xL, Algebra.smul_def]`. Conclude with `Finset.sum_congr rfl fun α _ => mul_comm _ _`. Rewrite using `[coefX, hfv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]`.
-/
lemma coefX_int (D : Lifts H U X) (hdet : (valM D).det ≠ 0)
    (hbasis : H.AA.carrier = Submodule.span R (Set.range fun (α : Nb p g) (y : Nb p g) =>
      ∏ j, (algebraMap R C (D.ε j) * D.u j y) ^ (α j).val))
    {f : Nb p g → C} (hf : f ∈ H.AA.carrier) :
    ∃ r : Nb p g → R, coefX D f = algebraMap R C ∘ r := by
  rw [hbasis] at hf
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hf
  refine ⟨r, ?_⟩
  have hfv : f = valM D *ᵥ (algebraMap R C ∘ r) := by
    rw [← hr]
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, valM, Matrix.of_apply,
      Function.comp_apply, monX, xL, Algebra.smul_def]
    exact Finset.sum_congr rfl fun α _ => mul_comm _ _
  rw [coefX, hfv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]

/- English proof (translation)
Simplify using `only [coefX, Matrix.mulVec_add]`.
-/
lemma coefX_add (D : Lifts H U X) (f f' : Nb p g → C) :
    coefX D (f + f') = coefX D f + coefX D f' := by
  simp only [coefX, Matrix.mulVec_add]

/- English proof (translation)
Simplify using `only [coefX, Matrix.mulVec_smul]`.
-/
lemma coefX_smul (D : Lifts H U X) (c : C) (f : Nb p g → C) :
    coefX D (c • f) = c • coefX D f := by
  simp only [coefX, Matrix.mulVec_smul]

/- English proof (translation)
Establish `hx : xL D j ∈ augIdeal H.AA.carrier` using `D.x_mem j`. Establish `hxA : xL D j ∈ H.AA.carrier` using `hx.1`. Establish `hx0 : xL D j 0 = 0` using `hx.2`. Establish `hpow : ∀ n : ℕ, xL D j ^ (n + 1) ∈ augIdeal H.AA.carrier`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => simpa using hx`. Consider the case `succ n ih`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ]`.

Conclude with `H.AA.mul_mem _ _ ih.1 hxA`. Use `show (xL D j ^ (n + 1 + 1)) 0 = 0`. Rewrite using `[Pi.pow_apply, hx0, zero_pow (by omega)]`. Establish `heq : (fun y => xL D j y ^ p) = xL D j * xL D j ^ (p - 1 - 1 + 1)`. Use function extensionality and compare the values at `y`.

Rewrite using `[Pi.mul_apply, Pi.pow_apply, ← pow_succ']`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Rewrite using `[heq]`. Conclude with `Submodule.subset_span ⟨_, hx, _, hpow _, rfl⟩`.
-/
lemma xL_pow_mem (D : Lifts H U X) (hp : 2 ≤ p) (j : Ix g) :
    (fun y => xL D j y ^ p) ∈ sqIdeal (augIdeal H.AA.carrier) := by
  have hx : xL D j ∈ augIdeal H.AA.carrier := D.x_mem j
  have hxA : xL D j ∈ H.AA.carrier := hx.1
  have hx0 : xL D j 0 = 0 := hx.2
  have hpow : ∀ n : ℕ, xL D j ^ (n + 1) ∈ augIdeal H.AA.carrier := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      refine ⟨?_, ?_⟩
      · rw [pow_succ]
        exact H.AA.mul_mem _ _ ih.1 hxA
      · show (xL D j ^ (n + 1 + 1)) 0 = 0
        rw [Pi.pow_apply, hx0, zero_pow (by omega)]
  have heq : (fun y => xL D j y ^ p) = xL D j * xL D j ^ (p - 1 - 1 + 1) := by
    funext y
    rw [Pi.mul_apply, Pi.pow_apply, ← pow_succ']
    congr 1
    omega
  rw [heq]
  exact Submodule.subset_span ⟨_, hx, _, hpow _, rfl⟩

def blockEquiv (D : Lifts H U X) (τ : Fin U.m) :
    blockL D τ ≃ₗ[R] ({l // D.κ l = τ} → R) where
  toFun c l := c.1 l.1
  invFun d := ⟨fun k => if h : D.κ k = τ then d ⟨k, h⟩ else 0, fun k hk => by simp [hk]⟩
  left_inv c := by
    apply Subtype.ext
    funext k
    by_cases h : D.κ k = τ
    · simp [h]
    · simp [h, c.2 k h]
  right_inv d := by funext l; simp [l.2]
  map_add' c c' := rfl
  map_smul' r c := rfl

end FrobA

/- English proof (translation)
Unfold `EigenLiftsFrobeniusStatement`. Introduce `p _ g C _ _ _ v R _ _ _ O _ _ σ cp hp2 hS H U X D hbasis i`. Establish `hv` using `hS.integers`. Establish `hinj : Function.Injective (algebraMap R C)` using `hv.hom_inj`. Establish `hp : 2 ≤ p` using `(Fact.out : p.Prime).two_le`.

Establish `hdet` using `h1 p g C v R O σ cp hS H U X D`. Take `⟨h2a, h2b⟩` from `h2 p g C v R O σ cp hp2 hS H U X D`. Establish `hsq : sqIdeal (augIdeal H.AA.carrier) ≤ H.AA.carrier`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨f, hf, f', hf', rfl⟩`.

Conclude with `H.AA.mul_mem _ _ hf.1 hf'.1`. Establish `hfS : ∀ j, (fun y => xL D j y ^ p) ∈ sqIdeal (augIdeal H.AA.carrier)` using `fun j => xL_pow_mem D hp j`. Establish `hrex : ∀ j : Ix g, ∃ r : Nb p g → R, coefX D (fun y => xL D j y ^ p) = algebraMap R C ∘ r` using `fun j => coefX_int D hdet hbasis (hsq (hfS j))`. Use `choose r hr using hrex`. Set `c : Ix g → Ix g → R` to `fun j k => if D.κ k = U.φ i then r j (Pi.single k 1) else 0`.

Establish `hc : ∀ j, D.κ j = i → ∀ k, algebraMap R C (c j k) = linX D (fun y => xL D j y ^ p) k`. Introduce `j hj k`. Distinguish the cases in `hk : D.κ k = U.φ i`. Simplify using `only [c, if_pos hk, linX, hr j, Function.comp_apply]`. Simplify using `only [c, if_neg hk, map_zero]`.

Conclude with `(h2a j k (by rw [hj]; exact hk)).symm`. Establish `hcard : Fintype.card {j // D.κ j = i} = Fintype.card {l // D.κ l = U.φ i}`. Rewrite using `[Fintype.card_subtype, Fintype.card_subtype, D.card_phi i]`. Set `e'' : {j // D.κ j = i} ≃ {l // D.κ l = U.φ i}` to `Fintype.equivOfCardEq hcard`. Set `eτ : {l // D.κ l = U.φ i} ≃ Fin (Fintype.card {l // D.κ l = U.φ i})` to `Fintype.equivFin _`.

Set `σE : Fin (Fintype.card {l // D.κ l = U.φ i}) ≃ {j // D.κ j = i}` to `eτ.symm.trans e''.symm`. Set `Y : Matrix (Fin (Fintype.card {l // D.κ l = U.φ i})) (Fin (Fintype.card {l // D.κ l = U.φ i})) R` to `fun a b => c (σE b).1 (eτ.symm a).1`. Set `Ψ : blockL D (U.φ i) ≃ₗ[R] (Fin (Fintype.card {l // D.κ l = U.φ i}) → R)` to `(blockEquiv D (U.φ i)).trans (LinearEquiv.funCongrLeft R R eτ.symm)`. Set `N : Submodule R (Ix g → R)` to `((LinearMap.range Y.mulVecLin).comap Ψ.toLinearMap).map (blockL D (U.φ i)).subtype`. Establish `hcomap : N.comap (blockL D (U.φ i)).subtype = (LinearMap.range Y.mulVecLin).comap Ψ.toLinearMap` using `Submodule.comap_map_eq_of_injective (blockL D (U.φ i)).injective_subtype _`.

Establish `hmapΨ : ((LinearMap.range Y.mulVecLin).comap Ψ.toLinearMap).map Ψ.toLinearMap = LinearMap.range Y.mulVecLin` using `Submodule.map_comap_eq_of_surjective Ψ.surjective _`. Establish `hlen : HasLen v R (blockL D (U.φ i) ⧸ N.comap (blockL D (U.φ i)).subtype) (v (algebraMap R C Y.det))`. Rewrite using `[hcomap]`. Conclude with `hasLen_of_linearEquiv (Submodule.Quotient.equiv _ _ Ψ hmapΨ) (Smith.hasLen_coker_det hv Y)`. Establish `hNle : N ≤ blockL D (U.φ i)` using `Submodule.map_subtype_le _ _`.

Establish `hreal : ∀ x ∈ N, ∃ f ∈ sqIdeal (augIdeal H.AA.carrier), ∀ k, algebraMap R C (x k) = linX D f k`. Introduce `x hx`. Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.mp hx`. Take `⟨w, hw⟩` from `LinearMap.mem_range.mp (Submodule.mem_comap.mp hy)`. Use `⟨∑ b, w b • (fun t => xL D (σE b).1 t ^ p), Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hfS _), ?_⟩` and prove the remaining obligations.

Introduce `k`. Establish `hyΨ : y = Ψ.symm (Y.mulVecLin w)` using `by rw [hw]; exact (Ψ.symm_apply_apply y).symm`. Establish `hyk : (y : Ix g → R) k = ∑ b, c (σE b).1 k * w b`. Rewrite using `[hyΨ]`. Distinguish the cases in `h : D.κ k = U.φ i`.

Use `show (if h' : D.κ k = U.φ i then (Y.mulVecLin w) (eτ ⟨k, h'⟩) else 0) = _`. Rewrite using `[dif_pos h]`. Use `show ∑ b, Y (eτ ⟨k, h⟩) b * w b = _`. Simplify using `only [Y, Equiv.symm_apply_apply]`. Use `show (if h' : D.κ k = U.φ i then (Y.mulVecLin w) (eτ ⟨k, h'⟩) else 0) = _`.

Rewrite using `[dif_neg h]`. Simplify using `[c, h]`. Use `show algebraMap R C ((y : Ix g → R) k) = _`. Rewrite using `[hyk, map_sum]`. Simplify using `only [linX, coefX, Matrix.mulVec_sum, Finset.sum_apply]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[← algebraMap_smul C (w b), Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_comm]`. Use `congr 1`. Conclude with `hc (σE b).1 (σE b).2 k`. Establish `hYdet : v (algebraMap R C Y.det) = X i ^ p / X (U.φ i)`.

Rewrite using `[RingHom.map_det]`. Establish `hYZ : (algebraMap R C).mapMatrix Y = (Matrix.of fun j l : {j // D.κ j = i} => linX D (fun y => xL D j.1 y ^ p) (e'' l).1)ᵀ.submatrix σE σE`. Use extensionality with `a b`. Use `show algebraMap R C (c (σE b).1 (eτ.symm a).1) = linX D (fun y => xL D (σE b).1 y ^ p) (e'' (σE a)).1`. Rewrite using `[hc (σE b).1 (σE b).2]`.

Simplify using `[σE]`. Rewrite using `[hYZ, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]`. Conclude with `h2b i e''`. Establish `hz` using `h3 p g C v R O σ cp hp2 hS H U X D hdet hbasis (U.φ i) N _ hNle hreal hlen`. Rewrite `hz` using `[hYdet]`.

Establish `hXne : X (U.φ i) ≠ 0`. Rewrite using `[← D.ε_prod (U.φ i)]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun j _ => (Valuation.ne_zero_iff v).mpr ((map_ne_zero_iff _ hinj).mpr (D.ε_ne j))`. Rewrite `hz` using `[div_le_iff₀ (pos_iff_ne_zero.mpr hXne)]`. Conclude with `hz.trans_eq (mul_comm _ _)`.
-/
theorem frob_of (h1 : LiftMonomialDeterminantStatement) (h2 : FrobeniusBlockStatement) (h3 : FrobeniusLengthBoundStatement) :
    EigenLiftsFrobeniusStatement := by
  unfold EigenLiftsFrobeniusStatement
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hp2 hS H U X D hbasis i
  have hv := hS.integers
  have hinj : Function.Injective (algebraMap R C) := hv.hom_inj
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hdet := h1 p g C v R O σ cp hS H U X D
  obtain ⟨h2a, h2b⟩ := h2 p g C v R O σ cp hp2 hS H U X D
  have hsq : sqIdeal (augIdeal H.AA.carrier) ≤ H.AA.carrier := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, hf, f', hf', rfl⟩
    exact H.AA.mul_mem _ _ hf.1 hf'.1
  have hfS : ∀ j, (fun y => xL D j y ^ p) ∈ sqIdeal (augIdeal H.AA.carrier) :=
    fun j => xL_pow_mem D hp j
  have hrex : ∀ j : Ix g, ∃ r : Nb p g → R,
      coefX D (fun y => xL D j y ^ p) = algebraMap R C ∘ r :=
    fun j => coefX_int D hdet hbasis (hsq (hfS j))
  choose r hr using hrex
  let c : Ix g → Ix g → R := fun j k => if D.κ k = U.φ i then r j (Pi.single k 1) else 0
  have hc : ∀ j, D.κ j = i → ∀ k, algebraMap R C (c j k) = linX D (fun y => xL D j y ^ p) k := by
    intro j hj k
    by_cases hk : D.κ k = U.φ i
    · simp only [c, if_pos hk, linX, hr j, Function.comp_apply]
    · simp only [c, if_neg hk, map_zero]
      exact (h2a j k (by rw [hj]; exact hk)).symm
  have hcard : Fintype.card {j // D.κ j = i} = Fintype.card {l // D.κ l = U.φ i} := by
    rw [Fintype.card_subtype, Fintype.card_subtype, D.card_phi i]
  let e'' : {j // D.κ j = i} ≃ {l // D.κ l = U.φ i} := Fintype.equivOfCardEq hcard
  let eτ : {l // D.κ l = U.φ i} ≃ Fin (Fintype.card {l // D.κ l = U.φ i}) := Fintype.equivFin _
  let σE : Fin (Fintype.card {l // D.κ l = U.φ i}) ≃ {j // D.κ j = i} := eτ.symm.trans e''.symm
  let Y : Matrix (Fin (Fintype.card {l // D.κ l = U.φ i})) (Fin (Fintype.card {l // D.κ l = U.φ i})) R :=
    fun a b => c (σE b).1 (eτ.symm a).1
  let Ψ : blockL D (U.φ i) ≃ₗ[R] (Fin (Fintype.card {l // D.κ l = U.φ i}) → R) :=
    (blockEquiv D (U.φ i)).trans (LinearEquiv.funCongrLeft R R eτ.symm)
  let N : Submodule R (Ix g → R) :=
    ((LinearMap.range Y.mulVecLin).comap Ψ.toLinearMap).map (blockL D (U.φ i)).subtype
  have hcomap : N.comap (blockL D (U.φ i)).subtype = (LinearMap.range Y.mulVecLin).comap Ψ.toLinearMap :=
    Submodule.comap_map_eq_of_injective (blockL D (U.φ i)).injective_subtype _
  have hmapΨ : ((LinearMap.range Y.mulVecLin).comap Ψ.toLinearMap).map Ψ.toLinearMap = LinearMap.range Y.mulVecLin :=
    Submodule.map_comap_eq_of_surjective Ψ.surjective _
  have hlen : HasLen v R (blockL D (U.φ i) ⧸ N.comap (blockL D (U.φ i)).subtype)
      (v (algebraMap R C Y.det)) := by
    rw [hcomap]
    exact hasLen_of_linearEquiv (Submodule.Quotient.equiv _ _ Ψ hmapΨ) (Smith.hasLen_coker_det hv Y)
  have hNle : N ≤ blockL D (U.φ i) := Submodule.map_subtype_le _ _
  have hreal : ∀ x ∈ N, ∃ f ∈ sqIdeal (augIdeal H.AA.carrier),
      ∀ k, algebraMap R C (x k) = linX D f k := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp (Submodule.mem_comap.mp hy)
    refine ⟨∑ b, w b • (fun t => xL D (σE b).1 t ^ p),
      Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hfS _), ?_⟩
    intro k
    have hyΨ : y = Ψ.symm (Y.mulVecLin w) := by rw [hw]; exact (Ψ.symm_apply_apply y).symm
    have hyk : (y : Ix g → R) k = ∑ b, c (σE b).1 k * w b := by
      rw [hyΨ]
      by_cases h : D.κ k = U.φ i
      · show (if h' : D.κ k = U.φ i then (Y.mulVecLin w) (eτ ⟨k, h'⟩) else 0) = _
        rw [dif_pos h]
        show ∑ b, Y (eτ ⟨k, h⟩) b * w b = _
        simp only [Y, Equiv.symm_apply_apply]
      · show (if h' : D.κ k = U.φ i then (Y.mulVecLin w) (eτ ⟨k, h'⟩) else 0) = _
        rw [dif_neg h]
        simp [c, h]
    show algebraMap R C ((y : Ix g → R) k) = _
    rw [hyk, map_sum]
    simp only [linX, coefX, Matrix.mulVec_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← algebraMap_smul C (w b), Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul,
      mul_comm]
    congr 1
    exact hc (σE b).1 (σE b).2 k
  have hYdet : v (algebraMap R C Y.det) = X i ^ p / X (U.φ i) := by
    rw [RingHom.map_det]
    have hYZ : (algebraMap R C).mapMatrix Y = (Matrix.of fun j l : {j // D.κ j = i} =>
        linX D (fun y => xL D j.1 y ^ p) (e'' l).1)ᵀ.submatrix σE σE := by
      ext a b
      show algebraMap R C (c (σE b).1 (eτ.symm a).1) =
        linX D (fun y => xL D (σE b).1 y ^ p) (e'' (σE a)).1
      rw [hc (σE b).1 (σE b).2]
      simp [σE]
    rw [hYZ, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]
    exact h2b i e''
  have hz := h3 p g C v R O σ cp hp2 hS H U X D hdet hbasis (U.φ i) N _ hNle hreal hlen
  rw [hYdet] at hz
  have hXne : X (U.φ i) ≠ 0 := by
    rw [← D.ε_prod (U.φ i)]
    exact Finset.prod_ne_zero_iff.mpr fun j _ =>
      (Valuation.ne_zero_iff v).mpr ((map_ne_zero_iff _ hinj).mpr (D.ε_ne j))
  rw [div_le_iff₀ (pos_iff_ne_zero.mpr hXne)] at hz
  exact hz.trans_eq (mul_comm _ _)

end ReciprocityTheory.PGsh.Up
