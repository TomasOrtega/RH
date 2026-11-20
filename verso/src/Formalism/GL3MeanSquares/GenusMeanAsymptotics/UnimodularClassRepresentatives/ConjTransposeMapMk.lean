import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomLiftBasis
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSkewValue

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.HU

open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

section

variable [Fact (IsFixF K F)]

/- English proof (translation)
The claim follows from `(conjTranspose_map _ (fun a => (star_mk 𝔭 k a).symm)).symm`.
-/
theorem conjTranspose_map_mk (𝔭 : Ideal (𝓞 F)) (k : ℕ) (Y : Matrix κ κ (𝓞 K)) :
    (Y.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)))ᴴ = Yᴴ.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) :=
  (conjTranspose_map _ (fun a => (star_mk 𝔭 k a).symm)).symm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i j`. Conclude with `Ideal.Quotient.eq.1 (congrFun (congrFun h i) j)`. Introduce `h`. Use extensionality with `i j`.

Conclude with `Ideal.Quotient.eq.2 (h i j)`.
-/
theorem map_mk_eq_iff (𝔭 : Ideal (𝓞 F)) (k : ℕ) (M N : Matrix κ κ (𝓞 K)) :
    M.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) = N.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) ↔
      ∀ i j, (M - N) i j ∈ extP K 𝔭 ^ k := by
  constructor
  · intro h i j
    exact Ideal.Quotient.eq.1 (congrFun (congrFun h i) j)
  · intro h
    ext i j
    exact Ideal.Quotient.eq.2 (h i j)

/- English proof (translation)
Rewrite using `[conjTranspose_map_mk, ← Matrix.map_mul, ← Matrix.map_mul, map_mk_eq_iff]`.
-/
theorem mk_form_iff (𝔭 : Ideal (𝓞 F)) (k : ℕ) (H Y : Matrix κ κ (𝓞 K)) :
    (Y.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)))ᴴ * Hq H 𝔭 k * Y.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) =
      Hq H 𝔭 k ↔ ∀ i j, (Yᴴ * H * Y - H) i j ∈ extP K 𝔭 ^ k := by
  rw [conjTranspose_map_mk, ← Matrix.map_mul, ← Matrix.map_mul, map_mk_eq_iff]

/- English proof (translation)
Establish `h0 : (0 : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k)) = (0 : Matrix κ κ (𝓞 K)).map (Ideal.Quotient.mk (extP K 𝔭 ^ k))`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[conjTranspose_map_mk, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add _), h0, map_mk_eq_iff, sub_zero, add_comm]`.
-/
theorem mk_sigma_iff (𝔭 : Ideal (𝓞 F)) (k : ℕ) (H Y : Matrix κ κ (𝓞 K)) :
    Hq H 𝔭 k * Y.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) +
      (Y.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)))ᴴ * Hq H 𝔭 k = 0 ↔
      ∀ i j, (Yᴴ * H + H * Y) i j ∈ extP K 𝔭 ^ k := by
  have h0 : (0 : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k)) =
      (0 : Matrix κ κ (𝓞 K)).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) := by
    ext i j
    simp
  rw [conjTranspose_map_mk, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add _), h0,
    map_mk_eq_iff, sub_zero, add_comm]

/- English proof (translation)
Use `choose Y hY using fun i j => Ideal.Quotient.mk_surjective (X i j)`. Conclude with `⟨Matrix.of Y, by ext i j; exact hY i j⟩`.
-/
theorem exists_map_mk (𝔭 : Ideal (𝓞 F)) (k : ℕ) (X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k)) :
    ∃ Y : Matrix κ κ (𝓞 K), Y.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) = X := by
  choose Y hY using fun i j => Ideal.Quotient.mk_surjective (X i j)
  exact ⟨Matrix.of Y, by ext i j; exact hY i j⟩

end

/- English proof (translation)
Rewrite using `[add_mulVec, dotProduct_add, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]`.
-/
theorem skew_mulVec {A : Type*} [CommRing A] [StarRing A] (M N : Matrix κ κ A) (u v : κ → A) :
    star (M *ᵥ u) ⬝ᵥ (N *ᵥ v) + star u ⬝ᵥ (N *ᵥ (M *ᵥ v)) = star u ⬝ᵥ ((Mᴴ * N + N * M) *ᵥ v) := by
  rw [add_mulVec, dotProduct_add, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]

/- English proof (translation)
The claim follows from `J.sum_mem fun i _ => J.mul_mem_left _ (J.sum_mem fun j _ => J.mul_mem_right _ (hM i j))`.
-/
theorem form_mem {J : Ideal (𝓞 K)} {M : Matrix κ κ (𝓞 K)} (hM : ∀ i j, M i j ∈ J) (u v : κ → 𝓞 K) :
    u ⬝ᵥ (M *ᵥ v) ∈ J :=
  J.sum_mem fun i _ => J.mul_mem_left _ (J.sum_mem fun j _ => J.mul_mem_right _ (hM i j))

/- English proof (translation)
Use `h𝔭.isPrime` as an intermediate fact. Establish `hF : IsFixF K F` using `hFF.out`. Unfold `sigmaCount`. Use `Nat.card_congr ((eL h𝔭 b j).subtypeEquiv fun X => ?_)` and prove the remaining obligations. Take `⟨Y, hXY⟩` from `exists_matrix_of_end h𝔭 b j X`.

Rewrite using `[(eL_eq_iff h𝔭 b j X Y).2 hXY, mk_sigma_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hX i l`. Establish `h1` using `hX _ _ _ _ (end_apply_cmb b j X Y hXY (Pi.single i 1)).symm (end_apply_cmb b j X Y hXY (Pi.single l 1)).symm`. Rewrite `h1` using `[congrP_iff_inP, sub_zero, coe_inA, coe_inA, coe_inA, coe_inA, form_cmb b hH, form_cmb b hH, ← map_add, skew_mulVec, form_single, inP_jK_iff h𝔭]`.

Conclude with `h1`. Introduce `hY x y x' y' hx hy`. Take `⟨c, hc⟩` from `exists_cmb h𝔭 b j (Submodule.Quotient.mk x)`. Take `⟨c', hc'⟩` from `exists_cmb h𝔭 b j (Submodule.Quotient.mk y)`. Rewrite `hx` using `[hc, end_apply_cmb b j X Y hXY c, mk_eq_iff]`.

Rewrite `hy` using `[hc', end_apply_cmb b j X Y hXY c', mk_eq_iff]`. Rewrite `hc`, `hc'` using `[mk_eq_iff]`. Rewrite using `[congrP_iff_inP, sub_zero]`. Establish `h1` using `form_congr hF b hH (inA 𝔭 b (cmb b (Y *ᵥ c))).2 y.2 hx hc'`. Establish `h2` using `form_congr hF b hH (inA 𝔭 b (cmb b c)).2 y'.2 hc hy`.

Establish `h3 : InP 𝔭 j (h (inA 𝔭 b (cmb b (Y *ᵥ c)) : V) (inA 𝔭 b (cmb b c') : V) + h (inA 𝔭 b (cmb b c) : V) (inA 𝔭 b (cmb b (Y *ᵥ c')) : V))`. Rewrite using `[coe_inA, coe_inA, coe_inA, coe_inA, form_cmb b hH, form_cmb b hH, ← map_add, skew_mulVec, inP_jK_iff h𝔭]`. Conclude with `form_mem hY _ _`. Use `(h1.add h2).add h3` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sigmaCount_basis [hFF : Fact (IsFixF K F)] (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis κ K V)
    {H : Matrix κ κ (𝓞 K)} (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (j : ℕ) :
    sigmaCount h (locF 𝔭 (spanO b)) 𝔭 j = Nat.card {Y : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ j) //
      Hq H 𝔭 j * Y + Yᴴ * Hq H 𝔭 j = 0} := by
  have := h𝔭.isPrime
  have hF : IsFixF K F := hFF.out
  unfold sigmaCount
  refine Nat.card_congr ((eL h𝔭 b j).subtypeEquiv fun X => ?_)
  obtain ⟨Y, hXY⟩ := exists_matrix_of_end h𝔭 b j X
  rw [(eL_eq_iff h𝔭 b j X Y).2 hXY, mk_sigma_iff]
  constructor
  · intro hX i l
    have h1 := hX _ _ _ _ (end_apply_cmb b j X Y hXY (Pi.single i 1)).symm
      (end_apply_cmb b j X Y hXY (Pi.single l 1)).symm
    rw [congrP_iff_inP, sub_zero, coe_inA, coe_inA, coe_inA, coe_inA, form_cmb b hH, form_cmb b hH,
      ← map_add, skew_mulVec, form_single, inP_jK_iff h𝔭] at h1
    exact h1
  · intro hY x y x' y' hx hy
    obtain ⟨c, hc⟩ := exists_cmb h𝔭 b j (Submodule.Quotient.mk x)
    obtain ⟨c', hc'⟩ := exists_cmb h𝔭 b j (Submodule.Quotient.mk y)
    rw [hc, end_apply_cmb b j X Y hXY c, mk_eq_iff] at hx
    rw [hc', end_apply_cmb b j X Y hXY c', mk_eq_iff] at hy
    rw [mk_eq_iff] at hc hc'
    rw [congrP_iff_inP, sub_zero]
    have h1 := form_congr hF b hH (inA 𝔭 b (cmb b (Y *ᵥ c))).2 y.2 hx hc'
    have h2 := form_congr hF b hH (inA 𝔭 b (cmb b c)).2 y'.2 hc hy
    have h3 : InP 𝔭 j (h (inA 𝔭 b (cmb b (Y *ᵥ c)) : V) (inA 𝔭 b (cmb b c') : V) +
        h (inA 𝔭 b (cmb b c) : V) (inA 𝔭 b (cmb b (Y *ᵥ c')) : V)) := by
      rw [coe_inA, coe_inA, coe_inA, coe_inA, form_cmb b hH, form_cmb b hH, ← map_add, skew_mulVec,
        inP_jK_iff h𝔭]
      exact form_mem hY _ _
    have := (h1.add h2).add h3
    convert this using 1
    ring

end Formalism.HermitianLattices.Ext.L3.HU
