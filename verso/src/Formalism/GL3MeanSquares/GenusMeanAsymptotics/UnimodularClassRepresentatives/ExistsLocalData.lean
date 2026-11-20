import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensitySixth
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityEighth
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.VdEqZeroOfNotLe
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapConjO

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.localValuationFiltration

open HermitianSublattices LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans traceDeterminantCongruences reductionMapsOfForms

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

/- English proof (translation)
Use `⟨Ideal.absNorm (Ideal.span {n}), fun e he => ?_⟩` and prove the remaining obligations. Establish `h1 : 𝔭 ^ e ∣ Ideal.span {n}` using `Ideal.dvd_span_singleton.mpr he`. Establish `h2 : Ideal.absNorm (𝔭 ^ e) ∣ Ideal.absNorm (Ideal.span {n})` using `map_dvd Ideal.absNorm h1`. Establish `h3 : Ideal.absNorm (Ideal.span {n}) ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`.

Conclude with `hn`. Establish `h4` using `Nat.le_of_dvd (Nat.pos_of_ne_zero h3) h2`. Rewrite `h4` using `[map_pow]`. Establish `h5 : Ideal.absNorm 𝔭 ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`.

Conclude with `idealPowerSpanBounds.ne_bot h𝔭`. Establish `h6 : Ideal.absNorm 𝔭 ≠ 1`. Rewrite using `[Ne, Ideal.absNorm_eq_one_iff]`. Conclude with `h𝔭.ne_top`. Establish `h7 : 2 ≤ Ideal.absNorm 𝔭` using `by omega`.

Establish `h8 : e < 2 ^ e` using `by first`. Consider the case `exact Nat.lt_two_pow_self`. Consider the case `exact Nat.lt_two_pow e`. Consider the case `exact Nat.lt_pow_self (by norm_num) e`. Consider the case `exact Nat.lt_pow_self (by norm_num)`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem bddAbove_vF {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) :
    BddAbove {e : ℕ | n ∈ 𝔭 ^ e} := by
  refine ⟨Ideal.absNorm (Ideal.span {n}), fun e he => ?_⟩
  have h1 : 𝔭 ^ e ∣ Ideal.span {n} := Ideal.dvd_span_singleton.mpr he
  have h2 : Ideal.absNorm (𝔭 ^ e) ∣ Ideal.absNorm (Ideal.span {n}) := map_dvd Ideal.absNorm h1
  have h3 : Ideal.absNorm (Ideal.span {n}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hn
  have h4 := Nat.le_of_dvd (Nat.pos_of_ne_zero h3) h2
  rw [map_pow] at h4
  have h5 : Ideal.absNorm 𝔭 ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact idealPowerSpanBounds.ne_bot h𝔭
  have h6 : Ideal.absNorm 𝔭 ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact h𝔭.ne_top
  have h7 : 2 ≤ Ideal.absNorm 𝔭 := by omega
  have h8 : e < 2 ^ e := by
    first
    | exact Nat.lt_two_pow_self
    | exact Nat.lt_two_pow e
    | exact Nat.lt_pow_self (by norm_num) e
    | exact Nat.lt_pow_self (by norm_num)
  calc e ≤ 2 ^ e := h8.le
    _ ≤ Ideal.absNorm 𝔭 ^ e := Nat.pow_le_pow_left h7 e
    _ ≤ _ := h4

/- English proof (translation)
Introduce `h`. Establish `h1` using `le_csSup (bddAbove_vF h𝔭 hn) (show vF 𝔭 n + 1 ∈ {e : ℕ | n ∈ 𝔭 ^ e} from h)`. Express the relevant statement in the definitionally equal form `vF 𝔭 n + 1 ≤ vF 𝔭 n at h1`. Use linear arithmetic over natural numbers and integers.
-/
theorem notMem_pow_vF {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) :
    n ∉ 𝔭 ^ (vF 𝔭 n + 1) := by
  intro h
  have h1 := le_csSup (bddAbove_vF h𝔭 hn) (show vF 𝔭 n + 1 ∈ {e : ℕ | n ∈ 𝔭 ^ e} from h)
  change vF 𝔭 n + 1 ≤ vF 𝔭 n at h1
  omega

/- English proof (translation)
The claim follows from `Nat.sSup_mem ⟨0, by simp⟩ (bddAbove_vF h𝔭 hn)`.
-/
theorem mem_pow_vF {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) :
    n ∈ 𝔭 ^ vF 𝔭 n := Nat.sSup_mem ⟨0, by simp⟩ (bddAbove_vF h𝔭 hn)

/- English proof (translation)
Establish `hy : (y : V) = ∑ i, algebraMap (𝓞 K) K (crd b y i) • b i` using `by conv_lhs => rw [← (bO b).sum_equivFun y]`. Rewrite using `[Submodule.coe_sum]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, algebraMap_smul]`. Use `congr 1`.

Simplify using `only [bO, Basis.span_apply]`. Rewrite using `[hy, map_sum]`. Simplify using `only [map_smul, Basis.repr_self, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
theorem repr_coe {κ : Type} [Fintype κ] [DecidableEq κ] (b : Basis κ K V) (y : spanO b) (j : κ) :
    b.repr (y : V) j = algebraMap (𝓞 K) K (crd b y j) := by
  have hy : (y : V) = ∑ i, algebraMap (𝓞 K) K (crd b y i) • b i := by
    conv_lhs => rw [← (bO b).sum_equivFun y]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Submodule.coe_smul, algebraMap_smul]
    congr 1
    simp only [bO, Basis.span_apply]
  rw [hy, map_sum]
  simp only [map_smul, Basis.repr_self, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/- English proof (translation)
Take `⟨b, hbL, hb⟩` from `exists_basis_locF hL h𝔭`. Take `⟨H, hH, hdet⟩` from `LocF.exists_gram hLi b hbL`. Establish `hHH : Hᴴ = H`. Use extensionality with `i j`. Use `show algebraMap (𝓞 K) K (star (H j i)) = algebraMap (𝓞 K) K (H i j)`.

Rewrite using `[hH, star_def]`. Use `show star (algebraMap (𝓞 K) K (H j i)) = _`. Rewrite using `[hH]`. Conclude with `hs.eq _ _`. Take `⟨D, hD⟩` from `(conjO_eq_iff_mem_range hF H.det).1 (by`.

Rewrite using `[← star_def, ← det_conjTranspose, hHH])`. Establish `hD0 : D ≠ 0`. Introduce and unpack `rfl`. Apply `LocF.gram_det_ne_zero h (LocF.aniso_of_totPosDef hd) b b.linearIndependent` to reduce the goal to its premises. Rewrite using `[← hdet, ← hD, map_zero, map_zero]`.

Use `⟨b, H, D, hb, hH, hHH, hD.symm, hD0, ?_⟩` and prove the remaining obligations. Rewrite using `[← vd_locF hF h L h𝔭, ← hb, vd_locF hF h _ h𝔭]`. Unfold `vd vF`. Use `congr 1`. Use extensionality with `e`.

Simplify using `only [Set.mem_ofPred_eq]`. Rewrite using `[← mem_pow_iff (K := K), hD]`. Prove the components needed by the constructor for the conclusion. Introduce `hle`. Conclude with `hle (Ideal.subset_span ⟨b, fun i => Submodule.subset_span ⟨i, rfl⟩, hdet⟩)`.

Introduce `hmem`. Use `BallB.discrIdeal_le b fun x hx z hz => ?_` and prove the remaining obligations. Establish `hx' : b.det x = algebraMap (𝓞 K) K (Matrix.of fun i j => crd b ⟨x j, hx j⟩ i).det`. Rewrite using `[Basis.det_apply, RingHom.map_det]`. Use `congr 1`.

Use extensionality with `i j`. Conclude with `repr_coe b ⟨x j, hx j⟩ i`. Establish `: z = star (Matrix.of fun i j => crd b ⟨x j, hx j⟩ i).det * H.det * (Matrix.of fun i j => crd b ⟨x j, hx j⟩ i).det`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Rewrite using `[hz, hx', BallB.gdet, ← hdet]`.

Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hmem)`.
-/
theorem exists_local_data (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L)
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ (b : Basis (Fin (finrank K V)) K V) (H : Matrix (Fin (finrank K V)) (Fin (finrank K V)) (𝓞 K))
      (D : 𝓞 F), locF 𝔭 (spanO b) = locF 𝔭 L ∧ (∀ i j, algebraMap (𝓞 K) K (H i j) = h (b i) (b j)) ∧
        Hᴴ = H ∧ H.det = ι D ∧ D ≠ 0 ∧ vd h L 𝔭 = vF 𝔭 D := by
  obtain ⟨b, hbL, hb⟩ := exists_basis_locF hL h𝔭
  obtain ⟨H, hH, hdet⟩ := LocF.exists_gram hLi b hbL
  have hHH : Hᴴ = H := by
    ext i j
    show algebraMap (𝓞 K) K (star (H j i)) = algebraMap (𝓞 K) K (H i j)
    rw [hH, star_def]
    show star (algebraMap (𝓞 K) K (H j i)) = _
    rw [hH]
    exact hs.eq _ _
  obtain ⟨D, hD⟩ := (conjO_eq_iff_mem_range hF H.det).1 (by
    rw [← star_def, ← det_conjTranspose, hHH])
  have hD0 : D ≠ 0 := by
    rintro rfl
    apply LocF.gram_det_ne_zero h (LocF.aniso_of_totPosDef hd) b b.linearIndependent
    rw [← hdet, ← hD, map_zero, map_zero]
  refine ⟨b, H, D, hb, hH, hHH, hD.symm, hD0, ?_⟩
  rw [← vd_locF hF h L h𝔭, ← hb, vd_locF hF h _ h𝔭]
  unfold vd vF
  congr 1
  ext e
  simp only [Set.mem_ofPred_eq]
  rw [← mem_pow_iff (K := K), hD]
  constructor
  · intro hle
    exact hle (Ideal.subset_span ⟨b, fun i => Submodule.subset_span ⟨i, rfl⟩, hdet⟩)
  · intro hmem
    refine BallB.discrIdeal_le b fun x hx z hz => ?_
    have hx' : b.det x = algebraMap (𝓞 K) K (Matrix.of fun i j => crd b ⟨x j, hx j⟩ i).det := by
      rw [Basis.det_apply, RingHom.map_det]
      congr 1
      ext i j
      exact repr_coe b ⟨x j, hx j⟩ i
    have : z = star (Matrix.of fun i j => crd b ⟨x j, hx j⟩ i).det * H.det *
        (Matrix.of fun i j => crd b ⟨x j, hx j⟩ i).det := by
      apply RingOfIntegers.coe_injective
      rw [hz, hx', BallB.gdet, ← hdet]
      rfl
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hmem)

variable [Fact (IsFixF K F)] {m : Type} [Fintype m] [DecidableEq m]

/- English proof (translation)
Establish `hF : IsFixF K F` using `Fact.out`. Take `⟨a, ha⟩` from `exists_trace_one hK hF h𝔭 (k + 1)`. Establish `hj : k + 1 ≤ 2 * (k - c)` using `by omega`. Establish `key` using `card_rep_succ (m := m) (r := m) hK h𝔭 H hH H hH hj (fun _ => True) (fun X Y _ => Iff.rfl) (fun X _ hX S hS hS' => by`. Take `⟨Y, hY, hY'⟩` from `exists_solve_matrix hF h𝔭 (by omega : c + 1 ≤ k) hD hDc hX (W := a • S) (fun i j => by`.

Rewrite using `[Matrix.smul_apply, smul_eq_mul]`. Conclude with `Ideal.mul_mem_left _ a (hS i j))`. Use `⟨Y, hY, fun i j => ?_⟩` and prove the remaining obligations. Establish `e1 : Yᴴ * H * X - (a • S)ᴴ = (Xᴴ * H * Y - a • S)ᴴ`. Simplify using `only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hH, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]`.

Establish `h2 : (Yᴴ * H * X - (a • S)ᴴ) i j ∈ extP K 𝔭 ^ (k + 1)`. Rewrite using `[e1, Matrix.conjTranspose_apply]`. Conclude with `conjO_mem_pow hF 𝔭 (k + 1) _ (hY' j i)`. Establish `h3 : (a • S + (a • S)ᴴ - S) i j ∈ extP K 𝔭 ^ (k + 1)`. Establish `e : (a • S + (a • S)ᴴ - S) i j = (a + star a - 1) * S i j + star a * ((Sᴴ - S) i j)`.

Simplify using `only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.conjTranspose_apply, smul_eq_mul, star_mul']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_left _ _ (hS' i j))`. Establish `e2 : (Xᴴ * H * Y + Yᴴ * H * X - S) i j = (Xᴴ * H * Y - a • S) i j + (Yᴴ * H * X - (a • S)ᴴ) i j + (a • S + (a • S)ᴴ - S) i j`.

Simplify using `only [Matrix.sub_apply, Matrix.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`. Conclude with `Ideal.add_mem _ (Ideal.add_mem _ (hY' i j) h2) h3)`. Simplify using `only [true_and] at key`.

Establish `hN : 0 < Ideal.absNorm 𝔭 ^ (Fintype.card m * Fintype.card m)` using `pow_pos (absNorm_pos h𝔭) _`. Establish `e : Ideal.absNorm 𝔭 ^ (2 * (Fintype.card m * Fintype.card m)) = Ideal.absNorm 𝔭 ^ (Fintype.card m * Fintype.card m) * Ideal.absNorm 𝔭 ^ (Fintype.card m * Fintype.card m)`. Rewrite using `[two_mul, pow_add]`. Apply `Nat.eq_of_mul_eq_mul_right hN` to reduce the goal to its premises. Rewrite using `[key, e]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem akM_succ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {H : Matrix m m (𝓞 K)} (hH : Hᴴ = H) {D : 𝓞 F} (hD : H.det = ι D) {c k : ℕ}
    (hDc : D ∉ 𝔭 ^ (c + 1)) (hk : 2 * c + 1 ≤ k) :
    Nat.card {X : Matrix m m (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) //
        Xᴴ * H.map (mkk K 𝔭 (k + 1)) * X = H.map (mkk K 𝔭 (k + 1))} =
      Ideal.absNorm 𝔭 ^ (Fintype.card m * Fintype.card m) *
        Nat.card {X : Matrix m m (𝓞 K ⧸ extP K 𝔭 ^ k) //
          Xᴴ * H.map (mkk K 𝔭 k) * X = H.map (mkk K 𝔭 k)} := by
  have hF : IsFixF K F := Fact.out
  obtain ⟨a, ha⟩ := exists_trace_one hK hF h𝔭 (k + 1)
  have hj : k + 1 ≤ 2 * (k - c) := by omega
  have key := card_rep_succ (m := m) (r := m) hK h𝔭 H hH H hH hj (fun _ => True)
    (fun X Y _ => Iff.rfl) (fun X _ hX S hS hS' => by
      obtain ⟨Y, hY, hY'⟩ := exists_solve_matrix hF h𝔭 (by omega : c + 1 ≤ k) hD hDc hX
        (W := a • S) (fun i j => by
          rw [Matrix.smul_apply, smul_eq_mul]
          exact Ideal.mul_mem_left _ a (hS i j))
      refine ⟨Y, hY, fun i j => ?_⟩
      have e1 : Yᴴ * H * X - (a • S)ᴴ = (Xᴴ * H * Y - a • S)ᴴ := by
        simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hH,
          Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      have h2 : (Yᴴ * H * X - (a • S)ᴴ) i j ∈ extP K 𝔭 ^ (k + 1) := by
        rw [e1, Matrix.conjTranspose_apply]
        exact conjO_mem_pow hF 𝔭 (k + 1) _ (hY' j i)
      have h3 : (a • S + (a • S)ᴴ - S) i j ∈ extP K 𝔭 ^ (k + 1) := by
        have e : (a • S + (a • S)ᴴ - S) i j =
            (a + star a - 1) * S i j + star a * ((Sᴴ - S) i j) := by
          simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
            Matrix.conjTranspose_apply, smul_eq_mul, star_mul']
          ring
        rw [e]
        exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_left _ _ (hS' i j))
      have e2 : (Xᴴ * H * Y + Yᴴ * H * X - S) i j = (Xᴴ * H * Y - a • S) i j +
          (Yᴴ * H * X - (a • S)ᴴ) i j + (a • S + (a • S)ᴴ - S) i j := by
        simp only [Matrix.sub_apply, Matrix.add_apply]
        ring
      rw [e2]
      exact Ideal.add_mem _ (Ideal.add_mem _ (hY' i j) h2) h3)
  simp only [true_and] at key
  have hN : 0 < Ideal.absNorm 𝔭 ^ (Fintype.card m * Fintype.card m) := pow_pos (absNorm_pos h𝔭) _
  have e : Ideal.absNorm 𝔭 ^ (2 * (Fintype.card m * Fintype.card m)) =
      Ideal.absNorm 𝔭 ^ (Fintype.card m * Fintype.card m) *
        Ideal.absNorm 𝔭 ^ (Fintype.card m * Fintype.card m) := by
    rw [two_mul, pow_add]
  apply Nat.eq_of_mul_eq_mul_right hN
  rw [key, e]
  ring

end Formalism.HermitianLattices.Ext.L3.localValuationFiltration
