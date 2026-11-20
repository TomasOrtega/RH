import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsTemperedCoeff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPrincipalCongruence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenIsCompactPrincipal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValZpowIff

open MeasureTheory GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.DoubleCosetVolume

/- English proof (translation)
Use `set C : Subgroup B := (B.map (MulAut.conj s).toMonoidHom).subgroupOf B with hC`. Establish `hidx : C.index ≠ 0` using `hfin`. Establish `: C.FiniteIndex` using `⟨hidx⟩`. Establish `: Finite (B ⧸ C)` using `inferInstance`. Use `letI : Fintype (B ⧸ C) := Fintype.ofFinite _`.

Establish `hmemC : ∀ w : B, w ∈ C ↔ ∃ b ∈ B, s * b * s⁻¹ = (w : Q)`. Introduce `w`. Rewrite using `[hC, Subgroup.mem_subgroupOf, Subgroup.mem_map]`. Simplify using `[MulAut.conj_apply]`. Set `r : B ⧸ C → Q` to `fun c => ((Quotient.out c : B) : Q) * s`.

Set `T : B ⧸ C → Set Q` to `fun c => (fun h => (r c)⁻¹ * h) ⁻¹' (B : Set Q)`. Establish `hcover : {q : Q | ∃ x ∈ B, ∃ y ∈ B, q = x * s * y} = ⋃ c, T c`. Use extensionality with `q`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_iUnion]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, hx, y, hy, rfl⟩`. Use `⟨QuotientGroup.mk (⟨x, hx⟩ : B), ?_⟩` and prove the remaining obligations. Establish `h1 : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk (⟨x, hx⟩ : B) : B ⧸ C)) : B ⧸ C) = QuotientGroup.mk (⟨x, hx⟩ : B)` using `QuotientGroup.out_eq' _`. Take `⟨b, hb, hbw⟩` from `(hmemC _).1 (QuotientGroup.eq.1 h1)`. Establish `h2 : ((Quotient.out (QuotientGroup.mk (⟨x, hx⟩ : B) : B ⧸ C) : B) : Q)⁻¹ * x = s * b * s⁻¹`.

Rewrite using `[hbw]`. Simplify using the standard rewrite rules. Use `show (r _)⁻¹ * (x * s * y) ∈ B`. Establish `h3 : (r (QuotientGroup.mk (⟨x, hx⟩ : B)))⁻¹ * (x * s * y) = b * y` using `by show (((Quotient.out (QuotientGroup.mk (⟨x, hx⟩ : B) : B ⧸ C) : B) : Q) * s)⁻¹ * (x * s * y) = b * y`. Rewrite using `[mul_inv_rev, mul_assoc s⁻¹, ← mul_assoc _ (x * s) y, ← mul_assoc _ x s, h2]`.

Use `group`. Rewrite using `[h3]`. Conclude with `B.mul_mem hb hy`. Introduce and unpack `⟨c, hc⟩`. Use `⟨_, (Quotient.out c : B).2, _, hc, ?_⟩` and prove the remaining obligations.

Use `show q = r c * ((r c)⁻¹ * q)`. Use `group`. Establish `hdisj : Pairwise (Function.onFun Disjoint T)`. Introduce `c c' hcc`. Use `Set.disjoint_left.2 fun q hq hq' => hcc ?_` and prove the remaining obligations.

Establish `hq1 : (r c)⁻¹ * q ∈ B` using `hq`. Establish `hq2 : (r c')⁻¹ * q ∈ B` using `hq'`. Establish `hw : (Quotient.out c : B)⁻¹ * (Quotient.out c' : B) ∈ C`. Use `(hmemC _).2 ⟨((r c)⁻¹ * q) * ((r c')⁻¹ * q)⁻¹, B.mul_mem hq1 (B.inv_mem hq2), ?_⟩` and prove the remaining obligations. Use `show _ = ((Quotient.out c : B) : Q)⁻¹ * ((Quotient.out c' : B) : Q)`.

Use `show s * (((((Quotient.out c : B) : Q) * s)⁻¹ * q) * (((((Quotient.out c' : B) : Q) * s)⁻¹ * q))⁻¹) * s⁻¹ = _`. Use `group`. Use `QuotientGroup.eq.2 hw` as an intermediate fact. Rewrite `this` using `[QuotientGroup.out_eq', QuotientGroup.out_eq']`. Conclude with `this`.

Establish `hopen : ∀ c, MeasurableSet (T c)` using `fun c => (hB.preimage (continuous_const.mul continuous_id)).measurableSet`. Establish `hT : ∀ c, μ (T c) = μ (B : Set Q)` using `fun c => measure_preimage_mul μ _ _`. Rewrite using `[hcover, measure_iUnion hdisj hopen]`. Simplify using `only [hT, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Use `congr 2`.

Use `show _ = C.index`. Rewrite using `[Subgroup.index, Nat.card_eq_fintype_card]`.
-/
theorem measure_doubleCoset {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [MeasurableSpace Q] [BorelSpace Q] (μ : Measure Q) [μ.IsMulLeftInvariant] (B : Subgroup Q)
    (hB : IsOpen (B : Set Q)) (s : Q)
    (hfin : (B.map (MulAut.conj s).toMonoidHom).relIndex B ≠ 0) :
    μ {q : Q | ∃ x ∈ B, ∃ y ∈ B, q = x * s * y} =
      ((B.map (MulAut.conj s).toMonoidHom).relIndex B : ENNReal) * μ (B : Set Q) := by
  classical
  set C : Subgroup B := (B.map (MulAut.conj s).toMonoidHom).subgroupOf B with hC
  have hidx : C.index ≠ 0 := hfin
  have : C.FiniteIndex := ⟨hidx⟩
  have : Finite (B ⧸ C) := inferInstance
  letI : Fintype (B ⧸ C) := Fintype.ofFinite _
  have hmemC : ∀ w : B, w ∈ C ↔ ∃ b ∈ B, s * b * s⁻¹ = (w : Q) := by
    intro w
    rw [hC, Subgroup.mem_subgroupOf, Subgroup.mem_map]
    simp [MulAut.conj_apply]
  let r : B ⧸ C → Q := fun c => ((Quotient.out c : B) : Q) * s
  let T : B ⧸ C → Set Q := fun c => (fun h => (r c)⁻¹ * h) ⁻¹' (B : Set Q)
  have hcover : {q : Q | ∃ x ∈ B, ∃ y ∈ B, q = x * s * y} = ⋃ c, T c := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      refine ⟨QuotientGroup.mk (⟨x, hx⟩ : B), ?_⟩
      have h1 : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk (⟨x, hx⟩ : B) : B ⧸ C)) : B ⧸ C) =
          QuotientGroup.mk (⟨x, hx⟩ : B) := QuotientGroup.out_eq' _
      obtain ⟨b, hb, hbw⟩ := (hmemC _).1 (QuotientGroup.eq.1 h1)
      have h2 : ((Quotient.out (QuotientGroup.mk (⟨x, hx⟩ : B) : B ⧸ C) : B) : Q)⁻¹ * x =
          s * b * s⁻¹ := by
        rw [hbw]; simp
      show (r _)⁻¹ * (x * s * y) ∈ B
      have h3 : (r (QuotientGroup.mk (⟨x, hx⟩ : B)))⁻¹ * (x * s * y) = b * y := by
        show (((Quotient.out (QuotientGroup.mk (⟨x, hx⟩ : B) : B ⧸ C) : B) : Q) * s)⁻¹ *
          (x * s * y) = b * y
        rw [mul_inv_rev, mul_assoc s⁻¹, ← mul_assoc _ (x * s) y, ← mul_assoc _ x s, h2]
        group
      rw [h3]
      exact B.mul_mem hb hy
    · rintro ⟨c, hc⟩
      refine ⟨_, (Quotient.out c : B).2, _, hc, ?_⟩
      show q = r c * ((r c)⁻¹ * q)
      group
  have hdisj : Pairwise (Function.onFun Disjoint T) := by
    intro c c' hcc
    refine Set.disjoint_left.2 fun q hq hq' => hcc ?_
    have hq1 : (r c)⁻¹ * q ∈ B := hq
    have hq2 : (r c')⁻¹ * q ∈ B := hq'
    have hw : (Quotient.out c : B)⁻¹ * (Quotient.out c' : B) ∈ C := by
      refine (hmemC _).2 ⟨((r c)⁻¹ * q) * ((r c')⁻¹ * q)⁻¹, B.mul_mem hq1 (B.inv_mem hq2), ?_⟩
      show _ = ((Quotient.out c : B) : Q)⁻¹ * ((Quotient.out c' : B) : Q)
      show s * (((((Quotient.out c : B) : Q) * s)⁻¹ * q) *
        (((((Quotient.out c' : B) : Q) * s)⁻¹ * q))⁻¹) * s⁻¹ = _
      group
    have := QuotientGroup.eq.2 hw
    rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
    exact this
  have hopen : ∀ c, MeasurableSet (T c) := fun c =>
    (hB.preimage (continuous_const.mul continuous_id)).measurableSet
  have hT : ∀ c, μ (T c) = μ (B : Set Q) := fun c => measure_preimage_mul μ _ _
  rw [hcover, measure_iUnion hdisj hopen]
  simp only [hT, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 2
  show _ = C.index
  rw [Subgroup.index, Nat.card_eq_fintype_card]

/- English proof (translation)
Rewrite using `[← Subgroup.relIndex_comap, ← Subgroup.inf_relIndex_right, ← Subgroup.inf_relIndex_right (H.map (MulAut.conj t).toMonoidHom)]`. Use `congr 1`. Use extensionality with `g`. Simplify using `only [Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_map]`. Use `and_congr_left fun hg => ?_` and prove the remaining obligations.

Simplify using `only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, exists_exists_and_eq_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, hh, he⟩`. Establish `h1 : (QuotientGroup.mk' Z) (t * h * t⁻¹) = (QuotientGroup.mk' Z) g`. Simplify using `using he`.

Conclude with `hZ g hg h hh (QuotientGroup.eq.1 h1)`. Introduce and unpack `⟨h, hh, rfl⟩`. Conclude with `⟨h, hh, by simp⟩`.
-/
theorem relIndex_map_mk {G : Type*} [Group G] (Z : Subgroup G) [Z.Normal] (H : Subgroup G) (t : G)
    (hZ : ∀ g ∈ H, ∀ h ∈ H, (t * h * t⁻¹)⁻¹ * g ∈ Z → ∃ h₂ ∈ H, t * h₂ * t⁻¹ = g) :
    ((H.map (QuotientGroup.mk' Z)).map (MulAut.conj (QuotientGroup.mk' Z t)).toMonoidHom).relIndex
        (H.map (QuotientGroup.mk' Z)) =
      (H.map (MulAut.conj t).toMonoidHom).relIndex H := by
  rw [← Subgroup.relIndex_comap, ← Subgroup.inf_relIndex_right,
    ← Subgroup.inf_relIndex_right (H.map (MulAut.conj t).toMonoidHom)]
  congr 1
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_map]
  refine and_congr_left fun hg => ?_
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, exists_exists_and_eq_and]
  constructor
  · rintro ⟨h, hh, he⟩
    have h1 : (QuotientGroup.mk' Z) (t * h * t⁻¹) = (QuotientGroup.mk' Z) g := by
      simpa using he
    exact hZ g hg h hh (QuotientGroup.eq.1 h1)
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, by simp⟩

/- English proof (translation)
Break down `le_total 0 x with h | h` into its components or cases. Use `lift x to ℕ using h`. Rewrite using `[← Nat.cast_mul, Int.toNat_natCast, Int.toNat_natCast]`. Establish `h1 : (j : ℤ) * x ≤ 0` using `mul_nonpos_of_nonneg_of_nonpos (by positivity) h`. Rewrite using `[Int.toNat_of_nonpos h1, Int.toNat_of_nonpos h, mul_zero]`.
-/
theorem toNat_natCast_mul (j : ℕ) (x : ℤ) : ((j : ℤ) * x).toNat = j * x.toNat := by
  rcases le_total 0 x with h | h
  · lift x to ℕ using h
    rw [← Nat.cast_mul, Int.toNat_natCast, Int.toNat_natCast]
  · have h1 : (j : ℤ) * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    rw [Int.toNat_of_nonpos h1, Int.toNat_of_nonpos h, mul_zero]

end GlobalTheory.CompanionTheory.DoubleCosetVolume

namespace GlobalTheory.CompanionTheory.DoubleCosetVolume

open ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k]

/- English proof (translation)
Take `⟨c, hc⟩` from `Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 hz`. Establish `hzv : (z : Matrix (Fin N) (Fin N) k) = Matrix.scalar (Fin N) c` using `hc.symm`. Establish `htinv : ((t⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = Matrix.diagonal fun i => (d i)⁻¹`. Use `Units.inv_eq_of_mul_eq_one_right ?_` and prove the remaining obligations. Rewrite using `[ht, Matrix.diagonal_mul_diagonal]`.

Simplify using `[hd, Matrix.diagonal_one]`. Introduce `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Establish `h1 : (g : Matrix (Fin N) (Fin N) k) i i = (h : Matrix (Fin N) (Fin N) k) i i * c`.

Rewrite using `[hgz]`. Simplify using `only [Units.val_mul, hzv, htinv, ht, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Clear denominators, using `[hd i]` for the nonvanishing conditions. Establish `h2 : valuation k ((h : Matrix (Fin N) (Fin N) k) i i) = 1`. Establish `h3` using `hh i i`.

Rewrite `h3` using `[Matrix.one_apply_eq]`. Establish `h4` using `Valuation.map_one_add_of_lt (valuation k) (h3.trans_lt hr)`. Rewrite `h4` using `[add_sub_cancel]`. Then use the resulting hypothesis. Establish `h5` using `hg i i`. Establish `h6` using `hh i i`.

Rewrite `h5`, `h6`, the goal using `[Matrix.one_apply_eq]`. Establish `h7 : (h : Matrix (Fin N) (Fin N) k) i i * (c - 1) = ((g : Matrix (Fin N) (Fin N) k) i i - 1) - ((h : Matrix (Fin N) (Fin N) k) i i - 1)`. Rewrite using `[h1]`. Expand and normalize the polynomial expressions, which then agree. Establish `h8 : valuation k (c - 1) ≤ r`.

Establish `h9` using `Valuation.map_sub (valuation k) ((g : Matrix (Fin N) (Fin N) k) i i - 1) ((h : Matrix (Fin N) (Fin N) k) i i - 1)`. Rewrite `h9` using `[← h7, map_mul, h2, one_mul]`. Conclude with `h9.trans (max_le h5 h6)`. Rewrite using `[hzv]`. Simplify using `using h8`.

Rewrite using `[hzv, Matrix.one_apply_ne hij]`. Simplify using `[Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]`.
-/
theorem central_mem_cong {N : ℕ} {r : ValueGroupWithZero k} (hr : r < 1)
    (t : GL (Fin N) k) (d : Fin N → k) (hd : ∀ i, d i ≠ 0)
    (ht : (t : Matrix (Fin N) (Fin N) k) = Matrix.diagonal d)
    (g h z : GL (Fin N) k)
    (hg : ∀ i j, valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ r)
    (hh : ∀ i j, valuation k ((h : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ r)
    (hz : z ∈ Subgroup.center (GL (Fin N) k)) (hgz : g = t * h * t⁻¹ * z) :
    ∀ i j, valuation k ((z : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ r := by
  obtain ⟨c, hc⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 hz
  have hzv : (z : Matrix (Fin N) (Fin N) k) = Matrix.scalar (Fin N) c := hc.symm
  have htinv : ((t⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = Matrix.diagonal fun i => (d i)⁻¹ := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [ht, Matrix.diagonal_mul_diagonal]
    simp [hd, Matrix.diagonal_one]
  intro i j
  by_cases hij : i = j
  · subst hij
    have h1 : (g : Matrix (Fin N) (Fin N) k) i i = (h : Matrix (Fin N) (Fin N) k) i i * c := by
      rw [hgz]
      simp only [Units.val_mul, hzv, htinv, ht, Matrix.scalar_apply, Matrix.mul_diagonal,
        Matrix.diagonal_mul]
      field_simp [hd i]
    have h2 : valuation k ((h : Matrix (Fin N) (Fin N) k) i i) = 1 := by
      have h3 := hh i i
      rw [Matrix.one_apply_eq] at h3
      have h4 := Valuation.map_one_add_of_lt (valuation k) (h3.trans_lt hr)
      rwa [add_sub_cancel] at h4
    have h5 := hg i i
    have h6 := hh i i
    rw [Matrix.one_apply_eq] at h5 h6 ⊢
    have h7 : (h : Matrix (Fin N) (Fin N) k) i i * (c - 1) =
        ((g : Matrix (Fin N) (Fin N) k) i i - 1) - ((h : Matrix (Fin N) (Fin N) k) i i - 1) := by
      rw [h1]; ring
    have h8 : valuation k (c - 1) ≤ r := by
      have h9 := Valuation.map_sub (valuation k) ((g : Matrix (Fin N) (Fin N) k) i i - 1)
        ((h : Matrix (Fin N) (Fin N) k) i i - 1)
      rw [← h7, map_mul, h2, one_mul] at h9
      exact h9.trans (max_le h5 h6)
    rw [hzv]
    simpa using h8
  · rw [hzv, Matrix.one_apply_ne hij]
    simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]

end GlobalTheory.CompanionTheory.DoubleCosetVolume

namespace GlobalTheory.CompanionTheory.DoubleCosetVolume

open ValuativeRel

/- English proof (translation)
Introduce `k _ _ _ _ N ϖ m a hϖ0 hϖ1 hunif hm ha D hD _ _ μ hμ j`. Establish `hϖm0 : ϖ ^ m ≠ 0` using `pow_ne_zero _ hϖ0`. Establish `hr : valuation k (ϖ ^ m) < 1`. Rewrite using `[map_pow]`. Conclude with `pow_lt_one₀ zero_le hϖ1 (by omega)`.

Take `⟨H, hH⟩` from `GlobalTheory.CompanionTheory.PrincipalCongruence.exists_principalCongruence k N (ϖ ^ m) hϖm0 hr`. Establish `hopen : IsOpen (H : Set (GL (Fin N) k))`. Rewrite using `[hH]`. Conclude with `(GlobalTheory.CompanionTheory.PrincipalCongruence.isOpen_isCompact_principal k N (ϖ ^ m) hϖm0 hr).1`. Establish `hmem : ∀ g : GL (Fin N) k, g ∈ H ↔ ∀ i j, valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ valuation k (ϖ ^ m)`.

Introduce `g`. Rewrite using `[← SetLike.mem_coe, hH]`. Both sides reduce to the same expression. Rewrite using `[← hH]`. Use `set t : GL (Fin N) k := D ^ j with ht`.

Establish `hDj : (t : Matrix (Fin N) (Fin N) k) = Matrix.diagonal (fun i => ϖ ^ ((j : ℤ) * a i))`. Rewrite using `[ht, Units.val_pow_eq_pow_val, hD, Matrix.diagonal_pow]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.pow_apply]`.

Rewrite using `[← zpow_natCast, ← zpow_mul, mul_comm]`. Establish `hanti : Antitone fun i => (j : ℤ) * a i` using `fun x y hxy => mul_le_mul_of_nonneg_left (ha hxy) (by positivity)`. Establish `hindex` using `GlobalTheory.CompanionTheory.CongIndex.index_main k N ϖ m (fun i => (j : ℤ) * a i) hϖ0 hϖ1 hunif hm hanti t hDj H hH`. Establish `hsum : (∑ i : Fin N, ∑ l : Fin N, if i < l then ((j : ℤ) * a i - (j : ℤ) * a l).toNat else 0) = j * ∑ i : Fin N, ∑ l : Fin N, if i < l then (a i - a l).toNat else 0`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Use `split_ifs`. Rewrite using `[← mul_sub, toNat_natCast_mul]`.

Simplify using the standard rewrite rules. Simplify using `only [hsum] at hindex`. Establish `hq : 0 < Nat.card (IsLocalRing.ResidueField (valuation k).integer)` using `Nat.card_pos`. Use `set Z : Subgroup (GL (Fin N) k) := Subgroup.center (GL (Fin N) k) with hZdef`. Establish `hmerge : ∀ g ∈ H, ∀ h ∈ H, (t * h * t⁻¹)⁻¹ * g ∈ Z → ∃ h₂ ∈ H, t * h₂ * t⁻¹ = g`.

Introduce `g hg h hh hz`. Establish `hzH : (t * h * t⁻¹)⁻¹ * g ∈ H` using `(hmem _).2 (central_mem_cong hr t _ (fun i => zpow_ne_zero _ hϖ0) hDj g h _ ((hmem g).1 hg) ((hmem h).1 hh) hz (by group))`. Use `⟨h * ((t * h * t⁻¹)⁻¹ * g), H.mul_mem hh hzH, ?_⟩` and prove the remaining obligations. Establish `hc` using `Subgroup.mem_center_iff.1 hz t⁻¹`. Combine the equalities or inequalities in the displayed calculation.

Establish `hI` using `relIndex_map_mk Z H t hmerge`. Use `set B : Subgroup (AdGL k N) := H.map (QuotientGroup.mk' Z) with hB`. Use `set s : AdGL k N := QuotientGroup.mk' Z t with hs`. Establish `hBopen : IsOpen (B : Set (AdGL k N))`. Use `QuotientGroup.isOpenMap_coe (N := Z) _ hopen` as an intermediate fact.

Simplify `this` using `[hB, Subgroup.coe_map]`. Establish `hBcoe : (QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' (H : Set (GL (Fin N) k)) = (B : Set (AdGL k N))`. Rewrite using `[hB, Subgroup.coe_map]`. Both sides reduce to the same expression. Establish `hdc : (QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {g : GL (Fin N) k | ∃ x ∈ (H : Set (GL (Fin N) k)), ∃ y ∈ (H : Set (GL (Fin N) k)), g = x * t * y} = {q : AdGL k N | ∃ x ∈ B, ∃ y ∈ B, q = x * s * y}`.

Use extensionality with `q`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩`. Conclude with `⟨_, Subgroup.mem_map_of_mem _ hx, _, Subgroup.mem_map_of_mem _ hy, rfl⟩`. Introduce and unpack `⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩`.

Conclude with `⟨x * t * y, ⟨x, hx, y, hy, rfl⟩, rfl⟩`. Rewrite using `[hBcoe, hdc, measure_doubleCoset μ B hBopen s (by rw [hI, hindex]; positivity), hI, hindex]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem measure_image_doubleCoset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : k) (m : ℕ) (a : Fin N → ℤ), ϖ ≠ 0 → ValuativeRel.valuation k (ϖ) < 1 → (∀ x : k, ValuativeRel.valuation k (x) < 1 → ValuativeRel.valuation k (x) ≤ ValuativeRel.valuation k (ϖ)) → 1 ≤ m → Antitone a → ∀ D : GL (Fin N) k, (D : Matrix (Fin N) (Fin N) k) = Matrix.diagonal (fun i => ϖ ^ (a i)) → ∀ [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)] (μ : MeasureTheory.Measure (AdGL k N)), μ.IsHaarMeasure → ∀ j : ℕ, μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {g : GL (Fin N) k | ∃ x ∈ {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)}, ∃ y ∈ {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)}, g = x * D ^ j * y}) = ((Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation k).integer) : ENNReal) ^ (j * (∑ i : Fin N, ∑ j : Fin N, if i < j then (a i - a j).toNat else 0))) * μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)}) := by
  intro k _ _ _ _ N ϖ m a hϖ0 hϖ1 hunif hm ha D hD _ _ μ hμ j
  have hϖm0 : ϖ ^ m ≠ 0 := pow_ne_zero _ hϖ0
  have hr : valuation k (ϖ ^ m) < 1 := by
    rw [map_pow]
    exact pow_lt_one₀ zero_le hϖ1 (by omega)
  obtain ⟨H, hH⟩ := GlobalTheory.CompanionTheory.PrincipalCongruence.exists_principalCongruence k N (ϖ ^ m) hϖm0 hr
  have hopen : IsOpen (H : Set (GL (Fin N) k)) := by
    rw [hH]
    exact (GlobalTheory.CompanionTheory.PrincipalCongruence.isOpen_isCompact_principal k N (ϖ ^ m) hϖm0 hr).1
  have hmem : ∀ g : GL (Fin N) k, g ∈ H ↔ ∀ i j, valuation k
      ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ valuation k (ϖ ^ m) := by
    intro g
    rw [← SetLike.mem_coe, hH]
    rfl
  rw [← hH]
  set t : GL (Fin N) k := D ^ j with ht
  have hDj : (t : Matrix (Fin N) (Fin N) k) = Matrix.diagonal (fun i => ϖ ^ ((j : ℤ) * a i)) := by
    rw [ht, Units.val_pow_eq_pow_val, hD, Matrix.diagonal_pow]
    congr 1
    funext i
    simp only [Pi.pow_apply]
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
  have hanti : Antitone fun i => (j : ℤ) * a i := fun x y hxy =>
    mul_le_mul_of_nonneg_left (ha hxy) (by positivity)
  have hindex := GlobalTheory.CompanionTheory.CongIndex.index_main k N ϖ m (fun i => (j : ℤ) * a i) hϖ0 hϖ1 hunif hm hanti t hDj H hH
  have hsum : (∑ i : Fin N, ∑ l : Fin N, if i < l then ((j : ℤ) * a i - (j : ℤ) * a l).toNat else 0) =
      j * ∑ i : Fin N, ∑ l : Fin N, if i < l then (a i - a l).toNat else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs
    · rw [← mul_sub, toNat_natCast_mul]
    · simp
  simp only [hsum] at hindex
  have hq : 0 < Nat.card (IsLocalRing.ResidueField (valuation k).integer) := Nat.card_pos
  set Z : Subgroup (GL (Fin N) k) := Subgroup.center (GL (Fin N) k) with hZdef
  have hmerge : ∀ g ∈ H, ∀ h ∈ H, (t * h * t⁻¹)⁻¹ * g ∈ Z → ∃ h₂ ∈ H, t * h₂ * t⁻¹ = g := by
    intro g hg h hh hz
    have hzH : (t * h * t⁻¹)⁻¹ * g ∈ H := (hmem _).2 (central_mem_cong hr t _
      (fun i => zpow_ne_zero _ hϖ0) hDj g h _ ((hmem g).1 hg) ((hmem h).1 hh) hz (by group))
    refine ⟨h * ((t * h * t⁻¹)⁻¹ * g), H.mul_mem hh hzH, ?_⟩
    have hc := Subgroup.mem_center_iff.1 hz t⁻¹
    calc t * (h * ((t * h * t⁻¹)⁻¹ * g)) * t⁻¹
        = t * h * (((t * h * t⁻¹)⁻¹ * g) * t⁻¹) := by group
      _ = t * h * (t⁻¹ * ((t * h * t⁻¹)⁻¹ * g)) := by rw [hc]
      _ = g := by group
  have hI := relIndex_map_mk Z H t hmerge
  set B : Subgroup (AdGL k N) := H.map (QuotientGroup.mk' Z) with hB
  set s : AdGL k N := QuotientGroup.mk' Z t with hs
  have hBopen : IsOpen (B : Set (AdGL k N)) := by
    have := QuotientGroup.isOpenMap_coe (N := Z) _ hopen
    simpa [hB, Subgroup.coe_map] using this
  have hBcoe : (QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' (H : Set (GL (Fin N) k)) = (B : Set (AdGL k N)) := by
    rw [hB, Subgroup.coe_map]; rfl
  have hdc : (QuotientGroup.mk : GL (Fin N) k → AdGL k N) ''
      {g : GL (Fin N) k | ∃ x ∈ (H : Set (GL (Fin N) k)), ∃ y ∈ (H : Set (GL (Fin N) k)), g = x * t * y} =
      {q : AdGL k N | ∃ x ∈ B, ∃ y ∈ B, q = x * s * y} := by
    ext q
    constructor
    · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
      exact ⟨_, Subgroup.mem_map_of_mem _ hx, _, Subgroup.mem_map_of_mem _ hy, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨x * t * y, ⟨x, hx, y, hy, rfl⟩, rfl⟩
  rw [hBcoe, hdc, measure_doubleCoset μ B hBopen s (by rw [hI, hindex]; positivity), hI, hindex]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.DoubleCosetVolume
