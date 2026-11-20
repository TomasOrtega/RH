import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NormalRepresentationLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagPartMulDiagPart

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice

namespace GlobalTheory.StepData.NormalForm

section Plain
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

end Plain

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Use `set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k`. Establish `hu0 : φ (uniformizer k) ≠ 0`. Rewrite using `[ne_eq, map_eq_zero]`. Conclude with `(uniformizer_pos).ne'`. Establish `hu1 : φ (uniformizer k) < 1`.

Rewrite using `[← map_one φ]`. Conclude with `φ.strictMono uniformizer_lt_one`. Take `⟨a, ha⟩` from `WithZero.ne_zero_iff_exists.mp hu0`. Establish `ha1 : a.toAdd < 0`. Rewrite `hu1` using `[← ha]`.

Conclude with `hu1` after adjusting the coercions. Establish `ha2 : -1 ≤ a.toAdd`. Establish `h1 : φ.symm ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < 1`. Rewrite using `[← map_one φ.symm]`. Conclude with `φ.symm.strictMono (by exact_mod_cast (show (Multiplicative.ofAdd (-1 : ℤ)) < 1 by decide))`.

Establish `h2` using `le_uniformizer_iff.mpr h1`. Establish `h3` using `φ.strictMono.monotone h2`. Simplify using `only [OrderMonoidIso.apply_symm_apply, ← ha] at h3`. Conclude with `h3` after adjusting the coercions. Establish `ha3 : a = Multiplicative.ofAdd (-1 : ℤ)`.

Apply `Multiplicative.toAdd.injective` to reduce the goal to its premises. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Establish `hd0 : φ (valuation k (d : k)) ≠ 0`. Rewrite using `[ne_eq, map_eq_zero, map_eq_zero]`.

Conclude with `d.ne_zero`. Take `⟨b, hb⟩` from `WithZero.ne_zero_iff_exists.mp hd0`. Establish `hz : φ (uniformizer k ^ (-b.toAdd)) = φ (uniformizer k) ^ (-b.toAdd)` using `map_zpow₀ φ _ _`. Establish `key : φ (valuation k (d : k)) = φ (valuation k (ϖ : k) ^ (-b.toAdd))`. Rewrite using `[hϖ, hz, ← ha, ← hb, ha3, ← WithZero.coe_zpow]`.

Use `congr 1`. Apply `Multiplicative.toAdd.injective` to reduce the goal to its premises. Simplify using the standard rewrite rules. Conclude with `⟨-b.toAdd, φ.injective key⟩`.
-/
theorem _root_.GlobalTheory.StepData.NormalForm.exists_valuation_eq_zpow {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k)
    (d : kˣ) : ∃ e : ℤ, valuation k (d : k) = valuation k (ϖ : k) ^ e := by
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have hu0 : φ (uniformizer k) ≠ 0 := by
    rw [ne_eq, map_eq_zero]; exact (uniformizer_pos).ne'
  have hu1 : φ (uniformizer k) < 1 := by
    rw [← map_one φ]; exact φ.strictMono uniformizer_lt_one
  obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.mp hu0
  have ha1 : a.toAdd < 0 := by
    rw [← ha] at hu1
    exact_mod_cast hu1
  have ha2 : -1 ≤ a.toAdd := by
    have h1 : φ.symm ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) < 1 := by
      rw [← map_one φ.symm]
      exact φ.symm.strictMono
        (by exact_mod_cast (show (Multiplicative.ofAdd (-1 : ℤ)) < 1 by decide))
    have h2 := le_uniformizer_iff.mpr h1
    have h3 := φ.strictMono.monotone h2
    simp only [OrderMonoidIso.apply_symm_apply, ← ha] at h3
    exact_mod_cast h3
  have ha3 : a = Multiplicative.ofAdd (-1 : ℤ) := by
    apply Multiplicative.toAdd.injective; simp; omega
  have hd0 : φ (valuation k (d : k)) ≠ 0 := by
    rw [ne_eq, map_eq_zero, map_eq_zero]; exact d.ne_zero
  obtain ⟨b, hb⟩ := WithZero.ne_zero_iff_exists.mp hd0
  have hz : φ (uniformizer k ^ (-b.toAdd)) = φ (uniformizer k) ^ (-b.toAdd) := map_zpow₀ φ _ _
  have key : φ (valuation k (d : k)) = φ (valuation k (ϖ : k) ^ (-b.toAdd)) := by
    rw [hϖ, hz, ← ha, ← hb, ha3, ← WithZero.coe_zpow]
    congr 1
    apply Multiplicative.toAdd.injective
    simp
  exact ⟨-b.toAdd, φ.injective key⟩

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Rewrite `hw` using `[_root_.GlobalTheory.StepData.mem_KO]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[_root_.GlobalTheory.StepData.latOf_le_iff]`. Simplify `hw.1` using `[← mul_assoc]`. Rewrite using `[_root_.GlobalTheory.StepData.latOf_le_iff]`.

Simplify `hw.2` using `[mul_assoc]`.
-/
private lemma latOf_mul_of_mem_KO' {K : Type} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] {Y : Type} [Fintype Y] [DecidableEq Y]
    (x w : GL Y K) (hw : w ∈ _root_.GlobalTheory.SplitWeil.KO K Y) :
    _root_.GlobalTheory.StepData.latOf (x * w) = _root_.GlobalTheory.StepData.latOf x := by
  rw [_root_.GlobalTheory.StepData.mem_KO] at hw
  apply le_antisymm
  · rw [_root_.GlobalTheory.StepData.latOf_le_iff]
    simpa [← mul_assoc] using hw.1
  · rw [_root_.GlobalTheory.StepData.latOf_le_iff]
    simpa [mul_assoc] using hw.2

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Introduce `k _ _ _ _ ϖ hϖ n _ _ c h`. Take `⟨b, hbT, w, hw, rfl⟩` from `_root_.GlobalTheory.SplitWeil.iwasawa_blockTriangular k (n ⊕ Fin c) (Sum.elim (fun _ => 0) (fun i => (i : ℕ) + 1)) h`. Establish `hbP : (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).BlockTriangular (_root_.GlobalTheory.RootEx.lev 1)`. Introduce `i j hij`. Apply `hbT` to reduce the goal to its premises.

Unfold `_root_.GlobalTheory.RootEx.lev at hij`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;> simp at hij ⊢ <;> omega`. Take `⟨u', hu', m, hm0, hmb, hbum⟩` from `_root_.GlobalTheory.RootEx.BlockLevi.exists_unip_mul_levi k n c 1 b hbP`. Establish `h21 : (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₂₁ = 0`. Use extensionality with `i j`.

Conclude with `hbT (by simp)`. Establish `hT : ((b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₂₂).BlockTriangular id`. Introduce `i j hij`. Conclude with `hbT (by simp only [Sum.elim_inr]; exact Nat.succ_lt_succ hij)`. Establish `hdet : (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).det ≠ 0` using `b.det_ne_zero`.

Establish `hbB` using `fromBlocks_toBlocks (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)`. Rewrite `hdet` using `[← hbB, h21, det_fromBlocks_zero₂₁, det_of_upperTriangular hT]`. Establish `hG : (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁.det ≠ 0` using `left_ne_zero_of_mul hdet`. Establish `ht : ∀ i : Fin c, (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inr i) (Sum.inr i) ≠ 0` using `fun i => Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hdet) i (Finset.mem_univ i)`. Use `set g : GL n k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hG with hg`.

Establish `hgv : (g : Matrix n n k) = (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁` using `rfl`. Use `choose e he using fun i => _root_.GlobalTheory.StepData.NormalForm.exists_valuation_eq_zpow hϖ (Units.mk0 _ (ht i))`. Use `set z : n → k := fun r => if hc : 0 < c then (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl r) (Sum.inr ⟨0, hc⟩) * ((b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inr ⟨0, hc⟩) (Sum.inr ⟨0, hc⟩))⁻¹ else 0 with hz`. Use `set εv : n ⊕ Fin c → kˣ := Sum.elim (fun _ => 1) (fun i => Units.mk0 _ (ht i) * ϖ ^ (-e i)) with hεv`. Establish `hϖ0 : (ϖ : k) ≠ 0` using `ϖ.ne_zero`.

Establish `key : m = _root_.GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.nfBasis ϖ g e z * _root_.GlobalTheory.SplitFlip.diagGL εv` using `by clear hbum hu' hbP hdet hbB hw hT h21 hϖ he`. Use extensionality with `r s`. Rewrite using `[Units.val_mul, _root_.GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.nfBasis_val, _root_.GlobalTheory.SplitFlip.diagGL_val, mul_diagonal]`. Apply the tactic sequence `rcases r with r | i <;> rcases s with s | j`. Rewrite using `[hmb _ _ (by simp [_root_.GlobalTheory.RootEx.lev])]`.

Simplify using `[hεv, hgv, toBlocks₁₁]`. Distinguish the cases in `hj : (j : ℕ) = 0`. Rewrite using `[hmb _ _ (by simp [_root_.GlobalTheory.RootEx.lev, hj])]`. Establish `hc : 0 < c` using `j.pos`. Establish `hj' : j = ⟨0, hc⟩` using `Fin.ext hj`.

Substitute `hj'` using the available equality. Simplify using `only [fromBlocks_apply₁₂, of_apply, hj, if_true, hz, dif_pos hc, hεv, Sum.elim_inr, Units.val_mul, Units.val_mk0, Units.val_zpow_eq_zpow_val, _root_.zpow_neg, Units.val_inv_eq_inv_val]`. Use `ht ⟨0, hc⟩` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Rewrite using `[hm0 _ _ (by simp [_root_.GlobalTheory.RootEx.lev]; omega)]`.

Simplify using `[hj]`. Distinguish the cases in `hi : (i : ℕ) = 0`. Rewrite using `[hmb _ _ (by simp [_root_.GlobalTheory.RootEx.lev, hi])]`. Simplify using `only [fromBlocks_apply₂₁, Matrix.zero_apply, zero_mul]`. Conclude with `hbT (by simp)`.

Rewrite using `[hm0 _ _ (by simp [_root_.GlobalTheory.RootEx.lev]; omega)]`. Rewrite using `[fromBlocks_apply₂₁, Matrix.zero_apply, zero_mul]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Use `ht i` as an intermediate fact.

Rewrite using `[hmb _ _ rfl]`. Simplify using `only [fromBlocks_apply₂₂, diagonal_apply_eq, hεv, Sum.elim_inr, Units.val_mul, Units.val_mk0, Units.val_zpow_eq_zpow_val, _root_.zpow_neg, Units.val_inv_eq_inv_val]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hm0 _ _ (by simp [_root_.GlobalTheory.RootEx.lev]; omega)]`. Simplify using `[diagonal_apply_ne _ hij]`.

Establish `hεinv : (_root_.GlobalTheory.SplitFlip.diagGL εv)⁻¹ = _root_.GlobalTheory.SplitFlip.diagGL εv⁻¹`. Apply `inv_eq_of_mul_eq_one_right` to reduce the goal to its premises. Use extensionality with `i j`. Rewrite using `[Units.val_mul, _root_.GlobalTheory.SplitFlip.diagGL_val, _root_.GlobalTheory.SplitFlip.diagGL_val, diagonal_mul_diagonal, Units.val_one]`. Simplify using `[diagonal_apply, one_apply]`.

Establish `hv0 : valuation k (ϖ : k) ≠ 0` using `(map_ne_zero _).mpr hϖ0`. Establish `hval : ∀ i, valuation k (εv i : k) = 1`. Introduce and unpack `(i | i)`. Simplify using `[hεv]`. Establish `hei` using `he i`.

Rewrite `hei` using `[Units.val_mk0]`. Simplify using `only [hεv, Sum.elim_inr, Units.val_mul, Units.val_mk0, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀]`. Rewrite using `[hei, ← zpow_add₀ hv0, add_neg_cancel, zpow_zero]`. Establish `hε : _root_.GlobalTheory.SplitFlip.diagGL εv ∈ _root_.GlobalTheory.SplitWeil.KO k (n ⊕ Fin c)`. Rewrite using `[_root_.GlobalTheory.SplitFlip.mem_KO_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce `i j`. Rewrite using `[_root_.GlobalTheory.SplitFlip.diagGL_val, diagonal_apply]`. Use `split_ifs`. Rewrite using `[Valuation.mem_integer_iff, hval]`.

Conclude with `zero_mem _`. Introduce `i j`. Rewrite using `[hεinv, _root_.GlobalTheory.SplitFlip.diagGL_val, diagonal_apply]`. Use `split_ifs`. Rewrite using `[Valuation.mem_integer_iff, Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, hval, inv_one]`.

Conclude with `zero_mem _`. Use `⟨u'⁻¹, inv_mem hu', g, e, z, ?_, ?_⟩` and prove the remaining obligations. Establish `hub : u'⁻¹ * (b * w) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.nfBasis ϖ g e z * (_root_.GlobalTheory.SplitFlip.diagGL εv * w)`. Rewrite using `[hbum, key]`. Use `group`.

Rewrite using `[hub, latOf_mul_of_mem_KO' _ _ (mul_mem hε hw)]`. Rewrite using `[latOf_mul_of_mem_KO' _ _ hw]`. Unfold `_root_.GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.MeetsIn`. Introduce `y`. Rewrite using `[_root_.GlobalTheory.StepData.mem_latOf, _root_.GlobalTheory.StepData.mem_latOf]`.

Establish `h1 : (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) *ᵥ Sum.elim ((↑g⁻¹ : Matrix n n k) *ᵥ y) 0 = Sum.elim y 0`. Rewrite using `[← hbB, h21, fromBlocks_mulVec]`. Simplify using `[← hgv, mulVec_mulVec]`. Establish `hv : (↑b⁻¹ : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) *ᵥ Sum.elim y 0 = Sum.elim ((↑g⁻¹ : Matrix n n k) *ᵥ y) 0`. Rewrite using `[← h1, mulVec_mulVec, Units.inv_mul, one_mulVec]`.

Rewrite using `[hv]`. Prove the components needed by the constructor for the conclusion. Introduce `H i`. Simplify using `using H (Sum.inl i)`. Introduce and unpack `H (i | i)`.

Simplify using `using H i`. Simplify using the standard rewrite rules.
-/
theorem _root_.GlobalTheory.StepData.NormalForm.normalFormModN : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], _root_.GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.NormalFormModN k := by
  intro k _ _ _ _ ϖ hϖ n _ _ c h
  obtain ⟨b, hbT, w, hw, rfl⟩ := _root_.GlobalTheory.SplitWeil.iwasawa_blockTriangular k (n ⊕ Fin c)
    (Sum.elim (fun _ => 0) (fun i => (i : ℕ) + 1)) h
  have hbP : (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).BlockTriangular
      (_root_.GlobalTheory.RootEx.lev 1) := by
    intro i j hij
    apply hbT
    unfold _root_.GlobalTheory.RootEx.lev at hij
    rcases i with i | i <;> rcases j with j | j <;> simp at hij ⊢ <;> omega
  obtain ⟨u', hu', m, hm0, hmb, hbum⟩ := _root_.GlobalTheory.RootEx.BlockLevi.exists_unip_mul_levi k n c 1 b hbP
  have h21 : (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₂₁ = 0 := by
    ext i j
    exact hbT (by simp)
  have hT : ((b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₂₂).BlockTriangular id := by
    intro i j hij
    exact hbT (by simp only [Sum.elim_inr]; exact Nat.succ_lt_succ hij)
  have hdet : (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).det ≠ 0 := b.det_ne_zero
  have hbB := fromBlocks_toBlocks (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
  rw [← hbB, h21, det_fromBlocks_zero₂₁, det_of_upperTriangular hT] at hdet
  have hG : (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁.det ≠ 0 := left_ne_zero_of_mul hdet
  have ht : ∀ i : Fin c, (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inr i) (Sum.inr i) ≠ 0 :=
    fun i => Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hdet) i (Finset.mem_univ i)
  set g : GL n k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hG with hg
  have hgv : (g : Matrix n n k) = (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁ := rfl
  choose e he using fun i => _root_.GlobalTheory.StepData.NormalForm.exists_valuation_eq_zpow hϖ (Units.mk0 _ (ht i))
  set z : n → k := fun r => if hc : 0 < c then
    (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl r) (Sum.inr ⟨0, hc⟩) *
      ((b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inr ⟨0, hc⟩) (Sum.inr ⟨0, hc⟩))⁻¹ else 0 with hz
  set εv : n ⊕ Fin c → kˣ := Sum.elim (fun _ => 1) (fun i => Units.mk0 _ (ht i) * ϖ ^ (-e i)) with hεv
  have hϖ0 : (ϖ : k) ≠ 0 := ϖ.ne_zero
  have key : m = _root_.GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.nfBasis ϖ g e z * _root_.GlobalTheory.SplitFlip.diagGL εv := by
    clear hbum hu' hbP hdet hbB hw hT h21 hϖ he
    ext r s
    rw [Units.val_mul, _root_.GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.nfBasis_val, _root_.GlobalTheory.SplitFlip.diagGL_val,
      mul_diagonal]
    rcases r with r | i <;> rcases s with s | j
    · rw [hmb _ _ (by simp [_root_.GlobalTheory.RootEx.lev])]
      simp [hεv, hgv, toBlocks₁₁]
    · by_cases hj : (j : ℕ) = 0
      · rw [hmb _ _ (by simp [_root_.GlobalTheory.RootEx.lev, hj])]
        have hc : 0 < c := j.pos
        have hj' : j = ⟨0, hc⟩ := Fin.ext hj
        subst hj'
        simp only [fromBlocks_apply₁₂, of_apply, hj, if_true, hz, dif_pos hc, hεv, Sum.elim_inr,
          Units.val_mul, Units.val_mk0, Units.val_zpow_eq_zpow_val, _root_.zpow_neg,
          Units.val_inv_eq_inv_val]
        have := ht ⟨0, hc⟩
        field_simp
      · rw [hm0 _ _ (by simp [_root_.GlobalTheory.RootEx.lev]; omega)]
        simp [hj]
    · by_cases hi : (i : ℕ) = 0
      · rw [hmb _ _ (by simp [_root_.GlobalTheory.RootEx.lev, hi])]
        simp only [fromBlocks_apply₂₁, Matrix.zero_apply, zero_mul]
        exact hbT (by simp)
      · rw [hm0 _ _ (by simp [_root_.GlobalTheory.RootEx.lev]; omega)]
        rw [fromBlocks_apply₂₁, Matrix.zero_apply, zero_mul]
    · by_cases hij : i = j
      · subst hij
        have := ht i
        rw [hmb _ _ rfl]
        simp only [fromBlocks_apply₂₂, diagonal_apply_eq, hεv, Sum.elim_inr,
          Units.val_mul, Units.val_mk0, Units.val_zpow_eq_zpow_val, _root_.zpow_neg,
          Units.val_inv_eq_inv_val]
        field_simp
      · rw [hm0 _ _ (by simp [_root_.GlobalTheory.RootEx.lev]; omega)]
        simp [diagonal_apply_ne _ hij]
  have hεinv : (_root_.GlobalTheory.SplitFlip.diagGL εv)⁻¹ = _root_.GlobalTheory.SplitFlip.diagGL εv⁻¹ := by
    apply inv_eq_of_mul_eq_one_right
    ext i j
    rw [Units.val_mul, _root_.GlobalTheory.SplitFlip.diagGL_val, _root_.GlobalTheory.SplitFlip.diagGL_val,
      diagonal_mul_diagonal, Units.val_one]
    simp [diagonal_apply, one_apply]
  have hv0 : valuation k (ϖ : k) ≠ 0 := (map_ne_zero _).mpr hϖ0
  have hval : ∀ i, valuation k (εv i : k) = 1 := by
    rintro (i | i)
    · simp [hεv]
    · have hei := he i
      rw [Units.val_mk0] at hei
      simp only [hεv, Sum.elim_inr, Units.val_mul, Units.val_mk0, Units.val_zpow_eq_zpow_val,
        map_mul, map_zpow₀]
      rw [hei, ← zpow_add₀ hv0, add_neg_cancel, zpow_zero]
  have hε : _root_.GlobalTheory.SplitFlip.diagGL εv ∈ _root_.GlobalTheory.SplitWeil.KO k (n ⊕ Fin c) := by
    rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff]
    constructor
    · intro i j
      rw [_root_.GlobalTheory.SplitFlip.diagGL_val, diagonal_apply]
      split_ifs
      · rw [Valuation.mem_integer_iff, hval]
      · exact zero_mem _
    · intro i j
      rw [hεinv, _root_.GlobalTheory.SplitFlip.diagGL_val, diagonal_apply]
      split_ifs
      · rw [Valuation.mem_integer_iff, Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, hval,
          inv_one]
      · exact zero_mem _
  refine ⟨u'⁻¹, inv_mem hu', g, e, z, ?_, ?_⟩
  · have hub : u'⁻¹ * (b * w) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.nfBasis ϖ g e z * (_root_.GlobalTheory.SplitFlip.diagGL εv * w) := by
      rw [hbum, key]; group
    rw [hub, latOf_mul_of_mem_KO' _ _ (mul_mem hε hw)]
  · rw [latOf_mul_of_mem_KO' _ _ hw]
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.MeetsIn
    intro y
    rw [_root_.GlobalTheory.StepData.mem_latOf, _root_.GlobalTheory.StepData.mem_latOf]
    have h1 : (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) *ᵥ Sum.elim ((↑g⁻¹ : Matrix n n k) *ᵥ y) 0 =
        Sum.elim y 0 := by
      rw [← hbB, h21, fromBlocks_mulVec]
      simp [← hgv, mulVec_mulVec]
    have hv : (↑b⁻¹ : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) *ᵥ Sum.elim y 0 =
        Sum.elim ((↑g⁻¹ : Matrix n n k) *ᵥ y) 0 := by
      rw [← h1, mulVec_mulVec, Units.inv_mul, one_mulVec]
    rw [hv]
    constructor
    · intro H i
      simpa using H (Sum.inl i)
    · rintro H (i | i)
      · simpa using H i
      · simp

end GlobalTheory.StepData.NormalForm
