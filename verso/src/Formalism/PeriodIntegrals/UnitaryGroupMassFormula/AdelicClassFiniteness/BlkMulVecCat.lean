import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.HformSelfStar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.PartSplitOfOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.HformSingleLeft
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.SpComp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.SpDen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.SplHformZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.PartBetween

noncomputable section

namespace PIW.AdelClassFin

open Formalism.UG NumberField
open scoped Matrix

namespace SpO

def cat {E : Type} [Field E] {m k n : ℕ} (e : Fin k ⊕ Fin n ≃ Fin m) (c : Fin k → E) (y : Fin n → E) :
    Fin m → E :=
  fun r => Sum.elim c y (e.symm r)

def blk {E : Type} [Field E] {m k n : ℕ} (e : Fin k ⊕ Fin n ≃ Fin m) (V : Matrix (Fin m) (Fin k) E)
    (W : Matrix (Fin m) (Fin n) E) : Matrix (Fin m) (Fin m) E :=
  Matrix.of fun r s => Sum.elim (fun i => V r i) (fun j => W r j) (e.symm s)

def catR {E : Type} [Field E] (R : Type) [CommRing R] [Algebra R E] {m k n : ℕ} (e : Fin k ⊕ Fin n ≃ Fin m) :
    (Fin n → E) →ₗ[R] (Fin m → E) where
  toFun y := cat e 0 y
  map_add' y y' := by
    funext r
    simp only [cat, Pi.add_apply]
    cases e.symm r <;> simp
  map_smul' a y := by
    funext r
    simp only [cat, Pi.smul_apply, RingHom.id_apply]
    cases e.symm r <;> simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem catR_apply {E : Type} [Field E] (R : Type) [CommRing R] [Algebra R E] {m k n : ℕ}
    (e : Fin k ⊕ Fin n ≃ Fin m) (y : Fin n → E) : catR R e y = cat e 0 y := rfl

/- English proof (translation)
Use function extensionality and compare the values at `r`. Simplify using `only [cat, Pi.add_apply]`. Apply the tactic sequence `cases e.symm r <;> simp`.
-/
theorem cat_add {E : Type} [Field E] {m k n : ℕ} (e : Fin k ⊕ Fin n ≃ Fin m) (c : Fin k → E) (y : Fin n → E) :
    cat e c 0 + cat e 0 y = cat e c y := by
  funext r
  simp only [cat, Pi.add_apply]
  cases e.symm r <;> simp

/- English proof (translation)
Use function extensionality and compare the values at `r`. Simplify using `only [Matrix.mulVec, dotProduct, blk, Matrix.of_apply, Pi.add_apply]`. Rewrite using `[← Equiv.sum_comp e, Fintype.sum_sum_type]`. Simplify using the standard rewrite rules.
-/
theorem blk_mulVec {E : Type} [Field E] {m k n : ℕ} (e : Fin k ⊕ Fin n ≃ Fin m) (V : Matrix (Fin m) (Fin k) E)
    (W : Matrix (Fin m) (Fin n) E) (x : Fin m → E) :
    blk e V W *ᵥ x = V *ᵥ (fun i => x (e (Sum.inl i))) + W *ᵥ (fun j => x (e (Sum.inr j))) := by
  funext r
  simp only [Matrix.mulVec, dotProduct, blk, Matrix.of_apply, Pi.add_apply]
  rw [← Equiv.sum_comp e, Fintype.sum_sum_type]
  simp

/- English proof (translation)
Rewrite using `[blk_mulVec]`. Simplify using `[cat]`.
-/
theorem blk_mulVec_cat {E : Type} [Field E] {m k n : ℕ} (e : Fin k ⊕ Fin n ≃ Fin m) (V : Matrix (Fin m) (Fin k) E)
    (W : Matrix (Fin m) (Fin n) E) (c : Fin k → E) (y : Fin n → E) :
    blk e V W *ᵥ cat e c y = V *ᵥ c + W *ᵥ y := by
  rw [blk_mulVec]
  simp [cat]

/- English proof (translation)
Use function extensionality and compare the values at `r`. Take `⟨t, rfl⟩` from `e.surjective r`. Consider the cases of `t with`. Consider the case `inl a => simp [cat, Pi.single_apply, e.injective.eq_iff]`. Consider the case `inr b => simp [cat, Pi.single_apply, e.injective.eq_iff]`.
-/
theorem single_inl {E : Type} [Field E] {m k n : ℕ} (e : Fin k ⊕ Fin n ≃ Fin m) (i : Fin k) :
    (Pi.single (e (Sum.inl i)) (1 : E) : Fin m → E) = cat e (Pi.single i 1) 0 := by
  funext r
  obtain ⟨t, rfl⟩ := e.surjective r
  cases t with
  | inl a => simp [cat, Pi.single_apply, e.injective.eq_iff]
  | inr b => simp [cat, Pi.single_apply, e.injective.eq_iff]

/- English proof (translation)
Use function extensionality and compare the values at `r`. Take `⟨t, rfl⟩` from `e.surjective r`. Consider the cases of `t with`. Consider the case `inl a => simp [cat, Pi.single_apply, e.injective.eq_iff]`. Consider the case `inr b => simp [cat, Pi.single_apply, e.injective.eq_iff]`.
-/
theorem single_inr {E : Type} [Field E] {m k n : ℕ} (e : Fin k ⊕ Fin n ≃ Fin m) (j : Fin n) :
    (Pi.single (e (Sum.inr j)) (1 : E) : Fin m → E) = cat e 0 (Pi.single j 1) := by
  funext r
  obtain ⟨t, rfl⟩ := e.surjective r
  cases t with
  | inl a => simp [cat, Pi.single_apply, e.injective.eq_iff]
  | inr b => simp [cat, Pi.single_apply, e.injective.eq_iff]

/- English proof (translation)
Use function extensionality and compare the values at `r`. Take `⟨t, rfl⟩` from `e.surjective r`. Consider the cases of `t with`. Consider the case `inl a => simp [cat, Finset.sum_apply, Pi.single_apply, e.injective.eq_iff]`. Consider the case `inr b => simp [cat, Finset.sum_apply, Pi.single_apply, e.injective.eq_iff]`.
-/
theorem cat_eq_sum {E : Type} [Field E] {m k n : ℕ} (e : Fin k ⊕ Fin n ≃ Fin m) (c : Fin k → E) :
    cat e c 0 = ∑ i, c i • (Pi.single (e (Sum.inl i)) (1 : E) : Fin m → E) := by
  funext r
  obtain ⟨t, rfl⟩ := e.surjective r
  cases t with
  | inl a => simp [cat, Finset.sum_apply, Pi.single_apply, e.injective.eq_iff]
  | inr b => simp [cat, Finset.sum_apply, Pi.single_apply, e.injective.eq_iff]

/- English proof (translation)
Simplify using `only [cT, hform, Matrix.mul_apply, Matrix.mulVec_single_one, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Both sides reduce to the same expression.
-/
theorem entry_eq {E : Type} [Field E] [StarRing E] {m : ℕ} (J A : Matrix (Fin m) (Fin m) E) (r s : Fin m) :
    (cT (starRingEnd E) A * J * A) r s =
      hform (starRingEnd E) J (A *ᵥ Pi.single r 1) (A *ᵥ Pi.single s 1) := by
  simp only [cT, hform, Matrix.mul_apply, Matrix.mulVec_single_one, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

end SpO

open SpO in
/- English proof (translation)
Introduce `E _ _ _ m k hk ih d hd Γ hΓ`. Distinguish the cases in `hkm : k ≤ m`. Use `swap`. Use `⟨∅, Set.finite_empty, ?_⟩` and prove the remaining obligations. Introduce and unpack `p ⟨_, v, _, hvΓ⟩`.

It suffices to derive a contradiction. Apply `hkm` to reduce the goal to its premises. Establish `hg : cT (starRingEnd E) (Matrix.of fun r i => v i r) * p.1 * (Matrix.of fun r i => v i r) = Γ` using `(gram_eq p.1 v).symm.trans (Set.mem_singleton_iff.mp hvΓ)`. Use `(spComp E k m (cT (starRingEnd E) (Matrix.of fun r i => v i r) * p.1) ((Matrix.of fun r i => v i r) * Γ⁻¹) ?_).1` and prove the remaining obligations. Rewrite using `[← Matrix.mul_assoc, hg, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hΓ)]`.

Take `⟨D, hD1, hDΓ⟩` from `spDen E k Γ⁻¹`. Establish `hnm : m - k < m` using `by omega`. Establish `hdD : 1 ≤ d * D` using `Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))`. Take `⟨T', hT'f, hT'⟩` from `ih (m - k) hnm (d * D) hdD`. Set `e : Fin k ⊕ Fin (m - k) ≃ Fin m` to `finSumFinEquiv.trans (finCongr (by omega))`.

Set `N : Submodule (𝓞 E) (Fin (m - k) → E) → Submodule (𝓞 E) (Fin m → E)` to `fun M' => Submodule.span (𝓞 E) (Set.range fun i : Fin k => (Pi.single (e (Sum.inl i)) (1 : E) : Fin m → E)) ⊔ M'.map (catR (𝓞 E) e)`. Set `Jb : Matrix (Fin (m - k)) (Fin (m - k)) E → Matrix (Fin m) (Fin m) E` to `fun J' => Matrix.of fun r s => Matrix.fromBlocks Γ 0 0 J' (e.symm r) (e.symm s)`. Set `T : Set (Matrix (Fin m) (Fin m) E × Submodule (𝓞 E) (Fin m → E))` to `⋃ q' ∈ {q' | q' ∈ T' ∧ q'.2.FG}, (fun M₀ => (Jb q'.1, M₀)) '' {M₀ : Submodule (𝓞 E) (Fin m → E) | N q'.2 ≤ M₀ ∧ ∀ x ∈ M₀, (D : 𝓞 E) • x ∈ N q'.2}`. Establish `hD0 : (D : 𝓞 E) ≠ 0`. Introduce `h0`.

Establish `h1` using `congrArg (algebraMap (𝓞 E) E) h0`. Rewrite `h1` using `[map_natCast, map_zero, Nat.cast_eq_zero]`. Use linear arithmetic over natural numbers and integers. Use `⟨T, ?_, ?_⟩` and prove the remaining obligations. Use `Set.Finite.biUnion (hT'f.subset fun q h => h.1) fun q' hq' => ?_` and prove the remaining obligations.

Use `Set.Finite.image _ (partBetween E m (N q'.2) ?_ (D : 𝓞 E) hD0)` and prove the remaining obligations. Conclude with `(Submodule.fg_span (Set.finite_range _)).sup (hq'.2.map _)`. Introduce and unpack `p ⟨hp, v, hv, hvΓ⟩`. Establish `hg : cT (starRingEnd E) (Matrix.of fun r i => v i r) * p.1 * (Matrix.of fun r i => v i r) = Γ` using `(gram_eq p.1 v).symm.trans (Set.mem_singleton_iff.mp hvΓ)`. Use `set V : Matrix (Fin m) (Fin k) E := Matrix.of fun r i => v i r with hVdef`.

Establish `hPR : (cT (starRingEnd E) V * p.1) * (V * Γ⁻¹) = 1`. Rewrite using `[← Matrix.mul_assoc, hg, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hΓ)]`. Take `⟨-, U, hPU, hUinj, hUsurj⟩` from `spComp E k m _ _ hPR`. Establish `hVM : ∀ i, (fun r => V r i) ∈ p.2` using `fun i => hv i`. Take `⟨hLat', hdec⟩` from `spLat E m k (m - k) d D p.1 p.2 V U hp hVM hD1 (by rw [hg]; exact hΓ) (by rw [hg]; exact hDΓ) hPU hUinj hUsurj`.

Take `⟨q', hq', B, hB1, hB2⟩` from `hT' _ hLat'`. Use `set W : Matrix (Fin m) (Fin (m - k)) E := U * (B : Matrix (Fin (m - k)) (Fin (m - k)) E) with hWdef`. Use `set A : Matrix (Fin m) (Fin m) E := blk e V W with hAdef`. Establish `hJh : p.1ᴴ = p.1` using `(isHerm_iff _).1 hp.1`. Establish `hUV : cT (starRingEnd E) U * p.1 * V = 0`.

Establish `h` using `congrArg Matrix.conjTranspose hPU`. Rewrite `h`, the goal using `[cT_star]`. Rewrite `h` using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJh, Matrix.conjTranspose_zero, ← Matrix.mul_assoc]`. Conclude with `h`. Establish `hPW : cT (starRingEnd E) V * p.1 * W = 0`.

Rewrite using `[hWdef, ← Matrix.mul_assoc, hPU, Matrix.zero_mul]`. Establish `hWy : ∀ y, W *ᵥ y = U *ᵥ ((B : Matrix (Fin (m - k)) (Fin (m - k)) E) *ᵥ y)` using `fun y => by`. Rewrite using `[hWdef, Matrix.mulVec_mulVec]`. Establish `hker : ∀ x, A *ᵥ x = 0 → x = 0`. Introduce `x hx`.

Rewrite `hx` using `[hAdef, blk_mulVec]`. Establish `h1` using `congrArg (fun z => (cT (starRingEnd E) V * p.1) *ᵥ z) hx`. Simplify using `only [Matrix.mulVec_add, Matrix.mulVec_mulVec, hg, hPW, Matrix.zero_mulVec, add_zero, Matrix.mulVec_zero] at h1`. Establish `hΓu : IsUnit Γ` using `(Matrix.isUnit_iff_isUnit_det Γ).mpr (isUnit_iff_ne_zero.mpr hΓ)`. Establish `hc0 : (fun i => x (e (Sum.inl i))) = 0` using `Matrix.mulVec_injective_iff_isUnit.mpr hΓu (by rw [h1, Matrix.mulVec_zero])`.

Rewrite `hx` using `[hc0, Matrix.mulVec_zero, zero_add, hWy]`. Establish `hBy : (B : Matrix (Fin (m - k)) (Fin (m - k)) E) *ᵥ (fun j => x (e (Sum.inr j))) = 0` using `hUinj (by rw [hx, Matrix.mulVec_zero])`. Establish `hy0 : (fun j => x (e (Sum.inr j))) = 0` using `Matrix.mulVec_injective_iff_isUnit.mpr (Units.isUnit B) (by rw [hBy, Matrix.mulVec_zero])`. Use function extensionality and compare the values at `r`. Take `⟨t, rfl⟩` from `e.surjective r`.

Consider the cases of `t with`. Consider the case `inl i => exact congrFun hc0 i`. Consider the case `inr j => exact congrFun hy0 j`. Establish `hAinj : Function.Injective A.mulVec`. Introduce `x x' h`.

Use `hker (x - x') (by rw [Matrix.mulVec_sub]; exact sub_eq_zero.mpr h)` as an intermediate fact. Conclude with `sub_eq_zero.mp this`. Establish `hdetA : A.det ≠ 0` using `((Matrix.isUnit_iff_isUnit_det A).mp (Matrix.mulVec_injective_iff_isUnit.mp hAinj)).ne_zero`. Use `set A' : GL (Fin m) E := Matrix.GeneralLinearGroup.mkOfDetNeZero A hdetA with hA'def`. Establish `hA'v : (A' : Matrix (Fin m) (Fin m) E) = A` using `rfl`.

Establish `hAcat : ∀ c y, A *ᵥ cat e c y = V *ᵥ c + U *ᵥ ((B : Matrix (Fin (m - k)) (Fin (m - k)) E) *ᵥ y)`. Introduce `c y`. Rewrite using `[hAdef, blk_mulVec_cat, hWy]`. Establish `hcol1 : ∀ i, A *ᵥ Pi.single (e (Sum.inl i)) 1 = V *ᵥ Pi.single i 1` using `fun i => by`. Rewrite using `[single_inl, hAcat, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]`.

Establish `hcol2 : ∀ j, A *ᵥ Pi.single (e (Sum.inr j)) 1 = U *ᵥ ((B : Matrix (Fin (m - k)) (Fin (m - k)) E) *ᵥ Pi.single j 1)` using `fun j => by`. Rewrite using `[single_inr, hAcat, Matrix.mulVec_zero, zero_add]`. Use `set M₀ : Submodule (𝓞 E) (Fin m → E) := p.2.comap (A.mulVecLin.restrictScalars (𝓞 E)) with hM₀`. Establish `hmem : ∀ x, x ∈ M₀ ↔ A *ᵥ x ∈ p.2` using `fun x => Iff.rfl`. Establish `hfg' : q'.2.FG`.

Establish `heq : q'.2 = (p.2.comap (U.mulVecLin.restrictScalars (𝓞 E))).map (((B⁻¹ : GL (Fin (m - k)) E) : Matrix (Fin (m - k)) (Fin (m - k)) E).mulVecLin.restrictScalars (𝓞 E))`. Use extensionality with `w`. Simplify using `only [Submodule.mem_map, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `hw`.

Use `⟨(B : Matrix (Fin (m - k)) (Fin (m - k)) E) *ᵥ w, (hB2 _).2 ⟨w, hw, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Introduce and unpack `⟨u, hu, rfl⟩`. Take `⟨w, hw, rfl⟩` from `(hB2 u).1 hu`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`.

Conclude with `hw`. Rewrite using `[heq]`. Conclude with `hLat'.2.2.1.map _`. Establish `hNle : N q'.2 ≤ M₀`. Use `sup_le ?_ ?_` and prove the remaining obligations.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[SetLike.mem_coe, hmem, hcol1, Matrix.mulVec_single_one]`. Conclude with `hv i`. Rewrite using `[Submodule.map_le_iff_le_comap]`.

Introduce `y hy`. Rewrite using `[Submodule.mem_comap, catR_apply, hmem, hAcat, Matrix.mulVec_zero, zero_add]`. Conclude with `(hB2 _).2 ⟨y, hy, rfl⟩`. Establish `hDN : ∀ x ∈ M₀, (D : 𝓞 E) • x ∈ N q'.2`. Introduce `x hx`.

Take `⟨c, hc, y', hy'M, hdecx⟩` from `hdec _ ((hmem x).1 hx)`. Take `⟨y0, hy0, hBy0⟩` from `(hB2 y').1 hy'M`. Establish `hxe : (D : 𝓞 E) • x = cat e c 0 + catR (𝓞 E) e y0`. Apply `hAinj` to reduce the goal to its premises. Rewrite using `[Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, Matrix.mulVec_smul, hdecx, catR_apply, cat_add, hAcat, hBy0]`.

Rewrite using `[hxe]`. Use `Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right (Submodule.mem_map_of_mem hy0))` and prove the remaining obligations. Rewrite using `[cat_eq_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `hc i`.

Rewrite using `[← ha, algebraMap_smul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Use `⟨(Jb q'.1, M₀), Set.mem_biUnion (x := q') ⟨hq', hfg'⟩ (Set.mem_image_of_mem _ ⟨hNle, hDN⟩), A', ?_, ?_⟩` and prove the remaining obligations. Use `show cT (starRingEnd E) (A' : Matrix (Fin m) (Fin m) E) * p.1 * (A' : Matrix (Fin m) (Fin m) E) = Jb q'.1`. Rewrite using `[hA'v]`.

Use extensionality with `r s`. Take `⟨t, rfl⟩` from `e.surjective r`. Take `⟨t', rfl⟩` from `e.surjective s`. Rewrite using `[entry_eq]`. Simplify using `only [Jb, Matrix.of_apply, Equiv.symm_apply_apply]`.

Apply the tactic sequence `rcases t with i | j <;> rcases t' with i' | j'`. Rewrite using `[hcol1, hcol1, hform_mulVec, hg, hform_single, Matrix.fromBlocks_apply₁₁]`. Rewrite using `[hcol1, hcol2, spl_cross p.1 V U hPU, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]`. Rewrite using `[hcol2, hcol1, spl_cross p.1 U V hUV, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]`. Rewrite using `[hcol2, hcol2, hform_mulVec, hform_mulVec, hB1, hform_single, Matrix.fromBlocks_apply₂₂]`.

Introduce `w`. Prove the components needed by the constructor for the conclusion. Introduce `hw`. Use `⟨((A'⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) *ᵥ w, ?_, ?_⟩` and prove the remaining obligations. Use `show A *ᵥ (((A'⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) *ᵥ w) ∈ p.2`.

Rewrite using `[← hA'v, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Conclude with `hw`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Introduce and unpack `⟨u, hu, rfl⟩`. Rewrite using `[hA'v]`.

Conclude with `hu`.
-/
theorem spOne : SpOne := by
  intro E _ _ _ m k hk ih d hd Γ hΓ
  classical
  by_cases hkm : k ≤ m
  swap
  · refine ⟨∅, Set.finite_empty, ?_⟩
    rintro p ⟨_, v, _, hvΓ⟩
    exfalso
    apply hkm
    have hg : cT (starRingEnd E) (Matrix.of fun r i => v i r) * p.1 * (Matrix.of fun r i => v i r) = Γ :=
      (gram_eq p.1 v).symm.trans (Set.mem_singleton_iff.mp hvΓ)
    refine (spComp E k m (cT (starRingEnd E) (Matrix.of fun r i => v i r) * p.1)
      ((Matrix.of fun r i => v i r) * Γ⁻¹) ?_).1
    rw [← Matrix.mul_assoc, hg, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hΓ)]
  obtain ⟨D, hD1, hDΓ⟩ := spDen E k Γ⁻¹
  have hnm : m - k < m := by omega
  have hdD : 1 ≤ d * D := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨T', hT'f, hT'⟩ := ih (m - k) hnm (d * D) hdD
  let e : Fin k ⊕ Fin (m - k) ≃ Fin m := finSumFinEquiv.trans (finCongr (by omega))
  let N : Submodule (𝓞 E) (Fin (m - k) → E) → Submodule (𝓞 E) (Fin m → E) := fun M' =>
    Submodule.span (𝓞 E) (Set.range fun i : Fin k => (Pi.single (e (Sum.inl i)) (1 : E) : Fin m → E)) ⊔
      M'.map (catR (𝓞 E) e)
  let Jb : Matrix (Fin (m - k)) (Fin (m - k)) E → Matrix (Fin m) (Fin m) E := fun J' =>
    Matrix.of fun r s => Matrix.fromBlocks Γ 0 0 J' (e.symm r) (e.symm s)
  let T : Set (Matrix (Fin m) (Fin m) E × Submodule (𝓞 E) (Fin m → E)) :=
    ⋃ q' ∈ {q' | q' ∈ T' ∧ q'.2.FG}, (fun M₀ => (Jb q'.1, M₀)) ''
      {M₀ : Submodule (𝓞 E) (Fin m → E) | N q'.2 ≤ M₀ ∧ ∀ x ∈ M₀, (D : 𝓞 E) • x ∈ N q'.2}
  have hD0 : (D : 𝓞 E) ≠ 0 := by
    intro h0
    have h1 := congrArg (algebraMap (𝓞 E) E) h0
    rw [map_natCast, map_zero, Nat.cast_eq_zero] at h1
    omega
  refine ⟨T, ?_, ?_⟩
  · refine Set.Finite.biUnion (hT'f.subset fun q h => h.1) fun q' hq' => ?_
    refine Set.Finite.image _ (partBetween E m (N q'.2) ?_ (D : 𝓞 E) hD0)
    exact (Submodule.fg_span (Set.finite_range _)).sup (hq'.2.map _)
  rintro p ⟨hp, v, hv, hvΓ⟩
  have hg : cT (starRingEnd E) (Matrix.of fun r i => v i r) * p.1 * (Matrix.of fun r i => v i r) = Γ :=
    (gram_eq p.1 v).symm.trans (Set.mem_singleton_iff.mp hvΓ)
  set V : Matrix (Fin m) (Fin k) E := Matrix.of fun r i => v i r with hVdef
  have hPR : (cT (starRingEnd E) V * p.1) * (V * Γ⁻¹) = 1 := by
    rw [← Matrix.mul_assoc, hg, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hΓ)]
  obtain ⟨-, U, hPU, hUinj, hUsurj⟩ := spComp E k m _ _ hPR
  have hVM : ∀ i, (fun r => V r i) ∈ p.2 := fun i => hv i
  obtain ⟨hLat', hdec⟩ := spLat E m k (m - k) d D p.1 p.2 V U hp hVM hD1 (by rw [hg]; exact hΓ)
    (by rw [hg]; exact hDΓ) hPU hUinj hUsurj
  obtain ⟨q', hq', B, hB1, hB2⟩ := hT' _ hLat'
  set W : Matrix (Fin m) (Fin (m - k)) E := U * (B : Matrix (Fin (m - k)) (Fin (m - k)) E) with hWdef
  set A : Matrix (Fin m) (Fin m) E := blk e V W with hAdef
  have hJh : p.1ᴴ = p.1 := (isHerm_iff _).1 hp.1
  have hUV : cT (starRingEnd E) U * p.1 * V = 0 := by
    have h := congrArg Matrix.conjTranspose hPU
    rw [cT_star] at h ⊢
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJh,
      Matrix.conjTranspose_zero, ← Matrix.mul_assoc] at h
    exact h
  have hPW : cT (starRingEnd E) V * p.1 * W = 0 := by
    rw [hWdef, ← Matrix.mul_assoc, hPU, Matrix.zero_mul]
  have hWy : ∀ y, W *ᵥ y = U *ᵥ ((B : Matrix (Fin (m - k)) (Fin (m - k)) E) *ᵥ y) := fun y => by
    rw [hWdef, Matrix.mulVec_mulVec]
  have hker : ∀ x, A *ᵥ x = 0 → x = 0 := by
    intro x hx
    rw [hAdef, blk_mulVec] at hx
    have h1 := congrArg (fun z => (cT (starRingEnd E) V * p.1) *ᵥ z) hx
    simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, hg, hPW, Matrix.zero_mulVec, add_zero,
      Matrix.mulVec_zero] at h1
    have hΓu : IsUnit Γ := (Matrix.isUnit_iff_isUnit_det Γ).mpr (isUnit_iff_ne_zero.mpr hΓ)
    have hc0 : (fun i => x (e (Sum.inl i))) = 0 :=
      Matrix.mulVec_injective_iff_isUnit.mpr hΓu (by rw [h1, Matrix.mulVec_zero])
    rw [hc0, Matrix.mulVec_zero, zero_add, hWy] at hx
    have hBy : (B : Matrix (Fin (m - k)) (Fin (m - k)) E) *ᵥ (fun j => x (e (Sum.inr j))) = 0 :=
      hUinj (by rw [hx, Matrix.mulVec_zero])
    have hy0 : (fun j => x (e (Sum.inr j))) = 0 :=
      Matrix.mulVec_injective_iff_isUnit.mpr (Units.isUnit B) (by rw [hBy, Matrix.mulVec_zero])
    funext r
    obtain ⟨t, rfl⟩ := e.surjective r
    cases t with
    | inl i => exact congrFun hc0 i
    | inr j => exact congrFun hy0 j
  have hAinj : Function.Injective A.mulVec := by
    intro x x' h
    have := hker (x - x') (by rw [Matrix.mulVec_sub]; exact sub_eq_zero.mpr h)
    exact sub_eq_zero.mp this
  have hdetA : A.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det A).mp (Matrix.mulVec_injective_iff_isUnit.mp hAinj)).ne_zero
  set A' : GL (Fin m) E := Matrix.GeneralLinearGroup.mkOfDetNeZero A hdetA with hA'def
  have hA'v : (A' : Matrix (Fin m) (Fin m) E) = A := rfl
  have hAcat : ∀ c y, A *ᵥ cat e c y = V *ᵥ c + U *ᵥ ((B : Matrix (Fin (m - k)) (Fin (m - k)) E) *ᵥ y) := by
    intro c y
    rw [hAdef, blk_mulVec_cat, hWy]
  have hcol1 : ∀ i, A *ᵥ Pi.single (e (Sum.inl i)) 1 = V *ᵥ Pi.single i 1 := fun i => by
    rw [single_inl, hAcat, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]
  have hcol2 : ∀ j, A *ᵥ Pi.single (e (Sum.inr j)) 1 =
      U *ᵥ ((B : Matrix (Fin (m - k)) (Fin (m - k)) E) *ᵥ Pi.single j 1) := fun j => by
    rw [single_inr, hAcat, Matrix.mulVec_zero, zero_add]
  set M₀ : Submodule (𝓞 E) (Fin m → E) := p.2.comap (A.mulVecLin.restrictScalars (𝓞 E)) with hM₀
  have hmem : ∀ x, x ∈ M₀ ↔ A *ᵥ x ∈ p.2 := fun x => Iff.rfl
  have hfg' : q'.2.FG := by
    have heq : q'.2 = (p.2.comap (U.mulVecLin.restrictScalars (𝓞 E))).map
        (((B⁻¹ : GL (Fin (m - k)) E) : Matrix (Fin (m - k)) (Fin (m - k)) E).mulVecLin.restrictScalars (𝓞 E)) := by
      ext w
      simp only [Submodule.mem_map, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply]
      constructor
      · intro hw
        refine ⟨(B : Matrix (Fin (m - k)) (Fin (m - k)) E) *ᵥ w, (hB2 _).2 ⟨w, hw, rfl⟩, ?_⟩
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      · rintro ⟨u, hu, rfl⟩
        obtain ⟨w, hw, rfl⟩ := (hB2 u).1 hu
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
        exact hw
    rw [heq]
    exact hLat'.2.2.1.map _
  have hNle : N q'.2 ≤ M₀ := by
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, hmem, hcol1, Matrix.mulVec_single_one]
      exact hv i
    · rw [Submodule.map_le_iff_le_comap]
      intro y hy
      rw [Submodule.mem_comap, catR_apply, hmem, hAcat, Matrix.mulVec_zero, zero_add]
      exact (hB2 _).2 ⟨y, hy, rfl⟩
  have hDN : ∀ x ∈ M₀, (D : 𝓞 E) • x ∈ N q'.2 := by
    intro x hx
    obtain ⟨c, hc, y', hy'M, hdecx⟩ := hdec _ ((hmem x).1 hx)
    obtain ⟨y0, hy0, hBy0⟩ := (hB2 y').1 hy'M
    have hxe : (D : 𝓞 E) • x = cat e c 0 + catR (𝓞 E) e y0 := by
      apply hAinj
      rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, Matrix.mulVec_smul, hdecx, catR_apply,
        cat_add, hAcat, hBy0]
    rw [hxe]
    refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right (Submodule.mem_map_of_mem hy0))
    rw [cat_eq_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨a, ha⟩ := hc i
    rw [← ha, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨(Jb q'.1, M₀), Set.mem_biUnion (x := q') ⟨hq', hfg'⟩ (Set.mem_image_of_mem _ ⟨hNle, hDN⟩), A', ?_, ?_⟩
  · show cT (starRingEnd E) (A' : Matrix (Fin m) (Fin m) E) * p.1 * (A' : Matrix (Fin m) (Fin m) E) = Jb q'.1
    rw [hA'v]
    ext r s
    obtain ⟨t, rfl⟩ := e.surjective r
    obtain ⟨t', rfl⟩ := e.surjective s
    rw [entry_eq]
    simp only [Jb, Matrix.of_apply, Equiv.symm_apply_apply]
    rcases t with i | j <;> rcases t' with i' | j'
    · rw [hcol1, hcol1, hform_mulVec, hg, hform_single, Matrix.fromBlocks_apply₁₁]
    · rw [hcol1, hcol2, spl_cross p.1 V U hPU, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
    · rw [hcol2, hcol1, spl_cross p.1 U V hUV, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    · rw [hcol2, hcol2, hform_mulVec, hform_mulVec, hB1, hform_single, Matrix.fromBlocks_apply₂₂]
  · intro w
    constructor
    · intro hw
      refine ⟨((A'⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) *ᵥ w, ?_, ?_⟩
      · show A *ᵥ (((A'⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) *ᵥ w) ∈ p.2
        rw [← hA'v, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
        exact hw
      · rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    · rintro ⟨u, hu, rfl⟩
      rw [hA'v]
      exact hu

end PIW.AdelClassFin
