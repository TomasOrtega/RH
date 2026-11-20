import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadNatZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW

section Block

variable {R S : Type} [CommRing R] [CommRing S] {j n : ℕ}

/- English proof (translation)
Use extensionality with `a b`. Express the relevant statement in the definitionally equal form `GroundTheory.Automorphic.FourierWhittaker.blockMat hj ((1 : Matrix (Fin j) (Fin j) S) - (1 : Matrix (Fin j) (Fin j) R).map s + (g : Matrix (Fin j) (Fin j) R).map s) a b = (1 : Matrix (Fin n) (Fin n) S) a b - s ((1 : Matrix (Fin n) (Fin n) R) a b) + s (GroundTheory.Automorphic.Fou …`. Rewrite using `[GroundTheory.Automorphic.FourierWhittaker.blockMat_apply, GroundTheory.Automorphic.FourierWhittaker.blockMat_apply]`. Distinguish the cases in `ha : a.val < j`. Distinguish the cases in `hb : b.val < j`.

Simplify using `only [dif_pos ha, dif_pos hb, Matrix.add_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.one_apply, Fin.ext_iff]`. Establish `hab : a ≠ b` using `fun h => hb (h ▸ ha)`. Simplify using `[ha, hb, hab, Matrix.one_apply]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Simplify using `[ha, Matrix.one_apply]`. Simplify using `[ha, hab, Matrix.one_apply]`.
-/
theorem blockGL_cornerGL (hj : j ≤ n) (s : R →ₙ+* S) (g : GL (Fin j) R) :
    GroundTheory.Automorphic.FourierWhittaker.blockGL hj (cornerGL j s g) =
      cornerGL n s (GroundTheory.Automorphic.FourierWhittaker.blockGL hj g) := by
  ext a b
  change GroundTheory.Automorphic.FourierWhittaker.blockMat hj
      ((1 : Matrix (Fin j) (Fin j) S) - (1 : Matrix (Fin j) (Fin j) R).map s + (g : Matrix (Fin j) (Fin j) R).map s) a b =
    (1 : Matrix (Fin n) (Fin n) S) a b - s ((1 : Matrix (Fin n) (Fin n) R) a b) +
      s (GroundTheory.Automorphic.FourierWhittaker.blockMat hj (g : Matrix (Fin j) (Fin j) R) a b)
  rw [GroundTheory.Automorphic.FourierWhittaker.blockMat_apply, GroundTheory.Automorphic.FourierWhittaker.blockMat_apply]
  by_cases ha : a.val < j
  · by_cases hb : b.val < j
    · simp only [dif_pos ha, dif_pos hb, Matrix.add_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.one_apply,
        Fin.ext_iff]
    · have hab : a ≠ b := fun h => hb (h ▸ ha)
      simp [ha, hb, hab, Matrix.one_apply]
  · by_cases hab : a = b
    · subst hab; simp [ha, Matrix.one_apply]
    · simp [ha, hab, Matrix.one_apply]

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[GroundTheory.Automorphic.FourierWhittaker.coe_blockGL, GroundTheory.Automorphic.FourierWhittaker.blockMat_apply]`. Simplify using `only [diagPow, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Matrix.diagonalRingHom_apply]`. Distinguish the cases in `ha : a.val < j`. Distinguish the cases in `hb : b.val < j`.

Simplify using `[ha, hb, Matrix.diagonal_apply, GlobalTheory.RSnmUnf.padNat, Fin.ext_iff, MulEquiv.piUnits]`. Establish `hab : a ≠ b` using `fun h => hb (h ▸ ha)`. Simplify using `[ha, hb, hab, Matrix.diagonal_apply]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Simplify using `[ha, Matrix.diagonal_apply, GlobalTheory.RSnmUnf.padNat, MulEquiv.piUnits]`. Simplify using `[ha, hab, Matrix.diagonal_apply]`.
-/
theorem blockGL_diagPow (hj : j ≤ n) (ϖ : Rˣ) (v : Fin j → ℕ) :
    GroundTheory.Automorphic.FourierWhittaker.blockGL hj (diagPow ϖ v) = diagPow ϖ (GlobalTheory.RSnmUnf.padNat (n := n) v) := by
  ext a b
  rw [GroundTheory.Automorphic.FourierWhittaker.coe_blockGL, GroundTheory.Automorphic.FourierWhittaker.blockMat_apply]
  simp only [diagPow, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Matrix.diagonalRingHom_apply]
  by_cases ha : a.val < j
  · by_cases hb : b.val < j
    · simp [ha, hb, Matrix.diagonal_apply, GlobalTheory.RSnmUnf.padNat, Fin.ext_iff, MulEquiv.piUnits]
    · have hab : a ≠ b := fun h => hb (h ▸ ha)
      simp [ha, hb, hab, Matrix.diagonal_apply]
  · by_cases hab : a = b
    · subst hab; simp [ha, Matrix.diagonal_apply, GlobalTheory.RSnmUnf.padNat, MulEquiv.piUnits]
    · simp [ha, hab, Matrix.diagonal_apply]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use function extensionality and compare the values at `i`. Use `congrFun h ⟨i.val, by omega⟩` as an intermediate fact. Simplify `this` using `[GlobalTheory.RSnmUnf.padNat, i.isLt]`.

Introduce and unpack `rfl`. Conclude with `GlobalTheory.RSnmUnf.padNat_zero`.
-/
theorem padNat_eq_zero_iff {m n : ℕ} (hmn : m ≤ n) (v : Fin m → ℕ) :
    GlobalTheory.RSnmUnf.padNat (n := n) v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext i
    have := congrFun h ⟨i.val, by omega⟩
    simpa [GlobalTheory.RSnmUnf.padNat, i.isLt] using this
  · rintro rfl
    exact GlobalTheory.RSnmUnf.padNat_zero

end Block

/- English proof (translation)
Establish `hsupp : (l.mapRange (GlobalTheory.RSnmUnf.padNat (n` using `m + r + 1 + 1)) GlobalTheory.RSnmUnf.padNat_zero).support = l.support := by`. Use extensionality with `w`. Simplify using `only [Finsupp.mem_support_iff, Finsupp.mapRange_apply, ne_eq]`. Rewrite using `[padNat_eq_zero_iff (by omega)]`. Unfold `tl`.

Rewrite using `[hsupp, map_list_prod, List.map_map]`. Use `congr 1`. Apply `List.map_congr_left` to reduce the goal to its premises. Introduce `w _`. Simplify using `only [Function.comp_apply, Finsupp.mapRange_apply]`.

Rewrite using `[finGL, locGL, blockGL_cornerGL, blockGL_cornerGL, blockGL_diagPow]`. Both sides reduce to the same expression.
-/
theorem blockGL_tl {E : Type} [Field E] [NumberField E] (m r : ℕ)
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ)) :
    GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) (GlobalTheory.JSW.tl ϖ l) =
      GlobalTheory.JSW.tl ϖ (l.mapRange GlobalTheory.RSnmUnf.padNat GlobalTheory.RSnmUnf.padNat_zero) := by
  have hsupp : (l.mapRange (GlobalTheory.RSnmUnf.padNat (n := m + r + 1 + 1)) GlobalTheory.RSnmUnf.padNat_zero).support = l.support := by
    ext w
    simp only [Finsupp.mem_support_iff, Finsupp.mapRange_apply, ne_eq]
    rw [padNat_eq_zero_iff (by omega)]
  unfold tl
  rw [hsupp, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro w _
  simp only [Function.comp_apply, Finsupp.mapRange_apply]
  rw [finGL, locGL, blockGL_cornerGL, blockGL_cornerGL, blockGL_diagPow]
  rfl

end GlobalTheory.JSW
