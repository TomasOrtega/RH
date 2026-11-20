import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdSubOfDvdSubX
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.ExpandCoeff

open Polynomial

/- English proof (translation)
Introduce `l hl a _ E hE hirr z hz hroot i hi`. Establish `hl0 : 0 < l` using `hl.out.pos`. Use `set K := ↥(Kunr l a)`. Establish `hzi : IsIntegral K z` using `Algebra.IsIntegral.isIntegral z`. Use `set m := minpoly K z with hm`.

Use `set φ := algebraMap K (Om l)`. Use `set EK := E.map (GlobalTheory.TameFrob.iota l a) with hEKdef`. Use `set Q := E.map (GlobalTheory.TameFrob.iotaO l a) with hQdef`. Establish `hcomp : φ.comp (GlobalTheory.TameFrob.iota l a) = GlobalTheory.TameFrob.iotaO l a` using `RingHom.ext fun w => rfl`. Establish `hmapQ : EK.map φ = Q` using `by rw [hEKdef, Polynomial.map_map, hcomp]`.

Establish `hev : ∀ y : Om l, Polynomial.aeval y EK = Q.eval y` using `fun y => by`. Rewrite using `[Polynomial.aeval_def, ← Polynomial.eval_map, hmapQ]`. Take `⟨y0, hy0⟩` from `IsAlgClosed.exists_pow_nat_eq z hl0`. Establish `hQ0 : Q.IsRoot y0` using `hroot z (minpoly.aeval K z) y0 hy0`. Establish `hEK : EK.Monic` using `hE.map _`.

Establish `hEKmin : EK = minpoly K y0` using `minpoly.eq_of_irreducible_of_monic hirr (by rw [hev]; exact hQ0) hEK`. Use `set P := Polynomial.expand K l m with hPdef`. Establish `hPmon : P.Monic` using `(minpoly.monic hzi).expand hl0`. Establish `hPy0 : Polynomial.aeval y0 P = 0`. Rewrite using `[hPdef, Polynomial.expand_aeval, hy0, minpoly.aeval]`.

Establish `hdvd : EK ∣ P` using `hEKmin ▸ minpoly.dvd K y0 hPy0`. Establish `hmsep : m.Separable` using `Algebra.IsSeparable.isSeparable K z`. Establish `hc0 : m.coeff 0 ≠ 0` using `minpoly.coeff_zero_ne_zero hzi hz`. Establish `hPsep : P.Separable`. Unfold `Polynomial.Separable`.

Rewrite using `[Polynomial.derivative_expand]`. Establish `h1 : IsCoprime P (Polynomial.expand K l (Polynomial.derivative m))` using `IsCoprime.map hmsep (Polynomial.expand K l).toRingHom`. Establish `h2 : IsCoprime P (Polynomial.X ^ (l - 1))`. Use `IsCoprime.pow_right ?_` and prove the remaining obligations. Use `IsCoprime.symm ((Polynomial.irreducible_X.coprime_iff_not_dvd).2 ?_)` and prove the remaining obligations.

Rewrite using `[Polynomial.X_dvd_iff, hPdef, Polynomial.coeff_expand hl0, if_pos (dvd_zero l), Nat.zero_div]`. Conclude with `hc0`. Establish `h3 : IsCoprime P ((l : K[X]))`. Establish `hu : IsUnit ((l : K[X]))`. Rewrite using `[← Polynomial.C_eq_natCast]`.

Conclude with `Polynomial.isUnit_C.2 (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hl.out.ne_zero))`. Conclude with `⟨0, ↑(hu.unit⁻¹), by rw [zero_mul, zero_add, IsUnit.val_inv_mul]⟩`. Conclude with `h1.mul_right (h3.mul_right h2)`. Use `set P' := P.map φ with hP'def`. Establish `hP'sep : P'.Separable` using `hPsep.map`.

Establish `hP'0 : P' ≠ 0` using `(hPmon.map φ).ne_zero`. Establish `hQne : Q ≠ 0` using `(hE.map _).ne_zero`. Establish `hnod : P'.roots.Nodup` using `Polynomial.nodup_roots hP'sep`. Establish `hcard : Multiset.card P'.roots = P'.natDegree` using `(Polynomial.splits_iff_card_roots).1 (IsAlgClosed.splits P')`. Establish `hle : P'.roots ≤ Q.roots`.

Use `(Multiset.le_iff_subset hnod).2 fun y hy => ?_` and prove the remaining obligations. Rewrite `hy` using `[Polynomial.mem_roots hP'0, Polynomial.IsRoot, hP'def, Polynomial.eval_map, ← Polynomial.aeval_def, hPdef, Polynomial.expand_aeval]`. Conclude with `(Polynomial.mem_roots hQne).2 (hroot _ hy y rfl)`. Establish `hdeg : P.natDegree ≤ EK.natDegree`. Establish `e1 : P'.natDegree = P.natDegree` using `Polynomial.natDegree_map φ`.

Establish `e2 : EK.natDegree = Q.natDegree`. Rewrite using `[hEKdef, hQdef, Polynomial.natDegree_map_eq_of_injective (GlobalTheory.TameFrob.iota_injective l a), Polynomial.natDegree_map_eq_of_injective (GlobalTheory.TameFrob.iotaO_injective l a)]`. Rewrite using `[← e1, e2, ← hcard]`. Conclude with `(Multiset.card_le_card hle).trans (Polynomial.card_roots' Q)`. Establish `hEq : P = EK` using `Polynomial.eq_of_monic_of_dvd_of_natDegree_le hEK hPmon hdvd hdeg`.

Establish `hci : GlobalTheory.TameFrob.iota l a (E.coeff i) = 0`. Rewrite using `[← Polynomial.coeff_map, ← hEKdef, ← hEq, hPdef, Polynomial.coeff_expand hl0, if_neg hi]`. Conclude with `GlobalTheory.TameFrob.iota_injective l a (hci.trans (map_zero _).symm)`.
-/
theorem coeff_eq_zero_of_roots : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (E : Polynomial (Wq l a)), E.Monic →
    Irreducible (E.map (GlobalTheory.TameFrob.iota l a)) → ∀ z : Om l, z ≠ 0 →
    (∀ z' : Om l, Polynomial.aeval z' (minpoly (↥(Kunr l a)) z) = 0 → ∀ y : Om l, y ^ l = z' →
      (E.map (GlobalTheory.TameFrob.iotaO l a)).IsRoot y) →
    ∀ i, ¬ l ∣ i → E.coeff i = 0 := by
  intro l hl a _ E hE hirr z hz hroot i hi
  have hl0 : 0 < l := hl.out.pos
  set K := ↥(Kunr l a)
  have hzi : IsIntegral K z := Algebra.IsIntegral.isIntegral z
  set m := minpoly K z with hm
  set φ := algebraMap K (Om l)
  set EK := E.map (GlobalTheory.TameFrob.iota l a) with hEKdef
  set Q := E.map (GlobalTheory.TameFrob.iotaO l a) with hQdef
  have hcomp : φ.comp (GlobalTheory.TameFrob.iota l a) = GlobalTheory.TameFrob.iotaO l a := RingHom.ext fun w => rfl
  have hmapQ : EK.map φ = Q := by rw [hEKdef, Polynomial.map_map, hcomp]
  have hev : ∀ y : Om l, Polynomial.aeval y EK = Q.eval y := fun y => by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hmapQ]
  obtain ⟨y0, hy0⟩ := IsAlgClosed.exists_pow_nat_eq z hl0
  have hQ0 : Q.IsRoot y0 := hroot z (minpoly.aeval K z) y0 hy0
  have hEK : EK.Monic := hE.map _
  have hEKmin : EK = minpoly K y0 := minpoly.eq_of_irreducible_of_monic hirr (by rw [hev]; exact hQ0) hEK
  set P := Polynomial.expand K l m with hPdef
  have hPmon : P.Monic := (minpoly.monic hzi).expand hl0
  have hPy0 : Polynomial.aeval y0 P = 0 := by
    rw [hPdef, Polynomial.expand_aeval, hy0, minpoly.aeval]
  have hdvd : EK ∣ P := hEKmin ▸ minpoly.dvd K y0 hPy0

  have hmsep : m.Separable := Algebra.IsSeparable.isSeparable K z
  have hc0 : m.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hzi hz
  have hPsep : P.Separable := by
    unfold Polynomial.Separable
    rw [Polynomial.derivative_expand]
    have h1 : IsCoprime P (Polynomial.expand K l (Polynomial.derivative m)) :=
      IsCoprime.map hmsep (Polynomial.expand K l).toRingHom
    have h2 : IsCoprime P (Polynomial.X ^ (l - 1)) := by
      refine IsCoprime.pow_right ?_
      refine IsCoprime.symm ((Polynomial.irreducible_X.coprime_iff_not_dvd).2 ?_)
      rw [Polynomial.X_dvd_iff, hPdef, Polynomial.coeff_expand hl0, if_pos (dvd_zero l), Nat.zero_div]
      exact hc0
    have h3 : IsCoprime P ((l : K[X])) := by
      have hu : IsUnit ((l : K[X])) := by
        rw [← Polynomial.C_eq_natCast]
        exact Polynomial.isUnit_C.2 (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hl.out.ne_zero))
      exact ⟨0, ↑(hu.unit⁻¹), by rw [zero_mul, zero_add, IsUnit.val_inv_mul]⟩
    exact h1.mul_right (h3.mul_right h2)
  set P' := P.map φ with hP'def
  have hP'sep : P'.Separable := hPsep.map
  have hP'0 : P' ≠ 0 := (hPmon.map φ).ne_zero
  have hQne : Q ≠ 0 := (hE.map _).ne_zero
  have hnod : P'.roots.Nodup := Polynomial.nodup_roots hP'sep
  have hcard : Multiset.card P'.roots = P'.natDegree :=
    (Polynomial.splits_iff_card_roots).1 (IsAlgClosed.splits P')
  have hle : P'.roots ≤ Q.roots := by
    refine (Multiset.le_iff_subset hnod).2 fun y hy => ?_
    rw [Polynomial.mem_roots hP'0, Polynomial.IsRoot, hP'def, Polynomial.eval_map, ← Polynomial.aeval_def,
      hPdef, Polynomial.expand_aeval] at hy
    exact (Polynomial.mem_roots hQne).2 (hroot _ hy y rfl)
  have hdeg : P.natDegree ≤ EK.natDegree := by
    have e1 : P'.natDegree = P.natDegree := Polynomial.natDegree_map φ
    have e2 : EK.natDegree = Q.natDegree := by
      rw [hEKdef, hQdef, Polynomial.natDegree_map_eq_of_injective (GlobalTheory.TameFrob.iota_injective l a),
        Polynomial.natDegree_map_eq_of_injective (GlobalTheory.TameFrob.iotaO_injective l a)]
    rw [← e1, e2, ← hcard]
    exact (Multiset.card_le_card hle).trans (Polynomial.card_roots' Q)
  have hEq : P = EK := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hEK hPmon hdvd hdeg
  have hci : GlobalTheory.TameFrob.iota l a (E.coeff i) = 0 := by
    rw [← Polynomial.coeff_map, ← hEKdef, ← hEq, hPdef, Polynomial.coeff_expand hl0, if_neg hi]
  exact GlobalTheory.TameFrob.iota_injective l a (hci.trans (map_zero _).symm)

end GlobalTheory.ExpandCoeff
