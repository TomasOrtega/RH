import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.TargetSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiProjPrimeMIdealOverGraph
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionExists
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistSubEqChartSecOver
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSegreBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RelDimMIdealOverEqTrdeg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsNeZeroOfWeight
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiProjPrimeSegreLift
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ZpowMemSubalgebraOfInvMem

open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2

namespace PositivityTheory.HtPt.Siub

/- English proof (translation)
Use `⟨⟨g, ?_, ?_⟩, fun _ => rfl⟩` and prove the remaining obligations. Introduce `inst v i x y`. Establish `h` using `hg v i x y`. Use `h` and compare the differences between its conclusion and the goal. Introduce `inst v i c x`.

Establish `hi : inst = instDecidableEqFin n` using `Subsingleton.elim _ _`. Substitute `hi` using the available equality. Establish `h` using `map_zsmul (AddMonoidHom.mk' (fun z : M => g (Function.update v i z)) (hg v i)) c x`. Simplify using `only [AddMonoidHom.mk'_apply] at h`. Use `h` and compare the differences between its conclusion and the goal.
-/
theorem exists_multilinear {M : Type} [AddCommGroup M] {n : ℕ} (g : (Fin n → M) → ℤ)
    (hg : ∀ (v : Fin n → M) (i : Fin n) (x y : M),
      g (Function.update v i (x + y)) = g (Function.update v i x) + g (Function.update v i y)) :
    ∃ f : MultilinearMap ℤ (fun _ : Fin n => M) ℤ, ∀ v, f v = g v := by
  refine ⟨⟨g, ?_, ?_⟩, fun _ => rfl⟩
  · intro inst v i x y
    have h := hg v i x y
    convert h
  · intro inst v i c x
    have hi : inst = instDecidableEqFin n := Subsingleton.elim _ _
    subst hi
    have h := map_zsmul (AddMonoidHom.mk' (fun z : M => g (Function.update v i z)) (hg v i)) c x
    simp only [AddMonoidHom.mk'_apply] at h
    convert h

/- English proof (translation)
Introduce `hK hS F _ K _ _ ι _ Ω _ _ y k₀ d μ hy hd hnef hpos`. Establish `hP` using `GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.isMultiProjPrime_mIdealOver (S := F) y hy.1`. Take `⟨f, hf⟩` from `exists_multilinear (M := K → ℤ) (n := d + 1) (fun v => GroundTheory.Heights₂.Heights.NumbersDVR.intNum F (mIdealOver F y) v) (GroundTheory.Heights₂.Heights.FieldNumbers.IntNumAdd.full F K ι (mIdealOver F y) hP.multiHomog hP.relevant (d + 1) hd)`. Take `⟨t, ht, hlt⟩` from `hnum (K → ℤ) d f μ (baseDeg k₀) (by rw [hf]; exact hpos)`. Take `⟨a, m, ha, hm, hva⟩` from `hK (d + 1) F K ι Ω y k₀ hy hd μ hnef t ht`.

Establish `hmpos : 0 < m`. Establish `ha' : (0 : ℚ) < a` using `by exact_mod_cast ha`. Establish `: (0 : ℚ) < m` using `by rw [hm]; exact mul_pos ha' ht`. Conclude with `this` after adjusting the coercions. Take `⟨r, rfl⟩` from `Int.eq_ofNat_of_zero_le hmpos.le`.

Establish `hr : 0 < r` using `by exact_mod_cast hmpos`. Establish `hlt'` using `hlt a r ha hm`. Rewrite `hlt'` using `[hf, hf]`. Establish `hq : (2 * (r : ℤ)) • baseDeg k₀ = (2 * r) • baseDeg k₀`. Rewrite using `[← natCast_zsmul]`.

Use `push_cast`. Both sides reduce to the same expression. Rewrite `hlt'` using `[hq]`. Take `⟨C, hC⟩` from `hS F K ι Ω y k₀ d (a • μ + (r : ℤ) • baseDeg k₀) (2 * r) hy hd hva (by omega)`. Take `⟨n, hn, hfin⟩` from `GroundTheory.Heights₂.Heights.Kleiman.exists_pos_of_eventually_lower (d := d) (sub_pos.mpr hlt') (C := C) (f := fun n : ℕ => (Module.finrank F (secOver F y (n • (a • μ + (r : ℤ) • baseDeg k₀ - (2 * r) • baseDeg k₀))) : ℝ)) (Filter.eventually_atTop.mpr ⟨1, fun n hn => by`.

Use `hC n hn` as an intermediate fact. Rewrite using `[Int.cast_sub, Int.cast_mul, Int.cast_natCast]⟩) 1 one_pos` and apply the resulting hypothesis. Rewrite `hfin` using `[one_mul]`. Establish `e : n • (a • μ + (r : ℤ) • baseDeg k₀ - (2 * r) • baseDeg k₀) = (n * a) • μ - ((n * r : ℕ) : ℤ) • baseDeg k₀` using `by module`. Rewrite `hfin` using `[e]`.

Use `⟨n * a, n * r, Nat.mul_pos hn ha, Nat.mul_pos hn hr, ?_⟩` and prove the remaining obligations. Use `Submodule.exists_mem_ne_zero_of_ne_bot fun h => ?_` and prove the remaining obligations. Rewrite `hfin` using `[h, finrank_bot]`. Simplify using `at hfin`.
-/
theorem siu_base_of (hnum : ∀ (M : Type) [AddCommGroup M] (d : ℕ) (f : MultilinearMap ℤ (fun _ : Fin (d + 1) => M) ℤ) (μ e : M), 0 < f (fun _ => μ) → ∃ t : ℚ, 0 < t ∧ ∀ (a : ℕ) (m : ℤ), 1 ≤ a → (m : ℚ) = a * t → ((d + 1 : ℕ) : ℤ) * f (Fin.snoc (α := fun _ => M) (fun _ : Fin d => a • μ + m • e) ((2 * m) • e)) < f (fun _ => a • μ + m • e)) :
    VeryAmpleNefPlusAmple.Statement → SectionCount.Statement → ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (d : ℕ) (μ : K → ℤ), IsModelWithBase F y k₀ → GroundTheory.Heights₂.Heights.FieldNumbers.relDim (mIdealOver F y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)) → IsNef F y μ → 0 < GroundTheory.Heights₂.Heights.NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => μ) → ∃ a m : ℕ, 1 ≤ a ∧ 1 ≤ m ∧ ∃ σ ∈ secOver F y (a • μ - (m : ℤ) • baseDeg k₀), σ ≠ 0 := by
  intro hK hS F _ K _ _ ι _ Ω _ _ y k₀ d μ hy hd hnef hpos
  have hP := GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.isMultiProjPrime_mIdealOver (S := F) y hy.1
  obtain ⟨f, hf⟩ := exists_multilinear (M := K → ℤ) (n := d + 1)
    (fun v => GroundTheory.Heights₂.Heights.NumbersDVR.intNum F (mIdealOver F y) v)
    (GroundTheory.Heights₂.Heights.FieldNumbers.IntNumAdd.full F K ι (mIdealOver F y) hP.multiHomog hP.relevant
      (d + 1) hd)
  obtain ⟨t, ht, hlt⟩ := hnum (K → ℤ) d f μ (baseDeg k₀) (by rw [hf]; exact hpos)
  obtain ⟨a, m, ha, hm, hva⟩ := hK (d + 1) F K ι Ω y k₀ hy hd μ hnef t ht
  have hmpos : 0 < m := by
    have ha' : (0 : ℚ) < a := by exact_mod_cast ha
    have : (0 : ℚ) < m := by rw [hm]; exact mul_pos ha' ht
    exact_mod_cast this
  obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le hmpos.le
  have hr : 0 < r := by exact_mod_cast hmpos
  have hlt' := hlt a r ha hm
  rw [hf, hf] at hlt'
  have hq : (2 * (r : ℤ)) • baseDeg k₀ = (2 * r) • baseDeg k₀ := by
    rw [← natCast_zsmul]; push_cast; rfl
  rw [hq] at hlt'
  obtain ⟨C, hC⟩ := hS F K ι Ω y k₀ d (a • μ + (r : ℤ) • baseDeg k₀) (2 * r) hy hd hva (by omega)
  obtain ⟨n, hn, hfin⟩ := GroundTheory.Heights₂.Heights.Kleiman.exists_pos_of_eventually_lower (d := d)
    (sub_pos.mpr hlt') (C := C)
    (f := fun n : ℕ => (Module.finrank F
      (secOver F y (n • (a • μ + (r : ℤ) • baseDeg k₀ - (2 * r) • baseDeg k₀))) : ℝ))
    (Filter.eventually_atTop.mpr ⟨1, fun n hn => by
      have := hC n hn
      rwa [Int.cast_sub, Int.cast_mul, Int.cast_natCast]⟩) 1 one_pos
  rw [one_mul] at hfin
  have e : n • (a • μ + (r : ℤ) • baseDeg k₀ - (2 * r) • baseDeg k₀) =
      (n * a) • μ - ((n * r : ℕ) : ℤ) • baseDeg k₀ := by
    module
  rw [e] at hfin
  refine ⟨n * a, n * r, Nat.mul_pos hn ha, Nat.mul_pos hn hr, ?_⟩
  refine Submodule.exists_mem_ne_zero_of_ne_bot fun h => ?_
  rw [h, finrank_bot] at hfin
  simp at hfin

/- English proof (translation)
Simplify using `only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply, Subalgebra.mem_toSubmodule]`. Introduce `c _`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Subalgebra.prod_mem _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.one_apply, zpow_neg_one, ← div_eq_mul_inv]`.

Conclude with `Algebra.subset_adjoin ⟨⟨k, i k⟩, rfl⟩`.
-/
theorem prod_mem_secOver {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [Field Ω]
    [Algebra F Ω] (y : (Σ k, ι k) → Ω) (i : ∀ k, ι k) :
    (∏ k, y ⟨k, i k⟩) ∈ secOver F y (1 : K → ℤ) := by
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]
  intro c _
  rw [← Finset.prod_mul_distrib]
  refine Subalgebra.prod_mem _ fun k _ => ?_
  rw [Pi.one_apply, zpow_neg_one, ← div_eq_mul_inv]
  exact Algebra.subset_adjoin ⟨⟨k, i k⟩, rfl⟩

open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization in
/- English proof (translation)
Introduce `hK hS F _ K _ _ ι _ Ω _ _ y d μ hy hd hnef hpos`. Take `⟨a, m, ha, hm, σ, hσ, hσ0⟩` from `hbase hK hS F (Unit ⊕ K) _ Ω (segreJoin y) (Sum.inl ()) d (pullDeg μ) (SegreBase.proof F K ι Ω y hy).1 ((SegreDim.proof F K ι Ω y hy).trans hd) ((SegreNef.proof SegreDim.proof SegreNum.proof F K ι Ω y hy μ).2 hnef) (lt_of_lt_of_eq hpos (SegreNum.proof F K ι Ω y hy (d + 1) (fun _ …`. Establish `e : a • pullDeg (K₁` using `Unit) μ - (m : ℤ) • baseDeg (Sum.inl ()) = pullDeg (a • μ) + (-(m : ℤ)) • baseDeg (Sum.inl ()) := by`. Rewrite using `[neg_smul, ← sub_eq_add_neg]`. Use `congr 1`.

Use function extensionality and compare the values at `k`. Apply the tactic sequence `cases k <;> simp [pullDeg]`. Rewrite `hσ` using `[e, SegreTwist.proof F K ι Ω y hy]`. Use `choose i hi using hy`. Establish `hp` using `ModelTwistGenerated.pow_mem_secOver y (prod_mem_secOver (F := F) y i) (m - 1)`.

Establish `hmul` using `ModelTwistGenerated.secOver_mul y hσ hp`. Establish `e' : ((a • μ + fun _ => -(m : ℤ)) + ((m - 1 : ℕ) : ℤ) • (1 : K → ℤ)) = a • μ - 1`. Use function extensionality and compare the values at `k`. Simplify using `only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, Nat.cast_sub hm]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `hmul` using `[e']`. Conclude with `⟨a, ha, _, hmul, mul_ne_zero hσ0 (pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun k _ => hi k))⟩`.
-/
theorem siu_segre_of_base (hbase : VeryAmpleNefPlusAmple.Statement → SectionCount.Statement → ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (d : ℕ) (μ : K → ℤ), IsModelWithBase F y k₀ → GroundTheory.Heights₂.Heights.FieldNumbers.relDim (mIdealOver F y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)) → IsNef F y μ → 0 < GroundTheory.Heights₂.Heights.NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => μ) → ∃ a m : ℕ, 1 ≤ a ∧ 1 ≤ m ∧ ∃ σ ∈ secOver F y (a • μ - (m : ℤ) • baseDeg k₀), σ ≠ 0) :
    VeryAmpleNefPlusAmple.Statement → SectionCount.Statement → ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (d : ℕ) (μ : K → ℤ), (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → GroundTheory.Heights₂.Heights.FieldNumbers.relDim (mIdealOver F y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)) → IsNef F y μ → 0 < GroundTheory.Heights₂.Heights.NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => μ) → ∃ a : ℕ, 1 ≤ a ∧ ∃ σ ∈ secOver F y (a • μ - 1), σ ≠ 0 := by
  intro hK hS F _ K _ _ ι _ Ω _ _ y d μ hy hd hnef hpos
  obtain ⟨a, m, ha, hm, σ, hσ, hσ0⟩ := hbase hK hS F (Unit ⊕ K) _ Ω (segreJoin y) (Sum.inl ()) d
    (pullDeg μ) (SegreBase.proof F K ι Ω y hy).1
    ((SegreDim.proof F K ι Ω y hy).trans hd)
    ((SegreNef.proof SegreDim.proof SegreNum.proof F K ι Ω y hy μ).2 hnef)
    (lt_of_lt_of_eq hpos (SegreNum.proof F K ι Ω y hy (d + 1) (fun _ => μ)).symm)
  have e : a • pullDeg (K₁ := Unit) μ - (m : ℤ) • baseDeg (Sum.inl ()) =
      pullDeg (a • μ) + (-(m : ℤ)) • baseDeg (Sum.inl ()) := by
    rw [neg_smul, ← sub_eq_add_neg]
    congr 1
    funext k
    cases k <;> simp [pullDeg]
  rw [e, SegreTwist.proof F K ι Ω y hy] at hσ
  choose i hi using hy
  have hp := ModelTwistGenerated.pow_mem_secOver y (prod_mem_secOver (F := F) y i) (m - 1)
  have hmul := ModelTwistGenerated.secOver_mul y hσ hp
  have e' : ((a • μ + fun _ => -(m : ℤ)) + ((m - 1 : ℕ) : ℤ) • (1 : K → ℤ)) = a • μ - 1 := by
    funext k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, Nat.cast_sub hm]
    push_cast
    ring
  rw [e'] at hmul
  exact ⟨a, ha, _, hmul, mul_ne_zero hσ0 (pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun k _ => hi k))⟩

/- English proof (translation)
The claim follows from `siu_segre_of_base (siu_base_of hnum)`.
-/
theorem siu_segre_of (hnum : ∀ (M : Type) [AddCommGroup M] (d : ℕ) (f : MultilinearMap ℤ (fun _ : Fin (d + 1) => M) ℤ) (μ e : M), 0 < f (fun _ => μ) → ∃ t : ℚ, 0 < t ∧ ∀ (a : ℕ) (m : ℤ), 1 ≤ a → (m : ℚ) = a * t → ((d + 1 : ℕ) : ℤ) * f (Fin.snoc (α := fun _ => M) (fun _ : Fin d => a • μ + m • e) ((2 * m) • e)) < f (fun _ => a • μ + m • e)) :
    VeryAmpleNefPlusAmple.Statement → SectionCount.Statement → ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (d : ℕ) (μ : K → ℤ), (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → GroundTheory.Heights₂.Heights.FieldNumbers.relDim (mIdealOver F y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)) → IsNef F y μ → 0 < GroundTheory.Heights₂.Heights.NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => μ) → ∃ a : ℕ, 1 ≤ a ∧ ∃ σ ∈ secOver F y (a • μ - 1), σ ≠ 0 :=
  siu_segre_of_base (siu_base_of hnum)

end PositivityTheory.HtPt.Siub
