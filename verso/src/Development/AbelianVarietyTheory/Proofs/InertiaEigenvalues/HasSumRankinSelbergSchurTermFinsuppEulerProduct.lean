import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdTsumEqTsumIndicatorEnnreal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultisetProdMapProductEqProdProd

open MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.ZEul

open GlobalTheory.JSW

def partVec {n : ℕ} (l : {l : Fin n → ℕ // Antitone l}) : Fin n → ℤ := fun j => (l.1 j : ℤ)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem partVec_injective {n : ℕ} : Function.Injective (partVec (n := n)) := by
  intro a b h
  apply Subtype.ext; funext j
  have := congrFun h j
  simpa [partVec] using this

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem partVec_valid {n : ℕ} (l : {l : Fin n → ℕ // Antitone l}) :
    (∀ i, 0 ≤ partVec l i) ∧ Antitone (partVec l) :=
  ⟨fun i => Int.natCast_nonneg _, fun a b h => Int.ofNat_le.2 (l.2 h)⟩

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem mem_range_partVec {n : ℕ} {v : Fin n → ℤ} (hv : (∀ i, 0 ≤ v i) ∧ Antitone v) :
    v ∈ Set.range (partVec (n := n)) :=
  ⟨⟨fun i => (v i).toNat, fun a b h => Int.toNat_le_toNat (hv.2 h)⟩, by
    funext j; simp [partVec, Int.toNat_of_nonneg (hv.1 j)]⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem rsTerm_partVec (q : ℕ) {n : ℕ} (α β : Fin n → ℂ) (x : ℝ) (l : {l : Fin n → ℕ // Antitone l}) :
    rsTerm q α β x (partVec l) =
      schurAt l.1 α * conj (schurAt l.1 β) * ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, l.1 i) := by
  rw [rsTerm, if_pos (partVec_valid l)]
  simp [partVec]

open Classical in

def sqTerm (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) (v : Fin n → ℤ) : ℝ :=
  if (∀ i, 0 ≤ v i) ∧ Antitone v then
    ‖schurAt (fun i => (v i).toNat) α‖ ^ 2 * (q : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x))
  else 0

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem sqTerm_nonneg (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) (v : Fin n → ℤ) : 0 ≤ sqTerm q α x v := by
  unfold sqTerm
  split_ifs
  · exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · exact le_rfl

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem sqTerm_zero (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) : sqTerm q α x 0 = 1 := by
  have hs : schurAt (fun _ : Fin n => 0) α = 1 := by rw [schurAt, schur_zero]; simp
  rw [sqTerm, if_pos ⟨fun i => le_rfl, antitone_const⟩]
  simp [hs]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem sqTerm_partVec (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) (l : {l : Fin n → ℕ // Antitone l}) :
    sqTerm q α x (partVec l) = ‖schurAt l.1 α‖ ^ 2 * (q : ℝ) ^ (-(((∑ i, l.1 i : ℕ) : ℝ) * x)) := by
  rw [sqTerm, if_pos (partVec_valid l)]
  simp [partVec]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_cpow_pow (q : ℕ) (hq : 0 < q) (x : ℝ) (k : ℕ) :
    ‖((q : ℂ) ^ (-(x : ℂ))) ^ k‖ = (q : ℝ) ^ (-((k : ℝ) * x)) := by
  rw [norm_pow, Complex.norm_natCast_cpow_of_pos hq]
  simp only [Complex.neg_re, Complex.ofReal_re]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q)]
  congr 1; ring

/- English proof (translation)
Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules.
-/
theorem norm_rsTerm_le (q : ℕ) (hq : 0 < q) {n : ℕ} (α β : Fin n → ℂ) (x : ℝ) (v : Fin n → ℤ) :
    ‖rsTerm q α β x v‖ ≤ (sqTerm q α x v + sqTerm q β x v) / 2 := by
  by_cases hv : (∀ i, 0 ≤ v i) ∧ Antitone v
  · rw [rsTerm, if_pos hv, sqTerm, if_pos hv, sqTerm, if_pos hv, norm_mul, norm_mul, Complex.norm_conj,
      norm_cpow_pow q hq]
    have hw : 0 ≤ (q : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    nlinarith [mul_nonneg (sq_nonneg (‖schurAt (fun i => (v i).toNat) α‖ - ‖schurAt (fun i => (v i).toNat) β‖)) hw]
  · rw [rsTerm, if_neg hv, sqTerm, if_neg hv, sqTerm, if_neg hv]; simp

end GlobalTheory.ZEul

namespace GlobalTheory.ZEul

open GlobalTheory.JSW

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem summable_sqTerm {I : Type} (q : I → ℕ) {n : ℕ} (α : I → Fin n → ℂ) (x : ℝ)
    (h : GlobalTheory.RSPole.eulD q α x ≠ ⊤) :
    Summable fun p : I × {v : Fin n → ℤ // v ≠ 0} => sqTerm (q p.1) (α p.1) x p.2 := by
  set f : I → (Fin n → ℤ) → ℝ≥0∞ := fun i v => ENNReal.ofReal (sqTerm (q i) (α i) x v) with hf
  have hf0 : ∀ i, f i 0 = 1 := fun i => by simp [hf, sqTerm_zero]
  have hloc : ∀ i, ∑' v, f i v = GlobalTheory.RSPole.schurDir (q i) (α i) x := by
    intro i
    rw [← (partVec_injective (n := n)).tsum_eq]
    · rw [GlobalTheory.RSPole.schurDir]
      refine tsum_congr fun l => ?_
      simp only [hf, sqTerm_partVec]
    · intro v hv
      by_cases hval : (∀ j, 0 ≤ v j) ∧ Antitone v
      · exact mem_range_partVec hval
      · exact absurd (by simp [hf, sqTerm, if_neg hval]) hv
  have hE : ∑' l : I →₀ (Fin n → ℤ), l.prod f = GlobalTheory.RSPole.eulD q α x := by
    rw [(GlobalTheory.EulerSum.euler_product_intVec_ennreal n f hf0).2, GlobalTheory.RSPole.eulD]
    exact tprod_congr hloc
  have hinj : Function.Injective fun p : I × {v : Fin n → ℤ // v ≠ 0} => Finsupp.single p.1 p.2.1 := by
    intro p p' hp
    rcases (Finsupp.single_eq_single_iff _ _ _ _).1 hp with ⟨h1, h2⟩ | ⟨h1, -⟩
    · exact Prod.ext h1 (Subtype.ext h2)
    · exact absurd h1 p.2.2
  have hle : ∑' p : I × {v : Fin n → ℤ // v ≠ 0}, f p.1 p.2 ≤ ∑' l : I →₀ (Fin n → ℤ), l.prod f := by
    have hc : (fun p : I × {v : Fin n → ℤ // v ≠ 0} => f p.1 p.2) =
        fun p => (fun l : I →₀ (Fin n → ℤ) => l.prod f) (Finsupp.single p.1 p.2.1) := by
      funext p; simp only; rw [Finsupp.prod_single_index (hf0 p.1)]
    rw [hc]
    exact ENNReal.tsum_comp_le_tsum_of_injective hinj _
  have hfin : ∑' p : I × {v : Fin n → ℤ // v ≠ 0}, f p.1 p.2 ≠ ⊤ := ne_top_of_le_ne_top (hE ▸ h) hle
  refine (ENNReal.summable_toReal hfin).congr fun p => ?_
  simp only [hf]
  exact ENNReal.toReal_ofReal (sqTerm_nonneg _ _ _ _)

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem hasSum_rsTerm_local (q : ℕ) {n : ℕ} (α β : Fin n → ℂˣ) (x : ℝ)
    (hs : Summable fun v : Fin n → ℤ => ‖rsTerm q (fun j => (α j : ℂ)) (fun j => (β j : ℂ)) x v‖) :
    HasSum (fun v => rsTerm q (fun j => (α j : ℂ)) (fun j => (β j : ℂ)) x v)
      (locL q (Finset.univ.val.map α) ((Finset.univ.val.map β).map (Units.map (starRingEnd ℂ).toMonoidHom))
        (x : ℂ)) := by
  set β' : Fin n → ℂˣ := fun j => Units.map (starRingEnd ℂ).toMonoidHom (β j) with hβ'
  have hconj : ∀ l : Fin n → ℕ, schurAt l (fun j => (β' j : ℂ)) = conj (schurAt l fun j => (β j : ℂ)) := by
    intro l
    rw [schurAt, schurAt, MvPolynomial.eval₂_comp_left, RingHom.ext_int ((starRingEnd ℂ).comp (Int.castRingHom ℂ))
      (Int.castRingHom ℂ)]
    rfl
  have hm : (Finset.univ.val.map β).map (Units.map (starRingEnd ℂ).toMonoidHom) = Finset.univ.val.map β' :=
    Multiset.map_map _ _ _
  rw [hm]
  have hs' : Summable fun l : {l : Fin n → ℕ // Antitone l} =>
      ‖schurAt (padTo le_rfl l.1) (fun i => (α i : ℂ)) * schurAt l.1 (fun j => (β' j : ℂ))‖ *
        ‖(q : ℂ) ^ (-(x : ℂ))‖ ^ (∑ i, l.1 i) := by
    refine (hs.comp_injective partVec_injective).congr fun l => ?_
    simp only [Function.comp, rsTerm_partVec, padTo_self, hconj, norm_mul, norm_pow, Complex.norm_conj]
  have hc := cauchy_locL le_rfl α β' q (x : ℂ) hs'
  rw [← (partVec_injective (n := n)).hasSum_iff]
  · convert hc using 1
    funext l
    simp only [Function.comp, rsTerm_partVec, padTo_self, hconj]
  · intro v hv
    by_cases hval : (∀ j, 0 ≤ v j) ∧ Antitone v
    · exact absurd (mem_range_partVec hval) hv
    · rw [rsTerm, if_neg hval]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem hasSum_rsTerm_finsupp : ∀ {I : Type} (q : I → ℕ) {n : ℕ} (α β : I → Fin n → ℂˣ) (x : ℝ), 1 < x → (∀ i, 2 ≤ q i) →
    GlobalTheory.RSPole.eulD q (fun i j => (α i j : ℂ)) x ≠ ⊤ → GlobalTheory.RSPole.eulD q (fun i j => (β i j : ℂ)) x ≠ ⊤ →
    HasSum (fun l : I →₀ (Fin n → ℤ) => l.prod fun i v => GlobalTheory.ZEul.rsTerm (q i) (fun j => (α i j : ℂ)) (fun j => (β i j : ℂ)) x v)
      (∏' i, GlobalTheory.JSW.locL (q i) (Finset.univ.val.map (α i)) ((Finset.univ.val.map (β i)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) := by
  intro I q n α β x _ hq hα hβ
  set f : I → (Fin n → ℤ) → ℂ := fun i v => rsTerm (q i) (fun j => (α i j : ℂ)) (fun j => (β i j : ℂ)) x v with hfdef
  have hf0 : ∀ i, f i 0 = 1 := fun i => rsTerm_zero _ _ _ _
  have hA := summable_sqTerm q (fun i j => (α i j : ℂ)) x hα
  have hB := summable_sqTerm q (fun i j => (β i j : ℂ)) x hβ
  have hsum : Summable fun p : I × {v : Fin n → ℤ // v ≠ 0} => ‖f p.1 p.2‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun p => by
        simpa only [hfdef] using norm_rsTerm_le (q p.1) (by have := hq p.1; omega) (fun j => (α p.1 j : ℂ)) (fun j => (β p.1 j : ℂ)) x p.2.1) ((hA.add hB).div_const 2)
  obtain ⟨hN, -, hE⟩ := GlobalTheory.EulerSum.euler_product_intVec n f hf0 hsum
  have hloc : ∀ i, ∑' v, f i v = locL (q i) (Finset.univ.val.map (α i))
      ((Finset.univ.val.map (β i)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) :=
    fun i => (hasSum_rsTerm_local (q i) (α i) (β i) x (GlobalTheory.EulerSum.summable_norm_local f hsum i)).tsum_eq
  rw [← hE.trans (tprod_congr hloc)]
  exact hN.of_norm.hasSum

end GlobalTheory.ZEul
