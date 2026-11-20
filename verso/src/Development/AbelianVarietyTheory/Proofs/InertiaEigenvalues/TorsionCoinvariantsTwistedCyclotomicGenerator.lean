import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPrimitiveRootPrimePowSubOnePadicComplex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicNormZpowSubOnePadicValInt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDecompositionCompletedCyclotomicIntegersStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormZpowSubOneLeTer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalProdEqZeroHodgeTateCyclotomicFrameStatement

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial

namespace GlobalTheory.CycCoinv

/- English proof (translation)
Establish `hmv : ∀ y : Fin r → C, (∀ a, y a ∈ O) → ∀ a, U.mulVec y a ∈ O` using `fun y hy a => by`. Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `O.sum_mem fun c _ => O.mul_mem (hU a c) (hy c)`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨0, fun a => O.zero_mem, by simp⟩`.

Consider the case `insert u s hu ih`. Take `⟨y, hy, he⟩` from `ih`. Use `⟨(∏ u ∈ s, (b - f u)) • w + (U.mulVec y - f u • y), fun a => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Conclude with `O.add_mem (O.mul_mem (O.prod_mem fun v _ => O.sub_mem hb (hf v)) (hw a)) (O.sub_mem (hmv y hy a) (O.mul_mem (hf u) (hy a)))`.

Rewrite using `[Finset.prod_insert hu, Finset.prod_insert hu, map_mul, ← Matrix.mulVec_mulVec, he, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]`. Simplify using `only [Matrix.sub_mulVec, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.one_mulVec]`. Use `module`.
-/
theorem prod_div {C ι : Type} [CommRing C] [DecidableEq ι] (O : Subring C) {r : ℕ}
    (U : Matrix (Fin r) (Fin r) C) (hU : ∀ a b, U a b ∈ O) (b : C) (hb : b ∈ O) (f : ι → C)
    (hf : ∀ u, f u ∈ O) (w : Fin r → C) (hw : ∀ a, w a ∈ O) (s : Finset ι) :
    ∃ y : Fin r → C, (∀ a, y a ∈ O) ∧
      (aeval U (∏ u ∈ s, (X - Polynomial.C (f u)))).mulVec w
        = (∏ u ∈ s, (b - f u)) • w + (U.mulVec y - b • y) := by
  have hmv : ∀ y : Fin r → C, (∀ a, y a ∈ O) → ∀ a, U.mulVec y a ∈ O := fun y hy a => by
    simp only [Matrix.mulVec, dotProduct]
    exact O.sum_mem fun c _ => O.mul_mem (hU a c) (hy c)
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun a => O.zero_mem, by simp⟩
  | insert u s hu ih =>
    obtain ⟨y, hy, he⟩ := ih
    refine ⟨(∏ u ∈ s, (b - f u)) • w + (U.mulVec y - f u • y), fun a => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact O.add_mem (O.mul_mem (O.prod_mem fun v _ => O.sub_mem hb (hf v)) (hw a))
        (O.sub_mem (hmv y hy a) (O.mul_mem (hf u) (hy a)))
    · rw [Finset.prod_insert hu, Finset.prod_insert hu, map_mul, ← Matrix.mulVec_mulVec, he,
        map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
      simp only [Matrix.sub_mulVec, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul,
        Matrix.smul_mulVec, Matrix.one_mulVec]
      module

/- English proof (translation)
Take `⟨y, hy, he⟩` from `prod_div O U hU (f i) (hf i) f hf w hw (J.erase i)`. Establish `hd : ∏ u ∈ J, (X - Polynomial.C (f u)) ∣ (∏ u ∈ J.erase i, (X - Polynomial.C (f u))) * (X - Polynomial.C (f i))`. Distinguish the cases in `hi : i ∈ J`. Rewrite using `[Finset.prod_erase_mul _ _ hi]`. Rewrite using `[Finset.erase_eq_of_notMem hi]`.

Conclude with `dvd_mul_right _ _`. Take `⟨q, hq⟩` from `hd`. Establish `h0 : aeval U ((∏ u ∈ J.erase i, (X - Polynomial.C (f u))) * (X - Polynomial.C (f i))) = 0`. Rewrite using `[hq, map_mul, hJ, zero_mul]`. Establish `h1` using `congrArg (fun M => Matrix.mulVec M w') h0`.

Simplify using `only [map_mul, ← Matrix.mulVec_mulVec, Matrix.zero_mulVec] at h1`. Rewrite `h1` using `[map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h, Matrix.mulVec_smul, smul_eq_zero]`. Establish `h2` using `h1.resolve_left hp`. Rewrite `he` using `[h2]`. Use `⟨-y, fun a => O.neg_mem (hy a), ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.mulVec_neg, eq_neg_of_add_eq_zero_left he.symm]`. Use `module`.
-/
theorem tors_int {C ι : Type} [Field C] [DecidableEq ι] (O : Subring C) {r : ℕ}
    (U : Matrix (Fin r) (Fin r) C) (hU : ∀ a b, U a b ∈ O) (f : ι → C)
    (hf : ∀ u, f u ∈ O) (J : Finset ι) (hJ : aeval U (∏ u ∈ J, (X - Polynomial.C (f u))) = 0)
    (i : ι) (w w' : Fin r → C) (hw : ∀ a, w a ∈ O) (p : C) (hp : p ≠ 0)
    (h : U.mulVec w' - f i • w' = p • w) :
    ∃ y : Fin r → C, (∀ a, y a ∈ O) ∧
      U.mulVec y - f i • y = (∏ u ∈ J.erase i, (f i - f u)) • w := by
  obtain ⟨y, hy, he⟩ := prod_div O U hU (f i) (hf i) f hf w hw (J.erase i)
  have hd : ∏ u ∈ J, (X - Polynomial.C (f u)) ∣
      (∏ u ∈ J.erase i, (X - Polynomial.C (f u))) * (X - Polynomial.C (f i)) := by
    by_cases hi : i ∈ J
    · rw [Finset.prod_erase_mul _ _ hi]
    · rw [Finset.erase_eq_of_notMem hi]; exact dvd_mul_right _ _
  obtain ⟨q, hq⟩ := hd
  have h0 : aeval U ((∏ u ∈ J.erase i, (X - Polynomial.C (f u))) * (X - Polynomial.C (f i))) = 0 := by
    rw [hq, map_mul, hJ, zero_mul]
  have h1 := congrArg (fun M => Matrix.mulVec M w') h0
  simp only [map_mul, ← Matrix.mulVec_mulVec, Matrix.zero_mulVec] at h1
  rw [map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, h, Matrix.mulVec_smul, smul_eq_zero] at h1
  have h2 := h1.resolve_left hp
  rw [h2] at he
  refine ⟨-y, fun a => O.neg_mem (hy a), ?_⟩
  rw [Matrix.mulVec_neg, eq_neg_of_add_eq_zero_left he.symm]
  module

variable {l : ℕ} [hl : Fact l.Prime]

noncomputable def fld (F : IntermediateField ℚ_[l] (Om l)) : Subfield (PadicComplex l) :=
  F.toSubfield.map (algebraMap (Om l) (PadicComplex l))

/- English proof (translation)
Simplify using `[fld, inC, PadicComplex.coe_eq]`.
-/
theorem mem_fld (F : IntermediateField ℚ_[l] (Om l)) (y : PadicComplex l) :
    y ∈ fld F ↔ y ∈ inC F := by
  simp [fld, inC, PadicComplex.coe_eq]

noncomputable def intR (F : IntermediateField ℚ_[l] (Om l)) : Subring (PadicComplex l) where
  carrier := intC F
  mul_mem' := fun {a b} ha hb => ⟨(mem_fld F _).1 (mul_mem ((mem_fld F _).2 ha.1) ((mem_fld F _).2 hb.1)),
    by rw [norm_mul]; exact mul_le_one₀ ha.2 (norm_nonneg _) hb.2⟩
  one_mem' := ⟨(mem_fld F _).1 (one_mem _), by simp⟩
  add_mem' := fun {a b} ha hb => ⟨(mem_fld F _).1 (add_mem ((mem_fld F _).2 ha.1) ((mem_fld F _).2 hb.1)),
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha.2 hb.2)⟩
  zero_mem' := ⟨(mem_fld F _).1 (zero_mem _), by simp⟩
  neg_mem' := fun {a} ha => ⟨(mem_fld F _).1 (neg_mem ((mem_fld F _).2 ha.1)), by simpa using ha.2⟩

/- English proof (translation)
The claim follows from `sup_le_sup_left (IntermediateField.adjoin.mono ℚ_[l] _ _ fun (x : Om l) hx => (show ∃ j : ℕ, x ^ (l ^ j) = 1 from ⟨j, hx⟩)) _`.
-/
theorem Ks_le_Kinf (K : FinExt l) (j : ℕ) : Ks K j ≤ Kinf K :=
  sup_le_sup_left (IntermediateField.adjoin.mono ℚ_[l] _ _ fun (x : Om l) hx =>
    (show ∃ j : ℕ, x ^ (l ^ j) = 1 from ⟨j, hx⟩)) _

/- English proof (translation)
Establish `hy' : y ∈ (intR (Kinf K)).topologicalClosure` using `(intR (Kinf K)).le_topologicalClosure (show y ∈ intC (Kinf K) from ⟨Set.image_mono (Ks_le_Kinf K j) hy.1, hy.2⟩)`. Establish `hx' : x ∈ (intR (Kinf K)).topologicalClosure` using `hx`. Conclude with `add_mem hy' hx'`.
-/
theorem add_mem_Ohat (K : FinExt l) (j : ℕ) {y x : PadicComplex l} (hy : y ∈ intC (Ks K j))
    (hx : x ∈ Ohat K) : y + x ∈ Ohat K := by
  have hy' : y ∈ (intR (Kinf K)).topologicalClosure :=
    (intR (Kinf K)).le_topologicalClosure
      (show y ∈ intC (Kinf K) from ⟨Set.image_mono (Ks_le_Kinf K j) hy.1, hy.2⟩)
  have hx' : x ∈ (intR (Kinf K)).topologicalClosure := hx
  exact add_mem hy' hx'

/- English proof (translation)
Use `haveI : NeZero l := ⟨hl.1.ne_zero⟩`. Take `⟨η, hη⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) l`. Establish `hη'` using `hη.map_of_injective (algebraMap (Om l) (PadicComplex l)).injective`. Take `⟨k, -, hk⟩` from `hη'.eq_pow_of_pow_eq_one h.pow_eq_one`. Use `⟨η ^ k, ?_, ?_⟩` and prove the remaining obligations.

Use `pow_mem (?_ : η ∈ Ks K j) k` and prove the remaining obligations. Use `(le_sup_right : _ ≤ Ks K j) (IntermediateField.subset_adjoin _ _ ?_)` and prove the remaining obligations. Conclude with `(hη.pow_eq_one_iff_dvd _).2 (dvd_pow_self l (by omega))`. Simplify using `only [PadicComplex.coe_eq, map_pow]`. Conclude with `hk`.
-/
theorem root_mem_inC (K : FinExt l) {j : ℕ} (hj : 1 ≤ j) {ζ : PadicComplex l}
    (h : IsPrimitiveRoot ζ l) : ζ ∈ inC (Ks K j) := by
  haveI : NeZero l := ⟨hl.1.ne_zero⟩
  obtain ⟨η, hη⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) l
  have hη' := hη.map_of_injective (algebraMap (Om l) (PadicComplex l)).injective
  obtain ⟨k, -, hk⟩ := hη'.eq_pow_of_pow_eq_one h.pow_eq_one
  refine ⟨η ^ k, ?_, ?_⟩
  · refine pow_mem (?_ : η ∈ Ks K j) k
    refine (le_sup_right : _ ≤ Ks K j) (IntermediateField.subset_adjoin _ _ ?_)
    exact (hη.pow_eq_one_iff_dvd _).2 (dvd_pow_self l (by omega))
  · simp only [PadicComplex.coe_eq, map_pow]
    exact hk

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨algebraMap ℚ_[l] (Om l) _, F.algebraMap_mem _, rfl⟩, by rwa [norm_algebraMap']⟩`.
-/
theorem algebraMap_mem (F : IntermediateField ℚ_[l] (Om l)) (t : ℚ_[l]) (ht : ‖t‖ ≤ 1) :
    algebraMap ℚ_[l] (PadicComplex l) t ∈ intR F :=
  ⟨⟨algebraMap ℚ_[l] (Om l) _, F.algebraMap_mem _, rfl⟩, by rwa [norm_algebraMap']⟩

/- English proof (translation)
Rewrite using `[← map_natCast (algebraMap ℚ_[l] (PadicComplex l)), norm_algebraMap', Padic.norm_p]`.
-/
theorem norm_l : ‖(l : PadicComplex l)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicComplex l)), norm_algebraMap', Padic.norm_p]

/- English proof (translation)
Establish `h1 : (1 : ℝ) < l` using `by exact_mod_cast hl.1.one_lt`. Establish `h2 : (2 : ℝ) ≤ l` using `by exact_mod_cast hl.1.two_le`. Establish `hz` using `GlobalTheory.Cyc.norm_primitiveRoot_sub_one l 1 le_rfl ζ (by rwa [pow_one])`. Establish `hz0 : ζ - 1 ≠ 0` using `sub_ne_zero.2 (h.ne_one hl.1.one_lt)`. Use `⟨(mem_fld _ _).1 (div_mem (pow_mem (natCast_mem _ _) _) (sub_mem ((mem_fld _ _).2 (root_mem_inC K hj h)) (one_mem _))), ?_⟩` and prove the remaining obligations.

Rewrite using `[norm_div, div_le_one (norm_pos_iff.2 hz0), norm_pow, norm_l, hz]`. Combine the equalities or inequalities in the displayed calculation. Apply `Real.rpow_le_rpow_of_exponent_le h1.le` to reduce the goal to its premises. Simplify using `only [tsub_self, pow_zero, one_mul]`. Rewrite using `[le_div_iff₀ (by linarith)]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem quot_mem (K : FinExt l) {j : ℕ} (hj : 1 ≤ j) {ζ : PadicComplex l}
    (h : IsPrimitiveRoot ζ l) {N : ℕ} (hN : 1 ≤ N) :
    (l : PadicComplex l) ^ N / (ζ - 1) ∈ intR (Ks K j) := by
  have h1 : (1 : ℝ) < l := by exact_mod_cast hl.1.one_lt
  have h2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.1.two_le
  have hz := GlobalTheory.Cyc.norm_primitiveRoot_sub_one l 1 le_rfl ζ (by rwa [pow_one])
  have hz0 : ζ - 1 ≠ 0 := sub_ne_zero.2 (h.ne_one hl.1.one_lt)
  refine ⟨(mem_fld _ _).1 (div_mem (pow_mem (natCast_mem _ _) _)
    (sub_mem ((mem_fld _ _).2 (root_mem_inC K hj h)) (one_mem _))), ?_⟩
  rw [norm_div, div_le_one (norm_pos_iff.2 hz0), norm_pow, norm_l, hz]
  calc ((l : ℝ)⁻¹) ^ N ≤ ((l : ℝ)⁻¹) ^ 1 :=
        pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ h1.le) hN
    _ = (l : ℝ) ^ (-1 : ℝ) := by rw [pow_one, Real.rpow_neg_one]
    _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le h1.le
        simp only [tsub_self, pow_zero, one_mul]
        rw [le_div_iff₀ (by linarith)]
        linarith

/- English proof (translation)
Establish `h1 : (1 : ℝ) < l` using `by exact_mod_cast hl.1.one_lt`. Establish `hu : ‖(χ g : ℚ_[l]) - 1‖ < 1`. Rewrite using `[hg.2]`. Conclude with `zpow_lt_one_of_neg₀ h1 (by have := hj.1; omega)`. Use `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := (χ g : ℚ_[l]) - 1) (y := 1) (by rw [norm_one]; exact hu.ne)` as an intermediate fact.

Rewrite `this` using `[sub_add_cancel, norm_one, max_eq_right hu.le]`. Then use the resulting hypothesis.
-/
theorem norm_chi {χ : GQ l →* ℚ_[l]ˣ} {K : FinExt l} {j : ℕ} (hj : Lev l j) {g : GQ l}
    (hg : IsGen χ K j g) : ‖(χ g : ℚ_[l])‖ = 1 := by
  have h1 : (1 : ℝ) < l := by exact_mod_cast hl.1.one_lt
  have hu : ‖(χ g : ℚ_[l]) - 1‖ < 1 := by
    rw [hg.2]
    exact zpow_lt_one_of_neg₀ h1 (by have := hj.1; omega)
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := (χ g : ℚ_[l]) - 1) (y := 1)
    (by rw [norm_one]; exact hu.ne)
  rwa [sub_add_cancel, norm_one, max_eq_right hu.le] at this

/- English proof (translation)
Rewrite using `[norm_prod, ← Finset.prod_pow_eq_pow_sum]`. Use `Finset.prod_congr rfl fun u hu => ?_` and prove the remaining obligations. Establish `hne : u - i ≠ 0` using `sub_ne_zero.2 (Finset.ne_of_mem_erase hu)`. Establish `e : (χ g : ℚ_[l]) ^ (-i) - (χ g : ℚ_[l]) ^ (-u) = (χ g : ℚ_[l]) ^ (-u) * ((χ g : ℚ_[l]) ^ (u - i) - 1)`. Rewrite using `[mul_sub, ← zpow_add₀ (χ g).ne_zero, mul_one]`.

Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, norm_mul, norm_zpow, norm_chi hj hg, one_zpow, one_mul, GlobalTheory.Cyc.LiftExp.norm_zpow_sub_one l j hj _ hg.2 _ hne, inv_pow, ← zpow_natCast, ← zpow_neg]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem norm_prod_chi {χ : GQ l →* ℚ_[l]ˣ} {K : FinExt l} {j : ℕ} (hj : Lev l j) {g : GQ l}
    (hg : IsGen χ K j g) (J : Finset ℤ) (i : ℤ) :
    ‖∏ u ∈ J.erase i, ((χ g : ℚ_[l]) ^ (-i) - (χ g : ℚ_[l]) ^ (-u))‖
      = ((l : ℝ)⁻¹) ^ (∑ u ∈ J.erase i, (j + padicValInt l (u - i))) := by
  rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun u hu => ?_
  have hne : u - i ≠ 0 := sub_ne_zero.2 (Finset.ne_of_mem_erase hu)
  have e : (χ g : ℚ_[l]) ^ (-i) - (χ g : ℚ_[l]) ^ (-u)
      = (χ g : ℚ_[l]) ^ (-u) * ((χ g : ℚ_[l]) ^ (u - i) - 1) := by
    rw [mul_sub, ← zpow_add₀ (χ g).ne_zero, mul_one]
    congr 2; ring
  rw [e, norm_mul, norm_zpow, norm_chi hj hg, one_zpow, one_mul,
    GlobalTheory.Cyc.LiftExp.norm_zpow_sub_one l j hj _ hg.2 _ hne, inv_pow, ← zpow_natCast, ← zpow_neg]
  push_cast; rfl

/- English proof (translation)
Take `⟨x, hx, rfl⟩` from `hy`. Use `(IntermediateField.mem_fixingSubgroup_iff F g).1 hg x hx` as an intermediate fact. Simplify using `only []`. Rewrite using `[hact.1, this]`.
-/
theorem act_fix {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (hact : IsActC act)
    {F : IntermediateField ℚ_[l] (Om l)} {g : GQ l} (hg : g ∈ F.fixingSubgroup)
    {y : PadicComplex l} (hy : y ∈ inC F) : act g y = y := by
  obtain ⟨x, hx, rfl⟩ := hy
  have := (IntermediateField.mem_fixingSubgroup_iff F g).1 hg x hx
  simp only []
  rw [hact.1, this]

/- English proof (translation)
Rewrite using `[twAct, twAct, twAct, ← smul_add, ← Matrix.mulVec_add]`. Use `congr 2`. Use function extensionality and compare the values at `a`. Simplify using the standard rewrite rules.
-/
theorem twAct_add (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ)
    {r : ℕ} (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l)
    (x y : Fin r → PadicComplex l) :
    twAct act χ i U g (x + y) = twAct act χ i U g x + twAct act χ i U g y := by
  rw [twAct, twAct, twAct, ← smul_add, ← Matrix.mulVec_add]
  congr 2
  funext a
  simp

/- English proof (translation)
Introduce `l hl act χ hact hχ K m r hm U g hF J hHT i w w' k hw hw' h`. Establish `heig` using `GlobalTheory.T.aeval_prod_eq_zero_hodgeTate_cyclotomicFrame l act χ hact hχ K m r hm U g hF J hHT`. Take `⟨hg, -, hUO, -, -, hU1⟩` from `hF`. Establish `hU : ∀ a b, U g a b ∈ intR (Ks K m)` using `hUO g hg.1`. Take `⟨hdec, huniq, hXO, hmul, hstab, -⟩` from `GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ hact hχ K m hm.1`.

Establish `hgX` using `hstab g (IntermediateField.fixingSubgroup_antitone (le_sup_left : K0 K ≤ Ks K m) hg.1)`. Use `choose w0 hw0 wx hwx hwe using fun a => hdec _ (hw a)`. Use `choose v0 hv0 vx hvx hve using fun a => hdec _ (hw' a)`. Take `rfl : w = w0 + wx` from `funext hwe`. Take `rfl : w' = v0 + vx` from `funext hve`.

Establish `hl0 : (l : PadicComplex l) ≠ 0` using `Nat.cast_ne_zero.2 hl.1.ne_zero`. Establish `hchi : ∀ u : ℤ, chiC χ u g = algebraMap ℚ_[l] (PadicComplex l) ((χ g : ℚ_[l]) ^ u)` using `fun u => by simp [chiC]`. Establish `hcO : ∀ u : ℤ, chiC χ u g ∈ intR (Ks K m)` using `fun u => by`. Rewrite using `[hchi]`. Conclude with `algebraMap_mem _ _ (by rw [norm_zpow, norm_chi hm hg, one_zpow])`.

Establish `hcc : chiC χ i g * chiC χ (-i) g = 1`. Rewrite using `[hchi, hchi, ← map_mul, ← zpow_add₀ (χ g).ne_zero]`. Simplify using the standard rewrite rules. Establish `htw : ∀ y : Fin r → PadicComplex l, (∀ a, y a ∈ intR (Ks K m)) → twAct act χ i U g y - y = chiC χ i g • ((U g).mulVec y - chiC χ (-i) g • y)`. Introduce `y hy`.

Establish `: (fun a => act g (y a)) = y` using `funext fun a => act_fix hact hg.1 (hy a).1`. Rewrite using `[twAct, this, smul_sub, smul_smul, hcc, one_smul]`. Establish `hlk : (l : PadicComplex l) ^ k ∈ intR (Ks K m)` using `pow_mem (natCast_mem _ _) _`. Establish `h0 : twAct act χ i U g v0 - v0 = (l : PadicComplex l) ^ k • w0`. Rewrite `h` using `[twAct_add]`.

Use function extensionality and compare the values at `a`. Establish `hO : (twAct act χ i U g v0 - v0) a - (l : PadicComplex l) ^ k * w0 a ∈ intR (Ks K m)`. Rewrite using `[htw v0 hv0]`. Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]`. Conclude with `sub_mem (mul_mem (hcO i) (sub_mem (sum_mem fun b _ => mul_mem (hU a b) (hv0 b)) (mul_mem (hcO _) (hv0 a)))) (mul_mem hlk (hw0 a))`.

Establish `hX : (l : PadicComplex l) ^ k * wx a - (twAct act χ i U g vx a - vx a) ∈ Xj K m`. Use `sub_mem (hmul _ hlk _ (hwx a)) (sub_mem ?_ (hvx a))` and prove the remaining obligations. Simplify using `only [twAct, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]`. Conclude with `hmul _ (hcO i) _ (sum_mem fun b _ => hmul _ (hU a b) _ (hgX _ (hvx b)))`. Use `huniq _ hO.1 _ hX 0 (by` as an intermediate fact.

Establish `ha` using `congrFun h a`. Simplify using `only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ha ⊢`. Take the linear combination `ha)`. Conclude with `sub_eq_zero.1 this`. Use `set N := max 1 (∑ u ∈ J.erase i, (m + padicValInt l (u - i))) with hN`.

Use `haveI : NeZero l := ⟨hl.1.ne_zero⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (PadicComplex l) l`. Establish `hz0 : ζ - 1 ≠ 0` using `sub_ne_zero.2 (hζ.ne_one hl.1.one_lt)`. Take `⟨yx, hyx, hyxe⟩` from `(GlobalTheory.CycSeries.perturbation l act χ hact hχ K m hm g hg r U hU hU1 i).2 ζ hζ (((l : PadicComplex l) ^ N / (ζ - 1)) • wx) (fun a => hmul _ (quot_mem K hm.1 hζ (le_max_left _ _)) _ (hwx a))`. Rewrite `hyxe` using `[smul_smul, mul_div_cancel₀ _ hz0]`.

Establish `h1 : (U g).mulVec v0 - chiC χ (-i) g • v0 = (chiC χ (-i) g * (l : PadicComplex l) ^ k) • w0`. Rewrite using `[mul_smul, ← h0, htw v0 hv0, smul_smul, mul_comm, hcc, one_smul]`. Establish `hci : chiC χ (-i) g ≠ 0` using `right_ne_zero_of_mul_eq_one hcc`. Take `⟨y, hy, hye⟩` from `tors_int (intR (Ks K m)) (U g) hU (fun u => chiC χ (-u) g) (fun u => hcO _) J heig i w0 v0 hw0 _ (mul_ne_zero hci (pow_ne_zero _ hl0)) h1`. Use `set β : ℚ_[l] := ∏ u ∈ J.erase i, ((χ g : ℚ_[l]) ^ (-i) - (χ g : ℚ_[l]) ^ (-u)) with hβ`.

Establish `hβn` using `norm_prod_chi hm hg J i`. Rewrite `hβn` using `[← hβ]`. Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast hl.1.one_lt`. Establish `hβ0 : β ≠ 0`. Rewrite using `[← norm_pos_iff, hβn]`.

Check the signs of the components of the expression. Establish `hβe : ∏ u ∈ J.erase i, (chiC χ (-i) g - chiC χ (-u) g) = algebraMap ℚ_[l] (PadicComplex l) β`. Simplify using `only [hchi, hβ, map_prod, map_sub]`. Establish `ht : algebraMap ℚ_[l] (PadicComplex l) ((l : ℚ_[l]) ^ N / β) ∈ intR (Ks K m)`. Apply `algebraMap_mem` to reduce the goal to its premises.

Rewrite using `[norm_div, div_le_one (norm_pos_iff.2 hβ0), hβn, norm_pow, Padic.norm_p]`. Conclude with `pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hl1.le) (le_max_right _ _)`. Use `set t := algebraMap ℚ_[l] (PadicComplex l) ((l : ℚ_[l]) ^ N / β) with htd`. Establish `htβ : t * algebraMap ℚ_[l] (PadicComplex l) β = (l : PadicComplex l) ^ N`. Rewrite using `[htd, ← map_mul, div_mul_cancel₀ _ hβ0, map_pow, map_natCast]`.

Establish `hy0 : ∀ a, ((t * chiC χ (-i) g) • y) a ∈ intR (Ks K m)` using `fun a => mul_mem (mul_mem ht (hcO _)) (hy a)`. Use `⟨(t * chiC χ (-i) g) • y + yx, fun a => add_mem_Ohat K m (hy0 a) (hXO _ (hyx a)), ?_⟩` and prove the remaining obligations. Establish `h2 : twAct act χ i U g ((t * chiC χ (-i) g) • y) - (t * chiC χ (-i) g) • y = (l : PadicComplex l) ^ N • w0`. Rewrite using `[htw _ hy0, Matrix.mulVec_smul, smul_comm (chiC χ (-i) g), ← smul_sub, hye, hβe, smul_smul, smul_smul, ← htβ]`. Use `congr 1`.

Take the linear combination `t * algebraMap ℚ_[l] (PadicComplex l) β * hcc`. Rewrite using `[twAct_add, smul_add, ← h2, ← hyxe]`. Normalize the expressions using the abelian group laws.
-/
theorem torsion_coinvariants : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m r : ℕ), Lev l m → ∀ (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l), Frame χ K m U g → ∀ J : Finset ℤ, HTBasis act χ (Gj K m) U (J : Set ℤ) → ∀ (i : ℤ) (w w' : Fin r → PadicComplex l) (k : ℕ), (∀ a, w a ∈ Ohat K) → (∀ a, w' a ∈ Ohat K) → twAct act χ i U g w' - w' = (l : PadicComplex l) ^ k • w → ∃ y : Fin r → PadicComplex l, (∀ a, y a ∈ Ohat K) ∧ twAct act χ i U g y - y = (l : PadicComplex l) ^ (max 1 (∑ u ∈ J.erase i, (m + padicValInt l (u - i)))) • w := by
  intro l hl act χ hact hχ K m r hm U g hF J hHT i w w' k hw hw' h
  have heig := GlobalTheory.T.aeval_prod_eq_zero_hodgeTate_cyclotomicFrame l act χ hact hχ K m r hm U g hF J hHT
  obtain ⟨hg, -, hUO, -, -, hU1⟩ := hF
  have hU : ∀ a b, U g a b ∈ intR (Ks K m) := hUO g hg.1
  obtain ⟨hdec, huniq, hXO, hmul, hstab, -⟩ := GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ hact hχ K m hm.1
  have hgX := hstab g (IntermediateField.fixingSubgroup_antitone (le_sup_left : K0 K ≤ Ks K m) hg.1)
  choose w0 hw0 wx hwx hwe using fun a => hdec _ (hw a)
  choose v0 hv0 vx hvx hve using fun a => hdec _ (hw' a)
  obtain rfl : w = w0 + wx := funext hwe
  obtain rfl : w' = v0 + vx := funext hve
  have hl0 : (l : PadicComplex l) ≠ 0 := Nat.cast_ne_zero.2 hl.1.ne_zero
  have hchi : ∀ u : ℤ, chiC χ u g = algebraMap ℚ_[l] (PadicComplex l) ((χ g : ℚ_[l]) ^ u) :=
    fun u => by simp [chiC]
  have hcO : ∀ u : ℤ, chiC χ u g ∈ intR (Ks K m) := fun u => by
    rw [hchi]
    exact algebraMap_mem _ _ (by rw [norm_zpow, norm_chi hm hg, one_zpow])
  have hcc : chiC χ i g * chiC χ (-i) g = 1 := by
    rw [hchi, hchi, ← map_mul, ← zpow_add₀ (χ g).ne_zero]; simp
  have htw : ∀ y : Fin r → PadicComplex l, (∀ a, y a ∈ intR (Ks K m)) →
      twAct act χ i U g y - y = chiC χ i g • ((U g).mulVec y - chiC χ (-i) g • y) := by
    intro y hy
    have : (fun a => act g (y a)) = y := funext fun a => act_fix hact hg.1 (hy a).1
    rw [twAct, this, smul_sub, smul_smul, hcc, one_smul]
  have hlk : (l : PadicComplex l) ^ k ∈ intR (Ks K m) := pow_mem (natCast_mem _ _) _

  have h0 : twAct act χ i U g v0 - v0 = (l : PadicComplex l) ^ k • w0 := by
    rw [twAct_add] at h
    funext a
    have hO : (twAct act χ i U g v0 - v0) a - (l : PadicComplex l) ^ k * w0 a ∈ intR (Ks K m) := by
      rw [htw v0 hv0]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
      exact sub_mem (mul_mem (hcO i) (sub_mem (sum_mem fun b _ => mul_mem (hU a b) (hv0 b))
        (mul_mem (hcO _) (hv0 a)))) (mul_mem hlk (hw0 a))
    have hX : (l : PadicComplex l) ^ k * wx a - (twAct act χ i U g vx a - vx a) ∈ Xj K m := by
      refine sub_mem (hmul _ hlk _ (hwx a)) (sub_mem ?_ (hvx a))
      simp only [twAct, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
      exact hmul _ (hcO i) _ (sum_mem fun b _ => hmul _ (hU a b) _ (hgX _ (hvx b)))
    have := huniq _ hO.1 _ hX 0 (by
      have ha := congrFun h a
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ha ⊢
      linear_combination ha)
    exact sub_eq_zero.1 this
  set N := max 1 (∑ u ∈ J.erase i, (m + padicValInt l (u - i))) with hN

  haveI : NeZero l := ⟨hl.1.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicComplex l) l
  have hz0 : ζ - 1 ≠ 0 := sub_ne_zero.2 (hζ.ne_one hl.1.one_lt)
  obtain ⟨yx, hyx, hyxe⟩ := (GlobalTheory.CycSeries.perturbation l act χ hact hχ K m hm g hg r U hU hU1 i).2 ζ hζ
    (((l : PadicComplex l) ^ N / (ζ - 1)) • wx)
    (fun a => hmul _ (quot_mem K hm.1 hζ (le_max_left _ _)) _ (hwx a))
  rw [smul_smul, mul_div_cancel₀ _ hz0] at hyxe

  have h1 : (U g).mulVec v0 - chiC χ (-i) g • v0
      = (chiC χ (-i) g * (l : PadicComplex l) ^ k) • w0 := by
    rw [mul_smul, ← h0, htw v0 hv0, smul_smul, mul_comm, hcc, one_smul]
  have hci : chiC χ (-i) g ≠ 0 := right_ne_zero_of_mul_eq_one hcc
  obtain ⟨y, hy, hye⟩ := tors_int (intR (Ks K m)) (U g) hU (fun u => chiC χ (-u) g)
    (fun u => hcO _) J heig i w0 v0 hw0 _ (mul_ne_zero hci (pow_ne_zero _ hl0)) h1
  set β : ℚ_[l] := ∏ u ∈ J.erase i, ((χ g : ℚ_[l]) ^ (-i) - (χ g : ℚ_[l]) ^ (-u)) with hβ
  have hβn := norm_prod_chi hm hg J i
  rw [← hβ] at hβn
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.1.one_lt
  have hβ0 : β ≠ 0 := by
    rw [← norm_pos_iff, hβn]; positivity
  have hβe : ∏ u ∈ J.erase i, (chiC χ (-i) g - chiC χ (-u) g)
      = algebraMap ℚ_[l] (PadicComplex l) β := by
    simp only [hchi, hβ, map_prod, map_sub]
  have ht : algebraMap ℚ_[l] (PadicComplex l) ((l : ℚ_[l]) ^ N / β) ∈ intR (Ks K m) := by
    apply algebraMap_mem
    rw [norm_div, div_le_one (norm_pos_iff.2 hβ0), hβn, norm_pow, Padic.norm_p]
    exact pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hl1.le) (le_max_right _ _)
  set t := algebraMap ℚ_[l] (PadicComplex l) ((l : ℚ_[l]) ^ N / β) with htd
  have htβ : t * algebraMap ℚ_[l] (PadicComplex l) β = (l : PadicComplex l) ^ N := by
    rw [htd, ← map_mul, div_mul_cancel₀ _ hβ0, map_pow, map_natCast]
  have hy0 : ∀ a, ((t * chiC χ (-i) g) • y) a ∈ intR (Ks K m) := fun a =>
    mul_mem (mul_mem ht (hcO _)) (hy a)
  refine ⟨(t * chiC χ (-i) g) • y + yx, fun a => add_mem_Ohat K m (hy0 a) (hXO _ (hyx a)), ?_⟩
  have h2 : twAct act χ i U g ((t * chiC χ (-i) g) • y) - (t * chiC χ (-i) g) • y
      = (l : PadicComplex l) ^ N • w0 := by
    rw [htw _ hy0, Matrix.mulVec_smul, smul_comm (chiC χ (-i) g), ← smul_sub, hye, hβe,
      smul_smul, smul_smul, ← htβ]
    congr 1
    linear_combination t * algebraMap ℚ_[l] (PadicComplex l) β * hcc
  rw [twAct_add, smul_add, ← h2, ← hyxe]
  abel

end GlobalTheory.CycCoinv
