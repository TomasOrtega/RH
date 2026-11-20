import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open Formalism.L2.Host (HChar atFin unif ordF)
open GlobalTheory.CharValCompare (IsFr dt)

namespace GlobalTheory.Mem.Col2.DetSpec

section Val

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {n : ℕ}

/- English proof (translation)
Set `M' : Matrix (Fin n) (Fin n) v.valuationSubring` to `fun i j => ⟨M i j, h i j⟩`. Establish `e : M.det = (M'.det : v.valuationSubring)`. Rewrite using `[← ValuationSubring.subtype_apply, RingHom.map_det]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `M'.det.2`.
-/
theorem val_det_le {M : Matrix (Fin n) (Fin n) K} (h : ∀ i j, v (M i j) ≤ 1) : v M.det ≤ 1 := by
  let M' : Matrix (Fin n) (Fin n) v.valuationSubring := fun i j => ⟨M i j, h i j⟩
  have e : M.det = (M'.det : v.valuationSubring) := by
    rw [← ValuationSubring.subtype_apply, RingHom.map_det]
    rfl
  rw [e]
  exact M'.det.2

/- English proof (translation)
Establish `h1 : ∀ i j, v (M i j) ≤ 1` using `fun i j => by`. Rewrite using `[← sub_add_cancel (M i j) ((1 : Matrix (Fin n) (Fin n) K) i j)]`. Use `Valuation.map_add_le _ (h i j).le ?_` and prove the remaining obligations. Rewrite using `[Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Set `M' : Matrix (Fin n) (Fin n) v.valuationSubring` to `fun i j => ⟨M i j, h1 i j⟩`. Establish `e : M.det = (M'.det : v.valuationSubring)`. Rewrite using `[← ValuationSubring.subtype_apply, RingHom.map_det]`. Both sides reduce to the same expression. Establish `e2 : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal v.valuationSubring)).mapMatrix M' = (Ideal.Quotient.mk (IsLocalRing.maximalIdeal v.valuationSubring)).mapMatrix 1`.

Use extensionality with `i j`. Use `Ideal.Quotient.eq.2 ((Valuation.mem_maximalIdeal_iff _ _).2 ?_)` and prove the remaining obligations. Use `h i j` as an intermediate fact. Rewrite `this`, the goal using `[Matrix.one_apply]`. Apply the tactic sequence `split_ifs at this ⊢ <;> simpa using this`.

Establish `e3` using `congrArg Matrix.det e2`. Rewrite `e3` using `[← RingHom.map_det, ← RingHom.map_det, Matrix.det_one]`. Establish `e4` using `(Valuation.mem_maximalIdeal_iff _ _).1 (Ideal.Quotient.eq.1 e3)`. Rewrite using `[e]`. Simplify using `using e4`.
-/
theorem val_det_sub_one_lt {M : Matrix (Fin n) (Fin n) K} (h : ∀ i j, v (M i j - (1 : Matrix (Fin n) (Fin n) K) i j) < 1) :
    v (M.det - 1) < 1 := by
  have h1 : ∀ i j, v (M i j) ≤ 1 := fun i j => by
    rw [← sub_add_cancel (M i j) ((1 : Matrix (Fin n) (Fin n) K) i j)]
    refine Valuation.map_add_le _ (h i j).le ?_
    rw [Matrix.one_apply]
    split_ifs <;> simp
  let M' : Matrix (Fin n) (Fin n) v.valuationSubring := fun i j => ⟨M i j, h1 i j⟩
  have e : M.det = (M'.det : v.valuationSubring) := by
    rw [← ValuationSubring.subtype_apply, RingHom.map_det]
    rfl
  have e2 : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal v.valuationSubring)).mapMatrix M' =
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal v.valuationSubring)).mapMatrix 1 := by
    ext i j
    refine Ideal.Quotient.eq.2 ((Valuation.mem_maximalIdeal_iff _ _).2 ?_)
    have := h i j
    rw [Matrix.one_apply] at this ⊢
    split_ifs at this ⊢ <;> simpa using this
  have e3 := congrArg Matrix.det e2
  rw [← RingHom.map_det, ← RingHom.map_det, Matrix.det_one] at e3
  have e4 := (Valuation.mem_maximalIdeal_iff _ _).1 (Ideal.Quotient.eq.1 e3)
  rw [e]
  simpa using e4

end Val

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def kMat (P : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) (AfE F E)) (f : Sp E n ≃ₗ[E] Sp E n) :
    Matrix (Fin n) (Fin n) (P.adicCompletion E) := fun i j => adAt F P (pullV g (f (Pi.single j 1)) i)

/- English proof (translation)
Use `ext1 i j`. Establish `e : (g : Matrix (Fin n) (Fin n) (AfE F E)).mulVec (pullV g (f (Pi.single j 1))) = fun i => Formalism.UG.inclE (F` using `F) (FiniteAdeleRing (𝓞 F) F) (f (Pi.single j 1) i) := by`. Unfold `pullV`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Establish `e2` using `congrArg (fun y => adAt F P (y i)) e`.

Simplify using `only [adAt_inclE, Matrix.mulVec, dotProduct, map_sum, map_mul] at e2`. Simplify using `only [Matrix.mul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix'_apply, kMat]`. Rewrite using `[e2]`. Use `congr 2`.
-/
theorem mul_kMat (P : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) (AfE F E)) (f : Sp E n ≃ₗ[E] Sp E n) :
    (adAt F P).mapMatrix (g : Matrix (Fin n) (Fin n) (AfE F E)) * kMat P g f =
      (algebraMap E (P.adicCompletion E)).mapMatrix (LinearMap.toMatrix' (f : Sp E n →ₗ[E] Sp E n)) := by
  ext1 i j
  have e : (g : Matrix (Fin n) (Fin n) (AfE F E)).mulVec (pullV g (f (Pi.single j 1))) =
      fun i => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (f (Pi.single j 1) i) := by
    unfold pullV
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have e2 := congrArg (fun y => adAt F P (y i)) e
  simp only [adAt_inclE, Matrix.mulVec, dotProduct, map_sum, map_mul] at e2
  simp only [Matrix.mul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix'_apply, kMat]
  rw [e2]
  congr 2

/- English proof (translation)
Rewrite using `[RingHom.map_det, ← Matrix.det_mul, mul_kMat, ← RingHom.map_det, LinearMap.det_toMatrix', CharValCompare.dt_eq]`.
-/
theorem det_kMat (P : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) (AfE F E)) (f : Sp E n ≃ₗ[E] Sp E n) :
    adAt F P (g : Matrix (Fin n) (Fin n) (AfE F E)).det * (kMat P g f).det = algebraMap E _ (dt f) := by
  rw [RingHom.map_det, ← Matrix.det_mul, mul_kMat, ← RingHom.map_det, LinearMap.det_toMatrix', CharValCompare.dt_eq]

/- English proof (translation)
Simplify using `only [pullV, Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.smul_apply, Algebra.smul_def, adAt_inclE, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem adAt_pullV_smul (P : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) (AfE F E)) (s : 𝓞 E) (x : Sp E n) (i : Fin n) :
    adAt F P (pullV g (s • x) i) = algebraMap E _ (algebraMap (𝓞 E) E s) * adAt F P (pullV g x i) := by
  simp only [pullV, Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.smul_apply, Algebra.smul_def, adAt_inclE, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

variable [StarRing E]

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨x, hx, rfl⟩` from `hy`. Take `⟨r, hr⟩` from `(mem_stdLat x).1 hx i`. Use `show Valued.v (adAt F P (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i))) ≤ 1`.

Rewrite using `[adAt_inclE, valued_algebraMap, ← hr]`. Conclude with `P.valuation_le_one r`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb`. Rewrite using `[Pi.add_apply, map_add]`.

Conclude with `Valuation.map_add_le _ ha hb`. Consider the case `smul c a _ ha => show Valued.v (adAt F P (c.1 * a i)) ≤ 1`. Rewrite using `[map_mul, map_mul]`. Conclude with `mul_le_one' ((mem_rInt_iff F E c.1).1 c.2 P) ha`.
-/
theorem val_le_of_mem_hatL (P : HeightOneSpectrum (𝓞 E)) {y : Fin n → AfE F E}
    (hy : y ∈ Formalism.L2.Herm.hatL (F := F) (stdLat E n)) (i : Fin n) : Valued.v (adAt F P (y i)) ≤ 1 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨r, hr⟩ := (mem_stdLat x).1 hx i
    show Valued.v (adAt F P (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i))) ≤ 1
    rw [adAt_inclE, valued_algebraMap, ← hr]
    exact P.valuation_le_one r
  | zero => simp
  | add a b _ _ ha hb =>
    rw [Pi.add_apply, map_add]
    exact Valuation.map_add_le _ ha hb
  | smul c a _ ha =>
    show Valued.v (adAt F P (c.1 * a i)) ≤ 1
    rw [map_mul, map_mul]
    exact mul_le_one' ((mem_rInt_iff F E c.1).1 c.2 P) ha

/- English proof (translation)
Take `⟨s, hs, hx⟩` from `(mem_locP _ _ _).1 ((hf _).2 (CharValCompare.single_mem_stdAt P j))`. Establish `h1 : pullV g (s • f (Pi.single j 1)) ∈ Formalism.L2.Herm.hatL (F` using `F) (stdLat E n) := (hg _).1 (Submodule.subset_span ⟨_, hx, rfl⟩)`. Establish `h2` using `val_le_of_mem_hatL P h1 i`. Rewrite `h2` using `[adAt_pullV_smul, map_mul, valued_algebraMap, CharValCompare.val_of_notMem hs, one_mul]`. Then use the resulting hypothesis.
-/
theorem val_kMat_le {P : HeightOneSpectrum (𝓞 E)} {g : GL (Fin n) (AfE F E)} {f : Sp E n ≃ₗ[E] Sp E n}
    {N : Submodule (𝓞 E) (Sp E n)} (hg : Formalism.L2.Herm.Carries g (stdLat E n) N) (hf : IsFr P N f) (i j : Fin n) :
    Valued.v (kMat P g f i j) ≤ 1 := by
  obtain ⟨s, hs, hx⟩ := (mem_locP _ _ _).1 ((hf _).2 (CharValCompare.single_mem_stdAt P j))
  have h1 : pullV g (s • f (Pi.single j 1)) ∈ Formalism.L2.Herm.hatL (F := F) (stdLat E n) :=
    (hg _).1 (Submodule.subset_span ⟨_, hx, rfl⟩)
  have h2 := val_le_of_mem_hatL P h1 i
  rwa [adAt_pullV_smul, map_mul, valued_algebraMap, CharValCompare.val_of_notMem hs, one_mul] at h2

variable {hc : Formalism.BasicNotions.CMData F E} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

/- English proof (translation)
Take `⟨s, hs, hx⟩` from `(mem_locP _ _ _).1 ((hf.1 _).2 (CharValCompare.single_mem_stdAt w.1 j))`. Take `⟨r, hr, h1⟩` from `h.be w _ hx i`. Establish `e : (s • (Pi.single j 1 : Sp E n)) i = algebraMap (𝓞 E) E (if i = j then s else 0)`. Rewrite using `[Pi.smul_apply, Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> simp [Algebra.smul_def]`.

Rewrite `hr` using `[← equiv_osmul, hf.2 _ (Submodule.smul_mem _ _ (CharValCompare.single_mem_stdAt w.1 j)), redV, e, reduction_coe, Ideal.Quotient.eq, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← valued_algebraMap]`. Use `replace hr : Valued.v (algebraMap E (w.1.adicCompletion E) (algebraMap (𝓞 E) E (r - if i = j then s else 0))) < 1 := hr`. Rewrite `hr` using `[map_sub, map_sub]`. Rewrite `h1` using `[adAt_pullV_smul]`. Establish `h2` using `Valuation.map_add_lt _ h1 hr`.

Rewrite `h2` using `[sub_add_sub_cancel]`. Establish `e2 : algebraMap E (w.1.adicCompletion E) (algebraMap (𝓞 E) E (if i = j then s else 0)) = algebraMap E (w.1.adicCompletion E) (algebraMap (𝓞 E) E s) * (1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) i j`. Rewrite using `[Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite `h2` using `[e2, ← mul_sub, map_mul, valued_algebraMap, CharValCompare.val_of_notMem hs, one_mul]`. Then use the resulting hypothesis.
-/
theorem val_kMat_sub_lt {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) (w : SG)
    {f : Sp E n ≃ₗ[E] Sp E n} (hf : TopStep.IsLiftFr p.deco.1 w f) (i j : Fin n) :
    Valued.v (kMat w.1 g f i j - (1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) i j) < 1 := by
  obtain ⟨s, hs, hx⟩ := (mem_locP _ _ _).1 ((hf.1 _).2 (CharValCompare.single_mem_stdAt w.1 j))
  obtain ⟨r, hr, h1⟩ := h.be w _ hx i
  have e : (s • (Pi.single j 1 : Sp E n)) i = algebraMap (𝓞 E) E (if i = j then s else 0) := by
    rw [Pi.smul_apply, Pi.single_apply]
    split_ifs <;> simp [Algebra.smul_def]
  rw [← equiv_osmul, hf.2 _ (Submodule.smul_mem _ _ (CharValCompare.single_mem_stdAt w.1 j)), redV, e, reduction_coe,
    Ideal.Quotient.eq, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← valued_algebraMap] at hr
  replace hr : Valued.v (algebraMap E (w.1.adicCompletion E) (algebraMap (𝓞 E) E (r - if i = j then s else 0))) < 1 := hr
  rw [map_sub, map_sub] at hr
  rw [adAt_pullV_smul] at h1
  have h2 := Valuation.map_add_lt _ h1 hr
  rw [sub_add_sub_cancel] at h2
  have e2 : algebraMap E (w.1.adicCompletion E) (algebraMap (𝓞 E) E (if i = j then s else 0)) =
      algebraMap E (w.1.adicCompletion E) (algebraMap (𝓞 E) E s) * (1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) i j := by
    rw [Matrix.one_apply]
    split_ifs <;> simp
  rwa [e2, ← mul_sub, map_mul, valued_algebraMap, CharValCompare.val_of_notMem hs, one_mul] at h2

end Loc

section Glob

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] {n : ℕ}
  {hc : Formalism.BasicNotions.CMData F E}

/- English proof (translation)
Establish `e : finAf F E a = Matrix.GeneralLinearGroup.det g * conjId hc.sig (finAf F E a)`. Rewrite using `[← h]`. Conclude with `(div_mul_cancel _ _).symm`. Rewrite using `[← map_mul, ← adAt_finAf F]`. Conclude with `congrArg (fun u : (AfE F E)ˣ => adAt F P u) e`.
-/
theorem compAt_eq {g : GL (Fin n) (AfE F E)} {a : Ideles E} (h : IsDetLift hc g a) (P : HeightOneSpectrum (𝓞 E)) :
    compAt P a = adAt F P (g : Matrix (Fin n) (Fin n) (AfE F E)).det *
      adAt F P (Formalism.UG.sigR hc.sig _ (finAf F E a : AfE F E)) := by
  have e : finAf F E a = Matrix.GeneralLinearGroup.det g * conjId hc.sig (finAf F E a) := by
    rw [← h]
    exact (div_mul_cancel _ _).symm
  rw [← map_mul, ← adAt_finAf F]
  exact congrArg (fun u : (AfE F E)ˣ => adAt F P u) e

omit [StarRing E] in

/- English proof (translation)
The claim follows from `(Valuation.ne_zero_iff _).2 ((Group.isUnit a).map (compAt P)).ne_zero`.
-/
theorem val_compAt_ne (P : HeightOneSpectrum (𝓞 E)) (a : Ideles E) : Valued.v (compAt P a) ≠ 0 :=
  (Valuation.ne_zero_iff _).2 ((Group.isUnit a).map (compAt P)).ne_zero

/- English proof (translation)
Establish `k : ∀ P : HeightOneSpectrum (𝓞 E), P.valuation E (dt (fr P)) * Valued.v (compAt (conjPrime₂ P) a) ≤ Valued.v (compAt P a)`. Introduce `P`. Rewrite using `[compAt_eq h P, map_mul, valued_sigR, adAt_finAf, ← valued_algebraMap, ← det_kMat P g, map_mul]`. Conclude with `mul_le_mul_left (mul_le_of_le_one_right' (val_det_le _ (val_kMat_le hg (hf P)))) _`. Use `le_antisymm ?_ (k P)` and prove the remaining obligations.

Establish `k2` using `k (conjPrime₂ P)`. Establish `k3` using `CharValCompare.val_dual hN (hf P) (hf (conjPrime₂ P))`. Rewrite `k3` using `[map_mul, valuation_star]`. Rewrite `k2`, `k3` using `[CharValCompare.conjP_conjP]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← mul_assoc, k3, one_mul]`. Use `_ ≤ _ := mul_le_mul_right k2 _`.
-/
theorem val_compAt_eq {g : GL (Fin n) (AfE F E)} {a : Ideles E} (h : IsDetLift hc g a) {N : Submodule (𝓞 E) (Sp E n)}
    (hN : IsSdLat N) (hg : Formalism.L2.Herm.Carries g (stdLat E n) N) {fr : HeightOneSpectrum (𝓞 E) → Sp E n ≃ₗ[E] Sp E n}
    (hf : ∀ P, IsFr P N (fr P)) (P : HeightOneSpectrum (𝓞 E)) :
    Valued.v (compAt P a) = P.valuation E (dt (fr P)) * Valued.v (compAt (conjPrime₂ P) a) := by
  have k : ∀ P : HeightOneSpectrum (𝓞 E), P.valuation E (dt (fr P)) * Valued.v (compAt (conjPrime₂ P) a) ≤ Valued.v (compAt P a) := by
    intro P
    rw [compAt_eq h P, map_mul, valued_sigR, adAt_finAf, ← valued_algebraMap, ← det_kMat P g, map_mul]
    exact mul_le_mul_left (mul_le_of_le_one_right' (val_det_le _ (val_kMat_le hg (hf P)))) _
  refine le_antisymm ?_ (k P)
  have k2 := k (conjPrime₂ P)
  have k3 := CharValCompare.val_dual hN (hf P) (hf (conjPrime₂ P))
  rw [map_mul, valuation_star] at k3
  rw [CharValCompare.conjP_conjP] at k2 k3
  calc Valued.v (compAt P a) = P.valuation E (dt (fr P)) * ((conjPrime₂ P).valuation E (dt (fr (conjPrime₂ P))) * Valued.v (compAt P a)) := by
        rw [← mul_assoc, k3, one_mul]
    _ ≤ _ := mul_le_mul_right k2 _

/- English proof (translation)
Establish `k3` using `CharValCompare.val_dual hN (hf P) (hf (conjPrime₂ P))`. Rewrite `k3` using `[map_mul, valuation_star, CharValCompare.conjP_conjP]`. Rewrite using `[compAt_detIdl _ hN.1, compAt_detIdl _ hN.1, CharValCompare.conjP_conjP]`. Distinguish the cases in `h1 : P ∈ SB`. Rewrite using `[if_pos h1, if_neg (hSB P h1), if_pos h1, map_one, mul_one, valued_algebraMap]`.

Distinguish the cases in `h2 : conjPrime₂ P ∈ SB`. Rewrite using `[if_neg h1, if_pos h2, if_pos h2, map_one, valued_algebraMap, k3]`. Rewrite using `[if_neg h1, if_neg h2, if_neg h2, if_neg h1, map_pow, map_pow, valued_algebraMap, valued_algebraMap, ordSub_detSub_eq hN.1 (hf P), ordSub_detSub_eq hN.1 (hf (conjPrime₂ P))]`. Establish `ex : ∀ (w : HeightOneSpectrum (𝓞 E)) (u : Eˣ), w.valuation E (u : E) = WithZero.exp (-ordF w u)` using `fun w u => by`. Unfold `ordF`.

Rewrite using `[neg_neg, WithZero.exp_log (by simp)]`. Rewrite `k3` using `[ex, ex, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_inj]`. Rewrite using `[ex, ex, ex, ordF_unif_self, ordF_unif_self, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add, WithZero.exp_inj]`. Simplify using `only [nsmul_eq_mul]`. Use linear arithmetic over natural numbers and integers.
-/
theorem val_compAt_detIdl {SB : Finset (HeightOneSpectrum (𝓞 E))} (hSB : ∀ P ∈ SB, conjPrime₂ P ∉ SB)
    {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) {fr : HeightOneSpectrum (𝓞 E) → Sp E n ≃ₗ[E] Sp E n}
    (hf : ∀ P, IsFr P N (fr P)) (P : HeightOneSpectrum (𝓞 E)) :
    Valued.v (compAt P (detIdl SB N fr)) = P.valuation E (dt (fr P)) * Valued.v (compAt (conjPrime₂ P) (detIdl SB N fr)) := by
  have k3 := CharValCompare.val_dual hN (hf P) (hf (conjPrime₂ P))
  rw [map_mul, valuation_star, CharValCompare.conjP_conjP] at k3
  rw [compAt_detIdl _ hN.1, compAt_detIdl _ hN.1, CharValCompare.conjP_conjP]
  by_cases h1 : P ∈ SB
  · rw [if_pos h1, if_neg (hSB P h1), if_pos h1, map_one, mul_one, valued_algebraMap]
  by_cases h2 : conjPrime₂ P ∈ SB
  · rw [if_neg h1, if_pos h2, if_pos h2, map_one, valued_algebraMap, k3]
  rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1, map_pow, map_pow, valued_algebraMap, valued_algebraMap,
    ordSub_detSub_eq hN.1 (hf P), ordSub_detSub_eq hN.1 (hf (conjPrime₂ P))]
  have ex : ∀ (w : HeightOneSpectrum (𝓞 E)) (u : Eˣ), w.valuation E (u : E) = WithZero.exp (-ordF w u) := fun w u => by
    unfold ordF
    rw [neg_neg, WithZero.exp_log (by simp)]
  rw [ex, ex, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_inj] at k3
  rw [ex, ex, ex, ordF_unif_self, ordF_unif_self, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add,
    WithZero.exp_inj]
  simp only [nsmul_eq_mul]
  omega

end Glob

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish `hN : IsSdLat p.deco.1.N` using `⟨p.deco.2.lat, p.deco.2.uni⟩`. Use `QuotientGroup.eq.2 (mem_KDq_of_conj hl _ (fun w => ?_) fun P hP => ?_)` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, map_inv₀, map_inv₀, val_compAt_eq ha hN hp.lat (isFr_ptFr p) w, ptIdl, val_compAt_detIdl hl.split hN (isFr_ptFr p) w]`. Establish `: w.valuation H.E (dt (ptFr p w)) ≠ 0` using `(Valuation.ne_zero_iff _).2 (CharValCompare.dt_ne _)`. Use `val_compAt_ne (conjPrime₂ w) a` as an intermediate fact.

Clear the denominators using the available nonvanishing facts. Establish `k1 : Valued.v ((kMat P g (ptFr p P)).det - 1) < 1`. Distinguish the cases in `h : P ∈ SG`. Conclude with `val_det_sub_one_lt _ (val_kMat_sub_lt hp ⟨P, h⟩ (isLiftFr_ptFr p ⟨P, h⟩))`. Establish `h' : P ∈ SQ` using `by simpa [h] using hP`.

Establish `e : (adAt H.F P).mapMatrix (g : Matrix (Fin n) (Fin n) (AfE H.F H.E)) = (algebraMap H.E (P.adicCompletion H.E)).mapMatrix (LinearMap.toMatrix' (ptFr p P : Sp H.E n →ₗ[H.E] Sp H.E n))` using `by ext1 i j`. Use `(hp.fr ⟨P, h'⟩ i j).trans ?_` and prove the remaining obligations. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix'_apply, extTo_fr]`. Use `congr 2`. Establish `e2` using `det_kMat P g (ptFr p P)`.

Rewrite `e2` using `[RingHom.map_det, e, ← RingHom.map_det, LinearMap.det_toMatrix', ← CharValCompare.dt_eq, mul_right_eq_self₀, map_eq_zero]`. Rewrite using `[e2.resolve_right (CharValCompare.dt_ne _), sub_self, map_zero]`. Conclude with `zero_lt_one`. Establish `k2 : Valued.v (adAt H.F P (Formalism.UG.sigR (host_cmData R H).sig _ (finAf H.F H.E (ptIdl H SQ p) : AfE H.F H.E)) - 1) < 1`. Establish `e` using `valued_sigR (host_cmData R H) P ((finAf H.F H.E (ptIdl H SQ p) : AfE H.F H.E) - 1)`.

Rewrite `e` using `[map_sub (Formalism.UG.sigR _ _), map_sub (adAt _ _), map_sub (adAt _ _), map_one, map_one, map_one, adAt_finAf]`. Rewrite using `[e, ptIdl, compAt_detIdl _ hN.1, if_neg (hl.split P hP), CharValCompare.conjP_conjP, if_pos hP, sub_self, map_zero]`. Conclude with `zero_lt_one`. Establish `e1 : compAt P (ptIdl H SQ p) = algebraMap H.E _ (dt (ptFr p P))`. Rewrite using `[ptIdl, compAt_detIdl _ hN.1, if_pos hP]`.

Establish `e2` using `compAt_eq ha P`. Establish `e3 : adAt H.F P (Formalism.UG.sigR (host_cmData R H).sig _ (finAf H.F H.E a : AfE H.F H.E)) * adAt H.F P (Formalism.UG.sigR (host_cmData R H).sig _ (finAf H.F H.E (a⁻¹ * ptIdl H SQ p) : AfE H.F H.E)) = adAt H.F P (Formalism.UG.sigR (host_cmData R H).sig _ (finAf H.F H.E (ptIdl H …`. Rewrite using `[← map_mul, ← map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel_left]`. Establish `h0 : compAt P a ≠ 0` using `((Group.isUnit a).map (compAt P)).ne_zero`. Establish `k3` using `val_mul_sub_one_lt _ k1 (val_inv_sub_one_lt _ k2)`.

Rewrite `h0` using `[e2]`. Rewrite using `[map_mul (compAt P), map_inv, e1, ← det_kMat P g, e2]`. Rewrite `k3` using `[← e3]`. Use `k3 using 3` and compare the differences between its conclusion and the goal. Use `left_ne_zero_of_mul h0` as an intermediate fact.

Clear the denominators using the available nonvanishing facts.
-/
theorem mk_eq_detPt (R : Ranks) (H : Formalism.BasicNotions.Host R) (n : ℕ) (ST SG Q SQ : Finset (HeightOneSpectrum (𝓞 H.E)))
    (p : DecoF H.E n ST SG Q) (g : GL (Fin n) (AfE H.F H.E)) (a : Ideles H.E) (hl : LevOk H SG SQ)
    (hp : IsPtOf (host_cmData R H) g (extTo SQ p)) (ha : IsDetLift (host_cmData R H) g a) :
    (QuotientGroup.mk a : DtQ H SQ) = detPt H SQ p := by
  classical
  have hN : IsSdLat p.deco.1.N := ⟨p.deco.2.lat, p.deco.2.uni⟩
  refine QuotientGroup.eq.2 (mem_KDq_of_conj hl _ (fun w => ?_) fun P hP => ?_)
  · rw [map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, map_inv₀, map_inv₀,
      val_compAt_eq ha hN hp.lat (isFr_ptFr p) w, ptIdl, val_compAt_detIdl hl.split hN (isFr_ptFr p) w]
    have : w.valuation H.E (dt (ptFr p w)) ≠ 0 := (Valuation.ne_zero_iff _).2 (CharValCompare.dt_ne _)
    have := val_compAt_ne (conjPrime₂ w) a
    field_simp
  · have k1 : Valued.v ((kMat P g (ptFr p P)).det - 1) < 1 := by
      by_cases h : P ∈ SG
      · exact val_det_sub_one_lt _ (val_kMat_sub_lt hp ⟨P, h⟩ (isLiftFr_ptFr p ⟨P, h⟩))
      · have h' : P ∈ SQ := by simpa [h] using hP
        have e : (adAt H.F P).mapMatrix (g : Matrix (Fin n) (Fin n) (AfE H.F H.E)) =
            (algebraMap H.E (P.adicCompletion H.E)).mapMatrix
              (LinearMap.toMatrix' (ptFr p P : Sp H.E n →ₗ[H.E] Sp H.E n)) := by
          ext1 i j
          refine (hp.fr ⟨P, h'⟩ i j).trans ?_
          simp only [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix'_apply, extTo_fr]
          congr 2
        have e2 := det_kMat P g (ptFr p P)
        rw [RingHom.map_det, e, ← RingHom.map_det, LinearMap.det_toMatrix', ← CharValCompare.dt_eq,
          mul_right_eq_self₀, map_eq_zero] at e2
        rw [e2.resolve_right (CharValCompare.dt_ne _), sub_self, map_zero]
        exact zero_lt_one
    have k2 : Valued.v (adAt H.F P (Formalism.UG.sigR (host_cmData R H).sig _ (finAf H.F H.E (ptIdl H SQ p) : AfE H.F H.E)) - 1) < 1 := by
      have e := valued_sigR (host_cmData R H) P ((finAf H.F H.E (ptIdl H SQ p) : AfE H.F H.E) - 1)
      rw [map_sub (Formalism.UG.sigR _ _), map_sub (adAt _ _), map_sub (adAt _ _), map_one, map_one, map_one, adAt_finAf] at e
      rw [e, ptIdl, compAt_detIdl _ hN.1, if_neg (hl.split P hP), CharValCompare.conjP_conjP, if_pos hP, sub_self, map_zero]
      exact zero_lt_one
    have e1 : compAt P (ptIdl H SQ p) = algebraMap H.E _ (dt (ptFr p P)) := by
      rw [ptIdl, compAt_detIdl _ hN.1, if_pos hP]
    have e2 := compAt_eq ha P
    have e3 : adAt H.F P (Formalism.UG.sigR (host_cmData R H).sig _ (finAf H.F H.E a : AfE H.F H.E)) *
        adAt H.F P (Formalism.UG.sigR (host_cmData R H).sig _ (finAf H.F H.E (a⁻¹ * ptIdl H SQ p) : AfE H.F H.E)) =
        adAt H.F P (Formalism.UG.sigR (host_cmData R H).sig _ (finAf H.F H.E (ptIdl H SQ p) : AfE H.F H.E)) := by
      rw [← map_mul, ← map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel_left]
    have h0 : compAt P a ≠ 0 := ((Group.isUnit a).map (compAt P)).ne_zero
    have k3 := val_mul_sub_one_lt _ k1 (val_inv_sub_one_lt _ k2)
    rw [e2] at h0
    rw [map_mul (compAt P), map_inv, e1, ← det_kMat P g, e2]
    rw [← e3] at k3
    convert k3 using 3
    have := left_ne_zero_of_mul h0
    field_simp

end GlobalTheory.Mem.Col2.DetSpec
