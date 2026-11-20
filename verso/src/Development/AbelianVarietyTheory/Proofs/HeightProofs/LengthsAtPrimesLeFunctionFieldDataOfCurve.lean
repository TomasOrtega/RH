import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.RegXInst
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
import Formalism.LocalToGlobal.ProjectiveLattices.LocRingPf
import Formalism.LocalToGlobal.ProjectiveLattices.TieInst
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
import Formalism.LocalToGlobal.ProjectiveLattices.HtXfer
import Formalism.LocalToGlobal.ProjectiveLattices.CompTie
import Formalism.LocalToGlobal.ProjectiveLattices.AxHInst
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.LocalToGlobal.ProjectiveLattices.CombAlgOfCombBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.KTFiniteDimensional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.OpIsDVR
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
import Development.AbelianVarietyTheory.Proofs.AlgebraicCurves.PlacesRestrictInjective
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RangeMulStep
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RealisationValuesEqValuedPointOrdersStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LengthQuotientLeOfOrderBound
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ValuationEqOrdAndEqZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.GaussRingCompletionRename
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRingHomTensorOmSOfPoint
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSectionMaps

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.T0 (TVar SVar OmS KTp KTf sImg sHom)
open scoped TensorProduct

namespace GlobalTheory.LengthTie

section Alg

variable {Ω : Type} [Field Ω] {D N : ℕ} (j₀ : Fin (N + 1)) (x : Fin N → Ω)

/- English proof (translation)
Establish `hC : ∀ a : Ω, algebraMap Ω (OmS Ω D N) a = algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) (MvPolynomial.C a)` using `fun a => IsScalarTower.algebraMap_apply Ω (MvPolynomial (SVar D N) Ω) (OmS Ω D N) a`. Rewrite using `[Fin.sum_univ_succAbove _ j₀]`. Simplify using `only [sImg, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, hy, hC, ← map_mul, ← map_sum, ← map_add]`. Use `congr 1`. Use `split_ifs`.

Simplify using `only [map_mul, add_mul, Finset.sum_mul, mul_assoc]`. Simplify using `only [map_mul, neg_mul, Finset.sum_mul, mul_assoc, neg_add_cancel, zero_mul]`.
-/
theorem sum_sImg (y : Fin (N + 1) → Ω) (hy : ∀ k, y (j₀.succAbove k) = x k * y j₀) (i : Fin (D + 1)) :
    ∑ k, sImg (D := D) j₀ x (i, k) * algebraMap Ω (OmS Ω D N) (y k) =
      algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N)
        (if i = 0 then MvPolynomial.X (Sum.inl ()) +
          ∑ k, MvPolynomial.X (Sum.inr (i, k)) * MvPolynomial.C (x k) else 0) *
        algebraMap Ω (OmS Ω D N) (y j₀) := by
  have hC : ∀ a : Ω, algebraMap Ω (OmS Ω D N) a =
      algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) (MvPolynomial.C a) := fun a =>
    IsScalarTower.algebraMap_apply Ω (MvPolynomial (SVar D N) Ω) (OmS Ω D N) a
  rw [Fin.sum_univ_succAbove _ j₀]
  simp only [sImg, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove, hy, hC, ← map_mul, ← map_sum, ← map_add]
  congr 1
  split_ifs
  · simp only [map_mul, add_mul, Finset.sum_mul, mul_assoc]
  · simp only [map_mul, neg_mul, Finset.sum_mul, mul_assoc, neg_add_cancel, zero_mul]

/- English proof (translation)
Rewrite using `[sum_sImg j₀ x y hy, if_neg (Fin.succ_ne_zero i), map_zero, zero_mul]`.
-/
theorem sum_sImg_succ (y : Fin (N + 1) → Ω) (hy : ∀ k, y (j₀.succAbove k) = x k * y j₀) (i : Fin D) :
    ∑ k, sImg (D := D) j₀ x (i.succ, k) * algebraMap Ω (OmS Ω D N) (y k) = 0 := by
  rw [sum_sImg j₀ x y hy, if_neg (Fin.succ_ne_zero i), map_zero, zero_mul]

/- English proof (translation)
Rewrite using `[sum_sImg j₀ x y hy, if_pos rfl]`. Use `mul_ne_zero ?_ ((map_ne_zero _).2 h0)` and prove the remaining obligations. Rewrite using `[map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (SVar D N) Ω) (OmS Ω D N))]`. Introduce `h`. Use `congrArg (MvPolynomial.eval (fun s : SVar D N => Sum.elim (fun _ => (1 : Ω)) (fun _ => 0) s)) h` as an intermediate fact.

Simplify using `at this`.
-/
theorem sum_sImg_zero (y : Fin (N + 1) → Ω) (hy : ∀ k, y (j₀.succAbove k) = x k * y j₀) (h0 : y j₀ ≠ 0) :
    ∑ k, sImg (D := D) j₀ x (0, k) * algebraMap Ω (OmS Ω D N) (y k) ≠ 0 := by
  rw [sum_sImg j₀ x y hy, if_pos rfl]
  refine mul_ne_zero ?_ ((map_ne_zero _).2 h0)
  rw [map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (SVar D N) Ω) (OmS Ω D N))]
  intro h
  have := congrArg (MvPolynomial.eval (fun s : SVar D N => Sum.elim (fun _ => (1 : Ω)) (fun _ => 0) s)) h
  simp at this

/- English proof (translation)
Proceed by induction on `hr using Submodule.span_induction with`. Consider the case `mem r hr => obtain ⟨s, hs, rfl⟩ := hr`. Conclude with `h1 s hs`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add]`.

Conclude with `lt_of_lt_of_le (lt_min ha hb) (u.map_add _ _)`. Consider the case `smul a b _ hb`. Rewrite using `[smul_eq_mul, map_mul, AddValuation.map_mul]`. Conclude with `lt_of_lt_of_le hb (le_add_of_nonneg_left (h0 a))`.
-/
theorem pos_of_mem_map {R R' C : Type} [CommRing R] [CommRing R'] [CommRing C] (f : R →+* R') (g : R' →+* C)
    (u : AddValuation C (WithTop ℤ)) (I : Ideal R) (h0 : ∀ r, 0 ≤ u (g r)) (h1 : ∀ r ∈ I, 0 < u (g (f r)))
    {r : R'} (hr : r ∈ I.map f) : 0 < u (g r) := by
  induction hr using Submodule.span_induction with
  | mem r hr => obtain ⟨s, hs, rfl⟩ := hr; exact h1 s hs
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact lt_of_lt_of_le (lt_min ha hb) (u.map_add _ _)
  | smul a b _ hb =>
    rw [smul_eq_mul, map_mul, AddValuation.map_mul]
    exact lt_of_lt_of_le hb (le_add_of_nonneg_left (h0 a))

/- English proof (translation)
Take `⟨t, ht⟩` from `hs.exists_right_inv`. Establish `h` using `congrArg u ht`. Rewrite `h` using `[AddValuation.map_mul, AddValuation.map_one]`. Establish `: u s ≠ ⊤` using `fun h' => by rw [h', top_add] at h; exact WithTop.top_ne_zero h`. Take `⟨n, hn⟩` from `WithTop.ne_top_iff_exists.1 this`.

Conclude with `⟨n, hn.symm⟩`.
-/
theorem val_unit_int {C : Type} [CommRing C] (u : AddValuation C (WithTop ℤ)) {s : C} (hs : IsUnit s) :
    ∃ n : ℤ, u s = n := by
  obtain ⟨t, ht⟩ := hs.exists_right_inv
  have h := congrArg u ht
  rw [AddValuation.map_mul, AddValuation.map_one] at h
  have : u s ≠ ⊤ := fun h' => by rw [h', top_add] at h; exact WithTop.top_ne_zero h
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 this
  exact ⟨n, hn.symm⟩

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact W.zero_mem`. Consider the case `add a b ha hb => exact W.add_mem ha hb`. Consider the case `tmul a l`. Take `⟨q, hq, p, h⟩` from `hb l`.

Establish `hl : l = ∑ k, (q⁻¹ * p k) • b k`. Simplify using `only [mul_smul, ← Finset.smul_sum]`. Simplify using `only [Algebra.smul_def (p _)]`. Rewrite using `[← h, ← Algebra.smul_def, inv_smul_smul₀ hq]`. Rewrite using `[hl, TensorProduct.tmul_sum]`.

Use `W.sum_mem fun k _ => ?_` and prove the remaining obligations. Establish `: a ⊗ₜ[F] ((q⁻¹ * p k) • b k) = ((q⁻¹ * p k) • a) • ((1 : K') ⊗ₜ[F] b k)`. Rewrite using `[← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[this]`. Conclude with `W.smul_mem _ (hW k)`.
-/
theorem eq_top_of_span {F K' L δ : Type} [Field F] [Field K'] [Field L] [Algebra F K'] [Algebra F L] [Fintype δ]
    (b : δ → L) (hb : ∀ l : L, ∃ q : F, q ≠ 0 ∧ ∃ p : δ → F, algebraMap F L q * l = ∑ k, algebraMap F L (p k) * b k)
    (W : Submodule K' (K' ⊗[F] L)) (hW : ∀ k, (1 : K') ⊗ₜ[F] b k ∈ W) (z : K' ⊗[F] L) : z ∈ W := by
  induction z using TensorProduct.induction_on with
  | zero => exact W.zero_mem
  | add a b ha hb => exact W.add_mem ha hb
  | tmul a l =>
    obtain ⟨q, hq, p, h⟩ := hb l
    have hl : l = ∑ k, (q⁻¹ * p k) • b k := by
      simp only [mul_smul, ← Finset.smul_sum]
      simp only [Algebra.smul_def (p _)]
      rw [← h, ← Algebra.smul_def, inv_smul_smul₀ hq]
    rw [hl, TensorProduct.tmul_sum]
    refine W.sum_mem fun k _ => ?_
    have : a ⊗ₜ[F] ((q⁻¹ * p k) • b k) = ((q⁻¹ * p k) • a) • ((1 : K') ⊗ₜ[F] b k) := by
      rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact W.smul_mem _ (hW k)

end Alg

section Comp

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

def eVar {D' N' : ℕ} (hD : D' = WeightFamilies.dimY D j) (eN : Fin (N' + 1) ≃ Fin N) : TVar D' N' ≃ Idx D j N :=
  Equiv.prodCongr (finCongr (by rw [hD])) eN

/- English proof (translation)
Establish `hZ : Z = c`. Assume the negation of the conclusion as `hne`. Take `⟨k, p, q, hp, -⟩` from `GlobalTheory.SecPoint.exists_ratio X N w (gF c) (hB c) hk 0`. Take `⟨g', h1, h2⟩` from `hsplit c _ p`. Take `⟨m, hm⟩` from `h k`.

Use `hm g'` as an intermediate fact. Rewrite `this` using `[h2 Z hne, h1, AddValuation.map_zero, top_add]`. Conclude with `hp ((AddValuation.top_iff v₀).1 this.symm)`. Substitute `hZ` using the available equality. Use `congr 1`.

Apply `AddValuation.ext` to reduce the goal to its premises. Introduce `a`. Take `⟨k, p, q, hp, hq⟩` from `GlobalTheory.SecPoint.exists_ratio X N w (gF Z) (hB Z) hk a`. Take `⟨m, hm⟩` from `h k`. Establish `h1` using `hm q`.

Rewrite `h1` using `[← hq, AddValuation.map_mul, AddValuation.map_mul, add_assoc, hm p]`. Conclude with `WithTop.add_right_cancel (fun h' => hp ((AddValuation.top_iff v₀).1 h')) h1`.
-/
theorem comp_val_eq {ι : Type} (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)]
    (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)
    (hsplit : ∀ (Z : ι) (u : WeightFamilies.Wt D j) (g : B.Cusp j u), ∃ g' : B.Cusp j u,
      gF Z (X.inc u g') = gF Z (X.inc u g) ∧ ∀ Z', Z' ≠ Z → gF Z' (X.inc u g') = 0)
    (hB : ∀ Z, CurveLoc.BirAt X N w (gF Z)) (Z c : ι) (hk : ∃ k, gF c (X.inc wL (w k)) ≠ 0)
    (v : AddValuation (Ω Z) (WithTop ℤ)) (v₀ : AddValuation (Ω c) (WithTop ℤ))
    (h : ∀ k : ℕ, ∃ m : ℤ, ∀ F : B.Cusp j (addL (wt0 D j) wL k),
      v (gF Z (X.inc _ F)) + m = v₀ (gF c (X.inc _ F))) :
    (⟨Z, v⟩ : Σ c, AddValuation (Ω c) (WithTop ℤ)) = ⟨c, v₀⟩ := by
  have hZ : Z = c := by
    by_contra hne
    obtain ⟨k, p, q, hp, -⟩ := GlobalTheory.SecPoint.exists_ratio X N w (gF c) (hB c) hk 0
    obtain ⟨g', h1, h2⟩ := hsplit c _ p
    obtain ⟨m, hm⟩ := h k
    have := hm g'
    rw [h2 Z hne, h1, AddValuation.map_zero, top_add] at this
    exact hp ((AddValuation.top_iff v₀).1 this.symm)
  subst hZ
  congr 1
  apply AddValuation.ext
  intro a
  obtain ⟨k, p, q, hp, hq⟩ := GlobalTheory.SecPoint.exists_ratio X N w (gF Z) (hB Z) hk a
  obtain ⟨m, hm⟩ := h k
  have h1 := hm q
  rw [← hq, AddValuation.map_mul, AddValuation.map_mul, add_assoc, hm p] at h1
  exact WithTop.add_right_cancel (fun h' => hp ((AddValuation.top_iff v₀).1 h')) h1

variable {D' N' : ℕ} (hD : D' = WeightFamilies.dimY D j) (eN : Fin (N' + 1) ≃ Fin N)
  [Algebra (KTf B.KO D' N') (Kp X la N)]
  (hC : ∀ a : B.KO, algebraMap (KTf B.KO D' N') (Kp X la N)
    (algebraMap (KTp B.KO D' N') (KTf B.KO D' N') (MvPolynomial.C a)) =
      algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a))
  (hT : ∀ p, algebraMap (KTf B.KO D' N') (Kp X la N)
    (algebraMap (KTp B.KO D' N') (KTf B.KO D' N') (MvPolynomial.X p)) =
      algebraMap (Op X la N) (Kp X la N) (Tv X la N (eVar hD eN p)))
  {Ω : Type} [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω) (j₀ : Fin (N' + 1)) (x : Fin N' → Ω)
  [Algebra (KTf B.KO D' N') (OmS Ω D' N')]
  (hS : ∀ p : KTp B.KO D' N', algebraMap (KTf B.KO D' N') (OmS Ω D' N')
    (algebraMap (KTp B.KO D' N') (KTf B.KO D' N') p) = sHom j₀ x p)
  (h0 : gF (X.inc wL (w (eN j₀))) ≠ 0)
  (hx : ∀ k, gF (X.inc wL (w (eN (j₀.succAbove k)))) = x k * gF (X.inc wL (w (eN j₀))))

include hC hT hS h0 hx in

/- English proof (translation)
Substitute `hD` using the available equality. Establish `key : ∀ (a : KTf B.KO (WeightFamilies.dimY D j) N') (l : OmS Ω (WeightFamilies.dimY D j) N'), algebraMap (Kp X la N) (Kp X la N ⊗[KTf B.KO (WeightFamilies.dimY D j) N'] OmS Ω (WeightFamilies.dimY D j) N') (algebraMap (KTf B.KO (WeightFamilies.dimY D j) N') (Kp X la N) a) * (1 ⊗ₜ …`. Introduce `a l`. Rewrite using `[← Algebra.smul_def, algebraMap_smul, ← Algebra.smul_def, TensorProduct.tmul_smul]`. Establish `hsum : ∀ i : Fin (WeightFamilies.dimY D j + 1), ∑ k, algebraMap (Kp X la N) (Kp X la N ⊗[KTf B.KO (WeightFamilies.dimY D j) N'] OmS Ω (WeightFamilies.dimY D j) N') (algebraMap (Op X la N) (Kp X la N) (Tv X la N (i, k))) * (1 ⊗ₜ algebraMap Ω (OmS Ω (WeightFamilies.dimY D j) N') (g …`.

Introduce `i`. Rewrite using `[← eN.sum_comp, TensorProduct.tmul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `hT (i, k)` as an intermediate fact. Rewrite `this` using `[show eVar rfl eN (i, k) = (i, eN k) from rfl]`.

Rewrite using `[← this, key, hS, sHom, MvPolynomial.aeval_X]`. Use `GlobalTheory.SecEval.exists_section_maps D B P j X la N wL u w _ (((Algebra.TensorProduct.includeRight : OmS Ω (WeightFamilies.dimY D j) N' →ₐ[KTf B.KO (WeightFamilies.dimY D j) N'] Kp X la N ⊗[KTf B.KO (WeightFamilies.dimY D j) N'] OmS Ω (WeightFamilies.dimY D j) N').toRingHom.c …` and prove the remaining obligations. Use `show (1 : Kp X la N) ⊗ₜ algebraMap Ω (OmS Ω (WeightFamilies.dimY D j) N') (gF (a • f)) = _ * (1 ⊗ₜ algebraMap Ω (OmS Ω (WeightFamilies.dimY D j) N') (gF f))`. Rewrite using `[← hC, key, hS, map_smul, Algebra.smul_def, map_mul, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]`. Use `(hsum i.succ).trans ?_` and prove the remaining obligations.

Rewrite using `[sum_sImg_succ j₀ x (fun k => gF (X.inc wL (w (eN k)))) hx, TensorProduct.tmul_zero]`. Use `(hsum 0).symm ▸ ?_` and prove the remaining obligations. Conclude with `(IsUnit.mk0 _ (sum_sImg_zero j₀ x (fun k => gF (X.inc wL (w (eN k)))) hx h0)).map (Algebra.TensorProduct.includeRight : OmS Ω (WeightFamilies.dimY D j) N' →ₐ[KTf B.KO (WeightFamilies.dimY D j) N'] Kp X la N ⊗[KTf B.KO (WeightFamilies.dimY D j) N'] OmS Ω (WeightFamilies.dimY D j) …`.
-/
theorem exists_comp_maps (u : WeightFamilies.Wt D j) :
    ∃ (Θ : Rp X la N →ₐ[Kp X la N] Kp X la N ⊗[KTf B.KO D' N'] OmS Ω D' N')
      (ψ : OsK X la w →ₐ[Kp X la N] Kp X la N ⊗[KTf B.KO D' N'] OmS Ω D' N')
      (Ψ : SectionSheafQuotient X la w u →ₗ[Kp X la N] Kp X la N ⊗[KTf B.KO D' N'] OmS Ω D' N'),
      (∀ F, Θ (emb X la N F) = 1 ⊗ₜ algebraMap Ω (OmS Ω D' N') (gF F)) ∧
      IsUnit (Θ (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0)) ∧
      (∀ (x : OsK X la w) (a : SectionSheafQuotient X la w u), Ψ (x • a) = ψ x * Ψ a) ∧
      (∀ (k : ℕ) (g : ↥(Vw X la N (addL (wt0 D j) wL k))),
        ψ (toOsK X la w (fr0 X la w k g)) * Θ (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0) ^ k = Θ g) ∧
      ∀ f : ↥(Vw X la N u), Ψ (rho0 X la w u f) = Θ f := by
  subst hD
  have key : ∀ (a : KTf B.KO (WeightFamilies.dimY D j) N') (l : OmS Ω (WeightFamilies.dimY D j) N'),
      algebraMap (Kp X la N) (Kp X la N ⊗[KTf B.KO (WeightFamilies.dimY D j) N'] OmS Ω (WeightFamilies.dimY D j) N')
        (algebraMap (KTf B.KO (WeightFamilies.dimY D j) N') (Kp X la N) a) * (1 ⊗ₜ l) =
        1 ⊗ₜ (algebraMap (KTf B.KO (WeightFamilies.dimY D j) N') (OmS Ω (WeightFamilies.dimY D j) N') a * l) := by
    intro a l
    rw [← Algebra.smul_def, algebraMap_smul, ← Algebra.smul_def, TensorProduct.tmul_smul]
  have hsum : ∀ i : Fin (WeightFamilies.dimY D j + 1),
      ∑ k, algebraMap (Kp X la N) (Kp X la N ⊗[KTf B.KO (WeightFamilies.dimY D j) N'] OmS Ω (WeightFamilies.dimY D j) N')
        (algebraMap (Op X la N) (Kp X la N) (Tv X la N (i, k))) *
          (1 ⊗ₜ algebraMap Ω (OmS Ω (WeightFamilies.dimY D j) N') (gF (X.inc wL (w k)))) =
      1 ⊗ₜ ∑ k, sImg j₀ x (i, k) * algebraMap Ω (OmS Ω (WeightFamilies.dimY D j) N') (gF (X.inc wL (w (eN k)))) := by
    intro i
    rw [← eN.sum_comp, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := hT (i, k)
    rw [show eVar rfl eN (i, k) = (i, eN k) from rfl] at this
    rw [← this, key, hS, sHom, MvPolynomial.aeval_X]
  refine GlobalTheory.SecEval.exists_section_maps D B P j X la N wL u w _
    (((Algebra.TensorProduct.includeRight : OmS Ω (WeightFamilies.dimY D j) N' →ₐ[KTf B.KO (WeightFamilies.dimY D j) N']
      Kp X la N ⊗[KTf B.KO (WeightFamilies.dimY D j) N'] OmS Ω (WeightFamilies.dimY D j) N').toRingHom.comp
      (algebraMap Ω (OmS Ω (WeightFamilies.dimY D j) N'))).comp gF.toRingHom) (fun a f => ?_) (fun i => ?_) ?_
  · show (1 : Kp X la N) ⊗ₜ algebraMap Ω (OmS Ω (WeightFamilies.dimY D j) N') (gF (a • f)) =
      _ * (1 ⊗ₜ algebraMap Ω (OmS Ω (WeightFamilies.dimY D j) N') (gF f))
    rw [← hC, key, hS, map_smul, Algebra.smul_def, map_mul, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]
  · refine (hsum i.succ).trans ?_
    rw [sum_sImg_succ j₀ x (fun k => gF (X.inc wL (w (eN k)))) hx, TensorProduct.tmul_zero]
  · refine (hsum 0).symm ▸ ?_
    exact (IsUnit.mk0 _ (sum_sImg_zero j₀ x (fun k => gF (X.inc wL (w (eN k)))) hx h0)).map
      (Algebra.TensorProduct.includeRight : OmS Ω (WeightFamilies.dimY D j) N' →ₐ[KTf B.KO (WeightFamilies.dimY D j) N']
        Kp X la N ⊗[KTf B.KO (WeightFamilies.dimY D j) N'] OmS Ω (WeightFamilies.dimY D j) N')

include hC hT hS h0 hx in

/- English proof (translation)
Substitute `hD` using the available equality. Take `⟨χ, h1, h2⟩` from `GlobalTheory.exists_ringHom_tensor_OmS_of_point B.KO Ω (Kp X la N) U (WeightFamilies.dimY D j) N' j₀ x (GlobalTheory.SecPoint.evK X la N ev) τ (fun p => algebraMap (Op X la N) (Kp X la N) (Tv X la N (eVar rfl eN p))) htr hS hT (fun a => by rw [hC, hτ]) (fun i => by`. Establish `h3` using `GlobalTheory.SecPoint.ev_sec X la N w gF ev τ σ hc i.succ`. Rewrite `h3` using `[honS, eq_comm, mul_eq_zero, or_iff_left hσ, ← eN.sum_comp, Fin.sum_univ_succAbove _ j₀]`. Simplify using `only [hx, map_mul, ← mul_assoc, ← Finset.sum_mul, ← add_mul] at h3`.

Conclude with `(mul_eq_zero.1 h3).resolve_right ((map_ne_zero τ).2 h0))`. Establish `key : ev g = χ (Θ g) * σ ^ k` using `by clear h`. Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨F, rfl⟩` from `hy`.

Rewrite using `[hΘ, h2, hc k _ (emb_mem_Vw X la N _ F)]`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add, map_add, map_add, ha, hb, add_mul]`. Consider the case `smul a b _ hb`. Rewrite using `[GlobalTheory.SecPoint.ev_smul, hb, map_smul, Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, h1, mul_assoc]`.

Rewrite using `[key, h, map_zero, zero_mul]`.
-/
theorem ev_eq_zero (htr : Algebra.trdeg B.KO Ω = D')
    (Θ : Rp X la N →ₐ[Kp X la N] Kp X la N ⊗[KTf B.KO D' N'] OmS Ω D' N')
    (hΘ : ∀ F, Θ (emb X la N F) = 1 ⊗ₜ algebraMap Ω (OmS Ω D' N') (gF F))
    {U : Type} [Field U] (ev : Rp X la N →+* U)
    (honS : ∀ i : Fin (WeightFamilies.dimY D j), ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i.succ) = 0)
    (τ : Ω →+* U) (σ : U) (hσ : σ ≠ 0)
    (hτ : ∀ a : B.KO, τ (algebraMap B.KO Ω a) =
      GlobalTheory.SecPoint.evK X la N ev (algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a)))
    (hc : ∀ (k : ℕ) (G : X.Forms), emb X la N G ∈ Vw X la N (addL (wt0 D j) wL k) →
      ev (emb X la N G) = τ (gF G) * σ ^ k)
    (k : ℕ) (g : Rp X la N) (hg : g ∈ Vw X la N (addL (wt0 D j) wL k)) (h : Θ g = 0) : ev g = 0 := by
  subst hD
  obtain ⟨χ, h1, h2⟩ := GlobalTheory.exists_ringHom_tensor_OmS_of_point B.KO Ω (Kp X la N) U (WeightFamilies.dimY D j) N' j₀ x (GlobalTheory.SecPoint.evK X la N ev) τ
    (fun p => algebraMap (Op X la N) (Kp X la N) (Tv X la N (eVar rfl eN p))) htr hS hT
    (fun a => by rw [hC, hτ]) (fun i => by
      have h3 := GlobalTheory.SecPoint.ev_sec X la N w gF ev τ σ hc i.succ
      rw [honS, eq_comm, mul_eq_zero, or_iff_left hσ, ← eN.sum_comp, Fin.sum_univ_succAbove _ j₀] at h3
      simp only [hx, map_mul, ← mul_assoc, ← Finset.sum_mul, ← add_mul] at h3
      exact (mul_eq_zero.1 h3).resolve_right ((map_ne_zero τ).2 h0))
  have key : ev g = χ (Θ g) * σ ^ k := by
    clear h
    induction hg using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨F, rfl⟩ := hy
      rw [hΘ, h2, hc k _ (emb_mem_Vw X la N _ F)]
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, map_add, map_add, ha, hb, add_mul]
    | smul a b _ hb =>
      rw [GlobalTheory.SecPoint.ev_smul, hb, map_smul, Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply, h1, mul_assoc]
  rw [key, h, map_zero, zero_mul]

end Comp

section Main

open ReciprocityTheory.ChartRestriction.G.T0 (Data ratio OT)

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
  {ι : Type} [Fintype ι] {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra B.KO (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra B.KO (A c)]
  [∀ c, Algebra (𝓞 B.KO) (A c)] {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

/- English proof (translation)
Use `letI := d.algOp hs la c`. Use `letI : Algebra (OT B.KO d.D d.N) (OmS (Ω c) d.D d.N) := (d.OTtoS c).toAlgebra`. Use `haveI : IsScalarTower (OT B.KO d.D d.N) (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (OmS (Ω c) d.D d.N) := IsScalarTower.of_algebraMap_eq fun x => by show _ = d.KTtoS hs c (ReciprocityTheory.ChartRestriction.G.T0.OpToKT d.D d.N la (algebraMap _ _ x))`. Rewrite using `[ReciprocityTheory.ChartRestriction.G.T0.OpToKT, IsLocalization.lift_eq]`. Conclude with `(IsFractionRing.lift_algebraMap (g := (d.sH c).toRingHom) (hs c) (ReciprocityTheory.ChartRestriction.G.T0.OTtoKT B.KO d.D d.N x)).symm`.

Establish `h` using `ReciprocityTheory.ChartRestriction.G.T0.ValPl.placesOver_iff_loc (O := ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (ReciprocityTheory.ChartRestriction.G.T0.laT d.D d.N la) w`. Conclude with `⟨fun hw => ⟨hw.1, h.2 hw.2⟩, fun hw => ⟨hw.1, h.1 hw.2⟩⟩`.
-/
theorem plOver_iff (d : Data B.KO ι Ω WT A) (hs : d.S1) (la : HeightOneSpectrum (𝓞 B.KO)) (c : ι)
    (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) :
    letI := d.algOp hs la c
    w ∈ ReciprocityTheory.ChartRestriction.G.T0.ValPl.PlacesOver (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (OmS (Ω c) d.D d.N) ↔
      w ∈ d.PlOver la c := by
  letI := d.algOp hs la c
  letI : Algebra (OT B.KO d.D d.N) (OmS (Ω c) d.D d.N) := (d.OTtoS c).toAlgebra
  haveI : IsScalarTower (OT B.KO d.D d.N) (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (OmS (Ω c) d.D d.N) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      show _ = d.KTtoS hs c (ReciprocityTheory.ChartRestriction.G.T0.OpToKT d.D d.N la (algebraMap _ _ x))
      rw [ReciprocityTheory.ChartRestriction.G.T0.OpToKT, IsLocalization.lift_eq]
      exact (IsFractionRing.lift_algebraMap (g := (d.sH c).toRingHom) (hs c)
        (ReciprocityTheory.ChartRestriction.G.T0.OTtoKT B.KO d.D d.N x)).symm
  have h := ReciprocityTheory.ChartRestriction.G.T0.ValPl.placesOver_iff_loc (O := ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la)
    (ReciprocityTheory.ChartRestriction.G.T0.laT d.D d.N la) w
  exact ⟨fun hw => ⟨hw.1, h.2 hw.2⟩, fun hw => ⟨hw.1, h.1 hw.2⟩⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 200000 in

/- English proof (translation)
Take `⟨f, φ, hflat, hloc, hmax, hres, hφ, hC, hT⟩` from `GlobalTheory.GaussCompletion.gaussRing_completion_rename D B P j X la G.N d.D d.N (eVar hD eN)`. Use `haveI := ReciprocityTheory.ChartRestriction.G.T0.Op_isDVR (K := B.KO) d.D d.N la`. Use `letI : Algebra (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Op X la G.N) := f.toAlgebra`. Use `letI : Algebra (KTf B.KO d.D d.N) (Kp X la G.N) := φ.toAlgebra`. Use `letI := ReciprocityTheory.ChartRestriction.G.T0.algOpKT (K := B.KO) d.D d.N la`.

Use `haveI := ReciprocityTheory.ChartRestriction.G.T0.isFractionRing_Op (K := B.KO) d.D d.N la`. Use `letI : Algebra (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Kp X la G.N) := ((algebraMap (Op X la G.N) (Kp X la G.N)).comp f).toAlgebra`. Use `haveI : IsScalarTower (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (KTf B.KO d.D d.N) (Kp X la G.N) := IsScalarTower.of_algebraMap_eq fun r => (hφ r).symm`. Use `haveI : IsScalarTower (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Op X la G.N) (Kp X la G.N) := IsScalarTower.of_algebraMap_eq fun r => rfl`. Use `haveI : Module.Flat (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Op X la G.N) := hflat`.

Use `haveI : IsLocalHom (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Op X la G.N)) := hloc`. Use `letI : ∀ c, Algebra (KTf B.KO d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (d.KTtoS hs c).toAlgebra`. Use `letI : ∀ c, Algebra (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (OmS (Ω c) d.D d.N) := fun c => d.algOp hs la c`. Use `haveI : ∀ c, IsScalarTower (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (KTf B.KO d.D d.N) (OmS (Ω c) d.D d.N) := fun c => IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : ∀ c, FiniteDimensional (KTf B.KO d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (d.omS_finite hd hs c).1`.

Establish `hS : ∀ c (p : KTp B.KO d.D d.N), algebraMap (KTf B.KO d.D d.N) (OmS (Ω c) d.D d.N) (algebraMap (KTp B.KO d.D d.N) (KTf B.KO d.D d.N) p) = sHom (d.jc c) (d.x c) p` using `fun c p => IsFractionRing.lift_algebraMap (hs c) p`. Use `choose Θ ψ Ψ hΘ hu hmul hfr hrho using fun c => exists_comp_maps X la G.w hD eN hC hT (gF c) (d.jc c) (d.x c) (hS c) (h0 c) (hx c) wF`. Take `⟨hfin, hred, hgen⟩` from `hcurve`. Use `haveI : CharZero (Kp X la G.N) := charZero_of_injective_ringHom ((algebraMap (X.Kl la) (Kp X la G.N)).comp (algebraMap B.KO (X.Kl la))).injective`. Use `haveI : ∀ ζ : PtsG G la, IsDVRAt ζ := (integralClosure_dvr' (Op X la G.N) (Kp X la G.N) (OsK X la G.w)).2`.

Establish `hirr : Irreducible (unifO X la G.N)` using `Op.irreducible_map _ _ _ (Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (X.Ol la)))`. Establish `hU : IsUnif (OsK X la G.w) (unifO X la G.N)` using `isUnif_of_field (Kp X la G.N) hirr`. Take `⟨hval, hzero⟩` from `GlobalTheory.OrdVal.valuation_eq_ord_and_eq_zero (Op X la G.N) (OsK X la G.w) (unifO X la G.N) hU`. Establish `hres' : ∀ (F : B.Cusp j wF) c, Ψ c (resF G la F) = 1 ⊗ₜ algebraMap (Ω c) (OmS (Ω c) d.D d.N) (gF c (X.inc wF F))` using `fun F c => (hrho c _).trans (hΘ c _)`. Set `s : ∀ c, Kp X la G.N ⊗[KTf B.KO d.D d.N] OmS (Ω c) d.D d.N` to `fun c => 1 ⊗ₜ algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ε c)⁻¹`.

Establish `hsu : ∀ c, IsUnit (s c)` using `fun c => (IsUnit.mk0 _ ((map_ne_zero (algebraMap (Ω c) (OmS (Ω c) d.D d.N))).2 (inv_ne_zero (hε c)))).map (Algebra.TensorProduct.includeRight : OmS (Ω c) d.D d.N →ₐ[KTf B.KO d.D d.N] Kp X la G.N ⊗[KTf B.KO d.D d.N] OmS (Ω c) d.D d.N)`. Set `Ψ' : ∀ c, SectionSheafQuotient X la G.w wF →ₗ[Kp X la G.N] Kp X la G.N ⊗[KTf B.KO d.D d.N] OmS (Ω c) d.D d.N` to `fun c => LinearMap.mulRight (Kp X la G.N) (s c) ∘ₗ Ψ c`. Establish `hΨ' : ∀ c a, Ψ' c a = Ψ c a * s c` using `fun _ _ => rfl`. Establish `ht : ∀ k c, Ψ' c (tL G la (eD k)) = 1 ⊗ₜ d.bvecG hd.sel hd.a4.choose k c`. Introduce `k c`.

Rewrite using `[hΨ', tL, hres', hb]`. Simplify using `only [s, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← map_mul, mul_inv_cancel_right₀ (hε c)]`. Both sides reduce to the same expression. Establish `hsurj : ∀ c z, z ∈ LinearMap.range (Ψ' c)`. Introduce `c`.

Use `eq_top_of_span (fun k => d.bvecG hd.sel hd.a4.choose k c) (fun l => ?_) _ fun k => ⟨_, ht k c⟩` and prove the remaining obligations. Take `⟨q, hq, p, hp⟩` from `hd.a4.choose_spec.2.2 (Pi.single c l)`. Use `⟨algebraMap (KTp B.KO d.D d.N) _ q, fun h => hq c ?_, fun k => algebraMap (KTp B.KO d.D d.N) _ (p k), ?_⟩` and prove the remaining obligations. Rewrite using `[Data.sH, ← hS, h, map_zero]`. Use `hp c` as an intermediate fact.

Rewrite `this` using `[Pi.single_eq_same]`. Simplify using `only [hS]`. Conclude with `this`. Establish `hcoord : ∀ c a, Ψ' c a = ψ c (coord Q.e a) * Ψ' c Q.e`. Introduce `c a`.

Use `conv_lhs => rw [← coord_smul_self hgen a]`. Rewrite using `[hΨ', hΨ', hmul, mul_assoc]`. Establish `heu : ∀ c, IsUnit (Ψ' c Q.e)`. Introduce `c`. Take `⟨a, ha⟩` from `hsurj c 1`.

Rewrite `ha` using `[hcoord, mul_comm]`. Conclude with `IsUnit.of_mul_eq_one _ ha`. Establish `hψs : ∀ c z, ∃ x, ψ c x = z`. Introduce `c z`. Take `⟨a, ha⟩` from `hsurj c (z * Ψ' c Q.e)`.

Rewrite `ha` using `[hcoord]`. Conclude with `⟨_, (heu c).mul_right_cancel ha⟩`. Establish `hψi : ∀ x, (∀ c, ψ c x = 0) → x = 0`. Introduce `x hx0`. Take `⟨x, rfl⟩` from `toOsK_surjective X la G.w x`.

Take `⟨k, g, rfl⟩` from `exists_weightZero_fraction_eq X la G.w x`. Use `hzero _ fun ζ => ?_` and prove the remaining obligations. Take `⟨U, _, ev, hevu, honS, htop⟩` from `hpt1 ζ`. Take `⟨Z, τ, σ, hσ, -, hτ, hc⟩` from `GlobalTheory.SecPoint.exists_point X la G.N G.w Ω gF hinj (fun Z k => hsplit Z wL (G.w k)) hB hCt ev hevu honS`. Use `htop k g (ev_eq_zero X la G.w hD eN hC hT (gF Z) (d.jc Z) (d.x Z) (hS Z) (h0 Z) (hx Z) (hd.trdeg Z) (Θ Z) (hΘ Z) ev honS τ σ hσ hτ hc k g g.2 ?_)` and prove the remaining obligations.

Rewrite using `[← hfr, hx0, zero_mul]`. Use `GlobalTheory.length_quotient_le_of_order_bound (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Op X la G.N) (KTf B.KO d.D d.N) (Kp X la G.N) hmax ?_ ι (fun c => OmS (Ω c) d.D d.N) (fun c w => d.ord c (d.Wres c w) d.wF (hd.a4.choose c)) (fun c => ?_) (Fin d.del) (Fin G.de …` and prove the remaining obligations. Introduce `r`. Take `⟨r, rfl⟩` from `IsLocalRing.residue_surjective r`. Take `⟨a, ha⟩` from `hres r`.

Use `⟨IsLocalRing.residue _ a, ?_⟩` and prove the remaining obligations. Rewrite using `[IsLocalRing.ResidueField.map_residue, eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]`. Conclude with `ha`. Take `⟨g, hg, hg'⟩` from `(GlobalTheory.PlaceRestrict.places_restrict_injective B.KO ι Ω WT A 𝒜 d hd hs la c).2.2.1 (fun w => d.ord c (d.Wres c w) d.wF (hd.a4.choose c))`. Conclude with `⟨algebraMap (Ω c) _ g, (map_ne_zero _).2 hg, fun w hw => hg' w ((plOver_iff d hs la c w).1 hw)⟩`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Establish `h1 : (coord Q.e a : OsK X la G.w) = 0` using `hψi _ fun c => by`. Establish `h2 : Ψ' c a = 0` using `congrFun ha c`. Rewrite `h2` using `[hcoord]`.

Conclude with `(heu c).mul_left_eq_zero.1 h2`. Rewrite using `[← coord_smul_self hgen a, h1, zero_smul]`. Introduce `a ha c w hw u hu1 hu0`. Establish `halg : ∀ r : Op X la G.N, ψ c (algebraMap (Op X la G.N) (OsK X la G.w) r) = algebraMap (Op X la G.N) (Kp X la G.N) r ⊗ₜ 1` using `fun r => by`. Rewrite using `[IsScalarTower.algebraMap_apply (Op X la G.N) (Kp X la G.N) (OsK X la G.w), AlgHom.commutes]`.

Both sides reduce to the same expression. Take `⟨ζ, hζ⟩` from `hval (u.comap (ψ c).toRingHom) (fun r => by show 0 ≤ u (ψ c _)`. Rewrite using `[halg]; exact hu0 r) (by`. Use `pos_of_mem_map f ((ψ c).toRingHom.comp (algebraMap (Op X la G.N) (OsK X la G.w))) u (IsLocalRing.maximalIdeal _) (fun r => ?_) (fun r hr => ?_) (hmax ▸ hirr.not_isUnit)` and prove the remaining obligations. Use `show 0 ≤ u (ψ c _)`.

Rewrite using `[halg]`. Conclude with `hu0 r`. Use `show 0 < u (ψ c (algebraMap (Op X la G.N) (OsK X la G.w) (f r)))`. Rewrite using `[halg, ← hφ]`. Establish `: (φ (ReciprocityTheory.ChartRestriction.G.T0.OpToKT d.D d.N la r) ⊗ₜ 1 : Kp X la G.N ⊗[KTf B.KO d.D d.N] OmS (Ω c) d.D d.N) = 1 ⊗ₜ algebraMap (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (OmS (Ω c) d.D d.N) r` using `Algebra.TensorProduct.tmul_one_eq_one_tmul (ReciprocityTheory.ChartRestriction.G.T0.OpToKT d.D d.N la r)`.

Rewrite using `[this, hu1]`. Conclude with `(hw.2 r).2.2 hr) (by`. Take `⟨π, hπ⟩` from `hw.1.2`. Take `⟨x, hx⟩` from `hψs c (1 ⊗ₜ π)`. Conclude with `⟨x, by show u (ψ c x) = 1; rw [hx, hu1, hπ]⟩)`.

Establish `hζ' : ∀ x, Formalism.MainNotions.Gaps.EtaleWeightGaps.ord (unifO X la G.N) ζ x = u (ψ c x)` using `hζ`. Establish `hW : ∀ a : Ω c, u (1 ⊗ₜ algebraMap (Ω c) (OmS (Ω c) d.D d.N) a) = d.Wres c w a` using `fun a => hu1 _`. Take `⟨Z, v, hv1, hv2⟩` from `hpt2 ζ`. Take `⟨n, hn⟩` from `val_unit_int u (hu c)`. Establish `heq` using `comp_val_eq X G.w Ω gF hsplit hB Z c ⟨_, h0 c⟩ v (d.Wres c w) fun k => by`.

Take `⟨m, hm⟩` from `hv1 k`. Use `⟨m + k * n, fun F => ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg u (hfr c k ⟨emb X la G.N (X.inc _ F), emb_mem_Vw X la G.N _ F⟩)`. Rewrite `h1` using `[AddValuation.map_mul, AddValuation.map_pow, hn, ← hζ', hm, hΘ, hW]`. Rewrite using `[← h1, add_assoc, ← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul]`.

Take `rfl : Z = c` from `congrArg Sigma.fst heq`. Take `rfl : v = d.Wres Z w` from `eq_of_heq (Sigma.mk.inj heq).2`. Establish `he : Ψ' Z Q.e = 1 ⊗ₜ algebraMap (Ω Z) (OmS (Ω Z) d.D d.N) (gF Z (X.inc wF Q.g0) * (ε Z)⁻¹)`. Rewrite using `[hΨ', LocalPointData.e, hres']`. Simplify using `only [s, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← map_mul]`.

Establish `hg0 : gF Z (X.inc wF Q.g0) ≠ 0`. Introduce `h`. Take `⟨n', hn'⟩` from `val_unit_int u (heu Z)`. Rewrite `hn'` using `[he, hW, h, zero_mul, AddValuation.map_zero]`. Conclude with `WithTop.top_ne_coe hn'`.

Establish `hball` using `(mem_ballO_iff Q.c hU hgen a).1 ha ζ`. Rewrite `hball` using `[ordV, hζ', hv2 hg0]`. Use `show 0 ≤ u (Ψ' Z a) + _`. Rewrite using `[hcoord, AddValuation.map_mul, he, hW, hord, add_assoc, ← add_assoc (d.Wres Z w _), ← AddValuation.map_mul, inv_mul_cancel_right₀ (hε Z)]`. Conclude with `hball`.
-/
theorem ila_le (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la)
    (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z) (d : Data B.KO ι Ω WT A) (hd : d.AxH 𝒜) (hs : d.S1)
    (eN : Fin (d.N + 1) ≃ Fin G.N) (eD : Fin d.del ≃ Fin G.del) (hD : d.D = WeightFamilies.dimY D j)
    (hinj : ∀ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), (∀ Z, gF Z (X.inc u F) = 0) → F = 0)
    (hsplit : ∀ (Z : ι) (u : WeightFamilies.Wt D j) (g : B.Cusp j u), ∃ g' : B.Cusp j u,
      gF Z (X.inc u g') = gF Z (X.inc u g) ∧ ∀ Z', Z' ≠ Z → gF Z' (X.inc u g') = 0)
    (hB : ∀ Z, CurveLoc.BirAt X G.N G.w (gF Z)) (hCt : ∀ Z, CurveLoc.CountQAt X la G.N G.w (gF Z))
    (h0 : ∀ c, gF c (X.inc wL (G.w (eN (d.jc c)))) ≠ 0)
    (hx : ∀ c k, gF c (X.inc wL (G.w (eN ((d.jc c).succAbove k)))) =
      d.x c k * gF c (X.inc wL (G.w (eN (d.jc c)))))
    (ε : ∀ c, Ω c) (hε : ∀ c, ε c ≠ 0)
    (hb : ∀ k c, gF c (X.inc wF (G.th' (eD k))) =
      ratio (Ω := Ω c) (d.thp (hd.sel k) c) (hd.a4.choose c) * ε c)
    (fr : ∀ c, AddValuation (Ω c) (WithTop ℤ) → ℤ)
    (hord : ∀ c v, ((d.ord c v d.wF (hd.a4.choose c) : ℤ) : WithTop ℤ) = v (ε c) + (fr c v : ℤ))
    (hcurve : Q.InCurve)
    (hpt1 : ∀ ζ : PtsG G la, ∃ (U : Type) (_ : Field U) (ev : Rp X la G.N →+* U)
      (hu : IsUnit (ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la G.w 0))),
      (∀ i : Fin (WeightFamilies.dimY D j), ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la G.w i.succ) = 0) ∧
      ∀ (k : ℕ) (g : ↥(Vw X la G.N (addL (wt0 D j) wL k))), ev g = 0 →
        Formalism.MainNotions.Gaps.EtaleWeightGaps.ord (unifO X la G.N) ζ (toOsK X la G.w (fr0 X la G.w k g)) = ⊤)
    (hpt2 : ∀ ζ : PtsG G la, ∃ (Z : ι) (v : AddValuation (Ω Z) (WithTop ℤ)),
      (∀ k : ℕ, ∃ m : ℤ, ∀ F : B.Cusp j (addL (wt0 D j) wL k),
        Formalism.MainNotions.Gaps.EtaleWeightGaps.ord (unifO X la G.N) ζ (toOsK X la G.w (fr0 X la G.w k
          ⟨emb X la G.N (X.inc _ F), emb_mem_Vw X la G.N _ F⟩)) = v (gF Z (X.inc _ F)) + (m : ℤ)) ∧
      (gF Z (X.inc wF Q.g0) ≠ 0 → ((Q.c ζ : ℤ) : WithTop ℤ) = v (gF Z (X.inc wF Q.g0)) + (fr Z v : ℤ))) :
    Q.Ila ≤ (d.htOf hd hs).Ila la := by
  classical
  obtain ⟨f, φ, hflat, hloc, hmax, hres, hφ, hC, hT⟩ :=
    GlobalTheory.GaussCompletion.gaussRing_completion_rename D B P j X la G.N d.D d.N (eVar hD eN)
  haveI := ReciprocityTheory.ChartRestriction.G.T0.Op_isDVR (K := B.KO) d.D d.N la
  letI : Algebra (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Op X la G.N) := f.toAlgebra
  letI : Algebra (KTf B.KO d.D d.N) (Kp X la G.N) := φ.toAlgebra
  letI := ReciprocityTheory.ChartRestriction.G.T0.algOpKT (K := B.KO) d.D d.N la
  haveI := ReciprocityTheory.ChartRestriction.G.T0.isFractionRing_Op (K := B.KO) d.D d.N la
  letI : Algebra (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Kp X la G.N) :=
    ((algebraMap (Op X la G.N) (Kp X la G.N)).comp f).toAlgebra
  haveI : IsScalarTower (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (KTf B.KO d.D d.N) (Kp X la G.N) :=
    IsScalarTower.of_algebraMap_eq fun r => (hφ r).symm
  haveI : IsScalarTower (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Op X la G.N) (Kp X la G.N) :=
    IsScalarTower.of_algebraMap_eq fun r => rfl
  haveI : Module.Flat (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Op X la G.N) := hflat
  haveI : IsLocalHom (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Op X la G.N)) := hloc
  letI : ∀ c, Algebra (KTf B.KO d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (d.KTtoS hs c).toAlgebra
  letI : ∀ c, Algebra (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (OmS (Ω c) d.D d.N) := fun c => d.algOp hs la c
  haveI : ∀ c, IsScalarTower (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (KTf B.KO d.D d.N) (OmS (Ω c) d.D d.N) :=
    fun c => IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : ∀ c, FiniteDimensional (KTf B.KO d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (d.omS_finite hd hs c).1
  have hS : ∀ c (p : KTp B.KO d.D d.N), algebraMap (KTf B.KO d.D d.N) (OmS (Ω c) d.D d.N)
      (algebraMap (KTp B.KO d.D d.N) (KTf B.KO d.D d.N) p) = sHom (d.jc c) (d.x c) p := fun c p =>
    IsFractionRing.lift_algebraMap (hs c) p
  choose Θ ψ Ψ hΘ hu hmul hfr hrho using fun c =>
    exists_comp_maps X la G.w hD eN hC hT (gF c) (d.jc c) (d.x c) (hS c) (h0 c) (hx c) wF
  obtain ⟨hfin, hred, hgen⟩ := hcurve
  haveI : CharZero (Kp X la G.N) :=
    charZero_of_injective_ringHom
      ((algebraMap (X.Kl la) (Kp X la G.N)).comp (algebraMap B.KO (X.Kl la))).injective
  haveI : ∀ ζ : PtsG G la, IsDVRAt ζ := (integralClosure_dvr' (Op X la G.N) (Kp X la G.N) (OsK X la G.w)).2
  have hirr : Irreducible (unifO X la G.N) :=
    Op.irreducible_map _ _ _ (Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (X.Ol la)))
  have hU : IsUnif (OsK X la G.w) (unifO X la G.N) := isUnif_of_field (Kp X la G.N) hirr
  obtain ⟨hval, hzero⟩ := GlobalTheory.OrdVal.valuation_eq_ord_and_eq_zero (Op X la G.N) (OsK X la G.w) (unifO X la G.N) hU
  have hres' : ∀ (F : B.Cusp j wF) c, Ψ c (resF G la F) = 1 ⊗ₜ algebraMap (Ω c) (OmS (Ω c) d.D d.N) (gF c (X.inc wF F)) :=
    fun F c => (hrho c _).trans (hΘ c _)
  let s : ∀ c, Kp X la G.N ⊗[KTf B.KO d.D d.N] OmS (Ω c) d.D d.N := fun c =>
    1 ⊗ₜ algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ε c)⁻¹
  have hsu : ∀ c, IsUnit (s c) := fun c =>
    (IsUnit.mk0 _ ((map_ne_zero (algebraMap (Ω c) (OmS (Ω c) d.D d.N))).2 (inv_ne_zero (hε c)))).map
      (Algebra.TensorProduct.includeRight : OmS (Ω c) d.D d.N →ₐ[KTf B.KO d.D d.N]
        Kp X la G.N ⊗[KTf B.KO d.D d.N] OmS (Ω c) d.D d.N)
  let Ψ' : ∀ c, SectionSheafQuotient X la G.w wF →ₗ[Kp X la G.N] Kp X la G.N ⊗[KTf B.KO d.D d.N] OmS (Ω c) d.D d.N := fun c =>
    LinearMap.mulRight (Kp X la G.N) (s c) ∘ₗ Ψ c
  have hΨ' : ∀ c a, Ψ' c a = Ψ c a * s c := fun _ _ => rfl
  have ht : ∀ k c, Ψ' c (tL G la (eD k)) = 1 ⊗ₜ d.bvecG hd.sel hd.a4.choose k c := by
    intro k c
    rw [hΨ', tL, hres', hb]
    simp only [s, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← map_mul, mul_inv_cancel_right₀ (hε c)]
    rfl
  have hsurj : ∀ c z, z ∈ LinearMap.range (Ψ' c) := by
    intro c
    refine eq_top_of_span (fun k => d.bvecG hd.sel hd.a4.choose k c) (fun l => ?_) _ fun k => ⟨_, ht k c⟩
    obtain ⟨q, hq, p, hp⟩ := hd.a4.choose_spec.2.2 (Pi.single c l)
    refine ⟨algebraMap (KTp B.KO d.D d.N) _ q, fun h => hq c ?_, fun k => algebraMap (KTp B.KO d.D d.N) _ (p k), ?_⟩
    · rw [Data.sH, ← hS, h, map_zero]
    · have := hp c
      rw [Pi.single_eq_same] at this
      simp only [hS]
      exact this
  have hcoord : ∀ c a, Ψ' c a = ψ c (coord Q.e a) * Ψ' c Q.e := by
    intro c a
    conv_lhs => rw [← coord_smul_self hgen a]
    rw [hΨ', hΨ', hmul, mul_assoc]
  have heu : ∀ c, IsUnit (Ψ' c Q.e) := by
    intro c
    obtain ⟨a, ha⟩ := hsurj c 1
    rw [hcoord, mul_comm] at ha
    exact IsUnit.of_mul_eq_one _ ha
  have hψs : ∀ c z, ∃ x, ψ c x = z := by
    intro c z
    obtain ⟨a, ha⟩ := hsurj c (z * Ψ' c Q.e)
    rw [hcoord] at ha
    exact ⟨_, (heu c).mul_right_cancel ha⟩
  have hψi : ∀ x, (∀ c, ψ c x = 0) → x = 0 := by
    intro x hx0
    obtain ⟨x, rfl⟩ := toOsK_surjective X la G.w x
    obtain ⟨k, g, rfl⟩ := exists_weightZero_fraction_eq X la G.w x
    refine hzero _ fun ζ => ?_
    obtain ⟨U, _, ev, hevu, honS, htop⟩ := hpt1 ζ
    obtain ⟨Z, τ, σ, hσ, -, hτ, hc⟩ := GlobalTheory.SecPoint.exists_point X la G.N G.w Ω gF hinj
      (fun Z k => hsplit Z wL (G.w k)) hB hCt ev hevu honS
    refine htop k g (ev_eq_zero X la G.w hD eN hC hT (gF Z) (d.jc Z) (d.x Z) (hS Z) (h0 Z) (hx Z) (hd.trdeg Z)
      (Θ Z) (hΘ Z) ev honS τ σ hσ hτ hc k g g.2 ?_)
    rw [← hfr, hx0, zero_mul]
  refine GlobalTheory.length_quotient_le_of_order_bound (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (Op X la G.N) (KTf B.KO d.D d.N) (Kp X la G.N) hmax ?_
    ι (fun c => OmS (Ω c) d.D d.N) (fun c w => d.ord c (d.Wres c w) d.wF (hd.a4.choose c)) (fun c => ?_)
    (Fin d.del) (Fin G.del) eD (d.bvecG hd.sel hd.a4.choose) (SectionSheafQuotient X la G.w wF) Q.A0 (tL G la)
    ((LinearMap.pi Ψ').restrictScalars (Op X la G.N)) ?_ ht ?_ (d.AdmissibleOmegaFamiliesAtPrimeOfSection hd.a4.choose la)
    (fun y hy c w hw => hy c w ((plOver_iff d hs la c w).2 hw))
  · intro r
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨a, ha⟩ := hres r
    refine ⟨IsLocalRing.residue _ a, ?_⟩
    rw [IsLocalRing.ResidueField.map_residue, eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact ha
  · obtain ⟨g, hg, hg'⟩ := (GlobalTheory.PlaceRestrict.places_restrict_injective B.KO ι Ω WT A 𝒜 d hd hs la c).2.2.1
      (fun w => d.ord c (d.Wres c w) d.wF (hd.a4.choose c))
    exact ⟨algebraMap (Ω c) _ g, (map_ne_zero _).2 hg, fun w hw => hg' w ((plOver_iff d hs la c w).1 hw)⟩
  · rw [injective_iff_map_eq_zero]
    intro a ha
    have h1 : (coord Q.e a : OsK X la G.w) = 0 := hψi _ fun c => by
      have h2 : Ψ' c a = 0 := congrFun ha c
      rw [hcoord] at h2
      exact (heu c).mul_left_eq_zero.1 h2
    rw [← coord_smul_self hgen a, h1, zero_smul]
  · intro a ha c w hw u hu1 hu0
    have halg : ∀ r : Op X la G.N, ψ c (algebraMap (Op X la G.N) (OsK X la G.w) r) =
        algebraMap (Op X la G.N) (Kp X la G.N) r ⊗ₜ 1 := fun r => by
      rw [IsScalarTower.algebraMap_apply (Op X la G.N) (Kp X la G.N) (OsK X la G.w), AlgHom.commutes]
      rfl
    obtain ⟨ζ, hζ⟩ := hval (u.comap (ψ c).toRingHom) (fun r => by
        show 0 ≤ u (ψ c _)
        rw [halg]; exact hu0 r) (by
        refine pos_of_mem_map f ((ψ c).toRingHom.comp (algebraMap (Op X la G.N) (OsK X la G.w))) u
          (IsLocalRing.maximalIdeal _) (fun r => ?_) (fun r hr => ?_) (hmax ▸ hirr.not_isUnit)
        · show 0 ≤ u (ψ c _)
          rw [halg]; exact hu0 r
        · show 0 < u (ψ c (algebraMap (Op X la G.N) (OsK X la G.w) (f r)))
          rw [halg, ← hφ]
          have : (φ (ReciprocityTheory.ChartRestriction.G.T0.OpToKT d.D d.N la r) ⊗ₜ 1 :
              Kp X la G.N ⊗[KTf B.KO d.D d.N] OmS (Ω c) d.D d.N) =
              1 ⊗ₜ algebraMap (ReciprocityTheory.ChartRestriction.G.T0.Op d.D d.N la) (OmS (Ω c) d.D d.N) r :=
            Algebra.TensorProduct.tmul_one_eq_one_tmul (ReciprocityTheory.ChartRestriction.G.T0.OpToKT d.D d.N la r)
          rw [this, hu1]
          exact (hw.2 r).2.2 hr) (by
        obtain ⟨π, hπ⟩ := hw.1.2
        obtain ⟨x, hx⟩ := hψs c (1 ⊗ₜ π)
        exact ⟨x, by show u (ψ c x) = 1; rw [hx, hu1, hπ]⟩)
    have hζ' : ∀ x, Formalism.MainNotions.Gaps.EtaleWeightGaps.ord (unifO X la G.N) ζ x = u (ψ c x) := hζ
    have hW : ∀ a : Ω c, u (1 ⊗ₜ algebraMap (Ω c) (OmS (Ω c) d.D d.N) a) = d.Wres c w a := fun a => hu1 _
    obtain ⟨Z, v, hv1, hv2⟩ := hpt2 ζ
    obtain ⟨n, hn⟩ := val_unit_int u (hu c)
    have heq := comp_val_eq X G.w Ω gF hsplit hB Z c ⟨_, h0 c⟩ v (d.Wres c w) fun k => by
      obtain ⟨m, hm⟩ := hv1 k
      refine ⟨m + k * n, fun F => ?_⟩
      have h1 := congrArg u (hfr c k ⟨emb X la G.N (X.inc _ F), emb_mem_Vw X la G.N _ F⟩)
      rw [AddValuation.map_mul, AddValuation.map_pow, hn, ← hζ', hm, hΘ, hW] at h1
      rw [← h1, add_assoc, ← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul]
    obtain rfl : Z = c := congrArg Sigma.fst heq
    obtain rfl : v = d.Wres Z w := eq_of_heq (Sigma.mk.inj heq).2
    have he : Ψ' Z Q.e = 1 ⊗ₜ algebraMap (Ω Z) (OmS (Ω Z) d.D d.N) (gF Z (X.inc wF Q.g0) * (ε Z)⁻¹) := by
      rw [hΨ', LocalPointData.e, hres']
      simp only [s, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← map_mul]
    have hg0 : gF Z (X.inc wF Q.g0) ≠ 0 := by
      intro h
      obtain ⟨n', hn'⟩ := val_unit_int u (heu Z)
      rw [he, hW, h, zero_mul, AddValuation.map_zero] at hn'
      exact WithTop.top_ne_coe hn'
    have hball := (mem_ballO_iff Q.c hU hgen a).1 ha ζ
    rw [ordV, hζ', hv2 hg0] at hball
    show 0 ≤ u (Ψ' Z a) + _
    rw [hcoord, AddValuation.map_mul, he, hW, hord, add_assoc, ← add_assoc (d.Wres Z w _),
      ← AddValuation.map_mul, inv_mul_cancel_right₀ (hε Z)]
    exact hball

end Main

section Points

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}
  {ζ : PtsG G la} {y : E.Pt' la}

/- English proof (translation)
Consider the cases of `a with`. Consider the case `top => rfl`. Consider the case `coe m => exact absurd h (EReal.coe_ne_top _)`.
-/
theorem eq_top_of_toE {a : WithTop ℤ} (h : toE a = ⊤) : a = ⊤ := by
  cases a with
  | top => rfl
  | coe m => exact absurd h (EReal.coe_ne_top _)

/- English proof (translation)
Consider the cases of `a with`. Consider the case `top => exact absurd h.symm (EReal.coe_ne_top _)`. Consider the case `coe m`. Establish `h1 : ((m : ℝ) : EReal) = ((n : ℝ) : EReal)` using `h`. Establish `h2 : m = n` using `by exact_mod_cast h1`.

Rewrite using `[h2]`.
-/
theorem eq_coe_of_toE {a : WithTop ℤ} {n : ℤ} (h : toE a = ((n : ℝ) : EReal)) : a = n := by
  cases a with
  | top => exact absurd h.symm (EReal.coe_ne_top _)
  | coe m =>
    have h1 : ((m : ℝ) : EReal) = ((n : ℝ) : EReal) := h
    have h2 : m = n := by exact_mod_cast h1
    rw [h2]

/- English proof (translation)
Apply `eq_top_of_toE` to reduce the goal to its premises. Rewrite using `[h.ord, coe_weightZeroFraction, h.lift_frac, hg, zero_mul, nval_zero]`.
-/
theorem order_eq_top_of_form_vanishes_at_realisation (h : SecPt ζ y) (k : ℕ) (g : ↥(Vw (xplus X E hM) la G.N (addL (wt0 D j) wL k)))
    (hg : h.ev g = 0) : Formalism.MainNotions.Gaps.EtaleWeightGaps.ord (unifO (xplus X E hM) la G.N) ζ
      (toOsK (xplus X E hM) la G.w (fr0 (xplus X E hM) la G.w k g)) = ⊤ := by
  apply eq_top_of_toE
  rw [h.ord, coe_weightZeroFraction, h.lift_frac, hg, zero_mul, nval_zero]

/- English proof (translation)
Establish `hb` using `h.s0.ne_zero`. Apply `eq_coe_of_toE` to reduce the goal to its premises. Rewrite using `[h.ord, coe_weightZeroFraction, h.lift_frac, nval_of_ne (mul_ne_zero hg (pow_ne_zero k (inv_ne_zero hb))), vV_mul hg (pow_ne_zero k (inv_ne_zero hb)), vV_pow' (inv_ne_zero hb), vV_inv' hb, Nat.cast_one, div_one]`.
-/
theorem order_eq_coe_of_form_ne_zero_at_realisation (h : SecPt ζ y) (k : ℕ) (g : ↥(Vw (xplus X E hM) la G.N (addL (wt0 D j) wL k)))
    (hg : h.ev g ≠ 0) : Formalism.MainNotions.Gaps.EtaleWeightGaps.ord (unifO (xplus X E hM) la G.N) ζ
      (toOsK (xplus X E hM) la G.w (fr0 (xplus X E hM) la G.w k g)) =
      ((vV h.T.V (h.ev g) + k * -vV h.T.V (h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0)) : ℤ) : WithTop ℤ) := by
  have hb := h.s0.ne_zero
  apply eq_coe_of_toE
  rw [h.ord, coe_weightZeroFraction, h.lift_frac, nval_of_ne (mul_ne_zero hg (pow_ne_zero k (inv_ne_zero hb))),
    vV_mul hg (pow_ne_zero k (inv_ne_zero hb)), vV_pow' (inv_ne_zero hb), vV_inv' hb, Nat.cast_one, div_one]

/- English proof (translation)
Distinguish the cases in `ha : a = 0`. Rewrite using `[order_eq_top_of_form_vanishes_at_realisation h k g (h0 ha), ha, AddValuation.map_zero, top_add]`. Rewrite using `[order_eq_coe_of_form_ne_zero_at_realisation h k g (h1 ha).1, WithTop.coe_add, (h1 ha).2, WithTop.coe_add, add_assoc]`.
-/
theorem order_at_point_eq_of_values_at_realisation (h : SecPt ζ y) {Ω : Type} [Field Ω] (v : AddValuation Ω (WithTop ℤ)) (k : ℕ)
    (g : ↥(Vw (xplus X E hM) la G.N (addL (wt0 D j) wL k))) (a : Ω) (m : ℤ) (h0 : a = 0 → h.ev g = 0)
    (h1 : a ≠ 0 → h.ev g ≠ 0 ∧ ((vV h.T.V (h.ev g) : ℤ) : WithTop ℤ) = v a + (m : ℤ)) :
    Formalism.MainNotions.Gaps.EtaleWeightGaps.ord (unifO (xplus X E hM) la G.N) ζ
      (toOsK (xplus X E hM) la G.w (fr0 (xplus X E hM) la G.w k g)) =
      v a + ((m + k * -vV h.T.V (h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0)) : ℤ) : WithTop ℤ) := by
  by_cases ha : a = 0
  · rw [order_eq_top_of_form_vanishes_at_realisation h k g (h0 ha), ha, AddValuation.map_zero, top_add]
  · rw [order_eq_coe_of_form_ne_zero_at_realisation h k g (h1 ha).1, WithTop.coe_add, (h1 ha).2, WithTop.coe_add, add_assoc]

end Points

/- English proof (translation)
Establish `h : ∃ r : Ω, (AddMonoidAlgebra.single G a : AddMonoidAlgebra Ω W) = r • AddMonoidAlgebra.single G b` using `⟨a / b, by rw [AddMonoidAlgebra.smul_single', div_mul_cancel₀ _ hb]⟩`. Rewrite using `[ReciprocityTheory.ChartRestriction.G.T0.ratio, dif_pos h]`. Establish `h1` using `h.choose_spec`. Generalize the expression as in `h.choose = r at h1 ⊢`. Rewrite `h1` using `[AddMonoidAlgebra.smul_single']`.

Conclude with `AddMonoidAlgebra.single_right_injective h1`.
-/
theorem ratio_single_mul {Ω W : Type} [Field Ω] (G : W) (a : Ω) {b : Ω} (hb : b ≠ 0) :
    a = ReciprocityTheory.ChartRestriction.G.T0.ratio (Ω := Ω) (AddMonoidAlgebra.single G a : AddMonoidAlgebra Ω W)
      (AddMonoidAlgebra.single G b) * b := by
  have h : ∃ r : Ω, (AddMonoidAlgebra.single G a : AddMonoidAlgebra Ω W) = r • AddMonoidAlgebra.single G b :=
    ⟨a / b, by rw [AddMonoidAlgebra.smul_single', div_mul_cancel₀ _ hb]⟩
  rw [ReciprocityTheory.ChartRestriction.G.T0.ratio, dif_pos h]
  have h1 := h.choose_spec
  generalize h.choose = r at h1 ⊢
  rw [AddMonoidAlgebra.smul_single'] at h1
  exact AddMonoidAlgebra.single_right_injective h1

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Introduce `D T h j hj hG _ ka wL wF G S g0 hH hInj hSplit hBIR y hw hCurve hTie δ hOrd d hd hs eN hD hdo hwL hwF hdw eD hth Gc PH Prw Pet la`. Establish `hT : GenFromTest (T.Q.Xo j) T.Q.c hG` using `fun Z => h.allTest j hj (Om Z) (genFr hG Z)`. Establish `hpt` using `GlobalTheory.T.realisation_values_eq_valuedPoint_orders D T h j hj hG ka wL wF G S g0 hH hInj hSplit hBIR y hw hCurve hTie δ hOrd la`. Establish `hct` using `countQAtSt_holds h j hj hG hT ka wL wF G S g0 la hH`. Establish `hev` using `formsEvR_inc h j hj hG hT`.

Establish `he` using `hd.a4.choose_spec.1`. Use `choose ε hε using fun Z => mem_AG.1 (he Z).1`. Establish `hε0 : ∀ Z, ε Z ≠ 0` using `fun Z h0 => (he Z).2 (by rw [hε, h0, AddMonoidAlgebra.single_zero])`. Establish `h0 : ∀ Z, evC hG Z (G.w (eN (d.jc Z))).1 ≠ 0` using `fun Z h0 => hd.w_base Z (by`. Rewrite using `[hdw, valC, h0, AddMonoidAlgebra.single_zero])`.

Use `ila_le (B := recB h.toLawsCore) (X := recPlus h j hj) G la (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0) (fun Z => formsEvR j hG hT Z) d hd hs eN eD hD (fun u F hF => hInj u F fun Z => (hev Z u F).symm.trans (hF Z)) (fun Z u g = …` and prove the remaining obligations. Take `⟨g', h1, h2⟩` from `hSplit Z u g`. Conclude with `⟨g', (hev Z u g').trans (h1.trans (hev Z u g).symm), fun Z' hZ' => (hev Z' u g').trans (h2 Z' hZ')⟩`. Use `(hev Z _ _).trans (Eq.trans ?_ (congrArg (d.x Z k * ·) (hev Z _ _).symm))` and prove the remaining obligations. Rewrite using `[ReciprocityTheory.ChartRestriction.G.T0.Data.x, hdw, hdw]`.

Conclude with `ratio_single_mul _ _ (h0 Z)`. Use `(hev Z _ _).trans ?_` and prove the remaining obligations. Rewrite using `[hth, hε, hwF]`. Conclude with `ratio_single_mul _ _ (hε0 Z)`. Rewrite using `[hdo, hε]`.

Conclude with `ordC_single _ _ _ (hε0 Z)`. Take `⟨Z, v, -, -, hv⟩` from `hpt ζ`. Use `⟨Z, v, fun k => ⟨_, fun F => order_at_point_eq_of_values_at_realisation (hw la ζ).toSecPt v k _ _ (frW (δ Z v) (wtZ (wtA (addL (wt0 D j) wL k)) (addL (wt0 D j) wL k).n)) (fun ha => (hv _ F).1 ((hev Z _ F).symm.trans ha)) fun ha => ?_⟩, fun ha => ?_⟩` and prove the remaining obligations. Establish `ha'` using `(hev Z _ F) ▸ ha`. Use `⟨((hv _ F).2 ha').1, ?_⟩` and prove the remaining obligations.

Use `(congrArg (fun n : ℤ => (n : WithTop ℤ)) ((hv _ F).2 ha').2).trans ?_` and prove the remaining obligations. Conclude with `(ordC_single _ _ _ ha').trans (congrArg (fun t => v t + _) (hev Z _ F).symm)`. Establish `ha'` using `(hev Z wF g0) ▸ ha`. Use `(congrArg (fun n : ℤ => (n : WithTop ℤ)) ((hv wF g0).2 ha').2).trans ?_` and prove the remaining obligations. Rewrite using `[hwF]`.

Conclude with `(ordC_single _ _ _ ha').trans (congrArg (fun t => v t + _) (hev Z wF g0).symm)`.
-/
theorem ilaTie_of_curveHyp : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → ∀ (y : ∀ la, PtsG G la → (extAll h j hj).Pt' la) (hw : ∀ la ζ, FromW (E := extAll h j hj) (hM := intAtExt_extAll h j hj) ζ (y la ζ)), (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InCurve) → (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InTie S) → ∀ (δ : ∀ Z : Comp (T.Q.Xo j) T.Q.c, AddValuation (Om Z) (WithTop ℤ) → Ix (T.Q.Dw j) → ℤ), OrdTie hG δ (trivialClassCondition (T.Q.Xo j) T.Q.c) (fun _ => Unit) (fun _ _ _ _ _ => True) → ∀ (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z)) (hd : d.AxH (fun Z => AG Z)) (hs : d.S1) (eN : Fin (d.N + 1) ≃ Fin G.N), d.D = WeightFamilies.dimY D j → (∀ Z v, d.ord Z v = ordC (δ Z v) v) → d.wL = wtZ (wtA wL) wL.n → d.wF = wtZ (wtA wF) wF.n → (∀ k, d.w k = valC hG (wtA wL) wL.n (G.w (eN k)).1) → ∀ (eD : Fin d.del ≃ Fin G.del), (∀ k, d.thp (hd.sel k) = valC hG (wtA wF) wF.n (G.th' (eD k)).1) → ∀ (Gc PH Prw Pet : ℝ), IlaTie (B := (recB h.toLawsCore)) d hd hs G (fun la => (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0)) Gc PH Prw Pet := by
  intro D T h j hj hG _ ka wL wF G S g0 hH hInj hSplit hBIR y hw hCurve hTie δ hOrd d hd hs eN hD hdo hwL hwF hdw
    eD hth Gc PH Prw Pet la
  have hT : GenFromTest (T.Q.Xo j) T.Q.c hG := fun Z => h.allTest j hj (Om Z) (genFr hG Z)
  have hpt := GlobalTheory.T.realisation_values_eq_valuedPoint_orders D T h j hj hG ka wL wF G S g0 hH hInj hSplit hBIR y hw hCurve hTie δ hOrd la
  have hct := countQAtSt_holds h j hj hG hT ka wL wF G S g0 la hH
  have hev := formsEvR_inc h j hj hG hT
  have he := hd.a4.choose_spec.1
  choose ε hε using fun Z => mem_AG.1 (he Z).1
  have hε0 : ∀ Z, ε Z ≠ 0 := fun Z h0 => (he Z).2 (by rw [hε, h0, AddMonoidAlgebra.single_zero])
  have h0 : ∀ Z, evC hG Z (G.w (eN (d.jc Z))).1 ≠ 0 := fun Z h0 => hd.w_base Z (by
    rw [hdw, valC, h0, AddMonoidAlgebra.single_zero])
  refine ila_le (B := recB h.toLawsCore) (X := recPlus h j hj) G la
    (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0)
    (fun Z => formsEvR j hG hT Z) d hd hs eN eD hD
    (fun u F hF => hInj u F fun Z => (hev Z u F).symm.trans (hF Z))
    (fun Z u g => ?_) (birAt_of h j hj hG hT G hBIR) hct
    (fun Z => (hev Z _ _).symm ▸ h0 Z) (fun Z k => ?_) ε hε0 (fun k Z => ?_)
    (fun Z v => frW (δ Z v) d.wF) (fun Z v => ?_) (hCurve la)
    (fun ζ => ⟨(hw la ζ).T.Fr, inferInstance, (hw la ζ).ev, (hw la ζ).s0, (hw la ζ).onS,
      order_eq_top_of_form_vanishes_at_realisation (hw la ζ).toSecPt⟩) (fun ζ => ?_)
  · obtain ⟨g', h1, h2⟩ := hSplit Z u g
    exact ⟨g', (hev Z u g').trans (h1.trans (hev Z u g).symm), fun Z' hZ' => (hev Z' u g').trans (h2 Z' hZ')⟩
  · refine (hev Z _ _).trans (Eq.trans ?_ (congrArg (d.x Z k * ·) (hev Z _ _).symm))
    rw [ReciprocityTheory.ChartRestriction.G.T0.Data.x, hdw, hdw]
    exact ratio_single_mul _ _ (h0 Z)
  · refine (hev Z _ _).trans ?_
    rw [hth, hε, hwF]
    exact ratio_single_mul _ _ (hε0 Z)
  · rw [hdo, hε]
    exact ordC_single _ _ _ (hε0 Z)
  · obtain ⟨Z, v, -, -, hv⟩ := hpt ζ
    refine ⟨Z, v, fun k => ⟨_, fun F => order_at_point_eq_of_values_at_realisation (hw la ζ).toSecPt v k _ _
      (frW (δ Z v) (wtZ (wtA (addL (wt0 D j) wL k)) (addL (wt0 D j) wL k).n))
      (fun ha => (hv _ F).1 ((hev Z _ F).symm.trans ha)) fun ha => ?_⟩, fun ha => ?_⟩
    · have ha' := (hev Z _ F) ▸ ha
      refine ⟨((hv _ F).2 ha').1, ?_⟩
      refine (congrArg (fun n : ℤ => (n : WithTop ℤ)) ((hv _ F).2 ha').2).trans ?_
      exact (ordC_single _ _ _ ha').trans (congrArg (fun t => v t + _) (hev Z _ F).symm)
    · have ha' := (hev Z wF g0) ▸ ha
      refine (congrArg (fun n : ℤ => (n : WithTop ℤ)) ((hv wF g0).2 ha').2).trans ?_
      rw [hwF]
      exact (ordC_single _ _ _ ha').trans (congrArg (fun t => v t + _) (hev Z wF g0).symm)

end GlobalTheory.LengthTie
