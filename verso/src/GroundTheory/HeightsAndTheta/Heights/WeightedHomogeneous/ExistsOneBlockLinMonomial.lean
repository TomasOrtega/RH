import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PointHeightDegreeHypotheses
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.POneBlockStandard
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (IsMultiHomog IsArithVar mCoordIdeal secM MRing MRingOver)

noncomputable section

/- English proof (translation)
Establish `hdeg : ∀ m : (Σ k, ι k) →₀ ℕ, ∑ i, m ⟨(), i⟩ = Finsupp.weight 1 m`. Introduce `m`. Establish `h1 : m.degree = Finsupp.weight 1 m`. Rewrite using `[Finsupp.degree_eq_weight_one]`. Both sides reduce to the same expression.

Rewrite using `[← h1, Finsupp.degree_eq_sum, Fintype.sum_sigma]`. Conclude with `(Fintype.sum_unique (fun u : Unit ↦ ∑ y : ι u, m ⟨u, y⟩)).symm`. Simplify using `only [IsMultiHomog, IsHomogeneous, IsWeightedHomogeneous, mem_support_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h d hd`.

Rewrite using `[← hdeg]`. Conclude with `h d hd ()`. Introduce `h m hm k`. Consider the cases of `k`. Rewrite using `[hdeg]`.

Conclude with `h hm`.
-/
theorem isMultiHomog_unit_iff {R : Type*} [CommRing R] {ι : Unit → Type*} [∀ k, Fintype (ι k)]
    (f : MvPolynomial (Σ k, ι k) R) (N : ℕ) :
    IsMultiHomog (R := R) (ι := ι) f (fun _ ↦ N) ↔ f.IsHomogeneous N := by
  have hdeg : ∀ m : (Σ k, ι k) →₀ ℕ, ∑ i, m ⟨(), i⟩ = Finsupp.weight 1 m := by
    intro m
    have h1 : m.degree = Finsupp.weight 1 m := by
      rw [Finsupp.degree_eq_weight_one]
      rfl
    rw [← h1, Finsupp.degree_eq_sum, Fintype.sum_sigma]
    exact (Fintype.sum_unique (fun u : Unit ↦ ∑ y : ι u, m ⟨u, y⟩)).symm
  simp only [IsMultiHomog, IsHomogeneous, IsWeightedHomogeneous, mem_support_iff]
  constructor
  · intro h d hd
    rw [← hdeg]
    exact h d hd ()
  · intro h m hm k
    cases k
    rw [hdeg]
    exact h hm

/- English proof (translation)
Take `⟨hne, ⟨hprime, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩` from `hP`. Set `E : MRing ι ≃+* MRing ι'` to `(renameEquiv ℤ e).toRingEquiv`. Establish `hQ : P.comap (rename e.symm : MRing ι' →ₐ[ℤ] MRing ι) = P.map E`. Rewrite using `[← Ideal.comap_symm]`. Both sides reduce to the same expression.

Use `⟨hne, ⟨?_, ⟨E '' S, ?_, ?_⟩, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Use `hprime` as an intermediate fact. Conclude with `Ideal.comap_isPrime _ _`. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Take `⟨a, ha⟩` from `hS g hg`.

Establish `ha' : a = fun _ ↦ a ()` using `funext fun k ↦ by cases k; rfl`. Rewrite `ha` using `[ha', isMultiHomog_unit_iff]`. Use `⟨fun _ ↦ a (), ?_⟩` and prove the remaining obligations. Rewrite using `[isMultiHomog_unit_iff]`. Conclude with `ha.rename_isHomogeneous`.

Rewrite using `[hQ, hPS, Ideal.map_span]`. Introduce `k`. Consider the cases of `k`. Take `⟨i, hi⟩` from `hrel ()`. Break down `hp : e ⟨(), i⟩ with ⟨⟨⟩, j⟩` into its components or cases.

Use `⟨j, fun hj ↦ hi ?_⟩` and prove the remaining obligations. Establish `hs : e.symm ⟨(), j⟩ = ⟨(), i⟩` using `(Equiv.symm_apply_eq e).mpr hp.symm`. Rewrite `hj` using `[Ideal.mem_comap, rename_X, hs]`. Conclude with `hj`. Establish `h : Ideal.comap (C : ℤ →+* MRing ι') (P.comap (rename e.symm : MRing ι' →ₐ[ℤ] MRing ι)) = Ideal.comap (C : ℤ →+* MRing ι) P`.

Use extensionality with `x`. Simplify using `only [Ideal.mem_comap, rename_C]`. Unfold `ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal`. Rewrite using `[h]`. Conclude with `hhor`.

Rewrite using `[← hdim]`. Conclude with `(ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv P _ E hQ)).symm`.
-/
theorem isArithVar_comap_rename {ι ι' : Unit → Type*} [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
    (e : (Σ k, ι k) ≃ (Σ k, ι' k)) {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) :
    IsArithVar (P.comap (rename e.symm : MRing ι' →ₐ[ℤ] MRing ι)) d := by
  obtain ⟨hne, ⟨hprime, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  let E : MRing ι ≃+* MRing ι' := (renameEquiv ℤ e).toRingEquiv
  have hQ : P.comap (rename e.symm : MRing ι' →ₐ[ℤ] MRing ι) = P.map E := by
    rw [← Ideal.comap_symm]
    rfl
  refine ⟨hne, ⟨?_, ⟨E '' S, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · have := hprime
    exact Ideal.comap_isPrime _ _
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨a, ha⟩ := hS g hg
    have ha' : a = fun _ ↦ a () := funext fun k ↦ by cases k; rfl
    rw [ha', isMultiHomog_unit_iff] at ha
    refine ⟨fun _ ↦ a (), ?_⟩
    rw [isMultiHomog_unit_iff]
    exact ha.rename_isHomogeneous
  · rw [hQ, hPS, Ideal.map_span]
  · intro k
    cases k
    obtain ⟨i, hi⟩ := hrel ()
    rcases hp : e ⟨(), i⟩ with ⟨⟨⟩, j⟩
    refine ⟨j, fun hj ↦ hi ?_⟩
    have hs : e.symm ⟨(), j⟩ = ⟨(), i⟩ := (Equiv.symm_apply_eq e).mpr hp.symm
    rw [Ideal.mem_comap, rename_X, hs] at hj
    exact hj
  · have h : Ideal.comap (C : ℤ →+* MRing ι') (P.comap (rename e.symm : MRing ι' →ₐ[ℤ] MRing ι)) =
        Ideal.comap (C : ℤ →+* MRing ι) P := by
      ext x
      simp only [Ideal.mem_comap, rename_C]
    unfold ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal
    rw [h]
    exact hhor
  · rw [← hdim]
    exact (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv P _ E hQ)).symm

section Values

variable {K : Type} [Field K] {d : ℕ} (om : Module.Basis (Fin d) ℤ (𝓞 K)) (i : ℕ)

def oneBlockLin : MvPolynomial (Σ _ : Unit, Fin d × Fin (i + 1)) ℤ →+* MvPolynomial (Fin (i + 1)) (𝓞 K) :=
  eval₂Hom (Int.castRingHom _) fun p ↦ C (om p.2.1) * X p.2.2

def affEval : MvPolynomial (Fin (i + 1)) (𝓞 K) →+* FractionRing (MvPolynomial (Fin i) K) :=
  eval₂Hom ((algebraMap K (FractionRing (MvPolynomial (Fin i) K))).comp (algebraMap (𝓞 K) K)) (affGen K i)

/- English proof (translation)
Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C a => simp only [eval₂_C, oneBlockLin, eval₂Hom_C, Int.coe_castRingHom, map_intCast]`. Consider the case `add p q hp hq => simp only [eval₂_add, map_add, hp, hq]`. Consider the case `mul_X p v hp`. Simplify using `only [eval₂_mul, map_mul, hp, eval₂_X]`.

Use `congr 1`. Simplify using `[oneBlockLin, affEval, oneBlockPt]`.
-/
theorem eval₂_oneBlockPt [NumberField K] (g : MvPolynomial (Σ _ : Unit, Fin d × Fin (i + 1)) ℤ) :
    eval₂ (Int.castRingHom _) (oneBlockPt om i) g = affEval i (oneBlockLin om i g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp only [eval₂_C, oneBlockLin, eval₂Hom_C, Int.coe_castRingHom, map_intCast]
  | add p q hp hq => simp only [eval₂_add, map_add, hp, hq]
  | mul_X p v hp =>
    simp only [eval₂_mul, map_mul, hp, eval₂_X]
    congr 1
    simp [oneBlockLin, affEval, oneBlockPt]

/- English proof (translation)
Establish `h : (eval₂ (Int.castRingHom (MvPolynomial (Fin (i + 1)) (𝓞 K))) (fun p ↦ C (om p.2.1) * X p.2.2) g).IsHomogeneous (1 * N)` using `hg.eval₂ _ _ (fun r ↦ ?_) (fun p ↦ ?_)`. Rewrite `h` using `[one_mul]`. Conclude with `h`. Use `show ((r : MvPolynomial (Fin (i + 1)) (𝓞 K))).IsHomogeneous 0`. Rewrite using `[← map_intCast (C : 𝓞 K →+* MvPolynomial (Fin (i + 1)) (𝓞 K)) r]`.

Conclude with `isHomogeneous_C _ _`. Simplify using `using (isHomogeneous_C (Fin (i + 1)) (om p.2.1)).mul (isHomogeneous_X (𝓞 K) p.2.2)`.
-/
theorem oneBlockLin_isHomogeneous {g : MvPolynomial (Σ _ : Unit, Fin d × Fin (i + 1)) ℤ} {N : ℕ}
    (hg : g.IsHomogeneous N) : (oneBlockLin om i g).IsHomogeneous N := by
  have h : (eval₂ (Int.castRingHom (MvPolynomial (Fin (i + 1)) (𝓞 K))) (fun p ↦ C (om p.2.1) * X p.2.2)
      g).IsHomogeneous (1 * N) := hg.eval₂ _ _ (fun r ↦ ?_) (fun p ↦ ?_)
  · rw [one_mul] at h
    exact h
  · show ((r : MvPolynomial (Fin (i + 1)) (𝓞 K))).IsHomogeneous 0
    rw [← map_intCast (C : 𝓞 K →+* MvPolynomial (Fin (i + 1)) (𝓞 K)) r]
    exact isHomogeneous_C _ _
  · simpa using (isHomogeneous_C (Fin (i + 1)) (om p.2.1)).mul (isHomogeneous_X (𝓞 K) p.2.2)

def linForm (c : 𝓞 K) (j : Fin (i + 1)) : MvPolynomial (Σ _ : Unit, Fin d × Fin (i + 1)) ℤ :=
  ∑ a, C (om.repr c a) * X ⟨(), (a, j)⟩

/- English proof (translation)
Use `IsHomogeneous.sum _ _ _ fun a _ ↦ ?_` and prove the remaining obligations. Simplify using `using (isHomogeneous_C _ (om.repr c a)).mul (isHomogeneous_X ℤ (⟨(), (a, j)⟩ : Σ _ : Unit, Fin d × Fin (i + 1)))`.
-/
theorem linForm_isHomogeneous (c : 𝓞 K) (j : Fin (i + 1)) : (linForm om i c j).IsHomogeneous 1 := by
  refine IsHomogeneous.sum _ _ _ fun a _ ↦ ?_
  simpa using (isHomogeneous_C _ (om.repr c a)).mul (isHomogeneous_X ℤ (⟨(), (a, j)⟩ : Σ _ : Unit, Fin d × Fin (i + 1)))

/- English proof (translation)
Use `conv_rhs => rw [← om.sum_repr c]`. Simplify using `only [linForm, oneBlockLin, map_sum, map_mul, eval₂Hom_C, eval₂Hom_X', Int.coe_castRingHom, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun a _ ↦ ?_` and prove the remaining obligations. Rewrite using `[zsmul_eq_mul, map_mul, map_intCast, mul_assoc]`.
-/
theorem oneBlockLin_linForm (c : 𝓞 K) (j : Fin (i + 1)) :
    oneBlockLin om i (linForm om i c j) = C c * X j := by
  conv_rhs => rw [← om.sum_repr c]
  simp only [linForm, oneBlockLin, map_sum, map_mul, eval₂Hom_C, eval₂Hom_X', Int.coe_castRingHom,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [zsmul_eq_mul, map_mul, map_intCast, mul_assoc]

def powForm (β : Fin (i + 1) →₀ ℕ) : MvPolynomial (Σ _ : Unit, Fin d × Fin (i + 1)) ℤ :=
  β.prod fun j n ↦ linForm om i 1 j ^ n

/- English proof (translation)
Establish `h` using `IsHomogeneous.prod β.support (fun j ↦ linForm om i 1 j ^ β j) (fun j ↦ 1 * β j) (fun j _ ↦ (linForm_isHomogeneous om i 1 j).pow (β j))`. Simplify using `only [one_mul] at h`. Conclude with `h`.
-/
theorem powForm_isHomogeneous (β : Fin (i + 1) →₀ ℕ) : (powForm om i β).IsHomogeneous β.degree := by
  have h := IsHomogeneous.prod β.support (fun j ↦ linForm om i 1 j ^ β j) (fun j ↦ 1 * β j)
    (fun j _ ↦ (linForm_isHomogeneous om i 1 j).pow (β j))
  simp only [one_mul] at h
  exact h

/- English proof (translation)
Rewrite using `[powForm, map_finsuppProd]`. Simplify using `only [map_pow, oneBlockLin_linForm, map_one, one_mul]`. Conclude with `prod_X_pow_eq_monomial`.
-/
theorem oneBlockLin_powForm (β : Fin (i + 1) →₀ ℕ) : oneBlockLin om i (powForm om i β) = monomial β 1 := by
  rw [powForm, map_finsuppProd]
  simp only [map_pow, oneBlockLin_linForm, map_one, one_mul]
  exact prod_X_pow_eq_monomial

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, α j ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hα (Finsupp.ext h)`. Establish `hle : Finsupp.single j 1 ≤ α` using `Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hj)`.

Establish `hsplit : α = Finsupp.single j 1 + (α - Finsupp.single j 1)` using `(add_tsub_cancel_of_le hle).symm`. Use `⟨linForm om i c j * powForm om i (α - Finsupp.single j 1), ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `(linForm_isHomogeneous om i c j).mul (powForm_isHomogeneous om i (α - Finsupp.single j 1))`. Use `h using 1` and compare the differences between its conclusion and the goal. Use `conv_lhs => rw [hsplit]`.

Rewrite using `[map_add, Finsupp.degree_single]`. Rewrite using `[map_mul, oneBlockLin_linForm, oneBlockLin_powForm, C_mul_X_eq_monomial, monomial_mul, mul_one, ← hsplit]`.
-/
theorem exists_oneBlockLin_monomial (α : Fin (i + 1) →₀ ℕ) (hα : α ≠ 0) (c : 𝓞 K) :
    ∃ g, g.IsHomogeneous α.degree ∧ oneBlockLin om i g = monomial α c := by
  obtain ⟨j, hj⟩ : ∃ j, α j ≠ 0 := by
    by_contra h
    push Not at h
    exact hα (Finsupp.ext h)
  have hle : Finsupp.single j 1 ≤ α := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hj)
  have hsplit : α = Finsupp.single j 1 + (α - Finsupp.single j 1) := (add_tsub_cancel_of_le hle).symm
  refine ⟨linForm om i c j * powForm om i (α - Finsupp.single j 1), ?_, ?_⟩
  · have h := (linForm_isHomogeneous om i c j).mul (powForm_isHomogeneous om i (α - Finsupp.single j 1))
    convert h using 1
    conv_lhs => rw [hsplit]
    rw [map_add, Finsupp.degree_single]
  · rw [map_mul, oneBlockLin_linForm, oneBlockLin_powForm, C_mul_X_eq_monomial, monomial_mul, mul_one,
      ← hsplit]

/- English proof (translation)
Establish `hev : ∀ F : MvPolynomial (Fin (i + 1)) (𝓞 K), eval₂ ((algebraMap K (FractionRing (MvPolynomial (Fin i) K))).comp (algebraMap (𝓞 K) K)) (affGen K i) F = affEval i F` using `fun _ ↦ rfl`. Simplify using `only [hev]`. Rewrite using `[secM, Submodule.mem_toAddSubgroup]`. Prove the components needed by the constructor for the conclusion. Introduce `hs`.

Proceed by induction on `hs using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨g, hg, rfl⟩` from `hx`. Rewrite `hg` using `[isMultiHomog_unit_iff]`. Use `⟨oneBlockLin om i g, oneBlockLin_isHomogeneous om i hg, ?_⟩` and prove the remaining obligations.

Conclude with `eval₂_oneBlockPt om i g`. Consider the case `zero => exact ⟨0, isHomogeneous_zero _ _ _, (map_zero (affEval i)).symm⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨F, hF, rfl⟩` from `hx`. Take `⟨G, hG, rfl⟩` from `hy`.

Conclude with `⟨F + G, hF.add hG, (map_add (affEval i) F G).symm⟩`. Consider the case `smul n x _ hx`. Take `⟨F, hF, rfl⟩` from `hx`. Use `⟨n • F, ?_, (map_zsmul (affEval i) n F).symm⟩` and prove the remaining obligations. Rewrite using `[zsmul_eq_mul, ← map_intCast (C : 𝓞 K →+* MvPolynomial (Fin (i + 1)) (𝓞 K)) n]`.

Simplify using `using hF.C_mul (n : 𝓞 K)`. Introduce and unpack `⟨F, hF, rfl⟩`. Rewrite using `[F.as_sum, map_sum]`. Use `Submodule.sum_mem _ fun α hα ↦ ?_` and prove the remaining obligations. Establish `hdeg : α.degree = N`.

Establish `h` using `hF (mem_support_iff.mp hα)`. Rewrite using `[← h, Finsupp.degree_eq_weight_one]`. Both sides reduce to the same expression. Establish `hα0 : α ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at hdeg`. Use linear arithmetic over natural numbers and integers. Take `⟨g, hg, hgα⟩` from `exists_oneBlockLin_monomial om i α hα0 (coeff α F)`. Rewrite `hg` using `[hdeg]`. Use `Submodule.subset_span ⟨g, (isMultiHomog_unit_iff g N).mpr hg, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hgα]`. Conclude with `eval₂_oneBlockPt om i g`.
-/
theorem mem_secM_oneBlockPt_iff [NumberField K] (N : ℕ) (hN : 1 ≤ N) (s : FractionRing (MvPolynomial (Fin i) K)) :
    s ∈ secM (oneBlockPt om i) (fun _ ↦ N) ↔
      ∃ F : MvPolynomial (Fin (i + 1)) (𝓞 K), F.IsHomogeneous N ∧
        s = eval₂ ((algebraMap K (FractionRing (MvPolynomial (Fin i) K))).comp
          (algebraMap (𝓞 K) K)) (affGen K i) F := by
  have hev : ∀ F : MvPolynomial (Fin (i + 1)) (𝓞 K),
      eval₂ ((algebraMap K (FractionRing (MvPolynomial (Fin i) K))).comp (algebraMap (𝓞 K) K))
        (affGen K i) F = affEval i F := fun _ ↦ rfl
  simp only [hev]
  rw [secM, Submodule.mem_toAddSubgroup]
  constructor
  · intro hs
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      rw [isMultiHomog_unit_iff] at hg
      refine ⟨oneBlockLin om i g, oneBlockLin_isHomogeneous om i hg, ?_⟩
      exact eval₂_oneBlockPt om i g
    | zero => exact ⟨0, isHomogeneous_zero _ _ _, (map_zero (affEval i)).symm⟩
    | add x y _ _ hx hy =>
      obtain ⟨F, hF, rfl⟩ := hx
      obtain ⟨G, hG, rfl⟩ := hy
      exact ⟨F + G, hF.add hG, (map_add (affEval i) F G).symm⟩
    | smul n x _ hx =>
      obtain ⟨F, hF, rfl⟩ := hx
      refine ⟨n • F, ?_, (map_zsmul (affEval i) n F).symm⟩
      rw [zsmul_eq_mul, ← map_intCast (C : 𝓞 K →+* MvPolynomial (Fin (i + 1)) (𝓞 K)) n]
      simpa using hF.C_mul (n : 𝓞 K)
  · rintro ⟨F, hF, rfl⟩
    rw [F.as_sum, map_sum]
    refine Submodule.sum_mem _ fun α hα ↦ ?_
    have hdeg : α.degree = N := by
      have h := hF (mem_support_iff.mp hα)
      rw [← h, Finsupp.degree_eq_weight_one]
      rfl
    have hα0 : α ≠ 0 := by
      rintro rfl
      simp at hdeg
      omega
    obtain ⟨g, hg, hgα⟩ := exists_oneBlockLin_monomial om i α hα0 (coeff α F)
    rw [hdeg] at hg
    refine Submodule.subset_span ⟨g, (isMultiHomog_unit_iff g N).mpr hg, ?_⟩
    rw [← hgα]
    exact eval₂_oneBlockPt om i g

end Values

def oneBlockReindexEquiv (e r : ℕ) :
    Coord (oneBlockSizes e r) ≃ (Σ _ : Unit, Fin (e + 1) × Fin (r + 1)) where
  toFun := oneBlockReindex e r
  invFun := oneBlockReindexInv e r
  left_inv v := by rcases v with ⟨⟨⟩, q⟩; simp [oneBlockReindex, oneBlockReindexInv]
  right_inv p := by rcases p with ⟨⟨⟩, q⟩; simp [oneBlockReindex, oneBlockReindexInv]

/- English proof (translation)
Introduce `K _ _ d om i`. Use `⟨?_, fun N hN s ↦ mem_secM_oneBlockPt_iff om i N hN s⟩` and prove the remaining obligations. Consider the cases of `d with`. Consider the case `zero => exact ((om.index_nonempty).elim fun x ↦ x.elim0)`. Consider the case `succ e`.

Take `⟨hstd, hideal, -⟩` from `Heights.OneBlockStandard.proof K e i om`. Establish `h` using `(hA K i (oneBlockSize e i) (HermLattice.standard K (i + 1)) (oneBlockForms om) hstd).2.2.1`. Rewrite `h` using `[hideal]`. Rewrite using `[mCoordIdeal_eq_comap om]`. Conclude with `isArithVar_comap_rename (oneBlockReindexEquiv e i) h`.
-/
theorem OneBlockModel.imp (hA : Heights.OneBlockModel.Statement) : OneBlockModel.Statement := by
  intro K _ _ d om i
  refine ⟨?_, fun N hN s ↦ mem_secM_oneBlockPt_iff om i N hN s⟩
  cases d with
  | zero => exact ((om.index_nonempty).elim fun x ↦ x.elim0)
  | succ e =>
    obtain ⟨hstd, hideal, -⟩ := Heights.OneBlockStandard.proof K e i om
    have h := (hA K i (oneBlockSize e i) (HermLattice.standard K (i + 1)) (oneBlockForms om) hstd).2.2.1
    rw [hideal] at h
    rw [mCoordIdeal_eq_comap om]
    exact isArithVar_comap_rename (oneBlockReindexEquiv e i) h

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
