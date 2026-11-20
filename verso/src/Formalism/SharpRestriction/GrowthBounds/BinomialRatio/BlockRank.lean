import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CountDefs
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SegLow
import Formalism.SharpRestriction.GrowthBounds.CountingStatementReduction
import Formalism.SharpRestriction.GrowthBounds.ProjectionOfIsotypicDecomposition

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

section

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {N r : ℕ} [NeZero r] (D : BlockData N)

def pre (x : (Fin D.T.t → ℕ) × ℕ) : MvPolynomial (BVar N r D.T.t) (KK O) :=
  (∏ i, D.Ehat O (r := r) i ^ x.1 i) * D.Eplus O (r := r) ^ x.2 *
      (∏ i, X (scalZ N r D.T.t (Fin.castSucc i)) ^ D.T.z i) * X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus

def xiExp (N r t : ℕ) (β : Fin r → ℕ) : BVar N r t →₀ ℕ := ∑ c, Finsupp.single (xiVar N r t c) (β c)

def xiMon (K : Type) [CommRing K] (N r t : ℕ) (β : Fin r → ℕ) : MvPolynomial (BVar N r t) K :=
  monomial (xiExp N r t β) 1

/- English proof (translation)
Introduce `c c' h`. Simplify `h` using `[xiVar]`.
-/
theorem xiVar_inj (N r t : ℕ) : Function.Injective (xiVar N r t) := by
  intro c c' h
  simpa [xiVar] using h

/- English proof (translation)
Simplify using `only [xiExp, Finsupp.finset_sum_apply, Finsupp.single_apply, (xiVar_inj N r t).eq_iff]`. Simplify using the standard rewrite rules.
-/
theorem xiExp_xi (N r t : ℕ) (β : Fin r → ℕ) (c : Fin r) : xiExp N r t β (xiVar N r t c) = β c := by
  classical
  simp only [xiExp, Finsupp.finset_sum_apply, Finsupp.single_apply, (xiVar_inj N r t).eq_iff]
  simp

/- English proof (translation)
Simplify using `only [xiExp, Finsupp.finset_sum_apply, Finsupp.single_apply]`. Conclude with `Finset.sum_eq_zero fun c _ => if_neg fun h => hv c h.symm`.
-/
theorem xiExp_other (N r t : ℕ) (β : Fin r → ℕ) (v : BVar N r t) (hv : ∀ c, v ≠ xiVar N r t c) :
    xiExp N r t β v = 0 := by
  classical
  simp only [xiExp, Finsupp.finset_sum_apply, Finsupp.single_apply]
  exact Finset.sum_eq_zero fun c _ => if_neg fun h => hv c h.symm

/- English proof (translation)
Use extensionality with `v`. Distinguish the cases in `hv : ∃ c, v = xiVar N r t c`. Take `⟨c, rfl⟩` from `hv`. Rewrite using `[xiExp_xi]`. Rewrite using `[xiExp_other _ _ _ _ _ (fun c hc => hv ⟨c, hc⟩)]`.

Assume the negation of the conclusion as `h0`. Conclude with `hv (h v (Finsupp.mem_support_iff.2 h0))`.
-/
theorem eq_xiExp (N r t : ℕ) (μ : BVar N r t →₀ ℕ) (h : ∀ v ∈ μ.support, ∃ c, v = xiVar N r t c) :
    μ = xiExp N r t fun c => μ (xiVar N r t c) := by
  ext v
  by_cases hv : ∃ c, v = xiVar N r t c
  · obtain ⟨c, rfl⟩ := hv
    rw [xiExp_xi]
  · rw [xiExp_other _ _ _ _ _ (fun c hc => hv ⟨c, hc⟩)]
    by_contra h0
    exact hv (h v (Finsupp.mem_support_iff.2 h0))

def ell (x : (Fin D.T.t → ℕ) × ℕ) (β : Fin r → ℕ) :
    MvPolynomial (Fin N × Fin r) (KK O) →ₗ[KK O] MvPolynomial (BVar N r D.T.t) (KK O) :=
  LinearMap.mulLeft (KK O) (pre (O := O) D x) ∘ₗ LinearMap.mulRight (KK O) (xiMon (KK O) N r D.T.t β) ∘ₗ
    (rename (chainEmb N r D.T.t)).toLinearMap

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ell_apply (x : (Fin D.T.t → ℕ) × ℕ) (β : Fin r → ℕ) (y : MvPolynomial (Fin N × Fin r) (KK O)) :
    ell D x β y = pre (O := O) D x * (rename (chainEmb N r D.T.t) y * xiMon (KK O) N r D.T.t β) := rfl

open Classical in

def Lv : Finset ((Fin D.T.t → ℕ) × ℕ) :=
  ((Fintype.piFinset fun i => Finset.range (D.LL.deg (D.letterAt (D.T.pos i)) + 1)) ×ˢ
    Finset.range (D.B + 1)).filter fun x => D.LevelOK x.1 x.2

/- English proof (translation)
Simplify using `only [Lv, Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_range]`. Prove the components needed by the constructor for the conclusion. Conclude with `fun h => h.2`. Introduce `h`. Conclude with `⟨⟨fun i => Nat.lt_succ_of_le (h.1 i).1, Nat.lt_succ_of_le (le_trans h.2 (min_le_right _ _))⟩, h⟩`.
-/
theorem mem_Lv (x : (Fin D.T.t → ℕ) × ℕ) : x ∈ Lv D ↔ D.LevelOK x.1 x.2 := by
  classical
  simp only [Lv, Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨⟨fun i => Nat.lt_succ_of_le (h.1 i).1, Nat.lt_succ_of_le (le_trans h.2 (min_le_right _ _))⟩, h⟩

def IF : Finset (Σ _ : (Fin D.T.t → ℕ) × ℕ, Fin r → ℕ) :=
  (Lv D).sigma fun x => Finset.Nat.antidiagonalTuple r (D.B - x.2)

abbrev Yx (i : Σ _ : (Fin D.T.t → ℕ) × ℕ, Fin r → ℕ) :
    Submodule (KK O) (MvPolynomial (Fin N × Fin r) (KK O)) :=
  Yjt (KK O) (r := r) (D.lettersAt i.1.1 i.1.2) D.T.J D.T.thr

instance (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) :
    FiniteDimensional (KK O) (Yjt (KK O) (r := r) LL J M) :=
  haveI : FiniteDimensional (KK O) (chPol (KK O) r LL) := Formalism.MainNotions.G.Joints.isoPol_finDim (K := KK O) (r := r) LL.deg
  Submodule.finiteDimensional_of_le (inf_le_left : Yjt (KK O) (r := r) LL J M ≤ chPol (KK O) r LL)

def Ltot : (∀ i : ↥(IF (r := r) D), ↥(Yx (O := O) D i.1)) →ₗ[KK O] MvPolynomial (BVar N r D.T.t) (KK O) :=
  LinearMap.lsum (KK O) _ (KK O) fun i => ell D i.1.1 i.1.2 ∘ₗ (Yx (O := O) D i.1).subtype

/- English proof (translation)
Simplify using `[Ltot]`.
-/
theorem Ltot_apply (v : ∀ i : ↥(IF (r := r) D), ↥(Yx (O := O) D i.1)) :
    Ltot D v = ∑ i, ell D i.1.1 i.1.2 (v i : MvPolynomial (Fin N × Fin r) (KK O)) := by
  simp [Ltot]

/- English proof (translation)
Use `⟨LinearMap.single (KK O) (fun j : ↥(IF (r := r) D) => ↥(Yx (O := O) D j.1)) i ⟨y, hy⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Ltot_apply, Finset.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Simplify using `[LinearMap.single_apply, Pi.single_eq_of_ne hj]`.

Simplify using the standard rewrite rules.
-/
theorem ell_mem_range (i : ↥(IF (r := r) D)) (y : MvPolynomial (Fin N × Fin r) (KK O)) (hy : y ∈ Yx (O := O) D i.1) :
    ell D i.1.1 i.1.2 y ∈ LinearMap.range (Ltot (O := O) D) := by
  classical
  refine ⟨LinearMap.single (KK O) (fun j : ↥(IF (r := r) D) => ↥(Yx (O := O) D j.1)) i ⟨y, hy⟩, ?_⟩
  rw [Ltot_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [LinearMap.single_apply, Pi.single_eq_of_ne hj]
  · simp

/- English proof (translation)
Proceed by induction on `k generalizing n with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[List.Nat.antidiagonalTuple, List.length_flatMap]`. Simplify using `only [List.length_map, ih, List.Nat.antidiagonal, List.map_map, Function.comp_def]`.

Establish `e : ((List.range (n + 1)).map fun i => (n - i + k).choose k).sum = ∑ j ∈ Finset.range (n + 1), (n - j + k).choose k` using `rfl`. Rewrite using `[e]`. Establish `h` using `Finset.sum_range_reflect (fun j => (j + k).choose k) (n + 1)`. Simplify using `only [add_tsub_cancel_right] at h`. Rewrite using `[h, Nat.sum_range_add_choose]`.

Put the polynomial expressions in normal form.
-/
private theorem list_antidiagonal_tuple_length_eq_choose (k n : ℕ) :
    (List.Nat.antidiagonalTuple (k + 1) n).length = (n + k).choose k := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [List.Nat.antidiagonalTuple, List.length_flatMap]
    simp only [List.length_map, ih, List.Nat.antidiagonal, List.map_map, Function.comp_def]
    have e : ((List.range (n + 1)).map fun i => (n - i + k).choose k).sum =
        ∑ j ∈ Finset.range (n + 1), (n - j + k).choose k := rfl
    rw [e]
    have h := Finset.sum_range_reflect (fun j => (j + k).choose k) (n + 1)
    simp only [add_tsub_cancel_right] at h
    rw [h, Nat.sum_range_add_choose]
    ring_nf

/- English proof (translation)
Take `⟨k, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hr`. Use `show (List.Nat.antidiagonalTuple (k + 1) b).length = _`. Rewrite using `[list_antidiagonal_tuple_length_eq_choose, sdXi]`. Simplify using the standard rewrite rules.
-/
theorem card_xi (r b : ℕ) (hr : r ≠ 0) : (Finset.Nat.antidiagonalTuple r b).card = sdXi r b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
  show (List.Nat.antidiagonalTuple (k + 1) b).length = _
  rw [list_antidiagonal_tuple_length_eq_choose, sdXi]
  simp

/- English proof (translation)
Rewrite using `[Module.finrank_pi_fintype]`. Rewrite using `[Finset.sum_coe_sort (IF (r := r) D) (fun i => Module.finrank (KK O) (Yx (O := O) D i))]`. Unfold `IF`. Rewrite using `[Finset.sum_sigma]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `∑ _s ∈ Finset.Nat.antidiagonalTuple r (D.B - x.2), Module.finrank (KK O) (Yjt (KK O) (r := r) (D.lettersAt x.1 x.2) D.T.J D.T.thr) = _`. Rewrite using `[Finset.sum_const, smul_eq_mul, mul_comm, card_xi _ _ (NeZero.ne r)]`.
-/
theorem finrank_dom : Module.finrank (KK O) (∀ i : ↥(IF (r := r) D), ↥(Yx (O := O) D i.1)) =
    ∑ x ∈ Lv D, Module.finrank (KK O) (Yjt (KK O) (r := r) (D.lettersAt x.1 x.2) D.T.J D.T.thr) *
      sdXi r (D.B - x.2) := by
  rw [Module.finrank_pi_fintype]
  rw [Finset.sum_coe_sort (IF (r := r) D) (fun i => Module.finrank (KK O) (Yx (O := O) D i))]
  unfold IF
  rw [Finset.sum_sigma]
  refine Finset.sum_congr rfl fun x _ => ?_
  change ∑ _s ∈ Finset.Nat.antidiagonalTuple r (D.B - x.2),
    Module.finrank (KK O) (Yjt (KK O) (r := r) (D.lettersAt x.1 x.2) D.T.J D.T.thr) = _
  rw [Finset.sum_const, smul_eq_mul, mul_comm, card_xi _ _ (NeZero.ne r)]

/- English proof (translation)
Rewrite using `[XiPolZ, Submodule.mem_inf, Submodule.restrictScalars_mem]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[MvPolynomial.mem_restrictSupport_iff]`. Introduce `m hm`. Establish `hm' : m = xiExp N r D.T.t β` using `Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)`.

Substitute `hm'` using the available equality. Use `⟨fun v hv => ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne push_neg at hne`. Conclude with `(Finsupp.mem_support_iff.mp hv) (xiExp_other N r D.T.t β v hne)`. Simplify using `only [xiExp_xi, hβ]`.

Rewrite using `[GLWeightTheory.mem_integral_poly_iff_coeff]`. Introduce `m`. Rewrite using `[xiMon, MvPolynomial.coeff_monomial]`. Use `split_ifs`. Conclude with `⟨1, by simp⟩`.

Conclude with `⟨0, by simp⟩`.
-/
theorem xiMon_mem (b : ℕ) (β : Fin r → ℕ) (hβ : ∑ c, β c = b) : xiMon (KK O) N r D.T.t β ∈ XiPolZ O N r D.T.t b := by
  rw [XiPolZ, Submodule.mem_inf, Submodule.restrictScalars_mem]
  constructor
  · rw [MvPolynomial.mem_restrictSupport_iff]
    intro m hm
    have hm' : m = xiExp N r D.T.t β := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)
    subst hm'
    refine ⟨fun v hv => ?_, ?_⟩
    · by_contra hne
      push_neg at hne
      exact (Finsupp.mem_support_iff.mp hv) (xiExp_other N r D.T.t β v hne)
    · simp only [xiExp_xi, hβ]
  · rw [GLWeightTheory.mem_integral_poly_iff_coeff]
    intro m
    classical
    rw [xiMon, MvPolynomial.coeff_monomial]
    split_ifs
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩

/- English proof (translation)
Take `⟨y, hy, g, hg, rfl⟩` from `hz`. Establish `hyK : y ∈ Yjt (KK O) (r` using `r) (D.lettersAt j jp) D.T.J D.T.thr := (Submodule.mem_inf.mp hy).1`. Establish `hgS` using `(Submodule.mem_inf.mp hg).1`. Rewrite `hgS` using `[Submodule.restrictScalars_mem, MvPolynomial.mem_restrictSupport_iff]`. Rewrite using `[g.as_sum, Finset.mul_sum]`.

Use `Submodule.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Take `⟨hsupp, hsum⟩` from `hgS hm`. Establish `hmono : monomial m (coeff m g) = coeff m g • xiMon (KK O) N r D.T.t (fun c => m (xiVar N r D.T.t c))`. Rewrite using `[xiMon, ← eq_xiExp N r D.T.t m hsupp, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[hmono, mul_smul_comm]`.

Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Establish `hi : (⟨(j, jp), fun c => m (xiVar N r D.T.t c)⟩ : Σ _ : (Fin D.T.t → ℕ) × ℕ, Fin r → ℕ) ∈ IF (r` using `r) D := by`. Rewrite using `[IF, Finset.mem_sigma, mem_Lv, Finset.Nat.mem_antidiagonalTuple]`. Conclude with `⟨hlev, hsum⟩`. Establish `h2` using `ell_mem_range D ⟨_, hi⟩ y hyK`.

Rewrite `h2` using `[ell_apply]`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [pre]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem mem_gens_span_le_range_of_levelOK (j : Fin D.T.t → ℕ) (jp : ℕ) (hlev : D.LevelOK j jp)
    (z : MvPolynomial (BVar N r D.T.t) (KK O)) (hz : z ∈ BlockData.gens O D (r := r) j jp) :
    z ∈ LinearMap.range (Ltot (O := O) D) := by
  classical
  obtain ⟨y, hy, g, hg, rfl⟩ := hz
  have hyK : y ∈ Yjt (KK O) (r := r) (D.lettersAt j jp) D.T.J D.T.thr := (Submodule.mem_inf.mp hy).1
  have hgS := (Submodule.mem_inf.mp hg).1
  rw [Submodule.restrictScalars_mem, MvPolynomial.mem_restrictSupport_iff] at hgS
  rw [g.as_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  obtain ⟨hsupp, hsum⟩ := hgS hm
  have hmono : monomial m (coeff m g) =
      coeff m g • xiMon (KK O) N r D.T.t (fun c => m (xiVar N r D.T.t c)) := by
    rw [xiMon, ← eq_xiExp N r D.T.t m hsupp, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hmono, mul_smul_comm]
  refine Submodule.smul_mem _ _ ?_
  have hi : (⟨(j, jp), fun c => m (xiVar N r D.T.t c)⟩ : Σ _ : (Fin D.T.t → ℕ) × ℕ, Fin r → ℕ) ∈
      IF (r := r) D := by
    rw [IF, Finset.mem_sigma, mem_Lv, Finset.Nat.mem_antidiagonalTuple]
    exact ⟨hlev, hsum⟩
  have h2 := ell_mem_range D ⟨_, hi⟩ y hyK
  rw [ell_apply] at h2
  convert h2 using 1
  simp only [pre]
  ring

/- English proof (translation)
Rewrite using `[Submodule.span_le]`. Introduce `x hx`. Establish `key : D.SSZ O (r` using `r) ≤ (LinearMap.range (Ltot (O := O) D)).restrictScalars O := by`. Unfold `BlockData.SSZ`. Rewrite using `[Submodule.span_le]`.

Introduce `z hz`. Simplify using `only [Set.mem_iUnion] at hz`. Take `⟨j, jp, hlev, hz⟩` from `hz`. Conclude with `mem_gens_span_le_range_of_levelOK D j jp hlev z hz`. Conclude with `key hx`.
-/
theorem span_le_range : Submodule.span (KK O) ((D.SSZ O (r := r) :
    Submodule O (MvPolynomial (BVar N r D.T.t) (KK O))) : Set (MvPolynomial (BVar N r D.T.t) (KK O))) ≤
    LinearMap.range (Ltot (O := O) D) := by
  rw [Submodule.span_le]
  intro x hx
  have key : D.SSZ O (r := r) ≤ (LinearMap.range (Ltot (O := O) D)).restrictScalars O := by
    unfold BlockData.SSZ
    rw [Submodule.span_le]
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨j, jp, hlev, hz⟩ := hz
    exact mem_gens_span_le_range_of_levelOK D j jp hlev z hz
  exact key hx

/- English proof (translation)
Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O) y.coeffs`. Establish `ha0 : algebraMap O (KK O) (b : O) ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2`. Establish `hi : i.1 ∈ IF (r` using `r) D := i.2`. Unfold `IF at hi`. Rewrite `hi` using `[Finset.mem_sigma, mem_Lv, Finset.Nat.mem_antidiagonalTuple]`.

Establish `hyK : algebraMap O (KK O) (b : O) • y ∈ Yjt (KK O) (r` using `r) (D.lettersAt i.1.1.1 i.1.1.2) D.T.J D.T.thr := Submodule.smul_mem _ _ hy`. Establish `hyI : algebraMap O (KK O) (b : O) • y ∈ IntPol O (Fin N × Fin r)`. Rewrite using `[GLWeightTheory.mem_integral_poly_iff_coeff]`. Introduce `m`. Distinguish the cases in `hm : m ∈ y.support`.

Take `⟨o, ho⟩` from `hb (coeff m y) (MvPolynomial.coeff_mem_coeffs m (MvPolynomial.mem_support_iff.mp hm))`. Use `⟨o, ?_⟩` and prove the remaining obligations. Rewrite using `[ho, MvPolynomial.coeff_smul, smul_eq_mul, Algebra.smul_def]`. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_smul, MvPolynomial.notMem_support_iff.mp hm, smul_zero, map_zero]`.

Establish `hmem : ell D i.1.1 i.1.2 (algebraMap O (KK O) (b : O) • y) ∈ D.SSZ O (r` using `r) := by`. Apply `Submodule.subset_span` to reduce the goal to its premises. Simplify using `only [Set.mem_iUnion]`. Use `⟨i.1.1.1, i.1.1.2, hi.1, _, Submodule.mem_inf.mpr ⟨hyK, hyI⟩, xiMon (KK O) N r D.T.t i.1.2, xiMon_mem D _ _ hi.2, ?_⟩` and prove the remaining obligations. Rewrite using `[ell_apply]`.

Simplify using `only [pre]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2` using `Submodule.smul_mem (Submodule.span (KK O) ((D.SSZ O (r := r) : Submodule O (MvPolynomial (BVar N r D.T.t) (KK O))) : Set (MvPolynomial (BVar N r D.T.t) (KK O)))) (algebraMap O (KK O) (b : O))⁻¹ (Submodule.subset_span hmem)`. Rewrite `h2` using `[map_smul, inv_smul_smul₀ ha0]`. Then use the resulting hypothesis.
-/
private theorem IF_range_le_span (i : ↥(IF (r := r) D)) (y : MvPolynomial (Fin N × Fin r) (KK O))
    (hy : y ∈ Yx (O := O) D i.1) :
    ell D i.1.1 i.1.2 y ∈ Submodule.span (KK O) ((D.SSZ O (r := r) :
      Submodule O (MvPolynomial (BVar N r D.T.t) (KK O))) : Set (MvPolynomial (BVar N r D.T.t) (KK O))) := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O) y.coeffs
  have ha0 : algebraMap O (KK O) (b : O) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have hi : i.1 ∈ IF (r := r) D := i.2
  unfold IF at hi
  rw [Finset.mem_sigma, mem_Lv, Finset.Nat.mem_antidiagonalTuple] at hi
  have hyK : algebraMap O (KK O) (b : O) • y ∈
      Yjt (KK O) (r := r) (D.lettersAt i.1.1.1 i.1.1.2) D.T.J D.T.thr := Submodule.smul_mem _ _ hy
  have hyI : algebraMap O (KK O) (b : O) • y ∈ IntPol O (Fin N × Fin r) := by
    rw [GLWeightTheory.mem_integral_poly_iff_coeff]
    intro m
    by_cases hm : m ∈ y.support
    · obtain ⟨o, ho⟩ := hb (coeff m y) (MvPolynomial.coeff_mem_coeffs m (MvPolynomial.mem_support_iff.mp hm))
      refine ⟨o, ?_⟩
      rw [ho, MvPolynomial.coeff_smul, smul_eq_mul, Algebra.smul_def]
    · refine ⟨0, ?_⟩
      rw [MvPolynomial.coeff_smul, MvPolynomial.notMem_support_iff.mp hm, smul_zero, map_zero]
  have hmem : ell D i.1.1 i.1.2 (algebraMap O (KK O) (b : O) • y) ∈ D.SSZ O (r := r) := by
    apply Submodule.subset_span
    simp only [Set.mem_iUnion]
    refine ⟨i.1.1.1, i.1.1.2, hi.1, _, Submodule.mem_inf.mpr ⟨hyK, hyI⟩,
      xiMon (KK O) N r D.T.t i.1.2, xiMon_mem D _ _ hi.2, ?_⟩
    rw [ell_apply]
    simp only [pre]
    ring
  have h2 := Submodule.smul_mem (Submodule.span (KK O) ((D.SSZ O (r := r) :
      Submodule O (MvPolynomial (BVar N r D.T.t) (KK O))) : Set (MvPolynomial (BVar N r D.T.t) (KK O))))
    (algebraMap O (KK O) (b : O))⁻¹ (Submodule.subset_span hmem)
  rwa [map_smul, inv_smul_smul₀ ha0] at h2

/- English proof (translation)
Introduce and unpack `_ ⟨v, rfl⟩`. Rewrite using `[Ltot_apply]`. Conclude with `Submodule.sum_mem _ fun i _ => IF_range_le_span D i (v i).1 (v i).2`.
-/
theorem range_le_span : LinearMap.range (Ltot (O := O) D) ≤ Submodule.span (KK O) ((D.SSZ O (r := r) :
    Submodule O (MvPolynomial (BVar N r D.T.t) (KK O))) : Set (MvPolynomial (BVar N r D.T.t) (KK O))) := by
  rintro _ ⟨v, rfl⟩
  rw [Ltot_apply]
  exact Submodule.sum_mem _ fun i _ => IF_range_le_span D i (v i).1 (v i).2

open Classical in
/- English proof (translation)
Rewrite using `[finsum_eq_sum_of_support_subset (s := Lv D)]`. Conclude with `Finset.sum_congr rfl fun x hx => if_pos ((mem_Lv D x).1 hx)`. Introduce `x hx`. Rewrite `hx` using `[Function.mem_support]`. Rewrite using `[Finset.mem_coe, mem_Lv]`.

Assume the negation of the conclusion as `h`. Conclude with `hx (if_neg h)`.
-/
theorem finsum_lv (f : (Fin D.T.t → ℕ) × ℕ → ℕ) :
    (∑ᶠ x : (Fin D.T.t → ℕ) × ℕ, if D.LevelOK x.1 x.2 then f x else 0) = ∑ x ∈ Lv D, f x := by
  rw [finsum_eq_sum_of_support_subset (s := Lv D)]
  · exact Finset.sum_congr rfl fun x hx => if_pos ((mem_Lv D x).1 hx)
  · intro x hx
    rw [Function.mem_support] at hx
    rw [Finset.mem_coe, mem_Lv]
    by_contra h
    exact hx (if_neg h)

/- English proof (translation)
The claim follows from `le_antisymm (span_le_range D) (range_le_span D)`.
-/
theorem span_eq_range : Submodule.span (KK O) ((D.SSZ O (r := r) :
    Submodule O (MvPolynomial (BVar N r D.T.t) (KK O))) : Set (MvPolynomial (BVar N r D.T.t) (KK O))) =
    LinearMap.range (Ltot (O := O) D) := le_antisymm (span_le_range D) (range_le_span D)

end

def RestInj : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N r : ℕ) [NeZero r] (D : BlockData N),
    Function.Injective (Ltot (O := O) (r := r) D)

/- English proof (translation)
Introduce `O _ _ _ N r _ D`. Rewrite using `[finsum_lv, span_eq_range, ← finrank_dom]`. Conclude with `LinearMap.finrank_range_of_inj (h O N r D)`.
-/
theorem blockRankAt_of (h : RestInj) : BlockRankAt := by
  intro O _ _ _ N r _ D
  rw [finsum_lv, span_eq_range, ← finrank_dom]
  exact LinearMap.finrank_range_of_inj (h O N r D)

end Formalism.MainNotions.ColumnSystems.Pf
