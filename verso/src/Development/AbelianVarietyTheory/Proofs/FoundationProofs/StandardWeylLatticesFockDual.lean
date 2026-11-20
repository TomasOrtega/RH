import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StdWeylLatticesFgAndSpanCoeffSpace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitriMonomialOfLowerTri
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LowerTriOfInterlaced
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FockQWordRowActAdj
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LowerTriIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApplyWordMemDualWeyl

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.StdDual

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `H`. Take `⟨a, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun K).mp hx`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Take `⟨r, hr⟩` from `H (D i) (Submodule.subset_span ⟨i, rfl⟩)`.

Establish `e : B (D i) (∑ j, a j • E j) = a i`. Simplify using `[map_sum, h]`. Rewrite `hr` using `[e]`. Rewrite using `[← hr, algebraMap_smul]`. Conclude with `Submodule.smul_mem _ r (Submodule.subset_span ⟨i, rfl⟩)`.

Introduce `H y hy`. Take `⟨a, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun R).mp H`. Take `⟨b, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun R).mp hy`. Rewrite using `[map_sum]`. Use `sum_mem fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[map_sum, LinearMap.sum_apply]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← algebraMap_smul K (a j), ← algebraMap_smul K (b i), map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, h, smul_eq_mul, smul_eq_mul]`. Use `mul_mem ⟨_, rfl⟩ (mul_mem (hc _ ⟨_, rfl⟩) ?_)` and prove the remaining obligations. Use `split_ifs`.

Conclude with `one_mem _`. Conclude with `zero_mem _`.
-/
theorem dual_span_iff {R K V κ : Type} [CommRing R] [Field K] [Algebra R K] [AddCommGroup V] [Module K V]
    [Module R V] [IsScalarTower R K V] [Fintype κ] [DecidableEq κ] {c : K →+* K}
    (hc : ∀ a ∈ (algebraMap R K).range, c a ∈ (algebraMap R K).range)
    (B : V →ₛₗ[c] V →ₗ[K] K) (D E : κ → V) (h : ∀ i j, B (D i) (E j) = if i = j then 1 else 0)
    (x : V) (hx : x ∈ Submodule.span K (Set.range E)) :
    (∀ y ∈ Submodule.span R (Set.range D), B y x ∈ (algebraMap R K).range) ↔
      x ∈ Submodule.span R (Set.range E) := by
  constructor
  · intro H
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨r, hr⟩ := H (D i) (Submodule.subset_span ⟨i, rfl⟩)
    have e : B (D i) (∑ j, a j • E j) = a i := by
      simp [map_sum, h]
    rw [e] at hr
    rw [← hr, algebraMap_smul]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨i, rfl⟩)
  · intro H y hy
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp H
    obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hy
    rw [map_sum]
    refine sum_mem fun j _ => ?_
    rw [map_sum, LinearMap.sum_apply]
    refine sum_mem fun i _ => ?_
    rw [← algebraMap_smul K (a j), ← algebraMap_smul K (b i), map_smul, LinearMap.map_smulₛₗ,
      LinearMap.smul_apply, h, smul_eq_mul, smul_eq_mul]
    refine mul_mem ⟨_, rfl⟩ (mul_mem (hc _ ⟨_, rfl⟩) ?_)
    split_ifs
    · exact one_mem _
    · exact zero_mem _

/- English proof (translation)
Use `LinearIndependent.restrict_scalars' R (K := K) ?_` and prove the remaining obligations. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `a ha i`. Establish `e : B (D i) (∑ j, a j • E j) = a i * N`. Simplify using `[map_sum, h]`.

Rewrite `e` using `[ha, map_zero]`. Conclude with `(mul_eq_zero.mp e.symm).resolve_right hN`.
-/
theorem linInd_of_dual {R K V κ : Type} [CommRing R] [Field K] [Algebra R K] [FaithfulSMul R K] [AddCommGroup V]
    [Module K V] [Module R V] [IsScalarTower R K V] [Fintype κ] [DecidableEq κ] {c : K →+* K}
    (B : V →ₛₗ[c] V →ₗ[K] K) (D E : κ → V) (N : K) (hN : N ≠ 0)
    (h : ∀ i j, B (D i) (E j) = if i = j then N else 0) : LinearIndependent R E := by
  refine LinearIndependent.restrict_scalars' R (K := K) ?_
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  have e : B (D i) (∑ j, a j • E j) = a i * N := by
    simp [map_sum, h]
  rw [ha, map_zero] at e
  exact (mul_eq_zero.mp e.symm).resolve_right hN

/- English proof (translation)
Establish `key : ∀ S T : Set (MvPolynomial σ ℚ), Submodule.span ℤ S ≤ Submodule.span ℤ T → Submodule.span R (MvPolynomial.map (algebraMap ℚ K) '' S) ≤ Submodule.span R (MvPolynomial.map (algebraMap ℚ K) '' T)`. Introduce `S T h`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Establish `hx'` using `h (Submodule.subset_span hx)`.

Use `clear hx`. Proceed by induction on `hx' using Submodule.span_induction with`. Consider the case `mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`.

Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `add_mem hy hz`. Consider the case `smul a y _ hy => rw [map_zsmul]`. Conclude with `zsmul_mem hy a`. Conclude with `le_antisymm (key S T h.le) (key T S h.ge)`.
-/
theorem span_image_eq {R K σ : Type} [CommRing R] [Field K] [CharZero K] [Algebra R K]
    (S T : Set (MvPolynomial σ ℚ)) (h : Submodule.span ℤ S = Submodule.span ℤ T) :
    Submodule.span R (MvPolynomial.map (algebraMap ℚ K) '' S) =
      Submodule.span R (MvPolynomial.map (algebraMap ℚ K) '' T) := by
  have key : ∀ S T : Set (MvPolynomial σ ℚ), Submodule.span ℤ S ≤ Submodule.span ℤ T →
      Submodule.span R (MvPolynomial.map (algebraMap ℚ K) '' S) ≤
        Submodule.span R (MvPolynomial.map (algebraMap ℚ K) '' T) := by
    intro S T h
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' := h (Submodule.subset_span hx)
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul a y _ hy => rw [map_zsmul]; exact zsmul_mem hy a
  exact le_antisymm (key S T h.le) (key T S h.ge)

def bidSet (R : Type) [CommRing R] (n : ℕ) (ν : Fin n → ℕ) : Set (MvPolynomial (Fin n × Fin n) R) :=
  {f | ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin n),
    Formalism.GradedWeylDivisibility.shapeDeg sz = ν ∧ f = Formalism.GradedWeylDivisibility.bideterminant R sz hsz I}

def wordSet (R : Type) [CommRing R] (n : ℕ) (ν : Fin n → ℕ) : Set (MvPolynomial (Fin n × Fin n) R) :=
  Set.range fun w : List (Fin n × Fin n × ℕ) => Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R le_rfl ν)

/- English proof (translation)
Use extensionality with `f`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨k, sz, hsz, I, h, rfl⟩, rfl⟩`. Conclude with `⟨k, sz, hsz, I, h, fk_map_bidet φ _ _ _⟩`. Introduce and unpack `⟨k, sz, hsz, I, h, rfl⟩`.

Conclude with `⟨_, ⟨k, sz, hsz, I, h, rfl⟩, fk_map_bidet φ _ _ _⟩`.
-/
theorem image_bidSet {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ) (ν : Fin n → ℕ) :
    MvPolynomial.map φ '' bidSet R n ν = bidSet S n ν := by
  ext f
  constructor
  · rintro ⟨_, ⟨k, sz, hsz, I, h, rfl⟩, rfl⟩
    exact ⟨k, sz, hsz, I, h, fk_map_bidet φ _ _ _⟩
  · rintro ⟨k, sz, hsz, I, h, rfl⟩
    exact ⟨_, ⟨k, sz, hsz, I, h, rfl⟩, fk_map_bidet φ _ _ _⟩

/- English proof (translation)
Unfold `wordSet`. Rewrite using `[← Set.range_comp]`. Use `congr 1`. Use function extensionality and compare the values at `w`. Simplify using `only [Function.comp]`.

Rewrite using `[← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]`.
-/
theorem image_wordSet {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ) (ν : Fin n → ℕ) :
    MvPolynomial.map φ '' wordSet R n ν = wordSet S n ν := by
  unfold wordSet
  rw [← Set.range_comp]
  congr 1
  funext w
  simp only [Function.comp]
  rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]

/- English proof (translation)
The claim follows from `Formalism.GradedWeylDivisibility.standardMonomialSpanDomain R n n ν`.
-/
theorem dualWeyl_eq (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (ν : Fin n → ℕ) :
    Formalism.GradedWeylDivisibility.dualWeyl R n n ν = Submodule.span R (bidSet R n ν) :=
  Formalism.GradedWeylDivisibility.standardMonomialSpanDomain R n n ν

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem weyl_eq (R : Type) [CommRing R] (n : ℕ) (ν : Fin n → ℕ) :
    Formalism.GradedWeylDivisibility.weyl R n n le_rfl ν = Submodule.span R (wordSet R n ν) := rfl

/- English proof (translation)
Rewrite using `[dualWeyl_eq, Submodule.map_span, ← image_bidSet (Int.castRingHom ℚ)]`. Both sides reduce to the same expression.
-/
theorem dualWeyl_intQ (n : ℕ) (ν : Fin n → ℕ) :
    (Formalism.GradedWeylDivisibility.dualWeyl ℤ n n ν).map (Formalism.GradedWeylDivisibility.intQ n n) = Submodule.span ℤ (bidSet ℚ n ν) := by
  rw [dualWeyl_eq, Submodule.map_span, ← image_bidSet (Int.castRingHom ℚ)]
  rfl

/- English proof (translation)
Rewrite using `[weyl_eq, Submodule.map_span, ← image_wordSet (Int.castRingHom ℚ)]`. Both sides reduce to the same expression.
-/
theorem weyl_intQ (n : ℕ) (ν : Fin n → ℕ) :
    (Formalism.GradedWeylDivisibility.weyl ℤ n n le_rfl ν).map (Formalism.GradedWeylDivisibility.intQ n n) = Submodule.span ℤ (wordSet ℚ n ν) := by
  rw [weyl_eq, Submodule.map_span, ← image_wordSet (Int.castRingHom ℚ)]
  rfl

/- English proof (translation)
Rewrite using `[dualWeyl_eq, Submodule.map_span, image_bidSet, ← image_bidSet (algebraMap (𝓞 K) K)]`. Both sides reduce to the same expression.
-/
theorem dualWeyl_toK (K : Type) [Field K] [NumberField K] (n : ℕ) (ν : Fin n → ℕ) :
    (Formalism.GradedWeylDivisibility.dualWeyl (𝓞 K) n n ν).map (toK K _) =
      Submodule.span (𝓞 K) (MvPolynomial.map (algebraMap ℚ K) '' bidSet ℚ n ν) := by
  rw [dualWeyl_eq, Submodule.map_span, image_bidSet, ← image_bidSet (algebraMap (𝓞 K) K)]
  rfl

/- English proof (translation)
Rewrite using `[weyl_eq, Submodule.map_span, image_wordSet, ← image_wordSet (algebraMap (𝓞 K) K)]`. Both sides reduce to the same expression.
-/
theorem weyl_toK (K : Type) [Field K] [NumberField K] (n : ℕ) (ν : Fin n → ℕ) :
    (Formalism.GradedWeylDivisibility.weyl (𝓞 K) n n le_rfl ν).map (toK K _) =
      Submodule.span (𝓞 K) (MvPolynomial.map (algebraMap ℚ K) '' wordSet ℚ n ν) := by
  rw [weyl_eq, Submodule.map_span, image_wordSet, ← image_wordSet (algebraMap (𝓞 K) K)]
  rfl

/- English proof (translation)
The claim follows from `GlobalTheory.WeylDuality.weyl_dualities.2 (GlobalTheory.WeylDuality.weyl_dualities.1 GlobalTheory.CoeffWord.coeffWord GlobalTheory.FockHighestWeight.fockQ_hw GlobalTheory.FockAdj.fockQ_word_rowAct_adj.1 GlobalTheory.WeylInt.lowerTriIntegral)`.
-/
theorem weylEqDualNabla : Formalism.GradedWeylDivisibility.WeylEqDualNabla :=
  GlobalTheory.WeylDuality.weyl_dualities.2 (GlobalTheory.WeylDuality.weyl_dualities.1 GlobalTheory.CoeffWord.coeffWord GlobalTheory.FockHighestWeight.fockQ_hw
    GlobalTheory.FockAdj.fockQ_word_rowAct_adj.1 GlobalTheory.WeylInt.lowerTriIntegral)

/- English proof (translation)
Take `⟨bZ, ⟨hli, hsp, -⟩, -⟩` from `Formalism.GradedWeylDivisibility.sSBasis ℤ n n ν`. Use `set N := Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl n) ν) (Formalism.GradedWeylDivisibility.hw ℚ (le_refl n) ν) with hN`. Establish `hN0 : N ≠ 0` using `((Formalism.GradedWeylDivisibility.fockQPos _ _ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl n) ν)).2 (Formalism.GradedWeylDivisibility.hwNe ℚ n n le_rfl _)).ne'`. Use `set b : Formalism.GradedWeylDivisibility.ssIdx n n ν → MvPolynomial (Fin n × Fin n) ℚ := fun i => Formalism.GradedWeylDivisibility.intQ n n (bZ i) with hb`. Establish `hbsp : Submodule.span ℤ (Set.range b) = (Formalism.GradedWeylDivisibility.dualWeyl ℤ n n ν).map (Formalism.GradedWeylDivisibility.intQ n n)`.

Rewrite using `[← hsp, Submodule.map_span, ← Set.range_comp]`. Both sides reduce to the same expression. Establish `hbli : LinearIndependent ℚ b`. Rewrite using `[← LinearIndependent.iff_fractionRing ℤ ℚ]`. Use `hli.map' (Formalism.GradedWeylDivisibility.intQ n n) (LinearMap.ker_eq_bot.mpr ?_)` and prove the remaining obligations.

Conclude with `MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective`. Establish `hbQ : Submodule.span ℚ (Set.range b) = Formalism.GradedWeylDivisibility.dualWeyl ℚ n n ν`. Rewrite using `[dualWeyl_eq, ← Submodule.span_span_of_tower ℤ ℚ (Set.range b), hbsp, dualWeyl_intQ, Submodule.span_span_of_tower]`. Establish `hdet` using `ps_gram_det_ne b hbli`. Use `set Q : Matrix (Formalism.GradedWeylDivisibility.ssIdx n n ν) (Formalism.GradedWeylDivisibility.ssIdx n n ν) ℚ := Matrix.of fun i j => Formalism.GradedWeylDivisibility.fockQ (b i) (b j) with hQ`.

Establish `hQu : IsUnit Q.det` using `isUnit_iff_ne_zero.mpr hdet`. Use `set d : Formalism.GradedWeylDivisibility.ssIdx n n ν → MvPolynomial (Fin n × Fin n) ℚ := fun j => ∑ k, (N * Q⁻¹ k j) • b k with hd`. Establish `hbd : ∀ i j, fockL (b i) (d j) = if i = j then N else 0`. Introduce `i j`. Establish `e` using `congrFun (congrFun (Matrix.mul_nonsing_inv Q hQu) i) j`.

Rewrite `e` using `[Matrix.mul_apply, Matrix.one_apply]`. Establish `e2 : fockL (b i) (d j) = N * ∑ k, Q i k * Q⁻¹ k j`. Simplify using `only [hd, map_sum, map_smul, smul_eq_mul, ps_fockL_rat, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hQ, Matrix.of_apply]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2, e]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hdb : Submodule.span ℚ (Set.range d) = Formalism.GradedWeylDivisibility.dualWeyl ℚ n n ν`. Rewrite using `[← hbQ]`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Establish `e : b i = ∑ j, (N⁻¹ * Q j i) • d j`. Simplify using `only [hd, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Establish `: ∀ k, ∑ j, (N⁻¹ * Q j i * (N * Q⁻¹ k j)) • b k = (if k = i then (1 : ℚ) else 0) • b k`.

Introduce `k`. Establish `e` using `congrFun (congrFun (Matrix.nonsing_inv_mul Q hQu) k) i`. Rewrite `e` using `[Matrix.mul_apply, Matrix.one_apply]`. Rewrite using `[← Finset.sum_smul, ← e]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Simplify using `[this]`. Rewrite using `[e]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`.

Use `⟨b, d, by rw [hbsp, dualWeyl_intQ], ?_, fun i j => by rw [← ps_fockL_rat, hbd]⟩` and prove the remaining obligations. Rewrite using `[← weyl_intQ, weylEqDualNabla n n le_rfl ν hν, ← hbsp]`. Establish `key` using `dual_span_iff (R := ℤ) (K := ℚ) (c := starRingEnd ℚ) (fun a ha => by simpa using ha) (N⁻¹ • fockL (K := ℚ) (σ := Fin n × Fin n)) b d (by`. Introduce `i j`. Simplify using `only [LinearMap.smul_apply, hbd, smul_eq_mul]`.

Use `split_ifs`. Conclude with `inv_mul_cancel₀ hN0`. Conclude with `mul_zero _)`. Establish `tr : ∀ x y : MvPolynomial (Fin n × Fin n) ℚ, (N⁻¹ • fockL (K` using `ℚ) (σ := Fin n × Fin n)) y x ∈ (algebraMap ℤ ℚ).range ↔ ∃ z : ℤ, Formalism.GradedWeylDivisibility.fockQ x y = z * N := by`. Introduce `x y`.

Rewrite using `[LinearMap.smul_apply, LinearMap.smul_apply, ps_fockL_rat, smul_eq_mul, (Formalism.GradedWeylDivisibility.fockQPos _ x y).1]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz⟩`. Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite `hz` using `[eq_intCast]`.

Rewrite using `[hz]`. Clear the denominators using the available nonvanishing facts. Introduce and unpack `⟨z, hz⟩`. Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_intCast, hz]`.

Clear the denominators using the available nonvanishing facts. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `hx' : x ∈ Submodule.span ℚ (Set.range d)` using `Submodule.span_le_restrictScalars ℤ ℚ _ hx`.

Conclude with `⟨hdb ▸ hx', fun y hy => (tr x y).mp ((key x hx').mpr hx y hy)⟩`. Introduce and unpack `⟨hx1, hx2⟩`. Conclude with `(key x (hdb ▸ hx1)).mp fun y hy => (tr x y).mpr (hx2 y hy)`.
-/
theorem exists_dual_bases (n : ℕ) (ν : Fin n → ℕ) (hν : Antitone ν) [Fintype (Formalism.GradedWeylDivisibility.ssIdx n n ν)]
    [DecidableEq (Formalism.GradedWeylDivisibility.ssIdx n n ν)] :
    ∃ b d : Formalism.GradedWeylDivisibility.ssIdx n n ν → MvPolynomial (Fin n × Fin n) ℚ,
      Submodule.span ℤ (Set.range b) = Submodule.span ℤ (bidSet ℚ n ν) ∧
      Submodule.span ℤ (Set.range d) = Submodule.span ℤ (wordSet ℚ n ν) ∧
      ∀ i j, Formalism.GradedWeylDivisibility.fockQ (b i) (d j) =
        if i = j then Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl n) ν) (Formalism.GradedWeylDivisibility.hw ℚ (le_refl n) ν) else 0 := by
  obtain ⟨bZ, ⟨hli, hsp, -⟩, -⟩ := Formalism.GradedWeylDivisibility.sSBasis ℤ n n ν
  set N := Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl n) ν) (Formalism.GradedWeylDivisibility.hw ℚ (le_refl n) ν) with hN
  have hN0 : N ≠ 0 :=
    ((Formalism.GradedWeylDivisibility.fockQPos _ _ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl n) ν)).2 (Formalism.GradedWeylDivisibility.hwNe ℚ n n le_rfl _)).ne'
  set b : Formalism.GradedWeylDivisibility.ssIdx n n ν → MvPolynomial (Fin n × Fin n) ℚ := fun i => Formalism.GradedWeylDivisibility.intQ n n (bZ i) with hb
  have hbsp : Submodule.span ℤ (Set.range b) = (Formalism.GradedWeylDivisibility.dualWeyl ℤ n n ν).map (Formalism.GradedWeylDivisibility.intQ n n) := by
    rw [← hsp, Submodule.map_span, ← Set.range_comp]
    rfl
  have hbli : LinearIndependent ℚ b := by
    rw [← LinearIndependent.iff_fractionRing ℤ ℚ]
    refine hli.map' (Formalism.GradedWeylDivisibility.intQ n n) (LinearMap.ker_eq_bot.mpr ?_)
    exact MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  have hbQ : Submodule.span ℚ (Set.range b) = Formalism.GradedWeylDivisibility.dualWeyl ℚ n n ν := by
    rw [dualWeyl_eq, ← Submodule.span_span_of_tower ℤ ℚ (Set.range b), hbsp, dualWeyl_intQ,
      Submodule.span_span_of_tower]
  have hdet := ps_gram_det_ne b hbli
  set Q : Matrix (Formalism.GradedWeylDivisibility.ssIdx n n ν) (Formalism.GradedWeylDivisibility.ssIdx n n ν) ℚ :=
    Matrix.of fun i j => Formalism.GradedWeylDivisibility.fockQ (b i) (b j) with hQ
  have hQu : IsUnit Q.det := isUnit_iff_ne_zero.mpr hdet
  set d : Formalism.GradedWeylDivisibility.ssIdx n n ν → MvPolynomial (Fin n × Fin n) ℚ := fun j => ∑ k, (N * Q⁻¹ k j) • b k with hd
  have hbd : ∀ i j, fockL (b i) (d j) = if i = j then N else 0 := by
    intro i j
    have e := congrFun (congrFun (Matrix.mul_nonsing_inv Q hQu) i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at e
    have e2 : fockL (b i) (d j) = N * ∑ k, Q i k * Q⁻¹ k j := by
      simp only [hd, map_sum, map_smul, smul_eq_mul, ps_fockL_rat, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hQ, Matrix.of_apply]
      ring
    rw [e2, e]
    split_ifs <;> simp
  have hdb : Submodule.span ℚ (Set.range d) = Formalism.GradedWeylDivisibility.dualWeyl ℚ n n ν := by
    rw [← hbQ]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have e : b i = ∑ j, (N⁻¹ * Q j i) • d j := by
        simp only [hd, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        have : ∀ k, ∑ j, (N⁻¹ * Q j i * (N * Q⁻¹ k j)) • b k = (if k = i then (1 : ℚ) else 0) • b k := by
          intro k
          have e := congrFun (congrFun (Matrix.nonsing_inv_mul Q hQu) k) i
          rw [Matrix.mul_apply, Matrix.one_apply] at e
          rw [← Finset.sum_smul, ← e]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          field_simp
        simp [this]
      rw [e]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  refine ⟨b, d, by rw [hbsp, dualWeyl_intQ], ?_, fun i j => by rw [← ps_fockL_rat, hbd]⟩
  rw [← weyl_intQ, weylEqDualNabla n n le_rfl ν hν, ← hbsp]
  have key := dual_span_iff (R := ℤ) (K := ℚ) (c := starRingEnd ℚ) (fun a ha => by simpa using ha)
    (N⁻¹ • fockL (K := ℚ) (σ := Fin n × Fin n)) b d (by
      intro i j
      simp only [LinearMap.smul_apply, hbd, smul_eq_mul]
      split_ifs
      · exact inv_mul_cancel₀ hN0
      · exact mul_zero _)
  have tr : ∀ x y : MvPolynomial (Fin n × Fin n) ℚ,
      (N⁻¹ • fockL (K := ℚ) (σ := Fin n × Fin n)) y x ∈ (algebraMap ℤ ℚ).range ↔
        ∃ z : ℤ, Formalism.GradedWeylDivisibility.fockQ x y = z * N := by
    intro x y
    rw [LinearMap.smul_apply, LinearMap.smul_apply, ps_fockL_rat, smul_eq_mul, (Formalism.GradedWeylDivisibility.fockQPos _ x y).1]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      rw [eq_intCast] at hz
      rw [hz]
      field_simp
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      rw [eq_intCast, hz]
      field_simp
  ext x
  constructor
  · intro hx
    have hx' : x ∈ Submodule.span ℚ (Set.range d) := Submodule.span_le_restrictScalars ℤ ℚ _ hx
    exact ⟨hdb ▸ hx', fun y hy => (tr x y).mp ((key x hx').mpr hx y hy)⟩
  · rintro ⟨hx1, hx2⟩
    exact (key x (hdb ▸ hx1)).mp fun y hy => (tr x y).mpr (hx2 y hy)

/- English proof (translation)
Introduce `K _ _ _ ι _ n lam x hx`. Use `haveI : ∀ τ, Fintype (Formalism.GradedWeylDivisibility.ssIdx n n (lam τ).natW) := fun τ => (Formalism.GradedWeylDivisibility.sSIdxFinite n n _).fintype`. Use `choose b d hb hd hbd using fun τ => exists_dual_bases n (lam τ).natW (natW_antitone (lam τ))`. Use `set φ := algebraMap ℚ K with hφ`. Establish `hne : ∀ τ, fockS (extremal K n (lam τ)) (extremal K n (lam τ)) ≠ 0`.

Introduce `τ`. Rewrite using `[← map_extremal φ, fockSQ K]`. Conclude with `(map_ne_zero φ).mpr ((Formalism.GradedWeylDivisibility.fockQPos _ _ (extremal ℚ n (lam τ))).2 (Formalism.GradedWeylDivisibility.hwNe ℚ n n le_rfl _)).ne'`. Establish `h1 : ∀ τ i j, fockL (MvPolynomial.map φ (b τ i)) (MvPolynomial.map φ (d τ j)) = if i = j then fockS (extremal K n (lam τ)) (extremal K n (lam τ)) else 0`. Introduce `τ i j`.

Rewrite using `[fockL_apply, ← map_extremal φ, fockSQ K, fockSQ K, hbd]`. Use `split_ifs`. Both sides reduce to the same expression. Conclude with `map_zero _`. Establish `h2 : ∀ τ i j, fockL (MvPolynomial.map φ (d τ i)) (MvPolynomial.map φ (b τ j)) = if i = j then fockS (extremal K n (lam τ)) (extremal K n (lam τ)) else 0`.

Introduce `τ i j`. Rewrite using `[fockL_apply, fockSQ K, (Formalism.GradedWeylDivisibility.fockQPos _ _ _).1, ← fockSQ K, ← fockL_apply, h1]`. Simplify using `only [eq_comm]`. Establish `hbK : ∀ τ, Submodule.span (𝓞 K) (Set.range fun i => MvPolynomial.map φ (b τ i)) = (nablaSq (𝓞 K) n (lam τ)).map (toK K _)`. Introduce `τ`.

Unfold `nablaSq`. Rewrite using `[dualWeyl_toK, ← span_image_eq _ _ (hb τ), ← Set.range_comp]`. Both sides reduce to the same expression. Establish `hdK : ∀ τ, Submodule.span (𝓞 K) (Set.range fun i => MvPolynomial.map φ (d τ i)) = (delSq (𝓞 K) n (lam τ)).map (toK K _)`. Introduce `τ`.

Unfold `delSq`. Rewrite using `[weyl_toK, ← span_image_eq _ _ (hd τ), ← Set.range_comp]`. Both sides reduce to the same expression. Establish `hB : Submodule.span (𝓞 K) (Set.range fun i : (∀ τ, Formalism.GradedWeylDivisibility.ssIdx n n (lam τ).natW) => ten fun τ => MvPolynomial.map φ (b τ (i τ))) = nabStd K lam` using `(Formalism.GradedWeylDivisibility.tensorBasis (𝓞 K) K ι n n _ _ (fun τ i => MvPolynomial.map φ (b τ i)) (fun τ => linInd_of_dual fockL _ _ _ (hne τ) (h2 τ)) hbK).2`. Establish `hD : Submodule.span (𝓞 K) (Set.range fun i : (∀ τ, Formalism.GradedWeylDivisibility.ssIdx n n (lam τ).natW) => ten fun τ => MvPolynomial.map φ (d τ (i τ))) = delStd K lam` using `(Formalism.GradedWeylDivisibility.tensorBasis (𝓞 K) K ι n n _ _ (fun τ i => MvPolynomial.map φ (d τ i)) (fun τ => linInd_of_dual fockL _ _ _ (hne τ) (h1 τ)) hdK).2`.

Establish `hpair : ∀ f g : ∀ τ, Formalism.GradedWeylDivisibility.ssIdx n n (lam τ).natW → MvPolynomial (Fin n × Fin n) K, (∀ τ i j, fockL (f τ i) (g τ j) = if i = j then fockS (extremal K n (lam τ)) (extremal K n (lam τ)) else 0) → ∀ i j : (∀ τ, Formalism.GradedWeylDivisibility.ssIdx n n (l …`. Introduce `f g h i j`. Establish `hg : gramTw lam (fun _ : ι => (1 : Matrix (Fin n) (Fin n) K)) = 1`. Unfold `gramTw`. Simplify using the standard rewrite rules.

Rewrite using `[pairP_apply, hg]`. Simplify using `only [Matrix.transpose_one]`. Rewrite using `[blockAct_one, AlgHom.id_apply, fockL_apply, fockSymTensor_holds K ι n]`. Simplify using `only [← fockL_apply (f _ _), h]`. Use `split_ifs with hij`.

Substitute `hij` using the available equality. Simplify using `only [if_true]`. Conclude with `div_mul_cancel₀ 1 (Finset.prod_ne_zero_iff.mpr fun τ _ => hne τ)`. Take `⟨τ, hτ⟩` from `Function.ne_iff.mp hij`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ τ) (if_neg hτ), mul_zero]`.

Establish `hc : ∀ a ∈ (algebraMap (𝓞 K) K).range, starRingEnd K a ∈ (algebraMap (𝓞 K) K).range`. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `⟨⟨_, (RingOfIntegers.isIntegral_coe a).map (starRingEnd K).toIntAlgHom⟩, rfl⟩`. Take `⟨-, -, hs1, hs2⟩` from `GlobalTheory.StdLatSpan.std_fg_span K ι n lam`. Rewrite `hs1` using `[← hB, Submodule.span_span_of_tower]`.

Rewrite `hs2` using `[← hD, Submodule.span_span_of_tower]`. Rewrite using `[← hB, ← hD]`. Conclude with `⟨dual_span_iff hc _ _ _ (hpair _ _ h2) x (hs1 ▸ hx), dual_span_iff hc _ _ _ (hpair _ _ h1) x (hs2 ▸ hx)⟩`.
-/
theorem std_dual : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (x : Pol K ι n), x ∈ VV K lam → ((∀ y ∈ delStd K lam, pairP lam (fun _ => 1) y x ∈ (algebraMap (𝓞 K) K).range) ↔ x ∈ nabStd K lam) ∧ ((∀ y ∈ nabStd K lam, pairP lam (fun _ => 1) y x ∈ (algebraMap (𝓞 K) K).range) ↔ x ∈ delStd K lam) := by
  classical
  intro K _ _ _ ι _ n lam x hx
  haveI : ∀ τ, Fintype (Formalism.GradedWeylDivisibility.ssIdx n n (lam τ).natW) :=
    fun τ => (Formalism.GradedWeylDivisibility.sSIdxFinite n n _).fintype
  choose b d hb hd hbd using fun τ => exists_dual_bases n (lam τ).natW (natW_antitone (lam τ))
  set φ := algebraMap ℚ K with hφ
  have hne : ∀ τ, fockS (extremal K n (lam τ)) (extremal K n (lam τ)) ≠ 0 := by
    intro τ
    rw [← map_extremal φ, fockSQ K]
    exact (map_ne_zero φ).mpr
      ((Formalism.GradedWeylDivisibility.fockQPos _ _ (extremal ℚ n (lam τ))).2 (Formalism.GradedWeylDivisibility.hwNe ℚ n n le_rfl _)).ne'
  have h1 : ∀ τ i j, fockL (MvPolynomial.map φ (b τ i)) (MvPolynomial.map φ (d τ j)) =
      if i = j then fockS (extremal K n (lam τ)) (extremal K n (lam τ)) else 0 := by
    intro τ i j
    rw [fockL_apply, ← map_extremal φ, fockSQ K, fockSQ K, hbd]
    split_ifs
    · rfl
    · exact map_zero _
  have h2 : ∀ τ i j, fockL (MvPolynomial.map φ (d τ i)) (MvPolynomial.map φ (b τ j)) =
      if i = j then fockS (extremal K n (lam τ)) (extremal K n (lam τ)) else 0 := by
    intro τ i j
    rw [fockL_apply, fockSQ K, (Formalism.GradedWeylDivisibility.fockQPos _ _ _).1, ← fockSQ K, ← fockL_apply, h1]
    simp only [eq_comm]
  have hbK : ∀ τ, Submodule.span (𝓞 K) (Set.range fun i => MvPolynomial.map φ (b τ i)) =
      (nablaSq (𝓞 K) n (lam τ)).map (toK K _) := by
    intro τ
    unfold nablaSq
    rw [dualWeyl_toK, ← span_image_eq _ _ (hb τ), ← Set.range_comp]
    rfl
  have hdK : ∀ τ, Submodule.span (𝓞 K) (Set.range fun i => MvPolynomial.map φ (d τ i)) =
      (delSq (𝓞 K) n (lam τ)).map (toK K _) := by
    intro τ
    unfold delSq
    rw [weyl_toK, ← span_image_eq _ _ (hd τ), ← Set.range_comp]
    rfl
  have hB : Submodule.span (𝓞 K) (Set.range fun i : (∀ τ, Formalism.GradedWeylDivisibility.ssIdx n n (lam τ).natW) =>
      ten fun τ => MvPolynomial.map φ (b τ (i τ))) = nabStd K lam :=
    (Formalism.GradedWeylDivisibility.tensorBasis (𝓞 K) K ι n n _ _ (fun τ i => MvPolynomial.map φ (b τ i))
      (fun τ => linInd_of_dual fockL _ _ _ (hne τ) (h2 τ)) hbK).2
  have hD : Submodule.span (𝓞 K) (Set.range fun i : (∀ τ, Formalism.GradedWeylDivisibility.ssIdx n n (lam τ).natW) =>
      ten fun τ => MvPolynomial.map φ (d τ (i τ))) = delStd K lam :=
    (Formalism.GradedWeylDivisibility.tensorBasis (𝓞 K) K ι n n _ _ (fun τ i => MvPolynomial.map φ (d τ i))
      (fun τ => linInd_of_dual fockL _ _ _ (hne τ) (h1 τ)) hdK).2
  have hpair : ∀ f g : ∀ τ, Formalism.GradedWeylDivisibility.ssIdx n n (lam τ).natW → MvPolynomial (Fin n × Fin n) K,
      (∀ τ i j, fockL (f τ i) (g τ j) =
        if i = j then fockS (extremal K n (lam τ)) (extremal K n (lam τ)) else 0) →
      ∀ i j : (∀ τ, Formalism.GradedWeylDivisibility.ssIdx n n (lam τ).natW),
        pairP lam (fun _ => 1) (ten fun τ => f τ (i τ)) (ten fun τ => g τ (j τ)) = if i = j then 1 else 0 := by
    intro f g h i j
    have hg : gramTw lam (fun _ : ι => (1 : Matrix (Fin n) (Fin n) K)) = 1 := by
      unfold gramTw
      simp
    rw [pairP_apply, hg]
    simp only [Matrix.transpose_one]
    rw [blockAct_one, AlgHom.id_apply, fockL_apply, fockSymTensor_holds K ι n]
    simp only [← fockL_apply (f _ _), h]
    split_ifs with hij
    · subst hij
      simp only [if_true]
      exact div_mul_cancel₀ 1 (Finset.prod_ne_zero_iff.mpr fun τ _ => hne τ)
    · obtain ⟨τ, hτ⟩ := Function.ne_iff.mp hij
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) (if_neg hτ), mul_zero]
  have hc : ∀ a ∈ (algebraMap (𝓞 K) K).range, starRingEnd K a ∈ (algebraMap (𝓞 K) K).range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨_, (RingOfIntegers.isIntegral_coe a).map (starRingEnd K).toIntAlgHom⟩, rfl⟩
  obtain ⟨-, -, hs1, hs2⟩ := GlobalTheory.StdLatSpan.std_fg_span K ι n lam
  rw [← hB, Submodule.span_span_of_tower] at hs1
  rw [← hD, Submodule.span_span_of_tower] at hs2
  rw [← hB, ← hD]
  exact ⟨dual_span_iff hc _ _ _ (hpair _ _ h2) x (hs1 ▸ hx), dual_span_iff hc _ _ _ (hpair _ _ h1) x (hs2 ▸ hx)⟩

end GlobalTheory.StdDual
