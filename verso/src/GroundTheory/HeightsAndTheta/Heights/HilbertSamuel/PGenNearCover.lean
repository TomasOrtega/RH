import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenNearCover
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGradedSubmodules
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GenNearCover

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {S : Type*} [CommRing S] {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*}
  [∀ k, Fintype (ι k)]

def blockDeg (p : Σ k, ι k) : K → ℕ := Pi.single p.1 1

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp), Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single k]`. Simplify using `[blockDeg]`. Introduce `b _ hb`. Simplify using `[blockDeg, Ne.symm hb]`. Simplify using the standard rewrite rules.
-/
theorem weight_blockDeg_apply [∀ k, Fintype (ι k)] (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blockDeg (ι := ι)) m k = ∑ i, m ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp), Finset.sum_apply,
    Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp [blockDeg]
  · intro b _ hb
    simp [blockDeg, Ne.symm hb]
  · simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h m hm k`. Rewrite using `[← weight_blockDeg_apply, h (mem_support_iff.1 hm)]`. Introduce `h m hm`. Use function extensionality and compare the values at `k`.

Rewrite using `[weight_blockDeg_apply]`. Conclude with `h m (mem_support_iff.2 hm) k`.
-/
theorem isWeightedHomogeneous_iff {f : MRingOver S ι} {a : K → ℕ} :
    IsWeightedHomogeneous (blockDeg (ι := ι)) f a ↔ IsMultiHomog f a := by
  constructor
  · intro h m hm k
    rw [← weight_blockDeg_apply, h (mem_support_iff.1 hm)]
  · intro h m hm
    funext k
    rw [weight_blockDeg_apply]
    exact h m (mem_support_iff.2 hm) k

omit [∀ k, Fintype (ι k)] in
open Classical in

/- English proof (translation)
Establish `hmem : f ∈ weightedHomogeneousSubmodule S (blockDeg (ι` using `ι)) E := (mem_weightedHomogeneousSubmodule _ _ _ _).2 hf`. Establish `h` using `DirectSum.coe_decompose_mul_of_right_mem (weightedHomogeneousSubmodule S (blockDeg (ι := ι))) D (a := g) hmem`. Rewrite using `[← weightedDecomposition.decompose'_apply, ← weightedDecomposition.decompose'_apply]`. Conclude with `h`.
-/
theorem component_mul {g f : MRingOver S ι} {E : K → ℕ}
    (hf : IsWeightedHomogeneous (blockDeg (ι := ι)) f E) (D : K → ℕ) :
    weightedHomogeneousComponent (blockDeg (ι := ι)) D (g * f) =
      if E ≤ D then weightedHomogeneousComponent (blockDeg (ι := ι)) (D - E) g * f else 0 := by
  have hmem : f ∈ weightedHomogeneousSubmodule S (blockDeg (ι := ι)) E :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).2 hf
  have h := DirectSum.coe_decompose_mul_of_right_mem
    (weightedHomogeneousSubmodule S (blockDeg (ι := ι))) D (a := g) hmem
  rw [← weightedDecomposition.decompose'_apply, ← weightedDecomposition.decompose'_apply]
  exact h

/- English proof (translation)
Take `⟨g, hg, hcoeff⟩` from `cyc_exists_blockComponent (fun k => cyc_isHomogeneous_of_isMultiHomogIdeal hA k) D Finset.univ hv`. Use `hg using 1` and compare the differences between its conclusion and the goal. Use extensionality with `m`. Rewrite using `[coeff_weightedHomogeneousComponent, hcoeff]`. Establish `e : Finsupp.weight (blockDeg (ι` using `ι)) m = D ↔ ∀ k ∈ Finset.univ, ∑ i, m ⟨k, i⟩ = D k := by`.

Prove the components needed by the constructor for the conclusion. Introduce `h k _`. Rewrite using `[← weight_blockDeg_apply, h]`. Introduce `h`. Use function extensionality and compare the values at `k`.

Rewrite using `[weight_blockDeg_apply]`. Conclude with `h k (Finset.mem_univ k)`. Distinguish the cases in `h : ∀ k ∈ Finset.univ, ∑ i, m ⟨k, i⟩ = D k`. Rewrite using `[if_pos h, if_pos (e.2 h)]`. Rewrite using `[if_neg h, if_neg (fun h' => h (e.1 h'))]`.
-/
theorem component_mem {A : Ideal (MRingOver S ι)} (hA : IsMultiHomogIdeal A) {v : MRingOver S ι}
    (hv : v ∈ A) (D : K → ℕ) : weightedHomogeneousComponent (blockDeg (ι := ι)) D v ∈ A := by
  obtain ⟨g, hg, hcoeff⟩ :=
    cyc_exists_blockComponent (fun k => cyc_isHomogeneous_of_isMultiHomogIdeal hA k) D Finset.univ hv
  convert hg using 1
  ext m
  rw [coeff_weightedHomogeneousComponent, hcoeff]
  have e : Finsupp.weight (blockDeg (ι := ι)) m = D ↔ ∀ k ∈ Finset.univ, ∑ i, m ⟨k, i⟩ = D k := by
    constructor
    · intro h k _
      rw [← weight_blockDeg_apply, h]
    · intro h
      funext k
      rw [weight_blockDeg_apply]
      exact h k (Finset.mem_univ k)
  by_cases h : ∀ k ∈ Finset.univ, ∑ i, m ⟨k, i⟩ = D k
  · rw [if_pos h, if_pos (e.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (e.1 h'))]

/- English proof (translation)
The claim follows from `cyc_isMultiHomogIdeal_of_isHomogeneous fun k => cyc_isHomogeneous_of_mem_minimalPrimes _ (cyc_isHomogeneous_of_isMultiHomogIdeal hJ k) hW`.
-/
theorem isMultiHomogIdeal_of_mem_minimalPrimes {J W : Ideal (MRingOver S ι)} (hJ : IsMultiHomogIdeal J)
    (hW : W ∈ J.minimalPrimes) : IsMultiHomogIdeal W :=
  cyc_isMultiHomogIdeal_of_isHomogeneous fun k =>
    cyc_isHomogeneous_of_mem_minimalPrimes _ (cyc_isHomogeneous_of_isMultiHomogIdeal hJ k) hW

omit [DecidableEq K] [∀ k, Fintype (ι k)] in

def cellProd (S : Type*) [CommRing S] (I : ∀ k, Finset (ι k)) : MRingOver S ι :=
  ∏ k, ∏ i ∈ I k, X ⟨k, i⟩

omit [DecidableEq K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
The claim follows from `Submonoid.prod_mem _ fun k _ => Submonoid.prod_mem _ fun i hi => Submonoid.subset_closure ⟨k, i, hi, rfl⟩`.
-/
theorem cellProd_mem (I : ∀ k, Finset (ι k)) : cellProd S I ∈ KH.cellMon S I :=
  Submonoid.prod_mem _ fun k _ => Submonoid.prod_mem _ fun i hi => Submonoid.subset_closure ⟨k, i, hi, rfl⟩

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
The claim follows from `IsWeightedHomogeneous.prod _ _ _ fun _ _ => IsWeightedHomogeneous.prod _ _ _ fun _ _ => isWeightedHomogeneous_X (R := S) _ _`.
-/
theorem cellProd_isWeightedHomogeneous (I : ∀ k, Finset (ι k)) :
    IsWeightedHomogeneous (blockDeg (ι := ι)) (cellProd S I) (∑ k, ∑ i ∈ I k, blockDeg ⟨k, i⟩) :=
  IsWeightedHomogeneous.prod _ _ _ fun _ _ =>
    IsWeightedHomogeneous.prod _ _ _ fun _ _ => isWeightedHomogeneous_X (R := S) _ _

omit [DecidableEq K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Introduce `k`. Take `⟨i, hi⟩` from `hI k`. Use `⟨i, fun hX => hW ?_⟩` and prove the remaining obligations. Establish `h1 : (X ⟨k, i⟩ : MRingOver S ι) ∣ ∏ j ∈ I k, (X ⟨k, j⟩ : MRingOver S ι)` using `Finset.dvd_prod_of_mem (fun j => (X ⟨k, j⟩ : MRingOver S ι)) hi`. Establish `h2 : (∏ j ∈ I k, (X ⟨k, j⟩ : MRingOver S ι)) ∣ cellProd S I` using `Finset.dvd_prod_of_mem (fun l => ∏ j ∈ I l, (X ⟨l, j⟩ : MRingOver S ι)) (Finset.mem_univ k)`.

Take `⟨c, hc⟩` from `h1.trans h2`. Rewrite using `[hc]`. Conclude with `W.mul_mem_right c hX`.
-/
theorem isRelevant_of_cellProd_notMem {I : ∀ k, Finset (ι k)} (hI : ∀ k, (I k).Nonempty)
    {W : Ideal (MRingOver S ι)} (hW : cellProd S I ∉ W) : IsRelevant W := by
  intro k
  obtain ⟨i, hi⟩ := hI k
  refine ⟨i, fun hX => hW ?_⟩
  have h1 : (X ⟨k, i⟩ : MRingOver S ι) ∣ ∏ j ∈ I k, (X ⟨k, j⟩ : MRingOver S ι) :=
    Finset.dvd_prod_of_mem (fun j => (X ⟨k, j⟩ : MRingOver S ι)) hi
  have h2 : (∏ j ∈ I k, (X ⟨k, j⟩ : MRingOver S ι)) ∣ cellProd S I :=
    Finset.dvd_prod_of_mem (fun l => ∏ j ∈ I l, (X ⟨l, j⟩ : MRingOver S ι)) (Finset.mem_univ k)
  obtain ⟨c, hc⟩ := h1.trans h2
  rw [hc]
  exact W.mul_mem_right c hX

omit [DecidableEq K] in

/- English proof (translation)
Take `⟨Q, ⟨hQ, hWQ⟩, hmax⟩` from `set_has_maximal_iff_noetherian.2 (inferInstance : IsNoetherian (MRingOver S ι) (MRingOver S ι)) {Q | IsMultiProjPrime Q ∧ W ≤ Q} ⟨W, hW, le_rfl⟩`. Use `⟨Q, ⟨hQ, fun Q' hQ' hle => ?_⟩, hWQ⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Conclude with `hmax Q' ⟨hQ', hWQ.trans hle⟩ (lt_of_le_of_ne hle (Ne.symm hne))`.
-/
theorem exists_isClosedMultiPt_ge [IsNoetherianRing S] {W : Ideal (MRingOver S ι)} (hW : IsMultiProjPrime W) :
    ∃ Q, IsClosedMultiPt Q ∧ W ≤ Q := by
  obtain ⟨Q, ⟨hQ, hWQ⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.2 (inferInstance : IsNoetherian (MRingOver S ι) (MRingOver S ι))
      {Q | IsMultiProjPrime Q ∧ W ≤ Q} ⟨W, hW, le_rfl⟩
  refine ⟨Q, ⟨hQ, fun Q' hQ' hle => ?_⟩, hWQ⟩
  by_contra hne
  exact hmax Q' ⟨hQ', hWQ.trans hle⟩ (lt_of_le_of_ne hle (Ne.symm hne))

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Proceed by induction on `y using LocalizedModule.induction_on with`. Consider the case `h m s => rw [LocalizedModule.smul'_mk, Module.mem_annihilator.1 hv m, LocalizedModule.zero_mk]`.
-/
theorem smul_eq_zero_of_mem_annihilator {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M]
    {T : Submonoid (MRingOver S ι)} {v : MRingOver S ι} (hv : v ∈ Module.annihilator (MRingOver S ι) M)
    (y : LocalizedModule T M) : v • y = 0 := by
  induction y using LocalizedModule.induction_on with
  | h m s => rw [LocalizedModule.smul'_mk, Module.mem_annihilator.1 hv m, LocalizedModule.zero_mk]

end GenNearCover

open GenNearCover in

/- English proof (translation)
Introduce `S _ K _ _ ι _ _ V M _ _ _ _ 𝓜 deg hS hgr hV hP`. Use `hS` as an intermediate fact. Set `Pt` to `{P : Ideal (MRingOver S ι) // IsClosedMultiPt P ∧ V ≤ P}`. Use `choose F δ c₀ hFδ hFP hgen using fun P : Pt => hP P.1 P.2.1 P.2.2`. Establish `hA : IsMultiHomogIdeal (Module.annihilator (MRingOver S ι) M)` using `(hG S K ι M 𝓜 hgr).1`.

Establish `hJ : IsMultiHomogIdeal (Module.annihilator (MRingOver S ι) M ⊔ Ideal.span (Set.range F))`. Take `⟨SA, hSA, hSAe⟩` from `id hA`. Use `⟨SA ∪ Set.range F, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `f (hf | ⟨P, rfl⟩)`. Conclude with `hSA f hf`.

Conclude with `⟨δ P, hFδ P⟩`. Rewrite using `[Ideal.span_union, ← hSAe]`. Establish `key : ∀ I : KH.Cell K ι 0, ∃ T : Finset Pt, cellProd S I.1 ∈ (Module.annihilator (MRingOver S ι) M ⊔ Ideal.span (Set.range fun P : T => F P.1)).radical`. Introduce `I`. Establish `hrad : cellProd S I.1 ∈ (Module.annihilator (MRingOver S ι) M ⊔ Ideal.span (Set.range F)).radical`.

Rewrite using `[← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]`. Introduce `W hW`. Assume the negation of the conclusion as `hX`. Establish `hWm : IsMultiProjPrime W` using `⟨hW.1.1, isMultiHomogIdeal_of_mem_minimalPrimes hJ hW, isRelevant_of_cellProd_notMem I.2.1 hX⟩`. Take `⟨Q, hQ, hWQ⟩` from `exists_isClosedMultiPt_ge hWm`.

Establish `hVQ : V ≤ Q` using `hV.trans ((le_sup_left.trans hW.1.2).trans hWQ)`. Conclude with `hFP ⟨Q, hQ, hVQ⟩ (hWQ (hW.1.2 (Ideal.mem_sup_right (Ideal.subset_span ⟨⟨Q, hQ, hVQ⟩, rfl⟩))))`. Take `⟨k, hk⟩` from `hrad`. Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.1 hk`. Take `⟨c, hc⟩` from `Finsupp.mem_span_range_iff_exists_finsupp.1 hz`.

Use `⟨c.support, k, ?_⟩` and prove the remaining obligations. Rewrite using `[← hyz]`. Use `Ideal.add_mem _ (Ideal.mem_sup_left hy) (Ideal.mem_sup_right ?_)` and prove the remaining obligations. Rewrite using `[← hc, Finsupp.sum]`. Conclude with `Ideal.sum_mem _ fun P hP => Submodule.smul_mem _ _ (Ideal.subset_span ⟨⟨P, hP⟩, rfl⟩)`.

Use `choose Tf hTf using key`. Set `: Fintype (KH.Cell K ι 0)` to `by unfold KH.Cell; infer_instance`. Use `⟨Finset.univ.sup fun I => (Tf I).sup c₀, fun c hc I x hx => ?_⟩` and prove the remaining obligations. Establish `hcP : ∀ P : Tf I, c₀ P.1 ≤ c` using `fun P => (Finset.le_sup (f := c₀) P.2).trans ((Finset.le_sup (f := fun I => (Tf I).sup c₀) (Finset.mem_univ I)).trans hc)`. Use `choose n t a r p z ht hta hp hz he using fun P : Tf I => hgen P.1 c (hcP P) I x hx`.

Take `⟨N, hnN⟩ : ∃ N, ∀ P, n P ≤ N` from `⟨Finset.univ.sup n, fun P => Finset.le_sup (Finset.mem_univ P)⟩`. Establish `hrad : cellProd S I.1 ∈ (Module.annihilator (MRingOver S ι) M ⊔ Ideal.span (Set.range fun P : Tf I => F P.1 ^ N)).radical`. Use `(Ideal.radical_le_radical_iff.2 (sup_le (le_sup_left.trans Ideal.le_radical) ?_)) (hTf I)` and prove the remaining obligations. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨P, rfl⟩`.

Conclude with `⟨N, Ideal.mem_sup_right (Ideal.subset_span ⟨P, rfl⟩)⟩`. Take `⟨k, hk⟩` from `hrad`. Take `⟨v, hv, y, hy, hvy⟩` from `Submodule.mem_sup.1 hk`. Take `⟨g, hg⟩` from `Ideal.mem_span_range_iff_exists_fun.1 hy`. Take `⟨D, hXk⟩ : ∃ D, IsWeightedHomogeneous (blockDeg (ι` from `ι)) (cellProd S I.1 ^ k) D := ⟨_, (cellProd_isWeightedHomogeneous I.1).pow k⟩`.

Establish `hFN : ∀ P : Tf I, IsWeightedHomogeneous (blockDeg (ι` using `ι)) (F P.1 ^ N) (N • δ P.1) := fun P => (isWeightedHomogeneous_iff.2 (hFδ P.1)).pow N`. Set `gc : Tf I → MRingOver S ι` to `fun P => if N • δ P.1 ≤ D then weightedHomogeneousComponent (blockDeg (ι := ι)) (D - N • δ P.1) (g P) else 0`. Establish `hdec : cellProd S I.1 ^ k = weightedHomogeneousComponent (blockDeg (ι` using `ι)) D v + ∑ P, gc P * F P.1 ^ N := by`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).2 hXk), if_pos rfl]`.

Use `_ = weightedHomogeneousComponent (blockDeg (ι := ι)) D (v + ∑ P, g P * F P.1 ^ N) := by rw [hg, hvy]`. Use `_ = _ := by`. Rewrite using `[map_add, map_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun P _ => ?_` and prove the remaining obligations.

Rewrite using `[component_mul (hFN P) D]`. Simplify using `only [gc]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hann : ∀ w : LocalizedModule (KH.cellMon S I.1) M, weightedHomogeneousComponent (blockDeg (ι` using `ι)) D v • w = 0 := smul_eq_zero_of_mem_annihilator (component_mem hA hv D)`. Establish `hsplit : ∀ P : Tf I, gc P * F P.1 ^ N * ∏ Q, t Q = (gc P * F P.1 ^ (N - n P) * ∏ Q ∈ Finset.univ.erase P, t Q) * (F P.1 ^ n P * t P)`.

Introduce `P`. Establish `e1 : F P.1 ^ N = F P.1 ^ (N - n P) * F P.1 ^ n P` using `by rw [← pow_add, Nat.sub_add_cancel (hnN P)]`. Rewrite using `[← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ P), e1]`. Expand and normalize the polynomial expressions, which then agree. Establish `heq : (cellProd S I.1 ^ k * ∏ Q, t Q) • x = ∑ P, ∑ j, (gc P * F P.1 ^ (N - n P) * (∏ Q ∈ Finset.univ.erase P, t Q) * p P j) • z P j I`.

Rewrite using `[hdec, add_mul, add_smul, mul_smul, hann, zero_add, Finset.sum_mul, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun P _ => ?_` and prove the remaining obligations. Rewrite using `[hsplit P, mul_smul, he P, Finset.smul_sum]`. Simplify using `only [smul_smul]`. Establish `hq : ∀ P j, IsMultiHomog (gc P * F P.1 ^ (N - n P) * (∏ Q ∈ Finset.univ.erase P, t Q) * p P j) (D + ∑ Q, a Q)`.

Introduce `P j`. Rewrite using `[← isWeightedHomogeneous_iff]`. Distinguish the cases in `hle : N • δ P.1 ≤ D`. Establish `h1 : IsWeightedHomogeneous (blockDeg (ι` using `ι)) (gc P) (D - N • δ P.1) := by`. Simplify using `only [gc, if_pos hle]`.

Conclude with `weightedHomogeneousComponent_isWeightedHomogeneous _ _`. Establish `h2` using `((h1.mul ((isWeightedHomogeneous_iff.2 (hFδ P.1)).pow (N - n P))).mul (IsWeightedHomogeneous.prod (Finset.univ.erase P) t a fun Q _ => isWeightedHomogeneous_iff.2 (hta Q))).mul (isWeightedHomogeneous_iff.2 (hp P j))`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[← Finset.add_sum_erase Finset.univ a (Finset.mem_univ P)]`. Use function extensionality and compare the values at `q`.

Establish `e2 : (N - n P) * δ P.1 q + n P * δ P.1 q = N * δ P.1 q`. Rewrite using `[← add_mul, Nat.sub_add_cancel (hnN P)]`. Establish `hleq` using `hle q`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Finset.sum_apply] at hleq ⊢`. Generalize the expression as in `(N - n P) * δ P.1 q = u₁ at e2 ⊢`.

Generalize the expression as in `n P * δ P.1 q = u₂ at e2 ⊢`. Generalize the expression as in `N * δ P.1 q = u₃ at e2 hleq ⊢`. Use linear arithmetic over natural numbers and integers. Establish `h0 : gc P = 0` using `by simp only [gc, if_neg hle]`. Rewrite using `[h0, zero_mul, zero_mul, zero_mul]`.

Conclude with `isWeightedHomogeneous_zero (R := S) _ _`. Set `σ` to `Σ P : Tf I, Fin (r P)`. Set `e` to `Fintype.equivFin σ`. Use `⟨cellProd S I.1 ^ k * ∏ Q, t Q, D + ∑ Q, a Q, Fintype.card σ, fun j => gc (e.symm j).1 * F (e.symm j).1.1 ^ (N - n (e.symm j).1) * (∏ Q ∈ Finset.univ.erase (e.symm j).1, t Q) * p (e.symm j).1 (e.symm j).2, fun j => z (e.symm j).1 (e.symm j).2, Submonoid.mul_mem _ (Submonoid.pow_m …` and prove the remaining obligations. Rewrite using `[heq]`.

Use `(Fintype.sum_sigma (fun s : σ => (gc s.1 * F s.1.1 ^ (N - n s.1) * (∏ Q ∈ Finset.univ.erase s.1, t Q) * p s.1 s.2) • z s.1 s.2 I)).symm.trans ?_` and prove the remaining obligations. Conclude with `(Equiv.sum_comp e.symm (fun s : σ => (gc s.1 * F s.1.1 ^ (N - n s.1) * (∏ Q ∈ Finset.univ.erase s.1, t Q) * p s.1 s.2) • z s.1 s.2 I)).symm`.
-/
theorem GenNearCover.proof (hG : GradedSubmodules.Statement) : GenNearCover.Statement := by
  intro S _ K _ _ ι _ _ V M _ _ _ _ 𝓜 deg hS hgr hV hP
  classical
  have := hS
  let Pt := {P : Ideal (MRingOver S ι) // IsClosedMultiPt P ∧ V ≤ P}
  choose F δ c₀ hFδ hFP hgen using fun P : Pt => hP P.1 P.2.1 P.2.2
  have hA : IsMultiHomogIdeal (Module.annihilator (MRingOver S ι) M) := (hG S K ι M 𝓜 hgr).1
  have hJ : IsMultiHomogIdeal (Module.annihilator (MRingOver S ι) M ⊔ Ideal.span (Set.range F)) := by
    obtain ⟨SA, hSA, hSAe⟩ := id hA
    refine ⟨SA ∪ Set.range F, ?_, ?_⟩
    · rintro f (hf | ⟨P, rfl⟩)
      · exact hSA f hf
      · exact ⟨δ P, hFδ P⟩
    · rw [Ideal.span_union, ← hSAe]

  have key : ∀ I : KH.Cell K ι 0, ∃ T : Finset Pt, cellProd S I.1 ∈
      (Module.annihilator (MRingOver S ι) M ⊔ Ideal.span (Set.range fun P : T => F P.1)).radical := by
    intro I
    have hrad : cellProd S I.1 ∈ (Module.annihilator (MRingOver S ι) M ⊔ Ideal.span (Set.range F)).radical := by
      rw [← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
      intro W hW
      by_contra hX
      have hWm : IsMultiProjPrime W :=
        ⟨hW.1.1, isMultiHomogIdeal_of_mem_minimalPrimes hJ hW, isRelevant_of_cellProd_notMem I.2.1 hX⟩
      obtain ⟨Q, hQ, hWQ⟩ := exists_isClosedMultiPt_ge hWm
      have hVQ : V ≤ Q := hV.trans ((le_sup_left.trans hW.1.2).trans hWQ)
      exact hFP ⟨Q, hQ, hVQ⟩
        (hWQ (hW.1.2 (Ideal.mem_sup_right (Ideal.subset_span ⟨⟨Q, hQ, hVQ⟩, rfl⟩))))
    obtain ⟨k, hk⟩ := hrad
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hk
    obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hz
    refine ⟨c.support, k, ?_⟩
    rw [← hyz]
    refine Ideal.add_mem _ (Ideal.mem_sup_left hy) (Ideal.mem_sup_right ?_)
    rw [← hc, Finsupp.sum]
    exact Ideal.sum_mem _ fun P hP => Submodule.smul_mem _ _ (Ideal.subset_span ⟨⟨P, hP⟩, rfl⟩)
  choose Tf hTf using key
  let : Fintype (KH.Cell K ι 0) := by unfold KH.Cell; infer_instance
  refine ⟨Finset.univ.sup fun I => (Tf I).sup c₀, fun c hc I x hx => ?_⟩
  have hcP : ∀ P : Tf I, c₀ P.1 ≤ c := fun P =>
    (Finset.le_sup (f := c₀) P.2).trans
      ((Finset.le_sup (f := fun I => (Tf I).sup c₀) (Finset.mem_univ I)).trans hc)
  choose n t a r p z ht hta hp hz he using fun P : Tf I => hgen P.1 c (hcP P) I x hx
  obtain ⟨N, hnN⟩ : ∃ N, ∀ P, n P ≤ N := ⟨Finset.univ.sup n, fun P => Finset.le_sup (Finset.mem_univ P)⟩

  have hrad : cellProd S I.1 ∈
      (Module.annihilator (MRingOver S ι) M ⊔ Ideal.span (Set.range fun P : Tf I => F P.1 ^ N)).radical := by
    refine (Ideal.radical_le_radical_iff.2 (sup_le (le_sup_left.trans Ideal.le_radical) ?_)) (hTf I)
    rw [Ideal.span_le]
    rintro _ ⟨P, rfl⟩
    exact ⟨N, Ideal.mem_sup_right (Ideal.subset_span ⟨P, rfl⟩)⟩
  obtain ⟨k, hk⟩ := hrad
  obtain ⟨v, hv, y, hy, hvy⟩ := Submodule.mem_sup.1 hk
  obtain ⟨g, hg⟩ := Ideal.mem_span_range_iff_exists_fun.1 hy
  obtain ⟨D, hXk⟩ : ∃ D, IsWeightedHomogeneous (blockDeg (ι := ι)) (cellProd S I.1 ^ k) D :=
    ⟨_, (cellProd_isWeightedHomogeneous I.1).pow k⟩
  have hFN : ∀ P : Tf I, IsWeightedHomogeneous (blockDeg (ι := ι)) (F P.1 ^ N) (N • δ P.1) := fun P =>
    (isWeightedHomogeneous_iff.2 (hFδ P.1)).pow N
  let gc : Tf I → MRingOver S ι := fun P =>
    if N • δ P.1 ≤ D then weightedHomogeneousComponent (blockDeg (ι := ι)) (D - N • δ P.1) (g P) else 0
  have hdec : cellProd S I.1 ^ k =
      weightedHomogeneousComponent (blockDeg (ι := ι)) D v + ∑ P, gc P * F P.1 ^ N := by
    calc cellProd S I.1 ^ k = weightedHomogeneousComponent (blockDeg (ι := ι)) D (cellProd S I.1 ^ k) := by
          rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).2 hXk), if_pos rfl]
      _ = weightedHomogeneousComponent (blockDeg (ι := ι)) D (v + ∑ P, g P * F P.1 ^ N) := by rw [hg, hvy]
      _ = _ := by
          rw [map_add, map_sum]
          congr 1
          refine Finset.sum_congr rfl fun P _ => ?_
          rw [component_mul (hFN P) D]
          simp only [gc]
          split_ifs <;> simp

  have hann : ∀ w : LocalizedModule (KH.cellMon S I.1) M,
      weightedHomogeneousComponent (blockDeg (ι := ι)) D v • w = 0 :=
    smul_eq_zero_of_mem_annihilator (component_mem hA hv D)
  have hsplit : ∀ P : Tf I, gc P * F P.1 ^ N * ∏ Q, t Q =
      (gc P * F P.1 ^ (N - n P) * ∏ Q ∈ Finset.univ.erase P, t Q) * (F P.1 ^ n P * t P) := by
    intro P
    have e1 : F P.1 ^ N = F P.1 ^ (N - n P) * F P.1 ^ n P := by rw [← pow_add, Nat.sub_add_cancel (hnN P)]
    rw [← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ P), e1]
    ring
  have heq : (cellProd S I.1 ^ k * ∏ Q, t Q) • x =
      ∑ P, ∑ j, (gc P * F P.1 ^ (N - n P) * (∏ Q ∈ Finset.univ.erase P, t Q) * p P j) • z P j I := by
    rw [hdec, add_mul, add_smul, mul_smul, hann, zero_add, Finset.sum_mul, Finset.sum_smul]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [hsplit P, mul_smul, he P, Finset.smul_sum]
    simp only [smul_smul]
  have hq : ∀ P j, IsMultiHomog (gc P * F P.1 ^ (N - n P) * (∏ Q ∈ Finset.univ.erase P, t Q) * p P j)
      (D + ∑ Q, a Q) := by
    intro P j
    rw [← isWeightedHomogeneous_iff]
    by_cases hle : N • δ P.1 ≤ D
    · have h1 : IsWeightedHomogeneous (blockDeg (ι := ι)) (gc P) (D - N • δ P.1) := by
        simp only [gc, if_pos hle]
        exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
      have h2 := ((h1.mul ((isWeightedHomogeneous_iff.2 (hFδ P.1)).pow (N - n P))).mul
        (IsWeightedHomogeneous.prod (Finset.univ.erase P) t a fun Q _ => isWeightedHomogeneous_iff.2 (hta Q))).mul
        (isWeightedHomogeneous_iff.2 (hp P j))
      convert h2 using 1
      rw [← Finset.add_sum_erase Finset.univ a (Finset.mem_univ P)]
      funext q
      have e2 : (N - n P) * δ P.1 q + n P * δ P.1 q = N * δ P.1 q := by
        rw [← add_mul, Nat.sub_add_cancel (hnN P)]
      have hleq := hle q
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Finset.sum_apply] at hleq ⊢
      generalize (N - n P) * δ P.1 q = u₁ at e2 ⊢
      generalize n P * δ P.1 q = u₂ at e2 ⊢
      generalize N * δ P.1 q = u₃ at e2 hleq ⊢
      omega
    · have h0 : gc P = 0 := by simp only [gc, if_neg hle]
      rw [h0, zero_mul, zero_mul, zero_mul]
      exact isWeightedHomogeneous_zero (R := S) _ _
  let σ := Σ P : Tf I, Fin (r P)
  let e := Fintype.equivFin σ
  refine ⟨cellProd S I.1 ^ k * ∏ Q, t Q, D + ∑ Q, a Q, Fintype.card σ,
    fun j => gc (e.symm j).1 * F (e.symm j).1.1 ^ (N - n (e.symm j).1) *
      (∏ Q ∈ Finset.univ.erase (e.symm j).1, t Q) * p (e.symm j).1 (e.symm j).2,
    fun j => z (e.symm j).1 (e.symm j).2,
    Submonoid.mul_mem _ (Submonoid.pow_mem _ (cellProd_mem I.1) k) (Submonoid.prod_mem _ fun Q _ => ht Q),
    isWeightedHomogeneous_iff.1
      (hXk.mul (IsWeightedHomogeneous.prod _ _ _ fun Q _ => isWeightedHomogeneous_iff.2 (hta Q))),
    fun j => hq _ _, fun j => hz _ _, ?_⟩
  rw [heq]
  refine (Fintype.sum_sigma (fun s : σ => (gc s.1 * F s.1.1 ^ (N - n s.1) *
    (∏ Q ∈ Finset.univ.erase s.1, t Q) * p s.1 s.2) • z s.1 s.2 I)).symm.trans ?_
  exact (Equiv.sum_comp e.symm (fun s : σ => (gc s.1 * F s.1.1 ^ (N - n s.1) *
    (∏ Q ∈ Finset.univ.erase s.1, t Q) * p s.1 s.2) • z s.1 s.2 I)).symm

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
