import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ColonSpanSingletonEqOfNotMem
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PHilbExactDivide
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace HilbertIncrement

variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_sum, Nat.cast_mul, intWeight, unitDeg, blockWeight]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases h : k = v.1 <;> simp [h]`.
-/
theorem weight_intWeight (e : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (intWeight (ι := ι)) e =
      fun k => ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ) := by
  funext k
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Nat.cast_sum, Nat.cast_mul, intWeight, unitDeg, blockWeight]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : k = v.1 <;> simp [h]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h e he`. Use function extensionality and compare the values at `k`. Establish `e1 : ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ) = (a k : ℤ)`. Use `congrFun (h he) k` as an intermediate fact.

Rewrite `this` using `[weight_intWeight]`. Conclude with `this`. Conclude with `e1` after adjusting the coercions. Introduce `h e he`. Rewrite using `[weight_intWeight, h he]`.
-/
theorem isWeightedHomogeneous_intWeight_iff {f : MRing ι F} {a : K → ℕ} :
    IsWeightedHomogeneous (intWeight (ι := ι)) f (fun k => (a k : ℤ)) ↔
      IsWeightedHomogeneous (blockWeight ι) f a := by
  constructor
  · intro h e he
    funext k
    have e1 : ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ) = (a k : ℤ) := by
      have := congrFun (h he) k
      rw [weight_intWeight] at this
      exact this
    exact_mod_cast e1
  · intro h e he
    rw [weight_intWeight, h he]

/- English proof (translation)
Use extensionality with `f`. Simplify using `only [ringPiece, mem_weightedHomogeneousSubmodule]`. Conclude with `isWeightedHomogeneous_intWeight_iff`.
-/
theorem ringPiece_natCast (a : K → ℕ) :
    ringPiece (F := F) (ι := ι) (fun k => (a k : ℤ)) =
      weightedHomogeneousSubmodule F (blockWeight ι) a := by
  ext f
  simp only [ringPiece, mem_weightedHomogeneousSubmodule]
  exact isWeightedHomogeneous_intWeight_iff

/- English proof (translation)
Distinguish the cases in `hm : ∀ k, 0 ≤ m k`. Establish `e : weightedHomogeneousComponent (intWeight (ι` using `ι)) m f = weightedHomogeneousComponent (blockWeight ι) (fun k => (m k).toNat) f := by`. Use extensionality with `e`. Rewrite using `[coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent, weight_intWeight]`. Establish `hiff : ((fun k => ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ)) = m) ↔ Finsupp.weight (blockWeight ι) e = fun k => (m k).toNat`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use function extensionality and compare the values at `k`. Establish `e1 : ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ) = m k` using `congrFun h k`. Use `hm k` as an intermediate fact.

Use `show _ = (m k).toNat`. Use linear arithmetic over natural numbers and integers. Introduce `h`. Use function extensionality and compare the values at `k`. Establish `e1 : Finsupp.weight (blockWeight ι) e k = (m k).toNat` using `congrFun h k`.

Use `hm k` as an intermediate fact. Use `show ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ) = m k`. Use linear arithmetic over natural numbers and integers. Simplify using `only [hiff]`. Rewrite using `[e]`.

Conclude with `hJ f hf _`. Use `push Not at hm`. Take `⟨k, hk⟩` from `hm`. Establish `e : weightedHomogeneousComponent (intWeight (ι` using `ι)) m f = 0 := by`. Use extensionality with `e`.

Rewrite using `[coeff_weightedHomogeneousComponent, weight_intWeight, coeff_zero, if_neg]`. Introduce `h`. Establish `e1 : ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ) = m k` using `congrFun h k`. Use linear arithmetic over natural numbers and integers. Rewrite using `[e]`.

Conclude with `J.zero_mem`.
-/
theorem component_intWeight_mem {J : Ideal (MRing ι F)} (hJ : IsMultiHomogIdeal J)
    {f : MRing ι F} (hf : f ∈ J) (m : K → ℤ) :
    weightedHomogeneousComponent (intWeight (ι := ι)) m f ∈ J := by
  classical
  by_cases hm : ∀ k, 0 ≤ m k
  · have e : weightedHomogeneousComponent (intWeight (ι := ι)) m f =
        weightedHomogeneousComponent (blockWeight ι) (fun k => (m k).toNat) f := by
      ext e
      rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent, weight_intWeight]
      have hiff : ((fun k => ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ)) = m) ↔
          Finsupp.weight (blockWeight ι) e = fun k => (m k).toNat := by
        constructor
        · intro h
          funext k
          have e1 : ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ) = m k := congrFun h k
          have := hm k
          show _ = (m k).toNat
          omega
        · intro h
          funext k
          have e1 : Finsupp.weight (blockWeight ι) e k = (m k).toNat := congrFun h k
          have := hm k
          show ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ) = m k
          omega
      simp only [hiff]
    rw [e]
    exact hJ f hf _
  · push Not at hm
    obtain ⟨k, hk⟩ := hm
    have e : weightedHomogeneousComponent (intWeight (ι := ι)) m f = 0 := by
      ext e
      rw [coeff_weightedHomogeneousComponent, weight_intWeight, coeff_zero, if_neg]
      intro h
      have e1 : ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ) = m k := congrFun h k
      omega
    rw [e]
    exact J.zero_mem

/- English proof (translation)
Introduce `f hf n`. Take `⟨p, hp, y, hy, rfl⟩` from `Submodule.mem_sup.mp hf`. Take `⟨t, rfl⟩` from `Ideal.mem_span_singleton'.mp hy`. Establish `hX : IsMultiHomog (X v : MRing ι F) (blockWeight ι v)` using `isWeightedHomogeneous_X F (blockWeight ι) v`. Rewrite using `[map_add, GroundTheory.Heights₂.Heights.FieldNumbers.HilbExactDivide.component_mul_form hX t n]`.

Use `Ideal.add_mem _ (Ideal.mem_sup_left (hq p hp n)) ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `Ideal.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩)`. Conclude with `zero_mem _`.
-/
theorem isMultiHomogIdeal_sup_X {q : Ideal (MRing ι F)} (hq : IsMultiHomogIdeal q)
    (v : Σ k, ι k) : IsMultiHomogIdeal (q ⊔ Ideal.span {(X v : MRing ι F)}) := by
  classical
  intro f hf n
  obtain ⟨p, hp, y, hy, rfl⟩ := Submodule.mem_sup.mp hf
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  have hX : IsMultiHomog (X v : MRing ι F) (blockWeight ι v) :=
    isWeightedHomogeneous_X F (blockWeight ι) v
  rw [map_add, GroundTheory.Heights₂.Heights.FieldNumbers.HilbExactDivide.component_mul_form hX t n]
  refine Ideal.add_mem _ (Ideal.mem_sup_left (hq p hp n)) ?_
  split_ifs
  · exact Ideal.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩)
  · exact zero_mem _

def quotPiece (J : Ideal (MRing ι F)) (m : K → ℤ) : Submodule F (MRing ι F ⧸ J) :=
  (ringPiece m).map (Ideal.Quotient.mkₐ F J).toLinearMap

/- English proof (translation)
Rewrite using `[quotPiece, gradedPiece, ringPiece_natCast]`.
-/
theorem quotPiece_natCast (J : Ideal (MRing ι F)) (a : K → ℕ) :
    quotPiece J (fun k => (a k : ℤ)) = gradedPiece J a := by
  rw [quotPiece, gradedPiece, ringPiece_natCast]

/- English proof (translation)
Rewrite using `[DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]`. Introduce `s v hv hsum m hm`. Establish `hex : ∀ i ∈ s, ∃ y ∈ ringPiece (F` using `F) (ι := ι) i, (Ideal.Quotient.mkₐ F J).toLinearMap y = v i := fun i hi => Submodule.mem_map.mp (hv i hi)`.

Use `choose! x hx hxv using hex`. Establish `hy : (∑ i ∈ s, x i) ∈ J`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sum]`. Rewrite using `[← hsum]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations.

Rewrite using `[← hxv i hi]`. Both sides reduce to the same expression. Establish `hc` using `component_intWeight_mem hJ hy m`. Rewrite `hc` using `[map_sum]`. Establish `hcs : (∑ i ∈ s, weightedHomogeneousComponent (intWeight (ι` using `ι)) m (x i)) = x m := by`.

Rewrite using `[Finset.sum_eq_single m]`. Rewrite using `[weightedHomogeneousComponent_of_mem (hx m hm), if_pos rfl]`. Introduce `j hj hjm`. Rewrite using `[weightedHomogeneousComponent_of_mem (hx j hj), if_neg (Ne.symm hjm)]`. Introduce `h`.

Conclude with `absurd hm h`. Rewrite `hc` using `[hcs]`. Rewrite using `[← hxv m hm]`. Simplify `hc` using `[Ideal.Quotient.eq_zero_iff_mem]`. Use `show (⨆ m, (ringPiece (F := F) (ι := ι) m).map (Ideal.Quotient.mkₐ F J).toLinearMap) = ⊤`.

Rewrite using `[← Submodule.map_iSup]`. Use `show Submodule.map _ (⨆ i, weightedHomogeneousSubmodule F (intWeight (ι := ι)) i) = ⊤`. Rewrite using `[(weightedDecomposition F (intWeight (ι := ι))).isInternal.submodule_iSup_eq_top, Submodule.map_top, LinearMap.range_eq_top]`. Conclude with `Ideal.Quotient.mkₐ_surjective F J`. Use `smul_mem := by`.

Introduce `v m x hx`. Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.mp hx`. Use `Submodule.mem_map.mpr ⟨(X v : MRing ι F) • y, isMultigrading_ring.smul_mem v m y hy, ?_⟩` and prove the remaining obligations. Simplify using `only [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, smul_eq_mul, map_mul]`. Both sides reduce to the same expression.
-/
theorem isMultigrading_quotPiece [Fintype K] {J : Ideal (MRing ι F)} (hJ : IsMultiHomogIdeal J) :
    IsMultigrading ι (MRing ι F ⧸ J) (quotPiece J) where
  internal := by
    classical
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    constructor
    · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
      intro s v hv hsum m hm
      have hex : ∀ i ∈ s, ∃ y ∈ ringPiece (F := F) (ι := ι) i,
          (Ideal.Quotient.mkₐ F J).toLinearMap y = v i := fun i hi => Submodule.mem_map.mp (hv i hi)
      choose! x hx hxv using hex
      have hy : (∑ i ∈ s, x i) ∈ J := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
        rw [← hsum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [← hxv i hi]
        rfl
      have hc := component_intWeight_mem hJ hy m
      rw [map_sum] at hc
      have hcs : (∑ i ∈ s, weightedHomogeneousComponent (intWeight (ι := ι)) m (x i)) = x m := by
        rw [Finset.sum_eq_single m]
        · rw [weightedHomogeneousComponent_of_mem (hx m hm), if_pos rfl]
        · intro j hj hjm
          rw [weightedHomogeneousComponent_of_mem (hx j hj), if_neg (Ne.symm hjm)]
        · intro h
          exact absurd hm h
      rw [hcs] at hc
      rw [← hxv m hm]
      simpa [Ideal.Quotient.eq_zero_iff_mem] using hc
    · show (⨆ m, (ringPiece (F := F) (ι := ι) m).map (Ideal.Quotient.mkₐ F J).toLinearMap) = ⊤
      rw [← Submodule.map_iSup]
      show Submodule.map _ (⨆ i, weightedHomogeneousSubmodule F (intWeight (ι := ι)) i) = ⊤
      rw [(weightedDecomposition F (intWeight (ι := ι))).isInternal.submodule_iSup_eq_top,
        Submodule.map_top, LinearMap.range_eq_top]
      exact Ideal.Quotient.mkₐ_surjective F J
  smul_mem := by
    intro v m x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    refine Submodule.mem_map.mpr ⟨(X v : MRing ι F) • y, isMultigrading_ring.smul_mem v m y hy, ?_⟩
    simp only [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, smul_eq_mul, map_mul]
    rfl

/- English proof (translation)
Introduce `d hmod F _ K _ _ ι _ q hq hdim b`. Take `⟨i, hi⟩` from `hq.relevant b`. Establish `hJ : IsMultiHomogIdeal (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)})` using `isMultiHomogIdeal_sup_X hq.multiHomog ⟨b, i⟩`. Take `⟨hstep, hsupp⟩` from `GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.HilbertIncrement.closed.{u} F K ι (d + 1) q b i hq hdim (by omega) hi`. Take `⟨a₀, C, hbd⟩` from `hmod F K ι (MRing ι F ⧸ (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)})) (quotPiece _) (isMultigrading_quotPiece hJ) (fun W hW hann => by`.

Rewrite `hann` using `[Ideal.annihilator_quotient]`. Simplify using `using hsupp W hW hann)`. Use `⟨a₀, C, fun a ha => ?_⟩` and prove the remaining obligations. Establish `h1 : hilbFn q (fun k => (a k : ℤ)) - hilbFn q ((fun k => (a k : ℤ)) - unitDeg b) = (Module.finrank F (quotPiece (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)}) fun k => (a k : ℤ)) : ℤ)`. Rewrite using `[show unitDeg b = Pi.single b 1 from rfl, hstep, hilbFn, if_pos (fun k => Nat.cast_nonneg _), quotPiece_natCast]`.

Establish `ha' : (fun k => ((a k : ℤ)).toNat) = a` using `funext fun k => by omega`. Rewrite using `[ha']`. Establish `h2 : intNum F q (Matrix.vecCons (unitDeg b) fun _ : Fin d => fun k => (a k : ℤ)) = topCycleNum F ι (MRing ι F ⧸ (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)})) d (fun _ => fun k => (a k : ℤ))`. Rewrite using `[hrec F K ι q d hq hdim b i hi]`. Unfold `topCycleNum`.

Use `finsum_congr fun W => ?_` and prove the remaining obligations. Establish `hann : Module.annihilator (MRing ι F) (MRing ι F ⧸ (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)})) = q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)}` using `Ideal.annihilator_quotient`. Distinguish the cases in `hc : IsMultiProjPrime W ∧ q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)} ≤ W ∧ ringKrullDim (MRing ι F ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)`. Rewrite using `[dif_pos hc, dif_pos (by rw [hann]; exact hc)]`. Both sides reduce to the same expression.

Rewrite using `[dif_neg hc, dif_neg (by rw [hann]; exact hc)]`. Rewrite using `[h1, h2]`. Simplify using `using hbd a ha`.
-/
theorem proof (hrec : IntersectionRecursion.Statement.{u}) : HilbertIncrement.Statement.{u} := by
  intro d hmod F _ K _ _ ι _ q hq hdim b
  obtain ⟨i, hi⟩ := hq.relevant b
  have hJ : IsMultiHomogIdeal (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)}) :=
    isMultiHomogIdeal_sup_X hq.multiHomog ⟨b, i⟩
  obtain ⟨hstep, hsupp⟩ :=
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.HilbertIncrement.closed.{u} F K ι (d + 1) q b i hq
      hdim (by omega) hi
  obtain ⟨a₀, C, hbd⟩ := hmod F K ι (MRing ι F ⧸ (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)}))
    (quotPiece _) (isMultigrading_quotPiece hJ) (fun W hW hann => by
      rw [Ideal.annihilator_quotient] at hann
      simpa using hsupp W hW hann)
  refine ⟨a₀, C, fun a ha => ?_⟩
  have h1 : hilbFn q (fun k => (a k : ℤ)) - hilbFn q ((fun k => (a k : ℤ)) - unitDeg b) =
      (Module.finrank F (quotPiece (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)})
        fun k => (a k : ℤ)) : ℤ) := by
    rw [show unitDeg b = Pi.single b 1 from rfl, hstep, hilbFn,
      if_pos (fun k => Nat.cast_nonneg _), quotPiece_natCast]
    have ha' : (fun k => ((a k : ℤ)).toNat) = a := funext fun k => by omega
    rw [ha']
  have h2 : intNum F q (Matrix.vecCons (unitDeg b) fun _ : Fin d => fun k => (a k : ℤ)) =
      topCycleNum F ι (MRing ι F ⧸ (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)})) d
        (fun _ => fun k => (a k : ℤ)) := by
    rw [hrec F K ι q d hq hdim b i hi]
    unfold topCycleNum
    refine finsum_congr fun W => ?_
    have hann : Module.annihilator (MRing ι F)
        (MRing ι F ⧸ (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)})) =
        q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)} := Ideal.annihilator_quotient
    by_cases hc : IsMultiProjPrime W ∧ q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)} ≤ W ∧
        ringKrullDim (MRing ι F ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)
    · rw [dif_pos hc, dif_pos (by rw [hann]; exact hc)]
      rfl
    · rw [dif_neg hc, dif_neg (by rw [hann]; exact hc)]
  rw [h1, h2]
  simpa using hbd a ha

end HilbertIncrement

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
