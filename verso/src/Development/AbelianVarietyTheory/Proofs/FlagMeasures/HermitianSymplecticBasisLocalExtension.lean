import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerIsometry
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfQuad
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationAdditiveQuadraticExtensionStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemCoord
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmulIntegral
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory.HL.SAN

noncomputable section
namespace GlobalTheory.HL.EichlerParams

section Local
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
variable {R : Type} [CommRing R] [Algebra K R] [TopologicalSpace R]

def Sm (L : LocE K R) (γ : K) (x : R) : Prop := ∃ o ∈ L.O, x = algebraMap K R γ * o

variable (L : LocE K R)

/- English proof (translation)
The claim follows from `(GlobalTheory.UnramOrder.algebraMap_mem_iff L k).2 hk`.
-/
theorem algO {k : K} (hk : k ∈ 𝒪[K]) : algebraMap K R k ∈ L.O :=
  (GlobalTheory.UnramOrder.algebraMap_mem_iff L k).2 hk

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, L.O.zero_mem, by simp⟩`.
-/
theorem sm_zero (γ : K) : Sm L γ 0 := ⟨0, L.O.zero_mem, by simp⟩

/- English proof (translation)
Take `⟨o, ho, rfl⟩` from `hx`. Take `⟨o', ho', rfl⟩` from `hy`. Conclude with `⟨o + o', L.O.add_mem ho ho', by ring⟩`.
-/
theorem sm_add {γ : K} {x y : R} (hx : Sm L γ x) (hy : Sm L γ y) : Sm L γ (x + y) := by
  obtain ⟨o, ho, rfl⟩ := hx; obtain ⟨o', ho', rfl⟩ := hy
  exact ⟨o + o', L.O.add_mem ho ho', by ring⟩

/- English proof (translation)
Take `⟨o, ho, rfl⟩` from `hx`. Conclude with `⟨-o, L.O.neg_mem ho, by ring⟩`.
-/
theorem sm_neg {γ : K} {x : R} (hx : Sm L γ x) : Sm L γ (-x) := by
  obtain ⟨o, ho, rfl⟩ := hx
  exact ⟨-o, L.O.neg_mem ho, by ring⟩

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `sm_add L hx (sm_neg L hy)`.
-/
theorem sm_sub {γ : K} {x y : R} (hx : Sm L γ x) (hy : Sm L γ y) : Sm L γ (x - y) := by
  rw [sub_eq_add_neg]; exact sm_add L hx (sm_neg L hy)

/- English proof (translation)
Take `⟨o, ho, rfl⟩` from `hx`. Take `⟨o', ho', rfl⟩` from `hy`. Conclude with `⟨o * o', L.O.mul_mem ho ho', by rw [map_mul]; ring⟩`.
-/
theorem sm_mul {a b : K} {x y : R} (hx : Sm L a x) (hy : Sm L b y) : Sm L (a * b) (x * y) := by
  obtain ⟨o, ho, rfl⟩ := hx; obtain ⟨o', ho', rfl⟩ := hy
  exact ⟨o * o', L.O.mul_mem ho ho', by rw [map_mul]; ring⟩

/- English proof (translation)
Take `⟨o, ho, rfl⟩` from `hx`. Conclude with `⟨L.cj o, GlobalTheory.UnramOrder.cj_mem L ho, by rw [map_mul, AlgEquiv.commutes]⟩`.
-/
theorem sm_cj {a : K} {x : R} (hx : Sm L a x) : Sm L a (L.cj x) := by
  obtain ⟨o, ho, rfl⟩ := hx
  exact ⟨L.cj o, GlobalTheory.UnramOrder.cj_mem L ho, by rw [map_mul, AlgEquiv.commutes]⟩

/- English proof (translation)
Take `⟨o, ho, rfl⟩` from `hx`. Conclude with `⟨algebraMap K R k * o, L.O.mul_mem (algO L hk) ho, by rw [h, map_mul]; ring⟩`.
-/
theorem sm_of_eq {a b k : K} {x : R} (hx : Sm L a x) (h : a = b * k) (hk : k ∈ 𝒪[K]) : Sm L b x := by
  obtain ⟨o, ho, rfl⟩ := hx
  exact ⟨algebraMap K R k * o, L.O.mul_mem (algO L hk) ho, by rw [h, map_mul]; ring⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using sm_zero L γ`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `sm_add L (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem sm_sum {ι : Type} (s : Finset ι) {γ : K} (f : ι → R) (h : ∀ i ∈ s, Sm L γ (f i)) :
    Sm L γ (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using sm_zero L γ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact sm_add L (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨o, ho, rfl⟩`. Simplify using `using ho`. Introduce `h; exact ⟨x, h, by simp⟩`.
-/
theorem sm_one {x : R} : Sm L 1 x ↔ x ∈ L.O := by
  constructor
  · rintro ⟨o, ho, rfl⟩; simpa using ho
  · intro h; exact ⟨x, h, by simp⟩

/- English proof (translation)
The claim follows from `(sm_one L).1 (sm_of_eq L hx (one_mul γ).symm hγ)`.
-/
theorem mem_of_sm {γ : K} {x : R} (hx : Sm L γ x) (hγ : γ ∈ 𝒪[K]) : x ∈ L.O :=
  (sm_one L).1 (sm_of_eq L hx (one_mul γ).symm hγ)

/- English proof (translation)
The claim follows from `sm_sum L _ _ fun i _ => sm_sum L _ _ fun j _ => sm_mul L (sm_mul L (hx i) (hH i j)) (sm_cj L (hy j))`.
-/
theorem hf_sm {N : ℕ} {a b c : K} {Hm : Matrix (Fin N) (Fin N) R} {x y : Fin N → R}
    (hx : ∀ i, Sm L a (x i)) (hH : ∀ i j, Sm L b (Hm i j)) (hy : ∀ j, Sm L c (y j)) :
    Sm L (a * b * c) (hf L Hm x y) :=
  sm_sum L _ _ fun i _ => sm_sum L _ _ fun j _ => sm_mul L (sm_mul L (hx i) (hH i j)) (sm_cj L (hy j))

/- English proof (translation)
Simplify using `[hf, add_mul, Finset.sum_add_distrib]`.
-/
theorem hf_add_l {N : ℕ} (Hm : Matrix (Fin N) (Fin N) R) (a b y : Fin N → R) :
    hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[hf, mul_add, Finset.sum_add_distrib]`.
-/
theorem hf_add_r {N : ℕ} (Hm : Matrix (Fin N) (Fin N) R) (a b y : Fin N → R) :
    hf L Hm y (a + b) = hf L Hm y a + hf L Hm y b := by
  simp [hf, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[hf, sub_mul, Finset.sum_sub_distrib]`.
-/
theorem hf_sub_l {N : ℕ} (Hm : Matrix (Fin N) (Fin N) R) (a b y : Fin N → R) :
    hf L Hm (a - b) y = hf L Hm a y - hf L Hm b y := by
  simp [hf, sub_mul, Finset.sum_sub_distrib]

/- English proof (translation)
Take `⟨t, ht⟩` from `(L.cj_fix (x + L.cj x)).1 (by rw [map_add, L.cj_cj, add_comm])`. Take `⟨n, hn⟩` from `(L.cj_fix (x * L.cj x)).1 (by rw [map_mul, L.cj_cj, mul_comm])`. Establish `key : ∀ k : K, ∃ c ∈ 𝒪[K], c ≠ 0 ∧ c * k ∈ 𝒪[K]`. Introduce `k`. Break down `(ValuativeRel.valuation K).valuationSubring.mem_or_inv_mem k with h | h` into its components or cases.

Conclude with `⟨1, (𝒪[K]).one_mem, one_ne_zero, by rw [one_mul]; exact h⟩`. Distinguish the cases in `hk : k = 0`. Conclude with `⟨1, (𝒪[K]).one_mem, one_ne_zero, by simp [hk]⟩`. Conclude with `⟨k⁻¹, h, inv_ne_zero hk, by rw [inv_mul_cancel₀ hk]; exact (𝒪[K]).one_mem⟩`. Take `⟨c1, hc1, hc10, ht1⟩` from `key t`.

Take `⟨c2, hc2, hc20, hn2⟩` from `key n`. Use `⟨c1 * c2, (𝒪[K]).mul_mem hc1 hc2, mul_ne_zero hc10 hc20, ?_⟩` and prove the remaining obligations. Establish `hI : algebraMap K R (c1 * c2) * x ∈ L.O`. Rewrite using `[L.O_def]`. Establish `htr : algebraMap K R (c2 * (c1 * t)) = algebraMap K R (c1 * c2) * x + L.cj (algebraMap K R (c1 * c2) * x)`.

Rewrite using `[map_mul L.cj, AlgEquiv.commutes, ← mul_add, ← ht]`. Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hnr : algebraMap K R ((c1 * c1 * c2) * (c2 * n)) = algebraMap K R (c1 * c2) * x * L.cj (algebraMap K R (c1 * c2) * x)`. Rewrite using `[map_mul L.cj, AlgEquiv.commutes]`.

Establish `: algebraMap K R (c1 * c2) * x * (algebraMap K R (c1 * c2) * L.cj x) = algebraMap K R (c1 * c2) * algebraMap K R (c1 * c2) * (x * L.cj x)` using `by ring`. Rewrite using `[this, ← hn]`. Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `GlobalTheory.HL.PlacesInt.isIntegral_of_quad (R := 𝒪[K]) _ _ ⟨_, (𝒪[K]).mul_mem hc2 ht1⟩ ⟨_, (𝒪[K]).mul_mem ((𝒪[K]).mul_mem ((𝒪[K]).mul_mem hc1 hc1) hc2) hn2⟩ htr hnr`.

Use `⟨_, hI, ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← map_mul, inv_mul_cancel₀ (mul_ne_zero hc10 hc20), map_one, one_mul]`.
-/
theorem exists_bound1 (x : R) : ∃ e ∈ 𝒪[K], e ≠ 0 ∧ Sm L e⁻¹ x := by
  obtain ⟨t, ht⟩ := (L.cj_fix (x + L.cj x)).1 (by rw [map_add, L.cj_cj, add_comm])
  obtain ⟨n, hn⟩ := (L.cj_fix (x * L.cj x)).1 (by rw [map_mul, L.cj_cj, mul_comm])
  have key : ∀ k : K, ∃ c ∈ 𝒪[K], c ≠ 0 ∧ c * k ∈ 𝒪[K] := by
    intro k
    rcases (ValuativeRel.valuation K).valuationSubring.mem_or_inv_mem k with h | h
    · exact ⟨1, (𝒪[K]).one_mem, one_ne_zero, by rw [one_mul]; exact h⟩
    · by_cases hk : k = 0
      · exact ⟨1, (𝒪[K]).one_mem, one_ne_zero, by simp [hk]⟩
      · exact ⟨k⁻¹, h, inv_ne_zero hk, by rw [inv_mul_cancel₀ hk]; exact (𝒪[K]).one_mem⟩
  obtain ⟨c1, hc1, hc10, ht1⟩ := key t
  obtain ⟨c2, hc2, hc20, hn2⟩ := key n
  refine ⟨c1 * c2, (𝒪[K]).mul_mem hc1 hc2, mul_ne_zero hc10 hc20, ?_⟩
  have hI : algebraMap K R (c1 * c2) * x ∈ L.O := by
    rw [L.O_def]
    have htr : algebraMap K R (c2 * (c1 * t)) = algebraMap K R (c1 * c2) * x +
        L.cj (algebraMap K R (c1 * c2) * x) := by
      rw [map_mul L.cj, AlgEquiv.commutes, ← mul_add, ← ht]; simp only [map_mul]; ring
    have hnr : algebraMap K R ((c1 * c1 * c2) * (c2 * n)) = algebraMap K R (c1 * c2) * x *
        L.cj (algebraMap K R (c1 * c2) * x) := by
      rw [map_mul L.cj, AlgEquiv.commutes]
      have : algebraMap K R (c1 * c2) * x * (algebraMap K R (c1 * c2) * L.cj x) =
        algebraMap K R (c1 * c2) * algebraMap K R (c1 * c2) * (x * L.cj x) := by ring
      rw [this, ← hn]; simp only [map_mul]; ring
    exact GlobalTheory.HL.PlacesInt.isIntegral_of_quad (R := 𝒪[K]) _ _
      ⟨_, (𝒪[K]).mul_mem hc2 ht1⟩ ⟨_, (𝒪[K]).mul_mem ((𝒪[K]).mul_mem ((𝒪[K]).mul_mem hc1 hc1) hc2) hn2⟩ htr hnr
  refine ⟨_, hI, ?_⟩
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (mul_ne_zero hc10 hc20), map_one, one_mul]

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.SmulIntegralDenominator.main`. Consider the case `exact _root_.GlobalTheory.SmulIntegralDenominator.main`. Consider the case `(apply _root_.GlobalTheory.SmulIntegralDenominator.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.SmulIntegralDenominator.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.SmulIntegralDenominator.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.SmulIntegralDenominator.main ..)`.
-/
theorem exists_bound {ι : Type} [Fintype ι] (f : ι → R) : ∃ e ∈ 𝒪[K], e ≠ 0 ∧ ∀ i, Sm L e⁻¹ (f i) := by
  first
  | exact @_root_.GlobalTheory.SmulIntegralDenominator.main
  | exact _root_.GlobalTheory.SmulIntegralDenominator.main
  | (apply _root_.GlobalTheory.SmulIntegralDenominator.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SmulIntegralDenominator.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SmulIntegralDenominator.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SmulIntegralDenominator.main ..)

def piL {N r : ℕ} (Hm : Matrix (Fin N) (Fin N) R) (X Y : Fin r → Fin N → R) (T : Finset (Fin r))
    (v : Fin N → R) : Fin N → R :=
  fun j => v j - ∑ a ∈ T, (hf L Hm v (Y a) * X a j + hf L Hm v (X a) * Y a j)

/- English proof (translation)
Establish `h2 : (2 : K) ∈ 𝒪[K]` using `by simpa using (𝒪[K]).natCast_mem 2`. Establish `hv' : ∀ a ∈ T, hf L Hm v (Y a) = hf L Hm (v - up) (Y a) ∧ hf L Hm v (X a) = hf L Hm (v - up) (X a)`. Introduce `a ha`. Rewrite using `[hf_sub_l, hf_sub_l, (horth a ha).1, (horth a ha).2, sub_zero, sub_zero]`. Conclude with `⟨rfl, rfl⟩`.

Establish `hmv : ∀ j, Sm L (2 * d' * e ^ 5) ((v - up) j)` using `fun j => by simpa using hv j`. Establish `hm' : ∀ j, Sm L (2 * d' * e ^ 2) (piL L Hm X Y T v j - up j)`. Introduce `j`. Establish `e1 : piL L Hm X Y T v j - up j = (v j - up j) - ∑ a ∈ T, (hf L Hm (v - up) (Y a) * X a j + hf L Hm (v - up) (X a) * Y a j)`. Simplify using `only [piL]`.

Rewrite using `[Finset.sum_congr rfl (fun a ha => by rw [(hv' a ha).1, (hv' a ha).2])]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Use `sm_sub L (sm_of_eq L (hv j) (by ring) (pow_mem he 3)) (sm_sum L _ _ fun a _ => ?_)` and prove the remaining obligations. Establish `hk : 2 * d' * e ^ 5 * e⁻¹ * e⁻¹ * e⁻¹ = 2 * d' * e ^ 2 * 1` using `by field_simp`.

Conclude with `sm_add L (sm_of_eq L (sm_mul L (hf_sm L hmv bH (bY a)) (bX a j)) hk (𝒪[K]).one_mem) (sm_of_eq L (sm_mul L (hf_sm L hmv bH (bX a)) (bY a j)) hk (𝒪[K]).one_mem)`. Use `⟨fun j => sm_of_eq L (hm' j) (by ring) (pow_mem he 2), ?_⟩` and prove the remaining obligations. Use `set m' : Fin N → R := fun j => piL L Hm X Y T v j - up j with hm'def`. Establish `hpv : piL L Hm X Y T v = up + m'` using `by funext j; simp [m']`. Establish `hm'' : ∀ j, Sm L (2 * d' * e ^ 2) (m' j)` using `hm'`.

Rewrite using `[hpv, hf_add_l, hf_add_r, hf_add_r]`. Establish `e2 : hf L Hm up up + hf L Hm up m' + (hf L Hm m' up + hf L Hm m' m') - hf L Hm up up = hf L Hm up m' + hf L Hm m' up + hf L Hm m' m'` using `by ring`. Rewrite using `[e2]`. Use `sm_add L (sm_add L ?_ ?_) ?_` and prove the remaining obligations. Conclude with `sm_of_eq L (hf_sm L bu bH hm'') (by field_simp) (𝒪[K]).one_mem`.

Conclude with `sm_of_eq L (hf_sm L hm'' bH bu) (by field_simp) (𝒪[K]).one_mem`. Conclude with `sm_of_eq L (hf_sm L hm'' bH hm'') (by field_simp) ((𝒪[K]).mul_mem ((𝒪[K]).mul_mem h2 hd') (pow_mem he 3))`.
-/
theorem local_choice {N r : ℕ} (Hm : Matrix (Fin N) (Fin N) R) (X Y : Fin r → Fin N → R)
    (T : Finset (Fin r)) (up : Fin N → R)
    (horth : ∀ a ∈ T, hf L Hm up (X a) = 0 ∧ hf L Hm up (Y a) = 0)
    {e d' : K} (he : e ∈ 𝒪[K]) (he0 : e ≠ 0) (hd' : d' ∈ 𝒪[K])
    (bH : ∀ i j, Sm L e⁻¹ (Hm i j)) (bX : ∀ a j, Sm L e⁻¹ (X a j)) (bY : ∀ a j, Sm L e⁻¹ (Y a j))
    (bu : ∀ j, Sm L e⁻¹ (up j)) (v : Fin N → R) (hv : ∀ j, Sm L (2 * d' * e ^ 5) (v j - up j)) :
    (∀ j, Sm L (2 * d') (piL L Hm X Y T v j - up j)) ∧
      Sm L (2 * d') (hf L Hm (piL L Hm X Y T v) (piL L Hm X Y T v) - hf L Hm up up) := by
  have h2 : (2 : K) ∈ 𝒪[K] := by simpa using (𝒪[K]).natCast_mem 2
  have hv' : ∀ a ∈ T, hf L Hm v (Y a) = hf L Hm (v - up) (Y a) ∧
      hf L Hm v (X a) = hf L Hm (v - up) (X a) := by
    intro a ha
    rw [hf_sub_l, hf_sub_l, (horth a ha).1, (horth a ha).2, sub_zero, sub_zero]
    exact ⟨rfl, rfl⟩
  have hmv : ∀ j, Sm L (2 * d' * e ^ 5) ((v - up) j) := fun j => by simpa using hv j
  have hm' : ∀ j, Sm L (2 * d' * e ^ 2) (piL L Hm X Y T v j - up j) := by
    intro j
    have e1 : piL L Hm X Y T v j - up j = (v j - up j) -
        ∑ a ∈ T, (hf L Hm (v - up) (Y a) * X a j + hf L Hm (v - up) (X a) * Y a j) := by
      simp only [piL]
      rw [Finset.sum_congr rfl (fun a ha => by rw [(hv' a ha).1, (hv' a ha).2])]
      ring
    rw [e1]
    refine sm_sub L (sm_of_eq L (hv j) (by ring) (pow_mem he 3)) (sm_sum L _ _ fun a _ => ?_)
    have hk : 2 * d' * e ^ 5 * e⁻¹ * e⁻¹ * e⁻¹ = 2 * d' * e ^ 2 * 1 := by field_simp
    exact sm_add L
      (sm_of_eq L (sm_mul L (hf_sm L hmv bH (bY a)) (bX a j)) hk (𝒪[K]).one_mem)
      (sm_of_eq L (sm_mul L (hf_sm L hmv bH (bX a)) (bY a j)) hk (𝒪[K]).one_mem)
  refine ⟨fun j => sm_of_eq L (hm' j) (by ring) (pow_mem he 2), ?_⟩
  set m' : Fin N → R := fun j => piL L Hm X Y T v j - up j with hm'def
  have hpv : piL L Hm X Y T v = up + m' := by funext j; simp [m']
  have hm'' : ∀ j, Sm L (2 * d' * e ^ 2) (m' j) := hm'
  rw [hpv, hf_add_l, hf_add_r, hf_add_r]
  have e2 : hf L Hm up up + hf L Hm up m' + (hf L Hm m' up + hf L Hm m' m') - hf L Hm up up =
      hf L Hm up m' + hf L Hm m' up + hf L Hm m' m' := by ring
  rw [e2]
  refine sm_add L (sm_add L ?_ ?_) ?_
  · exact sm_of_eq L (hf_sm L bu bH hm'') (by field_simp) (𝒪[K]).one_mem
  · exact sm_of_eq L (hf_sm L hm'' bH bu) (by field_simp) (𝒪[K]).one_mem
  · exact sm_of_eq L (hf_sm L hm'' bH hm'') (by field_simp)
      ((𝒪[K]).mul_mem ((𝒪[K]).mul_mem h2 hd') (pow_mem he 3))

end Local

section Global
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

/- English proof (translation)
Take `⟨p⟩` from `exists_place F`. Use `haveI := GlobalTheory.HL.PlacesInt.nontrivial_Ep (A.loc p)`. Apply `(A.loc p).ιE.injective` to reduce the goal to its premises. Rewrite using `[← (A.loc p).cj_ιE, ← (A.loc p).cj_ιE, ← A.L_cj, (A.L p).cj_cj]`.
-/
theorem sig_sig (A : Places F E sig) (y : E) : sig (sig y) = y := by
  obtain ⟨p⟩ := exists_place F
  haveI := GlobalTheory.HL.PlacesInt.nontrivial_Ep (A.loc p)
  apply (A.loc p).ιE.injective
  rw [← (A.loc p).cj_ιE, ← (A.loc p).cj_ιE, ← A.L_cj, (A.L p).cj_cj]

/- English proof (translation)
Simplify using `only [hq, map_sum, map_mul, sig_sig A]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hH]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hq_swap (A : Places F E sig) {N : ℕ} (Hm : Matrix (Fin N) (Fin N) E)
    (hH : ∀ i j, sig (Hm j i) = Hm i j) (x y : Fin N → E) : sig (hq sig Hm x y) = hq sig Hm y x := by
  simp only [hq, map_sum, map_mul, sig_sig A]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hH]
  ring

/- English proof (translation)
Simplify using `[hq, sub_mul, Finset.sum_sub_distrib]`.
-/
theorem hq_sub_l {N : ℕ} (Hm : Matrix (Fin N) (Fin N) E) (a b y : Fin N → E) :
    hq sig Hm (a - b) y = hq sig Hm a y - hq sig Hm b y := by
  simp [hq, sub_mul, Finset.sum_sub_distrib]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [hq]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hq_add_l, ih]`.
-/
theorem hq_sum_l {N : ℕ} (Hm : Matrix (Fin N) (Fin N) E) {ι : Type} (s : Finset ι) (f : ι → Fin N → E)
    (y : Fin N → E) : hq sig Hm (∑ a ∈ s, f a) y = ∑ a ∈ s, hq sig Hm (f a) y := by
  induction s using Finset.induction_on with
  | empty => simp [hq]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hq_add_l, ih]

def piQ (sig : E →ₐ[F] E) {N r : ℕ} (Hm : Matrix (Fin N) (Fin N) E) (X Y : Fin r → Fin N → E)
    (T : Finset (Fin r)) (w : Fin N → E) : Fin N → E :=
  fun j => w j - ∑ a ∈ T, (hq sig Hm w (Y a) * X a j + hq sig Hm w (X a) * Y a j)

/- English proof (translation)
Establish `e : piQ sig Hm X Y T w = w - ∑ a ∈ T, (hq sig Hm w (Y a) • X a + hq sig Hm w (X a) • Y a)`. Use function extensionality and compare the values at `j`. Simplify using `[piQ, Finset.sum_apply]`. Rewrite using `[e, hq_sub_l, hq_sum_l]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[hq_add_l, hq_smul_l, hq_smul_l]`.
-/
theorem hq_piQ {N r : ℕ} (Hm : Matrix (Fin N) (Fin N) E) (X Y : Fin r → Fin N → E)
    (T : Finset (Fin r)) (w z : Fin N → E) :
    hq sig Hm (piQ sig Hm X Y T w) z = hq sig Hm w z -
      ∑ a ∈ T, (hq sig Hm w (Y a) * hq sig Hm (X a) z + hq sig Hm w (X a) * hq sig Hm (Y a) z) := by
  have e : piQ sig Hm X Y T w = w - ∑ a ∈ T, (hq sig Hm w (Y a) • X a + hq sig Hm w (X a) • Y a) := by
    funext j; simp [piQ, Finset.sum_apply]
  rw [e, hq_sub_l, hq_sum_l]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hq_add_l, hq_smul_l, hq_smul_l]

/- English proof (translation)
Establish `h5 : ∀ x y : Fin N → E, (A.loc p).ιE (hq sig Hm x y) = hf (A.L p) (Hm.map (A.loc p).ιE) (A.bc p x) (A.bc p y)` using `fun x y => ((GlobalTheory.HL.RatExt.rational_extend A N p).2.2.2.2.1 Hm x y).symm`. Use function extensionality and compare the values at `j`. Simplify using `only [piQ, piL, Places.bc, map_sub, map_sum, map_add, map_mul, h5]`.
-/
theorem bc_piQ (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {N r : ℕ}
    (Hm : Matrix (Fin N) (Fin N) E) (X Y : Fin r → Fin N → E) (T : Finset (Fin r)) (w : Fin N → E) :
    A.bc p (piQ sig Hm X Y T w) = piL (A.L p) (Hm.map (A.loc p).ιE) (fun a => A.bc p (X a))
      (fun a => A.bc p (Y a)) T (A.bc p w) := by
  have h5 : ∀ x y : Fin N → E, (A.loc p).ιE (hq sig Hm x y) =
      hf (A.L p) (Hm.map (A.loc p).ιE) (A.bc p x) (A.bc p y) :=
    fun x y => ((GlobalTheory.HL.RatExt.rational_extend A N p).2.2.2.2.1 Hm x y).symm
  funext j
  simp only [piQ, piL, Places.bc, map_sub, map_sum, map_add, map_mul, h5]

end Global

/- English proof (translation)
Introduce `F E _ _ _ _ _ sig A N r Hm hH X Y T hXY hXX hYY up sp horth hs hint d hd`. Set `good : HeightOneSpectrum (𝓞 F) → Prop` to `fun p => (∀ i j, (A.loc p).ιE (Hm i j) ∈ (A.L p).O) ∧ (∀ a j, (A.loc p).ιE (X a j) ∈ (A.L p).O) ∧ (∀ a j, (A.loc p).ιE (Y a j) ∈ (A.L p).O) ∧ ((∀ j, up p j ∈ (A.L p).O) ∧ sp p ∈ (A.L p).O) ∧ (∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = d p) ∧ (∃ u : (𝒪[(A.l …`. Establish `IL` using `GlobalTheory.HL.PlacesInt.integers_local A`. Establish `hgood : {p | ¬ good p}.Finite`. Establish `s1 : (⋃ i, ⋃ j, {p | (A.loc p).ιE (Hm i j) ∉ (A.L p).O}).Finite` using `Set.finite_iUnion fun i => Set.finite_iUnion fun j => IL.2.1 (Hm i j)`.

Establish `s2 : (⋃ a, ⋃ j, {p | (A.loc p).ιE (X a j) ∉ (A.L p).O}).Finite` using `Set.finite_iUnion fun a => Set.finite_iUnion fun j => IL.2.1 (X a j)`. Establish `s3 : (⋃ a, ⋃ j, {p | (A.loc p).ιE (Y a j) ∉ (A.L p).O}).Finite` using `Set.finite_iUnion fun a => Set.finite_iUnion fun j => IL.2.1 (Y a j)`. Establish `s6 : {p | (A.loc p).ιE (algebraMap F E 2⁻¹) ∉ (A.L p).O}.Finite` using `IL.2.1 _`. Use `(((((s1.union s2).union s3).union hint).union hd).union s6).subset ?_` and prove the remaining obligations. Introduce `p hp`.

Simplify using `only [Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion] at hp ⊢`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Take `⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩` from `hc`. Apply `hp` to reduce the goal to its premises.

Use `⟨h1, h2, h3, h4, h5, ?_⟩` and prove the remaining obligations. Use `haveI := (A.loc p).char0`. Rewrite `h6` using `[(A.loc p).compat, GlobalTheory.UnramOrder.algebraMap_mem_iff, map_inv₀, map_ofNat]`. Establish `h2m : (2 : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp]` using `by simpa using (𝒪[(A.loc p).Fp]).natCast_mem 2`. Use `⟨Units.mkOfMulEqOne ⟨2, h2m⟩ ⟨2⁻¹, h6⟩ (Subtype.ext ?_), rfl⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(2 : (A.loc p).Fp) * 2⁻¹ = 1`. Conclude with `mul_inv_cancel₀ two_ne_zero`. Establish `hE : ∀ p, ∃ e ∈ 𝒪[(A.loc p).Fp], e ≠ 0 ∧ (∀ i j, Sm (A.L p) e⁻¹ ((A.loc p).ιE (Hm i j))) ∧ (∀ a j, Sm (A.L p) e⁻¹ ((A.loc p).ιE (X a j))) ∧ (∀ a j, Sm (A.L p) e⁻¹ ((A.loc p).ιE (Y a j))) ∧ (∀ j, Sm (A.L p) e⁻¹ (up p j)) ∧ (good p → e = 1)`. Introduce `p`. Distinguish the cases in `hg : good p`.

Use `⟨1, (𝒪[(A.loc p).Fp]).one_mem, one_ne_zero, ?_, ?_, ?_, ?_, fun _ => rfl⟩` and prove the remaining obligations. Introduce `i j`. Rewrite using `[inv_one]`. Conclude with `(sm_one _).2 (hg.1 i j)`. Introduce `a j`.

Rewrite using `[inv_one]`. Conclude with `(sm_one _).2 (hg.2.1 a j)`. Introduce `a j`. Rewrite using `[inv_one]`. Conclude with `(sm_one _).2 (hg.2.2.1 a j)`.

Introduce `j`. Rewrite using `[inv_one]`. Conclude with `(sm_one _).2 (hg.2.2.2.1.1 j)`. Take `⟨e, he, he0, h⟩` from `exists_bound (A.L p) (Sum.elim (fun ij : Fin N × Fin N => (A.loc p).ιE (Hm ij.1 ij.2)) (Sum.elim (fun aj : Fin r × Fin N => (A.loc p).ιE (X aj.1 aj.2)) (Sum.elim (fun aj : Fin r × Fin N => (A.loc p).ιE (Y aj.1 aj.2)) (fun j => up p j))))`. Conclude with `⟨e, he, he0, fun i j => h (Sum.inl (i, j)), fun a j => h (Sum.inr (Sum.inl (a, j))), fun a j => h (Sum.inr (Sum.inr (Sum.inl (a, j)))), fun j => h (Sum.inr (Sum.inr (Sum.inr j))), fun h' => absurd h' hg⟩`.

Use `choose e he he0 bH bX bY bu he1 using hE`. Establish `hD : ∀ p, ∃ d' ∈ 𝒪[(A.loc p).Fp], d' ≠ 0 ∧ (∃ k ∈ 𝒪[(A.loc p).Fp], d' = d p * k) ∧ (good p → d' = d p)`. Introduce `p`. Distinguish the cases in `h : ((d p : (A.loc p).Fp)) ∈ 𝒪[(A.loc p).Fp]`. Conclude with `⟨d p, h, Units.ne_zero _, ⟨1, (𝒪[(A.loc p).Fp]).one_mem, (mul_one _).symm⟩, fun _ => rfl⟩`.

Establish `hi : ((d p : (A.loc p).Fp))⁻¹ ∈ 𝒪[(A.loc p).Fp]` using `((ValuativeRel.valuation (A.loc p).Fp).valuationSubring.mem_or_inv_mem _).resolve_left h`. Use `⟨1, (𝒪[(A.loc p).Fp]).one_mem, one_ne_zero, ⟨_, hi, (mul_inv_cancel₀ (Units.ne_zero _)).symm⟩, fun hg => absurd ?_ h⟩` and prove the remaining obligations. Take `⟨u, hu⟩` from `hg.2.2.2.2.1`. Rewrite using `[← hu]`. Conclude with `u.1.2`.

Use `choose d' hd' hd'0 hdk hd'1 using hD`. Establish `h2O : ∀ p, (2 : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp]` using `fun p => by`. Simplify using `using (𝒪[(A.loc p).Fp]).natCast_mem 2`. Establish `hne : ∀ p, (2 * d' p * e p ^ 5 : (A.loc p).Fp) ≠ 0` using `fun p => by haveI := (A.loc p).char0`. Conclude with `mul_ne_zero (mul_ne_zero two_ne_zero (hd'0 p)) (pow_ne_zero 5 (he0 p))`.

Set `δ : ∀ p, ((A.loc p).Fp)ˣ` to `fun p => Units.mk0 _ (hne p)`. Establish `hδ : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = δ p}.Finite`. Use `hgood.subset fun p hp hg => hp ?_` and prove the remaining obligations. Take `⟨ud, hud⟩` from `hg.2.2.2.2.1`. Take `⟨u2, hu2⟩` from `hg.2.2.2.2.2`.

Use `⟨u2 * ud, ?_⟩` and prove the remaining obligations. Simplify using `only [δ, Units.val_mk0, he1 p hg, hd'1 p hg, one_pow, mul_one, Units.val_mul, MulMemClass.coe_mul, hu2, hud]`. Establish `AP` using `GlobalTheory.T.strong_approximation_additive_quadratic_extension A δ hδ`. Use `choose w hw using fun j => AP.2.1 (fun p => up p j) (hint.subset fun p hp h => hp (h.1 j))`. Establish `hv : ∀ p j, Sm (A.L p) (2 * d' p * e p ^ 5) (A.bc p w j - up p j)` using `fun p j => hw j p`.

Use `set u := piQ sig Hm X Y T w with hu`. Establish `LC : ∀ p, _` using `fun p => local_choice (A.L p) (Hm.map (A.loc p).ιE) (fun a => A.bc p (X a)) (fun a => A.bc p (Y a)) T (up p) (horth p) (he p) (he0 p) (hd' p) (bH p) (bX p) (bY p) (bu p) (A.bc p w) (hv p)`. Establish `LC' : ∀ p, (∀ j, Sm (A.L p) (2 * d' p) (A.bc p u j - up p j)) ∧ Sm (A.L p) (2 * d' p) (hf (A.L p) (Hm.map (A.loc p).ιE) (A.bc p u) (A.bc p u) - hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (up p))` using `fun p => by`. Rewrite using `[hu, bc_piQ]`. Conclude with `LC p`.

Establish `hYX : ∀ a b, hq sig Hm (Y a) (X b) = if b = a then 1 else 0`. Apply the tactic sequence `intro a b; rw [← hq_swap A Hm hH, hXY]; split_ifs <;> simp`. Establish `horthu : ∀ a ∈ T, hq sig Hm u (X a) = 0 ∧ hq sig Hm u (Y a) = 0`. Introduce `b hb`. Rewrite using `[hu, hq_piQ, hq_piQ]`.

Prove the components needed by the constructor for the conclusion. Simplify using `[hXX, hYX, hb]`. Simplify using `[hXY, hYY, hb]`. Use `set t := hq sig Hm u u with ht`. Establish `hιt : ∀ p, (A.loc p).ιE t = hf (A.L p) (Hm.map (A.loc p).ιE) (A.bc p u) (A.bc p u)` using `fun p => ((GlobalTheory.HL.RatExt.rational_extend A N p).2.2.2.2.1 Hm u u).symm`.

Set `y : ∀ p, (A.loc p).Ep` to `fun p => sp p + algebraMap (A.loc p).Fp (A.loc p).Ep 2⁻¹ * ((A.loc p).ιE t - hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (up p))`. Establish `hyd : ∀ p, Sm (A.L p) (d p) (y p - sp p)`. Introduce `p`. Use `haveI := (A.loc p).char0`. Establish `h1 : Sm (A.L p) (2⁻¹ : (A.loc p).Fp) (algebraMap (A.loc p).Fp (A.loc p).Ep 2⁻¹)` using `⟨1, (A.L p).O.one_mem, (mul_one _).symm⟩`.

Establish `h2` using `sm_mul (A.L p) h1 (LC' p).2`. Rewrite `h2` using `[← hιt p]`. Establish `e : y p - sp p = algebraMap (A.loc p).Fp (A.loc p).Ep 2⁻¹ * ((A.loc p).ιE t - hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (up p))` using `by simp [y]`. Rewrite using `[e]`. Take `⟨k, hk, hk'⟩` from `hdk p`.

Conclude with `sm_of_eq (A.L p) h2 (by rw [hk']; field_simp) hk`. Establish `hyO : {p | y p ∉ (A.L p).O}.Finite`. Use `hgood.subset fun p hp hg => hp ?_` and prove the remaining obligations. Establish `e : y p = sp p + (y p - sp p)` using `by ring`. Take `⟨ud, hud⟩` from `hg.2.2.2.2.1`.

Establish `hdO : ((d p : (A.loc p).Fp)) ∈ 𝒪[(A.loc p).Fp]` using `by rw [← hud]; exact ud.1.2`. Rewrite using `[e]`. Conclude with `(A.L p).O.add_mem hg.2.2.2.1.2 (mem_of_sm (A.L p) (hyd p) hdO)`. Establish `hytr : ∀ p, y p + (A.L p).cj (y p) = (A.loc p).ιE t`. Introduce `p`.

Use `haveI := (A.loc p).char0`. Establish `hcH : (A.L p).cj (hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (up p)) = hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (up p)`. Rewrite using `[← hs p, map_add, (A.L p).cj_cj, add_comm]`. Establish `hct : (A.L p).cj ((A.loc p).ιE t) = (A.loc p).ιE t`. Rewrite using `[A.L_cj, (A.loc p).cj_ιE, ht, hq_swap A Hm hH]`.

Establish `h2 : algebraMap (A.loc p).Fp (A.loc p).Ep 2⁻¹ * 2 = 1`. Rewrite using `[← map_ofNat (algebraMap (A.loc p).Fp (A.loc p).Ep) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]`. Simplify using `only [y, map_add, map_mul, map_sub, AlgEquiv.commutes, hcH, hct]`. Take the linear combination `((A.loc p).ιE t - hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (up p)) * h2 + hs p`. Take `⟨s, hs1, hs2⟩` from `(GlobalTheory.T.strong_approximation_additive_quadratic_extension A d hd).2.2 t y hyO hytr`.

Use `⟨u, s, horthu, hs1, fun p => ⟨fun j => ?_, ?_⟩⟩` and prove the remaining obligations. Take `⟨k, hk, hk'⟩` from `hdk p`. Conclude with `sm_of_eq (A.L p) ((LC' p).1 j) (by rw [hk']; ring) ((𝒪[(A.loc p).Fp]).mul_mem (h2O p) hk)`. Establish `h1 : Sm (A.L p) ((d p : (A.loc p).Fp)) ((A.loc p).ιE s - y p)` using `hs2 p`. Establish `e : (A.loc p).ιE s - sp p = ((A.loc p).ιE s - y p) + (y p - sp p)` using `by ring`.

Rewrite using `[e]`. Conclude with `sm_add (A.L p) h1 (hyd p)`.
-/
theorem strong_approx_params : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (N r : ℕ) (Hm : Matrix (Fin N) (Fin N) E) (hH : ∀ i j, sig (Hm j i) = Hm i j) (X Y : Fin r → Fin N → E) (T : Finset (Fin r)) (hXY : ∀ a b, hq sig Hm (X a) (Y b) = if a = b then 1 else 0) (hXX : ∀ a b, hq sig Hm (X a) (X b) = 0) (hYY : ∀ a b, hq sig Hm (Y a) (Y b) = 0) (up : ∀ p, Fin N → (A.loc p).Ep) (sp : ∀ p, (A.loc p).Ep) (horth : ∀ p, ∀ a ∈ T, hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (A.bc p (X a)) = 0 ∧ hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (A.bc p (Y a)) = 0) (hs : ∀ p, sp p + (A.L p).cj (sp p) = hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (up p)) (hint : {p | ¬ ((∀ j, up p j ∈ (A.L p).O) ∧ sp p ∈ (A.L p).O)}.Finite) (d : ∀ p, ((A.loc p).Fp)ˣ) (hd : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = d p}.Finite), ∃ (u : Fin N → E) (s : E), (∀ a ∈ T, hq sig Hm u (X a) = 0 ∧ hq sig Hm u (Y a) = 0) ∧ s + sig s = hq sig Hm u u ∧ ∀ p, (∀ j, ∃ o ∈ (A.L p).O, (A.loc p).ιE (u j) - up p j = algebraMap (A.loc p).Fp (A.loc p).Ep (d p) * o) ∧ ∃ o ∈ (A.L p).O, (A.loc p).ιE s - sp p = algebraMap (A.loc p).Fp (A.loc p).Ep (d p) * o := by
  intro F E _ _ _ _ _ sig A N r Hm hH X Y T hXY hXX hYY up sp horth hs hint d hd

  let good : HeightOneSpectrum (𝓞 F) → Prop := fun p =>
    (∀ i j, (A.loc p).ιE (Hm i j) ∈ (A.L p).O) ∧ (∀ a j, (A.loc p).ιE (X a j) ∈ (A.L p).O) ∧
    (∀ a j, (A.loc p).ιE (Y a j) ∈ (A.L p).O) ∧ ((∀ j, up p j ∈ (A.L p).O) ∧ sp p ∈ (A.L p).O) ∧
    (∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = d p) ∧
    (∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = 2)
  have IL := GlobalTheory.HL.PlacesInt.integers_local A
  have hgood : {p | ¬ good p}.Finite := by
    have s1 : (⋃ i, ⋃ j, {p | (A.loc p).ιE (Hm i j) ∉ (A.L p).O}).Finite :=
      Set.finite_iUnion fun i => Set.finite_iUnion fun j => IL.2.1 (Hm i j)
    have s2 : (⋃ a, ⋃ j, {p | (A.loc p).ιE (X a j) ∉ (A.L p).O}).Finite :=
      Set.finite_iUnion fun a => Set.finite_iUnion fun j => IL.2.1 (X a j)
    have s3 : (⋃ a, ⋃ j, {p | (A.loc p).ιE (Y a j) ∉ (A.L p).O}).Finite :=
      Set.finite_iUnion fun a => Set.finite_iUnion fun j => IL.2.1 (Y a j)
    have s6 : {p | (A.loc p).ιE (algebraMap F E 2⁻¹) ∉ (A.L p).O}.Finite := IL.2.1 _
    refine (((((s1.union s2).union s3).union hint).union hd).union s6).subset ?_
    intro p hp
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion] at hp ⊢
    by_contra hc
    push_neg at hc
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
    apply hp
    refine ⟨h1, h2, h3, h4, h5, ?_⟩
    haveI := (A.loc p).char0
    rw [(A.loc p).compat, GlobalTheory.UnramOrder.algebraMap_mem_iff, map_inv₀, map_ofNat] at h6
    have h2m : (2 : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp] := by simpa using (𝒪[(A.loc p).Fp]).natCast_mem 2
    refine ⟨Units.mkOfMulEqOne ⟨2, h2m⟩ ⟨2⁻¹, h6⟩ (Subtype.ext ?_), rfl⟩
    change (2 : (A.loc p).Fp) * 2⁻¹ = 1
    exact mul_inv_cancel₀ two_ne_zero

  have hE : ∀ p, ∃ e ∈ 𝒪[(A.loc p).Fp], e ≠ 0 ∧ (∀ i j, Sm (A.L p) e⁻¹ ((A.loc p).ιE (Hm i j))) ∧
      (∀ a j, Sm (A.L p) e⁻¹ ((A.loc p).ιE (X a j))) ∧ (∀ a j, Sm (A.L p) e⁻¹ ((A.loc p).ιE (Y a j))) ∧
      (∀ j, Sm (A.L p) e⁻¹ (up p j)) ∧ (good p → e = 1) := by
    intro p
    by_cases hg : good p
    · refine ⟨1, (𝒪[(A.loc p).Fp]).one_mem, one_ne_zero, ?_, ?_, ?_, ?_, fun _ => rfl⟩
      · intro i j; rw [inv_one]; exact (sm_one _).2 (hg.1 i j)
      · intro a j; rw [inv_one]; exact (sm_one _).2 (hg.2.1 a j)
      · intro a j; rw [inv_one]; exact (sm_one _).2 (hg.2.2.1 a j)
      · intro j; rw [inv_one]; exact (sm_one _).2 (hg.2.2.2.1.1 j)
    · obtain ⟨e, he, he0, h⟩ := exists_bound (A.L p)
        (Sum.elim (fun ij : Fin N × Fin N => (A.loc p).ιE (Hm ij.1 ij.2))
          (Sum.elim (fun aj : Fin r × Fin N => (A.loc p).ιE (X aj.1 aj.2))
            (Sum.elim (fun aj : Fin r × Fin N => (A.loc p).ιE (Y aj.1 aj.2)) (fun j => up p j))))
      exact ⟨e, he, he0, fun i j => h (Sum.inl (i, j)), fun a j => h (Sum.inr (Sum.inl (a, j))),
        fun a j => h (Sum.inr (Sum.inr (Sum.inl (a, j)))), fun j => h (Sum.inr (Sum.inr (Sum.inr j))),
        fun h' => absurd h' hg⟩
  choose e he he0 bH bX bY bu he1 using hE

  have hD : ∀ p, ∃ d' ∈ 𝒪[(A.loc p).Fp], d' ≠ 0 ∧ (∃ k ∈ 𝒪[(A.loc p).Fp], d' = d p * k) ∧
      (good p → d' = d p) := by
    intro p
    by_cases h : ((d p : (A.loc p).Fp)) ∈ 𝒪[(A.loc p).Fp]
    · exact ⟨d p, h, Units.ne_zero _, ⟨1, (𝒪[(A.loc p).Fp]).one_mem, (mul_one _).symm⟩, fun _ => rfl⟩
    · have hi : ((d p : (A.loc p).Fp))⁻¹ ∈ 𝒪[(A.loc p).Fp] :=
        ((ValuativeRel.valuation (A.loc p).Fp).valuationSubring.mem_or_inv_mem _).resolve_left h
      refine ⟨1, (𝒪[(A.loc p).Fp]).one_mem, one_ne_zero, ⟨_, hi, (mul_inv_cancel₀ (Units.ne_zero _)).symm⟩,
        fun hg => absurd ?_ h⟩
      obtain ⟨u, hu⟩ := hg.2.2.2.2.1
      rw [← hu]; exact u.1.2
  choose d' hd' hd'0 hdk hd'1 using hD
  have h2O : ∀ p, (2 : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp] := fun p => by
    simpa using (𝒪[(A.loc p).Fp]).natCast_mem 2
  have hne : ∀ p, (2 * d' p * e p ^ 5 : (A.loc p).Fp) ≠ 0 := fun p => by
    haveI := (A.loc p).char0
    exact mul_ne_zero (mul_ne_zero two_ne_zero (hd'0 p)) (pow_ne_zero 5 (he0 p))
  let δ : ∀ p, ((A.loc p).Fp)ˣ := fun p => Units.mk0 _ (hne p)
  have hδ : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = δ p}.Finite := by
    refine hgood.subset fun p hp hg => hp ?_
    obtain ⟨ud, hud⟩ := hg.2.2.2.2.1
    obtain ⟨u2, hu2⟩ := hg.2.2.2.2.2
    refine ⟨u2 * ud, ?_⟩
    simp only [δ, Units.val_mk0, he1 p hg, hd'1 p hg, one_pow, mul_one, Units.val_mul,
      MulMemClass.coe_mul, hu2, hud]

  have AP := GlobalTheory.T.strong_approximation_additive_quadratic_extension A δ hδ
  choose w hw using fun j => AP.2.1 (fun p => up p j) (hint.subset fun p hp h => hp (h.1 j))
  have hv : ∀ p j, Sm (A.L p) (2 * d' p * e p ^ 5) (A.bc p w j - up p j) := fun p j => hw j p
  set u := piQ sig Hm X Y T w with hu
  have LC : ∀ p, _ := fun p => local_choice (A.L p) (Hm.map (A.loc p).ιE) (fun a => A.bc p (X a))
    (fun a => A.bc p (Y a)) T (up p) (horth p) (he p) (he0 p) (hd' p) (bH p) (bX p) (bY p) (bu p)
    (A.bc p w) (hv p)
  have LC' : ∀ p, (∀ j, Sm (A.L p) (2 * d' p) (A.bc p u j - up p j)) ∧
      Sm (A.L p) (2 * d' p) (hf (A.L p) (Hm.map (A.loc p).ιE) (A.bc p u) (A.bc p u) -
        hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (up p)) := fun p => by
    rw [hu, bc_piQ]; exact LC p

  have hYX : ∀ a b, hq sig Hm (Y a) (X b) = if b = a then 1 else 0 := by
    intro a b; rw [← hq_swap A Hm hH, hXY]; split_ifs <;> simp
  have horthu : ∀ a ∈ T, hq sig Hm u (X a) = 0 ∧ hq sig Hm u (Y a) = 0 := by
    intro b hb
    rw [hu, hq_piQ, hq_piQ]
    constructor
    · simp [hXX, hYX, hb]
    · simp [hXY, hYY, hb]

  set t := hq sig Hm u u with ht
  have hιt : ∀ p, (A.loc p).ιE t = hf (A.L p) (Hm.map (A.loc p).ιE) (A.bc p u) (A.bc p u) :=
    fun p => ((GlobalTheory.HL.RatExt.rational_extend A N p).2.2.2.2.1 Hm u u).symm
  let y : ∀ p, (A.loc p).Ep := fun p => sp p + algebraMap (A.loc p).Fp (A.loc p).Ep 2⁻¹ *
    ((A.loc p).ιE t - hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (up p))
  have hyd : ∀ p, Sm (A.L p) (d p) (y p - sp p) := by
    intro p
    haveI := (A.loc p).char0
    have h1 : Sm (A.L p) (2⁻¹ : (A.loc p).Fp) (algebraMap (A.loc p).Fp (A.loc p).Ep 2⁻¹) :=
      ⟨1, (A.L p).O.one_mem, (mul_one _).symm⟩
    have h2 := sm_mul (A.L p) h1 (LC' p).2
    rw [← hιt p] at h2
    have e : y p - sp p = algebraMap (A.loc p).Fp (A.loc p).Ep 2⁻¹ *
        ((A.loc p).ιE t - hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (up p)) := by simp [y]
    rw [e]
    obtain ⟨k, hk, hk'⟩ := hdk p
    exact sm_of_eq (A.L p) h2 (by rw [hk']; field_simp) hk
  have hyO : {p | y p ∉ (A.L p).O}.Finite := by
    refine hgood.subset fun p hp hg => hp ?_
    have e : y p = sp p + (y p - sp p) := by ring
    obtain ⟨ud, hud⟩ := hg.2.2.2.2.1
    have hdO : ((d p : (A.loc p).Fp)) ∈ 𝒪[(A.loc p).Fp] := by rw [← hud]; exact ud.1.2
    rw [e]
    exact (A.L p).O.add_mem hg.2.2.2.1.2 (mem_of_sm (A.L p) (hyd p) hdO)
  have hytr : ∀ p, y p + (A.L p).cj (y p) = (A.loc p).ιE t := by
    intro p
    haveI := (A.loc p).char0
    have hcH : (A.L p).cj (hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (up p)) =
        hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (up p) := by
      rw [← hs p, map_add, (A.L p).cj_cj, add_comm]
    have hct : (A.L p).cj ((A.loc p).ιE t) = (A.loc p).ιE t := by
      rw [A.L_cj, (A.loc p).cj_ιE, ht, hq_swap A Hm hH]
    have h2 : algebraMap (A.loc p).Fp (A.loc p).Ep 2⁻¹ * 2 = 1 := by
      rw [← map_ofNat (algebraMap (A.loc p).Fp (A.loc p).Ep) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero,
        map_one]
    simp only [y, map_add, map_mul, map_sub, AlgEquiv.commutes, hcH, hct]
    linear_combination ((A.loc p).ιE t - hf (A.L p) (Hm.map (A.loc p).ιE) (up p) (up p)) * h2 + hs p
  obtain ⟨s, hs1, hs2⟩ := (GlobalTheory.T.strong_approximation_additive_quadratic_extension A d hd).2.2 t y hyO hytr
  refine ⟨u, s, horthu, hs1, fun p => ⟨fun j => ?_, ?_⟩⟩
  · obtain ⟨k, hk, hk'⟩ := hdk p
    exact sm_of_eq (A.L p) ((LC' p).1 j) (by rw [hk']; ring) ((𝒪[(A.loc p).Fp]).mul_mem (h2O p) hk)
  · have h1 : Sm (A.L p) ((d p : (A.loc p).Fp)) ((A.loc p).ιE s - y p) := hs2 p
    have e : (A.loc p).ιE s - sp p = ((A.loc p).ιE s - y p) + (y p - sp p) := by ring
    rw [e]
    exact sm_add (A.L p) h1 (hyd p)

end GlobalTheory.HL.EichlerParams
