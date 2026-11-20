import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.IdxChange
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.GramLoc

/- English proof (translation)
Take `⟨T, rfl⟩` from `hM`. Establish `h1 : ∀ y : T, ∃ s : R, s ∈ p.primeCompl ∧ s • (y : W) ∈ L` using `fun y => h (Submodule.subset_span y.2)`. Use `choose f hf hf' using h1`. Use `⟨∏ y, f y, Submonoid.prod_mem p.primeCompl (fun y _ => hf y), ?_⟩` and prove the remaining obligations. Introduce `y hy`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx => classical`. Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨x, hx⟩ : T)), mul_smul]`. Conclude with `L.smul_mem _ (hf' ⟨x, hx⟩)`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `L.add_mem hx hy`. Consider the case `smul a x _ hx => rw [smul_comm]`. Conclude with `L.smul_mem _ hx`.
-/
theorem exists_common_denom {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (p : Ideal R) [p.IsPrime] (L M : Submodule R W) (hM : M.FG) (h : M ≤ Formalism.HermitianLatticesTheory.localization₂ p L) :
    ∃ s : R, s ∉ p ∧ ∀ y ∈ M, s • y ∈ L := by
  obtain ⟨T, rfl⟩ := hM
  have h1 : ∀ y : T, ∃ s : R, s ∈ p.primeCompl ∧ s • (y : W) ∈ L := fun y =>
    h (Submodule.subset_span y.2)
  choose f hf hf' using h1
  refine ⟨∏ y, f y, Submonoid.prod_mem p.primeCompl (fun y _ => hf y), ?_⟩
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    classical
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨x, hx⟩ : T)), mul_smul]
    exact L.smul_mem _ (hf' ⟨x, hx⟩)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact L.add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact L.smul_mem _ hx

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def locRing (w : HeightOneSpectrum (𝓞 K)) : Subring K where
  carrier := {a | ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ ∃ r : 𝓞 K, (s : K) * a = r}
  mul_mem' := by
    rintro a b ⟨s, hs, r, hr⟩ ⟨t, ht, u, hu⟩
    refine ⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs ht, r * u, ?_⟩
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_add, map_neg] at *
    rw [← hr, ← hu]; ring
  one_mem' := ⟨1, (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top, 1, by simp⟩
  add_mem' := by
    rintro a b ⟨s, hs, r, hr⟩ ⟨t, ht, u, hu⟩
    refine ⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs ht, t * r + s * u, ?_⟩
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_add, map_neg] at *
    rw [← hr, ← hu]; ring
  zero_mem' := ⟨1, (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top, 0, by simp⟩
  neg_mem' := by
    rintro a ⟨s, hs, r, hr⟩
    refine ⟨s, hs, -r, ?_⟩
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_add, map_neg] at *
    rw [← hr]; ring

/- English proof (translation)
Rewrite using `[Matrix.det_apply']`. Conclude with `S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.prod_mem fun i _ => h _ _)`.
-/
theorem det_mem_subring (S : Subring K) (P : Matrix (Fin n) (Fin n) K) (h : ∀ a b, P a b ∈ S) :
    P.det ∈ S := by
  rw [Matrix.det_apply']
  exact S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.prod_mem fun i _ => h _ _)

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨j, rfl⟩`.
-/
theorem col_mem_colLat (B : GL (Fin n) K) (j : Fin n) :
    (fun a => (B : Matrix (Fin n) (Fin n) K) a j) ∈ colLat B :=
  Submodule.subset_span ⟨j, rfl⟩

/- English proof (translation)
Unfold `colLat at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`. Establish `h : ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) = 1` using `Units.inv_mul B`.

Establish `h2` using `congrFun (congrFun h j) i`. Use `⟨if j = i then 1 else 0, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K)) j i = _`. Rewrite using `[h2, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨r, hr⟩` from `hx`. Take `⟨u, hu⟩` from `hy`. Conclude with `⟨r + u, by rw [Matrix.mulVec_add, Pi.add_apply, hr, hu]; simp⟩`.

Consider the case `smul a x _ hx`. Take `⟨r, hr⟩` from `hx`. Use `⟨a * r, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_smul, Pi.smul_apply, hr, Algebra.smul_def]`. Simplify using the standard rewrite rules.
-/
theorem coord_of_mem_colLat (B : GL (Fin n) K) (x : Fin n → K) (hx : x ∈ colLat B) (j : Fin n) :
    ∃ r : 𝓞 K, (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) j = r := by
  unfold colLat at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    have h : ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) = 1 :=
      Units.inv_mul B
    have h2 := congrFun (congrFun h j) i
    refine ⟨if j = i then 1 else 0, ?_⟩
    change (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K)) j i = _
    rw [h2, Matrix.one_apply]
    split_ifs <;> simp
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨r, hr⟩ := hx
    obtain ⟨u, hu⟩ := hy
    exact ⟨r + u, by rw [Matrix.mulVec_add, Pi.add_apply, hr, hu]; simp⟩
  | smul a x _ hx =>
    obtain ⟨r, hr⟩ := hx
    refine ⟨a * r, ?_⟩
    rw [Matrix.mulVec_smul, Pi.smul_apply, hr, Algebra.smul_def]
    simp

variable [StarRing K]

/- English proof (translation)
Take `⟨s, hs, r, hr⟩` from `ha`. Distinguish the cases in `h0 : a = 0`. Rewrite using `[h0, ValuationRepresentative.vw_zero]`. Establish `hs0 : (s : K) ≠ 0`. Introduce `h`.

Apply `hs` to reduce the goal to its premises. Establish `: s = 0` using `by exact_mod_cast h`. Rewrite using `[this]`. Conclude with `zero_mem _`. Establish `h1` using `ValuationRepresentative.vw_mul w _ _ hs0 h0`.

Establish `h2 : vw w (s : K) = 0` using `idxChange_cnt_unit (K := K) w hs`. Establish `h3` using `ValuationRepresentative.vw_int_nonneg w r`. Rewrite `h1` using `[hr, h2]`. Use linear arithmetic over natural numbers and integers.
-/
theorem vw_nonneg_of_mem (w : HeightOneSpectrum (𝓞 K)) (a : K) (ha : a ∈ locRing w) :
    0 ≤ vw w a := by
  obtain ⟨s, hs, r, hr⟩ := ha
  by_cases h0 : a = 0
  · rw [h0, ValuationRepresentative.vw_zero]
  have hs0 : (s : K) ≠ 0 := by
    intro h
    apply hs
    have : s = 0 := by exact_mod_cast h
    rw [this]; exact zero_mem _
  have h1 := ValuationRepresentative.vw_mul w _ _ hs0 h0
  have h2 : vw w (s : K) = 0 := idxChange_cnt_unit (K := K) w hs
  have h3 := ValuationRepresentative.vw_int_nonneg w r
  rw [hr, h2] at h1
  omega

/- English proof (translation)
Introduce `h`. Apply `ht` to reduce the goal to its premises. Use `Ideal.mem_map_of_mem (cO K) h` as an intermediate fact. Rewrite `this` using `[ValuationRepresentative.cO_cO]`. Then use the resulting hypothesis.
-/
theorem cO_notMem (w : HeightOneSpectrum (𝓞 K)) (t : 𝓞 K) (ht : t ∉ (conjPl w).asIdeal) :
    cO K t ∉ w.asIdeal := by
  intro h
  apply ht
  have := Ideal.mem_map_of_mem (cO K) h
  rwa [ValuationRepresentative.cO_cO] at this

/- English proof (translation)
Introduce `x hx` and use `⟨1, one_mem _, by simpa using hx⟩`.
-/
theorem mem_localization_of_mem {w : HeightOneSpectrum (𝓞 K)} (M : Submodule (𝓞 K) (Fin n → K)) :
    M ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M := fun x hx =>
  ⟨1, one_mem _, by simpa using hx⟩

/- English proof (translation)
Unfold `IsBasisAt at hB hB'`. Establish `h1` using `mem_localization_of_mem (w := conjPl w) _ (col_mem_colLat B a)`. Establish `h2` using `mem_localization_of_mem (w := w) _ (col_mem_colLat B' b)`. Rewrite `h1` using `[← hB]`. Rewrite `h2` using `[← hB']`.

Take `⟨t, ht, h1⟩` from `h1`. Take `⟨u, hu, h2⟩` from `h2`. Rewrite `h2` using `[← hM]`. Take `⟨r, hr⟩` from `Submodule.mem_one.1 (h2 _ h1)`. Use `⟨cO K t * u, fun h => (w.isPrime.mem_or_mem h).elim (cO_notMem w t ht) hu, r, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `_ = algebraMap (𝓞 K) K r`. Rewrite using `[hr, Matrix.mul_assoc]`. Establish `hc : ((cO K t * u : 𝓞 K) : K) = star (t : K) * (u : K)`. Rewrite using `[← ValuationRepresentative.cO_apply]`. Conclude with `map_mul (algebraMap (𝓞 K) K) _ _`.

Rewrite using `[hc]`. Simplify using `only [Matrix.mul_apply, dotProduct, Matrix.mulVec, Pi.star_apply, Pi.smul_apply, Algebra.smul_def, Matrix.conjTranspose_apply, star_mul', Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `star (t : K) * (u : K) * _ = star (t : K) * _ * (_ * ((u : K) * _))`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_mem (G : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K))
    (hM : hdualFr G M = M) (w : HeightOneSpectrum (𝓞 K)) (B B' : GL (Fin n) K)
    (hB : IsBasisAt (conjPl w) M B) (hB' : IsBasisAt w M B') (a b : Fin n) :
    ((B : Matrix (Fin n) (Fin n) K)ᴴ * G * (B' : Matrix (Fin n) (Fin n) K)) a b ∈ locRing w := by
  unfold IsBasisAt at hB hB'
  have h1 := mem_localization_of_mem (w := conjPl w) _ (col_mem_colLat B a)
  have h2 := mem_localization_of_mem (w := w) _ (col_mem_colLat B' b)
  rw [← hB] at h1
  rw [← hB'] at h2
  obtain ⟨t, ht, h1⟩ := h1
  obtain ⟨u, hu, h2⟩ := h2
  rw [← hM] at h2
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 (h2 _ h1)
  refine ⟨cO K t * u, fun h => (w.isPrime.mem_or_mem h).elim (cO_notMem w t ht) hu, r, ?_⟩
  change _ = algebraMap (𝓞 K) K r
  rw [hr, Matrix.mul_assoc]
  have hc : ((cO K t * u : 𝓞 K) : K) = star (t : K) * (u : K) := by
    rw [← ValuationRepresentative.cO_apply]; exact map_mul (algebraMap (𝓞 K) K) _ _
  rw [hc]
  simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec, Pi.star_apply, Pi.smul_apply,
    Algebra.smul_def, Matrix.conjTranspose_apply, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change star (t : K) * (u : K) * _ = star (t : K) * _ * (_ * ((u : K) * _))
  ring

/- English proof (translation)
Unfold `IsBasisAt at hB hB'`. Take `⟨t, ht, h1⟩` from `exists_common_denom (conjPl w).asIdeal (colLat B) M hfg (hB ▸ mem_localization_of_mem M)`. Use `set C : Matrix (Fin n) (Fin n) K := ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hC`. Use `set x : Fin n → K := fun i => (G⁻¹ * Cᴴ) i b with hx`. Establish `hGx : G *ᵥ x = fun i => star (C b i)`.

Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `(G * (G⁻¹ * Cᴴ)) i b = _`. Rewrite using `[Matrix.mul_nonsing_inv_cancel_left _ _ hG, Matrix.conjTranspose_apply]`. Establish `hxM : cO K t • x ∈ hdualFr G M`. Introduce `y hy`.

Take `⟨r, hr⟩` from `coord_of_mem_colLat B _ (h1 y hy) b`. Use `Submodule.mem_one.2 ⟨cO K r, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((cO K r : 𝓞 K) : K) = _`. Rewrite using `[ValuationRepresentative.cO_apply, ← hr, Matrix.mulVec_smul, Matrix.mulVec_smul, hGx]`. Simplify using `only [dotProduct, Matrix.mulVec, Pi.star_apply, Pi.smul_apply, Algebra.smul_def, star_mul', Finset.mul_sum, star_sum, ← hC]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `star (t : K) * _ = _ * (star (t : K) * _)`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hxM` using `[hM]`. Establish `h3` using `mem_localization_of_mem (w := w) M hxM`.

Rewrite `h3` using `[hB']`. Take `⟨u, hu, h3⟩` from `h3`. Take `⟨r, hr⟩` from `coord_of_mem_colLat B' _ h3 a`. Use `⟨u * cO K t, fun h => (w.isPrime.mem_or_mem h).elim hu (cO_notMem w t ht), r, ?_⟩` and prove the remaining obligations. Rewrite using `[← hr, ← mul_smul, Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def]`.

Both sides reduce to the same expression.
-/
theorem gram_inv_mem (G : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K))
    (hG : IsUnit G.det) (hfg : M.FG)
    (hM : hdualFr G M = M) (w : HeightOneSpectrum (𝓞 K)) (B B' : GL (Fin n) K)
    (hB : IsBasisAt (conjPl w) M B) (hB' : IsBasisAt w M B') (a b : Fin n) :
    (((B'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (G⁻¹ * ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᴴ)) a b ∈ locRing w := by
  unfold IsBasisAt at hB hB'
  obtain ⟨t, ht, h1⟩ := exists_common_denom (conjPl w).asIdeal (colLat B) M hfg
    (hB ▸ mem_localization_of_mem M)
  set C : Matrix (Fin n) (Fin n) K := ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hC
  set x : Fin n → K := fun i => (G⁻¹ * Cᴴ) i b with hx
  have hGx : G *ᵥ x = fun i => star (C b i) := by
    funext i
    change (G * (G⁻¹ * Cᴴ)) i b = _
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hG, Matrix.conjTranspose_apply]
  have hxM : cO K t • x ∈ hdualFr G M := by
    intro y hy
    obtain ⟨r, hr⟩ := coord_of_mem_colLat B _ (h1 y hy) b
    refine Submodule.mem_one.2 ⟨cO K r, ?_⟩
    change ((cO K r : 𝓞 K) : K) = _
    rw [ValuationRepresentative.cO_apply, ← hr, Matrix.mulVec_smul, Matrix.mulVec_smul, hGx]
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Pi.smul_apply,
      Algebra.smul_def, star_mul', Finset.mul_sum, star_sum, ← hC]
    refine Finset.sum_congr rfl fun i _ => ?_
    change star (t : K) * _ = _ * (star (t : K) * _)
    ring
  rw [hM] at hxM
  have h3 := mem_localization_of_mem (w := w) M hxM
  rw [hB'] at h3
  obtain ⟨u, hu, h3⟩ := h3
  obtain ⟨r, hr⟩ := coord_of_mem_colLat B' _ h3 a
  refine ⟨u * cO K t, fun h => (w.isPrime.mem_or_mem h).elim hu (cO_notMem w t ht), r, ?_⟩
  rw [← hr, ← mul_smul, Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def]
  rfl

/- English proof (translation)
Introduce `K _ _ _ n G M _ hG hM w B B' hB hB'`. Establish `hfg : M.FG` using `hM.1.fg`. Establish `h1` using `gram_mem G M hM.2 w B B' hB hB'`. Establish `h2` using `gram_inv_mem G M hG hfg hM.2 w B B' hB hB'`. Use `⟨fun a b => vw_nonneg_of_mem w _ (h1 a b), ?_⟩` and prove the remaining obligations.

Establish `d1` using `vw_nonneg_of_mem w _ (det_mem_subring _ _ h1)`. Establish `d2` using `vw_nonneg_of_mem w _ (det_mem_subring _ _ h2)`. Establish `e : ((B : Matrix (Fin n) (Fin n) K)ᴴ * G * (B' : Matrix (Fin n) (Fin n) K)) * (((B'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (G⁻¹ * ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᴴ)) = 1`. Establish `e1 : (B' : Matrix (Fin n) (Fin n) K) * ((B'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1` using `Units.mul_inv B'`. Establish `e2 : ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) = 1` using `Units.inv_mul B`.

Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc (B' : Matrix (Fin n) (Fin n) K), e1, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hG, ← Matrix.conjTranspose_mul, e2, Matrix.conjTranspose_one]`. Establish `e'` using `congrArg Matrix.det e`. Rewrite `e'` using `[Matrix.det_mul, Matrix.det_one]`. Establish `e3` using `ValuationRepresentative.vw_mul w _ _ (left_ne_zero_of_mul_eq_one e') (right_ne_zero_of_mul_eq_one e')`. Rewrite `e3` using `[e', ValuationRepresentative.vw_one]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem gram_locally_unimodular : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (G : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K)), Gᴴ = G → IsUnit G.det → IsSelfDualK G M → ∀ (w : HeightOneSpectrum (𝓞 K)) (B B' : GL (Fin n) K), IsBasisAt (conjPl w) M B → IsBasisAt w M B' → (∀ a b, 0 ≤ vw w (((B : Matrix (Fin n) (Fin n) K)ᴴ * G * (B' : Matrix (Fin n) (Fin n) K)) a b)) ∧ vw w ((B : Matrix (Fin n) (Fin n) K)ᴴ * G * (B' : Matrix (Fin n) (Fin n) K)).det = 0 := by
  intro K _ _ _ n G M _ hG hM w B B' hB hB'
  have hfg : M.FG := hM.1.fg
  have h1 := gram_mem G M hM.2 w B B' hB hB'
  have h2 := gram_inv_mem G M hG hfg hM.2 w B B' hB hB'
  refine ⟨fun a b => vw_nonneg_of_mem w _ (h1 a b), ?_⟩
  have d1 := vw_nonneg_of_mem w _ (det_mem_subring _ _ h1)
  have d2 := vw_nonneg_of_mem w _ (det_mem_subring _ _ h2)
  have e : ((B : Matrix (Fin n) (Fin n) K)ᴴ * G * (B' : Matrix (Fin n) (Fin n) K)) *
      (((B'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (G⁻¹ * ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᴴ)) = 1 := by
    have e1 : (B' : Matrix (Fin n) (Fin n) K) * ((B'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
      Units.mul_inv B'
    have e2 : ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) = 1 :=
      Units.inv_mul B
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (B' : Matrix (Fin n) (Fin n) K), e1, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hG, ← Matrix.conjTranspose_mul, e2,
      Matrix.conjTranspose_one]
  have e' := congrArg Matrix.det e
  rw [Matrix.det_mul, Matrix.det_one] at e'
  have e3 := ValuationRepresentative.vw_mul w _ _ (left_ne_zero_of_mul_eq_one e') (right_ne_zero_of_mul_eq_one e')
  rw [e', ValuationRepresentative.vw_one] at e3
  omega

end GlobalTheory.GramLoc
