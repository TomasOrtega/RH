import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordRelationsHomogeneousStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogXpow
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFibreNormDehomRoots
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.AmpleBlock

open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.HilbertSamuel

variable {K : Type} [Fintype K] [DecidableEq K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]

/- English proof (translation)
Introduce `m hm k`. Rewrite `hm` using `[support_rename_of_injective sigma_mk_injective]`. Take `⟨m', hm', rfl⟩` from `Finset.mem_image.1 hm`. Establish `hd : ∑ i, m' i = n`. Use `h (mem_support_iff.1 hm')` as an intermediate fact.

Rewrite using `[← this, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]`. Simplify using the standard rewrite rules. Distinguish the cases in `hk : k = k₀`. Substitute `hk` using the available equality. Simplify using `[Finsupp.mapDomain_apply sigma_mk_injective, hd]`.

Establish `h0 : ∀ i, Finsupp.mapDomain (Sigma.mk k₀) m' ⟨k, i⟩ = 0` using `fun i => Finsupp.mapDomain_notin_range _ _ (by`. Introduce and unpack `⟨i', hi'⟩`. Conclude with `hk (congrArg Sigma.fst hi').symm)`. Simplify using `[h0, Pi.single_apply, hk]`.
-/
theorem homog_rename (k₀ : K) {F : MvPolynomial (J k₀) ℤ} {n : ℕ} (h : F.IsHomogeneous n) :
    IsMultiHomog (rename (Sigma.mk k₀) F : MRing J) (Pi.single k₀ n) := by
  classical
  intro m hm k
  rw [support_rename_of_injective sigma_mk_injective] at hm
  obtain ⟨m', hm', rfl⟩ := Finset.mem_image.1 hm
  have hd : ∑ i, m' i = n := by
    have := h (mem_support_iff.1 hm')
    rw [← this, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  by_cases hk : k = k₀
  · subst hk
    simp [Finsupp.mapDomain_apply sigma_mk_injective, hd]
  · have h0 : ∀ i, Finsupp.mapDomain (Sigma.mk k₀) m' ⟨k, i⟩ = 0 := fun i =>
      Finsupp.mapDomain_notin_range _ _ (by
        rintro ⟨i', hi'⟩
        exact hk (congrArg Sigma.fst hi').symm)
    simp [h0, Pi.single_apply, hk]

/- English proof (translation)
Establish `hm : (rename (Sigma.mk k₀) A * X ⟨k, j'⟩ - rename (Sigma.mk k₀) B * X ⟨k, j⟩ : MRing J) ∈ mCoordIdeal y`. Express the relevant statement in the definitionally equal form `mConeMap y _ = 0`. Rewrite using `[map_sub, map_mul, map_mul, ProjLine.mConeMap_eq_of_isMultiHomog y (homog_rename k₀ hA), ProjLine.mConeMap_eq_of_isMultiHomog y (homog_rename k₀ hB)]`. Simplify using `only [mConeMap, aeval_X, aeval_rename]`. Use `congrArg (C : Ω →+* MvPolynomial K Ω) hr` as an intermediate fact.

Rewrite `this` using `[map_mul, map_mul]`. Simplify using `only [Function.comp_def]`. Take the linear combination `((∏ k, (X k : MvPolynomial K Ω) ^ (Pi.single k₀ n : K → ℕ) k) * X k) * this`. Use `hz.2 _ hm` as an intermediate fact. Simplify using `only [map_sub, map_mul, aeval_X, aeval_rename, Function.comp_def] at this`.

Conclude with `sub_eq_zero.mp this`.
-/
theorem rel_at_point {y : (Σ k, J k) → Ω} (k₀ k : K) {A B : MvPolynomial (J k₀) ℤ} {n : ℕ}
    (hA : A.IsHomogeneous n) (hB : B.IsHomogeneous n) (j j' : J k)
    (hr : aeval (fun i => y ⟨k₀, i⟩) A * y ⟨k, j'⟩ = aeval (fun i => y ⟨k₀, i⟩) B * y ⟨k, j⟩)
    {L : Type} [Field L] {z : (Σ k, J k) → L} (hz : z ∈ Small.ptsOver L (mCoordIdeal y)) :
    aeval (fun i => z ⟨k₀, i⟩) A * z ⟨k, j'⟩ = aeval (fun i => z ⟨k₀, i⟩) B * z ⟨k, j⟩ := by
  have hm : (rename (Sigma.mk k₀) A * X ⟨k, j'⟩ - rename (Sigma.mk k₀) B * X ⟨k, j⟩ : MRing J) ∈ mCoordIdeal y := by
    change mConeMap y _ = 0
    rw [map_sub, map_mul, map_mul, ProjLine.mConeMap_eq_of_isMultiHomog y (homog_rename k₀ hA),
      ProjLine.mConeMap_eq_of_isMultiHomog y (homog_rename k₀ hB)]
    simp only [mConeMap, aeval_X, aeval_rename]
    have := congrArg (C : Ω →+* MvPolynomial K Ω) hr
    rw [map_mul, map_mul] at this
    simp only [Function.comp_def]
    linear_combination ((∏ k, (X k : MvPolynomial K Ω) ^ (Pi.single k₀ n : K → ℕ) k) * X k) * this
  have := hz.2 _ hm
  simp only [map_sub, map_mul, aeval_X, aeval_rename, Function.comp_def] at this
  exact sub_eq_zero.mp this

def gForm (k₀ : K) (i : J k₀) (e : ℕ) (G : K → MvPolynomial (J k₀) ℤ) : MRing J :=
  X ⟨k₀, i⟩ ^ e * ∏ k ∈ Finset.univ.erase k₀, rename (Sigma.mk k₀) (G k)

def hForm (k₀ : K) (j : ∀ k, J k) : MRing J :=
  ∏ k ∈ Finset.univ.erase k₀, X ⟨k, j k⟩

/- English proof (translation)
Establish `h` using `isMultiHomog_mul (isMultiHomog_pow (isMultiHomog_X' k₀ i : IsMultiHomog (X ⟨k₀, i⟩ : MRing J) _) e) (isMultiHomog_prod (Finset.univ.erase k₀) (fun k => rename (Sigma.mk k₀) (G k)) (fun k => Pi.single k₀ (d k)) fun k => homog_rename k₀ (hG k))`. Rewrite using `[gForm]`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k'`. Distinguish the cases in `hk : k' = k₀`.

Substitute `hk` using the available equality. Simplify using `[Finset.sum_apply]`. Simplify using `[Finset.sum_apply, Pi.single_apply, hk]`.
-/
theorem gForm_homog (k₀ : K) (i : J k₀) (e : ℕ) {G : K → MvPolynomial (J k₀) ℤ} {d : K → ℕ}
    (hG : ∀ k, (G k).IsHomogeneous (d k)) :
    IsMultiHomog (gForm k₀ i e G) (Pi.single k₀ (e + ∑ k ∈ Finset.univ.erase k₀, d k)) := by
  have h := isMultiHomog_mul (isMultiHomog_pow (isMultiHomog_X' k₀ i : IsMultiHomog (X ⟨k₀, i⟩ : MRing J) _) e)
    (isMultiHomog_prod (Finset.univ.erase k₀) (fun k => rename (Sigma.mk k₀) (G k))
      (fun k => Pi.single k₀ (d k)) fun k => homog_rename k₀ (hG k))
  rw [gForm]
  convert h using 1
  funext k'
  by_cases hk : k' = k₀
  · subst hk
    simp [Finset.sum_apply]
  · simp [Finset.sum_apply, Pi.single_apply, hk]

def hDeg (k₀ : K) : K → ℕ := fun k => if k = k₀ then 0 else 1

/- English proof (translation)
Establish `h` using `isMultiHomog_prod (Finset.univ.erase k₀) (fun k => (X ⟨k, j k⟩ : MRing J)) (fun k => Pi.single k 1) fun k => isMultiHomog_X' k (j k)`. Rewrite using `[hForm]`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k'`. Distinguish the cases in `hk : k' = k₀`.

Substitute `hk` using the available equality. Simplify using `[hDeg, Finset.sum_apply, Pi.single_apply]`. Simplify using `[hDeg, Finset.sum_apply, Pi.single_apply, hk]`.
-/
theorem hForm_homog (k₀ : K) (j : ∀ k, J k) : IsMultiHomog (hForm k₀ j) (hDeg k₀) := by
  have h := isMultiHomog_prod (Finset.univ.erase k₀) (fun k => (X ⟨k, j k⟩ : MRing J))
      (fun k => Pi.single k 1) fun k => isMultiHomog_X' k (j k)
  rw [hForm]
  convert h using 1
  funext k'
  by_cases hk : k' = k₀
  · subst hk
    simp [hDeg, Finset.sum_apply, Pi.single_apply]
  · simp [hDeg, Finset.sum_apply, Pi.single_apply, hk]

/- English proof (translation)
Simplify using `[gForm, map_prod, aeval_rename, Function.comp_def]`.
-/
theorem aeval_gForm {L : Type} [Field L] (z : (Σ k, J k) → L) (k₀ : K) (i : J k₀) (e : ℕ)
    (G : K → MvPolynomial (J k₀) ℤ) :
    aeval z (gForm k₀ i e G) = z ⟨k₀, i⟩ ^ e * ∏ k ∈ Finset.univ.erase k₀, aeval (fun i => z ⟨k₀, i⟩) (G k) := by
  simp [gForm, map_prod, aeval_rename, Function.comp_def]

/- English proof (translation)
Simplify using `[hForm, map_prod]`.
-/
theorem aeval_hForm {L : Type} [Field L] (z : (Σ k, J k) → L) (k₀ : K) (j : ∀ k, J k) :
    aeval z (hForm k₀ j) = ∏ k ∈ Finset.univ.erase k₀, z ⟨k, j k⟩ := by
  simp [hForm, map_prod]

def sec (y : (Σ k, J k) → Ω) (k₀ : K) (js : ∀ k, J k) (i : J k₀) (e : ℕ) (G : K → MvPolynomial (J k₀) ℤ) : Ω :=
  y ⟨k₀, i⟩ ^ e * ∏ k ∈ Finset.univ.erase k₀, aeval (fun i => y ⟨k₀, i⟩) (G k) / y ⟨k, js k⟩

/- English proof (translation)
Rewrite using `[aeval_gForm, aeval_hForm, sec, _root_.mul_assoc, ← Finset.prod_mul_distrib]`. Use `congr 1`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `hjs k` as an intermediate fact. Clear the denominators using the available nonvanishing facts.

Conclude with `(hr k).symm`.
-/
theorem sec_mul (y : (Σ k, J k) → Ω) (k₀ : K) (js j : ∀ k, J k) (hjs : ∀ k, y ⟨k, js k⟩ ≠ 0) (i : J k₀) (e : ℕ)
    (G G' : K → MvPolynomial (J k₀) ℤ)
    (hr : ∀ k, aeval (fun i => y ⟨k₀, i⟩) (G k) * y ⟨k, j k⟩ = aeval (fun i => y ⟨k₀, i⟩) (G' k) * y ⟨k, js k⟩) :
    aeval y (gForm k₀ i e G') = sec y k₀ js i e G * aeval y (hForm k₀ j) := by
  rw [aeval_gForm, aeval_hForm, sec, _root_.mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  have := hjs k
  field_simp
  exact (hr k).symm

/- English proof (translation)
Distinguish the cases in `hy : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0`. Use `swap`. Use `push_neg at hy`. Take `⟨k, hk⟩` from `hy`. Use `⟨0, 0, Fin.elim0, fun i => i.elim0, fun L _ _ z hz => ?_⟩` and prove the remaining obligations.

It suffices to derive a contradiction. Take `⟨i, hi⟩` from `hz.1 k`. Establish `hm : (X ⟨k, i⟩ : MRing J) ∈ mCoordIdeal y`. Express the relevant statement in the definitionally equal form `mConeMap y _ = 0`. Simplify using `[mConeMap, hk i]`.

Conclude with `hi (by simpa using hz.2 _ hm)`. Use `choose js hjs using hy`. Choose the witnesses or unpack the hypotheses as in `⟨N, hN⟩ : ∃ N : ℕ, ∀ T : ∀ k, Fin (l k), ∑ k ∈ Finset.univ.erase k₀, n k (T k) ≤ N := by`. Use `⟨∑ k, ∑ t, n k t, fun T => ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Set `eT : (∀ k, Fin (l k)) → ℕ` to `fun T => N - ∑ k ∈ Finset.univ.erase k₀, n k (T k)`. Establish `heT : ∀ T, eT T + ∑ k ∈ Finset.univ.erase k₀, n k (T k) = N` using `fun T => Nat.sub_add_cancel (hN T)`. Set `I` to `(∀ k, Fin (l k)) × J k₀`. Set `S : I → Ω` to `fun p => sec y k₀ js p.2 (eT p.1) fun k => F k (p.1 k) (js k)`. Establish `hdeg : ∀ k, ((Pi.single k₀ N : K → ℕ) k : ℤ) = hDeg k₀ k + (((N + 1 : ℕ) : ℤ) * a k - 1)`.

Introduce `k`. Distinguish the cases in `hk : k = k₀`. Substitute `hk` using the available equality. Simplify using `[hDeg, ha₀]`. Simplify using `[hDeg, Pi.single_apply, hk, ha k hk]`.

Establish `hform : ∀ (p : I) (j : ∀ k, J k), IsMultiHomog (gForm k₀ p.2 (eT p.1) fun k => F k (p.1 k) (j k)) (Pi.single k₀ N) ∧ aeval y (gForm k₀ p.2 (eT p.1) fun k => F k (p.1 k) (j k)) = S p * aeval y (hForm k₀ j)`. Introduce `p j`. Use `⟨?_, sec_mul y k₀ js j hjs _ _ _ _ fun k => rel k (p.1 k) (js k) (j k)⟩` and prove the remaining obligations. Use `gForm_homog k₀ p.2 (eT p.1) (G := fun k => F k (p.1 k) (j k)) (d := fun k => n k (p.1 k)) fun k => hom k _ _` as an intermediate fact. Rewrite `this` using `[heT]`. Then use the resulting hypothesis.

Use `⟨N + 1, Fintype.card I, fun q => S ((Fintype.equivFin I).symm q), fun q c hc => ?_, fun L _ _ z hz => ?_⟩` and prove the remaining obligations. Take `⟨h1, h2⟩` from `hform ((Fintype.equivFin I).symm q) c`. Establish `h3` using `FibreNormDehomRoots.aeval_mem_chartLatNm h1 c hc`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[h2, aeval_hForm, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k₀), ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k₀)]`.

Establish `e1 : ∏ k ∈ Finset.univ.erase k₀, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (((N + 1 : ℕ) : ℤ) * a k - 1))) = ∏ k ∈ Finset.univ.erase k₀, y ⟨k, c k⟩`. Use `Finset.prod_congr rfl fun k hk => ?_` and prove the remaining obligations. Simplify using `[ha k (Finset.ne_of_mem_erase hk)]`. Establish `e2 : ∏ k ∈ Finset.univ.erase k₀, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * ((1 * (Pi.single k₀ N : K → ℕ) k : ℕ) : ℤ))) = 1`. Use `Finset.prod_eq_one fun k hk => ?_` and prove the remaining obligations.

Simplify using `[Pi.single_apply, Finset.ne_of_mem_erase hk]`. Rewrite using `[e1, e2]`. Simplify using `[ha₀]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨i, hi⟩` from `hz.1 k₀ choose T jz hF using fun k => pts k L z hz`.

Establish `hzj : ∀ k, z ⟨k, jz k⟩ ≠ 0`. Introduce `k h0`. Take `⟨j', hj'⟩` from `hz.1 k`. Use `rel_at_point k₀ k (hom k (T k) (jz k)) (hom k (T k) j') (jz k) j' (rel k _ _ _) hz` as an intermediate fact. Rewrite `this` using `[h0, mul_zero]`.

Conclude with `mul_ne_zero (hF k) hj' this`. Take `⟨h1, h2⟩` from `hform (T, i) jz`. Establish `hg : aeval z (gForm k₀ i (eT T) fun k => F k (T k) (jz k)) ≠ 0`. Rewrite using `[aeval_gForm]`. Conclude with `mul_ne_zero (pow_ne_zero _ hi) (Finset.prod_ne_zero_iff.mpr fun k _ => hF k)`.

Establish `hh : aeval z (hForm k₀ jz) ≠ 0`. Rewrite using `[aeval_hForm]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun k _ => hzj k`. Use `⟨Fintype.equivFin I (T, i), _ / _, div_ne_zero hg hh, Pi.single k₀ N, hDeg k₀, _, hForm k₀ jz, h1, hForm_homog k₀ jz, hdeg, ?_, hh, (div_mul_cancel₀ _ hh).symm⟩` and prove the remaining obligations. Simplify using `using h2`.
-/
theorem ampleQ_of_forms (y : (Σ k, J k) → Ω) (k₀ : K) (a : K → ℤ) (ha₀ : a k₀ = 1) (ha : ∀ k, k ≠ k₀ → a k = 0)
    (l : K → ℕ) (n : ∀ k, Fin (l k) → ℕ) (F : ∀ k, Fin (l k) → J k → MvPolynomial (J k₀) ℤ)
    (hom : ∀ k t j, (F k t j).IsHomogeneous (n k t))
    (rel : ∀ k t j j', aeval (fun i => y ⟨k₀, i⟩) (F k t j) * y ⟨k, j'⟩ =
      aeval (fun i => y ⟨k₀, i⟩) (F k t j') * y ⟨k, j⟩)
    (pts : ∀ k (L : Type) [Field L] [CharZero L] (z : (Σ k, J k) → L), z ∈ Small.ptsOver L (mCoordIdeal y) →
      ∃ t j, aeval (fun i => z ⟨k₀, i⟩) (F k t j) ≠ 0) :
    Ht.AmpleQ y a := by
  by_cases hy : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0
  swap
  · push_neg at hy
    obtain ⟨k, hk⟩ := hy
    refine ⟨0, 0, Fin.elim0, fun i => i.elim0, fun L _ _ z hz => ?_⟩
    exfalso
    obtain ⟨i, hi⟩ := hz.1 k
    have hm : (X ⟨k, i⟩ : MRing J) ∈ mCoordIdeal y := by
      change mConeMap y _ = 0
      simp [mConeMap, hk i]
    exact hi (by simpa using hz.2 _ hm)
  choose js hjs using hy

  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ T : ∀ k, Fin (l k), ∑ k ∈ Finset.univ.erase k₀, n k (T k) ≤ N := by
    refine ⟨∑ k, ∑ t, n k t, fun T => ?_⟩
    calc ∑ k ∈ Finset.univ.erase k₀, n k (T k) ≤ ∑ k ∈ Finset.univ.erase k₀, ∑ t, n k t :=
          Finset.sum_le_sum fun k _ => Finset.single_le_sum (f := n k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
  let eT : (∀ k, Fin (l k)) → ℕ := fun T => N - ∑ k ∈ Finset.univ.erase k₀, n k (T k)
  have heT : ∀ T, eT T + ∑ k ∈ Finset.univ.erase k₀, n k (T k) = N := fun T => Nat.sub_add_cancel (hN T)
  let I := (∀ k, Fin (l k)) × J k₀
  let S : I → Ω := fun p => sec y k₀ js p.2 (eT p.1) fun k => F k (p.1 k) (js k)
  have hdeg : ∀ k, ((Pi.single k₀ N : K → ℕ) k : ℤ) = hDeg k₀ k + (((N + 1 : ℕ) : ℤ) * a k - 1) := by
    intro k
    by_cases hk : k = k₀
    · subst hk
      simp [hDeg, ha₀]
    · simp [hDeg, Pi.single_apply, hk, ha k hk]

  have hform : ∀ (p : I) (j : ∀ k, J k), IsMultiHomog (gForm k₀ p.2 (eT p.1) fun k => F k (p.1 k) (j k))
      (Pi.single k₀ N) ∧ aeval y (gForm k₀ p.2 (eT p.1) fun k => F k (p.1 k) (j k)) = S p * aeval y (hForm k₀ j) := by
    intro p j
    refine ⟨?_, sec_mul y k₀ js j hjs _ _ _ _ fun k => rel k (p.1 k) (js k) (j k)⟩
    have := gForm_homog k₀ p.2 (eT p.1) (G := fun k => F k (p.1 k) (j k)) (d := fun k => n k (p.1 k))
      fun k => hom k _ _
    rwa [heT] at this
  refine ⟨N + 1, Fintype.card I, fun q => S ((Fintype.equivFin I).symm q), fun q c hc => ?_, fun L _ _ z hz => ?_⟩
  · obtain ⟨h1, h2⟩ := hform ((Fintype.equivFin I).symm q) c
    have h3 := FibreNormDehomRoots.aeval_mem_chartLatNm h1 c hc
    convert h3 using 1
    rw [h2, aeval_hForm, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k₀),
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k₀)]
    have e1 : ∏ k ∈ Finset.univ.erase k₀, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (((N + 1 : ℕ) : ℤ) * a k - 1))) =
        ∏ k ∈ Finset.univ.erase k₀, y ⟨k, c k⟩ := by
      refine Finset.prod_congr rfl fun k hk => ?_
      simp [ha k (Finset.ne_of_mem_erase hk)]
    have e2 : ∏ k ∈ Finset.univ.erase k₀, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * ((1 * (Pi.single k₀ N : K → ℕ) k : ℕ) : ℤ))) = 1 := by
      refine Finset.prod_eq_one fun k hk => ?_
      simp [Pi.single_apply, Finset.ne_of_mem_erase hk]
    rw [e1, e2]
    simp [ha₀]
    ring
  · obtain ⟨i, hi⟩ := hz.1 k₀
    choose T jz hF using fun k => pts k L z hz
    have hzj : ∀ k, z ⟨k, jz k⟩ ≠ 0 := by
      intro k h0
      obtain ⟨j', hj'⟩ := hz.1 k
      have := rel_at_point k₀ k (hom k (T k) (jz k)) (hom k (T k) j') (jz k) j' (rel k _ _ _) hz
      rw [h0, mul_zero] at this
      exact mul_ne_zero (hF k) hj' this
    obtain ⟨h1, h2⟩ := hform (T, i) jz
    have hg : aeval z (gForm k₀ i (eT T) fun k => F k (T k) (jz k)) ≠ 0 := by
      rw [aeval_gForm]
      exact mul_ne_zero (pow_ne_zero _ hi) (Finset.prod_ne_zero_iff.mpr fun k _ => hF k)
    have hh : aeval z (hForm k₀ jz) ≠ 0 := by
      rw [aeval_hForm]
      exact Finset.prod_ne_zero_iff.mpr fun k _ => hzj k
    refine ⟨Fintype.equivFin I (T, i), _ / _, div_ne_zero hg hh, Pi.single k₀ N, hDeg k₀, _, hForm k₀ jz, h1,
      hForm_homog k₀ jz, hdeg, ?_, hh, (div_mul_cancel₀ _ hh).symm⟩
    simpa using h2

/- English proof (translation)
Introduce `X Ω _ _ ξ K _ J _ y k₀ a hT hE ha₀ ha`. Use `choose l n F hom rel pts using GlobalTheory.T.coord_relations_homogeneous X Ω ξ K J y k₀ hT hE`. Conclude with `ampleQ_of_forms y k₀ a ha₀ ha l n F hom rel fun k L _ _ z hz => pts k L z hz`.
-/
theorem ampleQ_of_embeds : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K) (a : K → ℤ), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → a k₀ = 1 → (∀ k, k ≠ k₀ → a k = 0) → Ht.AmpleQ y a := by
  intro X Ω _ _ ξ K _ J _ y k₀ a hT hE ha₀ ha
  classical
  choose l n F hom rel pts using GlobalTheory.T.coord_relations_homogeneous X Ω ξ K J y k₀ hT hE
  exact ampleQ_of_forms y k₀ a ha₀ ha l n F hom rel fun k L _ _ z hz => pts k L z hz

end GlobalTheory.CompanionTheory.Ar.AmpleBlock
