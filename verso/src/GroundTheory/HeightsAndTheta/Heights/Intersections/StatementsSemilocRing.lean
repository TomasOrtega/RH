import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.IdDeg
import GroundTheory.HeightsAndTheta.Heights.Intersections.LocRing
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

section Semiloc

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def semiLocRing (P : Ideal (MRing ι)) (𝒲 : Set (Ideal (MRing ι))) : Subring (FractionRing (MRing ι ⧸ P)) :=
  Subring.closure {x | ∃ (u w : MRing ι) (a : K → ℕ)
    (hw : Ideal.Quotient.mk P w ∈ nonZeroDivisors (MRing ι ⧸ P)),
    (∀ W ∈ 𝒲, w ∉ W) ∧ IsMultiHomog u a ∧ IsMultiHomog w a ∧
      x = IsLocalization.mk' (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) ⟨_, hw⟩}

end Semiloc

section Block

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

def fibreOver (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (W : Ideal (MRing ι)) :
    Set (Ideal (MRing ι')) :=
  {W' | IsMultiProjPrime W' ∧ P' ≤ W' ∧ imageZ v W' = W}

open Classical in

/- English proof (translation)
Introduce `m' hm' k'`. Rewrite `hm'` using `[support_rename_of_injective hv.2.1, Finset.mem_image]`. Take `⟨m, hm, rfl⟩` from `hm'`. Establish `hblock : ∀ (F : (Σ k', ι' k') → ℕ), ∑ i, F ⟨k', i⟩ = ∑ q, if q.1 = k' then F q else 0`. Introduce `F`.

Rewrite using `[Fintype.sum_sigma, Finset.sum_eq_single k']`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[hb]`. Simplify using the standard rewrite rules.

Rewrite using `[hblock]`. Establish `h1 : (∑ q, if q.1 = k' then Finsupp.mapDomain v m q else 0) = ∑ p, if κ p.1 = k' then m p else 0`. Use `Finsupp.sum_mapDomain_index_inj (h := fun (q : Σ k', ι' k') (n : ℕ) => if q.1 = k' then n else 0) (s := m) hv.2.1` as an intermediate fact. Rewrite `this` using `[Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp)]`. Simplify `this` using `[hv.2.2.1]`.

Establish `h2 : (∑ p : Σ k, ι k, if κ p.1 = k' then m p else 0) = ∑ k, if κ k = k' then a k else 0`. Rewrite using `[Fintype.sum_sigma]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `split_ifs with hk`. Conclude with `hf m hm k`.

Simplify using the standard rewrite rules. Use `h1.trans h2` and compare the differences between its conclusion and the goal. Distinguish the cases in `h : ∃ k, κ k = k'`. Take `⟨k, rfl⟩` from `h`. Rewrite using `[hv.1.extend_apply, Finset.sum_eq_single k]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[hv.1.ne hb]`. Simplify using the standard rewrite rules. Rewrite using `[Function.extend_apply' _ _ _ h]`.

Use `(Finset.sum_eq_zero fun k _ => ?_).symm` and prove the remaining obligations. Rewrite using `[if_neg fun hk => h ⟨k, hk⟩]`.
-/
theorem rename_isMultiHomog {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) :
    IsMultiHomog (rename v f) (Function.extend κ a 0) := by
  intro m' hm' k'
  rw [support_rename_of_injective hv.2.1, Finset.mem_image] at hm'
  obtain ⟨m, hm, rfl⟩ := hm'
  have hblock : ∀ (F : (Σ k', ι' k') → ℕ), ∑ i, F ⟨k', i⟩ = ∑ q, if q.1 = k' then F q else 0 := by
    intro F
    rw [Fintype.sum_sigma, Finset.sum_eq_single k']
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  rw [hblock]
  have h1 : (∑ q, if q.1 = k' then Finsupp.mapDomain v m q else 0) =
      ∑ p, if κ p.1 = k' then m p else 0 := by
    have := Finsupp.sum_mapDomain_index_inj (h := fun (q : Σ k', ι' k') (n : ℕ) => if q.1 = k' then n else 0)
      (s := m) hv.2.1
    rw [Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp)] at this
    simpa [hv.2.2.1] using this
  have h2 : (∑ p : Σ k, ι k, if κ p.1 = k' then m p else 0) = ∑ k, if κ k = k' then a k else 0 := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · exact hf m hm k
    · simp
  convert h1.trans h2
  by_cases h : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := h
    rw [hv.1.extend_apply, Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [hv.1.ne hb]
    · simp
  · rw [Function.extend_apply' _ _ _ h]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    rw [if_neg fun hk => h ⟨k, hk⟩]

abbrev quotMapZ (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) :
    MRing ι ⧸ imageZ v P' →+* MRing ι' ⧸ P' :=
  Ideal.quotientMap P' (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom le_rfl

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
/- English proof (translation)
The claim follows from `Ideal.quotientMap_injective`.
-/
theorem quotMapZ_injective (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) :
    Function.Injective (quotMapZ v P') :=
  Ideal.quotientMap_injective

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in

/- English proof (translation)
The claim follows from `Ideal.comap_isPrime _ _`.
-/
theorem imageZ_isPrime_of_prime (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) [P'.IsPrime] :
    (imageZ v P').IsPrime :=
  Ideal.comap_isPrime _ _

def fracMapZ (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) [P'.IsPrime] :
    FractionRing (MRing ι ⧸ imageZ v P') →+* FractionRing (MRing ι' ⧸ P') :=
  haveI := imageZ_isPrime_of_prime v P'
  IsFractionRing.lift (g := (algebraMap (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P'))).comp (quotMapZ v P'))
    ((IsFractionRing.injective (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P'))).comp (quotMapZ_injective v P'))

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
/- English proof (translation)
Use `imageZ_isPrime_of_prime v P'` as an intermediate fact. Unfold `fracMapZ`. Rewrite using `[IsFractionRing.lift_algebraMap]`. Both sides reduce to the same expression.
-/
theorem fracMapZ_algebraMap (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) [P'.IsPrime] (f : MRing ι) :
    fracMapZ v P' (algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') f)) =
      algebraMap _ _ (Ideal.Quotient.mk P' (rename v f)) := by
  have := imageZ_isPrime_of_prime v P'
  unfold fracMapZ
  rw [IsFractionRing.lift_algebraMap]
  rfl

/- English proof (translation)
Use `imageZ_isPrime_of_prime v P'` as an intermediate fact. Establish `hle : locRing (imageZ v P') W ≤ (semiLocRing P' (fibreOver v P' W)).comap (fracMapZ v P')`. Rewrite using `[locRing, Subring.closure_le]`. Introduce and unpack `_ ⟨u, w, a, hw, hwW, hu, hwa, rfl⟩`. Rewrite using `[SetLike.mem_coe, Subring.mem_comap]`.

Establish `hw0 : rename v w ∉ P'`. Introduce `h`. Apply `nonZeroDivisors.ne_zero hw` to reduce the goal to its premises. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `h`.

Establish `hw' : Ideal.Quotient.mk P' (rename v w) ∈ nonZeroDivisors (MRing ι' ⧸ P')` using `mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])`. Apply `Subring.subset_closure` to reduce the goal to its premises. Use `⟨rename v u, rename v w, Function.extend κ a 0, hw', ?_, rename_isMultiHomog hv hu, rename_isMultiHomog hv hwa, ?_⟩` and prove the remaining obligations. Introduce and unpack `W' ⟨-, -, hW'⟩ hmem`. Apply `hwW` to reduce the goal to its premises.

Rewrite using `[← hW']`. Conclude with `hmem`. Rewrite using `[IsFractionRing.mk'_eq_div, IsFractionRing.mk'_eq_div, map_div₀]`. Conclude with `congrArg₂ (· / ·) (fracMapZ_algebraMap v P' u) (fracMapZ_algebraMap v P' w)`. Conclude with `hle hx`.
-/
theorem fracMapZ_mem {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    (P' : Ideal (MRing ι')) [P'.IsPrime] (W : Ideal (MRing ι)) (x : FractionRing (MRing ι ⧸ imageZ v P'))
    (hx : x ∈ locRing (imageZ v P') W) : fracMapZ v P' x ∈ semiLocRing P' (fibreOver v P' W) := by
  have := imageZ_isPrime_of_prime v P'
  have hle : locRing (imageZ v P') W ≤ (semiLocRing P' (fibreOver v P' W)).comap (fracMapZ v P') := by
    rw [locRing, Subring.closure_le]
    rintro _ ⟨u, w, a, hw, hwW, hu, hwa, rfl⟩
    rw [SetLike.mem_coe, Subring.mem_comap]
    have hw0 : rename v w ∉ P' := by
      intro h
      apply nonZeroDivisors.ne_zero hw
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact h
    have hw' : Ideal.Quotient.mk P' (rename v w) ∈ nonZeroDivisors (MRing ι' ⧸ P') :=
      mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
    apply Subring.subset_closure
    refine ⟨rename v u, rename v w, Function.extend κ a 0, hw', ?_, rename_isMultiHomog hv hu,
      rename_isMultiHomog hv hwa, ?_⟩
    · rintro W' ⟨-, -, hW'⟩ hmem
      apply hwW
      rw [← hW']
      exact hmem
    · rw [IsFractionRing.mk'_eq_div, IsFractionRing.mk'_eq_div, map_div₀]
      exact congrArg₂ (· / ·) (fracMapZ_algebraMap v P' u) (fracMapZ_algebraMap v P' w)
  exact hle hx

def locToSemiloc {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    (P' : Ideal (MRing ι')) [P'.IsPrime] (W : Ideal (MRing ι)) :
    locRing (imageZ v P') W →+* semiLocRing P' (fibreOver v P' W) :=
  (fracMapZ v P').restrict _ _ (fun x hx => fracMapZ_mem hv P' W x hx)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem locToSemiloc_coe {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    (P' : Ideal (MRing ι')) [P'.IsPrime] (W : Ideal (MRing ι)) (x : locRing (imageZ v P') W) :
    ((locToSemiloc hv P' W x : semiLocRing P' (fibreOver v P' W)) : FractionRing (MRing ι' ⧸ P')) =
      fracMapZ v P' x :=
  rfl

end Block

namespace SemilocRing

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

open Classical in

def blkW : (Σ k, ι k) → K → ℕ := fun p => Pi.single p.1 1

open Classical in

/- English proof (translation)
Introduce `m hm k`. Rewrite using `[← h (mem_support_iff.mp hm), Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single k]`. Simplify using `[blkW]`. Introduce `b _ hb`. Simplify using `[blkW, Ne.symm hb]`.

Simplify using the standard rewrite rules.
-/
theorem isMultiHomog_of_wh {s : MRing ι} {a : K → ℕ} (h : IsWeightedHomogeneous (blkW (ι := ι)) s a) :
    IsMultiHomog s a := by
  intro m hm k
  rw [← h (mem_support_iff.mp hm), Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp),
    Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp [blkW]
  · intro b _ hb
    simp [blkW, Ne.symm hb]
  · simp

/- English proof (translation)
Establish `h : IsWeightedHomogeneous (blkW (ι` using `ι)) (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k) (∑ k, α k • blkW (ι := ι) ⟨k, i k⟩) := IsWeightedHomogeneous.prod _ _ _ fun k _ => (isWeightedHomogeneous_X ℤ _ _).pow (α k)`. Establish `e : (∑ k, α k • blkW (ι` using `ι) ⟨k, i k⟩) = α := by`. Use function extensionality and compare the values at `k`. Simplify using `only [blkW, Finset.sum_apply]`. Rewrite using `[Finset.sum_eq_single k]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Ne.symm hb]`. Simplify using the standard rewrite rules. Rewrite `h` using `[e]`.

Conclude with `isMultiHomog_of_wh h`.
-/
theorem isMultiHomog_coordPow (i : ∀ k, ι k) (α : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k) α := by
  have h : IsWeightedHomogeneous (blkW (ι := ι)) (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k)
      (∑ k, α k • blkW (ι := ι) ⟨k, i k⟩) :=
    IsWeightedHomogeneous.prod _ _ _ fun k _ => (isWeightedHomogeneous_X ℤ _ _).pow (α k)
  have e : (∑ k, α k • blkW (ι := ι) ⟨k, i k⟩) = α := by
    funext k
    simp only [blkW, Finset.sum_apply]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  rw [e] at h
  exact isMultiHomog_of_wh h

end SemilocRing

/- English proof (translation)
Use `choose i hi using hW`. Use `⟨∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k, SemilocRing.isMultiHomog_coordPow i α, fun h => ?_⟩` and prove the remaining obligations. Take `⟨k, -, hk⟩` from `hWp.prod_mem_iff.mp h`. Conclude with `hi k (hWp.mem_of_pow_mem _ hk)`.
-/
theorem exists_form_notMem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {W : Ideal (MRing ι)}
    (hW : IsRelevant W) (hWp : W.IsPrime) (α : K → ℕ) : ∃ t : MRing ι, IsMultiHomog t α ∧ t ∉ W := by
  choose i hi using hW
  refine ⟨∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k, SemilocRing.isMultiHomog_coordPow i α, fun h => ?_⟩
  obtain ⟨k, -, hk⟩ := hWp.prod_mem_iff.mp h
  exact hi k (hWp.mem_of_pow_mem _ hk)

section Example

end Example

end GroundTheory.Heights₂.Heights.Inter
