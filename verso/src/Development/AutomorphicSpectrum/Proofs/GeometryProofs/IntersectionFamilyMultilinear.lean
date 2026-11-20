import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFamilyFlatHermStatement
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.SumRoots

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
The claim follows from `ContDiffOn.exp hs.neg`.
-/
theorem smooth_ofWeight (u : ((Σ k, ι k) → ℂ) → ℝ)
    (hu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z) (hs : SmoothFn u) :
    IsSmoothHerm (HermLine.ofWeight u hu) :=
  ContDiffOn.exp hs.neg

/- English proof (translation)
The claim follows from `ContDiffOn.mul hA hB`.
-/
theorem smooth_tensor {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    IsSmoothHerm (A.tensor B) :=
  ContDiffOn.mul hA hB

/- English proof (translation)
Introduce `m hm k`. Rewrite `hm` using `[← C_1, C_apply]`. Use `Finset.mem_singleton.mp (support_monomial_subset hm)` as an intermediate fact. Simplify using `[this]`.
-/
theorem homog_one : IsMultiHomog (1 : MRing ι) (fun _ => 0) := by
  intro m hm k
  rw [← C_1, C_apply] at hm
  have := Finset.mem_singleton.mp (support_monomial_subset hm)
  simp [this]

/- English proof (translation)
Establish `h1 : (1 : MRing ι) ∉ W` using `(Ideal.ne_top_iff_one W).mp hW.2.1.1.ne_top`. Rewrite using `[hI.2.2 W n L _ 1 (fun _ => 0) hW hL (smooth_ofWeight u hu hs) (fun k => by simp [HermLine.ofWeight]) homog_one h1]`. Establish `hd : divSupp W (1 : MRing ι) = ∅`. Use extensionality with `V`. Simplify using `[divSupp, Ideal.minimalPrimes_top]`.

Establish `hl : logNorm (HermLine.ofWeight u hu) (1 : MRing ι) = u`. Use function extensionality and compare the values at `z`. Simplify using `[logNorm, HermLine.ofWeight]`. Unfold `recR arInt`. Rewrite using `[hd, hl]`.

Simplify using `only [finsum_mem_empty, zero_sub]`. Both sides reduce to the same expression.
-/
theorem inter_ofWeight {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (hI : IsIntersectionFamily I) {W : Ideal (MRing ι)} {n : ℕ} {L : Fin n → HermLine ι}
    (hW : IsArithVar W (n + 1)) (hL : ∀ j, IsSmoothHerm (L j)) (u : ((Σ k, ι k) → ℂ) → ℝ)
    (hu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z) (hs : SmoothFn u) :
    I W (n + 1) (Fin.snoc L (HermLine.ofWeight u hu)) = -ptsIntegral W (pot L) u := by
  have h1 : (1 : MRing ι) ∉ W := (Ideal.ne_top_iff_one W).mp hW.2.1.1.ne_top
  rw [hI.2.2 W n L _ 1 (fun _ => 0) hW hL (smooth_ofWeight u hu hs) (fun k => by simp [HermLine.ofWeight])
    homog_one h1]
  have hd : divSupp W (1 : MRing ι) = ∅ := by
    ext V
    simp [divSupp, Ideal.minimalPrimes_top]
  have hl : logNorm (HermLine.ofWeight u hu) (1 : MRing ι) = u := by
    funext z
    simp [logNorm, HermLine.ofWeight]
  unfold recR arInt
  rw [hd, hl]
  simp only [finsum_mem_empty, zero_sub]
  rfl

noncomputable def tens : (N : ℕ) → (Fin N → HermLine ι) → HermLine ι
  | 0, _ => HermLine.ofWeight (fun _ => 0) (fun _ _ _ => rfl)
  | N + 1, x => (tens N (fun i => x i.castSucc)).tensor (x (Fin.last N))

/- English proof (translation)
The claim follows from `| 0, _ => by simp [tens, HermLine.ofWeight] | N + 1, x => by rw [Fin.sum_univ_castSucc, ← tens_a N (fun i => x i.castSucc)] rfl`.
-/
theorem tens_a : ∀ (N : ℕ) (x : Fin N → HermLine ι), (tens N x).a = ∑ i, (x i).a
  | 0, _ => by simp [tens, HermLine.ofWeight]
  | N + 1, x => by
    rw [Fin.sum_univ_castSucc, ← tens_a N (fun i => x i.castSucc)]
    rfl

/- English proof (translation)
The claim follows from `| 0, _, _ => by simp [tens, HermLine.ofWeight] | N + 1, x, z => by rw [Fin.prod_univ_castSucc, ← tens_h N (fun i => x i.castSucc)] rfl`.
-/
theorem tens_h : ∀ (N : ℕ) (x : Fin N → HermLine ι) z, (tens N x).h z = ∏ i, (x i).h z
  | 0, _, _ => by simp [tens, HermLine.ofWeight]
  | N + 1, x, z => by
    rw [Fin.prod_univ_castSucc, ← tens_h N (fun i => x i.castSucc)]
    rfl

/- English proof (translation)
The claim follows from `| 0, _, _ => smooth_ofWeight _ _ contDiffOn_const | N + 1, x, hx => smooth_tensor (tens_smooth N _ fun _ => hx _) (hx _)`.
-/
theorem tens_smooth : ∀ (N : ℕ) (x : Fin N → HermLine ι), (∀ i, IsSmoothHerm (x i)) → IsSmoothHerm (tens N x)
  | 0, _, _ => smooth_ofWeight _ _ contDiffOn_const
  | N + 1, x, hx => smooth_tensor (tens_smooth N _ fun _ => hx _) (hx _)

/- English proof (translation)
Unfold `ptsIntegral`. Use `split_ifs with h`. Establish `: ∀ y w, sheetDensity W h.choose φ (fun _ => 0) y w = 0` using `fun y w => by`. Unfold `sheetDensity`. Apply the tactic sequence `split_ifs <;> simp`.

Simplify using `[ptsIntegralAt, this]`. Both sides reduce to the same expression.
-/
theorem ptsIntegral_zero (W : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral W φ (fun _ => 0) = 0 := by
  unfold ptsIntegral
  split_ifs with h
  · have : ∀ y w, sheetDensity W h.choose φ (fun _ => 0) y w = 0 := fun y w => by
      unfold sheetDensity
      split_ifs <;> simp
    simp [ptsIntegralAt, this]
  · rfl

/- English proof (translation)
The claim follows from `| 0, _, _ => by rw [tens, inter_ofWeight hI hW hL _ _ contDiffOn_const, ptsIntegral_zero] simp | N + 1, x, hx => by rw [tens, hI.2.1 W n L _ _ hW hL (tens_smooth N _ fun _ => hx _) (hx _), inter_tens hI hW hL N _ (fun _ => hx _), Fin.sum_univ_castSucc]`.
-/
theorem inter_tens {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (hI : IsIntersectionFamily I) {W : Ideal (MRing ι)} {n : ℕ} {L : Fin n → HermLine ι}
    (hW : IsArithVar W (n + 1)) (hL : ∀ j, IsSmoothHerm (L j)) :
    ∀ (N : ℕ) (x : Fin N → HermLine ι), (∀ i, IsSmoothHerm (x i)) →
      I W (n + 1) (Fin.snoc L (tens N x)) = ∑ i, I W (n + 1) (Fin.snoc L (x i))
  | 0, _, _ => by
    rw [tens, inter_ofWeight hI hW hL _ _ contDiffOn_const, ptsIntegral_zero]
    simp
  | N + 1, x, hx => by
    rw [tens, hI.2.1 W n L _ _ hW hL (tens_smooth N _ fun _ => hx _) (hx _),
      inter_tens hI hW hL N _ (fun _ => hx _), Fin.sum_univ_castSucc]

end GlobalTheory.CompanionTheory.Ar.Flat.SumRoots

/- English proof (translation)
Introduce `hP hM K _ ι _ Ω _ F _ _ y φ I W n L A S d N x v hI hV hO hyW hW hL hA hx hv hs ha hh`. Use `open GlobalTheory.CompanionTheory.Ar.Flat.SumRoots in`. Establish `hsn : ∀ B : HermLine ι, IsSmoothHerm B → ∀ j, IsSmoothHerm ((Fin.snoc L B : Fin (n + 1) → HermLine ι) j)` using `fun B hB j => by`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => simpa using hB`.

Consider the case `cast j => simpa using hL j`. Use `open GlobalTheory.CompanionTheory.Ar.Flat.SumRoots in`. Establish `hloc : I W (n + 1) (Fin.snoc L (tens N x)) = I W (n + 1) (Fin.snoc L (A.tensor (HermLine.ofWeight v hv)))`. Use `hM K ι I hI W (n + 1) _ _ hW (hsn _ (tens_smooth N x hx)) (hsn _ (smooth_tensor hA (smooth_ofWeight v hv hs))) (fun j => ?_) (fun j z hz => ?_)` and prove the remaining obligations. Proceed by induction on `j using Fin.lastCases with`.

Consider the case `last`. Simplify using `only [Fin.snoc_last]`. Rewrite using `[tens_a, ha]`. Simplify using `[HermLine.tensor, HermLine.ofWeight]`. Consider the case `cast j => simp only [Fin.snoc_castSucc]`.

Proceed by induction on `j using Fin.lastCases with`. Consider the case `last`. Simplify using `only [Fin.snoc_last]`. Rewrite using `[tens_h, hh z hz]`. Both sides reduce to the same expression.

Consider the case `cast j => simp only [Fin.snoc_castSucc]`. Use `open GlobalTheory.CompanionTheory.Ar.Flat.SumRoots in`. Rewrite using `[← inter_tens hI hW hL N x hx, hloc, hI.2.1 W n L _ _ hW hL hA (smooth_ofWeight v hv hs), inter_ofWeight hI hW hL v hv hs, GlobalTheory.T.intersection_family_flat_herm hP K ι Ω F y φ I W n L A S d hI hV hO hyW hW hL hA, sub_eq_add_neg]`.
-/
theorem GlobalTheory.CompanionTheory.Ar.Flat.sum_roots_eq : PtsIntegrableStatement → MetricLocalStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (W : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (A : HermLine ι) (S : FlatHerm y φ A) (d N : ℕ) (x : Fin N → HermLine ι) (v : ((Σ k, ι k) → ℂ) → ℝ), IsIntersectionFamily I → IsArithVar (mCoordIdeal y) d → OverInt y φ → mCoordIdeal y ≤ W → IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → (∀ i, IsSmoothHerm (x i)) → (∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → v (fun p => c p.1 * z p) = v z) → SmoothFn v → ∑ i, (x i).a = A.a → (∀ z ∈ mcPts W, ∏ i, (x i).h z = A.h z * Real.exp (-v z)) → ∑ i, I W (n + 1) (Fin.snoc L (x i)) = S.ht * ptsIntegral W (pot L) (fun _ => 1) - ptsIntegral W (pot L) v := by
  intro hP hM K _ ι _ Ω _ F _ _ y φ I W n L A S d N x v hI hV hO hyW hW hL hA hx hv hs ha hh
  open GlobalTheory.CompanionTheory.Ar.Flat.SumRoots in
  have hsn : ∀ B : HermLine ι, IsSmoothHerm B →
      ∀ j, IsSmoothHerm ((Fin.snoc L B : Fin (n + 1) → HermLine ι) j) := fun B hB j => by
    induction j using Fin.lastCases with
    | last => simpa using hB
    | cast j => simpa using hL j
  open GlobalTheory.CompanionTheory.Ar.Flat.SumRoots in
  have hloc : I W (n + 1) (Fin.snoc L (tens N x)) =
      I W (n + 1) (Fin.snoc L (A.tensor (HermLine.ofWeight v hv))) := by
    refine hM K ι I hI W (n + 1) _ _ hW (hsn _ (tens_smooth N x hx))
      (hsn _ (smooth_tensor hA (smooth_ofWeight v hv hs))) (fun j => ?_) (fun j z hz => ?_)
    · induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        rw [tens_a, ha]
        simp [HermLine.tensor, HermLine.ofWeight]
      | cast j => simp only [Fin.snoc_castSucc]
    · induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        rw [tens_h, hh z hz]
        rfl
      | cast j => simp only [Fin.snoc_castSucc]
  open GlobalTheory.CompanionTheory.Ar.Flat.SumRoots in
  rw [← inter_tens hI hW hL N x hx, hloc, hI.2.1 W n L _ _ hW hL hA (smooth_ofWeight v hv hs),
    inter_ofWeight hI hW hL v hv hs,
    GlobalTheory.T.intersection_family_flat_herm hP K ι Ω F y φ I W n L A S d hI hV hO hyW hW hL hA, sub_eq_add_neg]
