import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSegreHilb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  (F : Type) [Field F]

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]`. Simplify using `[blockWeight, Pi.single_apply]`.
-/
theorem weight_blockWeight_apply (e : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blockWeight ι) e k = ∑ i, e ⟨k, i⟩ := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_sigma]
  simp [blockWeight, Pi.single_apply]

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Use function extensionality and compare the values at `u`. Simplify using `[blockWeight]`.
-/
theorem blockWeight_unit (v : Σ _ : Unit, ∀ k, ι k) :
    blockWeight (fun _ : Unit => ∀ k, ι k) v = fun _ => 1 := by
  funext u
  simp [blockWeight]

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Proceed by induction on `hp using IsWeightedHomogeneous.induction_on with`. Consider the case `zero => rw [map_zero]`. Conclude with `isWeightedHomogeneous_zero _ _ _`. Consider the case `add p q _ _ hp hq => rw [map_add]`. Conclude with `hp.add hq`.

Consider the case `monomial d r hr`. Establish `hX : ∀ v : Σ _ : Unit, ∀ k, ι k, IsWeightedHomogeneous (blockWeight ι) (∏ k, (X ⟨k, v.2 k⟩ : MRing ι F)) (fun _ => 1)`. Introduce `v`. Establish `h` using `IsWeightedHomogeneous.prod (R := F) (w := blockWeight ι) Finset.univ (fun k => (X ⟨k, v.2 k⟩ : MRing ι F)) (fun k => blockWeight ι ⟨k, v.2 k⟩) (fun k _ => isWeightedHomogeneous_X _ _ _)`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `j`. Simplify using `[blockWeight, Finset.sum_apply, Pi.single_apply]`. Establish `hsum : ∑ v ∈ d.support, d v = m`. Establish `h` using `congrFun hr ()`. Rewrite `h` using `[Finsupp.weight_apply, Finsupp.sum]`.

Simplify `h` using `[blockWeight_unit, Finset.sum_apply]`. Establish `hdeg : (∑ v ∈ d.support, d v • (fun _ : K => 1) : K → ℕ) = fun _ => m`. Use function extensionality and compare the values at `k`. Simplify using `[Finset.sum_apply, hsum]`. Unfold `segreMap`.

Rewrite using `[aeval_monomial, algebraMap_eq, Finsupp.prod]`. Use `IsWeightedHomogeneous.C_mul ?_ r` and prove the remaining obligations. Rewrite using `[← hdeg]`. Conclude with `IsWeightedHomogeneous.prod _ _ _ fun v _ => (hX v).pow _`.
-/
theorem segreMap_isMultiHomog {m : ℕ} {p : MRing (fun _ : Unit => ∀ k, ι k) F}
    (hp : IsWeightedHomogeneous (blockWeight (fun _ : Unit => ∀ k, ι k)) p (fun _ => m)) :
    IsWeightedHomogeneous (blockWeight ι) (segreMap F p) (fun _ => m) := by
  classical
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => rw [map_zero]; exact isWeightedHomogeneous_zero _ _ _
  | add p q _ _ hp hq => rw [map_add]; exact hp.add hq
  | monomial d r hr =>
    have hX : ∀ v : Σ _ : Unit, ∀ k, ι k,
        IsWeightedHomogeneous (blockWeight ι) (∏ k, (X ⟨k, v.2 k⟩ : MRing ι F)) (fun _ => 1) := by
      intro v
      have h := IsWeightedHomogeneous.prod (R := F) (w := blockWeight ι) Finset.univ
        (fun k => (X ⟨k, v.2 k⟩ : MRing ι F)) (fun k => blockWeight ι ⟨k, v.2 k⟩)
        (fun k _ => isWeightedHomogeneous_X _ _ _)
      convert h using 1
      funext j
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    have hsum : ∑ v ∈ d.support, d v = m := by
      have h := congrFun hr ()
      rw [Finsupp.weight_apply, Finsupp.sum] at h
      simpa [blockWeight_unit, Finset.sum_apply] using h
    have hdeg : (∑ v ∈ d.support, d v • (fun _ : K => 1) : K → ℕ) = fun _ => m := by
      funext k
      simp [Finset.sum_apply, hsum]
    unfold segreMap
    rw [aeval_monomial, algebraMap_eq, Finsupp.prod]
    refine IsWeightedHomogeneous.C_mul ?_ r
    rw [← hdeg]
    exact IsWeightedHomogeneous.prod _ _ _ fun v _ => (hX v).pow _

omit [DecidableEq K] in

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Introduce `e he`. Establish `he0 : e = 0`. Use extensionality with `⟨k, i⟩`.

Conclude with `(Finset.sum_eq_zero_iff.mp (he k)) i (Finset.mem_univ _)`. Substitute `he0` using the available equality. Use `⟨1, ?_, ?_⟩` and prove the remaining obligations. Conclude with `isWeightedHomogeneous_one _ _`. Simplify using the standard rewrite rules.

Consider the case `succ m ih`. Introduce `e he`. Establish `hne : ∀ k, ∃ i, e ⟨k, i⟩ ≠ 0` using `fun k => by`. Take `⟨i, -, hi⟩` from `Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := fun i => e ⟨k, i⟩) (by rw [he k]; omega)`. Conclude with `⟨i, hi⟩`.

Use `choose f hf using hne`. Use `set s : (Σ k, ι k) →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun v => if v.2 = f v.1 then 1 else 0) with hs_def`. Establish `hs : ∀ k i, s ⟨k, i⟩ = if i = f k then 1 else 0` using `fun k i => by simp [hs_def]`. Establish `hse : s ≤ e`. Rewrite using `[Finsupp.le_def]`.

Introduce and unpack `⟨k, i⟩`. Rewrite using `[hs]`. Use `split_ifs with h`. Substitute `h` using the available equality. Conclude with `Nat.one_le_iff_ne_zero.mpr (hf k)`.

Conclude with `Nat.zero_le _`. Establish `hadd : e - s + s = e` using `tsub_add_cancel_of_le hse`. Establish `he' : ∀ k, ∑ i, (e - s) ⟨k, i⟩ = m` using `fun k => by`. Establish `h1 : ∑ i, (e - s) ⟨k, i⟩ + ∑ i, s ⟨k, i⟩ = m + 1`. Rewrite using `[← Finset.sum_add_distrib, ← he k]`.

Conclude with `Finset.sum_congr rfl fun i _ => by rw [← Finsupp.add_apply, hadd]`. Establish `h2 : ∑ i, s ⟨k, i⟩ = 1` using `by simp [hs]`. Use linear arithmetic over natural numbers and integers. Take `⟨g, hg, hge⟩` from `ih (e - s) he'`. Establish `hsX : monomial s (1 : F) = ∏ k, (X ⟨k, f k⟩ : MRing ι F)`.

Rewrite using `[monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `[hs]`. Use `⟨g * X ⟨(), f⟩, ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `(show IsWeightedHomogeneous _ g _ from hg).mul (isWeightedHomogeneous_X F (blockWeight (fun _ : Unit => ∀ k, ι k)) ⟨(), f⟩)`.

Rewrite `h` using `[blockWeight_unit]`. Conclude with `h`. Simplify using `only [AlgHom.toLinearMap_apply, map_mul] at hge ⊢`. Rewrite using `[hge, segreMap_X, ← hsX, monomial_mul, one_mul, hadd]`.
-/
theorem monomial_mem_map_segreMap (m : ℕ) :
    ∀ e : (Σ k, ι k) →₀ ℕ, (∀ k, ∑ i, e ⟨k, i⟩ = m) →
      monomial e (1 : F) ∈ (weightedHomogeneousSubmodule F
        (blockWeight (fun _ : Unit => ∀ k, ι k)) (fun _ => m)).map (segreMap F).toLinearMap := by
  classical
  induction m with
  | zero =>
    intro e he
    have he0 : e = 0 := by
      ext ⟨k, i⟩
      exact (Finset.sum_eq_zero_iff.mp (he k)) i (Finset.mem_univ _)
    subst he0
    refine ⟨1, ?_, ?_⟩
    · exact isWeightedHomogeneous_one _ _
    · simp
  | succ m ih =>
    intro e he
    have hne : ∀ k, ∃ i, e ⟨k, i⟩ ≠ 0 := fun k => by
      obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
        (f := fun i => e ⟨k, i⟩) (by rw [he k]; omega)
      exact ⟨i, hi⟩
    choose f hf using hne
    set s : (Σ k, ι k) →₀ ℕ :=
      Finsupp.equivFunOnFinite.symm (fun v => if v.2 = f v.1 then 1 else 0) with hs_def
    have hs : ∀ k i, s ⟨k, i⟩ = if i = f k then 1 else 0 := fun k i => by simp [hs_def]
    have hse : s ≤ e := by
      rw [Finsupp.le_def]
      rintro ⟨k, i⟩
      rw [hs]
      split_ifs with h
      · subst h; exact Nat.one_le_iff_ne_zero.mpr (hf k)
      · exact Nat.zero_le _
    have hadd : e - s + s = e := tsub_add_cancel_of_le hse
    have he' : ∀ k, ∑ i, (e - s) ⟨k, i⟩ = m := fun k => by
      have h1 : ∑ i, (e - s) ⟨k, i⟩ + ∑ i, s ⟨k, i⟩ = m + 1 := by
        rw [← Finset.sum_add_distrib, ← he k]
        exact Finset.sum_congr rfl fun i _ => by rw [← Finsupp.add_apply, hadd]
      have h2 : ∑ i, s ⟨k, i⟩ = 1 := by simp [hs]
      omega
    obtain ⟨g, hg, hge⟩ := ih (e - s) he'
    have hsX : monomial s (1 : F) = ∏ k, (X ⟨k, f k⟩ : MRing ι F) := by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
        Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      simp [hs]
    refine ⟨g * X ⟨(), f⟩, ?_, ?_⟩
    · have h := (show IsWeightedHomogeneous _ g _ from hg).mul
        (isWeightedHomogeneous_X F (blockWeight (fun _ : Unit => ∀ k, ι k)) ⟨(), f⟩)
      rw [blockWeight_unit] at h
      exact h
    · simp only [AlgHom.toLinearMap_apply, map_mul] at hge ⊢
      rw [hge, segreMap_X, ← hsX, monomial_mul, one_mul, hadd]

/- English proof (translation)
Use `le_antisymm ?_ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨p, hp, rfl⟩`. Conclude with `segreMap_isMultiHomog F hp`. Introduce `p hp`. Establish `hp' : IsWeightedHomogeneous (blockWeight ι) p (fun _ => m)` using `hp`.

Use `clear hp`. Proceed by induction on `hp' using IsWeightedHomogeneous.induction_on with`. Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `add p q _ _ hp hq => exact Submodule.add_mem _ hp hq`. Consider the case `monomial d r hr`.

Establish `hd : ∀ k, ∑ i, d ⟨k, i⟩ = m` using `fun k => by`. Rewrite using `[← weight_blockWeight_apply, hr]`. Establish `h` using `Submodule.smul_mem _ r (monomial_mem_map_segreMap F m d hd)`. Rewrite `h` using `[smul_monomial, smul_eq_mul, mul_one]`. Then use the resulting hypothesis.
-/
theorem map_segreMap_weightedHomogeneousSubmodule (m : ℕ) :
    (weightedHomogeneousSubmodule F (blockWeight (fun _ : Unit => ∀ k, ι k)) (fun _ => m)).map
        (segreMap F).toLinearMap =
      weightedHomogeneousSubmodule F (blockWeight ι) (fun _ => m) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨p, hp, rfl⟩
    exact segreMap_isMultiHomog F hp
  · intro p hp
    have hp' : IsWeightedHomogeneous (blockWeight ι) p (fun _ => m) := hp
    clear hp
    induction hp' using IsWeightedHomogeneous.induction_on with
    | zero => exact Submodule.zero_mem _
    | add p q _ _ hp hq => exact Submodule.add_mem _ hp hq
    | monomial d r hr =>
      have hd : ∀ k, ∑ i, d ⟨k, i⟩ = m := fun k => by
        rw [← weight_blockWeight_apply, hr]
      have h := Submodule.smul_mem _ r (monomial_mem_map_segreMap F m d hd)
      rwa [smul_monomial, smul_eq_mul, mul_one] at h

def segreQuotMap (q : Ideal (MRing ι F)) :
    MRing (fun _ : Unit => ∀ k, ι k) F ⧸ segrePrime F q →ₐ[F] MRing ι F ⧸ q :=
  Ideal.quotientMapₐ (I := segrePrime F q) q (segreMap F) fun _ h => h

omit [DecidableEq K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk q (segreMap F x) = 0 at ha`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_comap.mpr (Ideal.Quotient.eq_zero_iff_mem.mp ha))`.
-/
theorem segreQuotMap_injective (q : Ideal (MRing ι F)) : Function.Injective (segreQuotMap F q) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  change Ideal.Quotient.mk q (segreMap F x) = 0 at ha
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_comap.mpr (Ideal.Quotient.eq_zero_iff_mem.mp ha))

def segreGradedPieceEquiv (q : Ideal (MRing ι F)) (m : ℕ) :
    gradedPiece (segrePrime F q) (fun _ : Unit => m) ≃ₗ[F] gradedPiece q (fun _ : K => m) :=
  have hinj : Function.Injective (segreQuotMap F q).toLinearMap := segreQuotMap_injective F q
  have hmap : (gradedPiece (segrePrime F q) (fun _ : Unit => m)).map (segreQuotMap F q).toLinearMap =
      gradedPiece q (fun _ : K => m) := by
    have hc : (segreQuotMap F q).toLinearMap ∘ₗ (Ideal.Quotient.mkₐ F (segrePrime F q)).toLinearMap =
        (Ideal.Quotient.mkₐ F q).toLinearMap ∘ₗ (segreMap F).toLinearMap :=
      LinearMap.ext fun _ => rfl
    unfold gradedPiece
    rw [← Submodule.map_comp, hc, Submodule.map_comp, map_segreMap_weightedHomogeneousSubmodule]
  (Submodule.equivMapOfInjective _ hinj _).trans (LinearEquiv.ofEq _ _ hmap)

/- English proof (translation)
Introduce `F _ K _ _ _ ι _ q n`. Unfold `hilbFn`. Distinguish the cases in `hn : 0 ≤ n`. Rewrite using `[if_pos (fun _ => hn), if_pos (fun _ => hn)]`. Conclude with `congrArg (fun x : ℕ => (x : ℤ)) (segreGradedPieceEquiv F q n.toNat).finrank_eq`.

Rewrite using `[if_neg (fun h => hn (h ())), if_neg (fun h => hn (h (Classical.arbitrary K)))]`.
-/
theorem SegreHilb.proof : SegreHilb.Statement := by
  intro F _ K _ _ _ ι _ q n
  unfold hilbFn
  by_cases hn : 0 ≤ n
  · rw [if_pos (fun _ => hn), if_pos (fun _ => hn)]
    exact congrArg (fun x : ℕ => (x : ℤ)) (segreGradedPieceEquiv F q n.toNat).finrank_eq
  · rw [if_neg (fun h => hn (h ())), if_neg (fun h => hn (h (Classical.arbitrary K)))]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
