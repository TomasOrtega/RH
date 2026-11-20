import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIntegralExpression
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalZeroOfMemHomogeneousIdeal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealComponentMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusMonomialEvalCompat
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace GlobalTheory.CompanionTheory.GeoInteg

/- English proof (translation)
Rewrite using `[HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']`. Rewrite using `[IsLocalization.mk'_eq_iff_eq_mul]`. Establish `h : algebraMap _ (Localization.Away g) g * IsLocalization.Away.invSelf g = 1` using `IsLocalization.Away.mul_invSelf g`. Simplify using `only [map_pow]`. Rewrite using `[mul_assoc, ← mul_pow, mul_comm _ (algebraMap _ _ g), h, one_pow, mul_one]`.
-/
theorem away_val_mk {K : Type} [Field K] {N : ℕ} {g : MvPolynomial (Fin (N + 1)) K} {D : ℕ}
    (hg : g ∈ grK K N D) (n : ℕ) (x : MvPolynomial (Fin (N + 1)) K) (hx : x ∈ grK K N (n • D)) :
    (HomogeneousLocalization.Away.mk (grK K N) hg n x hx).val =
      algebraMap _ (Localization.Away g) x * (IsLocalization.Away.invSelf g : Localization.Away g) ^ n := by
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  rw [IsLocalization.mk'_eq_iff_eq_mul]
  have h : algebraMap _ (Localization.Away g) g * IsLocalization.Away.invSelf g = 1 :=
    IsLocalization.Away.mul_invSelf g
  simp only [map_pow]
  rw [mul_assoc, ← mul_pow, mul_comm _ (algebraMap _ _ g), h, one_pow, mul_one]

/- English proof (translation)
Establish `val_sum : ∀ (t : Finset ℕ) (u : ℕ → HomogeneousLocalization.Away (grK K N) g), (∑ l ∈ t, u l).val = ∑ l ∈ t, (u l).val` using `fun t u => map_sum (algebraMap (HomogeneousLocalization.Away (grK K N) g) (Localization.Away g)) u t`. Apply `HomogeneousLocalization.val_injective` to reduce the goal to its premises. Simplify using `only [HomogeneousLocalization.val_add, HomogeneousLocalization.val_pow, HomogeneousLocalization.val_mul, val_sum, away_val_mk]`. Rewrite using `[hFe]`. Simplify using `only [map_add, map_sum, map_mul, map_pow, add_mul, Finset.sum_mul]`.

Use `congr 1`. Rewrite using `[mul_pow, ← pow_mul, mul_comm s r]`. Use `Finset.sum_congr rfl fun l hl => ?_` and prove the remaining obligations. Establish `hl' : l ≤ s` using `(Finset.mem_range.1 hl).le`. Establish `: s * r = (s - l) * r + r * l`.

Take `⟨u, rfl⟩` from `Nat.exists_eq_add_of_le hl'`. Simplify using `only [Nat.add_sub_cancel_left]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, pow_add, mul_pow, ← pow_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem away_relation {K : Type} [Field K] {N : ℕ} {g : MvPolynomial (Fin (N + 1)) K} {D : ℕ}
    (hg : g ∈ grK K N D) (r s : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f ∈ grK K N (r • D))
    (c : ℕ → MvPolynomial (Fin (N + 1)) K) (hc : ∀ l, c l ∈ grK K N (((s - l) * r) • D))
    (F : MvPolynomial (Fin (N + 1)) K) (hF : F ∈ grK K N ((s * r) • D))
    (hFe : F = f ^ s + ∑ l ∈ Finset.range s, c l * f ^ l) :
    HomogeneousLocalization.Away.mk (grK K N) hg r f hf ^ s +
      ∑ l ∈ Finset.range s, HomogeneousLocalization.Away.mk (grK K N) hg _ (c l) (hc l) *
        HomogeneousLocalization.Away.mk (grK K N) hg r f hf ^ l =
      HomogeneousLocalization.Away.mk (grK K N) hg _ F hF := by
  have val_sum : ∀ (t : Finset ℕ) (u : ℕ → HomogeneousLocalization.Away (grK K N) g),
      (∑ l ∈ t, u l).val = ∑ l ∈ t, (u l).val := fun t u =>
    map_sum (algebraMap (HomogeneousLocalization.Away (grK K N) g) (Localization.Away g)) u t
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_add, HomogeneousLocalization.val_pow,
    HomogeneousLocalization.val_mul, val_sum, away_val_mk]
  rw [hFe]
  simp only [map_add, map_sum, map_mul, map_pow, add_mul, Finset.sum_mul]
  congr 1
  · rw [mul_pow, ← pow_mul, mul_comm s r]
  · refine Finset.sum_congr rfl fun l hl => ?_
    have hl' : l ≤ s := (Finset.mem_range.1 hl).le
    have : s * r = (s - l) * r + r * l := by
      obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hl'
      simp only [Nat.add_sub_cancel_left]
      ring
    rw [this, pow_add, mul_pow, ← pow_mul]
    ring

/- English proof (translation)
Establish `hf' : f.IsHomogeneous (r • D)` using `(MvPolynomial.mem_homogeneousSubmodule _ _).1 hf`. Use `add_mem ?_ (sum_mem fun l hl => ?_)` and prove the remaining obligations. Rewrite using `[MvPolynomial.mem_homogeneousSubmodule]`. Use `hf'.pow s using 1` and compare the differences between its conclusion and the goal. Simplify using `only [smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hl' : l ≤ s` using `(Finset.mem_range.1 hl).le`. Rewrite using `[MvPolynomial.mem_homogeneousSubmodule]`. Use `((MvPolynomial.mem_homogeneousSubmodule _ _).1 (hc l)).mul (hf'.pow l) using 1` and compare the differences between its conclusion and the goal. Take `⟨u, rfl⟩` from `Nat.exists_eq_add_of_le hl'`.

Simplify using `only [Nat.add_sub_cancel_left, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rel_mem {K : Type} [Field K] {N : ℕ} {D : ℕ} (r s : ℕ) (f : MvPolynomial (Fin (N + 1)) K)
    (hf : f ∈ grK K N (r • D)) (c : ℕ → MvPolynomial (Fin (N + 1)) K)
    (hc : ∀ l, c l ∈ grK K N (((s - l) * r) • D)) :
    f ^ s + ∑ l ∈ Finset.range s, c l * f ^ l ∈ grK K N ((s * r) • D) := by
  have hf' : f.IsHomogeneous (r • D) := (MvPolynomial.mem_homogeneousSubmodule _ _).1 hf
  refine add_mem ?_ (sum_mem fun l hl => ?_)
  · rw [MvPolynomial.mem_homogeneousSubmodule]
    convert hf'.pow s using 1
    simp only [smul_eq_mul]
    ring
  · have hl' : l ≤ s := (Finset.mem_range.1 hl).le
    rw [MvPolynomial.mem_homogeneousSubmodule]
    convert ((MvPolynomial.mem_homogeneousSubmodule _ _).1 (hc l)).mul (hf'.pow l) using 1
    obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hl'
    simp only [Nat.add_sub_cancel_left, smul_eq_mul]
    ring

/- English proof (translation)
Introduce `K _ X N d e i y hy V hV he q hq hfin S hS ht`. Use `letI := (strV q V).toAlgebra`. Introduce `a`. Establish `hg` using `yS_mem y hy S`. Take `⟨r, f, hf, rfl⟩` from `HomogeneousLocalization.Away.mk_surjective (grK K N) hg a`.

Distinguish the cases in `hS0 : S.card = 0`. Establish `hf0 : f.IsHomogeneous 0`. Use `(MvPolynomial.mem_homogeneousSubmodule _ _).1 hf` as an intermediate fact. Simplify `this` using `[hS0]`. Establish `hfC : f = MvPolynomial.C (MvPolynomial.coeff 0 f)` using `MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 hf0.totalDegree_le)`.

Establish `hc : (MvPolynomial.C (MvPolynomial.coeff 0 f) : MvPolynomial (Fin (d + 1)) K).IsHomogeneous (r * S.card)`. Rewrite using `[hS0, Nat.mul_zero]`. Conclude with `MvPolynomial.isHomogeneous_C _ _`. Establish `hmem` using `GlobalTheory.CompanionTheory.GeoTorus.aeval_mem_torusS i y hy hV he q hq S hS ht _ hc`. Establish `hfe : MvPolynomial.aeval y (MvPolynomial.C (MvPolynomial.coeff 0 f) : MvPolynomial (Fin (d + 1)) K) = f`.

Rewrite using `[MvPolynomial.aeval_C]`. Conclude with `hfC.symm`. Establish `heq : HomogeneousLocalization.Away.mk (grK K N) hg r (MvPolynomial.aeval y (MvPolynomial.C (MvPolynomial.coeff 0 f) : MvPolynomial (Fin (d + 1)) K)) (aeval_mem y hy S _ hc) = HomogeneousLocalization.Away.mk (grK K N) hg r f hf`. Simplify using `only [hfe]`. Rewrite `hmem` using `[heq]`.

Conclude with `isIntegral_algebraMap (R := torusS K (fun k => (ht k).unit) S) (x := ⟨_, hmem⟩)`. Establish `hD : 0 < S.card * e` using `Nat.mul_pos (Nat.pos_of_ne_zero hS0) he`. Establish `hfh : f.IsHomogeneous (e * (r * S.card))`. Use `(MvPolynomial.mem_homogeneousSubmodule _ _).1 hf` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨s, c, -, hc, hrel⟩` from `GlobalTheory.CompanionTheory.Geo.exists_hom_relation (homIdeal i) (GlobalTheory.CompanionTheory.Geo.homIdeal_homog i) e he y hy hfin (r * S.card) f hfh`. Establish `hc' : ∀ l, (c l).IsHomogeneous (((s - l) * r) * S.card)` using `fun l => by`. Rewrite using `[mul_assoc]`.

Conclude with `hc l`. Establish `hcm` using `fun l => aeval_mem y hy S (c l) (hc' l)`. Establish `hF` using `rel_mem r s f hf (fun l => MvPolynomial.aeval y (c l)) hcm`. Establish `hid` using `away_relation hg r s f hf (fun l => MvPolynomial.aeval y (c l)) hcm _ hF rfl`. Establish `hzero` using `GlobalTheory.CompanionTheory.GeoVanish.homIdeal_vanish i hD hg hF hrel V hS`.

Rewrite `hzero` using `[← hid]`. Rewrite `hzero` using `[map_add, map_sum]`. Simplify using `only [map_mul, map_pow] at hzero`. Establish `hco` using `fun l => GlobalTheory.CompanionTheory.GeoTorus.aeval_mem_torusS i y hy hV he q hq S hS ht (c l) (hc' l)`. Use `⟨Polynomial.X ^ s + ∑ l ∈ Finset.range s, Polynomial.C (⟨_, hco l⟩ : torusS K (fun k => (ht k).unit) S) * Polynomial.X ^ l, ?_, ?_⟩` and prove the remaining obligations.

Use `Polynomial.monic_X_pow_add ?_` and prove the remaining obligations. Rewrite using `[← Polynomial.mem_degreeLT]`. Use `Submodule.sum_mem _ fun l hl => ?_` and prove the remaining obligations. Rewrite using `[Polynomial.mem_degreeLT]`. Use `(Polynomial.degree_C_mul_X_pow_le l _).trans_lt ?_` and prove the remaining obligations.

Conclude with `Finset.mem_range.1 hl` after adjusting the coercions. Simplify using `only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_finset_sum, Polynomial.eval₂_mul, Polynomial.eval₂_C]`. Conclude with `hzero`.
-/
theorem isIntegral_torusS : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N) (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens} (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)), 0 < e → ∀ (q : X ⟶ Spec (CommRingCat.of K)), i ≫ PSpace.str K N = q → Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk (homIdeal i) (y k))) (MvPolynomial (Fin (N + 1)) K ⧸ homIdeal i) → ∀ (S : Finset (Fin (d + 1))) (hS : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S)) (ht : ∀ k, IsUnit (tV i y hy V hV k)), letI := (strV q V).toAlgebra; ∀ a, IsIntegral (torusS K (fun k => (ht k).unit) S) (evV i (yS y S) V hS a) := by
  intro K _ X N d e i y hy V hV he q hq hfin S hS ht
  letI := (strV q V).toAlgebra
  intro a
  have hg := yS_mem y hy S
  obtain ⟨r, f, hf, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (grK K N) hg a
  by_cases hS0 : S.card = 0
  ·
    have hf0 : f.IsHomogeneous 0 := by
      have := (MvPolynomial.mem_homogeneousSubmodule _ _).1 hf
      simpa [hS0] using this
    have hfC : f = MvPolynomial.C (MvPolynomial.coeff 0 f) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 hf0.totalDegree_le)
    have hc : (MvPolynomial.C (MvPolynomial.coeff 0 f) : MvPolynomial (Fin (d + 1)) K).IsHomogeneous (r * S.card) := by
      rw [hS0, Nat.mul_zero]
      exact MvPolynomial.isHomogeneous_C _ _
    have hmem := GlobalTheory.CompanionTheory.GeoTorus.aeval_mem_torusS i y hy hV he q hq S hS ht _ hc
    have hfe : MvPolynomial.aeval y (MvPolynomial.C (MvPolynomial.coeff 0 f) : MvPolynomial (Fin (d + 1)) K) = f := by
      rw [MvPolynomial.aeval_C]
      exact hfC.symm
    have heq : HomogeneousLocalization.Away.mk (grK K N) hg r (MvPolynomial.aeval y (MvPolynomial.C (MvPolynomial.coeff 0 f) : MvPolynomial (Fin (d + 1)) K)) (aeval_mem y hy S _ hc) = HomogeneousLocalization.Away.mk (grK K N) hg r f hf := by
      simp only [hfe]
    rw [heq] at hmem
    exact isIntegral_algebraMap (R := torusS K (fun k => (ht k).unit) S) (x := ⟨_, hmem⟩)
  · have hD : 0 < S.card * e := Nat.mul_pos (Nat.pos_of_ne_zero hS0) he
    have hfh : f.IsHomogeneous (e * (r * S.card)) := by
      have := (MvPolynomial.mem_homogeneousSubmodule _ _).1 hf
      convert this using 1
      simp only [smul_eq_mul]
      ring
    obtain ⟨s, c, -, hc, hrel⟩ := GlobalTheory.CompanionTheory.Geo.exists_hom_relation (homIdeal i) (GlobalTheory.CompanionTheory.Geo.homIdeal_homog i) e he y hy hfin (r * S.card) f hfh
    have hc' : ∀ l, (c l).IsHomogeneous (((s - l) * r) * S.card) := fun l => by
      rw [mul_assoc]
      exact hc l
    have hcm := fun l => aeval_mem y hy S (c l) (hc' l)
    have hF := rel_mem r s f hf (fun l => MvPolynomial.aeval y (c l)) hcm
    have hid := away_relation hg r s f hf (fun l => MvPolynomial.aeval y (c l)) hcm _ hF rfl
    have hzero := GlobalTheory.CompanionTheory.GeoVanish.homIdeal_vanish i hD hg hF hrel V hS
    rw [← hid] at hzero
    rw [map_add, map_sum] at hzero
    simp only [map_mul, map_pow] at hzero
    have hco := fun l => GlobalTheory.CompanionTheory.GeoTorus.aeval_mem_torusS i y hy hV he q hq S hS ht (c l) (hc' l)
    refine ⟨Polynomial.X ^ s + ∑ l ∈ Finset.range s,
      Polynomial.C (⟨_, hco l⟩ : torusS K (fun k => (ht k).unit) S) * Polynomial.X ^ l, ?_, ?_⟩
    · refine Polynomial.monic_X_pow_add ?_
      rw [← Polynomial.mem_degreeLT]
      refine Submodule.sum_mem _ fun l hl => ?_
      rw [Polynomial.mem_degreeLT]
      refine (Polynomial.degree_C_mul_X_pow_le l _).trans_lt ?_
      exact_mod_cast Finset.mem_range.1 hl
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_finset_sum, Polynomial.eval₂_mul, Polynomial.eval₂_C]
      exact hzero

end GlobalTheory.CompanionTheory.GeoInteg
