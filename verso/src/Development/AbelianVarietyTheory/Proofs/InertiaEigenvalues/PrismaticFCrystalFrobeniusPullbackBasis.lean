import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinHomEisensteinSpanAndNonZeroDivisorStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

/- English proof (translation)
Rewrite using `[← LocalizedModule.zero_mk (1 : Submonoid.powers t), LocalizedModule.mk_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨_, r, rfl⟩, h⟩`. Conclude with `⟨r, by simpa [Submonoid.smul_def] using h⟩`. Introduce and unpack `⟨r, h⟩`.

Conclude with `⟨⟨t ^ r, r, rfl⟩, by simpa [Submonoid.smul_def] using h⟩`.
-/
theorem mk_one_eq_zero_iff_pow_smul {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (t : A) (x : M) :
    LocalizedModule.mk x (1 : Submonoid.powers t) = 0 ↔ ∃ r : ℕ, t ^ r • x = 0 := by
  rw [← LocalizedModule.zero_mk (1 : Submonoid.powers t), LocalizedModule.mk_eq]
  constructor
  · rintro ⟨⟨_, r, rfl⟩, h⟩
    exact ⟨r, by simpa [Submonoid.smul_def] using h⟩
  · rintro ⟨r, h⟩
    exact ⟨⟨t ^ r, r, rfl⟩, by simpa [Submonoid.smul_def] using h⟩

/- English proof (translation)
Proceed by induction on `z using LocalizedModule.induction_on with`. Consider the case `_ n s`. Take `⟨_, k, rfl⟩` from `s`. Conclude with `⟨n, k, rfl⟩`.
-/
theorem exists_eq_mk_pow {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (t : A)
    (z : LocalizedModule (Submonoid.powers t) M) :
    ∃ (n : M) (k : ℕ), IsFrac t z n k := by
  induction z using LocalizedModule.induction_on with
  | _ n s =>
    obtain ⟨_, k, rfl⟩ := s
    exact ⟨n, k, rfl⟩

/- English proof (translation)
Rewrite using `[h, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]`. Conclude with `⟨1, by simp [Submonoid.smul_def]⟩`.
-/
theorem mk_one_eq_pow_smul_of_isFrac {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (t : A)
    (z : LocalizedModule (Submonoid.powers t) M) (m : M) (k : ℕ) (h : IsFrac t z m k) :
    LocalizedModule.mk m (1 : Submonoid.powers t) = t ^ k • z := by
  rw [h, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
  exact ⟨1, by simp [Submonoid.smul_def]⟩

/- English proof (translation)
Rewrite using `[← mk_one_eq_zero_iff_pow_smul]`. Establish `h1` using `mk_one_eq_pow_smul_of_isFrac t Z m k hm`. Establish `hlin : ∀ x : M, LocalizedModule.mk x (1 : Submonoid.powers t) = LocalizedModule.mkLinearMap (Submonoid.powers t) M x` using `fun _ => rfl`. Rewrite using `[hlin, map_sub, map_smul, map_smul, map_sum]`. Simplify using `only [map_smul, ← hlin, hw, h1, hZ, Finset.smul_sum, smul_smul]`.

Rewrite using `[sub_eq_zero]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← LocalizedModule.smul'_mk, hw, smul_smul, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_pow_smul_eq_zero_of_sum {A M ι : Type} [CommRing A] [AddCommGroup M] [Module A M] [Fintype ι]
    (t c : A) (m : M) (k : ℕ) (v : ι → A) (w : ι → M) (z : ι → LocalizedModule (Submonoid.powers t) M)
    (Z : LocalizedModule (Submonoid.powers t) M) (hm : IsFrac t Z m k) (hZ : Z = ∑ j, v j • z j)
    (hw : ∀ j, LocalizedModule.mk (w j) (1 : Submonoid.powers t) = c • z j) :
    ∃ r : ℕ, t ^ r • (c • m - t ^ k • ∑ j, v j • w j) = 0 := by
  rw [← mk_one_eq_zero_iff_pow_smul]
  have h1 := mk_one_eq_pow_smul_of_isFrac t Z m k hm
  have hlin : ∀ x : M, LocalizedModule.mk x (1 : Submonoid.powers t) =
      LocalizedModule.mkLinearMap (Submonoid.powers t) M x := fun _ => rfl
  rw [hlin, map_sub, map_smul, map_smul, map_sum]
  simp only [map_smul, ← hlin, hw, h1, hZ, Finset.smul_sum, smul_smul]
  rw [sub_eq_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← LocalizedModule.smul'_mk, hw, smul_smul, smul_smul]
  congr 1
  ring

/- English proof (translation)
Take `⟨n, s, hn⟩` from `exists_eq_mk_pow (d' : P'.A) (M.Φ P' d' (M.tr f x))`. Take `⟨r, hr⟩` from `M.Φ_nat f d d' x mx k n s h hn`. Rewrite `hr` using `[mul_pow, mul_smul]`. Establish `hr'` using `(hreg.pow r).right_eq_zero_of_smul hr`. Rewrite `hr'` using `[smul_sub, sub_eq_zero]`.

Rewrite using `[hn, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]`. Use `⟨⟨(d' : P'.A) ^ r, r, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify `hr'` using `[Submonoid.smul_def]`.
-/
theorem mk_tr_eq_smul_Φ_tr {l : ℕ} {R : Type} [CommRing R] (M : FCrys l R) {P P' : Obj l R} (f : Hom P P')
    (d : ↥P.I) (d' : ↥P'.I) (x mx : M.M P) (k : ℕ) (hreg : IsSMulRegular (M.M P') (f.f d))
    (h : IsFrac (d : P.A) (M.Φ P d x) mx k) :
    LocalizedModule.mk (M.tr f mx) (1 : Submonoid.powers (d' : P'.A)) = f.f d ^ k • M.Φ P' d' (M.tr f x) := by
  obtain ⟨n, s, hn⟩ := exists_eq_mk_pow (d' : P'.A) (M.Φ P' d' (M.tr f x))
  obtain ⟨r, hr⟩ := M.Φ_nat f d d' x mx k n s h hn
  rw [mul_pow, mul_smul] at hr
  have hr' := (hreg.pow r).right_eq_zero_of_smul hr
  rw [smul_sub, sub_eq_zero] at hr'
  rw [hn, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
  refine ⟨⟨(d' : P'.A) ^ r, r, rfl⟩, ?_⟩
  simpa [Submonoid.smul_def] using hr'

/- English proof (translation)
Establish `hreg : IsSMulRegular (M.M Q) (BK.hf g bk.E)` using `by haveI := M.proj Q`. Conclude with `Module.Flat.isSMulRegular_of_nonZeroDivisors (GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk Q g).2`. Establish `key : ∀ j : Fin d, LocalizedModule.mk (M.tr g (∑ i, bk.toP (A i j) • e i)) (1 : Submonoid.powers (t : Q.A)) = BK.hf g bk.E ^ a • M.Φ Q t (M.tr g (e j))` using `fun j => mk_tr_eq_smul_Φ_tr M g ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩ t (e j) _ a hreg (hA j)`. Establish `hsum : ∑ i, (A.map (BK.hf g)).mulVec (fun j => Q.D.φ (y j)) i • M.tr g (e i) = ∑ j, Q.D.φ (y j) • M.tr g (∑ i, bk.toP (A i j) • e i)`. Simplify using `only [map_sum, LinearMap.map_smulₛₗ, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Both sides reduce to the same expression. Establish `hΦ : M.Φ Q t (∑ j, y j • M.tr g (e j)) = ∑ j, Q.D.φ (y j) • M.Φ Q t (M.tr g (e j))`.

Simplify using `only [map_sum, LinearMap.map_smulₛₗ, RingHom.comp_apply, algebraMap_smul]`. Rewrite using `[hsum]`. Conclude with `exists_pow_smul_eq_zero_of_sum (t : Q.A) (BK.hf g bk.E ^ a) m k (fun j => Q.D.φ (y j)) (fun j => M.tr g (∑ i, bk.toP (A i j) • e i)) (fun j => M.Φ Q t (M.tr g (e j))) _ hm hΦ key`.
-/
theorem frob_tr_basis (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (M : FCrys l ↥(OL K))
    (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) (a : ℕ) (A : Matrix (Fin d) (Fin d) bk.S)
    (hA : ∀ j : Fin d, IsFrac (bk.toP bk.E) (M.Φ bk.prism ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩ (e j))
      (∑ i, bk.toP (A i j) • e i) a)
    (Q : Obj l ↥(OL K)) (g : Hom bk.prism Q) (t : ↥Q.I) (y : Fin d → Q.A) (m : M.M Q) (k : ℕ)
    (hm : IsFrac (t : Q.A) (M.Φ Q t (∑ j, y j • M.tr g (e j))) m k) :
    ∃ r : ℕ, (t : Q.A) ^ r • (BK.hf g bk.E ^ a • m - (t : Q.A) ^ k •
      ∑ i, (A.map (BK.hf g)).mulVec (fun j => Q.D.φ (y j)) i • M.tr g (e i)) = 0 := by
  have hreg : IsSMulRegular (M.M Q) (BK.hf g bk.E) := by
    haveI := M.proj Q
    exact Module.Flat.isSMulRegular_of_nonZeroDivisors (GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk Q g).2

  have key : ∀ j : Fin d, LocalizedModule.mk (M.tr g (∑ i, bk.toP (A i j) • e i)) (1 : Submonoid.powers (t : Q.A)) =
      BK.hf g bk.E ^ a • M.Φ Q t (M.tr g (e j)) := fun j =>
    mk_tr_eq_smul_Φ_tr M g ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩ t (e j) _ a hreg (hA j)
  have hsum : ∑ i, (A.map (BK.hf g)).mulVec (fun j => Q.D.φ (y j)) i • M.tr g (e i) =
      ∑ j, Q.D.φ (y j) • M.tr g (∑ i, bk.toP (A i j) • e i) := by
    simp only [map_sum, LinearMap.map_smulₛₗ, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_smul,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]; rfl
  have hΦ : M.Φ Q t (∑ j, y j • M.tr g (e j)) = ∑ j, Q.D.φ (y j) • M.Φ Q t (M.tr g (e j)) := by
    simp only [map_sum, LinearMap.map_smulₛₗ, RingHom.comp_apply, algebraMap_smul]
  rw [hsum]
  exact exists_pow_smul_eq_zero_of_sum (t : Q.A) (BK.hf g bk.E ^ a) m k (fun j => Q.D.φ (y j))
    (fun j => M.tr g (∑ i, bk.toP (A i j) • e i)) (fun j => M.Φ Q t (M.tr g (e j))) _ hm hΦ key

end GlobalTheory.BSP
