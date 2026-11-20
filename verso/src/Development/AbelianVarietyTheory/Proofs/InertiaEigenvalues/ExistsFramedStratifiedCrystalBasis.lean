import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeExistsBasisEqImageOfBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusMatrixFCrystalBreuilKisinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalFrobeniusPullbackBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinHomEisensteinSpanAndNonZeroDivisorStatement

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Establish `e1` using `congrArg (fun x => b.equivFun x i) h1`. Establish `e2` using `congrArg (fun x => b.equivFun x i) h2`. Simplify using `only [← b.equivFun_symm_apply, map_smul, map_sub, LinearEquiv.apply_symm_apply, map_zero, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at e1 e2`. Establish `f1` using `(mem_nonZeroDivisors_iff.1 (pow_mem ht r)).1 _ e1`. Establish `f2` using `(mem_nonZeroDivisors_iff.1 (pow_mem ht s)).1 _ e2`.

Rewrite using `[← sub_eq_zero]`. Apply `(mem_nonZeroDivisors_iff.1 (pow_mem ht k)).1` to reduce the goal to its premises. Take the linear combination `q * f1 - p * f2`.
-/
theorem frame_coord_cancel {B N : Type} [CommRing B] [AddCommGroup N] [Module B N] {d : ℕ}
    (b : Module.Basis (Fin d) B N) {t p q : B} (ht : t ∈ nonZeroDivisors B) {m : N} {k r s : ℕ}
    {v w : Fin d → B} (h1 : t ^ r • (p • m - t ^ k • ∑ i, v i • b i) = 0)
    (h2 : t ^ s • (q • m - t ^ k • ∑ i, w i • b i) = 0) (i : Fin d) : p * w i = q * v i := by
  have e1 := congrArg (fun x => b.equivFun x i) h1
  have e2 := congrArg (fun x => b.equivFun x i) h2
  simp only [← b.equivFun_symm_apply, map_smul, map_sub, LinearEquiv.apply_symm_apply, map_zero,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at e1 e2
  have f1 := (mem_nonZeroDivisors_iff.1 (pow_mem ht r)).1 _ e1
  have f2 := (mem_nonZeroDivisors_iff.1 (pow_mem ht s)).1 _ e2
  rw [← sub_eq_zero]
  apply (mem_nonZeroDivisors_iff.1 (pow_mem ht k)).1
  linear_combination q * f1 - p * f2

/- English proof (translation)
Simplify using `[Pi.single_apply]`.
-/
theorem frame_sum_single {B N : Type} [CommRing B] [AddCommGroup N] [Module B N] {d : ℕ} (v : Fin d → N)
    (j : Fin d) : ∑ i, (Pi.single j 1 : Fin d → B) i • v i = v j := by
  simp [Pi.single_apply]

/- English proof (translation)
Establish `h2 : (fun x => φ ((Pi.single j 1 : Fin d → B) x)) = Pi.single j 1`. Use extensionality with `x`. Apply the tactic sequence `by_cases hx : x = j <;> simp [hx]`. Simplify using `only [h2, Matrix.mulVec_single_one, Matrix.mul_apply, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[h x, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, mul_comm]`. Both sides reduce to the same expression.
-/
theorem frame_sum_mulVec {B N : Type} [CommRing B] [AddCommGroup N] [Module B N] {d : ℕ} (φ : B →+* B)
    (A ε : Matrix (Fin d) (Fin d) B) (v c : Fin d → N) (h : ∀ x, v x = ∑ i, ε i x • c i) (j : Fin d) :
    ∑ i, A.mulVec (fun x => φ ((Pi.single j 1 : Fin d → B) x)) i • v i = ∑ i, (ε * A) i j • c i := by
  have h2 : (fun x => φ ((Pi.single j 1 : Fin d → B) x)) = Pi.single j 1 := by
    ext x
    by_cases hx : x = j <;> simp [hx]
  simp only [h2, Matrix.mulVec_single_one, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [h x, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_smul, mul_comm]
  rfl

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ}

/- English proof (translation)
Take `⟨hI, ht⟩` from `GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk B f`. Set `t : ↥B.I` to `⟨BK.hf f bk.E, hI.ge (Ideal.mem_span_singleton_self _)⟩`. Use extensionality with `i j`. Take `⟨m, k, hm⟩` from `exists_isFrac (t : B.A) (M.Φ B t (M.tr g (e j)))`. Take `⟨r, hr⟩` from `GlobalTheory.T.prismaticFCrystal_frobenius_pullback_basis l K bk d M e a A hΦ B g t (Pi.single j 1) m k (Eq.subst (motive := fun z => IsFrac (t : B.A) (M.Φ B t z) m k) (frame_sum_single (fun i => M.tr g (e i)) j).symm hm)`.

Take `⟨s, hs⟩` from `GlobalTheory.T.prismaticFCrystal_frobenius_pullback_basis l K bk d M e a A hΦ B f t (fun i => ε i j) m k (Eq.subst (motive := fun z => IsFrac (t : B.A) (M.Φ B t z) m k) (htr j) hm)`. Establish `h1` using `frame_sum_mulVec B.D.φ (A.map (BK.hf g)) ε (fun i => M.tr g (e i)) c (fun x => (htr x).trans (Finset.sum_congr rfl fun i _ => congrArg (fun z => ε i x • z) (hc i).symm)) j`. Rewrite `hr` using `[h1]`. Simplify using `only [← hc] at hs`. Conclude with `frame_coord_cancel c ht hr hs i`.
-/
theorem frame_matrix_φ (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) (a : ℕ)
    (A : Matrix (Fin d) (Fin d) bk.S)
    (hΦ : ∀ j : Fin d, IsFrac (bk.toP bk.E)
      (M.Φ bk.prism ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩ (e j)) (∑ i, bk.toP (A i j) • e i) a)
    {B : Obj l ↥(OL K)} (f g : Hom bk.prism B) (c : Module.Basis (Fin d) B.A (M.M B))
    (hc : ∀ i, c i = M.tr f (e i)) (ε : Matrix (Fin d) (Fin d) B.A)
    (htr : ∀ j, M.tr g (e j) = ∑ i, ε i j • M.tr f (e i)) :
    BK.hf g bk.E ^ a • (A.map (BK.hf f) * ε.map B.D.φ) = BK.hf f bk.E ^ a • (ε * A.map (BK.hf g)) := by
  obtain ⟨hI, ht⟩ := GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk B f
  let t : ↥B.I := ⟨BK.hf f bk.E, hI.ge (Ideal.mem_span_singleton_self _)⟩
  ext i j
  obtain ⟨m, k, hm⟩ := exists_isFrac (t : B.A) (M.Φ B t (M.tr g (e j)))
  obtain ⟨r, hr⟩ := GlobalTheory.T.prismaticFCrystal_frobenius_pullback_basis l K bk d M e a A hΦ B g t (Pi.single j 1) m k
    (Eq.subst (motive := fun z => IsFrac (t : B.A) (M.Φ B t z) m k)
      (frame_sum_single (fun i => M.tr g (e i)) j).symm hm)
  obtain ⟨s, hs⟩ := GlobalTheory.T.prismaticFCrystal_frobenius_pullback_basis l K bk d M e a A hΦ B f t (fun i => ε i j) m k
    (Eq.subst (motive := fun z => IsFrac (t : B.A) (M.Φ B t z) m k) (htr j) hm)
  have h1 := frame_sum_mulVec B.D.φ (A.map (BK.hf g)) ε (fun i => M.tr g (e i)) c
    (fun x => (htr x).trans (Finset.sum_congr rfl fun i _ => congrArg (fun z => ε i x • z) (hc i).symm)) j
  rw [h1] at hr
  simp only [← hc] at hs
  exact frame_coord_cancel c ht hr hs i

/- English proof (translation)
Establish `hb : ∀ {B : Obj l ↥(OL K)} (f : Hom bk.prism B), ∃ c : Module.Basis (Fin d) B.A (M.M B), ∀ i, c i = M.tr f (e i)` using `fun f => GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ _ _ _ _ (M.tr_bc f) _ e`. Use `choose c hc using @hb`. Establish `htr : ∀ {B : Obj l ↥(OL K)} (f g : Hom bk.prism B) (j : Fin d), M.tr g (e j) = ∑ i, (c f).toMatrix (c g) i j • M.tr f (e i)` using `fun f g j => by`. Rewrite using `[← hc, ← (c f).sum_toMatrix_smul_self (c g) j]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [hc]`.

Establish `huniq : ∀ {B : Obj l ↥(OL K)} (f g : Hom bk.prism B) (j : Fin d) (v : Fin d → B.A), M.tr g (e j) = ∑ i, v i • M.tr f (e i) → ∀ i, (c f).toMatrix (c g) i j = v i` using `fun f g j v h i => by`. Express the relevant statement in the definitionally equal form `(c f).repr (c g j) i = v i`. Rewrite using `[hc, h]`. Simplify using `only [← hc]`. Rewrite using `[← (c f).equivFun_symm_apply, ← (c f).equivFun_apply, LinearEquiv.apply_symm_apply]`.

Use `⟨fun f g => (c f).toMatrix (c g), htr, fun f => (c f).toMatrix_self, fun f g h => (c f).toMatrix_mul_toMatrix (c g) (c h), fun k f g => ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Use `(huniq (k.comp f) (k.comp g) j (fun i => k.f ((c f).toMatrix (c g) i j)) ?_ i).symm` and prove the remaining obligations. Use `(M.tr_comp k g (e j)).trans ((congrArg (M.tr k) (htr f g j)).trans ?_)` and prove the remaining obligations. Use `(map_sum (M.tr k) _ _).trans (Finset.sum_congr rfl fun i _ => ?_)` and prove the remaining obligations.

Conclude with `((M.tr k).map_smulₛₗ _ _).trans (congrArg (fun z => k.f ((c f).toMatrix (c g) i j) • z) (M.tr_comp k f (e i)).symm)`.
-/
theorem exists_frame_matrices (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) :
    ∃ ε : ∀ {B : Obj l ↥(OL K)}, Hom bk.prism B → Hom bk.prism B → Matrix (Fin d) (Fin d) B.A,
      (∀ {B} (f g : Hom bk.prism B) (j : Fin d), M.tr g (e j) = ∑ i, ε f g i j • M.tr f (e i)) ∧
      (∀ {B} (f : Hom bk.prism B), ε f f = 1) ∧
      (∀ {B} (f g h : Hom bk.prism B), ε f g * ε g h = ε f h) ∧
      (∀ {B B'} (k : Hom B B') (f g : Hom bk.prism B), (ε f g).map k.f = ε (k.comp f) (k.comp g)) := by
  have hb : ∀ {B : Obj l ↥(OL K)} (f : Hom bk.prism B), ∃ c : Module.Basis (Fin d) B.A (M.M B),
      ∀ i, c i = M.tr f (e i) := fun f => GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ _ _ _ _ (M.tr_bc f) _ e
  choose c hc using @hb
  have htr : ∀ {B : Obj l ↥(OL K)} (f g : Hom bk.prism B) (j : Fin d),
      M.tr g (e j) = ∑ i, (c f).toMatrix (c g) i j • M.tr f (e i) := fun f g j => by
    rw [← hc, ← (c f).sum_toMatrix_smul_self (c g) j]
    exact Finset.sum_congr rfl fun i _ => by rw [hc]
  have huniq : ∀ {B : Obj l ↥(OL K)} (f g : Hom bk.prism B) (j : Fin d) (v : Fin d → B.A),
      M.tr g (e j) = ∑ i, v i • M.tr f (e i) → ∀ i, (c f).toMatrix (c g) i j = v i := fun f g j v h i => by
    change (c f).repr (c g j) i = v i
    rw [hc, h]
    simp only [← hc]
    rw [← (c f).equivFun_symm_apply, ← (c f).equivFun_apply, LinearEquiv.apply_symm_apply]
  refine ⟨fun f g => (c f).toMatrix (c g), htr, fun f => (c f).toMatrix_self,
    fun f g h => (c f).toMatrix_mul_toMatrix (c g) (c h), fun k f g => ?_⟩
  ext i j
  refine (huniq (k.comp f) (k.comp g) j (fun i => k.f ((c f).toMatrix (c g) i j)) ?_ i).symm
  refine (M.tr_comp k g (e j)).trans ((congrArg (M.tr k) (htr f g j)).trans ?_)
  refine (map_sum (M.tr k) _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
  exact ((M.tr k).map_smulₛₗ _ _).trans
    (congrArg (fun z => k.f ((c f).toMatrix (c g) i j) • z) (M.tr_comp k f (e i)).symm)

/- English proof (translation)
Establish `: IsLocalRing bk.prism.A` using `inferInstanceAs (IsLocalRing (Wq l bk.a)⟦X⟧)`. Use `M.fin bk.prism` as an intermediate fact. Use `M.proj bk.prism` as an intermediate fact. Establish `: Module.Free bk.prism.A (M.M bk.prism)` using `Module.free_of_flat_of_isLocalRing`. Take `⟨d, ⟨e⟩⟩ : ∃ d, Nonempty (Module.Basis (Fin d) bk.prism.A (M.M bk.prism))` from `⟨_, ⟨Module.finBasis bk.prism.A (M.M bk.prism)⟩⟩`.

Take `⟨a, b, A, A', hA, hΦ⟩` from `GlobalTheory.T.exists_frobenius_matrix_fCrystal_breuilKisin l K bk d M e`. Take `⟨ε, htr, h1, h2, h3⟩` from `exists_frame_matrices M e`. Use `⟨d, ⟨a, b, A, A', hA, ε, h1, h2, h3, fun f g => ?_⟩, e, htr, hΦ⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ _ _ _ _ (M.tr_bc f) _ e`. Conclude with `frame_matrix_φ M e a A hΦ f g c hc (ε f g) (htr f g)`.
-/
theorem exists_framed (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (M : FCrys l ↥(OL K)) :
    ∃ (d : ℕ) (S : Strat bk d) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e := by
  have : IsLocalRing bk.prism.A := inferInstanceAs (IsLocalRing (Wq l bk.a)⟦X⟧)
  have := M.fin bk.prism
  have := M.proj bk.prism
  have : Module.Free bk.prism.A (M.M bk.prism) := Module.free_of_flat_of_isLocalRing
  obtain ⟨d, ⟨e⟩⟩ : ∃ d, Nonempty (Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) :=
    ⟨_, ⟨Module.finBasis bk.prism.A (M.M bk.prism)⟩⟩
  obtain ⟨a, b, A, A', hA, hΦ⟩ := GlobalTheory.T.exists_frobenius_matrix_fCrystal_breuilKisin l K bk d M e
  obtain ⟨ε, htr, h1, h2, h3⟩ := exists_frame_matrices M e
  refine ⟨d, ⟨a, b, A, A', hA, ε, h1, h2, h3, fun f g => ?_⟩, e, htr, hΦ⟩
  obtain ⟨c, hc⟩ := GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ _ _ _ _ (M.tr_bc f) _ e
  exact frame_matrix_φ M e a A hΦ f g c hc (ε f g) (htr f g)

end GlobalTheory.BSP
