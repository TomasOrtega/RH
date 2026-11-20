import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeIffIsBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrismCoverReceivingBreuilKisinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveAndRangeOfPrismCoverStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStratifiedPhiModuleValueStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStratifiedValueTransitionBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalizedFractionSemilinearTransitionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeLocalizedOfTorsionBoundedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinHomEisensteinSpanAndNonZeroDivisorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusOnStratifiedValueStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedValueFrobeniusCommTransitionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearizedFrobeniusInvertibleUpToPowStatement

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.StratCrys

/- English proof (translation)
Use `letI := f.toAlgebra`. Set `u : M →ₛₗ[algebraMap A B] (B ⊗[A] M)` to `{ toFun := fun x => 1 ⊗ₜ x map_add' := fun x y => TensorProduct.tmul_add _ _ _ map_smul' := fun a x => by rw [algebraMap_smul, TensorProduct.tmul_smul] }`. Conclude with `⟨B ⊗[A] M, inferInstance, inferInstance, u, (GlobalTheory.T.isSemilinearBaseChange_iff_isBaseChange A B M (B ⊗[A] M) u (TensorProduct.mk A B M 1) fun _ => rfl).2 (TensorProduct.isBaseChange A M B)⟩`.
-/
theorem exists_semiBC {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (M : Type) [AddCommGroup M]
    [Module A M] : ∃ (P : Type) (_ : AddCommGroup P) (_ : Module B P) (u : M →ₛₗ[f] P), SemiBC u := by
  letI := f.toAlgebra
  let u : M →ₛₗ[algebraMap A B] (B ⊗[A] M) :=
    { toFun := fun x => 1 ⊗ₜ x
      map_add' := fun x y => TensorProduct.tmul_add _ _ _
      map_smul' := fun a x => by rw [algebraMap_smul, TensorProduct.tmul_smul] }
  exact ⟨B ⊗[A] M, inferInstance, inferInstance, u,
    (GlobalTheory.T.isSemilinearBaseChange_iff_isBaseChange A B M (B ⊗[A] M) u (TensorProduct.mk A B M 1) fun _ => rfl).2
      (TensorProduct.isBaseChange A M B)⟩

/- English proof (translation)
Take `⟨w, hw, -⟩` from `h M LinearMap.id`. Establish `h2 : u.comp w = LinearMap.id` using `h.hom_ext fun x => congrArg u (hw x)`. Conclude with `⟨Function.LeftInverse.injective (g := w) hw, fun y => ⟨w y, LinearMap.congr_fun h2 y⟩⟩`.
-/
theorem bijective_of_semiBC {A M N : Type} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (u : M →ₗ[A] N) (h : SemiBC u) : Function.Bijective u := by
  obtain ⟨w, hw, -⟩ := h M LinearMap.id
  have h2 : u.comp w = LinearMap.id := h.hom_ext fun x => congrArg u (hw x)
  exact ⟨Function.LeftInverse.injective (g := w) hw, fun y => ⟨w y, LinearMap.congr_fun h2 y⟩⟩

def fracMap {A N : Type} [CommRing A] [AddCommGroup N] [Module A N] {φ : A →+* A} (t : A) (a : ℕ)
    (Ψ : N →ₛₗ[φ] N) :
    N →ₛₗ[(algebraMap A (Localization.Away t)).comp φ] LocalizedModule (Submonoid.powers t) N where
  toFun x := LocalizedModule.mk (Ψ x) ⟨t ^ a, (Submonoid.mem_powers_iff _ _).2 ⟨a, rfl⟩⟩
  map_add' x y := by
    rw [map_add, LocalizedModule.mk_add_mk, ← smul_add, LocalizedModule.mk_cancel_common_left]
  map_smul' c x := by
    rw [Ψ.map_smulₛₗ, RingHom.comp_apply, algebraMap_smul, LocalizedModule.smul'_mk]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem isFrac_fracMap {A N : Type} [CommRing A] [AddCommGroup N] [Module A N] {φ : A →+* A} (t : A) (a : ℕ)
    (Ψ : N →ₛₗ[φ] N) (x : N) : IsFrac t (fracMap t a Ψ x) (Ψ x) a := rfl

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ} {S : Strat bk d}

/- English proof (translation)
Take `⟨C, c, ⟨f⟩, hc⟩` from `GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B`. Conclude with `(GlobalTheory.T.injective_and_range_of_prism_cover l K bk d S B C N V c f hc).1 (h C c f)`.
-/
theorem eval_ext {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N] (V : Eval S B N) {x y : N}
    (h : ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q), V.v a g x = V.v a g y) : x = y := by
  obtain ⟨C, c, ⟨f⟩, hc⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B
  exact (GlobalTheory.T.injective_and_range_of_prism_cover l K bk d S B C N V c f hc).1 (h C c f)

/- English proof (translation)
The claim follows from `bijective_of_semiBC (A := B.A) (V.v (Hom.id B) f) (V.bc (Hom.id B) f)`.
-/
theorem v_id_bijective {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N] (V : Eval S B N)
    (f : Hom bk.prism B) : Function.Bijective (V.v (Hom.id B) f) :=
  bijective_of_semiBC (A := B.A) (V.v (Hom.id B) f) (V.bc (Hom.id B) f)

/- English proof (translation)
Take `⟨P, _, _, u, hu⟩` from `exists_semiBC B.D.φ N`. Take `⟨L, hL, -⟩` from `hu N Ψ`. Take `⟨n, h1, h2⟩` from `GlobalTheory.T.linearizedFrobenius_invertible_up_to_pow l K bk d S B N V t ht Ψ hΨ P u hu L hL`. Conclude with `GlobalTheory.T.isSemilinearBaseChange_localized_of_torsion_bounded B.A B.D.φ t N P u hu L n S.a h1 h2 _ fun x => by`. Rewrite using `[hL]`.

Conclude with `isFrac_fracMap _ _ _ _`.
-/
theorem semiBC_fracMap {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N] (V : Eval S B N)
    (t : B.A) (ht : t ∈ B.I) (Ψ : N →ₛₗ[B.D.φ] N) (hΨ : IsPsi V t Ψ) : SemiBC (fracMap t S.a Ψ) := by
  obtain ⟨P, _, _, u, hu⟩ := exists_semiBC B.D.φ N
  obtain ⟨L, hL, -⟩ := hu N Ψ
  obtain ⟨n, h1, h2⟩ := GlobalTheory.T.linearizedFrobenius_invertible_up_to_pow l K bk d S B N V t ht Ψ hΨ P u hu L hL
  exact GlobalTheory.T.isSemilinearBaseChange_localized_of_torsion_bounded B.A B.D.φ t N P u hu L n S.a h1 h2 _ fun x => by
    rw [hL]; exact isFrac_fracMap _ _ _ _

variable (S) in

/- English proof (translation)
Use `choose N acg mod hV using GlobalTheory.T.exists_stratifiedPhiModuleValue l K bk d S`. Establish `V : ∀ B, Eval S B (N B)` using `fun B => (hV B).some`. Use `choose tr trbc htr using fun (B B' : Obj l ↥(OL K)) (k : Hom B B') => GlobalTheory.T.exists_stratifiedValue_transition_baseChange l K bk d S B B' (N B) (N B') (V B) (V B') k`. Use `choose Ψ hΨ using fun (B : Obj l ↥(OL K)) (t : ↥B.I) => GlobalTheory.T.exists_frobenius_on_stratifiedValue l K bk d S B (N B) (V B) t t.2`. Set `M : FCrys l ↥(OL K)` to `{ M := N acg := acg mod := mod fin := fun B => (V B).fin proj := fun B => (V B).proj tr := fun k => tr _ _ k tr_bc := fun k => trbc _ _ k tr_id := fun B x => eval_ext (V B) fun Q a g => htr _ _ _ Q a g x tr_comp := fun {B B' B''} k' k x => eval_ext (V B'') fun Q a g => (htr _ _ ( …`.

Conclude with `⟨M, V, fun B B' Q k a g x => htr _ _ k Q a g x, fun B t => ⟨Ψ B t, hΨ B t, fun _ => rfl⟩⟩`.
-/
theorem exists_crys : ∃ (M : FCrys l ↥(OL K)) (V : ∀ B, Eval S B (M.M B)),
    (∀ (B B' Q : Obj l ↥(OL K)) (k : Hom B B') (a : Hom B' Q) (g : Hom bk.prism Q) (x : M.M B),
      (V B').v a g (M.tr k x) = (V B).v (a.comp k) g x) ∧
    ∀ (B : Obj l ↥(OL K)) (t : ↥B.I), ∃ Ψ : M.M B →ₛₗ[B.D.φ] M.M B, IsPsi (V B) t Ψ ∧
      ∀ x, IsFrac (t : B.A) (M.Φ B t x) (Ψ x) S.a := by
  choose N acg mod hV using GlobalTheory.T.exists_stratifiedPhiModuleValue l K bk d S
  have V : ∀ B, Eval S B (N B) := fun B => (hV B).some
  choose tr trbc htr using fun (B B' : Obj l ↥(OL K)) (k : Hom B B') =>
    GlobalTheory.T.exists_stratifiedValue_transition_baseChange l K bk d S B B' (N B) (N B') (V B) (V B') k
  choose Ψ hΨ using fun (B : Obj l ↥(OL K)) (t : ↥B.I) =>
    GlobalTheory.T.exists_frobenius_on_stratifiedValue l K bk d S B (N B) (V B) t t.2
  let M : FCrys l ↥(OL K) :=
    { M := N
      acg := acg
      mod := mod
      fin := fun B => (V B).fin
      proj := fun B => (V B).proj
      tr := fun k => tr _ _ k
      tr_bc := fun k => trbc _ _ k
      tr_id := fun B x => eval_ext (V B) fun Q a g => htr _ _ _ Q a g x
      tr_comp := fun {B B' B''} k' k x => eval_ext (V B'') fun Q a g =>
        (htr _ _ (k'.comp k) Q a g x).trans
          ((htr _ _ k' Q a g _).trans (htr _ _ k Q (a.comp k') g x)).symm
      Φ := fun B t => fracMap (t : B.A) S.a (Ψ B t)
      Φ_bc := fun B t => semiBC_fracMap (V B) t t.2 _ (hΨ B t)
      Φ_nat := fun {B B'} k t t' x m i n j h1 h2 =>
        GlobalTheory.T.isLocalizedFraction_semilinear_transition B.A B'.A k.f (N B) (N B') (tr _ _ k) t t' S.a _ _ _ m _ n i j
          (isFrac_fracMap _ _ _ _) h1 (isFrac_fracMap _ _ _ _) h2
          (GlobalTheory.T.stratifiedValue_frobenius_comm_transition l K bk d S B B' (N B) (N B') (V B) (V B') k (tr _ _ k) (htr _ _ k) t t' _ _
            (hΨ B t) (hΨ B' t') x) }
  exact ⟨M, V, fun B B' Q k a g x => htr _ _ k Q a g x, fun B t => ⟨Ψ B t, hΨ B t, fun _ => rfl⟩⟩

/- English proof (translation)
Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`.
-/
theorem map_single {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (j i : Fin d) :
    f ((Pi.single j 1 : Fin d → A) i) = (Pi.single j 1 : Fin d → B) i := by
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/- English proof (translation)
Use extensionality with `i`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.
-/
theorem sum_single {A : Type} [CommRing A] (c : Fin d → A) :
    ∑ i, c i • (Pi.single i 1 : Fin d → A) = c := by
  ext i
  simp [Finset.sum_apply, Pi.single_apply]

/- English proof (translation)
Set `w : N →ₗ[B.A] (Fin d → B.A)` to `V.v (Hom.id B) f`. Set `q : N ≃ₗ[B.A] (Fin d → B.A)` to `LinearEquiv.ofBijective w (v_id_bijective V f)`. Use `⟨(Pi.basisFun _ _).map q.symm, fun j => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `q _ = _`. Simplify using the standard rewrite rules.
-/
theorem exists_basis {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N] (V : Eval S B N)
    (f : Hom bk.prism B) : ∃ e : Module.Basis (Fin d) B.A N, ∀ j, V.v (Hom.id B) f (e j) = Pi.single j 1 := by
  let w : N →ₗ[B.A] (Fin d → B.A) := V.v (Hom.id B) f
  let q : N ≃ₗ[B.A] (Fin d → B.A) := LinearEquiv.ofBijective w (v_id_bijective V f)
  refine ⟨(Pi.basisFun _ _).map q.symm, fun j => ?_⟩
  change q _ = _
  simp

/- English proof (translation)
Apply `(v_id_bijective V f).1` to reduce the goal to its premises. Set `w : N →ₗ[B.A] (Fin d → B.A)` to `V.v (Hom.id B) f`. Establish `he' : ∀ j, w (e j) = Pi.single j 1` using `he`. Express the relevant statement in the definitionally equal form `_ = w _`. Rewrite using `[h, map_sum]`.

Simplify using `only [map_smul, he']`. Conclude with `(sum_single c).symm`.
-/
theorem eq_sum_of_coord {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N] (V : Eval S B N)
    (f : Hom bk.prism B) (e : Fin d → N) (he : ∀ j, V.v (Hom.id B) f (e j) = Pi.single j 1) (x : N)
    (c : Fin d → B.A) (h : V.v (Hom.id B) f x = c) : x = ∑ i, c i • e i := by
  apply (v_id_bijective V f).1
  let w : N →ₗ[B.A] (Fin d → B.A) := V.v (Hom.id B) f
  have he' : ∀ j, w (e j) = Pi.single j 1 := he
  change _ = w _
  rw [h, map_sum]
  simp only [map_smul, he']
  exact (sum_single c).symm

/- English proof (translation)
Establish `h1` using `hΨ (Hom.id B) f x`. Rewrite `h1` using `[hx, funext (map_single B.D.φ j), Matrix.mulVec_single_one]`. Substitute `ht` using the available equality. Use extensionality with `i`. Conclude with `(mul_cancel_left_mem_nonZeroDivisors (pow_mem (GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk B f).2 S.a)).1 (congrFun h1 i)`.
-/
theorem coord_psi {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N] (V : Eval S B N)
    (f : Hom bk.prism B) (t : B.A) (ht : t = BK.hf f bk.E) (Ψ : N →ₛₗ[B.D.φ] N) (hΨ : IsPsi V t Ψ) (x : N)
    (j : Fin d) (hx : V.v (Hom.id B) f x = Pi.single j 1) :
    V.v (Hom.id B) f (Ψ x) = fun i => BK.hf f (S.A i j) := by
  have h1 := hΨ (Hom.id B) f x
  rw [hx, funext (map_single B.D.φ j), Matrix.mulVec_single_one] at h1
  subst ht
  ext i
  exact (mul_cancel_left_mem_nonZeroDivisors (pow_mem (GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk B f).2 S.a)).1 (congrFun h1 i)

/- English proof (translation)
Take `⟨M, V, htr, hΦ⟩` from `exists_crys S`. Take `⟨e, he⟩` from `exists_basis (V bk.prism) (Hom.id _)`. Establish `he' : ∀ {B : Obj l ↥(OL K)} (g : Hom bk.prism B) j, (V bk.prism).v g g (e j) = Pi.single j 1` using `fun g j => by`. Use extensionality with `i`. Use `(V bk.prism).v_nat g (Hom.id _) (Hom.id _) (e j) i` as an intermediate fact.

Rewrite `this` using `[he, map_single]`. Conclude with `this`. Use `⟨M, e, ⟨fun {B} f g j => ?_, fun j => ?_⟩⟩` and prove the remaining obligations. Establish `h1 : ∀ (g : Hom bk.prism B) x, (V B).v (Hom.id B) f (M.tr g x) = (V bk.prism).v g f x` using `fun g x => htr _ _ B g (Hom.id B) f x`. Use `eq_sum_of_coord (V B) f (fun i => M.tr f (e i)) (fun i => (h1 f _).trans (he' f i)) _ (fun i => S.ε f g i j) ?_` and prove the remaining obligations.

Rewrite using `[h1, (V _).v_ε g f g, he', Matrix.mulVec_single_one]`. Both sides reduce to the same expression. Establish `h0 : ∀ x, BK.hf (Hom.id bk.prism) x = bk.toP x` using `fun _ => rfl`. Establish `ht : bk.toP bk.E ∈ bk.prism.I`. Rewrite using `[(GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk bk.prism (Hom.id _)).1, h0]`.

Conclude with `Ideal.mem_span_singleton_self _`. Establish `hh` using `hΦ bk.prism ⟨bk.toP bk.E, ht⟩`. Take `⟨Ψ, hΨ, h⟩` from `hh`. Establish `h1` using `coord_psi (V _) (Hom.id _) _ (h0 _).symm Ψ hΨ _ j (he j)`. Establish `h2` using `eq_sum_of_coord (V _) (Hom.id _) e he _ _ h1`.

Simplify using `only [h0] at h2`. Conclude with `Eq.mp (congrArg (fun m => IsFrac (bk.toP bk.E) (M.Φ bk.prism ⟨bk.toP bk.E, ht⟩ (e j)) m S.a) h2) (h (e j))`.
-/
theorem exists_framed (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) :
    ∃ (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e := by
  obtain ⟨M, V, htr, hΦ⟩ := exists_crys S
  obtain ⟨e, he⟩ := exists_basis (V bk.prism) (Hom.id _)
  have he' : ∀ {B : Obj l ↥(OL K)} (g : Hom bk.prism B) j, (V bk.prism).v g g (e j) = Pi.single j 1 :=
    fun g j => by
      ext i
      have := (V bk.prism).v_nat g (Hom.id _) (Hom.id _) (e j) i
      rw [he, map_single] at this
      exact this
  refine ⟨M, e, ⟨fun {B} f g j => ?_, fun j => ?_⟩⟩
  · have h1 : ∀ (g : Hom bk.prism B) x, (V B).v (Hom.id B) f (M.tr g x) = (V bk.prism).v g f x :=
      fun g x => htr _ _ B g (Hom.id B) f x
    refine eq_sum_of_coord (V B) f (fun i => M.tr f (e i)) (fun i => (h1 f _).trans (he' f i)) _
      (fun i => S.ε f g i j) ?_
    rw [h1, (V _).v_ε g f g, he', Matrix.mulVec_single_one]
    rfl
  · have h0 : ∀ x, BK.hf (Hom.id bk.prism) x = bk.toP x := fun _ => rfl
    have ht : bk.toP bk.E ∈ bk.prism.I := by
      rw [(GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk bk.prism (Hom.id _)).1, h0]
      exact Ideal.mem_span_singleton_self _
    have hh := hΦ bk.prism ⟨bk.toP bk.E, ht⟩
    obtain ⟨Ψ, hΨ, h⟩ := hh
    have h1 := coord_psi (V _) (Hom.id _) _ (h0 _).symm Ψ hΨ _ j (he j)
    have h2 := eq_sum_of_coord (V _) (Hom.id _) e he _ _ h1
    simp only [h0] at h2
    exact Eq.mp (congrArg (fun m => IsFrac (bk.toP bk.E) (M.Φ bk.prism ⟨bk.toP bk.E, ht⟩ (e j)) m S.a) h2)
      (h (e j))

end GlobalTheory.BSP.StratCrys
