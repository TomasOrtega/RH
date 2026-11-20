import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentVarUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyLaurentAbsIntClosedLocalDomaiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyProdRingProjectionsBijectiveStatement
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsLocalRingIntegralClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicPolynomialsHaveRootsIntegralClosureAlgClosu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralStrictHenselianAcyclicFinitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentPiBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentClassVanishesFinitelyGeneratedSubalgebraStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralPi
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

noncomputable section
namespace GlobalTheory.EtC.GmKill

/- English proof (translation)
Rewrite using `[← Functor.map_comp, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Functor.map_comp, ← Spec.map_comp]; rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `sch.map (Spec.map (𝟙 _)) = _`. Rewrite using `[Spec.map_id, CategoryTheory.Functor.map_id]`.
-/
theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (sp A) := by
  change sch.map (Spec.map (𝟙 _)) = _
  rw [Spec.map_id, CategoryTheory.Functor.map_id]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `x y`. Establish `h : ∀ z : Ht q (sp B) d i, pull _ (spMap (e : A →+* B)) _ _ (pull _ (spMap (e.symm : B →+* A)) _ _ z) = z`. Introduce `z`. Rewrite using `[← pull_comp, spMap_comp]`.

Establish `: (e : A →+* B).comp (e.symm : B →+* A) = RingHom.id B` using `by ext; simp`. Rewrite using `[this, spMap_id, pull_id]`. Rewrite using `[← h x, ← h y, Subsingleton.elim (pull _ (spMap (e.symm : B →+* A)) _ _ x) (pull _ _ _ _ y)]`.
-/
theorem subsingleton_of_ringEquiv (q : ℕ) (d i : ℤ) {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B)
    [Subsingleton (Ht q (sp A) d i)] : Subsingleton (Ht q (sp B) d i) := by
  constructor
  intro x y
  have h : ∀ z : Ht q (sp B) d i,
      pull _ (spMap (e : A →+* B)) _ _ (pull _ (spMap (e.symm : B →+* A)) _ _ z) = z := by
    intro z
    rw [← pull_comp, spMap_comp]
    have : (e : A →+* B).comp (e.symm : B →+* A) = RingHom.id B := by ext; simp
    rw [this, spMap_id, pull_id]
  rw [← h x, ← h y, Subsingleton.elim (pull _ (spMap (e.symm : B →+* A)) _ _ x) (pull _ _ _ _ y)]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `x y`. Conclude with `(GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q A B d i).1 (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))`.
-/
theorem subsingleton_prod (q : ℕ) (d i : ℤ) (A B : Type) [CommRing A] [CommRing B]
    [Subsingleton (Ht q (sp A) d i)] [Subsingleton (Ht q (sp B) d i)] :
    Subsingleton (Ht q (sp (A × B)) d i) := by
  constructor
  intro x y
  exact (GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q A B d i).1 (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `a b`. Take `⟨x, hx⟩` from `(GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q A A d i).2 (a, b)`. Establish `hfs : RingHom.fst A A = RingHom.snd A A` using `RingHom.ext fun _ => Subsingleton.elim _ _`. Establish `h1` using `congrArg Prod.fst hx`.

Establish `h2` using `congrArg Prod.snd hx`. Simplify using `only at h1 h2`. Rewrite using `[← h1, ← h2, hfs]`.
-/
theorem subsingleton_of_subsingleton_ring (q : ℕ) (d i : ℤ) (A : Type) [CommRing A] [Subsingleton A] :
    Subsingleton (Ht q (sp A) d i) := by
  constructor
  intro a b
  obtain ⟨x, hx⟩ := (GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q A A d i).2 (a, b)
  have hfs : RingHom.fst A A = RingHom.snd A A := RingHom.ext fun _ => Subsingleton.elim _ _
  have h1 := congrArg Prod.fst hx
  have h2 := congrArg Prod.snd hx
  simp only at h1 h2
  rw [← h1, ← h2, hfs]

def piFinSuccRingEquiv (n : ℕ) (B : Fin (n + 1) → Type) [∀ j, CommRing (B j)] :
    (∀ j, B j) ≃+* B 0 × ∀ j : Fin n, B j.succ where
  toFun f := (f 0, fun j => f j.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by simp
  map_mul' f g := rfl
  map_add' f g := rfl

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `B _ _`. Conclude with `subsingleton_of_subsingleton_ring q d i _`.

Consider the case `succ n ih`. Introduce `B _ hB`. Use `ih (fun j => B j.succ) (fun j => hB j.succ)` as an intermediate fact. Use `hB 0` as an intermediate fact. Use `subsingleton_prod q d i (B 0) (∀ j : Fin n, B j.succ)` as an intermediate fact.

Conclude with `subsingleton_of_ringEquiv q d i (piFinSuccRingEquiv n B).symm`.
-/
theorem subsingleton_pi (q : ℕ) (d i : ℤ) : ∀ (n : ℕ) (B : Fin n → Type) [∀ j, CommRing (B j)],
    (∀ j, Subsingleton (Ht q (sp (B j)) d i)) → Subsingleton (Ht q (sp (∀ j, B j)) d i) := by
  intro n
  induction n with
  | zero =>
    intro B _ _
    exact subsingleton_of_subsingleton_ring q d i _
  | succ n ih =>
    intro B _ hB
    have := ih (fun j => B j.succ) (fun j => hB j.succ)
    have := hB 0
    have := subsingleton_prod q d i (B 0) (∀ j : Fin n, B j.succ)
    exact subsingleton_of_ringEquiv q d i (piFinSuccRingEquiv n B).symm

/- English proof (translation)
The claim follows from `_root_.GlobalTheory.IntegralPi.main x hx`.
-/
theorem isIntegral_pi {O : Type} [CommRing O] {ι : Type} [Finite ι] {R : ι → Type}
    [∀ i, CommRing (R i)] [∀ i, Algebra O (R i)] (x : ∀ i, R i) (hx : ∀ i, IsIntegral O (x i)) :
    IsIntegral O x :=
  _root_.GlobalTheory.IntegralPi.main x hx

/- English proof (translation)
Use `haveI : IsLocalRing (A ⧸ P) := IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective`. Use `haveI : HenselianLocalRing (A ⧸ P) := GlobalTheory.henselianLocalRing_of_finite A (A ⧸ P)`. Conclude with `GlobalTheory.EtC.Psi.isLocalRing_integralClosure _ _`.
-/
theorem isLocalRing_closure (A : Type) [CommRing A] [HenselianLocalRing A] (P : Ideal A) [P.IsPrime] :
    IsLocalRing (integralClosure (A ⧸ P) (AlgebraicClosure (FractionRing (A ⧸ P)))) := by
  haveI : IsLocalRing (A ⧸ P) := IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  haveI : HenselianLocalRing (A ⧸ P) := GlobalTheory.henselianLocalRing_of_finite A (A ⧸ P)
  exact GlobalTheory.EtC.Psi.isLocalRing_integralClosure _ _

/- English proof (translation)
Introduce `q _ A _ _ hA hq n i hn x`. Take `⟨hHens, -⟩` from `hA`. Set `ι` to `{p : Ideal A // p ∈ minimalPrimes A}`. Use `haveI : Finite ι := (minimalPrimes.finite_of_isNoetherianRing A).to_subtype`. Use `letI : Fintype ι := Fintype.ofFinite ι`.

Set `σ : Fin (Fintype.card ι) ≃ ι` to `(Fintype.equivFin ι).symm`. Set `P : Fin (Fintype.card ι) → Ideal A` to `fun k => (σ k).1`. Use `haveI hP : ∀ k, (P k).IsPrime := fun k => (σ k).2.1.1`. Set `T : Fin (Fintype.card ι) → Type` to `fun k => integralClosure (A ⧸ P k) (AlgebraicClosure (FractionRing (A ⧸ P k)))`. Use `letI : ∀ k, Algebra A (T k) := fun k => ((algebraMap (A ⧸ P k) (T k)).comp (Ideal.Quotient.mk (P k))).toAlgebra`.

Establish `hint : ∀ k (s : T k), IsIntegral A s`. Introduce `k s`. Establish `h : ((algebraMap (A ⧸ P k) (T k)).comp (Ideal.Quotient.mk (P k))).IsIntegral` using `RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective) (fun s => Algebra.IsIntegral.isIntegral s)`. Conclude with `h s`. Use `haveI : Algebra.IsIntegral A (∀ k, T k) := ⟨fun s => isIntegral_pi s (fun k => hint k (s k))⟩`.

Establish `hS : Subsingleton (Ht q (sp (LaurentPolynomial (∀ k, T k))) n i)`. Establish `hT : ∀ k, Subsingleton (Ht q (sp (LaurentPolynomial (T k))) n i)`. Introduce `k`. Use `haveI := isLocalRing_closure A (P k)`. Establish `hqk : IsUnit (q : T k)` using `by simpa using hq.map (algebraMap A (T k))`.

Conclude with `(GlobalTheory.T.tateTwistCohomology_laurent_absIntClosedLocalDomain q (T k) (GlobalTheory.aic_integralClosure_algebraicClosure (A ⧸ P k)) hqk n i).1 hn`. Use `haveI := subsingleton_pi q n i _ (fun k => LaurentPolynomial (T k)) hT`. Conclude with `subsingleton_of_ringEquiv q n i (RingEquiv.ofBijective _ (GlobalTheory.T.laurent_pi_bijective _ T)).symm`. Establish `hx0 : pull _ (spMap (laurentMap (algebraMap A (∀ k, T k)))) _ _ x = 0` using `Subsingleton.elim _ _`. Take `⟨t, ht⟩` from `GlobalTheory.T.laurent_class_vanishes_finitely_generated_subalgebra q A (∀ k, T k) hq n i x hx0`.

Use `⟨Algebra.adjoin A (t : Set (∀ k, T k)), inferInstance, inferInstance, GlobalTheory.EtC.IntAcyc.finite_finDiag A (∀ k, T k) t, ?_, ht⟩` and prove the remaining obligations. Introduce `a ha`. Rewrite `ha` using `[RingHom.mem_ker]`. Establish `ha' : algebraMap A (∀ k, T k) a = 0`. Use `congrArg Subtype.val ha` as an intermediate fact.

Conclude with `this`. Establish `hmem : ∀ k, a ∈ P k`. Introduce `k`. Establish `h1 : algebraMap A (T k) a = 0` using `congrFun ha' k`. Establish `h2 : algebraMap (A ⧸ P k) (AlgebraicClosure (FractionRing (A ⧸ P k))) (Ideal.Quotient.mk (P k) a) = 0` using `congrArg Subtype.val h1`.

Rewrite `h2` using `[IsScalarTower.algebraMap_eq (A ⧸ P k) (FractionRing (A ⧸ P k)) (AlgebraicClosure (FractionRing (A ⧸ P k))), RingHom.comp_apply]`. Establish `h3` using `(IsFractionRing.injective (A ⧸ P k) (FractionRing (A ⧸ P k))) ((algebraMap (FractionRing (A ⧸ P k)) _).injective (h2.trans (map_zero _).symm) |>.trans (map_zero _).symm)`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 h3`. Express the relevant statement in the definitionally equal form `a ∈ (⊥ : Ideal A).radical`. Rewrite using `[← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]`.

Introduce `p hp`. Take `⟨k, hk⟩` from `σ.surjective ⟨p, hp⟩`. Use `hmem k` as an intermediate fact. Simplify using `only [P, hk] at this`. Conclude with `this`.
-/
theorem main : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
  ∀ (n i : ℤ), 2 ≤ n → ∀ x : Ht q (sp (LaurentPolynomial A)) n i,
  ∃ (A' : Type) (_ : CommRing A') (_ : Algebra A A'), Module.Finite A A' ∧ RingHom.ker (algebraMap A A') ≤ nilradical A ∧
    pull _ (spMap (laurentMap (algebraMap A A'))) _ _ x = 0 := by
  classical
  intro q _ A _ _ hA hq n i hn x
  obtain ⟨hHens, -⟩ := hA
  let ι := {p : Ideal A // p ∈ minimalPrimes A}
  haveI : Finite ι := (minimalPrimes.finite_of_isNoetherianRing A).to_subtype
  letI : Fintype ι := Fintype.ofFinite ι
  let σ : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let P : Fin (Fintype.card ι) → Ideal A := fun k => (σ k).1
  haveI hP : ∀ k, (P k).IsPrime := fun k => (σ k).2.1.1
  let T : Fin (Fintype.card ι) → Type := fun k =>
    integralClosure (A ⧸ P k) (AlgebraicClosure (FractionRing (A ⧸ P k)))
  letI : ∀ k, Algebra A (T k) := fun k => ((algebraMap (A ⧸ P k) (T k)).comp (Ideal.Quotient.mk (P k))).toAlgebra
  have hint : ∀ k (s : T k), IsIntegral A s := by
    intro k s
    have h : ((algebraMap (A ⧸ P k) (T k)).comp (Ideal.Quotient.mk (P k))).IsIntegral :=
      RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective)
        (fun s => Algebra.IsIntegral.isIntegral s)
    exact h s
  haveI : Algebra.IsIntegral A (∀ k, T k) := ⟨fun s => isIntegral_pi s (fun k => hint k (s k))⟩
  have hS : Subsingleton (Ht q (sp (LaurentPolynomial (∀ k, T k))) n i) := by
    have hT : ∀ k, Subsingleton (Ht q (sp (LaurentPolynomial (T k))) n i) := by
      intro k
      haveI := isLocalRing_closure A (P k)
      have hqk : IsUnit (q : T k) := by simpa using hq.map (algebraMap A (T k))
      exact (GlobalTheory.T.tateTwistCohomology_laurent_absIntClosedLocalDomain q (T k) (GlobalTheory.aic_integralClosure_algebraicClosure (A ⧸ P k)) hqk n i).1 hn
    haveI := subsingleton_pi q n i _ (fun k => LaurentPolynomial (T k)) hT
    exact subsingleton_of_ringEquiv q n i (RingEquiv.ofBijective _ (GlobalTheory.T.laurent_pi_bijective _ T)).symm
  have hx0 : pull _ (spMap (laurentMap (algebraMap A (∀ k, T k)))) _ _ x = 0 := Subsingleton.elim _ _
  obtain ⟨t, ht⟩ := GlobalTheory.T.laurent_class_vanishes_finitely_generated_subalgebra q A (∀ k, T k) hq n i x hx0
  refine ⟨Algebra.adjoin A (t : Set (∀ k, T k)), inferInstance, inferInstance,
    GlobalTheory.EtC.IntAcyc.finite_finDiag A (∀ k, T k) t, ?_, ht⟩
  intro a ha
  rw [RingHom.mem_ker] at ha
  have ha' : algebraMap A (∀ k, T k) a = 0 := by
    have := congrArg Subtype.val ha
    exact this
  have hmem : ∀ k, a ∈ P k := by
    intro k
    have h1 : algebraMap A (T k) a = 0 := congrFun ha' k
    have h2 : algebraMap (A ⧸ P k) (AlgebraicClosure (FractionRing (A ⧸ P k))) (Ideal.Quotient.mk (P k) a) = 0 :=
      congrArg Subtype.val h1
    rw [IsScalarTower.algebraMap_eq (A ⧸ P k) (FractionRing (A ⧸ P k)) (AlgebraicClosure (FractionRing (A ⧸ P k))),
      RingHom.comp_apply] at h2
    have h3 := (IsFractionRing.injective (A ⧸ P k) (FractionRing (A ⧸ P k)))
      ((algebraMap (FractionRing (A ⧸ P k)) _).injective (h2.trans (map_zero _).symm) |>.trans (map_zero _).symm)
    exact Ideal.Quotient.eq_zero_iff_mem.1 h3
  change a ∈ (⊥ : Ideal A).radical
  rw [← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
  intro p hp
  obtain ⟨k, hk⟩ := σ.surjective ⟨p, hp⟩
  have := hmem k
  simp only [P, hk] at this
  exact this

end GlobalTheory.EtC.GmKill

end
