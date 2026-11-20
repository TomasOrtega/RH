import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSeriesOfExact
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelPushOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelPreimageOfInjectiveFinDimRepModelHomStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelObjAndAbcStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicityAdditiveExactSequenceStatement

noncomputable section
namespace GlobalTheory.Models
open GlobalTheory.PhiGam GlobalTheory.AdmLoc
open scoped LaurentSeries PowerSeries

/- English proof (translation)
Use `haveI : Nonempty (Fin B.m) := ⟨⟨0, Nat.pos_of_ne_zero hB⟩⟩`. Use `haveI : Nontrivial B.ρ.asModule := B.ρ.asModuleEquiv.toEquiv.nontrivial`. Establish `hfl` using `finiteLength_asModule B.ρ (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)`. Use `haveI := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).1`. Take `⟨S, hS, -⟩` from `(eq_top_or_exists_le_coatom (⊥ : Submodule (MonoidAlgebra k G) B.ρ.asModule)).resolve_left bot_ne_top`.

Set `S' : Submodule k (Fin B.m → k)` to `(S.restrictScalars k).comap B.ρ.asModuleEquiv.symm.toLinearMap`. Establish `hinv : ∀ g, S' ≤ S'.comap (B.ρ g)`. Introduce `g x hx`. Establish `hx' : B.ρ.asModuleEquiv.symm x ∈ S` using `hx`. Express the relevant statement in the definitionally equal form `B.ρ.asModuleEquiv.symm (B.ρ g x) ∈ S`.

Rewrite using `[Representation.asModuleEquiv_symm_map_rho]`. Conclude with `S.smul_mem _ hx'`. Take `⟨A, eA, hA⟩` from `exists_ob (B.ρ.subrepresentation S' hinv)`. Take `⟨C, eC, hC⟩` from `exists_ob (B.ρ.quotient S' hinv)`. Establish `hp : IsHom B C (eC.toLinearMap ∘ₗ S'.mkQ)` using `fun g x => hC g (S'.mkQ x)`.

Establish `hps : Function.Surjective (eC.toLinearMap ∘ₗ S'.mkQ)` using `eC.surjective.comp S'.mkQ_surjective`. Use `⟨A, C, S'.subtype ∘ₗ eA.symm.toLinearMap, eC.toLinearMap ∘ₗ S'.mkQ, ?_, hp, S'.subtype_injective.comp eA.symm.injective, hps, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g x`. Take `⟨y, rfl⟩` from `eA.surjective x`. Rewrite using `[← hA]`.

Simplify using the standard rewrite rules. Introduce `x`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Set.mem_range, Submodule.subtype_apply]`. Conclude with `⟨fun h => ⟨eA ⟨x, h⟩, by simp⟩, fun ⟨y, hy⟩ => hy ▸ (eA.symm y).2⟩`. Set `q` to `asModuleMap (π := B.ρ) (π' := C.ρ) _ hp`.

Establish `hq : Function.Surjective q` using `hps`. Establish `hk : S = LinearMap.ker q`. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `_ ↔ eC (S'.mkQ (B.ρ.asModuleEquiv x)) = 0`. Rewrite using `[LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`.

Conclude with `Iff.rfl`. Use `haveI := isSimpleModule_iff_isCoatom.mpr hS`. Conclude with `IsSimpleModule.congr ((Submodule.quotEquivOfEq _ _ hk).trans (q.quotKerEquivOfSurjective hq)).symm`. Establish `h1 : S' ≠ ⊤`. Introduce `h`.

Use `hS.1 (eq_top_iff.mpr fun x _ => ?_)` and prove the remaining obligations. Establish `: B.ρ.asModuleEquiv x ∈ S'` using `h ▸ Submodule.mem_top`. Conclude with `this`. Establish `h2` using `Submodule.finrank_lt h1`. Rewrite `h2` using `[eA.finrank_eq]`.

Simplify using `using h2`.
-/
theorem exists_simple_quotient {k G : Type} [Field k] [Group G] (B : Ob k G) (hB : B.m ≠ 0) :
    ∃ (A C : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin B.m → k) →ₗ[k] (Fin C.m → k)),
      IsHom A B f ∧ IsHom B C p ∧ Function.Injective f ∧ Function.Surjective p ∧ Function.Exact f p ∧
      IsSimpleModule (MonoidAlgebra k G) C.ρ.asModule ∧ A.m < B.m := by
  haveI : Nonempty (Fin B.m) := ⟨⟨0, Nat.pos_of_ne_zero hB⟩⟩
  haveI : Nontrivial B.ρ.asModule := B.ρ.asModuleEquiv.toEquiv.nontrivial
  have hfl := finiteLength_asModule B.ρ
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)
  haveI := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).1
  obtain ⟨S, hS, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule (MonoidAlgebra k G) B.ρ.asModule)).resolve_left
    bot_ne_top
  let S' : Submodule k (Fin B.m → k) := (S.restrictScalars k).comap B.ρ.asModuleEquiv.symm.toLinearMap
  have hinv : ∀ g, S' ≤ S'.comap (B.ρ g) := by
    intro g x hx
    have hx' : B.ρ.asModuleEquiv.symm x ∈ S := hx
    change B.ρ.asModuleEquiv.symm (B.ρ g x) ∈ S
    rw [Representation.asModuleEquiv_symm_map_rho]
    exact S.smul_mem _ hx'
  obtain ⟨A, eA, hA⟩ := exists_ob (B.ρ.subrepresentation S' hinv)
  obtain ⟨C, eC, hC⟩ := exists_ob (B.ρ.quotient S' hinv)
  have hp : IsHom B C (eC.toLinearMap ∘ₗ S'.mkQ) := fun g x => hC g (S'.mkQ x)
  have hps : Function.Surjective (eC.toLinearMap ∘ₗ S'.mkQ) := eC.surjective.comp S'.mkQ_surjective
  refine ⟨A, C, S'.subtype ∘ₗ eA.symm.toLinearMap, eC.toLinearMap ∘ₗ S'.mkQ, ?_, hp,
    S'.subtype_injective.comp eA.symm.injective, hps, ?_, ?_, ?_⟩
  · intro g x
    obtain ⟨y, rfl⟩ := eA.surjective x
    rw [← hA]
    simp
  · intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Set.mem_range, Submodule.subtype_apply]
    exact ⟨fun h => ⟨eA ⟨x, h⟩, by simp⟩, fun ⟨y, hy⟩ => hy ▸ (eA.symm y).2⟩
  · let q := asModuleMap (π := B.ρ) (π' := C.ρ) _ hp
    have hq : Function.Surjective q := hps
    have hk : S = LinearMap.ker q := by
      ext x
      change _ ↔ eC (S'.mkQ (B.ρ.asModuleEquiv x)) = 0
      rw [LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Iff.rfl
    haveI := isSimpleModule_iff_isCoatom.mpr hS
    exact IsSimpleModule.congr ((Submodule.quotEquivOfEq _ _ hk).trans (q.quotKerEquivOfSurjective hq)).symm
  · have h1 : S' ≠ ⊤ := by
      intro h
      refine hS.1 (eq_top_iff.mpr fun x _ => ?_)
      have : B.ρ.asModuleEquiv x ∈ S' := h ▸ Submodule.mem_top
      exact this
    have h2 := Submodule.finrank_lt h1
    rw [eA.finrank_eq] at h2
    simpa using h2

/- English proof (translation)
Establish `h1 : SameSS B.ρ ((C 0).ρ.prod (piRep fun a : Fin s => (C a.succ).ρ))` using `SameSS.of_exact_of_exact ef ep hf hp H (f' := LinearMap.inr k _ _) (p' := LinearMap.fst k _ _) (fun g x => by simp) (fun g x => by simp) LinearMap.inr_injective LinearMap.fst_surjective .inr_fst h (SameSS.refl _ (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, infe …`. Use `h1.congr_right (Fin.consLinearEquiv k fun a => Fin (C a).m → k) fun g x => ?_` and prove the remaining obligations. Use function extensionality and compare the values at `a`. Apply the tactic sequence `refine Fin.cases ?_ (fun j => ?_) a <;> rfl`.
-/
theorem sameSS_piRep_succ {k G : Type} [Field k] [Group G] {s : ℕ} (C : Fin (s + 1) → Ob k G) (A B : Ob k G)
    (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin B.m → k) →ₗ[k] (Fin (C 0).m → k))
    (ef : IsHom A B f) (ep : IsHom B (C 0) p) (hf : Function.Injective f) (hp : Function.Surjective p)
    (H : Function.Exact f p) (h : SameSS A.ρ (piRep fun a : Fin s => (C a.succ).ρ)) :
    SameSS B.ρ (piRep fun a => (C a).ρ) := by
  have h1 : SameSS B.ρ ((C 0).ρ.prod (piRep fun a : Fin s => (C a.succ).ρ)) :=
    SameSS.of_exact_of_exact ef ep hf hp H (f' := LinearMap.inr k _ _) (p' := LinearMap.fst k _ _)
      (fun g x => by simp) (fun g x => by simp) LinearMap.inr_injective LinearMap.fst_surjective .inr_fst h
      (SameSS.refl _ (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩))
  refine h1.congr_right (Fin.consLinearEquiv k fun a => Fin (C a).m → k) fun g x => ?_
  funext a
  refine Fin.cases ?_ (fun j => ?_) a <;> rfl

/- English proof (translation)
Introduce `k G _ _ l n _ _ _ R F r Dt M B`. Proceed by induction on `B using (measure fun A : Ob k G => A.m).wf.induction with`. Consider the case `_ B ih`. Introduce `N hN`. Distinguish the cases in `hB : B.m = 0`.

Use `haveI : IsEmpty (Fin B.m) := ⟨fun a => by have := a.2; omega⟩`. Use `⟨0, Fin.elim0, fun a => a.elim0, fun a => a.elim0, fun a => a.elim0, ?_, fun i x => ?_⟩` and prove the remaining obligations. Conclude with `SameSS.of_equiv (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩) (LinearEquiv.ofSubsingleton _ _) fun _ _ => Subsingleton.elim _ _`. Rewrite using `[Finset.univ_eq_empty, Finset.sum_empty]`. Unfold `sen qmult gmult`.

Conclude with `Module.finrank_zero_of_subsingleton`. Take `⟨A, C₀, f, p, ef, ep, hf, hp, H, hs, hlt⟩` from `exists_simple_quotient B hB`. Take `⟨s, C, L, hL, hC, hss, hsen⟩` from `ih A hlt _ (GlobalTheory.T.model_preimage_of_injective_finDimRepModelHom F M A B f N ef hf hN)`. Take `⟨hobj, hlat, -, hc⟩` from `GlobalTheory.T.obj_and_abc_of_model F M B N hN`. Set `C' : Fin (s + 1) → Ob k G` to `Fin.cons C₀ C`.

Use `⟨s + 1, C', Fin.cons (α := fun a => Lats k n (C' a).m) (F.push B C₀ p N) L, fun a => ?_, fun a => ?_, sameSS_piRep_succ C' A B f p ef ep hf hp H hss, fun i x => ?_⟩` and prove the remaining obligations. Use `Fin.cases ?_ (fun j => ?_) a` and prove the remaining obligations. Conclude with `ModTh.model_push_of_surjective F M B C₀ p N ep hp hN`. Conclude with `hL j`. Use `Fin.cases ?_ (fun j => ?_) a` and prove the remaining obligations.

Conclude with `hs`. Conclude with `hC j`. Rewrite using `[Fin.sum_univ_succ, GlobalTheory.T.senMultiplicity_additive_exact_sequence F A B C₀ f p N hobj ef ep hf hp H i (hlat i) (hc i) x, hsen, add_comm]`. Both sides reduce to the same expression.
-/
theorem ModTh.exists_simple_pieces : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (B : Ob k G) (N : Lats k n B.m), M.Model B N → ∃ (s : ℕ) (C : Fin s → Ob k G) (L : ∀ a, Lats k n (C a).m), (∀ a, M.Model (C a) (L a)) ∧ (∀ a, IsSimpleModule (MonoidAlgebra k G) (C a).ρ.asModule) ∧ SameSS B.ρ (piRep fun a => (C a).ρ) ∧ ∀ i x, sen ((F.D B).γ i) (N i) x = ∑ a, sen ((F.D (C a)).γ i) (L a i) x := by
  intro k G _ _ l n _ _ _ R F r Dt M B
  induction B using (measure fun A : Ob k G => A.m).wf.induction with
  | _ B ih =>
  intro N hN
  by_cases hB : B.m = 0
  · haveI : IsEmpty (Fin B.m) := ⟨fun a => by have := a.2; omega⟩
    refine ⟨0, Fin.elim0, fun a => a.elim0, fun a => a.elim0, fun a => a.elim0, ?_, fun i x => ?_⟩
    · exact SameSS.of_equiv (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)
        (LinearEquiv.ofSubsingleton _ _) fun _ _ => Subsingleton.elim _ _
    · rw [Finset.univ_eq_empty, Finset.sum_empty]
      unfold sen qmult gmult
      exact Module.finrank_zero_of_subsingleton
  · obtain ⟨A, C₀, f, p, ef, ep, hf, hp, H, hs, hlt⟩ := exists_simple_quotient B hB
    obtain ⟨s, C, L, hL, hC, hss, hsen⟩ := ih A hlt _ (GlobalTheory.T.model_preimage_of_injective_finDimRepModelHom F M A B f N ef hf hN)
    obtain ⟨hobj, hlat, -, hc⟩ := GlobalTheory.T.obj_and_abc_of_model F M B N hN
    let C' : Fin (s + 1) → Ob k G := Fin.cons C₀ C
    refine ⟨s + 1, C', Fin.cons (α := fun a => Lats k n (C' a).m) (F.push B C₀ p N) L, fun a => ?_, fun a => ?_,
      sameSS_piRep_succ C' A B f p ef ep hf hp H hss, fun i x => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) a
      · exact ModTh.model_push_of_surjective F M B C₀ p N ep hp hN
      · exact hL j
    · refine Fin.cases ?_ (fun j => ?_) a
      · exact hs
      · exact hC j
    · rw [Fin.sum_univ_succ, GlobalTheory.T.senMultiplicity_additive_exact_sequence F A B C₀ f p N hobj ef ep hf hp H i (hlat i) (hc i) x, hsen, add_comm]
      rfl

end GlobalTheory.Models
