import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CoreH
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.AuTeichEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.DenseU
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.WtBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CharpolyEqProd
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.KernelSemisimpleCharpolyProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologicalLocalComponentExponentsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CohomologicalCsdTemperedOfSegments
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.BnRepLin
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneCard
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

section SlopeTestRemainingChoices

open Formalism.MainNotions.N

/- English proof (translation)
Use `haveI : IsGalois (Lp L) L := inferInstance`. Establish `h` using `GlobalTheory.RayFromArtin.unramIn_of_ine (K := Lp L) (Ω := Ω) L (v := w.under (𝓞 (Lp L))) fun A hA σ hσ => by`. Take `⟨g, rfl⟩` from `s.unr A _ hA hσ`. Use extensionality with `x`. Apply `(algebraMap L Ω).injective` to reduce the goal to its premises.

Conclude with `(AlgEquiv.restrictNormal_commutes (W.resP L Ω g) L x).trans (g.commutes x)`. Establish `hb : w.asIdeal.inertia Gal(L/Lp L) = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `τ hτ`. Conclude with `h τ ⟨w.asIdeal, w.isPrime, ⟨rfl⟩, hτ⟩`.

Establish `h1` using `UpperTheory.V.CF.ineCard.1 (Lp L) L w`. Rewrite `h1` using `[hb, Subgroup.card_bot]`. Use `haveI := w.isPrime`. Use `haveI := w.isMaximal`. Use `haveI : (w.asIdeal.under (𝓞 (Lp L))).IsMaximal := Ideal.IsMaximal.under _ _`.

Conclude with `Ideal.ramificationIdx_eq_one_iff.1 h1.symm`.
-/
private theorem unr_of {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (w : HeightOneSpectrum (𝓞 L)) :
    Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal := by
  haveI : IsGalois (Lp L) L := inferInstance
  have h := GlobalTheory.RayFromArtin.unramIn_of_ine (K := Lp L) (Ω := Ω) L (v := w.under (𝓞 (Lp L))) fun A hA σ hσ => by
    obtain ⟨g, rfl⟩ := s.unr A _ hA hσ
    ext x
    apply (algebraMap L Ω).injective
    exact (AlgEquiv.restrictNormal_commutes (W.resP L Ω g) L x).trans (g.commutes x)
  have hb : w.asIdeal.inertia Gal(L/Lp L) = ⊥ := by
    rw [eq_bot_iff]
    intro τ hτ
    exact h τ ⟨w.asIdeal, w.isPrime, ⟨rfl⟩, hτ⟩
  have h1 := UpperTheory.V.CF.ineCard.1 (Lp L) L w
  rw [hb, Subgroup.card_bot] at h1
  haveI := w.isPrime
  haveI := w.isMaximal
  haveI : (w.asIdeal.under (𝓞 (Lp L))).IsMaximal := Ideal.IsMaximal.under _ _
  exact Ideal.ramificationIdx_eq_one_iff.1 h1.symm

variable {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h g => by obtain ⟨g, rfl⟩ := hφ g; exact h g, fun h g => h (φ g)⟩`.
-/
private theorem inv_comp {φ : Γ' →* Γ} (hφ : Function.Surjective φ) (r : Γ →* GL (Fin n) k) (M : Submodule k (Fin n → k)) :
    IsInv (r.comp φ) M ↔ IsInv r M :=
  ⟨fun h g => by obtain ⟨g, rfl⟩ := hφ g; exact h g, fun h g => h (φ g)⟩

/- English proof (translation)
Introduce `M hM` and use `by obtain ⟨M', h1, h2⟩ := h M ((inv_comp hφ r M).1 hM) exact ⟨M', (inv_comp hφ r M').2 h1, h2⟩`.
-/
private theorem ss_comp {φ : Γ' →* Γ} (hφ : Function.Surjective φ) {r : Γ →* GL (Fin n) k} (h : IsSSRep r) :
    IsSSRep (r.comp φ) := fun M hM => by
  obtain ⟨M', h1, h2⟩ := h M ((inv_comp hφ r M).1 hM)
  exact ⟨M', (inv_comp hφ r M').2 h1, h2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1, fun _ _ _ => Submodule.mem_top, fun M hM hi => h.2.2 M hM fun g => hi (φ g)⟩`.
-/
private theorem irr_of_comp (φ : Γ' →* Γ) {r : Γ →* GL (Fin n) k} (h : Af.IsIrr (r.comp φ)) : Af.IsIrr r :=
  ⟨h.1, fun _ _ _ => Submodule.mem_top, fun M hM hi => h.2.2 M hM fun g => hi (φ g)⟩

/- English proof (translation)
Introduce `M hM` and use `by rcases h.2.2 M le_top hM with rfl | rfl · exact ⟨⊤, h.2.1, isCompl_bot_top⟩ · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩ rw [(Submodule.mem_bot k).1 hv] simp`.
-/
private theorem ss_of_irr {r : Γ →* GL (Fin n) k} (h : Af.IsIrr r) : IsSSRep r := fun M hM => by
  rcases h.2.2 M le_top hM with rfl | rfl
  · exact ⟨⊤, h.2.1, isCompl_bot_top⟩
  · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
    rw [(Submodule.mem_bot k).1 hv]
    simp

/- English proof (translation)
Take `⟨P, hP⟩` from `e`. Use `⟨h.1, fun _ _ _ => Submodule.mem_top, fun M _ hM => ?_⟩` and prove the remaining obligations. Set `E : (Fin n → k) ≃ₗ[k] (Fin n → k)` to `(Matrix.GeneralLinearGroup.toLin P).toLinearEquiv`. Establish `hE : ∀ v, E v = (P : Matrix (Fin n) (Fin n) k).mulVec v` using `fun v => rfl`. Establish `hi : IsInv r (M.comap (E : (Fin n → k) →ₗ[k] (Fin n → k)))` using `fun g v hv => by`.

Use `hM g _ hv` as an intermediate fact. Express the relevant statement in the definitionally equal form `(r' g : Matrix (Fin n) (Fin n) k).mulVec ((P : Matrix (Fin n) (Fin n) k).mulVec v) ∈ M at this`. Express the relevant statement in the definitionally equal form `(P : Matrix (Fin n) (Fin n) k).mulVec _ ∈ M`. Rewrite `this` using `[Matrix.mulVec_mulVec, ← Units.val_mul, hP, inv_mul_cancel_right, Units.val_mul, ← Matrix.mulVec_mulVec]`. Then use the resulting hypothesis. Establish `hm : M = (M.comap (E : (Fin n → k) →ₗ[k] (Fin n → k))).map (E : (Fin n → k) →ₗ[k] (Fin n → k))` using `(Submodule.map_comap_eq_of_surjective E.surjective M).symm`.

Break down `h.2.2 _ le_top hi with h0 | h0` into its components or cases. Use `left`. Rewrite using `[hm, h0, Submodule.map_bot]`. Use `right`. Rewrite using `[hm, h0, Submodule.map_top, LinearEquiv.range]`.
-/
private theorem irr_iso {r r' : Γ →* GL (Fin n) k} (e : Af.RepIso r r') (h : Af.IsIrr r) : Af.IsIrr r' := by
  obtain ⟨P, hP⟩ := e
  refine ⟨h.1, fun _ _ _ => Submodule.mem_top, fun M _ hM => ?_⟩
  let E : (Fin n → k) ≃ₗ[k] (Fin n → k) := (Matrix.GeneralLinearGroup.toLin P).toLinearEquiv
  have hE : ∀ v, E v = (P : Matrix (Fin n) (Fin n) k).mulVec v := fun v => rfl
  have hi : IsInv r (M.comap (E : (Fin n → k) →ₗ[k] (Fin n → k))) := fun g v hv => by
    have := hM g _ hv
    change (r' g : Matrix (Fin n) (Fin n) k).mulVec ((P : Matrix (Fin n) (Fin n) k).mulVec v) ∈ M at this
    change (P : Matrix (Fin n) (Fin n) k).mulVec _ ∈ M
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, hP, inv_mul_cancel_right, Units.val_mul, ← Matrix.mulVec_mulVec] at this
  have hm : M = (M.comap (E : (Fin n → k) →ₗ[k] (Fin n → k))).map (E : (Fin n → k) →ₗ[k] (Fin n → k)) :=
    (Submodule.map_comap_eq_of_surjective E.surjective M).symm
  rcases h.2.2 _ le_top hi with h0 | h0
  · left; rw [hm, h0, Submodule.map_bot]
  · right; rw [hm, h0, Submodule.map_top, LinearEquiv.range]

/- English proof (translation)
Take `⟨P, hP⟩` from `AlgebraTools.Det.bnRep (W.mat r) (W.mat r') h h' fun g => by`. Rewrite using `[← (AlgebraTools.Det.repApi (W.mat r)).2.1 g, ← (AlgebraTools.Det.repApi (W.mat r')).2.1 g, e]`. Use `⟨P, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[eq_mul_inv_iff_mul_eq]`. Conclude with `Units.ext (hP g).symm`.
-/
private theorem iso_of_det {r r' : Γ →* GL (Fin n) k} (h : IsSSRep r) (h' : IsSSRep r')
    (e : W.GDet.ofRep (W.mat r) = W.GDet.ofRep (W.mat r')) : Af.RepIso r' r := by
  obtain ⟨P, hP⟩ := AlgebraTools.Det.bnRep (W.mat r) (W.mat r') h h' fun g => by
    rw [← (AlgebraTools.Det.repApi (W.mat r)).2.1 g, ← (AlgebraTools.Det.repApi (W.mat r')).2.1 g, e]
  refine ⟨P, fun g => ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  exact Units.ext (hP g).symm

/- English proof (translation)
Assemble the required witnesses or components as `⟨(Ideal.Quotient.liftₐ (RingHom.ker f) x fun _ hb => hx hb).comp (Ideal.quotientKerAlgEquivOfSurjective hf).symm.toAlgHom, fun b => by have : (Ideal.quotientKerAlgEquivOfSurjective hf).symm (f b) = Ideal.Quotient.mk _ b := by rw [AlgEquiv.symm_apply_eq]; rfl exact (congrArg (Idea …`.
-/
private theorem factor {O A T K : Type} [CommRing O] [CommRing A] [CommRing T] [CommRing K] [Algebra O A] [Algebra O T]
    [Algebra O K] (f : A →ₐ[O] T) (hf : Function.Surjective f) (x : A →ₐ[O] K) (hx : RingHom.ker f ≤ RingHom.ker x) :
    ∃ y : T →ₐ[O] K, ∀ b, y (f b) = x b :=
  ⟨(Ideal.Quotient.liftₐ (RingHom.ker f) x fun _ hb => hx hb).comp (Ideal.quotientKerAlgEquivOfSurjective hf).symm.toAlgHom,
    fun b => by
      have : (Ideal.quotientKerAlgEquivOfSurjective hf).symm (f b) = Ideal.Quotient.mk _ b := by
        rw [AlgEquiv.symm_apply_eq]; rfl
      exact (congrArg (Ideal.Quotient.liftₐ (RingHom.ker f) x fun _ hb => hx hb) this).trans rfl⟩

/- English proof (translation)
Take `rfl : x = y.comp f` from `RingHom.ext fun b => (h b).symm`. Both sides reduce to the same expression.
-/
private theorem map_comp {n : ℕ} {A T K Γ : Type} [CommRing A] [CommRing T] [CommRing K] [Group Γ] (D : W.GDet n A Γ)
    (f : A →+* T) (y : T →+* K) (x : A →+* K) (h : ∀ b, y (f b) = x b) : (D.map f).map y = D.map x := by
  obtain rfl : x = y.comp f := RingHom.ext fun b => (h b).symm
  rfl

end SlopeTestRemainingChoices

/- English proof (translation)
Take `⟨y, hy⟩` from `factor f hf x hx`. Establish `e1 : y.toRingHom.comp (algebraMap A _) = (x.comp j).toRingHom` using `RingHom.ext fun b => (congrArg y (hj b)).symm.trans (hy _)`. Take `⟨ρ, hc, hs, hP, hD, -⟩` from `out.pt lam hl y (e1 ▸ har)`. Conclude with `⟨ρ, hc, hs, hP, (map_comp D₀ f.toRingHom y.toRingHom x hy).symm.trans hD⟩`.
-/
private theorem absPt {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) {A : Type} [CommRing A] [Algebra c.O A] [IsLocalRing A] (θ : H.X.I.T →* Aˣ)
    (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] {R : Type} [CommRing R] [Algebra c.O R]
    (D₀ : W.GDet n R H.Gq) (j : A →ₐ[c.O] R) (f : R →ₐ[c.O] H.TK θ a K) (hf : Function.Surjective f)
    (hj : ∀ b, f (j b) = algebraMap A _ b) {P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop} {I : Ideal (H.TK θ a K)}
    {ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ} (out : H.Out θ a K P I (D₀.map f.toRingHom) ψ)
    (x : R →ₐ[c.O] Qbar l) (hx : RingHom.ker f ≤ RingHom.ker x) (lam : Wt L l n) (hl : lam ∈ H.admitted)
    (har : H.Arith θ (x.comp j).toRingHom lam) :
    ∃ ρ : H.Gq →* GL (Fin n) (Qbar l), Continuous ρ ∧ Formalism.MainNotions.N.IsSSRep ρ ∧ P lam ρ ∧
      D₀.map (x : R →+* Qbar l) = W.GDet.ofRep (W.mat ρ) := by
  obtain ⟨y, hy⟩ := factor f hf x hx
  have e1 : y.toRingHom.comp (algebraMap A _) = (x.comp j).toRingHom := RingHom.ext fun b =>
    (congrArg y (hj b)).symm.trans (hy _)
  obtain ⟨ρ, hc, hs, hP, hD, -⟩ := out.pt lam hl y (e1 ▸ har)
  exact ⟨ρ, hc, hs, hP, (map_comp D₀ f.toRingHom y.toRingHom x hy).symm.trans hD⟩

/- English proof (translation)
Break down `hJ with ⟨_, rfl⟩ | ⟨i1, i2, f, -, hmap, hsurj, hlam, rfl⟩` into its components or cases. Conclude with `absurd (hx (Submodule.mem_top (x := 1))) (by simp)`. Take `⟨⟨lam, hl⟩, hb⟩` from `wtBridge H.litN l L Ω s n hn V Q c R.m R.τ₀ r B Λ R.θ R.theta h ha.1`. Establish `har` using `(hb lam hl x).1.1 ha`. Establish `out` using `coreH H.litN L Ω l n c (hset Q R.τ₀) (axU H.litN l L Ω s n hn V Q c R.m R.τ₀) Λ.Λ R.θ R.isWt ι (PU r ι) (autU H l L Ω s n hn V Q c r ι R.m R.τ₀ R.type) lam (Set.mem_univ _) ((denseU H.litN l L Ω s n hn V Q c R.m R.τ₀ r Λ R.θ R.theta).2 lam) R.a K _ _ hmap`.

Take `⟨ρ, hc, hs, hP, e3⟩` from `absPt (hset Q R.τ₀) R.θ R.a K B.u.D (Λ.toPair B.u) f hsurj hlam out x hx lam (Set.mem_univ _) har`. Use `⟨lam, ρ, hc, hs, hP, ?_⟩` and prove the remaining obligations. Use `replace e3 : x.D = W.GDet.ofRep (W.mat ρ) := e3`. Express the relevant statement in the definitionally equal form `x.D.comap V.pr = _`. Rewrite using `[e3]`.

Conclude with `(AlgebraTools.Det.repApi (W.mat ρ)).2.2.2.2.2.2.1 V.pr`.
-/
private theorem core (H : Af.HypothesesH) {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} (hn : 1 ≤ n) {V : s.Lev} {Q : QData V} {c : Coef l}
    {r : Resid V.frame c.O n} {ι : Qbar l ≃+* ℂ} {B : UniversalOrdinaryDeterminantRing r} {Λ : LamObj r} {R : HD Q ι Λ} {K : (hset Q R.τ₀).Lev}
    {J : Ideal B.B} (hJ : R.IsJ B K J) (x : B.Pt) (h : s.Wt n) (hx : J ≤ RingHom.ker x) (ha : x.Arith h) :
    ∃ (lam : Wt L l n) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)), Continuous ρ ∧ Formalism.MainNotions.N.IsSSRep ρ ∧ PU r ι lam ρ ∧
      x.IsRep (ρ.comp V.pr) := by
  rcases hJ with ⟨_, rfl⟩ | ⟨i1, i2, f, -, hmap, hsurj, hlam, rfl⟩
  · exact absurd (hx (Submodule.mem_top (x := 1))) (by simp)
  obtain ⟨⟨lam, hl⟩, hb⟩ := wtBridge H.litN l L Ω s n hn V Q c R.m R.τ₀ r B Λ R.θ R.theta h ha.1
  have har := (hb lam hl x).1.1 ha
  have out := coreH H.litN L Ω l n c (hset Q R.τ₀) (axU H.litN l L Ω s n hn V Q c R.m R.τ₀) Λ.Λ R.θ R.isWt ι (PU r ι)
    (autU H l L Ω s n hn V Q c r ι R.m R.τ₀ R.type) lam (Set.mem_univ _)
    ((denseU H.litN l L Ω s n hn V Q c R.m R.τ₀ r Λ R.θ R.theta).2 lam) R.a K _ _ hmap
  obtain ⟨ρ, hc, hs, hP, e3⟩ := absPt (hset Q R.τ₀) R.θ R.a K B.u.D (Λ.toPair B.u) f hsurj hlam out x hx lam (Set.mem_univ _) har
  refine ⟨lam, ρ, hc, hs, hP, ?_⟩
  replace e3 : x.D = W.GDet.ofRep (W.mat ρ) := e3
  change x.D.comap V.pr = _
  rw [e3]
  exact (AlgebraTools.Det.repApi (W.mat ρ)).2.2.2.2.2.2.1 V.pr
