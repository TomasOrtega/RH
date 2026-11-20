import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetModuleMapInjectiveOfInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetWordMultiplicityAdditiveJordanHolder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissibleAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTensorProductHasFiniteLength
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationTprodChevalley
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SocleJm

section General

variable {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]

/- English proof (translation)
Set `R : Subrepresentation ρ` to `ι.range`. Set `p : ρ.IntertwiningMap (subQuot ⊤ R)` to `⟨Submodule.mkQ _ ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation ρ).toSubmodule LinearMap.id (fun _ => trivial), fun _ => rfl⟩`. Establish `hp : ∀ v, p v = 0 ↔ v ∈ R.toSubmodule` using `fun v => Submodule.Quotient.mk_eq_zero _`. Rewrite using `[jhMult_exact ι p hσ hι (fun x => ?_) (fun u => (hp _).2 ⟨u, rfl⟩) (fun v hv => (hp v).1 hv)]`. Conclude with `le_self_add`.

Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Conclude with `⟨v.1, rfl⟩`.
-/
theorem jhMult_le_of_injective {σ : Representation ℂ G U} {ρ₁ : Representation ℂ G V}
    {ρ : Representation ℂ G W} (hσ : σ.IsIrreducible) (ι : ρ₁.IntertwiningMap ρ)
    (hι : Function.Injective ι) : jhMult σ ρ₁ ≤ jhMult σ ρ := by
  let R : Subrepresentation ρ := ι.range
  let p : ρ.IntertwiningMap (subQuot ⊤ R) :=
    ⟨Submodule.mkQ _ ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation ρ).toSubmodule LinearMap.id
      (fun _ => trivial), fun _ => rfl⟩
  have hp : ∀ v, p v = 0 ↔ v ∈ R.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
  rw [jhMult_exact ι p hσ hι (fun x => ?_) (fun u => (hp _).2 ⟨u, rfl⟩) (fun v hv => (hp v).1 hv)]
  · exact le_self_add
  · obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨v.1, rfl⟩

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] {V W U X : Type} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X]

/- English proof (translation)
Use `jhMult_exact (jacMap e ι) (jacMap e p) hσ (GlobalTheory.JacInj.jacMap_injective k _ _ _ e W V π₁ π ι hπ hι) (fun x => ?_) (fun x => ?_) (fun x hx => ?_)` and prove the remaining obligations. Take `⟨u, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Take `⟨v, rfl⟩` from `hp u`. Conclude with `⟨Submodule.Quotient.mk v, rfl⟩`. Take `⟨u, rfl⟩` from `Submodule.Quotient.mk_surjective _ x show Submodule.Quotient.mk (p (ι u)) = 0`.

Rewrite using `[he.apply_apply_eq_zero]`. Both sides reduce to the same expression. Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Establish `h1 : p v ∈ twKer π₂ (unipRad k e) 1` using `(Submodule.Quotient.mk_eq_zero _).1 hx`. Take `⟨v', hv', h2⟩` from `GlobalTheory.SmGL.Exponents.Additive.exists_mem_twKer p hp _ h1`.

Take `⟨u, hu⟩` from `(he (v - v')).1 (by rw [map_sub, h2, sub_self])`. Use `⟨Submodule.Quotient.mk u, ?_⟩` and prove the remaining obligations. Use `show Submodule.Quotient.mk (ι u) = Submodule.Quotient.mk v`. Rewrite using `[hu]`. Conclude with `(Submodule.Quotient.eq _).2 (by simpa using hv')`.
-/
theorem jhMult_jac_exact (e : (Σ a, m a) ≃ n) {σ : Representation ℂ (Levi k m) X}
    (hσ : σ.IsIrreducible) {π : Representation ℂ (GL n k) V} {π₁ : Representation ℂ (GL n k) W}
    {π₂ : Representation ℂ (GL n k) U} (ι : π₁.IntertwiningMap π) (p : π.IntertwiningMap π₂)
    (hπ : IsSmooth π) (hι : Function.Injective ι) (hp : Function.Surjective p)
    (he : Function.Exact ι p) :
    jhMult σ (jac e π) = jhMult σ (jac e π₁) + jhMult σ (jac e π₂) := by
  refine jhMult_exact (jacMap e ι) (jacMap e p) hσ
    (GlobalTheory.JacInj.jacMap_injective k _ _ _ e W V π₁ π ι hπ hι) (fun x => ?_) (fun x => ?_)
    (fun x hx => ?_)
  · obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨v, rfl⟩ := hp u
    exact ⟨Submodule.Quotient.mk v, rfl⟩
  · obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show Submodule.Quotient.mk (p (ι u)) = 0
    rw [he.apply_apply_eq_zero]
    rfl
  · obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : p v ∈ twKer π₂ (unipRad k e) 1 := (Submodule.Quotient.mk_eq_zero _).1 hx
    obtain ⟨v', hv', h2⟩ := GlobalTheory.SmGL.Exponents.Additive.exists_mem_twKer p hp _ h1
    obtain ⟨u, hu⟩ := (he (v - v')).1 (by rw [map_sub, h2, sub_self])
    refine ⟨Submodule.Quotient.mk u, ?_⟩
    show Submodule.Quotient.mk (ι u) = Submodule.Quotient.mk v
    rw [hu]
    exact (Submodule.Quotient.eq _).2 (by simpa using hv')

/- English proof (translation)
Take `⟨v, hv⟩` from `hf`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, (f v).1.1 x ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hv (Subtype.ext (Subtype.ext (funext h)))`.

Set `φ` to `GlobalTheory.SmGL.Model.evalOne e f`. Establish `h1 : φ (Submodule.Quotient.mk (τ x v)) ≠ 0`. Establish `: φ (Submodule.Quotient.mk (τ x v)) = (f v).1.1 x` using `by show (f (τ x v)).1.1 1 = _`. Rewrite using `[f.isIntertwining, parInd_apply, one_mul]`. Rewrite using `[this]` and apply the resulting hypothesis.

Establish `h2 : Function.Surjective φ`. Introduce `w`. Break down `eq_bot_or_eq_top φ.range with e' | e'` into its components or cases. Establish `h3 : φ (Submodule.Quotient.mk (τ x v)) ∈ φ.range` using `(Representation.IntertwiningMap.mem_range _ _ _ _).2 ⟨_, rfl⟩`. Rewrite `h3` using `[e']`.

Conclude with `absurd h3 h1`. Establish `h3 : w ∈ φ.range` using `e' ▸ trivial`. Conclude with `(Representation.IntertwiningMap.mem_range _ _ _ _).1 h3`. Conclude with `ENat.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2 (.of_surjective φ h2))`.
-/
theorem one_le_jhMult_jac (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) X}
    (hρ : ρ.IsIrreducible) {τ : Representation ℂ (GL n k) V} (f : τ.IntertwiningMap (parInd e ρ))
    (hf : ∃ v, f v ≠ 0) : 1 ≤ jhMult ρ (jac e τ) := by
  obtain ⟨v, hv⟩ := hf
  obtain ⟨x, hx⟩ : ∃ x, (f v).1.1 x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (Subtype.ext (Subtype.ext (funext h)))
  let φ := GlobalTheory.SmGL.Model.evalOne e f
  have h1 : φ (Submodule.Quotient.mk (τ x v)) ≠ 0 := by
    have : φ (Submodule.Quotient.mk (τ x v)) = (f v).1.1 x := by
      show (f (τ x v)).1.1 1 = _
      rw [f.isIntertwining, parInd_apply, one_mul]
    rwa [this]
  have h2 : Function.Surjective φ := by
    intro w
    rcases eq_bot_or_eq_top φ.range with e' | e'
    · have h3 : φ (Submodule.Quotient.mk (τ x v)) ∈ φ.range :=
        (Representation.IntertwiningMap.mem_range _ _ _ _).2 ⟨_, rfl⟩
      rw [e'] at h3
      exact absurd h3 h1
    · have h3 : w ∈ φ.range := e' ▸ trivial
      exact (Representation.IntertwiningMap.mem_range _ _ _ _).1 h3
  exact ENat.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2 (.of_surjective φ h2))

/- English proof (translation)
The claim follows from `GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => (x a).2.rep.irr) fun a φ hφ => GlobalTheory.SchurAdm.schur_admissible (GL (Fin (x a).1) k) (KO k (Fin (x a).1)) GlobalTheory.SplitFlip.isOpen_KO GlobalTheory.SplitFlip.isCompact_KO _ (x a).rep (x a).2.rep.i …`.
-/
theorem isIrreducible_piTensor (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h : ℕ} (x : Fin h → IrrGL k) :
    (piTensor fun a => (x a).rep).IsIrreducible :=
  GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => (x a).2.rep.irr) fun a φ hφ =>
    GlobalTheory.SchurAdm.schur_admissible (GL (Fin (x a).1) k) (KO k (Fin (x a).1)) GlobalTheory.SplitFlip.isOpen_KO
      GlobalTheory.SplitFlip.isCompact_KO _ (x a).rep (x a).2.rep.irr
      (hA k _ _ _ (x a).2.rep.smooth (x a).2.rep.irr) φ hφ

/- English proof (translation)
Take `⟨hGT, hLT⟩` from `(hasFiniteLength_iff_wellFounded _).1 hfl`. Use `haveI : IsAtomic (Subrepresentation π) := isAtomic_of_orderBot_wellFounded_lt wellFounded_lt`. Establish `hnt : (⊤ : Subrepresentation π) ≠ ⊥` using `fun hb => by`. Take `⟨u, hu⟩` from `exists_ne (0 : V)`. Establish `h1 : u ∈ (⊥ : Subrepresentation π)` using `hb ▸ trivial`.

Conclude with `hu h1`. Take `⟨S, hS, -⟩` from `(eq_bot_or_exists_atom_le (⊤ : Subrepresentation π)).resolve_left hnt`. Set `ι : S.toRepresentation.IntertwiningMap π` to `⟨S.toSubmodule.subtype, fun _ => rfl⟩`. Establish `huniq : ∀ T : Subrepresentation π, IsAtom T → T = S`. Introduce `T hT`.

Assume the negation of the conclusion as `hne`. Establish `hdis : T ⊓ S = ⊥` using `(hT.disjoint_of_ne hS hne).eq_bot`. Set `p : π.IntertwiningMap (subQuot ⊤ S)` to `⟨Submodule.mkQ _ ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation π).toSubmodule LinearMap.id (fun _ => trivial), fun _ => rfl⟩`. Establish `hp0 : ∀ v, p v = 0 ↔ v ∈ S.toSubmodule` using `fun v => Submodule.Quotient.mk_eq_zero _`. Establish `hps : Function.Surjective p` using `fun y => by`.

Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Conclude with `⟨v.1, rfl⟩`. Establish `hQ : IsSmooth (subQuot ⊤ S)` using `(IsSubquotient.of_surjective p hps).isSmooth hs`. Establish `hex : Function.Exact ι p` using `fun v => ⟨fun h0 => ⟨⟨v, (hp0 v).1 h0⟩, rfl⟩, fun ⟨u, hu⟩ => (hp0 v).2 (hu ▸ u.2)⟩`. Establish `hadd` using `jhMult_jac_exact e hρ ι p hs Subtype.val_injective hps hex`.

Set `ιT : T.toRepresentation.IntertwiningMap π` to `⟨T.toSubmodule.subtype, fun _ => rfl⟩`. Establish `hinj : Function.Injective (p.comp ιT)`. Use `(injective_iff_map_eq_zero _).2 fun u hu => ?_` and prove the remaining obligations. Establish `h1 : (u : V) ∈ S.toSubmodule` using `(hp0 _).1 hu`. Establish `h2 : (u : V) ∈ (T ⊓ S)` using `⟨u.2, h1⟩`.

Rewrite `h2` using `[hdis]`. Conclude with `Subtype.ext h2`. Establish `h1 : 1 ≤ jhMult ρ (jac e (subQuot ⊤ S))` using `(hone T hT).trans (jhMult_le_of_injective hρ (jacMap e (p.comp ιT)) (GlobalTheory.JacInj.jacMap_injective k _ _ _ e _ _ _ _ _ hQ hinj))`. Establish `h2 : (2 : ℕ∞) ≤ jhMult ρ (jac e π)`. Rewrite using `[hadd]`.

Conclude with `(by norm_num : (2 : ℕ∞) = 1 + 1).le.trans (add_le_add (hone S hS) h1)`. Conclude with `absurd (h2.trans hjm) (by norm_num)`. Establish `hirr` using `GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom S hS`. Use `⟨⟨S.toSubmodule, S.toRepresentation, (IsSubquotient.of_injective ι Subtype.val_injective).isSmooth hs, hirr⟩, hirr, ι, Subtype.val_injective, fun T hT => ?_⟩` and prove the remaining obligations. Rewrite using `[huniq T hT]`.

Use `SetLike.ext fun v => ⟨fun hv => (Representation.IntertwiningMap.mem_range _ _ _ _).2 ⟨⟨v, hv⟩, rfl⟩, fun hv => ?_⟩` and prove the remaining obligations. Take `⟨u, rfl⟩` from `(Representation.IntertwiningMap.mem_range _ _ _ _).1 hv`. Conclude with `u.2`.
-/
theorem exists_isSocle_of_forall_isAtom (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) X}
    (hρ : ρ.IsIrreducible) {π : Representation ℂ (GL n k) V} (hs : IsSmooth π) [Nontrivial V]
    (hfl : HasFiniteLength π)
    (hone : ∀ T : Subrepresentation π, IsAtom T → 1 ≤ jhMult ρ (jac e T.toRepresentation))
    (hjm : jhMult ρ (jac e π) ≤ 1) : ∃ τ : IrrRep (GL n k), IsSocle τ.ρ π := by
  obtain ⟨hGT, hLT⟩ := (hasFiniteLength_iff_wellFounded _).1 hfl
  haveI : IsAtomic (Subrepresentation π) := isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
  have hnt : (⊤ : Subrepresentation π) ≠ ⊥ := fun hb => by
    obtain ⟨u, hu⟩ := exists_ne (0 : V)
    have h1 : u ∈ (⊥ : Subrepresentation π) := hb ▸ trivial
    exact hu h1
  obtain ⟨S, hS, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Subrepresentation π)).resolve_left hnt
  let ι : S.toRepresentation.IntertwiningMap π := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  have huniq : ∀ T : Subrepresentation π, IsAtom T → T = S := by
    intro T hT
    by_contra hne
    have hdis : T ⊓ S = ⊥ := (hT.disjoint_of_ne hS hne).eq_bot
    let p : π.IntertwiningMap (subQuot ⊤ S) :=
      ⟨Submodule.mkQ _ ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation π).toSubmodule
        LinearMap.id (fun _ => trivial), fun _ => rfl⟩
    have hp0 : ∀ v, p v = 0 ↔ v ∈ S.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
    have hps : Function.Surjective p := fun y => by
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact ⟨v.1, rfl⟩
    have hQ : IsSmooth (subQuot ⊤ S) := (IsSubquotient.of_surjective p hps).isSmooth hs
    have hex : Function.Exact ι p := fun v =>
      ⟨fun h0 => ⟨⟨v, (hp0 v).1 h0⟩, rfl⟩, fun ⟨u, hu⟩ => (hp0 v).2 (hu ▸ u.2)⟩
    have hadd := jhMult_jac_exact e hρ ι p hs Subtype.val_injective hps hex
    let ιT : T.toRepresentation.IntertwiningMap π := ⟨T.toSubmodule.subtype, fun _ => rfl⟩
    have hinj : Function.Injective (p.comp ιT) := by
      refine (injective_iff_map_eq_zero _).2 fun u hu => ?_
      have h1 : (u : V) ∈ S.toSubmodule := (hp0 _).1 hu
      have h2 : (u : V) ∈ (T ⊓ S) := ⟨u.2, h1⟩
      rw [hdis] at h2
      exact Subtype.ext h2
    have h1 : 1 ≤ jhMult ρ (jac e (subQuot ⊤ S)) :=
      (hone T hT).trans (jhMult_le_of_injective hρ (jacMap e (p.comp ιT))
        (GlobalTheory.JacInj.jacMap_injective k _ _ _ e _ _ _ _ _ hQ hinj))
    have h2 : (2 : ℕ∞) ≤ jhMult ρ (jac e π) := by
      rw [hadd]
      exact (by norm_num : (2 : ℕ∞) = 1 + 1).le.trans (add_le_add (hone S hS) h1)
    exact absurd (h2.trans hjm) (by norm_num)
  have hirr := GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom S hS
  refine ⟨⟨S.toSubmodule, S.toRepresentation,
    (IsSubquotient.of_injective ι Subtype.val_injective).isSmooth hs, hirr⟩, hirr, ι,
    Subtype.val_injective, fun T hT => ?_⟩
  rw [huniq T hT]
  refine SetLike.ext fun v => ⟨fun hv => (Representation.IntertwiningMap.mem_range _ _ _ _).2
    ⟨⟨v, hv⟩, rfl⟩, fun hv => ?_⟩
  obtain ⟨u, rfl⟩ := (Representation.IntertwiningMap.mem_range _ _ _ _).1 hv
  exact u.2

/- English proof (translation)
Use `haveI : Nontrivial X := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hρ`. Take `⟨u, hu⟩` from `exists_ne (0 : X)`. Take `⟨f, hf, -⟩` from `GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one e ρ hsρ u`. Conclude with `⟨f, 0, fun h => hu (by rw [← hf, h]; rfl)⟩`.
-/
theorem nontrivial_indSp (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) X}
    (hρ : ρ.IsIrreducible) (hsρ : IsSmooth ρ) : Nontrivial (IndSp e ρ) := by
  haveI : Nontrivial X := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hρ
  obtain ⟨u, hu⟩ := exists_ne (0 : X)
  obtain ⟨f, hf, -⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one e ρ hsρ u
  exact ⟨f, 0, fun h => hu (by rw [← hf, h]; rfl)⟩

/- English proof (translation)
Set `ιT : T.toRepresentation.IntertwiningMap (parInd e ρ)` to `⟨T.toSubmodule.subtype, fun _ => rfl⟩`. Use `one_le_jhMult_jac e hρ ιT ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hT.1 (Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun v hv => (Submodule.mem_bot ℂ).2 (hc ⟨v, hv⟩)))`.
-/
theorem one_le_jhMult_jac_atom (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) X}
    (hρ : ρ.IsIrreducible) (T : Subrepresentation (parInd e ρ)) (hT : IsAtom T) :
    1 ≤ jhMult ρ (jac e T.toRepresentation) := by
  let ιT : T.toRepresentation.IntertwiningMap (parInd e ρ) := ⟨T.toSubmodule.subtype, fun _ => rfl⟩
  refine one_le_jhMult_jac e hρ ιT ?_
  by_contra hc
  push_neg at hc
  exact hT.1 (Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun v hv =>
    (Submodule.mem_bot ℂ).2 (hc ⟨v, hv⟩)))

/- English proof (translation)
Introduce `k _ _ _ _ hA h N x hd hjm`. Establish `hρ` using `isIrreducible_piTensor hA x`. Establish `hsρ : IsSmooth (piTensor fun a => (x a).rep)` using `isSmooth_piTensor fun a => (x a).2.rep.smooth`. Use `haveI := nontrivial_indSp (stdBlocks (fun a => (x a).1) hd) hρ hsρ`. Conclude with `exists_isSocle_of_forall_isAtom (stdBlocks (fun a => (x a).1) hd) hρ (isSmooth_parInd _ _) (GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k _ _ _ _ _ _ hsρ (hasFiniteLength_of_isIrreducible hρ)) (one_le_jhMult_jac_atom _ hρ) hjm`.
-/
theorem exists_isSocle_of_jm_le_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ}
    (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), jm x hd (prodIrr x hd) ≤ 1 →
    ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr x hd) := by
  intro k _ _ _ _ hA h N x hd hjm
  have hρ := isIrreducible_piTensor hA x
  have hsρ : IsSmooth (piTensor fun a => (x a).rep) := isSmooth_piTensor fun a => (x a).2.rep.smooth
  haveI := nontrivial_indSp (stdBlocks (fun a => (x a).1) hd) hρ hsρ
  exact exists_isSocle_of_forall_isAtom (stdBlocks (fun a => (x a).1) hd) hρ
    (isSmooth_parInd _ _)
    (GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k _ _ _ _ _ _ hsρ (hasFiniteLength_of_isIrreducible hρ))
    (one_le_jhMult_jac_atom _ hρ) hjm

end GlobalTheory.CompanionTheory.SocleJm

end
