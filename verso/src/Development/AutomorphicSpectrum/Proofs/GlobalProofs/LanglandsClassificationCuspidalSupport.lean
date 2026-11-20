import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TotallyDisjointProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCuspidalSupportIrreducibleSmoothGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSubquotientParIndProductsFlattened
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionProductBlockRenamingEquivStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiExteriorTensorSmoothIrreducibleIsIrreducibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapInjectiveOfInjective
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.CuspEmbed

def piTensorMap {α : Type} {Γ Y Z : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (Y a)]
    [∀ a, Module ℂ (Y a)] [∀ a, AddCommGroup (Z a)] [∀ a, Module ℂ (Z a)]
    {ρ : ∀ a, Representation ℂ (Γ a) (Y a)} {σ : ∀ a, Representation ℂ (Γ a) (Z a)}
    (f : ∀ a, (ρ a).IntertwiningMap (σ a)) : (piTensor ρ).IntertwiningMap (piTensor σ) where
  toLinearMap := PiTensorProduct.map fun a => (f a).toLinearMap
  isIntertwining' g := by
    ext x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, piTensor_tprod,
      PiTensorProduct.map_tprod]
    congr 1
    funext a
    exact (f a).isIntertwining _ _ _ _

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.PiTensor.map_injective_of_injective ℂ α Y Z (fun a => (f a).toLinearMap) hf`.
-/
theorem piTensorMap_injective {α : Type} [Fintype α] [DecidableEq α] {Γ Y Z : α → Type}
    [∀ a, Group (Γ a)] [∀ a, AddCommGroup (Y a)]
    [∀ a, Module ℂ (Y a)] [∀ a, AddCommGroup (Z a)] [∀ a, Module ℂ (Z a)]
    {ρ : ∀ a, Representation ℂ (Γ a) (Y a)} {σ : ∀ a, Representation ℂ (Γ a) (Z a)}
    (f : ∀ a, (ρ a).IntertwiningMap (σ a)) (hf : ∀ a, Function.Injective (f a)) :
    Function.Injective (piTensorMap f) :=
  GlobalTheory.CompanionTheory.PiTensor.map_injective_of_injective ℂ α Y Z (fun a => (f a).toLinearMap) hf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Introduce `x y h` and use `Subtype.ext (Subtype.ext (funext fun g => hf (congrArg (fun z : IndSp e σ => z.1.1 g) h)))`.
-/
theorem parIndMap_injective {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) V} {σ : Representation ℂ (Levi k m) W}
    (f : ρ.IntertwiningMap σ) (hf : Function.Injective f) :
    Function.Injective (parIndMap e f) := fun x y h =>
  Subtype.ext (Subtype.ext (funext fun g => hf
    (congrArg (fun z : IndSp e σ => z.1.1 g) h)))

def Embeds (N : ℕ) (Q : Irr k N) : Prop :=
  ∃ (s : ℕ) (u : Fin s → IrrGL k) (e : (Σ a, Fin (u a).1) ≃ Fin N),
    (∀ a, (u a).IsCusp) ∧ ∃ φ : Q.π.IntertwiningMap (multiProd e fun a => (u a).rep),
      Function.Injective φ

/- English proof (translation)
Rewrite using `[Subsingleton.elim g 1, map_one, map_one]`. Both sides reduce to the same expression.
-/
theorem intertw_of_subsingleton {G V W : Type} [Group G] [Subsingleton G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (f : V →ₗ[ℂ] W)
    (g : G) : f ∘ₗ ρ g = σ g ∘ₗ f := by
  rw [Subsingleton.elim g 1, map_one, map_one]
  rfl

/- English proof (translation)
Establish `hQ` using `Q.irr`. Use `nontrivial_of_irreducible hQ` as an intermediate fact. Use `haveI : Subsingleton (GL (Fin 0) k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩`. Take `⟨v, hv⟩` from `exists_ne (0 : Q.V)`. Choose the witnesses or unpack the hypotheses as in `⟨f, hf⟩ : ∃ f : Module.Dual ℂ Q.V, f v ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 h)`. Establish `hker : Function.Injective f`. Set `S : Subrepresentation Q.π` to `⟨LinearMap.ker f, fun g x hx => by`.

Rewrite using `[Subsingleton.elim g 1, map_one]`. Conclude with `hx⟩`. Break down `eq_bot_or_eq_top S with h | h` into its components or cases. Establish `h' : LinearMap.ker f = ⊥` using `congrArg Subrepresentation.toSubmodule h`. Conclude with `LinearMap.ker_eq_bot.1 h'`.

Establish `h' : LinearMap.ker f = ⊤` using `congrArg Subrepresentation.toSubmodule h`. Conclude with `absurd (LinearMap.ker_eq_top.1 h' ▸ rfl : f v = 0) hf`. Set `u : Fin 0 → IrrGL k` to `fun a => a.elim0`. Use `haveI : IsEmpty (Σ a, Fin (u a).1) := ⟨fun x => x.1.elim0⟩`. Set `e : (Σ a, Fin (u a).1) ≃ Fin 0` to `Equiv.equivOfIsEmpty _ _`.

Set `L` to `GlobalTheory.EmptyProd.lineEquiv (k := k) e fun a => (u a).rep`. Conclude with `⟨0, u, e, fun a => a.elim0, ⟨L.symm.toLinearMap ∘ₗ f, intertw_of_subsingleton _ _ _⟩, L.symm.injective.comp hker⟩`.
-/
theorem embeds_zero (Q : Irr k 0) : Embeds 0 Q := by
  have hQ := Q.irr
  have := nontrivial_of_irreducible hQ
  haveI : Subsingleton (GL (Fin 0) k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : Q.V)
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ Q.V, f v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 h)
  have hker : Function.Injective f := by
    let S : Subrepresentation Q.π := ⟨LinearMap.ker f, fun g x hx => by
      rw [Subsingleton.elim g 1, map_one]
      exact hx⟩
    rcases eq_bot_or_eq_top S with h | h
    · have h' : LinearMap.ker f = ⊥ := congrArg Subrepresentation.toSubmodule h
      exact LinearMap.ker_eq_bot.1 h'
    · have h' : LinearMap.ker f = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact absurd (LinearMap.ker_eq_top.1 h' ▸ rfl : f v = 0) hf
  let u : Fin 0 → IrrGL k := fun a => a.elim0
  haveI : IsEmpty (Σ a, Fin (u a).1) := ⟨fun x => x.1.elim0⟩
  let e : (Σ a, Fin (u a).1) ≃ Fin 0 := Equiv.equivOfIsEmpty _ _
  let L := GlobalTheory.EmptyProd.lineEquiv (k := k) e fun a => (u a).rep
  exact ⟨0, u, e, fun a => a.elim0,
    ⟨L.symm.toLinearMap ∘ₗ f, intertw_of_subsingleton _ _ _⟩, L.symm.injective.comp hker⟩

/- English proof (translation)
Set `e : (Σ _ : Fin 1, Fin n) ≃ Fin n` to `{ toFun := fun p => p.2, invFun := fun i => ⟨0, i⟩, left_inv := fun p => by`. Take `⟨a, i⟩` from `p`. Take `rfl : a = 0` from `Subsingleton.elim _ _`. Both sides reduce to the same expression. Use `right_inv := fun _ => rfl }`.

Take `⟨φ⟩` from `nonempty_equiv_multiProd_one π.smooth e (fun _ _ => rfl)`. Set `x : IrrGL k` to `IrrGL.of π.π π.smooth π.irr`. Set `ψ` to `multiProdEquiv e fun _ : Fin 1 => IrrGL.equivOf π.π π.smooth π.irr`. Use `⟨1, fun _ => x, e, fun _ => (IrrGL.isCusp_of.2 ⟨hn, hc⟩), (φ.trans ψ).toIntertwiningMap, (φ.trans ψ).toLinearEquiv.injective⟩` and prove the remaining obligations.
-/
theorem embeds_cusp (n : ℕ) (hn : 0 < n) (π : Irr k n) (hc : IsCuspidal π.π) : Embeds n π := by
  let e : (Σ _ : Fin 1, Fin n) ≃ Fin n :=
    { toFun := fun p => p.2, invFun := fun i => ⟨0, i⟩,
      left_inv := fun p => by
        obtain ⟨a, i⟩ := p
        obtain rfl : a = 0 := Subsingleton.elim _ _
        rfl
      right_inv := fun _ => rfl }
  obtain ⟨φ⟩ := nonempty_equiv_multiProd_one π.smooth e (fun _ _ => rfl)
  let x : IrrGL k := IrrGL.of π.π π.smooth π.irr
  let ψ := multiProdEquiv e fun _ : Fin 1 => IrrGL.equivOf π.π π.smooth π.irr
  refine ⟨1, fun _ => x, e, fun _ => (IrrGL.isCusp_of.2 ⟨hn, hc⟩), (φ.trans ψ).toIntertwiningMap,
    (φ.trans ψ).toLinearEquiv.injective⟩

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨s, d, e, hne, hns⟩ : ∃ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), unipRad k e ≠ ⊥ ∧ ¬ Subsingleton (Jacquet π.π (unipRad k e)) := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hc ⟨π.smooth, fun s d e hne => h s d e hne⟩`. Take `⟨Y, _, _, τ, hτi, hτs, hτq, φ, hφ⟩` from `GlobalTheory.CuspSupportExist.L_jacq hBZ k n π s d e hns`.

Take `⟨σ, hσ⟩` from `GlobalTheory.CuspSupportExist.L_tens hGL k n π s d e Y τ hτi hτq`. Establish `hirr : (piTensor fun a => (σ a).π).IsIrreducible` using `GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k (Fin s) (fun a => Fin (d a)) fun a => (σ a).toIrrRep`. Take `⟨ε⟩` from `hσ.nonempty_equiv hτi hirr`. Set `ψ` to `parIndEquiv e ε.symm`. Conclude with `⟨s, d, e, σ, GlobalTheory.CuspSupportExist.L_lt k n s d e hne, ψ.toIntertwiningMap.comp φ, ψ.toLinearEquiv.injective.comp hφ⟩`.
-/
theorem reduce_embed (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    (hGL : GlobalTheory.Published.GeometricLemma) (n : ℕ) (π : Irr k n) (hc : ¬ IsCuspidal π.π) :
    ∃ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (σ : ∀ a, Irr k (d a)),
      (∀ a, d a < n) ∧ ∃ φ : π.π.IntertwiningMap (multiProd e fun a => (σ a).π),
        Function.Injective φ := by
  obtain ⟨s, d, e, hne, hns⟩ : ∃ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n),
      unipRad k e ≠ ⊥ ∧ ¬ Subsingleton (Jacquet π.π (unipRad k e)) := by
    by_contra h
    push_neg at h
    exact hc ⟨π.smooth, fun s d e hne => h s d e hne⟩
  obtain ⟨Y, _, _, τ, hτi, hτs, hτq, φ, hφ⟩ := GlobalTheory.CuspSupportExist.L_jacq hBZ k n π s d e hns
  obtain ⟨σ, hσ⟩ := GlobalTheory.CuspSupportExist.L_tens hGL k n π s d e Y τ hτi hτq
  have hirr : (piTensor fun a => (σ a).π).IsIrreducible :=
    GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k (Fin s) (fun a => Fin (d a)) fun a => (σ a).toIrrRep
  obtain ⟨ε⟩ := hσ.nonempty_equiv hτi hirr
  let ψ := parIndEquiv e ε.symm
  exact ⟨s, d, e, σ, GlobalTheory.CuspSupportExist.L_lt k n s d e hne,
    ψ.toIntertwiningMap.comp φ, ψ.toLinearEquiv.injective.comp hφ⟩

/- English proof (translation)
Take `⟨E0, ⟨χ⟩⟩` from `GlobalTheory.SmGL.Stages.stages_equiv (k := k) s d t (fun a b => (u a b).1) e' (fun a b => (u a b).2.rep.V) (fun a b => (u a b).rep) (Fin n) e`. Set `F : Fin (∑ a, t a) ≃ Σₗ a, Fin (t a)` to `finSigmaFinEquiv.symm.trans toLex`. Set `E : (Σ c : Fin (∑ a, t a), Fin (u (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2).1) ≃ Fin n` to `(Equiv.sigmaCongrLeft (β := fun c : Σₗ a, Fin (t a) => Fin (u (ofLex c).1 (ofLex c).2).1) F).trans E0`. Take `⟨ω⟩` from `GlobalTheory.T.parabolicInductionProduct_block_renaming_equiv (k := k) F (GlobalTheory.T.finSigmaFinEquiv_symm_strictMono_toLex s t) F.surjective E0 E (fun _ _ => rfl) fun c => (u (ofLex c).1 (ofLex c).2).rep`. Set `Ψ` to `parIndMap e (piTensorMap ψ)`.

Establish `hΨ : Function.Injective Ψ` using `parIndMap_injective e _ (piTensorMap_injective ψ hψ)`. Conclude with `⟨∑ a, t a, fun c => u (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2, E, fun c => hu _ _, (χ.trans ω).toIntertwiningMap.comp (Ψ.comp φ), (χ.trans ω).toLinearEquiv.injective.comp (hΨ.comp hφ)⟩`.
-/
theorem glue_embed (n : ℕ) (π : Irr k n) (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n)
    (σ : ∀ a, Irr k (d a)) (φ : π.π.IntertwiningMap (multiProd e fun a => (σ a).π))
    (hφ : Function.Injective φ) (t : Fin s → ℕ) (u : ∀ a, Fin (t a) → IrrGL k)
    (e' : ∀ a, (Σ b, Fin (u a b).1) ≃ Fin (d a)) (hu : ∀ a b, (u a b).IsCusp)
    (ψ : ∀ a, (σ a).π.IntertwiningMap (multiProd (e' a) fun b => (u a b).rep))
    (hψ : ∀ a, Function.Injective (ψ a)) : Embeds n π := by
  obtain ⟨E0, ⟨χ⟩⟩ := GlobalTheory.SmGL.Stages.stages_equiv (k := k) s d t (fun a b => (u a b).1) e'
    (fun a b => (u a b).2.rep.V) (fun a b => (u a b).rep) (Fin n) e
  let F : Fin (∑ a, t a) ≃ Σₗ a, Fin (t a) := finSigmaFinEquiv.symm.trans toLex
  let E : (Σ c : Fin (∑ a, t a),
      Fin (u (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2).1) ≃ Fin n :=
    (Equiv.sigmaCongrLeft (β := fun c : Σₗ a, Fin (t a) => Fin (u (ofLex c).1 (ofLex c).2).1) F).trans E0
  obtain ⟨ω⟩ := GlobalTheory.T.parabolicInductionProduct_block_renaming_equiv (k := k) F (GlobalTheory.T.finSigmaFinEquiv_symm_strictMono_toLex s t) F.surjective E0 E
    (fun _ _ => rfl) fun c => (u (ofLex c).1 (ofLex c).2).rep
  let Ψ := parIndMap e (piTensorMap ψ)
  have hΨ : Function.Injective Ψ := parIndMap_injective e _ (piTensorMap_injective ψ hψ)
  exact ⟨∑ a, t a, fun c => u (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2, E,
    fun c => hu _ _, (χ.trans ω).toIntertwiningMap.comp (Ψ.comp φ),
    (χ.trans ω).toLinearEquiv.injective.comp (hΨ.comp hφ)⟩

/- English proof (translation)
Proceed by induction on `N using Nat.strong_induction_on with`. Consider the case `_ n ih`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Conclude with `embeds_zero Q`. Distinguish the cases in `hc : IsCuspidal Q.π`.

Conclude with `embeds_cusp n hn Q hc`. Establish `hr` using `reduce_embed hBZ hGL n Q hc`. Take `⟨s, d, e, σ, hlt, hr⟩` from `hr`. Take `⟨φ, hφ⟩` from `hr`. Establish `h : ∀ a, Embeds (d a) (σ a)` using `fun a => ih (d a) (hlt a) (σ a)`.

Unfold `Embeds at h`. Use `choose t u e' hu ψ hψ using h`. Conclude with `glue_embed n Q s d e σ φ hφ t u e' hu ψ hψ`.
-/
theorem embeds (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (hGL : GlobalTheory.Published.GeometricLemma)
    (N : ℕ) (Q : Irr k N) : Embeds N Q := by
  induction N using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact embeds_zero Q
  by_cases hc : IsCuspidal Q.π
  · exact embeds_cusp n hn Q hc
  · have hr := reduce_embed hBZ hGL n Q hc
    obtain ⟨s, d, e, σ, hlt, hr⟩ := hr
    obtain ⟨φ, hφ⟩ := hr
    have h : ∀ a, Embeds (d a) (σ a) := fun a => ih (d a) (hlt a) (σ a)
    unfold Embeds at h
    choose t u e' hu ψ hψ using h
    exact glue_embed n Q s d e σ φ hφ t u e' hu ψ hψ

/- English proof (translation)
Introduce `hBZ hGL _ _ _ _ _ N Q` and use `embeds hBZ hGL N Q`.
-/
theorem main : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (N : ℕ) (Q : GlobalTheory.SplitRead.Irr k N),
      ∃ (s : ℕ) (u : Fin s → GlobalTheory.LocGL.IrrGL k) (e : (Σ a, Fin (u a).1) ≃ Fin N),
        (∀ a, (u a).IsCusp) ∧
          ∃ φ : Q.π.IntertwiningMap (GlobalTheory.SmGL.multiProd e fun a => (u a).rep),
            Function.Injective φ :=
  fun hBZ hGL _ _ _ _ _ N Q => embeds hBZ hGL N Q

end GlobalTheory.CompanionTheory.CuspEmbed
