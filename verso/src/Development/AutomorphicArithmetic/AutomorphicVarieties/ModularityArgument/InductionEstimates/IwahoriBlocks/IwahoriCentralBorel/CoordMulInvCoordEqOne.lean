import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.TensLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.TensSimple
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.XSimple
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.OpenStab
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.PiHomExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsCompactIsOpen

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks

section Abs

variable {A B H H₁ H₂ V : Type} [Group A] [Group B] [Group H] [Group H₁] [Group H₂] [AddCommGroup V] [Module ℂ V]

private def tr (a : A) (b : B) (F : A × B → ℂ) : A × B → ℂ := fun x => F (x.1 * a, x.2 * b)

/- English proof (translation)
Introduce `F hF`. Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem F h`. Take `⟨φ, hφ, ψ, hψ, rfl⟩` from `h`. Conclude with `Submodule.subset_span ⟨_, h₁ φ hφ, _, h₂ ψ hψ, rfl⟩`.

Consider the case `zero => exact zero_mem _`. Consider the case `add x y _ _ hx hy => exact add_mem hx hy`. Consider the case `smul c x _ hx => exact Submodule.smul_mem _ c hx`.
-/
private theorem tens_tr (X₁ : Submodule ℂ (A → ℂ)) (X₂ : Submodule ℂ (B → ℂ)) (a : A) (b : B)
    (h₁ : ∀ φ ∈ X₁, (fun x => φ (x * a)) ∈ X₁) (h₂ : ∀ ψ ∈ X₂, (fun x => ψ (x * b)) ∈ X₂) :
    ∀ F ∈ tensFn X₁ X₂, tr a b F ∈ tensFn X₁ X₂ := by
  intro F hF
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨φ, hφ, ψ, hψ, rfl⟩ := h
    exact Submodule.subset_span ⟨_, h₁ φ hφ, _, h₂ ψ hψ, rfl⟩
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

/- English proof (translation)
Establish `hnt : Nontrivial X` using `Submodule.nontrivial_iff_ne_bot.2 hne`. Use `{ exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }` and prove the remaining obligations. Take `⟨x, hx⟩` from `exists_ne (0 : X)`. Establish `h1 : x ∈ (⊤ : Subrepresentation (GlobalTheory.PRep.sub ρ X hs.1)).toSubmodule` using `Submodule.mem_top`. Rewrite `h1` using `[← h]`.

Conclude with `hx ((Submodule.mem_bot ℂ).1 h1)`. Establish `hst : ∀ g, ∀ v ∈ S.toSubmodule.map X.subtype, ρ g v ∈ S.toSubmodule.map X.subtype`. Introduce and unpack `g _ ⟨u, hu, rfl⟩`. Conclude with `⟨GlobalTheory.PRep.sub ρ X hs.1 g u, S.apply_mem_toSubmodule g hu, rfl⟩`. Break down `hs.2 _ (Submodule.map_subtype_le X _) hst with h | h` into its components or cases.

Use `left`. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Apply `Submodule.map_injective_of_injective X.injective_subtype` to reduce the goal to its premises. Rewrite using `[h]`. Conclude with `Submodule.map_bot _ |>.symm`.

Use `right`. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Apply `Submodule.map_injective_of_injective X.injective_subtype` to reduce the goal to its premises. Rewrite using `[h]`. Conclude with `(Submodule.map_subtype_top X).symm`.
-/
private theorem irr_sub (ρ : Representation ℂ H V) (X : Submodule ℂ V) (hs : SimpleIn ρ X) (hne : X ≠ ⊥) :
    (GlobalTheory.PRep.sub ρ X hs.1).IsIrreducible := by
  have hnt : Nontrivial X := Submodule.nontrivial_iff_ne_bot.2 hne
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · obtain ⟨x, hx⟩ := exists_ne (0 : X)
    have h1 : x ∈ (⊤ : Subrepresentation (GlobalTheory.PRep.sub ρ X hs.1)).toSubmodule := Submodule.mem_top
    rw [← h] at h1
    exact hx ((Submodule.mem_bot ℂ).1 h1)
  · have hst : ∀ g, ∀ v ∈ S.toSubmodule.map X.subtype, ρ g v ∈ S.toSubmodule.map X.subtype := by
      rintro g _ ⟨u, hu, rfl⟩
      exact ⟨GlobalTheory.PRep.sub ρ X hs.1 g u, S.apply_mem_toSubmodule g hu, rfl⟩
    rcases hs.2 _ (Submodule.map_subtype_le X _) hst with h | h
    · left
      apply Subrepresentation.toSubmodule_injective
      apply Submodule.map_injective_of_injective X.injective_subtype
      rw [h]
      exact Submodule.map_bot _ |>.symm
    · right
      apply Subrepresentation.toSubmodule_injective
      apply Submodule.map_injective_of_injective X.injective_subtype
      rw [h]
      exact (Submodule.map_subtype_top X).symm

/- English proof (translation)
Introduce `T hT`. Use `c T fun g v v' h => ?_` and prove the remaining obligations. Establish `h' : v' = GlobalTheory.PRep.sub ρ X hU g v` using `Subtype.ext h`. Rewrite using `[h', hT]`. Both sides reduce to the same expression.
-/
private theorem schur_sub (ρ : Representation ℂ H V) (X : Submodule ℂ V) (hU : ∀ g, ∀ v ∈ X, ρ g v ∈ X)
    (c : SchurIn ρ X) : Schur (GlobalTheory.PRep.sub ρ X hU) := by
  intro T hT
  refine c T fun g v v' h => ?_
  have h' : v' = GlobalTheory.PRep.sub ρ X hU g v := Subtype.ext h
  rw [h', hT]
  rfl

/- English proof (translation)
Use `Submodule.span_eq_bot.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨φ, hφ, ψ, _, rfl⟩`. Rewrite `hφ` using `[h, Submodule.mem_bot]`. Substitute `hφ` using the available equality. Use function extensionality and compare the values at `x`.

Simplify using the standard rewrite rules.
-/
private theorem tens_bot_left (X₁ : Submodule ℂ (A → ℂ)) (X₂ : Submodule ℂ (B → ℂ)) (h : X₁ = ⊥) :
    tensFn X₁ X₂ = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro _ ⟨φ, hφ, ψ, _, rfl⟩
  rw [h, Submodule.mem_bot] at hφ
  subst hφ
  funext x
  simp

/- English proof (translation)
Use `Submodule.span_eq_bot.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨φ, _, ψ, hψ, rfl⟩`. Rewrite `hψ` using `[h, Submodule.mem_bot]`. Substitute `hψ` using the available equality. Use function extensionality and compare the values at `x`.

Simplify using the standard rewrite rules.
-/
private theorem tens_bot_right (X₁ : Submodule ℂ (A → ℂ)) (X₂ : Submodule ℂ (B → ℂ)) (h : X₂ = ⊥) :
    tensFn X₁ X₂ = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro _ ⟨φ, _, ψ, hψ, rfl⟩
  rw [h, Submodule.mem_bot] at hψ
  subst hψ
  funext x
  simp

/- English proof (translation)
Distinguish the cases in `n₁ : X₁ = ⊥`. Use `left`. Conclude with `le_bot_iff.1 (hQ.trans (tens_bot_left X₁ X₂ n₁).le)`. Distinguish the cases in `n₂ : X₂ = ⊥`. Use `left`.

Conclude with `le_bot_iff.1 (hQ.trans (tens_bot_right X₁ X₂ n₂).le)`. Take `⟨e, he⟩` from `(tensLaws X₁ X₂).1`. Establish `hirr` using `(tensSimple _ _ (irr_sub _ X₁ s₁ n₁) (schur_sub _ X₁ s₁.1 c₁) (irr_sub _ X₂ s₂ n₂)).1`. Use `set E := extTensor (GlobalTheory.PRep.sub _ X₁ s₁.1) (GlobalTheory.PRep.sub _ X₂ s₂.1) with hE`. Establish `law : ∀ g y, (e (E g y)).1 = tr (θ₁ g.1) (θ₂ g.2) (e y).1`.

Introduce `g y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Both sides reduce to the same expression. Consider the case `tmul φ ψ`.

Rewrite using `[hE, extTensor_tmul]`. Use function extensionality and compare the values at `x`. Rewrite using `[he]`. Use `show _ = (e (φ ⊗ₜ ψ)).1 _`. Rewrite using `[he]`.

Both sides reduce to the same expression. Consider the case `add a b ha hb`. Simplify using `only [map_add, Submodule.coe_add, ha, hb]`. Both sides reduce to the same expression. Set `S : Subrepresentation E` to `⟨(Q.comap (tensFn X₁ X₂).subtype).comap e.toLinearMap, fun g y hy => by show (e (E g y)).1 ∈ Q`.

Rewrite using `[law]`. Conclude with `hst _ _ _ hy⟩`. Establish `hmem : ∀ F (hF : F ∈ tensFn X₁ X₂), F ∈ Q ↔ e.symm ⟨F, hF⟩ ∈ S.toSubmodule`. Introduce `F hF`. Use `show _ ↔ (e (e.symm ⟨F, hF⟩)).1 ∈ Q`.

Simplify using the standard rewrite rules. Break down `IsSimpleOrder.eq_bot_or_eq_top S with h | h` into its components or cases. Use `left`. Use `(Submodule.eq_bot_iff _).2 fun F hF => ?_` and prove the remaining obligations. Establish `h1` using `(hmem F (hQ hF)).1 hF`.

Rewrite `h1` using `[h]`. Establish `h2 : e.symm ⟨F, hQ hF⟩ = 0` using `(Submodule.mem_bot ℂ).1 h1`. Establish `h3` using `congrArg Subtype.val (e.symm_apply_eq.1 h2)`. Simplify using `using h3`. Use `right`.

Use `le_antisymm hQ fun F hF => (hmem F hF).2 ?_` and prove the remaining obligations. Rewrite using `[h]`. Conclude with `Submodule.mem_top`.
-/
private theorem tens_simple (θ₁ : H₁ →* A) (θ₂ : H₂ →* B) (X₁ : Submodule ℂ (A → ℂ)) (X₂ : Submodule ℂ (B → ℂ))
    (s₁ : SimpleIn ((rightReg ℂ A ℂ).comp θ₁) X₁) (c₁ : SchurIn ((rightReg ℂ A ℂ).comp θ₁) X₁)
    (s₂ : SimpleIn ((rightReg ℂ B ℂ).comp θ₂) X₂) (Q : Submodule ℂ (A × B → ℂ)) (hQ : Q ≤ tensFn X₁ X₂)
    (hst : ∀ g₁ g₂, ∀ F ∈ Q, tr (θ₁ g₁) (θ₂ g₂) F ∈ Q) : Q = ⊥ ∨ Q = tensFn X₁ X₂ := by
  by_cases n₁ : X₁ = ⊥
  · left; exact le_bot_iff.1 (hQ.trans (tens_bot_left X₁ X₂ n₁).le)
  by_cases n₂ : X₂ = ⊥
  · left; exact le_bot_iff.1 (hQ.trans (tens_bot_right X₁ X₂ n₂).le)
  obtain ⟨e, he⟩ := (tensLaws X₁ X₂).1
  have hirr := (tensSimple _ _ (irr_sub _ X₁ s₁ n₁) (schur_sub _ X₁ s₁.1 c₁) (irr_sub _ X₂ s₂ n₂)).1
  set E := extTensor (GlobalTheory.PRep.sub _ X₁ s₁.1) (GlobalTheory.PRep.sub _ X₂ s₂.1) with hE
  have law : ∀ g y, (e (E g y)).1 = tr (θ₁ g.1) (θ₂ g.2) (e y).1 := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]; rfl
    | tmul φ ψ =>
      rw [hE, extTensor_tmul]
      funext x
      rw [he]
      show _ = (e (φ ⊗ₜ ψ)).1 _
      rw [he]
      rfl
    | add a b ha hb =>
      simp only [map_add, Submodule.coe_add, ha, hb]
      rfl
  let S : Subrepresentation E :=
    ⟨(Q.comap (tensFn X₁ X₂).subtype).comap e.toLinearMap, fun g y hy => by
      show (e (E g y)).1 ∈ Q
      rw [law]
      exact hst _ _ _ hy⟩
  have hmem : ∀ F (hF : F ∈ tensFn X₁ X₂), F ∈ Q ↔ e.symm ⟨F, hF⟩ ∈ S.toSubmodule := by
    intro F hF
    show _ ↔ (e (e.symm ⟨F, hF⟩)).1 ∈ Q
    simp
  rcases IsSimpleOrder.eq_bot_or_eq_top S with h | h
  · left
    refine (Submodule.eq_bot_iff _).2 fun F hF => ?_
    have h1 := (hmem F (hQ hF)).1 hF
    rw [h] at h1
    have h2 : e.symm ⟨F, hQ hF⟩ = 0 := (Submodule.mem_bot ℂ).1 h1
    have h3 := congrArg Subtype.val (e.symm_apply_eq.1 h2)
    simpa using h3
  · right
    refine le_antisymm hQ fun F hF => (hmem F hF).2 ?_
    rw [h]
    exact Submodule.mem_top

end Abs

section Glob

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
The claim follows from `GlobalTheory.ParabLevel.continuous_leviTwo_symm.comp (GlobalTheory.ParabLevel.continuous_leviProj _)`.
-/
private theorem continuous_lev₂ (v : Pl K) : Continuous (lev₂ v) :=
  GlobalTheory.ParabLevel.continuous_leviTwo_symm.comp (GlobalTheory.ParabLevel.continuous_leviProj _)

/- English proof (translation)
Use `⟨⟨leviEmb (v.adicCompletion K) (two (stdSum (rfl : 2 + 2 = 2 + 2))) (leviTwo (v.adicCompletion K) (Fin 2) (Fin 2) (a, b)), leviEmb_mem_parab _ _ _⟩, ?_⟩` and prove the remaining obligations. Use `show (leviTwo (v.adicCompletion K) (Fin 2) (Fin 2)).symm (leviProj (v.adicCompletion K) (two (stdSum (rfl : 2 + 2 = 2 + 2))) ⟨_, _⟩) = _`. Rewrite using `[leviProj_leviEmb, MulEquiv.symm_apply_apply]`.
-/
private theorem lev₂_surj (v : Pl K) (a b : Gw 2 v) : ∃ q : PW v, lev₂ v q = (a, b) := by
  refine ⟨⟨leviEmb (v.adicCompletion K) (two (stdSum (rfl : 2 + 2 = 2 + 2))) (leviTwo (v.adicCompletion K) (Fin 2) (Fin 2) (a, b)),
    leviEmb_mem_parab _ _ _⟩, ?_⟩
  show (leviTwo (v.adicCompletion K) (Fin 2) (Fin 2)).symm (leviProj (v.adicCompletion K) (two (stdSum (rfl : 2 + 2 = 2 + 2))) ⟨_, _⟩) = _
  rw [leviProj_leviEmb, MulEquiv.symm_apply_apply]

/- English proof (translation)
The claim follows from `(isSmoothChar_deltaHalf (v.adicCompletion K)).comp _ (GlobalTheory.ParabLevel.continuous_leviProj _)`.
-/
private theorem smooth_dl (v : Pl K) : IsSmoothChar (dl v) :=
  (isSmoothChar_deltaHalf (v.adicCompletion K)).comp _ (GlobalTheory.ParabLevel.continuous_leviProj _)

/- English proof (translation)
Unfold `dS`. Use `Finset.prod_induction _ IsSmoothChar (fun _ _ => IsSmoothChar.mul) ?_ fun i _ => ?_` and prove the remaining obligations. Unfold `IsSmoothChar`. Simplify using the standard rewrite rules. Conclude with `(smooth_dl (w i)).comp _ (continuous_apply i)`.
-/
private theorem smooth_dS {r : ℕ} (w : Fin r → Pl K) : IsSmoothChar (dS w) := by
  unfold dS
  refine Finset.prod_induction _ IsSmoothChar (fun _ _ => IsSmoothChar.mul) ?_ fun i _ => ?_
  · unfold IsSmoothChar; simp
  · exact (smooth_dl (w i)).comp _ (continuous_apply i)

private noncomputable def L₁ {r : ℕ} (w : Fin r → Pl K) : (∀ i, PW (w i)) →* GS 2 w :=
  MonoidHom.pi fun i => (MonoidHom.fst _ _).comp ((lev₂ (w i)).comp (Pi.evalMonoidHom (fun i => PW (w i)) i))

private noncomputable def L₂ {r : ℕ} (w : Fin r → Pl K) : (∀ i, PW (w i)) →* GS 2 w :=
  MonoidHom.pi fun i => (MonoidHom.snd _ _).comp ((lev₂ (w i)).comp (Pi.evalMonoidHom (fun i => PW (w i)) i))

/- English proof (translation)
The claim follows from `continuous_pi fun i => continuous_fst.comp ((continuous_lev₂ (w i)).comp (continuous_apply i))`.
-/
private theorem continuous_L₁ {r : ℕ} (w : Fin r → Pl K) : Continuous (L₁ w) :=
  continuous_pi fun i => continuous_fst.comp ((continuous_lev₂ (w i)).comp (continuous_apply i))

/- English proof (translation)
The claim follows from `continuous_pi fun i => continuous_snd.comp ((continuous_lev₂ (w i)).comp (continuous_apply i))`.
-/
private theorem continuous_L₂ {r : ℕ} (w : Fin r → Pl K) : Continuous (L₂ w) :=
  continuous_pi fun i => continuous_snd.comp ((continuous_lev₂ (w i)).comp (continuous_apply i))

/- English proof (translation)
Use `choose q hq using fun i => lev₂_surj (w i) (g₁ i) (g₂ i)`. Use `⟨q, funext fun i => ?_, funext fun i => ?_⟩` and prove the remaining obligations. Conclude with `congrArg Prod.fst (hq i)`. Conclude with `congrArg Prod.snd (hq i)`.
-/
private theorem L_surj {r : ℕ} (w : Fin r → Pl K) (g₁ g₂ : GS 2 w) : ∃ p, L₁ w p = g₁ ∧ L₂ w p = g₂ := by
  choose q hq using fun i => lev₂_surj (w i) (g₁ i) (g₂ i)
  refine ⟨q, funext fun i => ?_, funext fun i => ?_⟩
  · exact congrArg Prod.fst (hq i)
  · exact congrArg Prod.snd (hq i)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem xS_eq {r : ℕ} {w : Fin r → Pl K} (ι : GS 2 w →* FA K 2) (p : ∀ i, PW (w i)) (F : G1 K 2 × G1 K 2 → ℂ) :
    xS ι p F = ((dS w p : ℂˣ) : ℂ) • tr (fin1 (ι (L₁ w p))) (fin1 (ι (L₂ w p))) F := rfl

end Glob

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks

/- English proof (translation)
Introduce `K _ _ _ μ _ τ₁ τ₂ κ p₁ p₂ c₁ c₂ r₁ r₂ r w ι hw hι`. Take `⟨s₁, sc₁⟩` from `xSimple μ τ₁ κ p₁ c₁ r₁ w ι hw hι`. Take `⟨s₂, -⟩` from `xSimple μ τ₂ κ p₂ c₂ r₂ w ι hw hι`. Establish `m₁` using `(xMem μ τ₁ κ p₁ r₁.1).2 c₁ w ι hw hι`. Establish `m₂` using `(xMem μ τ₂ κ p₂ r₂.1).2 c₂ w ι hw hι`.

Use `set X₁ := Xs μ τ₁ κ p₁ (im w) with hX₁`. Use `set X₂ := Xs μ τ₂ κ p₂ (im w) with hX₂`. Establish `hstab : ∀ p, ∀ F ∈ tensFn X₁ X₂, tr (fin1 (ι (L₁ w p))) (fin1 (ι (L₂ w p))) F ∈ tensFn X₁ X₂` using `fun p => tens_tr X₁ X₂ _ _ (fun φ hφ => (m₁ φ hφ).2 (L₁ w p)) (fun ψ hψ => (m₂ ψ hψ).2 (L₂ w p))`. Use `⟨⟨fun p F hF => ?_, fun Q hQ hst => ?_⟩, fun F hF => ?_⟩` and prove the remaining obligations. Rewrite using `[xS_eq]`.

Conclude with `Submodule.smul_mem _ _ (hstab p F hF)`. Use `tens_simple ((MultiplicityOne.finProj K 2).comp ι) ((MultiplicityOne.finProj K 2).comp ι) X₁ X₂ s₁ sc₁ s₂ Q hQ fun g₁ g₂ F hF => ?_` and prove the remaining obligations. Take `⟨p, rfl, rfl⟩` from `L_surj w g₁ g₂`. Establish `h` using `Q.smul_mem (((dS w p)⁻¹ : ℂˣ) : ℂ) (hst p F hF)`. Rewrite `h` using `[xS_eq, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]`.

Conclude with `h`. Establish `hsm : tensFn X₁ X₂ ≤ GlobalTheory.PRep.smoothPart ((rightReg ℂ (G1 K 2 × G1 K 2) ℂ).comp (blocks ι))`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨φ, hφ, ψ, hψ, rfl⟩`. Use `mem_smoothPart_of_nhds (Filter.mem_of_superset ((((m₁ φ hφ).1.preimage (continuous_L₁ w)).inter ((m₂ ψ hψ).1.preimage (continuous_L₂ w))).mem_nhds ?_) ?_)` and prove the remaining obligations.

Apply the tactic sequence `constructor <;> simp`. Introduce and unpack `p ⟨h₁, h₂⟩`. Use function extensionality and compare the values at `x`. Establish `e₁` using `congrFun h₁ x.1`. Establish `e₂` using `congrFun h₂ x.2`.

Use `show φ (x.1 * _) * ψ (x.2 * _) = φ x.1 * ψ x.2`. Conclude with `congrArg₂ (· * ·) e₁ e₂`. Establish `hF₀ : IsOpen {p | (rightReg ℂ (G1 K 2 × G1 K 2) ℂ).comp (blocks ι) p F = F}` using `hsm hF`. Establish `hk : IsOpen ((dS w).ker : Set (∀ i, PW (w i)))` using `smooth_dS w`. Establish `hF' : F ∈ GlobalTheory.PRep.smoothPart (xS ι)`.

Use `mem_smoothPart_of_nhds (Filter.mem_of_superset ((hF₀.inter hk).mem_nhds ?_) ?_)` and prove the remaining obligations. Conclude with `⟨by simp, one_mem _⟩`. Introduce and unpack `p ⟨h₁, h₂⟩`. Establish `h₃ : dS w p = 1` using `h₂`. Use `show ((dS w p : ℂˣ) : ℂ) • (rightReg ℂ (G1 K 2 × G1 K 2) ℂ).comp (blocks ι) p F = F`.

Rewrite using `[h₃, Units.val_one, one_smul]`. Conclude with `h₁`. Conclude with `hF'`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.x12 :
    ∀ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ : Measure (G1 K 2)) [μ.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ)) (κ : Measure (archCompact K 2)) (p₁ p₂ : archCompact K 2 → ℂ),
      CuspIrr μ τ₁ → CuspIrr μ τ₂ → RankInf μ τ₁ κ p₁ → RankInf μ τ₂ κ p₂ → ∀ {r : ℕ} (w : Fin r → Pl K) (ι : GS 2 w →* FA K 2), Function.Injective w → IsEmb w ι →
      SimpleIn (xS ι) (tensFn (Xs μ τ₁ κ p₁ (im w)) (Xs μ τ₂ κ p₂ (im w))) ∧
        ∀ F ∈ tensFn (Xs μ τ₁ κ p₁ (im w)) (Xs μ τ₂ κ p₂ (im w)), IsOpen {p | xS ι p F = F} := by
  intro K _ _ _ μ _ τ₁ τ₂ κ p₁ p₂ c₁ c₂ r₁ r₂ r w ι hw hι
  obtain ⟨s₁, sc₁⟩ := xSimple μ τ₁ κ p₁ c₁ r₁ w ι hw hι
  obtain ⟨s₂, -⟩ := xSimple μ τ₂ κ p₂ c₂ r₂ w ι hw hι
  have m₁ := (xMem μ τ₁ κ p₁ r₁.1).2 c₁ w ι hw hι
  have m₂ := (xMem μ τ₂ κ p₂ r₂.1).2 c₂ w ι hw hι
  set X₁ := Xs μ τ₁ κ p₁ (im w) with hX₁
  set X₂ := Xs μ τ₂ κ p₂ (im w) with hX₂
  have hstab : ∀ p, ∀ F ∈ tensFn X₁ X₂, tr (fin1 (ι (L₁ w p))) (fin1 (ι (L₂ w p))) F ∈ tensFn X₁ X₂ := fun p =>
    tens_tr X₁ X₂ _ _ (fun φ hφ => (m₁ φ hφ).2 (L₁ w p)) (fun ψ hψ => (m₂ ψ hψ).2 (L₂ w p))
  refine ⟨⟨fun p F hF => ?_, fun Q hQ hst => ?_⟩, fun F hF => ?_⟩
  · rw [xS_eq]
    exact Submodule.smul_mem _ _ (hstab p F hF)
  · refine tens_simple ((MultiplicityOne.finProj K 2).comp ι) ((MultiplicityOne.finProj K 2).comp ι) X₁ X₂ s₁ sc₁ s₂ Q hQ
      fun g₁ g₂ F hF => ?_
    obtain ⟨p, rfl, rfl⟩ := L_surj w g₁ g₂
    have h := Q.smul_mem (((dS w p)⁻¹ : ℂˣ) : ℂ) (hst p F hF)
    rw [xS_eq, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul] at h
    exact h
  · have hsm : tensFn X₁ X₂ ≤ GlobalTheory.PRep.smoothPart ((rightReg ℂ (G1 K 2 × G1 K 2) ℂ).comp (blocks ι)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨φ, hφ, ψ, hψ, rfl⟩
      refine mem_smoothPart_of_nhds (Filter.mem_of_superset
        ((((m₁ φ hφ).1.preimage (continuous_L₁ w)).inter ((m₂ ψ hψ).1.preimage (continuous_L₂ w))).mem_nhds ?_) ?_)
      · constructor <;> simp
      · rintro p ⟨h₁, h₂⟩
        funext x
        have e₁ := congrFun h₁ x.1
        have e₂ := congrFun h₂ x.2
        show φ (x.1 * _) * ψ (x.2 * _) = φ x.1 * ψ x.2
        exact congrArg₂ (· * ·) e₁ e₂
    have hF₀ : IsOpen {p | (rightReg ℂ (G1 K 2 × G1 K 2) ℂ).comp (blocks ι) p F = F} := hsm hF
    have hk : IsOpen ((dS w).ker : Set (∀ i, PW (w i))) := smooth_dS w
    have hF' : F ∈ GlobalTheory.PRep.smoothPart (xS ι) := by
      refine mem_smoothPart_of_nhds (Filter.mem_of_superset
        ((hF₀.inter hk).mem_nhds ?_) ?_)
      · exact ⟨by simp, one_mem _⟩
      · rintro p ⟨h₁, h₂⟩
        have h₃ : dS w p = 1 := h₂
        show ((dS w p : ℂˣ) : ℂ) • (rightReg ℂ (G1 K 2 × G1 K 2) ℂ).comp (blocks ι) p F = F
        rw [h₃, Units.val_one, one_smul]
        exact h₁
    exact hF'
