import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionPullbackCartesianGroupSchemesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomCharacterEndOfTorusExtensionActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusTangentVectorsAddMonoidHomStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorLie

section Grp
variable {S Z : Scheme.{0}} {G : Over S} [GrpObj G]

/- English proof (translation)
Use `show (toUnit T ≫ η[G]).left = _`. Rewrite using `[Over.comp_left, Over.toUnit_left]`.
-/
theorem one_left' (T : Over S) : (1 : T ⟶ G).left = T.hom ≫ η[G].left := by
  show (toUnit T ≫ η[G]).left = _
  rw [Over.comp_left, Over.toUnit_left]

/- English proof (translation)
Establish `hb : u' ≫ T'.hom = u ≫ T.hom`. Rewrite using `[← Over.w x, ← Over.w x', ← Category.assoc, ← hx, Category.assoc]`. Set `U : Over.mk (u ≫ T.hom) ⟶ T` to `Over.homMk u rfl`. Set `U' : Over.mk (u ≫ T.hom) ⟶ T'` to `Over.homMk u' hb`. Establish `e1 : U ≫ x = U' ≫ x'` using `Over.OverMorphism.ext hx`.

Establish `e2 : U ≫ y = U' ≫ y'` using `Over.OverMorphism.ext hy`. Establish `: U ≫ (x * y) = U' ≫ (x' * y')` using `by rw [MonObj.comp_mul, MonObj.comp_mul, e1, e2]`. Conclude with `congrArg (fun k => k.left) this`.
-/
theorem mul_left_congr {T T' : Over S} (x y : T ⟶ G) (x' y' : T' ⟶ G) (u : Z ⟶ T.left) (u' : Z ⟶ T'.left)
    (hx : u ≫ x.left = u' ≫ x'.left) (hy : u ≫ y.left = u' ≫ y'.left) :
    u ≫ (x * y).left = u' ≫ (x' * y').left := by
  have hb : u' ≫ T'.hom = u ≫ T.hom := by
    rw [← Over.w x, ← Over.w x', ← Category.assoc, ← hx, Category.assoc]
  let U : Over.mk (u ≫ T.hom) ⟶ T := Over.homMk u rfl
  let U' : Over.mk (u ≫ T.hom) ⟶ T' := Over.homMk u' hb
  have e1 : U ≫ x = U' ≫ x' := Over.OverMorphism.ext hx
  have e2 : U ≫ y = U' ≫ y' := Over.OverMorphism.ext hy
  have : U ≫ (x * y) = U' ≫ (x' * y') := by rw [MonObj.comp_mul, MonObj.comp_mul, e1, e2]
  exact congrArg (fun k => k.left) this

end Grp

/- English proof (translation)
Establish `hw : ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = (Over.mk (T.hom ≫ f)).hom`. Rewrite using `[Category.assoc, h.1.w, ← Category.assoc, Over.w]`. Both sides reduce to the same expression. Set `x₀ : Over.mk (T.hom ≫ f) ⟶ G` to `Over.homMk ((1 : T ⟶ G').left ≫ φ) hw`. Establish `hm` using `h.2 T 1 1 x₀ x₀ rfl rfl`.

Rewrite `hm` using `[_root_.mul_one]`. Establish `hx : x₀ * x₀ = x₀` using `Over.OverMorphism.ext hm`. Establish `h1 : x₀ = 1` using `by simpa using hx`. Establish `: x₀.left = (Over.mk (T.hom ≫ f)).hom ≫ η[G].left` using `by rw [h1, one_left']`. Conclude with `this`.
-/
theorem pull_one_left {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = (T.hom ≫ f) ≫ η[G].left := by
  have hw : ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = (Over.mk (T.hom ≫ f)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]; rfl
  let x₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) hw
  have hm := h.2 T 1 1 x₀ x₀ rfl rfl
  rw [_root_.mul_one] at hm
  have hx : x₀ * x₀ = x₀ := Over.OverMorphism.ext hm
  have h1 : x₀ = 1 := by simpa using hx
  have : x₀.left = (Over.mk (T.hom ≫ f)).hom ≫ η[G].left := by rw [h1, one_left']
  exact this

end GlobalTheory.TorLie

open GlobalTheory.TorLie in
/- English proof (translation)
Introduce `S G _ _ O _ act hhom h1 hmul hadd k _ x E`. Use `letI := E.addCommGroup`. Use `haveI := E.i_hom`. Use `set Gx := (Over.pullback x).obj G with hGx`. Establish `hGP` using `isGrpPullback_pullback G x`.

Take `⟨act', ⟨hhom', h1', hmul', hadd'⟩, hact'⟩` from `GlobalTheory.T.exists_ring_action_pullback_cartesian_group_schemes S (Sp k) x G Gx (pullback.fst G.hom x) hGP O act hhom h1 hmul hadd`. Take `⟨ρ, hρ⟩` from `GlobalTheory.T.ringHom_characterEnd_of_torusExtension_action k Gx E O act' hhom' h1' hmul' hadd'`. Take `⟨U₀, hinj, hone, hU₀mul, hscale, hequi⟩` from `GlobalTheory.T.splitTorus_tangentVectors_addMonoidHom k E.X`. Establish `heq : ∀ l, ((U₀ l ≫ E.i).left ≫ pullback.fst G.hom x) ≫ G.hom = (epsPt (𝟙 (Sp k))).hom ≫ x`. Introduce `l`.

Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc]`. Conclude with `congrArg (· ≫ x) (Over.w (U₀ l ≫ E.i))`. Establish `hw : ∀ l, ((U₀ l ≫ E.i).left ≫ pullback.fst G.hom x) ≫ G.hom = (epsPt x).hom`. Introduce `l`. Rewrite using `[heq l]`.

Simplify using `[epsPt]`. Set `U : (E.X →+ k) → (epsPt x ⟶ G)` to `fun l => Over.homMk _ (hw l)`. Establish `hUl : ∀ l, (U l).left = (U₀ l).left ≫ E.i.left ≫ pullback.fst G.hom x`. Introduce `l`. Simplify using `[U]`.

Use `haveI : Mono E.i := E.isKernel.mono_fst_of_mono (IsTerminal.mono_from isTerminalTensorUnit _)`. Use `⟨ρ, U, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `l l' h`. Establish `hl` using `congrArg Over.Hom.left h`. Rewrite `hl` using `[hUl, hUl, ← Category.assoc, ← Category.assoc]`.

Establish `h2 : (U₀ l ≫ E.i).left = (U₀ l' ≫ E.i).left`. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify `hl` using `[Over.comp_left]`. Conclude with `(Over.w (U₀ l ≫ E.i)).trans (Over.w (U₀ l' ≫ E.i)).symm`. Conclude with `hinj ((cancel_mono E.i).1 (Over.OverMorphism.ext h2))`.

Introduce `l`. Rewrite using `[hUl, ← Category.assoc, hone l, ← Category.assoc, ← Over.comp_left, MonObj.one_comp, pull_one_left hGP, one_left']`. Simplify using the standard rewrite rules. Introduce `l l'`. Set `x₀ : Over.mk ((epsPt (𝟙 (Sp k))).hom ≫ x) ⟶ G` to `Over.homMk _ (heq l)`.

Set `y₀ : Over.mk ((epsPt (𝟙 (Sp k))).hom ≫ x) ⟶ G` to `Over.homMk _ (heq l')`. Establish `key` using `hGP.2 (epsPt (𝟙 (Sp k))) (U₀ l ≫ E.i) (U₀ l' ≫ E.i) x₀ y₀ rfl rfl`. Rewrite `key` using `[← mul_comp, ← hU₀mul]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Establish `hc` using `mul_left_congr (U l) (U l') x₀ y₀ (𝟙 _) (𝟙 _) rfl rfl`.

Simplify using `only [Category.id_comp] at hc`. Rewrite using `[hc, key, hUl, Over.comp_left, Category.assoc]`. Introduce `t l`. Rewrite using `[hUl, hUl, hscale]`. Simplify using `[Category.assoc]`.

Introduce `a l`. Take `⟨τ, hτ, hχ⟩` from `hρ a`. Establish `hτl : τ.left ≫ E.i.left = E.i.left ≫ (act' a).left`. Simplify using `using congrArg Over.Hom.left hτ`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Establish `hτU : U₀ l ≫ τ = U₀ (l.comp (ρ a).toAddMonoidHom)` using `hequi τ (ρ a).toAddMonoidHom (fun χ => hχ χ) l`. Rewrite using `[Over.comp_left, hUl, hUl, ← hτU, Over.comp_left]`. Simplify using `only [Category.assoc, ← hact' a, reassoc_of% hτl]`.
-/
theorem GlobalTheory.torus_part_lie : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (O : Type) [Ring O] (act : O → (G ⟶ G)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S) (E : TorusExtension ((Over.pullback x).obj G)), letI := E.addCommGroup; ∃ (ρ : O →+* Module.End ℤ E.X) (U : (E.X →+ k) → (epsPt x ⟶ G)), Function.Injective U ∧ (∀ l, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (U l).left = (1 : Over.mk x ⟶ G).left) ∧ (∀ l l', U (l + l') = U l * U l') ∧ (∀ (t : k) l, (U ((AddMonoidHom.mulLeft t).comp l)).left = spMap (epsScale t) ≫ (U l).left) ∧ ∀ a l, U l ≫ act a = U (l.comp (ρ a).toAddMonoidHom) := by
  intro S G _ _ O _ act hhom h1 hmul hadd k _ x E
  letI := E.addCommGroup
  haveI := E.i_hom
  set Gx := (Over.pullback x).obj G with hGx
  have hGP := isGrpPullback_pullback G x
  obtain ⟨act', ⟨hhom', h1', hmul', hadd'⟩, hact'⟩ :=
    GlobalTheory.T.exists_ring_action_pullback_cartesian_group_schemes S (Sp k) x G Gx (pullback.fst G.hom x) hGP O act hhom h1 hmul hadd
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.ringHom_characterEnd_of_torusExtension_action k Gx E O act' hhom' h1' hmul' hadd'
  obtain ⟨U₀, hinj, hone, hU₀mul, hscale, hequi⟩ := GlobalTheory.T.splitTorus_tangentVectors_addMonoidHom k E.X

  have heq : ∀ l, ((U₀ l ≫ E.i).left ≫ pullback.fst G.hom x) ≫ G.hom = (epsPt (𝟙 (Sp k))).hom ≫ x := by
    intro l
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ x) (Over.w (U₀ l ≫ E.i))
  have hw : ∀ l, ((U₀ l ≫ E.i).left ≫ pullback.fst G.hom x) ≫ G.hom = (epsPt x).hom := by
    intro l; rw [heq l]; simp [epsPt]
  let U : (E.X →+ k) → (epsPt x ⟶ G) := fun l => Over.homMk _ (hw l)
  have hUl : ∀ l, (U l).left = (U₀ l).left ≫ E.i.left ≫ pullback.fst G.hom x := by
    intro l; simp [U]
  haveI : Mono E.i := E.isKernel.mono_fst_of_mono (IsTerminal.mono_from isTerminalTensorUnit _)
  refine ⟨ρ, U, ?_, ?_, ?_, ?_, ?_⟩
  · intro l l' h
    have hl := congrArg Over.Hom.left h
    rw [hUl, hUl, ← Category.assoc, ← Category.assoc] at hl
    have h2 : (U₀ l ≫ E.i).left = (U₀ l' ≫ E.i).left := by
      apply pullback.hom_ext
      · simpa [Over.comp_left] using hl
      · exact (Over.w (U₀ l ≫ E.i)).trans (Over.w (U₀ l' ≫ E.i)).symm
    exact hinj ((cancel_mono E.i).1 (Over.OverMorphism.ext h2))
  · intro l
    rw [hUl, ← Category.assoc, hone l, ← Category.assoc, ← Over.comp_left, MonObj.one_comp,
      pull_one_left hGP, one_left']
    simp
  · intro l l'
    let x₀ : Over.mk ((epsPt (𝟙 (Sp k))).hom ≫ x) ⟶ G := Over.homMk _ (heq l)
    let y₀ : Over.mk ((epsPt (𝟙 (Sp k))).hom ≫ x) ⟶ G := Over.homMk _ (heq l')
    have key := hGP.2 (epsPt (𝟙 (Sp k))) (U₀ l ≫ E.i) (U₀ l' ≫ E.i) x₀ y₀ rfl rfl
    rw [← mul_comp, ← hU₀mul] at key
    apply Over.OverMorphism.ext
    have hc := mul_left_congr (U l) (U l') x₀ y₀ (𝟙 _) (𝟙 _) rfl rfl
    simp only [Category.id_comp] at hc
    rw [hc, key, hUl, Over.comp_left, Category.assoc]
  · intro t l
    rw [hUl, hUl, hscale]
    simp [Category.assoc]
  · intro a l
    obtain ⟨τ, hτ, hχ⟩ := hρ a
    have hτl : τ.left ≫ E.i.left = E.i.left ≫ (act' a).left := by
      simpa using congrArg Over.Hom.left hτ
    apply Over.OverMorphism.ext
    have hτU : U₀ l ≫ τ = U₀ (l.comp (ρ a).toAddMonoidHom) := hequi τ (ρ a).toAddMonoidHom (fun χ => hχ χ) l
    rw [Over.comp_left, hUl, hUl, ← hτU, Over.comp_left]
    simp only [Category.assoc, ← hact' a, reassoc_of% hτl]
