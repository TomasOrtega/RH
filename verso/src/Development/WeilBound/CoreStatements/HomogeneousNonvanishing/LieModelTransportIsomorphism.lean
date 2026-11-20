import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.MvSecValComp
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeilPairingPullbackIffStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

open PositivityTheory.UnitarySelfGeneration.Isomove

namespace Isomove

variable {X X' : Scheme.{0}} {G : Over X} {G' : Over X'} [GrpObj G] [GrpObj G'] {f : X' ⟶ X} {φ : G'.left ⟶ G.left}
  {g : X ⟶ X'} {ψ : G.left ⟶ G'.left} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω ⟶ X'}
  {V : Type} [AddCommGroup V] [Module Ω V]

/- English proof (translation)
Take `⟨v1, hv1, ht1⟩` from `mv_bc (G := G) σ (x := X.fromSpecStalk q.1) (x' := X'.fromSpecStalk q'.1 ≫ f) h1 v`. Establish `hw : (v1.left ≫ ψ) ≫ G'.hom = (epsAt (X'.fromSpecStalk q'.1)).hom`. Rewrite using `[Category.assoc, hψ.1.w, ← Category.assoc, Over.w v1]`. Simplify using `[epsAt, fg]`. Both sides reduce to the same expression.

Set `v' : epsAt (X'.fromSpecStalk q'.1) ⟶ G'` to `Over.homMk (v1.left ≫ ψ) hw`. Establish `hgx : (X'.fromSpecStalk q'.1 ≫ f) ≫ g = X'.fromSpecStalk q'.1`. Rewrite using `[Category.assoc, fg, Category.comp_id]`. Establish `key : spMap (dualMap (genMap ξ q)) = spMap (dualMap (genMap ξ' q')) ≫ spMap (dualMap σ)`. Rewrite using `[mv_dual_comp, h2]`.

Use `⟨v', ⟨mv_tan hψ hgx (v' := v1) (v := v') rfl (ht1 hv.1), ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hM e, hv.2] show spMap (dualMap (genMap ξ q)) ≫ v.left ≫ ψ = spMap (dualMap (genMap ξ' q')) ≫ v1.left ≫ ψ`. Rewrite using `[key, hv1]`. Simplify using `only [Category.assoc]`. Use `show v1.left ≫ ψ = _`.

Rewrite using `[hv1, Category.assoc]`.
-/
theorem extends_pull (hψ : IsGrpPullback G G' g ψ) (fg : f ≫ g = 𝟙 _) (hξ : ξ' ≫ f = ξ)
    {M : LieModel G ξ V} {M' : LieModel G' ξ' V} (hM : ∀ e, (M.pt e).left ≫ ψ = (M'.pt e).left)
    (q' : Cpt ξ') (q : Cpt ξ) (σ : X.presheaf.stalk q.1 →+* X'.presheaf.stalk q'.1)
    (h1 : spMap σ ≫ X.fromSpecStalk q.1 = X'.fromSpecStalk q'.1 ≫ f) (h2 : (genMap ξ' q').comp σ = genMap ξ q)
    (e : V) (v) (hv : M.Extends q e v) :
    ∃ v', M'.Extends q' e v' ∧ v'.left = spMap (dualMap σ) ≫ v.left ≫ ψ := by
  obtain ⟨v1, hv1, ht1⟩ := mv_bc (G := G) σ (x := X.fromSpecStalk q.1) (x' := X'.fromSpecStalk q'.1 ≫ f) h1 v
  have hw : (v1.left ≫ ψ) ≫ G'.hom = (epsAt (X'.fromSpecStalk q'.1)).hom := by
    rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w v1]
    simp [epsAt, fg]
    rfl
  let v' : epsAt (X'.fromSpecStalk q'.1) ⟶ G' := Over.homMk (v1.left ≫ ψ) hw
  have hgx : (X'.fromSpecStalk q'.1 ≫ f) ≫ g = X'.fromSpecStalk q'.1 := by
    rw [Category.assoc, fg, Category.comp_id]
  have key : spMap (dualMap (genMap ξ q)) = spMap (dualMap (genMap ξ' q')) ≫ spMap (dualMap σ) := by
    rw [mv_dual_comp, h2]
  refine ⟨v', ⟨mv_tan hψ hgx (v' := v1) (v := v') rfl (ht1 hv.1), ?_⟩, ?_⟩
  · rw [← hM e, hv.2]
    show spMap (dualMap (genMap ξ q)) ≫ v.left ≫ ψ = spMap (dualMap (genMap ξ' q')) ≫ v1.left ≫ ψ
    rw [key, hv1]
    simp only [Category.assoc]
  · show v1.left ≫ ψ = _
    rw [hv1, Category.assoc]

/- English proof (translation)
Take `⟨σ, h1, h2, -⟩` from `mv_stalk hξ q' q hq`. Proceed by induction on `he using Submodule.span_induction with`. Consider the case `mem e he`. Take `⟨v, hv⟩` from `he`. Take `⟨v', hv', -⟩` from `extends_pull hψ fg hξ hM q' q σ h1 h2 e v hv`.

Conclude with `Submodule.subset_span ⟨v', hv'⟩`. Consider the case `zero => exact zero_mem _`. Consider the case `add a b _ _ ha hb => exact add_mem ha hb`. Consider the case `smul c a _ ha => exact (M'.lat q').smul_mem ⟨c, mv_regAt_le hξ q' q hq c.2⟩ ha`.
-/
theorem lat_le (hψ : IsGrpPullback G G' g ψ) (fg : f ≫ g = 𝟙 _) (hξ : ξ' ≫ f = ξ)
    {M : LieModel G ξ V} {M' : LieModel G' ξ' V} (hM : ∀ e, (M.pt e).left ≫ ψ = (M'.pt e).left)
    (q' : Cpt ξ') (q : Cpt ξ) (hq : f q'.1 = q.1) (e : V) (he : e ∈ M.lat q) : e ∈ M'.lat q' := by
  obtain ⟨σ, h1, h2, -⟩ := mv_stalk hξ q' q hq
  induction he using Submodule.span_induction with
  | mem e he =>
    obtain ⟨v, hv⟩ := he
    obtain ⟨v', hv', -⟩ := extends_pull hψ fg hξ hM q' q σ h1 h2 e v hv
    exact Submodule.subset_span ⟨v', hv'⟩
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul c a _ ha => exact (M'.lat q').smul_mem ⟨c, mv_regAt_le hξ q' q hq c.2⟩ ha

/- English proof (translation)
Establish `hgq : g q.1 = q'.1`. Rewrite using `[← hq, ← Scheme.Hom.comp_apply, fg]`. Both sides reduce to the same expression. Establish `hξg : ξ ≫ g = ξ'` using `by rw [← hξ, Category.assoc, fg, Category.comp_id]`. Establish `hreg : regAt ξ' q' ≤ regAt ξ q` using `mv_regAt_le (f := g) hξg q q' hgq`.

Establish `hx' : x'.left = x.left ≫ ψ` using `by rw [← hx, Category.assoc, φψ, Category.comp_id]`. Take `⟨hw0, W', s', hηW', htor', hext'⟩` from `hw`. Use `⟨?_, ψ ⁻¹ᵁ W', ψ.app W' s', ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `e he`. Conclude with `hreg (hw0 e (lat_le hψ fg hξ hM q' q hq e he))`.

Rewrite using `[Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, mv_eta hψ, Scheme.Hom.comp_apply, hgq]`. Conclude with `hηW'`. Introduce `k _ _ i xk g0 c h hxk hpow hweil`. Establish `hz : (spMap i ≫ ξ) ≫ g = spMap i ≫ ξ'` using `by rw [Category.assoc, hξg]`. Establish `hz' : (spMap i ≫ ξ') ≫ f = spMap i ≫ ξ` using `by rw [Category.assoc, hξ]`.

Establish `comm : ∀ a : Over.mk (spMap i ≫ ξ) ⟶ G, (a.left ≫ ψ) ≫ G'.hom = (Over.mk (spMap i ≫ ξ')).hom`. Introduce `a`. Rewrite using `[Category.assoc, hψ.1.w, ← Category.assoc, Over.w a]`. Simplify using `using hz`. Set `xk' : Over.mk (spMap i ≫ ξ') ⟶ G'` to `Over.homMk (xk.left ≫ ψ) (comm xk)`.

Set `g0' : Over.mk (spMap i ≫ ξ') ⟶ G'` to `Over.homMk (g0.left ≫ ψ) (comm g0)`. Establish `hback : ∀ a : Over.mk (spMap i ≫ ξ) ⟶ G, (a.left ≫ ψ) ≫ φ = a.left`. Introduce `a`. Rewrite using `[Category.assoc, ψφ, Category.comp_id]`. Establish `hweil'` using `hW k (spMap i ≫ ξ') (spMap i ≫ ξ) hz' xk' g0' xk g0 c (hback xk) (hback g0) hweil`.

Establish `hxk' : xk'.left = spMap i ≫ x'.left` using `by show xk.left ≫ ψ = _`. Rewrite using `[hx', hxk, Category.assoc]`. Establish `hpow' : g0' ^ n = 1` using `mv_pow hψ hz (a' := g0) (a := g0') rfl hpow`. Establish `h' : ⊤ ≤ g0'.left ⁻¹ᵁ W'` using `by show ⊤ ≤ (g0.left ≫ ψ) ⁻¹ᵁ W'`. Rewrite using `[Scheme.Hom.comp_preimage]`.

Conclude with `h`. Rewrite using `[← htor' k i xk' g0' c h' hxk' hpow' hweil']`. Conclude with `mv_secVal_comp g0.left ψ g0'.left rfl W' s' h h'`. Introduce `e v hv h`. Take `⟨σ, h1, h2, -⟩` from `mv_stalk hξ q' q hq`.

Take `⟨v', hv', hvl⟩` from `extends_pull hψ fg hξ hM q' q σ h1 h2 e v hv`. Establish `hh : ⊤ ≤ (spMap (dualMap σ) ≫ v.left) ⁻¹ᵁ (ψ ⁻¹ᵁ W')` using `fun p _ => h trivial`. Establish `h' : ⊤ ≤ v'.left ⁻¹ᵁ W'`. Rewrite using `[hvl]`. Conclude with `fun p _ => hh trivial`.

Take `⟨r, hr, hwe⟩` from `hext' e v' hv' h'`. Use `⟨r, hreg hr, ?_⟩` and prove the remaining obligations. Rewrite using `[hwe]`. Use `congr 1`. Establish `hcomp : (spMap (dualMap σ) ≫ v.left) ≫ ψ = v'.left`.

Rewrite using `[hvl]`. Conclude with `Category.assoc _ _ _`. Establish `e1` using `mv_secVal_comp (spMap (dualMap σ) ≫ v.left) ψ v'.left hcomp W' s' hh h'`. Establish `e2` using `mv_secVal_bc (dualMap σ) v.left (spMap (dualMap σ) ≫ v.left) rfl (ψ ⁻¹ᵁ W') (ψ.app W' s') h hh`. Establish `hs : secVal v'.left W' h' s' = dualMap σ (secVal v.left (ψ ⁻¹ᵁ W') h (ψ.app W' s'))` using `e1.symm.trans e2`.

Rewrite using `[hs, ← h2]`. Simplify using `[dualMap]`.
-/
theorem htAt_push (hψ : IsGrpPullback G G' g ψ) (fg : f ≫ g = 𝟙 _) (gf : g ≫ f = 𝟙 _)
    (φψ : φ ≫ ψ = 𝟙 _) (ψφ : ψ ≫ φ = 𝟙 _) (hξ : ξ' ≫ f = ξ)
    {M : LieModel G ξ V} {M' : LieModel G' ξ' V} (hM : ∀ e, (M.pt e).left ≫ ψ = (M'.pt e).left)
    {L : LB G.left} {L' : LB G'.left} {n : ℕ}
    (hW : ∀ (k : Type) [Field k] (z' : Sp k ⟶ X') (z : Sp k ⟶ X), z' ≫ f = z →
      ∀ (a' b' : Over.mk z' ⟶ G') (a b : Over.mk z ⟶ G) (c : kˣ), a'.left ≫ φ = a.left → b'.left ≫ φ = b.left →
      Out.WeilIs G L n a b (unitOn c) → Out.WeilIs G' L' n a' b' (unitOn c))
    (q' : Cpt ξ') (q : Cpt ξ) (hq : f q'.1 = q.1) (x' : Over.mk ξ' ⟶ G') (x : Over.mk ξ ⟶ G)
    (hx : x'.left ≫ φ = x.left) (w : Module.Dual Ω V) (hw : M'.IsHTAt L' n x' q' w) : M.IsHTAt L n x q w := by
  have hgq : g q.1 = q'.1 := by
    rw [← hq, ← Scheme.Hom.comp_apply, fg]
    rfl
  have hξg : ξ ≫ g = ξ' := by rw [← hξ, Category.assoc, fg, Category.comp_id]
  have hreg : regAt ξ' q' ≤ regAt ξ q := mv_regAt_le (f := g) hξg q q' hgq
  have hx' : x'.left = x.left ≫ ψ := by rw [← hx, Category.assoc, φψ, Category.comp_id]
  obtain ⟨hw0, W', s', hηW', htor', hext'⟩ := hw
  refine ⟨?_, ψ ⁻¹ᵁ W', ψ.app W' s', ?_, ?_, ?_⟩
  · intro e he
    exact hreg (hw0 e (lat_le hψ fg hξ hM q' q hq e he))
  · rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, mv_eta hψ, Scheme.Hom.comp_apply, hgq]
    exact hηW'
  · intro k _ _ i xk g0 c h hxk hpow hweil
    have hz : (spMap i ≫ ξ) ≫ g = spMap i ≫ ξ' := by rw [Category.assoc, hξg]
    have hz' : (spMap i ≫ ξ') ≫ f = spMap i ≫ ξ := by rw [Category.assoc, hξ]
    have comm : ∀ a : Over.mk (spMap i ≫ ξ) ⟶ G, (a.left ≫ ψ) ≫ G'.hom = (Over.mk (spMap i ≫ ξ')).hom := by
      intro a
      rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w a]
      simpa using hz
    let xk' : Over.mk (spMap i ≫ ξ') ⟶ G' := Over.homMk (xk.left ≫ ψ) (comm xk)
    let g0' : Over.mk (spMap i ≫ ξ') ⟶ G' := Over.homMk (g0.left ≫ ψ) (comm g0)
    have hback : ∀ a : Over.mk (spMap i ≫ ξ) ⟶ G, (a.left ≫ ψ) ≫ φ = a.left := by
      intro a
      rw [Category.assoc, ψφ, Category.comp_id]
    have hweil' := hW k (spMap i ≫ ξ') (spMap i ≫ ξ) hz' xk' g0' xk g0 c (hback xk) (hback g0) hweil
    have hxk' : xk'.left = spMap i ≫ x'.left := by
      show xk.left ≫ ψ = _
      rw [hx', hxk, Category.assoc]
    have hpow' : g0' ^ n = 1 := mv_pow hψ hz (a' := g0) (a := g0') rfl hpow
    have h' : ⊤ ≤ g0'.left ⁻¹ᵁ W' := by
      show ⊤ ≤ (g0.left ≫ ψ) ⁻¹ᵁ W'
      rw [Scheme.Hom.comp_preimage]
      exact h
    rw [← htor' k i xk' g0' c h' hxk' hpow' hweil']
    exact mv_secVal_comp g0.left ψ g0'.left rfl W' s' h h'
  · intro e v hv h
    obtain ⟨σ, h1, h2, -⟩ := mv_stalk hξ q' q hq
    obtain ⟨v', hv', hvl⟩ := extends_pull hψ fg hξ hM q' q σ h1 h2 e v hv
    have hh : ⊤ ≤ (spMap (dualMap σ) ≫ v.left) ⁻¹ᵁ (ψ ⁻¹ᵁ W') := fun p _ => h trivial
    have h' : ⊤ ≤ v'.left ⁻¹ᵁ W' := by
      rw [hvl]
      exact fun p _ => hh trivial
    obtain ⟨r, hr, hwe⟩ := hext' e v' hv' h'
    refine ⟨r, hreg hr, ?_⟩
    rw [hwe]
    congr 1
    have hcomp : (spMap (dualMap σ) ≫ v.left) ≫ ψ = v'.left := by
      rw [hvl]
      exact Category.assoc _ _ _
    have e1 := mv_secVal_comp (spMap (dualMap σ) ≫ v.left) ψ v'.left hcomp W' s' hh h'
    have e2 := mv_secVal_bc (dualMap σ) v.left (spMap (dualMap σ) ≫ v.left) rfl (ψ ⁻¹ᵁ W') (ψ.app W' s') h hh
    have hs : secVal v'.left W' h' s' = dualMap σ (secVal v.left (ψ ⁻¹ᵁ W') h (ψ.app W' s')) := e1.symm.trans e2
    rw [hs, ← h2]
    simp [dualMap]

/- English proof (translation)
Establish `hξ' : ξ ≫ g = ξ'` using `by rw [← hξ, Category.assoc, fg, Category.comp_id]`. Establish `hq' : g q.1 = q'.1` using `by rw [← hq, ← Scheme.Hom.comp_apply, fg]; rfl`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem w hw`. Take `⟨x', hx', hw⟩` from `hw`.

Take `⟨x, hx⟩` from `mv_push hφ.1.w hξ x'`. Conclude with `Submodule.subset_span ⟨x, mv_pow hφ hξ hx hx', htAt_push hψ fg gf φψ ψφ hξ hM hW q' q hq x' x hx w hw⟩`. Consider the case `zero => exact zero_mem _`. Consider the case `add a b _ _ ha hb => exact add_mem ha hb`. Consider the case `smul c a _ ha => exact (M.htOm L n q).smul_mem ⟨c, mv_regAt_le hξ' q q' hq' c.2⟩ ha`.
-/
theorem htOm_le (hφ : IsGrpPullback G' G f φ) (hψ : IsGrpPullback G G' g ψ) (fg : f ≫ g = 𝟙 _) (gf : g ≫ f = 𝟙 _)
    (φψ : φ ≫ ψ = 𝟙 _) (ψφ : ψ ≫ φ = 𝟙 _) (hξ : ξ' ≫ f = ξ)
    {M : LieModel G ξ V} {M' : LieModel G' ξ' V} (hM : ∀ e, (M.pt e).left ≫ ψ = (M'.pt e).left)
    {L : LB G.left} {L' : LB G'.left} {n : ℕ}
    (hW : ∀ (k : Type) [Field k] (z' : Sp k ⟶ X') (z : Sp k ⟶ X), z' ≫ f = z →
      ∀ (a' b' : Over.mk z' ⟶ G') (a b : Over.mk z ⟶ G) (c : kˣ), a'.left ≫ φ = a.left → b'.left ≫ φ = b.left →
      Out.WeilIs G L n a b (unitOn c) → Out.WeilIs G' L' n a' b' (unitOn c))
    (q' : Cpt ξ') (q : Cpt ξ) (hq : f q'.1 = q.1) (w : Module.Dual Ω V) (hw : w ∈ M'.htOm L' n q') :
    w ∈ M.htOm L n q := by
  have hξ' : ξ ≫ g = ξ' := by rw [← hξ, Category.assoc, fg, Category.comp_id]
  have hq' : g q.1 = q'.1 := by rw [← hq, ← Scheme.Hom.comp_apply, fg]; rfl
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x', hx', hw⟩ := hw
    obtain ⟨x, hx⟩ := mv_push hφ.1.w hξ x'
    exact Submodule.subset_span ⟨x, mv_pow hφ hξ hx hx',
      htAt_push hψ fg gf φψ ψφ hξ hM hW q' q hq x' x hx w hw⟩
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul c a _ ha => exact (M.htOm L n q).smul_mem ⟨c, mv_regAt_le hξ' q q' hq' c.2⟩ ha

/- English proof (translation)
Establish `hξg : ξ ≫ g = ξ'` using `by rw [← hξ, Category.assoc, fg, Category.comp_id]`. Establish `hy : (Spec.map (CommRingCat.ofHom (algebraMap Ω (DualNumber Ω))) ≫ ξ) ≫ g = Spec.map (CommRingCat.ofHom (algebraMap Ω (DualNumber Ω))) ≫ ξ'`. Rewrite using `[Category.assoc, hξg]`. Establish `hc : ∀ a : epsAt ξ ⟶ G, (a.left ≫ ψ) ≫ G'.hom = (epsAt ξ').hom`. Introduce `a`.

Rewrite using `[Category.assoc, hψ.1.w, ← Category.assoc, Over.w a]`. Simplify using `using hy`. Set `P : V → (epsAt ξ' ⟶ G')` to `fun e => Over.homMk ((M.pt e).left ≫ ψ) (hc (M.pt e))`. Use `⟨{ pt := P, tan := ?_, inj := ?_, onto := ?_, add := ?_, smul := ?_ }, fun e => rfl⟩` and prove the remaining obligations. Introduce `e`.

Conclude with `mv_tan hψ hξg (v' := M.pt e) (v := P e) rfl (M.tan e)`. Introduce `e e' h`. Apply `M.inj` to reduce the goal to its premises. Establish `h1 : (M.pt e).left ≫ ψ = (M.pt e').left ≫ ψ` using `congrArg (fun a => Over.Hom.left a) h`. Conclude with `Over.OverMorphism.ext ((cancel_mono ψ).1 h1)`.

Introduce `v hv`. Establish `hφc : (v.left ≫ φ) ≫ G.hom = (epsAt ξ).hom`. Rewrite using `[Category.assoc, hφ.1.w, ← Category.assoc, Over.w v]`. Simplify using `[hξ]`. Set `u : epsAt ξ ⟶ G` to `Over.homMk (v.left ≫ φ) hφc`.

Take `⟨e, he⟩` from `M.onto u (mv_tan hφ hξ (v' := v) (v := u) rfl hv)`. Use `⟨e, Over.OverMorphism.ext ?_⟩` and prove the remaining obligations. Use `show (M.pt e).left ≫ ψ = v.left`. Rewrite using `[he]`. Use `show (v.left ≫ φ) ≫ ψ = v.left`.

Rewrite using `[Category.assoc, φψ, Category.comp_id]`. Introduce `e e'`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `show (M.pt (e + e')).left ≫ ψ = _`. Rewrite using `[M.add]`.

Conclude with `mv_mul hψ hy (a' := M.pt e) (b' := M.pt e') (a := P e) (b := P e') rfl rfl`. Introduce `c e show (M.pt (c • e)).left ≫ ψ = _ ≫ (M.pt e).left ≫ ψ`. Rewrite using `[M.smul, Category.assoc]`.
-/
theorem model (hφ : IsGrpPullback G' G f φ) (hψ : IsGrpPullback G G' g ψ) (fg : f ≫ g = 𝟙 _)
    (φψ : φ ≫ ψ = 𝟙 _) (hξ : ξ' ≫ f = ξ) (M : LieModel G ξ V) [Mono ψ] :
    ∃ M' : LieModel G' ξ' V, ∀ e, (M.pt e).left ≫ ψ = (M'.pt e).left := by
  have hξg : ξ ≫ g = ξ' := by rw [← hξ, Category.assoc, fg, Category.comp_id]
  have hy : (Spec.map (CommRingCat.ofHom (algebraMap Ω (DualNumber Ω))) ≫ ξ) ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap Ω (DualNumber Ω))) ≫ ξ' := by
    rw [Category.assoc, hξg]
  have hc : ∀ a : epsAt ξ ⟶ G, (a.left ≫ ψ) ≫ G'.hom = (epsAt ξ').hom := by
    intro a
    rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w a]
    simpa using hy
  let P : V → (epsAt ξ' ⟶ G') := fun e => Over.homMk ((M.pt e).left ≫ ψ) (hc (M.pt e))
  refine ⟨{ pt := P, tan := ?_, inj := ?_, onto := ?_, add := ?_, smul := ?_ }, fun e => rfl⟩
  · intro e
    exact mv_tan hψ hξg (v' := M.pt e) (v := P e) rfl (M.tan e)
  · intro e e' h
    apply M.inj
    have h1 : (M.pt e).left ≫ ψ = (M.pt e').left ≫ ψ := congrArg (fun a => Over.Hom.left a) h
    exact Over.OverMorphism.ext ((cancel_mono ψ).1 h1)
  · intro v hv
    have hφc : (v.left ≫ φ) ≫ G.hom = (epsAt ξ).hom := by
      rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w v]
      simp [hξ]
    let u : epsAt ξ ⟶ G := Over.homMk (v.left ≫ φ) hφc
    obtain ⟨e, he⟩ := M.onto u (mv_tan hφ hξ (v' := v) (v := u) rfl hv)
    refine ⟨e, Over.OverMorphism.ext ?_⟩
    show (M.pt e).left ≫ ψ = v.left
    rw [he]
    show (v.left ≫ φ) ≫ ψ = v.left
    rw [Category.assoc, φψ, Category.comp_id]
  · intro e e'
    apply Over.OverMorphism.ext
    show (M.pt (e + e')).left ≫ ψ = _
    rw [M.add]
    exact mv_mul hψ hy (a' := M.pt e) (b' := M.pt e') (a := P e) (b := P e') rfl rfl
  · intro c e
    show (M.pt (c • e)).left ≫ ψ = _ ≫ (M.pt e).left ≫ ψ
    rw [M.smul, Category.assoc]

/- English proof (translation)
Use `⟨IsPullback.id_horiz G.hom, ?_⟩` and prove the remaining obligations. Introduce `T x y x₀ y₀ hx hy`. Establish `key : ∀ (t : T.left ⟶ X), t = T.hom → ∀ (a b : Over.mk t ⟶ G), a.left = x.left → b.left = y.left → (a * b).left = (x * y).left`. Introduce `t ht`. Substitute `ht` using the available equality.

Introduce `a b ha hb`. Establish `e1 : a = x` using `Over.OverMorphism.ext ha`. Establish `e2 : b = y` using `Over.OverMorphism.ext hb`. Rewrite using `[e1, e2]`. Conclude with `(key _ (Category.comp_id _) x₀ y₀ (hx.trans (Category.comp_id _)) (hy.trans (Category.comp_id _))).trans (Category.comp_id _).symm`.
-/
theorem grp_id (G : Over X) [GrpObj G] : IsGrpPullback G G (𝟙 X) (𝟙 G.left) := by
  refine ⟨IsPullback.id_horiz G.hom, ?_⟩
  intro T x y x₀ y₀ hx hy
  have key : ∀ (t : T.left ⟶ X), t = T.hom → ∀ (a b : Over.mk t ⟶ G),
      a.left = x.left → b.left = y.left → (a * b).left = (x * y).left := by
    intro t ht
    subst ht
    intro a b ha hb
    have e1 : a = x := Over.OverMorphism.ext ha
    have e2 : b = y := Over.OverMorphism.ext hb
    rw [e1, e2]
  exact (key _ (Category.comp_id _) x₀ y₀ (hx.trans (Category.comp_id _)) (hy.trans (Category.comp_id _))).trans
    (Category.comp_id _).symm

end Isomove

/- English proof (translation)
Introduce `E _ _ _ H X X' e Ω _ ξ ξ' t t' m V _ _ M hξ`. Establish `hφ : IsGrpPullback t'.G t.G e.hom m.φ` using `m.cart`. Use `haveI : IsIso m.φ := hφ.1.isIso_fst_of_isIso`. Establish `φψ : m.φ ≫ inv m.φ = 𝟙 _` using `IsIso.hom_inv_id _`. Establish `ψφ : inv m.φ ≫ m.φ = 𝟙 _` using `IsIso.inv_hom_id _`.

Establish `fg : e.hom ≫ e.inv = 𝟙 X'` using `e.hom_inv_id`. Establish `gf : e.inv ≫ e.hom = 𝟙 X` using `e.inv_hom_id`. Establish `hψw : inv m.φ ≫ t'.G.hom = t.G.hom ≫ e.inv`. Rewrite using `[← cancel_mono e.hom, Category.assoc, Category.assoc, ← hφ.1.w, gf, Category.comp_id, ← Category.assoc, ψφ, Category.id_comp]`. Establish `hψ : IsGrpPullback t.G t'.G e.inv (inv m.φ)`.

Use `IsGrpPullback.cancel hφ ?_ hψw` and prove the remaining obligations. Rewrite using `[gf, ψφ]`. Conclude with `Isomove.grp_id t.G`. Establish `hξ' : ξ ≫ e.inv = ξ'` using `by rw [← hξ, Category.assoc, fg, Category.comp_id]`. Take `⟨M', hM⟩` from `Isomove.model hφ hψ fg φψ hξ M`.

Establish `hM' : ∀ v, (M'.pt v).left ≫ m.φ = (M.pt v).left`. Introduce `v`. Rewrite using `[← hM v, Category.assoc, ψφ, Category.comp_id]`. Establish `hW1 : ∀ (n : ℕ) (k : Type) [Field k] (z' : Sp k ⟶ X') (z : Sp k ⟶ X), z' ≫ e.hom = z → ∀ (a' b' : Over.mk z' ⟶ t'.G) (a b : Over.mk z ⟶ t.G) (c : kˣ), a'.left ≫ m.φ = a.left → b'.left ≫ m.φ = b.left → Out.WeilIs t.G t.PP.L (n : ℤ) a b (unitOn c) → Out.WeilIs t'.G t'.PP.L (n : ℤ) …`. Introduce `n k _ z' z hz a' b' a b c ha hb hw`.

Substitute `hz` using the available equality. Conclude with `(GlobalTheory.T.weil_pairing_pullback_iff E H X X' t t' e.hom m k z' a' b' a b n c ha hb).mpr hw`. Establish `hW2 : ∀ (n : ℕ) (k : Type) [Field k] (z' : Sp k ⟶ X) (z : Sp k ⟶ X'), z' ≫ e.inv = z → ∀ (a' b' : Over.mk z' ⟶ t.G) (a b : Over.mk z ⟶ t'.G) (c : kˣ), a'.left ≫ inv m.φ = a.left → b'.left ≫ inv m.φ = b.left → Out.WeilIs t'.G t'.PP.L (n : ℤ) a b (unitOn c) → Out.WeilIs t.G t.PP.L …`. Introduce `n k _ z' z hz a' b' a b c ha hb hw`. Establish `hz2 : z' = z ≫ e.hom` using `by rw [← hz, Category.assoc, gf, Category.comp_id]`.

Substitute `hz2` using the available equality. Establish `ha' : a.left ≫ m.φ = a'.left` using `by rw [← ha, Category.assoc, ψφ, Category.comp_id]`. Establish `hb' : b.left ≫ m.φ = b'.left` using `by rw [← hb, Category.assoc, ψφ, Category.comp_id]`. Conclude with `(GlobalTheory.T.weil_pairing_pullback_iff E H X X' t t' e.hom m k z a b a' b' n c ha' hb').mp hw`. Use `⟨M', hM', ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `n hT k _ i g' hpow`. Establish `hy : (spMap i ≫ ξ') ≫ e.hom = spMap i ≫ ξ` using `by rw [Category.assoc, hξ]`. Take `⟨a, ha⟩` from `mv_push hφ.1.w hy g'`. Take `⟨x, hx⟩` from `hT k i a (mv_pow hφ hy ha hpow)`. Take `⟨x', hx'⟩` from `mv_push hψw hξ' x`.

Use `⟨x', ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Introduce `hc`. Establish `hsp : ∀ p : Cpt ξ', genPt ξ ⤳ e.hom p.1`. Introduce `p`.

Establish `h0 : genPt ξ = e.hom (genPt ξ')` using `by show ξ _ = e.hom (ξ' _)`. Rewrite using `[← hξ]`. Conclude with `Scheme.Hom.comp_apply _ _ _`. Rewrite using `[h0]`. Conclude with `p.2.map e.hom.continuous`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `key : ∀ ζ : Sp Ω ⟶ X, ξ' ≫ e.hom = ζ → Function.Bijective (Scheme.stalkClosedPointTo ζ).hom → Function.Bijective (Scheme.stalkClosedPointTo ξ').hom`. Introduce `ζ hζ hb`. Substitute `hζ` using the available equality. Rewrite `hb` using `[Scheme.stalkClosedPointTo_comp]`.

Express the relevant statement in the definitionally equal form `Function.Bijective ((Scheme.stalkClosedPointTo ξ').hom ∘ (e.hom.stalkMap _).hom) at hb`. Conclude with `(Function.Bijective.of_comp_iff _ (ConcreteCategory.bijective_of_isIso (e.hom.stalkMap _))).mp hb`. Conclude with `key ξ hξ hc.bij`. Introduce `p a b hab`. Take `⟨σ, -, h2, hbij⟩` from `mv_stalk hξ p ⟨e.hom p.1, hsp p⟩ rfl`.

Take `⟨a0, rfl⟩` from `(hbij inferInstance).2 a`. Take `⟨b0, rfl⟩` from `(hbij inferInstance).2 b`. Establish `hab' : genMap ξ ⟨e.hom p.1, hsp p⟩ a0 = genMap ξ ⟨e.hom p.1, hsp p⟩ b0`. Rewrite using `[← h2]`. Conclude with `hab`.

Rewrite using `[hc.inj _ hab']`. Introduce `q h`. Establish `hq2 : e.inv (e.hom q.1) = q.1`. Rewrite using `[← Scheme.Hom.comp_apply, e.hom_inv_id]`. Both sides reduce to the same expression.

Use `⟨le_antisymm (mv_regAt_le (f := e.inv) hξ' ⟨e.hom q.1, h⟩ q hq2) (mv_regAt_le hξ q ⟨e.hom q.1, h⟩ rfl), ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce `hv`. Conclude with `Isomove.lat_le hφ gf hξ' hM' ⟨e.hom q.1, h⟩ q hq2 v hv`.

Introduce `hv`. Conclude with `Isomove.lat_le hψ fg hξ hM q ⟨e.hom q.1, h⟩ rfl v hv`. Introduce `n`. Use extensionality with `w`. Prove the components needed by the constructor for the conclusion.

Introduce `hw`. Conclude with `Isomove.htOm_le hφ hψ fg gf φψ ψφ hξ hM (hW1 n) q ⟨e.hom q.1, h⟩ rfl w hw`. Introduce `hw`. Conclude with `Isomove.htOm_le hψ hφ gf fg ψφ φψ hξ' hM' (hW2 n) ⟨e.hom q.1, h⟩ q hq2 w hw`.
-/
theorem lie_model_transport_isomorphism : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (e : X' ≅ X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (t : SAB H X) (t' : SAB H X') (m : SABMap t' t e.hom) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V), ξ' ≫ e.hom = ξ → ∃ M' : LieModel t'.G ξ' V, (∀ v, (M'.pt v).left ≫ m.φ = (M.pt v).left) ∧ (∀ n, FullTorsion t.G ξ n → FullTorsion t'.G ξ' n) ∧ (IsCptGen ξ → IsCptGen ξ') ∧ ∀ (q : Cpt ξ') (h : genPt ξ ⤳ e.hom q.1), regAt ξ' q = regAt ξ ⟨e.hom q.1, h⟩ ∧ (M'.lat q : Set V) = M.lat ⟨e.hom q.1, h⟩ ∧ ∀ n, (M'.htOm t'.PP.L n q : Set (Module.Dual Ω V)) = M.htOm t.PP.L n ⟨e.hom q.1, h⟩ := by
  intro E _ _ _ H X X' e Ω _ ξ ξ' t t' m V _ _ M hξ
  have hφ : IsGrpPullback t'.G t.G e.hom m.φ := m.cart
  haveI : IsIso m.φ := hφ.1.isIso_fst_of_isIso
  have φψ : m.φ ≫ inv m.φ = 𝟙 _ := IsIso.hom_inv_id _
  have ψφ : inv m.φ ≫ m.φ = 𝟙 _ := IsIso.inv_hom_id _
  have fg : e.hom ≫ e.inv = 𝟙 X' := e.hom_inv_id
  have gf : e.inv ≫ e.hom = 𝟙 X := e.inv_hom_id
  have hψw : inv m.φ ≫ t'.G.hom = t.G.hom ≫ e.inv := by
    rw [← cancel_mono e.hom, Category.assoc, Category.assoc, ← hφ.1.w, gf, Category.comp_id,
      ← Category.assoc, ψφ, Category.id_comp]
  have hψ : IsGrpPullback t.G t'.G e.inv (inv m.φ) := by
    refine IsGrpPullback.cancel hφ ?_ hψw
    rw [gf, ψφ]
    exact Isomove.grp_id t.G
  have hξ' : ξ ≫ e.inv = ξ' := by rw [← hξ, Category.assoc, fg, Category.comp_id]
  obtain ⟨M', hM⟩ := Isomove.model hφ hψ fg φψ hξ M
  have hM' : ∀ v, (M'.pt v).left ≫ m.φ = (M.pt v).left := by
    intro v
    rw [← hM v, Category.assoc, ψφ, Category.comp_id]
  have hW1 : ∀ (n : ℕ) (k : Type) [Field k] (z' : Sp k ⟶ X') (z : Sp k ⟶ X), z' ≫ e.hom = z →
      ∀ (a' b' : Over.mk z' ⟶ t'.G) (a b : Over.mk z ⟶ t.G) (c : kˣ), a'.left ≫ m.φ = a.left →
        b'.left ≫ m.φ = b.left → Out.WeilIs t.G t.PP.L (n : ℤ) a b (unitOn c) →
          Out.WeilIs t'.G t'.PP.L (n : ℤ) a' b' (unitOn c) := by
    intro n k _ z' z hz a' b' a b c ha hb hw
    subst hz
    exact (GlobalTheory.T.weil_pairing_pullback_iff E H X X' t t' e.hom m k z' a' b' a b n c ha hb).mpr hw
  have hW2 : ∀ (n : ℕ) (k : Type) [Field k] (z' : Sp k ⟶ X) (z : Sp k ⟶ X'), z' ≫ e.inv = z →
      ∀ (a' b' : Over.mk z' ⟶ t.G) (a b : Over.mk z ⟶ t'.G) (c : kˣ), a'.left ≫ inv m.φ = a.left →
        b'.left ≫ inv m.φ = b.left → Out.WeilIs t'.G t'.PP.L (n : ℤ) a b (unitOn c) →
          Out.WeilIs t.G t.PP.L (n : ℤ) a' b' (unitOn c) := by
    intro n k _ z' z hz a' b' a b c ha hb hw
    have hz2 : z' = z ≫ e.hom := by rw [← hz, Category.assoc, gf, Category.comp_id]
    subst hz2
    have ha' : a.left ≫ m.φ = a'.left := by rw [← ha, Category.assoc, ψφ, Category.comp_id]
    have hb' : b.left ≫ m.φ = b'.left := by rw [← hb, Category.assoc, ψφ, Category.comp_id]
    exact (GlobalTheory.T.weil_pairing_pullback_iff E H X X' t t' e.hom m k z a b a' b' n c ha' hb').mp hw
  refine ⟨M', hM', ?_, ?_, ?_⟩
  · intro n hT k _ i g' hpow
    have hy : (spMap i ≫ ξ') ≫ e.hom = spMap i ≫ ξ := by rw [Category.assoc, hξ]
    obtain ⟨a, ha⟩ := mv_push hφ.1.w hy g'
    obtain ⟨x, hx⟩ := hT k i a (mv_pow hφ hy ha hpow)
    obtain ⟨x', hx'⟩ := mv_push hψw hξ' x
    refine ⟨x', ?_⟩
    calc g'.left = (g'.left ≫ m.φ) ≫ inv m.φ := by rw [Category.assoc, φψ, Category.comp_id]
      _ = (spMap i ≫ x.left) ≫ inv m.φ := by rw [ha, hx]
      _ = spMap i ≫ x'.left := by rw [Category.assoc, hx']
  · intro hc
    have hsp : ∀ p : Cpt ξ', genPt ξ ⤳ e.hom p.1 := by
      intro p
      have h0 : genPt ξ = e.hom (genPt ξ') := by
        show ξ _ = e.hom (ξ' _)
        rw [← hξ]
        exact Scheme.Hom.comp_apply _ _ _
      rw [h0]
      exact p.2.map e.hom.continuous
    refine ⟨?_, ?_⟩
    · have key : ∀ ζ : Sp Ω ⟶ X, ξ' ≫ e.hom = ζ → Function.Bijective (Scheme.stalkClosedPointTo ζ).hom →
          Function.Bijective (Scheme.stalkClosedPointTo ξ').hom := by
        intro ζ hζ hb
        subst hζ
        rw [Scheme.stalkClosedPointTo_comp] at hb
        change Function.Bijective ((Scheme.stalkClosedPointTo ξ').hom ∘ (e.hom.stalkMap _).hom) at hb
        exact (Function.Bijective.of_comp_iff _ (ConcreteCategory.bijective_of_isIso (e.hom.stalkMap _))).mp hb
      exact key ξ hξ hc.bij
    · intro p a b hab
      obtain ⟨σ, -, h2, hbij⟩ := mv_stalk hξ p ⟨e.hom p.1, hsp p⟩ rfl
      obtain ⟨a0, rfl⟩ := (hbij inferInstance).2 a
      obtain ⟨b0, rfl⟩ := (hbij inferInstance).2 b
      have hab' : genMap ξ ⟨e.hom p.1, hsp p⟩ a0 = genMap ξ ⟨e.hom p.1, hsp p⟩ b0 := by
        rw [← h2]
        exact hab
      rw [hc.inj _ hab']
  · intro q h
    have hq2 : e.inv (e.hom q.1) = q.1 := by
      rw [← Scheme.Hom.comp_apply, e.hom_inv_id]
      rfl
    refine ⟨le_antisymm (mv_regAt_le (f := e.inv) hξ' ⟨e.hom q.1, h⟩ q hq2)
      (mv_regAt_le hξ q ⟨e.hom q.1, h⟩ rfl), ?_, ?_⟩
    · ext v
      constructor
      · intro hv
        exact Isomove.lat_le hφ gf hξ' hM' ⟨e.hom q.1, h⟩ q hq2 v hv
      · intro hv
        exact Isomove.lat_le hψ fg hξ hM q ⟨e.hom q.1, h⟩ rfl v hv
    · intro n
      ext w
      constructor
      · intro hw
        exact Isomove.htOm_le hφ hψ fg gf φψ ψφ hξ hM (hW1 n) q ⟨e.hom q.1, h⟩ rfl w hw
      · intro hw
        exact Isomove.htOm_le hψ hφ gf fg ψφ φψ hξ' hM' (hW2 n) ⟨e.hom q.1, h⟩ q hq2 w hw

end PositivityTheory.UnitarySelfGeneration
