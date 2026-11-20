import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecompositionStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SpanLoc

/- English proof (translation)
Introduce `L _ _ _ n a S hS s σ hloc c hc hcL`. Take `⟨i, T0, hi, hiL, hT0inj, hT0S, hT0eq⟩` from `hloc`. Establish `hci : c = i`. Establish `hd` using `IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (K := maximalRealSubfield L) s.v`. Establish `hfun : (c : s.v.adicCompletion (maximalRealSubfield L) → s.w.adicCompletion L) = i`.

Use `hd.equalizer hc hi (funext fun y => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Rewrite using `[← s.i.commutes y, hcL, hiL]`. Conclude with `RingEquiv.ext (congrFun hfun)`. Substitute `hci` using the available equality.

Take `⟨hdec, hcomm, -⟩` from `GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s`. Establish `hrt : ∀ (h h' : GAf L n) (f : GAf L n → a.W), NG.rt L n h (NG.rt L n h' f) = NG.rt L n (h * h') f`. Introduce `h h' f`. Use function extensionality and compare the values at `g`. Simplify using `[NG.rt, mul_assoc]`.

Establish `hnt : Nontrivial σ.V` using `by haveI := σ.irr`. Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[not_nontrivial_iff_subsingleton]`. Apply `(bot_ne_top : (⊥ : Subrepresentation σ.ρ) ≠ ⊤)` to reduce the goal to its premises. Establish `: ∀ W : Subrepresentation σ.ρ, W = ⊥`.

Introduce `W`. Use extensionality with `x`. Simplify using `[Subsingleton.elim x 0]`. Rewrite using `[this ⊤]`. Unfold `NG.isoTyp`.

Use `sSup_le ?_` and prove the remaining obligations. Introduce and unpack `S' ⟨hS'irr, Φ, hΦ⟩`. Set `Good : (σ.V →ₗ[ℂ] (GAf L n → a.W)) → Prop` to `fun T => (∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)) ∧ ∀ u, T u ∈ S'`. Set `Wd : Submodule ℂ (GAf L n → a.W)` to `⨆ T : {T // Good T}, LinearMap.range T.1`. Establish `hWdS' : Wd ≤ S'`.

Use `iSup_le fun T => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨u, rfl⟩`. Conclude with `T.2.2 u`. Establish `hWdle : Wd ≤ ⨆ (T : σ.V →ₗ[ℂ] (GAf L n → a.W)) (_ : (∀ v, T v ∈ NG.AFall L n a.ρ) ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)), LinearMap.range T`. Use `iSup_le fun T => ?_` and prove the remaining obligations.

Conclude with `le_iSup₂_of_le (f := fun (T : σ.V →ₗ[ℂ] (GAf L n → a.W)) (_ : (∀ v, T v ∈ NG.AFall L n a.ρ) ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)) => LinearMap.range T) T.1 ⟨fun u => hS'irr.1.le (T.2.2 u) …`. Establish `htr : ∀ (T : σ.V →ₗ[ℂ] (GAf L n → a.W)) (y : GAf L n), Good T → TrivOutside {s.v}ᶜ y → Good ((NG.rt L n y).comp T)`. Introduce `T y hT hy`. Use `⟨fun x hx u => ?_, fun u => hS'irr.1.stable y _ (hT.2 u)⟩` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply]`.

Rewrite using `[hT.1 x hx u, hrt, hrt, (hcomm x y hx hy).eq]`. Establish `hstab : ∀ h, ∀ f ∈ Wd, NG.rt L n h f ∈ Wd`. Introduce `h f hf`. Use `Submodule.iSup_induction _ (motive := fun f => NG.rt L n h f ∈ Wd) hf ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `T _ ⟨u, rfl⟩`.

Take `⟨x, y, hx, hy, he⟩` from `hdec h`. Establish `e : NG.rt L n h (T.1 u) = ((NG.rt L n y).comp T.1) (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) u)`. Rewrite using `[LinearMap.comp_apply, T.2.1 x hx u, hrt, he, (hcomm x y hx hy).eq]`. Rewrite using `[e]`. Conclude with `Submodule.mem_iSup_of_mem (⟨_, htr T.1 y T.2 hy⟩ : {T // Good T}) ⟨_, rfl⟩`.

Simplify using the standard rewrite rules. Introduce `f₁ f₂ h₁ h₂`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ h₁ h₂`. Set `T1 : σ.V →ₗ[ℂ] (GAf L n → a.W)` to `S'.subtype ∘ₗ Φ.toLinearMap ∘ₗ LinearMap.codRestrict S T0 hT0S`.

Establish `hT1 : Good T1`. Use `⟨fun x hx u => ?_, fun u => (Φ _).2⟩` and prove the remaining obligations. Conclude with `hΦ x ⟨T0 u, hT0S u⟩ ⟨T0 _, hT0S _⟩ (hT0eq x hx u)`. Establish `hrc` using `hS'irr.2.2 Wd ⟨hWdS'.trans hS'irr.1.le, hstab⟩ hWdS'`. Break down `hrc with h0 | h0` into its components or cases.

It suffices to derive a contradiction. Take `⟨u, hu⟩` from `exists_ne (0 : σ.V)`. Establish `hmem : T1 u ∈ Wd` using `Submodule.mem_iSup_of_mem (⟨T1, hT1⟩ : {T // Good T}) ⟨u, rfl⟩`. Rewrite `hmem` using `[h0, Submodule.mem_bot]`. Apply `hu` to reduce the goal to its premises.

Apply `hT0inj` to reduce the goal to its premises. Establish `h2 : Φ (LinearMap.codRestrict S T0 hT0S u) = 0` using `Subtype.ext hmem`. Rewrite using `[map_zero]`. Establish `h3` using `Φ.injective (h2.trans Φ.map_zero.symm)`. Conclude with `congrArg Subtype.val h3`.

Rewrite using `[← h0]`. Conclude with `hWdle`.
-/
theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → NG.isoTyp a.ρ S ≤ ⨆ (T : σ.V →ₗ[ℂ] (GAf L n → a.W)) (_ : (∀ v, T v ∈ NG.AFall L n a.ρ) ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)), LinearMap.range T := by
  intro L _ _ _ n a S hS s σ hloc c hc hcL
  obtain ⟨i, T0, hi, hiL, hT0inj, hT0S, hT0eq⟩ := hloc

  have hci : c = i := by
    have hd := IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (K := maximalRealSubfield L) s.v
    have hfun : (c : s.v.adicCompletion (maximalRealSubfield L) → s.w.adicCompletion L) = i := by
      refine hd.equalizer hc hi (funext fun y => ?_)
      simp only [Function.comp_apply]
      rw [← s.i.commutes y, hcL, hiL]
    exact RingEquiv.ext (congrFun hfun)
  subst hci
  obtain ⟨hdec, hcomm, -⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  have hrt : ∀ (h h' : GAf L n) (f : GAf L n → a.W), NG.rt L n h (NG.rt L n h' f) = NG.rt L n (h * h') f := by
    intro h h' f; funext g; simp [NG.rt, mul_assoc]
  have hnt : Nontrivial σ.V := by
    haveI := σ.irr
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    apply (bot_ne_top : (⊥ : Subrepresentation σ.ρ) ≠ ⊤)
    have : ∀ W : Subrepresentation σ.ρ, W = ⊥ := by
      intro W
      ext x
      simp [Subsingleton.elim x 0]
    rw [this ⊤]
  unfold NG.isoTyp
  refine sSup_le ?_
  rintro S' ⟨hS'irr, Φ, hΦ⟩
  let Good : (σ.V →ₗ[ℂ] (GAf L n → a.W)) → Prop := fun T =>
    (∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)) ∧
      ∀ u, T u ∈ S'
  let Wd : Submodule ℂ (GAf L n → a.W) := ⨆ T : {T // Good T}, LinearMap.range T.1
  have hWdS' : Wd ≤ S' := by
    refine iSup_le fun T => ?_
    rintro _ ⟨u, rfl⟩
    exact T.2.2 u
  have hWdle : Wd ≤ ⨆ (T : σ.V →ₗ[ℂ] (GAf L n → a.W)) (_ : (∀ v, T v ∈ NG.AFall L n a.ρ) ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)), LinearMap.range T := by
    refine iSup_le fun T => ?_
    exact le_iSup₂_of_le (f := fun (T : σ.V →ₗ[ℂ] (GAf L n → a.W)) (_ : (∀ v, T v ∈ NG.AFall L n a.ρ) ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)) => LinearMap.range T)
      T.1 ⟨fun u => hS'irr.1.le (T.2.2 u), T.2.1⟩ le_rfl

  have htr : ∀ (T : σ.V →ₗ[ℂ] (GAf L n → a.W)) (y : GAf L n), Good T → TrivOutside {s.v}ᶜ y → Good ((NG.rt L n y).comp T) := by
    intro T y hT hy
    refine ⟨fun x hx u => ?_, fun u => hS'irr.1.stable y _ (hT.2 u)⟩
    simp only [LinearMap.comp_apply]
    rw [hT.1 x hx u, hrt, hrt, (hcomm x y hx hy).eq]
  have hstab : ∀ h, ∀ f ∈ Wd, NG.rt L n h f ∈ Wd := by
    intro h f hf
    refine Submodule.iSup_induction _ (motive := fun f => NG.rt L n h f ∈ Wd) hf ?_ ?_ ?_
    · rintro T _ ⟨u, rfl⟩
      obtain ⟨x, y, hx, hy, he⟩ := hdec h
      have e : NG.rt L n h (T.1 u) = ((NG.rt L n y).comp T.1) (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) u) := by
        rw [LinearMap.comp_apply, T.2.1 x hx u, hrt, he, (hcomm x y hx hy).eq]
      rw [e]
      exact Submodule.mem_iSup_of_mem (⟨_, htr T.1 y T.2 hy⟩ : {T // Good T}) ⟨_, rfl⟩
    · simp
    · intro f₁ f₂ h₁ h₂; rw [map_add]; exact Submodule.add_mem _ h₁ h₂

  let T1 : σ.V →ₗ[ℂ] (GAf L n → a.W) := S'.subtype ∘ₗ Φ.toLinearMap ∘ₗ LinearMap.codRestrict S T0 hT0S
  have hT1 : Good T1 := by
    refine ⟨fun x hx u => ?_, fun u => (Φ _).2⟩
    exact hΦ x ⟨T0 u, hT0S u⟩ ⟨T0 _, hT0S _⟩ (hT0eq x hx u)
  have hrc := hS'irr.2.2 Wd ⟨hWdS'.trans hS'irr.1.le, hstab⟩ hWdS'
  rcases hrc with h0 | h0
  · exfalso
    obtain ⟨u, hu⟩ := exists_ne (0 : σ.V)
    have hmem : T1 u ∈ Wd := Submodule.mem_iSup_of_mem (⟨T1, hT1⟩ : {T // Good T}) ⟨u, rfl⟩
    rw [h0, Submodule.mem_bot] at hmem
    apply hu
    apply hT0inj
    have h2 : Φ (LinearMap.codRestrict S T0 hT0S u) = 0 := Subtype.ext hmem
    rw [map_zero]
    have h3 := Φ.injective (h2.trans Φ.map_zero.symm)
    exact congrArg Subtype.val h3
  · rw [← h0]; exact hWdle

end GlobalTheory.SpanLoc
