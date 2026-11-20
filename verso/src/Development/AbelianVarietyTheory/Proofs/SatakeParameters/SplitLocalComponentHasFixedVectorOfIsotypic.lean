import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalHeckeScalarOnTypeSpacesAllPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedVectorsNeBotOfMemSumIntertwiningRanges
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceCompletionEquivUnique
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IsoTypFixLoc

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `[NG.rt, mul_assoc]`.
-/
theorem rt_rt (h h' : GAf L n) (f : GAf L n → W) : NG.rt L n h (NG.rt L n h' f) = NG.rt L n (h * h') f := by
  funext g; simp [NG.rt, mul_assoc]

def LocEq (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T : τ.V →ₗ[ℂ] (GAf L n → W)) : Prop :=
  ∀ x : GAf L n, TrivOutside {s.v} x → ∀ a, T (τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) a) = NG.rt L n x (T a)

/- English proof (translation)
Take `⟨hdec, hcomm, -⟩` from `GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s`. Establish `hnt : Nontrivial τ.V` using `by haveI := τ.irr`. Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[not_nontrivial_iff_subsingleton]`. Apply `(bot_ne_top : (⊥ : Subrepresentation τ.ρ) ≠ ⊤)` to reduce the goal to its premises.

Establish `: ∀ W : Subrepresentation τ.ρ, W = ⊥`. Introduce `W`. Use extensionality with `x`. Simplify using `[Subsingleton.elim x 0]`. Rewrite using `[this ⊤]`.

Set `Good : (τ.V →ₗ[ℂ] (GAf L n → W)) → Prop` to `fun T => LocEq s τ i T ∧ ∀ u, T u ∈ S`. Set `Wd : Submodule ℂ (GAf L n → W)` to `⨆ T : {T // Good T}, LinearMap.range T.1`. Establish `hWdS : Wd ≤ S`. Use `iSup_le fun T => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨u, rfl⟩`.

Conclude with `T.2.2 u`. Establish `hWdle : Wd ≤ ⨆ T : {T : τ.V →ₗ[ℂ] (GAf L n → W) // LocEq s τ i T}, LinearMap.range T.1` using `iSup_le fun T => le_iSup_of_le (⟨T.1, T.2.1⟩ : {T : τ.V →ₗ[ℂ] (GAf L n → W) // LocEq s τ i T}) le_rfl`. Establish `htr : ∀ (T : τ.V →ₗ[ℂ] (GAf L n → W)) (y : GAf L n), Good T → TrivOutside {s.v}ᶜ y → Good ((NG.rt L n y).comp T)`. Introduce `T y hT hy`. Use `⟨fun x hx u => ?_, fun u => hS.1.stable y _ (hT.2 u)⟩` and prove the remaining obligations.

Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[hT.1 x hx u, rt_rt, rt_rt, (hcomm x y hx hy).eq]`. Establish `hstab : ∀ h, ∀ f ∈ Wd, NG.rt L n h f ∈ Wd`. Introduce `h f hf`. Use `Submodule.iSup_induction _ (motive := fun f => NG.rt L n h f ∈ Wd) hf ?_ ?_ ?_` and prove the remaining obligations.

Introduce and unpack `T _ ⟨u, rfl⟩`. Take `⟨x, y, hx, hy, he⟩` from `hdec h`. Establish `e : NG.rt L n h (T.1 u) = ((NG.rt L n y).comp T.1) (τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) u)`. Rewrite using `[LinearMap.comp_apply, T.2.1 x hx u, rt_rt, he, (hcomm x y hx hy).eq]`. Rewrite using `[e]`.

Conclude with `Submodule.mem_iSup_of_mem (⟨_, htr T.1 y T.2 hy⟩ : {T // Good T}) ⟨_, rfl⟩`. Simplify using the standard rewrite rules. Introduce `f₁ f₂ h₁ h₂`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ h₁ h₂`.

Establish `hT0 : Good T0` using `⟨hT0eq, hT0S⟩`. Break down `hS.2.2 Wd ⟨hWdS.trans hS.1.le, hstab⟩ hWdS with h0 | h0` into its components or cases. It suffices to derive a contradiction. Take `⟨u, hu⟩` from `exists_ne (0 : τ.V)`. Establish `hmem : T0 u ∈ Wd` using `Submodule.mem_iSup_of_mem (⟨T0, hT0⟩ : {T // Good T}) ⟨u, rfl⟩`.

Rewrite `hmem` using `[h0, Submodule.mem_bot]`. Conclude with `hu (hT0inj (hmem.trans (map_zero T0).symm))`. Rewrite using `[← h0]`. Conclude with `hWdle`.
-/
theorem le_iSup_range (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)) (hS : NG.IsIrrRep ρ S)
    (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T0 : τ.V →ₗ[ℂ] (GAf L n → W))
    (hT0inj : Function.Injective T0) (hT0S : ∀ a, T0 a ∈ S) (hT0eq : LocEq s τ i T0) :
    S ≤ ⨆ T : {T : τ.V →ₗ[ℂ] (GAf L n → W) // LocEq s τ i T}, LinearMap.range T.1 := by
  obtain ⟨hdec, hcomm, -⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  have hnt : Nontrivial τ.V := by
    haveI := τ.irr
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    apply (bot_ne_top : (⊥ : Subrepresentation τ.ρ) ≠ ⊤)
    have : ∀ W : Subrepresentation τ.ρ, W = ⊥ := by
      intro W
      ext x
      simp [Subsingleton.elim x 0]
    rw [this ⊤]
  let Good : (τ.V →ₗ[ℂ] (GAf L n → W)) → Prop := fun T => LocEq s τ i T ∧ ∀ u, T u ∈ S
  let Wd : Submodule ℂ (GAf L n → W) := ⨆ T : {T // Good T}, LinearMap.range T.1
  have hWdS : Wd ≤ S := by
    refine iSup_le fun T => ?_
    rintro _ ⟨u, rfl⟩
    exact T.2.2 u
  have hWdle : Wd ≤ ⨆ T : {T : τ.V →ₗ[ℂ] (GAf L n → W) // LocEq s τ i T}, LinearMap.range T.1 :=
    iSup_le fun T => le_iSup_of_le (⟨T.1, T.2.1⟩ : {T : τ.V →ₗ[ℂ] (GAf L n → W) // LocEq s τ i T}) le_rfl
  have htr : ∀ (T : τ.V →ₗ[ℂ] (GAf L n → W)) (y : GAf L n), Good T → TrivOutside {s.v}ᶜ y → Good ((NG.rt L n y).comp T) := by
    intro T y hT hy
    refine ⟨fun x hx u => ?_, fun u => hS.1.stable y _ (hT.2 u)⟩
    simp only [LinearMap.comp_apply]
    rw [hT.1 x hx u, rt_rt, rt_rt, (hcomm x y hx hy).eq]
  have hstab : ∀ h, ∀ f ∈ Wd, NG.rt L n h f ∈ Wd := by
    intro h f hf
    refine Submodule.iSup_induction _ (motive := fun f => NG.rt L n h f ∈ Wd) hf ?_ ?_ ?_
    · rintro T _ ⟨u, rfl⟩
      obtain ⟨x, y, hx, hy, he⟩ := hdec h
      have e : NG.rt L n h (T.1 u) = ((NG.rt L n y).comp T.1) (τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) u) := by
        rw [LinearMap.comp_apply, T.2.1 x hx u, rt_rt, he, (hcomm x y hx hy).eq]
      rw [e]
      exact Submodule.mem_iSup_of_mem (⟨_, htr T.1 y T.2 hy⟩ : {T // Good T}) ⟨_, rfl⟩
    · simp
    · intro f₁ f₂ h₁ h₂; rw [map_add]; exact Submodule.add_mem _ h₁ h₂
  have hT0 : Good T0 := ⟨hT0eq, hT0S⟩
  rcases hS.2.2 Wd ⟨hWdS.trans hS.1.le, hstab⟩ hWdS with h0 | h0
  · exfalso
    obtain ⟨u, hu⟩ := exists_ne (0 : τ.V)
    have hmem : T0 u ∈ Wd := Submodule.mem_iSup_of_mem (⟨T0, hT0⟩ : {T // Good T}) ⟨u, rfl⟩
    rw [h0, Submodule.mem_bot] at hmem
    exact hu (hT0inj (hmem.trans (map_zero T0).symm))
  · rw [← h0]
    exact hWdle

/- English proof (translation)
Use `sSup_le ?_` and prove the remaining obligations. Introduce and unpack `S' ⟨hS', E, hE⟩`. Set `T1 : τ.V →ₗ[ℂ] (GAf L n → W)` to `S'.subtype ∘ₗ (E : S →ₗ[ℂ] S') ∘ₗ LinearMap.codRestrict S T0 hT0S`. Use `le_iSup_range ρ S' hS' s τ i T1 ?_ (fun a => (E _).2) ?_` and prove the remaining obligations. Introduce `a b hab`.

Apply `hT0inj` to reduce the goal to its premises. Use `E.injective (Subtype.ext hab)` as an intermediate fact. Conclude with `congrArg Subtype.val this`. Introduce `x hx a`. Conclude with `hE x ⟨T0 a, hT0S a⟩ ⟨_, hT0S _⟩ (hT0eq x hx a)`.
-/
theorem isoTyp_le (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W))
    (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T0 : τ.V →ₗ[ℂ] (GAf L n → W))
    (hT0inj : Function.Injective T0) (hT0S : ∀ a, T0 a ∈ S) (hT0eq : LocEq s τ i T0) :
    NG.isoTyp ρ S ≤ ⨆ T : {T : τ.V →ₗ[ℂ] (GAf L n → W) // LocEq s τ i T}, LinearMap.range T.1 := by
  refine sSup_le ?_
  rintro S' ⟨hS', E, hE⟩
  let T1 : τ.V →ₗ[ℂ] (GAf L n → W) := S'.subtype ∘ₗ (E : S →ₗ[ℂ] S') ∘ₗ LinearMap.codRestrict S T0 hT0S
  refine le_iSup_range ρ S' hS' s τ i T1 ?_ (fun a => (E _).2) ?_
  · intro a b hab
    apply hT0inj
    have := E.injective (Subtype.ext hab)
    exact congrArg Subtype.val this
  · intro x hx a
    exact hE x ⟨T0 a, hT0S a⟩ ⟨_, hT0S _⟩ (hT0eq x hx a)

end GlobalTheory.IsoTypFixLoc

open GlobalTheory.IsoTypFixLoc in

/- English proof (translation)
Introduce `L _ _ _ n W _ _ ρ S hS s τ hloc i hi hiL f hf hf0 hfix`. Take `⟨i', T0, hi', hi'L, hT0inj, hT0S, hT0eq⟩` from `hloc`. Take `rfl` from `GlobalTheory.splitPlace_completion_equiv_unique L s i' i hi' hi hi'L hiL`. Establish `hspan` using `isoTyp_le ρ S s τ i' T0 hT0inj hT0S hT0eq hf`. Establish `hI` using `GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s`.

Set `H : Subgroup (GAf L n)` to `{ carrier := {x | TrivOutside {s.v} x} mul_mem' := fun hx hy => GlobalTheory.HeckeScalarSph.triv_mul hx hy one_mem' := GlobalTheory.HeckeScalarSph.triv_one inv_mem' := fun hx => GlobalTheory.HeckeScalarSph.triv_inv hx }`. Set `φ : H →* GL (Fin n) (s.w.adicCompletion L)` to `(Matrix.GeneralLinearGroup.map i'.toRingHom).comp ((s.loc n).comp H.subtype)`. Establish `hφ : Function.Surjective φ`. Introduce `h`. Take `⟨x, ⟨hx, e⟩, -⟩` from `hI.2.2 (Matrix.GeneralLinearGroup.map i'.symm.toRingHom h)`.

Use `⟨⟨x, hx⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Matrix.GeneralLinearGroup.map i'.toRingHom (s.loc n x) = h`. Rewrite using `[e]`. Conclude with `Units.ext (Matrix.ext fun a b => i'.apply_symm_apply _)`. Set `σ' : Representation ℂ H τ.V` to `τ.ρ.comp φ`.

Establish `hσ' : σ'.IsIrreducible` using `GlobalTheory.LocCompSplit.isIrreducible_comp_of_surjective τ.ρ φ hφ τ.irr`. Set `ρ' : Representation ℂ H (GAf L n → W)` to `{ toFun := fun x => NG.rt L n (x : GAf L n) map_one' := by`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `g`. Use function extensionality and compare the values at `a`.

Simplify using `[NG.rt]`. Use the proof step `map_mul' := fun x y => by`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `g`. Use function extensionality and compare the values at `a`.

Simplify using `[NG.rt, mul_assoc] }`. Rewrite `hspan` using `[Submodule.mem_iSup_iff_exists_finset]`. Take `⟨t, ht⟩` from `hspan`. Set `T : t → σ'.IntertwiningMap ρ'` to `fun j => ⟨j.1.1, fun g => LinearMap.ext fun a => j.1.2 g.1 g.2 a⟩`. Establish `hf' : f ∈ ⨆ j, LinearMap.range (T j).toLinearMap`.

Rewrite `ht` using `[iSup_subtype']`. Conclude with `ht`. Set `K : Subgroup H` to `(GlobalTheory.HeckeScalarSph.locK n s.v).comap H.subtype`. Establish `hfixK : ∀ k ∈ K, ρ' k f = f` using `fun k hk => hfix k.1 hk`. Establish `hne` using `GlobalTheory.UnrLoc.fixed_ne_bot_of_mem_iSup_range hσ' T K hf' hf0 hfixK`.

Rewrite `hne` using `[Submodule.ne_bot_iff]`. Take `⟨y, hy, hy0⟩` from `hne`. Use `⟨y, hy0, fun κ hκ => ?_⟩` and prove the remaining obligations. Conclude with `(GlobalTheory.Parabolic.mem_fixed.1 hy) ⟨κ, hκ.2⟩ hκ`.
-/
theorem GlobalTheory.IsoTypFixLoc.main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)), NG.IsIrrRep ρ S → ∀ (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s τ → ∀ (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous i → (∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ f ∈ NG.isoTyp ρ S, f ≠ 0 → (∀ κ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, NG.rt L n κ f = f) → ∃ a : τ.V, a ≠ 0 ∧ ∀ κ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n κ)) a = a := by
  intro L _ _ _ n W _ _ ρ S hS s τ hloc i hi hiL f hf hf0 hfix
  classical
  obtain ⟨i', T0, hi', hi'L, hT0inj, hT0S, hT0eq⟩ := hloc
  obtain rfl := GlobalTheory.splitPlace_completion_equiv_unique L s i' i hi' hi hi'L hiL
  have hspan := isoTyp_le ρ S s τ i' T0 hT0inj hT0S hT0eq hf
  have hI := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  let H : Subgroup (GAf L n) :=
    { carrier := {x | TrivOutside {s.v} x}
      mul_mem' := fun hx hy => GlobalTheory.HeckeScalarSph.triv_mul hx hy
      one_mem' := GlobalTheory.HeckeScalarSph.triv_one
      inv_mem' := fun hx => GlobalTheory.HeckeScalarSph.triv_inv hx }
  let φ : H →* GL (Fin n) (s.w.adicCompletion L) :=
    (Matrix.GeneralLinearGroup.map i'.toRingHom).comp ((s.loc n).comp H.subtype)
  have hφ : Function.Surjective φ := by
    intro h
    obtain ⟨x, ⟨hx, e⟩, -⟩ := hI.2.2 (Matrix.GeneralLinearGroup.map i'.symm.toRingHom h)
    refine ⟨⟨x, hx⟩, ?_⟩
    change Matrix.GeneralLinearGroup.map i'.toRingHom (s.loc n x) = h
    rw [e]
    exact Units.ext (Matrix.ext fun a b => i'.apply_symm_apply _)
  let σ' : Representation ℂ H τ.V := τ.ρ.comp φ
  have hσ' : σ'.IsIrreducible := GlobalTheory.LocCompSplit.isIrreducible_comp_of_surjective τ.ρ φ hφ τ.irr
  let ρ' : Representation ℂ H (GAf L n → W) :=
    { toFun := fun x => NG.rt L n (x : GAf L n)
      map_one' := by
        apply LinearMap.ext
        intro g
        funext a
        simp [NG.rt]
      map_mul' := fun x y => by
        apply LinearMap.ext
        intro g
        funext a
        simp [NG.rt, mul_assoc] }
  rw [Submodule.mem_iSup_iff_exists_finset] at hspan
  obtain ⟨t, ht⟩ := hspan
  let T : t → σ'.IntertwiningMap ρ' := fun j =>
    ⟨j.1.1, fun g => LinearMap.ext fun a => j.1.2 g.1 g.2 a⟩
  have hf' : f ∈ ⨆ j, LinearMap.range (T j).toLinearMap := by
    rw [iSup_subtype'] at ht
    exact ht
  let K : Subgroup H := (GlobalTheory.HeckeScalarSph.locK n s.v).comap H.subtype
  have hfixK : ∀ k ∈ K, ρ' k f = f := fun k hk => hfix k.1 hk
  have hne := GlobalTheory.UnrLoc.fixed_ne_bot_of_mem_iSup_range hσ' T K hf' hf0 hfixK
  rw [Submodule.ne_bot_iff] at hne
  obtain ⟨y, hy, hy0⟩ := hne
  refine ⟨y, hy0, fun κ hκ => ?_⟩
  exact (GlobalTheory.Parabolic.mem_fixed.1 hy) ⟨κ, hκ.2⟩ hκ
