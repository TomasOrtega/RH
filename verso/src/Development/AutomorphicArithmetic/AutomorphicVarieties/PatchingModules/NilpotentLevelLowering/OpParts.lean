import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.PsModule
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.PsLinSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.SpLocIdem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.FreeSummand
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TopNilMapMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.ChiApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.PairMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Pa.Lev.OpP

/- English proof (translation)
Set `T' : τ → Module.End Λ M` to `fun s => (T s).restrictScalars Λ`. Establish `hT' : ∀ i j, Commute (T' i) (T' j)`. Introduce `i j`. Conclude with `LinearMap.ext fun m => congrArg (fun g : Module.End R M => g m) (hT i j).eq`. Take `⟨e, he, hidem, hrange⟩` from `exists_idem_topNil Λ τ M T' hT'`.

Establish `hcomm : ∀ ψ : Module.End Λ M, (∀ s, Commute (T' s) ψ) → Commute e ψ`. Introduce `ψ hψ`. Establish `hle : Algebra.adjoin Λ (Set.range T') ≤ Subalgebra.centralizer Λ {ψ}`. Apply `Algebra.adjoin_le` to reduce the goal to its premises. Introduce and unpack `_ ⟨s, rfl⟩`.

Rewrite using `[SetLike.mem_coe, Subalgebra.mem_centralizer_iff]`. Introduce and unpack `g rfl`. Conclude with `(hψ s).eq.symm`. Establish `hmem` using `hle he`. Rewrite `hmem` using `[Subalgebra.mem_centralizer_iff]`.

Conclude with `(hmem ψ rfl).symm`. Establish `heR : ∀ (r : R) (m : M), e (r • m) = r • e m`. Introduce `r m`. Establish `h` using `hcomm ((r • (LinearMap.id : M →ₗ[R] M)).restrictScalars Λ) (fun s => by`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations.

Use `show T s (r • x) = r • T s x`. Conclude with `map_smul _ _ _)`. Conclude with `congrArg (fun g : Module.End Λ M => g m) h.eq`. Establish `heT : ∀ s m, e (T s m) = T s (e m)`. Introduce `s m`.

Conclude with `congrArg (fun g : Module.End Λ M => g m) (hcomm (T' s) (fun s' => hT' s' s)).eq`. Establish `hee : ∀ m, e (e m) = e m` using `fun m => congrArg (fun g : Module.End Λ M => g m) hidem.eq`. Set `Ns : Submodule R M` to `{ carrier := {m | e m = m} add_mem' := by`. Introduce `a b ha hb`. Use `show e (a + b) = a + b`.

Rewrite using `[map_add, show e a = a from ha, show e b = b from hb]`. Use the proof step `zero_mem' := by show e 0 = 0`. Conclude with `map_zero e`. Use the proof step `smul_mem' := by`. Introduce `r m hm`.

Use `show e (r • m) = r • m`. Rewrite using `[heR, show e m = m from hm] }`. Use `haveI : IsNoetherian Λ M := isNoetherian_of_isNoetherianRing_of_finite Λ M`. Use `haveI hfin : Module.Finite Λ Ns := by haveI := isNoetherian_submodule' (Ns.restrictScalars Λ)`. Conclude with `inferInstanceAs (Module.Finite Λ (Ns.restrictScalars Λ))`.

Set `Tn : τ → Module.End R Ns` to `fun s => { toFun := fun x => ⟨T s x, show e (T s x) = T s x by rw [heT, show e x = x from x.2]⟩ map_add' := fun a b => Subtype.ext (map_add _ _ _) map_smul' := fun r a => Subtype.ext (map_smul _ _ _) }`. Establish `hTn : ∀ i j, Commute (Tn i) (Tn j)`. Introduce `i j`. Conclude with `LinearMap.ext fun x => Subtype.ext (congrArg (fun g : Module.End R M => g x) (hT i j).eq)`. Set `pr : M →ₗ[Λ] Ns` to `{ toFun := fun m => ⟨e m, hee m⟩ map_add' := fun a b => Subtype.ext (map_add e a b) map_smul' := fun c m => Subtype.ext (e.map_smul c m) }`.

Set `i : Ns →ₗ[Λ] M` to `{ toFun := fun x => (x : M) map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `hpowN : ∀ s (r : ℕ) (x : Ns), (((Tn s).restrictScalars Λ ^ r) x : M) = (T' s ^ r) (x : M)`. Introduce `s r`. Proceed by induction on `r with`. Consider the case `zero => intro x`.

Both sides reduce to the same expression. Consider the case `succ r ih`. Introduce `x`. Rewrite using `[pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]`. Both sides reduce to the same expression.

Establish `htop : (topNil (maximalIdeal Λ) fun s => (Tn s).restrictScalars Λ) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `x _`. Rewrite using `[mem_topNil]`. Introduce `s k`.

Establish `hx : (x : M) ∈ topNil (maximalIdeal Λ) T'`. Rewrite using `[← hrange]`. Conclude with `⟨x, x.2⟩`. Rewrite `hx` using `[mem_topNil]`. Use `(hx s k).mono fun r hr => ?_` and prove the remaining obligations.

Establish `hmap : (maximalIdeal Λ ^ k • ⊤ : Submodule Λ M).map pr ≤ maximalIdeal Λ ^ k • ⊤`. Rewrite using `[Submodule.map_smul'']`. Conclude with `Submodule.smul_mono le_rfl le_top`. Establish `hin` using `hmap ⟨_, hr, rfl⟩`. Establish `heq : pr ((T' s ^ r) (x : M)) = ((Tn s).restrictScalars Λ ^ r) x`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show e ((T' s ^ r) (x : M)) = _`. Rewrite using `[← hpowN]`. Conclude with `(((Tn s).restrictScalars Λ ^ r) x).2`. Rewrite `hin` using `[heq]`.

Conclude with `hin`. Take `⟨act, hact⟩` from `psModule Λ R Ns τ Tn hTn htop`. Use `letI modP : Module (MvPowerSeries τ R) Ns := Module.compHom Ns act.toRingHom`. Use `haveI tow : IsScalarTower Λ (MvPowerSeries τ R) Ns := by`. Use `⟨fun c f x => ?_⟩` and prove the remaining obligations.

Use `show act (c • f) x = c • act f x`. Rewrite using `[← algebraMap_smul R c f, map_smul, LinearMap.smul_apply, algebraMap_smul]`. Use `⟨Ns, inferInstance, modP, inferInstance, tow, i, pr, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Conclude with `Subtype.ext x.2`.

Introduce `a x show ((act (MvPowerSeries.C a) x : Ns) : M) = a • (x : M)`. Establish `hCa : (MvPowerSeries.C a : MvPowerSeries τ R) = algebraMap R (MvPowerSeries τ R) a`. Rewrite using `[MvPowerSeries.algebraMap_apply]`. Both sides reduce to the same expression. Rewrite using `[hCa, act.commutes, Module.algebraMap_end_apply]`.

Both sides reduce to the same expression. Introduce `s x show ((act (MvPowerSeries.X s) x : Ns) : M) = T s x`. Rewrite using `[hact s]`. Both sides reduce to the same expression. Use `show LinearMap.range i = topNil (maximalIdeal Λ) T'`.

Rewrite using `[← hrange]`. Use extensionality with `m`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩`. Conclude with `⟨x, x.2⟩`.

Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨pr y, rfl⟩`. Introduce `φ hφ m`. Establish `h` using `hcomm φ (fun s => LinearMap.ext fun x => (hφ s x).symm)`. Conclude with `congrArg (fun g : Module.End Λ M => g m) h.eq`.
-/
theorem nilPart {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ]
    {R M τ : Type} [CommRing R] [Algebra Λ R] [AddCommGroup M] [Module R M] [Module Λ M] [IsScalarTower Λ R M]
    [Module.Finite Λ M] [Fintype τ] (T : τ → Module.End R M) (hT : ∀ i j, Commute (T i) (T j)) :
    ∃ (N : Type) (_ : AddCommGroup N) (_ : Module (MvPowerSeries τ R) N) (_ : Module Λ N)
      (_ : IsScalarTower Λ (MvPowerSeries τ R) N) (i : N →ₗ[Λ] M) (pr : M →ₗ[Λ] N), (∀ x, pr (i x) = x) ∧
      (∀ a x, i ((MvPowerSeries.C a : MvPowerSeries τ R) • x) = a • i x) ∧
      (∀ s x, i ((MvPowerSeries.X s : MvPowerSeries τ R) • x) = T s (i x)) ∧
      LinearMap.range i = topNil (maximalIdeal Λ) (fun s => (T s).restrictScalars Λ) ∧
      ∀ φ : Module.End Λ M, (∀ s m, φ (T s m) = T s (φ m)) → ∀ m, i (pr (φ m)) = φ (i (pr m)) := by
  classical
  let T' : τ → Module.End Λ M := fun s => (T s).restrictScalars Λ
  have hT' : ∀ i j, Commute (T' i) (T' j) := by
    intro i j
    exact LinearMap.ext fun m => congrArg (fun g : Module.End R M => g m) (hT i j).eq
  obtain ⟨e, he, hidem, hrange⟩ := exists_idem_topNil Λ τ M T' hT'
  have hcomm : ∀ ψ : Module.End Λ M, (∀ s, Commute (T' s) ψ) → Commute e ψ := by
    intro ψ hψ
    have hle : Algebra.adjoin Λ (Set.range T') ≤ Subalgebra.centralizer Λ {ψ} := by
      apply Algebra.adjoin_le
      rintro _ ⟨s, rfl⟩
      rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      rintro g rfl
      exact (hψ s).eq.symm
    have hmem := hle he
    rw [Subalgebra.mem_centralizer_iff] at hmem
    exact (hmem ψ rfl).symm
  have heR : ∀ (r : R) (m : M), e (r • m) = r • e m := by
    intro r m
    have h := hcomm ((r • (LinearMap.id : M →ₗ[R] M)).restrictScalars Λ) (fun s => by
      refine LinearMap.ext fun x => ?_
      show T s (r • x) = r • T s x
      exact map_smul _ _ _)
    exact congrArg (fun g : Module.End Λ M => g m) h.eq
  have heT : ∀ s m, e (T s m) = T s (e m) := by
    intro s m
    exact congrArg (fun g : Module.End Λ M => g m) (hcomm (T' s) (fun s' => hT' s' s)).eq
  have hee : ∀ m, e (e m) = e m := fun m => congrArg (fun g : Module.End Λ M => g m) hidem.eq
  let Ns : Submodule R M :=
    { carrier := {m | e m = m}
      add_mem' := by
        intro a b ha hb
        show e (a + b) = a + b
        rw [map_add, show e a = a from ha, show e b = b from hb]
      zero_mem' := by
        show e 0 = 0
        exact map_zero e
      smul_mem' := by
        intro r m hm
        show e (r • m) = r • m
        rw [heR, show e m = m from hm] }
  haveI : IsNoetherian Λ M := isNoetherian_of_isNoetherianRing_of_finite Λ M
  haveI hfin : Module.Finite Λ Ns := by
    haveI := isNoetherian_submodule' (Ns.restrictScalars Λ)
    exact inferInstanceAs (Module.Finite Λ (Ns.restrictScalars Λ))
  let Tn : τ → Module.End R Ns := fun s =>
    { toFun := fun x => ⟨T s x, show e (T s x) = T s x by rw [heT, show e x = x from x.2]⟩
      map_add' := fun a b => Subtype.ext (map_add _ _ _)
      map_smul' := fun r a => Subtype.ext (map_smul _ _ _) }
  have hTn : ∀ i j, Commute (Tn i) (Tn j) := by
    intro i j
    exact LinearMap.ext fun x => Subtype.ext (congrArg (fun g : Module.End R M => g x) (hT i j).eq)
  let pr : M →ₗ[Λ] Ns :=
    { toFun := fun m => ⟨e m, hee m⟩
      map_add' := fun a b => Subtype.ext (map_add e a b)
      map_smul' := fun c m => Subtype.ext (e.map_smul c m) }
  let i : Ns →ₗ[Λ] M :=
    { toFun := fun x => (x : M)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hpowN : ∀ s (r : ℕ) (x : Ns), (((Tn s).restrictScalars Λ ^ r) x : M) = (T' s ^ r) (x : M) := by
    intro s r
    induction r with
    | zero => intro x; rfl
    | succ r ih =>
      intro x
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
      rfl
  have htop : (topNil (maximalIdeal Λ) fun s => (Tn s).restrictScalars Λ) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [mem_topNil]
    intro s k
    have hx : (x : M) ∈ topNil (maximalIdeal Λ) T' := by
      rw [← hrange]
      exact ⟨x, x.2⟩
    rw [mem_topNil] at hx
    refine (hx s k).mono fun r hr => ?_
    have hmap : (maximalIdeal Λ ^ k • ⊤ : Submodule Λ M).map pr ≤ maximalIdeal Λ ^ k • ⊤ := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    have hin := hmap ⟨_, hr, rfl⟩
    have heq : pr ((T' s ^ r) (x : M)) = ((Tn s).restrictScalars Λ ^ r) x := by
      apply Subtype.ext
      show e ((T' s ^ r) (x : M)) = _
      rw [← hpowN]
      exact (((Tn s).restrictScalars Λ ^ r) x).2
    rw [heq] at hin
    exact hin
  obtain ⟨act, hact⟩ := psModule Λ R Ns τ Tn hTn htop
  letI modP : Module (MvPowerSeries τ R) Ns := Module.compHom Ns act.toRingHom
  haveI tow : IsScalarTower Λ (MvPowerSeries τ R) Ns := by
    refine ⟨fun c f x => ?_⟩
    show act (c • f) x = c • act f x
    rw [← algebraMap_smul R c f, map_smul, LinearMap.smul_apply, algebraMap_smul]
  refine ⟨Ns, inferInstance, modP, inferInstance, tow, i, pr, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact Subtype.ext x.2
  · intro a x
    show ((act (MvPowerSeries.C a) x : Ns) : M) = a • (x : M)
    have hCa : (MvPowerSeries.C a : MvPowerSeries τ R) = algebraMap R (MvPowerSeries τ R) a := by
      rw [MvPowerSeries.algebraMap_apply]
      rfl
    rw [hCa, act.commutes, Module.algebraMap_end_apply]
    rfl
  · intro s x
    show ((act (MvPowerSeries.X s) x : Ns) : M) = T s x
    rw [hact s]
    rfl
  · show LinearMap.range i = topNil (maximalIdeal Λ) T'
    rw [← hrange]
    ext m
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2⟩
    · rintro ⟨y, rfl⟩
      exact ⟨pr y, rfl⟩
  · intro φ hφ m
    have h := hcomm φ (fun s => LinearMap.ext fun x => (hφ s x).symm)
    exact congrArg (fun g : Module.End Λ M => g m) h.eq

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `x _`. Use `show ∀ (i : τ) (j : ℕ), ∀ᶠ (r : ℕ) in Filter.atTop, _`. Introduce `i j`. Take `⟨d, hd⟩` from `hn i j x`.

Rewrite using `[Filter.eventually_atTop]`. Use `⟨d, fun r hr => ?_⟩` and prove the remaining obligations. Take `⟨e, rfl⟩` from `Nat.exists_eq_add_of_le hr`. Establish `key : (((Module.toModuleEnd Λ (S` using `T) Y).comp θ0) (MvPowerSeries.X i) ^ (d + e)) x = θ0 (MvPowerSeries.X i) ^ e • (θ0 (MvPowerSeries.X i) ^ d • x) := by`. Rewrite using `[← map_pow, smul_smul, ← pow_add, Nat.add_comm e d, RingHom.comp_apply, map_pow θ0]`.

Both sides reduce to the same expression. Rewrite using `[key]`. Set `g : Y →ₗ[Λ] Y` to `Module.toModuleEnd Λ (S := T) Y (θ0 (MvPowerSeries.X i) ^ e)`. Establish `hle : (I ^ j • ⊤ : Submodule Λ Y).map g ≤ I ^ j • ⊤`. Rewrite using `[Submodule.map_smul'']`.

Conclude with `Submodule.smul_mono le_rfl le_top`. Conclude with `hle ⟨_, hd, rfl⟩`.
-/
private theorem topNil_toModuleEnd_X_eq_top_of_pow_smul_mem {Λ τ R T Y : Type} [CommRing Λ] [CommRing R] [CommRing T] [Algebra Λ T]
    [AddCommGroup Y] [Module T Y] [Module Λ Y] [IsScalarTower Λ T Y] (I : Ideal Λ)
    (θ0 : MvPowerSeries τ R →+* T)
    (hn : ∀ s (k : ℕ) (x : Y), ∃ d : ℕ, θ0 (MvPowerSeries.X s) ^ d • x ∈ (I ^ k • ⊤ : Submodule Λ Y)) :
    topNil I (fun i => ((Module.toModuleEnd Λ (S := T) Y).comp θ0) (MvPowerSeries.X i)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  show ∀ (i : τ) (j : ℕ), ∀ᶠ (r : ℕ) in Filter.atTop, _
  intro i j
  obtain ⟨d, hd⟩ := hn i j x
  rw [Filter.eventually_atTop]
  refine ⟨d, fun r hr => ?_⟩
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hr
  have key : (((Module.toModuleEnd Λ (S := T) Y).comp θ0) (MvPowerSeries.X i) ^ (d + e)) x
      = θ0 (MvPowerSeries.X i) ^ e • (θ0 (MvPowerSeries.X i) ^ d • x) := by
    rw [← map_pow, smul_smul, ← pow_add, Nat.add_comm e d, RingHom.comp_apply, map_pow θ0]
    rfl
  rw [key]
  let g : Y →ₗ[Λ] Y := Module.toModuleEnd Λ (S := T) Y (θ0 (MvPowerSeries.X i) ^ e)
  have hle : (I ^ j • ⊤ : Submodule Λ Y).map g ≤ I ^ j • ⊤ := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact hle ⟨_, hd, rfl⟩

/- English proof (translation)
Establish `hΛ : ∀ (c : Λ) (x : X), f (c • x) = c • f x`. Introduce `c x`. Establish `hc` using `hC (algebraMap Λ R c) x`. Rewrite `hc` using `[h, h', algebraMap_smul, algebraMap_smul]`. Conclude with `hc`.

Set `φ : X →ₗ[Λ] X'` to `{ toFun := f, map_add' := f.map_add, map_smul' := hΛ }`. Conclude with `psLin Λ R X X' τ ((Module.toModuleEnd Λ (S := S) X).comp θ) ((Module.toModuleEnd Λ (S := S') X').comp θ') φ (topNil_toModuleEnd_X_eq_top_of_pow_smul_mem _ θ hn) (topNil_toModuleEnd_X_eq_top_of_pow_smul_mem _ θ' hn') (fun a m => hC a m) (fun i m => hX i m) t x`.
-/
theorem psLin' {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ]
    {R τ S S' X X' : Type} [CommRing R] [Algebra Λ R] [Fintype τ] [CommRing S] [Algebra Λ S] [CommRing S'] [Algebra Λ S']
    [AddCommGroup X] [Module S X] [Module Λ X] [IsScalarTower Λ S X] [Module.Finite Λ X]
    [AddCommGroup X'] [Module S' X'] [Module Λ X'] [IsScalarTower Λ S' X'] [Module.Finite Λ X']
    (θ : MvPowerSeries τ R →+* S) (θ' : MvPowerSeries τ R →+* S')
    (h : ∀ c, θ (MvPowerSeries.C (algebraMap Λ R c)) = algebraMap Λ S c)
    (h' : ∀ c, θ' (MvPowerSeries.C (algebraMap Λ R c)) = algebraMap Λ S' c)
    (hn : ∀ s (k : ℕ) (x : X), ∃ d : ℕ, θ (MvPowerSeries.X s) ^ d • x ∈ (maximalIdeal Λ ^ k • ⊤ : Submodule Λ X))
    (hn' : ∀ s (k : ℕ) (x : X'), ∃ d : ℕ, θ' (MvPowerSeries.X s) ^ d • x ∈ (maximalIdeal Λ ^ k • ⊤ : Submodule Λ X'))
    (f : X →+ X') (hC : ∀ a x, f (θ (MvPowerSeries.C a) • x) = θ' (MvPowerSeries.C a) • f x)
    (hX : ∀ s x, f (θ (MvPowerSeries.X s) • x) = θ' (MvPowerSeries.X s) • f x) (t : MvPowerSeries τ R) (x : X) :
    f (θ t • x) = θ' t • f x := by
  have hΛ : ∀ (c : Λ) (x : X), f (c • x) = c • f x := by
    intro c x
    have hc := hC (algebraMap Λ R c) x
    rw [h, h', algebraMap_smul, algebraMap_smul] at hc
    exact hc
  let φ : X →ₗ[Λ] X' := { toFun := f, map_add' := f.map_add, map_smul' := hΛ }
  exact psLin Λ R X X' τ ((Module.toModuleEnd Λ (S := S) X).comp θ)
    ((Module.toModuleEnd Λ (S := S') X').comp θ') φ (topNil_toModuleEnd_X_eq_top_of_pow_smul_mem _ θ hn) (topNil_toModuleEnd_X_eq_top_of_pow_smul_mem _ θ' hn')
    (fun a m => hC a m) (fun i m => hX i m) t x

/- English proof (translation)
Establish `hinj : Function.Injective i` using `Function.LeftInverse.injective (g := pr) hpi`. Set `E : N ≃ₗ[Λ] LinearMap.range i` to `LinearEquiv.ofInjective i hinj`. Establish `hE : ∀ x, (E x : M) = i x` using `fun x => rfl`. Set `f : M →ₗ[Λ] LinearMap.range i` to `i.rangeRestrict.comp pr`. Establish `hf : ∀ x : LinearMap.range i, f x = x`.

Introduce and unpack `⟨_, y, rfl⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[f, hpi]`. Establish `hker : ∀ m, m ∈ LinearMap.ker f ↔ pr m = 0`. Introduce `m`.

Rewrite using `[LinearMap.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce `h0`. Apply `hinj` to reduce the goal to its premises. Establish `h1` using `congrArg Subtype.val h0`.

Simplify `h1` using `[f]`. Introduce `h0 show i.rangeRestrict (pr m) = 0`. Rewrite using `[h0, map_zero]`. Set `act : MvPowerSeries (Fin q × Fin n) Λ →ₐ[Λ] Module.End Λ (LinearMap.range i)` to `{ toFun := fun z => E.conj (Algebra.lsmul Λ Λ N (s z)) map_one' := by ext x; simp [LinearEquiv.conj_apply] map_mul' := by intro a b; ext x; simp [LinearEquiv.conj_apply, mul_smul] map_zero' := by ext x; simp [LinearEquiv.conj_apply] map_add' := by intro a b; ext x; simp [LinearEq …`. Establish `hact : ∀ z y, act z (E y) = E (s z • y)`.

Introduce `z y`. Use `show E.conj (Algebra.lsmul Λ Λ N (s z)) (E y) = _`. Simplify using `[LinearEquiv.conj_apply]`. Take `⟨rk, e, he⟩` from `freeSummand Λ l q n a M ρ (LinearMap.range i) (LinearMap.ker f) hl hm hP (LinearMap.isCompl_of_proj hf) (by`. Introduce and unpack `g _ ⟨y, rfl⟩`.

Conclude with `⟨pr (ρ g (i y)), by rw [hρ, hpi]⟩)`. Use the proof step `(by`. Introduce `g m hm0`. Rewrite `hm0`, the goal using `[hker]`. Apply `hinj` to reduce the goal to its premises.

Simplify using `[hρ, hm0])`. Use `act`. Use the proof step `(by`. Introduce and unpack `p ⟨_, y, rfl⟩`. Use `show ((act (1 + MvPowerSeries.X p)) (E y) : M) = _`.

Rewrite using `[hact, hE, hs])`. Use `⟨rk, E.toAddEquiv.trans e, fun z m => ?_⟩` and prove the remaining obligations. Use `show e (E (s z • m)) = z • e (E m)`. Rewrite using `[← hact, he]`.
-/
theorem freePart {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ]
    {l q n : ℕ} {a : Fin q → ℕ} {M S N : Type} [AddCommGroup M] [Module Λ M] [Module.Finite Λ M] [CommRing S] [Algebra Λ S]
    [AddCommGroup N] [Module S N] [Module Λ N] [IsScalarTower Λ S N] (ρ : Representation Λ (Del l n a) M) (hl : l.Prime)
    (hm : (l : Λ) ∈ maximalIdeal Λ) (hP : Module.Projective (MonoidAlgebra Λ (Del l n a)) ρ.asModule)
    (i : N →ₗ[Λ] M) (pr : M →ₗ[Λ] N) (hpi : ∀ x, pr (i x) = x) (hρ : ∀ g m, i (pr (ρ g m)) = ρ g (i (pr m)))
    (s : MvPowerSeries (Fin q × Fin n) Λ →ₐ[Λ] S)
    (hs : ∀ p x, i (s (1 + MvPowerSeries.X p) • x) = ρ (Pi.mulSingle p (Multiplicative.ofAdd 1)) (i x)) :
    ∃ (rk : ℕ) (e : N ≃+ (Fin rk → MvPowerSeries (Fin q × Fin n) Λ ⧸ delIdeal l Λ n a)), ∀ z m, e (s z • m) = z • e m := by
  have hinj : Function.Injective i := Function.LeftInverse.injective (g := pr) hpi
  let E : N ≃ₗ[Λ] LinearMap.range i := LinearEquiv.ofInjective i hinj
  have hE : ∀ x, (E x : M) = i x := fun x => rfl
  let f : M →ₗ[Λ] LinearMap.range i := i.rangeRestrict.comp pr
  have hf : ∀ x : LinearMap.range i, f x = x := by
    rintro ⟨_, y, rfl⟩
    apply Subtype.ext
    simp [f, hpi]
  have hker : ∀ m, m ∈ LinearMap.ker f ↔ pr m = 0 := by
    intro m
    rw [LinearMap.mem_ker]
    constructor
    · intro h0
      apply hinj
      have h1 := congrArg Subtype.val h0
      simpa [f] using h1
    · intro h0
      show i.rangeRestrict (pr m) = 0
      rw [h0, map_zero]
  let act : MvPowerSeries (Fin q × Fin n) Λ →ₐ[Λ] Module.End Λ (LinearMap.range i) :=
    { toFun := fun z => E.conj (Algebra.lsmul Λ Λ N (s z))
      map_one' := by ext x; simp [LinearEquiv.conj_apply]
      map_mul' := by intro a b; ext x; simp [LinearEquiv.conj_apply, mul_smul]
      map_zero' := by ext x; simp [LinearEquiv.conj_apply]
      map_add' := by intro a b; ext x; simp [LinearEquiv.conj_apply, add_smul]
      commutes' := by intro c; ext x; simp [LinearEquiv.conj_apply, algebraMap_smul] }
  have hact : ∀ z y, act z (E y) = E (s z • y) := by
    intro z y
    show E.conj (Algebra.lsmul Λ Λ N (s z)) (E y) = _
    simp [LinearEquiv.conj_apply]
  obtain ⟨rk, e, he⟩ := freeSummand Λ l q n a M ρ (LinearMap.range i) (LinearMap.ker f) hl hm hP
    (LinearMap.isCompl_of_proj hf)
    (by
      rintro g _ ⟨y, rfl⟩
      exact ⟨pr (ρ g (i y)), by rw [hρ, hpi]⟩)
    (by
      intro g m hm0
      rw [hker] at hm0 ⊢
      apply hinj
      simp [hρ, hm0])
    act
    (by
      rintro p ⟨_, y, rfl⟩
      show ((act (1 + MvPowerSeries.X p)) (E y) : M) = _
      rw [hact, hE, hs])
  refine ⟨rk, E.toAddEquiv.trans e, fun z m => ?_⟩
  show e (E (s z • m)) = z • e (E m)
  rw [← hact, he]

/- English proof (translation)
Rewrite using `[← Finset.univ_prod_mulSingle g]`. Use `Submonoid.prod_mem S fun p _ => ?_` and prove the remaining obligations. Use `haveI : NeZero (l ^ a p.1) := ⟨pow_ne_zero _ hl.ne_zero⟩`. Establish `hg : g p = (Multiplicative.ofAdd (1 : ZMod (l ^ a p.1))) ^ (Multiplicative.toAdd (g p)).val`. Rewrite using `[← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val]`.

Both sides reduce to the same expression. Rewrite using `[hg, Pi.mulSingle_pow]`. Conclude with `Submonoid.pow_mem S (h p) _`.
-/
theorem del_gen {l q n : ℕ} (hl : l.Prime) {a : Fin q → ℕ} (S : Submonoid (Del l n a))
    (h : ∀ p, (Pi.mulSingle p (Multiplicative.ofAdd 1) : Del l n a) ∈ S) (g : Del l n a) : g ∈ S := by
  rw [← Finset.univ_prod_mulSingle g]
  refine Submonoid.prod_mem S fun p _ => ?_
  haveI : NeZero (l ^ a p.1) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hg : g p = (Multiplicative.ofAdd (1 : ZMod (l ^ a p.1))) ^ (Multiplicative.toAdd (g p)).val := by
    rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val]
    rfl
  rw [hg, Pi.mulSingle_pow]
  exact Submonoid.pow_mem S (h p) _

/- English proof (translation)
Establish `hle : f.ker ≤ g.ker` using `fun a ha => AddMonoidHom.mem_ker.mpr (h a (AddMonoidHom.mem_ker.mp ha))`. Set `eq` to `QuotientAddGroup.quotientKerEquivOfSurjective f hf`. Use `⟨(QuotientAddGroup.lift f.ker g hle).comp eq.symm.toAddMonoidHom, fun a => ?_⟩` and prove the remaining obligations. Establish `hq : eq.symm (f a) = (a : A ⧸ f.ker)`. Apply `eq.injective` to reduce the goal to its premises.

Rewrite using `[AddEquiv.apply_symm_apply]`. Both sides reduce to the same expression. Simplify using `only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, hq]`. Both sides reduce to the same expression.
-/
theorem exLift {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (f : A →+ B)
    (hf : Function.Surjective f) (g : A →+ C) (h : ∀ a, f a = 0 → g a = 0) : ∃ k : B →+ C, ∀ a, k (f a) = g a := by
  have hle : f.ker ≤ g.ker := fun a ha => AddMonoidHom.mem_ker.mpr (h a (AddMonoidHom.mem_ker.mp ha))
  let eq := QuotientAddGroup.quotientKerEquivOfSurjective f hf
  refine ⟨(QuotientAddGroup.lift f.ker g hle).comp eq.symm.toAddMonoidHom, fun a => ?_⟩
  have hq : eq.symm (f a) = (a : A ⧸ f.ker) := by
    apply eq.injective
    rw [AddEquiv.apply_symm_apply]
    rfl
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, hq]
  rfl

/- English proof (translation)
Use `set J : Submodule S N := (Ideal.span (Set.range y) • ⊤ : Submodule S N) with hJ`. Establish `hkill : ∀ p m, tr (act1 (MvPolynomial.X (Sum.inr p)) m) = 0`. Introduce `p m`. Rewrite using `[← LinearMap.mem_ker, hker]`. Conclude with `Submodule.mem_iSup_of_mem p ⟨m, rfl⟩`.

Establish `hC1 : ∀ (a : R) (m : M), act1 (MvPolynomial.C a) m = a • m`. Introduce `a m`. Rewrite using `[← MvPolynomial.algebraMap_eq, act1.commutes]`. Both sides reduce to the same expression. Establish `hCw : ∀ (a : R) (w : W), actw (MvPolynomial.C a) w = a • w`.

Introduce `a w`. Rewrite using `[← MvPolynomial.algebraMap_eq, actw.commutes]`. Both sides reduce to the same expression. Establish `htr : ∀ t m, tr (act1 (MvPolynomial.rename Sum.inl t) m) = actw t (tr m)`. Introduce `t`.

Proceed by induction on `t using MvPolynomial.induction_on`. Name the introduced variables `a`. Introduce `m`. Rewrite using `[MvPolynomial.rename_C, hC1, hCw, map_smul]`. Name the introduced variables `p1 p2 hp1 hp2`.

Introduce `m`. Simplify using `only [map_add, LinearMap.add_apply, hp1, hp2]`. Name the introduced variables `p1 s hp1`. Introduce `m`. Simplify using `only [map_mul, MvPolynomial.rename_X, Module.End.mul_apply]`.

Rewrite using `[hp1, hu]`. Establish `hJkill : ∀ n ∈ J, tr (i n) = 0`. Introduce `n hn`. Establish `key : ∀ b ∈ Ideal.span (Set.range y), ∀ n : N, tr (i (b • n)) = 0`. Introduce `b hb`.

Use `Submodule.span_induction (p := fun b _ => ∀ n : N, tr (i (b • n)) = 0) ?_ ?_ ?_ ?_ hb` and prove the remaining obligations. Introduce and unpack `_ ⟨p, rfl⟩ n`. Rewrite using `[hy, hi]`. Conclude with `hkill p _`. Introduce `n`.

Rewrite using `[zero_smul, map_zero, map_zero]`. Introduce `x w _ _ hx hw n`. Rewrite using `[add_smul, map_add, map_add, hx, hw, add_zero]`. Introduce `a x _ hx n`. Rewrite using `[smul_eq_mul, mul_comm, mul_smul]`.

Conclude with `hx _`. Use `Submodule.smul_induction_on hn (fun b hb n _ => key b hb n) ?_` and prove the remaining obligations. Introduce `a b ha hb`. Rewrite using `[map_add, map_add, ha, hb, add_zero]`. Establish `hprJ : ∀ m, tr m = 0 → pr m ∈ J`.

Introduce `m hm`. Rewrite `hm` using `[← LinearMap.mem_ker, hker]`. Use `Submodule.iSup_induction _ (motive := fun m => pr m ∈ J) hm ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `p _ ⟨m', rfl⟩ show pr (act1 (MvPolynomial.X (Sum.inr p)) m') ∈ J`. Rewrite using `[hpr, ← hy]`.

Conclude with `Submodule.smul_mem_smul (Ideal.subset_span ⟨p, rfl⟩) Submodule.mem_top`. Use `show pr 0 ∈ J`. Rewrite using `[map_zero]`. Conclude with `Submodule.zero_mem _`. Introduce `a b ha hb show pr (a + b) ∈ J`.

Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ ha hb`. Take `⟨j, hj0⟩` from `exLift J.mkQ.toAddMonoidHom J.mkQ_surjective (tr.toAddMonoidHom.comp i.toAddMonoidHom) (fun a ha => hJkill a ((Submodule.Quotient.mk_eq_zero J).mp ha))`. Establish `hj : ∀ n, j (J.mkQ n) = tr (i n)` using `hj0`. Take `⟨κ, hκ0⟩` from `exLift tr.toAddMonoidHom hsurj (J.mkQ.toAddMonoidHom.comp pr.toAddMonoidHom) (fun a ha => (Submodule.Quotient.mk_eq_zero J).mpr (hprJ a ha))`.

Establish `hκ : ∀ m, κ (tr m) = J.mkQ (pr m)` using `hκ0`. Use `⟨j, κ, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `t x`. Take `⟨n, rfl⟩` from `J.mkQ_surjective x`. Rewrite using `[← map_smul J.mkQ, hj, hj, hi, htr]`.

Introduce `t v`. Take `⟨m, rfl⟩` from `hsurj v`. Rewrite using `[← htr, hκ, hκ, hpr, map_smul]`. Introduce `x`. Take `⟨n, rfl⟩` from `J.mkQ_surjective x`.

Rewrite using `[hj, hκ, hpi]`. Introduce `v haveI : Module.Finite Λ W := Module.Finite.of_surjective (tr.restrictScalars Λ) hsurj`. Set `T : σ ⊕ σ → Module.End Λ M` to `fun s => (act1 (MvPolynomial.X s - MvPolynomial.C (Sum.elim ut 0 s))).restrictScalars Λ`. Set `T' : σ ⊕ σ → Module.End Λ W` to `Sum.elim (fun p => (actw (MvPolynomial.X p - MvPolynomial.C (ut p))).restrictScalars Λ) (fun _ => 0)`. Establish `hcT : ∀ s s', Commute (T s) (T s')`.

Introduce `s s'`. Use `show T s * T s' = T s' * T s`. Use `LinearMap.ext fun m => ?_` and prove the remaining obligations. Use `show act1 _ (act1 _ m) = act1 _ (act1 _ m)`. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]`.

Establish `hcT' : ∀ s s', Commute (T' s) (T' s')`. Introduce and unpack `(p | p) (p' | p')`. Use `show T' (Sum.inl p) * T' (Sum.inl p') = T' (Sum.inl p') * T' (Sum.inl p)`. Use `LinearMap.ext fun w => ?_` and prove the remaining obligations. Use `show actw _ (actw _ w) = actw _ (actw _ w)`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]`. Conclude with `Commute.zero_right _`. Conclude with `Commute.zero_left _`. Conclude with `Commute.zero_left _`. Establish `hf : ∀ s m, tr.restrictScalars Λ (T s m) = T' s (tr.restrictScalars Λ m)`.

Introduce and unpack `(p | p) m`. Use `show tr (act1 (MvPolynomial.X (Sum.inl p) - MvPolynomial.C (ut p)) m) = actw (MvPolynomial.X p - MvPolynomial.C (ut p)) (tr m)`. Establish `hren : MvPolynomial.rename Sum.inl (MvPolynomial.X p - MvPolynomial.C (ut p) : MvPolynomial σ R) = (MvPolynomial.X (Sum.inl p) - MvPolynomial.C (ut p) : MvPolynomial (σ ⊕ σ) R)`. Simplify using the standard rewrite rules. Rewrite using `[← htr, hren]`.

Use `show tr (act1 (MvPolynomial.X (Sum.inr p) - MvPolynomial.C 0) m) = 0`. Rewrite using `[map_zero, sub_zero]`. Conclude with `hkill p m`. Take `⟨hmap, -⟩` from `topNil_map Λ (σ ⊕ σ) M W T T' hcT hcT' (tr.restrictScalars Λ) hf`. Establish `hrange : LinearMap.range (tr.restrictScalars Λ) = ⊤` using `LinearMap.range_eq_top.mpr hsurj`.

Rewrite `hmap` using `[hrange, inf_top_eq]`. Establish `hT : topNil (maximalIdeal Λ) T = LinearMap.range i` using `hr.symm`. Establish `hTW : v ∈ topNil (maximalIdeal Λ) (fun p => (actw (MvPolynomial.X p - MvPolynomial.C (ut p))).restrictScalars Λ) ↔ v ∈ topNil (maximalIdeal Λ) T'`. Rewrite using `[mem_topNil, mem_topNil]`. Prove the components needed by the constructor for the conclusion.

Introduce `hv s k`. Break down `s with p | p` into its components or cases. Conclude with `hv p k`. Rewrite using `[Filter.eventually_atTop]`. Use `⟨1, fun r hr => ?_⟩` and prove the remaining obligations.

Take `⟨r', rfl⟩` from `Nat.exists_eq_add_of_le hr`. Use `show ((0 : Module.End Λ W) ^ (1 + r')) v ∈ _`. Rewrite using `[zero_pow (by omega), LinearMap.zero_apply]`. Conclude with `Submodule.zero_mem _`. Introduce `hv p k`.

Conclude with `hv (Sum.inl p) k`. Rewrite using `[hTW, ← hmap, hT]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, ⟨n, rfl⟩, rfl⟩`. Conclude with `⟨J.mkQ n, hj n⟩`.

Introduce and unpack `⟨x, rfl⟩`. Take `⟨n, rfl⟩` from `J.mkQ_surjective x`. Conclude with `⟨i n, ⟨n, rfl⟩, (hj n).symm⟩`.
-/
theorem quotPart {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ]
    {R σ S M W N : Type} [CommRing R] [Algebra Λ R] [CommRing S] [AddCommGroup M] [Module R M] [Module Λ M]
    [IsScalarTower Λ R M] [Module.Finite Λ M] [AddCommGroup W] [Module R W] [Module Λ W] [IsScalarTower Λ R W]
    [AddCommGroup N] [Module S N] [Module Λ N]
    (act1 : MvPolynomial (σ ⊕ σ) R →ₐ[R] Module.End R M) (actw : MvPolynomial σ R →ₐ[R] Module.End R W)
    (tr : M →ₗ[R] W) (hsurj : Function.Surjective tr)
    (hker : LinearMap.ker tr = ⨆ p : σ, LinearMap.range (act1 (MvPolynomial.X (.inr p))))
    (hu : ∀ p m, tr (act1 (MvPolynomial.X (.inl p)) m) = actw (MvPolynomial.X p) (tr m)) (ut : σ → R)
    (ev : MvPolynomial (σ ⊕ σ) R →+* S) (i : N →ₗ[Λ] M) (pr : M →ₗ[Λ] N) (hpi : ∀ x, pr (i x) = x)
    (hi : ∀ t x, i (ev t • x) = act1 t (i x)) (hpr : ∀ t m, pr (act1 t m) = ev t • pr m)
    (hr : LinearMap.range i = topNil (maximalIdeal Λ)
      fun s => (act1 (MvPolynomial.X s - MvPolynomial.C (Sum.elim ut 0 s))).restrictScalars Λ)
    (y : σ → S) (hy : ∀ p, y p = ev (MvPolynomial.X (.inr p))) :
    ∃ (j : (N ⧸ (Ideal.span (Set.range y) • ⊤ : Submodule S N)) →+ W)
      (κ : W →+ N ⧸ (Ideal.span (Set.range y) • ⊤ : Submodule S N)),
      (∀ t x, j (ev (MvPolynomial.rename Sum.inl t) • x) = actw t (j x)) ∧
      (∀ t v, κ (actw t v) = ev (MvPolynomial.rename Sum.inl t) • κ v) ∧ (∀ x, κ (j x) = x) ∧
      ∀ v, v ∈ topNil (maximalIdeal Λ) (fun p => (actw (MvPolynomial.X p - MvPolynomial.C (ut p))).restrictScalars Λ) ↔
        ∃ x, j x = v := by
  set J : Submodule S N := (Ideal.span (Set.range y) • ⊤ : Submodule S N) with hJ
  have hkill : ∀ p m, tr (act1 (MvPolynomial.X (Sum.inr p)) m) = 0 := by
    intro p m
    rw [← LinearMap.mem_ker, hker]
    exact Submodule.mem_iSup_of_mem p ⟨m, rfl⟩
  have hC1 : ∀ (a : R) (m : M), act1 (MvPolynomial.C a) m = a • m := by
    intro a m
    rw [← MvPolynomial.algebraMap_eq, act1.commutes]
    rfl
  have hCw : ∀ (a : R) (w : W), actw (MvPolynomial.C a) w = a • w := by
    intro a w
    rw [← MvPolynomial.algebraMap_eq, actw.commutes]
    rfl
  have htr : ∀ t m, tr (act1 (MvPolynomial.rename Sum.inl t) m) = actw t (tr m) := by
    intro t
    induction t using MvPolynomial.induction_on
    · rename_i a
      intro m
      rw [MvPolynomial.rename_C, hC1, hCw, map_smul]
    · rename_i p1 p2 hp1 hp2
      intro m
      simp only [map_add, LinearMap.add_apply, hp1, hp2]
    · rename_i p1 s hp1
      intro m
      simp only [map_mul, MvPolynomial.rename_X, Module.End.mul_apply]
      rw [hp1, hu]
  have hJkill : ∀ n ∈ J, tr (i n) = 0 := by
    intro n hn
    have key : ∀ b ∈ Ideal.span (Set.range y), ∀ n : N, tr (i (b • n)) = 0 := by
      intro b hb
      refine Submodule.span_induction (p := fun b _ => ∀ n : N, tr (i (b • n)) = 0) ?_ ?_ ?_ ?_ hb
      · rintro _ ⟨p, rfl⟩ n
        rw [hy, hi]
        exact hkill p _
      · intro n
        rw [zero_smul, map_zero, map_zero]
      · intro x w _ _ hx hw n
        rw [add_smul, map_add, map_add, hx, hw, add_zero]
      · intro a x _ hx n
        rw [smul_eq_mul, mul_comm, mul_smul]
        exact hx _
    refine Submodule.smul_induction_on hn (fun b hb n _ => key b hb n) ?_
    intro a b ha hb
    rw [map_add, map_add, ha, hb, add_zero]
  have hprJ : ∀ m, tr m = 0 → pr m ∈ J := by
    intro m hm
    rw [← LinearMap.mem_ker, hker] at hm
    refine Submodule.iSup_induction _ (motive := fun m => pr m ∈ J) hm ?_ ?_ ?_
    · rintro p _ ⟨m', rfl⟩
      show pr (act1 (MvPolynomial.X (Sum.inr p)) m') ∈ J
      rw [hpr, ← hy]
      exact Submodule.smul_mem_smul (Ideal.subset_span ⟨p, rfl⟩) Submodule.mem_top
    · show pr 0 ∈ J
      rw [map_zero]
      exact Submodule.zero_mem _
    · intro a b ha hb
      show pr (a + b) ∈ J
      rw [map_add]
      exact Submodule.add_mem _ ha hb
  obtain ⟨j, hj0⟩ := exLift J.mkQ.toAddMonoidHom J.mkQ_surjective
    (tr.toAddMonoidHom.comp i.toAddMonoidHom)
    (fun a ha => hJkill a ((Submodule.Quotient.mk_eq_zero J).mp ha))
  have hj : ∀ n, j (J.mkQ n) = tr (i n) := hj0
  obtain ⟨κ, hκ0⟩ := exLift tr.toAddMonoidHom hsurj (J.mkQ.toAddMonoidHom.comp pr.toAddMonoidHom)
    (fun a ha => (Submodule.Quotient.mk_eq_zero J).mpr (hprJ a ha))
  have hκ : ∀ m, κ (tr m) = J.mkQ (pr m) := hκ0
  refine ⟨j, κ, ?_, ?_, ?_, ?_⟩
  · intro t x
    obtain ⟨n, rfl⟩ := J.mkQ_surjective x
    rw [← map_smul J.mkQ, hj, hj, hi, htr]
  · intro t v
    obtain ⟨m, rfl⟩ := hsurj v
    rw [← htr, hκ, hκ, hpr, map_smul]
  · intro x
    obtain ⟨n, rfl⟩ := J.mkQ_surjective x
    rw [hj, hκ, hpi]
  · intro v
    haveI : Module.Finite Λ W := Module.Finite.of_surjective (tr.restrictScalars Λ) hsurj
    let T : σ ⊕ σ → Module.End Λ M := fun s =>
      (act1 (MvPolynomial.X s - MvPolynomial.C (Sum.elim ut 0 s))).restrictScalars Λ
    let T' : σ ⊕ σ → Module.End Λ W :=
      Sum.elim (fun p => (actw (MvPolynomial.X p - MvPolynomial.C (ut p))).restrictScalars Λ) (fun _ => 0)
    have hcT : ∀ s s', Commute (T s) (T s') := by
      intro s s'
      show T s * T s' = T s' * T s
      refine LinearMap.ext fun m => ?_
      show act1 _ (act1 _ m) = act1 _ (act1 _ m)
      rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]
    have hcT' : ∀ s s', Commute (T' s) (T' s') := by
      rintro (p | p) (p' | p')
      · show T' (Sum.inl p) * T' (Sum.inl p') = T' (Sum.inl p') * T' (Sum.inl p)
        refine LinearMap.ext fun w => ?_
        show actw _ (actw _ w) = actw _ (actw _ w)
        rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]
      · exact Commute.zero_right _
      · exact Commute.zero_left _
      · exact Commute.zero_left _
    have hf : ∀ s m, tr.restrictScalars Λ (T s m) = T' s (tr.restrictScalars Λ m) := by
      rintro (p | p) m
      · show tr (act1 (MvPolynomial.X (Sum.inl p) - MvPolynomial.C (ut p)) m) =
          actw (MvPolynomial.X p - MvPolynomial.C (ut p)) (tr m)
        have hren : MvPolynomial.rename Sum.inl (MvPolynomial.X p - MvPolynomial.C (ut p) : MvPolynomial σ R) =
            (MvPolynomial.X (Sum.inl p) - MvPolynomial.C (ut p) : MvPolynomial (σ ⊕ σ) R) := by
          simp
        rw [← htr, hren]
      · show tr (act1 (MvPolynomial.X (Sum.inr p) - MvPolynomial.C 0) m) = 0
        rw [map_zero, sub_zero]
        exact hkill p m
    obtain ⟨hmap, -⟩ := topNil_map Λ (σ ⊕ σ) M W T T' hcT hcT' (tr.restrictScalars Λ) hf
    have hrange : LinearMap.range (tr.restrictScalars Λ) = ⊤ := LinearMap.range_eq_top.mpr hsurj
    rw [hrange, inf_top_eq] at hmap
    have hT : topNil (maximalIdeal Λ) T = LinearMap.range i := hr.symm
    have hTW : v ∈ topNil (maximalIdeal Λ)
        (fun p => (actw (MvPolynomial.X p - MvPolynomial.C (ut p))).restrictScalars Λ) ↔
        v ∈ topNil (maximalIdeal Λ) T' := by
      rw [mem_topNil, mem_topNil]
      constructor
      · intro hv s k
        rcases s with p | p
        · exact hv p k
        · rw [Filter.eventually_atTop]
          refine ⟨1, fun r hr => ?_⟩
          obtain ⟨r', rfl⟩ := Nat.exists_eq_add_of_le hr
          show ((0 : Module.End Λ W) ^ (1 + r')) v ∈ _
          rw [zero_pow (by omega), LinearMap.zero_apply]
          exact Submodule.zero_mem _
      · intro hv p k
        exact hv (Sum.inl p) k
    rw [hTW, ← hmap, hT]
    constructor
    · rintro ⟨m, ⟨n, rfl⟩, rfl⟩
      exact ⟨J.mkQ n, hj n⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨n, rfl⟩ := J.mkQ_surjective x
      exact ⟨i n, ⟨n, rfl⟩, (hj n).symm⟩

/- English proof (translation)
Take `⟨k, φ, hφ⟩` from `Module.Finite.exists_fin' B A`. Set `F : (Fin k → M) →ₗ[Λ] A ⊗[B] M` to `∑ i, ((TensorProduct.mk B A M (φ (fun j => if i = j then 1 else 0))).restrictScalars Λ).comp (LinearMap.proj i)`. Use `Module.Finite.of_surjective F ?_` and prove the remaining obligations. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`.

Consider the case `zero => exact ⟨0, map_zero F⟩`. Consider the case `tmul a m`. Take `⟨v, rfl⟩` from `hφ a`. Use `⟨fun i => v i • m, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.pi_apply_eq_sum_univ φ v, TensorProduct.sum_tmul]`.

Simplify using `[F, LinearMap.sum_apply, TensorProduct.smul_tmul]`. Consider the case `add x y hx hy`. Take `⟨u, rfl⟩` from `hx`. Take `⟨w, rfl⟩` from `hy`. Conclude with `⟨u + w, map_add F u w⟩`.
-/
theorem finTens {Λ B A M : Type} [CommRing Λ] [CommRing B] [Algebra Λ B] [CommRing A] [Algebra B A] [Algebra Λ A]
    [IsScalarTower Λ B A] [AddCommGroup M] [Module B M] [Module Λ M] [IsScalarTower Λ B M] [Module.Finite B A]
    [Module.Finite Λ M] : Module.Finite Λ (A ⊗[B] M) := by
  obtain ⟨k, φ, hφ⟩ := Module.Finite.exists_fin' B A
  let F : (Fin k → M) →ₗ[Λ] A ⊗[B] M :=
    ∑ i, ((TensorProduct.mk B A M (φ (fun j => if i = j then 1 else 0))).restrictScalars Λ).comp
      (LinearMap.proj i)
  refine Module.Finite.of_surjective F ?_
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero F⟩
  | tmul a m =>
    obtain ⟨v, rfl⟩ := hφ a
    refine ⟨fun i => v i • m, ?_⟩
    rw [LinearMap.pi_apply_eq_sum_univ φ v, TensorProduct.sum_tmul]
    simp [F, LinearMap.sum_apply, TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨w, rfl⟩ := hy
    exact ⟨u + w, map_add F u w⟩

/- English proof (translation)
Establish `hz : ∀ a, π a = 0 → e * a = 0`. Introduce `a ha`. Establish `hmem : a ∈ Ideal.span {1 - e}` using `hker ▸ (RingHom.mem_ker.mpr ha)`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp hmem`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨s, hs⟩` from `exLift π.toRingHom.toAddMonoidHom hπ (AddMonoidHom.mulLeft e) (fun a ha => hz a ha)`. Establish `hs' : ∀ a, s (π a) = e * a` using `hs`. Set `sL : A' →ₗ[B] A` to `{ toFun := s map_add' := s.map_add map_smul' := by`. Introduce `b x`. Take `⟨a, rfl⟩` from `hπ x`.

Rewrite using `[← map_smul, hs', hs', RingHom.id_apply, mul_smul_comm] }`. Establish `hsL : ∀ a, sL (π a) = e * a` using `hs'`. Use `⟨(sL.rTensor M).toAddMonoidHom, fun z => ?_⟩` and prove the remaining obligations. Use `show sL.rTensor M (π.toLinearMap.rTensor M z) = e • z`. Rewrite using `[← LinearMap.comp_apply, ← LinearMap.rTensor_comp]`.

Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a m`. Rewrite using `[LinearMap.rTensor_tmul, LinearMap.comp_apply, AlgHom.toLinearMap_apply, hsL, TensorProduct.smul_tmul', smul_eq_mul]`. Consider the case `add x y hx hy => rw [map_add, smul_add, hx, hy]`.
-/
theorem tensSec {B A A' M : Type} [CommRing B] [CommRing A] [Algebra B A] [CommRing A'] [Algebra B A']
    [AddCommGroup M] [Module B M] (π : A →ₐ[B] A') (hπ : Function.Surjective π) (e : A) (he : IsIdempotentElem e)
    (hker : RingHom.ker π = Ideal.span {1 - e}) :
    ∃ ι : A' ⊗[B] M →+ A ⊗[B] M, ∀ z, ι (π.toLinearMap.rTensor M z) = e • z := by
  have hz : ∀ a, π a = 0 → e * a = 0 := by
    intro a ha
    have hmem : a ∈ Ideal.span {1 - e} := hker ▸ (RingHom.mem_ker.mpr ha)
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hmem
    calc e * (c * (1 - e)) = c * (e - e * e) := by ring
      _ = 0 := by rw [he.eq, sub_self, mul_zero]
  obtain ⟨s, hs⟩ := exLift π.toRingHom.toAddMonoidHom hπ (AddMonoidHom.mulLeft e) (fun a ha => hz a ha)
  have hs' : ∀ a, s (π a) = e * a := hs
  let sL : A' →ₗ[B] A :=
    { toFun := s
      map_add' := s.map_add
      map_smul' := by
        intro b x
        obtain ⟨a, rfl⟩ := hπ x
        rw [← map_smul, hs', hs', RingHom.id_apply, mul_smul_comm] }
  have hsL : ∀ a, sL (π a) = e * a := hs'
  refine ⟨(sL.rTensor M).toAddMonoidHom, fun z => ?_⟩
  show sL.rTensor M (π.toLinearMap.rTensor M z) = e • z
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    rw [LinearMap.rTensor_tmul, LinearMap.comp_apply, AlgHom.toLinearMap_apply, hsL,
      TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [map_add, smul_add, hx, hy]

/- English proof (translation)
Set `g : V →ₗ[Λ] V'` to `{ toFun := f, map_add' := f.map_add, map_smul' := hf }`. Establish `hle : (I • ⊤ : Submodule Λ V).map g ≤ I • ⊤`. Rewrite using `[Submodule.map_smul'']`. Conclude with `Submodule.smul_mono le_rfl le_top`. Conclude with `hle ⟨v, hv, rfl⟩`.
-/
theorem nilMap {Λ V V' : Type} [CommRing Λ] [AddCommGroup V] [Module Λ V] [AddCommGroup V'] [Module Λ V']
    (I : Ideal Λ) (f : V →+ V') (hf : ∀ (c : Λ) v, f (c • v) = c • f v) {v : V} (hv : v ∈ (I • ⊤ : Submodule Λ V)) :
    f v ∈ (I • ⊤ : Submodule Λ V') := by
  let g : V →ₗ[Λ] V' := { toFun := f, map_add' := f.map_add, map_smul' := hf }
  have hle : (I • ⊤ : Submodule Λ V).map g ≤ I • ⊤ := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact hle ⟨v, hv, rfl⟩

/- English proof (translation)
Establish `hroot : ∀ j i, IsIntegral B (MSplitAlg.root P n j i)`. Introduce `j i`. Use `⟨P j, hm j, ?_⟩` and prove the remaining obligations. Establish `hD : Polynomial.map (Ideal.Quotient.mk (mSplitIdeal P n)) (∏ i', (Polynomial.X - Polynomial.C (MvPolynomial.X (j, i'))) - Polynomial.map MvPolynomial.C (P j)) = 0`. Use extensionality with `k`.

Rewrite using `[Polynomial.coeff_map, Polynomial.coeff_zero, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.subset_span ⟨(j, k), rfl⟩`. Simplify using `only [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_X, Polynomial.map_C, Polynomial.map_map] at hD`. Rewrite `hD` using `[sub_eq_zero]`. Rewrite using `[Polynomial.eval₂_eq_eval_map]`.

Establish `hC : (Ideal.Quotient.mk (mSplitIdeal P n)).comp MvPolynomial.C = algebraMap B (MSplitAlg P n)` using `rfl`. Rewrite using `[← hC, ← hD, Polynomial.eval_prod]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (by simp [MSplitAlg.root])`. Establish `hint : Algebra.IsIntegral B (MSplitAlg P n)`. Prove the components needed by the constructor for the conclusion.

Introduce `x`. Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Proceed by induction on `p using MvPolynomial.induction_on`. Conclude with `isIntegral_algebraMap`. Rewrite using `[map_add]`.

Conclude with `IsIntegral.add ‹_› ‹_›`. Rewrite using `[map_mul]`. Conclude with `IsIntegral.mul ‹_› (hroot _ _)`. Establish `hft : Algebra.FiniteType B (MSplitAlg P n)` using `Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ B (mSplitIdeal P n)) (Ideal.Quotient.mkₐ_surjective B _)`. Conclude with `Algebra.IsIntegral.finite`.
-/
private theorem module_finite_mSplitAlg_of_monic {B κ : Type} [CommRing B] [Finite κ] {n : ℕ} (P : κ → Polynomial B)
    (hm : ∀ j, (P j).Monic) : Module.Finite B (MSplitAlg P n) := by
  have hroot : ∀ j i, IsIntegral B (MSplitAlg.root P n j i) := by
    intro j i
    refine ⟨P j, hm j, ?_⟩
    have hD : Polynomial.map (Ideal.Quotient.mk (mSplitIdeal P n))
        (∏ i', (Polynomial.X - Polynomial.C (MvPolynomial.X (j, i'))) -
          Polynomial.map MvPolynomial.C (P j)) = 0 := by
      ext k
      rw [Polynomial.coeff_map, Polynomial.coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span ⟨(j, k), rfl⟩
    simp only [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_X, Polynomial.map_C,
      Polynomial.map_map] at hD
    rw [sub_eq_zero] at hD
    rw [Polynomial.eval₂_eq_eval_map]
    have hC : (Ideal.Quotient.mk (mSplitIdeal P n)).comp MvPolynomial.C = algebraMap B (MSplitAlg P n) := rfl
    rw [← hC, ← hD, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [MSplitAlg.root])
  have hint : Algebra.IsIntegral B (MSplitAlg P n) := by
    constructor
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction p using MvPolynomial.induction_on
    · exact isIntegral_algebraMap
    · rw [map_add]
      exact IsIntegral.add ‹_› ‹_›
    · rw [map_mul]
      exact IsIntegral.mul ‹_› (hroot _ _)
  have hft : Algebra.FiniteType B (MSplitAlg P n) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ B (mSplitIdeal P n))
      (Ideal.Quotient.mkₐ_surjective B _)
  exact Algebra.IsIntegral.finite

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hy`. Establish `key : ∀ b ∈ Ideal.map (algebraMap Λ B) I, ∀ z : Y, b • z ∈ (I • ⊤ : Submodule Λ Y)`. Introduce `b hb`. Use `Submodule.span_induction (p := fun b _ => ∀ z : Y, b • z ∈ (I • ⊤ : Submodule Λ Y)) ?_ ?_ ?_ ?_ hb` and prove the remaining obligations.

Introduce and unpack `_ ⟨c, hc, rfl⟩ z`. Rewrite using `[algebraMap_smul]`. Conclude with `Submodule.smul_mem_smul hc Submodule.mem_top`. Introduce `z`. Rewrite using `[zero_smul]`.

Conclude with `Submodule.zero_mem _`. Introduce `x w _ _ hx hw z`. Rewrite using `[add_smul]`. Conclude with `Submodule.add_mem _ (hx z) (hw z)`. Introduce `a x _ hx z`.

Rewrite using `[smul_eq_mul, mul_comm, mul_smul]`. Conclude with `hx _`. Conclude with `Submodule.smul_induction_on hy (fun b hb z _ => key b hb z) (fun _ _ h1 h2 => Submodule.add_mem _ h1 h2)`. Introduce `hy`. Use `Submodule.smul_induction_on hy (fun c hc z _ => ?_) (fun _ _ h1 h2 => Submodule.add_mem _ h1 h2)` and prove the remaining obligations.

Rewrite using `[← algebraMap_smul B c z]`. Conclude with `Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hc) Submodule.mem_top`.
-/
private theorem mem_map_algebraMap_smul_top_iff_mem_smul_top {Λ B Y : Type} [CommRing Λ] [CommRing B] [Algebra Λ B] [AddCommGroup Y]
    [Module B Y] [Module Λ Y] [IsScalarTower Λ B Y] (I : Ideal Λ) (y : Y) :
    y ∈ (Ideal.map (algebraMap Λ B) I • ⊤ : Submodule B Y) ↔ y ∈ (I • ⊤ : Submodule Λ Y) := by
  constructor
  · intro hy
    have key : ∀ b ∈ Ideal.map (algebraMap Λ B) I, ∀ z : Y, b • z ∈ (I • ⊤ : Submodule Λ Y) := by
      intro b hb
      refine Submodule.span_induction (p := fun b _ => ∀ z : Y, b • z ∈ (I • ⊤ : Submodule Λ Y))
        ?_ ?_ ?_ ?_ hb
      · rintro _ ⟨c, hc, rfl⟩ z
        rw [algebraMap_smul]
        exact Submodule.smul_mem_smul hc Submodule.mem_top
      · intro z
        rw [zero_smul]
        exact Submodule.zero_mem _
      · intro x w _ _ hx hw z
        rw [add_smul]
        exact Submodule.add_mem _ (hx z) (hw z)
      · intro a x _ hx z
        rw [smul_eq_mul, mul_comm, mul_smul]
        exact hx _
    exact Submodule.smul_induction_on hy (fun b hb z _ => key b hb z)
      (fun _ _ h1 h2 => Submodule.add_mem _ h1 h2)
  · intro hy
    refine Submodule.smul_induction_on hy (fun c hc z _ => ?_) (fun _ _ h1 h2 => Submodule.add_mem _ h1 h2)
    rw [← algebraMap_smul B c z]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hc) Submodule.mem_top

/- English proof (translation)
Take `⟨π, hπ1, hπ2, e, he1, he2, he3⟩` from `spLoc Λ B M q n P ub hm hd`. Take `⟨φ, ψ, h1, h2, h3, h4⟩` from `h`. Use `haveI : Module.Finite B (MSplitAlg P n) := module_finite_mSplitAlg_of_monic P hm`. Use `haveI : Module.Finite B (Sp P ub) := Module.Finite.of_surjective π.toLinearMap hπ2`. Take `⟨ι, hι⟩` from `tensSec (M := M) π hπ2 e he1 he2`.

Use `set Pt := π.toLinearMap.rTensor M with hPtdef`. Establish `hsurj : Function.Surjective Pt` using `LinearMap.rTensor_surjective M (g := π.toLinearMap) hπ2`. Establish `hPt : ∀ (x : MSplitAlg P n) (z : MSplitAlg P n ⊗[B] M), Pt (x • z) = π x • Pt z`. Introduce `x z`. Proceed by induction on `z using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a m => simp [Pt, TensorProduct.smul_tmul', LinearMap.rTensor_tmul]`. Consider the case `add y w hy hw => rw [smul_add, map_add, hy, hw, map_add, smul_add]`. Establish `hπe : π e = 1`. Establish `h0 : 1 - e ∈ RingHom.ker π`.

Rewrite using `[he2]`. Conclude with `Ideal.mem_span_singleton_self _`. Rewrite `h0` using `[RingHom.mem_ker, map_sub, map_one, sub_eq_zero]`. Conclude with `h0.symm`. Establish `hactC : ∀ (r : R) (w : W), act (MvPolynomial.C r) w = r • w`.

Introduce `r w`. Rewrite using `[← MvPolynomial.algebraMap_eq, act.commutes]`. Both sides reduce to the same expression. Establish `hφΛ : ∀ (c : Λ) z, φ (c • z) = c • φ z`. Introduce `c z`.

Establish `hh` using `h1 (MvPolynomial.C (algebraMap Λ R c)) z`. Rewrite `hh` using `[MvPolynomial.map_C, hβ, hactC, algebraMap_smul]`. Rewrite using `[← hh]`. Use `congr 1`. Use `show _ = (algebraMap B (MSplitAlg P n) (algebraMap Λ B c)) • z`.

Rewrite using `[algebraMap_smul, algebraMap_smul]`. Establish `hψΛ : ∀ (c : Λ) v, ψ (c • v) = c • ψ v`. Introduce `c v`. Establish `hh` using `h2 (MvPolynomial.C (algebraMap Λ R c)) v`. Rewrite `hh` using `[MvPolynomial.map_C, hβ, hactC, algebraMap_smul]`.

Rewrite using `[hh]`. Use `show (algebraMap B (MSplitAlg P n) (algebraMap Λ B c)) • ψ v = c • ψ v`. Rewrite using `[algebraMap_smul, algebraMap_smul]`. Establish `hτ : ∀ j i, Ideal.Quotient.mk (mSplitIdeal P n) (MvPolynomial.map β (MvPolynomial.X (j, i) - MvPolynomial.C (ut (j, i)))) = MSplitAlg.root P n j i - algebraMap B (MSplitAlg P n) (ub j i)`. Introduce `j i`.

Rewrite using `[map_sub, MvPolynomial.map_X, MvPolynomial.map_C, map_sub, hub]`. Both sides reduce to the same expression. Establish `hu : ∀ j i, π (MSplitAlg.root P n j i - algebraMap B (MSplitAlg P n) (ub j i)) = Sp.mk P ub (MvPowerSeries.X (j, i))`. Introduce `j i`. Establish `hc : Sp.mk P ub (MvPowerSeries.C (ub j i)) = algebraMap B (Sp P ub) (ub j i)` using `(Sp.mk P ub).commutes (ub j i)`.

Rewrite using `[map_sub, hπ1, AlgHom.commutes, Sp.u, map_add, hc, add_sub_cancel_left]`. Establish `hpowW : ∀ (x : PU R q n) (r : ℕ) (w : W), (((act x).restrictScalars Λ) ^ r) w = act (x ^ r) w`. Introduce `x r w`. Rewrite using `[map_pow, Module.End.pow_apply, Module.End.pow_apply]`. Both sides reduce to the same expression.

Set `η : PU R q n →+* Sp P ub` to `π.toRingHom.comp ((Ideal.Quotient.mk (mSplitIdeal P n)).comp (MvPolynomial.map β))`. Establish `hη : ∀ t, η t = π (Ideal.Quotient.mk (mSplitIdeal P n) (MvPolynomial.map β t))` using `fun t => rfl`. Use `⟨finTens, ?_, η, φ.comp ι, Pt.toAddMonoidHom.comp ψ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨j, i⟩ k z`. Take `⟨z0, rfl⟩` from `hsurj z`.

Establish `hy : e • (e • z0) = e • z0` using `by rw [smul_smul, he1.eq]`. Take `⟨d, hd⟩` from `(he3 (e • z0)).mp hy j i k`. Use `⟨d, ?_⟩` and prove the remaining obligations. Establish `h6` using `nilMap _ Pt.toAddMonoidHom (fun c w => LinearMap.map_smul_of_tower Pt c w) ((mem_map_algebraMap_smul_top_iff_mem_smul_top _ _).mp hd)`. Rewrite `h6` using `[LinearMap.toAddMonoidHom_coe, hPt, hPt, hπe, one_smul, map_pow, hu]`.

Conclude with `h6`. Introduce `a`. Rewrite using `[hη, MvPolynomial.map_C]`. Conclude with `π.commutes (β a)`. Introduce `j i`.

Rewrite using `[hη, MvPolynomial.map_X]`. Conclude with `hπ1 j i`. Introduce `t z`. Take `⟨z0, rfl⟩` from `hsurj z`. Use `show φ (ι (η t • Pt z0)) = act t (φ (ι (Pt z0)))`.

Rewrite using `[hη, ← hPt, hι, hι, smul_smul, mul_comm, ← smul_smul, h1]`. Introduce `t v show Pt (ψ (act t v)) = η t • Pt (ψ v)`. Rewrite using `[h2, hPt, hη]`. Introduce `z`. Take `⟨z0, rfl⟩` from `hsurj z`.

Use `show Pt (ψ (φ (ι (Pt z0)))) = η f • Pt z0`. Rewrite using `[hι, h4, hPt, hPt, hπe, one_smul, hη]`. Introduce `z`. Take `⟨z0, rfl⟩` from `hsurj z`. Rewrite using `[mem_topNil]`.

Introduce and unpack `⟨j, i⟩ k`. Rewrite using `[Filter.eventually_atTop]`. Establish `hy : e • (e • z0) = e • z0` using `by rw [smul_smul, he1.eq]`. Take `⟨d, hd⟩` from `(he3 (e • z0)).mp hy j i k`. Use `⟨d, fun r hr => ?_⟩` and prove the remaining obligations.

Take `⟨s, rfl⟩` from `Nat.exists_eq_add_of_le hr`. Use `show ((act (MvPolynomial.X (j, i) - MvPolynomial.C (ut (j, i)))).restrictScalars Λ ^ (d + s)) (φ (ι (Pt z0))) ∈ _`. Rewrite using `[hpowW, hι, ← h1]`. Simplify using `only [map_pow]`. Rewrite using `[hτ, pow_add, mul_comm, ← smul_smul]`.

Apply `nilMap _ φ hφΛ` to reduce the goal to its premises. Conclude with `nilMap (maximalIdeal Λ ^ k) (DistribMulAction.toAddMonoidHom (MSplitAlg P n ⊗[B] M) ((MSplitAlg.root P n j i - algebraMap B (MSplitAlg P n) (ub j i)) ^ s)) (fun c w => smul_comm _ c w) ((mem_map_algebraMap_smul_top_iff_mem_smul_top _ _).mp hd)`. Introduce `v hv`. Rewrite `hv` using `[mem_topNil]`. Use `show φ (ι (Pt (ψ v))) = act f v`.

Establish `he' : e • ψ v = ψ v`. Rewrite using `[he3]`. Introduce `j i k`. Take `⟨d, hd⟩` from `(hv (j, i) k).exists`. Use `⟨d, ?_⟩` and prove the remaining obligations.

Rewrite `hd` using `[hpowW]`. Establish `h5` using `nilMap _ ψ hψΛ hd`. Rewrite `h5` using `[h2]`. Simplify using `only [map_pow] at h5`. Rewrite `h5` using `[hτ]`.

Conclude with `(mem_map_algebraMap_smul_top_iff_mem_smul_top _ _).mpr h5`. Rewrite using `[hι, he', h3]`.
-/
theorem spPart {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ]
    {B M : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] [Algebra Λ B]
    [IsLocalHom (algebraMap Λ B)] [AddCommGroup M] [Module B M] [Module Λ M] [IsScalarTower Λ B M] [Module.Finite Λ M]
    {q n : ℕ} (P : Fin q → Polynomial B) (hm : ∀ j, (P j).Monic) (hd : ∀ j, (P j).natDegree = n)
    {R W : Type} [CommRing R] [Algebra Λ R] [AddCommGroup W] [Module R W] [Module Λ W] [IsScalarTower Λ R W]
    (β : R →+* B) (hβ : ∀ c, β (algebraMap Λ R c) = algebraMap Λ B c) (ut : Fin q × Fin n → R) (ub : Fin q → Fin n → B)
    (hub : ∀ j i, ub j i = β (ut (j, i)))
    (act : PU R q n →ₐ[R] Module.End R W) (f : PU R q n) (h : TwoMaps (M := M) β P act f) :
    Module.Finite Λ (Sp P ub ⊗[B] M) ∧
    (∀ p (k : ℕ) (z : Sp P ub ⊗[B] M), ∃ d : ℕ, Sp.mk P ub (MvPowerSeries.X p) ^ d • z ∈
      (maximalIdeal Λ ^ k • ⊤ : Submodule Λ (Sp P ub ⊗[B] M))) ∧
    ∃ (η : PU R q n →+* Sp P ub) (φ : Sp P ub ⊗[B] M →+ W) (ψ : W →+ Sp P ub ⊗[B] M),
      (∀ a, η (MvPolynomial.C a) = algebraMap B _ (β a)) ∧ (∀ j i, η (MvPolynomial.X (j, i)) = Sp.u P ub j i) ∧
      (∀ t z, φ (η t • z) = act t (φ z)) ∧ (∀ t v, ψ (act t v) = η t • ψ v) ∧ (∀ z, ψ (φ z) = η f • z) ∧
      (∀ z, φ z ∈ topNil (maximalIdeal Λ) fun p => (act (MvPolynomial.X p - MvPolynomial.C (ut p))).restrictScalars Λ) ∧
      ∀ v ∈ topNil (maximalIdeal Λ) fun p => (act (MvPolynomial.X p - MvPolynomial.C (ut p))).restrictScalars Λ,
        φ (ψ v) = act f v := by
  obtain ⟨π, hπ1, hπ2, e, he1, he2, he3⟩ := spLoc Λ B M q n P ub hm hd
  obtain ⟨φ, ψ, h1, h2, h3, h4⟩ := h
  haveI : Module.Finite B (MSplitAlg P n) := module_finite_mSplitAlg_of_monic P hm
  haveI : Module.Finite B (Sp P ub) := Module.Finite.of_surjective π.toLinearMap hπ2
  obtain ⟨ι, hι⟩ := tensSec (M := M) π hπ2 e he1 he2
  set Pt := π.toLinearMap.rTensor M with hPtdef
  have hsurj : Function.Surjective Pt := LinearMap.rTensor_surjective M (g := π.toLinearMap) hπ2
  have hPt : ∀ (x : MSplitAlg P n) (z : MSplitAlg P n ⊗[B] M), Pt (x • z) = π x • Pt z := by
    intro x z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a m => simp [Pt, TensorProduct.smul_tmul', LinearMap.rTensor_tmul]
    | add y w hy hw => rw [smul_add, map_add, hy, hw, map_add, smul_add]
  have hπe : π e = 1 := by
    have h0 : 1 - e ∈ RingHom.ker π := by
      rw [he2]
      exact Ideal.mem_span_singleton_self _
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at h0
    exact h0.symm
  have hactC : ∀ (r : R) (w : W), act (MvPolynomial.C r) w = r • w := by
    intro r w
    rw [← MvPolynomial.algebraMap_eq, act.commutes]
    rfl
  have hφΛ : ∀ (c : Λ) z, φ (c • z) = c • φ z := by
    intro c z
    have hh := h1 (MvPolynomial.C (algebraMap Λ R c)) z
    rw [MvPolynomial.map_C, hβ, hactC, algebraMap_smul] at hh
    rw [← hh]
    congr 1
    show _ = (algebraMap B (MSplitAlg P n) (algebraMap Λ B c)) • z
    rw [algebraMap_smul, algebraMap_smul]
  have hψΛ : ∀ (c : Λ) v, ψ (c • v) = c • ψ v := by
    intro c v
    have hh := h2 (MvPolynomial.C (algebraMap Λ R c)) v
    rw [MvPolynomial.map_C, hβ, hactC, algebraMap_smul] at hh
    rw [hh]
    show (algebraMap B (MSplitAlg P n) (algebraMap Λ B c)) • ψ v = c • ψ v
    rw [algebraMap_smul, algebraMap_smul]
  have hτ : ∀ j i, Ideal.Quotient.mk (mSplitIdeal P n)
      (MvPolynomial.map β (MvPolynomial.X (j, i) - MvPolynomial.C (ut (j, i)))) =
      MSplitAlg.root P n j i - algebraMap B (MSplitAlg P n) (ub j i) := by
    intro j i
    rw [map_sub, MvPolynomial.map_X, MvPolynomial.map_C, map_sub, hub]
    rfl
  have hu : ∀ j i, π (MSplitAlg.root P n j i - algebraMap B (MSplitAlg P n) (ub j i)) =
      Sp.mk P ub (MvPowerSeries.X (j, i)) := by
    intro j i
    have hc : Sp.mk P ub (MvPowerSeries.C (ub j i)) = algebraMap B (Sp P ub) (ub j i) :=
      (Sp.mk P ub).commutes (ub j i)
    rw [map_sub, hπ1, AlgHom.commutes, Sp.u, map_add, hc, add_sub_cancel_left]
  have hpowW : ∀ (x : PU R q n) (r : ℕ) (w : W), (((act x).restrictScalars Λ) ^ r) w = act (x ^ r) w := by
    intro x r w
    rw [map_pow, Module.End.pow_apply, Module.End.pow_apply]
    rfl
  let η : PU R q n →+* Sp P ub :=
    π.toRingHom.comp ((Ideal.Quotient.mk (mSplitIdeal P n)).comp (MvPolynomial.map β))
  have hη : ∀ t, η t = π (Ideal.Quotient.mk (mSplitIdeal P n) (MvPolynomial.map β t)) := fun t => rfl
  refine ⟨finTens, ?_, η, φ.comp ι, Pt.toAddMonoidHom.comp ψ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨j, i⟩ k z
    obtain ⟨z0, rfl⟩ := hsurj z
    have hy : e • (e • z0) = e • z0 := by rw [smul_smul, he1.eq]
    obtain ⟨d, hd⟩ := (he3 (e • z0)).mp hy j i k
    refine ⟨d, ?_⟩
    have h6 := nilMap _ Pt.toAddMonoidHom (fun c w => LinearMap.map_smul_of_tower Pt c w)
      ((mem_map_algebraMap_smul_top_iff_mem_smul_top _ _).mp hd)
    rw [LinearMap.toAddMonoidHom_coe, hPt, hPt, hπe, one_smul, map_pow, hu] at h6
    exact h6
  · intro a
    rw [hη, MvPolynomial.map_C]
    exact π.commutes (β a)
  · intro j i
    rw [hη, MvPolynomial.map_X]
    exact hπ1 j i
  · intro t z
    obtain ⟨z0, rfl⟩ := hsurj z
    show φ (ι (η t • Pt z0)) = act t (φ (ι (Pt z0)))
    rw [hη, ← hPt, hι, hι, smul_smul, mul_comm, ← smul_smul, h1]
  · intro t v
    show Pt (ψ (act t v)) = η t • Pt (ψ v)
    rw [h2, hPt, hη]
  · intro z
    obtain ⟨z0, rfl⟩ := hsurj z
    show Pt (ψ (φ (ι (Pt z0)))) = η f • Pt z0
    rw [hι, h4, hPt, hPt, hπe, one_smul, hη]
  · intro z
    obtain ⟨z0, rfl⟩ := hsurj z
    rw [mem_topNil]
    rintro ⟨j, i⟩ k
    rw [Filter.eventually_atTop]
    have hy : e • (e • z0) = e • z0 := by rw [smul_smul, he1.eq]
    obtain ⟨d, hd⟩ := (he3 (e • z0)).mp hy j i k
    refine ⟨d, fun r hr => ?_⟩
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hr
    show ((act (MvPolynomial.X (j, i) - MvPolynomial.C (ut (j, i)))).restrictScalars Λ ^ (d + s))
      (φ (ι (Pt z0))) ∈ _
    rw [hpowW, hι, ← h1]
    simp only [map_pow]
    rw [hτ, pow_add, mul_comm, ← smul_smul]
    apply nilMap _ φ hφΛ
    exact nilMap (maximalIdeal Λ ^ k) (DistribMulAction.toAddMonoidHom (MSplitAlg P n ⊗[B] M)
      ((MSplitAlg.root P n j i - algebraMap B (MSplitAlg P n) (ub j i)) ^ s))
      (fun c w => smul_comm _ c w) ((mem_map_algebraMap_smul_top_iff_mem_smul_top _ _).mp hd)
  · intro v hv
    rw [mem_topNil] at hv
    show φ (ι (Pt (ψ v))) = act f v
    have he' : e • ψ v = ψ v := by
      rw [he3]
      intro j i k
      obtain ⟨d, hd⟩ := (hv (j, i) k).exists
      refine ⟨d, ?_⟩
      rw [hpowW] at hd
      have h5 := nilMap _ ψ hψΛ hd
      rw [h2] at h5
      simp only [map_pow] at h5
      rw [hτ] at h5
      exact (mem_map_algebraMap_smul_top_iff_mem_smul_top _ _).mpr h5
    rw [hι, he', h3]

end UpperTheory.V.Pa.Lev.OpP
