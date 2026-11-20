import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
import Formalism.LocalToGlobal.IndefiniteReal.PartsRow
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

namespace GlobalTheory.OccRowVec

open Representation

/- English proof (translation)
Use `haveI : Nontrivial S := by`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_nontrivial_iff_subsingleton]`. Apply `hU0` to reduce the goal to its premises. Establish `: (⨆ i, LinearMap.range (Φ i)) = ⊥`.

Rewrite using `[iSup_eq_bot]`. Introduce `i`. Rewrite using `[LinearMap.range_eq_bot]`. Use extensionality with `x`. Simplify using `[Subsingleton.elim x 0]`.

Rewrite `hU` using `[this]`. Conclude with `(Submodule.mem_bot ℂ).1 hU`. Use `haveI : IsSimpleModule (MonoidAlgebra ℂ G) σ.asModule := by haveI : Nontrivial σ.asModule := σ.asModuleEquiv.toEquiv.nontrivial`. Use `{ exists_pair_ne := exists_pair_ne _, eq_bot_or_eq_top := fun N => ?_ }` and prove the remaining obligations. Set `W : Submodule ℂ S` to `{ carrier := {s | σ.asModuleEquiv.symm s ∈ N} zero_mem' := by simp add_mem' := fun {a b} ha hb => by show σ.asModuleEquiv.symm (a + b) ∈ N`.

Rewrite using `[map_add]`. Conclude with `N.add_mem ha hb`. Use the proof step `smul_mem' := fun c a ha => by show σ.asModuleEquiv.symm (c • a) ∈ N`. Rewrite using `[asModuleEquiv_symm_map_smul]`. Conclude with `N.smul_mem _ ha }`.

Establish `hW : ∀ g, ∀ x ∈ W, σ g x ∈ W`. Introduce `g x hx`. Use `show σ.asModuleEquiv.symm (σ g x) ∈ N`. Rewrite using `[asModuleEquiv_symm_map_rho]`. Conclude with `N.smul_mem _ hx`.

Break down `hirr W hW with h | h` into its components or cases. Use `left`. Rewrite using `[eq_bot_iff]`. Introduce `y hy`. Establish `: σ.asModuleEquiv y ∈ W` using `by show σ.asModuleEquiv.symm (σ.asModuleEquiv y) ∈ N`.

Simplify using `using hy`. Rewrite `this` using `[h, Submodule.mem_bot]`. Rewrite using `[Submodule.mem_bot]`. Simplify using `using this`. Use `right`.

Rewrite using `[eq_top_iff]`. Introduce `y _`. Establish `: σ.asModuleEquiv y ∈ W` using `by rw [h]; trivial`. Simplify `this` using `[W]`. Set `Φ' : ι → σ.asModule →ₗ[MonoidAlgebra ℂ G] ρ.asModule` to `fun i => IntertwiningMap.equivLinearMapAsModule σ ρ ⟨Φ i, fun g => LinearMap.ext fun v => hΦ i g v⟩`.

Establish `hΦ' : ∀ i v, Φ' i (σ.asModuleEquiv.symm v) = ρ.asModuleEquiv.symm (Φ i v)` using `fun i v => rfl`. Set `Ψ : (ι → σ.asModule) →ₗ[MonoidAlgebra ℂ G] ρ.asModule` to `∑ i, (Φ' i).comp (LinearMap.proj i)`. Establish `hΨ : ∀ i w, Ψ (Pi.single i w) = Φ' i w`. Introduce `i w`. Simplify using `[Ψ, Pi.single_apply, apply_ite]`.

Establish `hUr : ρ.asModuleEquiv.symm U ∈ LinearMap.range Ψ` using `by clear hU0`. Proceed by induction on `hU using Submodule.iSup_induction' with`. Consider the case `mem i y hy`. Take `⟨v, rfl⟩` from `hy`. Conclude with `⟨Pi.single i (σ.asModuleEquiv.symm v), by rw [hΨ, hΦ']⟩`.

Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `Submodule.add_mem _ ha hb`. Take `⟨C, hC⟩` from `exists_isCompl (LinearMap.ker Ψ)`.

Take `⟨m, hm⟩` from `hUr`. Establish `hmem : m ∈ LinearMap.ker Ψ ⊔ C` using `by rw [hC.sup_eq_top]; trivial`. Take `⟨a, ha, c, hc, rfl⟩` from `Submodule.mem_sup.1 hmem`. Establish `hΨc : Ψ c = ρ.asModuleEquiv.symm U`. Rewrite using `[← hm, map_add, LinearMap.mem_ker.1 ha, zero_add]`.

Establish `hc0 : c ≠ 0`. Introduce `h`. Apply `hU0` to reduce the goal to its premises. Rewrite `hΨc` using `[h, map_zero]`. Use `congrArg ρ.asModuleEquiv hΨc` as an intermediate fact.

Simplify using `using this.symm`. Take `⟨i, hi⟩` from `Function.ne_iff.1 hc0`. Use `⟨σ.asModuleEquiv (c i), by simpa using hi, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hxc : x • c ∈ LinearMap.ker Ψ ⊓ C`. Use `Submodule.mem_inf.2 ⟨?_, C.smul_mem x hc⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.mem_ker, map_smul, hΨc]`. Apply `ρ.asModuleEquiv.injective` to reduce the goal to its premises. Rewrite using `[asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply, hx, map_zero]`. Rewrite `hxc` using `[hC.inf_eq_bot, Submodule.mem_bot]`. Rewrite using `[← asModuleEquiv_map_smul]`.

Establish `: x • c i = 0`. Use `congrFun hxc i` as an intermediate fact. Simplify using `using this`. Rewrite using `[this, map_zero]`.
-/
theorem exists_ne_zero_ann {G : Type} [Group G] {S A : Type} [AddCommGroup S] [Module ℂ S] [AddCommGroup A] [Module ℂ A]
    (σ : Representation ℂ G S) (ρ : Representation ℂ G A)
    (hirr : ∀ W : Submodule ℂ S, (∀ g, ∀ x ∈ W, σ g x ∈ W) → W = ⊥ ∨ W = ⊤)
    {ι : Type} [Fintype ι] (Φ : ι → S →ₗ[ℂ] A) (hΦ : ∀ i g x, Φ i (σ g x) = ρ g (Φ i x))
    {U : A} (hU : U ∈ ⨆ i, LinearMap.range (Φ i)) (hU0 : U ≠ 0) :
    ∃ v : S, v ≠ 0 ∧ ∀ x : MonoidAlgebra ℂ G, ρ.asAlgebraHom x U = 0 → σ.asAlgebraHom x v = 0 := by
  classical
  haveI : Nontrivial S := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply hU0
    have : (⨆ i, LinearMap.range (Φ i)) = ⊥ := by
      rw [iSup_eq_bot]
      intro i
      rw [LinearMap.range_eq_bot]
      ext x
      simp [Subsingleton.elim x 0]
    rw [this] at hU
    exact (Submodule.mem_bot ℂ).1 hU
  haveI : IsSimpleModule (MonoidAlgebra ℂ G) σ.asModule := by
    haveI : Nontrivial σ.asModule := σ.asModuleEquiv.toEquiv.nontrivial
    refine { exists_pair_ne := exists_pair_ne _, eq_bot_or_eq_top := fun N => ?_ }
    let W : Submodule ℂ S :=
      { carrier := {s | σ.asModuleEquiv.symm s ∈ N}
        zero_mem' := by simp
        add_mem' := fun {a b} ha hb => by
          show σ.asModuleEquiv.symm (a + b) ∈ N
          rw [map_add]; exact N.add_mem ha hb
        smul_mem' := fun c a ha => by
          show σ.asModuleEquiv.symm (c • a) ∈ N
          rw [asModuleEquiv_symm_map_smul]; exact N.smul_mem _ ha }
    have hW : ∀ g, ∀ x ∈ W, σ g x ∈ W := by
      intro g x hx
      show σ.asModuleEquiv.symm (σ g x) ∈ N
      rw [asModuleEquiv_symm_map_rho]; exact N.smul_mem _ hx
    rcases hirr W hW with h | h
    · left
      rw [eq_bot_iff]
      intro y hy
      have : σ.asModuleEquiv y ∈ W := by
        show σ.asModuleEquiv.symm (σ.asModuleEquiv y) ∈ N
        simpa using hy
      rw [h, Submodule.mem_bot] at this
      rw [Submodule.mem_bot]
      simpa using this
    · right
      rw [eq_top_iff]
      intro y _
      have : σ.asModuleEquiv y ∈ W := by rw [h]; trivial
      simpa [W] using this
  let Φ' : ι → σ.asModule →ₗ[MonoidAlgebra ℂ G] ρ.asModule := fun i =>
    IntertwiningMap.equivLinearMapAsModule σ ρ ⟨Φ i, fun g => LinearMap.ext fun v => hΦ i g v⟩
  have hΦ' : ∀ i v, Φ' i (σ.asModuleEquiv.symm v) = ρ.asModuleEquiv.symm (Φ i v) := fun i v => rfl
  let Ψ : (ι → σ.asModule) →ₗ[MonoidAlgebra ℂ G] ρ.asModule := ∑ i, (Φ' i).comp (LinearMap.proj i)
  have hΨ : ∀ i w, Ψ (Pi.single i w) = Φ' i w := by
    intro i w
    simp [Ψ, Pi.single_apply, apply_ite]
  have hUr : ρ.asModuleEquiv.symm U ∈ LinearMap.range Ψ := by
    clear hU0
    induction hU using Submodule.iSup_induction' with
    | mem i y hy =>
      obtain ⟨v, rfl⟩ := hy
      exact ⟨Pi.single i (σ.asModuleEquiv.symm v), by rw [hΨ, hΦ']⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  obtain ⟨C, hC⟩ := exists_isCompl (LinearMap.ker Ψ)
  obtain ⟨m, hm⟩ := hUr
  have hmem : m ∈ LinearMap.ker Ψ ⊔ C := by rw [hC.sup_eq_top]; trivial
  obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 hmem
  have hΨc : Ψ c = ρ.asModuleEquiv.symm U := by
    rw [← hm, map_add, LinearMap.mem_ker.1 ha, zero_add]
  have hc0 : c ≠ 0 := by
    intro h
    apply hU0
    rw [h, map_zero] at hΨc
    have := congrArg ρ.asModuleEquiv hΨc
    simpa using this.symm
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hc0
  refine ⟨σ.asModuleEquiv (c i), by simpa using hi, fun x hx => ?_⟩
  have hxc : x • c ∈ LinearMap.ker Ψ ⊓ C := by
    refine Submodule.mem_inf.2 ⟨?_, C.smul_mem x hc⟩
    rw [LinearMap.mem_ker, map_smul, hΨc]
    apply ρ.asModuleEquiv.injective
    rw [asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply, hx, map_zero]
  rw [hC.inf_eq_bot, Submodule.mem_bot] at hxc
  rw [← asModuleEquiv_map_smul]
  have : x • c i = 0 := by
    have := congrFun hxc i
    simpa using this
  rw [this, map_zero]

end GlobalTheory.OccRowVec

namespace GlobalTheory.OccRowVec

open Representation

section FinRep

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

noncomputable def finRep (π : Formalism.L2.NG.FinTyp L n) : Representation ℂ (Formalism.AUTREP.GAf L n) π.S where
  toFun h := (Formalism.L2.NG.rt L n h).restrict (fun f hf => π.stable h f hf)
  map_one' := by
    ext f x
    simp [LinearMap.restrict_apply, Formalism.IndefR.principalLevelFrame.rt_one]
  map_mul' a b := by
    ext f x
    simp [LinearMap.restrict_apply, Formalism.IndefR.principalLevelFrame.rt_rt]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finRep_coe (π : Formalism.L2.NG.FinTyp L n) (h : Formalism.AUTREP.GAf L n) (f : π.S) :
    ((finRep π h f : π.S) : Formalism.AUTREP.GAf L n → ℂ) = Formalism.L2.NG.rt L n h f := rfl

/- English proof (translation)
Introduce `W hW`. Establish `hst : ∀ h, ∀ f ∈ W.map π.S.subtype, Formalism.L2.NG.rt L n h f ∈ W.map π.S.subtype`. Introduce and unpack `g _ ⟨x, hx, rfl⟩`. Conclude with `⟨finRep π g x, hW g x hx, rfl⟩`. Break down `π.irr (W.map π.S.subtype) (Submodule.map_subtype_le _ _) hst with h | h` into its components or cases.

Use `left`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Establish `: (x : Formalism.AUTREP.GAf L n → ℂ) ∈ W.map π.S.subtype` using `⟨x, hx, rfl⟩`. Rewrite `this` using `[h, Submodule.mem_bot]`.

Rewrite using `[Submodule.mem_bot]`. Conclude with `Subtype.ext this`. Use `right`. Rewrite using `[eq_top_iff]`. Introduce `x _`.

Establish `: (x : Formalism.AUTREP.GAf L n → ℂ) ∈ W.map π.S.subtype` using `by rw [h]; exact x.2`. Take `⟨y, hy, hxy⟩` from `this`. Establish `: y = x` using `Subtype.ext hxy`. Substitute `this` using the available equality. Conclude with `hy`.
-/
theorem finRep_irr (π : Formalism.L2.NG.FinTyp L n) :
    ∀ W : Submodule ℂ π.S, (∀ g, ∀ x ∈ W, finRep π g x ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro W hW
  have hst : ∀ h, ∀ f ∈ W.map π.S.subtype, Formalism.L2.NG.rt L n h f ∈ W.map π.S.subtype := by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨finRep π g x, hW g x hx, rfl⟩
  rcases π.irr (W.map π.S.subtype) (Submodule.map_subtype_le _ _) hst with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have : (x : Formalism.AUTREP.GAf L n → ℂ) ∈ W.map π.S.subtype := ⟨x, hx, rfl⟩
    rw [h, Submodule.mem_bot] at this
    rw [Submodule.mem_bot]
    exact Subtype.ext this
  · right
    rw [eq_top_iff]
    intro x _
    have : (x : Formalism.AUTREP.GAf L n → ℂ) ∈ W.map π.S.subtype := by rw [h]; exact x.2
    obtain ⟨y, hy, hxy⟩ := this
    have : y = x := Subtype.ext hxy
    subst this
    exact hy

end FinRep

/- English proof (translation)
Proceed by induction on `hT using Submodule.span_induction with`. Consider the case `mem T h => exact h.lev`. Consider the case `zero => intro v k _ g`. Simplify using the standard rewrite rules. Consider the case `add T T' _ _ h h' => intro v k hk g`.

Simplify using `[h v k hk g, h' v k hk g, mul_add]`. Consider the case `smul c T _ h => intro v k hk g`. Simplify using `[h v k hk g, mul_left_comm]`.
-/
theorem mult_lev {D : D7} {V : HSp D} {Sp : D.what₂.Tau → SPar} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {M : DSModel V Sp} {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : T ∈ Mult θ M J χ) :
    ∀ v, ∀ k ∈ J, ∀ g, T v (g * k) = χ k * T v g := by
  induction hT using Submodule.span_induction with
  | mem T h => exact h.lev
  | zero => intro v k _ g; simp
  | add T T' _ _ h h' => intro v k hk g; simp [h v k hk g, h' v k hk g, mul_add]
  | smul c T _ h => intro v k hk g; simp [h v k hk g, mul_left_comm]

/- English proof (translation)
Establish `hx' : x ∈ levG (Yc D 0) β (Lc.dat0 Lc.triv)` using `hx`. Take `⟨hG, hpar, hr⟩` from `mem_levA.1 hx'`. Establish `hH : (Lc.dat0 Lc.triv).P.H = ⊥`. Apply the tactic sequence `simp [LevCh.dat0, datY, LevelP.triv] <;> rfl`. Establish `hr1 : rTup β (Lc.dat0 Lc.triv) (finE (Yc D 0) x) = 1`.

Use `hr` as an intermediate fact. Rewrite `this` using `[hH]`. Conclude with `(Subgroup.mem_bot).1 this`. Establish `hr1' : rTup β (Lc.dat0 P) (finE (Yc D 0) x) = 1` using `hr1`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Use `show x ∈ levG (Yc D 0) β (Lc.dat0 P)`. Use `mem_levA.2 ⟨hG, hpar, ?_⟩` and prove the remaining obligations. Use `show rTup β (Lc.dat0 P) (finE (Yc D 0) x) ∈ (Lc.dat0 P).P.H`. Rewrite using `[hr1']`. Conclude with `Subgroup.one_mem _`.

Unfold `levChi levFn`. Rewrite using `[hr1', blockDiagonalExtendByOnePrimeField_one]`. Simplify using `[LevCh.dat0, datY]`.
-/
theorem lev_triv {D : D7} {T : Type} (Lc : LevCh D T) (β : GL (Fin (Yc D 0).rank) (Lev.EAf D)) (P : LevelP Lc.Pg D.R.r ℂ)
    {x : GA D (Yc D 0)} (hx : x ∈ levS (Yc D 0) β (Lc.dat0 Lc.triv)) :
    x ∈ levS (Yc D 0) β (Lc.dat0 P) ∧ levChi (Yc D 0) β (Lc.dat0 P) x = 1 := by
  have hx' : x ∈ levG (Yc D 0) β (Lc.dat0 Lc.triv) := hx
  obtain ⟨hG, hpar, hr⟩ := mem_levA.1 hx'
  have hH : (Lc.dat0 Lc.triv).P.H = ⊥ := by
    simp [LevCh.dat0, datY, LevelP.triv] <;> rfl
  have hr1 : rTup β (Lc.dat0 Lc.triv) (finE (Yc D 0) x) = 1 := by
    have := hr
    rw [hH] at this
    exact (Subgroup.mem_bot).1 this
  have hr1' : rTup β (Lc.dat0 P) (finE (Yc D 0) x) = 1 := hr1
  refine ⟨?_, ?_⟩
  · show x ∈ levG (Yc D 0) β (Lc.dat0 P)
    refine mem_levA.2 ⟨hG, hpar, ?_⟩
    show rTup β (Lc.dat0 P) (finE (Yc D 0) x) ∈ (Lc.dat0 P).P.H
    rw [hr1']
    exact Subgroup.one_mem _
  · unfold levChi levFn
    rw [hr1', blockDiagonalExtendByOnePrimeField_one]
    simp [LevCh.dat0, datY]

/- English proof (translation)
Unfold `levChi levFn`. Simplify using `only [flagL, withP, LevelP.full]`. Unfold `ext1`. Use `split_ifs`. Simplify using `[LevCh.dat0, datY]`.

Both sides reduce to the same expression. Simplify using `[LevCh.dat0, datY]`.
-/
theorem levChi_flag_triv {D : D7} {T : Type} (Lc : LevCh D T) (β : GL (Fin (Yc D 0).rank) (Lev.EAf D)) (x : GA D (Yc D 0)) :
    levChi (Yc D 0) β (flagL (Lc.dat0 Lc.triv)) x = 1 := by
  unfold levChi levFn
  simp only [flagL, withP, LevelP.full]
  unfold ext1
  split_ifs
  · simp [LevCh.dat0, datY]
    rfl
  · simp [LevCh.dat0, datY]
end GlobalTheory.OccRowVec

namespace GlobalTheory.OccRowVec

open Representation

/- English proof (translation)
Introduce `D G _ _ Pl0 T A Ks _ _ _ R F s _ _ n PY π hπ`. Take `⟨b, hb⟩` from `hπ`. Take `⟨U, hU, hU0⟩` from `(Submodule.ne_bot_iff _).1 hb`. Establish `hU' : U ∈ goodPart R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F b))) (levChi _ (R.βY 0) (R.dat0 (R.levR F b))) R.e0 ⊓ principalLevelFrame.isotIn (principalLevelFrame.actM PY (R.MY 0)) (principalLevelFrame.Minf R.θ PY (R.MY 0)) (principalLevelFrame.FinTyp.conjT π)` using `hU`. Take `⟨hgood, hiso⟩` from `Submodule.mem_inf.1 hU'`.

Take `⟨hMult, hker⟩` from `Submodule.mem_inf.1 hgood`. Establish `he0 : postOn (R.MY 0) R.e0 U = U`. Use `LinearMap.mem_ker.1 hker` as an intermediate fact. Rewrite `this` using `[LinearMap.sub_apply, sub_eq_zero]`. Simplify using `using this`.

Unfold `principalLevelFrame.isotIn at hiso`. Rewrite `hiso` using `[iSup_subtype']`. Take `⟨sF, hsF⟩` from `Submodule.mem_iSup_iff_exists_finset.1 hiso`. Rewrite `hsF` using `[iSup_subtype']`. Establish `hΦ : ∀ (i : {x // x ∈ sF}) (g : Formalism.AUTREP.GAf D.host.E n) (x : (principalLevelFrame.FinTyp.conjT π).S), (i.1.1 : (principalLevelFrame.FinTyp.conjT π).S →ₗ[ℂ] MMap (R.MY 0)) (finRep (principalLevelFrame.FinTyp.conjT π) g x) = principalLevelFrame.actM PY (R.MY 0) g (i.1.1 x)` using `fun i g x => i.1.2.1 g x`.

Take `⟨v, hv0, hv⟩` from `exists_ne_zero_ann (ι := {x // x ∈ sF}) (finRep (principalLevelFrame.FinTyp.conjT π)) (principalLevelFrame.actM PY (R.MY 0)) (finRep_irr _) (fun i => i.1.1) hΦ hsF hU0`. Use `⟨(v : Formalism.AUTREP.GAf D.host.E n → ℂ), v.2, fun h => hv0 (Subtype.ext h), ?_, ?_⟩` and prove the remaining obligations. Introduce `κ hκ`. Establish `hl` using `lev_triv R.toLevCh (R.βY 0) (R.levR F b) hκ`. Establish `hU1 : principalLevelFrame.actM PY (R.MY 0) κ U = U`.

Apply `MultilinearMap.ext` to reduce the goal to its premises. Introduce `w`. Use function extensionality and compare the values at `x`. Rewrite using `[principalLevelFrame.actM_apply, mult_lev hMult w _ hl.1 x, hl.2, one_mul]`. Establish `h1` using `hv (MonoidAlgebra.of ℂ _ κ - 1) (by`.

Rewrite using `[map_sub, asAlgebraHom_of, map_one, LinearMap.sub_apply, hU1, Module.End.one_apply, sub_self])`. Rewrite `h1` using `[map_sub, asAlgebraHom_of, map_one, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]`. Rewrite using `[one_smul]`. Conclude with `congrArg Subtype.val h1`. Introduce `κ hκ`.

Establish `hHas : ∀ w, HasType (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv)) (U w)`. Introduce `w k hk h`. Establish `hl` using `lev_triv R.toLevCh (R.βY 0) (R.levR F b) (x := k) hk`. Establish `hl0` using `lev_triv R.toLevCh (R.βY 0) R.triv (x := k) hk`. Use `show U w (h * k) = levChi (Yc D 0) (R.βY 0) (R.dat0 R.triv) k * U w h`.

Rewrite using `[mult_lev hMult w _ hl.1 h, hl.2, hl0.2]`. Establish `hchi : ∀ g, levChi (Yc D 0) (R.βY 0) (flagL (R.dat0 R.triv)) (PY.ψ (κ g)) = 1`. Introduce `g`. Conclude with `levChi_flag_triv R.toLevCh _ _`. Establish `hU2 : ∑ g, RealDat.eC (A` using `A) D.what₂.embLL g • principalLevelFrame.actM PY (R.MY 0) (κ g) U = U := by`.

Apply `MultilinearMap.ext` to reduce the goal to its premises. Introduce `w`. Use function extensionality and compare the values at `x`. Establish `h1` using `congrArg (fun T : MMap (R.MY 0) => T w x) he0`. Simplify using `only [postOn_apply] at h1`.

Rewrite using `[← h1]`. Establish `hact : ∀ g, actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (U w) x = U w (x * PY.ψ (κ g))`. Introduce `g`. Rewrite using `[level_action_spec (hHas w) ⟨_, hκ g⟩ (PY.ψ (κ g)) (hκ g) x, hchi g, inv_one, one_mul]`. Establish `hL : (∑ g, RealDat.eC (A` using `A) D.what₂.embLL g • principalLevelFrame.actM PY (R.MY 0) (κ g) U) w x = ∑ g, RealDat.eC (A := A) D.what₂.embLL g * U w (x * PY.ψ (κ g)) := by`.

Rewrite using `[MultilinearMap.sum_apply, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[MultilinearMap.smul_apply, Pi.smul_apply, principalLevelFrame.actM_apply, smul_eq_mul]`. Establish `hR : R.e0 (U w) x = ∑ g, RealDat.eC (A` using `A) D.what₂.embLL g * actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (U w) x := by show (∑ g, RealDat.eC (A := A) D.what₂.embLL g • actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g)) (U w) x = _`. Rewrite using `[LinearMap.sum_apply, Finset.sum_apply]`.

Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]`. Both sides reduce to the same expression. Rewrite using `[hL, hR]`. Conclude with `Finset.sum_congr rfl fun g _ => by rw [hact g]`.

Establish `h1` using `hv (∑ g, MonoidAlgebra.single (κ g) (RealDat.eC (A := A) D.what₂.embLL g) - 1) (by`. Rewrite using `[map_sub, map_sum, map_one, LinearMap.sub_apply, Module.End.one_apply, LinearMap.sum_apply]`. Simplify using `only [asAlgebraHom_single, LinearMap.smul_apply]`. Rewrite using `[hU2, sub_self])`. Rewrite `h1` using `[map_sub, map_sum, map_one, LinearMap.sub_apply, Module.End.one_apply, LinearMap.sum_apply, sub_eq_zero]`.

Simplify using `only [asAlgebraHom_single, LinearMap.smul_apply] at h1`. Establish `h2` using `congrArg Subtype.val h1`. Rewrite `h2` using `[Submodule.coe_sum]`. Simplify `h2` using `[Submodule.coe_smul, finRep_coe]`.
-/
theorem exists_vec_of_occRows : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → ∀ {n : ℕ} (PY : principalLevelFrame.RowPsi (Yc D 0) n) π, π ∈ principalLevelFrame.OccRows R.θ PY (R.MY 0) (fun b => (levS _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun b => (levChi _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun _ => R.e0) → ∃ v ∈ (principalLevelFrame.FinTyp.conjT π).S, v ≠ 0 ∧ principalLevelFrame.IsTypeVec (PY.ψ ⁻¹' levS _ (R.βY 0) (R.dat0 R.triv)) (fun _ => 1) v ∧ ∀ κ : G → Formalism.AUTREP.GAf D.host.E n, (∀ g, IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (PY.ψ (κ g))) → ∑ g, RealDat.eC (A := A) D.what₂.embLL g • Formalism.L2.NG.rt D.host.E n (κ g) v = v := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s _ _ n PY π hπ
  obtain ⟨b, hb⟩ := hπ
  obtain ⟨U, hU, hU0⟩ := (Submodule.ne_bot_iff _).1 hb
  have hU' : U ∈ goodPart R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F b)))
      (levChi _ (R.βY 0) (R.dat0 (R.levR F b))) R.e0 ⊓
      principalLevelFrame.isotIn (principalLevelFrame.actM PY (R.MY 0)) (principalLevelFrame.Minf R.θ PY (R.MY 0)) (principalLevelFrame.FinTyp.conjT π) := hU
  obtain ⟨hgood, hiso⟩ := Submodule.mem_inf.1 hU'
  obtain ⟨hMult, hker⟩ := Submodule.mem_inf.1 hgood
  have he0 : postOn (R.MY 0) R.e0 U = U := by
    have := LinearMap.mem_ker.1 hker
    rw [LinearMap.sub_apply, sub_eq_zero] at this
    simpa using this
  unfold principalLevelFrame.isotIn at hiso
  rw [iSup_subtype'] at hiso
  obtain ⟨sF, hsF⟩ := Submodule.mem_iSup_iff_exists_finset.1 hiso
  rw [iSup_subtype'] at hsF
  have hΦ : ∀ (i : {x // x ∈ sF}) (g : Formalism.AUTREP.GAf D.host.E n) (x : (principalLevelFrame.FinTyp.conjT π).S),
      (i.1.1 : (principalLevelFrame.FinTyp.conjT π).S →ₗ[ℂ] MMap (R.MY 0)) (finRep (principalLevelFrame.FinTyp.conjT π) g x) =
        principalLevelFrame.actM PY (R.MY 0) g (i.1.1 x) := fun i g x => i.1.2.1 g x
  obtain ⟨v, hv0, hv⟩ := exists_ne_zero_ann (ι := {x // x ∈ sF}) (finRep (principalLevelFrame.FinTyp.conjT π))
    (principalLevelFrame.actM PY (R.MY 0)) (finRep_irr _) (fun i => i.1.1) hΦ hsF hU0
  refine ⟨(v : Formalism.AUTREP.GAf D.host.E n → ℂ), v.2, fun h => hv0 (Subtype.ext h), ?_, ?_⟩
  · intro κ hκ
    have hl := lev_triv R.toLevCh (R.βY 0) (R.levR F b) hκ
    have hU1 : principalLevelFrame.actM PY (R.MY 0) κ U = U := by
      apply MultilinearMap.ext
      intro w
      funext x
      rw [principalLevelFrame.actM_apply, mult_lev hMult w _ hl.1 x, hl.2, one_mul]
    have h1 := hv (MonoidAlgebra.of ℂ _ κ - 1) (by
      rw [map_sub, asAlgebraHom_of, map_one, LinearMap.sub_apply, hU1, Module.End.one_apply, sub_self])
    rw [map_sub, asAlgebraHom_of, map_one, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1
    rw [one_smul]
    exact congrArg Subtype.val h1
  · intro κ hκ
    have hHas : ∀ w, HasType (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv)) (U w) := by
      intro w k hk h
      have hl := lev_triv R.toLevCh (R.βY 0) (R.levR F b) (x := k) hk
      have hl0 := lev_triv R.toLevCh (R.βY 0) R.triv (x := k) hk
      show U w (h * k) = levChi (Yc D 0) (R.βY 0) (R.dat0 R.triv) k * U w h
      rw [mult_lev hMult w _ hl.1 h, hl.2, hl0.2]
    have hchi : ∀ g, levChi (Yc D 0) (R.βY 0) (flagL (R.dat0 R.triv)) (PY.ψ (κ g)) = 1 := by
      intro g
      exact levChi_flag_triv R.toLevCh _ _
    have hU2 : ∑ g, RealDat.eC (A := A) D.what₂.embLL g • principalLevelFrame.actM PY (R.MY 0) (κ g) U = U := by
      apply MultilinearMap.ext
      intro w
      funext x
      have h1 := congrArg (fun T : MMap (R.MY 0) => T w x) he0
      simp only [postOn_apply] at h1
      rw [← h1]
      have hact : ∀ g, actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (U w) x = U w (x * PY.ψ (κ g)) := by
        intro g
        rw [level_action_spec (hHas w) ⟨_, hκ g⟩ (PY.ψ (κ g)) (hκ g) x, hchi g, inv_one, one_mul]
      have hL : (∑ g, RealDat.eC (A := A) D.what₂.embLL g • principalLevelFrame.actM PY (R.MY 0) (κ g) U) w x =
          ∑ g, RealDat.eC (A := A) D.what₂.embLL g * U w (x * PY.ψ (κ g)) := by
        rw [MultilinearMap.sum_apply, Finset.sum_apply]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [MultilinearMap.smul_apply, Pi.smul_apply, principalLevelFrame.actM_apply, smul_eq_mul]
      have hR : R.e0 (U w) x =
          ∑ g, RealDat.eC (A := A) D.what₂.embLL g * actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (U w) x := by
        show (∑ g, RealDat.eC (A := A) D.what₂.embLL g • actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g)) (U w) x = _
        rw [LinearMap.sum_apply, Finset.sum_apply]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
        rfl
      rw [hL, hR]
      exact Finset.sum_congr rfl fun g _ => by rw [hact g]
    have h1 := hv (∑ g, MonoidAlgebra.single (κ g) (RealDat.eC (A := A) D.what₂.embLL g) - 1) (by
      rw [map_sub, map_sum, map_one, LinearMap.sub_apply, Module.End.one_apply, LinearMap.sum_apply]
      simp only [asAlgebraHom_single, LinearMap.smul_apply]
      rw [hU2, sub_self])
    rw [map_sub, map_sum, map_one, LinearMap.sub_apply, Module.End.one_apply, LinearMap.sum_apply,
      sub_eq_zero] at h1
    simp only [asAlgebraHom_single, LinearMap.smul_apply] at h1
    have h2 := congrArg Subtype.val h1
    rw [Submodule.coe_sum] at h2
    simpa [Submodule.coe_smul, finRep_coe] using h2

end GlobalTheory.OccRowVec
