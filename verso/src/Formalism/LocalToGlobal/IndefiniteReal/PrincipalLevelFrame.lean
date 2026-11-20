import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsFinTyp

noncomputable section

open NumberField IsDedekindDomain
open Formalism.L2.Theta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S
open scoped TensorProduct

namespace Formalism.IndefR.principalLevelFrame

section Core

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def IsStable (U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)) : Prop :=
  ∀ h, ∀ f ∈ U, Formalism.L2.NG.rt L n h f ∈ U

def IsSmoothF (f : Formalism.AUTREP.GAf L n → ℂ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∀ κ, Formalism.L2.NG.Cong L n N κ → Formalism.L2.NG.rt L n κ f = f

def cyc (f : Formalism.AUTREP.GAf L n → ℂ) : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ) :=
  Submodule.span ℂ (Set.range fun h => Formalism.L2.NG.rt L n h f)

variable (L n) in

def CongConj : Prop :=
  ∀ (h : Formalism.AUTREP.GAf L n) (N : ℕ), 0 < N → ∃ N' : ℕ, 0 < N' ∧
    ∀ κ, Formalism.L2.NG.Cong L n N' κ → Formalism.L2.NG.Cong L n N (h⁻¹ * κ * h)

def IsTypeVec (J' : Set (Formalism.AUTREP.GAf L n)) (χ' : Formalism.AUTREP.GAf L n → ℂ) (f : Formalism.AUTREP.GAf L n → ℂ) : Prop :=
  ∀ κ ∈ J', Formalism.L2.NG.rt L n κ f = χ' κ • f

def heckeG {ι : Type} (s : Finset ι) (γ : ι → Formalism.AUTREP.GAf L n) :
    (Formalism.AUTREP.GAf L n → ℂ) →ₗ[ℂ] (Formalism.AUTREP.GAf L n → ℂ) :=
  ∑ i ∈ s, Formalism.L2.NG.rt L n (γ i)

def IsCoMax (f : Formalism.AUTREP.GAf L n → ℂ) (U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)) : Prop :=
  U ≤ cyc f ∧ IsStable U ∧ f ∉ U ∧
    ∀ U' : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ), U ≤ U' → U' ≤ cyc f → IsStable U' → f ∉ U' → U' = U

def mc (l : (Formalism.AUTREP.GAf L n → ℂ) →ₗ[ℂ] ℂ) : (Formalism.AUTREP.GAf L n → ℂ) →ₗ[ℂ] (Formalism.AUTREP.GAf L n → ℂ) where
  toFun f g := l (Formalism.L2.NG.rt L n g f)
  map_add' f f' := by
    funext g
    simp
  map_smul' a f := by
    funext g
    simp

def HeckeScalarG (J' : Set (Formalism.AUTREP.GAf L n)) (χ' : Formalism.AUTREP.GAf L n → ℂ) {ι : Type} (s : Finset ι)
    (γ : ι → Formalism.AUTREP.GAf L n) : Prop :=
  ∀ π : Formalism.L2.NG.FinTyp L n, ∃ a : ℂ, ∀ x ∈ π.S, IsTypeVec J' χ' x → heckeG s γ x = a • x

end Core

section CoreProofs

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rt_apply (h : Formalism.AUTREP.GAf L n) (f : Formalism.AUTREP.GAf L n → ℂ) (x : Formalism.AUTREP.GAf L n) :
    Formalism.L2.NG.rt L n h f x = f (x * h) := rfl

/- English proof (translation)
Use function extensionality and compare the values at `x`. Rewrite using `[rt_apply, rt_apply, rt_apply, mul_assoc]`.
-/
theorem rt_rt (g h : Formalism.AUTREP.GAf L n) (f : Formalism.AUTREP.GAf L n → ℂ) :
    Formalism.L2.NG.rt L n g (Formalism.L2.NG.rt L n h f) = Formalism.L2.NG.rt L n (g * h) f := by
  funext x
  rw [rt_apply, rt_apply, rt_apply, mul_assoc]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Rewrite using `[rt_apply, mul_one]`.
-/
theorem rt_one (f : Formalism.AUTREP.GAf L n → ℂ) : Formalism.L2.NG.rt L n 1 f = f := by
  funext x
  rw [rt_apply, mul_one]

/- English proof (translation)
Establish `h` using `Submodule.subset_span (R := ℂ) (Set.mem_range_self (f := fun h : Formalism.AUTREP.GAf L n => Formalism.L2.NG.rt L n h f) (1 : Formalism.AUTREP.GAf L n))`. Simplify using `only [rt_one] at h`. Conclude with `h`.
-/
theorem self_mem_cyc (f : Formalism.AUTREP.GAf L n → ℂ) : f ∈ cyc f := by
  have h := Submodule.subset_span (R := ℂ)
    (Set.mem_range_self (f := fun h : Formalism.AUTREP.GAf L n => Formalism.L2.NG.rt L n h f) (1 : Formalism.AUTREP.GAf L n))
  simp only [rt_one] at h
  exact h

/- English proof (translation)
Conclude with `Submodule.subset_span ⟨h, rfl⟩`.
-/
theorem rt_mem_cyc (f : Formalism.AUTREP.GAf L n → ℂ) (h : Formalism.AUTREP.GAf L n) : Formalism.L2.NG.rt L n h f ∈ cyc f := by
  exact Submodule.subset_span ⟨h, rfl⟩

/- English proof (translation)
Introduce `h g hg`. Establish `hle : cyc f ≤ (cyc f).comap (Formalism.L2.NG.rt L n h)`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Use `show Formalism.L2.NG.rt L n h (Formalism.L2.NG.rt L n k f) ∈ cyc f`.

Rewrite using `[rt_rt]`. Conclude with `rt_mem_cyc f _`. Conclude with `hle hg`.
-/
theorem cyc_stable (f : Formalism.AUTREP.GAf L n → ℂ) : IsStable (cyc f) := by
  intro h g hg
  have hle : cyc f ≤ (cyc f).comap (Formalism.L2.NG.rt L n h) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    show Formalism.L2.NG.rt L n h (Formalism.L2.NG.rt L n k f) ∈ cyc f
    rw [rt_rt]
    exact rt_mem_cyc f _
  exact hle hg

/- English proof (translation)
Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `hU k f hf`.
-/
theorem cyc_le {f : Formalism.AUTREP.GAf L n → ℂ} {U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)} (hU : IsStable U) (hf : f ∈ U) :
    cyc f ≤ U := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  exact hU k f hf

/- English proof (translation)
Set `S : Set (Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ))` to `{U | U ≤ cyc f ∧ IsStable U ∧ f ∉ U}`. Establish `h0 : (⊥ : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)) ∈ S`. Use `⟨bot_le, fun h g hg => ?_, ?_⟩` and prove the remaining obligations. Rewrite `hg`, the goal using `[Submodule.mem_bot]`. Rewrite using `[hg, map_zero]`.

Rewrite using `[Submodule.mem_bot]`. Conclude with `hf`. Take `⟨U, -, hU⟩` from `zorn_le_nonempty₀ S (fun c hcS hc y hy => by`. Establish `hne : c.Nonempty` using `⟨y, hy⟩`. Establish `hdir` using `hc.directedOn`.

Use `⟨sSup c, ⟨sSup_le fun z hz => (hcS hz).1, fun h g hg => ?_, fun hf' => ?_⟩, fun z hz => le_sSup hz⟩` and prove the remaining obligations. Take `⟨z, hz, hgz⟩` from `(Submodule.mem_sSup_of_directed hne hdir).mp hg`. Conclude with `(Submodule.mem_sSup_of_directed hne hdir).mpr ⟨z, hz, (hcS hz).2.1 h g hgz⟩`. Take `⟨z, hz, hfz⟩` from `(Submodule.mem_sSup_of_directed hne hdir).mp hf'`. Conclude with `(hcS hz).2.2 hfz) ⊥ h0`.

Use `⟨U, hU.prop.1, hU.prop.2.1, hU.prop.2.2, fun U' hUU' hU'c hU's hfU' => ?_⟩` and prove the remaining obligations. Conclude with `hU.eq_of_ge ⟨hU'c, hU's, hfU'⟩ hUU'`.
-/
theorem exists_coMax (f : Formalism.AUTREP.GAf L n → ℂ) (hf : f ≠ 0) : ∃ U, IsCoMax f U := by
  classical
  let S : Set (Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)) := {U | U ≤ cyc f ∧ IsStable U ∧ f ∉ U}
  have h0 : (⊥ : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)) ∈ S := by
    refine ⟨bot_le, fun h g hg => ?_, ?_⟩
    · rw [Submodule.mem_bot] at hg ⊢
      rw [hg, map_zero]
    · rw [Submodule.mem_bot]
      exact hf
  obtain ⟨U, -, hU⟩ := zorn_le_nonempty₀ S (fun c hcS hc y hy => by
    have hne : c.Nonempty := ⟨y, hy⟩
    have hdir := hc.directedOn
    refine ⟨sSup c, ⟨sSup_le fun z hz => (hcS hz).1, fun h g hg => ?_, fun hf' => ?_⟩,
      fun z hz => le_sSup hz⟩
    · obtain ⟨z, hz, hgz⟩ := (Submodule.mem_sSup_of_directed hne hdir).mp hg
      exact (Submodule.mem_sSup_of_directed hne hdir).mpr ⟨z, hz, (hcS hz).2.1 h g hgz⟩
    · obtain ⟨z, hz, hfz⟩ := (Submodule.mem_sSup_of_directed hne hdir).mp hf'
      exact (hcS hz).2.2 hfz) ⊥ h0
  refine ⟨U, hU.prop.1, hU.prop.2.1, hU.prop.2.2, fun U' hUU' hU'c hU's hfU' => ?_⟩
  exact hU.eq_of_ge ⟨hU'c, hU's, hfU'⟩ hUU'

/- English proof (translation)
Establish `hq : U.mkQ f ≠ 0`. Rewrite using `[Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]` and apply the resulting hypothesis. Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ ((Formalism.AUTREP.GAf L n → ℂ) ⧸ U), φ (U.mkQ f) ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Conclude with `hq ((Module.forall_dual_apply_eq_zero_iff ℂ (U.mkQ f)).mp hcon)`. Use `⟨φ.comp U.mkQ, fun u hu => ?_, hφ⟩` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero U).mpr hu, map_zero]`.
-/
theorem exists_sep (U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)) (f : Formalism.AUTREP.GAf L n → ℂ) (hf : f ∉ U) :
    ∃ l : (Formalism.AUTREP.GAf L n → ℂ) →ₗ[ℂ] ℂ, (∀ u ∈ U, l u = 0) ∧ l f ≠ 0 := by
  have hq : U.mkQ f ≠ 0 := by
    rwa [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ ((Formalism.AUTREP.GAf L n → ℂ) ⧸ U), φ (U.mkQ f) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hq ((Module.forall_dual_apply_eq_zero_iff ℂ (U.mkQ f)).mp hcon)
  refine ⟨φ.comp U.mkQ, fun u hu => ?_, hφ⟩
  rw [LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero U).mpr hu, map_zero]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mc_apply (l : (Formalism.AUTREP.GAf L n → ℂ) →ₗ[ℂ] ℂ) (f : Formalism.AUTREP.GAf L n → ℂ) (g : Formalism.AUTREP.GAf L n) :
    mc l f g = l (Formalism.L2.NG.rt L n g f) := rfl

/- English proof (translation)
Use function extensionality and compare the values at `g`. Rewrite using `[mc_apply, rt_apply, mc_apply, rt_rt]`.
-/
theorem mc_rt (l : (Formalism.AUTREP.GAf L n → ℂ) →ₗ[ℂ] ℂ) (h : Formalism.AUTREP.GAf L n) (f : Formalism.AUTREP.GAf L n → ℂ) :
    mc l (Formalism.L2.NG.rt L n h f) = Formalism.L2.NG.rt L n h (mc l f) := by
  funext g
  rw [mc_apply, rt_apply, mc_apply, rt_rt]

/- English proof (translation)
Use function extensionality and compare the values at `g`. Rewrite using `[mc_apply, Pi.zero_apply]`. Conclude with `hl _ (hU g u hu)`.
-/
theorem mc_eq_zero {l : (Formalism.AUTREP.GAf L n → ℂ) →ₗ[ℂ] ℂ} {U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)} (hU : IsStable U)
    (hl : ∀ u ∈ U, l u = 0) {u : Formalism.AUTREP.GAf L n → ℂ} (hu : u ∈ U) : mc l u = 0 := by
  funext g
  rw [mc_apply, Pi.zero_apply]
  exact hl _ (hU g u hu)

/- English proof (translation)
Simplify using `[heckeG]`.
-/
theorem heckeG_apply {ι : Type} (s : Finset ι) (γ : ι → Formalism.AUTREP.GAf L n) (f : Formalism.AUTREP.GAf L n → ℂ) :
    heckeG s γ f = ∑ i ∈ s, Formalism.L2.NG.rt L n (γ i) f := by
  simp [heckeG]

/- English proof (translation)
Rewrite using `[heckeG_apply, heckeG_apply, map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => mc_rt l (γ i) f`.
-/
theorem mc_heckeG (l : (Formalism.AUTREP.GAf L n → ℂ) →ₗ[ℂ] ℂ) {ι : Type} (s : Finset ι) (γ : ι → Formalism.AUTREP.GAf L n)
    (f : Formalism.AUTREP.GAf L n → ℂ) : mc l (heckeG s γ f) = heckeG s γ (mc l f) := by
  rw [heckeG_apply, heckeG_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => mc_rt l (γ i) f

/- English proof (translation)
Introduce `κ hκ`. Rewrite using `[← mc_rt, hf κ hκ, map_smul]`.
-/
theorem mc_typeVec (l : (Formalism.AUTREP.GAf L n → ℂ) →ₗ[ℂ] ℂ) {J' : Set (Formalism.AUTREP.GAf L n)} {χ' : Formalism.AUTREP.GAf L n → ℂ}
    {f : Formalism.AUTREP.GAf L n → ℂ} (hf : IsTypeVec J' χ' f) : IsTypeVec J' χ' (mc l f) := by
  intro κ hκ
  rw [← mc_rt, hf κ hκ, map_smul]

def coMaxOf (f : Formalism.AUTREP.GAf L n → ℂ) (hf : f ≠ 0) : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ) :=
  (exists_coMax f hf).choose

/- English proof (translation)
Conclude with `(exists_coMax f hf).choose_spec`.
-/
theorem coMaxOf_spec (f : Formalism.AUTREP.GAf L n → ℂ) (hf : f ≠ 0) : IsCoMax f (coMaxOf f hf) := by
  exact (exists_coMax f hf).choose_spec

def lOf (f : Formalism.AUTREP.GAf L n → ℂ) (hf : f ≠ 0) : (Formalism.AUTREP.GAf L n → ℂ) →ₗ[ℂ] ℂ :=
  (exists_sep (coMaxOf f hf) f (coMaxOf_spec f hf).2.2.1).choose

/- English proof (translation)
Conclude with `(exists_sep (coMaxOf f hf) f (coMaxOf_spec f hf).2.2.1).choose_spec`.
-/
theorem lOf_spec (f : Formalism.AUTREP.GAf L n → ℂ) (hf : f ≠ 0) :
    (∀ u ∈ coMaxOf f hf, lOf f hf u = 0) ∧ lOf f hf f ≠ 0 := by
  exact (exists_sep (coMaxOf f hf) f (coMaxOf_spec f hf).2.2.1).choose_spec

def qOf (f : Formalism.AUTREP.GAf L n → ℂ) (hf : f ≠ 0) : (Formalism.AUTREP.GAf L n → ℂ) →ₗ[ℂ] (Formalism.AUTREP.GAf L n → ℂ) :=
  mc (lOf f hf)

def SOf (f : Formalism.AUTREP.GAf L n → ℂ) (hf : f ≠ 0) : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ) :=
  (cyc f).map (qOf f hf)

/- English proof (translation)
Introduce `h x hx`. Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.mp hx`. Conclude with `Submodule.mem_map.mpr ⟨_, cyc_stable f h y hy, mc_rt _ h y⟩`.
-/
theorem SOf_stable (f : Formalism.AUTREP.GAf L n → ℂ) (hf : f ≠ 0) : IsStable (SOf f hf) := by
  intro h x hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  exact Submodule.mem_map.mpr ⟨_, cyc_stable f h y hy, mc_rt _ h y⟩

/- English proof (translation)
Conclude with `Submodule.mem_map_of_mem (self_mem_cyc f)`.
-/
theorem qOf_self_mem (f : Formalism.AUTREP.GAf L n → ℂ) (hf : f ≠ 0) : qOf f hf f ∈ SOf f hf := by
  exact Submodule.mem_map_of_mem (self_mem_cyc f)

/- English proof (translation)
Introduce `h0`. Establish `h1` using `congrFun h0 1`. Rewrite `h1` using `[Pi.zero_apply]`. Apply `(lOf_spec f hf).2` to reduce the goal to its premises. Establish `h2 : qOf f hf f 1 = lOf f hf (Formalism.L2.NG.rt L n 1 f)` using `rfl`.

Rewrite `h1` using `[h2, rt_one]`. Conclude with `h1`.
-/
theorem qOf_self_ne (f : Formalism.AUTREP.GAf L n → ℂ) (hf : f ≠ 0) : qOf f hf f ≠ 0 := by
  intro h0
  have h1 := congrFun h0 1
  rw [Pi.zero_apply] at h1
  apply (lOf_spec f hf).2
  have h2 : qOf f hf f 1 = lOf f hf (Formalism.L2.NG.rt L n 1 f) := rfl
  rw [h2, rt_one] at h1
  exact h1

/- English proof (translation)
Introduce `h`. Establish `hm` using `qOf_self_mem f hf`. Rewrite `hm` using `[h, Submodule.mem_bot]`. Conclude with `qOf_self_ne f hf hm`.
-/
theorem SOf_ne (f : Formalism.AUTREP.GAf L n → ℂ) (hf : f ≠ 0) : SOf f hf ≠ ⊥ := by
  intro h
  have hm := qOf_self_mem f hf
  rw [h, Submodule.mem_bot] at hm
  exact qOf_self_ne f hf hm

/- English proof (translation)
Establish `hUspec` using `coMaxOf_spec f hf`. Establish `hl` using `lOf_spec f hf`. Set `W : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)` to `S'.comap (qOf f hf) ⊓ cyc f`. Establish `hWst : IsStable W`. Introduce `h g hg`.

Take `⟨hg1, hg2⟩` from `Submodule.mem_inf.mp hg`. Use `Submodule.mem_inf.mpr ⟨?_, cyc_stable f h g hg2⟩` and prove the remaining obligations. Use `show qOf f hf (Formalism.L2.NG.rt L n h g) ∈ S'`. Rewrite using `[show qOf f hf (Formalism.L2.NG.rt L n h g) = Formalism.L2.NG.rt L n h (qOf f hf g) from mc_rt _ h g]`. Conclude with `hst h _ hg1`.

Establish `hq0 : ∀ u ∈ coMaxOf f hf, qOf f hf u = 0` using `fun u hu => mc_eq_zero hUspec.2.1 hl.1 hu`. Establish `hUW : coMaxOf f hf ≤ W` using `fun u hu => Submodule.mem_inf.mpr ⟨by show qOf f hf u ∈ S'; rw [hq0 u hu]; exact S'.zero_mem, hUspec.1 hu⟩`. Distinguish the cases in `hfW : f ∈ W`. Use `right`. Use `le_antisymm hle ?_` and prove the remaining obligations.

Establish `hcW : cyc f ≤ W` using `cyc_le hWst hfW`. Introduce `x hx`. Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.mp hx`. Conclude with `(Submodule.mem_inf.mp (hcW hy)).1`. Use `left`.

Establish `hWU : W = coMaxOf f hf` using `hUspec.2.2.2 W hUW inf_le_right hWst hfW`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.mp (hle hx)`. Establish `hyW : y ∈ W` using `Submodule.mem_inf.mpr ⟨hx, hy⟩`.

Rewrite `hyW` using `[hWU]`. Rewrite using `[Submodule.mem_bot]`. Conclude with `hq0 y hyW`.
-/
theorem SOf_irr (f : Formalism.AUTREP.GAf L n → ℂ) (hf : f ≠ 0) (S' : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ))
    (hle : S' ≤ SOf f hf) (hst : ∀ h, ∀ g ∈ S', Formalism.L2.NG.rt L n h g ∈ S') : S' = ⊥ ∨ S' = SOf f hf := by
  classical
  have hUspec := coMaxOf_spec f hf
  have hl := lOf_spec f hf
  let W : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ) := S'.comap (qOf f hf) ⊓ cyc f
  have hWst : IsStable W := by
    intro h g hg
    obtain ⟨hg1, hg2⟩ := Submodule.mem_inf.mp hg
    refine Submodule.mem_inf.mpr ⟨?_, cyc_stable f h g hg2⟩
    show qOf f hf (Formalism.L2.NG.rt L n h g) ∈ S'
    rw [show qOf f hf (Formalism.L2.NG.rt L n h g) = Formalism.L2.NG.rt L n h (qOf f hf g) from mc_rt _ h g]
    exact hst h _ hg1
  have hq0 : ∀ u ∈ coMaxOf f hf, qOf f hf u = 0 := fun u hu => mc_eq_zero hUspec.2.1 hl.1 hu
  have hUW : coMaxOf f hf ≤ W := fun u hu => Submodule.mem_inf.mpr
    ⟨by show qOf f hf u ∈ S'; rw [hq0 u hu]; exact S'.zero_mem, hUspec.1 hu⟩
  by_cases hfW : f ∈ W
  · right
    refine le_antisymm hle ?_
    have hcW : cyc f ≤ W := cyc_le hWst hfW
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    exact (Submodule.mem_inf.mp (hcW hy)).1
  · left
    have hWU : W = coMaxOf f hf := hUspec.2.2.2 W hUW inf_le_right hWst hfW
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp (hle hx)
    have hyW : y ∈ W := Submodule.mem_inf.mpr ⟨hx, hy⟩
    rw [hWU] at hyW
    rw [Submodule.mem_bot]
    exact hq0 y hyW

/- English proof (translation)
Introduce `x hx`. Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.mp hx`. Take `⟨N, hN, hκ⟩` from `hsm y hy`. Use `⟨N, hN, fun κ hκN => ?_⟩` and prove the remaining obligations. Rewrite using `[show Formalism.L2.NG.rt L n κ (qOf f hf y) = qOf f hf (Formalism.L2.NG.rt L n κ y) from (mc_rt _ κ y).symm, hκ κ hκN]`.
-/
theorem SOf_smooth (f : Formalism.AUTREP.GAf L n → ℂ) (hf : f ≠ 0) (hsm : ∀ g ∈ cyc f, IsSmoothF g) :
    ∀ x ∈ SOf f hf, ∃ N : ℕ, 0 < N ∧ ∀ κ, Formalism.L2.NG.Cong L n N κ → Formalism.L2.NG.rt L n κ x = x := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  obtain ⟨N, hN, hκ⟩ := hsm y hy
  refine ⟨N, hN, fun κ hκN => ?_⟩
  rw [show Formalism.L2.NG.rt L n κ (qOf f hf y) = qOf f hf (Formalism.L2.NG.rt L n κ y) from (mc_rt _ κ y).symm,
    hκ κ hκN]

/- English proof (translation)
Establish `cong_dvd : ∀ (a b : ℕ) (κ : Formalism.AUTREP.GAf L n), Formalism.L2.NG.Cong L n (a * b) κ → Formalism.L2.NG.Cong L n a κ`. Introduce `a b κ hκ`. Unfold `Formalism.L2.NG.Cong at hκ ⊢`. Use `⟨hκ.1, fun i j => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, hy'⟩` from `hκ.2 i j`.

Use `⟨(b : _) * y, mul_mem (natCast_mem _ b) hy, ?_⟩` and prove the remaining obligations. Rewrite using `[hy', Nat.cast_mul, mul_assoc]`. Set `Sm : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)` to `{ carrier := {g | IsSmoothF g} zero_mem' := ⟨1, one_pos, fun κ _ => map_zero _⟩ add_mem' := by`. Introduce and unpack `a b ⟨N1, hN1, h1⟩ ⟨N2, hN2, h2⟩`. Use `⟨N1 * N2, Nat.mul_pos hN1 hN2, fun κ hκ => ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, h1 κ (cong_dvd N1 N2 κ hκ), h2 κ (cong_dvd N2 N1 κ (by rw [mul_comm]; exact hκ))]`. Use the proof step `smul_mem' := by`. Introduce and unpack `c a ⟨N1, hN1, h1⟩`. Conclude with `⟨N1, hN1, fun κ hκ => by rw [map_smul, h1 κ hκ]⟩ }`. Introduce `g hg`.

Establish `hle : cyc f ≤ Sm`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨h, rfl⟩`. Take `⟨N, hN, hκ⟩` from `h0`. Take `⟨N', hN', hcon⟩` from `hc h N hN`.

Use `⟨N', hN', fun κ hκ' => ?_⟩` and prove the remaining obligations. Rewrite using `[rt_rt, show κ * h = h * (h⁻¹ * κ * h) by group, ← rt_rt, hκ _ (hcon κ hκ')]`. Conclude with `hle hg`.
-/
theorem cyc_smooth (hc : CongConj L n) {f : Formalism.AUTREP.GAf L n → ℂ} (h0 : IsSmoothF f) : ∀ g ∈ cyc f, IsSmoothF g := by
  have cong_dvd : ∀ (a b : ℕ) (κ : Formalism.AUTREP.GAf L n), Formalism.L2.NG.Cong L n (a * b) κ →
      Formalism.L2.NG.Cong L n a κ := by
    intro a b κ hκ
    unfold Formalism.L2.NG.Cong at hκ ⊢
    refine ⟨hκ.1, fun i j => ?_⟩
    obtain ⟨y, hy, hy'⟩ := hκ.2 i j
    refine ⟨(b : _) * y, mul_mem (natCast_mem _ b) hy, ?_⟩
    rw [hy', Nat.cast_mul, mul_assoc]
  let Sm : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ) :=
    { carrier := {g | IsSmoothF g}
      zero_mem' := ⟨1, one_pos, fun κ _ => map_zero _⟩
      add_mem' := by
        rintro a b ⟨N1, hN1, h1⟩ ⟨N2, hN2, h2⟩
        refine ⟨N1 * N2, Nat.mul_pos hN1 hN2, fun κ hκ => ?_⟩
        rw [map_add, h1 κ (cong_dvd N1 N2 κ hκ),
          h2 κ (cong_dvd N2 N1 κ (by rw [mul_comm]; exact hκ))]
      smul_mem' := by
        rintro c a ⟨N1, hN1, h1⟩
        exact ⟨N1, hN1, fun κ hκ => by rw [map_smul, h1 κ hκ]⟩ }
  intro g hg
  have hle : cyc f ≤ Sm := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨h, rfl⟩
    obtain ⟨N, hN, hκ⟩ := h0
    obtain ⟨N', hN', hcon⟩ := hc h N hN
    refine ⟨N', hN', fun κ hκ' => ?_⟩
    rw [rt_rt, show κ * h = h * (h⁻¹ * κ * h) by group, ← rt_rt, hκ _ (hcon κ hκ')]
  exact hle hg

def finTypOf (f : Formalism.AUTREP.GAf L n → ℂ) (hf : f ≠ 0) (hsm : ∀ g ∈ cyc f, IsSmoothF g) : Formalism.L2.NG.FinTyp L n where
  S := SOf f hf
  stable := SOf_stable f hf
  smooth := SOf_smooth f hf hsm
  ne := SOf_ne f hf
  irr := SOf_irr f hf

/- English proof (translation)
Use `⟨qOf_self_mem f hf, qOf_self_ne f hf, fun J' χ' ht => mc_typeVec _ ht, fun s γ a ha => ?_⟩` and prove the remaining obligations. Use `show heckeG s γ (mc (lOf f hf) f) = a • mc (lOf f hf) f`. Rewrite using `[← mc_heckeG, ha, map_smul]`.
-/
theorem finTypOf_spec (f : Formalism.AUTREP.GAf L n → ℂ) (hf : f ≠ 0) (hsm : ∀ g ∈ cyc f, IsSmoothF g) :
    qOf f hf f ∈ (finTypOf f hf hsm).S ∧ qOf f hf f ≠ 0 ∧
      (∀ (J' : Set (Formalism.AUTREP.GAf L n)) (χ' : Formalism.AUTREP.GAf L n → ℂ), IsTypeVec J' χ' f → IsTypeVec J' χ' (qOf f hf f)) ∧
      ∀ {ι : Type} (s : Finset ι) (γ : ι → Formalism.AUTREP.GAf L n) (a : ℂ), heckeG s γ f = a • f →
        heckeG s γ (qOf f hf f) = a • qOf f hf f := by
  refine ⟨qOf_self_mem f hf, qOf_self_ne f hf, fun J' χ' ht => mc_typeVec _ ht, fun s γ a ha => ?_⟩
  show heckeG s γ (mc (lOf f hf) f) = a • mc (lOf f hf) f
  rw [← mc_heckeG, ha, map_smul]

/- English proof (translation)
Take `⟨T, hT⟩` from `hI`. Set `x' : π.S` to `⟨x, hx⟩`. Establish `hrt : ∀ h, ((T ⟨Formalism.L2.NG.rt L n h x, π.stable h x hx⟩ : π'.S) : Formalism.AUTREP.GAf L n → ℂ) = Formalism.L2.NG.rt L n h (T x')` using `fun h => hT h x' ⟨_, π.stable h x hx⟩ rfl`. Use `⟨T x', (T x').2, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`.

Apply `hx0` to reduce the goal to its premises. Establish `h1 : T x' = 0` using `Subtype.ext h0`. Establish `h2` using `T.injective (h1.trans (map_zero T).symm)`. Conclude with `congrArg Subtype.val h2`. Introduce `κ hκ`.

Rewrite using `[← hrt κ]`. Establish `e : (⟨Formalism.L2.NG.rt L n κ x, π.stable κ x hx⟩ : π.S) = χ' κ • x'` using `Subtype.ext (ht κ hκ)`. Rewrite using `[e, map_smul]`. Both sides reduce to the same expression. Rewrite using `[heckeG_apply]`.

Establish `e : (∑ i ∈ s, Formalism.L2.NG.rt L n (γ i) (T x' : Formalism.AUTREP.GAf L n → ℂ)) = ((T (∑ i ∈ s, (⟨Formalism.L2.NG.rt L n (γ i) x, π.stable (γ i) x hx⟩ : π.S)) : π'.S) : Formalism.AUTREP.GAf L n → ℂ)`. Rewrite using `[map_sum, Submodule.coe_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => (hrt (γ i)).symm`. Rewrite using `[e]`. Establish `e2 : (∑ i ∈ s, (⟨Formalism.L2.NG.rt L n (γ i) x, π.stable (γ i) x hx⟩ : π.S)) = a • x'`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Submodule.coe_sum, ← heckeG_apply, hh]`. Both sides reduce to the same expression. Rewrite using `[e2, map_smul]`. Both sides reduce to the same expression.
-/
theorem iso_transfer {π π' : Formalism.L2.NG.FinTyp L n} (hI : π.Iso π') {J' : Set (Formalism.AUTREP.GAf L n)}
    {χ' : Formalism.AUTREP.GAf L n → ℂ} {ι : Type} (s : Finset ι) (γ : ι → Formalism.AUTREP.GAf L n) (a : ℂ)
    {x : Formalism.AUTREP.GAf L n → ℂ} (hx : x ∈ π.S) (hx0 : x ≠ 0) (ht : IsTypeVec J' χ' x) (hh : heckeG s γ x = a • x) :
    ∃ y ∈ π'.S, y ≠ 0 ∧ IsTypeVec J' χ' y ∧ heckeG s γ y = a • y := by
  obtain ⟨T, hT⟩ := hI
  let x' : π.S := ⟨x, hx⟩
  have hrt : ∀ h, ((T ⟨Formalism.L2.NG.rt L n h x, π.stable h x hx⟩ : π'.S) : Formalism.AUTREP.GAf L n → ℂ) =
      Formalism.L2.NG.rt L n h (T x') := fun h => hT h x' ⟨_, π.stable h x hx⟩ rfl
  refine ⟨T x', (T x').2, ?_, ?_, ?_⟩
  · intro h0
    apply hx0
    have h1 : T x' = 0 := Subtype.ext h0
    have h2 := T.injective (h1.trans (map_zero T).symm)
    exact congrArg Subtype.val h2
  · intro κ hκ
    rw [← hrt κ]
    have e : (⟨Formalism.L2.NG.rt L n κ x, π.stable κ x hx⟩ : π.S) = χ' κ • x' := Subtype.ext (ht κ hκ)
    rw [e, map_smul]
    rfl
  · rw [heckeG_apply]
    have e : (∑ i ∈ s, Formalism.L2.NG.rt L n (γ i) (T x' : Formalism.AUTREP.GAf L n → ℂ)) =
        ((T (∑ i ∈ s, (⟨Formalism.L2.NG.rt L n (γ i) x, π.stable (γ i) x hx⟩ : π.S)) : π'.S) :
          Formalism.AUTREP.GAf L n → ℂ) := by
      rw [map_sum, Submodule.coe_sum]
      exact Finset.sum_congr rfl fun i _ => (hrt (γ i)).symm
    rw [e]
    have e2 : (∑ i ∈ s, (⟨Formalism.L2.NG.rt L n (γ i) x, π.stable (γ i) x hx⟩ : π.S)) = a • x' := by
      apply Subtype.ext
      rw [Submodule.coe_sum, ← heckeG_apply, hh]
      rfl
    rw [e2, map_smul]
    rfl

end CoreProofs

section Conc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance instCMHost (D : Formalism.BasicNotions.D7) : IsCMField D.host.E := D.host.isCMField_hostE

variable {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ)

structure RowPsi where
  ψ : Formalism.AUTREP.GAf D.host.E n →* GA D V
  inj : Function.Injective ψ
  into : ∀ h, ψ h ∈ GfC V
  onto : ∀ g ∈ GfC V, ∃ h, ψ h = g

variable {V n}

open Classical in

def pre (P : RowPsi V n) (γ : GA D V) : Formalism.AUTREP.GAf D.host.E n :=
  if h : ∃ x, P.ψ x = γ then h.choose else 1

def LevOK (P : RowPsi V n) (J : Set (GA D V)) (χ : GA D V → ℂ) : Prop :=
  ∃ N0 : ℕ, 0 < N0 ∧ ∀ κ, Formalism.L2.NG.Cong D.host.E n N0 κ → P.ψ κ ∈ J ∧ χ (P.ψ κ) = 1

def Hecke₃ (P : RowPsi V n) (R : Finset (GA D V)) :
    (Formalism.AUTREP.GAf D.host.E n → ℂ) →ₗ[ℂ] (Formalism.AUTREP.GAf D.host.E n → ℂ) :=
  heckeG R (pre P)

def HeckeScalar (P : RowPsi V n) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Prop :=
  ∀ Pr d R, Mult.Hecke₂ V J χ Sb Pr d R → HeckeScalarG (P.ψ ⁻¹' J) (fun κ => χ (P.ψ κ)) R (pre P)

variable {Sp : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))

def RowRepExists (P : RowPsi V n) (M : Mult.DSModel V Sp) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) : Prop :=
  ∃ rep : Mult.IxFull θ M J χ Sb e → Formalism.L2.NG.FinTyp D.host.E n,
    (∀ c c', (rep c).Iso (rep c') → c = c') ∧
    ∀ c, ∃ x ∈ (rep c).S, x ≠ 0 ∧ IsTypeVec (P.ψ ⁻¹' J) (fun κ => χ (P.ψ κ)) x ∧
      ∀ Pr d R, Mult.Hecke₂ V J χ Sb Pr d R → Hecke₃ P R x = c.1 Pr d • x

end Conc

section ConcProofs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance instCMHost' (D : Formalism.BasicNotions.D7) : IsCMField D.host.E := D.host.isCMField_hostE

variable {D : Formalism.BasicNotions.D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ}
variable {Sp : D.what₂.Tau → SPar} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
variable {M : Mult.DSModel V Sp} {J : Set (GA D V)} {χ : GA D V → ℂ} {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))}
variable {e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)}

/- English proof (translation)
Introduce `v k hk g`. Proceed by induction on `hT using Submodule.span_induction with`. Consider the case `mem x hx => exact hx.lev v k hk g`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`.

Simplify using `only [MultilinearMap.add_apply, Pi.add_apply, hx, hy]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `smul a x _ hx`. Simplify using `only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mult_lev {T : Mult.MMap M} (hT : T ∈ Mult.Mult θ M J χ) : ∀ v, ∀ k ∈ J, ∀ g, T v (g * k) = χ k * T v g := by
  intro v k hk g
  induction hT using Submodule.span_induction with
  | mem x hx => exact hx.lev v k hk g
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [MultilinearMap.add_apply, Pi.add_apply, hx, hy]
    ring
  | smul a x _ hx =>
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx]
    ring

/- English proof (translation)
Unfold `pre`. Rewrite using `[dif_pos (P.onto γ hγ)]`. Conclude with `(P.onto γ hγ).choose_spec`.
-/
theorem pre_spec (P : RowPsi V n) {γ : GA D V} (hγ : γ ∈ GfC V) : P.ψ (pre P γ) = γ := by
  unfold pre
  rw [dif_pos (P.onto γ hγ)]
  exact (P.onto γ hγ).choose_spec

/- English proof (translation)
Take `⟨T, hT, hT0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot c.2.2`. Use `⟨T, hT, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hT0 (MultilinearMap.ext fun v => funext fun g => hcon v g)`.
-/
theorem exists_wit (c : Mult.IxFull θ M J χ Sb e) :
    ∃ T : Mult.MMap M, T ∈ Mult.partFull θ M J χ Sb c.1 ⊓ Mult.goodPart θ M J χ e ∧ ∃ v g0, T v g0 ≠ 0 := by
  obtain ⟨T, hT, hT0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot c.2.2
  refine ⟨T, hT, ?_⟩
  by_contra hcon
  push_neg at hcon
  exact hT0 (MultilinearMap.ext fun v => funext fun g => hcon v g)

def witT (c : Mult.IxFull θ M J χ Sb e) : Mult.MMap M := (exists_wit c).choose

def witV (c : Mult.IxFull θ M J χ Sb e) : M.Vec := (exists_wit c).choose_spec.2.choose

def witG (c : Mult.IxFull θ M J χ Sb e) : GA D V := (exists_wit c).choose_spec.2.choose_spec.choose

/- English proof (translation)
Conclude with `(exists_wit c).choose_spec.1`.
-/
theorem witT_mem (c : Mult.IxFull θ M J χ Sb e) :
    witT c ∈ Mult.partFull θ M J χ Sb c.1 ⊓ Mult.goodPart θ M J χ e := by
  exact (exists_wit c).choose_spec.1

/- English proof (translation)
Conclude with `(exists_wit c).choose_spec.2.choose_spec.choose_spec`.
-/
theorem wit_ne (c : Mult.IxFull θ M J χ Sb e) : witT c (witV c) (witG c) ≠ 0 := by
  exact (exists_wit c).choose_spec.2.choose_spec.choose_spec

def srcOf (P : RowPsi V n) (c : Mult.IxFull θ M J χ Sb e) : Formalism.AUTREP.GAf D.host.E n → ℂ :=
  fun h => witT c (witV c) (witG c * P.ψ h)

/- English proof (translation)
Introduce `h0`. Establish `h1` using `congrFun h0 1`. Simplify using `only [srcOf, map_one, mul_one, Pi.zero_apply] at h1`. Conclude with `wit_ne c h1`.
-/
theorem srcOf_ne (P : RowPsi V n) (c : Mult.IxFull θ M J χ Sb e) : srcOf P c ≠ 0 := by
  intro h0
  have h1 := congrFun h0 1
  simp only [srcOf, map_one, mul_one, Pi.zero_apply] at h1
  exact wit_ne c h1

/- English proof (translation)
Introduce `κ hκ`. Use function extensionality and compare the values at `h`. Rewrite using `[rt_apply, Pi.smul_apply, smul_eq_mul]`. Simplify using `only [srcOf, map_mul, ← mul_assoc]`. Conclude with `mult_lev (Submodule.mem_inf.mp (Submodule.mem_inf.mp (witT_mem c)).1).1 (witV c) (P.ψ κ) hκ (witG c * P.ψ h)`.
-/
theorem srcOf_type (P : RowPsi V n) (c : Mult.IxFull θ M J χ Sb e) :
    IsTypeVec (P.ψ ⁻¹' J) (fun κ => χ (P.ψ κ)) (srcOf P c) := by
  intro κ hκ
  funext h
  rw [rt_apply, Pi.smul_apply, smul_eq_mul]
  simp only [srcOf, map_mul, ← mul_assoc]
  exact mult_lev (Submodule.mem_inf.mp (Submodule.mem_inf.mp (witT_mem c)).1).1 (witV c) (P.ψ κ) hκ
    (witG c * P.ψ h)

/- English proof (translation)
Take `⟨N0, hN0, hκ⟩` from `hl`. Use `⟨N0, hN0, fun κ hκN => ?_⟩` and prove the remaining obligations. Establish `h1` using `srcOf_type P c κ (hκ κ hκN).1`. Simplify using `only [(hκ κ hκN).2, one_smul] at h1`. Conclude with `h1`.
-/
theorem srcOf_smooth (P : RowPsi V n) (hl : LevOK P J χ) (c : Mult.IxFull θ M J χ Sb e) : IsSmoothF (srcOf P c) := by
  obtain ⟨N0, hN0, hκ⟩ := hl
  refine ⟨N0, hN0, fun κ hκN => ?_⟩
  have h1 := srcOf_type P c κ (hκ κ hκN).1
  simp only [(hκ κ hκN).2, one_smul] at h1
  exact h1

/- English proof (translation)
Establish `hrep : ∀ γ ∈ R, γ ∈ GfC V`. Take `⟨_, _, _, _, -, -, -, -, -, -, -, -, -, -, hrep⟩` from `id hR`. Conclude with `fun γ hγ => (hrep.1 γ hγ).1`. Establish `hmem` using `Submodule.mem_inf.mp (Submodule.mem_inf.mp (witT_mem c)).1`. Establish `hker : witT c ∈ LinearMap.ker (Mult.heckeOn M R - c.1 Pr d • LinearMap.id)` using `(Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hmem.2 Pr) d) R) hR`.

Establish `hT : Mult.heckeOn M R (witT c) = c.1 Pr d • witT c`. Establish `h1` using `LinearMap.mem_ker.mp hker`. Rewrite `h1` using `[LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]`. Then use the resulting hypothesis. Establish `hTvg : ∀ g, ∑ γ ∈ R, witT c (witV c) (g * γ) = c.1 Pr d * witT c (witV c) g`. Introduce `g`.

Establish `h1` using `congrArg (fun T : Mult.MMap M => T (witV c) g) hT`. Simplify `h1` using `[Mult.heckeOn, Mult.postOn, Mult.heckeLin]`. Use function extensionality and compare the values at `h`. Rewrite using `[Hecke₃, heckeG_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Simplify using `only [rt_apply, srcOf, map_mul]`.

Rewrite using `[← hTvg]`. Use `Finset.sum_congr rfl fun γ hγ => ?_` and prove the remaining obligations. Rewrite using `[pre_spec P (hrep γ hγ), mul_assoc]`.
-/
theorem srcOf_hecke (P : RowPsi V n) (c : Mult.IxFull θ M J χ Sb e) {Pr : HeightOneSpectrum (𝓞 D.host.E)} {d : List ℤ}
    {R : Finset (GA D V)} (hR : Mult.Hecke₂ V J χ Sb Pr d R) : Hecke₃ P R (srcOf P c) = c.1 Pr d • srcOf P c := by
  have hrep : ∀ γ ∈ R, γ ∈ GfC V := by
    obtain ⟨_, _, _, _, -, -, -, -, -, -, -, -, -, -, hrep⟩ := id hR
    exact fun γ hγ => (hrep.1 γ hγ).1
  have hmem := Submodule.mem_inf.mp (Submodule.mem_inf.mp (witT_mem c)).1
  have hker : witT c ∈ LinearMap.ker (Mult.heckeOn M R - c.1 Pr d • LinearMap.id) :=
    (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp
      ((Submodule.mem_iInf _).mp hmem.2 Pr) d) R) hR
  have hT : Mult.heckeOn M R (witT c) = c.1 Pr d • witT c := by
    have h1 := LinearMap.mem_ker.mp hker
    rwa [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h1
  have hTvg : ∀ g, ∑ γ ∈ R, witT c (witV c) (g * γ) = c.1 Pr d * witT c (witV c) g := by
    intro g
    have h1 := congrArg (fun T : Mult.MMap M => T (witV c) g) hT
    simpa [Mult.heckeOn, Mult.postOn, Mult.heckeLin] using h1
  funext h
  rw [Hecke₃, heckeG_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [rt_apply, srcOf, map_mul]
  rw [← hTvg]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  rw [pre_spec P (hrep γ hγ), mul_assoc]

def rowRep (P : RowPsi V n) (hc : CongConj D.host.E n) (hl : LevOK P J χ) (c : Mult.IxFull θ M J χ Sb e) :
    Formalism.L2.NG.FinTyp D.host.E n :=
  finTypOf (srcOf P c) (srcOf_ne P c) (cyc_smooth hc (srcOf_smooth P hl c))

/- English proof (translation)
Take `⟨h1, h2, h3, h4⟩` from `finTypOf_spec (srcOf P c) (srcOf_ne P c) (cyc_smooth hc (srcOf_smooth P hl c))`. Conclude with `⟨_, h1, h2, h3 _ _ (srcOf_type P c), fun Pr d R hR => h4 R (pre P) _ (srcOf_hecke P c hR)⟩`.
-/
theorem rowRep_spec (P : RowPsi V n) (hc : CongConj D.host.E n) (hl : LevOK P J χ) (c : Mult.IxFull θ M J χ Sb e) :
    ∃ x ∈ (rowRep P hc hl c).S, x ≠ 0 ∧ IsTypeVec (P.ψ ⁻¹' J) (fun κ => χ (P.ψ κ)) x ∧
      ∀ Pr d R, Mult.Hecke₂ V J χ Sb Pr d R → Hecke₃ P R x = c.1 Pr d • x := by
  obtain ⟨h1, h2, h3, h4⟩ :=
    finTypOf_spec (srcOf P c) (srcOf_ne P c) (cyc_smooth hc (srcOf_smooth P hl c))
  exact ⟨_, h1, h2, h3 _ _ (srcOf_type P c), fun Pr d R hR => h4 R (pre P) _ (srcOf_hecke P c hR)⟩

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `Pr d`. Distinguish the cases in `hH : ∃ R, Mult.Hecke₂ V J χ Sb Pr d R`. Take `⟨R, hR⟩` from `hH`. Take `⟨x, hx, hx0, hxt, hxh⟩` from `rowRep_spec P hc hl c`.

Take `⟨x', hx', hx0', hxt', hxh'⟩` from `rowRep_spec P hc hl c'`. Take `⟨y, hy, hy0, hyt, hyh⟩` from `iso_transfer hI R (pre P) (c.1 Pr d) hx hx0 hxt (hxh Pr d R hR)`. Take `⟨a, ha⟩` from `hS Pr d R hR (rowRep P hc hl c')`. Establish `e1 : c.1 Pr d • y = a • y` using `hyh.symm.trans (ha y hy hyt)`. Establish `e2 : c'.1 Pr d • x' = a • x'` using `(hxh' Pr d R hR).symm.trans (ha x' hx' hxt')`.

Conclude with `(smul_left_injective ℂ hy0 e1).trans (smul_left_injective ℂ hx0' e2).symm`. Rewrite using `[c.2.1 Pr d hH, c'.2.1 Pr d hH]`.
-/
theorem rowRep_inj (P : RowPsi V n) (hc : CongConj D.host.E n) (hl : LevOK P J χ) (hS : HeckeScalar P J χ Sb)
    (c c' : Mult.IxFull θ M J χ Sb e) (hI : (rowRep P hc hl c).Iso (rowRep P hc hl c')) : c = c' := by
  apply Subtype.ext
  funext Pr d
  by_cases hH : ∃ R, Mult.Hecke₂ V J χ Sb Pr d R
  · obtain ⟨R, hR⟩ := hH
    obtain ⟨x, hx, hx0, hxt, hxh⟩ := rowRep_spec P hc hl c
    obtain ⟨x', hx', hx0', hxt', hxh'⟩ := rowRep_spec P hc hl c'
    obtain ⟨y, hy, hy0, hyt, hyh⟩ := iso_transfer hI R (pre P) (c.1 Pr d) hx hx0 hxt (hxh Pr d R hR)
    obtain ⟨a, ha⟩ := hS Pr d R hR (rowRep P hc hl c')
    have e1 : c.1 Pr d • y = a • y := hyh.symm.trans (ha y hy hyt)
    have e2 : c'.1 Pr d • x' = a • x' := (hxh' Pr d R hR).symm.trans (ha x' hx' hxt')
    exact (smul_left_injective ℂ hy0 e1).trans (smul_left_injective ℂ hx0' e2).symm
  · rw [c.2.1 Pr d hH, c'.2.1 Pr d hH]

/- English proof (translation)
Conclude with `⟨rowRep P hc hl, fun c c' h => rowRep_inj P hc hl hS c c' h, rowRep_spec P hc hl⟩`.
-/
theorem rowRepExists_of (P : RowPsi V n) (hc : CongConj D.host.E n) (hl : LevOK P J χ) (hS : HeckeScalar P J χ Sb) :
    RowRepExists θ P M J χ Sb e := by
  exact ⟨rowRep P hc hl, fun c c' h => rowRep_inj P hc hl hS c c' h, rowRep_spec P hc hl⟩

end ConcProofs

end Formalism.IndefR.principalLevelFrame
