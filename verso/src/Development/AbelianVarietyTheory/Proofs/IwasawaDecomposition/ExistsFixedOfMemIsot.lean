import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.ConjSubConjSub
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowFix

open Formalism.L2.NG Formalism.IndefR.principalLevelFrame

/- English proof (translation)
Set `ι` to `{Φ : π.S →ₗ[ℂ] A // IsEqvA ρ π Φ ∧ Q Φ}`. Establish `hy' : y ∈ ⨆ j : ι, LinearMap.range j.1`. Rewrite `hy` using `[iSup_subtype']`. Then use the resulting hypothesis. Take `⟨s, hs⟩` from `Submodule.mem_iSup_iff_exists_finset.1 hy'`. Set `Y : Finset ι → Submodule ℂ A` to `fun t => ⨆ j ∈ t, LinearMap.range j.1`.

Establish `hYst : ∀ (t : Finset ι) (g : Formalism.AUTREP.GAf L n) (x : A), x ∈ Y t → ρ g x ∈ Y t`. Introduce `t g x hx`. Establish `hle : Y t ≤ (Y t).comap (ρ g)`. Use `iSup₂_le fun j hj => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, rfl⟩`.

Rewrite using `[Submodule.mem_comap, ← j.2.1 g v]`. Conclude with `(le_iSup₂ (f := fun j (_ : j ∈ t) => LinearMap.range j.1) j hj) (LinearMap.mem_range_self _ _)`. Conclude with `hle hx`. Establish `key : ∀ (t : Finset ι) (x : A), x ∈ Y t → x ≠ 0 → (∀ κ, Kp κ → ρ κ x = x) → ∃ f ∈ π.S, f ≠ 0 ∧ ∀ κ, Kp κ → rt L n κ f = f`. Introduce `t`.

Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty`. Introduce `x hx hx0 _`. Conclude with `absurd (by simpa [Y] using hx) hx0`. Consider the case `insert j t hjt ih`.

Introduce `x hx hx0 hxfix`. Establish `hx' : x ∈ LinearMap.range j.1 ⊔ Y t`. Simplify `hx` using `[Y, Finset.iSup_insert]`. Take `⟨_, ⟨v, rfl⟩, z, hz, rfl⟩` from `Submodule.mem_sup.1 hx'`. Set `U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)` to `((Y t).comap j.1).map π.S.subtype`.

Establish `hUst : ∀ h, ∀ f ∈ U, rt L n h f ∈ U`. Introduce and unpack `h _ ⟨a, ha, rfl⟩`. Use `⟨⟨rt L n h a, π.stable h a a.2⟩, ?_, rfl⟩` and prove the remaining obligations. Establish `ha' : j.1 a ∈ Y t` using `ha`. Use `show j.1 _ ∈ Y t`.

Rewrite using `[j.2.1 h a]`. Conclude with `hYst t h _ ha'`. Break down `π.irr U (Submodule.map_subtype_le _ _) hUst with hU | hU` into its components or cases. Establish `hvfix : ∀ κ, Kp κ → rt L n κ (v : Formalism.AUTREP.GAf L n → ℂ) = v`. Introduce `κ hκ`.

Set `v' : π.S` to `⟨rt L n κ v, π.stable κ v v.2⟩`. Establish `hmem : v' - v ∈ (Y t).comap j.1`. Rewrite using `[Submodule.mem_comap, map_sub, j.2.1 κ v]`. Establish `h1` using `hxfix κ hκ`. Rewrite `h1` using `[map_add]`.

Establish `h3 : ρ κ (j.1 v) - j.1 v = z - ρ κ z`. Rewrite using `[sub_eq_sub_iff_add_eq_add, h1, add_comm]`. Rewrite using `[h3]`. Conclude with `sub_mem hz (hYst t κ z hz)`. Establish `hU' : ((v' - v : π.S) : Formalism.AUTREP.GAf L n → ℂ) ∈ U` using `⟨_, hmem, rfl⟩`.

Rewrite `hU'` using `[hU, Submodule.mem_bot]`. Conclude with `sub_eq_zero.1 hU'`. Distinguish the cases in `hv : (v : Formalism.AUTREP.GAf L n → ℂ) = 0`. Establish `hv' : v = 0` using `Subtype.ext hv`. Substitute `hv'` using the available equality.

Simplify using `only [map_zero, zero_add] at hx0 hxfix`. Conclude with `ih z hz hx0 hxfix`. Conclude with `⟨v, v.2, hv, hvfix⟩`. Establish `hvU : (v : Formalism.AUTREP.GAf L n → ℂ) ∈ U` using `by rw [hU]; exact v.2`. Take `⟨a, ha, hav⟩` from `hvU`.

Establish `: a = v` using `Subtype.ext hav`. Substitute `this` using the available equality. Conclude with `ih _ (add_mem ha hz) hx0 hxfix`. Conclude with `key s y (by simpa [Y] using hs) hy0 hfix`.
-/
theorem exists_fixed_of_mem_isot {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {A : Type} [AddCommGroup A] [Module ℂ A] (ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A)
    (π : FinTyp L n) (Q : (π.S →ₗ[ℂ] A) → Prop) (Kp : Formalism.AUTREP.GAf L n → Prop) {y : A}
    (hy : y ∈ ⨆ (Φ : π.S →ₗ[ℂ] A) (_ : IsEqvA ρ π Φ ∧ Q Φ), LinearMap.range Φ) (hy0 : y ≠ 0)
    (hfix : ∀ κ, Kp κ → ρ κ y = y) :
    ∃ f ∈ π.S, f ≠ 0 ∧ ∀ κ, Kp κ → rt L n κ f = f := by
  classical
  let ι := {Φ : π.S →ₗ[ℂ] A // IsEqvA ρ π Φ ∧ Q Φ}
  have hy' : y ∈ ⨆ j : ι, LinearMap.range j.1 := by
    rwa [iSup_subtype'] at hy
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hy'
  let Y : Finset ι → Submodule ℂ A := fun t => ⨆ j ∈ t, LinearMap.range j.1
  have hYst : ∀ (t : Finset ι) (g : Formalism.AUTREP.GAf L n) (x : A), x ∈ Y t → ρ g x ∈ Y t := by
    intro t g x hx
    have hle : Y t ≤ (Y t).comap (ρ g) := by
      refine iSup₂_le fun j hj => ?_
      rintro _ ⟨v, rfl⟩
      rw [Submodule.mem_comap, ← j.2.1 g v]
      exact (le_iSup₂ (f := fun j (_ : j ∈ t) => LinearMap.range j.1) j hj) (LinearMap.mem_range_self _ _)
    exact hle hx
  have key : ∀ (t : Finset ι) (x : A), x ∈ Y t → x ≠ 0 → (∀ κ, Kp κ → ρ κ x = x) →
      ∃ f ∈ π.S, f ≠ 0 ∧ ∀ κ, Kp κ → rt L n κ f = f := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro x hx hx0 _
      exact absurd (by simpa [Y] using hx) hx0
    | insert j t hjt ih =>
      intro x hx hx0 hxfix
      have hx' : x ∈ LinearMap.range j.1 ⊔ Y t := by
        simpa [Y, Finset.iSup_insert] using hx
      obtain ⟨_, ⟨v, rfl⟩, z, hz, rfl⟩ := Submodule.mem_sup.1 hx'
      let U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ) := ((Y t).comap j.1).map π.S.subtype
      have hUst : ∀ h, ∀ f ∈ U, rt L n h f ∈ U := by
        rintro h _ ⟨a, ha, rfl⟩
        refine ⟨⟨rt L n h a, π.stable h a a.2⟩, ?_, rfl⟩
        have ha' : j.1 a ∈ Y t := ha
        show j.1 _ ∈ Y t
        rw [j.2.1 h a]
        exact hYst t h _ ha'
      rcases π.irr U (Submodule.map_subtype_le _ _) hUst with hU | hU
      ·
        have hvfix : ∀ κ, Kp κ → rt L n κ (v : Formalism.AUTREP.GAf L n → ℂ) = v := by
          intro κ hκ
          let v' : π.S := ⟨rt L n κ v, π.stable κ v v.2⟩
          have hmem : v' - v ∈ (Y t).comap j.1 := by
            rw [Submodule.mem_comap, map_sub, j.2.1 κ v]
            have h1 := hxfix κ hκ
            rw [map_add] at h1
            have h3 : ρ κ (j.1 v) - j.1 v = z - ρ κ z := by
              rw [sub_eq_sub_iff_add_eq_add, h1, add_comm]
            rw [h3]
            exact sub_mem hz (hYst t κ z hz)
          have hU' : ((v' - v : π.S) : Formalism.AUTREP.GAf L n → ℂ) ∈ U := ⟨_, hmem, rfl⟩
          rw [hU, Submodule.mem_bot] at hU'
          exact sub_eq_zero.1 hU'
        by_cases hv : (v : Formalism.AUTREP.GAf L n → ℂ) = 0
        · have hv' : v = 0 := Subtype.ext hv
          subst hv'
          simp only [map_zero, zero_add] at hx0 hxfix
          exact ih z hz hx0 hxfix
        · exact ⟨v, v.2, hv, hvfix⟩
      · have hvU : (v : Formalism.AUTREP.GAf L n → ℂ) ∈ U := by rw [hU]; exact v.2
        obtain ⟨a, ha, hav⟩ := hvU
        have : a = v := Subtype.ext hav
        subst this
        exact ih _ (add_mem ha hz) hx0 hxfix
  exact key s y (by simpa [Y] using hs) hy0 hfix

/- English proof (translation)
Introduce `D V n Sp θ P M J χ e σ Kp hK`. Take `⟨b, hb⟩` from `rowRepR_occ θ σ`. Take `⟨y, hy, hy0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hb`. Establish `hy' : y ∈ Formalism.IndefR.Mult.goodPart θ M (J b) (χ b) (e b) ⊓ isotIn (actM P M) (Minf θ P M) (FinTyp.conjT (rowRepR θ σ))` using `hy`. Rewrite `hy'` using `[Submodule.mem_inf]`.

Establish `hM : y ∈ Formalism.IndefR.Mult.Mult θ M (J b) (χ b)` using `(Submodule.mem_inf.1 hy'.1).1`. Establish `hfixY : ∀ κ, Kp κ → actM P M κ y = y`. Introduce `κ hκ`. Establish `hle : Formalism.IndefR.Mult.Mult θ M (J b) (χ b) ≤ LinearMap.ker (actM P M κ - LinearMap.id)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce `T hT`. Establish `hT' : Formalism.IndefR.Mult.IsMultMap θ M (J b) (χ b) T` using `hT`. Rewrite using `[SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]`. Apply `MultilinearMap.ext` to reduce the goal to its premises. Introduce `v`.

Use function extensionality and compare the values at `g`. Rewrite using `[actM_apply, hT'.lev v _ (hK b κ hκ).1 g, (hK b κ hκ).2, one_mul]`. Establish `h` using `hle hM`. Rewrite `h` using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]`. Conclude with `h`.

Take `⟨f, hf, hf0, hffix⟩` from `exists_fixed_of_mem_isot (actM P M) (FinTyp.conjT (rowRepR θ σ)) (fun Φ => LinearMap.range Φ ≤ Minf θ P M) Kp hy'.2 hy0 hfixY`. Use `⟨fun g => star (f g), (mem_conjSub).1 hf, ?_, fun κ hκ => ?_⟩` and prove the remaining obligations. Introduce `h0`. Apply `hf0` to reduce the goal to its premises. Use function extensionality and compare the values at `g`.

Use `congrFun h0 g` as an intermediate fact. Simplify using `using this`. Rewrite using `[← conj_rt, hffix κ hκ]`.
-/
theorem exists_fixed_rowRep : ∀ (D : D7) (V : HSp D) (n : ℕ) (Sp : D.what₂.Tau → SPar) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (P : principalLevelFrame.RowPsi V n) (M : Mult.DSModel V Sp) (J : Bool → Set (GA D V)) (χ : Bool → GA D V → ℂ) (e : Bool → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (σ : principalLevelFrame.FTR θ P M J χ e) (Kp : Formalism.AUTREP.GAf D.host.E n → Prop), (∀ b κ, Kp κ → P.ψ κ ∈ J b ∧ χ b (P.ψ κ) = 1) → ∃ f ∈ (principalLevelFrame.rowRepR θ σ).S, f ≠ 0 ∧ ∀ κ, Kp κ → NG.rt D.host.E n κ f = f := by
  intro D V n Sp θ P M J χ e σ Kp hK
  obtain ⟨b, hb⟩ := rowRepR_occ θ σ
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  have hy' : y ∈ Formalism.IndefR.Mult.goodPart θ M (J b) (χ b) (e b) ⊓
      isotIn (actM P M) (Minf θ P M) (FinTyp.conjT (rowRepR θ σ)) := hy
  rw [Submodule.mem_inf] at hy'
  have hM : y ∈ Formalism.IndefR.Mult.Mult θ M (J b) (χ b) := (Submodule.mem_inf.1 hy'.1).1
  have hfixY : ∀ κ, Kp κ → actM P M κ y = y := by
    intro κ hκ
    have hle : Formalism.IndefR.Mult.Mult θ M (J b) (χ b) ≤ LinearMap.ker (actM P M κ - LinearMap.id) := by
      refine Submodule.span_le.2 ?_
      intro T hT
      have hT' : Formalism.IndefR.Mult.IsMultMap θ M (J b) (χ b) T := hT
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      apply MultilinearMap.ext
      intro v
      funext g
      rw [actM_apply, hT'.lev v _ (hK b κ hκ).1 g, (hK b κ hκ).2, one_mul]
    have h := hle hM
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h
    exact h
  obtain ⟨f, hf, hf0, hffix⟩ := exists_fixed_of_mem_isot (actM P M) (FinTyp.conjT (rowRepR θ σ))
    (fun Φ => LinearMap.range Φ ≤ Minf θ P M) Kp hy'.2 hy0 hfixY
  refine ⟨fun g => star (f g), (mem_conjSub).1 hf, ?_, fun κ hκ => ?_⟩
  · intro h0
    apply hf0
    funext g
    have := congrFun h0 g
    simpa using this
  · rw [← conj_rt, hffix κ hκ]

end GlobalTheory.RowFix
