import Mathlib
import GroundTheory.AutomorphicForms.GeometricLemmaCompact
import GroundTheory.AutomorphicForms.GeometricLemmaAverage
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

section PermConj

variable {β : Fin n → ℕ} (w : Equiv.Perm (Fin n))

variable (F β) in

def permConj : blockUpper F n (β ∘ w) →* blockUpper F n β where
  toFun x := ⟨permGL F w * x * (permGL F w)⁻¹, (conj_permGL_mem_blockUpper_iff w).2 x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_permConj (x : blockUpper F n (β ∘ w)) :
    ((permConj F β w x : blockUpper F n β) : GL (Fin n) F) =
      permGL F w * x * (permGL F w)⁻¹ := rfl

variable {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)

variable (β) in

def cellRep : Representation ℂ (blockUpper F n (β ∘ w)) W :=
  (inflateTwist F n β σ).comp (permConj F β w)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cellRep_apply (x : blockUpper F n (β ∘ w)) (v : W) :
    cellRep β w σ x v = inflateTwist F n β σ (permConj F β w x) v := rfl

/- English proof (translation)
Establish `h` using `((mem_parabolicIndSpace σ).1 f.2).1 (permConj F β w x) (permGL F w * y)`. Rewrite `h` using `[coe_permConj]`. Rewrite using `[cellRep_apply, inflateTwist_apply, ← h]`. Use `group`.
-/
theorem parabolicInd_permGL_mul (f : parabolicIndSpace F n β σ) (x : blockUpper F n (β ∘ w))
    (y : GL (Fin n) F) :
    (f : GL (Fin n) F → W) (permGL F w * ((x : GL (Fin n) F) * y)) =
      cellRep β w σ x ((f : GL (Fin n) F → W) (permGL F w * y)) := by
  have h := ((mem_parabolicIndSpace σ).1 f.2).1 (permConj F β w x) (permGL F w * y)
  rw [coe_permConj] at h
  rw [cellRep_apply, inflateTwist_apply, ← h]
  group

end PermConj

section Subgroups

variable (F) (β γ : Fin n → ℕ) (w : Equiv.Perm (Fin n))

def cellUnipotent : Subgroup (GL (Fin n) F) :=
  unipotentRadical F n γ ⊓ blockUpper F n (β ∘ w)

def cellLeviParabolic : Subgroup (GL (Fin n) F) :=
  levi F n γ ⊓ blockUpper F n (β ∘ w)

variable {F β γ w}

/- English proof (translation)
The claim follows from `inf_le_right`.
-/
theorem cellUnipotent_le_blockUpper : cellUnipotent F β γ w ≤ blockUpper F n (β ∘ w) :=
  inf_le_right

/- English proof (translation)
The claim follows from `inf_le_left`.
-/
theorem cellUnipotent_le_unipotentRadical : cellUnipotent F β γ w ≤ unipotentRadical F n γ :=
  inf_le_left

/- English proof (translation)
The claim follows from `inf_le_right`.
-/
theorem cellLeviParabolic_le_blockUpper : cellLeviParabolic F β γ w ≤ blockUpper F n (β ∘ w) :=
  inf_le_right

/- English proof (translation)
The claim follows from `inf_le_left`.
-/
theorem cellLeviParabolic_le_levi : cellLeviParabolic F β γ w ≤ levi F n γ :=
  inf_le_left

/- English proof (translation)
Assemble the required witnesses or components as `⟨conj_mem_unipotentRadical (levi_le_blockUpper hb.1) ha.1, (blockUpper F n (β ∘ w)).mul_mem ((blockUpper F n (β ∘ w)).mul_mem hb.2 ha.2) ((blockUpper F n (β ∘ w)).inv_mem hb.2)⟩`.
-/
theorem conj_mem_cellUnipotent {b a : GL (Fin n) F} (hb : b ∈ cellLeviParabolic F β γ w)
    (ha : a ∈ cellUnipotent F β γ w) : b * a * b⁻¹ ∈ cellUnipotent F β γ w :=
  ⟨conj_mem_unipotentRadical (levi_le_blockUpper hb.1) ha.1,
    (blockUpper F n (β ∘ w)).mul_mem ((blockUpper F n (β ∘ w)).mul_mem hb.2 ha.2)
      ((blockUpper F n (β ∘ w)).inv_mem hb.2)⟩

variable {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)

variable (β γ w) in

def cellRepA : Representation ℂ (cellUnipotent F β γ w) W :=
  (cellRep β w σ).comp (Subgroup.inclusion cellUnipotent_le_blockUpper)

variable (β γ w) in

def cellRepM : Representation ℂ (cellLeviParabolic F β γ w) W :=
  (cellRep β w σ).comp (Subgroup.inclusion cellLeviParabolic_le_blockUpper)

/- English proof (translation)
The claim follows from `parabolicInd_permGL_mul w σ f (Subgroup.inclusion cellUnipotent_le_blockUpper a) y`.
-/
theorem parabolicInd_permGL_mul_cellUnipotent (f : parabolicIndSpace F n β σ)
    (a : cellUnipotent F β γ w) (y : GL (Fin n) F) :
    (f : GL (Fin n) F → W) (permGL F w * ((a : GL (Fin n) F) * y)) =
      cellRepA β γ w σ a ((f : GL (Fin n) F → W) (permGL F w * y)) :=
  parabolicInd_permGL_mul w σ f (Subgroup.inclusion cellUnipotent_le_blockUpper a) y

/- English proof (translation)
The claim follows from `parabolicInd_permGL_mul w σ f (Subgroup.inclusion cellLeviParabolic_le_blockUpper b) y`.
-/
theorem parabolicInd_permGL_mul_cellLeviParabolic (f : parabolicIndSpace F n β σ)
    (b : cellLeviParabolic F β γ w) (y : GL (Fin n) F) :
    (f : GL (Fin n) F → W) (permGL F w * ((b : GL (Fin n) F) * y)) =
      cellRepM β γ w σ b ((f : GL (Fin n) F → W) (permGL F w * y)) :=
  parabolicInd_permGL_mul w σ f (Subgroup.inclusion cellLeviParabolic_le_blockUpper b) y

/- English proof (translation)
Simplify using `only [cellRepM, cellRepA, MonoidHom.coe_comp, Function.comp_apply, ← map_mul]`. Use `congr 1`. Use `ext`. Simplify using the standard rewrite rules.
-/
theorem cellRepM_mul_cellRepA (b : cellLeviParabolic F β γ w) (a : cellUnipotent F β γ w) :
    cellRepM β γ w σ b * cellRepA β γ w σ a =
      cellRepA β γ w σ ⟨b * a * b⁻¹, conj_mem_cellUnipotent b.2 a.2⟩ * cellRepM β γ w σ b := by
  simp only [cellRepM, cellRepA, MonoidHom.coe_comp, Function.comp_apply, ← map_mul]
  congr 1
  ext
  simp

end Subgroups

section LeviProjCongruence

variable {α : Type*} [LinearOrder α] {β : Fin n → α}

/- English proof (translation)
Rewrite `hp`, the goal using `[mem_congruenceSubgroup_iff]`. Take `⟨hint, hcong⟩` from `hp`. Use `⟨?_, fun i k => ?_⟩` and prove the remaining obligations. Rewrite `hint`, the goal using `[mem_integralGL_iff F n]`. Use `⟨fun i k => ?_, fun i k => ?_⟩` and prove the remaining obligations.

Rewrite using `[leviProj_apply] split_ifs`. Conclude with `hint.1 i k`. Conclude with `zero_mem _`. Establish `: ((leviProj F n β p : levi F n β) : GL (Fin n) F)⁻¹ = ((leviProj F n β p⁻¹ : levi F n β) : GL (Fin n) F)`. Rewrite using `[map_inv]`.

Both sides reduce to the same expression. Rewrite using `[this, leviProj_apply]`. Use `split_ifs`. Conclude with `hint.2 i k`. Conclude with `zero_mem _`.

Rewrite using `[leviProj_apply] split_ifs with h`. Conclude with `hcong i k`. Establish `hik : i ≠ k` using `fun e => h (e ▸ rfl)`. Rewrite using `[Matrix.one_apply_ne hik, sub_zero, map_zero]`. Conclude with `zero_le`.
-/
theorem leviProj_mem_congruenceSubgroup' {j : ℕ} {p : blockUpper F n β}
    (hp : (p : GL (Fin n) F) ∈ congruenceSubgroup F n j) :
    ((leviProj F n β p : levi F n β) : GL (Fin n) F) ∈ congruenceSubgroup F n j := by
  rw [mem_congruenceSubgroup_iff] at hp ⊢
  obtain ⟨hint, hcong⟩ := hp
  refine ⟨?_, fun i k => ?_⟩
  · rw [mem_integralGL_iff F n] at hint ⊢
    refine ⟨fun i k => ?_, fun i k => ?_⟩
    · rw [leviProj_apply]
      split_ifs
      · exact hint.1 i k
      · exact zero_mem _
    · have : ((leviProj F n β p : levi F n β) : GL (Fin n) F)⁻¹ =
          ((leviProj F n β p⁻¹ : levi F n β) : GL (Fin n) F) := by
        rw [map_inv]
        rfl
      rw [this, leviProj_apply]
      split_ifs
      · exact hint.2 i k
      · exact zero_mem _
  · rw [leviProj_apply]
    split_ifs with h
    · exact hcong i k
    · have hik : i ≠ k := fun e => h (e ▸ rfl)
      rw [Matrix.one_apply_ne hik, sub_zero, map_zero]
      exact zero_le

/- English proof (translation)
Rewrite `hp`, the goal using `[← congruenceSubgroup_zero]`. Conclude with `leviProj_mem_congruenceSubgroup' hp`.
-/
theorem leviProj_mem_integralGL {p : blockUpper F n β}
    (hp : (p : GL (Fin n) F) ∈ integralGL F n) :
    ((leviProj F n β p : levi F n β) : GL (Fin n) F) ∈ integralGL F n := by
  rw [← congruenceSubgroup_zero] at hp ⊢
  exact leviProj_mem_congruenceSubgroup' hp

end LeviProjCongruence

section Smooth

variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}

/- English proof (translation)
Take `⟨U, hU, hUe⟩` from `isOpen_induced_iff.1 (hσ v)`. Establish `h1 : (1 : GL (Fin n) F) ∈ U`. Establish `: (1 : levi F n β) ∈ (stabilizerOf σ v : Set (levi F n β))` using `(stabilizerOf σ v).one_mem`. Rewrite `this` using `[← hUe]`. Conclude with `this`.

Take `⟨j, -, hj⟩` from `(hasBasis_nhds_one F n).mem_iff.1 (hU.mem_nhds h1)`. Use `⟨j, fun m hm => ?_⟩` and prove the remaining obligations. Establish `: m ∈ (stabilizerOf σ v : Set (levi F n β))`. Rewrite using `[← hUe]`. Conclude with `hj hm`.

Conclude with `this`.
-/
theorem exists_congruence_fixed (hσ : IsSmooth σ) (v : W) :
    ∃ j : ℕ, ∀ m : levi F n β, (m : GL (Fin n) F) ∈ congruenceSubgroup F n j → σ m v = v := by
  obtain ⟨U, hU, hUe⟩ := isOpen_induced_iff.1 (hσ v)
  have h1 : (1 : GL (Fin n) F) ∈ U := by
    have : (1 : levi F n β) ∈ (stabilizerOf σ v : Set (levi F n β)) := (stabilizerOf σ v).one_mem
    rw [← hUe] at this
    exact this
  obtain ⟨j, -, hj⟩ := (hasBasis_nhds_one F n).mem_iff.1 (hU.mem_nhds h1)
  refine ⟨j, fun m hm => ?_⟩
  have : m ∈ (stabilizerOf σ v : Set (levi F n β)) := by
    rw [← hUe]
    exact hj hm
  exact this

/- English proof (translation)
Use `show ((NNReal.sqrt (MeasureTheory.Measure.modularCharacter p) : ℝ) : ℂ) = 1`. Rewrite using `[Measures.modularCharacter_eq_one_of_mem_integralGL p hp]`. Simplify using the standard rewrite rules.
-/
theorem sqrtModular_of_mem_integralGL' {p : blockUpper F n β}
    (hp : (p : GL (Fin n) F) ∈ integralGL F n) : sqrtModular F n β p = 1 := by
  show ((NNReal.sqrt (MeasureTheory.Measure.modularCharacter p) : ℝ) : ℂ) = 1
  rw [Measures.modularCharacter_eq_one_of_mem_integralGL p hp]
  simp

/- English proof (translation)
Take `⟨j, hj⟩` from `exists_congruence_fixed hσ v`. Use `⟨j, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[cellRep_apply, inflateTwist_apply, sqrtModular_of_mem_integralGL' (p := permConj F β w x) (congruenceSubgroup_le F n j hx), one_smul]`. Conclude with `hj _ (leviProj_mem_congruenceSubgroup' (p := permConj F β w x) hx)`.
-/
theorem exists_cellRep_fixed (hσ : IsSmooth σ) (v : W) :
    ∃ j : ℕ, ∀ x : blockUpper F n (β ∘ w),
      permGL F w * x * (permGL F w)⁻¹ ∈ congruenceSubgroup F n j → cellRep β w σ x v = v := by
  obtain ⟨j, hj⟩ := exists_congruence_fixed hσ v
  refine ⟨j, fun x hx => ?_⟩
  rw [cellRep_apply, inflateTwist_apply,
    sqrtModular_of_mem_integralGL' (p := permConj F β w x) (congruenceSubgroup_le F n j hx),
    one_smul]
  exact hj _ (leviProj_mem_congruenceSubgroup' (p := permConj F β w x) hx)

/- English proof (translation)
The claim follows from `(conjHomeomorph (permGL F w)).continuous`.
-/
theorem continuous_permGL_conj (w : Equiv.Perm (Fin n)) :
    Continuous fun x : GL (Fin n) F => permGL F w * x * (permGL F w)⁻¹ :=
  (conjHomeomorph (permGL F w)).continuous

/- English proof (translation)
Introduce `v`. Take `⟨j, hj⟩` from `exists_cellRep_fixed (w := w) hσ v`. Set `U : Subgroup (cellUnipotent F β γ w)` to `((congruenceSubgroup F n j).comap (MulAut.conj (permGL F w)).toMonoidHom).subgroupOf _`. Use `Subgroup.isOpen_mono (H₁ := U) (fun a ha => ?_) ?_` and prove the remaining obligations. Rewrite using `[mem_stabilizerOf]`.

Conclude with `hj _ ha`. Use `show IsOpen (Subtype.val ⁻¹' ((fun x : GL (Fin n) F => permGL F w * x * (permGL F w)⁻¹) ⁻¹' (congruenceSubgroup F n j : Set (GL (Fin n) F))))`. Conclude with `((isOpen_congruenceSubgroup F n j).preimage (continuous_permGL_conj w)).preimage continuous_subtype_val`.
-/
theorem isSmooth_cellRepA (hσ : IsSmooth σ) : IsSmooth (cellRepA β γ w σ) := by
  intro v
  obtain ⟨j, hj⟩ := exists_cellRep_fixed (w := w) hσ v
  let U : Subgroup (cellUnipotent F β γ w) :=
    ((congruenceSubgroup F n j).comap (MulAut.conj (permGL F w)).toMonoidHom).subgroupOf _
  refine Subgroup.isOpen_mono (H₁ := U) (fun a ha => ?_) ?_
  · rw [mem_stabilizerOf]
    exact hj _ ha
  · show IsOpen (Subtype.val ⁻¹' ((fun x : GL (Fin n) F => permGL F w * x * (permGL F w)⁻¹) ⁻¹'
      (congruenceSubgroup F n j : Set (GL (Fin n) F))))
    exact ((isOpen_congruenceSubgroup F n j).preimage (continuous_permGL_conj w)).preimage
      continuous_subtype_val

end Smooth

section UnipotentCompactG

variable {γ : Fin n → ℕ}

/- English proof (translation)
Take `⟨e, he⟩` from `entryBound_of_isCompact hS`. Conclude with `⟨e, fun u hu => mem_unipotentCompactG_of_bound (hSN hu) (he u hu).1 (he u hu).2⟩`.
-/
theorem exists_unipotentCompactG_of_isCompact {S : Set (GL (Fin n) F)} (hS : IsCompact S)
    (hSN : S ⊆ unipotentRadical F n γ) :
    ∃ e : ℕ, S ⊆ (unipotentCompactG (F := F) γ e : Set (GL (Fin n) F)) := by
  obtain ⟨e, he⟩ := entryBound_of_isCompact hS
  exact ⟨e, fun u hu => mem_unipotentCompactG_of_bound (hSN hu) (he u hu).1 (he u hu).2⟩

/- English proof (translation)
Take `⟨huN, hu'⟩` from `mem_unipotentCompactG.1 hu`. Use `mem_unipotentCompactG.2 ⟨conj_mem_unipotentRadical (levi_le_blockUpper hk) huN, ?_⟩` and prove the remaining obligations. Establish `hc` using `rankTorus_commute (β := γ) e hk`. Establish `hcomm : Commute (rankTorus F n γ e) k` using `hc`. Establish `h2 : k⁻¹ * (rankTorus F n γ e)⁻¹ = (rankTorus F n γ e)⁻¹ * k⁻¹` using `(hcomm.inv_inv).eq.symm`.

Establish `: rankTorus F n γ e * (k * u * k⁻¹) * (rankTorus F n γ e)⁻¹ = k * (rankTorus F n γ e * u * (rankTorus F n γ e)⁻¹) * k⁻¹`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[this]`. Conclude with `(integralGL F n).mul_mem ((integralGL F n).mul_mem hk' hu') ((integralGL F n).inv_mem hk')`.
-/
theorem conj_mem_unipotentCompactG {k u : GL (Fin n) F} (hk : k ∈ levi F n γ)
    (hk' : k ∈ integralGL F n) {e : ℕ} (hu : u ∈ unipotentCompactG γ e) :
    k * u * k⁻¹ ∈ unipotentCompactG γ e := by
  obtain ⟨huN, hu'⟩ := mem_unipotentCompactG.1 hu
  refine mem_unipotentCompactG.2 ⟨conj_mem_unipotentRadical (levi_le_blockUpper hk) huN, ?_⟩
  have hc := rankTorus_commute (β := γ) e hk
  have hcomm : Commute (rankTorus F n γ e) k := hc
  have h2 : k⁻¹ * (rankTorus F n γ e)⁻¹ = (rankTorus F n γ e)⁻¹ * k⁻¹ := (hcomm.inv_inv).eq.symm
  have : rankTorus F n γ e * (k * u * k⁻¹) * (rankTorus F n γ e)⁻¹ =
      k * (rankTorus F n γ e * u * (rankTorus F n γ e)⁻¹) * k⁻¹ := by
    calc rankTorus F n γ e * (k * u * k⁻¹) * (rankTorus F n γ e)⁻¹
        = (rankTorus F n γ e * k) * u * (k⁻¹ * (rankTorus F n γ e)⁻¹) := by group
      _ = (k * rankTorus F n γ e) * u * ((rankTorus F n γ e)⁻¹ * k⁻¹) := by rw [hc, h2]
      _ = k * (rankTorus F n γ e * u * (rankTorus F n γ e)⁻¹) * k⁻¹ := by group
  rw [this]
  exact (integralGL F n).mul_mem ((integralGL F n).mul_mem hk' hu') ((integralGL F n).inv_mem hk')

/- English proof (translation)
Take `⟨e, he⟩` from `exists_unipotentCompactG_of_isCompact (γ := γ) ((s.finite_toSet.image (fun x : H => (x : GL (Fin n) F))).isCompact) (by rintro _ ⟨x, -, rfl⟩; exact hHN x.2)`. Use `⟨(unipotentCompactG γ e).subgroupOf H, ?_, ?_, fun x hx => he ⟨x, hx, rfl⟩⟩` and prove the remaining obligations. Rewrite using `[Subgroup.coe_subgroupOf]`. Conclude with `hH.isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_unipotentCompactG e)`. Establish `: (unipotentCompactG (F` using `F) γ e).subgroupOf H = ((integralGL F n).comap (MulAut.conj (rankTorus F n γ e)).toMonoidHom).subgroupOf H := by`.

Use extensionality with `x`. Simplify using `only [Subgroup.mem_subgroupOf, unipotentCompactG_eq, Subgroup.mem_inf]`. Conclude with `⟨fun h => h.2, fun h => ⟨hHN x.2, h⟩⟩`. Rewrite using `[this, Subgroup.coe_subgroupOf]`. Conclude with `(isOpen_conj_integralGL _).preimage continuous_subtype_val`.
-/
theorem exists_compactOpen_subgroupOf {H : Subgroup (GL (Fin n) F)}
    (hH : IsClosed (H : Set (GL (Fin n) F))) (hHN : H ≤ unipotentRadical F n γ)
    (s : Finset H) :
    ∃ K : Subgroup H, IsCompact (K : Set H) ∧ IsOpen (K : Set H) ∧ ∀ x ∈ s, x ∈ K := by
  obtain ⟨e, he⟩ := exists_unipotentCompactG_of_isCompact (γ := γ)
    ((s.finite_toSet.image (fun x : H => (x : GL (Fin n) F))).isCompact)
    (by rintro _ ⟨x, -, rfl⟩; exact hHN x.2)
  refine ⟨(unipotentCompactG γ e).subgroupOf H, ?_, ?_, fun x hx => he ⟨x, hx, rfl⟩⟩
  · rw [Subgroup.coe_subgroupOf]
    exact hH.isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_unipotentCompactG e)
  · have : (unipotentCompactG (F := F) γ e).subgroupOf H =
        ((integralGL F n).comap (MulAut.conj (rankTorus F n γ e)).toMonoidHom).subgroupOf H := by
      ext x
      simp only [Subgroup.mem_subgroupOf, unipotentCompactG_eq, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨hHN x.2, h⟩⟩
    rw [this, Subgroup.coe_subgroupOf]
    exact (isOpen_conj_integralGL _).preimage continuous_subtype_val

/- English proof (translation)
The claim follows from `isClosed_unipotentRadical.inter (Measures.isClosed_blockUpper F n (β ∘ w))`.
-/
theorem isClosed_cellUnipotent {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} :
    IsClosed (cellUnipotent F β γ w : Set (GL (Fin n) F)) :=
  isClosed_unipotentRadical.inter (Measures.isClosed_blockUpper F n (β ∘ w))

end UnipotentCompactG

section LeviIwasawa

variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)}

/- English proof (translation)
Set `ρ : Fin n → ℕ ×ₗ ℕ` to `fun i => toLex (γ i, β (w i))`. Take `⟨p, hp, k, hk, hpk⟩` from `exists_blockUpper_mul_integralGL' (β := ρ) m`. Establish `hρ : ∀ {i j : Fin n}, γ j < γ i → ρ j < ρ i` using `fun h => by show toLex (γ _, β (w _)) < toLex (γ _, β (w _))`. Rewrite using `[Prod.Lex.lt_iff]`. Conclude with `Or.inl h`.

Establish `hpQ : p ∈ blockUpper F n γ` using `fun i j hij => hp (hρ hij)`. Establish `hmQ : m ∈ blockUpper F n γ` using `levi_le_blockUpper hm`. Establish `hkQ : k ∈ blockUpper F n γ`. Establish `: k = p⁻¹ * m` using `by rw [hpk]; group`. Rewrite using `[this]`.

Conclude with `(blockUpper F n γ).mul_mem ((blockUpper F n γ).inv_mem hpQ) hmQ`. Use `set b := leviProj F n γ ⟨p, hpQ⟩`. Use `set k' := leviProj F n γ ⟨k, hkQ⟩`. Use `⟨b, ⟨b.2, fun i j hij => ?_⟩, k', ⟨k'.2, leviProj_mem_integralGL (p := ⟨k, hkQ⟩) hk⟩, ?_⟩` and prove the remaining obligations. Use `show ((leviProj F n γ ⟨p, hpQ⟩ : levi F n γ) : GL (Fin n) F) i j = 0`.

Rewrite using `[leviProj_apply]`. Use `split_ifs with h`. Apply `hp show toLex (γ j, β (w j)) < toLex (γ i, β (w i))` to reduce the goal to its premises. Rewrite using `[Prod.Lex.lt_iff]`. Conclude with `Or.inr ⟨h.symm, hij⟩`.

Both sides reduce to the same expression. Establish `h1 : leviProj F n γ ⟨m, hmQ⟩ = b * k'`. Rewrite using `[← map_mul]`. Use `congr 1`. Conclude with `Subtype.ext hpk`.

Rewrite `h1` using `[leviProj_of_mem_levi hm]`. Conclude with `congrArg Subtype.val h1`.
-/
theorem exists_levi_eq_mul {m : GL (Fin n) F} (hm : m ∈ levi F n γ) :
    ∃ b ∈ cellLeviParabolic F β γ w, ∃ k ∈ levi F n γ ⊓ integralGL F n, m = b * k := by
  let ρ : Fin n → ℕ ×ₗ ℕ := fun i => toLex (γ i, β (w i))
  obtain ⟨p, hp, k, hk, hpk⟩ := exists_blockUpper_mul_integralGL' (β := ρ) m
  have hρ : ∀ {i j : Fin n}, γ j < γ i → ρ j < ρ i := fun h => by
    show toLex (γ _, β (w _)) < toLex (γ _, β (w _))
    rw [Prod.Lex.lt_iff]
    exact Or.inl h
  have hpQ : p ∈ blockUpper F n γ := fun i j hij => hp (hρ hij)
  have hmQ : m ∈ blockUpper F n γ := levi_le_blockUpper hm
  have hkQ : k ∈ blockUpper F n γ := by
    have : k = p⁻¹ * m := by rw [hpk]; group
    rw [this]
    exact (blockUpper F n γ).mul_mem ((blockUpper F n γ).inv_mem hpQ) hmQ
  set b := leviProj F n γ ⟨p, hpQ⟩
  set k' := leviProj F n γ ⟨k, hkQ⟩
  refine ⟨b, ⟨b.2, fun i j hij => ?_⟩, k', ⟨k'.2, leviProj_mem_integralGL (p := ⟨k, hkQ⟩) hk⟩, ?_⟩
  · show ((leviProj F n γ ⟨p, hpQ⟩ : levi F n γ) : GL (Fin n) F) i j = 0
    rw [leviProj_apply]
    split_ifs with h
    · apply hp
      show toLex (γ j, β (w j)) < toLex (γ i, β (w i))
      rw [Prod.Lex.lt_iff]
      exact Or.inr ⟨h.symm, hij⟩
    · rfl
  · have h1 : leviProj F n γ ⟨m, hmQ⟩ = b * k' := by
      rw [← map_mul]
      congr 1
      exact Subtype.ext hpk
    rw [leviProj_of_mem_levi hm] at h1
    exact congrArg Subtype.val h1

/- English proof (translation)
Use `set K₀ := levi F n γ ⊓ integralGL F n`. Use `set L := (levi F n γ ⊓ congruenceSubgroup F n j).subgroupOf K₀`. Establish `hK₀ : IsCompact (K₀ : Set (GL (Fin n) F))` using `(isCompact_integralGL F n).inter_left isClosed_levi`. Establish `hfin : L.index ≠ 0`. Establish `h` using `relIndex_ne_zero_of_isCompact_of_isOpen hK₀ (isOpen_congruenceSubgroup F n j)`.

Establish `: L = (congruenceSubgroup F n j).subgroupOf K₀`. Use extensionality with `x`. Simplify using `only [L, Subgroup.mem_subgroupOf, Subgroup.mem_inf]`. Conclude with `⟨fun h => h.2, fun h => ⟨x.2.1, h⟩⟩`. Rewrite using `[this]`.

Conclude with `h`. Establish `: L.FiniteIndex` using `⟨hfin⟩`. Set `_` to `Fintype.ofFinite (K₀ ⧸ L)`. Use `⟨Finset.univ.image fun q : K₀ ⧸ L => ((Quotient.out q : K₀) : GL (Fin n) F), fun t ht => ?_, fun m hm => ?_⟩` and prove the remaining obligations. Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 ht`.

Conclude with `(Quotient.out q).2`. Take `⟨b, hb, k, hk, rfl⟩` from `exists_levi_eq_mul (β := β) (w := w) hm set q : K₀ ⧸ L := QuotientGroup.mk ⟨k, hk⟩`. Establish `hq : (Quotient.out q : K₀)⁻¹ * ⟨k, hk⟩ ∈ L`. Rewrite using `[← QuotientGroup.eq]`. Conclude with `QuotientGroup.out_eq' q`.

Use `⟨b, hb, (Quotient.out q : K₀), Finset.mem_image_of_mem _ (Finset.mem_univ q), ((Quotient.out q : K₀) : GL (Fin n) F)⁻¹ * k, Subgroup.mem_subgroupOf.1 hq, ?_⟩` and prove the remaining obligations. Use `group`.
-/
theorem exists_finset_levi_eq_mul (j : ℕ) :
    ∃ T : Finset (GL (Fin n) F), (∀ t ∈ T, t ∈ levi F n γ ⊓ integralGL F n) ∧
      ∀ m ∈ levi F n γ, ∃ b ∈ cellLeviParabolic F β γ w, ∃ t ∈ T,
        ∃ k ∈ levi F n γ ⊓ congruenceSubgroup F n j, m = b * t * k := by
  classical
  set K₀ := levi F n γ ⊓ integralGL F n
  set L := (levi F n γ ⊓ congruenceSubgroup F n j).subgroupOf K₀
  have hK₀ : IsCompact (K₀ : Set (GL (Fin n) F)) :=
    (isCompact_integralGL F n).inter_left isClosed_levi
  have hfin : L.index ≠ 0 := by
    have h := relIndex_ne_zero_of_isCompact_of_isOpen hK₀ (isOpen_congruenceSubgroup F n j)
    have : L = (congruenceSubgroup F n j).subgroupOf K₀ := by
      ext x
      simp only [L, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨x.2.1, h⟩⟩
    rw [this]
    exact h
  have : L.FiniteIndex := ⟨hfin⟩
  let _ := Fintype.ofFinite (K₀ ⧸ L)
  refine ⟨Finset.univ.image fun q : K₀ ⧸ L => ((Quotient.out q : K₀) : GL (Fin n) F),
    fun t ht => ?_, fun m hm => ?_⟩
  · obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ht
    exact (Quotient.out q).2
  · obtain ⟨b, hb, k, hk, rfl⟩ := exists_levi_eq_mul (β := β) (w := w) hm
    set q : K₀ ⧸ L := QuotientGroup.mk ⟨k, hk⟩
    have hq : (Quotient.out q : K₀)⁻¹ * ⟨k, hk⟩ ∈ L := by
      rw [← QuotientGroup.eq]
      exact QuotientGroup.out_eq' q
    refine ⟨b, hb, (Quotient.out q : K₀), Finset.mem_image_of_mem _ (Finset.mem_univ q),
      ((Quotient.out q : K₀) : GL (Fin n) F)⁻¹ * k, Subgroup.mem_subgroupOf.1 hq, ?_⟩
    group

end LeviIwasawa

section Coinvariants

variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (levi F n β) W)

def cellCoinvAction (b : cellLeviParabolic F β γ w) :
    Representation.Coinvariants (cellRepA β γ w σ) →ₗ[ℂ]
      Representation.Coinvariants (cellRepA β γ w σ) :=
  Representation.Coinvariants.lift _ ((Representation.Coinvariants.mk _) ∘ₗ cellRepM β γ w σ b)
    fun a => by
      ext v
      simp only [LinearMap.coe_comp, Function.comp_apply]
      have := congrArg (fun T : Module.End ℂ W => T v) (cellRepM_mul_cellRepA σ b a)
      simp only [Module.End.mul_apply] at this
      rw [this, Representation.Coinvariants.mk_self_apply]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cellCoinvAction_mk (b : cellLeviParabolic F β γ w) (v : W) :
    cellCoinvAction σ b (Representation.Coinvariants.mk _ v) =
      Representation.Coinvariants.mk _ (cellRepM β γ w σ b v) := rfl

def cellCoinvRep : Representation ℂ (cellLeviParabolic F β γ w)
    (Representation.Coinvariants (cellRepA β γ w σ)) where
  toFun := cellCoinvAction σ
  map_one' := Representation.Coinvariants.hom_ext (LinearMap.ext fun v => by
    simp [cellCoinvAction_mk])
  map_mul' b b' := Representation.Coinvariants.hom_ext (LinearMap.ext fun v => by
    simp [cellCoinvAction_mk, Module.End.mul_apply])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cellCoinvRep_mk (b : cellLeviParabolic F β γ w) (v : W) :
    cellCoinvRep σ b (Representation.Coinvariants.mk _ v) =
      Representation.Coinvariants.mk _ (cellRepM β γ w σ b v) := rfl

end Coinvariants

end Parabolic

end GroundTheory.Automorphic
