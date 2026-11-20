import Mathlib
import GroundTheory.AutomorphicForms.LeviStagesJacquet
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa MeasureTheory Measure Topology Set ValuativeRel Measures GLnLocal
open scoped NNReal

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

section LeviParabolic

variable {β γ : Fin n → ℕ}

variable (F n β γ) in

abbrev leviParabolic : Subgroup (levi F n β) := (blockUpper F n γ).subgroupOf (levi F n β)

variable (F n β γ) in

def leviParabolicToLeviPar : leviParabolic F n β γ →* leviPar F n β γ where
  toFun q := ⟨((q : levi F n β) : GL (Fin n) F), (q : levi F n β).2, Subgroup.mem_subgroupOf.1 q.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

variable (F n β γ) in

def leviParabolicIncl : leviParabolic F n β γ →* blockUpper F n γ where
  toFun q := ⟨((q : levi F n β) : GL (Fin n) F), Subgroup.mem_subgroupOf.1 q.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_leviParabolicIncl (q : leviParabolic F n β γ) :
    ((leviParabolicIncl F n β γ q : blockUpper F n γ) : GL (Fin n) F) = q := rfl

/- English proof (translation)
Introduce `i j hij`. Use `show ((leviProj F n β p : levi F n β) : GL (Fin n) F) i j = 0`. Rewrite using `[leviProj_apply]`. Use `split_ifs`. Conclude with `hp hij`.

Both sides reduce to the same expression.
-/
theorem leviProj_mem_blockUpper (p : blockUpper F n β)
    (hp : (p : GL (Fin n) F) ∈ blockUpper F n γ) :
    ((leviProj F n β p : levi F n β) : GL (Fin n) F) ∈ blockUpper F n γ := by
  intro i j hij
  show ((leviProj F n β p : levi F n β) : GL (Fin n) F) i j = 0
  rw [leviProj_apply]
  split_ifs
  · exact hp hij
  · rfl

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `i j`. Simplify using `only [leviProj_apply]`. Use `split_ifs with h1 h2`. Both sides reduce to the same expression.

Conclude with `absurd (h.eq_of_eq h1) h2`. Both sides reduce to the same expression.
-/
theorem leviProj_leviProj (h : Refines β γ) (p : blockUpper F n γ) :
    leviProj F n γ ⟨((leviProj F n β ⟨p, h.blockUpper_le F p.2⟩ : levi F n β) : GL (Fin n) F),
      leviProj_mem_blockUpper _ p.2⟩ = leviProj F n γ p := by
  apply Subtype.ext
  ext i j
  simp only [leviProj_apply]
  split_ifs with h1 h2
  · rfl
  · exact absurd (h.eq_of_eq h1) h2
  · rfl

/- English proof (translation)
Use `set p' : blockUpper F n β := ⟨p, h.blockUpper_le F p.2⟩`. Use `set m := leviProj F n β p'`. Establish `hmγ : ((m : levi F n β) : GL (Fin n) F) ∈ blockUpper F n γ` using `leviProj_mem_blockUpper _ p.2`. Use `set u : blockUpper F n β := (leviIncl m)⁻¹ * p'`. Establish `hu : (u : GL (Fin n) F) ∈ unipotentRadical F n β` using `leviProj_inv_mul_mem p'`.

Establish `huγ : (u : GL (Fin n) F) ∈ unipotentRadical F n γ` using `h.unipotentRadical_le F hu`. Establish `hp : p = (⟨m, hmγ⟩ : blockUpper F n γ) * ⟨u, (mem_unipotentRadical.1 huγ).1⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Subgroup.coe_mul]`. Use `show (p : GL (Fin n) F) = (m : GL (Fin n) F) * (((leviIncl m)⁻¹ * p' : blockUpper F n β) : GL (Fin n) F)`.

Rewrite using `[Subgroup.coe_mul, Subgroup.coe_inv, leviIncl_coe, mul_inv_cancel_left]`. Establish `key` using `sqrtModular_refine h ⟨(m : GL (Fin n) F), m.2, hmγ⟩`. Establish `hu1 : sqrtModular F n γ ⟨u, (mem_unipotentRadical.1 huγ).1⟩ = 1` using `sqrtModular_of_mem _ huγ`. Use `conv_lhs => rw [hp, map_mul, hu1, mul_one]`. Rewrite using `[key, ← sqrtModular_leviProj p']`.

Both sides reduce to the same expression.
-/
theorem sqrtModular_blockUpper_refine (h : Refines β γ) (p : blockUpper F n γ) :
    sqrtModular F n γ p = sqrtModular F n β ⟨p, h.blockUpper_le F p.2⟩ *
      sqrtModularLeviPar F n β γ
        ⟨((leviProj F n β ⟨p, h.blockUpper_le F p.2⟩ : levi F n β) : GL (Fin n) F),
          (leviProj F n β ⟨p, h.blockUpper_le F p.2⟩).2, leviProj_mem_blockUpper _ p.2⟩ := by
  set p' : blockUpper F n β := ⟨p, h.blockUpper_le F p.2⟩
  set m := leviProj F n β p'
  have hmγ : ((m : levi F n β) : GL (Fin n) F) ∈ blockUpper F n γ := leviProj_mem_blockUpper _ p.2
  set u : blockUpper F n β := (leviIncl m)⁻¹ * p'
  have hu : (u : GL (Fin n) F) ∈ unipotentRadical F n β := leviProj_inv_mul_mem p'
  have huγ : (u : GL (Fin n) F) ∈ unipotentRadical F n γ := h.unipotentRadical_le F hu
  have hp : p = (⟨m, hmγ⟩ : blockUpper F n γ) * ⟨u, (mem_unipotentRadical.1 huγ).1⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    show (p : GL (Fin n) F) = (m : GL (Fin n) F) *
      (((leviIncl m)⁻¹ * p' : blockUpper F n β) : GL (Fin n) F)
    rw [Subgroup.coe_mul, Subgroup.coe_inv, leviIncl_coe, mul_inv_cancel_left]
  have key := sqrtModular_refine h ⟨(m : GL (Fin n) F), m.2, hmγ⟩
  have hu1 : sqrtModular F n γ ⟨u, (mem_unipotentRadical.1 huγ).1⟩ = 1 := sqrtModular_of_mem _ huγ
  conv_lhs => rw [hp, map_mul, hu1, mul_one]
  rw [key, ← sqrtModular_leviProj p']
  rfl

end LeviParabolic

section LeviInduction

variable {β γ : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

variable (F n β γ) in

def leviInflateTwist (τ : Representation ℂ (levi F n γ) W) :
    Representation ℂ (leviParabolic F n β γ) W :=
  twist ((sqrtModularLeviPar F n β γ).comp (leviParabolicToLeviPar F n β γ))
    (τ.comp ((leviProj F n γ).comp (leviParabolicIncl F n β γ)))

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem leviInflateTwist_apply (τ : Representation ℂ (levi F n γ) W)
    (q : leviParabolic F n β γ) (w : W) :
    leviInflateTwist F n β γ τ q w = sqrtModularLeviPar F n β γ (leviParabolicToLeviPar F n β γ q) •
      τ (leviProj F n γ (leviParabolicIncl F n β γ q)) w := rfl

variable (F n β γ) in

abbrev leviParabolicIndSpace (τ : Representation ℂ (levi F n γ) W) :
    Submodule ℂ (levi F n β → W) :=
  indSpace (leviParabolic F n β γ) (leviInflateTwist F n β γ τ)

variable (F n β γ) in

abbrev leviParabolicInd (τ : Representation ℂ (levi F n γ) W) :
    Representation ℂ (levi F n β) (leviParabolicIndSpace F n β γ τ) :=
  indRep (leviParabolic F n β γ) (leviInflateTwist F n β γ τ)

end LeviInduction

section Stages

variable {β γ : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (τ : Representation ℂ (levi F n γ) W)

/- English proof (translation)
Establish `hf` using `(mem_indSpace.1 f.2).1 (leviIncl x) g`. Rewrite `hf` using `[leviIncl_coe]`. Rewrite using `[hf, inflateTwist_apply, leviProj_leviIncl]`. Both sides reduce to the same expression.
-/
theorem parabolicInd_levi_apply (f : parabolicIndSpace F n β (leviParabolicInd F n β γ τ))
    (x : levi F n β) (g : GL (Fin n) F) (y : levi F n β) :
    (((f : GL (Fin n) F → leviParabolicIndSpace F n β γ τ) ((x : GL (Fin n) F) * g) :
      leviParabolicIndSpace F n β γ τ) : levi F n β → W) y =
      sqrtModular F n β (leviIncl x) •
        (((f : GL (Fin n) F → leviParabolicIndSpace F n β γ τ) g :
          leviParabolicIndSpace F n β γ τ) : levi F n β → W) (y * x) := by
  have hf := (mem_indSpace.1 f.2).1 (leviIncl x) g
  rw [leviIncl_coe] at hf
  rw [hf, inflateTwist_apply, leviProj_leviIncl]
  rfl

def stagesFun (f : parabolicIndSpace F n β (leviParabolicInd F n β γ τ)) : GL (Fin n) F → W :=
  fun g => (((f : GL (Fin n) F → leviParabolicIndSpace F n β γ τ) g :
    leviParabolicIndSpace F n β γ τ) : levi F n β → W) 1

/- English proof (translation)
Take `⟨hfP, K, hKo, hfK⟩` from `mem_indSpace.1 f.2`. Use `⟨fun p g => ?_, K, hKo, fun k hk g => ?_⟩` and prove the remaining obligations. Use `set p' : blockUpper F n β := ⟨p, h.blockUpper_le F p.2⟩ set m := leviProj F n β p'`. Establish `hmγ : ((m : levi F n β) : GL (Fin n) F) ∈ blockUpper F n γ` using `leviProj_mem_blockUpper _ p.2`. Use `set φ : leviParabolicIndSpace F n β γ τ := (f : GL (Fin n) F → leviParabolicIndSpace F n β γ τ) g`.

Establish `h1 : (((f : GL (Fin n) F → leviParabolicIndSpace F n β γ τ) ((p : GL (Fin n) F) * g) : leviParabolicIndSpace F n β γ τ) : levi F n β → W) 1 = sqrtModular F n β p' • (φ : levi F n β → W) m`. Use `hfP p' g` as an intermediate fact. Express the relevant statement in the definitionally equal form `(f : GL (Fin n) F → leviParabolicIndSpace F n β γ τ) ((p' : GL (Fin n) F) * g) = _ at this`. Rewrite using `[this, inflateTwist_apply]`. Use `show sqrtModular F n β p' • (φ : levi F n β → W) (1 * m) = _`.

Rewrite using `[one_mul]`. Establish `h2 : (φ : levi F n β → W) m = sqrtModularLeviPar F n β γ ⟨(m : GL (Fin n) F), m.2, hmγ⟩ • τ (leviProj F n γ p) ((φ : levi F n β → W) 1)`. Use `(mem_indSpace.1 φ.2).1 ⟨m, Subgroup.mem_subgroupOf.2 hmγ⟩ 1` as an intermediate fact. Rewrite `this` using `[mul_one]`. Establish `e : leviProj F n γ (leviParabolicIncl F n β γ ⟨m, Subgroup.mem_subgroupOf.2 hmγ⟩) = leviProj F n γ p` using `leviProj_leviProj h p`.

Rewrite using `[this, leviInflateTwist_apply, e]`. Both sides reduce to the same expression. Use `show stagesFun τ f ((p : GL (Fin n) F) * g) = sqrtModular F n γ p • τ (leviProj F n γ p) (stagesFun τ f g)`. Rewrite using `[stagesFun, h1, h2, smul_smul, sqrtModular_blockUpper_refine h p]`. Both sides reduce to the same expression.

Use `show (((f : GL (Fin n) F → leviParabolicIndSpace F n β γ τ) (g * k) : leviParabolicIndSpace F n β γ τ) : levi F n β → W) 1 = _`. Rewrite using `[hfK k hk g]`. Both sides reduce to the same expression.
-/
theorem stagesFun_mem (h : Refines β γ) (f : parabolicIndSpace F n β (leviParabolicInd F n β γ τ)) :
    stagesFun τ f ∈ parabolicIndSpace F n γ τ := by
  obtain ⟨hfP, K, hKo, hfK⟩ := mem_indSpace.1 f.2
  refine ⟨fun p g => ?_, K, hKo, fun k hk g => ?_⟩
  · set p' : blockUpper F n β := ⟨p, h.blockUpper_le F p.2⟩
    set m := leviProj F n β p'
    have hmγ : ((m : levi F n β) : GL (Fin n) F) ∈ blockUpper F n γ :=
      leviProj_mem_blockUpper _ p.2
    set φ : leviParabolicIndSpace F n β γ τ :=
      (f : GL (Fin n) F → leviParabolicIndSpace F n β γ τ) g
    have h1 : (((f : GL (Fin n) F → leviParabolicIndSpace F n β γ τ) ((p : GL (Fin n) F) * g) :
        leviParabolicIndSpace F n β γ τ) : levi F n β → W) 1 =
        sqrtModular F n β p' • (φ : levi F n β → W) m := by
      have := hfP p' g
      change (f : GL (Fin n) F → leviParabolicIndSpace F n β γ τ) ((p' : GL (Fin n) F) * g) = _
        at this
      rw [this, inflateTwist_apply]
      show sqrtModular F n β p' • (φ : levi F n β → W) (1 * m) = _
      rw [one_mul]
    have h2 : (φ : levi F n β → W) m =
        sqrtModularLeviPar F n β γ ⟨(m : GL (Fin n) F), m.2, hmγ⟩ •
          τ (leviProj F n γ p) ((φ : levi F n β → W) 1) := by
      have := (mem_indSpace.1 φ.2).1 ⟨m, Subgroup.mem_subgroupOf.2 hmγ⟩ 1
      rw [mul_one] at this
      have e : leviProj F n γ (leviParabolicIncl F n β γ ⟨m, Subgroup.mem_subgroupOf.2 hmγ⟩) =
          leviProj F n γ p := leviProj_leviProj h p
      rw [this, leviInflateTwist_apply, e]
      rfl
    show stagesFun τ f ((p : GL (Fin n) F) * g) =
      sqrtModular F n γ p • τ (leviProj F n γ p) (stagesFun τ f g)
    rw [stagesFun, h1, h2, smul_smul, sqrtModular_blockUpper_refine h p]
    rfl
  · show (((f : GL (Fin n) F → leviParabolicIndSpace F n β γ τ) (g * k) :
      leviParabolicIndSpace F n β γ τ) : levi F n β → W) 1 = _
    rw [hfK k hk g]
    rfl

def stagesInnerFun (φ : parabolicIndSpace F n γ τ) (g : GL (Fin n) F) : levi F n β → W :=
  fun x => invSqrtModular F n β (leviIncl x) • (φ : GL (Fin n) F → W) ((x : GL (Fin n) F) * g)

/- English proof (translation)
Take `⟨hφP, K, hKo, hφK⟩` from `mem_indSpace.1 φ.2`. Use `⟨fun q x => ?_, ?_⟩` and prove the remaining obligations. Establish `key` using `sqrtModular_refine h (leviParabolicToLeviPar F n β γ q)`. Establish `key' : sqrtModular F n γ (leviParabolicIncl F n β γ q) = sqrtModular F n β (leviIncl (q : levi F n β)) * sqrtModularLeviPar F n β γ (leviParabolicToLeviPar F n β γ q)` using `key`. Establish `hinv : invSqrtModular F n β (leviIncl (q : levi F n β)) * sqrtModular F n β (leviIncl (q : levi F n β)) = 1`.

Rewrite using `[mul_comm]`. Conclude with `sqrtModular_mul_invSqrtModular _`. Establish `hφq` using `hφP (leviParabolicIncl F n β γ q) ((x : GL (Fin n) F) * g)`. Rewrite `hφq` using `[inflateTwist_apply, coe_leviParabolicIncl]`. Simplify using `only [stagesInnerFun, leviInflateTwist_apply, map_smul, smul_smul]`.

Rewrite using `[map_mul, Subgroup.coe_mul, mul_assoc, hφq, smul_smul, key']`. Use `congr 1`. Rewrite using `[map_mul]`. Take the linear combination `(sqrtModularLeviPar F n β γ (leviParabolicToLeviPar F n β γ q) * invSqrtModular F n β (leviIncl x)) * hinv`. Set `K' : Subgroup (GL (Fin n) F)` to `K.comap (MulAut.conj g⁻¹).toMonoidHom ⊓ integralGL F n`.

Establish `hc : Continuous fun k : GL (Fin n) F => (MulAut.conj g⁻¹).toMonoidHom k`. Simplify using `only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`. Use `fun_prop`. Use `⟨K'.subgroupOf (levi F n β), ?_, fun k hk x => ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.coe_subgroupOf, Subgroup.coe_inf, Subgroup.coe_comap]`.

Conclude with `((hKo.preimage hc).inter (isOpen_integralGL F n)).preimage continuous_subtype_val`. Take `⟨hk1, hk2⟩` from `Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hk)`. Establish `hk1' : g⁻¹ * (k : GL (Fin n) F) * g ∈ K`. Use `Subgroup.mem_comap.1 hk1` as an intermediate fact. Simplify `this` using `[MulAut.conj_apply]`.

Simplify using `only [stagesInnerFun]`. Rewrite using `[map_mul, map_mul, invSqrtModular_leviIncl_of_mem k hk2, mul_one, Subgroup.coe_mul]`. Use `congr 1`. Establish `e : (x : GL (Fin n) F) * (k : GL (Fin n) F) * g = (x : GL (Fin n) F) * g * (g⁻¹ * (k : GL (Fin n) F) * g)` using `by group`. Rewrite using `[e, hφK _ hk1']`.
-/
theorem stagesInnerFun_mem (h : Refines β γ) (φ : parabolicIndSpace F n γ τ) (g : GL (Fin n) F) :
    stagesInnerFun τ φ g ∈ leviParabolicIndSpace F n β γ τ := by
  obtain ⟨hφP, K, hKo, hφK⟩ := mem_indSpace.1 φ.2
  refine ⟨fun q x => ?_, ?_⟩
  · have key := sqrtModular_refine h (leviParabolicToLeviPar F n β γ q)
    have key' : sqrtModular F n γ (leviParabolicIncl F n β γ q) =
        sqrtModular F n β (leviIncl (q : levi F n β)) *
          sqrtModularLeviPar F n β γ (leviParabolicToLeviPar F n β γ q) := key
    have hinv : invSqrtModular F n β (leviIncl (q : levi F n β)) *
        sqrtModular F n β (leviIncl (q : levi F n β)) = 1 := by
      rw [mul_comm]
      exact sqrtModular_mul_invSqrtModular _
    have hφq := hφP (leviParabolicIncl F n β γ q) ((x : GL (Fin n) F) * g)
    rw [inflateTwist_apply, coe_leviParabolicIncl] at hφq
    simp only [stagesInnerFun, leviInflateTwist_apply, map_smul, smul_smul]
    rw [map_mul, Subgroup.coe_mul, mul_assoc, hφq, smul_smul, key']
    congr 1
    rw [map_mul]
    linear_combination (sqrtModularLeviPar F n β γ (leviParabolicToLeviPar F n β γ q) *
      invSqrtModular F n β (leviIncl x)) * hinv
  · let K' : Subgroup (GL (Fin n) F) :=
      K.comap (MulAut.conj g⁻¹).toMonoidHom ⊓ integralGL F n
    have hc : Continuous fun k : GL (Fin n) F => (MulAut.conj g⁻¹).toMonoidHom k := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      fun_prop
    refine ⟨K'.subgroupOf (levi F n β), ?_, fun k hk x => ?_⟩
    · rw [Subgroup.coe_subgroupOf, Subgroup.coe_inf, Subgroup.coe_comap]
      exact ((hKo.preimage hc).inter (isOpen_integralGL F n)).preimage continuous_subtype_val
    · obtain ⟨hk1, hk2⟩ := Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hk)
      have hk1' : g⁻¹ * (k : GL (Fin n) F) * g ∈ K := by
        have := Subgroup.mem_comap.1 hk1
        simpa [MulAut.conj_apply] using this
      simp only [stagesInnerFun]
      rw [map_mul, map_mul, invSqrtModular_leviIncl_of_mem k hk2, mul_one, Subgroup.coe_mul]
      congr 1
      have e : (x : GL (Fin n) F) * (k : GL (Fin n) F) * g =
          (x : GL (Fin n) F) * g * (g⁻¹ * (k : GL (Fin n) F) * g) := by group
      rw [e, hφK _ hk1']

def stagesInvFun (h : Refines β γ) (φ : parabolicIndSpace F n γ τ) :
    GL (Fin n) F → leviParabolicIndSpace F n β γ τ :=
  fun g => ⟨stagesInnerFun τ φ g, stagesInnerFun_mem τ h φ g⟩

/- English proof (translation)
Take `⟨hφP, K, hKo, hφK⟩` from `mem_indSpace.1 φ.2`. Use `⟨fun p g => ?_, K, hKo, fun k hk g => ?_⟩` and prove the remaining obligations. Rewrite using `[inflateTwist_apply]`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`.

Use `set m := leviProj F n β p`. Use `set u : blockUpper F n β := (leviIncl m)⁻¹ * p`. Establish `hu : (u : GL (Fin n) F) ∈ unipotentRadical F n β` using `leviProj_inv_mul_mem p`. Establish `hxm : ((x : GL (Fin n) F) * (m : GL (Fin n) F)) ∈ blockUpper F n β` using `mul_mem (levi_le_blockUpper x.2) (levi_le_blockUpper m.2)`. Use `set n'' : GL (Fin n) F := (x : GL (Fin n) F) * (m : GL (Fin n) F) * (u : GL (Fin n) F) * ((x : GL (Fin n) F) * (m : GL (Fin n) F))⁻¹`.

Establish `hn'' : n'' ∈ unipotentRadical F n γ` using `h.unipotentRadical_le F (conj_mem_unipotentRadical hxm hu)`. Establish `hφn : ∀ y, (φ : GL (Fin n) F → W) (n'' * y) = (φ : GL (Fin n) F → W) y`. Introduce `y`. Use `hφP ⟨n'', (mem_unipotentRadical.1 hn'').1⟩ y` as an intermediate fact. Rewrite `this` using `[inflateTwist_apply, sqrtModular_of_mem _ hn'', (mem_unipotentRadical_iff_leviProj (p := ⟨n'', (mem_unipotentRadical.1 hn'').1⟩)).1 hn'', map_one, one_smul, Module.End.one_apply]`.

Conclude with `this`. Establish `hp : (p : GL (Fin n) F) = (m : GL (Fin n) F) * (u : GL (Fin n) F)` using `by show (p : GL (Fin n) F) = (m : GL (Fin n) F) * (((leviIncl m)⁻¹ * p : blockUpper F n β) : GL (Fin n) F)`. Rewrite using `[Subgroup.coe_mul, Subgroup.coe_inv, leviIncl_coe, mul_inv_cancel_left]`. Establish `e : (x : GL (Fin n) F) * ((p : GL (Fin n) F) * g) = n'' * ((x : GL (Fin n) F) * (m : GL (Fin n) F) * g)`. Rewrite using `[hp]`.

Simplify using `only [n'']`. Use `group`. Establish `hs : sqrtModular F n β p = sqrtModular F n β (leviIncl m)` using `(sqrtModular_leviProj p).symm`. Use `show invSqrtModular F n β (leviIncl x) • (φ : GL (Fin n) F → W) ((x : GL (Fin n) F) * ((p : GL (Fin n) F) * g)) = sqrtModular F n β p • (invSqrtModular F n β (leviIncl (x * m)) • (φ : GL (Fin n) F → W) (((x * m : levi F n β) : GL (Fin n) F) * g))`. Rewrite using `[e, hφn, smul_smul, hs, map_mul, map_mul, Subgroup.coe_mul]`.

Use `congr 1`. Establish `h1` using `sqrtModular_mul_invSqrtModular (leviIncl m)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1, mul_one]`. Use `_ = _ := by ring`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Use `show invSqrtModular F n β (leviIncl x) • (φ : GL (Fin n) F → W) ((x : GL (Fin n) F) * (g * k)) = invSqrtModular F n β (leviIncl x) • (φ : GL (Fin n) F → W) ((x : GL (Fin n) F) * g)`. Rewrite using `[← mul_assoc, hφK k hk]`.
-/
theorem stagesInvFun_mem (h : Refines β γ) (φ : parabolicIndSpace F n γ τ) :
    stagesInvFun τ h φ ∈ parabolicIndSpace F n β (leviParabolicInd F n β γ τ) := by
  obtain ⟨hφP, K, hKo, hφK⟩ := mem_indSpace.1 φ.2
  refine ⟨fun p g => ?_, K, hKo, fun k hk g => ?_⟩
  · rw [inflateTwist_apply]
    apply Subtype.ext
    funext x
    set m := leviProj F n β p
    set u : blockUpper F n β := (leviIncl m)⁻¹ * p
    have hu : (u : GL (Fin n) F) ∈ unipotentRadical F n β := leviProj_inv_mul_mem p
    have hxm : ((x : GL (Fin n) F) * (m : GL (Fin n) F)) ∈ blockUpper F n β :=
      mul_mem (levi_le_blockUpper x.2) (levi_le_blockUpper m.2)
    set n'' : GL (Fin n) F := (x : GL (Fin n) F) * (m : GL (Fin n) F) * (u : GL (Fin n) F) *
      ((x : GL (Fin n) F) * (m : GL (Fin n) F))⁻¹
    have hn'' : n'' ∈ unipotentRadical F n γ :=
      h.unipotentRadical_le F (conj_mem_unipotentRadical hxm hu)
    have hφn : ∀ y, (φ : GL (Fin n) F → W) (n'' * y) = (φ : GL (Fin n) F → W) y := by
      intro y
      have := hφP ⟨n'', (mem_unipotentRadical.1 hn'').1⟩ y
      rw [inflateTwist_apply, sqrtModular_of_mem _ hn'',
        (mem_unipotentRadical_iff_leviProj (p := ⟨n'', (mem_unipotentRadical.1 hn'').1⟩)).1 hn'',
        map_one, one_smul, Module.End.one_apply] at this
      exact this
    have hp : (p : GL (Fin n) F) = (m : GL (Fin n) F) * (u : GL (Fin n) F) := by
      show (p : GL (Fin n) F) = (m : GL (Fin n) F) *
        (((leviIncl m)⁻¹ * p : blockUpper F n β) : GL (Fin n) F)
      rw [Subgroup.coe_mul, Subgroup.coe_inv, leviIncl_coe, mul_inv_cancel_left]
    have e : (x : GL (Fin n) F) * ((p : GL (Fin n) F) * g) =
        n'' * ((x : GL (Fin n) F) * (m : GL (Fin n) F) * g) := by
      rw [hp]
      simp only [n'']
      group
    have hs : sqrtModular F n β p = sqrtModular F n β (leviIncl m) :=
      (sqrtModular_leviProj p).symm
    show invSqrtModular F n β (leviIncl x) • (φ : GL (Fin n) F → W) ((x : GL (Fin n) F) * ((p : GL (Fin n) F) * g)) =
      sqrtModular F n β p • (invSqrtModular F n β (leviIncl (x * m)) •
        (φ : GL (Fin n) F → W) (((x * m : levi F n β) : GL (Fin n) F) * g))
    rw [e, hφn, smul_smul, hs, map_mul, map_mul, Subgroup.coe_mul]
    congr 1
    have h1 := sqrtModular_mul_invSqrtModular (leviIncl m)
    calc invSqrtModular F n β (leviIncl x)
        = invSqrtModular F n β (leviIncl x) *
            (sqrtModular F n β (leviIncl m) * invSqrtModular F n β (leviIncl m)) := by
          rw [h1, mul_one]
      _ = _ := by ring
  · apply Subtype.ext
    funext x
    show invSqrtModular F n β (leviIncl x) • (φ : GL (Fin n) F → W) ((x : GL (Fin n) F) * (g * k)) =
      invSqrtModular F n β (leviIncl x) • (φ : GL (Fin n) F → W) ((x : GL (Fin n) F) * g)
    rw [← mul_assoc, hφK k hk]

def inductionStagesLinearEquiv (h : Refines β γ) :
    parabolicIndSpace F n β (leviParabolicInd F n β γ τ) ≃ₗ[ℂ] parabolicIndSpace F n γ τ where
  toFun f := ⟨stagesFun τ f, stagesFun_mem τ h f⟩
  map_add' f f' := rfl
  map_smul' c f := rfl
  invFun φ := ⟨stagesInvFun τ h φ, stagesInvFun_mem τ h φ⟩
  left_inv f := by
    apply Subtype.ext
    funext g
    apply Subtype.ext
    funext x
    show invSqrtModular F n β (leviIncl x) • stagesFun τ f ((x : GL (Fin n) F) * g) = _
    rw [stagesFun, parabolicInd_levi_apply, smul_smul, one_mul, mul_comm,
      sqrtModular_mul_invSqrtModular, one_smul]
  right_inv φ := by
    apply Subtype.ext
    funext g
    show invSqrtModular F n β (leviIncl 1) • (φ : GL (Fin n) F → W) (((1 : levi F n β) :
      GL (Fin n) F) * g) = (φ : GL (Fin n) F → W) g
    rw [map_one, map_one, one_smul, OneMemClass.coe_one, one_mul]

def inductionStages (h : Refines β γ) :
    (parabolicInd F n β (leviParabolicInd F n β γ τ)).Equiv (parabolicInd F n γ τ) :=
  Representation.Equiv.mk (inductionStagesLinearEquiv τ h) fun _ => LinearMap.ext fun _ => rfl

end Stages

section Frobenius

variable {β γ : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {U : Type*} [AddCommGroup U] [Module ℂ U] (σ : Representation ℂ (levi F n β) U)
  (τ : Representation ℂ (levi F n γ) W)

/- English proof (translation)
Introduce `_ hu` and use `Subgroup.mem_subgroupOf.2 (mem_unipotentRadical.1 (Subgroup.mem_subgroupOf.1 hu)).1`.
-/
theorem leviUnipotent_le_leviParabolic : leviUnipotent F n β γ ≤ leviParabolic F n β γ :=
  fun _ hu => Subgroup.mem_subgroupOf.2 (mem_unipotentRadical.1 (Subgroup.mem_subgroupOf.1 hu)).1

/- English proof (translation)
The claim follows from `Subgroup.mem_subgroupOf.2 (levi_le_blockUpper m.2)`.
-/
theorem Refines.leviIncl_mem_leviParabolic (h : Refines β γ) (m : levi F n γ) :
    h.leviIncl F m ∈ leviParabolic F n β γ :=
  Subgroup.mem_subgroupOf.2 (levi_le_blockUpper m.2)

/- English proof (translation)
Rewrite using `[leviInflateTwist_apply, sqrtModularLeviPar_of_mem h _ hu, (mem_unipotentRadical_iff_leviProj (p := leviParabolicIncl F n β γ u)).1 hu, map_one, one_smul, Module.End.one_apply]`.
-/
theorem leviInflateTwist_of_mem (h : Refines β γ) (u : leviParabolic F n β γ)
    (hu : ((u : levi F n β) : GL (Fin n) F) ∈ unipotentRadical F n γ) (w : W) :
    leviInflateTwist F n β γ τ u w = w := by
  rw [leviInflateTwist_apply, sqrtModularLeviPar_of_mem h _ hu,
    (mem_unipotentRadical_iff_leviProj (p := leviParabolicIncl F n β γ u)).1 hu, map_one, one_smul,
    Module.End.one_apply]

/- English proof (translation)
Establish `e : leviProj F n γ (leviParabolicIncl F n β γ ⟨h.leviIncl F m, h.leviIncl_mem_leviParabolic m⟩) = m` using `leviProj_of_mem_levi m.2`. Rewrite using `[leviInflateTwist_apply, e]`. Both sides reduce to the same expression.
-/
theorem leviInflateTwist_leviIncl (h : Refines β γ) (m : levi F n γ) (w : W) :
    leviInflateTwist F n β γ τ ⟨h.leviIncl F m, h.leviIncl_mem_leviParabolic m⟩ w =
      sqrtModularLeviPar F n β γ (h.leviToLeviPar F m) • τ m w := by
  have e : leviProj F n γ (leviParabolicIncl F n β γ ⟨h.leviIncl F m,
      h.leviIncl_mem_leviParabolic m⟩) = m := leviProj_of_mem_levi m.2
  rw [leviInflateTwist_apply, e]
  rfl

/- English proof (translation)
Rewrite using `[leviJacquetRep_mk, smul_smul, sqrtModularLeviPar_mul_inv, one_smul]`.
-/
theorem mk_leviIncl_apply (h : Refines β γ) (m : levi F n γ) (w : U) :
    Representation.Coinvariants.mk (σ.comp (leviUnipotent F n β γ).subtype) (σ (h.leviIncl F m) w) =
      sqrtModularLeviPar F n β γ (h.leviToLeviPar F m) •
        leviJacquetRep h σ m (Representation.Coinvariants.mk _ w) := by
  rw [leviJacquetRep_mk, smul_smul, sqrtModularLeviPar_mul_inv, one_smul]

def leviJacquetAdjunction (h : Refines β γ) :
    Representation.IntertwiningMap (σ.comp (leviParabolic F n β γ).subtype)
        (leviInflateTwist F n β γ τ) ≃ₗ[ℂ]
      Representation.IntertwiningMap (leviJacquetRep h σ) τ where
  toFun φ := ⟨Representation.Coinvariants.lift _ φ.toLinearMap fun u => LinearMap.ext fun v => by
      have hu : ((u : levi F n β) : GL (Fin n) F) ∈ unipotentRadical F n γ :=
        Subgroup.mem_subgroupOf.1 u.2
      have e := Representation.IntertwiningMap.isIntertwining _ _ φ
        ⟨u, leviUnipotent_le_leviParabolic u.2⟩ v
      simp only [MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply] at e
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidHom.coe_comp,
        Subgroup.coe_subtype, Representation.IntertwiningMap.toLinearMap_apply]
      rw [e, leviInflateTwist_of_mem τ h _ hu],
    fun m => Representation.Coinvariants.hom_ext (LinearMap.ext fun v => by
      have e := Representation.IntertwiningMap.isIntertwining _ _ φ
        ⟨h.leviIncl F m, h.leviIncl_mem_leviParabolic m⟩ v
      simp only [MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply] at e
      simp only [LinearMap.coe_comp, Function.comp_apply, leviJacquetRep_mk, map_smul,
        Representation.Coinvariants.lift_mk, Representation.IntertwiningMap.toLinearMap_apply]
      rw [e, leviInflateTwist_leviIncl τ h, smul_smul, mul_comm, sqrtModularLeviPar_mul_inv,
        one_smul])⟩
  map_add' φ ψ := Representation.IntertwiningMap.ext (Representation.Coinvariants.hom_ext
    (LinearMap.ext fun v => rfl))
  map_smul' c φ := Representation.IntertwiningMap.ext (Representation.Coinvariants.hom_ext
    (LinearMap.ext fun v => rfl))
  invFun ψ := ⟨ψ.toLinearMap ∘ₗ Representation.Coinvariants.mk _, fun q => LinearMap.ext fun v => by
      set m := leviProj F n γ (leviParabolicIncl F n β γ q)
      set u : levi F n β := (h.leviIncl F m)⁻¹ * (q : levi F n β)
      have hu : ((u : levi F n β) : GL (Fin n) F) ∈ unipotentRadical F n γ := by
        have := leviProj_inv_mul_mem (leviParabolicIncl F n β γ q)
        exact this
      have hq : (q : levi F n β) = h.leviIncl F m * u := by
        simp only [u, mul_inv_cancel_left]
      have hsq : sqrtModularLeviPar F n β γ (leviParabolicToLeviPar F n β γ q) =
          sqrtModularLeviPar F n β γ (h.leviToLeviPar F m) := by
        have hmul : leviParabolicToLeviPar F n β γ q = h.leviToLeviPar F m *
            ⟨(u : GL (Fin n) F), u.2, (mem_unipotentRadical.1 hu).1⟩ := by
          apply Subtype.ext
          show ((q : levi F n β) : GL (Fin n) F) = _
          rw [hq]
          rfl
        rw [hmul, map_mul, sqrtModularLeviPar_of_mem h
          ⟨(u : GL (Fin n) F), u.2, (mem_unipotentRadical.1 hu).1⟩ hu, mul_one]
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidHom.coe_comp,
        Subgroup.coe_subtype, Representation.IntertwiningMap.toLinearMap_apply]
      have hmk : Representation.Coinvariants.mk (σ.comp (leviUnipotent F n β γ).subtype) (σ u v) =
          Representation.Coinvariants.mk _ v :=
        Representation.Coinvariants.mk_self_apply (σ.comp (leviUnipotent F n β γ).subtype)
          ⟨u, Subgroup.mem_subgroupOf.2 hu⟩ v
      rw [hq, map_mul, Module.End.mul_apply, mk_leviIncl_apply σ h, hmk, map_smul,
        Representation.IntertwiningMap.isIntertwining _ _ ψ, leviInflateTwist_apply, hsq]⟩
  left_inv φ := Representation.IntertwiningMap.ext (LinearMap.ext fun v => rfl)
  right_inv ψ := Representation.IntertwiningMap.ext (Representation.Coinvariants.hom_ext
    (LinearMap.ext fun v => rfl))

def leviFrobenius (h : Refines β γ) (hσ : IsSmooth σ) :
    Representation.IntertwiningMap σ (leviParabolicInd F n β γ τ) ≃ₗ[ℂ]
      Representation.IntertwiningMap (leviJacquetRep h σ) τ :=
  (frobenius (leviParabolic F n β γ) (leviInflateTwist F n β γ τ) hσ).trans
    (leviJacquetAdjunction σ τ h)

end Frobenius

end Parabolic

end GroundTheory.Automorphic
