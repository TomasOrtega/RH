import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleAdmissibleDecomposableCompEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContractsTensorProductChain
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivProdChosenIrrGLPairDegreeZero
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
import GroundTheory.AutomorphicForms.GLnLocal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleOfFiniteLengthSubquotients
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalOfSmIndFixed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIrreducibleOfFixed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfSumApplyEqZero

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.LeviTensor

section Abstract

variable {G H V X : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]

/- English proof (translation)
Use `haveI : IsSimpleOrder (Subrepresentation ρ) := hi`. Break down `eq_bot_or_eq_top (⟨T, hT⟩ : Subrepresentation ρ) with h | h` into its components or cases. Conclude with `absurd (congrArg Subrepresentation.toSubmodule h) h0`. Conclude with `congrArg Subrepresentation.toSubmodule h`.
-/
theorem eq_top_of_stable {ρ : Representation ℂ G V} (hi : ρ.IsIrreducible) (T : Submodule ℂ V)
    (hT : ∀ g, ∀ x ∈ T, ρ g x ∈ T) (h0 : T ≠ ⊥) : T = ⊤ := by
  haveI : IsSimpleOrder (Subrepresentation ρ) := hi
  rcases eq_bot_or_eq_top (⟨T, hT⟩ : Subrepresentation ρ) with h | h
  · exact absurd (congrArg Subrepresentation.toSubmodule h) h0
  · exact congrArg Subrepresentation.toSubmodule h

/- English proof (translation)
Establish `hst : ∀ v ∈ fixed σ K, A v ∈ fixed σ K` using `fun v hv x => by`. Establish `h` using `hv x`. Simplify using `only [MonoidHom.one_apply, Units.val_one, one_smul] at h ⊢`. Rewrite using `[← hA, h]`. Set `B : Module.End ℂ (fixed σ K)` to `A.restrict hst`.

Use `haveI : Nontrivial (fixed σ K) := ⟨⟨⟨u, hu⟩, 0, fun h => hu0 (congrArg Subtype.val h)⟩⟩`. Take `⟨c, hc⟩` from `Module.End.exists_eigenvalue B`. Take `⟨w, hw⟩` from `hc.exists_hasEigenvector`. Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `hT` using `eq_top_of_stable hi (LinearMap.ker (A - c • LinearMap.id)) (fun g x hx => by`.

Simplify using `only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hx ⊢`. Rewrite using `[hA, hx, map_smul]) (fun h => by`. Establish `h1 : (w : X) ∈ LinearMap.ker (A - c • LinearMap.id)`. Use `congrArg Subtype.val hw.apply_eq_smul` as an intermediate fact. Simplify `this` using `[B, sub_eq_zero]`.

Rewrite `h1` using `[h, Submodule.mem_bot]`. Conclude with `hw.2 (Subtype.ext h1))`. Use extensionality with `x`. Establish `: x ∈ LinearMap.ker (A - c • LinearMap.id)` using `hT ▸ Submodule.mem_top`. Simplify `this` using `[sub_eq_zero]`.
-/
theorem schur {σ : Representation ℂ G X} (hi : σ.IsIrreducible) (K : Subgroup G)
    [FiniteDimensional ℂ (fixed σ K)] {u : X} (hu : u ∈ fixed σ K) (hu0 : u ≠ 0)
    (A : X →ₗ[ℂ] X) (hA : ∀ g s, A (σ g s) = σ g (A s)) : ∃ c : ℂ, A = c • LinearMap.id := by
  have hst : ∀ v ∈ fixed σ K, A v ∈ fixed σ K := fun v hv x => by
    have h := hv x
    simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h ⊢
    rw [← hA, h]
  let B : Module.End ℂ (fixed σ K) := A.restrict hst
  haveI : Nontrivial (fixed σ K) := ⟨⟨⟨u, hu⟩, 0, fun h => hu0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue B
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  refine ⟨c, ?_⟩
  have hT := eq_top_of_stable hi (LinearMap.ker (A - c • LinearMap.id)) (fun g x hx => by
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        sub_eq_zero] at hx ⊢
      rw [hA, hx, map_smul]) (fun h => by
      have h1 : (w : X) ∈ LinearMap.ker (A - c • LinearMap.id) := by
        have := congrArg Subtype.val hw.apply_eq_smul
        simpa [B, sub_eq_zero] using this
      rw [h, Submodule.mem_bot] at h1
      exact hw.2 (Subtype.ext h1))
  ext x
  have : x ∈ LinearMap.ker (A - c • LinearMap.id) := hT ▸ Submodule.mem_top
  simpa [sub_eq_zero] using this

def homSp (ρ : Representation ℂ (G × H) V) (σ : Representation ℂ G X) : Submodule ℂ (X →ₗ[ℂ] V) where
  carrier := {f | ∀ g s, f (σ g s) = ρ (g, 1) (f s)}
  add_mem' := fun {a b} ha hb g s => by simp [ha g s, hb g s]
  zero_mem' := fun g s => by simp
  smul_mem' := fun c f hf g s => by simp [hf g s]

/- English proof (translation)
Rewrite using `[← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]`. Simplify using the standard rewrite rules.
-/
theorem comm_one (ρ : Representation ℂ (G × H) V) (g : G) (h : H) (v : V) :
    ρ (1, h) (ρ (g, 1) v) = ρ (g, 1) (ρ (1, h) v) := by
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  simp

def homRep (ρ : Representation ℂ (G × H) V) (σ : Representation ℂ G X) :
    Representation ℂ H (homSp ρ σ) where
  toFun h := LinearMap.restrict (LinearMap.compRight ℂ (ρ (1, h)) : (X →ₗ[ℂ] V) →ₗ[ℂ] (X →ₗ[ℂ] V))
    (fun f hf g s => by
      show ρ (1, h) (f (σ g s)) = ρ (g, 1) (ρ (1, h) (f s))
      rw [hf g s, comm_one])
  map_one' := by
    ext f s
    have : ((1 : G), (1 : H)) = 1 := rfl
    simp [this]
  map_mul' a b := by
    ext f s
    show ρ (1, a * b) ((f : X →ₗ[ℂ] V) s) = ρ (1, a) (ρ (1, b) ((f : X →ₗ[ℂ] V) s))
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem homRep_apply (ρ : Representation ℂ (G × H) V) (σ : Representation ℂ G X) (h : H)
    (f : homSp ρ σ) (s : X) : (homRep ρ σ h f : X →ₗ[ℂ] V) s = ρ (1, h) ((f : X →ₗ[ℂ] V) s) := rfl

def evMap (ρ : Representation ℂ (G × H) V) (σ : Representation ℂ G X) : X ⊗[ℂ] homSp ρ σ →ₗ[ℂ] V :=
  TensorProduct.lift (LinearMap.flip (homSp ρ σ).subtype)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem evMap_tmul (ρ : Representation ℂ (G × H) V) (σ : Representation ℂ G X) (s : X)
    (f : homSp ρ σ) : evMap ρ σ (s ⊗ₜ f) = (f : X →ₗ[ℂ] V) s := rfl

/- English proof (translation)
Proceed by induction on `x with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul s f`. Take `⟨g, h⟩` from `p`.

Rewrite using `[extTensor_tmul, evMap_tmul, evMap_tmul, homRep_apply, f.2 g s, ← Module.End.mul_apply, ← map_mul]`. Simplify using the standard rewrite rules.
-/
theorem evMap_equivariant (ρ : Representation ℂ (G × H) V) (σ : Representation ℂ G X) (p : G × H)
    (x : X ⊗[ℂ] homSp ρ σ) :
    evMap ρ σ (extTensor σ (homRep ρ σ) p x) = ρ p (evMap ρ σ x) := by
  induction x with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul s f =>
    obtain ⟨g, h⟩ := p
    rw [extTensor_tmul, evMap_tmul, evMap_tmul, homRep_apply, f.2 g s, ← Module.End.mul_apply, ← map_mul]
    simp

end Abstract

section Step

variable {G H V X : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]

/- English proof (translation)
Establish `hT` using `eq_top_of_stable hσ (LinearMap.ker (f - f')) (fun g x hx => by`. Simplify using `only [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hx ⊢`. Rewrite using `[hf g x, hf' g x, hx]) (fun h0 => by`. Establish `h1 : u ∈ LinearMap.ker (f - f')` using `by simp [h]`. Rewrite `h1` using `[h0, Submodule.mem_bot]`.

Conclude with `hu h1)`. Use extensionality with `x`. Establish `: x ∈ LinearMap.ker (f - f')` using `hT ▸ Submodule.mem_top`. Simplify `this` using `[sub_eq_zero]`.
-/
theorem eq_of_eq_at {ρ : Representation ℂ (G × H) V} {σ : Representation ℂ G X} (hσ : σ.IsIrreducible)
    {u : X} (hu : u ≠ 0) {f f' : X →ₗ[ℂ] V} (hf : f ∈ homSp ρ σ) (hf' : f' ∈ homSp ρ σ) (h : f u = f' u) :
    f = f' := by
  have hT := eq_top_of_stable hσ (LinearMap.ker (f - f')) (fun g x hx => by
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hx ⊢
      rw [hf g x, hf' g x, hx]) (fun h0 => by
      have h1 : u ∈ LinearMap.ker (f - f') := by simp [h]
      rw [h0, Submodule.mem_bot] at h1
      exact hu h1)
  ext x
  have : x ∈ LinearMap.ker (f - f') := hT ▸ Submodule.mem_top
  simpa [sub_eq_zero] using this

/- English proof (translation)
Use `⟨GlobalTheory.CompanionTheory.EvalTensor.lift_flip_subtype_injective σ (ρ.comp (MonoidHom.inl G H)) hσ hS (homSp ρ σ) (fun f hf g s => hf g s), ?_⟩` and prove the remaining obligations. Establish `hT` using `eq_top_of_stable hi (LinearMap.range (evMap ρ σ)) (by`. Introduce and unpack `p _ ⟨x, rfl⟩`. Conclude with `⟨_, evMap_equivariant ρ σ p x⟩) (fun hb => by`. Take `⟨s, hs⟩ : ∃ s, i s ≠ 0` from `by by_contra! h`.

Conclude with `h0 (LinearMap.ext h)`. Establish `h1 : i s ∈ LinearMap.range (evMap ρ σ)` using `⟨s ⊗ₜ ⟨i, hm⟩, rfl⟩`. Rewrite `h1` using `[hb, Submodule.mem_bot]`. Conclude with `hs h1)`. Conclude with `LinearMap.range_eq_top.1 hT`.
-/
theorem evMap_bijective {ρ : Representation ℂ (G × H) V} {σ : Representation ℂ G X}
    (hi : ρ.IsIrreducible) (hσ : σ.IsIrreducible)
    (hS : ∀ A : X →ₗ[ℂ] X, (∀ g s, A (σ g s) = σ g (A s)) → ∃ c : ℂ, A = c • LinearMap.id)
    {i : X →ₗ[ℂ] V} (hm : i ∈ homSp ρ σ) (h0 : i ≠ 0) : Function.Bijective (evMap ρ σ) := by
  refine ⟨GlobalTheory.CompanionTheory.EvalTensor.lift_flip_subtype_injective σ (ρ.comp (MonoidHom.inl G H)) hσ hS (homSp ρ σ) (fun f hf g s => hf g s), ?_⟩
  have hT := eq_top_of_stable hi (LinearMap.range (evMap ρ σ)) (by
      rintro p _ ⟨x, rfl⟩
      exact ⟨_, evMap_equivariant ρ σ p x⟩) (fun hb => by
      obtain ⟨s, hs⟩ : ∃ s, i s ≠ 0 := by
        by_contra! h
        exact h0 (LinearMap.ext h)
      have h1 : i s ∈ LinearMap.range (evMap ρ σ) := ⟨s ⊗ₜ ⟨i, hm⟩, rfl⟩
      rw [hb, Submodule.mem_bot] at h1
      exact hs h1)
  exact LinearMap.range_eq_top.1 hT

/- English proof (translation)
Establish `hnt : Nontrivial (Subrepresentation (homRep ρ σ))` using `⟨⊥, ⊤, fun h => by`. Establish `h1` using `congrArg Subrepresentation.toSubmodule h`. Establish `h2 : (⟨i, hm⟩ : homSp ρ σ) ∈ (⊥ : Submodule ℂ (homSp ρ σ))`. Establish `: (⟨i, hm⟩ : homSp ρ σ) ∈ (⊤ : Subrepresentation (homRep ρ σ)).toSubmodule` using `Submodule.mem_top`. Rewrite `this` using `[← h1]`.

Conclude with `this`. Rewrite `h2` using `[Submodule.mem_bot]`. Conclude with `h0 (congrArg Subtype.val h2)⟩`. Use `⟨fun Q => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hQ : Q.toSubmodule = ⊥`.

Conclude with `Or.inl (Subrepresentation.toSubmodule_injective hQ)`. Use `Or.inr (Subrepresentation.toSubmodule_injective ?_)` and prove the remaining obligations. Use `show Q.toSubmodule = ⊤`. Take `⟨f₁, hf₁, hf₁0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hQ`. Set `R : Submodule ℂ V` to `Submodule.span ℂ {v | ∃ f ∈ Q.toSubmodule, ∃ s, v = (f : X →ₗ[ℂ] V) s}`.

Establish `hRtop : R = ⊤`. Use `eq_top_of_stable hi R (fun p x hx => ?_) (fun hb0 => ?_)` and prove the remaining obligations. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f, hf, s, rfl⟩` from `hx`.

Use `Submodule.subset_span ⟨homRep ρ σ p.2 f, Q.apply_mem_toSubmodule _ hf, σ p.1 s, ?_⟩` and prove the remaining obligations. Rewrite using `[homRep_apply, f.2 p.1 s, ← Module.End.mul_apply, ← map_mul]`. Simplify using the standard rewrite rules. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add]`.

Conclude with `R.add_mem ha hb`. Consider the case `smul c a _ ha => rw [map_smul]`. Conclude with `R.smul_mem c ha`. Take `⟨s, hs⟩ : ∃ s, (f₁ : X →ₗ[ℂ] V) s ≠ 0` from `by by_contra! h`. Conclude with `hf₁0 (Subtype.ext (LinearMap.ext h))`.

Establish `h1 : (f₁ : X →ₗ[ℂ] V) s ∈ R` using `Submodule.subset_span ⟨f₁, hf₁, s, rfl⟩`. Rewrite `h1` using `[hb0, Submodule.mem_bot]`. Conclude with `hs h1`. Assume the negation of the conclusion as `hne`. Take `⟨f₀, hf₀⟩ : ∃ f₀, f₀ ∉ Q.toSubmodule` from `by by_contra! h`.

Conclude with `hne (Submodule.eq_top_iff'.2 h)`. Take `⟨l, hl1, hl2⟩` from `Submodule.exists_le_ker_of_notMem hf₀`. Take `⟨s, hs⟩ : ∃ s, (f₁ : X →ₗ[ℂ] V) s ≠ 0` from `by by_contra! h`. Conclude with `hf₁0 (Subtype.ext (LinearMap.ext h))`. Establish `hs0 : s ≠ 0` using `fun h => hs (by simp [h])`.

Set `E` to `LinearEquiv.ofBijective (evMap ρ σ) hb`. Set `j : X ⊗[ℂ] homSp ρ σ →ₗ[ℂ] X` to `(TensorProduct.rid ℂ X).toLinearMap ∘ₗ LinearMap.lTensor X l`. Establish `hj : ∀ (x : X) (f : homSp ρ σ), j (x ⊗ₜ f) = l f • x` using `fun x f => by simp [j]`. Establish `hz : ∀ v ∈ R, j (E.symm v) = 0`. Introduce `v hv`.

Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f, hf, t, rfl⟩` from `hx`. Establish `: E.symm ((f : X →ₗ[ℂ] V) t) = t ⊗ₜ f` using `E.symm_apply_eq.2 rfl`. Rewrite using `[this, hj, hl2 hf]`.

Simplify using the standard rewrite rules. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => simp [ha, hb]`. Consider the case `smul c a _ ha => simp [ha]`. Establish `h3` using `hz ((f₀ : X →ₗ[ℂ] V) s) (hRtop ▸ Submodule.mem_top)`.

Establish `: E.symm ((f₀ : X →ₗ[ℂ] V) s) = s ⊗ₜ f₀` using `E.symm_apply_eq.2 rfl`. Rewrite `h3` using `[this, hj]`. Conclude with `(smul_ne_zero hl1 hs0) h3`.
-/
theorem homRep_irreducible {ρ : Representation ℂ (G × H) V} {σ : Representation ℂ G X}
    (hi : ρ.IsIrreducible) (hb : Function.Bijective (evMap ρ σ)) {i : X →ₗ[ℂ] V} (hm : i ∈ homSp ρ σ)
    (h0 : i ≠ 0) : (homRep ρ σ).IsIrreducible := by
  have hnt : Nontrivial (Subrepresentation (homRep ρ σ)) := ⟨⊥, ⊤, fun h => by
    have h1 := congrArg Subrepresentation.toSubmodule h
    have h2 : (⟨i, hm⟩ : homSp ρ σ) ∈ (⊥ : Submodule ℂ (homSp ρ σ)) := by
      have : (⟨i, hm⟩ : homSp ρ σ) ∈ (⊤ : Subrepresentation (homRep ρ σ)).toSubmodule := Submodule.mem_top
      rw [← h1] at this
      exact this
    rw [Submodule.mem_bot] at h2
    exact h0 (congrArg Subtype.val h2)⟩
  refine ⟨fun Q => ?_⟩
  by_cases hQ : Q.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hQ)
  refine Or.inr (Subrepresentation.toSubmodule_injective ?_)
  show Q.toSubmodule = ⊤
  obtain ⟨f₁, hf₁, hf₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ

  let R : Submodule ℂ V := Submodule.span ℂ {v | ∃ f ∈ Q.toSubmodule, ∃ s, v = (f : X →ₗ[ℂ] V) s}
  have hRtop : R = ⊤ := by
    refine eq_top_of_stable hi R (fun p x hx => ?_) (fun hb0 => ?_)
    · induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨f, hf, s, rfl⟩ := hx
        refine Submodule.subset_span ⟨homRep ρ σ p.2 f, Q.apply_mem_toSubmodule _ hf, σ p.1 s, ?_⟩
        rw [homRep_apply, f.2 p.1 s, ← Module.End.mul_apply, ← map_mul]
        simp
      | zero => simp
      | add a b _ _ ha hb => rw [map_add]; exact R.add_mem ha hb
      | smul c a _ ha => rw [map_smul]; exact R.smul_mem c ha
    · obtain ⟨s, hs⟩ : ∃ s, (f₁ : X →ₗ[ℂ] V) s ≠ 0 := by
        by_contra! h
        exact hf₁0 (Subtype.ext (LinearMap.ext h))
      have h1 : (f₁ : X →ₗ[ℂ] V) s ∈ R := Submodule.subset_span ⟨f₁, hf₁, s, rfl⟩
      rw [hb0, Submodule.mem_bot] at h1
      exact hs h1
  by_contra hne
  obtain ⟨f₀, hf₀⟩ : ∃ f₀, f₀ ∉ Q.toSubmodule := by
    by_contra! h
    exact hne (Submodule.eq_top_iff'.2 h)
  obtain ⟨l, hl1, hl2⟩ := Submodule.exists_le_ker_of_notMem hf₀
  obtain ⟨s, hs⟩ : ∃ s, (f₁ : X →ₗ[ℂ] V) s ≠ 0 := by
    by_contra! h
    exact hf₁0 (Subtype.ext (LinearMap.ext h))
  have hs0 : s ≠ 0 := fun h => hs (by simp [h])
  let E := LinearEquiv.ofBijective (evMap ρ σ) hb
  let j : X ⊗[ℂ] homSp ρ σ →ₗ[ℂ] X := (TensorProduct.rid ℂ X).toLinearMap ∘ₗ LinearMap.lTensor X l
  have hj : ∀ (x : X) (f : homSp ρ σ), j (x ⊗ₜ f) = l f • x := fun x f => by simp [j]
  have hz : ∀ v ∈ R, j (E.symm v) = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, t, rfl⟩ := hx
      have : E.symm ((f : X →ₗ[ℂ] V) t) = t ⊗ₜ f := E.symm_apply_eq.2 rfl
      rw [this, hj, hl2 hf]
      simp
    | zero => simp
    | add a b _ _ ha hb => simp [ha, hb]
    | smul c a _ ha => simp [ha]
  have h3 := hz ((f₀ : X →ₗ[ℂ] V) s) (hRtop ▸ Submodule.mem_top)
  have : E.symm ((f₀ : X →ₗ[ℂ] V) s) = s ⊗ₜ f₀ := E.symm_apply_eq.2 rfl
  rw [this, hj] at h3
  exact (smul_ne_zero hl1 hs0) h3

end Step

section Top

variable {G H V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H]
  [IsTopologicalGroup H] [AddCommGroup V] [Module ℂ V]

def HasCOBasis (G : Type) [Group G] [TopologicalSpace G] : Prop :=
  ∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/- English proof (translation)
Establish `key : ∀ (f : homSp ρ σ) (h : H), ρ (1, h) ((f : X →ₗ[ℂ] V) u) = (f : X →ₗ[ℂ] V) u → homRep ρ σ h f = f` using `fun f h hh => Subtype.ext (eq_of_eq_at hσ hu (homRep ρ σ h f).2 f.2 hh)`. Use `⟨fun f => ?_, fun K' hKo' hKc' => ?_⟩` and prove the remaining obligations. Establish `: {h : H | homRep ρ σ h f = f} = (fun h : H => ((1 : G), h)) ⁻¹' {p : G × H | ρ p ((f : X →ₗ[ℂ] V) u) = (f : X →ₗ[ℂ] V) u}`. Use extensionality with `h`. Use `⟨fun hh => ?_, key f h⟩` and prove the remaining obligations.

Use `congrArg (fun F : homSp ρ σ => (F : X →ₗ[ℂ] V) u) hh` as an intermediate fact. Conclude with `this`. Rewrite using `[this]`. Conclude with `(ha.1 _).preimage (by fun_prop)`. Establish `hop : IsOpen ((K.prod K' : Subgroup (G × H)) : Set (G × H))`.

Rewrite using `[Subgroup.coe_prod]`. Conclude with `hKo.prod hKo'`. Establish `hcp : IsCompact ((K.prod K' : Subgroup (G × H)) : Set (G × H))`. Rewrite using `[Subgroup.coe_prod]`. Conclude with `hKc.prod hKc'`.

Use `haveI := ha.2 _ hop hcp`. Set `L : fixed (homRep ρ σ) K' →ₗ[ℂ] fixed ρ (K.prod K')` to `LinearMap.codRestrict _ ((LinearMap.applyₗ u : (X →ₗ[ℂ] V) →ₗ[ℂ] V) ∘ₗ (homSp ρ σ).subtype ∘ₗ (fixed (homRep ρ σ) K').subtype) (fun f p => by`. Establish `h1` using `f.2 ⟨p.1.2, (Subgroup.mem_prod.1 p.2).2⟩`. Simplify using `only [MonoidHom.one_apply, Units.val_one, one_smul] at h1 ⊢`. Establish `h2` using `congrArg (fun F : homSp ρ σ => (F : X →ₗ[ℂ] V) u) h1`.

Establish `h3 : ρ (1, p.1.2) ((f.1 : X →ₗ[ℂ] V) u) = (f.1 : X →ₗ[ℂ] V) u` using `h2`. Establish `h4` using `f.1.2 p.1.1 u`. Rewrite `h4` using `[hfix _ (Subgroup.mem_prod.1 p.2).1]`. Establish `h5 : (p.1 : G × H) = (1, p.1.2) * (p.1.1, 1)` using `by simp`. Use `show ρ p.1 ((f.1 : X →ₗ[ℂ] V) u) = (f.1 : X →ₗ[ℂ] V) u`.

Rewrite using `[h5, map_mul, Module.End.mul_apply, ← h4, h3])`. Use `FiniteDimensional.of_injective L fun a b hab => ?_` and prove the remaining obligations. Establish `h1 : (a.1 : X →ₗ[ℂ] V) u = (b.1 : X →ₗ[ℂ] V) u` using `congrArg Subtype.val hab`. Conclude with `Subtype.ext (Subtype.ext (eq_of_eq_at hσ hu a.1.2 b.1.2 h1))`.
-/
theorem isAdmissible_homRep {X : Type} [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ (G × H) V}
    {σ : Representation ℂ G X} (ha : IsAdmissible ρ) (hσ : σ.IsIrreducible) {K : Subgroup G}
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) {u : X} (hu : u ≠ 0)
    (hfix : ∀ x ∈ K, σ x u = u) : IsAdmissible (homRep ρ σ) := by
  have key : ∀ (f : homSp ρ σ) (h : H), ρ (1, h) ((f : X →ₗ[ℂ] V) u) = (f : X →ₗ[ℂ] V) u →
      homRep ρ σ h f = f := fun f h hh =>
    Subtype.ext (eq_of_eq_at hσ hu (homRep ρ σ h f).2 f.2 hh)
  refine ⟨fun f => ?_, fun K' hKo' hKc' => ?_⟩
  · have : {h : H | homRep ρ σ h f = f} =
        (fun h : H => ((1 : G), h)) ⁻¹' {p : G × H | ρ p ((f : X →ₗ[ℂ] V) u) = (f : X →ₗ[ℂ] V) u} := by
      ext h
      refine ⟨fun hh => ?_, key f h⟩
      have := congrArg (fun F : homSp ρ σ => (F : X →ₗ[ℂ] V) u) hh
      exact this
    rw [this]
    exact (ha.1 _).preimage (by fun_prop)
  · have hop : IsOpen ((K.prod K' : Subgroup (G × H)) : Set (G × H)) := by
      rw [Subgroup.coe_prod]; exact hKo.prod hKo'
    have hcp : IsCompact ((K.prod K' : Subgroup (G × H)) : Set (G × H)) := by
      rw [Subgroup.coe_prod]; exact hKc.prod hKc'
    haveI := ha.2 _ hop hcp
    let L : fixed (homRep ρ σ) K' →ₗ[ℂ] fixed ρ (K.prod K') :=
      LinearMap.codRestrict _
        ((LinearMap.applyₗ u : (X →ₗ[ℂ] V) →ₗ[ℂ] V) ∘ₗ (homSp ρ σ).subtype ∘ₗ (fixed (homRep ρ σ) K').subtype)
        (fun f p => by
          have h1 := f.2 ⟨p.1.2, (Subgroup.mem_prod.1 p.2).2⟩
          simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h1 ⊢
          have h2 := congrArg (fun F : homSp ρ σ => (F : X →ₗ[ℂ] V) u) h1
          have h3 : ρ (1, p.1.2) ((f.1 : X →ₗ[ℂ] V) u) = (f.1 : X →ₗ[ℂ] V) u := h2
          have h4 := f.1.2 p.1.1 u
          rw [hfix _ (Subgroup.mem_prod.1 p.2).1] at h4
          have h5 : (p.1 : G × H) = (1, p.1.2) * (p.1.1, 1) := by simp
          show ρ p.1 ((f.1 : X →ₗ[ℂ] V) u) = (f.1 : X →ₗ[ℂ] V) u
          rw [h5, map_mul, Module.End.mul_apply, ← h4, h3])
    refine FiniteDimensional.of_injective L fun a b hab => ?_
    have h1 : (a.1 : X →ₗ[ℂ] V) u = (b.1 : X →ₗ[ℂ] V) u := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext (eq_of_eq_at hσ hu a.1.2 b.1.2 h1))

/- English proof (translation)
Take `⟨K, S, u, hKo, hKc, huS, hu0, hfix, hSi, hfd⟩` from `GlobalTheory.CompanionTheory.ProdSub.exists_irreducible_sub_inl hG hH ρ ha hi`. Set `σ` to `S.toRepresentation`. Set `u' : S.toSubmodule` to `⟨u, huS⟩`. Establish `hu' : u' ≠ 0` using `fun h => hu0 (congrArg Subtype.val h)`. Establish `hfix' : ∀ x ∈ K, σ x u' = u'` using `fun x hx => Subtype.ext (hfix x hx)`.

Establish `hmem : u' ∈ fixed σ K` using `fun x => by`. Simplify using `using hfix' x x.2`. Establish `hS` using `fun A hA => schur hSi K hmem hu' A hA`. Establish `hm : S.toSubmodule.subtype ∈ homSp ρ σ` using `fun g s => rfl`. Establish `h0 : S.toSubmodule.subtype ≠ 0` using `fun h => hu0 (by`.

Use `congrArg (fun F : S.toSubmodule →ₗ[ℂ] V => F u') h` as an intermediate fact. Conclude with `this)`. Establish `hb` using `evMap_bijective hi hSi hS hm h0`. Establish `hsm : IsSmooth σ` using `fun v => by`. Establish `: {g : G | σ g v = v} = (fun g : G => (g, (1 : H))) ⁻¹' {p : G × H | ρ p v.1 = v.1}`.

Use extensionality with `g`. Conclude with `Subtype.ext_iff`. Rewrite using `[this]`. Conclude with `(ha.1 _).preimage (by fun_prop)`. Establish `hadm` using `isAdmissible_homRep ha hSi hKo hKc hu' hfix'`.

Use `⟨⟨_, σ, hsm, hSi⟩, ⟨_, homRep ρ σ, hadm.1, homRep_irreducible hi hb hm h0⟩, hadm, ⟨?_⟩⟩` and prove the remaining obligations. Conclude with `.mk (LinearEquiv.ofBijective (evMap ρ σ) hb) fun p => LinearMap.ext fun x => evMap_equivariant ρ σ p x`.
-/
theorem exists_extTensor_equiv (hG : HasCOBasis G) (hH : HasCOBasis H) (ρ : Representation ℂ (G × H) V)
    (ha : IsAdmissible ρ) (hi : ρ.IsIrreducible) :
    ∃ (σ : IrrRep G) (μ : IrrRep H), IsAdmissible μ.ρ ∧ Nonempty ((extTensor σ.ρ μ.ρ).Equiv ρ) := by
  obtain ⟨K, S, u, hKo, hKc, huS, hu0, hfix, hSi, hfd⟩ := GlobalTheory.CompanionTheory.ProdSub.exists_irreducible_sub_inl hG hH ρ ha hi
  let σ := S.toRepresentation
  let u' : S.toSubmodule := ⟨u, huS⟩
  have hu' : u' ≠ 0 := fun h => hu0 (congrArg Subtype.val h)
  have hfix' : ∀ x ∈ K, σ x u' = u' := fun x hx => Subtype.ext (hfix x hx)
  have hmem : u' ∈ fixed σ K := fun x => by
    simpa using hfix' x x.2
  have hS := fun A hA => schur hSi K hmem hu' A hA
  have hm : S.toSubmodule.subtype ∈ homSp ρ σ := fun g s => rfl
  have h0 : S.toSubmodule.subtype ≠ 0 := fun h => hu0 (by
    have := congrArg (fun F : S.toSubmodule →ₗ[ℂ] V => F u') h
    exact this)
  have hb := evMap_bijective hi hSi hS hm h0
  have hsm : IsSmooth σ := fun v => by
    have : {g : G | σ g v = v} = (fun g : G => (g, (1 : H))) ⁻¹' {p : G × H | ρ p v.1 = v.1} := by
      ext g
      exact Subtype.ext_iff
    rw [this]
    exact (ha.1 _).preimage (by fun_prop)
  have hadm := isAdmissible_homRep ha hSi hKo hKc hu' hfix'
  refine ⟨⟨_, σ, hsm, hSi⟩, ⟨_, homRep ρ σ, hadm.1, homRep_irreducible hi hb hm h0⟩, hadm, ⟨?_⟩⟩
  exact .mk (LinearEquiv.ofBijective (evMap ρ σ) hb) fun p => LinearMap.ext fun x => evMap_equivariant ρ σ p x

end Top

section Family

def splitEquiv {s : ℕ} (Γ : Fin (s + 1) → Type) [∀ a, Group (Γ a)] [∀ a, TopologicalSpace (Γ a)] :
    (Γ 0 × ∀ a : Fin s, Γ a.succ) ≃ₜ* ∀ a, Γ a where
  toFun p := Fin.cons p.1 p.2
  invFun f := (f 0, fun a => f a.succ)
  left_inv p := by simp
  right_inv f := by
    funext a
    refine Fin.cases ?_ (fun b => ?_) a <;> simp
  map_mul' p q := by
    funext a
    refine Fin.cases ?_ (fun b => ?_) a <;> simp
  continuous_toFun := by
    refine continuous_pi fun a => ?_
    refine Fin.cases ?_ (fun b => ?_) a
    · exact continuous_fst
    · exact (continuous_apply b).comp continuous_snd
  continuous_invFun := by
    refine Continuous.prodMk (continuous_apply 0) (continuous_pi fun a => continuous_apply a.succ)

/- English proof (translation)
Introduce `U hU` and use `by rw [nhds_pi, Filter.mem_pi] at hU obtain ⟨I, -, t, ht, hsub⟩ := hU choose K hKo hKc hKt using fun a => hB a (t a) (ht a) refine ⟨Subgroup.pi Set.univ K, ?_, ?_, ?_⟩ · exact isOpen_set_pi Set.finite_univ fun a _ => hKo a · exact isCompact_univ_pi fun a => hKc a · exact fun x hx …`.
-/
theorem hasCOBasis_pi {ι : Type} [Finite ι] {Γ : ι → Type} [∀ a, Group (Γ a)] [∀ a, TopologicalSpace (Γ a)]
    (hB : ∀ a, HasCOBasis (Γ a)) : HasCOBasis (∀ a, Γ a) := fun U hU => by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hsub⟩ := hU
  choose K hKo hKc hKt using fun a => hB a (t a) (ht a)
  refine ⟨Subgroup.pi Set.univ K, ?_, ?_, ?_⟩
  · exact isOpen_set_pi Set.finite_univ fun a _ => hKo a
  · exact isCompact_univ_pi fun a => hKc a
  · exact fun x hx => hsub fun a _ => hKt a (hx a (Set.mem_univ a))

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Take `⟨e, he⟩` from `GlobalTheory.OneFunctional.exists_piTensor_succ_equiv_map s F`. Set `L : (⨂[ℂ] a, F a) ≃ₗ[ℂ] V` to `(e.symm.trans (TensorProduct.comm ℂ _ _)).trans ((TensorProduct.congr (LinearEquiv.refl ℂ (F 0)) E'.toLinearEquiv).trans E.toLinearEquiv)`. Establish `hL : ∀ (t : ⨂[ℂ] a : Fin s, F a.succ) (a : F 0), L (e (t ⊗ₜ a)) = E (a ⊗ₜ E' t)` using `fun t a => by`. Simplify using `[L]`. Both sides reduce to the same expression.

Use `⟨.mk L fun g => ?_⟩` and prove the remaining obligations. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩` from `e.surjective x`. Use `show L (piTensor π g (e y)) = ρ g (L (e y))`. Proceed by induction on `y with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul t a`. Establish `h1 : piTensor π g = PiTensorProduct.map fun a => π a (g a)` using `rfl`. Establish `h2 : (piTensor fun a : Fin s => π a.succ) (fun a => g a.succ) = PiTensorProduct.map fun a : Fin s => π a.succ (g a.succ)` using `rfl`.

Rewrite using `[h1, he, hL, hL, ← h2]`. Establish `h3 : E' ((piTensor fun a : Fin s => π a.succ) (fun a => g a.succ) t) = μ (fun a => g a.succ) (E' t)` using `E'.toIntertwiningMap.isIntertwining _ _ _ t`. Rewrite using `[h3]`. Establish `h4` using `E.toIntertwiningMap.isIntertwining _ _ ((splitEquiv Γ).symm g) (a ⊗ₜ E' t)`. Establish `h5 : (splitEquiv Γ).symm g = ((g 0, fun a : Fin s => g a.succ) : Γ 0 × ∀ a : Fin s, Γ a.succ)` using `rfl`.

Establish `h6 : (splitEquiv Γ) ((splitEquiv Γ).symm g) = g` using `(splitEquiv Γ).apply_symm_apply g`. Rewrite `h4` using `[h5, extTensor_tmul]`. Use `h4.trans ?_` and prove the remaining obligations. Use `show ρ ((splitEquiv Γ) ((g 0, fun a : Fin s => g a.succ) : Γ 0 × ∀ a : Fin s, Γ a.succ)) _ = _`. Rewrite using `[← h5, h6]`.

Both sides reduce to the same expression.
-/
theorem piTensor_succ_equiv {s : ℕ} (Γ : Fin (s + 1) → Type) [∀ a, Group (Γ a)]
    [∀ a, TopologicalSpace (Γ a)] (F : Fin (s + 1) → Type) [∀ a, AddCommGroup (F a)] [∀ a, Module ℂ (F a)]
    (π : ∀ a, Representation ℂ (Γ a) (F a)) (ρ : Representation ℂ (∀ a, Γ a) V) {Y : Type} [AddCommGroup Y]
    [Module ℂ Y] (μ : Representation ℂ (∀ a : Fin s, Γ a.succ) Y)
    (E : (extTensor (π 0) μ).Equiv (ρ.comp (splitEquiv Γ).toMulEquiv.toMonoidHom))
    (E' : (piTensor fun a : Fin s => π a.succ).Equiv μ) : Nonempty ((piTensor π).Equiv ρ) := by
  obtain ⟨e, he⟩ := GlobalTheory.OneFunctional.exists_piTensor_succ_equiv_map s F
  let L : (⨂[ℂ] a, F a) ≃ₗ[ℂ] V :=
    (e.symm.trans (TensorProduct.comm ℂ _ _)).trans
      ((TensorProduct.congr (LinearEquiv.refl ℂ (F 0)) E'.toLinearEquiv).trans E.toLinearEquiv)
  have hL : ∀ (t : ⨂[ℂ] a : Fin s, F a.succ) (a : F 0), L (e (t ⊗ₜ a)) = E (a ⊗ₜ E' t) := fun t a => by
    simp [L]
    rfl
  refine ⟨.mk L fun g => ?_⟩
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ := e.surjective x
  show L (piTensor π g (e y)) = ρ g (L (e y))
  induction y with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul t a =>
    have h1 : piTensor π g = PiTensorProduct.map fun a => π a (g a) := rfl
    have h2 : (piTensor fun a : Fin s => π a.succ) (fun a => g a.succ) =
      PiTensorProduct.map fun a : Fin s => π a.succ (g a.succ) := rfl
    rw [h1, he, hL, hL, ← h2]
    have h3 : E' ((piTensor fun a : Fin s => π a.succ) (fun a => g a.succ) t) =
        μ (fun a => g a.succ) (E' t) :=
      E'.toIntertwiningMap.isIntertwining _ _ _ t
    rw [h3]
    have h4 := E.toIntertwiningMap.isIntertwining _ _ ((splitEquiv Γ).symm g) (a ⊗ₜ E' t)
    have h5 : (splitEquiv Γ).symm g = ((g 0, fun a : Fin s => g a.succ) : Γ 0 × ∀ a : Fin s, Γ a.succ) := rfl
    have h6 : (splitEquiv Γ) ((splitEquiv Γ).symm g) = g := (splitEquiv Γ).apply_symm_apply g
    rw [h5, extTensor_tmul] at h4
    refine h4.trans ?_
    show ρ ((splitEquiv Γ) ((g 0, fun a : Fin s => g a.succ) : Γ 0 × ∀ a : Fin s, Γ a.succ)) _ = _
    rw [← h5, h6]
    rfl

/- English proof (translation)
Introduce `s`. Proceed by induction on `s with`. Consider the case `zero`. Introduce `Γ _ _ _ _ V _ _ ρ _ hi`. Use `⟨fun a => a.elim0, ?_⟩` and prove the remaining obligations.

Use `haveI : Subsingleton (∀ a : Fin 0, Γ a) := inferInstance`. Take `⟨f⟩` from `exists_linearEquiv_of_subsingleton hi`. Establish `h1 : ∀ (g : ∀ a : Fin 0, Γ a) (v : V), ρ g v = v` using `fun g v => by`. Rewrite using `[Subsingleton.elim g 1, map_one]`. Both sides reduce to the same expression.

Set `L` to `(PiTensorProduct.isEmptyEquiv (R := ℂ) (Fin 0) (s := fun a : Fin 0 => ((a.elim0 : IrrRep (Γ a))).V)).trans f.symm`. Use `⟨.mk L fun g => LinearMap.ext fun x => ?_⟩` and prove the remaining obligations. Establish `h2 : piTensor (fun a : Fin 0 => ((a.elim0 : IrrRep (Γ a))).ρ) g = 1`. Rewrite using `[Subsingleton.elim g 1, map_one]`. Use `show L (piTensor _ g x) = ρ g (L x)`.

Rewrite using `[h2, h1]`. Both sides reduce to the same expression. Consider the case `succ s ih`. Introduce `Γ _ _ _ hB V _ _ ρ ha hi`. Establish `hPi : HasCOBasis (∀ a : Fin s, Γ a.succ)` using `hasCOBasis_pi fun a => hB a.succ`.

Take `⟨σ₀, μ, hμ, ⟨E⟩⟩` from `exists_extTensor_equiv (hB 0) hPi (ρ.comp (splitEquiv Γ).toMulEquiv.toMonoidHom) (GlobalTheory.CuspMult.isAdmissible_comp_equiv ρ _ ha) (GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv ρ _ hi)`. Take `⟨σs, ⟨E'⟩⟩` from `ih (fun a => Γ a.succ) (fun a => hB a.succ) μ.ρ hμ μ.irr`. Use `⟨Fin.cons (α := fun a => IrrRep (Γ a)) σ₀ σs, ?_⟩` and prove the remaining obligations. Conclude with `piTensor_succ_equiv Γ (fun a => (Fin.cons (α := fun a => IrrRep (Γ a)) σ₀ σs a).V) (fun a => (Fin.cons (α := fun a => IrrRep (Γ a)) σ₀ σs a).ρ) ρ μ.ρ E E'`.
-/
theorem exists_piTensor_equiv : ∀ (s : ℕ) (Γ : Fin s → Type) [∀ a, Group (Γ a)] [∀ a, TopologicalSpace (Γ a)]
    [∀ a, IsTopologicalGroup (Γ a)], (∀ a, HasCOBasis (Γ a)) →
    ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (∀ a, Γ a) V), IsAdmissible ρ →
    ρ.IsIrreducible → ∃ σ : ∀ a, IrrRep (Γ a), Nonempty ((piTensor fun a => (σ a).ρ).Equiv ρ) := by
  intro s
  induction s with
  | zero =>
    intro Γ _ _ _ _ V _ _ ρ _ hi
    refine ⟨fun a => a.elim0, ?_⟩
    haveI : Subsingleton (∀ a : Fin 0, Γ a) := inferInstance
    obtain ⟨f⟩ := exists_linearEquiv_of_subsingleton hi
    have h1 : ∀ (g : ∀ a : Fin 0, Γ a) (v : V), ρ g v = v := fun g v => by
      rw [Subsingleton.elim g 1, map_one]; rfl
    let L := (PiTensorProduct.isEmptyEquiv (R := ℂ) (Fin 0)
      (s := fun a : Fin 0 => ((a.elim0 : IrrRep (Γ a))).V)).trans f.symm
    refine ⟨.mk L fun g => LinearMap.ext fun x => ?_⟩
    have h2 : piTensor (fun a : Fin 0 => ((a.elim0 : IrrRep (Γ a))).ρ) g = 1 := by
      rw [Subsingleton.elim g 1, map_one]
    show L (piTensor _ g x) = ρ g (L x)
    rw [h2, h1]
    rfl
  | succ s ih =>
    intro Γ _ _ _ hB V _ _ ρ ha hi
    have hPi : HasCOBasis (∀ a : Fin s, Γ a.succ) := hasCOBasis_pi fun a => hB a.succ
    obtain ⟨σ₀, μ, hμ, ⟨E⟩⟩ := exists_extTensor_equiv (hB 0) hPi
      (ρ.comp (splitEquiv Γ).toMulEquiv.toMonoidHom)
      (GlobalTheory.CuspMult.isAdmissible_comp_equiv ρ _ ha)
      (GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv ρ _ hi)
    obtain ⟨σs, ⟨E'⟩⟩ := ih (fun a => Γ a.succ) (fun a => hB a.succ) μ.ρ hμ μ.irr
    refine ⟨Fin.cons (α := fun a => IrrRep (Γ a)) σ₀ σs, ?_⟩
    exact piTensor_succ_equiv Γ (fun a => (Fin.cons (α := fun a => IrrRep (Γ a)) σ₀ σs a).V)
      (fun a => (Fin.cons (α := fun a => IrrRep (Γ a)) σ₀ σs a).ρ) ρ μ.ρ E E'

end Family

section Levi

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Introduce `U hU` and use `by obtain ⟨m, -, hm⟩ := (GroundTheory.Automorphic.GLnLocal.hasBasis_nhds_one k n).mem_iff.1 hU exact ⟨_, GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k n m, GroundTheory.Automorphic.GLnLocal.isCompact_congruenceSubgroup k n m, hm⟩`.
-/
theorem hasCOBasis_GL (n : ℕ) : HasCOBasis (GL (Fin n) k) := fun U hU => by
  obtain ⟨m, -, hm⟩ := (GroundTheory.Automorphic.GLnLocal.hasBasis_nhds_one k n).mem_iff.1 hU
  exact ⟨_, GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k n m,
    GroundTheory.Automorphic.GLnLocal.isCompact_congruenceSubgroup k n m, hm⟩

/- English proof (translation)
Establish `h1` using `GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k (Fin s) (Fin (∑ a, d a)) (fun a => Fin (d a)) (GlobalTheory.CompanionTheory.BZInd.stdE d) τ.V τ.ρ τ.smooth (hasFiniteLength_of_isIrreducible τ.irr)`. Establish `hs` using `isSmooth_parInd (GlobalTheory.CompanionTheory.BZInd.stdE d) τ.ρ`. Conclude with `GlobalTheory.CompanionTheory.LeviAdm.isAdmissible_of_parInd d τ.ρ τ.smooth (GlobalTheory.CompanionTheory.AdmFL.isAdmissible_of_hasFiniteLength _ hs h1 fun W _ _ σ hq hi => hA k _ W σ (hq.isSmooth hs) hi)`.
-/
theorem isAdmissible_levi (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {s : ℕ} (d : Fin s → ℕ)
    (τ : IrrRep (Levi k fun a => Fin (d a))) : IsAdmissible τ.ρ := by
  have h1 := GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k (Fin s) (Fin (∑ a, d a)) (fun a => Fin (d a))
    (GlobalTheory.CompanionTheory.BZInd.stdE d) τ.V τ.ρ τ.smooth (hasFiniteLength_of_isIrreducible τ.irr)
  have hs := isSmooth_parInd (GlobalTheory.CompanionTheory.BZInd.stdE d) τ.ρ
  exact GlobalTheory.CompanionTheory.LeviAdm.isAdmissible_of_parInd d τ.ρ τ.smooth (GlobalTheory.CompanionTheory.AdmFL.isAdmissible_of_hasFiniteLength _ hs h1 fun W _ _ σ hq hi =>
    hA k _ W σ (hq.isSmooth hs) hi)

/- English proof (translation)
Introduce `k _ _ _ _ hA s d τ`. Take `⟨σ, ⟨E⟩⟩` from `exists_piTensor_equiv s (fun a => GL (Fin (d a)) k) (fun a => hasCOBasis_GL _) τ.ρ (isAdmissible_levi hA d τ) τ.irr`. Use `⟨fun a => (σ a).cl, ⟨?_⟩⟩` and prove the remaining obligations. Establish `e : ∀ a, (σ a).ρ.Equiv (σ a).cl.rep.ρ` using `fun a => ((σ a).nonempty_equiv_rep.some).symm`. Conclude with `E.symm.trans (piTensorEquiv e)`.
-/
theorem nonempty_equiv_piTensor : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {s : ℕ} (d : Fin s → ℕ)
    (τ : IrrRep (Levi k fun a => Fin (d a))), ∃ σ : ∀ a, IrrCl (GL (Fin (d a)) k),
      Nonempty (τ.ρ.Equiv (piTensor fun a => (σ a).rep.ρ)) := by
  intro k _ _ _ _ hA s d τ
  obtain ⟨σ, ⟨E⟩⟩ := exists_piTensor_equiv s (fun a => GL (Fin (d a)) k) (fun a => hasCOBasis_GL _) τ.ρ
    (isAdmissible_levi hA d τ) τ.irr
  refine ⟨fun a => (σ a).cl, ⟨?_⟩⟩
  have e : ∀ a, (σ a).ρ.Equiv (σ a).cl.rep.ρ := fun a => ((σ a).nonempty_equiv_rep.some).symm
  exact E.symm.trans (piTensorEquiv e)

end Levi

end GlobalTheory.CompanionTheory.LeviTensor

end
