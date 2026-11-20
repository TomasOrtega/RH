import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartCompactStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartFiniteDimensionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartInvariantSubmoduleDenseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartPreservedByEquivariantStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.LowKScalar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Introduce `r hr`. Establish `htens : ∀ ψ : (κ → R) → ℂ, tens ev (c • ψ) r = c • tens ev ψ r`. Introduce `ψ`. Use function extensionality and compare the values at `x`. Simplify using `[tens, mul_assoc]`.

Distinguish the cases in `hc : c = 0`. Substitute `hc` using the available equality. Establish `h0 : ∀ ψ : (κ → R) → ℂ, tens ev ((0 : ℂ) • ψ) r = 0`. Introduce `ψ`. Rewrite using `[htens, zero_smul]`.

Rewrite using `[h0, h0, map_zero]`. Establish `hr' : Rest ev φ r`. Use `⟨hr.1, ?_⟩` and prove the remaining obligations. Establish `h2` using `(schA F κ).smul_mem c⁻¹ hr.2`. Rewrite `h2` using `[htens, smul_smul, inv_mul_cancel₀ hc, one_smul]`. Then use the resulting hypothesis.

Rewrite using `[htens, htens, map_smul, h r hr']`.
-/
theorem acts_smul {R κ : Type} [Zero R] [Fintype κ] (ev : AF F → R)
    (A : Module.End ℂ ((κ → AF F) → ℂ)) {φ φ₁ : (κ → R) → ℂ} (h : Acts ev A φ φ₁) (c : ℂ) :
    Acts ev A (c • φ) (c • φ₁) := by
  intro r hr
  have htens : ∀ ψ : (κ → R) → ℂ, tens ev (c • ψ) r = c • tens ev ψ r := by
    intro ψ; funext x; simp [tens, mul_assoc]
  by_cases hc : c = 0
  · subst hc
    have h0 : ∀ ψ : (κ → R) → ℂ, tens ev ((0 : ℂ) • ψ) r = 0 := by
      intro ψ; rw [htens, zero_smul]
    rw [h0, h0, map_zero]
  · have hr' : Rest ev φ r := by
      refine ⟨hr.1, ?_⟩
      have h2 := (schA F κ).smul_mem c⁻¹ hr.2
      rwa [htens, smul_smul, inv_mul_cancel₀ hc, one_smul] at h2
    rw [htens, htens, map_smul, h r hr']

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM T hT`. Use `set V := lowPartInf B G.M R.p with hVdef`. Use `haveI : FiniteDimensional ℂ V := GlobalTheory.T.lowPart_finite_dimensional hKP F E σ B a a' G X om om' R Rf hM`. Establish `hirr` using `GlobalTheory.T.lowPart_invariant_submodule_dense hKP F E σ B a a' G X om om' R Rf hM`. Establish `hmap` using `GlobalTheory.T.lowPart_preserved_by_equivariant hKP F E σ B a a' G X om om' R Rf hM T hT`.

Establish `hstab` using `(GlobalTheory.T.low_part_compact_stable hKP F E σ B a a' G X om om' R Rf hM).1`. Distinguish the cases in `hV : V = ⊥`. Use `⟨0, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[hV, Submodule.mem_bot]`. Simplify using `[hx]`.

Use `haveI : Nontrivial V := Submodule.nontrivial_iff_ne_bot.2 hV`. Take `⟨c, hc⟩` from `Module.End.exists_eigenvalue (T.restrict hmap)`. Take `⟨y, hy, hy0⟩` from `hc.exists_hasEigenvector`. Use `⟨c, ?_⟩` and prove the remaining obligations. Set `N : Submodule ℂ R.Pi` to `V ⊓ LinearMap.ker (T - c • LinearMap.id)`.

Establish `hmemN : ∀ x, x ∈ N ↔ x ∈ V ∧ T x = c • x`. Introduce `x`. Simplify using `only [N, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]`. Establish `hNst : ∀ k ∈ KInf σ G.W B.emb, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (1, k)) f f₁ → R.p f ∈ N → R.p f₁ ∈ N`. Introduce `k hk f hf f₁ hact hfN`.

Rewrite `hfN`, the goal using `[hmemN]`. Take `⟨hfV, hTf⟩` from `hfN`. Use `⟨hstab k hk f hf f₁ hact hfV, ?_⟩` and prove the remaining obligations. Establish `hact' : Acts (evI F) (om (1, k)) ⇑(c • f) ⇑(c • f₁)`. Establish `e1 : ∀ g : SInf F (Fin a × Fin (a + a')), ⇑(c • g) = c • ⇑g` using `fun g => by ext x; simp`.

Rewrite using `[e1, e1]`. Conclude with `acts_smul (evI F) (om (1, k)) hact c`. Use `hT k hk f hf f₁ hact hfV (c • f) ((G.M.Pol B.ψ B.emb).smul_mem c hf) (c • f₁) hact' (by rw [map_smul, hTf])` as an intermediate fact. Rewrite using `[this, map_smul]`. Establish `hNle : N ≤ V` using `inf_le_left`.

Break down `hirr N hNle hNst with hN | hN` into its components or cases. It suffices to derive a contradiction. Apply `hy0` to reduce the goal to its premises. Establish `hyN : (y : R.Pi) ∈ N`. Rewrite using `[hmemN]`.

Use `⟨y.2, ?_⟩` and prove the remaining obligations. Establish `h1 : T.restrict hmap y = c • y` using `Module.End.mem_eigenspace_iff.1 hy`. Establish `h2` using `congrArg Subtype.val h1`. Simplify using `using h2`. Rewrite `hyN` using `[hN, Submodule.mem_bot]`.

Conclude with `Subtype.ext hyN`. Introduce `x hx`. Establish `hx' : x ∈ N` using `by rw [hN]; exact hx`. Conclude with `((hmemN x).1 hx').2`.
-/
theorem lowPart_scalar_of_kEqOn : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
      ∀ T : R.Pi →ₗ[ℂ] R.Pi, KEqOn B G.M om R.p (lowPartInf B G.M R.p) T →
        ∃ c : ℂ, ∀ x ∈ lowPartInf B G.M R.p, T x = c • x := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM T hT
  set V := lowPartInf B G.M R.p with hVdef
  haveI : FiniteDimensional ℂ V := GlobalTheory.T.lowPart_finite_dimensional hKP F E σ B a a' G X om om' R Rf hM
  have hirr := GlobalTheory.T.lowPart_invariant_submodule_dense hKP F E σ B a a' G X om om' R Rf hM
  have hmap := GlobalTheory.T.lowPart_preserved_by_equivariant hKP F E σ B a a' G X om om' R Rf hM T hT
  have hstab := (GlobalTheory.T.low_part_compact_stable hKP F E σ B a a' G X om om' R Rf hM).1
  by_cases hV : V = ⊥
  · refine ⟨0, fun x hx => ?_⟩
    rw [hV, Submodule.mem_bot] at hx
    simp [hx]
  haveI : Nontrivial V := Submodule.nontrivial_iff_ne_bot.2 hV
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (T.restrict hmap)
  obtain ⟨y, hy, hy0⟩ := hc.exists_hasEigenvector
  refine ⟨c, ?_⟩
  let N : Submodule ℂ R.Pi := V ⊓ LinearMap.ker (T - c • LinearMap.id)
  have hmemN : ∀ x, x ∈ N ↔ x ∈ V ∧ T x = c • x := by
    intro x
    simp only [N, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero]
  have hNst : ∀ k ∈ KInf σ G.W B.emb, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + a')),
      Acts (evI F) (om (1, k)) f f₁ → R.p f ∈ N → R.p f₁ ∈ N := by
    intro k hk f hf f₁ hact hfN
    rw [hmemN] at hfN ⊢
    obtain ⟨hfV, hTf⟩ := hfN
    refine ⟨hstab k hk f hf f₁ hact hfV, ?_⟩
    have hact' : Acts (evI F) (om (1, k)) ⇑(c • f) ⇑(c • f₁) := by
      have e1 : ∀ g : SInf F (Fin a × Fin (a + a')), ⇑(c • g) = c • ⇑g := fun g => by ext x; simp
      rw [e1, e1]
      exact acts_smul (evI F) (om (1, k)) hact c
    have := hT k hk f hf f₁ hact hfV (c • f) ((G.M.Pol B.ψ B.emb).smul_mem c hf) (c • f₁) hact'
      (by rw [map_smul, hTf])
    rw [this, map_smul]
  have hNle : N ≤ V := inf_le_left
  rcases hirr N hNle hNst with hN | hN
  · exfalso
    apply hy0
    have hyN : (y : R.Pi) ∈ N := by
      rw [hmemN]
      refine ⟨y.2, ?_⟩
      have h1 : T.restrict hmap y = c • y := Module.End.mem_eigenspace_iff.1 hy
      have h2 := congrArg Subtype.val h1
      simpa using h2
    rw [hN, Submodule.mem_bot] at hyN
    exact Subtype.ext hyN
  · intro x hx
    have hx' : x ∈ N := by rw [hN]; exact hx
    exact ((hmemN x).1 hx').2

end GlobalTheory.LowKScalar
