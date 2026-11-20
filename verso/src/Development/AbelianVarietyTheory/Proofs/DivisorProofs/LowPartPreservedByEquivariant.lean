import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartCompactStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartFiniteDimensionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLinePolynomialEquivarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPolynomialTripleProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedKStableFiniteExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedLowPartKEquivariantStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.LowKInto

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[Submodule.disjoint_def]`. Introduce `x hxN hxA`. Take `⟨v, hv, c, hc, rfl⟩` from `Submodule.mem_sup.1 hxA`. Establish `hc' : c ∈ V ⊔ N`.

Establish `: c = (v + c) + (-v)` using `by abel`. Rewrite using `[this]`. Conclude with `Submodule.add_mem _ (Submodule.mem_sup_right hxN) (Submodule.neg_mem _ (Submodule.mem_sup_left hv))`. Establish `hc0 : c = 0` using `(Submodule.disjoint_def.1 hC.disjoint) c hc' hc`. Substitute `hc0` using the available equality.

Rewrite `hxN`, the goal using `[add_zero]`. Establish `: v ∈ V ⊓ N` using `⟨hv, hxN⟩`. Rewrite `this` using `[hVN]`. Conclude with `this`. Rewrite using `[codisjoint_iff]`.

Establish `h1` using `hC.sup_eq_top`. Rewrite using `[eq_top_iff, ← h1]`. Conclude with `sup_le (sup_le (le_sup_of_le_right le_sup_left) le_sup_left) (le_sup_of_le_right le_sup_right)`.
-/
theorem isCompl_of_disjoint {P : Type} [AddCommGroup P] [Module ℂ P] (V N C : Submodule ℂ P) (hVN : V ⊓ N = ⊥)
    (hC : IsCompl (V ⊔ N) C) : IsCompl N (V ⊔ C) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hxN hxA
    obtain ⟨v, hv, c, hc, rfl⟩ := Submodule.mem_sup.1 hxA
    have hc' : c ∈ V ⊔ N := by
      have : c = (v + c) + (-v) := by abel
      rw [this]
      exact Submodule.add_mem _ (Submodule.mem_sup_right hxN) (Submodule.neg_mem _ (Submodule.mem_sup_left hv))
    have hc0 : c = 0 := (Submodule.disjoint_def.1 hC.disjoint) c hc' hc
    subst hc0
    rw [add_zero] at hxN ⊢
    have : v ∈ V ⊓ N := ⟨hv, hxN⟩
    rw [hVN] at this
    exact this
  · rw [codisjoint_iff]
    have h1 := hC.sup_eq_top
    rw [eq_top_iff, ← h1]
    exact sup_le (sup_le (le_sup_of_le_right le_sup_left) le_sup_left) (le_sup_of_le_right le_sup_right)

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM T hT`. Use `set V := lowPartInf B G.M R.p with hVdef`. Use `haveI hfin : FiniteDimensional ℂ V := GlobalTheory.T.lowPart_finite_dimensional hKP F E σ B a a' G X om om' R Rf hM`. Establish `hstab` using `(GlobalTheory.T.low_part_compact_stable hKP F E σ B a a' G X om om' R Rf hM).1`. Establish `hact` using `(GlobalTheory.T.real_line_polynomial_equivariance hKP F E σ B a a' G X om om' hM.triple).2.2.2`.

Use `haveI : FiniteDimensional ℂ (V.map T) := Module.Finite.map V T`. Take `⟨N, hNst, hVN, hU⟩` from `GlobalTheory.T.matched_K_stable_finite_extension hKP F E σ B a a' G X om om' R Rf hM (V.map T) inferInstance`. Take `⟨C, hC⟩` from `Submodule.exists_isCompl (V ⊔ N)`. Establish `hc` using `isCompl_of_disjoint V N C hVN hC`. Set `π : R.Pi →ₗ[ℂ] R.Pi` to `N.subtype ∘ₗ Submodule.linearProjOfIsCompl N (V ⊔ C) hc`.

Establish `hπ : ∀ y ∈ V, ∀ n ∈ N, π (y + n) = n`. Introduce `y hy n hn`. Establish `h1 : Submodule.linearProjOfIsCompl N (V ⊔ C) hc y = 0` using `(Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc).2 (Submodule.mem_sup_left hy)`. Establish `h2 : Submodule.linearProjOfIsCompl N (V ⊔ C) hc n = ⟨n, hn⟩` using `Submodule.linearProjOfIsCompl_apply_left hc ⟨n, hn⟩`. Use `show N.subtype (Submodule.linearProjOfIsCompl N (V ⊔ C) hc (y + n)) = n`.

Rewrite using `[map_add, h1, h2, zero_add]`. Both sides reduce to the same expression. Establish `hTV : ∀ x ∈ V, T x ∈ V ⊔ N` using `fun x hx => hU (Submodule.mem_map_of_mem hx)`. Set `S : R.Pi →ₗ[ℂ] R.Pi` to `π ∘ₗ T`. Establish `hSN : ∀ x ∈ V, S x ∈ N` using `fun x _ => (Submodule.linearProjOfIsCompl N (V ⊔ C) hc (T x)).2`.

Establish `hS : KEqOn B G.M om R.p V S`. Introduce `k hk f hf f₁ hf₁ hfV g hg g₁ hg₁ hSf`. Take `⟨v, hv, n, hn, hvn⟩` from `Submodule.mem_sup.1 (hTV _ hfV)`. Establish `hng : n = R.p g`. Rewrite using `[← hSf]`.

Use `show n = π (T (R.p f))`. Rewrite using `[← hvn, hπ v hv n hn]`. Take `⟨fv, hfvD, rfl⟩` from `(Submodule.mem_map).1 hv`. Establish `hfvP : fv ∈ G.M.Pol B.ψ B.emb` using `fockDeg_le_pol G.M B.ψ B.emb _ hfvD`. Establish `hTtop : T (R.p f) ∈ (G.M.Pol B.ψ B.emb).map R.p`.

Rewrite using `[hM.real.quot.onto]`. Conclude with `Submodule.mem_top`. Take `⟨t, ht, hpt⟩` from `(Submodule.mem_map).1 hTtop`. Take `⟨t₁, -, ht₁, -⟩` from `hact k hk t ht`. Take `⟨fv₁, -, hfv₁, -⟩` from `hact k hk fv hfvP`.

Establish `hTf₁ : T (R.p f₁) = R.p t₁` using `hT k hk f hf f₁ hf₁ hfV t ht t₁ ht₁ hpt.symm`. Establish `hsum : R.p t = R.p fv + R.p g` using `by rw [hpt, ← hvn, hng]`. Establish `hsum₁` using `GlobalTheory.T.matched_polynomial_triple_product hKP F E σ B a a' G X om om' R Rf hM k hk t ht fv hfvP g hg t₁ fv₁ g₁ ht₁ hfv₁ hg₁ hsum`. Establish `hv₁ : R.p fv₁ ∈ V` using `hstab k hk fv hfvP fv₁ hfv₁ ⟨fv, hfvD, rfl⟩`. Establish `hg₁N : R.p g₁ ∈ N` using `hNst k hk g hg g₁ hg₁ (hng ▸ hn)`.

Use `show π (T (R.p f₁)) = R.p g₁`. Rewrite using `[hTf₁, hsum₁, hπ _ hv₁ _ hg₁N]`. Introduce `x hx`. Establish `h0` using `GlobalTheory.T.matched_low_part_K_equivariant hKP F E σ B a a' G X om om' R Rf hM S hS N hNst hVN hSN x hx`. Take `⟨v, hv, n, hn, hvn⟩` from `Submodule.mem_sup.1 (hTV x hx)`.

Establish `: n = 0`. Establish `e : S x = π (T x)` using `rfl`. Rewrite `h0` using `[e, ← hvn, hπ v hv n hn]`. Conclude with `h0`. Rewrite using `[← hvn, this, add_zero]`.

Conclude with `hv`.
-/
theorem lowPart_map_into : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
      ∀ T : R.Pi →ₗ[ℂ] R.Pi, KEqOn B G.M om R.p (lowPartInf B G.M R.p) T →
        ∀ x ∈ lowPartInf B G.M R.p, T x ∈ lowPartInf B G.M R.p := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM T hT
  set V := lowPartInf B G.M R.p with hVdef
  haveI hfin : FiniteDimensional ℂ V := GlobalTheory.T.lowPart_finite_dimensional hKP F E σ B a a' G X om om' R Rf hM
  have hstab := (GlobalTheory.T.low_part_compact_stable hKP F E σ B a a' G X om om' R Rf hM).1
  have hact := (GlobalTheory.T.real_line_polynomial_equivariance hKP F E σ B a a' G X om om' hM.triple).2.2.2
  haveI : FiniteDimensional ℂ (V.map T) := Module.Finite.map V T
  obtain ⟨N, hNst, hVN, hU⟩ := GlobalTheory.T.matched_K_stable_finite_extension hKP F E σ B a a' G X om om' R Rf hM (V.map T) inferInstance
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (V ⊔ N)
  have hc := isCompl_of_disjoint V N C hVN hC
  let π : R.Pi →ₗ[ℂ] R.Pi := N.subtype ∘ₗ Submodule.linearProjOfIsCompl N (V ⊔ C) hc
  have hπ : ∀ y ∈ V, ∀ n ∈ N, π (y + n) = n := by
    intro y hy n hn
    have h1 : Submodule.linearProjOfIsCompl N (V ⊔ C) hc y = 0 :=
      (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc).2 (Submodule.mem_sup_left hy)
    have h2 : Submodule.linearProjOfIsCompl N (V ⊔ C) hc n = ⟨n, hn⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hc ⟨n, hn⟩
    show N.subtype (Submodule.linearProjOfIsCompl N (V ⊔ C) hc (y + n)) = n
    rw [map_add, h1, h2, zero_add]
    rfl
  have hTV : ∀ x ∈ V, T x ∈ V ⊔ N := fun x hx => hU (Submodule.mem_map_of_mem hx)
  let S : R.Pi →ₗ[ℂ] R.Pi := π ∘ₗ T
  have hSN : ∀ x ∈ V, S x ∈ N := fun x _ => (Submodule.linearProjOfIsCompl N (V ⊔ C) hc (T x)).2
  have hS : KEqOn B G.M om R.p V S := by
    intro k hk f hf f₁ hf₁ hfV g hg g₁ hg₁ hSf
    obtain ⟨v, hv, n, hn, hvn⟩ := Submodule.mem_sup.1 (hTV _ hfV)
    have hng : n = R.p g := by
      rw [← hSf]
      show n = π (T (R.p f))
      rw [← hvn, hπ v hv n hn]
    obtain ⟨fv, hfvD, rfl⟩ := (Submodule.mem_map).1 hv
    have hfvP : fv ∈ G.M.Pol B.ψ B.emb := fockDeg_le_pol G.M B.ψ B.emb _ hfvD
    have hTtop : T (R.p f) ∈ (G.M.Pol B.ψ B.emb).map R.p := by
      rw [hM.real.quot.onto]; exact Submodule.mem_top
    obtain ⟨t, ht, hpt⟩ := (Submodule.mem_map).1 hTtop
    obtain ⟨t₁, -, ht₁, -⟩ := hact k hk t ht
    obtain ⟨fv₁, -, hfv₁, -⟩ := hact k hk fv hfvP
    have hTf₁ : T (R.p f₁) = R.p t₁ := hT k hk f hf f₁ hf₁ hfV t ht t₁ ht₁ hpt.symm
    have hsum : R.p t = R.p fv + R.p g := by rw [hpt, ← hvn, hng]
    have hsum₁ := GlobalTheory.T.matched_polynomial_triple_product hKP F E σ B a a' G X om om' R Rf hM k hk t ht fv hfvP g hg t₁ fv₁ g₁ ht₁ hfv₁ hg₁ hsum
    have hv₁ : R.p fv₁ ∈ V := hstab k hk fv hfvP fv₁ hfv₁ ⟨fv, hfvD, rfl⟩
    have hg₁N : R.p g₁ ∈ N := hNst k hk g hg g₁ hg₁ (hng ▸ hn)
    show π (T (R.p f₁)) = R.p g₁
    rw [hTf₁, hsum₁, hπ _ hv₁ _ hg₁N]
  intro x hx
  have h0 := GlobalTheory.T.matched_low_part_K_equivariant hKP F E σ B a a' G X om om' R Rf hM S hS N hNst hVN hSN x hx
  obtain ⟨v, hv, n, hn, hvn⟩ := Submodule.mem_sup.1 (hTV x hx)
  have : n = 0 := by
    have e : S x = π (T x) := rfl
    rw [e, ← hvn, hπ v hv n hn] at h0
    exact h0
  rw [← hvn, this, add_zero]
  exact hv

end GlobalTheory.LowKInto
