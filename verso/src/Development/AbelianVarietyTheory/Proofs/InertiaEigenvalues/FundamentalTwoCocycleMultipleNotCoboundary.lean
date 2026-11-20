import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousTwoCocycleMultipleOfFundamental
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicCoboundaryOfDivisible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

namespace GlobalTheory.TateNat

/- English proof (translation)
Introduce `p _ O _ _ _ _ _ _ G _ _ χ c hgen φ ε hεφ ϖ hϖ hp hopen a f hf hd`. Establish `key : ∀ n : ℕ, a ∈ (powSub (M` using `O) ϖ n : Submodule O O) := by`. Introduce `n`. Use `set N : Submodule O O := powSub (M := O) ϖ n with hN`. Use `letI : Module ℤ_[p] (O ⧸ N) := Module.compHom (O ⧸ N) φ`.

Establish `hs : ∀ (t : ℤ_[p]) (x : O), t • (Submodule.Quotient.mk x : O ⧸ N) = Submodule.Quotient.mk (φ t * x)` using `fun t x => by show (φ t) • (Submodule.Quotient.mk x : O ⧸ N) = _`. Rewrite using `[← Submodule.Quotient.mk_smul, smul_eq_mul]`. Use `haveI : Finite (O ⧸ N) := AddSubgroup.quotient_finite_of_isOpen N.toAddSubgroup (hopen n)`. Establish `hM : ∀ m : O ⧸ N, (p : ℤ_[p]) ^ n • m = 0`. Introduce `m`.

Proceed by induction on `m using Submodule.Quotient.induction_on with`. Consider the case `H x`. Rewrite using `[hs, Submodule.Quotient.mk_eq_zero, map_pow, map_natCast]`. Rewrite `hp` using `[hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]`. Take `⟨u, hu⟩` from `hp`.

Use `mem_powSub.2 ⟨u ^ n * x, ?_⟩` and prove the remaining obligations. Rewrite using `[hu, smul_eq_mul, mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Establish `hlc : IsLocallyConstant (fun g => (Submodule.Quotient.mk (f g) : O ⧸ N))`. Introduce `s`.

Establish `ho : IsOpen ((Submodule.Quotient.mk : O → O ⧸ N) ⁻¹' s)`. Rewrite using `[isOpen_iff_forall_mem_open]`. Introduce `x hx`. Use `⟨(fun y => y - x) ⁻¹' (N : Set O), fun y hy => ?_, (hopen n).preimage (continuous_id.sub continuous_const), ?_⟩` and prove the remaining obligations. Establish `e : (Submodule.Quotient.mk y : O ⧸ N) = Submodule.Quotient.mk x` using `(Submodule.Quotient.eq N).2 hy show (Submodule.Quotient.mk y : O ⧸ N) ∈ s`.

Rewrite using `[e]`. Conclude with `hx`. Use `show x - x ∈ N`. Rewrite using `[sub_self]`. Conclude with `N.zero_mem`.

Conclude with `ho.preimage hf`. Establish `h3` using `((hgen n) (O ⧸ N) hM).2.2 (Submodule.Quotient.mk a) (fun g => Submodule.Quotient.mk (f g)) hlc fun q => by`. Take `⟨g, h⟩` from `q`. Establish `e` using `hd g h`. Simplify using `only [d1_apply] at e`.

Express the relevant statement in the definitionally equal form `(ε g : O) • f h - f (g * h) + f g = a * φ (c (g, h)) at e`. Rewrite `e` using `[smul_eq_mul, hεφ]`. Simplify using `only [GlobalTheory.TateTop.cob, hs]`. Rewrite using `[← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add]`. Use `congr 1`.

Take the linear combination `-e`. Conclude with `(Submodule.Quotient.mk_eq_zero N).1 h3`. Establish `hbot` using `Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal O) (IsLocalRing.maximalIdeal.isMaximal O).ne_top`. Establish `hmem : a ∈ ⨅ i, (IsLocalRing.maximalIdeal O) ^ i`. Use `Submodule.mem_iInf _ |>.2 fun i => ?_` and prove the remaining obligations.

Take `⟨y, hy⟩` from `mem_powSub.1 (key i)`. Rewrite using `[hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← hy, smul_eq_mul]`. Conclude with `dvd_mul_right _ _`. Rewrite `hmem` using `[hbot]`. Conclude with `(Submodule.mem_bot O).1 hmem`.
-/
theorem free_inj : ∀ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] {G : Type} [Group G] [TopologicalSpace G] (χ : G →* ℤ_[p]ˣ) (c : G × G → ℤ_[p]), (∀ r, GlobalTheory.TateTop.Gen χ r c) → ∀ (φ : ℤ_[p] →+* O) (ε : G →* Oˣ), (∀ g, ((ε g : Oˣ) : O) = φ (χ g : ℤ_[p])) → ∀ (ϖ : O), Irreducible ϖ → (p : O) ∈ IsLocalRing.maximalIdeal O → (∀ n : ℕ, IsOpen ((powSub (M := O) ϖ n : Submodule O O) : Set O)) → ∀ (a : O) (f : G → O), Continuous f → (∀ g h : G, d1 (twist ε O) f (g, h) = a * φ (c (g, h))) → a = 0 := by
  intro p _ O _ _ _ _ _ _ G _ _ χ c hgen φ ε hεφ ϖ hϖ hp hopen a f hf hd
  have key : ∀ n : ℕ, a ∈ (powSub (M := O) ϖ n : Submodule O O) := by
    intro n
    set N : Submodule O O := powSub (M := O) ϖ n with hN
    letI : Module ℤ_[p] (O ⧸ N) := Module.compHom (O ⧸ N) φ
    have hs : ∀ (t : ℤ_[p]) (x : O), t • (Submodule.Quotient.mk x : O ⧸ N) =
        Submodule.Quotient.mk (φ t * x) := fun t x => by
      show (φ t) • (Submodule.Quotient.mk x : O ⧸ N) = _
      rw [← Submodule.Quotient.mk_smul, smul_eq_mul]
    haveI : Finite (O ⧸ N) := AddSubgroup.quotient_finite_of_isOpen N.toAddSubgroup (hopen n)
    have hM : ∀ m : O ⧸ N, (p : ℤ_[p]) ^ n • m = 0 := by
      intro m
      induction m using Submodule.Quotient.induction_on with
      | H x =>
        rw [hs, Submodule.Quotient.mk_eq_zero, map_pow, map_natCast]
        rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hp
        obtain ⟨u, hu⟩ := hp
        refine mem_powSub.2 ⟨u ^ n * x, ?_⟩
        rw [hu, smul_eq_mul, mul_pow]
        ring
    have hlc : IsLocallyConstant (fun g => (Submodule.Quotient.mk (f g) : O ⧸ N)) := by
      intro s
      have ho : IsOpen ((Submodule.Quotient.mk : O → O ⧸ N) ⁻¹' s) := by
        rw [isOpen_iff_forall_mem_open]
        intro x hx
        refine ⟨(fun y => y - x) ⁻¹' (N : Set O), fun y hy => ?_,
          (hopen n).preimage (continuous_id.sub continuous_const), ?_⟩
        · have e : (Submodule.Quotient.mk y : O ⧸ N) = Submodule.Quotient.mk x :=
            (Submodule.Quotient.eq N).2 hy
          show (Submodule.Quotient.mk y : O ⧸ N) ∈ s
          rw [e]
          exact hx
        · show x - x ∈ N
          rw [sub_self]
          exact N.zero_mem
      exact ho.preimage hf
    have h3 := ((hgen n) (O ⧸ N) hM).2.2 (Submodule.Quotient.mk a)
      (fun g => Submodule.Quotient.mk (f g)) hlc fun q => by
        obtain ⟨g, h⟩ := q
        have e := hd g h
        simp only [d1_apply] at e
        change (ε g : O) • f h - f (g * h) + f g = a * φ (c (g, h)) at e
        rw [smul_eq_mul, hεφ] at e
        simp only [GlobalTheory.TateTop.cob, hs]
        rw [← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add]
        congr 1
        linear_combination -e
    exact (Submodule.Quotient.mk_eq_zero N).1 h3
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal O)
    (IsLocalRing.maximalIdeal.isMaximal O).ne_top
  have hmem : a ∈ ⨅ i, (IsLocalRing.maximalIdeal O) ^ i := by
    refine Submodule.mem_iInf _ |>.2 fun i => ?_
    obtain ⟨y, hy⟩ := mem_powSub.1 (key i)
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← hy, smul_eq_mul]
    exact dvd_mul_right _ _
  rw [hbot] at hmem
  exact (Submodule.mem_bot O).1 hmem

end GlobalTheory.TateNat
