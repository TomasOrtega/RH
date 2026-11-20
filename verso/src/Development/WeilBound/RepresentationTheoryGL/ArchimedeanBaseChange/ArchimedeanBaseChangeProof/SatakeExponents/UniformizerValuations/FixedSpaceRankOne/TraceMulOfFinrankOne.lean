import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FixedSpaceRankOne.FinrankFixedEqOne

noncomputable section

open scoped Pointwise

namespace PositivityTheory.Rg.BcB.F.EigA

section Inv

variable {G : Type} [Group G]

/- English proof (translation)
Establish `hone : τ 1 = 1`. Establish `h` using `hmul 1 1`. Rewrite `h` using `[mul_one]`. Conclude with `(mul_eq_left.mp h.symm)`. Establish `hτinv : ∀ a, τ a⁻¹ = (τ a)⁻¹` using `fun a => by`.

Establish `h` using `hmul a a⁻¹`. Rewrite `h` using `[mul_inv_cancel, hone]`. Conclude with `eq_inv_of_mul_eq_one_left h.symm`. Set `σ : G → G` to `fun x => τ x⁻¹`. Establish `hσmul : ∀ a b, σ (a * b) = σ a * σ b`.

Introduce `a b`. Simplify using `only [σ, mul_inv_rev, hmul]`. Establish `hσσ : ∀ a, σ (σ a) = a`. Introduce `a`. Simplify using `only [σ, hτinv, inv_inv, hinv]`.

Establish `hσK : ∀ k ∈ K, σ k ∈ K` using `fun k hk => hK _ (K.inv_mem hk)`. Establish `hFτ : ∀ x, F (τ x) = F x` using `fun x => by`. Take `⟨k₁, h₁, k₂, h₂, e⟩` from `hdc x`. Rewrite using `[e, hF _ h₁ _ h₂]`. Establish `hFr : ∀ x, ∀ k ∈ K, F (x * k) = F x` using `fun x k hk => by`.

Simplify using `using hF 1 K.one_mem k hk x`. Set `s : G ⧸ K → G ⧸ K` to `fun q => ((σ q.out : G) : G ⧸ K)`. Establish `hs : ∀ q, s (s q) = q`. Introduce `q`. Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul K (σ q.out)`.

Use `show ((σ ((σ q.out : G) : G ⧸ K).out : G) : G ⧸ K) = q`. Rewrite using `[hk, hσmul, hσσ, QuotientGroup.mk_mul_of_mem _ (hσK _ k.2), QuotientGroup.out_eq']`. Set `e : G ⧸ K ≃ G ⧸ K` to `⟨s, s, hs, hs⟩`. Use `conv_rhs => rw [← finsum_comp_equiv e]`. Use `finsum_congr fun q => ?_` and prove the remaining obligations.

Use `show F (q.out)⁻¹ = F ((σ q.out : G) : G ⧸ K).out`. Rewrite using `[out_mk_inv K F hFr]`. Use `show F (q.out)⁻¹ = F (τ (q.out)⁻¹)`. Rewrite using `[hFτ]`.
-/
theorem finsum_inv_eq {K : Subgroup G} (τ : G → G) (hmul : ∀ a b, τ (a * b) = τ b * τ a) (hinv : ∀ a, τ (τ a) = a)
    (hdc : ∀ g : G, ∃ k₁ ∈ K, ∃ k₂ ∈ K, τ g = k₁ * g * k₂) (hK : ∀ k ∈ K, τ k ∈ K)
    {M : Type} [AddCommMonoid M] (F : G → M) (hF : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ x, F (k₁ * x * k₂) = F x) :
    ∑ᶠ q : G ⧸ K, F (q.out)⁻¹ = ∑ᶠ q : G ⧸ K, F q.out := by
  have hone : τ 1 = 1 := by
    have h := hmul 1 1
    rw [mul_one] at h
    exact (mul_eq_left.mp h.symm)
  have hτinv : ∀ a, τ a⁻¹ = (τ a)⁻¹ := fun a => by
    have h := hmul a a⁻¹
    rw [mul_inv_cancel, hone] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  let σ : G → G := fun x => τ x⁻¹
  have hσmul : ∀ a b, σ (a * b) = σ a * σ b := by
    intro a b
    simp only [σ, mul_inv_rev, hmul]
  have hσσ : ∀ a, σ (σ a) = a := by
    intro a
    simp only [σ, hτinv, inv_inv, hinv]
  have hσK : ∀ k ∈ K, σ k ∈ K := fun k hk => hK _ (K.inv_mem hk)
  have hFτ : ∀ x, F (τ x) = F x := fun x => by
    obtain ⟨k₁, h₁, k₂, h₂, e⟩ := hdc x
    rw [e, hF _ h₁ _ h₂]
  have hFr : ∀ x, ∀ k ∈ K, F (x * k) = F x := fun x k hk => by
    simpa using hF 1 K.one_mem k hk x
  let s : G ⧸ K → G ⧸ K := fun q => ((σ q.out : G) : G ⧸ K)
  have hs : ∀ q, s (s q) = q := by
    intro q
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (σ q.out)
    show ((σ ((σ q.out : G) : G ⧸ K).out : G) : G ⧸ K) = q
    rw [hk, hσmul, hσσ, QuotientGroup.mk_mul_of_mem _ (hσK _ k.2), QuotientGroup.out_eq']
  let e : G ⧸ K ≃ G ⧸ K := ⟨s, s, hs, hs⟩
  conv_rhs => rw [← finsum_comp_equiv e]
  refine finsum_congr fun q => ?_
  show F (q.out)⁻¹ = F ((σ q.out : G) : G ⧸ K).out
  rw [out_mk_inv K F hFr]
  show F (q.out)⁻¹ = F (τ (q.out)⁻¹)
  rw [hFτ]

end Inv

section Top

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/- English proof (translation)
Take `⟨s, hs⟩` from `hf.isCompact.elim_finite_subcover (fun x : tsupport f => (x : G) • (K : Set G)) (fun x => hK.smul _) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, ⟨1, K.one_mem, mul_one x⟩⟩)`. Use `(s.finite_toSet.image (fun i : tsupport f => ((i : G) : G ⧸ K))).subset ?_` and prove the remaining obligations. Introduce `q hq`. Establish `hx : q.out ∈ tsupport f` using `subset_tsupport _ hq`. Establish `h2` using `hs hx`.

Simplify using `only [Set.mem_iUnion] at h2`. Take `⟨i, hi, k, hk, hik⟩` from `h2`. Use `⟨i, hi, ?_⟩` and prove the remaining obligations. Use `show ((i : G) : G ⧸ K) = q`. Use `conv_rhs => rw [← QuotientGroup.out_eq' q]`.

Rewrite using `[← hik]`. Conclude with `(QuotientGroup.mk_mul_of_mem (i : G) hk).symm`.
-/
theorem finite_support_quot (K : Subgroup G) (hK : IsOpen (K : Set G)) {M : Type} [Zero M] [TopologicalSpace M]
    (f : G → M) (hf : HasCompactSupport f) : {q : G ⧸ K | f q.out ≠ 0}.Finite := by
  obtain ⟨s, hs⟩ := hf.isCompact.elim_finite_subcover (fun x : tsupport f => (x : G) • (K : Set G))
    (fun x => hK.smul _) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, ⟨1, K.one_mem, mul_one x⟩⟩)
  refine (s.finite_toSet.image (fun i : tsupport f => ((i : G) : G ⧸ K))).subset ?_
  intro q hq
  have hx : q.out ∈ tsupport f := subset_tsupport _ hq
  have h2 := hs hx
  simp only [Set.mem_iUnion] at h2
  obtain ⟨i, hi, k, hk, hik⟩ := h2
  refine ⟨i, hi, ?_⟩
  show ((i : G) : G ⧸ K) = q
  conv_rhs => rw [← QuotientGroup.out_eq' q]
  rw [← hik]
  exact (QuotientGroup.mk_mul_of_mem (i : G) hk).symm

end Top

section Line

variable {M : Type} [AddCommGroup M] [Module ℂ M]

/- English proof (translation)
Use `haveI : FiniteDimensional ℂ M := Module.finite_of_finrank_eq_succ h`. Set `b : Module.Basis (Fin 1) ℂ M` to `Module.finBasisOfFinrankEq ℂ M h`. Apply `b.ext` to reduce the goal to its premises. Introduce `i`. Establish `hi : i = 0` using `Subsingleton.elim _ _`.

Substitute `hi` using the available equality. Rewrite using `[LinearMap.trace_eq_matrix_trace ℂ b f, Matrix.trace_fin_one, LinearMap.toMatrix_apply, LinearMap.smul_apply, Module.End.one_apply]`. Use `conv_lhs => rw [← b.sum_repr (f (b 0))]`. Rewrite using `[Fin.sum_univ_one]`.
-/
theorem end_eq_trace_smul (h : Module.finrank ℂ M = 1) (f : Module.End ℂ M) : f = LinearMap.trace ℂ M f • 1 := by
  haveI : FiniteDimensional ℂ M := Module.finite_of_finrank_eq_succ h
  let b : Module.Basis (Fin 1) ℂ M := Module.finBasisOfFinrankEq ℂ M h
  apply b.ext
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  rw [LinearMap.trace_eq_matrix_trace ℂ b f, Matrix.trace_fin_one, LinearMap.toMatrix_apply,
    LinearMap.smul_apply, Module.End.one_apply]
  conv_lhs => rw [← b.sum_repr (f (b 0))]
  rw [Fin.sum_univ_one]

/- English proof (translation)
Use `haveI : FiniteDimensional ℂ M := Module.finite_of_finrank_eq_succ h`. Establish `hf` using `end_eq_trace_smul h f`. Establish `hg` using `end_eq_trace_smul h g`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hf, ← hg]`.

Use `_ = LinearMap.trace ℂ M f * LinearMap.trace ℂ M g := by`. Rewrite using `[smul_mul_smul_comm, one_mul, map_smul, LinearMap.trace_one, h, smul_eq_mul, Nat.cast_one, mul_one]`.
-/
theorem trace_mul_of_finrank_one (h : Module.finrank ℂ M = 1) (f g : Module.End ℂ M) :
    LinearMap.trace ℂ M (f * g) = LinearMap.trace ℂ M f * LinearMap.trace ℂ M g := by
  haveI : FiniteDimensional ℂ M := Module.finite_of_finrank_eq_succ h
  have hf := end_eq_trace_smul h f
  have hg := end_eq_trace_smul h g
  calc LinearMap.trace ℂ M (f * g)
      = LinearMap.trace ℂ M ((LinearMap.trace ℂ M f • 1) * (LinearMap.trace ℂ M g • 1)) := by
        rw [← hf, ← hg]
    _ = LinearMap.trace ℂ M f * LinearMap.trace ℂ M g := by
        rw [smul_mul_smul_comm, one_mul, map_smul, LinearMap.trace_one, h, smul_eq_mul, Nat.cast_one, mul_one]

end Line

end PositivityTheory.Rg.BcB.F.EigA

end
