import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothSmInd

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.TwAvgInd

open GlobalTheory.CompanionTheory.TwistedAverage

/- English proof (translation)
Use `haveI := finiteIndex_stabKer hρ hL θ hθ x`. Use `haveI : Finite (L ⧸ stabKer ρ L θ x) := Subgroup.finite_quotient_of_finiteIndex`. Use `letI := Fintype.ofFinite (L ⧸ stabKer ρ L θ x)`. Establish `hn : ((Fintype.card (L ⧸ stabKer ρ L θ x) : ℕ) : ℂ) ≠ 0`. Conclude with `Fintype.card_ne_zero` after adjusting the coercions.

Establish `hF : ∀ a b : L, (QuotientGroup.mk a : L ⧸ stabKer ρ L θ x) = QuotientGroup.mk b → twOrbit ρ L θ x a = twOrbit ρ L θ x b`. Introduce `a b h`. Establish `hm : a⁻¹ * b ∈ stabKer ρ L θ x` using `QuotientGroup.eq.1 h`. Use `twOrbit_mul_right ρ L θ x a _ hm` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_left]`.

Conclude with `this.symm`. Use `⟨L ⧸ stabKer ρ L θ x, inferInstance, Quotient.out, ((Fintype.card (L ⧸ stabKer ρ L θ x) : ℕ) : ℂ)⁻¹, ?_, ?_⟩` and prove the remaining obligations. Establish `e : x - ((Fintype.card (L ⧸ stabKer ρ L θ x) : ℕ) : ℂ)⁻¹ • ∑ q : L ⧸ stabKer ρ L θ x, twOrbit ρ L θ x (Quotient.out q) = ((Fintype.card (L ⧸ stabKer ρ L θ x) : ℕ) : ℂ)⁻¹ • ∑ q : L ⧸ stabKer ρ L θ x, (x - twOrbit ρ L θ x (Quotient.out q))`. Rewrite using `[Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hn, one_smul]`. Rewrite using `[e]`.

Use `Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => ?_)` and prove the remaining obligations. Establish `e2 : x - twOrbit ρ L θ x (Quotient.out q) = (-(((θ (Quotient.out q))⁻¹ : ℂˣ) : ℂ)) • (ρ ((Quotient.out q : L) : G) x - (θ (Quotient.out q) : ℂ) • x)`. Rewrite using `[twOrbit, smul_sub, smul_smul, neg_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, neg_smul, neg_smul, one_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[e2]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, rfl⟩)`. Introduce `l`. Establish `h1 : ∀ t : L, ρ (l : G) (twOrbit ρ L θ x t) = (θ l : ℂ) • twOrbit ρ L θ x (l * t)`. Introduce `t`. Establish `h0 : θ l * (θ (l * t))⁻¹ = (θ t)⁻¹`.

Rewrite using `[map_mul, mul_inv, mul_inv_cancel_left]`. Simplify using `only [twOrbit, map_smul, smul_smul]`. Rewrite using `[← Units.val_mul, h0, Subgroup.coe_mul, map_mul, Module.End.mul_apply]`. Establish `h2 : ∑ q : L ⧸ stabKer ρ L θ x, twOrbit ρ L θ x (l * Quotient.out q) = ∑ q : L ⧸ stabKer ρ L θ x, twOrbit ρ L θ x (Quotient.out q)`. Set `e : Equiv.Perm (L ⧸ stabKer ρ L θ x)` to `MulAction.toPerm l`.

Establish `h3 : ∀ q : L ⧸ stabKer ρ L θ x, twOrbit ρ L θ x (l * Quotient.out q) = twOrbit ρ L θ x (Quotient.out (e q))`. Introduce `q`. Use `hF _ _ ?_` and prove the remaining obligations. Rewrite using `[QuotientGroup.out_eq']`. Use `conv_rhs => rw [← QuotientGroup.out_eq' q]`.

Both sides reduce to the same expression. Rewrite using `[Finset.sum_congr rfl fun q _ => h3 q]`. Conclude with `Equiv.sum_comp e (fun q => twOrbit ρ L θ x (Quotient.out q))`. Rewrite using `[map_smul, map_sum, Finset.sum_congr rfl fun q _ => h1 _, ← Finset.smul_sum, h2, smul_comm]`.
-/
theorem exists_finite_average {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    {L : Subgroup G} (hL : IsCompact (L : Set G)) (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L))
    (x : V) :
    ∃ (ι : Type) (_ : Fintype ι) (r : ι → L) (c : ℂ),
      x - c • ∑ i, twOrbit ρ L θ x (r i) ∈ twKer ρ L θ ∧
      ∀ l : L, ρ (l : G) (c • ∑ i, twOrbit ρ L θ x (r i)) =
        (θ l : ℂ) • (c • ∑ i, twOrbit ρ L θ x (r i)) := by
  classical
  haveI := finiteIndex_stabKer hρ hL θ hθ x
  haveI : Finite (L ⧸ stabKer ρ L θ x) := Subgroup.finite_quotient_of_finiteIndex
  letI := Fintype.ofFinite (L ⧸ stabKer ρ L θ x)
  have hn : ((Fintype.card (L ⧸ stabKer ρ L θ x) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hF : ∀ a b : L, (QuotientGroup.mk a : L ⧸ stabKer ρ L θ x) = QuotientGroup.mk b →
      twOrbit ρ L θ x a = twOrbit ρ L θ x b := by
    intro a b h
    have hm : a⁻¹ * b ∈ stabKer ρ L θ x := QuotientGroup.eq.1 h
    have := twOrbit_mul_right ρ L θ x a _ hm
    rw [mul_inv_cancel_left] at this
    exact this.symm
  refine ⟨L ⧸ stabKer ρ L θ x, inferInstance, Quotient.out,
    ((Fintype.card (L ⧸ stabKer ρ L θ x) : ℕ) : ℂ)⁻¹, ?_, ?_⟩
  · have e : x - ((Fintype.card (L ⧸ stabKer ρ L θ x) : ℕ) : ℂ)⁻¹ •
          ∑ q : L ⧸ stabKer ρ L θ x, twOrbit ρ L θ x (Quotient.out q) =
        ((Fintype.card (L ⧸ stabKer ρ L θ x) : ℕ) : ℂ)⁻¹ •
          ∑ q : L ⧸ stabKer ρ L θ x, (x - twOrbit ρ L θ x (Quotient.out q)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, smul_sub,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hn, one_smul]
    rw [e]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => ?_)
    have e2 : x - twOrbit ρ L θ x (Quotient.out q) =
        (-(((θ (Quotient.out q))⁻¹ : ℂˣ) : ℂ)) •
          (ρ ((Quotient.out q : L) : G) x - (θ (Quotient.out q) : ℂ) • x) := by
      rw [twOrbit, smul_sub, smul_smul, neg_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        neg_smul, neg_smul, one_smul]
      abel
    rw [e2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, rfl⟩)
  · intro l
    have h1 : ∀ t : L, ρ (l : G) (twOrbit ρ L θ x t) = (θ l : ℂ) • twOrbit ρ L θ x (l * t) := by
      intro t
      have h0 : θ l * (θ (l * t))⁻¹ = (θ t)⁻¹ := by
        rw [map_mul, mul_inv, mul_inv_cancel_left]
      simp only [twOrbit, map_smul, smul_smul]
      rw [← Units.val_mul, h0, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
    have h2 : ∑ q : L ⧸ stabKer ρ L θ x, twOrbit ρ L θ x (l * Quotient.out q) =
        ∑ q : L ⧸ stabKer ρ L θ x, twOrbit ρ L θ x (Quotient.out q) := by
      let e : Equiv.Perm (L ⧸ stabKer ρ L θ x) := MulAction.toPerm l
      have h3 : ∀ q : L ⧸ stabKer ρ L θ x, twOrbit ρ L θ x (l * Quotient.out q) =
          twOrbit ρ L θ x (Quotient.out (e q)) := by
        intro q
        refine hF _ _ ?_
        rw [QuotientGroup.out_eq']
        conv_rhs => rw [← QuotientGroup.out_eq' q]
        rfl
      rw [Finset.sum_congr rfl fun q _ => h3 q]
      exact Equiv.sum_comp e (fun q => twOrbit ρ L θ x (Quotient.out q))
    rw [map_smul, map_sum, Finset.sum_congr rfl fun q _ => h1 _, ← Finset.smul_sum, h2,
      smul_comm]

def evalAt {G W : Type} [AddCommGroup W] [Module ℂ W] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (P : Subgroup G) (τ : Representation ℂ P W)
    (g : G) : smoothPart (ind P τ) →ₗ[ℂ] W :=
  (LinearMap.proj g) ∘ₗ (indSpace P τ).subtype ∘ₗ (smoothPart (ind P τ)).subtype

/- English proof (translation)
Take `⟨ι, _, r, c, h1, h2⟩` from `exists_finite_average (smInd P τ) (GlobalTheory.CompanionTheory.BZFun.isSmooth_smInd P τ) hL θ hθ f`. Use `⟨_, h1, ?_, ?_⟩` and prove the remaining obligations. Introduce `g hg`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Apply `hg` to reduce the goal to its premises. Establish `hz : ∀ i, evalAt P τ g (twOrbit (smInd P τ) L θ f (r i)) = 0`. Introduce `i`. Establish `: evalAt P τ g (smInd P τ ((r i : L) : G) f) = 0` using `hcon _ (r i).2`. Simplify using `only [twOrbit, map_smul, this, smul_zero]`.

Establish `: evalAt P τ g (c • ∑ i, twOrbit (smInd P τ) L θ f (r i)) = 0`. Rewrite using `[map_smul, map_sum, Finset.sum_eq_zero fun i _ => hz i, smul_zero]`. Conclude with `this`. Introduce `l g`. Establish `h3` using `congrArg (evalAt P τ g) (h2 l)`.

Rewrite `h3` using `[map_smul]`. Conclude with `h3`.
-/
theorem exists_twisted_average_smInd {G : Type} {W : Type} [AddCommGroup W] [Module ℂ W] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (P : Subgroup G) (τ : Representation ℂ P W)
    (L : Subgroup G) (hL : IsCompact (L : Set G)) (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L))
    (f : smoothPart (ind P τ)) :
    ∃ f' : smoothPart (ind P τ), f - f' ∈ twKer (smInd P τ) L θ ∧
      (∀ g, f'.1.1 g ≠ 0 → ∃ l ∈ L, f.1.1 (g * l) ≠ 0) ∧
      ∀ (l : L) (g : G), f'.1.1 (g * l) = (θ l : ℂ) • f'.1.1 g := by
  obtain ⟨ι, _, r, c, h1, h2⟩ :=
    exists_finite_average (smInd P τ) (GlobalTheory.CompanionTheory.BZFun.isSmooth_smInd P τ) hL θ hθ f
  refine ⟨_, h1, ?_, ?_⟩
  · intro g hg
    by_contra hcon
    push_neg at hcon
    apply hg
    have hz : ∀ i, evalAt P τ g (twOrbit (smInd P τ) L θ f (r i)) = 0 := by
      intro i
      have : evalAt P τ g (smInd P τ ((r i : L) : G) f) = 0 := hcon _ (r i).2
      simp only [twOrbit, map_smul, this, smul_zero]
    have : evalAt P τ g (c • ∑ i, twOrbit (smInd P τ) L θ f (r i)) = 0 := by
      rw [map_smul, map_sum, Finset.sum_eq_zero fun i _ => hz i, smul_zero]
    exact this
  · intro l g
    have h3 := congrArg (evalAt P τ g) (h2 l)
    rw [map_smul] at h3
    exact h3

end GlobalTheory.CompanionTheory.TwAvgInd
