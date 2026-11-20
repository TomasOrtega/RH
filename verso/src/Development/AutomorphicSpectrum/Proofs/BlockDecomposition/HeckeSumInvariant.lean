import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff

namespace GlobalTheory.CompanionTheory.Hecke

/- English proof (translation)
Introduce `G V _ _ _ ρ K f hfin hbi v hv k hk`. Establish `hsupp : (Function.support fun q : G ⧸ K => f q.out • ρ q.out v).Finite`. Use `hfin.subset ?_` and prove the remaining obligations. Introduce `q hq h0`. Apply `hq` to reduce the goal to its premises.

Establish `h0' : f q.out = 0` using `h0`. Simplify using `[h0']`. Establish `hstep : ∀ q : G ⧸ K, ρ k (f q.out • ρ q.out v) = f (MulAction.toPerm k q).out • ρ (MulAction.toPerm k q).out v`. Introduce `q`. Establish `hmk : ((MulAction.toPerm k q : G ⧸ K).out : G ⧸ K) = ((k * q.out : G) : G ⧸ K)`.

Rewrite using `[QuotientGroup.out_eq', MulAction.toPerm_apply]`. Use `conv_lhs => rw [← QuotientGroup.out_eq' q]`. Both sides reduce to the same expression. Establish `hκ : (k * q.out)⁻¹ * (MulAction.toPerm k q : G ⧸ K).out ∈ K` using `QuotientGroup.eq.mp hmk.symm`. Take `⟨κ, hκK, hκ⟩ : ∃ κ ∈ K, (MulAction.toPerm k q : G ⧸ K).out = k * q.out * κ` from `⟨_, hκ, by group⟩`.

Rewrite using `[hκ, (hbi κ hκK _).2, (hbi k hk _).1, map_mul, map_mul, map_smul]`. Simplify using `[hv κ hκK]`. Establish `h1` using `(ρ k).toAddMonoidHom.map_finsum hsupp`. Establish `h2 : ρ k (∑ᶠ q : G ⧸ K, f q.out • ρ q.out v) = ∑ᶠ q : G ⧸ K, ρ k (f q.out • ρ q.out v)` using `h1`. Rewrite using `[h2, finsum_congr hstep]`.

Conclude with `finsum_comp_equiv (MulAction.toPerm k) (f := fun q : G ⧸ K => f q.out • ρ q.out v)`.
-/
theorem heckeSum_fixed :
    ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
      (K : Subgroup G) (f : G → ℂ), (Function.support fun q : G ⧸ K => f q.out).Finite →
      (∀ k ∈ K, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) → ∀ v : V, (∀ k ∈ K, ρ k v = v) →
      ∀ k ∈ K, ρ k (∑ᶠ q : G ⧸ K, f q.out • ρ q.out v) = ∑ᶠ q : G ⧸ K, f q.out • ρ q.out v := by
  intro G V _ _ _ ρ K f hfin hbi v hv k hk
  have hsupp : (Function.support fun q : G ⧸ K => f q.out • ρ q.out v).Finite := by
    refine hfin.subset ?_
    intro q hq h0
    apply hq
    have h0' : f q.out = 0 := h0
    simp [h0']
  have hstep : ∀ q : G ⧸ K, ρ k (f q.out • ρ q.out v)
      = f (MulAction.toPerm k q).out • ρ (MulAction.toPerm k q).out v := by
    intro q
    have hmk : ((MulAction.toPerm k q : G ⧸ K).out : G ⧸ K) = ((k * q.out : G) : G ⧸ K) := by
      rw [QuotientGroup.out_eq', MulAction.toPerm_apply]
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have hκ : (k * q.out)⁻¹ * (MulAction.toPerm k q : G ⧸ K).out ∈ K :=
      QuotientGroup.eq.mp hmk.symm
    obtain ⟨κ, hκK, hκ⟩ : ∃ κ ∈ K, (MulAction.toPerm k q : G ⧸ K).out = k * q.out * κ :=
      ⟨_, hκ, by group⟩
    rw [hκ, (hbi κ hκK _).2, (hbi k hk _).1, map_mul, map_mul, map_smul]
    simp [hv κ hκK]
  have h1 := (ρ k).toAddMonoidHom.map_finsum hsupp
  have h2 : ρ k (∑ᶠ q : G ⧸ K, f q.out • ρ q.out v)
      = ∑ᶠ q : G ⧸ K, ρ k (f q.out • ρ q.out v) := h1
  rw [h2, finsum_congr hstep]
  exact finsum_comp_equiv (MulAction.toPerm k) (f := fun q : G ⧸ K => f q.out • ρ q.out v)

end GlobalTheory.CompanionTheory.Hecke
