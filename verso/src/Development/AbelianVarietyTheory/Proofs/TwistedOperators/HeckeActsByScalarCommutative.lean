import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeVecMemFixed

noncomputable section

namespace GlobalTheory.LFun.HeckeScalar

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.LFun.SatCompare

variable {G V M : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
  {ρ : Representation ℂ G V} {K : Subgroup G} {x : V}

def finOrbit (τ : Representation ℂ G M) (K : Subgroup G) : Submodule ℂ M where
  carrier := {m | (Set.range fun k : K => τ k m).Finite}
  zero_mem' := (Set.finite_singleton 0).subset (by rintro _ ⟨k, rfl⟩; simp)
  add_mem' {a b} ha hb := (Set.Finite.add ha hb).subset (by
    rintro _ ⟨k, rfl⟩
    exact ⟨_, ⟨k, rfl⟩, _, ⟨k, rfl⟩, by simp⟩)
  smul_mem' c a ha := (Set.Finite.image (c • ·) ha).subset (by
    rintro _ ⟨k, rfl⟩
    exact ⟨_, ⟨k, rfl⟩, by simp⟩)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(∀ k : L, τ k v = ((1 : L →* ℂˣ) k : ℂ) • v) ↔ _`. Simplify using the standard rewrite rules.
-/
private theorem mem_fixed_iff_twisted_operators {W : Type} [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ G W)
    (L : Subgroup G) (v : W) : v ∈ fixed τ L ↔ ∀ k : L, τ k v = v := by
  change (∀ k : L, τ k v = ((1 : L →* ℂˣ) k : ℂ) • v) ↔ _
  simp

/- English proof (translation)
Establish `hfin : (Set.range fun k : K => τ k m).Finite` using `hm`. Apply the tactic sequence `obtain ⟨O, hO⟩ : ∃ O : Finset M, ∀ o, o ∈ O ↔ ∃ k : K, τ k m = o := ⟨hfin.toFinset, fun o => by rw [Set.Finite.mem_toFinset]; try exact Iff.rfl⟩`. Establish `hmul : ∀ (a b : K) (o : M), τ (a : G) (τ (b : G) o) = τ ((a * b : K) : G) o`. Introduce `a b o`. Rewrite using `[Subgroup.coe_mul, map_mul, Module.End.mul_apply]`.

Establish `hperm : ∀ a : K, ∑ o ∈ O, τ (a : G) o = ∑ o ∈ O, o`. Introduce `a`. Use `Finset.sum_nbij' (fun o => τ (a : G) o) (fun o => τ ((a⁻¹ : K) : G) o) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `o ho`. Take `⟨k, rfl⟩` from `(hO o).1 ho`.

Conclude with `(hO _).2 ⟨a * k, (hmul a k m).symm⟩`. Introduce `o ho`. Take `⟨k, rfl⟩` from `(hO o).1 ho`. Conclude with `(hO _).2 ⟨a⁻¹ * k, (hmul a⁻¹ k m).symm⟩`. Introduce `o _ show τ ((a⁻¹ : K) : G) (τ (a : G) o) = o`.

Rewrite using `[hmul, inv_mul_cancel]`. Simplify using the standard rewrite rules. Introduce `o _ show τ (a : G) (τ ((a⁻¹ : K) : G) o) = o`. Rewrite using `[hmul, mul_inv_cancel]`. Simplify using the standard rewrite rules.

Introduce `o _`. Both sides reduce to the same expression. Establish `hne : (O.card : ℂ) ≠ 0`. Establish `hm' : m ∈ O` using `(hO m).2 ⟨1, by simp⟩`. Conclude with `Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem hm')`.

Use `⟨(O.card : ℂ)⁻¹ • ∑ o ∈ O, o, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_fixed_iff_twisted_operators]`. Introduce `a`. Rewrite using `[map_smul, map_sum, hperm a]`. Establish `hconst : ∀ o ∈ O, π o = π m`.

Introduce `o ho`. Take `⟨k, rfl⟩` from `(hO o).1 ho`. Rewrite using `[hπ]`. Conclude with `(mem_fixed_iff_twisted_operators ρ K (π m)).1 hy k`. Rewrite using `[map_smul, map_sum, Finset.sum_congr rfl hconst, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hne, one_smul]`.
-/
theorem exists_fixed_preimage {τ : Representation ℂ G M} (π : M →ₗ[ℂ] V) (hπ : ∀ g m, π (τ g m) = ρ g (π m))
    {m : M} (hm : m ∈ finOrbit τ K) (hy : π m ∈ fixed ρ K) : ∃ m' ∈ fixed τ K, π m' = π m := by
  classical

  have hfin : (Set.range fun k : K => τ k m).Finite := hm
  obtain ⟨O, hO⟩ : ∃ O : Finset M, ∀ o, o ∈ O ↔ ∃ k : K, τ k m = o :=
    ⟨hfin.toFinset, fun o => by rw [Set.Finite.mem_toFinset]; try exact Iff.rfl⟩
  have hmul : ∀ (a b : K) (o : M), τ (a : G) (τ (b : G) o) = τ ((a * b : K) : G) o := by
    intro a b o
    rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  have hperm : ∀ a : K, ∑ o ∈ O, τ (a : G) o = ∑ o ∈ O, o := by
    intro a
    refine Finset.sum_nbij' (fun o => τ (a : G) o) (fun o => τ ((a⁻¹ : K) : G) o) ?_ ?_ ?_ ?_ ?_
    · intro o ho
      obtain ⟨k, rfl⟩ := (hO o).1 ho
      exact (hO _).2 ⟨a * k, (hmul a k m).symm⟩
    · intro o ho
      obtain ⟨k, rfl⟩ := (hO o).1 ho
      exact (hO _).2 ⟨a⁻¹ * k, (hmul a⁻¹ k m).symm⟩
    · intro o _
      show τ ((a⁻¹ : K) : G) (τ (a : G) o) = o
      rw [hmul, inv_mul_cancel]
      simp
    · intro o _
      show τ (a : G) (τ ((a⁻¹ : K) : G) o) = o
      rw [hmul, mul_inv_cancel]
      simp
    · intro o _
      rfl
  have hne : (O.card : ℂ) ≠ 0 := by
    have hm' : m ∈ O := (hO m).2 ⟨1, by simp⟩
    exact Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem hm')
  refine ⟨(O.card : ℂ)⁻¹ • ∑ o ∈ O, o, ?_, ?_⟩
  · rw [mem_fixed_iff_twisted_operators]
    intro a
    rw [map_smul, map_sum, hperm a]
  · have hconst : ∀ o ∈ O, π o = π m := by
      intro o ho
      obtain ⟨k, rfl⟩ := (hO o).1 ho
      rw [hπ]
      exact (mem_fixed_iff_twisted_operators ρ K (π m)).1 hy k
    rw [map_smul, map_sum, Finset.sum_congr rfl hconst, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul, inv_mul_cancel₀ hne, one_smul]

def permRep (K : Subgroup G) : Representation ℂ G (G ⧸ K →₀ ℂ) where
  toFun g := Finsupp.lmapDomain ℂ ℂ (g • ·)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_smul]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Finsupp.mapDomain (g • ·) (Finsupp.single c a) = _`. Conclude with `Finsupp.mapDomain_single`.
-/
theorem permRep_single (g : G) (c : G ⧸ K) (a : ℂ) :
    permRep K g (Finsupp.single c a) = Finsupp.single (g • c) a := by
  change Finsupp.mapDomain (g • ·) (Finsupp.single c a) = _
  exact Finsupp.mapDomain_single

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem permRep_apply_eq_mapDomain (g : G) (φ : G ⧸ K →₀ ℂ) :
    permRep K g φ = Finsupp.mapDomain (g • ·) φ :=
  rfl

/- English proof (translation)
Rewrite using `[permRep_apply_eq_mapDomain]`. Conclude with `Finsupp.mapDomain_apply (MulAction.injective g) φ c`.
-/
theorem permRep_apply (g : G) (φ : G ⧸ K →₀ ℂ) (c : G ⧸ K) : permRep K g φ (g • c) = φ c := by
  rw [permRep_apply_eq_mapDomain]
  exact Finsupp.mapDomain_apply (MulAction.injective g) φ c

/- English proof (translation)
Establish `hpi : (Set.pi Set.univ fun c : φ.support => MulAction.orbit K (c : G ⧸ K)).Finite`. Use `Set.Finite.pi fun c => ?_` and prove the remaining obligations. Take `⟨s, hs⟩` from `QuotientGroup.mk_surjective (c : G ⧸ K)`. Rewrite using `[← hs]`. Conclude with `Formalism.UG.P.orbit_coset_finite K hK s`.

Express the relevant statement in the definitionally equal form `(Set.range fun k : K => permRep K k φ).Finite`. Use `(hpi.image fun t => ∑ c : φ.support, Finsupp.single (t c) (φ c)).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Use `⟨fun c => k • (c : G ⧸ K), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.mem_univ_pi]`.

Introduce `c`. Conclude with `MulAction.mem_orbit _ k`. Use `show (∑ c : φ.support, Finsupp.single (k • (c : G ⧸ K)) (φ c)) = permRep K (k : G) φ`. Rewrite using `[permRep_apply_eq_mapDomain]`. Conclude with `Finset.sum_coe_sort φ.support fun a => Finsupp.single ((k : G) • a) (φ a)`.
-/
theorem mem_finOrbit (hK : IsCommensurated K) (φ : G ⧸ K →₀ ℂ) : φ ∈ finOrbit (permRep K) K := by
  classical

  have hpi : (Set.pi Set.univ fun c : φ.support => MulAction.orbit K (c : G ⧸ K)).Finite := by
    refine Set.Finite.pi fun c => ?_
    obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (c : G ⧸ K)
    rw [← hs]
    exact Formalism.UG.P.orbit_coset_finite K hK s
  change (Set.range fun k : K => permRep K k φ).Finite
  refine (hpi.image fun t => ∑ c : φ.support, Finsupp.single (t c) (φ c)).subset ?_
  rintro _ ⟨k, rfl⟩
  refine ⟨fun c => k • (c : G ⧸ K), ?_, ?_⟩
  · rw [Set.mem_univ_pi]
    intro c
    exact MulAction.mem_orbit _ k
  · show (∑ c : φ.support, Finsupp.single (k • (c : G ⧸ K)) (φ c)) = permRep K (k : G) φ
    rw [permRep_apply_eq_mapDomain]
    exact Finset.sum_coe_sort φ.support fun a => Finsupp.single ((k : G) • a) (φ a)

def orbitMap (ρ : Representation ℂ G V) (K : Subgroup G) (x : V) : (G ⧸ K →₀ ℂ) →ₗ[ℂ] V :=
  Finsupp.linearCombination ℂ fun c => ρ c.out x

/- English proof (translation)
Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul (s := K) g`. Simplify using `only [orbitMap, Finsupp.linearCombination_single]`. Rewrite using `[hk, map_mul, Module.End.mul_apply, (mem_fixed_iff_twisted_operators ρ K x).1 hx k]`.
-/
theorem orbitMap_single (hx : x ∈ fixed ρ K) (g : G) (a : ℂ) :
    orbitMap ρ K x (Finsupp.single (g : G ⧸ K) a) = a • ρ g x := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (s := K) g
  simp only [orbitMap, Finsupp.linearCombination_single]
  rw [hk, map_mul, Module.End.mul_apply, (mem_fixed_iff_twisted_operators ρ K x).1 hx k]

/- English proof (translation)
Proceed by induction on `φ using Finsupp.induction_linear with`. Consider the case `zero => simp only [map_zero]`. Consider the case `add φ₁ φ₂ h₁ h₂ => simp only [map_add, h₁, h₂]`. Consider the case `single c a`. Take `⟨h, rfl⟩` from `QuotientGroup.mk_surjective c`.

Rewrite using `[permRep_single, MulAction.Quotient.smul_mk, smul_eq_mul, orbitMap_single hx, orbitMap_single hx, map_smul, map_mul, Module.End.mul_apply]`.
-/
theorem orbitMap_permRep (hx : x ∈ fixed ρ K) (g : G) (φ : G ⧸ K →₀ ℂ) :
    orbitMap ρ K x (permRep K g φ) = ρ g (orbitMap ρ K x φ) := by
  induction φ using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add φ₁ φ₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | single c a =>
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective c
    rw [permRep_single, MulAction.Quotient.smul_mk, smul_eq_mul, orbitMap_single hx, orbitMap_single hx, map_smul,
      map_mul, Module.End.mul_apply]

/- English proof (translation)
Set `S : Subrepresentation ρ` to `⟨LinearMap.range (orbitMap ρ K x), by`. Introduce `g v hv`. Take `⟨φ, rfl⟩` from `LinearMap.mem_range.1 hv`. Conclude with `LinearMap.mem_range.2 ⟨permRep K g φ, orbitMap_permRep hx g φ⟩⟩`. Establish `hxS : x ∈ S.toSubmodule` using `by show x ∈ LinearMap.range (orbitMap ρ K x)`.

Use `LinearMap.mem_range.2 ⟨Finsupp.single ((1 : G) : G ⧸ K) 1, ?_⟩` and prove the remaining obligations. Rewrite using `[orbitMap_single hx, one_smul, map_one, Module.End.one_apply]`. Use `haveI : IsSimpleOrder (Subrepresentation ρ) := hρ`. Break down `eq_bot_or_eq_top S with h | h` into its components or cases. Rewrite `hxS` using `[h]`.

Conclude with `absurd ((Submodule.mem_bot ℂ).1 hxS) h0`. Introduce `y`. Establish `hy : y ∈ S.toSubmodule`. Rewrite using `[h]`. Conclude with `Submodule.mem_top`.

Conclude with `LinearMap.mem_range.1 hy`.
-/
theorem orbitMap_surjective (hρ : ρ.IsIrreducible) (hx : x ∈ fixed ρ K) (h0 : x ≠ 0) :
    Function.Surjective (orbitMap ρ K x) := by

  let S : Subrepresentation ρ := ⟨LinearMap.range (orbitMap ρ K x), by
    intro g v hv
    obtain ⟨φ, rfl⟩ := LinearMap.mem_range.1 hv
    exact LinearMap.mem_range.2 ⟨permRep K g φ, orbitMap_permRep hx g φ⟩⟩
  have hxS : x ∈ S.toSubmodule := by
    show x ∈ LinearMap.range (orbitMap ρ K x)
    refine LinearMap.mem_range.2 ⟨Finsupp.single ((1 : G) : G ⧸ K) 1, ?_⟩
    rw [orbitMap_single hx, one_smul, map_one, Module.End.one_apply]
  haveI : IsSimpleOrder (Subrepresentation ρ) := hρ
  rcases eq_bot_or_eq_top S with h | h
  · rw [h] at hxS
    exact absurd ((Submodule.mem_bot ℂ).1 hxS) h0
  · intro y
    have hy : y ∈ S.toSubmodule := by
      rw [h]
      exact Submodule.mem_top
    exact LinearMap.mem_range.1 hy

/- English proof (translation)
Take `⟨φ, hφ⟩` from `orbitMap_surjective hρ hx h0 y`. Take `⟨ψ, hψ, hψφ⟩` from `exists_fixed_preimage (orbitMap ρ K x) (fun g m => orbitMap_permRep hx g m) (mem_finOrbit hK φ) (by rw [hφ]; exact hy)`. Establish `hψ' : ∀ (a : K) (c : G ⧸ K), ψ ((a : G) • c) = ψ c`. Introduce `a c`. Establish `h1` using `(mem_fixed_iff_twisted_operators (permRep K) K ψ).1 hψ a`.

Combine the equalities or inequalities in the displayed calculation. Use `⟨fun g => ψ (g : G ⧸ K), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Formalism.UG.P.mem_hecke_iff]`. Unfold `Formalism.UG.IsBiInv Formalism.UG.FinDosetSupp`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Introduce `a b g show ψ (((a : G) * g * b : G) : G ⧸ K) = ψ (g : G ⧸ K)`. Establish `hab : (((a : G) * g * b : G) : G ⧸ K) = (a : G) • (g : G ⧸ K)`. Rewrite using `[MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]`. Establish `e : ((a : G) * g * b)⁻¹ * ((a : G) * g) = (b : G)⁻¹` using `by group`. Rewrite using `[e]`.

Conclude with `inv_mem b.2`. Rewrite using `[hab, hψ']`. Use `⟨ψ.support.image (fun c : G ⧸ K => c.out), fun g hg => ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul (s := K) g`. Use `⟨(g : G ⧸ K).out, Finset.mem_image_of_mem _ (Finsupp.mem_support_iff.2 hg), 1, k⁻¹, ?_⟩` and prove the remaining obligations.

Rewrite using `[hk]`. Simplify using the standard rewrite rules. Unfold `heckeVec`. Simplify using `only [QuotientGroup.out_eq']`. Rewrite using `[finsum_eq_sum_of_support_subset (s := ψ.support), ← hφ, ← hψφ]`.

Simplify using `only [orbitMap, Finsupp.linearCombination_apply, Finsupp.sum]`. Introduce `c hc`. Rewrite `hc` using `[Function.mem_support]`. Rewrite using `[Finset.mem_coe, Finsupp.mem_support_iff]`. Introduce `h`.

Conclude with `hc (by simp [h])`.
-/
theorem exists_heckeVec_eq (hK : IsCommensurated K) (hρ : ρ.IsIrreducible) (hx : x ∈ fixed ρ K) (h0 : x ≠ 0)
    {y : V} (hy : y ∈ fixed ρ K) : ∃ f ∈ Hecke ℂ K, heckeVec ρ K f x = y := by
  classical
  obtain ⟨φ, hφ⟩ := orbitMap_surjective hρ hx h0 y
  obtain ⟨ψ, hψ, hψφ⟩ := exists_fixed_preimage (orbitMap ρ K x) (fun g m => orbitMap_permRep hx g m)
    (mem_finOrbit hK φ) (by rw [hφ]; exact hy)

  have hψ' : ∀ (a : K) (c : G ⧸ K), ψ ((a : G) • c) = ψ c := by
    intro a c
    have h1 := (mem_fixed_iff_twisted_operators (permRep K) K ψ).1 hψ a
    calc ψ ((a : G) • c) = permRep K (a : G) ψ ((a : G) • c) := by rw [h1]
      _ = ψ c := permRep_apply _ _ _
  refine ⟨fun g => ψ (g : G ⧸ K), ?_, ?_⟩
  · rw [Formalism.UG.P.mem_hecke_iff]
    unfold Formalism.UG.IsBiInv Formalism.UG.FinDosetSupp
    refine ⟨?_, ?_⟩
    · intro a b g
      show ψ (((a : G) * g * b : G) : G ⧸ K) = ψ (g : G ⧸ K)
      have hab : (((a : G) * g * b : G) : G ⧸ K) = (a : G) • (g : G ⧸ K) := by
        rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
        have e : ((a : G) * g * b)⁻¹ * ((a : G) * g) = (b : G)⁻¹ := by group
        rw [e]
        exact inv_mem b.2
      rw [hab, hψ']
    · refine ⟨ψ.support.image (fun c : G ⧸ K => c.out), fun g hg => ?_⟩
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (s := K) g
      refine ⟨(g : G ⧸ K).out, Finset.mem_image_of_mem _ (Finsupp.mem_support_iff.2 hg), 1, k⁻¹, ?_⟩
      rw [hk]
      simp
  · unfold heckeVec
    simp only [QuotientGroup.out_eq']
    rw [finsum_eq_sum_of_support_subset (s := ψ.support), ← hφ, ← hψφ]
    · simp only [orbitMap, Finsupp.linearCombination_apply, Finsupp.sum]
    · intro c hc
      rw [Function.mem_support] at hc
      rw [Finset.mem_coe, Finsupp.mem_support_iff]
      intro h
      exact hc (by simp [h])

/- English proof (translation)
Introduce `h hh`. Distinguish the cases in `hz : ∃ v ∈ fixed ρ K, v ≠ 0`. Take `⟨v, hv, hv0⟩` from `hz`. Set `T : Module.End ℂ (fixed ρ K)` to `(heckeLin hK hh ρ).restrict (fun y hy => by`. Rewrite using `[heckeLin_apply]`.

Conclude with `heckeVec_mem_fixed hK hh hy)`. Use `haveI : Nontrivial (fixed ρ K) := ⟨⟨⟨v, hv⟩, 0, fun e => hv0 (congrArg Subtype.val e)⟩⟩`. Take `⟨c, hev⟩` from `Module.End.exists_eigenvalue T`. Take `⟨w, hw⟩` from `hev.exists_hasEigenvector`. Establish `hw0 : (w : V) ≠ 0` using `fun e => hw.2 (Subtype.ext e)`.

Establish `hTw : heckeVec ρ K h w = c • (w : V)`. Use `congrArg Subtype.val hw.apply_eq_smul` as an intermediate fact. Simplify `this` using `[T]`. Use `⟨c, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨f, hf, rfl⟩` from `exists_heckeVec_eq hK hρ w.2 hw0 hy`.

Rewrite using `[← heckeVec_conv hK hh hf w.2, hc h hh f hf, heckeVec_conv hK hf hh w.2, hTw, heckeVec_smul hK hf]`. Use `push_neg at hz`. Use `⟨0, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[hz y hy, zero_smul]`. Use `heckeVec_smul (ρ := ρ) hK hh (0 : ℂ) (0 : V)` as an intermediate fact.

Simplify using `using this`.
-/
theorem heckeVec_scalar (G : Type) [Group G] (K : Subgroup G) (hK : IsCommensurated K)
    (hc : ∀ f₁ ∈ Hecke ℂ K, ∀ f₂ ∈ Hecke ℂ K, conv K f₁ f₂ = conv K f₂ f₁) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : ρ.IsIrreducible) (hf : FiniteDimensional ℂ (fixed ρ K)) :
    ∀ h ∈ Hecke ℂ K, ∃ c : ℂ, ∀ x ∈ fixed ρ K, heckeVec ρ K h x = c • x := by
  intro h hh
  by_cases hz : ∃ v ∈ fixed ρ K, v ≠ 0
  · obtain ⟨v, hv, hv0⟩ := hz

    let T : Module.End ℂ (fixed ρ K) := (heckeLin hK hh ρ).restrict (fun y hy => by
      rw [heckeLin_apply]
      exact heckeVec_mem_fixed hK hh hy)
    haveI : Nontrivial (fixed ρ K) := ⟨⟨⟨v, hv⟩, 0, fun e => hv0 (congrArg Subtype.val e)⟩⟩
    obtain ⟨c, hev⟩ := Module.End.exists_eigenvalue T
    obtain ⟨w, hw⟩ := hev.exists_hasEigenvector
    have hw0 : (w : V) ≠ 0 := fun e => hw.2 (Subtype.ext e)
    have hTw : heckeVec ρ K h w = c • (w : V) := by
      have := congrArg Subtype.val hw.apply_eq_smul
      simpa [T] using this
    refine ⟨c, fun y hy => ?_⟩
    obtain ⟨f, hf, rfl⟩ := exists_heckeVec_eq hK hρ w.2 hw0 hy
    rw [← heckeVec_conv hK hh hf w.2, hc h hh f hf, heckeVec_conv hK hf hh w.2, hTw, heckeVec_smul hK hf]
  · push_neg at hz
    refine ⟨0, fun y hy => ?_⟩
    rw [hz y hy, zero_smul]
    have := heckeVec_smul (ρ := ρ) hK hh (0 : ℂ) (0 : V)
    simpa using this

end GlobalTheory.LFun.HeckeScalar

end
