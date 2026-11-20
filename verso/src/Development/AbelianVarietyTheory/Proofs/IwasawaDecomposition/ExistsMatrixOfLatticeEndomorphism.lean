import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Formalism.LocalToGlobal.ProjectiveLattices.FibreUniformisationLevelTwo
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

/- English proof (translation)
Introduce `E _ _ _ r X w`. Take `⟨t, hts, hspan, hli⟩` from `exists_linearIndependent E (X.Λ : Set (Fin r → E))`. Establish `htop : ⊤ ≤ Submodule.span E (Set.range ((↑) : t → Fin r → E))`. Rewrite using `[Subtype.range_coe, hspan, X.Λ_span]`. Set `bE : Module.Basis t E (Fin r → E)` to `Module.Basis.mk hli htop`.

Establish `hb : ∀ i : t, bE i = (i : Fin r → E)` using `fun i => by simp [bE]`. Set `wi : t → X.Λ` to `fun i => w ⟨(i : Fin r → E), hts i.2⟩`. Set `f : (Fin r → E) →ₗ[E] (Fin r → E)` to `bE.constr E (fun i => ((wi i : X.Λ) : Fin r → E))`. Use `⟨LinearMap.toMatrix' f, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.toMatrix'_mulVec]`.

Use `set c := bE.repr (v : Fin r → E) with hc`. Take `⟨d, hd⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E)) c.support (fun i => c i)`. Use `choose! a ha using hd`. Establish `hsum : ((d : 𝓞 E) • v : X.Λ) = ∑ i ∈ c.support, a i • (⟨(i : Fin r → E), hts i.2⟩ : X.Λ)`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `only [SetLike.val_smul, Submodule.coe_sum]`. Establish `hv : (v : Fin r → E) = ∑ i ∈ c.support, c i • bE i` using `by conv_lhs => rw [← bE.linearCombination_repr (v : Fin r → E)]`. Rewrite using `[Finsupp.linearCombination_apply, Finsupp.sum]`. Rewrite using `[hv, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations.

Rewrite using `[hb, ← algebraMap_smul E (a i), ha i hi, smul_assoc]`. Establish `key : (d : 𝓞 E) • f (v : Fin r → E) = (d : 𝓞 E) • ((w v : X.Λ) : Fin r → E)`. Establish `h1 : (d : 𝓞 E) • ((w v : X.Λ) : Fin r → E) = ((w ((d : 𝓞 E) • v) : X.Λ) : Fin r → E)`. Rewrite using `[map_smul]`. Both sides reduce to the same expression.

Establish `h2 : (d : 𝓞 E) • f (v : Fin r → E) = f (((d : 𝓞 E) • v : X.Λ) : Fin r → E)`. Rewrite using `[SetLike.val_smul, LinearMap.map_smul_of_tower]`. Rewrite using `[h1, h2, hsum, map_sum, Submodule.coe_sum, Submodule.coe_sum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, SetLike.val_smul, SetLike.val_smul, LinearMap.map_smul_of_tower]`.

Use `congr 1`. Use `bE.constr_basis E (fun i => ((wi i : X.Λ) : Fin r → E)) i` as an intermediate fact. Rewrite `this` using `[hb]`. Conclude with `this`. Establish `hd0 : (algebraMap (𝓞 E) E (d : 𝓞 E)) ≠ 0`.

Rewrite using `[ne_eq, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)]`. Conclude with `nonZeroDivisors.ne_zero d.2`. Rewrite `key` using `[← algebraMap_smul E (d : 𝓞 E), ← algebraMap_smul E (d : 𝓞 E) ((w v : X.Λ) : Fin r → E)]`. Conclude with `smul_right_injective _ hd0 key`.
-/
theorem GlobalTheory.FlagDomain.lattice_endo_matrix : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (w : X.Λ →ₗ[𝓞 E] X.Λ), ∃ W : Matrix (Fin r) (Fin r) E, ∀ v : X.Λ, W *ᵥ (v : Fin r → E) = (w v : Fin r → E) := by
  intro E _ _ _ r X w
  obtain ⟨t, hts, hspan, hli⟩ := exists_linearIndependent E (X.Λ : Set (Fin r → E))
  have htop : ⊤ ≤ Submodule.span E (Set.range ((↑) : t → Fin r → E)) := by
    rw [Subtype.range_coe, hspan, X.Λ_span]
  let bE : Module.Basis t E (Fin r → E) := Module.Basis.mk hli htop
  have hb : ∀ i : t, bE i = (i : Fin r → E) := fun i => by simp [bE]
  let wi : t → X.Λ := fun i => w ⟨(i : Fin r → E), hts i.2⟩
  let f : (Fin r → E) →ₗ[E] (Fin r → E) := bE.constr E (fun i => ((wi i : X.Λ) : Fin r → E))
  refine ⟨LinearMap.toMatrix' f, fun v => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  classical
  set c := bE.repr (v : Fin r → E) with hc
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E)) c.support (fun i => c i)
  choose! a ha using hd

  have hsum : ((d : 𝓞 E) • v : X.Λ) = ∑ i ∈ c.support, a i • (⟨(i : Fin r → E), hts i.2⟩ : X.Λ) := by
    apply Subtype.ext
    simp only [SetLike.val_smul, Submodule.coe_sum]
    have hv : (v : Fin r → E) = ∑ i ∈ c.support, c i • bE i := by
      conv_lhs => rw [← bE.linearCombination_repr (v : Fin r → E)]
      rw [Finsupp.linearCombination_apply, Finsupp.sum]
    rw [hv, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hb, ← algebraMap_smul E (a i), ha i hi, smul_assoc]
  have key : (d : 𝓞 E) • f (v : Fin r → E) = (d : 𝓞 E) • ((w v : X.Λ) : Fin r → E) := by
    have h1 : (d : 𝓞 E) • ((w v : X.Λ) : Fin r → E) = ((w ((d : 𝓞 E) • v) : X.Λ) : Fin r → E) := by
      rw [map_smul]; rfl
    have h2 : (d : 𝓞 E) • f (v : Fin r → E) = f (((d : 𝓞 E) • v : X.Λ) : Fin r → E) := by
      rw [SetLike.val_smul, LinearMap.map_smul_of_tower]
    rw [h1, h2, hsum, map_sum, Submodule.coe_sum, Submodule.coe_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, SetLike.val_smul, SetLike.val_smul, LinearMap.map_smul_of_tower]
    congr 1
    have := bE.constr_basis E (fun i => ((wi i : X.Λ) : Fin r → E)) i
    rw [hb] at this
    exact this
  have hd0 : (algebraMap (𝓞 E) E (d : 𝓞 E)) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)]
    exact nonZeroDivisors.ne_zero d.2
  rw [← algebraMap_smul E (d : 𝓞 E), ← algebraMap_smul E (d : 𝓞 E) ((w v : X.Λ) : Fin r → E)] at key
  exact smul_right_injective _ hd0 key
