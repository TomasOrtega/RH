import Mathlib
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
open Formalism.BasicNotions Formalism.L2 NumberField IsDedekindDomain Module

namespace GlobalTheory

/- English proof (translation)
Introduce `hli _ A U U' hUU'`. Use `set F := FractionRing O`. Set `p : V →ₗ[K] V` to `U.subtype ∘ₗ U.projectionOnto U' hUU'`. Establish `hpU : ∀ u ∈ U, p u = u` using `fun u hu => by`. Establish `h` using `Submodule.projectionOnto_apply_left hUU' ⟨u, hu⟩`.

Use `show ((U.projectionOnto U' hUU') ((⟨u, hu⟩ : U) : V) : V) = u`. Rewrite using `[h]`. Establish `hpU' : ∀ u ∈ U', p u = 0` using `fun u hu => by`. Establish `h` using `Submodule.projectionOnto_apply_right hUU' ⟨u, hu⟩`. Use `show ((U.projectionOnto U' hUU') ((⟨u, hu⟩ : U') : V) : V) = 0`.

Rewrite using `[h]`. Both sides reduce to the same expression. Establish `hpmem : ∀ v, p v ∈ U` using `fun v => by simp [p]`. Establish `hdec : ∀ v, ∃ u ∈ U, ∃ u' ∈ U', u + u' = v` using `fun v => by`. Establish `: v ∈ U ⊔ U'` using `by rw [hUU'.sup_eq_top]; trivial`.

Conclude with `Submodule.mem_sup.mp this`. Establish `hpdiff : ∀ v, p v - v ∈ U'` using `fun v => by`. Take `⟨u, hu, u', hu', rfl⟩` from `hdec v`. Rewrite using `[map_add, hpU u hu, hpU' u' hu', add_zero]`. Simplify using `using U'.neg_mem hu'`.

Set `W : Submodule F V'` to `Submodule.span F (Set.range fun a => iV (b a))`. Set `f : W →ₗ[F] V'` to `(Basis.span hli).constr F (fun a => iV (p (b a)))`. Take `⟨q, hq⟩` from `LinearMap.exists_extend f`. Establish `hqi : ∀ v, q (iV v) = iV (p v)`. Establish `: (q.comp iV : V →ₛₗ[e] V') = iV.comp p`.

Use `b.ext fun a => ?_` and prove the remaining obligations. Establish `hmem : iV (b a) ∈ W` using `Submodule.subset_span ⟨a, rfl⟩`. Establish `h1 : q (iV (b a)) = f ⟨iV (b a), hmem⟩`. Rewrite using `[← hq]`. Both sides reduce to the same expression.

Establish `h2 : (⟨iV (b a), hmem⟩ : W) = Basis.span hli a`. Rewrite using `[Basis.span_apply]`. Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[h1, h2, Basis.constr_basis]`. Introduce `v`.

Conclude with `congrArg (fun g => g v) this`. Establish `hqU : ∀ x ∈ Submodule.span F (iV '' (U : Set V)), q x = x`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨u, hu, rfl⟩` from `hy`. Rewrite using `[hqi, hpU u hu]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy]`. Consider the case `smul c x _ hx => rw [map_smul, hx]`.

Establish `hqU' : ∀ x ∈ Submodule.span F (iV '' (U' : Set V)), q x = 0`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨u, hu, rfl⟩` from `hy`.

Rewrite using `[hqi, hpU' u hu, map_zero]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]`. Consider the case `smul c x _ hx => rw [map_smul, hx, smul_zero]`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨w, hw, rfl⟩`. Simplify using `only [SetLike.mem_coe, Submodule.mem_inf, Submodule.restrictScalars_mem] at hw`. Take `⟨hwU, hwA⟩` from `hw`. Take `⟨a, ha, u', hu', rfl⟩` from `Submodule.mem_sup.mp hwA`.

Use `Submodule.mem_inf.mpr ⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `Submodule.subset_span ⟨_, hwU, rfl⟩`. Rewrite using `[map_add]`. Use `Submodule.add_mem_sup (Submodule.subset_span ⟨a, ha, rfl⟩) ?_` and prove the remaining obligations. Conclude with `Submodule.subset_span ⟨u', hu', rfl⟩`.

Introduce `x hx`. Take `⟨hxU, hxs⟩` from `Submodule.mem_inf.mp hx`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.mp hxs`. Establish `hxq : q (y + z) = y + z` using `hqU _ hxU`. Rewrite `hxq` using `[map_add, hqU' z hz, add_zero]`.

Rewrite using `[← hxq]`. Establish `hmap : q y ∈ Submodule.map (q.restrictScalars O) (Submodule.span O (iV '' (A : Set V)))` using `⟨y, hy, rfl⟩`. Rewrite `hmap` using `[Submodule.map_span]`. Use `Submodule.span_mono ?_ hmap` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨a, ha, rfl⟩, rfl⟩`.

Use `⟨p a, ?_, (hqi a).symm⟩` and prove the remaining obligations. Simplify using `only [SetLike.mem_coe, Submodule.mem_inf, Submodule.restrictScalars_mem]`. Use `⟨hpmem a, ?_⟩` and prove the remaining obligations. Establish `: p a = a + (p a - a)` using `by abel`. Rewrite using `[this]`.

Conclude with `Submodule.add_mem_sup ha (hpdiff a)`.
-/
theorem projection_span_extend_scalars
    (K : Type) [Field K] [NumberField K] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (e : K →+* FractionRing O) (V V' : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] [AddCommGroup V'] [Module (FractionRing O) V']
    [Module O V'] [IsScalarTower O (FractionRing O) V'] (iV : V →ₛₗ[e] V') (ι : Type) (b : Basis ι K V) :
    LinearIndependent (FractionRing O) (fun a => iV (b a)) →
    (∀ a : 𝓞 K, e (a : K) ∈ (algebraMap O (FractionRing O)).range) →
    ∀ (A : Submodule (𝓞 K) V) (U U' : Submodule K V), IsCompl U U' →
    Submodule.span O (iV '' ((U.restrictScalars (𝓞 K) ⊓ (A ⊔ U'.restrictScalars (𝓞 K)) :
        Submodule (𝓞 K) V) : Set V)) =
      (Submodule.span (FractionRing O) (iV '' (U : Set V))).restrictScalars O ⊓
        (Submodule.span O (iV '' (A : Set V)) ⊔
          (Submodule.span (FractionRing O) (iV '' (U' : Set V))).restrictScalars O) := by
  intro hli _ A U U' hUU'
  set F := FractionRing O

  let p : V →ₗ[K] V := U.subtype ∘ₗ U.projectionOnto U' hUU'
  have hpU : ∀ u ∈ U, p u = u := fun u hu => by
    have h := Submodule.projectionOnto_apply_left hUU' ⟨u, hu⟩
    show ((U.projectionOnto U' hUU') ((⟨u, hu⟩ : U) : V) : V) = u
    rw [h]
  have hpU' : ∀ u ∈ U', p u = 0 := fun u hu => by
    have h := Submodule.projectionOnto_apply_right hUU' ⟨u, hu⟩
    show ((U.projectionOnto U' hUU') ((⟨u, hu⟩ : U') : V) : V) = 0
    rw [h]; rfl
  have hpmem : ∀ v, p v ∈ U := fun v => by simp [p]
  have hdec : ∀ v, ∃ u ∈ U, ∃ u' ∈ U', u + u' = v := fun v => by
    have : v ∈ U ⊔ U' := by rw [hUU'.sup_eq_top]; trivial
    exact Submodule.mem_sup.mp this
  have hpdiff : ∀ v, p v - v ∈ U' := fun v => by
    obtain ⟨u, hu, u', hu', rfl⟩ := hdec v
    rw [map_add, hpU u hu, hpU' u' hu', add_zero]
    simpa using U'.neg_mem hu'

  let W : Submodule F V' := Submodule.span F (Set.range fun a => iV (b a))
  let f : W →ₗ[F] V' := (Basis.span hli).constr F (fun a => iV (p (b a)))
  obtain ⟨q, hq⟩ := LinearMap.exists_extend f
  have hqi : ∀ v, q (iV v) = iV (p v) := by
    have : (q.comp iV : V →ₛₗ[e] V') = iV.comp p := by
      refine b.ext fun a => ?_
      have hmem : iV (b a) ∈ W := Submodule.subset_span ⟨a, rfl⟩
      have h1 : q (iV (b a)) = f ⟨iV (b a), hmem⟩ := by
        rw [← hq]; rfl
      have h2 : (⟨iV (b a), hmem⟩ : W) = Basis.span hli a := by
        rw [Basis.span_apply]
      simp only [LinearMap.comp_apply]
      rw [h1, h2, Basis.constr_basis]
    intro v
    exact congrArg (fun g => g v) this
  have hqU : ∀ x ∈ Submodule.span F (iV '' (U : Set V)), q x = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, hu, rfl⟩ := hy
      rw [hqi, hpU u hu]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul c x _ hx => rw [map_smul, hx]
  have hqU' : ∀ x ∈ Submodule.span F (iV '' (U' : Set V)), q x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, hu, rfl⟩ := hy
      rw [hqi, hpU' u hu, map_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, hx, smul_zero]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_inf, Submodule.restrictScalars_mem] at hw
    obtain ⟨hwU, hwA⟩ := hw
    obtain ⟨a, ha, u', hu', rfl⟩ := Submodule.mem_sup.mp hwA
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · exact Submodule.subset_span ⟨_, hwU, rfl⟩
    · rw [map_add]
      refine Submodule.add_mem_sup (Submodule.subset_span ⟨a, ha, rfl⟩) ?_
      exact Submodule.subset_span ⟨u', hu', rfl⟩
  · intro x hx
    obtain ⟨hxU, hxs⟩ := Submodule.mem_inf.mp hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hxs
    have hxq : q (y + z) = y + z := hqU _ hxU
    rw [map_add, hqU' z hz, add_zero] at hxq
    rw [← hxq]
    have hmap : q y ∈ Submodule.map (q.restrictScalars O) (Submodule.span O (iV '' (A : Set V))) :=
      ⟨y, hy, rfl⟩
    rw [Submodule.map_span] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨p a, ?_, (hqi a).symm⟩
    simp only [SetLike.mem_coe, Submodule.mem_inf, Submodule.restrictScalars_mem]
    refine ⟨hpmem a, ?_⟩
    have : p a = a + (p a - a) := by abel
    rw [this]
    exact Submodule.add_mem_sup ha (hpdiff a)

end GlobalTheory
