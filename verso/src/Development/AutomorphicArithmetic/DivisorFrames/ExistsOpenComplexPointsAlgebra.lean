import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointsNonemptyDenseVariety
open NumberField CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section
open GlobalTheory.Cartier GlobalTheory.CxPts ReciprocityTheory.ChartRestriction.G.DVR.FlatBC

/- English proof (translation)
Take `⟨U, hU, a, rfl⟩` from `hf.exists_fnOf`. Take `⟨W, hW, b, rfl⟩` from `hg.exists_fnOf`. Establish `hy : y ∈ ptsIn q σ (U ⊓ W)` using `mem_ptsIn.2 ⟨hU, hW⟩`. Rewrite using `[← fnOf_resG (inf_le_left : U ⊓ W ≤ U) (gen_mem (memInf hU hW)), ← fnOf_resG (inf_le_right : U ⊓ W ≤ W) (gen_mem (memInf hU hW)), ← map_add, ratVal_fnOf hy, ratVal_fnOf hy, ratVal_fnOf hy, ev_add]`.
-/
private theorem ratVal_add' {k : Type} [CommRing k] {Z : Scheme.{0}} [AlgebraicGeometry.IsIntegral Z]
    {q : Z ⟶ Sp k} {σ : k →+* ℂ} {y : GlobalTheory.CxPts q σ} {f g : Z.functionField}
    (hf : RegAt (under y) f) (hg : RegAt (under y) g) :
    ratVal (f + g) y = ratVal f y + ratVal g y := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  obtain ⟨W, hW, b, rfl⟩ := hg.exists_fnOf
  have hy : y ∈ ptsIn q σ (U ⊓ W) := mem_ptsIn.2 ⟨hU, hW⟩
  rw [← fnOf_resG (inf_le_left : U ⊓ W ≤ U) (gen_mem (memInf hU hW)),
    ← fnOf_resG (inf_le_right : U ⊓ W ≤ W) (gen_mem (memInf hU hW)), ← map_add,
    ratVal_fnOf hy, ratVal_fnOf hy, ratVal_fnOf hy, ev_add]

/- English proof (translation)
Establish `hv : ∀ a : 𝓞 K, ratVal (ψ (algebraMap K Ω (a : K))) y = σ (a : K)` using `fun a => by`. Rewrite using `[hψ, ratVal_fnOf mem_ptsIn_top, ev_algX mem_ptsIn_top]`. Both sides reduce to the same expression. Establish `hr : ∀ a : 𝓞 K, RegAt (under y) (ψ (algebraMap K Ω (a : K)))` using `fun a => by`. Rewrite using `[hψ]`.

Conclude with `regAt_fnOf (TopologicalSpace.Opens.mem_top _) _ _`. Take `⟨n, d, hd, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 K) c`. Establish `hd0 : (d : K) ≠ 0`. Use `nonZeroDivisors.ne_zero hd` as an intermediate fact. Conclude with `this` after adjusting the coercions.

Establish `hs : σ (d : K) ≠ 0` using `(map_ne_zero σ).2 hd0`. Establish `hu : UnitAt (under y) (ψ (algebraMap K Ω (d : K)))`. Rewrite using `[hψ, unitAt_fnOf_iff (TopologicalSpace.Opens.mem_top _)]`. Use `mem_ptsIn.1 ((mem_ptsIn_basicOpen mem_ptsIn_top _).2 ?_)` and prove the remaining obligations. Rewrite using `[ev_algX mem_ptsIn_top]`.

Conclude with `hs`. Establish `hreg : RegAt (under y) (ψ (algebraMap K Ω ((n : K) / (d : K))))`. Rewrite using `[map_div₀, map_div₀, div_eq_mul_inv]`. Conclude with `(hr n).mul hu.inv.regAt`. Use `⟨hreg, ?_⟩` and prove the remaining obligations.

Establish `h` using `ratVal_mul hreg hu.regAt`. Rewrite `h` using `[← map_mul, ← map_mul, div_mul_cancel₀ _ hd0, hv, hv]`. Express the relevant statement in the definitionally equal form `ratVal (ψ (algebraMap K Ω ((n : K) / (d : K)))) y = σ ((n : K) / (d : K))`. Rewrite using `[map_div₀ σ, eq_div_iff hs]`. Conclude with `h.symm`.
-/
private theorem const_reg {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    {X : Scheme.{0}} [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (ψ : Ω →+* X.functionField)
    (hψ : ∀ a : 𝓞 K, ψ (algebraMap K Ω (a : K)) =
      fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p ⊤ a))
    (σ : K →+* ℂ) (y : GlobalTheory.CxPts p (σ.comp (algebraMap (𝓞 K) K))) (c : K) :
    RegAt (under y) (ψ (algebraMap K Ω c)) ∧ ratVal (ψ (algebraMap K Ω c)) y = σ c := by
  have hv : ∀ a : 𝓞 K, ratVal (ψ (algebraMap K Ω (a : K))) y = σ (a : K) := fun a => by
    rw [hψ, ratVal_fnOf mem_ptsIn_top, ev_algX mem_ptsIn_top]; rfl
  have hr : ∀ a : 𝓞 K, RegAt (under y) (ψ (algebraMap K Ω (a : K))) := fun a => by
    rw [hψ]; exact regAt_fnOf (TopologicalSpace.Opens.mem_top _) _ _
  obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) c
  have hd0 : (d : K) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hd
    exact_mod_cast this
  have hs : σ (d : K) ≠ 0 := (map_ne_zero σ).2 hd0
  have hu : UnitAt (under y) (ψ (algebraMap K Ω (d : K))) := by
    rw [hψ, unitAt_fnOf_iff (TopologicalSpace.Opens.mem_top _)]
    refine mem_ptsIn.1 ((mem_ptsIn_basicOpen mem_ptsIn_top _).2 ?_)
    rw [ev_algX mem_ptsIn_top]
    exact hs
  have hreg : RegAt (under y) (ψ (algebraMap K Ω ((n : K) / (d : K)))) := by
    rw [map_div₀, map_div₀, div_eq_mul_inv]
    exact (hr n).mul hu.inv.regAt
  refine ⟨hreg, ?_⟩
  have h := ratVal_mul hreg hu.regAt
  rw [← map_mul, ← map_mul, div_mul_cancel₀ _ hd0, hv, hv] at h
  change ratVal (ψ (algebraMap K Ω ((n : K) / (d : K)))) y = σ ((n : K) / (d : K))
  rw [map_div₀ σ, eq_div_iff hs]
  exact h.symm

end

open GlobalTheory.Cartier GlobalTheory.CxPts in
/- English proof (translation)
Introduce `K Ω _ _ _ _ X _ p ψ hψ R hR`. Take `⟨s, hs⟩` from `(Subalgebra.fg_iff_finiteType R).2 hR`. Use `choose U hU a ha using fun r : Ω => (regAt_genericPoint (ψ r)).exists_fnOf`. Establish `hmem : ∀ x : X, x ∈ s.inf U ↔ ∀ r ∈ s, x ∈ U r` using `fun x => by`. Rewrite using `[← SetLike.mem_coe, TopologicalSpace.Opens.coe_finset_inf, Finset.inf_set_eq_iInter]`.

Simplify using the standard rewrite rules. Use `⟨s.inf U, ⟨genericPoint X, (hmem _).2 fun r _ => hU r⟩, fun σ y hy => ?_⟩` and prove the remaining obligations. Establish `hreg : ∀ r ∈ R, RegAt (under y) (ψ r)`. Introduce `r hr`. Rewrite `hr` using `[← hs]`.

Proceed by induction on `hr using Algebra.adjoin_induction with`. Consider the case `mem r hr`. Rewrite using `[← ha r]`. Conclude with `regAt_fnOf ((hmem _).1 (mem_ptsIn.1 hy) r hr) _ _`. Consider the case `algebraMap c => exact (const_reg p ψ hψ σ y c).1`.

Consider the case `add r t _ _ h1 h2 => rw [map_add]`. Conclude with `h1.add h2`. Consider the case `mul r t _ _ h1 h2 => rw [map_mul]`. Conclude with `h1.mul h2`. Establish `hc` using `fun c => (const_reg p ψ hψ σ y c).2`.

Use `⟨{ toFun := fun r => ratVal (ψ r) y map_one' := ?_ map_mul' := fun r t => ?_ map_zero' := ?_ map_add' := fun r t => ?_ }, RingHom.ext fun c => hc c, fun r => ⟨hreg r r.2, rfl⟩⟩` and prove the remaining obligations. Simplify using `using hc 1`. Rewrite using `[Subalgebra.coe_mul, map_mul, ratVal_mul (hreg r r.2) (hreg t t.2)]`. Simplify using `using hc 0`. Rewrite using `[Subalgebra.coe_add, map_add, ratVal_add' (hreg r r.2) (hreg t t.2)]`.
-/
theorem UpperTheory.exists_open_complex_points_algebra :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (ψ : Ω →+* X.functionField), (∀ a : 𝓞 K, ψ (algebraMap K Ω (a : K)) = GlobalTheory.Cartier.fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤ a)) → ∀ (R : Subalgebra K Ω), Algebra.FiniteType K R → ∃ V : X.Opens, (V : Set X).Nonempty ∧ ∀ (σ : K →+* ℂ) (y : GlobalTheory.CxPts p (σ.comp (algebraMap (𝓞 K) K))), y ∈ GlobalTheory.CxPts.ptsIn p _ V → ∃ φ : R →+* ℂ, φ.comp (algebraMap K R) = σ ∧ ∀ a : R, GlobalTheory.Cartier.RegAt (GlobalTheory.Cartier.under y) (ψ a) ∧ GlobalTheory.Cartier.ratVal (ψ a) y = φ a := by
  intro K Ω _ _ _ _ X _ p ψ hψ R hR
  obtain ⟨s, hs⟩ := (Subalgebra.fg_iff_finiteType R).2 hR
  choose U hU a ha using fun r : Ω => (regAt_genericPoint (ψ r)).exists_fnOf
  have hmem : ∀ x : X, x ∈ s.inf U ↔ ∀ r ∈ s, x ∈ U r := fun x => by
    rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_finset_inf, Finset.inf_set_eq_iInter]
    simp
  refine ⟨s.inf U, ⟨genericPoint X, (hmem _).2 fun r _ => hU r⟩, fun σ y hy => ?_⟩
  have hreg : ∀ r ∈ R, RegAt (under y) (ψ r) := by
    intro r hr
    rw [← hs] at hr
    induction hr using Algebra.adjoin_induction with
    | mem r hr =>
      rw [← ha r]
      exact regAt_fnOf ((hmem _).1 (mem_ptsIn.1 hy) r hr) _ _
    | algebraMap c => exact (const_reg p ψ hψ σ y c).1
    | add r t _ _ h1 h2 => rw [map_add]; exact h1.add h2
    | mul r t _ _ h1 h2 => rw [map_mul]; exact h1.mul h2
  have hc := fun c => (const_reg p ψ hψ σ y c).2
  refine ⟨{ toFun := fun r => ratVal (ψ r) y
            map_one' := ?_
            map_mul' := fun r t => ?_
            map_zero' := ?_
            map_add' := fun r t => ?_ }, RingHom.ext fun c => hc c, fun r => ⟨hreg r r.2, rfl⟩⟩
  · simpa using hc 1
  · rw [Subalgebra.coe_mul, map_mul, ratVal_mul (hreg r r.2) (hreg t t.2)]
  · simpa using hc 0
  · rw [Subalgebra.coe_add, map_add, ratVal_add' (hreg r r.2) (hreg t t.2)]
