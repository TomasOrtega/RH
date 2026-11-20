import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMapEqSelfOfInjectiveFiniteHopf

set_option autoImplicit false

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

/- English proof (translation)
Use `set K := kerIdeal ((G.mulP 1).comp (f.app 1)) with hK`. Set `x` to `Ideal.Quotient.mkₐ R K`. Establish `hx` using `(kerIdeal_le_ker_iff ((G.mulP 1).comp (f.app 1)) x).1 fun c hc => Ideal.Quotient.eq_zero_iff_mem.2 hc`. Set `y` to `x.comp (f.app 2 : H.A 2 →ₐ[R] G.A 2)`. Establish `hy : torsionIdeal R (H.A 2) p ≤ RingHom.ker y` using `(kerIdeal_le_ker_iff _ y).2 fun z => by`.

Establish `e : f.app 2 (mulBy R _ p z) = G.mulP 1 (f.app 1 (H.res 1 z))`. Rewrite using `[map_mulBy, ← PDivGroup.res_app, mulP_res]`. Use `hx (H.res 1 z)` as an intermediate fact. Rewrite `this` using `[CoalgHomClass.counit_comp_apply]`. Conclude with `(congrArg x e).trans this`.

Take `⟨b, rfl⟩` from `G.res_surjective 1 a`. Rewrite `ha` using `[← PDivGroup.res_app]`. Establish `hb : g.app 2 b ∈ torsionIdeal R (H.A 2) p`. Establish `: g.app 2 b ∈ torsionIdeal R (H.A 2) (p ^ 1)`. Rewrite using `[← H.ker_res 1]`.

Conclude with `ha`. Rewrite `this` using `[pow_one]`. Then use the resulting hypothesis. Establish `h1 : x (f.app 2 (g.app 2 b)) = 0` using `hy hb`. Establish `e2 : f.app 2 (g.app 2 b) = mulBy R _ p b`. Use `congrArg (fun φ : G ⟶ G => φ.app 2 b) hfg` as an intermediate fact.

Simplify using `only [comp_app, natCast_smul_id_app] at this`. Conclude with `this`. Rewrite `h1` using `[e2]`. Rewrite using `[mulP_res]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 h1`.
-/
theorem mulP_mem_kerIdeal_comp_of_app_eq_zero (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (G H : PDivGroup p R) (f : G ⟶ H) (g : H ⟶ G) (hfg : f ≫ g = (p : ℤ_[p]) • 𝟙 G)
    (a : G.A 1) (ha : g.app 1 a = 0) :
    G.mulP 1 a ∈ kerIdeal ((G.mulP 1).comp (f.app 1)) := by
  set K := kerIdeal ((G.mulP 1).comp (f.app 1)) with hK
  let x := Ideal.Quotient.mkₐ R K
  have hx := (kerIdeal_le_ker_iff ((G.mulP 1).comp (f.app 1)) x).1
    fun c hc => Ideal.Quotient.eq_zero_iff_mem.2 hc
  let y := x.comp (f.app 2 : H.A 2 →ₐ[R] G.A 2)
  have hy : torsionIdeal R (H.A 2) p ≤ RingHom.ker y :=
    (kerIdeal_le_ker_iff _ y).2 fun z => by
      have e : f.app 2 (mulBy R _ p z) = G.mulP 1 (f.app 1 (H.res 1 z)) := by
        rw [map_mulBy, ← PDivGroup.res_app, mulP_res]
      have := hx (H.res 1 z)
      rw [CoalgHomClass.counit_comp_apply] at this
      exact (congrArg x e).trans this
  obtain ⟨b, rfl⟩ := G.res_surjective 1 a
  rw [← PDivGroup.res_app] at ha
  have hb : g.app 2 b ∈ torsionIdeal R (H.A 2) p := by
    have : g.app 2 b ∈ torsionIdeal R (H.A 2) (p ^ 1) := by
      rw [← H.ker_res 1]
      exact ha
    rwa [pow_one] at this
  have h1 : x (f.app 2 (g.app 2 b)) = 0 := hy hb
  have e2 : f.app 2 (g.app 2 b) = mulBy R _ p b := by
    have := congrArg (fun φ : G ⟶ G => φ.app 2 b) hfg
    simp only [comp_app, natCast_smul_id_app] at this
    exact this
  rw [e2] at h1
  rw [mulP_res]
  exact Ideal.Quotient.eq_zero_iff_mem.1 h1

end GlobalTheory.PDivGroup

open GlobalTheory.PDivGroup in

/- English proof (translation)
Introduce `p _ K _ G H f g hfg _ a ha`. Establish `hmulP : Function.Injective (G.mulP 1)` using `fun a b e => by`. Use `CartierDual.eq_of_forall_apply (R := K) fun φ => ?_` and prove the remaining obligations. Take `⟨ψ, rfl⟩` from `G.dual_mulP_surjective 1 φ`. Express the relevant statement in the definitionally equal form `ψ.ofConv (G.mulP 1 a) = ψ.ofConv (G.mulP 1 b)`.

Rewrite using `[e]`. Establish `h1` using `mulP_mem_kerIdeal_comp_of_app_eq_zero p K G H f g hfg a ha`. Rewrite `h1` using `[kerIdeal_comp]`. Rewrite using `[← GlobalTheory.PDiv.comap_map_eq_self_of_hopf_injective K _ _ (G.mulP 1) hmulP (kerIdeal (f.app 1))]`. Conclude with `h1`.
-/
theorem GlobalTheory.PDivGroup.mem_kerIdeal_of_app_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K]
    (G H : PDivGroup p K) (f : G ⟶ H) (g : H ⟶ G), f ≫ g = (p : ℤ_[p]) • 𝟙 G →
    g ≫ f = (p : ℤ_[p]) • 𝟙 H → ∀ a : G.A 1, g.app 1 a = 0 → a ∈ kerIdeal (f.app 1) := by
  intro p _ K _ G H f g hfg _ a ha
  have hmulP : Function.Injective (G.mulP 1) := fun a b e => by
    refine CartierDual.eq_of_forall_apply (R := K) fun φ => ?_
    obtain ⟨ψ, rfl⟩ := G.dual_mulP_surjective 1 φ
    change ψ.ofConv (G.mulP 1 a) = ψ.ofConv (G.mulP 1 b)
    rw [e]
  have h1 := mulP_mem_kerIdeal_comp_of_app_eq_zero p K G H f g hfg a ha
  rw [kerIdeal_comp] at h1
  rw [← GlobalTheory.PDiv.comap_map_eq_self_of_hopf_injective K _ _ (G.mulP 1) hmulP (kerIdeal (f.app 1))]
  exact h1
