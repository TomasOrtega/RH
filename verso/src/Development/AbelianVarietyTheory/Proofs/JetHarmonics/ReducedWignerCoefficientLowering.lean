import Mathlib
import Formalism.HermitianCurvature.CapelliDeterminantAndBranching
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Definitions.Jets.Imports
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LastComatrixRowInvertsDual
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumStarProjectionEigenspaceEqSelfOfEigenvaluesLi
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirEigenvalueDual
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorDualStandardRel

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

namespace GlobalTheory

/- English proof (translation)
Introduce `V _ _ _ n E Et Om β L l hH hE hEt hOm M v hv`. Use `set m : Fin (n + 1) → ℂ := shf β L with hm`. Establish `hcap : ∀ w v, qdet E w v = (∏ j, (w + m j)) • v` using `fun w v => hH.cap w v`. Establish `hrel` using `tensor_dual_standard_rel V n E Et Om hH.gl hE hEt hOm`. Take `⟨K, hK1, hK2⟩` from `lastComatrixRow_inverts_dual V n E Om m hH.gl hcap hOm`.

Establish `hinj : Function.Injective m`. Introduce `i j hij`. Establish `h1 : ((L i : ℤ) : ℂ) = ((L j : ℤ) : ℂ)`. Simplify `hij` using `[hm, shf]`. Conclude with `hH.anti.injective (by exact_mod_cast h1)`.

Set `ev : PiLp 2 (fun _ : Fin (n + 1) => V) →ₗ[ℂ] V` to `{ toFun := fun x => x (Fin.last n) map_add' := fun x y => by simp map_smul' := fun c x => by simp }`. Set `q : ℂ → ℂ` to `fun u => ∏ j, (u + shf β M j)`. Establish `hq : Continuous q`. Conclude with `continuous_finsetProd _ (fun j _ => continuous_id.add continuous_const)`. Establish `hKy : ∀ u, K u (PiLp.single 2 (Fin.last n) v) = q u • v`.

Introduce `u`. Rewrite using `[hK2]`. Conclude with `(mem_CapSp.mp hv) u`. Establish `hres` using `ev_starProjection_eigenspace_eq_residue (PiLp 2 (fun _ : Fin (n + 1) => V)) V (n + 1) m (n : ℂ) Om ev K q (PiLp.single 2 (Fin.last n) v) v l hinj hrel.2.2.1 (splitCasimir_eigenvalue_dual V n E Et Om m hH.gl hE hcap hEt hOm) (fun u x => hK1 u x) hq hKy`. Establish `hev : m l + (n : ℂ) = β + L l + (n : ℂ)` using `by simp [hm, shf]`.

Rewrite `hres` using `[hev]`. Express the relevant statement in the definitionally equal form `ev _ = _`. Rewrite using `[hres]`. Use `congr 1`. Simplify using `only [q, hm, shf, WigSh.wM]`.

Use `push_cast`. Use `congr 1`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `j _`. Expand and normalize the polynomial expressions, which then agree.

Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `j _`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem reducedWigner_lowering : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) - if c = b then y a else 0) → (∀ y a, Om y a = ∑ c, E a c (y c)) → ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA E) (shf β M) → (Module.End.eigenspace Om (β + L l + (n : ℂ))).starProjection (PiLp.single 2 (Fin.last n) v) (Fin.last n) = (GlobalTheory.WigSh.wM L M l : ℂ) • v := by
  intro V _ _ _ n E Et Om β L l hH hE hEt hOm M v hv
  set m : Fin (n + 1) → ℂ := shf β L with hm
  have hcap : ∀ w v, qdet E w v = (∏ j, (w + m j)) • v := fun w v => hH.cap w v
  have hrel := tensor_dual_standard_rel V n E Et Om hH.gl hE hEt hOm
  obtain ⟨K, hK1, hK2⟩ := lastComatrixRow_inverts_dual V n E Om m hH.gl hcap hOm
  have hinj : Function.Injective m := by
    intro i j hij
    have h1 : ((L i : ℤ) : ℂ) = ((L j : ℤ) : ℂ) := by
      simpa [hm, shf] using hij
    exact hH.anti.injective (by exact_mod_cast h1)
  let ev : PiLp 2 (fun _ : Fin (n + 1) => V) →ₗ[ℂ] V :=
    { toFun := fun x => x (Fin.last n)
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp }
  let q : ℂ → ℂ := fun u => ∏ j, (u + shf β M j)
  have hq : Continuous q := by
    exact continuous_finsetProd _ (fun j _ => continuous_id.add continuous_const)
  have hKy : ∀ u, K u (PiLp.single 2 (Fin.last n) v) = q u • v := by
    intro u
    rw [hK2]
    exact (mem_CapSp.mp hv) u
  have hres := ev_starProjection_eigenspace_eq_residue (PiLp 2 (fun _ : Fin (n + 1) => V)) V (n + 1)
    m (n : ℂ) Om ev K q (PiLp.single 2 (Fin.last n) v) v l hinj hrel.2.2.1
    (splitCasimir_eigenvalue_dual V n E Et Om m hH.gl hE hcap hEt hOm)
    (fun u x => hK1 u x) hq hKy
  have hev : m l + (n : ℂ) = β + L l + (n : ℂ) := by simp [hm, shf]
  rw [hev] at hres
  change ev _ = _
  rw [hres]
  congr 1
  simp only [q, hm, shf, WigSh.wM]
  push_cast
  congr 1
  · apply Finset.prod_congr rfl
    intro j _
    ring
  · apply Finset.prod_congr rfl
    intro j _
    ring

end GlobalTheory
