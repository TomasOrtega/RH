import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HostAdeleIso

/- English proof (translation)
Use `AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy` and prove the remaining obligations. Introduce and unpack `_ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩`. Use `AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `mul_mem (ha w) (hb w)`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul]`. Both sides reduce to the same expression. Introduce `x _`. Rewrite using `[zero_mul]`. Conclude with `zero_mem _`.

Introduce `x _`. Rewrite using `[mul_zero]`. Conclude with `zero_mem _`. Introduce `x y z _ _ _ h1 h2`. Rewrite using `[add_mul]`.

Conclude with `add_mem h1 h2`. Introduce `x y z _ _ _ h1 h2`. Rewrite using `[mul_add]`. Conclude with `add_mem h1 h2`. Introduce `x y _ _ h`.

Rewrite using `[neg_mul]`. Conclude with `neg_mem h`. Introduce `x y _ _ h`. Rewrite using `[mul_neg]`. Conclude with `neg_mem h`.
-/
theorem intAE_mul_mem (D : D7) {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D)
    (hy : y ∈ intAE D) : x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hy`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem r hr`. Take `⟨a, ha, x, rfl⟩` from `hr`.

Establish `e : Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (a ⊗ₜ[D.host.F] (x : D.host.E)) = ((x : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)) * ((1 : D.host.E) ⊗ₜ[D.host.F] a)`. Rewrite using `[Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Rewrite using `[e]`. Conclude with `mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, x, rfl⟩, rfl⟩)) (Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩))`. Consider the case `zero => rw [map_zero]`.

Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `add_mem ha hb`. Consider the case `neg a _ ha => rw [map_neg]`. Conclude with `neg_mem ha`.

Introduce `hw`. Set `c` to `(Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm`. Establish `key : ∀ z ∈ Formalism.L2.DIV.RInt D.host.F D.host.E, c z ∈ intAE D`. Introduce `z hz`. Proceed by induction on `hz using Subring.closure_induction with`.

Consider the case `mem r hr`. Break down `hr with ⟨⟨_, b, rfl⟩, rfl⟩ | ⟨⟨β, hβ⟩, rfl⟩` into its components or cases. Conclude with `AddSubgroup.subset_closure ⟨1, one_mem (Formalism.UG.intAd D.host.F), b, rfl⟩`. Conclude with `AddSubgroup.subset_closure ⟨β, hβ, 1, rfl⟩`. Consider the case `zero => rw [map_zero]`.

Conclude with `zero_mem _`. Consider the case `one`. Rewrite using `[map_one]`. Conclude with `AddSubgroup.subset_closure ⟨1, one_mem (Formalism.UG.intAd D.host.F), 1, rfl⟩`. Consider the case `add a b _ _ ha hb => rw [map_add]`.

Conclude with `add_mem ha hb`. Consider the case `neg a _ ha => rw [map_neg]`. Conclude with `neg_mem ha`. Consider the case `mul a b _ _ ha hb => rw [map_mul]`. Conclude with `intAE_mul_mem D ha hb`.

Use `key _ hw` as an intermediate fact. Rewrite `this` using `[show c (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E y) = y from (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm_apply_apply _]`. Then use the resulting hypothesis.
-/
theorem mem_intAE_iff_comm (D : D7) (y : Af D.host.F ⊗[D.host.F] D.host.E) :
    y ∈ intAE D ↔ Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E y ∈
      Formalism.L2.DIV.RInt D.host.F D.host.E := by
  constructor
  · intro hy
    induction hy using AddSubgroup.closure_induction with
    | mem r hr =>
      obtain ⟨a, ha, x, rfl⟩ := hr
      have e : Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E
          (a ⊗ₜ[D.host.F] (x : D.host.E)) =
          ((x : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)) * ((1 : D.host.E) ⊗ₜ[D.host.F] a) := by
        rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [e]
      exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, x, rfl⟩, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩))
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | neg a _ ha => rw [map_neg]; exact neg_mem ha
  · intro hw
    let c := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm
    have key : ∀ z ∈ Formalism.L2.DIV.RInt D.host.F D.host.E, c z ∈ intAE D := by
      intro z hz
      induction hz using Subring.closure_induction with
      | mem r hr =>
        rcases hr with ⟨⟨_, b, rfl⟩, rfl⟩ | ⟨⟨β, hβ⟩, rfl⟩
        · exact AddSubgroup.subset_closure ⟨1, one_mem (Formalism.UG.intAd D.host.F), b, rfl⟩
        · exact AddSubgroup.subset_closure ⟨β, hβ, 1, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | one =>
        rw [map_one]
        exact AddSubgroup.subset_closure ⟨1, one_mem (Formalism.UG.intAd D.host.F), 1, rfl⟩
      | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | neg a _ ha => rw [map_neg]; exact neg_mem ha
      | mul a b _ _ ha hb => rw [map_mul]; exact intAE_mul_mem D ha hb
    have := key _ hw
    rwa [show c (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E y) = y from
      (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm_apply_apply _] at this

/- English proof (translation)
Introduce `D`. Take `⟨ι, h1, h2, -, h4⟩` from `GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv D.host.F D.host.E`. Use `⟨(Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv.trans ι, fun x => h1 x, fun y => (mem_intAE_iff_comm D y).trans (h2 _), fun a k P n h => h4 a k P n h⟩` and prove the remaining obligations.
-/
theorem exists_finiteAdele_equiv : ∀ D : D7, ∃ ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E, (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x) ∧ (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) ∧ (∀ (a : Af D.host.F) (k : D.host.F) (P : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ), Valued.v (a (P.under (𝓞 D.host.F)) - algebraMap D.host.F _ k) ≤ WithZero.exp (-(n : ℤ)) → Valued.v (ι (a ⊗ₜ[D.host.F] (1 : D.host.E)) P - algebraMap D.host.E _ (algebraMap D.host.F D.host.E k)) ≤ WithZero.exp (-(n : ℤ))) := by
  intro D
  obtain ⟨ι, h1, h2, -, h4⟩ :=
    GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv D.host.F D.host.E
  refine ⟨(Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv.trans ι,
    fun x => h1 x, fun y => (mem_intAE_iff_comm D y).trans (h2 _), fun a k P n h => h4 a k P n h⟩

end GlobalTheory.HostAdeleIso
