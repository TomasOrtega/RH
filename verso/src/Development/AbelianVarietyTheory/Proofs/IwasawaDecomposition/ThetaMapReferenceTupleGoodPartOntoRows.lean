import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

/- English proof (translation)
Unfold `kOf`. Establish `h : ∃ b : K, σ b = σ a` using `⟨a, rfl⟩`. Rewrite using `[dif_pos h]`. Conclude with `σ.injective h.choose_spec`.
-/
theorem kOf_apply_self_on {K : Type} [Field K] (σ : K →+* ℂ) (a : K) : kOf σ (σ a) = a := by
  unfold kOf
  have h : ∃ b : K, σ b = σ a := ⟨a, rfl⟩
  rw [dif_pos h]
  exact σ.injective h.choose_spec

/- English proof (translation)
Use extensionality with `i k`. Establish `h : ∃ y, f y = f (Pi.single k 1)` using `⟨_, rfl⟩`. Establish `: solve f (f (Pi.single k 1)) = Pi.single k 1`. Unfold `solve`. Rewrite using `[dif_pos h]`.

Conclude with `hf h.choose_spec`. Simplify using `only [relMat, Matrix.of_apply, this, Matrix.one_apply, Pi.single_apply]`.
-/
theorem relMat_self_on {E : Type} [AddCommGroup E] [Module ℂ E] {n : ℕ} (f : (Fin n → ℂ) →ₗ[ℂ] E)
    (hf : Function.Injective f) : relMat f f = 1 := by
  ext i k
  have h : ∃ y, f y = f (Pi.single k 1) := ⟨_, rfl⟩
  have : solve f (f (Pi.single k 1)) = Pi.single k 1 := by
    unfold solve
    rw [dif_pos h]
    exact hf h.choose_spec
  simp only [relMat, Matrix.of_apply, this, Matrix.one_apply, Pi.single_apply]

/- English proof (translation)
Use extensionality with `i k`. Simplify using `only [kMat, Matrix.map_apply, Matrix.one_apply]`. Use `split_ifs`. Simplify using `using kOf_apply_self_on σ 1`. Simplify using `using kOf_apply_self_on σ 0`.
-/
theorem kMat_one_on {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ} : kMat σ (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext i k
  simp only [kMat, Matrix.map_apply, Matrix.one_apply]
  split_ifs
  · simpa using kOf_apply_self_on σ 1
  · simpa using kOf_apply_self_on σ 0

/- English proof (translation)
Introduce `D Bs A X fc s R cr eV hF hI hV`. Establish `h1 : X.rowMat cr true Bs.μ0 = 1`. Unfold `CxData.rowMat CxData.rowMatC`. Rewrite using `[relMat_self_on _ hF.h2.1, kMat_one_on]`. Rewrite using `[eq_top_iff, ← D.jEE_basis.2, Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Take `⟨x, hx⟩` from `R.eRR.surjective (D.div.RR.b i)`. Take `⟨y, hy⟩` from `hF.wf.Pq_surj Bs.μ0 x`. Use `⟨R.jV y, ?_, ?_⟩` and prove the remaining obligations. Establish `: R.jV y ∈ Submodule.span ℂ (Set.range R.jV)` using `Submodule.subset_span ⟨y, rfl⟩`.

Rewrite `this` using `[hV]`. Conclude with `this`. Use `hI y` as an intermediate fact. Rewrite `this` using `[h1, Matrix.one_mulVec]`. Conclude with `this.trans (congrArg D.jEE ((congrArg R.eRR hy).trans hx))`.
-/
theorem thetaMap_referenceTuple_goodPart_onto_rows : ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) (R : Read D X fc s) (cr : Crd A fc) (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → D.what₂.LL) →ₗ[D.what₂.LL] A.FR t), CxFacts X cr eV → R.IotaRd cr → R.ReadingFormsSpanGoodSubspace → (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  intro D Bs A X fc s R cr eV hF hI hV
  have h1 : X.rowMat cr true Bs.μ0 = 1 := by
    unfold CxData.rowMat CxData.rowMatC
    rw [relMat_self_on _ hF.h2.1, kMat_one_on]
  rw [eq_top_iff, ← D.jEE_basis.2, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨x, hx⟩ := R.eRR.surjective (D.div.RR.b i)
  obtain ⟨y, hy⟩ := hF.wf.Pq_surj Bs.μ0 x
  refine ⟨R.jV y, ?_, ?_⟩
  · have : R.jV y ∈ Submodule.span ℂ (Set.range R.jV) := Submodule.subset_span ⟨y, rfl⟩
    rw [hV] at this
    exact this
  · have := hI y
    rw [h1, Matrix.one_mulVec] at this
    exact this.trans (congrArg D.jEE ((congrArg R.eRR hy).trans hx))

end GlobalTheory.Mem.SJ
