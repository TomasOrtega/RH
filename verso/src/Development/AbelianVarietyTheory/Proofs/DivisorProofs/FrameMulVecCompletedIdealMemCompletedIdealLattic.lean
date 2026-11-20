import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrConjApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FrameColSmul

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact hG y hy`. Consider the case `zero`. Establish `: (fun i => c i * (0 : A)) = 0` using `by funext i; simp`. Rewrite using `[this]`.

Conclude with `M.zero_mem`. Consider the case `add a b _ _ ha hb`. Establish `: (fun i => c i * (a + b)) = (fun i => c i * a) + (fun i => c i * b)`. Use function extensionality and compare the values at `i`. Simplify using `[mul_add]`.

Rewrite using `[this]`. Conclude with `M.add_mem ha hb`. Consider the case `smul r a _ ha`. Establish `: (fun i => c i * (r • a)) = r • (fun i => c i * a)`. Use function extensionality and compare the values at `i`.

Use `show c i * ((r : A) * a) = (r : A) * (c i * a)`. Conclude with `mul_left_comm _ _ _`. Rewrite using `[this]`. Conclude with `M.smul_mem r ha`.
-/
theorem colMul_mem_of_span {A : Type} [CommRing A] (S : Subring A) {ι : Type} (M : Submodule S (ι → A))
    (c : ι → A) (G : Set A) (hG : ∀ y ∈ G, (fun i => c i * y) ∈ M) (x : A)
    (hx : x ∈ Submodule.span S G) : (fun i => c i * x) ∈ M := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact hG y hy
  | zero =>
    have : (fun i => c i * (0 : A)) = 0 := by funext i; simp
    rw [this]; exact M.zero_mem
  | add a b _ _ ha hb =>
    have : (fun i => c i * (a + b)) = (fun i => c i * a) + (fun i => c i * b) := by
      funext i; simp [mul_add]
    rw [this]; exact M.add_mem ha hb
  | smul r a _ ha =>
    have : (fun i => c i * (r • a)) = r • (fun i => c i * a) := by
      funext i
      show c i * ((r : A) * a) = (r : A) * (c i * a)
      exact mul_left_comm _ _ _
    rw [this]; exact M.smul_mem r ha

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, Finset.sum_apply]`.
-/
theorem mulVec_eq_sum_col {A : Type} [CommRing A] {n : ℕ} (P : Matrix (Fin n) (Fin n) A) (w : Fin n → A) :
    P *ᵥ w = ∑ j, (fun i => P i j * w j) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show _ = φ ((b : E) * c i)`. Rewrite using `[map_mul, mul_comm]`.
-/
theorem map_col_mul {E A : Type} [Field E] [NumberField E] [CommRing A] (φ : E →+* A) {n : ℕ}
    (c : Fin n → E) (b : 𝓞 E) :
    (fun i => φ (c i) * φ (b : E)) = fun i => φ ((b • c) i) := by
  funext i
  show _ = φ ((b : E) * c i)
  rw [map_mul, mul_comm]

/- English proof (translation)
Establish `hcol : (fun i => (fr : Matrix (Fin n) (Fin n) D.host.E) i j) ∈ colLat fr` using `Submodule.subset_span ⟨j, rfl⟩`. Establish `hm : b • (fun i => (fr : Matrix (Fin n) (Fin n) D.host.E) i j) ∈ 𝔪 • colLat fr` using `Submodule.smul_mem_smul hb hcol`. Rewrite using `[map_col_mul]`. Conclude with `Submodule.subset_span ⟨_, hm, rfl⟩`.
-/
theorem gen_mem {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) (𝔪 : Ideal (𝓞 D.host.E)) (j : Fin n)
    (b : 𝓞 D.host.E) (hb : b ∈ 𝔪) :
    (fun i => GlobalTheory.FrameTransport.inclEAf D ((fr : Matrix (Fin n) (Fin n) D.host.E) i j) *
        GlobalTheory.FrameTransport.inclEAf D (b : D.host.E)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • colLat fr) := by
  have hcol : (fun i => (fr : Matrix (Fin n) (Fin n) D.host.E) i j) ∈ colLat fr :=
    Submodule.subset_span ⟨j, rfl⟩
  have hm : b • (fun i => (fr : Matrix (Fin n) (Fin n) D.host.E) i j) ∈ 𝔪 • colLat fr :=
    Submodule.smul_mem_smul hb hcol
  rw [map_col_mul]
  exact Submodule.subset_span ⟨_, hm, rfl⟩

/- English proof (translation)
Introduce `D n fr 𝔪 w hw`. Rewrite using `[mulVec_eq_sum_col]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Conclude with `colMul_mem_of_span (Formalism.L2.Herm.intAf D.host.F D.host.E) _ (fun i => GlobalTheory.FrameTransport.inclEAf D ((fr : Matrix (Fin n) (Fin n) D.host.E) i j)) _ (by`. Introduce and unpack `_ ⟨b, hb, rfl⟩`.

Conclude with `gen_mem fr 𝔪 j b hb) (w j) (hw j)`.
-/
theorem mulVec_mem : ∀ {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) (𝔪 : Ideal (𝓞 D.host.E)) (w : Fin n → Lev.EAf D), (∀ i, w i ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E) ((fun b : 𝓞 D.host.E => GlobalTheory.FrameTransport.inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E)))) → (Formalism.UG.bc (GlobalTheory.FrameTransport.inclEAf D) fr).val *ᵥ w ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • colLat fr) := by
  intro D n fr 𝔪 w hw
  rw [mulVec_eq_sum_col]
  refine Submodule.sum_mem _ fun j _ => ?_
  exact colMul_mem_of_span (Formalism.L2.Herm.intAf D.host.F D.host.E) _
    (fun i => GlobalTheory.FrameTransport.inclEAf D ((fr : Matrix (Fin n) (Fin n) D.host.E) i j)) _
    (by
      rintro _ ⟨b, hb, rfl⟩
      exact gen_mem fr 𝔪 j b hb) (w j) (hw j)

end GlobalTheory.FrameColSmul
