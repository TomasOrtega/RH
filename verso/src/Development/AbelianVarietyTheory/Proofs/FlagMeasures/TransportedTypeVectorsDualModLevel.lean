import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrLink
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicColumnLatticeEqSpanPartTransportedFrameStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.DualMod

open Formalism.L2.SG.Pf.unitaryCongruence

section Gen

variable (I : AutInst)

/- English proof (translation)
Establish `hd : ∀ (J : Matrix n n A) (x y : n → A), Formalism.UG.hform σ J x y = (σ ∘ x) ⬝ᵥ (J *ᵥ y)`. Introduce `J x y`. Simplify using `only [Formalism.UG.hform, dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, mul_assoc]`. Establish `hσ : σ ∘ (M *ᵥ x) = M.map σ *ᵥ (σ ∘ x)`. Use function extensionality and compare the values at `i`.

Conclude with `RingHom.map_mulVec σ M x i`. Rewrite using `[hd, hd, hσ, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Formalism.UG.cT, Matrix.mul_assoc]`.
-/
theorem hform_mulVec_conj {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J M : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ M * J * M) x y := by
  have hd : ∀ (J : Matrix n n A) (x y : n → A), Formalism.UG.hform σ J x y = (σ ∘ x) ⬝ᵥ (J *ᵥ y) := by
    intro J x y
    simp only [Formalism.UG.hform, dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, mul_assoc]
  have hσ : σ ∘ (M *ᵥ x) = M.map σ *ᵥ (σ ∘ x) := by
    funext i
    exact RingHom.map_mulVec σ M x i
  rw [hd, hd, hσ, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec,
    mulVec_mulVec, Formalism.UG.cT, Matrix.mul_assoc]

/- English proof (translation)
Establish `h : Formalism.UG.cT (sigA I) (I.fmat x) * I.J.map (Formalism.UG.inclE (F` using `I.F) (Af I.F)) * I.fmat x = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := x.2`. Unfold `hA`. Rewrite using `[hform_mulVec_conj, h]`.
-/
theorem hA_unitary (x : I.Gf) (u v : VA I) : hA I (I.fmat x *ᵥ u) (I.fmat x *ᵥ v) = hA I u v := by
  have h : Formalism.UG.cT (sigA I) (I.fmat x) * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * I.fmat x =
      I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := x.2
  unfold hA
  rw [hform_mulVec_conj, h]

/- English proof (translation)
Take `⟨s, hs, rfl⟩` from `ha`. Take `⟨t, ht, rfl⟩` from `hb`. Conclude with `⟨s + t, add_mem hs ht, by ring⟩`.
-/
theorem zmod_add {g : ℕ} {a b : I.E ⊗[I.F] Af I.F} (ha : ZMod' I g a) (hb : ZMod' I g b) :
    ZMod' I g (a + b) := by
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨t, ht, rfl⟩ := hb
  exact ⟨s + t, add_mem hs ht, by ring⟩

/- English proof (translation)
Take `⟨s, hs, rfl⟩` from `ha`. Conclude with `⟨c * s, mul_mem hc hs, by ring⟩`.
-/
theorem zmod_mul {g : ℕ} {a c : I.E ⊗[I.F] Af I.F} (hc : c ∈ IntAf I.F I.E) (ha : ZMod' I g a) :
    ZMod' I g (c * a) := by
  obtain ⟨s, hs, rfl⟩ := ha
  exact ⟨c * s, mul_mem hc hs, by ring⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, zero_mem _, by simp⟩`.
-/
theorem zmod_zero (g : ℕ) : ZMod' I g 0 := ⟨0, zero_mem _, by simp⟩

/- English proof (translation)
Simplify using `[hA, Formalism.UG.hform]`.
-/
theorem hA_zero_left (y : VA I) : hA I 0 y = 0 := by simp [hA, Formalism.UG.hform]
/- English proof (translation)
Simplify using `[hA, Formalism.UG.hform]`.
-/
theorem hA_zero_right (y : VA I) : hA I y 0 = 0 := by simp [hA, Formalism.UG.hform]

/- English proof (translation)
Proceed by induction on `hm using Submodule.span_induction with`. Consider the case `mem m hm`. Take `⟨x, hx, rfl⟩` from `hm`. Rewrite using `[hA_smul_left, map_natCast]`. Conclude with `⟨hA I x y, hA_int I hx hy, rfl⟩`.

Consider the case `zero => rw [hA_zero_left]`. Conclude with `zmod_zero I g`. Consider the case `add a b _ _ ha hb => rw [hA_add_left]`. Conclude with `zmod_add I ha hb`. Consider the case `smul c a _ ha => show ZMod' I g (hA I ((c : I.E ⊗[I.F] Af I.F) • a) y)`.

Rewrite using `[hA_smul_left]`. Conclude with `zmod_mul I (sigA_mem I c.2) ha`.
-/
theorem hA_mL_left {g : ℕ} {m y : VA I} (hm : m ∈ mL I g) (hy : y ∈ I.Lf) : ZMod' I g (hA I m y) := by
  induction hm using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨x, hx, rfl⟩ := hm
    rw [hA_smul_left, map_natCast]
    exact ⟨hA I x y, hA_int I hx hy, rfl⟩
  | zero => rw [hA_zero_left]; exact zmod_zero I g
  | add a b _ _ ha hb => rw [hA_add_left]; exact zmod_add I ha hb
  | smul c a _ ha =>
    show ZMod' I g (hA I ((c : I.E ⊗[I.F] Af I.F) • a) y)
    rw [hA_smul_left]; exact zmod_mul I (sigA_mem I c.2) ha

/- English proof (translation)
Proceed by induction on `hm using Submodule.span_induction with`. Consider the case `mem m hm`. Take `⟨x, hx, rfl⟩` from `hm`. Rewrite using `[hA_smul_right]`. Conclude with `⟨hA I y x, hA_int I hy hx, rfl⟩`.

Consider the case `zero => rw [hA_zero_right]`. Conclude with `zmod_zero I g`. Consider the case `add a b _ _ ha hb => rw [hA_add_right]`. Conclude with `zmod_add I ha hb`. Consider the case `smul c a _ ha => show ZMod' I g (hA I y ((c : I.E ⊗[I.F] Af I.F) • a))`.

Rewrite using `[hA_smul_right]`. Conclude with `zmod_mul I c.2 ha`.
-/
theorem hA_mL_right {g : ℕ} {m y : VA I} (hm : m ∈ mL I g) (hy : y ∈ I.Lf) : ZMod' I g (hA I y m) := by
  induction hm using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨x, hx, rfl⟩ := hm
    rw [hA_smul_right]
    exact ⟨hA I y x, hA_int I hy hx, rfl⟩
  | zero => rw [hA_zero_right]; exact zmod_zero I g
  | add a b _ _ ha hb => rw [hA_add_right]; exact zmod_add I ha hb
  | smul c a _ ha =>
    show ZMod' I g (hA I y ((c : I.E ⊗[I.F] Af I.F) • a))
    rw [hA_smul_right]; exact zmod_mul I c.2 ha

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite using `[Nat.cast_smul_eq_nsmul]`. Conclude with `I.Lf.nsmul_mem hx g`.
-/
theorem mL_le (g : ℕ) : mL I g ≤ I.Lf := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [Nat.cast_smul_eq_nsmul]
  exact I.Lf.nsmul_mem hx g

end Gen

/- English proof (translation)
Introduce `D X u wt ιA hW hι c p b bd hb hbd hm i j`. Take `⟨-, h2, -⟩` from `GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hW hι`. Establish `hY : ∀ i, X.B.I.fmat (X.xu u) *ᵥ X.bw i ∈ X.B.I.Lf` using `fun i => K_mv X.B.I (X.xu_K u) (X.vectorsInLattice.2.2 i).1`. Establish `hYd : ∀ i, X.B.I.fmat (X.xu u) *ᵥ X.bwd i ∈ X.B.I.Lf` using `fun i => K_mv X.B.I (X.xu_K u) (X.vectorsInLattice.2.2 i).2`. Establish `hm1 : embA X wt ιA (b j) - X.B.I.fmat (X.xu u) *ᵥ X.bw j ∈ mL X.B.I X.B.g`.

Rewrite using `[hb j]`. Conclude with `(hm j).1`. Establish `hm2 : embA X wt ιA (bd i) - X.B.I.fmat (X.xu u) *ᵥ X.bwd i ∈ mL X.B.I X.B.g`. Rewrite using `[hbd i]`. Conclude with `(hm i).2`.

Establish `key : ZMod' X.B.I X.B.g (hA X.B.I (embA X wt ιA (bd i)) (embA X wt ιA (b j)) - if i = j then X.ew else 0)`. Generalize the expression as in `hm' : embA X wt ιA (b j) - X.B.I.fmat (X.xu u) *ᵥ X.bw j = m' at hm1`. Generalize the expression as in `hmm : embA X wt ιA (bd i) - X.B.I.fmat (X.xu u) *ᵥ X.bwd i = m at hm2`. Establish `e1 : embA X wt ιA (b j) = X.B.I.fmat (X.xu u) *ᵥ X.bw j + m'` using `by rw [← hm']; abel`. Establish `e2 : embA X wt ιA (bd i) = X.B.I.fmat (X.xu u) *ᵥ X.bwd i + m` using `by rw [← hmm]; abel`.

Rewrite using `[e1, e2, hA_add_left, hA_add_right, hA_add_right, hA_unitary]`. Establish `e3 : hA X.B.I (X.bwd i) (X.bw j) + hA X.B.I (X.B.I.fmat (X.xu u) *ᵥ X.bwd i) m' + (hA X.B.I m (X.B.I.fmat (X.xu u) *ᵥ X.bw j) + hA X.B.I m m') - (if i = j then X.ew else 0) = (hA X.B.I (X.bwd i) (X.bw j) - (if i = j then X.ew else 0)) + hA X.B.I (X.B.I.fmat (X.xu u) *ᵥ X.bwd i) m …` using `by ring`. Rewrite using `[e3]`. Use `zmod_add _ (zmod_add _ (X.bw_dual i j) (hA_mL_right _ hm1 (hYd i))) (zmod_add _ (hA_mL_left _ hm2 (hY j)) (hA_mL_left _ hm2 (mL_le _ _ hm1)))` and prove the remaining obligations. Take `⟨t, ht, he⟩` from `key`.

Use `⟨ιA t, (hι.2 t).1 ht, ?_⟩` and prove the remaining obligations. Establish `hg : ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E ⊗[D.host.F] Ad D.host.F) = ιA (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)`. Rewrite using `[map_natCast, X.g_eq]`. Apply the tactic sequence `have hif : (if i = j then ιA X.ew else 0) = ιA (if i = j then X.ew else 0) := by split_ifs <;> simp`. Rewrite using `[← h2, hg, hif, ← map_sub, he, map_mul]`.
-/
theorem dual_mod : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), ∀ (b bd : Fin D.R.k → Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F), (∀ i, embA X wt ιA (b i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i)) → (∀ i, embA X wt ιA (bd i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i)) → (∀ i, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i) - X.B.I.fmat (X.xu u) *ᵥ X.bw i ∈ mL X.B.I X.B.g ∧ (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i) - X.B.I.fmat (X.xu u) *ᵥ X.bwd i ∈ mL X.B.I X.B.g) → ∀ i j, ∃ t ∈ OAd D.host.F D.host.E, hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F) (bd i) (b j) - (if i = j then ιA X.ew else 0) = ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E ⊗[D.host.F] Ad D.host.F) * t := by
  intro D X u wt ιA hW hι c p b bd hb hbd hm i j
  obtain ⟨-, h2, -⟩ := GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hW hι
  have hY : ∀ i, X.B.I.fmat (X.xu u) *ᵥ X.bw i ∈ X.B.I.Lf :=
    fun i => K_mv X.B.I (X.xu_K u) (X.vectorsInLattice.2.2 i).1
  have hYd : ∀ i, X.B.I.fmat (X.xu u) *ᵥ X.bwd i ∈ X.B.I.Lf :=
    fun i => K_mv X.B.I (X.xu_K u) (X.vectorsInLattice.2.2 i).2
  have hm1 : embA X wt ιA (b j) - X.B.I.fmat (X.xu u) *ᵥ X.bw j ∈ mL X.B.I X.B.g := by
    rw [hb j]; exact (hm j).1
  have hm2 : embA X wt ιA (bd i) - X.B.I.fmat (X.xu u) *ᵥ X.bwd i ∈ mL X.B.I X.B.g := by
    rw [hbd i]; exact (hm i).2
  have key : ZMod' X.B.I X.B.g
      (hA X.B.I (embA X wt ιA (bd i)) (embA X wt ιA (b j)) - if i = j then X.ew else 0) := by
    generalize hm' : embA X wt ιA (b j) - X.B.I.fmat (X.xu u) *ᵥ X.bw j = m' at hm1
    generalize hmm : embA X wt ιA (bd i) - X.B.I.fmat (X.xu u) *ᵥ X.bwd i = m at hm2
    have e1 : embA X wt ιA (b j) = X.B.I.fmat (X.xu u) *ᵥ X.bw j + m' := by rw [← hm']; abel
    have e2 : embA X wt ιA (bd i) = X.B.I.fmat (X.xu u) *ᵥ X.bwd i + m := by rw [← hmm]; abel
    rw [e1, e2, hA_add_left, hA_add_right, hA_add_right, hA_unitary]
    have e3 : hA X.B.I (X.bwd i) (X.bw j) + hA X.B.I (X.B.I.fmat (X.xu u) *ᵥ X.bwd i) m' +
        (hA X.B.I m (X.B.I.fmat (X.xu u) *ᵥ X.bw j) + hA X.B.I m m') - (if i = j then X.ew else 0) =
        (hA X.B.I (X.bwd i) (X.bw j) - (if i = j then X.ew else 0)) +
          hA X.B.I (X.B.I.fmat (X.xu u) *ᵥ X.bwd i) m' +
          (hA X.B.I m (X.B.I.fmat (X.xu u) *ᵥ X.bw j) + hA X.B.I m m') := by ring
    rw [e3]
    refine zmod_add _ (zmod_add _ (X.bw_dual i j) (hA_mL_right _ hm1 (hYd i)))
      (zmod_add _ (hA_mL_left _ hm2 (hY j)) (hA_mL_left _ hm2 (mL_le _ _ hm1)))
  obtain ⟨t, ht, he⟩ := key
  refine ⟨ιA t, (hι.2 t).1 ht, ?_⟩
  have hg : ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E ⊗[D.host.F] Ad D.host.F) =
      ιA (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
    rw [map_natCast, X.g_eq]
  have hif : (if i = j then ιA X.ew else 0) = ιA (if i = j then X.ew else 0) := by
    split_ifs <;> simp
  rw [← h2, hg, hif, ← map_sub, he, map_mul]

end GlobalTheory.St.G.DualMod
