import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReadPk
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundColumns

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.Mats

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]

omit [NumberField K] in

/- English proof (translation)
Introduce `a` and use `by rcases InfinitePlace.embedding_mk_eq σ with e | e · rw [e] exact hσ a · rw [e, ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, hσ a]`.
-/
theorem isConjAt_mk {σ : K →+* ℂ} (hσ : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) :
    Formalism.DivisionValues.IsConjAt (InfinitePlace.mk σ) := fun a => by
  rcases InfinitePlace.embedding_mk_eq σ with e | e
  · rw [e]
    exact hσ a
  · rw [e, ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, hσ a]

omit [NumberField K] [StarRing K] in

/- English proof (translation)
Break down `InfinitePlace.embedding_mk_eq σ with e | e` into its components or cases. Rewrite `h` using `[e]`. Then use the resulting hypothesis. Rewrite `h` using `[e]`. Establish `h1` using `h.isHermitian`. Establish `e2 : H.map σ = (H.map (ComplexEmbedding.conjugate σ))ᵀ`.

Use extensionality with `i j`. Use `h1.apply j i` as an intermediate fact. Simplify using `only [Matrix.map_apply, ComplexEmbedding.conjugate_coe_eq, Matrix.transpose_apply] at this ⊢`. Rewrite using `[← this]`. Simplify using the standard rewrite rules.

Rewrite using `[e2]`. Conclude with `h.transpose`.
-/
theorem posDef_of_mk {n : ℕ} {σ : K →+* ℂ} {H : Matrix (Fin n) (Fin n) K}
    (h : (H.map (InfinitePlace.mk σ).embedding).PosDef) : (H.map σ).PosDef := by
  rcases InfinitePlace.embedding_mk_eq σ with e | e
  · rwa [e] at h
  · rw [e] at h
    have h1 := h.isHermitian
    have e2 : H.map σ = (H.map (ComplexEmbedding.conjugate σ))ᵀ := by
      ext i j
      have := h1.apply j i
      simp only [Matrix.map_apply, ComplexEmbedding.conjugate_coe_eq, Matrix.transpose_apply] at this ⊢
      rw [← this]
      simp
    rw [e2]
    exact h.transpose

omit [NumberField K] in

/- English proof (translation)
Unfold `Formalism.DivisionValues.hform`. Rewrite using `[Matrix.toLinearMapₛₗ₂'_apply]`. Simplify using `only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply, RingHom.id_apply, smul_eq_mul]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations.
-/
theorem hform_eq_dot {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    Formalism.DivisionValues.hform H x y = star x ⬝ᵥ H.mulVec y := by
  unfold Formalism.DivisionValues.hform
  rw [Matrix.toLinearMapₛₗ₂'_apply]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply, RingHom.id_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

omit [NumberField K] in

/- English proof (translation)
Rewrite using `[hform_eq_dot, hform_eq_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]`.
-/
theorem hform_sa {n : ℕ} {H A : Matrix (Fin n) (Fin n) K} (h : Aᴴ * H = H * A) (x y : Fin n → K) :
    Formalism.DivisionValues.hform H (A.mulVec x) y = Formalism.DivisionValues.hform H x (A.mulVec y) := by
  rw [hform_eq_dot, hform_eq_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

omit [NumberField K] [StarRing K] [Fintype G] in

/- English proof (translation)
Use `show ((0 : Matrix (Fin 0) (Fin 0) K).map σ).PosDef`. Rewrite using `[Subsingleton.elim ((0 : Matrix (Fin 0) (Fin 0) K).map σ) 1]`. Conclude with `Matrix.PosDef.one`. Use `lat := by show Submodule.IsLattice K (⊤ : Submodule (𝓞 K) (Fin 0 → K))`. Use `⟨?_, Subsingleton.elim _ _⟩` and prove the remaining obligations.

Rewrite using `[Subsingleton.elim (⊤ : Submodule (𝓞 K) (Fin 0 → K)) ⊥]`. Conclude with `Submodule.fg_bot`. Use `add _ _ := Subsingleton.elim (α := Matrix (Fin 0) (Fin 0) K) _ _`. Use `smul _ _ := Subsingleton.elim (α := Matrix (Fin 0) (Fin 0) K) _ _`. Use `one := Subsingleton.elim (α := Matrix (Fin 0) (Fin 0) K) _ _`.

Use `mul _ _ _ _ := Subsingleton.elim (α := Matrix (Fin 0) (Fin 0) K) _ _`. Use `E_eq := rfl`. Use `cen := hc`. Use `idem := hi`. Use `sa x y := by`.

Rewrite using `[hform_eq_dot, hform_eq_dot]`. Both sides reduce to the same expression.
-/
theorem zero_laws [NumberField K] [StarRing K] (σ : K →+* ℂ) {e : MonoidAlgebra K G}
    (hc : e ∈ Subalgebra.center K (MonoidAlgebra K G)) (hi : IsIdempotentElem e) : (Mat1.zero K G).Laws σ e where
  pos := by
    show ((0 : Matrix (Fin 0) (Fin 0) K).map σ).PosDef
    rw [Subsingleton.elim ((0 : Matrix (Fin 0) (Fin 0) K).map σ) 1]
    exact Matrix.PosDef.one
  lat := by
    show Submodule.IsLattice K (⊤ : Submodule (𝓞 K) (Fin 0 → K))
    refine ⟨?_, Subsingleton.elim _ _⟩
    rw [Subsingleton.elim (⊤ : Submodule (𝓞 K) (Fin 0 → K)) ⊥]
    exact Submodule.fg_bot
  add _ _ := Subsingleton.elim (α := Matrix (Fin 0) (Fin 0) K) _ _
  smul _ _ := Subsingleton.elim (α := Matrix (Fin 0) (Fin 0) K) _ _
  one := Subsingleton.elim (α := Matrix (Fin 0) (Fin 0) K) _ _
  mul _ _ _ _ := Subsingleton.elim (α := Matrix (Fin 0) (Fin 0) K) _ _
  E_eq := rfl
  cen := hc
  idem := hi
  sa x y := by
    rw [hform_eq_dot, hform_eq_dot]
    rfl

def lvlMat (S : CSD K) (r : Representation K G S.Forms) (P : Subgroup G) (ψ : P →* Kˣ) (e : MonoidAlgebra K G) : Mat1 K G :=
  ⟨S.lvlDim r P ψ, S.lvlH r P ψ, S.lvlOp r P ψ e, S.lvlNab r P ψ, fun a => S.lvlOp r P ψ a⟩

/- English proof (translation)
Establish `h0` using `isConjAt_mk hσ`. Establish `hP` using `(level_idempotent_spec K _ h0 G P ψ).1`. Establish `hI` using `idempotent_spec K _ h0 G X hX`. Establish `hinj : Function.Injective (S.lvlE r P ψ).mulVec` using `(image_idempotent_spec K _ _).1`. Establish `hE : ∀ i j, S.lvlE r P ψ i j ∈ Formalism.DivisionValues.cmMax K` using `image_idempotent_rational K S.dim (S.gaMat r (lvlIdem P ψ)) (gaMat_rat S r hrat _ hP.rat)`.

Establish `hproj` using `(orthogonal_projection_spec K _ h0 S (hpos _) G r hr _ hP.idem hP.selfAdj).1.1`. Establish `hop` using `level_operator_spec K _ h0 S (hpos _) G r hr P ψ`. Use `⟨posDef_of_mk (cut_posDef S.H (S.lvlE r P ψ) hinj hE (Nat.card P) Nat.card_pos _ (hpos _)), Formalism.DivisionValues.exponent_index_lattice.cut_isLattice _ (fun _ _ hxy => hinj hxy) _ (S.lf_nabLat_isLattice hS), fun a b => ?_, fun c a => ?_, ?_, fun a _ b hb => (hop b (Subalgebra …` and prove the remaining obligations. Use `show S.lvlOp r P ψ (a + b) = S.lvlOp r P ψ a + S.lvlOp r P ψ b`. Unfold `CSD.lvlOp`.

Rewrite using `[CSD.gaMat_eq_lift, CSD.gaMat_eq_lift, CSD.gaMat_eq_lift, map_add, Matrix.mul_add, Matrix.add_mul]`. Use `show S.lvlOp r P ψ (c • a) = c • S.lvlOp r P ψ a`. Unfold `CSD.lvlOp`. Rewrite using `[CSD.gaMat_eq_lift, CSD.gaMat_eq_lift, map_smul, Matrix.mul_smul, Matrix.smul_mul]`. Use `show S.lvlOp r P ψ 1 = 1`.

Unfold `CSD.lvlOp`. Rewrite using `[(group_action_matrix_hom K S G r).1, Matrix.mul_one]`. Conclude with `hproj`. Establish `h1` using `(hop (idemOf X) (hI.2 _).symm).1`. Establish `h2` using `group_action_matrix_adjoint K S G r hr (idemOf X)`.

Rewrite `h2` using `[hI.1.selfAdj]`. Use `show (S.lvlOp r P ψ (idemOf X))ᴴ * ((Nat.card P : K)⁻¹ • ((S.lvlE r P ψ)ᴴ * S.H * S.lvlE r P ψ)) = ((Nat.card P : K)⁻¹ • ((S.lvlE r P ψ)ᴴ * S.H * S.lvlE r P ψ)) * S.lvlOp r P ψ (idemOf X)`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_mul, Matrix.mul_assoc (S.lvlE r P ψ)ᴴ, h2, Matrix.mul_assoc _ (S.lvlE r P ψ), h1]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem lvlMat_laws {σ : K →+* ℂ} (hσ : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) (S : CSD K) {s : ℕ} (hS : S.Good s)
    (hpos : ∀ v : InfinitePlace K, (S.H.map v.embedding).PosDef) (r : Representation K G S.Forms) (hr : S.ActGood r)
    (hrat : S.ActRat r) (P : Subgroup G) (ψ : P →* Kˣ) (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) :
    (lvlMat S r P ψ (idemOf X)).Laws σ (idemOf X) := by
  have h0 := isConjAt_mk hσ
  have hP := (level_idempotent_spec K _ h0 G P ψ).1
  have hI := idempotent_spec K _ h0 G X hX
  have hinj : Function.Injective (S.lvlE r P ψ).mulVec := (image_idempotent_spec K _ _).1
  have hE : ∀ i j, S.lvlE r P ψ i j ∈ Formalism.DivisionValues.cmMax K :=
    image_idempotent_rational K S.dim (S.gaMat r (lvlIdem P ψ)) (gaMat_rat S r hrat _ hP.rat)
  have hproj := (orthogonal_projection_spec K _ h0 S (hpos _) G r hr _ hP.idem hP.selfAdj).1.1
  have hop := level_operator_spec K _ h0 S (hpos _) G r hr P ψ
  refine ⟨posDef_of_mk (cut_posDef S.H (S.lvlE r P ψ) hinj hE (Nat.card P) Nat.card_pos _ (hpos _)),
    Formalism.DivisionValues.exponent_index_lattice.cut_isLattice _ (fun _ _ hxy => hinj hxy) _ (S.lf_nabLat_isLattice hS), fun a b => ?_, fun c a => ?_, ?_,
    fun a _ b hb => (hop b (Subalgebra.mem_center_iff.1 hb _).symm).2 a, rfl, Subalgebra.mem_center_iff.2 hI.2, hI.1.idem,
    hform_sa ?_⟩
  · show S.lvlOp r P ψ (a + b) = S.lvlOp r P ψ a + S.lvlOp r P ψ b
    unfold CSD.lvlOp
    rw [CSD.gaMat_eq_lift, CSD.gaMat_eq_lift, CSD.gaMat_eq_lift, map_add, Matrix.mul_add, Matrix.add_mul]
  · show S.lvlOp r P ψ (c • a) = c • S.lvlOp r P ψ a
    unfold CSD.lvlOp
    rw [CSD.gaMat_eq_lift, CSD.gaMat_eq_lift, map_smul, Matrix.mul_smul, Matrix.smul_mul]
  · show S.lvlOp r P ψ 1 = 1
    unfold CSD.lvlOp
    rw [(group_action_matrix_hom K S G r).1, Matrix.mul_one]
    exact hproj
  · have h1 := (hop (idemOf X) (hI.2 _).symm).1
    have h2 := group_action_matrix_adjoint K S G r hr (idemOf X)
    rw [hI.1.selfAdj] at h2
    show (S.lvlOp r P ψ (idemOf X))ᴴ * ((Nat.card P : K)⁻¹ • ((S.lvlE r P ψ)ᴴ * S.H * S.lvlE r P ψ)) =
      ((Nat.card P : K)⁻¹ • ((S.lvlE r P ψ)ᴴ * S.H * S.lvlE r P ψ)) * S.lvlOp r P ψ (idemOf X)
    rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h1,
      Matrix.conjTranspose_mul, Matrix.mul_assoc (S.lvlE r P ψ)ᴴ, h2, Matrix.mul_assoc _ (S.lvlE r P ψ), h1]
    simp only [Matrix.mul_assoc]

end Gen

section Col

variable {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Ranks} (W : Formalism.L2.Col.Wts X Pr.Word R) (Ch : Formalism.L2.Col.Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok) (v0 : InfinitePlace X.K)
  (TU : Finset (Tup X.F X.E X.K S)) (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
  (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ) {σ : X.K →+* ℂ} (hσ : ∀ a, σ (star a) = starRingEnd ℂ (σ a))
  (hirr : ∀ χ ∈ Xg, IsAbsIrrChar χ) (P : Subgroup (Formalism.L2.Col.G0 X.E Pr.vGs R.r)) (ψ : P →* X.Kˣ)

include hσ hirr

/- English proof (translation)
The claim follows from `lvlMat_laws hσ _ (Formalism.L2.Col.MtildeKCSD_good W Ch sel τ.1 hX _) (fun v => (Formalism.L2.Col.mtildeK_rat W Ch sel τ.1 hX).posH _ v) _ (Formalism.L2.Col.unipotentActionForms_good W Ch sel τ.1 hX _) (Formalism.L2.Col.unipotentActionForms_rational W Ch sel τ.1 hX _) P ψ Xg hirr`.
-/
theorem rows_laws (τ : TupF TU) :
    (lvlMat ((colIn W Ch sel hX v0 TU Xg S0 xiVal).MtildeCSD τ) ((colIn W Ch sel hX v0 TU Xg S0 xiVal).leftGroupActionRight τ) P ψ
      (idemOf Xg)).Laws σ (idemOf Xg) :=
  lvlMat_laws hσ _ (Formalism.L2.Col.MtildeKCSD_good W Ch sel τ.1 hX _) (fun v => (Formalism.L2.Col.mtildeK_rat W Ch sel τ.1 hX).posH _ v) _
    (Formalism.L2.Col.unipotentActionForms_good W Ch sel τ.1 hX _) (Formalism.L2.Col.unipotentActionForms_rational W Ch sel τ.1 hX _) P ψ Xg hirr

/- English proof (translation)
The claim follows from `lvlMat_laws hσ _ (Formalism.L2.Col.MtKCSD_good W Ch sel τ.1 hX (j.1 + 1) _) (fun v => (Formalism.L2.Col.mtK_rat W Ch sel τ.1 hX (j.1 + 1)).posH _ v) _ (Formalism.L2.Col.unipotentActionClassSum_good W Ch sel τ.1 hX (j.1 + 1) _) (Formalism.L2.Col.unipotentActionClassSum_rational W …`.
-/
theorem lifts_laws (j : Fin R.m) (τ : TupF TU) :
    (lvlMat ((colIn W Ch sel hX v0 TU Xg S0 xiVal).MtCSD j τ) ((colIn W Ch sel hX v0 TU Xg S0 xiVal).leftGroupActionLift j τ) P ψ
      (idemOf Xg)).Laws σ (idemOf Xg) :=
  lvlMat_laws hσ _ (Formalism.L2.Col.MtKCSD_good W Ch sel τ.1 hX (j.1 + 1) _)
    (fun v => (Formalism.L2.Col.mtK_rat W Ch sel τ.1 hX (j.1 + 1)).posH _ v) _
    (Formalism.L2.Col.unipotentActionClassSum_good W Ch sel τ.1 hX (j.1 + 1) _) (Formalism.L2.Col.unipotentActionClassSum_rational W Ch sel τ.1 hX (j.1 + 1) _) P ψ Xg hirr

end Col

section Fam

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} (A : FamIn D.what₂.LL G Pl0 T D.R.m)
  (P : Subgroup G) (ψ : P →* D.what₂.LLˣ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rMat_eq (t : T) : rMat A P ψ t = lvlMat (A.MtildeCSD t) (A.leftGroupActionRight t) P ψ (idemOf A.X) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lMat_eq (i : Fin D.R.m) (t : T) : lMat A P ψ i t = lvlMat (A.MtCSD i t) (A.leftGroupActionLift i t) P ψ⁻¹ (idemOf A.X) := rfl

end Fam

/- English proof (translation)
Introduce `X px I hX Xg tr _ hirr`. Use `⟨fun b a => ?_, fun a j => ?_⟩` and prove the remaining obligations. Unfold `mAU`. Rewrite using `[rMat_eq]`. Conclude with `rows_laws (X := X.B.fields) (Pr := X.B.primes px) X.B.wts I.Ch I.sel hX (InfinitePlace.mk X.B.embLL) (tuOf I Set.univ) Xg ∅ (xiValOf I) (σ := X.B.embLL) X.B.starLL_cx hirr _ _ (tAll I a)`.

Unfold `mLU split_ifs with h`. Rewrite using `[lMat_eq]`. Conclude with `lifts_laws (X := X.B.fields) (Pr := X.B.primes px) X.B.wts I.Ch I.sel hX (InfinitePlace.mk X.B.embLL) (tuOf I Set.univ) Xg ∅ (xiValOf I) (σ := X.B.embLL) X.B.starLL_cx hirr _ _ _ (tAll I a)`. Establish `hI` using `idempotent_central X.B.LL (Gc X.B px) Xg hirr`. Conclude with `zero_laws _ (Subalgebra.mem_center_iff.2 hI.2) hI.1`.
-/
theorem mats_laws : ∀ (X : Stages) (px : PreX X.B.toPre) (I : ColIn X.B px) (hX : X.B.fields.Ok) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px), I.Ok → (∀ χ ∈ Xg, IsAbsIrrChar χ) → (∀ b a, (mAU X I hX Xg tr b a).Laws X.toD7.what₂.embLL (idemOf Xg)) ∧ ∀ a j, (mLU X I hX Xg tr a j).Laws X.toD7.what₂.embLL (idemOf Xg) := by
  intro X px I hX Xg tr _ hirr
  refine ⟨fun b a => ?_, fun a j => ?_⟩
  · unfold mAU
    rw [rMat_eq]
    exact rows_laws (X := X.B.fields) (Pr := X.B.primes px) X.B.wts I.Ch I.sel hX (InfinitePlace.mk X.B.embLL) (tuOf I Set.univ) Xg ∅
      (xiValOf I) (σ := X.B.embLL) X.B.starLL_cx hirr _ _ (tAll I a)
  · unfold mLU
    split_ifs with h
    · rw [lMat_eq]
      exact lifts_laws (X := X.B.fields) (Pr := X.B.primes px) X.B.wts I.Ch I.sel hX (InfinitePlace.mk X.B.embLL) (tuOf I Set.univ) Xg ∅
        (xiValOf I) (σ := X.B.embLL) X.B.starLL_cx hirr _ _ _ (tAll I a)
    · have hI := idempotent_central X.B.LL (Gc X.B px) Xg hirr
      exact zero_laws _ (Subalgebra.mem_center_iff.2 hI.2) hI.1

end GlobalTheory.Mem.R3.Rw.Mats

end
