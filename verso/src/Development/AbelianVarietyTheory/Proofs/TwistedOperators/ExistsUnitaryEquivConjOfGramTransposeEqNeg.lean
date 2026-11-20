import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPair

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GrpConj

variable {D : D7}

/- English proof (translation)
Establish `hcc : (M.map c).map c = M` using `Matrix.ext fun i j => hc _`. Establish `hB : B = (-Aᵀ).submatrix e.symm e.symm`. Rewrite using `[hAB, neg_neg]`. Use extensionality with `i j`. Simplify using the standard rewrite rules.

Establish `h2 : Mᵀ * Aᵀ * M.map c = Aᵀ`. Use `congrArg Matrix.transpose hM` as an intermediate fact. Rewrite `this` using `[Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc]`. Then use the resulting hypothesis. Rewrite using `[← Matrix.submatrix_map, hcc, Matrix.transpose_submatrix]`. Use `conv_rhs => rw [hB]`.

Rewrite using `[hB, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.mul_neg, Matrix.neg_mul, h2]`.
-/
theorem conj_mem {R : Type} [CommRing R] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (c : R →+* R) (hc : ∀ x, c (c x) = x) (e : m ≃ n) (A : Matrix m m R) (B : Matrix n n R)
    (hAB : Aᵀ = -(B.submatrix e e)) (M : Matrix m m R) (hM : (M.map c)ᵀ * A * M = A) :
    (((M.map c).submatrix e.symm e.symm).map c)ᵀ * B * (M.map c).submatrix e.symm e.symm = B := by
  have hcc : (M.map c).map c = M := Matrix.ext fun i j => hc _
  have hB : B = (-Aᵀ).submatrix e.symm e.symm := by
    rw [hAB, neg_neg]; ext i j; simp
  have h2 : Mᵀ * Aᵀ * M.map c = Aᵀ := by
    have := congrArg Matrix.transpose hM
    rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc] at this
  rw [← Matrix.submatrix_map, hcc, Matrix.transpose_submatrix]
  conv_rhs => rw [hB]
  rw [hB, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.mul_neg, Matrix.neg_mul, h2]

/- English proof (translation)
Establish `hB : B = (-Aᵀ).submatrix e.symm e.symm`. Rewrite using `[hAB, neg_neg]`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[hB]`.

Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem symm_hyp {R : Type} [CommRing R] {m n : Type} (e : m ≃ n) (A : Matrix m m R) (B : Matrix n n R)
    (hAB : Aᵀ = -(B.submatrix e e)) : Bᵀ = -(A.submatrix e.symm e.symm) := by
  have hB : B = (-Aᵀ).submatrix e.symm e.symm := by
    rw [hAB, neg_neg]; ext i j; simp
  rw [hB]; ext i j; simp

def gmap {R : Type} [CommRing R] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (c : R →+* R) (e : m ≃ n) : GL m R →* GL n R :=
  (Units.map (Matrix.reindexAlgEquiv R R e).toRingEquiv.toRingHom.toMonoidHom).comp (GeneralLinearGroup.map c)

/- English proof (translation)
Use extensionality with `i j`. Establish `k` using `congrArg (fun X => incA D (X i j)) h`. Simplify `k` using `[GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.transpose_apply]`.
-/
theorem incM_hyp {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gramᵀ = -(W.gram.submatrix e e)) :
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM V.gram)ᵀ = -((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM W.gram).submatrix e e) := by
  ext i j
  have k := congrArg (fun X => incA D (X i j)) h
  simpa [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.transpose_apply] using k

end GlobalTheory.GrpConj

namespace GlobalTheory.GrpConj

variable {D : D7}

def fwd (V W : HSp D) (e : Fin V.rank ≃ Fin W.rank) (h : V.gramᵀ = -(W.gram.submatrix e e)) : GA D V →* GA D W where
  toFun g := show HR (AF D.host.F) D.sp.cm.sig W.gram from ⟨gmap (cA D) e (matHom V g), by
    show ((((mt V g).map (cA D)).submatrix e.symm e.symm).map (cA D))ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM W.gram *
      ((mt V g).map (cA D)).submatrix e.symm e.symm = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM W.gram
    exact conj_mem (cA D) Formalism.L2.Theta.cA_cA e _ _ (incM_hyp e h) _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mt_gram V g)⟩
  map_one' := by
    apply Subtype.ext
    show gmap (cA D) e (matHom V 1) = 1
    rw [map_one, map_one]
  map_mul' a b := by
    apply Subtype.ext
    show gmap (cA D) e (matHom V (a * b)) = gmap (cA D) e (matHom V a) * gmap (cA D) e (matHom V b)
    rw [map_mul, map_mul]

def conjEquiv (V W : HSp D) (e : Fin V.rank ≃ Fin W.rank) (h : V.gramᵀ = -(W.gram.submatrix e e)) : GA D V ≃* GA D W where
  toFun := fwd V W e h
  invFun := fwd W V e.symm (symm_hyp e _ _ h)
  left_inv g := by
    apply Subtype.ext; apply Units.ext; ext i j
    show cA D (cA D (mt V g (e.symm (e i)) (e.symm (e j)))) = mt V g i j
    rw [Formalism.L2.Theta.cA_cA]; simp
  right_inv g := by
    apply Subtype.ext; apply Units.ext; ext i j
    show cA D (cA D (mt W g (e (e.symm i)) (e (e.symm j)))) = mt W g i j
    rw [Formalism.L2.Theta.cA_cA]; simp
  map_mul' := (fwd V W e h).map_mul

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mt_conjEquiv (V W : HSp D) (e : Fin V.rank ≃ Fin W.rank) (h : V.gramᵀ = -(W.gram.submatrix e e)) (g : GA D V) :
    mt W (conjEquiv V W e h g) = ((mt V g).map (cA D)).submatrix e.symm e.symm := rfl

/- English proof (translation)
Establish `h1 : Continuous (matHom V)` using `continuous_subtype_val`. Use `Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _` and prove the remaining obligations. Conclude with `((Units.continuous_val.comp h1).matrix_map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D)).matrix_submatrix _ _`. Conclude with `((Units.continuous_coe_inv.comp h1).matrix_map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D)).matrix_submatrix _ _`.
-/
theorem continuous_conjEquiv (V W : HSp D) (e : Fin V.rank ≃ Fin W.rank) (h : V.gramᵀ = -(W.gram.submatrix e e)) :
    Continuous (conjEquiv V W e h) := by
  have h1 : Continuous (matHom V) := continuous_subtype_val
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact ((Units.continuous_val.comp h1).matrix_map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D)).matrix_submatrix _ _
  · exact ((Units.continuous_coe_inv.comp h1).matrix_map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D)).matrix_submatrix _ _

/- English proof (translation)
The claim follows from `Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)`.
-/
theorem inclR_inj : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

/- English proof (translation)
Take `⟨y, -, ey⟩` from `hγ`. Establish `e' : mt V γ = (y : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F` using `D.host.F) (AF D.host.F)) := (congrArg Units.val ey).symm`. Use `set Z := ((y : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (D.sp.cm.sig : D.host.E →+* D.host.E)).submatrix e.symm e.symm with hZdef`. Establish `hZ : mt W (conjEquiv V W e h γ) = Z.map (inclR (F` using `D.host.F) (AF D.host.F)) := by`. Rewrite using `[mt_conjEquiv, e']`.

Use extensionality with `i j`. Both sides reduce to the same expression. Use `⟨gmap (D.sp.cm.sig : D.host.E →+* D.host.E) e y, ?_, Units.ext ?_⟩` and prove the remaining obligations. Establish `hm` using `(conjEquiv V W e h γ).2`. Express the relevant statement in the definitionally equal form `Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mt W (conjEquiv V W e h γ)) * JR (AF D.host.F) W.gram * mt W (conjEquiv V W e h γ) = JR (AF D.host.F) W.gram at hm`.

Rewrite `hm` using `[hZ]`. Establish `hcT : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (Z.map (inclR (F` using `D.host.F) (AF D.host.F))) = (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Z).map (inclR (F := D.host.F) (AF D.host.F)) := by`. Use extensionality with `i j`. Both sides reduce to the same expression. Rewrite `hm` using `[hcT]`.

Use `show Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Z * W.gram * Z = W.gram`. Apply `Matrix.map_injective inclR_inj` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[Matrix.map_mul, Matrix.map_mul]`. Conclude with `hm`.

Conclude with `hZ.symm`.
-/
theorem rat_conjEquiv (V W : HSp D) (e : Fin V.rank ≃ Fin W.rank) (h : V.gramᵀ = -(W.gram.submatrix e e)) (γ : GA D V)
    (hγ : γ ∈ GQ V) : conjEquiv V W e h γ ∈ GQ W := by
  obtain ⟨y, -, ey⟩ := hγ
  have e' : mt V γ = (y : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (AF D.host.F)) :=
    (congrArg Units.val ey).symm
  set Z := ((y : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (D.sp.cm.sig : D.host.E →+* D.host.E)).submatrix
    e.symm e.symm with hZdef
  have hZ : mt W (conjEquiv V W e h γ) = Z.map (inclR (F := D.host.F) (AF D.host.F)) := by
    rw [mt_conjEquiv, e']; ext i j; rfl
  refine ⟨gmap (D.sp.cm.sig : D.host.E →+* D.host.E) e y, ?_, Units.ext ?_⟩
  · have hm := (conjEquiv V W e h γ).2
    change Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mt W (conjEquiv V W e h γ)) *
      JR (AF D.host.F) W.gram * mt W (conjEquiv V W e h γ) = JR (AF D.host.F) W.gram at hm
    rw [hZ] at hm
    have hcT : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (Z.map (inclR (F := D.host.F) (AF D.host.F))) =
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Z).map (inclR (F := D.host.F) (AF D.host.F)) := by
      ext i j; rfl
    rw [hcT] at hm
    show Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Z * W.gram * Z = W.gram
    apply Matrix.map_injective inclR_inj
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul]
    exact hm
  · exact hZ.symm

/- English proof (translation)
Introduce `i j`. Establish `k : (mt W (conjEquiv V W e h g) - 1) i j = cA D ((mt V g - 1) (e.symm i) (e.symm j))`. Rewrite using `[mt_conjEquiv]`. Simplify using `only [Matrix.sub_apply, Matrix.one_apply, Matrix.submatrix_apply, Matrix.map_apply, map_sub, EmbeddingLike.apply_eq_iff_eq]`. Apply the tactic sequence `split_ifs <;> simp`.

Rewrite using `[k]`. Use `congrArg (cA D) (hs (e.symm i) (e.symm j))` as an intermediate fact. Rewrite `this` using `[map_mul, map_add, Formalism.L2.Theta.cA_cA, add_comm]`. Conclude with `this`.
-/
theorem suppAt_conjEquiv (V W : HSp D) (e : Fin V.rank ≃ Fin W.rank) (h : V.gramᵀ = -(W.gram.submatrix e e)) (a : AE D)
    (g : GA D V) (hs : SuppAt a V g) : SuppAt a W (conjEquiv V W e h g) := by
  intro i j
  have k : (mt W (conjEquiv V W e h g) - 1) i j = cA D ((mt V g - 1) (e.symm i) (e.symm j)) := by
    rw [mt_conjEquiv]
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.submatrix_apply, Matrix.map_apply, map_sub,
      EmbeddingLike.apply_eq_iff_eq]
    split_ifs <;> simp
  rw [k]
  have := congrArg (cA D) (hs (e.symm i) (e.symm j))
  rw [map_mul, map_add, Formalism.L2.Theta.cA_cA, add_comm] at this
  exact this

/- English proof (translation)
Rewrite using `[mt_conjEquiv, Matrix.det_submatrix_equiv_self, GlobalTheory.ConjAdjWeil.det_inv_eq]`. Conclude with `(RingHom.map_det (cA D) _).symm`.
-/
theorem det_conjEquiv (V W : HSp D) (e : Fin V.rank ≃ Fin W.rank) (h : V.gramᵀ = -(W.gram.submatrix e e)) (g : GA D V) :
    (mt W (conjEquiv V W e h g)).det = (mt V g⁻¹).det := by
  rw [mt_conjEquiv, Matrix.det_submatrix_equiv_self, GlobalTheory.ConjAdjWeil.det_inv_eq]
  exact (RingHom.map_det (cA D) _).symm

/- English proof (translation)
Introduce `D S T' e₁ h`. Use `⟨conjEquiv T' S e₁ h, continuous_conjEquiv T' S e₁ h, rat_conjEquiv T' S e₁ h, fun g => ?_, fun a g hs => suppAt_conjEquiv T' S e₁ h a g hs, det_conjEquiv T' S e₁ h⟩` and prove the remaining obligations. Rewrite using `[mt_conjEquiv]`. Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem exists_conj_equiv : ∀ (D : D7) (S T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank), T'.gramᵀ = -(S.gram.submatrix e₁ e₁) →
    ∃ φ' : GA D T' ≃* GA D S, Continuous φ' ∧ (∀ γ ∈ GQ T', φ' γ ∈ GQ S) ∧
      (∀ h, (Formalism.L2.Theta.mt S (φ' h)).submatrix e₁ e₁ = (Formalism.L2.Theta.mt T' h).map (cA D)) ∧
      (∀ e h, SuppAt e T' h → SuppAt e S (φ' h)) ∧ ∀ h, (Formalism.L2.Theta.mt S (φ' h)).det = (Formalism.L2.Theta.mt T' h⁻¹).det := by
  intro D S T' e₁ h
  refine ⟨conjEquiv T' S e₁ h, continuous_conjEquiv T' S e₁ h, rat_conjEquiv T' S e₁ h, fun g => ?_,
    fun a g hs => suppAt_conjEquiv T' S e₁ h a g hs, det_conjEquiv T' S e₁ h⟩
  rw [mt_conjEquiv]; ext i j; simp

end GlobalTheory.GrpConj

end
