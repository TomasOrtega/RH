import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTamagawa
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulVecMemGenLatSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocHomVal

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published

namespace GlobalTheory.TamCnt.PlaceComp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {M : ℕ}

/- English proof (translation)
The claim follows from `RestrictedProduct.ext _ _ h`.
-/
theorem af_ext {a b : Af F} (h : ∀ w, evalV F w a = evalV F w b) : a = b :=
  RestrictedProduct.ext _ _ h

def singleLin (v : HeightOneSpectrum (𝓞 F)) : Fv F v →ₗ[F] Af F where
  toFun := singleV F v
  map_add' x y := af_ext fun w => by
    by_cases hw : w = v
    · subst hw; simp only [map_add, StrongApprox.evalV_single_same]
    · simp only [map_add, StrongApprox.evalV_single_ne hw, add_zero]
  map_smul' c y := af_ext fun w => by
    by_cases hw : w = v
    · subst hw; simp only [map_smul, StrongApprox.evalV_single_same, RingHom.id_apply]
    · simp only [map_smul, StrongApprox.evalV_single_ne hw, RingHom.id_apply, smul_zero]

def sTen (v : HeightOneSpectrum (𝓞 F)) : Fv F v ⊗[F] E →ₗ[F] Af F ⊗[F] E :=
  TensorProduct.map (singleLin v) LinearMap.id

abbrev piV (v : HeightOneSpectrum (𝓞 F)) : Af F ⊗[F] E →ₐ[F] Fv F v ⊗[F] E :=
  Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b`. Simplify using `[sTen, singleLin, Algebra.TensorProduct.map_tmul, StrongApprox.evalV_single_same]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem piV_sTen (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v ⊗[F] E) : piV v (sTen v x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp [sTen, singleLin, Algebra.TensorProduct.map_tmul, StrongApprox.evalV_single_same]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
Introduce `w` and use `by by_cases hw : w = v · subst hw; rw [StrongApprox.evalV_single_same]; exact ha · rw [StrongApprox.evalV_single_ne hw]; exact zero_mem _`.
-/
theorem singleV_mem_intAf (v : HeightOneSpectrum (𝓞 F)) {a : Fv F v} (ha : a ∈ v.adicCompletionIntegers F) :
    singleV F v a ∈ intAf F := fun w => by
  by_cases hw : w = v
  · subst hw; rw [StrongApprox.evalV_single_same]; exact ha
  · rw [StrongApprox.evalV_single_ne hw]; exact zero_mem _

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, x, hx, rfl⟩` from `hz`. Conclude with `AddSubgroup.subset_closure ⟨evalV F v a, ha v, x, hx, by funext i; simp⟩`. Consider the case `zero`.

Establish `e : (fun i => piV v ((0 : Fin M → Af F ⊗[F] E) i)) = 0` using `by funext i; simp`. Rewrite using `[e]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy`. Establish `e : (fun i => piV v ((x + y) i)) = (fun i => piV v (x i)) + fun i => piV v (y i)`.

Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx`.

Establish `e : (fun i => piV v ((-x) i)) = -fun i => piV v (x i)` using `by funext i; simp`. Rewrite using `[e]`. Conclude with `neg_mem hx`.
-/
theorem piV_mem_compLat (v : HeightOneSpectrum (𝓞 F)) (L : Set (Fin M → E)) {z : Fin M → Af F ⊗[F] E}
    (hz : z ∈ latHat F E L) : (fun i => piV v (z i)) ∈ compLat v L := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨evalV F v a, ha v, x, hx, by funext i; simp⟩
  | zero =>
    have e : (fun i => piV v ((0 : Fin M → Af F ⊗[F] E) i)) = 0 := by funext i; simp
    rw [e]; exact zero_mem _
  | add x y _ _ hx hy =>
    have e : (fun i => piV v ((x + y) i)) = (fun i => piV v (x i)) + fun i => piV v (y i) := by
      funext i; simp
    rw [e]; exact add_mem hx hy
  | neg x _ hx =>
    have e : (fun i => piV v ((-x) i)) = -fun i => piV v (x i) := by funext i; simp
    rw [e]; exact neg_mem hx

/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, x, hx, rfl⟩` from `hz`. Conclude with `AddSubgroup.subset_closure ⟨singleV F v a, singleV_mem_intAf v ha, x, hx, by`. Use function extensionality and compare the values at `i`.

Simplify using `[sTen, singleLin]⟩`. Consider the case `zero`. Establish `e : (fun i => sTen v ((0 : Fin M → Fv F v ⊗[F] E) i)) = 0` using `by funext i; simp`. Rewrite using `[e]`. Conclude with `zero_mem _`.

Consider the case `add x y _ _ hx hy`. Establish `e : (fun i => sTen v ((x + y) i)) = (fun i => sTen v (x i)) + fun i => sTen v (y i)`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Rewrite using `[e]`.

Conclude with `add_mem hx hy`. Consider the case `neg x _ hx`. Establish `e : (fun i => sTen v ((-x) i)) = -fun i => sTen v (x i)` using `by funext i; simp`. Rewrite using `[e]`. Conclude with `neg_mem hx`.
-/
theorem sTen_mem_latHat (v : HeightOneSpectrum (𝓞 F)) (L : Set (Fin M → E)) {y : Fin M → Fv F v ⊗[F] E}
    (hy : y ∈ compLat v L) : (fun i => sTen v (y i)) ∈ latHat F E L := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨singleV F v a, singleV_mem_intAf v ha, x, hx, by
      funext i; simp [sTen, singleLin]⟩
  | zero =>
    have e : (fun i => sTen v ((0 : Fin M → Fv F v ⊗[F] E) i)) = 0 := by funext i; simp
    rw [e]; exact zero_mem _
  | add x y _ _ hx hy =>
    have e : (fun i => sTen v ((x + y) i)) = (fun i => sTen v (x i)) + fun i => sTen v (y i) := by
      funext i; simp
    rw [e]; exact add_mem hx hy
  | neg x _ hx =>
    have e : (fun i => sTen v ((-x) i)) = -fun i => sTen v (x i) := by funext i; simp
    rw [e]; exact neg_mem hx

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `RingHom.map_mulVec (piV (E := E) v).toRingHom m (fun j => sTen v (y j)) i` as an intermediate fact. Simplify using `only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this`. Rewrite using `[this]`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Simplify using `[piV_sTen]`.
-/
theorem map_mulVec_eq (v : HeightOneSpectrum (𝓞 F)) (m : Matrix (Fin M) (Fin M) (Af F ⊗[F] E))
    (y : Fin M → Fv F v ⊗[F] E) :
    m.map (piV v) *ᵥ y = fun i => piV v ((m *ᵥ fun j => sTen v (y j)) i) := by
  funext i
  have := RingHom.map_mulVec (piV (E := E) v).toRingHom m (fun j => sTen v (y j)) i
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
  rw [this]
  congr 1
  funext j
  simp [piV_sTen]

/- English proof (translation)
Rewrite using `[map_mulVec_eq]`. Conclude with `piV_mem_compLat v L' (hm _ (sTen_mem_latHat v L hy))`.
-/
theorem map_mulVec_mem (v : HeightOneSpectrum (𝓞 F)) (L L' : Set (Fin M → E))
    (m : Matrix (Fin M) (Fin M) (Af F ⊗[F] E)) (hm : ∀ z ∈ latHat F E L, m *ᵥ z ∈ latHat F E L')
    {y : Fin M → Fv F v ⊗[F] E} (hy : y ∈ compLat v L) : m.map (piV v) *ᵥ y ∈ compLat v L' := by
  rw [map_mulVec_eq]
  exact piV_mem_compLat v L' (hm _ (sTen_mem_latHat v L hy))

end GlobalTheory.TamCnt.PlaceComp

namespace GlobalTheory.TamCnt.PlaceComp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {M : ℕ}

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [compV, sigR, Algebra.TensorProduct.map_tmul]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]`.
-/
theorem compV_sigR (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : AF F ⊗[F] E) :
    compV v (sigR (AF F) σ x) = sigR (Fv F v) σ (compV v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [compV, sigR, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/- English proof (translation)
Simplify using `[compV, inclR, Algebra.TensorProduct.map_tmul]`.
-/
theorem compV_inclR (v : HeightOneSpectrum (𝓞 F)) (x : E) :
    compV v (inclR (AF F) x) = inclR (F := F) (Fv F v) x := by
  simp [compV, inclR, Algebra.TensorProduct.map_tmul]

end GlobalTheory.TamCnt.PlaceComp

namespace GlobalTheory.TamCnt

open PlaceComp in

/- English proof (translation)
Use `set A : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) := ((HA.mat (AF F) σ J h.1 : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) with hA`. Use `set c : AF F ⊗[F] E →+* Fv F v ⊗[F] E := (compV (E := E) v).toRingHom with hc`. Establish `hval' : ((locHom σ J v h : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) = A.map c` using `rfl`. Establish `hval` using `locHom_val σ J v h`. Establish `fwd : ∀ g : GlobalTheory.Published.SUAdelic σ J, g ∈ congG σ J Λ v k → ∀ y ∈ compLat v (Λ : Set (Fin M → E)), ((locHom σ J v g : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) *ᵥ y ∈ compLat v (Λ : Set (Fin M → E))`.

Introduce `g hg y hy`. Rewrite using `[locHom_val]`. Conclude with `map_mulVec_mem v _ _ _ (fun z hz => (hg.1 z).1 hz) hy`. Use `⟨?_, ?_, fun y => ⟨fwd h hh y, fun hy => ?_⟩, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hm : Formalism.UG.cT (sigR (AF F) σ) A * JR (AF F) J * A = JR (AF F) J` using `(show HR (AF F) σ J from h.1).2`.

Use `show Formalism.UG.cT (sigR (Fv F v) σ) _ * JR (Fv F v) J * _ = JR (Fv F v) J`. Rewrite using `[hval']`. Establish `key` using `congrArg (fun X => X.map c) hm`. Simplify using `only [Matrix.map_mul] at key`. Establish `e1 : (Formalism.UG.cT (sigR (AF F) σ) A).map c = Formalism.UG.cT (sigR (Fv F v) σ) (A.map c)`.

Use extensionality with `i j`. Simplify using `only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, hc, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]`. Conclude with `compV_sigR σ v _`. Establish `e2 : (JR (AF F) J).map c = JR (Fv F v) J`. Use extensionality with `i j`.

Simplify using `only [JR, Matrix.map_apply, hc, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]`. Conclude with `compV_inclR v _`. Rewrite `key` using `[e1, e2]`. Conclude with `key`. Rewrite using `[hval', ← RingHom.mapMatrix_apply, ← RingHom.map_det, StrongApprox.mem_SUAdelic.1 h.2, map_one]`.

Establish `h2` using `fwd h⁻¹ (inv_mem hh) _ hy`. Rewrite `h2` using `[Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec]`. Then use the resulting hypothesis. Establish `e : ((locHom σ J v h : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) - 1 = (finMat σ J h.1 - 1).map (piV v)`. Rewrite using `[hval]`. Express the relevant statement in the definitionally equal form `_ = (piV (E := E) v).toRingHom.mapMatrix (finMat σ J h.1 - 1)`.

Rewrite using `[map_sub, map_one]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `map_mulVec_mem v _ _ _ hh.2 hy`.
-/
theorem locHom_mem_locCong (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (Λ : Submodule (𝓞 E) (Fin M → E))
    (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) (h : GlobalTheory.Published.SUAdelic σ J) (hh : h ∈ congG σ J Λ v k) :
    locHom σ J v h ∈ locCong σ J Λ v k := by
  set A : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) :=
    ((HA.mat (AF F) σ J h.1 : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) with hA
  set c : AF F ⊗[F] E →+* Fv F v ⊗[F] E := (compV (E := E) v).toRingHom with hc
  have hval' : ((locHom σ J v h : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) =
      A.map c := rfl
  have hval := locHom_val σ J v h

  have fwd : ∀ g : GlobalTheory.Published.SUAdelic σ J, g ∈ congG σ J Λ v k → ∀ y ∈ compLat v (Λ : Set (Fin M → E)),
      ((locHom σ J v g : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) *ᵥ y ∈
        compLat v (Λ : Set (Fin M → E)) := by
    intro g hg y hy
    rw [locHom_val]
    exact map_mulVec_mem v _ _ _ (fun z hz => (hg.1 z).1 hz) hy
  refine ⟨?_, ?_, fun y => ⟨fwd h hh y, fun hy => ?_⟩, fun y hy => ?_⟩
  ·
    have hm : Formalism.UG.cT (sigR (AF F) σ) A * JR (AF F) J * A = JR (AF F) J := (show HR (AF F) σ J from h.1).2
    show Formalism.UG.cT (sigR (Fv F v) σ) _ * JR (Fv F v) J * _ = JR (Fv F v) J
    rw [hval']
    have key := congrArg (fun X => X.map c) hm
    simp only [Matrix.map_mul] at key
    have e1 : (Formalism.UG.cT (sigR (AF F) σ) A).map c = Formalism.UG.cT (sigR (Fv F v) σ) (A.map c) := by
      ext i j
      simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, hc, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      exact compV_sigR σ v _
    have e2 : (JR (AF F) J).map c = JR (Fv F v) J := by
      ext i j
      simp only [JR, Matrix.map_apply, hc, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      exact compV_inclR v _
    rw [e1, e2] at key
    exact key
  ·
    rw [hval', ← RingHom.mapMatrix_apply, ← RingHom.map_det, StrongApprox.mem_SUAdelic.1 h.2, map_one]
  ·
    have h2 := fwd h⁻¹ (inv_mem hh) _ hy
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      Matrix.one_mulVec] at h2
  ·
    have e : ((locHom σ J v h : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) - 1 =
        (finMat σ J h.1 - 1).map (piV v) := by
      rw [hval]
      change _ = (piV (E := E) v).toRingHom.mapMatrix (finMat σ J h.1 - 1)
      rw [map_sub, map_one]
      rfl
    rw [e]
    exact map_mulVec_mem v _ _ _ hh.2 hy

end GlobalTheory.TamCnt
