import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartFPlaceIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2

noncomputable section

open scoped TensorProduct Matrix BoundedContinuousFunction
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix

namespace GlobalTheory.RealWeilF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Top

variable (F E) in
/- English proof (translation)
Assemble the required witnesses or components as `⟨rfl⟩`.
-/
theorem isModuleTopology_AE : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩

variable (F E) in
/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI := isModuleTopology_AE F E`. Conclude with `IsModuleTopology.isTopologicalRing (AF F) _`.
-/
theorem isTopologicalRing_AE : IsTopologicalRing (AF F ⊗[F] E) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := isModuleTopology_AE F E
  exact IsModuleTopology.isTopologicalRing (AF F) _

instance instTopRingAE : IsTopologicalRing (AF F ⊗[F] E) := isTopologicalRing_AE F E

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI := isModuleTopology_AE F E`. Set `l : (AF F ⊗[F] E) →ₗ[AF F] (AF F ⊗[F] E)` to `(Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ).toLinearMap`. Establish `e : (cAF (F` using `F) σ : AF F ⊗[F] E → AF F ⊗[F] E) = l := by`. Use function extensionality and compare the values at `z`.

Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e => rfl`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`. Rewrite using `[e]`.

Conclude with `IsModuleTopology.continuous_of_linearMap l`.
-/
theorem continuous_cAF (σ : E →ₐ[F] E) : Continuous (cAF (F := F) σ) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := isModuleTopology_AE F E
  let l : (AF F ⊗[F] E) →ₗ[AF F] (AF F ⊗[F] E) :=
    (Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ).toLinearMap
  have e : (cAF (F := F) σ : AF F ⊗[F] E → AF F ⊗[F] E) = l := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [e]
  exact IsModuleTopology.continuous_of_linearMap l

variable (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (xi0 : E)

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI := isModuleTopology_AE F E`. Establish `hy' : ∀ i j, Continuous fun t => cAF σ (y t i j)` using `fun i j => (continuous_cAF σ).comp ((continuous_apply j).comp ((continuous_apply i).comp hy))`. Establish `hx' : ∀ i j, Continuous fun t => x t i j` using `fun i j => (continuous_apply j).comp ((continuous_apply i).comp hx)`. Establish `hh : Continuous fun t => hOF σ JS JT (x t) (y t)` using `continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ => ((continuous_const.mul (hy' _ _)).mul continuous_const).mul (hx' _ _)`.

Establish `ht : Continuous (Algebra.trace (AF F) (AEF F E))` using `IsModuleTopology.continuous_of_linearMap _`. Conclude with `continuous_const.mul (ht.comp (continuous_const.mul hh))`.
-/
theorem continuous_symplOHF {X : Type} [TopologicalSpace X] {x y : X → WOF F E nS nT} (hx : Continuous x)
    (hy : Continuous y) : Continuous fun t => symplOHF σ JS JT xi0 (x t) (y t) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := isModuleTopology_AE F E
  have hy' : ∀ i j, Continuous fun t => cAF σ (y t i j) := fun i j =>
    (continuous_cAF σ).comp ((continuous_apply j).comp ((continuous_apply i).comp hy))
  have hx' : ∀ i j, Continuous fun t => x t i j := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp hx)
  have hh : Continuous fun t => hOF σ JS JT (x t) (y t) :=
    continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ =>
      continuous_finsetSum _ fun _ _ => ((continuous_const.mul (hy' _ _)).mul continuous_const).mul (hx' _ _)
  have ht : Continuous (Algebra.trace (AF F) (AEF F E)) := IsModuleTopology.continuous_of_linearMap _
  exact continuous_const.mul (ht.comp (continuous_const.mul hh))

end Top

section Form

variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {xi0 : E}

/- English proof (translation)
Simplify using `only [symplOHF, symplOF, hOF, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add]`.
-/
theorem symplOHF_add_left (x x' y : WOF F E nS nT) :
    symplOHF σ JS JT xi0 (x + x') y = symplOHF σ JS JT xi0 x y + symplOHF σ JS JT xi0 x' y := by
  simp only [symplOHF, symplOF, hOF, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add]

/- English proof (translation)
Simplify using `only [symplOHF, symplOF, hOF, Matrix.add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]`.
-/
theorem symplOHF_add_right (x y y' : WOF F E nS nT) :
    symplOHF σ JS JT xi0 x (y + y') = symplOHF σ JS JT xi0 x y + symplOHF σ JS JT xi0 x y' := by
  simp only [symplOHF, symplOF, hOF, Matrix.add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]

variable {ψ : AddChar (AF F) ℂ}

/- English proof (translation)
Use function extensionality and compare the values at `u`. Simplify using `only [heisOF, Pi.smul_apply, smul_eq_mul, symplOHF_add_left, symplOHF_add_right, AddChar.map_add_eq_mul, add_assoc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem heisOF_heisOF (w w' : WOF F E nS nT) (f : WOF F E nS nT → ℂ) :
    heisOF σ JS JT xi0 ψ w (heisOF σ JS JT xi0 ψ w' f) =
      ψ (symplOHF σ JS JT xi0 w w') • heisOF σ JS JT xi0 ψ (w + w') f := by
  funext u
  simp only [heisOF, Pi.smul_apply, smul_eq_mul, symplOHF_add_left, symplOHF_add_right, AddChar.map_add_eq_mul,
    add_assoc]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `u`. Establish `: symplOHF σ JS JT xi0 u 0 = 0` using `by simp [symplOHF, symplOF, hOF]`. Simplify using `[heisOF, this]`.
-/
theorem heisOF_zero (f : WOF F E nS nT → ℂ) : heisOF σ JS JT xi0 ψ 0 f = f := by
  funext u
  have : symplOHF σ JS JT xi0 u 0 = 0 := by simp [symplOHF, symplOF, hOF]
  simp [heisOF, this]

/- English proof (translation)
Simplify using `only [heisOF]`. Rewrite using `[add_assoc, hf, symplOHF_add_left, symplOHF_add_right, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem heisOF_quasi (w₀ : WOF F E nS nT) (f : WOF F E nS nT → ℂ)
    (hf : ∀ γ w, f (ratWF γ + w) = ψ (-(symplOHF σ JS JT xi0 (ratWF γ) w)) * f w) (γ w) :
    heisOF σ JS JT xi0 ψ w₀ f (ratWF γ + w) = ψ (-(symplOHF σ JS JT xi0 (ratWF γ) w)) * heisOF σ JS JT xi0 ψ w₀ f w := by
  simp only [heisOF]
  rw [add_assoc, hf, symplOHF_add_left, symplOHF_add_right, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul,
    ← AddChar.map_add_eq_mul]
  congr 2
  ring

/- English proof (translation)
Simplify using `only [heisOF, norm_mul, hψ.2.1, one_mul]`.
-/
theorem norm_heisOF (hψ : IsCharAF F ψ) (f : WOF F E nS nT → ℂ) (u w : WOF F E nS nT) :
    ‖heisOF σ JS JT xi0 ψ u f w‖ = ‖f (w + u)‖ := by
  simp only [heisOF, norm_mul, hψ.2.1, one_mul]

end Form

section Quasi

open GlobalTheory.RealWeil

variable (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (xi0 : E)
  (ψ : AddChar (AF F) ℂ)

abbrev BBF : Submodule ℂ (WOF F E nS nT →ᵇ ℂ) :=
  QB (ratWF (F := F) (E := E) (nS := nS) (nT := nT)) fun γ w => ψ (-(symplOHF σ JS JT xi0 (ratWF γ) w))

def rhoBF (hψ : IsCharAF F ψ) (w : WOF F E nS nT) : BBF σ JS JT xi0 ψ →L[ℂ] BBF σ JS JT xi0 ψ :=
  trB (fun x => ψ (symplOHF σ JS JT xi0 x w)) w
    (hψ.1.comp (continuous_symplOHF σ JS JT xi0 continuous_id continuous_const)) (fun _ => hψ.2.1 _)
    fun f hf => heisOF_quasi (ψ := ψ) w f hf

variable {σ JS JT xi0 ψ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_rhoBF (hψ : IsCharAF F ψ) (w : WOF F E nS nT) (f : BBF σ JS JT xi0 ψ) :
    ((rhoBF σ JS JT xi0 ψ hψ w f).1 : WOF F E nS nT → ℂ) = heisOF σ JS JT xi0 ψ w f.1 := rfl

/- English proof (translation)
Use `le_antisymm (norm_QB_le _ (norm_nonneg _) fun x => ?_) (norm_QB_le _ (norm_nonneg _) fun x => ?_)` and prove the remaining obligations. Rewrite using `[coe_rhoBF, norm_heisOF hψ]`. Conclude with `norm_ev_le _ f`. Use `norm_ev_le (x - w) (rhoBF σ JS JT xi0 ψ hψ w f)` as an intermediate fact. Rewrite `this` using `[coe_rhoBF, norm_heisOF hψ, sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem norm_rhoBF (hψ : IsCharAF F ψ) (w : WOF F E nS nT) (f : BBF σ JS JT xi0 ψ) :
    ‖rhoBF σ JS JT xi0 ψ hψ w f‖ = ‖f‖ := by
  refine le_antisymm (norm_QB_le _ (norm_nonneg _) fun x => ?_) (norm_QB_le _ (norm_nonneg _) fun x => ?_)
  · rw [coe_rhoBF, norm_heisOF hψ]; exact norm_ev_le _ f
  · have := norm_ev_le (x - w) (rhoBF σ JS JT xi0 ψ hψ w f)
    rwa [coe_rhoBF, norm_heisOF hψ, sub_add_cancel] at this

/- English proof (translation)
The claim follows from `QB_ext fun x => congrFun (heisOF_heisOF w w' f.1) x`.
-/
theorem rhoBF_rhoBF (hψ : IsCharAF F ψ) (w w' : WOF F E nS nT) (f : BBF σ JS JT xi0 ψ) :
    rhoBF σ JS JT xi0 ψ hψ w (rhoBF σ JS JT xi0 ψ hψ w' f) =
      ψ (symplOHF σ JS JT xi0 w w') • rhoBF σ JS JT xi0 ψ hψ (w + w') f :=
  QB_ext fun x => congrFun (heisOF_heisOF w w' f.1) x

/- English proof (translation)
The claim follows from `QB_ext fun x => congrFun (heisOF_zero f.1) x`.
-/
theorem rhoBF_zero (hψ : IsCharAF F ψ) (f : BBF σ JS JT xi0 ψ) : rhoBF σ JS JT xi0 ψ hψ 0 f = f :=
  QB_ext fun x => congrFun (heisOF_zero f.1) x

/- English proof (translation)
Introduce and unpack `_ ⟨γ, rfl⟩ w`. Use `congrArg norm (f.2 γ w)` as an intermediate fact. Rewrite `this` using `[norm_mul, hψ.2.1, one_mul]`. Conclude with `this`.
-/
theorem BBF_norm_periodic (hψ : IsCharAF F ψ) (f : BBF σ JS JT xi0 ψ) :
    ∀ γ ∈ ratLF F E nS nT, ∀ w, ‖f.1 (γ + w)‖ = ‖f.1 w‖ := by
  rintro _ ⟨γ, rfl⟩ w
  have := congrArg norm (f.2 γ w)
  rw [norm_mul, hψ.2.1, one_mul] at this
  exact this

end Quasi

section Coord

variable (F E) in

abbrev IxF (nS nT : ℕ) : Type := (Fin nT × Fin nS) × InfinitePlace F

structure IsChartF (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)) (ι : (InfinitePlace F → ℂ) →+ AEF F E) : Prop where
  cont : Continuous ι
  fin : ∀ z, finPartF F E (ι z) = 0
  comp : ∀ z w, θ w (infPartF F E (ι z)) = z w
  ext : ∀ a : AEF F E, finPartF F E a = 0 → (∀ w, θ w (infPartF F E a) = 0) → a = 0

def iotaVF {nS nT : ℕ} (ι : (InfinitePlace F → ℂ) →+ AEF F E) (v : IxF F nS nT → ℂ) : WOF F E nS nT :=
  Matrix.of fun i j => ι fun w => v ((i, j), w)

def piWF {nS nT : ℕ} (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)) (x : WOF F E nS nT) : IxF F nS nT → ℂ :=
  fun p => θ p.2 (infPartF F E (x p.1.1 p.1.2))

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [iotaVF, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]`. Rewrite using `[← map_add]`. Both sides reduce to the same expression.
-/
theorem iotaVF_add {nS nT : ℕ} (ι : (InfinitePlace F → ℂ) →+ AEF F E) (v v' : IxF F nS nT → ℂ) :
    iotaVF ι (v + v') = iotaVF ι v + iotaVF ι v' := by
  ext i j
  simp only [iotaVF, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  rw [← map_add]
  rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [iotaVF, Matrix.of_apply, Matrix.zero_apply]`. Conclude with `map_zero ι`.
-/
theorem iotaVF_zero {nS nT : ℕ} (ι : (InfinitePlace F → ℂ) →+ AEF F E) : iotaVF ι (0 : IxF F nS nT → ℂ) = 0 := by
  ext i j
  simp only [iotaVF, Matrix.of_apply, Matrix.zero_apply]
  exact map_zero ι

variable (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (xi0 : E)
  (ψ : AddChar (AF F) ℂ)

def rhoVF (hψ : IsCharAF F ψ) (ι : (InfinitePlace F → ℂ) →+ AEF F E) (v : IxF F nS nT → ℂ) :
    BBF σ JS JT xi0 ψ →L[ℂ] BBF σ JS JT xi0 ψ :=
  rhoBF σ JS JT xi0 ψ hψ (iotaVF ι v)

open Classical in

def HMF (tau : InfinitePlace F → (E →+* ℂ)) : Matrix (IxF F nS nT) (IxF F nS nT) ℂ :=
  GlobalTheory.RealWeil.blk (fun w => ((2 * (tau w xi0).im : ℝ) : ℂ) • JT.map (tau w)) fun w => (JS.map (tau w))⁻¹

def compAtF (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)) (w : InfinitePlace F) {m n : ℕ}
    (x : Matrix (Fin m) (Fin n) (AEF F E)) : Matrix (Fin m) (Fin n) ℂ :=
  x.map ((θ w).comp (infPartF F E))

open Classical in

def mMF (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)) :
    GAF σ JS × GAF σ JT →* Matrix (IxF F nS nT) (IxF F nS nT) ℂ where
  toFun p := GlobalTheory.RealWeil.blk (fun w => compAtF θ w (mtF σ JT p.2)) fun w => compAtF θ w (mtF σ JS p.1⁻¹)
  map_one' := by
    have h1 : ∀ {n : ℕ} (J : Matrix (Fin n) (Fin n) E) w, compAtF θ w (mtF σ J 1) = 1 := by
      intro n J w
      have : mtF σ J 1 = 1 := by unfold mtF; rw [map_one]; rfl
      rw [compAtF, this, Matrix.map_one _ (map_zero _) (map_one _)]
    simp only [Prod.snd_one, Prod.fst_one, inv_one, h1]
    exact GlobalTheory.RealWeil.blk_one
  map_mul' p q := by
    have h1 : ∀ {n : ℕ} (J : Matrix (Fin n) (Fin n) E) w (g g' : GAF σ J),
        compAtF θ w (mtF σ J (g * g')) = compAtF θ w (mtF σ J g) * compAtF θ w (mtF σ J g') := by
      intro n J w g g'
      rw [compAtF, GlobalTheory.WeilPartsF.mtF_mul, Matrix.map_mul]
      rfl
    rw [GlobalTheory.RealWeil.blk_mul]
    simp only [Prod.snd_mul, Prod.fst_mul, _root_.mul_inv_rev, h1]

open Classical in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mMF_apply (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)) (g : GAF σ JS) (h : GAF σ JT) :
    mMF σ JS JT θ (g, h) =
      GlobalTheory.RealWeil.blk (fun w => compAtF θ w (mtF σ JT h)) fun w => compAtF θ w (mtF σ JS g⁻¹) := rfl

end Coord

section Helpers

open GlobalTheory.RealWeil

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
  {ψ : AddChar (AF F) ℂ}

noncomputable def toBF (f : WOF F E nS nT → ℂ) (hc : Continuous f) (hb : ∃ C, ∀ x, ‖f x‖ ≤ C)
    (hq : ∀ γ w, f (ratWF γ + w) = ψ (-(symplOHF σ JS JT ξ₀ (ratWF γ) w)) * f w) : BBF σ JS JT ξ₀ ψ :=
  mkB f hc hb hq

/- English proof (translation)
The claim follows from `continuous_pi fun i => continuous_pi fun j => hι.cont.comp (continuous_pi fun w => continuous_apply _)`.
-/
theorem continuous_iotaVF {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
    (hι : IsChartF θ ι) : Continuous (iotaVF (nS := nS) (nT := nT) ι) :=
  continuous_pi fun i => continuous_pi fun j => hι.cont.comp (continuous_pi fun w => continuous_apply _)

/- English proof (translation)
Use extensionality with `i j`. Conclude with `hι.fin _`.
-/
theorem real_iotaVF {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
    (hι : IsChartF θ ι) (v : IxF F nS nT → ℂ) : (iotaVF ι v).map (finPartF F E) = 0 := by
  ext i j
  exact hι.fin _

/- English proof (translation)
Unfold `actOF`. Rewrite using `[Matrix.mul_add, Matrix.add_mul]`.
-/
theorem actOF_add (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    actOF σ JS JT g h (x + y) = actOF σ JS JT g h x + actOF σ JS JT g h y := by
  unfold actOF
  rw [Matrix.mul_add, Matrix.add_mul]

/- English proof (translation)
Establish `h1 : (mtF σ J g).map (infPartF F E) = 1` using `congrArg Units.val (MonoidHom.mem_ker.1 hg)`. Establish `h2 : compAtF θ w (mtF σ J g) = ((mtF σ J g).map (infPartF F E)).map (θ w)` using `rfl`. Rewrite using `[h2, h1, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem compAtF_fin (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : GAF σ J}
    (hg : g ∈ GlobalTheory.WeilPartsF.GfCF σ J) (w : InfinitePlace F) : compAtF θ w (mtF σ J g) = 1 := by
  have h1 : (mtF σ J g).map (infPartF F E) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hg)
  have h2 : compAtF θ w (mtF σ J g) = ((mtF σ J g).map (infPartF F E)).map (θ w) := rfl
  rw [h2, h1, Matrix.map_one _ (map_zero _) (map_one _)]

open Classical in
/- English proof (translation)
Rewrite using `[mMF_apply]`. Simplify using `only [compAtF_fin θ hh, compAtF_fin θ (inv_mem hg)]`. Conclude with `blk_one`.
-/
theorem mMF_fin (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)) {g : GAF σ JS} {h : GAF σ JT}
    (hg : g ∈ GlobalTheory.WeilPartsF.GfCF σ JS) (hh : h ∈ GlobalTheory.WeilPartsF.GfCF σ JT) : mMF σ JS JT θ (g, h) = 1 := by
  rw [mMF_apply]
  simp only [compAtF_fin θ hh, compAtF_fin θ (inv_mem hg)]
  exact blk_one

/- English proof (translation)
Set `toB : ∀ f, IsThetaFunOF σ JS JT ξ₀ ψ f → BBF σ JS JT ξ₀ ψ` to `fun f hf => toBF f hf.cont (hbd f hf) hf.quasi`. Establish `coe_toB : ∀ f hf, ((toB f hf).1 : WOF F E nS nT → ℂ) = f` using `fun _ _ => rfl`. Establish `ht : ∀ f : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ, IsThetaFunOF σ JS JT ξ₀ ψ (toB f.1 f.2).1` using `fun f => f.2`. Establish `hb : ∀ (x : BBF σ JS JT ξ₀ ψ) (hx : IsThetaFunOF σ JS JT ξ₀ ψ x.1), toB x.1 hx = x` using `fun x hx => QB_ext fun _ => rfl`. Set `w : G → Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ)` to `fun p => { toFun := fun f => ⟨(Ω p (toB f.1 f.2)).1, hth p _ (ht f)⟩ map_add' := fun f g => by`.

Establish `e : toB (f + g).1 (f + g).2 = toB f.1 f.2 + toB g.1 g.2` using `QB_ext fun x => rfl`. Use `Subtype.ext ?_` and prove the remaining obligations. Simplify using `only [e, hadd p _ _ (ht f) (ht g)]`. Both sides reduce to the same expression. Use the proof step `map_smul' := fun a f => by`.

Establish `e : toB (a • f).1 (a • f).2 = a • toB f.1 f.2` using `QB_ext fun x => rfl`. Use `Subtype.ext ?_` and prove the remaining obligations. Simplify using `only [e, hsmul p a _ (ht f)]`. Use `rfl }`. Establish `hw : ∀ p f, (w p f).1 = (Ω p (toB f.1 f.2)).1` using `fun _ _ => rfl`.

Set `w' : G →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ)` to `{ toFun := w map_one' := LinearMap.ext fun f => Subtype.ext (by rw [hw, hone _ (ht f)]; exact coe_toB f.1 f.2) map_mul' := fun p p' => LinearMap.ext fun f => Subtype.ext (by`. Rewrite using `[hw, hmul _ _ _ (ht f), Module.End.mul_apply, hw]`. Conclude with `congrArg (fun x : BBF σ JS JT ξ₀ ψ => ((Ω p x).1 : WOF F E nS nT → ℂ)) (hb _ (hth p' _ (ht f))).symm) }`. Take `⟨om, hom⟩` from `GlobalTheory.WeilPartsF.exists_extend (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ) w'`. Use `⟨om, fun p x hx => (hom p ⟨x.1, hx⟩).trans ((hw p ⟨x.1, hx⟩).trans ?_)⟩` and prove the remaining obligations.

Conclude with `congrArg (fun y : BBF σ JS JT ξ₀ ψ => ((Ω p y).1 : WOF F E nS nT → ℂ)) (hb x hx)`.
-/
theorem exists_homF (hbd : ∀ f : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ ψ f → ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    {G : Type} [Group G] (Ω : G → BBF σ JS JT ξ₀ ψ → BBF σ JS JT ξ₀ ψ)
    (hth : ∀ p x, IsThetaFunOF σ JS JT ξ₀ ψ x.1 → IsThetaFunOF σ JS JT ξ₀ ψ (Ω p x).1)
    (hadd : ∀ p x x', IsThetaFunOF σ JS JT ξ₀ ψ x.1 → IsThetaFunOF σ JS JT ξ₀ ψ x'.1 → Ω p (x + x') = Ω p x + Ω p x')
    (hsmul : ∀ p (a : ℂ) x, IsThetaFunOF σ JS JT ξ₀ ψ x.1 → Ω p (a • x) = a • Ω p x)
    (hone : ∀ x, IsThetaFunOF σ JS JT ξ₀ ψ x.1 → Ω 1 x = x)
    (hmul : ∀ p p' x, IsThetaFunOF σ JS JT ξ₀ ψ x.1 → Ω (p * p') x = Ω p (Ω p' x)) :
    ∃ om : G →* Module.End ℂ (WOF F E nS nT → ℂ),
      ∀ p (x : BBF σ JS JT ξ₀ ψ), IsThetaFunOF σ JS JT ξ₀ ψ x.1 → om p x.1 = (Ω p x).1 := by
  let toB : ∀ f, IsThetaFunOF σ JS JT ξ₀ ψ f → BBF σ JS JT ξ₀ ψ := fun f hf => toBF f hf.cont (hbd f hf) hf.quasi
  have coe_toB : ∀ f hf, ((toB f hf).1 : WOF F E nS nT → ℂ) = f := fun _ _ => rfl
  have ht : ∀ f : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ, IsThetaFunOF σ JS JT ξ₀ ψ (toB f.1 f.2).1 := fun f => f.2
  have hb : ∀ (x : BBF σ JS JT ξ₀ ψ) (hx : IsThetaFunOF σ JS JT ξ₀ ψ x.1), toB x.1 hx = x :=
    fun x hx => QB_ext fun _ => rfl
  let w : G → Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ) := fun p =>
    { toFun := fun f => ⟨(Ω p (toB f.1 f.2)).1, hth p _ (ht f)⟩
      map_add' := fun f g => by
        have e : toB (f + g).1 (f + g).2 = toB f.1 f.2 + toB g.1 g.2 := QB_ext fun x => rfl
        refine Subtype.ext ?_
        simp only [e, hadd p _ _ (ht f) (ht g)]
        rfl
      map_smul' := fun a f => by
        have e : toB (a • f).1 (a • f).2 = a • toB f.1 f.2 := QB_ext fun x => rfl
        refine Subtype.ext ?_
        simp only [e, hsmul p a _ (ht f)]
        rfl }
  have hw : ∀ p f, (w p f).1 = (Ω p (toB f.1 f.2)).1 := fun _ _ => rfl
  let w' : G →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ) :=
    { toFun := w
      map_one' := LinearMap.ext fun f => Subtype.ext (by rw [hw, hone _ (ht f)]; exact coe_toB f.1 f.2)
      map_mul' := fun p p' => LinearMap.ext fun f => Subtype.ext (by
        rw [hw, hmul _ _ _ (ht f), Module.End.mul_apply, hw]
        exact congrArg (fun x : BBF σ JS JT ξ₀ ψ => ((Ω p x).1 : WOF F E nS nT → ℂ)) (hb _ (hth p' _ (ht f))).symm) }
  obtain ⟨om, hom⟩ := GlobalTheory.WeilPartsF.exists_extend (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ) w'
  refine ⟨om, fun p x hx => (hom p ⟨x.1, hx⟩).trans ((hw p ⟨x.1, hx⟩).trans ?_)⟩
  exact congrArg (fun y : BBF σ JS JT ξ₀ ψ => ((Ω p y).1 : WOF F E nS nT → ℂ)) (hb x hx)

end Helpers

end GlobalTheory.RealWeilF

end
