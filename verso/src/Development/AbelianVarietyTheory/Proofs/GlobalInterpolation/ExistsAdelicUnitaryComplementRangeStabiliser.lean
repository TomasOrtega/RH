import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InfiniteCoordinateUnfold
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryStabilizerAnisotropicVectorEquivComplemen
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

noncomputable section

namespace GlobalTheory.StabiliserOfVector

open Formalism.UG (cT UJ)
open GlobalTheory.FrameStep

/- English proof (translation)
Take `⟨-, hE, h2, hτ⟩` from `hCM`. Establish `: FiniteDimensional F E` using `Module.Finite.of_restrictScalars_finite ℚ F E`. Set `K : Submodule F E` to `LinearMap.ker (σ.toLinearMap - LinearMap.id)`. Establish `hK : ∀ z, z ∈ K ↔ σ z = z` using `fun z => by simp [K, sub_eq_zero]`. Establish `hne : K ≠ ⊤`.

Introduce `h`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Use `IsTotallyComplex.complexEmbedding_not_isReal τ ?_` and prove the remaining obligations. Rewrite using `[ComplexEmbedding.isReal_iff]`. Use extensionality with `z`.

Establish `hz : σ z = z` using `(hK z).1 (h ▸ Submodule.mem_top)`. Use `hτ τ z` as an intermediate fact. Rewrite `this` using `[hz]`. Conclude with `this.symm`. Establish `hlt` using `Submodule.finrank_lt hne`.

Establish `hle : Submodule.span F {(1 : E)} ≤ K`. Rewrite using `[Submodule.span_singleton_le_iff_mem, hK, map_one]`. Establish `heq : Submodule.span F {(1 : E)} = K`. Use `Submodule.eq_of_le_of_finrank_le hle ?_` and prove the remaining obligations. Rewrite using `[finrank_span_singleton one_ne_zero]`.

Use linear arithmetic over natural numbers and integers. Establish `hmem : y ∈ Submodule.span F {(1 : E)}` using `heq ▸ (hK y).2 hy`. Take `⟨a, ha⟩` from `Submodule.mem_span_singleton.1 hmem`. Conclude with `⟨a, by rw [← ha, Algebra.algebraMap_eq_smul_one]⟩`.
-/
theorem exists_of_conj_fixed {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {y : E} (hy : σ y = y) :
    ∃ a : F, algebraMap F E a = y := by
  obtain ⟨-, hE, h2, hτ⟩ := hCM
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let K : Submodule F E := LinearMap.ker (σ.toLinearMap - LinearMap.id)
  have hK : ∀ z, z ∈ K ↔ σ z = z := fun z => by simp [K, sub_eq_zero]
  have hne : K ≠ ⊤ := by
    intro h
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
    rw [ComplexEmbedding.isReal_iff]
    ext z
    have hz : σ z = z := (hK z).1 (h ▸ Submodule.mem_top)
    have := hτ τ z
    rw [hz] at this
    exact this.symm
  have hlt := Submodule.finrank_lt hne
  have hle : Submodule.span F {(1 : E)} ≤ K := by
    rw [Submodule.span_singleton_le_iff_mem, hK, map_one]
  have heq : Submodule.span F {(1 : E)} = K := by
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    rw [finrank_span_singleton one_ne_zero]
    omega
  have hmem : y ∈ Submodule.span F {(1 : E)} := heq ▸ (hK y).2 hy
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
  exact ⟨a, by rw [← ha, Algebra.algebraMap_eq_smul_one]⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, -, hk⟩`. Conclude with `⟨k, congrArg (fun u : GL (Fin M) (R ⊗[F] E) => (u : Matrix (Fin M) (Fin M) (R ⊗[F] E))) hk⟩`. Introduce and unpack `⟨k, hk⟩`. Establish `hinj : Function.Injective (inclR (F` using `F) (E := E) R) := (inclR (F := F) (E := E) R).injective`.

Establish `hdet : k.det ≠ 0`. Introduce `h0`. Establish `hu : IsUnit (k.map (inclR (F` using `F) R)).det := by`. Rewrite using `[hk]`. Conclude with `(Matrix.isUnits_det_units _)`.

Establish `h1` using `(inclR (F := F) (E := E) R).map_det k`. Rewrite `h1` using `[h0, map_zero]`. Rewrite `h1` using `[RingHom.mapMatrix_apply]`. Rewrite `hu` using `[← h1]`. Conclude with `not_isUnit_zero hu`.

Use `⟨Matrix.GeneralLinearGroup.mkOfDetNeZero k hdet, ?_, Units.ext hk⟩` and prove the remaining obligations. Use `show cT (σ : E →+* E) k * J * k = J`. Apply `Matrix.map_injective hinj` to reduce the goal to its premises. Establish `hg : cT (sigR R σ) (HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * (HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J` using `g.2`. Rewrite `hg` using `[← hk, cT_map, JR, ← Matrix.map_mul, ← Matrix.map_mul]`.

Conclude with `hg`.
-/
theorem mem_ratPts_iff {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] [Nontrivial R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (g : HA R σ J) :
    g ∈ ratPts R σ J ↔ ∃ k : Matrix (Fin M) (Fin M) E, k.map (inclR (F := F) R) =
      ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) := by
  constructor
  · rintro ⟨k, -, hk⟩
    exact ⟨k, congrArg (fun u : GL (Fin M) (R ⊗[F] E) => (u : Matrix (Fin M) (Fin M) (R ⊗[F] E))) hk⟩
  · rintro ⟨k, hk⟩
    have hinj : Function.Injective (inclR (F := F) (E := E) R) := (inclR (F := F) (E := E) R).injective
    have hdet : k.det ≠ 0 := by
      intro h0
      have hu : IsUnit (k.map (inclR (F := F) R)).det := by
        rw [hk]; exact (Matrix.isUnits_det_units _)
      have h1 := (inclR (F := F) (E := E) R).map_det k
      rw [h0, map_zero] at h1
      rw [RingHom.mapMatrix_apply] at h1
      rw [← h1] at hu
      exact not_isUnit_zero hu
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero k hdet, ?_, Units.ext hk⟩
    show cT (σ : E →+* E) k * J * k = J
    apply Matrix.map_injective hinj
    have hg : cT (sigR R σ) (HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
      (HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J := g.2
    rw [← hk, cT_map, JR, ← Matrix.map_mul, ← Matrix.map_mul] at hg
    exact hg

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M M' J J' B x hM hJ hJ' hBB hxB hxx`. Substitute `hM` using the available equality. Establish `hσ : ∀ y, σ (σ y) = y`. Introduce `y`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`.

Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hCM.2.2.2, hCM.2.2.2, star_star]`. Establish `hfix : σ (hE σ J (x 0) (x 0)) = hE σ J (x 0) (x 0)`. Simplify using `only [hE, Formalism.UG.hform, map_sum, map_mul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hJ.1 i j]`. Use `show σ (σ (x 0 j)) * J i j * σ (x 0 i) = σ (x 0 i) * J i j * x 0 j`. Rewrite using `[hσ]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨a, ha⟩` from `exists_of_conj_fixed σ hCM hfix`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Conclude with `hxx (by rw [← ha, map_zero])`. Establish `h : GlobalTheory.GaugeEx.StepData σ J x a B J'` using `⟨hJ, ha0, ha.symm, hxB, hBB.symm, hJ'⟩`.

Take `⟨-, L₁, L, c, hL, h11, h21, h22, hsum, hXB, hBX⟩` from `exists_dual σ hσ h`. Establish `: Nontrivial (AF F)` using `inferInstanceAs (Nontrivial (InfiniteAdeleRing F × _))`. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := F) (E := E)` as an intermediate fact. Use `set X : Matrix (Fin (M' + 1)) (Fin 1) E := (Matrix.of x).transpose with hXdef`. Use `set ι : E →+* AF F ⊗[F] E := inclR (AF F) with hι`.

Establish `hone : ∀ k : ℕ, (1 : Matrix (Fin k) (Fin k) E).map ι = 1` using `fun k => Matrix.map_one _ (map_zero ι) (map_one ι)`. Establish `hzero : ∀ k l : ℕ, (0 : Matrix (Fin k) (Fin l) E).map ι = 0` using `fun k l => Matrix.map_zero _ (map_zero ι)`. Establish `h22' : L.map ι * B.map ι = 1` using `by rw [← Matrix.map_mul, h22, hone]`. Establish `hsum' : X.map ι * L₁.map ι + B.map ι * L.map ι = 1`. Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add ι), hsum, hone]`.

Establish `hS : ∀ g : HA (AF F) σ J, g ∈ Hstab (AF F) σ J x ↔ ((HA.mat (AF F) σ J g : GL (Fin (M' + 1)) (AF F ⊗[F] E)) : Matrix (Fin (M' + 1)) (Fin (M' + 1)) (AF F ⊗[F] E)) * X.map ι = X.map ι`. Introduce `g`. Use `MulAction.mem_stabilizer_iff.trans ⟨fun hg => ?_, fun hg => ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Conclude with `congrFun (congrFun hg j) i`.

Use function extensionality and compare the values at `j i`. Conclude with `congrFun (congrFun hg i) j`. Take `⟨e, he⟩ : ∃ e : Hstab (AF F) σ J x ≃* HA (AF F) σ J', ∀ g : Hstab (AF F) σ J x, FrameRel J J' B (g : HA (AF F) σ J) (e g)` from `exists_equiv (sigR (AF F) σ) (JR (AF F) J) (JR (AF F) J') (X.map ι) (B.map ι) (L₁.map ι) (L.map ι) (c.map ι) (by rw [hL, Matrix.map_mul, Matrix.map_mul, cT_map]; rfl) (by rw [← Matrix.map_mul, h11, hone]) (by rw [← Matrix.map_mul, h21, hzero]) h22' hsum' (by rw [cT_map, JR, ← Mat …`. Set `φ : HA (AF F) σ J' →* HA (AF F) σ J` to `(Hstab (AF F) σ J x).subtype.comp e.symm.toMonoidHom`. Establish `hφ : ∀ g, φ g = (e.symm g : HA (AF F) σ J)` using `fun g => rfl`.

Establish `hrel : ∀ g, FrameRel J J' B (φ g) g`. Introduce `g`. Use `he (e.symm g)` as an intermediate fact. Rewrite `this` using `[MulEquiv.apply_symm_apply]`. Then use the resulting hypothesis. Establish `hfor : ∀ g, ((HA.mat (AF F) σ J' g : GL (Fin M') (AF F ⊗[F] E)) : Matrix (Fin M') (Fin M') (AF F ⊗[F] E)) = L.map ι * ((HA.mat (AF F) σ J (φ g) : GL (Fin (M' + 1)) (AF F ⊗[F] E)) : Matrix (Fin (M' + 1)) (Fin (M' + 1)) (AF F ⊗[F] E)) * B.map ι`.

Introduce `g`. Establish `hr` using `hrel g`. Rewrite `hr` using `[FrameRel, ← hι]`. Rewrite using `[Matrix.mul_assoc]`. Use `erw [hr, ← Matrix.mul_assoc, h22', Matrix.one_mul]`.

Establish `hback : ∀ g, ((HA.mat (AF F) σ J (φ g) : GL (Fin (M' + 1)) (AF F ⊗[F] E)) : Matrix (Fin (M' + 1)) (Fin (M' + 1)) (AF F ⊗[F] E)) = X.map ι * L₁.map ι + B.map ι * ((HA.mat (AF F) σ J' g : GL (Fin M') (AF F ⊗[F] E)) : Matrix (Fin M') (Fin M') (AF F ⊗[F] E)) * L.map ι`. Introduce `g`. Establish `hr` using `hrel g`. Rewrite `hr` using `[FrameRel, ← hι]`. Establish `h3` using `congrArg (((HA.mat (AF F) σ J (φ g) : GL (Fin (M' + 1)) (AF F ⊗[F] E)) : Matrix (Fin (M' + 1)) (Fin (M' + 1)) (AF F ⊗[F] E)) * ·) hsum'`.

Simplify using `only [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.mul_one] at h3`. Rewrite `h3` using `[(hS (φ g)).1 (e.symm g).2]`. Use `erw [hr] at h3`. Conclude with `h3.symm`. Establish `cm : Continuous fun g : HA (AF F) σ J' => HA.mat (AF F) σ J' g` using `continuous_subtype_val`.

Establish `cφ : ∀ f : HA (AF F) σ J' → HA (AF F) σ J', (Continuous fun g => ((HA.mat (AF F) σ J' (f g) : GL (Fin M') (AF F ⊗[F] E)) : Matrix (Fin M') (Fin M') (AF F ⊗[F] E))) → Continuous fun g => ((HA.mat (AF F) σ J (φ (f g)) : GL (Fin (M' + 1)) (AF F ⊗[F] E)) : Matrix (Fin (M' + 1)) (Fin …`. Introduce `f hf`. Simplify using `only [hback]`. Conclude with `continuous_const.add ((continuous_const.matrix_mul hf).matrix_mul continuous_const)`. Use `⟨φ, ?_, Subtype.val_injective.comp e.symm.injective, ?_, hrel, fun g => ?_⟩` and prove the remaining obligations.

Use `continuous_into (AF F) σ J _ (cφ id (Units.continuous_val.comp cm)) ?_` and prove the remaining obligations. Simplify using `only [← map_inv]`. Conclude with `cφ (fun g => g⁻¹) (Units.continuous_coe_inv.comp cm)`. Use extensionality with `h`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨g, rfl⟩`. Conclude with `(e.symm g).2`. Introduce `hh`. Conclude with `⟨e ⟨h, hh⟩, by rw [hφ, MulEquiv.symm_apply_apply]⟩`. Rewrite using `[mem_ratPts_iff, mem_ratPts_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk⟩`. Conclude with `⟨L * k * B, by rw [hfor, ← hk, Matrix.map_mul, Matrix.map_mul]⟩`. Introduce and unpack `⟨k, hk⟩`. Conclude with `⟨X * L₁ + B * k * L, by`.

Rewrite using `[hback, ← hk, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]⟩`.
-/
theorem exists_hom_range_stabiliser : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M M' : ℕ) (J : Matrix (Fin M) (Fin M) E) (J' : Matrix (Fin M') (Fin M') E) (B : Matrix (Fin M) (Fin M') E) (x : Fin 1 → Fin M → E), M' + 1 = M → IsHermND σ J → IsHermND σ J' → Formalism.UG.cT (σ : E →+* E) B * J * B = J' → (∀ j, hE σ J (x 0) (fun i => B i j) = 0) → hE σ J (x 0) (x 0) ≠ 0 → ∃ φ : HA (AF F) σ J' →* HA (AF F) σ J, Continuous φ ∧ Function.Injective φ ∧ φ.range = Hstab (AF F) σ J x ∧ (∀ g, FrameRel J J' B (φ g) g) ∧ ∀ g, φ g ∈ ratPts (AF F) σ J ↔ g ∈ ratPts (AF F) σ J' := by
  intro F E _ _ _ _ _ σ hCM M M' J J' B x hM hJ hJ' hBB hxB hxx
  subst hM
  have hσ : ∀ y, σ (σ y) = y := by
    intro y
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hCM.2.2.2, hCM.2.2.2, star_star]
  have hfix : σ (hE σ J (x 0) (x 0)) = hE σ J (x 0) (x 0) := by
    simp only [hE, Formalism.UG.hform, map_sum, map_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hJ.1 i j]
    show σ (σ (x 0 j)) * J i j * σ (x 0 i) = σ (x 0 i) * J i j * x 0 j
    rw [hσ]; ring
  obtain ⟨a, ha⟩ := exists_of_conj_fixed σ hCM hfix
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hxx (by rw [← ha, map_zero])
  have h : GlobalTheory.GaugeEx.StepData σ J x a B J' := ⟨hJ, ha0, ha.symm, hxB, hBB.symm, hJ'⟩
  obtain ⟨-, L₁, L, c, hL, h11, h21, h22, hsum, hXB, hBX⟩ := exists_dual σ hσ h
  have : Nontrivial (AF F) := inferInstanceAs (Nontrivial (InfiniteAdeleRing F × _))
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := F) (E := E)
  set X : Matrix (Fin (M' + 1)) (Fin 1) E := (Matrix.of x).transpose with hXdef
  set ι : E →+* AF F ⊗[F] E := inclR (AF F) with hι
  have hone : ∀ k : ℕ, (1 : Matrix (Fin k) (Fin k) E).map ι = 1 := fun k =>
    Matrix.map_one _ (map_zero ι) (map_one ι)
  have hzero : ∀ k l : ℕ, (0 : Matrix (Fin k) (Fin l) E).map ι = 0 := fun k l =>
    Matrix.map_zero _ (map_zero ι)
  have h22' : L.map ι * B.map ι = 1 := by rw [← Matrix.map_mul, h22, hone]
  have hsum' : X.map ι * L₁.map ι + B.map ι * L.map ι = 1 := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add ι), hsum, hone]
  have hS : ∀ g : HA (AF F) σ J, g ∈ Hstab (AF F) σ J x ↔
      ((HA.mat (AF F) σ J g : GL (Fin (M' + 1)) (AF F ⊗[F] E)) :
        Matrix (Fin (M' + 1)) (Fin (M' + 1)) (AF F ⊗[F] E)) * X.map ι = X.map ι := by
    intro g
    refine MulAction.mem_stabilizer_iff.trans ⟨fun hg => ?_, fun hg => ?_⟩
    · ext i j
      exact congrFun (congrFun hg j) i
    · funext j i
      exact congrFun (congrFun hg i) j
  obtain ⟨e, he⟩ : ∃ e : Hstab (AF F) σ J x ≃* HA (AF F) σ J',
      ∀ g : Hstab (AF F) σ J x, FrameRel J J' B (g : HA (AF F) σ J) (e g) :=
    exists_equiv (sigR (AF F) σ) (JR (AF F) J) (JR (AF F) J') (X.map ι) (B.map ι) (L₁.map ι)
      (L.map ι) (c.map ι)
      (by rw [hL, Matrix.map_mul, Matrix.map_mul, cT_map]; rfl)
      (by rw [← Matrix.map_mul, h11, hone]) (by rw [← Matrix.map_mul, h21, hzero]) h22' hsum'
      (by rw [cT_map, JR, ← Matrix.map_mul, ← Matrix.map_mul, hXB, hzero])
      (by rw [cT_map, JR, ← Matrix.map_mul, ← Matrix.map_mul, hBX, hzero])
      (by rw [cT_map, JR, ← Matrix.map_mul, ← Matrix.map_mul, hBB]; rfl)
      (Hstab (AF F) σ J x) hS
  let φ : HA (AF F) σ J' →* HA (AF F) σ J :=
    (Hstab (AF F) σ J x).subtype.comp e.symm.toMonoidHom
  have hφ : ∀ g, φ g = (e.symm g : HA (AF F) σ J) := fun g => rfl
  have hrel : ∀ g, FrameRel J J' B (φ g) g := by
    intro g
    have := he (e.symm g)
    rwa [MulEquiv.apply_symm_apply] at this
  have hfor : ∀ g, ((HA.mat (AF F) σ J' g : GL (Fin M') (AF F ⊗[F] E)) :
      Matrix (Fin M') (Fin M') (AF F ⊗[F] E)) =
        L.map ι * ((HA.mat (AF F) σ J (φ g) : GL (Fin (M' + 1)) (AF F ⊗[F] E)) :
        Matrix (Fin (M' + 1)) (Fin (M' + 1)) (AF F ⊗[F] E)) * B.map ι := by
    intro g
    have hr := hrel g
    rw [FrameRel, ← hι] at hr
    rw [Matrix.mul_assoc]
    erw [hr, ← Matrix.mul_assoc, h22', Matrix.one_mul]
  have hback : ∀ g, ((HA.mat (AF F) σ J (φ g) : GL (Fin (M' + 1)) (AF F ⊗[F] E)) :
        Matrix (Fin (M' + 1)) (Fin (M' + 1)) (AF F ⊗[F] E)) =
        X.map ι * L₁.map ι +
          B.map ι * ((HA.mat (AF F) σ J' g : GL (Fin M') (AF F ⊗[F] E)) :
            Matrix (Fin M') (Fin M') (AF F ⊗[F] E)) * L.map ι := by
    intro g
    have hr := hrel g
    rw [FrameRel, ← hι] at hr
    have h3 := congrArg (((HA.mat (AF F) σ J (φ g) : GL (Fin (M' + 1)) (AF F ⊗[F] E)) :
      Matrix (Fin (M' + 1)) (Fin (M' + 1)) (AF F ⊗[F] E)) * ·) hsum'
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.mul_one] at h3
    rw [(hS (φ g)).1 (e.symm g).2] at h3
    erw [hr] at h3
    exact h3.symm
  have cm : Continuous fun g : HA (AF F) σ J' => HA.mat (AF F) σ J' g := continuous_subtype_val
  have cφ : ∀ f : HA (AF F) σ J' → HA (AF F) σ J',
      (Continuous fun g => ((HA.mat (AF F) σ J' (f g) : GL (Fin M') (AF F ⊗[F] E)) :
            Matrix (Fin M') (Fin M') (AF F ⊗[F] E))) →
      Continuous fun g => ((HA.mat (AF F) σ J (φ (f g)) : GL (Fin (M' + 1)) (AF F ⊗[F] E)) :
        Matrix (Fin (M' + 1)) (Fin (M' + 1)) (AF F ⊗[F] E)) := by
    intro f hf
    simp only [hback]
    exact continuous_const.add ((continuous_const.matrix_mul hf).matrix_mul continuous_const)
  refine ⟨φ, ?_, Subtype.val_injective.comp e.symm.injective, ?_, hrel, fun g => ?_⟩
  · refine continuous_into (AF F) σ J _ (cφ id (Units.continuous_val.comp cm)) ?_
    simp only [← map_inv]
    exact cφ (fun g => g⁻¹) (Units.continuous_coe_inv.comp cm)
  · ext h
    constructor
    · rintro ⟨g, rfl⟩
      exact (e.symm g).2
    · intro hh
      exact ⟨e ⟨h, hh⟩, by rw [hφ, MulEquiv.symm_apply_apply]⟩
  · rw [mem_ratPts_iff, mem_ratPts_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨L * k * B, by rw [hfor, ← hk, Matrix.map_mul, Matrix.map_mul]⟩
    · rintro ⟨k, hk⟩
      exact ⟨X * L₁ + B * k * L, by
        rw [hback, ← hk, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul,
          Matrix.map_mul]⟩

end GlobalTheory.StabiliserOfVector
