import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeRationalTranslateInvariance
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovolCong

/- English proof (translation)
Introduce `z hz`. Set `φ : (Fin n → GlobalTheory.AdLat.RA F E) →+ (Fin n → GlobalTheory.AdLat.RA F E)` to `DistribMulAction.toAddMonoidHom _ ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] b)`. Establish `hle : GlobalTheory.AdLat.hat F S ≤ (GlobalTheory.AdLat.hat F T).comap φ`. Unfold `GlobalTheory.AdLat.hat`. Rewrite using `[AddSubgroup.closure_le]`.

Introduce and unpack `_ ⟨a, ha, x, hx, rfl⟩`. Rewrite using `[SetLike.mem_coe, AddSubgroup.mem_comap]`. Use `AddSubgroup.subset_closure ⟨a, ha, b • x, hb x hx, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `only [φ, DistribMulAction.toAddMonoidHom_apply, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`.

Conclude with `hle hz`.
-/
theorem smul_mem_hat (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (S T : Set (Fin n → E)) (b : E) (hb : ∀ x ∈ S, b • x ∈ T) :
    ∀ z ∈ GlobalTheory.AdLat.hat F S, ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] b) • z ∈ GlobalTheory.AdLat.hat F T := by
  intro z hz
  let φ : (Fin n → GlobalTheory.AdLat.RA F E) →+ (Fin n → GlobalTheory.AdLat.RA F E) :=
    DistribMulAction.toAddMonoidHom _ ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] b)
  have hle : GlobalTheory.AdLat.hat F S ≤ (GlobalTheory.AdLat.hat F T).comap φ := by
    unfold GlobalTheory.AdLat.hat
    rw [AddSubgroup.closure_le]
    rintro _ ⟨a, ha, x, hx, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap]
    refine AddSubgroup.subset_closure ⟨a, ha, b • x, hb x hx, ?_⟩
    funext i
    simp only [φ, DistribMulAction.toAddMonoidHom_apply, Pi.smul_apply, smul_eq_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  exact hle hz

/- English proof (translation)
Establish `hA : D.host.AA ≠ 0` using `AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D`. Establish `hsub` using `(GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.2`. Set `f : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)` to `(b • LinearMap.id : (Fin V.rank → D.host.E) →ₗ[D.host.E] (Fin V.rank → D.host.E)).restrictScalars (𝓞 D.host.E)`. Establish `hf : (Formalism.L2.Pj.latG V 1).map f ≤ GlobalTheory.Member.latC V`. Rewrite using `[hsub, Submodule.map_span_le]`.

Introduce and unpack `_ ⟨a, ha, x, hx, rfl⟩`. Establish `hba : b * a ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)`. Rewrite using `[← inv_mul_cancel₀ hA]`. Conclude with `FractionalIdeal.mul_mem_mul hb ha`. Take `⟨r, hr⟩` from `(FractionalIdeal.mem_one_iff _).1 hba`.

Establish `: f (a • x) = r • x`. Simplify using `only [f, LinearMap.restrictScalars_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_smul]`. Rewrite using `[← hr, algebraMap_smul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ r hx`.

Establish `h1 : f y ∈ (I • Formalism.L2.Pj.latG V 1).map f` using `Submodule.mem_map_of_mem hy`. Rewrite `h1` using `[Submodule.map_smul'']`. Conclude with `Submodule.smul_mono le_rfl hf h1`.
-/
theorem inv_smul_mem {D : D7} (V : HSp D) (I : Ideal (𝓞 D.host.E)) (b : D.host.E)
    (hb : b ∈ (D.host.AA⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))
    (y : Fin V.rank → D.host.E)
    (hy : y ∈ (I • Formalism.L2.Pj.latG V 1 : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))) :
    b • y ∈ (I • GlobalTheory.Member.latC V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) := by
  have hA : D.host.AA ≠ 0 := AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D
  have hsub := (GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.2
  let f : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) :=
    (b • LinearMap.id : (Fin V.rank → D.host.E) →ₗ[D.host.E] (Fin V.rank → D.host.E)).restrictScalars (𝓞 D.host.E)
  have hf : (Formalism.L2.Pj.latG V 1).map f ≤ GlobalTheory.Member.latC V := by
    rw [hsub, Submodule.map_span_le]
    rintro _ ⟨a, ha, x, hx, rfl⟩
    have hba : b * a ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
      rw [← inv_mul_cancel₀ hA]
      exact FractionalIdeal.mul_mem_mul hb ha
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 hba
    have : f (a • x) = r • x := by
      simp only [f, LinearMap.restrictScalars_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
      rw [← hr, algebraMap_smul]
    rw [this]
    exact Submodule.smul_mem _ r hx
  have h1 : f y ∈ (I • Formalism.L2.Pj.latG V 1).map f := Submodule.mem_map_of_mem hy
  rw [Submodule.map_smul''] at h1
  exact Submodule.smul_mono le_rfl hf h1

/- English proof (translation)
Establish `hA : D.host.AA ≠ 0` using `AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D`. Establish `hsub` using `(GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.2`. Set `ψ : (Fin V.rank → GlobalTheory.AdLat.RA D.host.F D.host.E) →+ (Fin V.rank → GlobalTheory.AdLat.RA D.host.F D.host.E)` to `AddMonoidHom.mk' (fun z => K *ᵥ z - z) (fun x y => by rw [Matrix.mulVec_add]; abel)`. Establish `hψs : ∀ (s : GlobalTheory.AdLat.RA D.host.F D.host.E) z, ψ (s • z) = s • ψ z`. Introduce `s z`.

Simplify using `only [ψ, AddMonoidHom.mk'_apply, Matrix.mulVec_smul, smul_sub]`. Establish `h1 : (1 : D.host.E) ∈ ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E) * ((D.host.AA⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E))`. Rewrite using `[← FractionalIdeal.coe_mul, mul_inv_cancel₀ hA]`. Conclude with `(FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩`. Establish `key` using `Submodule.mul_induction_on (C := fun t : D.host.E => ψ (fun i => c ⊗ₜ[D.host.F] (t * x i)) ∈ GlobalTheory.AdLat.hat D.host.F ((I • GlobalTheory.Member.latC V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E))) h1 ?_ ?_`.

Simplify using `only [one_mul] at key`. Conclude with `key`. Introduce `m hm b hb`. Establish `hw : (fun i => c ⊗ₜ[D.host.F] (m * x i)) ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.latG V 1 : Set (Fin V.rank → D.host.E))`. Use `AddSubgroup.subset_closure ⟨c, hc, m • x, ?_, rfl⟩` and prove the remaining obligations.

Rewrite using `[hsub]`. Conclude with `Submodule.subset_span ⟨m, hm, x, hx, rfl⟩`. Establish `h2` using `smul_mem_hat D.host.F _ _ b (fun y hy => inv_smul_mem V I b hb y hy) _ (h _ hw)`. Establish `e : ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] b) • (K *ᵥ (fun i => c ⊗ₜ[D.host.F] (m * x i)) - (fun i => c ⊗ₜ[D.host.F] (m * x i))) = ψ (fun i => c ⊗ₜ[D.host.F] (m * b * x i))`. Establish `: (fun i => c ⊗ₜ[D.host.F] (m * b * x i)) = ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] b) • (fun i => c ⊗ₜ[D.host.F] (m * x i))`.

Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, hψs]`.

Both sides reduce to the same expression. Rewrite using `[← e]`. Conclude with `h2`. Introduce `t t' ht ht'`. Establish `: (fun i => c ⊗ₜ[D.host.F] ((t + t') * x i)) = (fun i => c ⊗ₜ[D.host.F] (t * x i)) + (fun i => c ⊗ₜ[D.host.F] (t' * x i))`.

Use function extensionality and compare the values at `i`. Simplify using `only [Pi.add_apply, add_mul, TensorProduct.tmul_add]`. Use `beta_reduce at ht ht' ⊢`. Rewrite using `[this, AddMonoidHom.map_add ψ]`. Conclude with `(GlobalTheory.AdLat.hat _ _).add_mem ht ht'`.
-/
theorem gen_mem {D : D7} (V : HSp D) (K : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E))
    (I : Ideal (𝓞 D.host.E))
    (h : ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.latG V 1 : Set (Fin V.rank → D.host.E)), K *ᵥ z - z ∈
      GlobalTheory.AdLat.hat D.host.F ((I • Formalism.L2.Pj.latG V 1 : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
        Set (Fin V.rank → D.host.E)))
    (c : FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    (hc : ∀ v : HeightOneSpectrum (𝓞 D.host.F), c v ∈ HeightOneSpectrum.adicCompletionIntegers D.host.F v)
    (x : Fin V.rank → D.host.E) (hx : x ∈ GlobalTheory.Member.latC V) :
    K *ᵥ (fun i => c ⊗ₜ[D.host.F] x i) - (fun i => c ⊗ₜ[D.host.F] x i) ∈
      GlobalTheory.AdLat.hat D.host.F ((I • GlobalTheory.Member.latC V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
        Set (Fin V.rank → D.host.E)) := by
  have hA : D.host.AA ≠ 0 := AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D
  have hsub := (GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.2
  let ψ : (Fin V.rank → GlobalTheory.AdLat.RA D.host.F D.host.E) →+ (Fin V.rank → GlobalTheory.AdLat.RA D.host.F D.host.E) :=
    AddMonoidHom.mk' (fun z => K *ᵥ z - z) (fun x y => by rw [Matrix.mulVec_add]; abel)
  have hψs : ∀ (s : GlobalTheory.AdLat.RA D.host.F D.host.E) z, ψ (s • z) = s • ψ z := by
    intro s z
    simp only [ψ, AddMonoidHom.mk'_apply, Matrix.mulVec_smul, smul_sub]
  have h1 : (1 : D.host.E) ∈ ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E) *
      ((D.host.AA⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E)) := by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hA]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
  have key := Submodule.mul_induction_on (C := fun t : D.host.E => ψ (fun i => c ⊗ₜ[D.host.F] (t * x i)) ∈
      GlobalTheory.AdLat.hat D.host.F ((I • GlobalTheory.Member.latC V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
        Set (Fin V.rank → D.host.E))) h1 ?_ ?_
  · simp only [one_mul] at key
    exact key
  · intro m hm b hb
    have hw : (fun i => c ⊗ₜ[D.host.F] (m * x i)) ∈
        GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.latG V 1 : Set (Fin V.rank → D.host.E)) := by
      refine AddSubgroup.subset_closure ⟨c, hc, m • x, ?_, rfl⟩
      rw [hsub]
      exact Submodule.subset_span ⟨m, hm, x, hx, rfl⟩
    have h2 := smul_mem_hat D.host.F _ _ b (fun y hy => inv_smul_mem V I b hb y hy) _ (h _ hw)
    have e : ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] b) • (K *ᵥ (fun i => c ⊗ₜ[D.host.F] (m * x i)) -
        (fun i => c ⊗ₜ[D.host.F] (m * x i))) = ψ (fun i => c ⊗ₜ[D.host.F] (m * b * x i)) := by
      have : (fun i => c ⊗ₜ[D.host.F] (m * b * x i)) =
          ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] b) • (fun i => c ⊗ₜ[D.host.F] (m * x i)) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        congr 1
        ring
      rw [this, hψs]
      rfl
    rw [← e]
    exact h2
  · intro t t' ht ht'
    have : (fun i => c ⊗ₜ[D.host.F] ((t + t') * x i)) =
        (fun i => c ⊗ₜ[D.host.F] (t * x i)) + (fun i => c ⊗ₜ[D.host.F] (t' * x i)) := by
      funext i
      simp only [Pi.add_apply, add_mul, TensorProduct.tmul_add]
    beta_reduce at ht ht' ⊢
    rw [this, AddMonoidHom.map_add ψ]
    exact (GlobalTheory.AdLat.hat _ _).add_mem ht ht'

end GlobalTheory.CovolCong

open GlobalTheory.CovolCong in

/- English proof (translation)
Introduce `D V K I h`. Set `ψ : (Fin V.rank → GlobalTheory.AdLat.RA D.host.F D.host.E) →+ (Fin V.rank → GlobalTheory.AdLat.RA D.host.F D.host.E)` to `AddMonoidHom.mk' (fun z => K *ᵥ z - z) (fun x y => by rw [Matrix.mulVec_add]; abel)`. Establish `hle : GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) ≤ (GlobalTheory.AdLat.hat D.host.F ((I • GlobalTheory.Member.latC V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E))).comap ψ`. Unfold `GlobalTheory.AdLat.hat`. Rewrite using `[AddSubgroup.closure_le]`.

Introduce and unpack `_ ⟨c, hc, x, hx, rfl⟩`. Conclude with `gen_mem V K I h c hc x hx`. Introduce `z hz`. Conclude with `hle hz`.
-/
theorem GlobalTheory.CovolCong.cong_latC_of_cong_latG : ∀ {D : D7} (V : HSp D) (K : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E)) (I : Ideal (𝓞 D.host.E)), (∀ z ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.latG V 1 : Set (Fin V.rank → D.host.E)), K *ᵥ z - z ∈ GlobalTheory.AdLat.hat D.host.F ((I • Formalism.L2.Pj.latG V 1 : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E))) → ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)), K *ᵥ z - z ∈ GlobalTheory.AdLat.hat D.host.F ((I • GlobalTheory.Member.latC V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) := by
  intro D V K I h
  let ψ : (Fin V.rank → GlobalTheory.AdLat.RA D.host.F D.host.E) →+ (Fin V.rank → GlobalTheory.AdLat.RA D.host.F D.host.E) :=
    AddMonoidHom.mk' (fun z => K *ᵥ z - z) (fun x y => by rw [Matrix.mulVec_add]; abel)
  have hle : GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) ≤
      (GlobalTheory.AdLat.hat D.host.F ((I • GlobalTheory.Member.latC V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
        Set (Fin V.rank → D.host.E))).comap ψ := by
    unfold GlobalTheory.AdLat.hat
    rw [AddSubgroup.closure_le]
    rintro _ ⟨c, hc, x, hx, rfl⟩
    exact gen_mem V K I h c hc x hx
  intro z hz
  exact hle hz
