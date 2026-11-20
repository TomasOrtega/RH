import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBumpB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCoefficientTendstoZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerLocallyConstant
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeBumpB
open scoped GlobalTheory.VacAny

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Set `c` to `GlobalTheory.LocTateInt.coordEv (F := F) (E := E) v`. Set `f : (Fin n → Fv F v ⊗[F] E) →+ (Fin n → Fin (Module.finrank F E) → Fv F v)` to `{ toFun := fun y i => c (y i) map_zero' := by funext i; simp map_add' := fun a b => by funext i; simp }`. Establish `hf : Continuous f` using `continuous_pi fun i => c.continuous.comp (continuous_apply i)`. Set `g : (Fin n → Fin (Module.finrank F E) → Fv F v) → (Fin n → Fv F v ⊗[F] E)` to `fun z i => c.symm (z i)`. Establish `hg : Continuous g` using `continuous_pi fun i => c.symm.continuous.comp (continuous_apply i)`.

Establish `g0 : g 0 = 0` using `by funext i; simp [g]`. Establish `hU' : g ⁻¹' U ∈ 𝓝 0` using `hg.continuousAt.preimage_mem_nhds (by rwa [g0])`. Use `haveI : NonarchimedeanAddGroup (Fin n → Fin (Module.finrank F E) → Fv F v) := IsUltrametricDist.nonarchimedeanAddGroup`. Take `⟨V, hV⟩` from `NonarchimedeanAddGroup.is_nonarchimedean _ hU'`. Use `⟨V.toAddSubgroup.comap f, V.isOpen.preimage hf, fun y hy => ?_⟩` and prove the remaining obligations.

Establish `h : g (f y) ∈ U` using `hV hy`. Establish `e : g (f y) = y` using `by funext i; simp [g, f]`. Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
private theorem exists_open_sub (v : Pl F) (n : ℕ) (U : Set (Fin n → Fv F v ⊗[F] E)) (hU : U ∈ 𝓝 0) :
    ∃ L : AddSubgroup (Fin n → Fv F v ⊗[F] E), IsOpen (L : Set (Fin n → Fv F v ⊗[F] E)) ∧ ∀ y ∈ L, y ∈ U := by
  let c := GlobalTheory.LocTateInt.coordEv (F := F) (E := E) v
  let f : (Fin n → Fv F v ⊗[F] E) →+ (Fin n → Fin (Module.finrank F E) → Fv F v) :=
    { toFun := fun y i => c (y i)
      map_zero' := by funext i; simp
      map_add' := fun a b => by funext i; simp }
  have hf : Continuous f := continuous_pi fun i => c.continuous.comp (continuous_apply i)
  let g : (Fin n → Fin (Module.finrank F E) → Fv F v) → (Fin n → Fv F v ⊗[F] E) := fun z i => c.symm (z i)
  have hg : Continuous g := continuous_pi fun i => c.symm.continuous.comp (continuous_apply i)
  have g0 : g 0 = 0 := by funext i; simp [g]
  have hU' : g ⁻¹' U ∈ 𝓝 0 := hg.continuousAt.preimage_mem_nhds (by rwa [g0])
  haveI : NonarchimedeanAddGroup (Fin n → Fin (Module.finrank F E) → Fv F v) :=
    IsUltrametricDist.nonarchimedeanAddGroup
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hU'
  refine ⟨V.toAddSubgroup.comap f, V.isOpen.preimage hf, fun y hy => ?_⟩
  have h : g (f y) ∈ U := hV hy
  have e : g (f y) = y := by funext i; simp [g, f]
  rwa [e] at h

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul b e => simp [sigR, TensorProduct.smul_tmul']`. Consider the case `add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]`.
-/
private theorem sigR_smul (σ : E →ₐ[F] E) (v : Pl F) (a : Fv F v) (t : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (a • t) = a • sigR (Fv F v) σ t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b e => simp [sigR, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

private noncomputable def locY {σ : E →ₐ[F] E} {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W)
    (H' : Plane E d d₁) (v : Pl F) :
    (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) where
  toFun y := GlobalTheory.LatVac.locCo M.co v (yAt H' v y)
  map_add' s t := by
    rw [← map_add]
    congr 1
    ext i j
    simp only [yAt, Matrix.vecMulVec_apply, Matrix.add_apply, Pi.add_apply, map_add, add_mul]
  map_smul' a t := by
    rw [RingHom.id_apply, ← GlobalTheory.VanishLocCont.locCo_smul]
    congr 1
    ext i j
    simp only [yAt, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, GlobalTheory.VanishLocCont.liftT_smul,
      smul_mul_assoc]

private noncomputable def trY (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Pl F)
    (x : Fin n → Fv F v ⊗[F] E) : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v] Fv F v where
  toFun y := Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (pairV σ J v x y)
  map_add' s t := by rw [pairV_add_right, map_add]
  map_smul' a t := by
    rw [RingHom.id_apply, ← map_smul]
    congr 1
    have e : (fun i => sigR (Fv F v) σ ((a • t) i)) = a • fun i => sigR (Fv F v) σ (t i) :=
      funext fun i => sigR_smul σ v a (t i)
    rw [pairV, pairV, e, Matrix.mulVec_smul, dotProduct_smul]

end

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d d₁ X W M H' hψ v φ hφ x`. Use `haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩`. Establish `hψv : Continuous (GlobalTheory.LatVac.psiAt B.ψ v)` using `GlobalTheory.SchrSB.continuous_psiAt B.ψ hψ v`. Establish `hc : Continuous (locY M H' v)` using `IsModuleTopology.continuous_of_linearMap _`. Establish `hc' : Continuous (trY σ X.J v x)` using `IsModuleTopology.continuous_of_linearMap _`.

Establish `h1` using `hc.tendsto 0`. Rewrite `h1` using `[map_zero]`. Establish `e1` using `h1.eventually (GlobalTheory.SchrSmall.schr_eventually_eq v _ hψv φ hφ)`. Establish `e2` using `((GlobalTheory.SchrSB.isLocallyConstant_addChar _ hψv).comp_continuous hc').eventually_eq (x := 0)`. Take `⟨L, hL, hLU⟩` from `exists_open_sub v n _ (e1.and e2)`.

Use `⟨L, hL, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨a, b⟩` from `hLU y hy`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[(locOp_rho M.co hψ v _ hφ).2]`. Conclude with `a`.

Simplify using `only [Function.comp_apply, map_zero, AddChar.map_zero_eq_one] at b`. Conclude with `b`.
-/
theorem UpperTheory.theta_local_open_subgroup :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W)
        (H' : Plane E d d₁), Continuous B.ψ → ∀ (v : Pl F), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ x : Fin n → Fv F v ⊗[F] E,
        ∃ L : AddSubgroup (Fin n → Fv F v ⊗[F] E), IsOpen (L : Set (Fin n → Fv F v ⊗[F] E)) ∧ ∀ y ∈ L,
          locOp v (M.co.rho B.ψ (partFin v (yAt H' v y))) φ = φ ∧ GlobalTheory.LatVac.psiAt B.ψ v (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (pairV σ X.J v x y)) = 1 := by
  intro F E _ _ _ _ _ σ B n d d₁ X W M H' hψ v φ hφ x
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have hψv : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt B.ψ hψ v
  have hc : Continuous (locY M H' v) := IsModuleTopology.continuous_of_linearMap _
  have hc' : Continuous (trY σ X.J v x) := IsModuleTopology.continuous_of_linearMap _
  have h1 := hc.tendsto 0
  rw [map_zero] at h1
  have e1 := h1.eventually (GlobalTheory.SchrSmall.schr_eventually_eq v _ hψv φ hφ)
  have e2 := ((GlobalTheory.SchrSB.isLocallyConstant_addChar _ hψv).comp_continuous hc').eventually_eq (x := 0)
  obtain ⟨L, hL, hLU⟩ := exists_open_sub v n _ (e1.and e2)
  refine ⟨L, hL, fun y hy => ?_⟩
  obtain ⟨a, b⟩ := hLU y hy
  refine ⟨?_, ?_⟩
  · rw [(locOp_rho M.co hψ v _ hφ).2]
    exact a
  · simp only [Function.comp_apply, map_zero, AddChar.map_zero_eq_one] at b
    exact b
