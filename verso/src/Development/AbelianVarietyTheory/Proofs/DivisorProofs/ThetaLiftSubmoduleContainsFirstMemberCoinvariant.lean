import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEval
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOneParameterSubgroupUnitaryOfRealPlaceLieAStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIndefiniteUnitaryLieAlgAddISmulEqStatement

noncomputable section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/- English proof (translation)
Unfold `atPl`. Rewrite using `[PiTensorProduct.map_tprod]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i = w`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne h]`.
-/
theorem coinv_atPl_tprod (w : ι) (L : Module.End ℂ (V w)) (f : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L (f w))) := by
  unfold atPl
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases h : i = w
  · subst h
    simp
  · simp [Function.update_of_ne h]

/- English proof (translation)
Unfold `sumPl`. Rewrite using `[LinearMap.sum_apply, Finset.sum_eq_single w, coinv_atPl_tprod]`. Introduce `i _ hi`. Rewrite using `[coinv_atPl_tprod, hL i hi, LinearMap.zero_apply, MultilinearMap.map_update_zero]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ w) h`.
-/
theorem coinv_sumPl_tprod (w : ι) (L : ∀ i, Module.End ℂ (V i)) (hL : ∀ i, i ≠ w → L i = 0) (f : ∀ i, V i) :
    sumPl L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L w (f w))) := by
  unfold sumPl
  rw [LinearMap.sum_apply, Finset.sum_eq_single w, coinv_atPl_tprod]
  · intro i _ hi
    rw [coinv_atPl_tprod, hL i hi, LinearMap.zero_apply, MultilinearMap.map_update_zero]
  · intro h
    exact absurd (Finset.mem_univ w) h

end Tensor

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n d X W M ψ om τ P Q R S Φ c N hCM hN hr A hA hact`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨f, ⟨w, hw⟩, rfl⟩`. Set `e : Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w) →ₗ[ℂ] TensD F P Q R S` to `(PiTensorProduct.tprod ℂ).toLinearMap f w`. Establish `he : ∀ g, e g = PiTensorProduct.tprod ℂ (Function.update f w g)` using `fun g => rfl`.

Establish `key : ∀ Z ∈ upq (P w) (Q w), ∀ g, fockAct1 (P w) (Q w) (R w) (S w) Z g - (-c w * Z.trace) • g ∈ (N.comap Φ).comap e`. Introduce `Z hZ g`. Set `Y : ∀ i : InfinitePlace F, Mat (P i) (Q i)` to `Pi.single w Z`. Establish `hY : ∀ i, Y i ∈ upq (P i) (Q i)`. Introduce `i`.

Distinguish the cases in `h : i = w`. Substitute `h` using the available equality. Simplify `hZ` using `[Y]`. Simplify using `[Y, Pi.single_eq_of_ne h, upq]`. Take `⟨γ, hγ, hgen⟩` from `GlobalTheory.T.exists_oneParameterSubgroup_unitary_of_realPlace_lieAlg F E σ (Fin n) P Q τ (incM F X.J) 1 A hCM hA Y hY`.

Establish `h1` using `hact γ hγ Y hgen (e g)`. Establish `h2` using `(actsLaws F (Fin n × Fin d) _ _ 0).1 _ (fun t => map_zero _) h1`. Establish `h3` using `hN.2.1 γ hγ _ (hr ▸ LinearMap.mem_range_self Φ (e g)) _ h2`. Rewrite `h3` using `[he, coinv_sumPl_tprod w _ (fun i hi => by simp [Y, Pi.single_eq_of_ne hi])]`. Rewrite using `[Submodule.mem_comap, Submodule.mem_comap, he]`.

Simplify `h3` using `[Y, sub_eq_add_neg]`. Establish `hle : GlobalTheory.HoweR.coinv (P w) (Q w) (R w) (S w) (-c w) ≤ (N.comap Φ).comap e`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨Z, g, rfl⟩`. Take `⟨Z₁, h₁, Z₂, h₂, rfl⟩` from `GlobalTheory.T.exists_indefiniteUnitaryLieAlg_add_I_smul_eq _ _ Z`.

Establish `h` using `Submodule.add_mem _ (key Z₁ h₁ g) (Submodule.smul_mem _ Complex.I (key Z₂ h₂ g))`. Rewrite using `[SetLike.mem_coe]`. Use `h using 1` and compare the differences between its conclusion and the goal. Simplify using `only [map_add, map_smul, Matrix.trace_add, Matrix.trace_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]`. Use `module`.

Establish `h` using `hle hw`. Rewrite `h` using `[Submodule.mem_comap, he, Function.update_eq_self]`. Conclude with `h`.
-/
theorem tensAny_coinv_le_comap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (om : Rep σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w) (P Q R S : InfinitePlace F → ℕ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (c : InfinitePlace F → ℂ) (N : Submodule ℂ (SInf F (Fin n × Fin d))), IsCMExt F E σ → GlobalTheory.Published.ThetaSubInf M ψ τ om N → LinearMap.range Φ = M.Pol ψ τ → ∀ A : ∀ w : InfinitePlace F, Matrix (Fin n) (Ix (P w) (Q w)) ℂ, (∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (τ w))) (A w)) → ActsByD τ A (om.comp (MonoidHom.inl _ _)) Φ (fun w => fockAct1 (P w) (Q w) (R w) (S w)) c → GlobalTheory.HoweR.tensAny (fun w => GlobalTheory.HoweR.coinv (P w) (Q w) (R w) (S w) (-c w)) ≤ N.comap Φ := by
  intro F E _ _ _ _ _ σ n d X W M ψ om τ P Q R S Φ c N hCM hN hr A hA hact
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, ⟨w, hw⟩, rfl⟩
  let e : Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w) →ₗ[ℂ] TensD F P Q R S := (PiTensorProduct.tprod ℂ).toLinearMap f w
  have he : ∀ g, e g = PiTensorProduct.tprod ℂ (Function.update f w g) := fun g => rfl
  have key : ∀ Z ∈ upq (P w) (Q w), ∀ g,
      fockAct1 (P w) (Q w) (R w) (S w) Z g - (-c w * Z.trace) • g ∈ (N.comap Φ).comap e := by
    intro Z hZ g
    let Y : ∀ i : InfinitePlace F, Mat (P i) (Q i) := Pi.single w Z
    have hY : ∀ i, Y i ∈ upq (P i) (Q i) := by
      intro i
      by_cases h : i = w
      · subst h
        simpa [Y] using hZ
      · simp [Y, Pi.single_eq_of_ne h, upq]
    obtain ⟨γ, hγ, hgen⟩ := GlobalTheory.T.exists_oneParameterSubgroup_unitary_of_realPlace_lieAlg F E σ (Fin n) P Q τ (incM F X.J) 1 A hCM hA Y hY
    have h1 := hact γ hγ Y hgen (e g)
    have h2 := (actsLaws F (Fin n × Fin d) _ _ 0).1 _ (fun t => map_zero _) h1
    have h3 := hN.2.1 γ hγ _ (hr ▸ LinearMap.mem_range_self Φ (e g)) _ h2
    rw [he, coinv_sumPl_tprod w _ (fun i hi => by simp [Y, Pi.single_eq_of_ne hi])] at h3
    rw [Submodule.mem_comap, Submodule.mem_comap, he]
    simpa [Y, sub_eq_add_neg] using h3
  have hle : GlobalTheory.HoweR.coinv (P w) (Q w) (R w) (S w) (-c w) ≤ (N.comap Φ).comap e := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨Z, g, rfl⟩
    obtain ⟨Z₁, h₁, Z₂, h₂, rfl⟩ := GlobalTheory.T.exists_indefiniteUnitaryLieAlg_add_I_smul_eq _ _ Z
    have h := Submodule.add_mem _ (key Z₁ h₁ g) (Submodule.smul_mem _ Complex.I (key Z₂ h₂ g))
    rw [SetLike.mem_coe]
    convert h using 1
    simp only [map_add, map_smul, Matrix.trace_add, Matrix.trace_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    module
  have h := hle hw
  rw [Submodule.mem_comap, he, Function.update_eq_self] at h
  exact h

end GlobalTheory.HoweD

end
