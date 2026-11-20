import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AutomorphicFormsFiniteIdeal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDimensionalSpanSeparately
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDimensionalSpanCoefficients
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutFinLit GlobalTheory.Published.AutFin
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (LieAt LieInf atPlace IsExpFam IsSmoothInf wordDer)
open scoped TensorProduct DirectSum Classical

namespace GlobalTheory.SepTypes

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients`. Consider the case `exact _root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients`. Consider the case `(apply _root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients ..)`.
-/
theorem coeffSpan_finiteDimensional {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G W) : FiniteDimensional ℂ (coeffSpan ρ) := by
  first
  | exact @_root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients
  | exact _root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients
  | (apply _root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients ..)

/- English proof (translation)
Establish `hle : coeffSpan ρ ≤ (coeffSpan ρ).comap (LinearMap.funLeft ℂ ℂ (fun k : G => k * c))`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `f ⟨ℓ, w, rfl⟩`. Use `Submodule.subset_span ⟨ℓ, ρ c w, funext fun k => ?_⟩` and prove the remaining obligations. Simplify using `[LinearMap.funLeft, map_mul]`.

Conclude with `hle hh`.
-/
theorem coeffSpan_rtrans {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W) (c : G) {h : G → ℂ} (hh : h ∈ coeffSpan ρ) :
    (fun k => h (k * c)) ∈ coeffSpan ρ := by
  have hle : coeffSpan ρ ≤ (coeffSpan ρ).comap (LinearMap.funLeft ℂ ℂ (fun k : G => k * c)) := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨ℓ, w, rfl⟩
    refine Submodule.subset_span ⟨ℓ, ρ c w, funext fun k => ?_⟩
    simp [LinearMap.funLeft, map_mul]
  exact hle hh

/- English proof (translation)
Set `S : Submodule ℂ (K → ℂ)` to `{ carrier := {f | Continuous f ∧ ∀ τ (k₀ : K), (fun κ => f (k₀ * j (Pi.mulSingle τ κ))) ∈ coeffSpan (ρ τ)} add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun τ k₀ => Submodule.add_mem _ (ha.2 τ k₀) (hb.2 τ k₀)⟩ zero_mem' := ⟨continuous_const, fun τ k₀ => Submodule.zero_mem _⟩ smu …`. Establish `hfd : ∀ τ, FiniteDimensional ℂ (coeffSpan (ρ τ))` using `fun τ => coeffSpan_finiteDimensional (ρ τ)`. Establish `hfin` using `GlobalTheory.finiteDimensional_span_separately ι Γ (fun τ => coeffSpan (ρ τ)) hfd`. Establish `hupd : ∀ (x : ∀ τ, Γ τ) τ y, Function.update x τ y = Function.update x τ 1 * Pi.mulSingle τ y`. Introduce `x τ y`.

Use function extensionality and compare the values at `τ'`. Distinguish the cases in `h : τ' = τ`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne h, Pi.mulSingle_eq_of_ne h]`.

Set `M` to `Submodule.span ℂ {F : (∀ τ, Γ τ) → ℂ | ∀ τ x, (fun y => F (Function.update x τ y)) ∈ coeffSpan (ρ τ)}`. Set `T : S →ₗ[ℂ] M` to `{ toFun := fun f => ⟨fun x => (f : K → ℂ) (j x), Submodule.subset_span fun τ x => by`. Use `f.2.2 τ (j (Function.update x τ 1))` as an intermediate fact. Use `this using 2 with y` and compare the differences between its conclusion and the goal. Rewrite using `[hupd x τ y, map_mul]⟩`.

Use the proof step `map_add' := fun a b => rfl`. Use the proof step `map_smul' := fun c a => rfl }`. Establish `hT : Function.Injective T`. Introduce `a b hab`. Use `congrArg (fun u : M => (u : (∀ τ, Γ τ) → ℂ)) hab` as an intermediate fact.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `k`. Take `⟨x, rfl⟩` from `hjs k`. Conclude with `congrFun this x`. Use `⟨S, Module.Finite.of_injective T hT, fun f hf => hf.1, ?_, ?_⟩` and prove the remaining obligations.

Introduce `f hf k`. Use `⟨hf.1.comp (continuous_id.mul continuous_const), fun τ k₀ => ?_⟩` and prove the remaining obligations. Take `⟨κ₁, rfl⟩` from `hjs k`. Establish `key : ∀ κ, k₀ * j (Pi.mulSingle τ κ) * j κ₁ = (k₀ * j (Function.update κ₁ τ 1)) * j (Pi.mulSingle τ (κ * κ₁ τ))`. Introduce `κ`.

Rewrite using `[mul_assoc, mul_assoc, ← map_mul, ← map_mul]`. Use `congr 2`. Use function extensionality and compare the values at `τ'`. Distinguish the cases in `h : τ' = τ`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne h, Pi.mulSingle_eq_of_ne h]`. Simplify using `only [key]`. Conclude with `coeffSpan_rtrans (ρ τ) (κ₁ τ) (hf.2 τ _)`. Introduce `φ hφ hty g`.

Use `⟨hφ.comp (continuous_const.mul continuous_subtype_val), fun τ k₀ => ?_⟩` and prove the remaining obligations. Use `hty τ (g * (k₀ : G))` as an intermediate fact. Simplify `this` using `only [Subgroup.coe_mul, hj, mul_assoc]`.
-/
theorem exists_space {ι : Type} [Fintype ι] [DecidableEq ι] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {Γ : ι → Type} [∀ i, Group (Γ i)] (K : Subgroup G) (j : (∀ i, Γ i) →* K)
    (hjs : Function.Surjective j) (a : ∀ i, Γ i → G) (hj : ∀ i k, (j (Pi.mulSingle i k) : G) = a i k)
    (W : ι → Type) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] [∀ i, FiniteDimensional ℂ (W i)]
    (ρ : ∀ i, Representation ℂ (Γ i) (W i)) :
    ∃ S : Submodule ℂ (K → ℂ), FiniteDimensional ℂ S ∧ (∀ f ∈ S, Continuous f) ∧
      (∀ f ∈ S, ∀ k, (fun x => f (x * k)) ∈ S) ∧
      ∀ φ : G → ℂ, Continuous φ → (∀ i x, (fun k => φ (x * a i k)) ∈ coeffSpan (ρ i)) →
        ∀ g, (fun k : K => φ (g * k)) ∈ S := by
  let S : Submodule ℂ (K → ℂ) :=
    { carrier := {f | Continuous f ∧ ∀ τ (k₀ : K), (fun κ => f (k₀ * j (Pi.mulSingle τ κ))) ∈ coeffSpan (ρ τ)}
      add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun τ k₀ => Submodule.add_mem _ (ha.2 τ k₀) (hb.2 τ k₀)⟩
      zero_mem' := ⟨continuous_const, fun τ k₀ => Submodule.zero_mem _⟩
      smul_mem' := fun c {a} ha => ⟨ha.1.const_smul c, fun τ k₀ => Submodule.smul_mem _ c (ha.2 τ k₀)⟩ }
  have hfd : ∀ τ, FiniteDimensional ℂ (coeffSpan (ρ τ)) := fun τ => coeffSpan_finiteDimensional (ρ τ)
  have hfin := GlobalTheory.finiteDimensional_span_separately ι Γ (fun τ => coeffSpan (ρ τ)) hfd
  have hupd : ∀ (x : ∀ τ, Γ τ) τ y,
      Function.update x τ y = Function.update x τ 1 * Pi.mulSingle τ y := by
    intro x τ y
    funext τ'
    by_cases h : τ' = τ
    · subst h; simp
    · simp [Function.update_of_ne h, Pi.mulSingle_eq_of_ne h]
  let M := Submodule.span ℂ {F : (∀ τ, Γ τ) → ℂ |
    ∀ τ x, (fun y => F (Function.update x τ y)) ∈ coeffSpan (ρ τ)}
  let T : S →ₗ[ℂ] M :=
    { toFun := fun f => ⟨fun x => (f : K → ℂ) (j x), Submodule.subset_span fun τ x => by
        have := f.2.2 τ (j (Function.update x τ 1))
        convert this using 2 with y
        rw [hupd x τ y, map_mul]⟩
      map_add' := fun a b => rfl
      map_smul' := fun c a => rfl }
  have hT : Function.Injective T := by
    intro a b hab
    have := congrArg (fun u : M => (u : (∀ τ, Γ τ) → ℂ)) hab
    apply Subtype.ext
    funext k
    obtain ⟨x, rfl⟩ := hjs k
    exact congrFun this x
  refine ⟨S, Module.Finite.of_injective T hT, fun f hf => hf.1, ?_, ?_⟩
  · intro f hf k
    refine ⟨hf.1.comp (continuous_id.mul continuous_const), fun τ k₀ => ?_⟩
    obtain ⟨κ₁, rfl⟩ := hjs k
    have key : ∀ κ, k₀ * j (Pi.mulSingle τ κ) * j κ₁ =
        (k₀ * j (Function.update κ₁ τ 1)) * j (Pi.mulSingle τ (κ * κ₁ τ)) := by
      intro κ
      rw [mul_assoc, mul_assoc, ← map_mul, ← map_mul]
      congr 2
      funext τ'
      by_cases h : τ' = τ
      · subst h; simp
      · simp [Function.update_of_ne h, Pi.mulSingle_eq_of_ne h]
    simp only [key]
    exact coeffSpan_rtrans (ρ τ) (κ₁ τ) (hf.2 τ _)
  · intro φ hφ hty g
    refine ⟨hφ.comp (continuous_const.mul continuous_subtype_val), fun τ k₀ => ?_⟩
    have := hty τ (g * (k₀ : G))
    simpa only [Subgroup.coe_mul, hj, mul_assoc] using this

end GlobalTheory.SepTypes

/- English proof (translation)
Introduce `D θ _ V ε fr _ K ⟨j, hjs, hj⟩ W _ _ _ ρ`. Use `haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _`. Conclude with `GlobalTheory.SepTypes.exists_space K j hjs (fun τ k => kAt θ V τ (ε τ) (fr τ) k) hj W ρ`.
-/
theorem GlobalTheory.typesFiniteSpace : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D), ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ K : Subgroup (GA D V), (∃ j : (∀ τ, Formalism.REAL.KG (ε τ)) →* K, Function.Surjective j ∧ ∀ τ k, (j (Pi.mulSingle τ k) : GA D V) = kAt θ V τ (ε τ) (fr τ) k) → ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)), ∃ S : Submodule ℂ (K → ℂ), FiniteDimensional ℂ S ∧ (∀ f ∈ S, Continuous f) ∧ (∀ f ∈ S, ∀ k, (fun x => f (x * k)) ∈ S) ∧ ∀ φ : GA D V → ℂ, Continuous φ → (∀ τ, HasTypeAt θ V τ (ε τ) (fr τ) (ρ τ) φ) → ∀ g, (fun k : K => φ (g * k)) ∈ S := by
  intro D θ _ V ε fr _ K ⟨j, hjs, hj⟩ W _ _ _ ρ
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  exact GlobalTheory.SepTypes.exists_space K j hjs (fun τ k => kAt θ V τ (ε τ) (fr τ) k) hj W ρ
