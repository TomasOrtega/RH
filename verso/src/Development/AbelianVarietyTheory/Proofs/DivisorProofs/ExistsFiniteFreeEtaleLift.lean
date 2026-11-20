import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEquivalenceFiniteEtaleBaseChangeResidueField

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaleLiftQuot

open IsLocalRing TensorProduct

/- English proof (translation)
Introduce `x hx`. Use `GlobalTheory.mem_jacobson_bot_of_forall_isMaximal fun n hn ↦ ?_` and prove the remaining obligations. Take `⟨τ, hτ⟩` from `h n hn`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, ← hτ, RingHom.mem_ker.1 hx, map_zero]`.
-/
theorem ker_le_jacobson_of_factor {S T F : Type} [CommRing S] [CommRing T] [FunLike F S T]
    [RingHomClass F S T] (g : F)
    (h : ∀ n : Ideal S, n.IsMaximal → ∃ τ : T →+* S ⧸ n, ∀ x, τ (g x) = Ideal.Quotient.mk n x) :
    RingHom.ker g ≤ (⊥ : Ideal S).jacobson := by
  intro x hx
  refine GlobalTheory.mem_jacobson_bot_of_forall_isMaximal fun n hn ↦ ?_
  obtain ⟨τ, hτ⟩ := h n hn
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← hτ, RingHom.mem_ker.1 hx, map_zero]

def residueToQuot (R : Type) [CommRing R] [IsLocalRing R] {S : Type} [CommRing S] [Algebra R S]
    [Module.Finite R S] (n : Ideal S) [n.IsMaximal] : ResidueField R →ₐ[R] S ⧸ n :=
  Ideal.Quotient.liftₐ (maximalIdeal R) (Algebra.ofId R _) fun a ha ↦ by
    rw [← GlobalTheory.comap_eq_maximalIdeal_of_finite n] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.2 ha

variable {R : Type} [CommRing R] [HenselianLocalRing R] (I : Ideal R)

abbrev algQuotResidue (hI : I ≤ maximalIdeal R) : Algebra (R ⧸ I) (ResidueField R) :=
  (Ideal.Quotient.factor hI : R ⧸ I →+* R ⧸ maximalIdeal R).toAlgebra

/- English proof (translation)
Use `letI := algQuotResidue I hI`. Establish `: IsScalarTower R (R ⧸ I) (ResidueField R)` using `.of_algebraMap_eq fun _ ↦ rfl`. Establish `hsurj : Function.Surjective (algebraMap R (R ⧸ I))` using `Ideal.Quotient.mk_surjective`. Establish `hk : Function.Surjective (algebraMap (R ⧸ I) (ResidueField R))` using `fun y ↦ by`. Take `⟨x, rfl⟩` from `residue_surjective y`.

Conclude with `⟨Ideal.Quotient.mk I x, rfl⟩`. Use `letI : Algebra R E := ((algebraMap (R ⧸ I) E).comp (algebraMap R (R ⧸ I))).toAlgebra`. Establish `: IsScalarTower R (R ⧸ I) E` using `.of_algebraMap_eq fun _ ↦ rfl`. Establish `: Module.Finite R E` using `.trans (R ⧸ I) E`. Take `⟨B, _, _, hBfin, hBet, ⟨e⟩⟩` from `GlobalTheory.exists_etale_lift_of_etale.{0, 0} R (ResidueField R ⊗[R ⧸ I] E)`.

Use `⟨B, inferInstance, inferInstance, hBfin, hBet, ?_⟩` and prove the remaining obligations. Establish `: IsScalarTower R (R ⧸ I) (ResidueField R ⊗[R ⧸ I] E)` using `.of_algebraMap_eq fun _ ↦ rfl`. Establish `: IsScalarTower R (R ⧸ I) (ResidueField R ⊗[R] B)` using `.of_algebraMap_eq fun _ ↦ rfl`. Set `πE : E →ₐ[R ⧸ I] ResidueField R ⊗[R ⧸ I] E` to `Algebra.TensorProduct.includeRight`. Establish `hπE : Function.Surjective πE` using `Algebra.TensorProduct.includeRight_surjective _ hk`.

Establish `hkerE : RingHom.ker πE ≤ (⊥ : Ideal E).jacobson`. Use `ker_le_jacobson_of_factor πE fun n hn ↦ ?_` and prove the remaining obligations. Set `σ` to `(residueToQuot R n).extendScalarsOfSurjective hsurj`. Set `τ` to `Algebra.TensorProduct.lift σ (Ideal.Quotient.mkₐ (R ⧸ I) n) fun _ _ ↦ .all _ _`. Conclude with `⟨τ.toRingHom, fun x ↦ by simp [τ, πE]⟩`.

Set `J` to `I.map (algebraMap R B)`. Establish `hJ : ∀ (T : Type) [CommRing T] [Algebra R T] (g : B →ₐ[R] T), (∀ r ∈ I, algebraMap R T r = 0) → ∀ a ∈ J, g a = 0` using `fun T _ _ g hT a ha ↦ by`. Establish `: J ≤ RingHom.ker g`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `r hr`.

Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes]`. Conclude with `hT r hr`. Conclude with `this ha`. Establish `hres : ∀ r ∈ I, algebraMap R (ResidueField R ⊗[R] B) r = 0` using `fun r hr ↦ by`. Establish `h0 : algebraMap R (ResidueField R) r = 0` using `(residue_eq_zero_iff r).2 (hI hr)`.

Rewrite using `[IsScalarTower.algebraMap_apply R (ResidueField R), h0, map_zero]`. Set `πB₀ : B ⧸ J →ₐ[R] ResidueField R ⊗[R] B` to `Ideal.Quotient.liftₐ J Algebra.TensorProduct.includeRight (hJ _ _ hres)`. Set `πB : B ⧸ J →ₐ[R ⧸ I] ResidueField R ⊗[R] B` to `πB₀.extendScalarsOfSurjective hsurj`. Establish `hπB_mk : ∀ b : B, πB (Ideal.Quotient.mk J b) = 1 ⊗ₜ b` using `fun b ↦ rfl`. Establish `hπB : Function.Surjective πB` using `fun y ↦ by`.

Take `⟨b, rfl⟩` from `Algebra.TensorProduct.includeRight_surjective B residue_surjective y`. Conclude with `⟨Ideal.Quotient.mk J b, rfl⟩`. Establish `hkerB : RingHom.ker πB ≤ (⊥ : Ideal (B ⧸ J)).jacobson`. Use `ker_le_jacobson_of_factor πB fun n hn ↦ ?_` and prove the remaining obligations. Set `τ` to `Algebra.TensorProduct.lift (residueToQuot R n) ((Ideal.Quotient.mkₐ R n).comp (Ideal.Quotient.mkₐ R J)) fun _ _ ↦ .all _ _`.

Use `⟨τ.toRingHom, fun x ↦ ?_⟩` and prove the remaining obligations. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite using `[hπB_mk]`. Simplify using `[τ]`. Take `⟨φ, hφ⟩` from `(GlobalTheory.bijective_algHom_comp_of_etale_of_henselian R (k := R) (A := B) (πE.restrictScalars R) hπE hkerE).2 ((e.toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight)`.

Establish `hφb : ∀ b, πE (φ b) = e (1 ⊗ₜ b)` using `fun b ↦ congr($hφ b)`. Take `⟨ψ, hψ⟩` from `(GlobalTheory.bijective_algHom_comp_of_etale_of_henselian R (k := R ⧸ I) (A := E) πB hπB hkerB).2 ((e.symm.toAlgHom.restrictScalars (R ⧸ I)).comp πE)`. Establish `hψx : ∀ x, πB (ψ x) = e.symm (πE x)` using `fun x ↦ congr($hψ x)`. Establish `hEI : ∀ r ∈ I, algebraMap R E r = 0` using `fun r hr ↦ by`. Rewrite using `[IsScalarTower.algebraMap_apply R (R ⧸ I), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]`.

Set `φ' : B ⧸ J →ₐ[R ⧸ I] E` to `(Ideal.Quotient.liftₐ J φ (hJ _ _ hEI)).extendScalarsOfSurjective hsurj`. Establish `hφ'_mk : ∀ b, φ' (Ideal.Quotient.mk J b) = φ b` using `fun b ↦ rfl`. Establish `key : ∀ y, πE (φ' y) = e (πB y)` using `fun y ↦ by`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Rewrite using `[hφ'_mk, hφb, hπB_mk]`.

Establish `h1 : φ'.comp ψ = AlgHom.id (R ⧸ I) E`. Use `(GlobalTheory.bijective_algHom_comp_of_etale_of_henselian R (k := R ⧸ I) (A := E) πE hπE hkerE).1 (AlgHom.ext fun x ↦ ?_)` and prove the remaining obligations. Simplify using `only [AlgHom.comp_apply, AlgHom.id_apply, key, hψx, AlgEquiv.apply_symm_apply]`. Establish `h2 : ψ.comp φ' = AlgHom.id (R ⧸ I) (B ⧸ J)`. Establish `H` using `(GlobalTheory.bijective_algHom_comp_of_etale_of_henselian R (k := R) (A := B) (πB.restrictScalars R) hπB hkerB).1 (a₁ := (ψ.restrictScalars R).comp φ) (a₂ := Ideal.Quotient.mkₐ R J) (AlgHom.ext fun b ↦ by`.

Simplify using `only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Ideal.Quotient.mkₐ_eq_mk]`. Rewrite using `[hψx, hφb, AlgEquiv.symm_apply_apply, hπB_mk])`. Use `AlgHom.ext fun y ↦ ?_` and prove the remaining obligations. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Rewrite using `[AlgHom.comp_apply, AlgHom.id_apply, hφ'_mk]`.

Simplify using `using congr($H b)`. Conclude with `⟨AlgEquiv.ofAlgHom φ' ψ h1 h2⟩`.
-/
theorem exists_lift (hI : I ≤ maximalIdeal R) (E : Type) [CommRing E] [Algebra (R ⧸ I) E] [Module.Finite (R ⧸ I) E]
    [Algebra.Etale (R ⧸ I) E] :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B), Module.Finite R B ∧ Algebra.Etale R B ∧
      Nonempty ((B ⧸ I.map (algebraMap R B)) ≃ₐ[R ⧸ I] E) := by
  letI := algQuotResidue I hI
  have : IsScalarTower R (R ⧸ I) (ResidueField R) := .of_algebraMap_eq fun _ ↦ rfl
  have hsurj : Function.Surjective (algebraMap R (R ⧸ I)) := Ideal.Quotient.mk_surjective
  have hk : Function.Surjective (algebraMap (R ⧸ I) (ResidueField R)) := fun y ↦ by
    obtain ⟨x, rfl⟩ := residue_surjective y
    exact ⟨Ideal.Quotient.mk I x, rfl⟩
  letI : Algebra R E := ((algebraMap (R ⧸ I) E).comp (algebraMap R (R ⧸ I))).toAlgebra
  have : IsScalarTower R (R ⧸ I) E := .of_algebraMap_eq fun _ ↦ rfl
  have : Module.Finite R E := .trans (R ⧸ I) E
  obtain ⟨B, _, _, hBfin, hBet, ⟨e⟩⟩ :=
    GlobalTheory.exists_etale_lift_of_etale.{0, 0} R (ResidueField R ⊗[R ⧸ I] E)
  refine ⟨B, inferInstance, inferInstance, hBfin, hBet, ?_⟩
  have : IsScalarTower R (R ⧸ I) (ResidueField R ⊗[R ⧸ I] E) := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R (R ⧸ I) (ResidueField R ⊗[R] B) := .of_algebraMap_eq fun _ ↦ rfl

  let πE : E →ₐ[R ⧸ I] ResidueField R ⊗[R ⧸ I] E := Algebra.TensorProduct.includeRight
  have hπE : Function.Surjective πE := Algebra.TensorProduct.includeRight_surjective _ hk
  have hkerE : RingHom.ker πE ≤ (⊥ : Ideal E).jacobson := by
    refine ker_le_jacobson_of_factor πE fun n hn ↦ ?_
    let σ := (residueToQuot R n).extendScalarsOfSurjective hsurj
    let τ := Algebra.TensorProduct.lift σ (Ideal.Quotient.mkₐ (R ⧸ I) n) fun _ _ ↦ .all _ _
    exact ⟨τ.toRingHom, fun x ↦ by simp [τ, πE]⟩

  let J := I.map (algebraMap R B)
  have hJ : ∀ (T : Type) [CommRing T] [Algebra R T] (g : B →ₐ[R] T),
      (∀ r ∈ I, algebraMap R T r = 0) → ∀ a ∈ J, g a = 0 := fun T _ _ g hT a ha ↦ by
    have : J ≤ RingHom.ker g := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes]
      exact hT r hr
    exact this ha
  have hres : ∀ r ∈ I, algebraMap R (ResidueField R ⊗[R] B) r = 0 := fun r hr ↦ by
    have h0 : algebraMap R (ResidueField R) r = 0 := (residue_eq_zero_iff r).2 (hI hr)
    rw [IsScalarTower.algebraMap_apply R (ResidueField R), h0, map_zero]
  let πB₀ : B ⧸ J →ₐ[R] ResidueField R ⊗[R] B :=
    Ideal.Quotient.liftₐ J Algebra.TensorProduct.includeRight (hJ _ _ hres)
  let πB : B ⧸ J →ₐ[R ⧸ I] ResidueField R ⊗[R] B := πB₀.extendScalarsOfSurjective hsurj
  have hπB_mk : ∀ b : B, πB (Ideal.Quotient.mk J b) = 1 ⊗ₜ b := fun b ↦ rfl
  have hπB : Function.Surjective πB := fun y ↦ by
    obtain ⟨b, rfl⟩ := Algebra.TensorProduct.includeRight_surjective B residue_surjective y
    exact ⟨Ideal.Quotient.mk J b, rfl⟩
  have hkerB : RingHom.ker πB ≤ (⊥ : Ideal (B ⧸ J)).jacobson := by
    refine ker_le_jacobson_of_factor πB fun n hn ↦ ?_
    let τ := Algebra.TensorProduct.lift (residueToQuot R n)
      ((Ideal.Quotient.mkₐ R n).comp (Ideal.Quotient.mkₐ R J)) fun _ _ ↦ .all _ _
    refine ⟨τ.toRingHom, fun x ↦ ?_⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hπB_mk]
    simp [τ]

  obtain ⟨φ, hφ⟩ := (GlobalTheory.bijective_algHom_comp_of_etale_of_henselian R (k := R) (A := B)
    (πE.restrictScalars R) hπE hkerE).2
    ((e.toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight)
  have hφb : ∀ b, πE (φ b) = e (1 ⊗ₜ b) := fun b ↦ congr($hφ b)

  obtain ⟨ψ, hψ⟩ := (GlobalTheory.bijective_algHom_comp_of_etale_of_henselian R (k := R ⧸ I) (A := E)
    πB hπB hkerB).2 ((e.symm.toAlgHom.restrictScalars (R ⧸ I)).comp πE)
  have hψx : ∀ x, πB (ψ x) = e.symm (πE x) := fun x ↦ congr($hψ x)
  have hEI : ∀ r ∈ I, algebraMap R E r = 0 := fun r hr ↦ by
    rw [IsScalarTower.algebraMap_apply R (R ⧸ I), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
  let φ' : B ⧸ J →ₐ[R ⧸ I] E := (Ideal.Quotient.liftₐ J φ (hJ _ _ hEI)).extendScalarsOfSurjective hsurj
  have hφ'_mk : ∀ b, φ' (Ideal.Quotient.mk J b) = φ b := fun b ↦ rfl
  have key : ∀ y, πE (φ' y) = e (πB y) := fun y ↦ by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hφ'_mk, hφb, hπB_mk]
  have h1 : φ'.comp ψ = AlgHom.id (R ⧸ I) E := by
    refine (GlobalTheory.bijective_algHom_comp_of_etale_of_henselian R (k := R ⧸ I) (A := E)
      πE hπE hkerE).1 (AlgHom.ext fun x ↦ ?_)
    simp only [AlgHom.comp_apply, AlgHom.id_apply, key, hψx, AlgEquiv.apply_symm_apply]
  have h2 : ψ.comp φ' = AlgHom.id (R ⧸ I) (B ⧸ J) := by
    have H := (GlobalTheory.bijective_algHom_comp_of_etale_of_henselian R (k := R) (A := B)
      (πB.restrictScalars R) hπB hkerB).1
      (a₁ := (ψ.restrictScalars R).comp φ) (a₂ := Ideal.Quotient.mkₐ R J) (AlgHom.ext fun b ↦ by
        simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Ideal.Quotient.mkₐ_eq_mk]
        rw [hψx, hφb, AlgEquiv.symm_apply_apply, hπB_mk])
    refine AlgHom.ext fun y ↦ ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [AlgHom.comp_apply, AlgHom.id_apply, hφ'_mk]
    simpa using congr($H b)
  exact ⟨AlgEquiv.ofAlgHom φ' ψ h1 h2⟩

end GlobalTheory.EtaleLiftQuot

namespace GlobalTheory.EtaleLiftQuot

open IsLocalRing TensorProduct

/- English proof (translation)
Introduce `R _ _ _ hc f hf E _ _ _ _`. Establish `: HenselianRing R (maximalIdeal R)` using `@IsAdicComplete.henselianRing R _ _ hc`. Establish `: HenselianLocalRing R` using `GlobalTheory.henselianLocalRing_of_henselianRing R`. Take `⟨B, _, _, h₁, h₂, h₃⟩` from `exists_lift (Ideal.span {f}) ((Ideal.span_singleton_le_iff_mem _).2 hf) E`. Conclude with `⟨B, inferInstance, inferInstance, h₁, Module.free_of_flat_of_isLocalRing, h₂, h₃⟩`.
-/
theorem exists_finite_free_etale_lift : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
    IsAdicComplete (maximalIdeal R) R → ∀ f ∈ maximalIdeal R, ∀ (E : Type) [CommRing E]
    [Algebra (R ⧸ Ideal.span {f}) E] [Module.Finite (R ⧸ Ideal.span {f}) E]
    [Algebra.Etale (R ⧸ Ideal.span {f}) E], ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B),
      Module.Finite R B ∧ Module.Free R B ∧ Algebra.Etale R B ∧
        Nonempty ((B ⧸ (Ideal.span {f}).map (algebraMap R B)) ≃ₐ[R ⧸ Ideal.span {f}] E) := by
  intro R _ _ _ hc f hf E _ _ _ _
  have : HenselianRing R (maximalIdeal R) := @IsAdicComplete.henselianRing R _ _ hc
  have : HenselianLocalRing R := GlobalTheory.henselianLocalRing_of_henselianRing R
  obtain ⟨B, _, _, h₁, h₂, h₃⟩ :=
    exists_lift (Ideal.span {f}) ((Ideal.span_singleton_le_iff_mem _).2 hf) E
  exact ⟨B, inferInstance, inferInstance, h₁, Module.free_of_flat_of_isLocalRing, h₂, h₃⟩

end GlobalTheory.EtaleLiftQuot
