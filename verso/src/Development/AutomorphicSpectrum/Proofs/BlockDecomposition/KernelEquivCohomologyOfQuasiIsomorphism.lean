import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.PerfKerCoh

/- English proof (translation)
Introduce `S P₀ P₁ P₂ T B₀ B₁ B₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a₀ a₁ π dT Z dB b₁ f ψ₀ hπ hex hdT hZ hf hψ hq`. Establish `hdTπ : ∀ x, dT (π x) = a₁ x` using `fun x => LinearMap.congr_fun hdT x`. Set `H : LinearMap.ker a₁ →ₗ[S] LinearMap.ker dT` to `(π.comp (LinearMap.ker a₁).subtype).codRestrict (LinearMap.ker dT) fun x => by`. Rewrite using `[LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply, hdTπ]`. Conclude with `x.2`.

Set `G : LinearMap.ker a₁ →ₗ[S] Z ⧸ LinearMap.range dB` to `(LinearMap.range dB).mkQ.comp ((f.comp (LinearMap.ker a₁).subtype).codRestrict Z fun x => (hZ _).2 (hf _ x.2))`. Establish `hH : Function.Surjective H`. Introduce and unpack `⟨t, ht⟩`. Take `⟨x, rfl⟩` from `hπ t`. Establish `hx : a₁ x = 0`.

Rewrite using `[← hdTπ]`. Conclude with `ht`. Conclude with `⟨⟨x, hx⟩, rfl⟩`. Establish `hG : Function.Surjective G`. Introduce `q`.

Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Take `⟨x, y, hx, hxy⟩` from `hq.2 z ((hZ z).1 z.2)`. Use `⟨⟨x, hx⟩, ?_⟩` and prove the remaining obligations. Use `show Submodule.Quotient.mk _ = Submodule.Quotient.mk _`. Rewrite using `[Submodule.Quotient.eq]`.

Conclude with `⟨y, Subtype.ext hxy.symm⟩`. Establish `hker : LinearMap.ker H = LinearMap.ker G`. Use extensionality with `⟨x, hx⟩`. Rewrite using `[LinearMap.mem_ker, LinearMap.mem_ker]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `h' : π x = 0` using `congrArg Subtype.val h`. Take `⟨y, rfl⟩` from `(hex x).1 h'`. Use `show Submodule.Quotient.mk _ = 0`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`.

Conclude with `⟨ψ₀ y, Subtype.ext (hψ y).symm⟩`. Introduce `h`. Establish `h' : (⟨f x, (hZ _).2 (hf _ hx)⟩ : Z) ∈ LinearMap.range dB` using `(Submodule.Quotient.mk_eq_zero _).1 h`. Take `⟨y, hy⟩` from `h'`. Take `⟨y', rfl⟩` from `hq.1 x hx ⟨y, congrArg Subtype.val hy⟩`.

Conclude with `Subtype.ext ((hex _).2 ⟨y', rfl⟩)`. Conclude with `⟨(LinearMap.quotKerEquivOfSurjective H hH).symm.trans ((Submodule.quotEquivOfEq _ _ hker).trans (LinearMap.quotKerEquivOfSurjective G hG))⟩`.
-/
theorem ker_equiv_cohomology : ∀ (S P₀ P₁ P₂ T B₀ B₁ B₂ : Type) [CommRing S] [AddCommGroup P₀] [Module S P₀] [AddCommGroup P₁] [Module S P₁] [AddCommGroup P₂] [Module S P₂] [AddCommGroup T] [Module S T] [AddCommGroup B₀] [Module S B₀] [AddCommGroup B₁] [Module S B₁] [AddCommGroup B₂] [Module S B₂] (a₀ : P₀ →ₗ[S] P₁) (a₁ : P₁ →ₗ[S] P₂) (π : P₁ →ₗ[S] T) (dT : T →ₗ[S] P₂) (Z : Submodule S B₁) (dB : B₀ →ₗ[S] Z) (b₁ : B₁ →ₗ[S] B₂) (f : P₁ →ₗ[S] B₁) (ψ₀ : P₀ →ₗ[S] B₀), Function.Surjective π → Function.Exact a₀ π → dT ∘ₗ π = a₁ → (∀ z, z ∈ Z ↔ b₁ z = 0) → (∀ x, a₁ x = 0 → b₁ (f x) = 0) → (∀ y, f (a₀ y) = (dB (ψ₀ y) : B₁)) → QIsoAt a₀ a₁ (Z.subtype ∘ₗ dB) b₁ f → Nonempty (LinearMap.ker dT ≃ₗ[S] Z ⧸ LinearMap.range dB) := by
  intro S P₀ P₁ P₂ T B₀ B₁ B₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a₀ a₁ π dT Z dB b₁ f ψ₀ hπ hex hdT hZ hf hψ hq
  have hdTπ : ∀ x, dT (π x) = a₁ x := fun x => LinearMap.congr_fun hdT x
  let H : LinearMap.ker a₁ →ₗ[S] LinearMap.ker dT :=
    (π.comp (LinearMap.ker a₁).subtype).codRestrict (LinearMap.ker dT) fun x => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply, hdTπ]
      exact x.2
  let G : LinearMap.ker a₁ →ₗ[S] Z ⧸ LinearMap.range dB :=
    (LinearMap.range dB).mkQ.comp ((f.comp (LinearMap.ker a₁).subtype).codRestrict Z fun x =>
      (hZ _).2 (hf _ x.2))
  have hH : Function.Surjective H := by
    rintro ⟨t, ht⟩
    obtain ⟨x, rfl⟩ := hπ t
    have hx : a₁ x = 0 := by
      rw [← hdTπ]
      exact ht
    exact ⟨⟨x, hx⟩, rfl⟩
  have hG : Function.Surjective G := by
    intro q
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨x, y, hx, hxy⟩ := hq.2 z ((hZ z).1 z.2)
    refine ⟨⟨x, hx⟩, ?_⟩
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [Submodule.Quotient.eq]
    exact ⟨y, Subtype.ext hxy.symm⟩
  have hker : LinearMap.ker H = LinearMap.ker G := by
    ext ⟨x, hx⟩
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    constructor
    · intro h
      have h' : π x = 0 := congrArg Subtype.val h
      obtain ⟨y, rfl⟩ := (hex x).1 h'
      show Submodule.Quotient.mk _ = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact ⟨ψ₀ y, Subtype.ext (hψ y).symm⟩
    · intro h
      have h' : (⟨f x, (hZ _).2 (hf _ hx)⟩ : Z) ∈ LinearMap.range dB :=
        (Submodule.Quotient.mk_eq_zero _).1 h
      obtain ⟨y, hy⟩ := h'
      obtain ⟨y', rfl⟩ := hq.1 x hx ⟨y, congrArg Subtype.val hy⟩
      exact Subtype.ext ((hex _).2 ⟨y', rfl⟩)
  exact ⟨(LinearMap.quotKerEquivOfSurjective H hH).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans (LinearMap.quotKerEquivOfSurjective G hG))⟩

end GlobalTheory.CompanionTheory.PerfKerCoh
