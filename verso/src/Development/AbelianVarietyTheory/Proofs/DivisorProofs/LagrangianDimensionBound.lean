import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulTransposeInjective

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

namespace GlobalTheory

/- English proof (translation)
Set `ω : ((κ → F) × (κ → F)) →ₗ[F] Module.Dual F ((κ → F) × (κ → F))` to `LinearMap.mk₂ F (fun b a => a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2) (by intro b b' a; simp [dotProduct_add, add_dotProduct]; ring) (by intro c b a; simp [dotProduct_smul, smul_dotProduct]; ring) (by intro b a a'; simp [dotProduct_add, add_dotProduct]; ring) (by intro c b a; simp [dotProduct_smu …`. Establish `hω : ∀ b a, ω b a = a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2` using `fun b a => rfl`. Establish `hinj : Function.Injective ω`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `b hb`.

Establish `h1 : ∀ i, b.2 i = 0`. Introduce `i`. Use `congrArg (fun f => f (Pi.single i 1, 0)) hb` as an intermediate fact. Simplify `this` using `[hω, single_dotProduct]`. Establish `h2 : ∀ i, b.1 i = 0`.

Introduce `i`. Use `congrArg (fun f => f (0, Pi.single i 1)) hb` as an intermediate fact. Simplify `this` using `[hω, dotProduct_single]`. Conclude with `Prod.ext (funext h2) (funext h1)`. Set `g : L →ₗ[F] L.dualAnnihilator` to `((ω.domRestrict L).codRestrict L.dualAnnihilator (by`.

Introduce `b`. Rewrite using `[Submodule.mem_dualAnnihilator]`. Introduce `a ha`. Simplify using `only [LinearMap.domRestrict_apply, hω]`. Rewrite using `[hL a ha b b.2, sub_self]))`.

Establish `hg : Function.Injective g`. Introduce `x y hxy`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises. Use `congrArg Subtype.val hxy` as an intermediate fact.

Simplify `this` using `[g]`. Establish `h1` using `LinearMap.finrank_le_finrank_of_injective hg`. Establish `h2` using `Subspace.finrank_add_finrank_dualAnnihilator_eq L`. Establish `h3 : Module.finrank F ((κ → F) × (κ → F)) = 2 * Fintype.card κ`. Rewrite using `[Module.finrank_prod, Module.finrank_fintype_fun_eq_card]`.

Expand and normalize the polynomial expressions, which then agree. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_le_card_of_isotropic_prod_pi (F : Type) [Field F] (κ : Type) [Fintype κ]
    (L : Submodule F ((κ → F) × (κ → F)))
    (hL : ∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) :
    Module.finrank F L ≤ Fintype.card κ := by
  classical
  let ω : ((κ → F) × (κ → F)) →ₗ[F] Module.Dual F ((κ → F) × (κ → F)) :=
    LinearMap.mk₂ F (fun b a => a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2)
      (by intro b b' a; simp [dotProduct_add, add_dotProduct]; ring)
      (by intro c b a; simp [dotProduct_smul, smul_dotProduct]; ring)
      (by intro b a a'; simp [dotProduct_add, add_dotProduct]; ring)
      (by intro c b a; simp [dotProduct_smul, smul_dotProduct]; ring)
  have hω : ∀ b a, ω b a = a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2 := fun b a => rfl
  have hinj : Function.Injective ω := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    have h1 : ∀ i, b.2 i = 0 := by
      intro i
      have := congrArg (fun f => f (Pi.single i 1, 0)) hb
      simpa [hω, single_dotProduct] using this
    have h2 : ∀ i, b.1 i = 0 := by
      intro i
      have := congrArg (fun f => f (0, Pi.single i 1)) hb
      simpa [hω, dotProduct_single] using this
    exact Prod.ext (funext h2) (funext h1)
  let g : L →ₗ[F] L.dualAnnihilator :=
    ((ω.domRestrict L).codRestrict L.dualAnnihilator (by
      intro b
      rw [Submodule.mem_dualAnnihilator]
      intro a ha
      simp only [LinearMap.domRestrict_apply, hω]
      rw [hL a ha b b.2, sub_self]))
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply hinj
    have := congrArg Subtype.val hxy
    simpa [g] using this
  have h1 := LinearMap.finrank_le_finrank_of_injective hg
  have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq L
  have h3 : Module.finrank F ((κ → F) × (κ → F)) = 2 * Fintype.card κ := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]; ring
  omega

end GlobalTheory

/- English proof (translation)
The claim follows from `GlobalTheory.finrank_le_card_of_isotropic_prod_pi`.
-/
example : ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] (L : Submodule F ((κ → F) × (κ → F))),
    (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) → Module.finrank F L ≤ Fintype.card κ :=
  GlobalTheory.finrank_le_card_of_isotropic_prod_pi
