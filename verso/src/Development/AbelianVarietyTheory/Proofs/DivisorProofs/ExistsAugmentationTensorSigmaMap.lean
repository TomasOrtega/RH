import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

/- English proof (translation)
Rewrite using `[Algebra.smul_def]`. Establish `h : algebraMap R B i * x ∈ I.map (algebraMap R B) * I.map (algebraMap R B)` using `Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ hi) hx`. Rewrite `h` using `[← Ideal.map_mul, ← pow_two, hI, Ideal.zero_eq_bot, Ideal.map_bot]`. Simplify using `using h`.
-/
theorem smul_mem_map_eq_zero {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {I : Ideal R} (hI : I ^ 2 = 0)
    {i : R} (hi : i ∈ I) {x : B} (hx : x ∈ I.map (algebraMap R B)) : i • x = 0 := by
  rw [Algebra.smul_def]
  have h : algebraMap R B i * x ∈ I.map (algebraMap R B) * I.map (algebraMap R B) :=
    Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ hi) hx
  rw [← Ideal.map_mul, ← pow_two, hI, Ideal.zero_eq_bot, Ideal.map_bot] at h
  simpa using h

/- English proof (translation)
Introduce `R R₀ _ _ I hI π hπ hk R₁ _ _ α B B₀ _ _ _ _ p hs hp hker`. Establish `key : ∀ (y : R₁) (b b' : B), p b = p b' → α.k y • b = α.k y • b'`. Introduce `y b b' h`. Establish `hm : b - b' ∈ I.map (algebraMap R B)` using `(hker _).1 (by rw [map_sub, h, sub_self])`. Use `smul_mem_map_eq_zero hI (α.mem y) hm` as an intermediate fact.

Rewrite `this` using `[smul_sub, sub_eq_zero]`. Then use the resulting hypothesis. Set `s : B₀ → B` to `Function.surjInv hp`. Establish `hs' : ∀ b₀, p (s b₀) = b₀` using `Function.surjInv_eq hp`. Set `f : R₁ →+ B₀ →+ B` to `AddMonoidHom.mk' (fun y ↦ AddMonoidHom.mk' (fun b₀ ↦ α.k y • s b₀) (by`. Introduce `b₀ b₀'`.

Rewrite using `[← smul_add]`. Conclude with `key y _ _ (by rw [map_add, hs', hs', hs'])))`. Use the proof step `(by`. Introduce `y y'`. Use extensionality with `b₀`.

Simplify using `[add_smul])`. Use `⟨TensorProduct.liftAddHom f ?_, ?_⟩` and prove the remaining obligations. Introduce `r₀ y b₀`. Take `⟨r, rfl⟩` from `hπ r₀`. Express the relevant statement in the definitionally equal form `α.k (π r • y) • s b₀ = α.k y • s (π r • b₀)`.

Rewrite using `[α.smul, mul_comm, mul_smul]`. Conclude with `key y _ _ (by rw [hs, hs', hs'])`. Introduce `y b`. Express the relevant statement in the definitionally equal form `α.k y • s (p b) = α.k y • b`. Conclude with `key y _ _ (hs' _)`.
-/
theorem exists_isSig : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)), ∃ σ : R₁ ⊗[R₀] B₀ →+ B, α.IsSig p σ := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α B B₀ _ _ _ _ p hs hp hker
  have key : ∀ (y : R₁) (b b' : B), p b = p b' → α.k y • b = α.k y • b' := by
    intro y b b' h
    have hm : b - b' ∈ I.map (algebraMap R B) := (hker _).1 (by rw [map_sub, h, sub_self])
    have := smul_mem_map_eq_zero hI (α.mem y) hm
    rwa [smul_sub, sub_eq_zero] at this
  let s : B₀ → B := Function.surjInv hp
  have hs' : ∀ b₀, p (s b₀) = b₀ := Function.surjInv_eq hp
  let f : R₁ →+ B₀ →+ B := AddMonoidHom.mk' (fun y ↦ AddMonoidHom.mk' (fun b₀ ↦ α.k y • s b₀) (by
      intro b₀ b₀'
      rw [← smul_add]
      exact key y _ _ (by rw [map_add, hs', hs', hs'])))
    (by
      intro y y'
      ext b₀
      simp [add_smul])
  refine ⟨TensorProduct.liftAddHom f ?_, ?_⟩
  · intro r₀ y b₀
    obtain ⟨r, rfl⟩ := hπ r₀
    change α.k (π r • y) • s b₀ = α.k y • s (π r • b₀)
    rw [α.smul, mul_comm, mul_smul]
    exact key y _ _ (by rw [hs, hs', hs'])
  · intro y b
    change α.k y • s (p b) = α.k y • b
    exact key y _ _ (hs' _)

end GlobalTheory.Obs
