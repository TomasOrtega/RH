import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LengthEqLengthInvariantsOfTorsionLevels

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

/- English proof (translation)
Establish `: Fintype N` using `Fintype.ofFinite N`. Establish `hfinD : Finite (N →ₗ[ZMod n] ZMod n)` using `Finite.of_injective (fun f : N →ₗ[ZMod n] ZMod n => (f : N → ZMod n)) DFunLike.coe_injective`. Establish `hcard : Nat.card (AddChar N ℂ) = Nat.card N`. Rewrite using `[Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]`. Apply `le_antisymm` to reduce the goal to its premises.

Establish `hinj : Function.Injective (fun f : N →ₗ[ZMod n] ZMod n => ZMod.stdAddChar.compAddMonoidHom f.toAddMonoidHom)`. Introduce `f g h`. Use `AddChar.compAddMonoidHom_injective_right _ ZMod.injective_stdAddChar h` as an intermediate fact. Use extensionality with `x`. Conclude with `DFunLike.congr_fun this x`.

Rewrite using `[← hcard]`. Conclude with `Nat.card_le_card_of_injective _ hinj`. Set `φ : AddChar N ℂ → N → AddChar (ZMod n) ℂ` to `fun ψ x => ψ.compAddMonoidHom (LinearMap.toSpanSingleton (ZMod n) N x).toAddMonoidHom`. Establish `hφ : ∀ ψ x y, φ ψ (x + y) = φ ψ x + φ ψ y`. Introduce `ψ x y`.

Use extensionality with `k`. Simplify using `[φ, smul_add, AddChar.map_add_eq_mul]`. Set `g : AddChar N ℂ → (N →ₗ[ZMod n] ZMod n)` to `fun ψ => AddMonoidHom.toZModLinearMap n (AddMonoidHom.mk' (fun x => AddChar.zmodAddEquiv.symm (φ ψ x)) (fun x y => by rw [hφ, map_add]))`. Establish `hg : Function.Injective g`. Introduce `ψ ψ' h`.

Use extensionality with `x`. Establish `h1 : φ ψ x = φ ψ' x`. Use `LinearMap.congr_fun h x` as an intermediate fact. Simplify `this` using `[g]`. Use `DFunLike.congr_fun h1 1` as an intermediate fact.

Simplify `this` using `[φ]`. Rewrite using `[← hcard]`. Conclude with `Nat.card_le_card_of_injective g hg`.
-/
private theorem card_linearMap_zmod_eq_card (n : ℕ) [NeZero n] (N : Type) [AddCommGroup N] [Module (ZMod n) N]
    [Finite N] : Nat.card (N →ₗ[ZMod n] ZMod n) = Nat.card N := by
  classical
  have : Fintype N := Fintype.ofFinite N
  have hfinD : Finite (N →ₗ[ZMod n] ZMod n) :=
    Finite.of_injective (fun f : N →ₗ[ZMod n] ZMod n => (f : N → ZMod n)) DFunLike.coe_injective
  have hcard : Nat.card (AddChar N ℂ) = Nat.card N := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]
  apply le_antisymm
  · have hinj : Function.Injective
        (fun f : N →ₗ[ZMod n] ZMod n => ZMod.stdAddChar.compAddMonoidHom f.toAddMonoidHom) := by
      intro f g h
      have := AddChar.compAddMonoidHom_injective_right _ ZMod.injective_stdAddChar h
      ext x
      exact DFunLike.congr_fun this x
    rw [← hcard]
    exact Nat.card_le_card_of_injective _ hinj
  · let φ : AddChar N ℂ → N → AddChar (ZMod n) ℂ := fun ψ x =>
      ψ.compAddMonoidHom (LinearMap.toSpanSingleton (ZMod n) N x).toAddMonoidHom
    have hφ : ∀ ψ x y, φ ψ (x + y) = φ ψ x + φ ψ y := by
      intro ψ x y
      ext k
      simp [φ, smul_add, AddChar.map_add_eq_mul]
    let g : AddChar N ℂ → (N →ₗ[ZMod n] ZMod n) := fun ψ =>
      AddMonoidHom.toZModLinearMap n (AddMonoidHom.mk' (fun x => AddChar.zmodAddEquiv.symm (φ ψ x))
        (fun x y => by rw [hφ, map_add]))
    have hg : Function.Injective g := by
      intro ψ ψ' h
      ext x
      have h1 : φ ψ x = φ ψ' x := by
        have := LinearMap.congr_fun h x
        simpa [g] using this
      have := DFunLike.congr_fun h1 1
      simpa [φ] using this
    rw [← hcard]
    exact Nat.card_le_card_of_injective g hg

/- English proof (translation)
Introduce `hfin hdual k Ω _ _ _ _ _ l _ r hr v A hA M _ _ _ _ _ ρ hcont τ hτ`. Take `⟨-, h1, h2, -⟩` from `hfin k Ω l r M A ρ v hr hA hcont`. Take `⟨⟨e⟩, -, -, -, hb⟩` from `hdual k Ω l r M A ρ v hr hA hcont`. Use `⟨h1, h2, ?_⟩` and prove the remaining obligations. Establish `hτ' : τ = twDual ((cycMod k Ω l r).comp (Dec (F` using `k) A).subtype) ρ := by`.

Use extensionality with `g φ m`. Rewrite using `[hτ]`. Both sides reduce to the same expression. Substitute `hτ'` using the available equality. Establish `: NeZero (l ^ r)` using `⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`.

Establish `hfinD : Finite (TDual (ZMod (l ^ r)) M)` using `Finite.of_injective (fun f : Module.Dual (ZMod (l ^ r)) M => (f : M → ZMod (l ^ r))) DFunLike.coe_injective`. Establish `hA1` using `Nat.card_congr (Equiv.ofBijective _ hb)`. Establish `hA2` using `Nat.card_congr (LinearEquiv.congrRight (M := ↥(H0 (MonoidHom.comp (twDual ((cycMod k Ω l r).comp (Dec (F := k) A).subtype) ρ) (MonoidHom.id ↥(Dec (F := k) A))))) e).toEquiv`. Establish `hA3` using `card_linearMap_zmod_eq_card (l ^ r) ↥(H0 (MonoidHom.comp (twDual ((cycMod k Ω l r).comp (Dec (F := k) A).subtype) ρ) (MonoidHom.id ↥(Dec (F := k) A))))`. Conclude with `hA1.trans (hA2.trans hA3)`.
-/
theorem UpperTheory.V.X.So.locCard :
    LocalFiniteness → LocalTateDuality → ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ (v : HeightOneSpectrum (𝓞 k)) (A : ValuationSubring Ω), IsPlaceOver A v → ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation (ZMod (l ^ r)) (Dec (F := k) A) M), ContAction ρ → ∀ (τ : Representation (ZMod (l ^ r)) (Dec (F := k) A) (TDual (ZMod (l ^ r)) M)), (∀ g φ m, τ g φ m = (cycMod k Ω l r g : ZMod (l ^ r)) * φ (ρ g⁻¹ m)) → Finite (H1 ρ) ∧ Finite (H2 ρ) ∧ Nat.card (H2 ρ) = Nat.card (H0 τ) := by
  intro hfin hdual k Ω _ _ _ _ _ l _ r hr v A hA M _ _ _ _ _ ρ hcont τ hτ
  obtain ⟨-, h1, h2, -⟩ := hfin k Ω l r M A ρ v hr hA hcont
  obtain ⟨⟨e⟩, -, -, -, hb⟩ := hdual k Ω l r M A ρ v hr hA hcont
  refine ⟨h1, h2, ?_⟩
  have hτ' : τ = twDual ((cycMod k Ω l r).comp (Dec (F := k) A).subtype) ρ := by
    ext g φ m
    rw [hτ]
    rfl
  subst hτ'
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hfinD : Finite (TDual (ZMod (l ^ r)) M) :=
    Finite.of_injective (fun f : Module.Dual (ZMod (l ^ r)) M => (f : M → ZMod (l ^ r))) DFunLike.coe_injective
  have hA1 := Nat.card_congr (Equiv.ofBijective _ hb)
  have hA2 := Nat.card_congr (LinearEquiv.congrRight (M := ↥(H0 (MonoidHom.comp
    (twDual ((cycMod k Ω l r).comp (Dec (F := k) A).subtype) ρ) (MonoidHom.id ↥(Dec (F := k) A))))) e).toEquiv
  have hA3 := card_linearMap_zmod_eq_card (l ^ r) ↥(H0 (MonoidHom.comp
    (twDual ((cycMod k Ω l r).comp (Dec (F := k) A).subtype) ρ) (MonoidHom.id ↥(Dec (F := k) A))))
  exact hA1.trans (hA2.trans hA3)
