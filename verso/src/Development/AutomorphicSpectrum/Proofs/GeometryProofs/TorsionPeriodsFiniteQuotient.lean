import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsToricTorsionCubWeilOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExponentialSurjectiveSemiabelianStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
Establish `hNc : (N : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hN.ne'`. Establish `hmem : ∀ z : V, z ∈ Γ₀ ↔ E z = 1` using `fun z => by`. Use `Set.ext_iff.1 hΓ z` as an intermediate fact. Simplify using `using this`. Establish `h0 : E 0 = 1`.

Use `hadd 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `left_eq_mul.1 this`. Establish `hpow : ∀ (k : ℕ) (z : V), E ((k : ℂ) • z) = E z ^ k`. Introduce `k z`.

Proceed by induction on `k with`. Consider the case `zero => simp [h0]`. Consider the case `succ k ih => rw [Nat.cast_succ, add_smul, one_smul, hadd, ih, pow_succ]`. Establish `hdiv : ∀ z : V, (N : ℂ) • (N : ℂ)⁻¹ • z = z` using `fun z => by rw [smul_smul, mul_inv_cancel₀ hNc, one_smul]`. Set `Eh : V →+ Additive P` to `AddMonoidHom.mk' (fun z => Additive.ofMul (E z)) (fun a b => by`.

Rewrite using `[hadd]`. Use the proof step `rfl)`. Set `d : Γ₀ →+ V` to `(((N : ℂ)⁻¹ • (LinearMap.id : V →ₗ[ℂ] V)).toAddMonoidHom).comp Γ₀.subtype.toAddMonoidHom`. Set `f : Γ₀ →ₗ[ℤ] Additive P` to `(Eh.comp d).toIntLinearMap`. Establish `hf : ∀ x : Γ₀, f x = Additive.ofMul (E ((N : ℂ)⁻¹ • (x : V)))` using `fun x => rfl`.

Establish `hle : LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀)) ≤ LinearMap.ker f`. Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[LinearMap.mem_ker, hf]`. Establish `: (N : ℂ)⁻¹ • (((((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀)) y : Γ₀)) : V) = y`. Establish `: ((((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀)) y : Γ₀) : V) = (N : ℂ) • (y : V)`.

Simplify using `[Nat.cast_smul_eq_nsmul]`. Rewrite using `[this, smul_smul, inv_mul_cancel₀ hNc, one_smul]`. Rewrite using `[this, (hmem _).1 y.2]`. Both sides reduce to the same expression. Set `φ` to `Submodule.liftQ _ f hle`.

Establish `hφ : ∀ x : Γ₀, φ (Submodule.Quotient.mk x) = Additive.ofMul (E ((N : ℂ)⁻¹ • (x : V)))` using `fun x => rfl`. Establish `hφN : ∀ q, (Additive.toMul (φ q)) ^ N = 1`. Introduce `q`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Rewrite using `[hφ, toMul_ofMul, ← hpow, hdiv]`.

Conclude with `(hmem _).1 x.2`. Establish `hinj : Function.Injective φ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `q hq`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`.

Rewrite `hq` using `[hφ]`. Establish `h1 : E ((N : ℂ)⁻¹ • (x : V)) = 1` using `hq`. Establish `h2 : (N : ℂ)⁻¹ • (x : V) ∈ Γ₀` using `(hmem _).2 h1`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Use `⟨⟨_, h2⟩, Subtype.ext ?_⟩` and prove the remaining obligations.

Establish `: ((((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀)) ⟨_, h2⟩ : Γ₀) : V) = (N : ℂ) • (N : ℂ)⁻¹ • (x : V)`. Simplify using `[Nat.cast_smul_eq_nsmul]`. Rewrite using `[this, hdiv]`. Establish `hrange : ∀ p : P, p ^ N = 1 → ∃ q, Additive.toMul (φ q) = p`. Introduce `p hp`.

Take `⟨z, rfl⟩` from `hsurj p`. Establish `h1 : (N : ℂ) • z ∈ Γ₀` using `(hmem _).2 (by rw [hpow, hp])`. Use `⟨Submodule.Quotient.mk ⟨_, h1⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hφ, toMul_ofMul]`. Use `congr 1`.

Express the relevant statement in the definitionally equal form `(N : ℂ)⁻¹ • (N : ℂ) • z = z`. Rewrite using `[smul_smul, inv_mul_cancel₀ hNc, one_smul]`. Set `ψ : (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))) → P` to `fun q => Additive.toMul (φ q)`. Establish `hψ : Function.Injective ψ` using `fun a b h => hinj (Additive.toMul.injective h)`. Use `⟨ψ ⁻¹' T₀, ?_, ?_, ?_, fun x => hφN (Submodule.Quotient.mk x)⟩` and prove the remaining obligations.

Use `Nat.card_congr (Equiv.ofBijective (fun q => ⟨ψ q, hφN q⟩) ⟨?_, ?_⟩)` and prove the remaining obligations. Conclude with `fun a b h => hψ (congrArg Subtype.val h)`. Introduce and unpack `⟨p, hp⟩`. Take `⟨q, hq⟩` from `hrange p hp`. Conclude with `⟨q, Subtype.ext hq⟩`.

Use `Nat.card_congr (Equiv.ofBijective (fun q => ⟨ψ q.1, q.2⟩) ⟨?_, ?_⟩)` and prove the remaining obligations. Conclude with `fun a b h => Subtype.ext (hψ (congrArg Subtype.val h))`. Introduce and unpack `⟨p, hp⟩`. Take `⟨q, hq⟩` from `hrange p (hT₀ p hp)`. Use `⟨⟨q, ?_⟩, Subtype.ext hq⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `ψ q ∈ T₀`. Rewrite using `[show ψ q = p from hq]`. Conclude with `hp`. Introduce `x hx`. Conclude with `hx`.
-/
theorem exists_periodQuot_transport {V P : Type} [AddCommGroup V] [Module ℂ V] [CommGroup P] (E : V → P)
    (hadd : ∀ z w, E (z + w) = E z * E w) (hsurj : Function.Surjective E) (Γ₀ : Submodule ℤ V)
    (hΓ : (Γ₀ : Set V) = {z | E z = 1}) (N : ℕ) (hN : 0 < N) (T₀ : Set P) (hT₀ : ∀ τ ∈ T₀, τ ^ N = 1) :
    ∃ T : Set (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))),
      Nat.card (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))) = Nat.card {p : P // p ^ N = 1} ∧
      Nat.card T = Nat.card T₀ ∧
      (∀ x : Γ₀, Submodule.Quotient.mk x ∈ T → E ((N : ℂ)⁻¹ • (x : V)) ∈ T₀) ∧
      ∀ x : Γ₀, E ((N : ℂ)⁻¹ • (x : V)) ^ N = 1 := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hmem : ∀ z : V, z ∈ Γ₀ ↔ E z = 1 := fun z => by
    have := Set.ext_iff.1 hΓ z
    simpa using this
  have h0 : E 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hpow : ∀ (k : ℕ) (z : V), E ((k : ℂ) • z) = E z ^ k := by
    intro k z
    induction k with
    | zero => simp [h0]
    | succ k ih => rw [Nat.cast_succ, add_smul, one_smul, hadd, ih, pow_succ]
  have hdiv : ∀ z : V, (N : ℂ) • (N : ℂ)⁻¹ • z = z := fun z => by rw [smul_smul, mul_inv_cancel₀ hNc, one_smul]
  let Eh : V →+ Additive P := AddMonoidHom.mk' (fun z => Additive.ofMul (E z)) (fun a b => by
    rw [hadd]; rfl)
  let d : Γ₀ →+ V := (((N : ℂ)⁻¹ • (LinearMap.id : V →ₗ[ℂ] V)).toAddMonoidHom).comp Γ₀.subtype.toAddMonoidHom
  let f : Γ₀ →ₗ[ℤ] Additive P := (Eh.comp d).toIntLinearMap
  have hf : ∀ x : Γ₀, f x = Additive.ofMul (E ((N : ℂ)⁻¹ • (x : V))) := fun x => rfl
  have hle : LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀)) ≤ LinearMap.ker f := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, hf]
    have : (N : ℂ)⁻¹ • (((((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀)) y : Γ₀)) : V) = y := by
      have : ((((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀)) y : Γ₀) : V) = (N : ℂ) • (y : V) := by
        simp [Nat.cast_smul_eq_nsmul]
      rw [this, smul_smul, inv_mul_cancel₀ hNc, one_smul]
    rw [this, (hmem _).1 y.2]
    rfl
  let φ := Submodule.liftQ _ f hle
  have hφ : ∀ x : Γ₀, φ (Submodule.Quotient.mk x) = Additive.ofMul (E ((N : ℂ)⁻¹ • (x : V))) := fun x => rfl
  have hφN : ∀ q, (Additive.toMul (φ q)) ^ N = 1 := by
    intro q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [hφ, toMul_ofMul, ← hpow, hdiv]
    exact (hmem _).1 x.2
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [hφ] at hq
    have h1 : E ((N : ℂ)⁻¹ • (x : V)) = 1 := hq
    have h2 : (N : ℂ)⁻¹ • (x : V) ∈ Γ₀ := (hmem _).2 h1
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨⟨_, h2⟩, Subtype.ext ?_⟩
    have : ((((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀)) ⟨_, h2⟩ : Γ₀) : V) = (N : ℂ) • (N : ℂ)⁻¹ • (x : V) := by
      simp [Nat.cast_smul_eq_nsmul]
    rw [this, hdiv]
  have hrange : ∀ p : P, p ^ N = 1 → ∃ q, Additive.toMul (φ q) = p := by
    intro p hp
    obtain ⟨z, rfl⟩ := hsurj p
    have h1 : (N : ℂ) • z ∈ Γ₀ := (hmem _).2 (by rw [hpow, hp])
    refine ⟨Submodule.Quotient.mk ⟨_, h1⟩, ?_⟩
    rw [hφ, toMul_ofMul]
    congr 1
    change (N : ℂ)⁻¹ • (N : ℂ) • z = z
    rw [smul_smul, inv_mul_cancel₀ hNc, one_smul]
  let ψ : (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))) → P := fun q => Additive.toMul (φ q)
  have hψ : Function.Injective ψ := fun a b h => hinj (Additive.toMul.injective h)
  refine ⟨ψ ⁻¹' T₀, ?_, ?_, ?_, fun x => hφN (Submodule.Quotient.mk x)⟩
  · refine Nat.card_congr (Equiv.ofBijective (fun q => ⟨ψ q, hφN q⟩) ⟨?_, ?_⟩)
    · exact fun a b h => hψ (congrArg Subtype.val h)
    · rintro ⟨p, hp⟩
      obtain ⟨q, hq⟩ := hrange p hp
      exact ⟨q, Subtype.ext hq⟩
  · refine Nat.card_congr (Equiv.ofBijective (fun q => ⟨ψ q.1, q.2⟩) ⟨?_, ?_⟩)
    · exact fun a b h => Subtype.ext (hψ (congrArg Subtype.val h))
    · rintro ⟨p, hp⟩
      obtain ⟨q, hq⟩ := hrange p (hT₀ p hp)
      refine ⟨⟨q, ?_⟩, Subtype.ext hq⟩
      change ψ q ∈ T₀
      rw [show ψ q = p from hq]
      exact hp
  · intro x hx
    exact hx

/- English proof (translation)
Introduce `E _ _ _ H R _ t g n M B ψ e dG b₀ hb₀ Γ₀ hΓ N hN`. Establish `hNc : (N : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hN.ne'`. Take `⟨T₀, hT₁, hT₂, hT₃⟩` from `GlobalTheory.exists_toric_torsion_cubWeil_one GlobalTheory.firstFiveLaws.2.2.1 (Sp R) t.G t.semi t.PP t.cub g N ℂ (spMap (ψ b₀)) dG hNc`. Establish `hsurj` using `GlobalTheory.T.exponential_surjective_semiabelian R t.G g n M B ψ e t.semi b₀ hb₀`. Take `⟨T, h₁, h₂, h₃, h₄⟩` from `exists_periodQuot_transport (e.ex b₀) (e.add b₀ hb₀) hsurj Γ₀ hΓ N hN T₀ hT₁`.

Use `⟨T, by rw [h₁, h₂, hT₃], fun x y hx => ?_⟩` and prove the remaining obligations. Conclude with `hT₂ _ (h₃ x hx) _ (h₄ y)`.
-/
theorem toric_torsion_radical_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp t.G M B ψ), SmoothOfRelativeDimension g t.G.hom → ∀ b₀ ∈ B, ∀ Γ₀ : Submodule ℤ (Fin g → ℂ), (Γ₀ : Set (Fin g → ℂ)) = e.per b₀ → ∀ N : ℕ, 0 < N → ∃ T : Set (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))), Nat.card (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))) * Nat.card T = N ^ (2 * g) ∧ ∀ x y : Γ₀, Submodule.Quotient.mk x ∈ T → GlobalTheory.UU.CubWeil t.cub N (e.ex b₀ ((N : ℂ)⁻¹ • (x : Fin g → ℂ))) (e.ex b₀ ((N : ℂ)⁻¹ • (y : Fin g → ℂ))) 1 := by
  intro E _ _ _ H R _ t g n M B ψ e dG b₀ hb₀ Γ₀ hΓ N hN
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨T₀, hT₁, hT₂, hT₃⟩ := GlobalTheory.exists_toric_torsion_cubWeil_one GlobalTheory.firstFiveLaws.2.2.1 (Sp R) t.G t.semi t.PP t.cub g N ℂ
    (spMap (ψ b₀)) dG hNc
  have hsurj := GlobalTheory.T.exponential_surjective_semiabelian R t.G g n M B ψ e t.semi b₀ hb₀
  obtain ⟨T, h₁, h₂, h₃, h₄⟩ := exists_periodQuot_transport (e.ex b₀) (e.add b₀ hb₀) hsurj Γ₀ hΓ N hN T₀ hT₁
  refine ⟨T, by rw [h₁, h₂, hT₃], fun x y hx => ?_⟩
  exact hT₂ _ (h₃ x hx) _ (h₄ y)

end GlobalTheory.CompanionTheory.Ar.Flat
