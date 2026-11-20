import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverZpOfInFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExtendLin
open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
namespace GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 p _ o _ _ ho Dc hF hpS τ σ hσ s q hs hq e`. Establish `hp : p.Prime` using `Fact.out`. Establish `hover` using `HT.ModelTest.overZp_of_inFibre 𝔐 hp q hq`. Establish `hu : ∀ p' ∈ S, InFibre 𝔐.ξ p' q → p' = p` using `fun p' h' hf => hover p' (𝔐.S_prime p' h') hf`. Establish `hV : 𝔐.V (Sum.inr τ) q = 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb (Sum.inr τ)) q`.

Unfold `HodgeCpt.V`. Rewrite using `[Lat.patch_of_unique _ _ _ hpS hq hu]`. Both sides reduce to the same expression. Establish `hσ' : ∀ a : 𝓞 E, 𝔐.emb (Sum.inr τ) a = (σ.comp (cmConj E).toRingHom) (a : E)`. Introduce `a`.

Establish `h1 : 𝔐.emb (Sum.inr τ) a = 𝔐.emb (Sum.inl τ) (H.bar a)` using `rfl`. Rewrite using `[h1, ← hσ, ← HT.ModelTest.bar_eq H a]`. Both sides reduce to the same expression. Establish `hom` using `hF.om'_loc s q hs hq`. Rewrite using `[hV, LieModel.mem_htDual_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨HT.LatBasic.mem_eigSp.2 fun a => ?_, fun w hw => ?_⟩` and prove the remaining obligations. Use `(Submodule.mem_iInf _).mp h1 a` as an intermediate fact. Rewrite using `[← hσ' a]`.

Simplify `this` using `[sub_eq_zero]`. Rewrite using `[one_mul]`. Use `h2 w ?_` and prove the remaining obligations. Establish `: w ∈ HT.omP 𝔐 p q`. Rewrite using `[hom]`.

Conclude with `Submodule.subset_span hw`. Conclude with `this`. Introduce and unpack `⟨h1, h2⟩`. Use `⟨(Submodule.mem_iInf _).mpr fun a => ?_, fun w hw => ?_⟩` and prove the remaining obligations. Use `HT.LatBasic.mem_eigSp.1 h1 a` as an intermediate fact.

Rewrite `this` using `[← hσ' a]`. Simplify `this` using `[sub_eq_zero]`. Establish `hw' : w ∈ HT.omP 𝔐 p q` using `hw`. Rewrite `hw'` using `[hom]`. Use `clear hw`.

Proceed by induction on `hw' using Submodule.span_induction with`. Consider the case `mem x hx => simpa using h2 x hx`. Consider the case `zero => simpa using (regAt 𝔐.ξ q).zero_mem`. Consider the case `add x y _ _ hx hy => simpa using (regAt 𝔐.ξ q).add_mem hx hy`. Consider the case `smul c x _ hx`.

Establish `: (c • x) e = (c : Ω) * x e` using `rfl`. Rewrite using `[this]`. Conclude with `(regAt 𝔐.ξ q).mul_mem c.2 hx`.
-/
theorem mem_V_inr_iff_latOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)), IsHTFamily 𝔐 p o Dc → p ∈ S → ∀ (τ : CMType H) (σ : E →+* Ω), (∀ a : 𝓞 E, σ (a : E) = 𝔐.emb (Sum.inl τ) a) → ∀ (s : {s : ∀ k, J k // mseg y s ≠ 0}) (q : Cpt 𝔐.ξ), InChart 𝔐.ξ (mseg y) s.1 q → InFibre 𝔐.ξ p q → ∀ e : 𝔐.Li, e ∈ 𝔐.V (Sum.inr τ) q ↔ e ∈ HTL.latOn (Dc s) (GlobalTheory.CompanionTheory.Ar.HT.eigSp 𝔐.ρ (σ.comp (cmConj E).toRingHom)) 1 (regAt 𝔐.ξ q) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 p _ o _ _ ho Dc hF hpS τ σ hσ s q hs hq e
  have hp : p.Prime := Fact.out
  have hover := HT.ModelTest.overZp_of_inFibre 𝔐 hp q hq
  have hu : ∀ p' ∈ S, InFibre 𝔐.ξ p' q → p' = p := fun p' h' hf => hover p' (𝔐.S_prime p' h') hf
  have hV : 𝔐.V (Sum.inr τ) q = 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb (Sum.inr τ)) q := by
    unfold HodgeCpt.V
    rw [Lat.patch_of_unique _ _ _ hpS hq hu]
    rfl
  have hσ' : ∀ a : 𝓞 E, 𝔐.emb (Sum.inr τ) a = (σ.comp (cmConj E).toRingHom) (a : E) := by
    intro a
    have h1 : 𝔐.emb (Sum.inr τ) a = 𝔐.emb (Sum.inl τ) (H.bar a) := rfl
    rw [h1, ← hσ, ← HT.ModelTest.bar_eq H a]
    rfl
  have hom := hF.om'_loc s q hs hq
  rw [hV, LieModel.mem_htDual_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨HT.LatBasic.mem_eigSp.2 fun a => ?_, fun w hw => ?_⟩
    · have := (Submodule.mem_iInf _).mp h1 a
      rw [← hσ' a]
      simpa [sub_eq_zero] using this
    · rw [one_mul]
      refine h2 w ?_
      have : w ∈ HT.omP 𝔐 p q := by
        rw [hom]
        exact Submodule.subset_span hw
      exact this
  · rintro ⟨h1, h2⟩
    refine ⟨(Submodule.mem_iInf _).mpr fun a => ?_, fun w hw => ?_⟩
    · have := HT.LatBasic.mem_eigSp.1 h1 a
      rw [← hσ' a] at this
      simpa [sub_eq_zero] using this
    · have hw' : w ∈ HT.omP 𝔐 p q := hw
      rw [hom] at hw'
      clear hw
      induction hw' using Submodule.span_induction with
      | mem x hx => simpa using h2 x hx
      | zero => simpa using (regAt 𝔐.ξ q).zero_mem
      | add x y _ _ hx hy => simpa using (regAt 𝔐.ξ q).add_mem hx hy
      | smul c x _ hx =>
        have : (c • x) e = (c : Ω) * x e := rfl
        rw [this]
        exact (regAt 𝔐.ξ q).mul_mem c.2 hx

end GlobalTheory.CompanionTheory.Ar.Flat
