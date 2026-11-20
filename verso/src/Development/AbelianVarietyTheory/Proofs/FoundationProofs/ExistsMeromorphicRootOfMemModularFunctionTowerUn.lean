import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPlaceOverJLineOfUpperHalfPlanePointStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AnMeromorphicAtUpperHalfPlaneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHolomorphicRootUpperHalfPlaneOfOrderDvdStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
open Filter Topology

namespace GlobalTheory.KZ.MeroRoot

/- English proof (translation)
The claim follows from `GlobalTheory.T.exists_place_over_jLine_of_upperHalfPlane_point X τ hτ`.
-/
theorem valAt {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (τ : ℂ) (hτ : τ ∈ Hs) :
    ∃ W : ValuationSubring X.K, X.OverY W ∧ ∀ x : X.K, W.valuation x = 1 → ∀ φ : ℂ → ℂ,
      X.an x = (φ : Mero) → meromorphicOrderAt φ τ = 0 := GlobalTheory.T.exists_place_over_jLine_of_upperHalfPlane_point X τ hτ

/- English proof (translation)
The claim follows from `GlobalTheory.T.an_meromorphicAt_upperHalfPlane X x φ hφ τ hτ`.
-/
theorem repAt {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (x : X.K) (φ : ℂ → ℂ)
    (hφ : X.an x = (φ : Mero)) (τ : ℂ) (hτ : τ ∈ Hs) :
    MeromorphicAt φ τ ∧ (x ≠ 0 → meromorphicOrderAt φ τ ≠ ⊤) := GlobalTheory.T.an_meromorphicAt_upperHalfPlane X x φ hφ τ hτ

/- English proof (translation)
The claim follows from `GlobalTheory.T.exists_holomorphic_root_upperHalfPlane_of_order_dvd h m hm hh hdiv`.
-/
theorem rootHs (h : ℂ → ℂ) (m : ℕ) (hm : 0 < m) (hh : DifferentiableOn ℂ h Hs)
    (hdiv : ∀ τ ∈ Hs, ∀ k : ℤ, meromorphicOrderAt h τ = (k : WithTop ℤ) → (m : ℤ) ∣ k) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Hs ∧ ∀ z ∈ Hs, g z ^ m = h z := GlobalTheory.T.exists_holomorphic_root_upperHalfPlane_of_order_dvd h m hm hh hdiv

end GlobalTheory.KZ.MeroRoot

namespace GlobalTheory.KZ.MeroRoot

/- English proof (translation)
The claim follows from `isOpen_lt continuous_const Complex.continuous_im`.
-/
theorem isOpen_Hs : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

/- English proof (translation)
Establish `h1` using `(mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hFG) τ hτ`. Establish `h2 : Hs ∈ 𝓝[≠] τ` using `nhdsWithin_le_nhds (isOpen_Hs.mem_nhds hτ)`. Use `filter_upwards [h1, h2] with z hz1 hz2`. Break down `hz1 with hz | hz` into its components or cases. Conclude with `hz`.

Conclude with `absurd hz2 hz`.
-/
theorem nhdsNE_of_codisc {F G : ℂ → ℂ} (hFG : F =ᶠ[codiscreteWithin Hs] G) {τ : ℂ} (hτ : τ ∈ Hs) :
    F =ᶠ[𝓝[≠] τ] G := by
  have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hFG) τ hτ
  have h2 : Hs ∈ 𝓝[≠] τ := nhdsWithin_le_nhds (isOpen_Hs.mem_nhds hτ)
  filter_upwards [h1, h2] with z hz1 hz2
  rcases hz1 with hz | hz
  · exact hz
  · exact absurd hz2 hz

/- English proof (translation)
Proceed by induction on `x using Filter.Germ.inductionOn with`. Consider the case `h φ => exact ⟨φ, rfl⟩`.
-/
theorem germ_rep (x : Mero) : ∃ φ : ℂ → ℂ, x = (φ : Mero) := by
  induction x using Filter.Germ.inductionOn with
  | h φ => exact ⟨φ, rfl⟩

/- English proof (translation)
Establish `hm0 : (m : WithTop ℤ) ≠ 0` using `by exact_mod_cast hm.ne'`. Consider the cases of `u with`. Consider the case `top => rw [WithTop.mul_top hm0, WithTop.top_add] at hk`. Conclude with `absurd hk (WithTop.coe_ne_top)`. Consider the case `coe p`.

Consider the cases of `v with`. Consider the case `top => rw [WithTop.mul_top hm0, WithTop.add_top] at hk`. Conclude with `absurd hk (WithTop.coe_ne_top)`. Consider the case `coe q`. Establish `: k = (m : ℤ) * p + (m : ℤ) * q` using `by exact_mod_cast hk`.

Conclude with `⟨p + q, by rw [this]; ring⟩`.
-/
theorem wt_dvd {m : ℕ} (hm : 0 < m) {k : ℤ} {u v : WithTop ℤ}
    (hk : (k : WithTop ℤ) = (m : WithTop ℤ) * u + (m : WithTop ℤ) * v) : (m : ℤ) ∣ k := by
  have hm0 : (m : WithTop ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  cases u with
  | top => rw [WithTop.mul_top hm0, WithTop.top_add] at hk; exact absurd hk (WithTop.coe_ne_top)
  | coe p =>
    cases v with
    | top => rw [WithTop.mul_top hm0, WithTop.add_top] at hk; exact absurd hk (WithTop.coe_ne_top)
    | coe q =>
      have : k = (m : ℤ) * p + (m : ℤ) * q := by exact_mod_cast hk
      exact ⟨p + q, by rw [this]; ring⟩

/- English proof (translation)
Introduce `τ hτ k hk`. Take `⟨W, hW, hWv⟩` from `valAt X τ hτ`. Take `⟨g, hg⟩` from `hf W hW`. Take `⟨φf, hφf⟩` from `germ_rep (X.an (f : X.K))`. Take `⟨φg, hφg⟩` from `germ_rep (X.an (g : X.K))`.

Take `⟨ψ, hψ⟩` from `germ_rep (X.an ((f : X.K) / (g : X.K) ^ m))`. Establish `hψ0 : meromorphicOrderAt ψ τ = 0` using `hWv _ hg ψ hψ`. Establish `hfm` using `(repAt X _ φf hφf τ hτ).1`. Establish `hgm` using `(repAt X _ φg hφg τ hτ).1`. Establish `hψm` using `(repAt X _ ψ hψ τ hτ).1`.

Establish `hbm : MeromorphicAt b τ` using `((hb.analyticOnNhd isOpen_Hs) τ hτ).meromorphicAt`. Establish `e1 : (φf : Mero) = ((fun z => ψ z * φg z ^ m : ℂ → ℂ) : Mero)`. Establish `: (f : X.K) = ((f : X.K) / (g : X.K) ^ m) * (g : X.K) ^ m`. Rewrite using `[div_mul_cancel₀]`. Conclude with `pow_ne_zero _ g.ne_zero`.

Rewrite using `[← hφf, this, map_mul, map_pow, hψ, hφg]`. Both sides reduce to the same expression. Establish `e1' : φf =ᶠ[𝓝[≠] τ] (fun z => ψ z * φg z ^ m)` using `nhdsNE_of_codisc (Filter.Germ.coe_eq.1 e1) hτ`. Establish `e2 : ((fun z => a z * b z ^ (m - 1) : ℂ → ℂ) : Mero) = ((fun z => φf z * b z ^ m : ℂ → ℂ) : Mero)`. Take `⟨n, rfl⟩ : ∃ n, m = n + 1` from `⟨m - 1, by omega⟩`.

Simplify using `only [Nat.add_sub_cancel]`. Use `show ((a * b ^ n : ℂ → ℂ) : Mero) = ((φf * b ^ (n + 1) : ℂ → ℂ) : Mero)`. Rewrite using `[Filter.Germ.coe_mul, Filter.Germ.coe_mul, Filter.Germ.coe_pow, Filter.Germ.coe_pow, ← hab, hφf, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2'` using `nhdsNE_of_codisc (Filter.Germ.coe_eq.1 e2) hτ`.

Establish `o1 : meromorphicOrderAt φf τ = (m : WithTop ℤ) * meromorphicOrderAt φg τ`. Rewrite using `[meromorphicOrderAt_congr e1']`. Rewrite using `[show (fun z => ψ z * φg z ^ m) = ψ * φg ^ m from rfl, meromorphicOrderAt_mul hψm (hgm.pow m), meromorphicOrderAt_pow hgm, hψ0, zero_add]`. Rewrite `hk` using `[meromorphicOrderAt_congr e2', show (fun z => φf z * b z ^ m) = φf * b ^ m from rfl, meromorphicOrderAt_mul hfm (hbm.pow m), meromorphicOrderAt_pow hbm, o1]`. Conclude with `wt_dvd hm hk.symm`.
-/
theorem orders_dvd {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (m : ℕ) (hm : 0 < m)
    (f : X.Kˣ) (hf : f ∈ X.Un m) (a b : ℂ → ℂ) (hb : DifferentiableOn ℂ b Hs)
    (hab : X.an (f : X.K) * (b : Mero) = (a : Mero)) :
    ∀ τ ∈ Hs, ∀ k : ℤ, meromorphicOrderAt (fun z => a z * b z ^ (m - 1)) τ = (k : WithTop ℤ) → (m : ℤ) ∣ k := by
  intro τ hτ k hk
  obtain ⟨W, hW, hWv⟩ := valAt X τ hτ
  obtain ⟨g, hg⟩ := hf W hW
  obtain ⟨φf, hφf⟩ := germ_rep (X.an (f : X.K))
  obtain ⟨φg, hφg⟩ := germ_rep (X.an (g : X.K))
  obtain ⟨ψ, hψ⟩ := germ_rep (X.an ((f : X.K) / (g : X.K) ^ m))
  have hψ0 : meromorphicOrderAt ψ τ = 0 := hWv _ hg ψ hψ
  have hfm := (repAt X _ φf hφf τ hτ).1
  have hgm := (repAt X _ φg hφg τ hτ).1
  have hψm := (repAt X _ ψ hψ τ hτ).1
  have hbm : MeromorphicAt b τ :=
    ((hb.analyticOnNhd isOpen_Hs) τ hτ).meromorphicAt

  have e1 : (φf : Mero) = ((fun z => ψ z * φg z ^ m : ℂ → ℂ) : Mero) := by
    have : (f : X.K) = ((f : X.K) / (g : X.K) ^ m) * (g : X.K) ^ m := by
      rw [div_mul_cancel₀]; exact pow_ne_zero _ g.ne_zero
    rw [← hφf, this, map_mul, map_pow, hψ, hφg]; rfl
  have e1' : φf =ᶠ[𝓝[≠] τ] (fun z => ψ z * φg z ^ m) := nhdsNE_of_codisc (Filter.Germ.coe_eq.1 e1) hτ
  have e2 : ((fun z => a z * b z ^ (m - 1) : ℂ → ℂ) : Mero) = ((fun z => φf z * b z ^ m : ℂ → ℂ) : Mero) := by
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    show ((a * b ^ n : ℂ → ℂ) : Mero) = ((φf * b ^ (n + 1) : ℂ → ℂ) : Mero)
    rw [Filter.Germ.coe_mul, Filter.Germ.coe_mul, Filter.Germ.coe_pow, Filter.Germ.coe_pow, ← hab, hφf, pow_succ]
    ring
  have e2' := nhdsNE_of_codisc (Filter.Germ.coe_eq.1 e2) hτ
  have o1 : meromorphicOrderAt φf τ = (m : WithTop ℤ) * meromorphicOrderAt φg τ := by
    rw [meromorphicOrderAt_congr e1']
    rw [show (fun z => ψ z * φg z ^ m) = ψ * φg ^ m from rfl, meromorphicOrderAt_mul hψm (hgm.pow m),
      meromorphicOrderAt_pow hgm, hψ0, zero_add]
  rw [meromorphicOrderAt_congr e2', show (fun z => φf z * b z ^ m) = φf * b ^ m from rfl,
    meromorphicOrderAt_mul hfm (hbm.pow m), meromorphicOrderAt_pow hbm, o1] at hk
  exact wt_dvd hm hk.symm

end GlobalTheory.KZ.MeroRoot

namespace GlobalTheory.KZ.MeroRoot

/- English proof (translation)
Introduce `Ω _ _ _ ε X _ _ m hm f hf`. Take `⟨a, b, ha, hb, hb0, hab⟩` from `X.an_mero (f : X.K)`. Take `⟨g, hg, hgm⟩` from `rootHs (fun z => a z * b z ^ (m - 1)) m hm (ha.mul (hb.pow _)) (orders_dvd X m hm f hf a b hb hab)`. Use `⟨g, b, hg, hb, hb0, ?_⟩` and prove the remaining obligations. Take `⟨n, rfl⟩ : ∃ n, m = n + 1` from `⟨m - 1, by omega⟩`.

Establish `e : ((fun z => a z * b z ^ n : ℂ → ℂ) : Mero) = ((fun z => g z ^ (n + 1) : ℂ → ℂ) : Mero)`. Use `Filter.Germ.coe_eq.2 ?_` and prove the remaining obligations. Use `filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz`. Simplify using `using (hgm z hz).symm`. Rewrite using `[pow_succ, mul_comm ((b : Mero) ^ n), ← mul_assoc, hab, ← Filter.Germ.coe_pow, ← Filter.Germ.coe_pow, ← Filter.Germ.coe_mul]`.

Conclude with `e`.
-/
theorem exists_mero_root : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ (m : ℕ), 0 < m → ∀ f ∈ X.Un m, ∃ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs ∧ DifferentiableOn ℂ b Hs ∧
      (b : Mero) ≠ 0 ∧ X.an (f : X.K) * (b : Mero) ^ m = (a : Mero) ^ m := by
  intro Ω _ _ _ ε X _ _ m hm f hf
  obtain ⟨a, b, ha, hb, hb0, hab⟩ := X.an_mero (f : X.K)
  obtain ⟨g, hg, hgm⟩ := rootHs (fun z => a z * b z ^ (m - 1)) m hm (ha.mul (hb.pow _))
    (orders_dvd X m hm f hf a b hb hab)
  refine ⟨g, b, hg, hb, hb0, ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have e : ((fun z => a z * b z ^ n : ℂ → ℂ) : Mero) = ((fun z => g z ^ (n + 1) : ℂ → ℂ) : Mero) := by
    refine Filter.Germ.coe_eq.2 ?_
    filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz
    simpa using (hgm z hz).symm
  rw [pow_succ, mul_comm ((b : Mero) ^ n), ← mul_assoc, hab, ← Filter.Germ.coe_pow, ← Filter.Germ.coe_pow,
    ← Filter.Germ.coe_mul]
  exact e

end GlobalTheory.KZ.MeroRoot
