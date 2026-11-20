import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FinConstFor
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperNormalCompactificationStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HermitianSignatureBasisStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLinePAdicBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeValuationAgreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLinePAdicFrameStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FinAll

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
Establish `h : (exteriorPower.ιMulti R r (M` using `M)).compLinearMap S.subtype = c.det.smulRight (exteriorPower.ιMulti R r (fun i => (c i : M))) := by`. Use `Module.Basis.ext_alternating c fun i hi => ?_` and prove the remaining obligations. Set `σ : Equiv.Perm (Fin r)` to `Equiv.ofBijective i (Finite.injective_iff_bijective.1 hi)`. Express the relevant statement in the definitionally equal form `((exteriorPower.ιMulti R r (M := M)).compLinearMap S.subtype) (c ∘ σ) = c.det (c ∘ σ) • exteriorPower.ιMulti R r (fun i => (c i : M))`. Rewrite using `[AlternatingMap.map_perm, AlternatingMap.map_perm, Module.Basis.det_self, smul_assoc, one_smul]`.

Both sides reduce to the same expression. Conclude with `DFunLike.congr_fun h v`.
-/
theorem iotaMulti_coe_eq_det_smul {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {r : ℕ}
    {S : Submodule R M} (c : Module.Basis (Fin r) R S) (v : Fin r → S) :
    exteriorPower.ιMulti R r (fun i => (v i : M)) =
      c.det v • exteriorPower.ιMulti R r (fun i => (c i : M)) := by
  have h : (exteriorPower.ιMulti R r (M := M)).compLinearMap S.subtype =
      c.det.smulRight (exteriorPower.ιMulti R r (fun i => (c i : M))) := by
    refine Module.Basis.ext_alternating c fun i hi => ?_
    let σ : Equiv.Perm (Fin r) := Equiv.ofBijective i (Finite.injective_iff_bijective.1 hi)
    change ((exteriorPower.ιMulti R r (M := M)).compLinearMap S.subtype) (c ∘ σ) =
      c.det (c ∘ σ) • exteriorPower.ιMulti R r (fun i => (c i : M))
    rw [AlternatingMap.map_perm, AlternatingMap.map_perm, Module.Basis.det_self, smul_assoc, one_smul]
    rfl
  exact DFunLike.congr_fun h v

/- English proof (translation)
Establish `hmem : α • a ∈ (L.inter S).wedge n x` using `by rw [h]; exact Submodule.mem_span_singleton_self _`. Establish `key : ∀ y ∈ (L.inter S).wedge n x, ∃ c : Ω, y = c • exteriorPower.ιMulti Ω n v`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨b, hb, rfl⟩` from `hy`. Set `e : Module.Basis (Fin n) Ω (Submodule.span Ω (Set.range v))` to `Module.Basis.span hv`. Set `b' : Fin n → Submodule.span Ω (Set.range v)` to `fun i => ⟨b i, by rw [hS]; exact (hb i).2⟩`. Use `⟨e.det b', ?_⟩` and prove the remaining obligations. Establish `h1` using `iotaMulti_coe_eq_det_smul e b'`.

Establish `h2 : (fun i => ((e i : Submodule.span Ω (Set.range v)) : V)) = v`. Use function extensionality and compare the values at `i`. Use `show ((Module.Basis.span hv i : Submodule.span Ω (Set.range v)) : V) = v i`. Rewrite using `[Module.Basis.span_apply]`. Rewrite `h1` using `[h2]`.

Conclude with `h1`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨c, rfl⟩` from `hy`. Take `⟨d, rfl⟩` from `hz`.

Conclude with `⟨c + d, by rw [add_smul]⟩`. Consider the case `smul r y _ hy`. Take `⟨c, rfl⟩` from `hy`. Conclude with `⟨(r : Ω) * c, by rw [Subring.smul_def, smul_smul]⟩`. Take `⟨c, hc⟩` from `key _ hmem`.

Use `⟨α⁻¹ * c, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul, ← hc, smul_smul, inv_mul_cancel₀ hα, one_smul]`.
-/
theorem exists_smul_iotaMulti {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {V : Type} [AddCommGroup V] [Module Ω V] (L : Lat ξ V) (S : Submodule Ω V) {n : ℕ} (v : Fin n → V)
    (a : ⋀[Ω]^n V) (x : Cpt ξ) (α : Ω) (hα : α ≠ 0) (hv : LinearIndependent Ω v)
    (hS : Submodule.span Ω (Set.range v) = S)
    (h : (L.inter S).wedge n x = Submodule.span (regAt ξ x) {α • a}) :
    ∃ c : Ω, a = c • exteriorPower.ιMulti Ω n v := by
  have hmem : α • a ∈ (L.inter S).wedge n x := by rw [h]; exact Submodule.mem_span_singleton_self _
  have key : ∀ y ∈ (L.inter S).wedge n x, ∃ c : Ω, y = c • exteriorPower.ιMulti Ω n v := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      let e : Module.Basis (Fin n) Ω (Submodule.span Ω (Set.range v)) := Module.Basis.span hv
      let b' : Fin n → Submodule.span Ω (Set.range v) := fun i => ⟨b i, by rw [hS]; exact (hb i).2⟩
      refine ⟨e.det b', ?_⟩
      have h1 := iotaMulti_coe_eq_det_smul e b'
      have h2 : (fun i => ((e i : Submodule.span Ω (Set.range v)) : V)) = v := by
        funext i; show ((Module.Basis.span hv i : Submodule.span Ω (Set.range v)) : V) = v i
        rw [Module.Basis.span_apply]
      rw [h2] at h1
      exact h1
    | zero => exact ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨c, rfl⟩ := hy
      obtain ⟨d, rfl⟩ := hz
      exact ⟨c + d, by rw [add_smul]⟩
    | smul r y _ hy =>
      obtain ⟨c, rfl⟩ := hy
      exact ⟨(r : Ω) * c, by rw [Subring.smul_def, smul_smul]⟩
  obtain ⟨c, hc⟩ := key _ hmem
  refine ⟨α⁻¹ * c, ?_⟩
  rw [mul_smul, ← hc, smul_smul, inv_mul_cancel₀ hα, one_smul]

/- English proof (translation)
Establish `hy : IsIntegral ℤ (κ x)`. Apply the tactic sequence `convert map_isIntegral_int κ hx using 1 <;> first | exact Subsingleton.elim _ _ | rfl`. Establish `h1 : IsIntegral (NormedField.valuation (K` using `ℂ_[p])).integer (κ x) := hy.tower_top`. Establish `h2` using `(Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).mem_of_integral h1`. Establish `h3 : ‖κ x‖₊ ≤ 1` using `h2`.

Conclude with `h3` after adjusting the coercions.
-/
theorem norm_le_one_of_isIntegral (p : Nat.Primes) (R : Type) [CommRing R] (κ : R →+* ℂ_[p]) (x : R)
    (hx : IsIntegral ℤ x) : ‖κ x‖ ≤ 1 := by
  have hy : IsIntegral ℤ (κ x) := by
    convert map_isIntegral_int κ hx using 1 <;> first | exact Subsingleton.elim _ _ | rfl
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[p])).integer (κ x) := hy.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).mem_of_integral h1
  have h3 : ‖κ x‖₊ ≤ 1 := h2
  exact_mod_cast h3

/- English proof (translation)
Distinguish the cases in `hx : ‖κ x‖ ≤ 1`. Conclude with `Or.inl ((h x).1 hx)`. Use `right`. Apply `(h _).1` to reduce the goal to its premises. Rewrite using `[map_inv₀, norm_inv]`.

Use `push_neg at hx`. Conclude with `inv_le_one_of_one_le₀ hx.le`.
-/
theorem mem_or_inv_mem {F : Type} [Field F] {O : Type} [CommRing O] (β : O →+* F) {p : Nat.Primes}
    (κ : F →+* ℂ_[p]) (h : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ β.range) (x : F) : x ∈ β.range ∨ x⁻¹ ∈ β.range := by
  by_cases hx : ‖κ x‖ ≤ 1
  · exact Or.inl ((h x).1 hx)
  · right
    apply (h _).1
    rw [map_inv₀, norm_inv]
    push_neg at hx
    exact inv_le_one_of_one_le₀ hx.le

/- English proof (translation)
Break down `hr x with ⟨a, rfl⟩ | ⟨b, hb⟩` into its components or cases. Conclude with `⟨a, 1, one_ne_zero, by simp⟩`. Distinguish the cases in `hx : x = 0`. Conclude with `⟨0, 1, one_ne_zero, by simp [hx]⟩`. Use `⟨1, b, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `rfl`. Simplify using `at hb`. Conclude with `hx hb.symm`. Rewrite using `[hb, mul_inv_cancel₀ hx, map_one]`.
-/
theorem exists_frac {F : Type} [Field F] {O : Type} [CommRing O] [IsDomain O] (β : O →+* F)
    (hr : ∀ x : F, x ∈ β.range ∨ x⁻¹ ∈ β.range) (x : F) : ∃ a b : O, b ≠ 0 ∧ x * β b = β a := by
  rcases hr x with ⟨a, rfl⟩ | ⟨b, hb⟩
  · exact ⟨a, 1, one_ne_zero, by simp⟩
  · by_cases hx : x = 0
    · exact ⟨0, 1, one_ne_zero, by simp [hx]⟩
    · refine ⟨1, b, ?_, ?_⟩
      · rintro rfl; simp at hb; exact hx hb.symm
      · rw [hb, mul_inv_cancel₀ hx, map_one]

/- English proof (translation)
Rewrite using `[← map_natCast (algebraMap ℚ_[(p : ℕ)] ℂ_[(p : ℕ)]) (p : ℕ), norm_algebraMap', Padic.norm_p]`.
-/
theorem norm_natCast_prime (p : Nat.Primes) : ‖(((p : ℕ) : ℂ_[p]))‖ = ((p : ℕ) : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[(p : ℕ)] ℂ_[(p : ℕ)]) (p : ℕ), norm_algebraMap', Padic.norm_p]

/- English proof (translation)
Establish `hnu : ¬ IsUnit ((p : ℕ) : O)`. Introduce and unpack `⟨u, hu⟩`. Establish `hmem : ((p : ℕ) : F)⁻¹ ∈ β.range`. Use `⟨(u⁻¹ : Oˣ), ?_⟩` and prove the remaining obligations. Establish `h1 : β (u : O) * β ((u⁻¹ : Oˣ) : O) = 1` using `by rw [← map_mul, Units.mul_inv, map_one]`.

Rewrite `h1` using `[hu, map_natCast]`. Conclude with `(eq_inv_of_mul_eq_one_right h1)`. Establish `hle` using `(h _).2 hmem`. Rewrite `hle` using `[map_inv₀, map_natCast, norm_inv, norm_natCast_prime, inv_inv]`. Establish `h1 : (1 : ℝ) < (p : ℕ)` using `by exact_mod_cast p.2.one_lt`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hm : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O` using `(IsLocalRing.mem_maximalIdeal _).2 hnu`. Rewrite `hm` using `[hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]`. Conclude with `hm`.
-/
theorem dvd_prime {F : Type} [Field F] [CharZero F] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (β : O →+* F) {p : Nat.Primes}
    (κ : F →+* ℂ_[p]) (h : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ β.range) {ϖ : O} (hϖ : Irreducible ϖ) :
    ϖ ∣ ((p : ℕ) : O) := by
  have hnu : ¬ IsUnit ((p : ℕ) : O) := by
    rintro ⟨u, hu⟩
    have hmem : ((p : ℕ) : F)⁻¹ ∈ β.range := by
      refine ⟨(u⁻¹ : Oˣ), ?_⟩
      have h1 : β (u : O) * β ((u⁻¹ : Oˣ) : O) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
      rw [hu, map_natCast] at h1
      exact (eq_inv_of_mul_eq_one_right h1)
    have hle := (h _).2 hmem
    rw [map_inv₀, map_natCast, norm_inv, norm_natCast_prime, inv_inv] at hle
    have h1 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.one_lt
    linarith
  have hm : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hnu
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  exact hm

/- English proof (translation)
Use `letI : Algebra O Ω := (inc.comp β).toAlgebra`. Introduce `a ha`. Take `⟨f, hf0, hfa⟩` from `ha`. Take `⟨y, rfl⟩` from `hg a ⟨f.map β, (Polynomial.map_ne_zero_iff hβ).2 hf0, by`. Rewrite using `[Polynomial.eval₂_map]`.

Conclude with `hfa⟩`. Take `⟨x', y', hy', e⟩` from `hfr y`. Use `⟨x', y', hy', ?_⟩` and prove the remaining obligations. Use `show inc y * inc (β y') = inc (β x')`. Rewrite using `[← map_mul, e]`.
-/
theorem constClosed_of_isGeom {F : Type} [Field F] {Ω : Type} [Field Ω] {O : Type} [CommRing O]
    (β : O →+* F) (inc : F →+* Ω) (hβ : Function.Injective β)
    (hfr : ∀ x : F, ∃ a b : O, b ≠ 0 ∧ x * β b = β a)
    (hg : ∀ x : Ω, (∃ f : Polynomial F, f ≠ 0 ∧ f.eval₂ inc x = 0) → x ∈ Set.range inc) :
    @ConstClosed O Ω _ _ (inc.comp β).toAlgebra := by
  letI : Algebra O Ω := (inc.comp β).toAlgebra
  intro a ha
  obtain ⟨f, hf0, hfa⟩ := ha
  obtain ⟨y, rfl⟩ := hg a ⟨f.map β, (Polynomial.map_ne_zero_iff hβ).2 hf0, by
    rw [Polynomial.eval₂_map]; exact hfa⟩
  obtain ⟨x', y', hy', e⟩ := hfr y
  refine ⟨x', y', hy', ?_⟩
  show inc y * inc (β y') = inc (β x')
  rw [← map_mul, e]

/- English proof (translation)
Set `b` to `Module.finBasisOfFinrankEq K S h`. Establish `hli : LinearIndependent K (S.subtype ∘ b)` using `b.linearIndependent.map' S.subtype S.ker_subtype`. Use `⟨S.subtype ∘ b, hli, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]`.
-/
theorem exists_basis_of_finrank {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S : Submodule K V) {n : ℕ} (h : Module.finrank K S = n) :
    ∃ v : Fin n → V, LinearIndependent K v ∧ Submodule.span K (Set.range v) = S := by
  let b := Module.finBasisOfFinrankEq K S h
  have hli : LinearIndependent K (S.subtype ∘ b) := b.linearIndependent.map' S.subtype S.ker_subtype
  refine ⟨S.subtype ∘ b, hli, ?_⟩
  rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c O _ _ _ β Y U Z τ p κ φ hτ hβ hnorm hsplit hN3 hgeom hflat hline`. Establish `hr` using `mem_or_inv_mem β κ hnorm`. Establish `hfr` using `exists_frac β hr`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hdvd : ϖ ∣ ((p : ℕ) : O)` using `dvd_prime β κ hnorm hϖ`.

Take `⟨hprop, hnormal, hover, hgf, hfd, hrk, hrk'⟩` from `GlobalTheory.T.proper_normal_compactification E H D l Xo c O β Y U Z τ hβ hfr hτ`. Use `letI : Algebra O Z.Ω := (Z.inc.comp β).toAlgebra`. Use `haveI := hfd`. Use `haveI := hprop`. Use `haveI : CharZero Z.Ω := (RingHom.charZero_iff Z.inc.injective).1 inferInstance`.

Set `σ : E →+* Z.Ω` to `Z.inc.comp (τ.codRestrict c.F.toSubfield (c.conj τ) : E →+* c.F)`. Set `σ' : E →+* Z.Ω` to `Z.inc.comp ((ComplexEmbedding.conjugate τ).codRestrict c.F.toSubfield (c.conj _) : E →+* c.F)`. Establish `hσ : ∀ b : 𝓞 E, σ (b : E) = Z.inc (tauIn c τ b)` using `fun b => rfl`. Establish `hbar : ∀ a : 𝓞 E, σ' (a : E) = σ (H.bar a : 𝓞 E)`. Introduce `a`.

Use `show Z.inc _ = Z.inc _`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (ComplexEmbedding.conjugate τ) (a : E) = τ ((H.bar a : 𝓞 E) : E)`. Rewrite using `[H.bar_eq, IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]`.

Establish `hinv : ∀ a, H.bar (H.bar a) = a`. Introduce `a`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[H.bar_eq, IsCMField.complexEmbedding_complexConj, H.bar_eq, IsCMField.complexEmbedding_complexConj, Complex.conj_conj]`.

Establish `heig : HT.eigSp Z.ρ σ = eigSp Z.ρ (Z.inc.comp (tauIn c τ))` using `rfl`. Establish `heig' : HT.eigSp Z.ρ σ' = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ)))` using `rfl`. Take `⟨v, hvli, hvsp⟩` from `exists_basis_of_finrank (HT.eigSp Z.ρ σ) (heig ▸ hrk)`. Take `⟨w, hwli, hwsp⟩` from `exists_basis_of_finrank (HT.eigSp Z.ρ σ') (heig' ▸ hrk')`. Take `⟨𝓗, hdeg⟩` from `GlobalTheory.T.eigen_line_p_adic_bound E H D l Xo c O β Y U Z τ ϖ (p : ℕ) hϖ p.2 hdvd hβ hr hsplit hN3`.

Take `⟨u, hu, -, -⟩` from `GlobalTheory.T.hermitian_signature_basis E Z.Ω Z.V Z.ρ 𝓗.ρH H.bar σ σ' D.p D.q v w 𝓗.act_fst 𝓗.act_inr hbar hinv hvli hvsp hwli hwsp`. Take `⟨-, a, b, ⟨ha0, hb0, hco⟩, hrep⟩` from `hflat`. Set `x₀ : Cpt (Z.ξ₀ ≫ Y.j)` to `⟨genPt (Z.ξ₀ ≫ Y.j), specializes_rfl⟩`. Establish `hx₀ : x₀ ∈ Z.genFib` using `⟨Y.jQ (genPt Z.ξ₀), rfl⟩`. Take `⟨α₁, β₁, hα₁, hβ₁, hA, hB, -⟩` from `hco x₀ hx₀`.

Take `⟨α, rfl⟩` from `exists_smul_iotaMulti Z.M.lat (HT.eigSp Z.ρ σ) v a x₀ α₁ hα₁ hvli hvsp hA`. Take `⟨κ', rfl⟩` from `exists_smul_iotaMulti Z.M.lat (HT.eigSp Z.ρ σ') w b x₀ β₁ hβ₁ hwli hwsp hB`. Establish `hκ' : κ' ≠ 0` using `fun h => hb0 (by rw [h, zero_smul])`. Establish `hgfe : Z.genFib = genFibre O (Z.ξ₀ ≫ Y.j)` using `Set.ext fun x => hgf x`. Establish `hline' : IsLineGenOn (Z.M.lat.inter (HT.eigSp Z.ρ σ)) (Z.M.lat.inter (HT.eigSp Z.ρ σ')) D.p D.q (α • exteriorPower.ιMulti Z.Ω D.p v) (κ' • exteriorPower.ιMulti Z.Ω D.q w) (genFibre O (Z.ξ₀ ≫ Y.j))`.

Rewrite using `[← hgfe]`. Conclude with `⟨ha0, hb0, hco⟩`. Establish `hinjO : Function.Injective (algebraMap O Z.Ω)` using `Z.inc.injective.comp hβ`. Establish `hσrange : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap O Z.Ω).range`. Introduce `a`.

Take `⟨o, ho⟩` from `(hnorm (tauIn c τ a)).1 (norm_le_one_of_isIntegral p (𝓞 E) (κ.comp (tauIn c τ)) a (RingOfIntegers.isIntegral a))`. Conclude with `⟨o, by show Z.inc (β o) = Z.inc (tauIn c τ a); rw [ho]⟩`. Establish `hcc : ConstClosed O Z.Ω` using `constClosed_of_isGeom β Z.inc hβ hfr hgeom`. Take `⟨M, k, hM, hord⟩` from `GlobalTheory.T.hodge_lattice_valuation_agree Y.X Z.Ω (Z.ξ₀ ≫ Y.j) E Z.V Z.M.lat Z.ρ H.bar D.p D.q 𝓗 σ σ' v w u α κ' O Y.s ϖ hϖ hinjO hover Z.gen hnormal hcc hσrange hbar hinv hvli hvsp hwli hwsp hu (hdeg σ) hline'`. Conclude with `GlobalTheory.T.eigen_line_p_adic_frame E H D l Xo c O β Y U Z τ ϖ p κ φ 𝓗 σ v w u α κ' M k hτ hϖ hβ hnorm hσ hvli hvsp hwli (hwsp.trans heig') hu hM hord hκ' hrep hline`.
-/
theorem finConstAll : FinConstAll := by
  intro E _ _ _ H D l Xo c O _ _ _ β Y U Z τ p κ φ hτ hβ hnorm hsplit hN3 hgeom hflat hline
  have hr := mem_or_inv_mem β κ hnorm
  have hfr := exists_frac β hr
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hdvd : ϖ ∣ ((p : ℕ) : O) := dvd_prime β κ hnorm hϖ
  obtain ⟨hprop, hnormal, hover, hgf, hfd, hrk, hrk'⟩ :=
    GlobalTheory.T.proper_normal_compactification E H D l Xo c O β Y U Z τ hβ hfr hτ
  letI : Algebra O Z.Ω := (Z.inc.comp β).toAlgebra
  haveI := hfd
  haveI := hprop
  haveI : CharZero Z.Ω := (RingHom.charZero_iff Z.inc.injective).1 inferInstance
  let σ : E →+* Z.Ω := Z.inc.comp (τ.codRestrict c.F.toSubfield (c.conj τ) : E →+* c.F)
  let σ' : E →+* Z.Ω := Z.inc.comp
    ((ComplexEmbedding.conjugate τ).codRestrict c.F.toSubfield (c.conj _) : E →+* c.F)
  have hσ : ∀ b : 𝓞 E, σ (b : E) = Z.inc (tauIn c τ b) := fun b => rfl
  have hbar : ∀ a : 𝓞 E, σ' (a : E) = σ (H.bar a : 𝓞 E) := by
    intro a
    show Z.inc _ = Z.inc _
    congr 1
    apply Subtype.ext
    show (ComplexEmbedding.conjugate τ) (a : E) = τ ((H.bar a : 𝓞 E) : E)
    rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]
  have hinv : ∀ a, H.bar (H.bar a) = a := by
    intro a
    apply RingOfIntegers.ext
    apply τ.injective
    rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, H.bar_eq, IsCMField.complexEmbedding_complexConj,
      Complex.conj_conj]
  have heig : HT.eigSp Z.ρ σ = eigSp Z.ρ (Z.inc.comp (tauIn c τ)) := rfl
  have heig' : HT.eigSp Z.ρ σ' = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) := rfl
  obtain ⟨v, hvli, hvsp⟩ := exists_basis_of_finrank (HT.eigSp Z.ρ σ) (heig ▸ hrk)
  obtain ⟨w, hwli, hwsp⟩ := exists_basis_of_finrank (HT.eigSp Z.ρ σ') (heig' ▸ hrk')
  obtain ⟨𝓗, hdeg⟩ := GlobalTheory.T.eigen_line_p_adic_bound E H D l Xo c O β Y U Z τ ϖ (p : ℕ) hϖ p.2 hdvd hβ hr hsplit hN3
  obtain ⟨u, hu, -, -⟩ := GlobalTheory.T.hermitian_signature_basis E Z.Ω Z.V Z.ρ 𝓗.ρH H.bar σ σ' D.p D.q v w 𝓗.act_fst 𝓗.act_inr
    hbar hinv hvli hvsp hwli hwsp
  obtain ⟨-, a, b, ⟨ha0, hb0, hco⟩, hrep⟩ := hflat
  let x₀ : Cpt (Z.ξ₀ ≫ Y.j) := ⟨genPt (Z.ξ₀ ≫ Y.j), specializes_rfl⟩
  have hx₀ : x₀ ∈ Z.genFib := ⟨Y.jQ (genPt Z.ξ₀), rfl⟩
  obtain ⟨α₁, β₁, hα₁, hβ₁, hA, hB, -⟩ := hco x₀ hx₀
  obtain ⟨α, rfl⟩ := exists_smul_iotaMulti Z.M.lat (HT.eigSp Z.ρ σ) v a x₀ α₁ hα₁ hvli hvsp hA
  obtain ⟨κ', rfl⟩ := exists_smul_iotaMulti Z.M.lat (HT.eigSp Z.ρ σ') w b x₀ β₁ hβ₁ hwli hwsp hB
  have hκ' : κ' ≠ 0 := fun h => hb0 (by rw [h, zero_smul])
  have hgfe : Z.genFib = genFibre O (Z.ξ₀ ≫ Y.j) := Set.ext fun x => hgf x
  have hline' : IsLineGenOn (Z.M.lat.inter (HT.eigSp Z.ρ σ)) (Z.M.lat.inter (HT.eigSp Z.ρ σ')) D.p D.q
      (α • exteriorPower.ιMulti Z.Ω D.p v) (κ' • exteriorPower.ιMulti Z.Ω D.q w)
      (genFibre O (Z.ξ₀ ≫ Y.j)) := by
    rw [← hgfe]; exact ⟨ha0, hb0, hco⟩
  have hinjO : Function.Injective (algebraMap O Z.Ω) := Z.inc.injective.comp hβ
  have hσrange : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap O Z.Ω).range := by
    intro a
    obtain ⟨o, ho⟩ := (hnorm (tauIn c τ a)).1
      (norm_le_one_of_isIntegral p (𝓞 E) (κ.comp (tauIn c τ)) a (RingOfIntegers.isIntegral a))
    exact ⟨o, by show Z.inc (β o) = Z.inc (tauIn c τ a); rw [ho]⟩
  have hcc : ConstClosed O Z.Ω := constClosed_of_isGeom β Z.inc hβ hfr hgeom
  obtain ⟨M, k, hM, hord⟩ := GlobalTheory.T.hodge_lattice_valuation_agree Y.X Z.Ω (Z.ξ₀ ≫ Y.j) E Z.V Z.M.lat Z.ρ H.bar D.p D.q 𝓗 σ σ'
    v w u α κ' O Y.s ϖ hϖ hinjO hover Z.gen hnormal hcc hσrange hbar hinv hvli hvsp hwli hwsp hu (hdeg σ) hline'
  exact GlobalTheory.T.eigen_line_p_adic_frame E H D l Xo c O β Y U Z τ ϖ p κ φ 𝓗 σ v w u α κ' M k hτ hϖ hβ hnorm hσ hvli hvsp hwli
    (hwsp.trans heig') hu hM hord hκ' hrep hline

end GlobalTheory.CompanionTheory.Ar.Flat.FinAll
