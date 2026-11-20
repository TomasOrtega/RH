import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.MemMCoordIdealOfAevalEqZero

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo

namespace OverUnique

open GroundTheory.Heights₂.Heights.LowerBoundFree

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Establish `h : algebraMap ℤ ℂ = Int.castRingHom ℂ` using `RingHom.ext_int _ _`. Simplify using `only [evC, eval_map, aeval_def, h]`.
-/
theorem evC_eq_aeval (z : (Σ k, ι k) → ℂ) (g : MRing ι) : evC z g = aeval z g := by
  have h : algebraMap ℤ ℂ = Int.castRingHom ℂ := RingHom.ext_int _ _
  simp only [evC, eval_map, aeval_def, h]

/- English proof (translation)
Introduce `m hm k`. Rewrite `hm` using `[support_X, Finset.mem_singleton]`. Substitute `hm` using the available equality. Take `⟨k0, i0⟩` from `p`. Distinguish the cases in `h : k = k0`.

Substitute `h` using the available equality. Simplify using `[Finsupp.single_apply]`. Establish `h' : ∀ i : ι k, ¬ ((⟨k0, i0⟩ : Σ k, ι k) = ⟨k, i⟩)` using `fun i e => h (congrArg Sigma.fst e).symm`. Simplify using `[Finsupp.single_apply, h', h]`.
-/
theorem homog_X [DecidableEq K] (p : Σ k, ι k) : IsMultiHomog (X p : MRing ι) (Pi.single p.1 1) := by
  classical
  intro m hm k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  obtain ⟨k0, i0⟩ := p
  by_cases h : k = k0
  · subst h
    simp [Finsupp.single_apply]
  · have h' : ∀ i : ι k, ¬ ((⟨k0, i0⟩ : Σ k, ι k) = ⟨k, i⟩) := fun i e => h (congrArg Sigma.fst e).symm
    simp [Finsupp.single_apply, h', h]

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Use `isMultiHomog_add hg ?_` and prove the remaining obligations. Introduce `m hm`. Conclude with `hh m (by simpa using hm)`.
-/
theorem homog_sub {g h : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) (hh : IsMultiHomog h d) :
    IsMultiHomog (g - h) d := by
  rw [sub_eq_add_neg]
  refine isMultiHomog_add hg ?_
  intro m hm
  exact hh m (by simpa using hm)

/- English proof (translation)
Proceed by induction on `G using MvPolynomial.induction_on with`. Consider the case `C a`. Use `⟨0, C a, 1, ?_, isMultiHomog_one, fun L _ w hw => ?_⟩` and prove the remaining obligations. Introduce `m hm k`. Use `support_monomial_subset hm` as an intermediate fact.

Simplify using `at this`. Simplify using `[this]`. Simplify using the standard rewrite rules. Consider the case `add p q hp hq`. Take `⟨D₁, H₁, M₁, h₁, m₁, e₁⟩` from `hp`.

Take `⟨D₂, H₂, M₂, h₂, m₂, e₂⟩` from `hq`. Use `⟨D₁ + D₂, H₁ * M₂ + H₂ * M₁, M₁ * M₂, isMultiHomog_add (isMultiHomog_mul h₁ m₂) (by rw [add_comm D₁]; exact isMultiHomog_mul h₂ m₁), isMultiHomog_mul m₁ m₂, fun L _ w hw => ?_⟩` and prove the remaining obligations. Take `⟨n₁, f₁⟩` from `e₁ L w hw`. Take `⟨n₂, f₂⟩` from `e₂ L w hw`. Use `⟨by rw [map_mul]; exact mul_ne_zero n₁ n₂, ?_⟩` and prove the remaining obligations.

Simplify using `only [map_add, map_mul, f₁, f₂]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul_X p i hp`. Take `⟨D, H, M, h, m, e⟩` from `hp`. Establish `hX₁ : IsMultiHomog (X i : MRing ι) (Pi.single i.1 1 : K → ℕ)` using `homog_X i`.

Establish `hX₂ : IsMultiHomog (X ⟨i.1, c i.1⟩ : MRing ι) (Pi.single i.1 1 : K → ℕ)` using `homog_X (⟨i.1, c i.1⟩ : Σ k, ι k)`. Establish `hH` using `isMultiHomog_mul h hX₁`. Establish `hM` using `isMultiHomog_mul m hX₂`. Use `⟨_, _, _, hH, hM, fun L _ w hw => ?_⟩` and prove the remaining obligations. Take `⟨n, f⟩` from `e L w hw`.

Establish `hc` using `hw i.1`. Use `⟨by rw [map_mul, aeval_X]; exact mul_ne_zero n hc, ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, aeval_X, f]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_form (c : ∀ k, ι k) (G : MRing ι) :
    ∃ (D : K → ℕ) (H M : MRing ι), IsMultiHomog H D ∧ IsMultiHomog M D ∧
      ∀ (L : Type) [Field L] (w : (Σ k, ι k) → L), (∀ k, w ⟨k, c k⟩ ≠ 0) →
        aeval w M ≠ 0 ∧ aeval w H = aeval w M * aeval (fun p => w p / w ⟨p.1, c p.1⟩) G := by
  classical
  induction G using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, C a, 1, ?_, isMultiHomog_one, fun L _ w hw => ?_⟩
    · intro m hm k
      have := support_monomial_subset hm
      simp at this
      simp [this]
    · simp
  | add p q hp hq =>
    obtain ⟨D₁, H₁, M₁, h₁, m₁, e₁⟩ := hp
    obtain ⟨D₂, H₂, M₂, h₂, m₂, e₂⟩ := hq
    refine ⟨D₁ + D₂, H₁ * M₂ + H₂ * M₁, M₁ * M₂,
      isMultiHomog_add (isMultiHomog_mul h₁ m₂) (by rw [add_comm D₁]; exact isMultiHomog_mul h₂ m₁),
      isMultiHomog_mul m₁ m₂, fun L _ w hw => ?_⟩
    obtain ⟨n₁, f₁⟩ := e₁ L w hw
    obtain ⟨n₂, f₂⟩ := e₂ L w hw
    refine ⟨by rw [map_mul]; exact mul_ne_zero n₁ n₂, ?_⟩
    simp only [map_add, map_mul, f₁, f₂]
    ring
  | mul_X p i hp =>
    obtain ⟨D, H, M, h, m, e⟩ := hp
    have hX₁ : IsMultiHomog (X i : MRing ι) (Pi.single i.1 1 : K → ℕ) := homog_X i
    have hX₂ : IsMultiHomog (X ⟨i.1, c i.1⟩ : MRing ι) (Pi.single i.1 1 : K → ℕ) :=
      homog_X (⟨i.1, c i.1⟩ : Σ k, ι k)
    have hH := isMultiHomog_mul h hX₁
    have hM := isMultiHomog_mul m hX₂
    refine ⟨_, _, _, hH, hM, fun L _ w hw => ?_⟩
    obtain ⟨n, f⟩ := e L w hw
    have hc := hw i.1
    refine ⟨by rw [map_mul, aeval_X]; exact mul_ne_zero n hc, ?_⟩
    simp only [map_mul, aeval_X, f]
    field_simp

variable {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}

/- English proof (translation)
Rewrite using `[← evC_eq_aeval]`. Conclude with `hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hP h0)`.
-/
theorem aeval_eq_zero {P : MRing ι} {d : K → ℕ} (hz : z ∈ mcPts (mCoordIdeal y)) (hP : IsMultiHomog P d)
    (h0 : aeval y P = 0) : aeval z P = 0 := by
  rw [← evC_eq_aeval]
  exact hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hP h0)

/- English proof (translation)
Introduce `h0`. Apply `h` to reduce the goal to its premises. Use `aeval_eq_zero hz (homog_X (⟨k, i⟩ : Σ k, ι k)) (by rw [aeval_X]; exact h0)` as an intermediate fact. Simplify using `using this`.
-/
theorem chart_ne {k : K} {i : ι k} (hz : z ∈ mcPts (mCoordIdeal y)) (h : z ⟨k, i⟩ ≠ 0) : y ⟨k, i⟩ ≠ 0 := by
  classical
  intro h0
  apply h
  have := aeval_eq_zero hz (homog_X (⟨k, i⟩ : Σ k, ι k)) (by rw [aeval_X]; exact h0)
  simpa using this

/- English proof (translation)
Take `⟨D, H, M, h, m, e⟩` from `exists_form c G`. Take `⟨-, fy⟩` from `e Ω y hy`. Take `⟨nz, fz⟩` from `e ℂ z hc`. Rewrite `fy` using `[h0, mul_zero]`. Use `aeval_eq_zero hz h fy` as an intermediate fact.

Rewrite `this` using `[fz]`. Conclude with `(mul_eq_zero.mp this).resolve_left nz`.
-/
theorem chart_ker (hz : z ∈ mcPts (mCoordIdeal y)) {c : ∀ k, ι k} (hc : ∀ k, z ⟨k, c k⟩ ≠ 0)
    (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) {G : MRing ι} (h0 : aeval (fun p => y p / y ⟨p.1, c p.1⟩) G = 0) :
    aeval (fun p => z p / z ⟨p.1, c p.1⟩) G = 0 := by
  obtain ⟨D, H, M, h, m, e⟩ := exists_form c G
  obtain ⟨-, fy⟩ := e Ω y hy
  obtain ⟨nz, fz⟩ := e ℂ z hc
  rw [h0, mul_zero] at fy
  have := aeval_eq_zero hz h fy
  rw [fz] at this
  exact (mul_eq_zero.mp this).resolve_left nz

/- English proof (translation)
Use `set v : (Σ k, ι k) → Ω := fun p => y p / y ⟨p.1, c p.1⟩ with hv`. Use `set u : (Σ k, ι k) → ℂ := fun p => z p / z ⟨p.1, c p.1⟩ with hu`. Set `A : MRing ι →ₐ[ℤ] Ω` to `aeval v`. Set `ψ : MRing ι →+* A.range` to `(A.rangeRestrict : MRing ι →+* A.range)`. Set `ψ' : MRing ι →+* ℂ` to `((aeval u : MRing ι →ₐ[ℤ] ℂ) : MRing ι →+* ℂ)`.

Establish `hs : Function.Surjective ψ` using `A.rangeRestrict_surjective`. Establish `hker : RingHom.ker ψ ≤ RingHom.ker ψ'`. Introduce `G hGk`. Rewrite `hGk`, the goal using `[RingHom.mem_ker]`. Establish `h1 : aeval v G = 0` using `congrArg Subtype.val hGk`.

Conclude with `chart_ker hz hc hy h1`. Set `l : A.range →+* ℂ` to `RingHom.liftOfSurjective ψ hs ⟨ψ', hker⟩`. Establish `hl : ∀ G, l (ψ G) = ψ' G` using `fun G => RingHom.liftOfRightInverse_comp_apply ψ _ _ ⟨ψ', hker⟩ G`. Set `ρ : 𝓞 F →+* A.range` to `(φ.comp (algebraMap (𝓞 F) F)).codRestrict A.range (fun a => by`. Take `⟨G, hG'⟩` from `hG a`.

Conclude with `⟨G, hG'⟩)`. Use `⟨l.comp ρ, fun a G h => ?_⟩` and prove the remaining obligations. Establish `: ρ a = ψ G` using `Subtype.ext h.symm`. Rewrite using `[RingHom.comp_apply, this, hl]`. Both sides reduce to the same expression.
-/
theorem exists_intHom (φ : F →+* Ω) (hz : z ∈ mcPts (mCoordIdeal y)) {c : ∀ k, ι k}
    (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) (hy : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (hG : ∀ a : 𝓞 F, ∃ G : MRing ι, aeval (fun p => y p / y ⟨p.1, c p.1⟩) G = φ (a : F)) :
    ∃ τ : 𝓞 F →+* ℂ, ∀ (a : 𝓞 F) (G : MRing ι), aeval (fun p => y p / y ⟨p.1, c p.1⟩) G = φ (a : F) →
      τ a = aeval (fun p => z p / z ⟨p.1, c p.1⟩) G := by
  set v : (Σ k, ι k) → Ω := fun p => y p / y ⟨p.1, c p.1⟩ with hv
  set u : (Σ k, ι k) → ℂ := fun p => z p / z ⟨p.1, c p.1⟩ with hu
  let A : MRing ι →ₐ[ℤ] Ω := aeval v
  let ψ : MRing ι →+* A.range := (A.rangeRestrict : MRing ι →+* A.range)
  let ψ' : MRing ι →+* ℂ := ((aeval u : MRing ι →ₐ[ℤ] ℂ) : MRing ι →+* ℂ)
  have hs : Function.Surjective ψ := A.rangeRestrict_surjective
  have hker : RingHom.ker ψ ≤ RingHom.ker ψ' := by
    intro G hGk
    rw [RingHom.mem_ker] at hGk ⊢
    have h1 : aeval v G = 0 := congrArg Subtype.val hGk
    exact chart_ker hz hc hy h1
  let l : A.range →+* ℂ := RingHom.liftOfSurjective ψ hs ⟨ψ', hker⟩
  have hl : ∀ G, l (ψ G) = ψ' G := fun G =>
    RingHom.liftOfRightInverse_comp_apply ψ _ _ ⟨ψ', hker⟩ G
  let ρ : 𝓞 F →+* A.range := (φ.comp (algebraMap (𝓞 F) F)).codRestrict A.range (fun a => by
    obtain ⟨G, hG'⟩ := hG a
    exact ⟨G, hG'⟩)
  refine ⟨l.comp ρ, fun a G h => ?_⟩
  have : ρ a = ψ G := Subtype.ext h.symm
  rw [RingHom.comp_apply, this, hl]
  rfl

/- English proof (translation)
Rewrite using `[RingHom.injective_iff_ker_eq_bot]`. Apply `Ideal.eq_bot_of_comap_eq_bot (R := ℤ)` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`. Introduce `n hn`. Rewrite `hn` using `[Ideal.mem_comap, RingHom.mem_ker]`.

Simplify using `using hn`.
-/
theorem intHom_injective (τ : 𝓞 F →+* ℂ) : Function.Injective τ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  rw [eq_bot_iff]
  intro n hn
  rw [Ideal.mem_comap, RingHom.mem_ker] at hn
  simpa using hn

end OverUnique

open OverUnique GroundTheory.Heights₂.Heights.LowerBoundFree in

/- English proof (translation)
Introduce `z hz`. Use `choose c hc using hz.1`. Establish `hy : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k => chart_ne hz (hc k)`. Establish `hG : ∀ a : 𝓞 F, ∃ G : MRing ι, aeval (fun p => y p / y ⟨p.1, c p.1⟩) G = φ (a : F)`. Introduce `a`.

Establish `h` using `hO.2 c hy a`. Rewrite `h` using `[chartRingZ, Algebra.adjoin_range_eq_range_aeval]`. Conclude with `h`. Take `⟨τ, hτ⟩` from `exists_intHom φ hz hc hy hG`. Establish `hinj` using `intHom_injective τ`.

Set `σ : F →+* ℂ` to `IsFractionRing.lift hinj`. Establish `hσ : ∀ a : 𝓞 F, σ (a : F) = τ a` using `fun a => IsFractionRing.lift_algebraMap hinj a`. Use `⟨σ, ⟨hz, fun a d g h hg hh he => ?_⟩, fun σ' hσ' => ?_⟩` and prove the remaining obligations. Take `⟨a₁, a₂, ha₂, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 F) a`. Establish `ha₂' : algebraMap (𝓞 F) F a₂ ≠ 0`.

Simplify using `using nonZeroDivisors.ne_zero ha₂`. Take `⟨G₁, e₁⟩` from `hG a₁`. Take `⟨G₂, e₂⟩` from `hG a₂`. Take `⟨D₁, H₁, M₁, h₁, m₁, f₁⟩` from `exists_form c G₁`. Take `⟨D₂, H₂, M₂, h₂, m₂, f₂⟩` from `exists_form c G₂`.

Take `⟨ny₁, y₁⟩` from `f₁ Ω y hy`. Take `⟨ny₂, y₂⟩` from `f₂ Ω y hy`. Take `⟨nz₁, z₁⟩` from `f₁ ℂ z hc`. Take `⟨nz₂, z₂⟩` from `f₂ ℂ z hc`. Establish `hP : IsMultiHomog (H₂ * M₁ * g - H₁ * M₂ * h) (D₁ + D₂ + d)`.

Use `homog_sub ?_ (isMultiHomog_mul (isMultiHomog_mul h₁ m₂) hh)` and prove the remaining obligations. Rewrite using `[add_comm D₁]`. Conclude with `isMultiHomog_mul (isMultiHomog_mul h₂ m₁) hg`. Establish `h0 : aeval y (H₂ * M₁ * g - H₁ * M₂ * h) = 0`. Establish `hφ : φ (algebraMap (𝓞 F) F a₂) ≠ 0` using `by simpa using ha₂'`.

Simplify using `only [map_sub, map_mul, y₁, y₂, he, e₁, e₂]`. Rewrite using `[map_div₀]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `aeval_eq_zero hz hP h0`.

Simplify using `only [map_sub, map_mul, z₁, z₂, ← hτ a₁ G₁ e₁, ← hτ a₂ G₂ e₂, ← evC_eq_aeval z g, ← evC_eq_aeval z h, ← hσ] at h1`. Establish `hs₂ : σ (algebraMap (𝓞 F) F a₂) ≠ 0` using `by simpa using ha₂'`. Rewrite using `[map_div₀]`. Establish `hM : aeval z M₁ * aeval z M₂ ≠ 0` using `mul_ne_zero nz₁ nz₂`. Establish `h2 : σ (algebraMap (𝓞 F) F a₂) * evC z g = σ (algebraMap (𝓞 F) F a₁) * evC z h`.

Apply `mul_left_cancel₀ hM` to reduce the goal to its premises. Take the linear combination `h1`. Clear the denominators using the available nonvanishing facts. Take the linear combination `h2`. Use `RingHom.ext fun a => ?_` and prove the remaining obligations.

Establish `key : ∀ a : 𝓞 F, σ' (a : F) = σ (a : F)`. Introduce `a`. Take `⟨G, e⟩` from `hG a`. Take `⟨D, H, M, h, m, f⟩` from `exists_form c G`. Take `⟨-, fy⟩` from `f Ω y hy`.

Take `⟨nz, fz⟩` from `f ℂ z hc`. Establish `hy' : aeval y H = φ (a : F) * aeval y M` using `by rw [fy, e, mul_comm]`. Establish `h1` using `hσ'.2 (a : F) D H M h m hy'`. Rewrite `h1` using `[evC_eq_aeval, evC_eq_aeval, fz]`. Rewrite using `[hσ, hτ a G e]`.

Use `mul_left_cancel₀ nz (h1.trans (mul_comm _ _))` as an intermediate fact. Conclude with `this.symm`. Take `⟨a₁, a₂, -, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 F) a`. Rewrite using `[map_div₀, map_div₀]`. Conclude with `congrArg₂ _ (key a₁) (key a₂)`.
-/
theorem existsUnique_ptOver (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (hO : OverInt y φ) :
    ∀ z ∈ mcPts (mCoordIdeal y), ∃! σ : F →+* ℂ, PtOver y φ σ z := by
  classical
  intro z hz
  choose c hc using hz.1
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => chart_ne hz (hc k)
  have hG : ∀ a : 𝓞 F, ∃ G : MRing ι, aeval (fun p => y p / y ⟨p.1, c p.1⟩) G = φ (a : F) := by
    intro a
    have h := hO.2 c hy a
    rw [chartRingZ, Algebra.adjoin_range_eq_range_aeval] at h
    exact h
  obtain ⟨τ, hτ⟩ := exists_intHom φ hz hc hy hG
  have hinj := intHom_injective τ
  let σ : F →+* ℂ := IsFractionRing.lift hinj
  have hσ : ∀ a : 𝓞 F, σ (a : F) = τ a := fun a => IsFractionRing.lift_algebraMap hinj a
  refine ⟨σ, ⟨hz, fun a d g h hg hh he => ?_⟩, fun σ' hσ' => ?_⟩
  · obtain ⟨a₁, a₂, ha₂, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) a
    have ha₂' : algebraMap (𝓞 F) F a₂ ≠ 0 := by
      simpa using nonZeroDivisors.ne_zero ha₂
    obtain ⟨G₁, e₁⟩ := hG a₁
    obtain ⟨G₂, e₂⟩ := hG a₂
    obtain ⟨D₁, H₁, M₁, h₁, m₁, f₁⟩ := exists_form c G₁
    obtain ⟨D₂, H₂, M₂, h₂, m₂, f₂⟩ := exists_form c G₂
    obtain ⟨ny₁, y₁⟩ := f₁ Ω y hy
    obtain ⟨ny₂, y₂⟩ := f₂ Ω y hy
    obtain ⟨nz₁, z₁⟩ := f₁ ℂ z hc
    obtain ⟨nz₂, z₂⟩ := f₂ ℂ z hc
    have hP : IsMultiHomog (H₂ * M₁ * g - H₁ * M₂ * h) (D₁ + D₂ + d) := by
      refine homog_sub ?_ (isMultiHomog_mul (isMultiHomog_mul h₁ m₂) hh)
      rw [add_comm D₁]
      exact isMultiHomog_mul (isMultiHomog_mul h₂ m₁) hg
    have h0 : aeval y (H₂ * M₁ * g - H₁ * M₂ * h) = 0 := by
      have hφ : φ (algebraMap (𝓞 F) F a₂) ≠ 0 := by simpa using ha₂'
      simp only [map_sub, map_mul, y₁, y₂, he, e₁, e₂]
      rw [map_div₀]
      field_simp
      ring
    have h1 := aeval_eq_zero hz hP h0
    simp only [map_sub, map_mul, z₁, z₂, ← hτ a₁ G₁ e₁, ← hτ a₂ G₂ e₂, ← evC_eq_aeval z g,
      ← evC_eq_aeval z h, ← hσ] at h1
    have hs₂ : σ (algebraMap (𝓞 F) F a₂) ≠ 0 := by simpa using ha₂'
    rw [map_div₀]
    have hM : aeval z M₁ * aeval z M₂ ≠ 0 := mul_ne_zero nz₁ nz₂
    have h2 : σ (algebraMap (𝓞 F) F a₂) * evC z g = σ (algebraMap (𝓞 F) F a₁) * evC z h := by
      apply mul_left_cancel₀ hM
      linear_combination h1
    field_simp
    linear_combination h2
  · refine RingHom.ext fun a => ?_
    have key : ∀ a : 𝓞 F, σ' (a : F) = σ (a : F) := by
      intro a
      obtain ⟨G, e⟩ := hG a
      obtain ⟨D, H, M, h, m, f⟩ := exists_form c G
      obtain ⟨-, fy⟩ := f Ω y hy
      obtain ⟨nz, fz⟩ := f ℂ z hc
      have hy' : aeval y H = φ (a : F) * aeval y M := by rw [fy, e, mul_comm]
      have h1 := hσ'.2 (a : F) D H M h m hy'
      rw [evC_eq_aeval, evC_eq_aeval, fz] at h1
      rw [hσ, hτ a G e]
      have := mul_left_cancel₀ nz (h1.trans (mul_comm _ _))
      exact this.symm
    obtain ⟨a₁, a₂, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) a
    rw [map_div₀, map_div₀]
    exact congrArg₂ _ (key a₁) (key a₂)

end GlobalTheory.CompanionTheory.Ar.Flat
