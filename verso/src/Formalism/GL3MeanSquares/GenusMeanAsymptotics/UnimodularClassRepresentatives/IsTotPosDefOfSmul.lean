import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.DiscrIdealSmulLeIff
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocFSpanConsBasis
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SigmaCount

open NumberField Module Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.PinD

section One

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

omit [NumberField K] [NumberField F] in
/- English proof (translation)
The claim follows from `(hF _).2 ⟨c, rfl⟩`.
-/
theorem star_cK (hF : IsFixF K F) (c : F) : star (algebraMap F K c) = algebraMap F K c :=
  (hF _).2 ⟨c, rfl⟩

omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [NumberField K] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem smul_form_apply (c : K) (h : V →ₗ⋆[K] V →ₗ[K] K) (x y : V) : (c • h) x y = c * h x y := by
  rfl

omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [NumberField K]
  [NumberField F] in
/- English proof (translation)
Use `⟨fun x y => ?_⟩` and prove the remaining obligations. Establish `hxy` using `hs.eq x y`. Rewrite `hxy` using `[smul_form_apply, smul_form_apply, map_mul]`. Establish `hst : (starRingEnd K) (algebraMap F K c) = algebraMap F K c` using `star_cK hF c`. Rewrite `hxy` using `[hst]`.

Conclude with `mul_left_cancel₀ hc hxy`.
-/
theorem isSymm_of_smul (hF : IsFixF K F) {c : F} (hc : algebraMap F K c ≠ 0)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : (algebraMap F K c • h).IsSymm) : h.IsSymm := by
  refine ⟨fun x y => ?_⟩
  have hxy := hs.eq x y
  rw [smul_form_apply, smul_form_apply, map_mul] at hxy
  have hst : (starRingEnd K) (algebraMap F K c) = algebraMap F K c := star_cK hF c
  rw [hst] at hxy
  exact mul_left_cancel₀ hc hxy

omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [NumberField F] in
/- English proof (translation)
Establish `hx0 : x₀ ≠ 0`. Introduce and unpack `rfl`. Simplify using `at h1`. Introduce `x hx φ`. Establish `hreal : ∀ a : K, star a = a → (φ a).im = 0`.

Introduce `a ha`. Use `hK.2.1 φ a` as an intermediate fact. Rewrite `this` using `[ha]`. Conclude with `Complex.conj_eq_iff_im.1 this.symm`. Establish `hc0` using `hd x₀ hx0 φ`.

Rewrite `hc0` using `[smul_form_apply, h1, mul_one]`. Establish `hcx` using `hd x hx φ`. Rewrite `hcx` using `[smul_form_apply, map_mul]`. Establish `hcr : (φ (algebraMap F K c)).im = 0` using `hreal _ (star_cK hF c)`. Rewrite `hcx` using `[Complex.mul_re, hcr, zero_mul, sub_zero]`.

Conclude with `pos_of_mul_pos_right hcx hc0.le`.
-/
theorem isTotPosDef_of_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {c : F}
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef (algebraMap F K c • h)) {x₀ : V}
    (h1 : h x₀ x₀ = 1) : IsTotPosDef h := by
  have hx0 : x₀ ≠ 0 := by
    rintro rfl
    simp at h1
  intro x hx φ
  have hreal : ∀ a : K, star a = a → (φ a).im = 0 := by
    intro a ha
    have := hK.2.1 φ a
    rw [ha] at this
    exact Complex.conj_eq_iff_im.1 this.symm
  have hc0 := hd x₀ hx0 φ
  rw [smul_form_apply, h1, mul_one] at hc0
  have hcx := hd x hx φ
  rw [smul_form_apply, map_mul] at hcx
  have hcr : (φ (algebraMap F K c)).im = 0 := hreal _ (star_cK hF c)
  rw [Complex.mul_re, hcr, zero_mul, sub_zero] at hcx
  exact pos_of_mul_pos_right hcx hc0.le

/- English proof (translation)
Conclude with `firstFamilyOperatorEnd.alphaL_eq hK hF hs hd hL hLi h𝔭 (by omega)`.
-/
theorem alphaL_eq_of_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : 2 * vd h L 𝔭 + 2 ≤ k) :
    alphaL h L 𝔭 = (akCount h L 𝔭 k : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * finrank K V ^ 2) := by
  exact firstFamilyOperatorEnd.alphaL_eq hK hF hs hd hL hLi h𝔭 (by omega)

/- English proof (translation)
Establish `hN : (Ideal.absNorm 𝔭 : ℝ) ≠ 0`. Rewrite using `[Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)`. Establish `key : ∀ k, 2 * vd h L 𝔭 + 1 + vF 𝔭 c ≤ k → (akCount (algebraMap F K (c : F) • h) L 𝔭 k : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * finrank K V ^ 2) = (Ideal.absNorm 𝔭 : ℝ) ^ (vF 𝔭 c * finrank K V ^ 2) * alphaL h L 𝔭`. Introduce `k hk`.

Take `⟨m, rfl⟩ : ∃ m, k = m + vF 𝔭 c` from `⟨k - vF 𝔭 c, by omega⟩`. Rewrite using `[PinA.akCount_smul hK hF hs hd hL hLi h𝔭 hc (k := m + vF 𝔭 c) (by omega), Nat.add_sub_cancel, firstFamilyOperatorEnd.alphaL_eq hK hF hs hd hL hLi h𝔭 (k := m) (by omega)]`. Use `push_cast`. Rewrite using `[show (m + vF 𝔭 c) * finrank K V ^ 2 = m * finrank K V ^ 2 + vF 𝔭 c * finrank K V ^ 2 by ring, show 2 * vF 𝔭 c * finrank K V ^ 2 = vF 𝔭 c * finrank K V ^ 2 + vF 𝔭 c * finrank K V ^ 2 by ring, pow_add, pow_add]`. Apply the tactic sequence `field_simp <;> ring`.

Conclude with `(tendsto_const_nhds.congr' (Filter.eventually_atTop.2 ⟨_, fun k hk => (key k hk).symm⟩)).limUnder_eq`.
-/
theorem alphaL_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) (hs' : (algebraMap F K (c : F) • h).IsSymm)
    (hd' : IsTotPosDef (algebraMap F K (c : F) • h)) :
    alphaL (algebraMap F K (c : F) • h) L 𝔭 =
      (Ideal.absNorm 𝔭 : ℝ) ^ (vF 𝔭 c * finrank K V ^ 2) * alphaL h L 𝔭 := by
  have hN : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
  have key : ∀ k, 2 * vd h L 𝔭 + 1 + vF 𝔭 c ≤ k →
      (akCount (algebraMap F K (c : F) • h) L 𝔭 k : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * finrank K V ^ 2) =
        (Ideal.absNorm 𝔭 : ℝ) ^ (vF 𝔭 c * finrank K V ^ 2) * alphaL h L 𝔭 := by
    intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + vF 𝔭 c := ⟨k - vF 𝔭 c, by omega⟩
    rw [PinA.akCount_smul hK hF hs hd hL hLi h𝔭 hc (k := m + vF 𝔭 c) (by omega), Nat.add_sub_cancel,
      firstFamilyOperatorEnd.alphaL_eq hK hF hs hd hL hLi h𝔭 (k := m) (by omega)]
    push_cast
    rw [show (m + vF 𝔭 c) * finrank K V ^ 2 = m * finrank K V ^ 2 + vF 𝔭 c * finrank K V ^ 2 by ring,
      show 2 * vF 𝔭 c * finrank K V ^ 2 = vF 𝔭 c * finrank K V ^ 2 + vF 𝔭 c * finrank K V ^ 2 by ring,
      pow_add, pow_add]
    field_simp <;> ring
  exact (tendsto_const_nhds.congr'
    (Filter.eventually_atTop.2 ⟨_, fun k hk => (key k hk).symm⟩)).limUnder_eq

/- English proof (translation)
Establish `hN : (Ideal.absNorm 𝔭 : ℝ) ≠ 0`. Rewrite using `[Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)`. Establish `key : ∀ k, 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2 + vF 𝔭 c ≤ k → (nkCount (algebraMap F K (c : F) • h) L 𝔭 k (c * n) : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) = (Ideal.absNorm 𝔭 : ℝ) ^ vF 𝔭 c * alphaN h L 𝔭 n`. Introduce `k hk`.

Take `⟨m, rfl⟩ : ∃ m, k = m + vF 𝔭 c` from `⟨k - vF 𝔭 c, by omega⟩`. Rewrite using `[PinA.nkCount_smul hK hF hs hd hL hLi h𝔭 hc n (k := m + vF 𝔭 c) (by omega), Nat.add_sub_cancel, alphaN_eq_of_le hK hF hs hd hL hLi h𝔭 hn (k := m) (by omega)]`. Use `push_cast`. Establish `h2 : 2 * vF 𝔭 c * finrank K V = vF 𝔭 c * (2 * finrank K V - 1) + vF 𝔭 c`. Establish `h3 : 2 * finrank K V = (2 * finrank K V - 1) + 1` using `by omega`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h2, show (m + vF 𝔭 c) * (2 * finrank K V - 1) = m * (2 * finrank K V - 1) + vF 𝔭 c * (2 * finrank K V - 1) by ring, pow_add, pow_add]`. Apply the tactic sequence `field_simp <;> ring`. Conclude with `(tendsto_const_nhds.congr' (Filter.eventually_atTop.2 ⟨_, fun k hk => (key k hk).symm⟩)).limUnder_eq`.
-/
theorem alphaN_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) (hs' : (algebraMap F K (c : F) • h).IsSymm)
    (hd' : IsTotPosDef (algebraMap F K (c : F) • h)) (hm : 1 ≤ finrank K V) {n : 𝓞 F} (hn : n ≠ 0) :
    alphaN (algebraMap F K (c : F) • h) L 𝔭 (c * n) =
      (Ideal.absNorm 𝔭 : ℝ) ^ vF 𝔭 c * alphaN h L 𝔭 n := by
  have hN : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
  have key : ∀ k, 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2 + vF 𝔭 c ≤ k →
      (nkCount (algebraMap F K (c : F) • h) L 𝔭 k (c * n) : ℝ) /
          (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) =
        (Ideal.absNorm 𝔭 : ℝ) ^ vF 𝔭 c * alphaN h L 𝔭 n := by
    intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + vF 𝔭 c := ⟨k - vF 𝔭 c, by omega⟩
    rw [PinA.nkCount_smul hK hF hs hd hL hLi h𝔭 hc n (k := m + vF 𝔭 c) (by omega), Nat.add_sub_cancel,
      alphaN_eq_of_le hK hF hs hd hL hLi h𝔭 hn (k := m) (by omega)]
    push_cast
    have h2 : 2 * vF 𝔭 c * finrank K V = vF 𝔭 c * (2 * finrank K V - 1) + vF 𝔭 c := by
      have h3 : 2 * finrank K V = (2 * finrank K V - 1) + 1 := by omega
      calc 2 * vF 𝔭 c * finrank K V = vF 𝔭 c * (2 * finrank K V) := by ring
        _ = vF 𝔭 c * ((2 * finrank K V - 1) + 1) := by rw [← h3]
        _ = _ := by ring
    rw [h2, show (m + vF 𝔭 c) * (2 * finrank K V - 1) =
        m * (2 * finrank K V - 1) + vF 𝔭 c * (2 * finrank K V - 1) by ring, pow_add, pow_add]
    field_simp <;> ring
  exact (tendsto_const_nhds.congr'
    (Filter.eventually_atTop.2 ⟨_, fun k hk => (key k hk).symm⟩)).limUnder_eq

end One

section Two

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

omit [NumberField K] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
Use extensionality with `g`. Use `show (∀ x y, (c • h) (g x) (g y) = (c • h) x y) ↔ ∀ x y, h (g x) (g y) = h x y`. Simplify using `only [smul_form_apply, mul_right_inj' hc]`.
-/
theorem isom_smul {c : K} (hc : c ≠ 0) (h : V →ₗ⋆[K] V →ₗ[K] K) :
    Formalism.HermitianLatticesTheory.isom (c • h) = Formalism.HermitianLatticesTheory.isom h := by
  ext g
  show (∀ x y, (c • h) (g x) (g y) = (c • h) x y) ↔ ∀ x y, h (g x) (g y) = h x y
  simp only [smul_form_apply, mul_right_inj' hc]

def unscale {c : K} (hc : c ≠ 0) (S : VecSplit (c • h) (c • h')) : VecSplit h h' where
  x₀ := S.x₀
  ι := S.ι
  inj := S.inj
  hx₀ := fun e => S.hx₀ (by rw [smul_form_apply, e, mul_zero])
  isom := fun a b => by
    have := S.isom a b
    rw [smul_form_apply, smul_form_apply] at this
    exact mul_left_cancel₀ hc this
  orth := fun a => by
    have := S.orth a
    rw [smul_form_apply] at this
    exact (mul_eq_zero.1 this).resolve_left hc
  cover := S.cover

omit [FiniteDimensional K V] [FiniteDimensional K V'] in
/- English proof (translation)
Simplify using `only [fibLoc, isom_smul hc]`. Both sides reduce to the same expression.
-/
theorem fibLoc_unscale {c : K} (hc : c ≠ 0) (S : VecSplit (c • h) (c • h')) (L : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) (T : Submodule (𝓞 K) V') :
    fibLoc S L 𝔭 T = fibLoc (unscale hc S) L 𝔭 T := by
  simp only [fibLoc, isom_smul hc]
  rfl

/- English proof (translation)
Establish `hLi'` using `PinA.isIntegralLat_smul hLi c`. Establish `hiso : Formalism.HermitianLatticesTheory.isom (algebraMap F K (c : F) • h') = Formalism.HermitianLatticesTheory.isom h'` using `isom_smul hc h'`. Use `⟨fun T hT => ?_, fun T hTl hTi hTf => ?_⟩` and prove the remaining obligations. Take `⟨h1, -, h3⟩` from `hr.1 T hT`. Rewrite `h3` using `[← fibLoc_unscale]`.

Take `⟨C, -, hCi, hC⟩` from `UnimodularLocalization.exists_lattice_of_fibLoc_ne_zero S hL hLi' h3`. Use `⟨h1, ?_, h3⟩` and prove the remaining obligations. Use `GoodPrimeTerms.isIntegralAt_locF h𝔭.isPrime hF hCi` as an intermediate fact. Rewrite `this` using `[hC, h1]`. Then use the resulting hypothesis. Rewrite `hTf` using `[fibLoc_unscale hc]`.

Take `⟨C, -, hCi, hC⟩` from `UnimodularLocalization.exists_lattice_of_fibLoc_ne_zero (unscale hc S) hL hLi hTf`. Establish `hTi' : IsIntegralAt 𝔭 h' T`. Use `GoodPrimeTerms.isIntegralAt_locF h𝔭.isPrime hF hCi` as an intermediate fact. Rewrite `this` using `[hC, hTl]`. Then use the resulting hypothesis. Rewrite using `[hiso]`.

Conclude with `hr.2 T hTl hTi' hTf`.
-/
theorem isLocReps_scale (hF : IsFixF K F) {c : 𝓞 F} (hc : algebraMap F K (c : F) ≠ 0)
    (S : VecSplit (algebraMap F K (c : F) • h) (algebraMap F K (c : F) • h'))
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {s : Finset (Submodule (𝓞 K) V')}
    (hr : IsLocReps (unscale hc S) L 𝔭 s) : IsLocReps S L 𝔭 s := by
  have hLi' := PinA.isIntegralLat_smul hLi c
  have hiso : Formalism.HermitianLatticesTheory.isom (algebraMap F K (c : F) • h') = Formalism.HermitianLatticesTheory.isom h' := isom_smul hc h'
  refine ⟨fun T hT => ?_, fun T hTl hTi hTf => ?_⟩
  · obtain ⟨h1, -, h3⟩ := hr.1 T hT
    rw [← fibLoc_unscale] at h3
    obtain ⟨C, -, hCi, hC⟩ := UnimodularLocalization.exists_lattice_of_fibLoc_ne_zero S hL hLi' h3
    refine ⟨h1, ?_, h3⟩
    have := GoodPrimeTerms.isIntegralAt_locF h𝔭.isPrime hF hCi
    rwa [hC, h1] at this
  · rw [fibLoc_unscale hc] at hTf
    obtain ⟨C, -, hCi, hC⟩ := UnimodularLocalization.exists_lattice_of_fibLoc_ne_zero (unscale hc S) hL hLi hTf
    have hTi' : IsIntegralAt 𝔭 h' T := by
      have := GoodPrimeTerms.isIntegralAt_locF h𝔭.isPrime hF hCi
      rwa [hC, hTl] at this
    rw [hiso]
    exact hr.2 T hTl hTi' hTf

/- English proof (translation)
Establish `hN : (Ideal.absNorm 𝔭 : ℝ) ≠ 0`. Rewrite using `[Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)`. Establish `hdim` using `S.finrank_add_one`. Establish `hA` using `alphaL_pos hK hF hs hd hL hLi h𝔭`.

Establish `h1𝔭 : (1 : 𝓞 F) ∉ 𝔭 ^ (0 + 1)`. Rewrite using `[zero_add, pow_one]`. Conclude with `(Ideal.ne_top_iff_one 𝔭).1 h𝔭.ne_top`. Establish `key : ∀ k, 2 * vd h L 𝔭 + 2 ≤ k → alphaN h L 𝔭 1 ≠ 0 ∧ (akCount h' (S.cut L) 𝔭 k : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * finrank K V' ^ 2) = alphaL h L 𝔭 / alphaN h L 𝔭 1`. Introduce `k hk`.

Establish `eA` using `firstFamilyOperatorEnd.alphaL_eq hK hF hs hd hL hLi h𝔭 (k := k) (by omega)`. Establish `eB` using `firstFamilyOperatorEnd.alphaN_eq hK hF hs hd hL hLi h𝔭 h1𝔭 (k := k) (by omega)`. Establish `eS` using `PinB.akCount_split hK hF hs hd S h1 hL hLi hx h𝔭 hv (k := k) (by omega)`. Rewrite `eA` using `[eS, Nat.cast_mul]`. Establish `hnk : (nkCount h L 𝔭 k 1 : ℝ) ≠ 0`.

Introduce `h0`. Rewrite `eA` using `[h0, zero_mul, zero_div]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hB : alphaN h L 𝔭 1 ≠ 0`. Rewrite using `[eB]`.

Conclude with `div_ne_zero hnk (pow_ne_zero _ hN)`. Use `⟨hB, ?_⟩` and prove the remaining obligations. Rewrite using `[eA, eB, ← hdim]`. Establish `e1 : k * (finrank K V' + 1) ^ 2 = k * (2 * (finrank K V' + 1) - 1) + k * finrank K V' ^ 2`. Establish `: 2 * (finrank K V' + 1) - 1 = 2 * finrank K V' + 1` using `by omega`.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, pow_add]`. Apply the tactic sequence `field_simp <;> ring`. Take `⟨hB, -⟩` from `key _ le_rfl`.

Establish `hl : alphaL h' (S.cut L) 𝔭 = alphaL h L 𝔭 / alphaN h L 𝔭 1` using `(tendsto_const_nhds.congr' (Filter.eventually_atTop.2 ⟨_, fun k hk => ((key k hk).2).symm⟩)).limUnder_eq`. Rewrite using `[hl]`. Clear the denominators using the available nonvanishing facts.
-/
theorem alphaL_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 ≤ 1) :
    alphaL h L 𝔭 = alphaN h L 𝔭 1 * alphaL h' (S.cut L) 𝔭 := by
  have hN : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
  have hdim := S.finrank_add_one
  have hA := alphaL_pos hK hF hs hd hL hLi h𝔭
  have h1𝔭 : (1 : 𝓞 F) ∉ 𝔭 ^ (0 + 1) := by
    rw [zero_add, pow_one]; exact (Ideal.ne_top_iff_one 𝔭).1 h𝔭.ne_top
  have key : ∀ k, 2 * vd h L 𝔭 + 2 ≤ k → alphaN h L 𝔭 1 ≠ 0 ∧
      (akCount h' (S.cut L) 𝔭 k : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * finrank K V' ^ 2) =
        alphaL h L 𝔭 / alphaN h L 𝔭 1 := by
    intro k hk
    have eA := firstFamilyOperatorEnd.alphaL_eq hK hF hs hd hL hLi h𝔭 (k := k) (by omega)
    have eB := firstFamilyOperatorEnd.alphaN_eq hK hF hs hd hL hLi h𝔭 h1𝔭 (k := k) (by omega)
    have eS := PinB.akCount_split hK hF hs hd S h1 hL hLi hx h𝔭 hv (k := k) (by omega)
    rw [eS, Nat.cast_mul] at eA
    have hnk : (nkCount h L 𝔭 k 1 : ℝ) ≠ 0 := by
      intro h0
      rw [h0, zero_mul, zero_div] at eA
      linarith
    have hB : alphaN h L 𝔭 1 ≠ 0 := by
      rw [eB]; exact div_ne_zero hnk (pow_ne_zero _ hN)
    refine ⟨hB, ?_⟩
    rw [eA, eB, ← hdim]
    have e1 : k * (finrank K V' + 1) ^ 2 =
        k * (2 * (finrank K V' + 1) - 1) + k * finrank K V' ^ 2 := by
      have : 2 * (finrank K V' + 1) - 1 = 2 * finrank K V' + 1 := by omega
      rw [this]; ring
    rw [e1, pow_add]
    field_simp <;> ring
  obtain ⟨hB, -⟩ := key _ le_rfl
  have hl : alphaL h' (S.cut L) 𝔭 = alphaL h L 𝔭 / alphaN h L 𝔭 1 :=
    (tendsto_const_nhds.congr'
      (Filter.eventually_atTop.2 ⟨_, fun k hk => ((key k hk).2).symm⟩)).limUnder_eq
  rw [hl]
  field_simp

end Two

end Formalism.HermitianLattices.Ext.L3.PinD
