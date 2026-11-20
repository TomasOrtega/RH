import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.TateTwists.EtaleTwistedCupAssocOfTwistedPairingExistsAssoc
import Development.EtaleCohomology.TateTwists.EtaleTensorPairTwistResolutionMul
import Development.EtaleCohomology.TateTwists.EtaleTensorPairProductAssociative
import Development.EtaleCohomology.TateTwists.EtaleTwistResolutionUniversalExtension
import Development.EtaleCohomology.TateTwists.EtaleCupProductNaturalInCoefficients
import Development.EtaleCohomology.TateTwists.EtaleCochainCupAssociativeOfPairing

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def t_pa_tens_ex : Prop :=
  ∀ (R : Type) [CommRing R] (I J : Cx R), ∃ (T : Cx R) (τ : Pair I J T), τ.IsTensor

def t_pa_tens_univ : Prop :=
  ∀ (R : Type) [CommRing R] {I J T K : Cx R} (τ : Pair I J T), τ.IsTensor →
    ∀ μ : Pair I J K, ∃ u : T ⟶ K, τ.Compat μ (𝟙 I) (𝟙 J) u

def t_pa_precomp : Prop :=
  ∀ (R : Type) [CommRing R] {I I' J K : Cx R} (u : I ⟶ I') (μ : Pair I' J K),
    ∃ ρ : Pair I J K, ρ.Compat μ u (𝟙 J) (𝟙 K)

def t_pa_cpush_id : Prop :=
  ∀ (R : Type) [CommRing R] (E : Spc) (I : Cx R) (n : ℤ) (x : CohomologyClass ((chains R).obj E) I n),
    cpush _ (𝟙 I) n x = x

def t_pa_cpush_htpy : Prop :=
  ∀ (R : Type) [CommRing R] (E : Spc) {I J : Cx R} (u u' : I ⟶ J), Homotopy u u' →
    ∀ (n : ℤ) (x : CohomologyClass ((chains R).obj E) I n), cpush _ u n x = cpush _ u' n x

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pa_sec_map_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (𝟙 F) x = x := rfl

/- English proof (translation)
Introduce `q _ E i j l k₁ k₂ k e1 e2 e3 μ₁ μ₂ ν₁ ν₂ p1 p2 p3 p4 n m p s₁ s₂ s h₁ h₂ h₃ h₄ a b c`. Take `⟨T, τ, hτ⟩` from `hex (ZMod q) (res _ (tw q i)) (res _ (tw q j))`. Take `⟨T3, τ', hτ'⟩` from `hex (ZMod q) T (res _ (tw q l))`. Take `⟨u, hu⟩` from `huniv (ZMod q) τ hτ μ₁`. Take `⟨ρ, hρ⟩` from `hpre (ZMod q) u μ₂`.

Take `⟨ν, hν⟩` from `htri (ZMod q) τ τ' hτ hτ' ν₁ ν₂`. Take `⟨w₁, hw₁⟩` from `huniv (ZMod q) τ' hτ' ρ`. Take `⟨w₂, hw₂⟩` from `huniv (ZMod q) τ' hτ' ν`. Take `⟨ri, -, -⟩` from `hext q i`. Take `⟨rj, fj, -⟩` from `hext q j`.

Take `⟨rl, fl, -⟩` from `hext q l`. Establish `hT` using `htw q i j k₁ e1 _ _ ri rj fj τ hτ`. Establish `ek : k₁ + l = k` using `by omega`. Establish `hT3` using `htw q k₁ l k ek _ _ hT rl fl τ' hτ'`. Take `⟨-, -, huniq⟩` from `hext q k`.

Take `⟨H⟩` from `(huniq _ hT3).2 w₁ w₂ (by`. Introduce `U ζ`. Rewrite using `[hw₁, hw₂]`. Simplify using `only [HomologicalComplex.id_f, pa_sec_map_id]`. Rewrite using `[hν U 0 0 0 0 0 0 (add_zero 0) (add_zero 0) (add_zero 0) (add_zero 0)]`.

Establish `r1` using `hρ U 0 0 0 (add_zero 0) (τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)) (resGen l ζ)`. Simplify using `only [HomologicalComplex.id_f, pa_sec_map_id] at r1`. Establish `r2` using `hu U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)`. Simplify using `only [HomologicalComplex.id_f, pa_sec_map_id] at r2`. Use `erw [r1, r2, p1, p2, p3, p4])`.

Establish `L1 : μ₁.cup E h₁ a b = cpush _ u s₁ (τ.cup E h₁ a b)`. Rewrite using `[hcc _ τ μ₁ (𝟙 _) (𝟙 _) u hu E h₁ a b, hid, hid]`. Establish `L2 : ∀ y, μ₂.cup E h₂ (cpush _ u s₁ y) c = ρ.cup E h₂ y c`. Introduce `y`. Use `hcc _ ρ μ₂ u (𝟙 _) (𝟙 _) hρ E h₂ y c` as an intermediate fact.

Rewrite `this` using `[hid, hid]`. Conclude with `this.symm`. Establish `L3 : ∀ y, ρ.cup E h₂ y c = cpush _ w₁ s (τ'.cup E h₂ y c)`. Introduce `y`. Rewrite using `[hcc _ τ' ρ (𝟙 _) (𝟙 _) w₁ hw₁ E h₂ y c, hid, hid]`.

Establish `L4 : ∀ y, ν.cup E h₂ y c = cpush _ w₂ s (τ'.cup E h₂ y c)`. Introduce `y`. Rewrite using `[hcc _ τ' ν (𝟙 _) (𝟙 _) w₂ hw₂ E h₂ y c, hid, hid]`. Rewrite using `[← ha0 _ τ ν ν₁ ν₂ hν E h₁ h₂ h₃ h₄ a b c, L1, L2, L3, L4, hhtpy _ E w₁ w₂ H]`.
-/
theorem t_pair_assoc_of (htw : EtaleTensorPairTwistResolutionMul) (htri : EtaleTensorPairProductAssociative) (hext : EtaleTwistResolutionUniversalExtension)
    (hcc : EtaleCupProductNaturalInCoefficients) (ha0 : EtaleCochainCupAssociativeOfPairing) (hex : t_pa_tens_ex) (huniv : t_pa_tens_univ)
    (hpre : t_pa_precomp) (hid : t_pa_cpush_id) (hhtpy : t_pa_cpush_htpy) : t_pair_assoc := by
  intro q _ E i j l k₁ k₂ k e1 e2 e3 μ₁ μ₂ ν₁ ν₂ p1 p2 p3 p4 n m p s₁ s₂ s h₁ h₂ h₃ h₄ a b c
  obtain ⟨T, τ, hτ⟩ := hex (ZMod q) (res _ (tw q i)) (res _ (tw q j))
  obtain ⟨T3, τ', hτ'⟩ := hex (ZMod q) T (res _ (tw q l))
  obtain ⟨u, hu⟩ := huniv (ZMod q) τ hτ μ₁
  obtain ⟨ρ, hρ⟩ := hpre (ZMod q) u μ₂
  obtain ⟨ν, hν⟩ := htri (ZMod q) τ τ' hτ hτ' ν₁ ν₂
  obtain ⟨w₁, hw₁⟩ := huniv (ZMod q) τ' hτ' ρ
  obtain ⟨w₂, hw₂⟩ := huniv (ZMod q) τ' hτ' ν
  obtain ⟨ri, -, -⟩ := hext q i
  obtain ⟨rj, fj, -⟩ := hext q j
  obtain ⟨rl, fl, -⟩ := hext q l
  have hT := htw q i j k₁ e1 _ _ ri rj fj τ hτ
  have ek : k₁ + l = k := by omega
  have hT3 := htw q k₁ l k ek _ _ hT rl fl τ' hτ'
  obtain ⟨-, -, huniq⟩ := hext q k
  obtain ⟨H⟩ := (huniq _ hT3).2 w₁ w₂ (by
    intro U ζ
    rw [hw₁, hw₂]
    simp only [HomologicalComplex.id_f, pa_sec_map_id]
    rw [hν U 0 0 0 0 0 0 (add_zero 0) (add_zero 0) (add_zero 0) (add_zero 0)]
    have r1 := hρ U 0 0 0 (add_zero 0) (τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)) (resGen l ζ)
    simp only [HomologicalComplex.id_f, pa_sec_map_id] at r1
    have r2 := hu U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)
    simp only [HomologicalComplex.id_f, pa_sec_map_id] at r2
    erw [r1, r2, p1, p2, p3, p4])
  have L1 : μ₁.cup E h₁ a b = cpush _ u s₁ (τ.cup E h₁ a b) := by
    rw [hcc _ τ μ₁ (𝟙 _) (𝟙 _) u hu E h₁ a b, hid, hid]
  have L2 : ∀ y, μ₂.cup E h₂ (cpush _ u s₁ y) c = ρ.cup E h₂ y c := by
    intro y
    have := hcc _ ρ μ₂ u (𝟙 _) (𝟙 _) hρ E h₂ y c
    rw [hid, hid] at this
    exact this.symm
  have L3 : ∀ y, ρ.cup E h₂ y c = cpush _ w₁ s (τ'.cup E h₂ y c) := by
    intro y
    rw [hcc _ τ' ρ (𝟙 _) (𝟙 _) w₁ hw₁ E h₂ y c, hid, hid]
  have L4 : ∀ y, ν.cup E h₂ y c = cpush _ w₂ s (τ'.cup E h₂ y c) := by
    intro y
    rw [hcc _ τ' ν (𝟙 _) (𝟙 _) w₂ hw₂ E h₂ y c, hid, hid]
  rw [← ha0 _ τ ν ν₁ ν₂ hν E h₁ h₂ h₃ h₄ a b c, L1, L2, L3, L4, hhtpy _ E w₁ w₂ H]

end LateralTheory.EtaleFoundations
