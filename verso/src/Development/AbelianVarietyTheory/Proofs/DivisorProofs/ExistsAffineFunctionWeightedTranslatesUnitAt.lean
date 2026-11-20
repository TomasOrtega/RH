import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharIndepAt

variable {X : Scheme.{0}} [IsIntegral X] {x : X}

def liftStalk (σ : X.functionField →+* X.functionField) (h : ∀ f, RegAt x f → RegAt x (σ f)) :
    X.presheaf.stalk x →+* X.presheaf.stalk x where
  toFun s := (h _ ⟨s, rfl⟩).choose
  map_one' := IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by
    rw [(h _ ⟨_, rfl⟩).choose_spec, map_one, map_one])
  map_mul' s t := IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by
    rw [(h _ ⟨_, rfl⟩).choose_spec, map_mul, map_mul, map_mul, (h _ ⟨s, rfl⟩).choose_spec,
      (h _ ⟨t, rfl⟩).choose_spec])
  map_zero' := IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by
    rw [(h _ ⟨_, rfl⟩).choose_spec, map_zero, map_zero])
  map_add' s t := IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by
    rw [(h _ ⟨_, rfl⟩).choose_spec, map_add, map_add, map_add, (h _ ⟨s, rfl⟩).choose_spec,
      (h _ ⟨t, rfl⟩).choose_spec])

/- English proof (translation)
The claim follows from `(h _ ⟨s, rfl⟩).choose_spec`.
-/
theorem algebraMap_liftStalk (σ : X.functionField →+* X.functionField) (h : ∀ f, RegAt x f → RegAt x (σ f))
    (s : X.presheaf.stalk x) :
    algebraMap _ X.functionField (liftStalk σ h s) = σ (algebraMap _ X.functionField s) :=
  (h _ ⟨s, rfl⟩).choose_spec

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `e f ⟨s, rfl⟩`. Use `⟨liftStalk σ h s - s, ?_, by rw [map_sub, algebraMap_liftStalk]⟩` and prove the remaining obligations. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]`. Conclude with `RingHom.congr_fun e s`.

Introduce `H`. Use extensionality with `s`. Take `⟨m, hm, e⟩` from `H _ ⟨s, rfl⟩`. Establish `: m = liftStalk σ h s - s` using `IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by`. Rewrite using `[e, map_sub, algebraMap_liftStalk])`.

Substitute `this` using the available equality. Rewrite `hm` using `[← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]`. Conclude with `hm`.
-/
theorem residue_liftStalk_eq_iff (σ : X.functionField →+* X.functionField) (h : ∀ f, RegAt x f → RegAt x (σ f)) :
    (IsLocalRing.residue (X.presheaf.stalk x)).comp (liftStalk σ h) = IsLocalRing.residue (X.presheaf.stalk x) ↔
      ∀ f, RegAt x f → ZeroAt x (σ f - f) := by
  constructor
  · rintro e f ⟨s, rfl⟩
    refine ⟨liftStalk σ h s - s, ?_, by rw [map_sub, algebraMap_liftStalk]⟩
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact RingHom.congr_fun e s
  · intro H
    ext s
    obtain ⟨m, hm, e⟩ := H _ ⟨s, rfl⟩
    have : m = liftStalk σ h s - s := IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by
      rw [e, map_sub, algebraMap_liftStalk])
    subst this
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at hm
    exact hm

end GlobalTheory.CharIndepAt

open GlobalTheory.CharIndepAt in

/- English proof (translation)
Introduce `X _ U hU x hx ι _ σ u h1 h2 h3 h4 h5 h6`. Set `R` to `X.presheaf.stalk x`. Set `res` to `IsLocalRing.residue R`. Set `g : Γ(X, U) →+* R` to `(X.presheaf.germ U x hx).hom`. Set `ψ : ι → (R →+* IsLocalRing.ResidueField R)` to `fun i => res.comp (liftStalk (σ i) (h1 i))`.

Set `χ : ι → (Γ(X, U) →* IsLocalRing.ResidueField R)` to `fun i => ((ψ i).comp g : Γ(X, U) →+* _)`. Set `χ₀ : Γ(X, U) →* IsLocalRing.ResidueField R` to `(res.comp g : Γ(X, U) →+* _)`. Use `letI : Algebra Γ(X, U) R := X.presheaf.algebra_section_stalk ⟨x, hx⟩`. Establish `hl : IsLocalization.AtPrime R (hU.primeIdealOf ⟨x, hx⟩).asIdeal` using `hU.isLocalization_stalk ⟨x, hx⟩`. Establish `hext : ∀ i, χ i = χ₀ → ψ i = res`.

Introduce `i e`. Use `IsLocalization.ringHom_ext (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl ?_` and prove the remaining obligations. Use extensionality with `a`. Conclude with `DFunLike.congr_fun e a`. Use `choose t ht using h3`.

Establish `hone : ∀ j, χ j = χ₀ → res (t j) = 1`. Introduce `j e`. Take `⟨m, hm, em⟩` from `h4 j ((residue_liftStalk_eq_iff (σ j) (h1 j)).1 (hext j e))`. Establish `: m = t j - 1` using `IsFractionRing.injective R X.functionField (by rw [em, map_sub, map_one, ht])`. Substitute `this` using the available equality.

Rewrite `hm` using `[← IsLocalRing.residue_eq_zero_iff, map_sub, map_one, sub_eq_zero]`. Conclude with `hm`. Take `⟨i₀, hi₀⟩` from `h6`. Establish `h0 : χ i₀ = χ₀`. Use `(residue_liftStalk_eq_iff (σ i₀) (h1 i₀)).2 hi₀` as an intermediate fact.

Use extensionality with `a`. Conclude with `RingHom.congr_fun this (g a)`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `hsum : ∀ a : Γ(X, U), ∑ i, res (t i) * χ i a = 0`.

Introduce `a`. Assume the negation of the conclusion as `hz`. Use `hne a ⟨∑ i, liftStalk (σ i) (h1 i) (g a) * t i, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, map_sum]`. Introduce `h`.

Apply `hz` to reduce the goal to its premises. Rewrite using `[← h]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, mul_comm]`. Both sides reduce to the same expression.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, algebraMap_liftStalk, ht]`. Use `congr 2`. Conclude with `algebraMap_germ hx a`.

Establish `hli` using `linearIndependent_monoidHom Γ(X, U) (IsLocalRing.ResidueField R)`. Rewrite `hli` using `[linearIndependent_iff']`. Set `c : (Γ(X, U) →* IsLocalRing.ResidueField R) → IsLocalRing.ResidueField R` to `fun φ => ∑ i ∈ Finset.univ.filter (fun i => χ i = φ), res (t i)`. Establish `hcomb : ∑ φ ∈ Finset.univ.image χ, c φ • (φ : Γ(X, U) → IsLocalRing.ResidueField R) = 0`. Use extensionality with `a`.

Rewrite using `[Finset.sum_apply]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]`. Rewrite using `[← hsum a, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image χ) (g := χ) (fun i _ => Finset.mem_image_of_mem χ (Finset.mem_univ i))]`. Use `Finset.sum_congr rfl fun φ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[(Finset.mem_filter.1 hi).2]`. Establish `hc` using `hli _ c hcomb χ₀ (by rw [← h0]; exact Finset.mem_image_of_mem χ (Finset.mem_univ i₀))`. Establish `hc' : c χ₀ = ((Finset.univ.filter fun i => χ i = χ₀).card : IsLocalRing.ResidueField R)`. Express the relevant statement in the definitionally equal form `∑ i ∈ Finset.univ.filter (fun i => χ i = χ₀), res (t i) = _`.

Rewrite using `[Finset.sum_congr rfl fun i hi => hone i (Finset.mem_filter.1 hi).2, Finset.sum_const, nsmul_one]`. Establish `hn : (Finset.univ.filter fun i => χ i = χ₀).card ≠ 0` using `(Finset.card_pos.2 ⟨i₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩⟩).ne'`. Take `⟨s, hs, es⟩` from `h5 _ hn`. Establish `: s = ((Finset.univ.filter fun i => χ i = χ₀).card : R)` using `IsFractionRing.injective R X.functionField (by rw [es, map_natCast])`. Substitute `this` using the available equality.

Use `(IsLocalRing.residue_ne_zero_iff_isUnit _).2 hs` as an intermediate fact. Rewrite `this` using `[map_natCast, ← hc']`. Conclude with `this hc`.
-/
theorem GlobalTheory.CharIndepAt.main : ∀ (X : Scheme.{0}) [IsIntegral X] (U : X.Opens), IsAffineOpen U → ∀ (x : X) (hx : x ∈ U)
    (ι : Type) [Fintype ι] (σ : ι → X.functionField →+* X.functionField) (u : ι → X.functionField),
    (∀ i f, RegAt x f → RegAt x (σ i f)) → (∀ i f, ZeroAt x f → ZeroAt x (σ i f)) →
    (∀ i, RegAt x (u i)) →
    (∀ i, (∀ f, RegAt x f → ZeroAt x (σ i f - f)) → ZeroAt x (u i - 1)) →
    (∀ n : ℕ, n ≠ 0 → UnitAt x (n : X.functionField)) →
    (∃ i, ∀ f, RegAt x f → ZeroAt x (σ i f - f)) →
    ∃ a : Γ(X, U), UnitAt x (∑ i, σ i (fnOf U (gen_mem hx) a) * u i) := by

  intro X _ U hU x hx ι _ σ u h1 h2 h3 h4 h5 h6
  classical
  let R := X.presheaf.stalk x
  let res := IsLocalRing.residue R
  let g : Γ(X, U) →+* R := (X.presheaf.germ U x hx).hom
  let ψ : ι → (R →+* IsLocalRing.ResidueField R) := fun i => res.comp (liftStalk (σ i) (h1 i))
  let χ : ι → (Γ(X, U) →* IsLocalRing.ResidueField R) := fun i => ((ψ i).comp g : Γ(X, U) →+* _)
  let χ₀ : Γ(X, U) →* IsLocalRing.ResidueField R := (res.comp g : Γ(X, U) →+* _)
  letI : Algebra Γ(X, U) R := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have hl : IsLocalization.AtPrime R (hU.primeIdealOf ⟨x, hx⟩).asIdeal := hU.isLocalization_stalk ⟨x, hx⟩
  have hext : ∀ i, χ i = χ₀ → ψ i = res := by
    intro i e
    refine IsLocalization.ringHom_ext (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl ?_
    ext a
    exact DFunLike.congr_fun e a
  choose t ht using h3
  have hone : ∀ j, χ j = χ₀ → res (t j) = 1 := by
    intro j e
    obtain ⟨m, hm, em⟩ := h4 j ((residue_liftStalk_eq_iff (σ j) (h1 j)).1 (hext j e))
    have : m = t j - 1 := IsFractionRing.injective R X.functionField (by rw [em, map_sub, map_one, ht])
    subst this
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_one, sub_eq_zero] at hm
    exact hm
  obtain ⟨i₀, hi₀⟩ := h6
  have h0 : χ i₀ = χ₀ := by
    have := (residue_liftStalk_eq_iff (σ i₀) (h1 i₀)).2 hi₀
    ext a
    exact RingHom.congr_fun this (g a)
  by_contra hne
  push_neg at hne
  have hsum : ∀ a : Γ(X, U), ∑ i, res (t i) * χ i a = 0 := by
    intro a
    by_contra hz
    refine hne a ⟨∑ i, liftStalk (σ i) (h1 i) (g a) * t i, ?_, ?_⟩
    · rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sum]
      intro h
      apply hz
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, mul_comm]
      rfl
    · rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, algebraMap_liftStalk, ht]
      congr 2
      exact algebraMap_germ hx a
  have hli := linearIndependent_monoidHom Γ(X, U) (IsLocalRing.ResidueField R)
  rw [linearIndependent_iff'] at hli
  let c : (Γ(X, U) →* IsLocalRing.ResidueField R) → IsLocalRing.ResidueField R :=
    fun φ => ∑ i ∈ Finset.univ.filter (fun i => χ i = φ), res (t i)
  have hcomb : ∑ φ ∈ Finset.univ.image χ, c φ • (φ : Γ(X, U) → IsLocalRing.ResidueField R) = 0 := by
    ext a
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← hsum a, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image χ) (g := χ)
      (fun i _ => Finset.mem_image_of_mem χ (Finset.mem_univ i))]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]
  have hc := hli _ c hcomb χ₀ (by rw [← h0]; exact Finset.mem_image_of_mem χ (Finset.mem_univ i₀))
  have hc' : c χ₀ = ((Finset.univ.filter fun i => χ i = χ₀).card : IsLocalRing.ResidueField R) := by
    change ∑ i ∈ Finset.univ.filter (fun i => χ i = χ₀), res (t i) = _
    rw [Finset.sum_congr rfl fun i hi => hone i (Finset.mem_filter.1 hi).2, Finset.sum_const, nsmul_one]
  have hn : (Finset.univ.filter fun i => χ i = χ₀).card ≠ 0 :=
    (Finset.card_pos.2 ⟨i₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩⟩).ne'
  obtain ⟨s, hs, es⟩ := h5 _ hn
  have : s = ((Finset.univ.filter fun i => χ i = χ₀).card : R) :=
    IsFractionRing.injective R X.functionField (by rw [es, map_natCast])
  subst this
  have := (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hs
  rw [map_natCast, ← hc'] at this
  exact this hc
