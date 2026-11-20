import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.BlockPolyLevelMove
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.BlockProductLattices
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.BetaIsPrincipal
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ZeroNotAdmissibleOfRankPos
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.BaseClassMove

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShortLawsCompare

open NumberField MvPolynomial Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.IndefiniteRowSideFullHecke

section Lattice

variable {E : Type} [Field E] [NumberField E]

variable {n₁ n₂ : ℕ}

set_option autoImplicit false in
open NumberField MvPolynomial in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {E : Type} [Field E] [NumberField E] in
variable {n₁ n₂ : ℕ} in
/- English proof (translation)
Simplify using `only [_root_.GlobalTheory.BetaEx.mem_std]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨fun j => h _, fun j => h _⟩`. Introduce and unpack `⟨h₁, h₂⟩ j`.

Use `Fin.addCases (fun i => ?_) (fun i => ?_) j` and prove the remaining obligations. Conclude with `h₁ i`. Conclude with `h₂ i`.
-/
theorem _root_.GlobalTheory.ShortLawsCompare.mem_std_block (v : Fin (n₁ + n₂) → E) :
    v ∈ _root_.Formalism.L2.Pj.stdLat E (n₁ + n₂) ↔
      (fun j => v (Fin.castAdd n₂ j)) ∈ _root_.Formalism.L2.Pj.stdLat E n₁ ∧
        (fun j => v (Fin.natAdd n₁ j)) ∈ _root_.Formalism.L2.Pj.stdLat E n₂ := by
  simp only [_root_.GlobalTheory.BetaEx.mem_std]
  constructor
  · intro h
    exact ⟨fun j => h _, fun j => h _⟩
  · rintro ⟨h₁, h₂⟩ j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · exact h₁ i
    · exact h₂ i

set_option autoImplicit false in
open NumberField MvPolynomial in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {E : Type} [Field E] [NumberField E] in
variable {n₁ n₂ : ℕ} in
/- English proof (translation)
Rewrite using `[Submodule.smul_le]`. Introduce `r hr v hv`. Rewrite `hv`, the goal using `[Submodule.mem_inf, Submodule.mem_comap, Submodule.mem_comap]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul]`.

Conclude with `h₁ (Submodule.smul_mem_smul hr hv.1)`. Rewrite using `[map_smul]`. Conclude with `h₂ (Submodule.smul_mem_smul hr hv.2)`.
-/
private theorem smul_inf_comap_funLeft_le (I : Ideal (𝓞 E)) (L₁ P₁ : Submodule (𝓞 E) (Fin n₁ → E))
    (L₂ P₂ : Submodule (𝓞 E) (Fin n₂ → E)) (h₁ : I • L₁ ≤ P₁) (h₂ : I • L₂ ≤ P₂) :
    I • (L₁.comap (LinearMap.funLeft (𝓞 E) E (Fin.castAdd n₂)) ⊓
        L₂.comap (LinearMap.funLeft (𝓞 E) E (Fin.natAdd n₁))) ≤
      P₁.comap (LinearMap.funLeft (𝓞 E) E (Fin.castAdd n₂)) ⊓
        P₂.comap (LinearMap.funLeft (𝓞 E) E (Fin.natAdd n₁)) := by
  rw [Submodule.smul_le]
  intro r hr v hv
  rw [Submodule.mem_inf, Submodule.mem_comap, Submodule.mem_comap] at hv ⊢
  refine ⟨?_, ?_⟩
  · rw [map_smul]
    exact h₁ (Submodule.smul_mem_smul hr hv.1)
  · rw [map_smul]
    exact h₂ (Submodule.smul_mem_smul hr hv.2)

set_option autoImplicit false in
open NumberField MvPolynomial in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {E : Type} [Field E] [NumberField E] in
variable {n₁ n₂ : ℕ} in
/- English proof (translation)
Use extensionality with `v`. Conclude with `_root_.GlobalTheory.ShortLawsCompare.mem_std_block v`.
-/
private theorem stdLat_add_eq_inf_comap_funLeft :
    _root_.Formalism.L2.Pj.stdLat E (n₁ + n₂) =
      (_root_.Formalism.L2.Pj.stdLat E n₁).comap (LinearMap.funLeft (𝓞 E) E (Fin.castAdd n₂)) ⊓
        (_root_.Formalism.L2.Pj.stdLat E n₂).comap (LinearMap.funLeft (𝓞 E) E (Fin.natAdd n₁)) := by
  ext v
  exact _root_.GlobalTheory.ShortLawsCompare.mem_std_block v

set_option autoImplicit false in
open NumberField MvPolynomial in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {E : Type} [Field E] [NumberField E] in
variable {n₁ n₂ : ℕ} in
/- English proof (translation)
Unfold `_root_.Formalism.L2.Pj.GenLat.LevOK _root_.Formalism.L2.Pj.GenLat.Ln at *`. Use `⟨h₁.1, h₁.2.1, ?_⟩` and prove the remaining obligations. Establish `key` using `smul_inf_comap_funLeft_le (Ideal.span {((N : ℕ) : 𝓞 E)}) _ _ _ _ h₁.2.2 h₂.2.2`. Rewrite using `[stdLat_add_eq_inf_comap_funLeft]`. Use `key.trans ?_` and prove the remaining obligations.

Introduce `v hv`. Simplify using `only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockProductLattices.blockLat, Submodule.mem_inf, Submodule.mem_comap] at hv ⊢`. The claim follows by propositional logic.
-/
theorem _root_.GlobalTheory.ShortLawsCompare.levOK_block {Λ₁ : _root_.Formalism.L2.Pj.GenLat E n₁} {Λ₂ : _root_.Formalism.L2.Pj.GenLat E n₂} {N M : ℕ}
    (h₁ : Λ₁.LevOK N M) (h₂ : Λ₂.LevOK N M) :
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockProductLattices.blockLat Λ₁ Λ₂).LevOK N M := by
  unfold _root_.Formalism.L2.Pj.GenLat.LevOK _root_.Formalism.L2.Pj.GenLat.Ln at *
  refine ⟨h₁.1, h₁.2.1, ?_⟩
  have key := smul_inf_comap_funLeft_le (Ideal.span {((N : ℕ) : 𝓞 E)}) _ _ _ _ h₁.2.2 h₂.2.2
  rw [stdLat_add_eq_inf_comap_funLeft]
  refine key.trans ?_
  intro v hv
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockProductLattices.blockLat, Submodule.mem_inf, Submodule.mem_comap] at hv ⊢
  tauto

set_option autoImplicit false in
open NumberField MvPolynomial in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {E : Type} [Field E] [NumberField E] in
variable {n₁ n₂ : ℕ} in
/- English proof (translation)
Unfold `_root_.Formalism.L2.Pj.GenLat.TrivAt`. Apply the tactic sequence `refine ⟨1, Nat.coprime_one_left _, ?_, ?_⟩ <;> simp`.
-/
theorem _root_.GlobalTheory.ShortLawsCompare.trivAt_std (n b : ℕ) :
    _root_.Formalism.L2.Pj.GenLat.TrivAt (⟨_root_.Formalism.L2.Pj.stdLat E n⟩ : _root_.Formalism.L2.Pj.GenLat E n) b := by
  unfold _root_.Formalism.L2.Pj.GenLat.TrivAt
  refine ⟨1, Nat.coprime_one_left _, ?_, ?_⟩ <;> simp

set_option autoImplicit false in
open NumberField MvPolynomial in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {E : Type} [Field E] [NumberField E] in
variable {n₁ n₂ : ℕ} in
/- English proof (translation)
Assemble the required witnesses or components as `⟨RingOfIntegers.mapRingHom (IsCMField.complexConj E : E →+* E) a, rfl⟩`.
-/
private theorem complexConj_coe_mem_range_algebraMap [IsCMField E] (a : 𝓞 E) :
    IsCMField.complexConj E (a : E) ∈ (algebraMap (𝓞 E) E).range :=
  ⟨RingOfIntegers.mapRingHom (IsCMField.complexConj E : E →+* E) a, rfl⟩

set_option autoImplicit false in
open NumberField MvPolynomial in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {E : Type} [Field E] [NumberField E] in
variable {n₁ n₂ : ℕ} in
/- English proof (translation)
Unfold `_root_.Formalism.L2.Pj.GenLat.Unimod`. Introduce `v`. Use `show v ∈ _root_.Formalism.L2.Pj.stdLat E n ↔ ∀ w ∈ _root_.Formalism.L2.Pj.stdLat E n, _`. Prove the components needed by the constructor for the conclusion. Introduce `hv w hw`.

Rewrite `hv`, `hw` using `[_root_.GlobalTheory.BetaEx.mem_std]`. Use `Subring.sum_mem _ fun j _ => Subring.mul_mem _ ?_ ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `hv j`. Rewrite using `[← ha]`. Conclude with `complexConj_coe_mem_range_algebraMap a`.

Take `⟨b, hb⟩` from `hw j`. Conclude with `⟨b, hb⟩`. Introduce `h`. Rewrite using `[_root_.GlobalTheory.BetaEx.mem_std]`. Introduce `j`.

Establish `hsingle : (Pi.single j 1 : Fin n → E) ∈ _root_.Formalism.L2.Pj.stdLat E n`. Rewrite using `[_root_.GlobalTheory.BetaEx.mem_std]`. Introduce `i`. Use `⟨if i = j then 1 else 0, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hij]`. Establish `hc` using `h _ hsingle`. Simplify using `only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hc`.

Take `⟨b, hb⟩` from `hc`. Take `⟨a, ha⟩` from `complexConj_coe_mem_range_algebraMap b`. Use `⟨a, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(algebraMap (𝓞 E) E) a = v j`. Rewrite using `[ha]`.

Express the relevant statement in the definitionally equal form `IsCMField.complexConj E ((algebraMap (𝓞 E) E) b) = v j`. Rewrite using `[hb, _root_.mul_one, IsCMField.complexConj_apply_apply]`.
-/
theorem _root_.GlobalTheory.ShortLawsCompare.unimod_std [IsCMField E] (n : ℕ) :
    _root_.Formalism.L2.Pj.GenLat.Unimod (⟨_root_.Formalism.L2.Pj.stdLat E n⟩ : _root_.Formalism.L2.Pj.GenLat E n) := by
  unfold _root_.Formalism.L2.Pj.GenLat.Unimod
  intro v
  show v ∈ _root_.Formalism.L2.Pj.stdLat E n ↔ ∀ w ∈ _root_.Formalism.L2.Pj.stdLat E n, _
  constructor
  · intro hv w hw
    rw [_root_.GlobalTheory.BetaEx.mem_std] at hv hw
    refine Subring.sum_mem _ fun j _ => Subring.mul_mem _ ?_ ?_
    · obtain ⟨a, ha⟩ := hv j
      rw [← ha]
      exact complexConj_coe_mem_range_algebraMap a
    · obtain ⟨b, hb⟩ := hw j
      exact ⟨b, hb⟩
  · intro h
    rw [_root_.GlobalTheory.BetaEx.mem_std]
    intro j
    have hsingle : (Pi.single j 1 : Fin n → E) ∈ _root_.Formalism.L2.Pj.stdLat E n := by
      rw [_root_.GlobalTheory.BetaEx.mem_std]
      intro i
      refine ⟨if i = j then 1 else 0, ?_⟩
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    have hc := h _ hsingle
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at hc
    obtain ⟨b, hb⟩ := hc
    obtain ⟨a, ha⟩ := complexConj_coe_mem_range_algebraMap b
    refine ⟨a, ?_⟩
    change (algebraMap (𝓞 E) E) a = v j
    rw [ha]
    change IsCMField.complexConj E ((algebraMap (𝓞 E) E) b) = v j
    rw [hb, _root_.mul_one, IsCMField.complexConj_apply_apply]

end Lattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Beta

variable (c : Coeff l)

set_option autoImplicit false in
open NumberField MvPolynomial in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} in
variable (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) in
/- English proof (translation)
Unfold `_root_.Formalism.L2.Pj.idealAt`. Take `⟨k, hk, -, hkstd⟩` from `hT`. Establish `hk0 : k ≠ 0`. Introduce and unpack `rfl`. Conclude with `hb (Nat.coprime_zero_left _ |>.mp hk)`.

Establish `hfrac` using `_root_.GlobalTheory.BetaEx.frac_of_bdd (_root_.GlobalTheory.BetaEx.bdd_of_unimod Λ hU)`. Take `⟨s, hs⟩` from `FractionalIdeal.fg_of_isNoetherianRing le_rfl (⟨_, hfrac⟩ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)`. Establish `hspan : Submodule.span (𝓞 c.F) (_root_.Formalism.L2.Pj.embF c τ '' _root_.Formalism.L2.Pj.detSet Λ.La) = Submodule.span (𝓞 c.F) (_root_.Formalism.L2.Pj.embF c τ '' (s : Set E))`. Rewrite using `[← _root_.GlobalTheory.BetaEx.span_image_span (_root_.Formalism.L2.Pj.embF c τ) (_root_.Formalism.L2.Pj.detSet Λ.La), ← _root_.GlobalTheory.BetaEx.span_image_span (_root_.Formalism.L2.Pj.embF c τ) (s : Set E)]`. Use `congr 2`.

Rewrite using `[hs]`. Both sides reduce to the same expression. Establish `hfg : (Submodule.span (𝓞 c.F) (_root_.Formalism.L2.Pj.embF c τ '' _root_.Formalism.L2.Pj.detSet Λ.La)).FG`. Rewrite using `[hspan]`. Conclude with `Submodule.fg_span (s.finite_toSet.image _)`.

Set `J : FractionalIdeal (nonZeroDivisors (𝓞 c.F)) c.F` to `⟨_, FractionalIdeal.isFractional_of_fg hfg⟩`. Establish `hdet : ((k : E) ^ n) ∈ _root_.Formalism.L2.Pj.detSet Λ.La`. Rewrite using `[_root_.GlobalTheory.BetaEx.mem_detSet]`. Use `⟨(k : E) • (1 : Matrix (Fin n) (Fin n) E), fun i => ?_, by simp [Matrix.det_smul]⟩` and prove the remaining obligations. Establish `hrow : ((k : E) • (1 : Matrix (Fin n) (Fin n) E)) i = ((k : ℕ) : 𝓞 E) • (1 : Matrix (Fin n) (Fin n) E) i`.

Use extensionality with `j`. Simplify using `[Algebra.smul_def]`. Rewrite using `[hrow]`. Apply `hkstd` to reduce the goal to its premises. Use `Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) ?_` and prove the remaining obligations.

Rewrite using `[_root_.GlobalTheory.BetaEx.mem_std]`. Introduce `j`. Use `⟨if i = j then 1 else 0, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hJ : J ≠ 0`. Introduce `h0`. Establish `hbot : (J : Submodule (𝓞 c.F) c.F) = ⊥`. Rewrite using `[h0]`. Conclude with `FractionalIdeal.coe_zero`.

Establish `hmem : _root_.Formalism.L2.Pj.embF c τ ((k : E) ^ n) ∈ (J : Submodule (𝓞 c.F) c.F)` using `Submodule.subset_span ⟨_, hdet, rfl⟩`. Rewrite `hmem` using `[hbot, Submodule.mem_bot, map_eq_zero]`. Conclude with `pow_ne_zero n (Nat.cast_ne_zero.mpr hk0) hmem`. Use `isUnit_iff_exists_inv.mpr ⟨((J⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 c.F)) c.F) : Submodule (𝓞 c.F) c.F), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(J : Submodule (𝓞 c.F) c.F) * _ = 1`.

Rewrite using `[← FractionalIdeal.coe_mul, mul_inv_cancel₀ hJ, FractionalIdeal.coe_one]`.
-/
theorem _root_.GlobalTheory.ShortLawsCompare.isUnit_idealAt {n b : ℕ} {Λ : _root_.Formalism.L2.Pj.GenLat E n}
    (hT : Λ.TrivAt b) (hU : Λ.Unimod) (hb : b ≠ 1) (τ : E →+* ℂ) :
    IsUnit (_root_.Formalism.L2.Pj.idealAt c Λ.La τ) := by
  unfold _root_.Formalism.L2.Pj.idealAt
  obtain ⟨k, hk, -, hkstd⟩ := hT
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hb (Nat.coprime_zero_left _ |>.mp hk)
  have hfrac := _root_.GlobalTheory.BetaEx.frac_of_bdd
    (_root_.GlobalTheory.BetaEx.bdd_of_unimod Λ hU)
  obtain ⟨s, hs⟩ := FractionalIdeal.fg_of_isNoetherianRing le_rfl
    (⟨_, hfrac⟩ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
  have hspan : Submodule.span (𝓞 c.F) (_root_.Formalism.L2.Pj.embF c τ '' _root_.Formalism.L2.Pj.detSet Λ.La) =
      Submodule.span (𝓞 c.F) (_root_.Formalism.L2.Pj.embF c τ '' (s : Set E)) := by
    rw [← _root_.GlobalTheory.BetaEx.span_image_span (_root_.Formalism.L2.Pj.embF c τ) (_root_.Formalism.L2.Pj.detSet Λ.La),
      ← _root_.GlobalTheory.BetaEx.span_image_span (_root_.Formalism.L2.Pj.embF c τ) (s : Set E)]
    congr 2
    rw [hs]
    rfl
  have hfg : (Submodule.span (𝓞 c.F) (_root_.Formalism.L2.Pj.embF c τ '' _root_.Formalism.L2.Pj.detSet Λ.La)).FG := by
    rw [hspan]
    exact Submodule.fg_span (s.finite_toSet.image _)
  let J : FractionalIdeal (nonZeroDivisors (𝓞 c.F)) c.F :=
    ⟨_, FractionalIdeal.isFractional_of_fg hfg⟩
  have hdet : ((k : E) ^ n) ∈ _root_.Formalism.L2.Pj.detSet Λ.La := by
    rw [_root_.GlobalTheory.BetaEx.mem_detSet]
    refine ⟨(k : E) • (1 : Matrix (Fin n) (Fin n) E), fun i => ?_, by simp [Matrix.det_smul]⟩
    have hrow : ((k : E) • (1 : Matrix (Fin n) (Fin n) E)) i =
        ((k : ℕ) : 𝓞 E) • (1 : Matrix (Fin n) (Fin n) E) i := by
      ext j
      simp [Algebra.smul_def]
    rw [hrow]
    apply hkstd
    refine Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) ?_
    rw [_root_.GlobalTheory.BetaEx.mem_std]
    intro j
    refine ⟨if i = j then 1 else 0, ?_⟩
    rw [Matrix.one_apply]
    split_ifs <;> simp
  have hJ : J ≠ 0 := by
    intro h0
    have hbot : (J : Submodule (𝓞 c.F) c.F) = ⊥ := by
      rw [h0]
      exact FractionalIdeal.coe_zero
    have hmem : _root_.Formalism.L2.Pj.embF c τ ((k : E) ^ n) ∈ (J : Submodule (𝓞 c.F) c.F) :=
      Submodule.subset_span ⟨_, hdet, rfl⟩
    rw [hbot, Submodule.mem_bot, map_eq_zero] at hmem
    exact pow_ne_zero n (Nat.cast_ne_zero.mpr hk0) hmem
  refine isUnit_iff_exists_inv.mpr
    ⟨((J⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 c.F)) c.F) : Submodule (𝓞 c.F) c.F), ?_⟩
  change (J : Submodule (𝓞 c.F) c.F) * _ = 1
  rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hJ, FractionalIdeal.coe_one]

set_option autoImplicit false in
open NumberField MvPolynomial in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} in
variable (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) in

/- English proof (translation)
Unfold `_root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility.IsBeta _root_.Formalism.L2.Pj.BetaIs _root_.Formalism.L2.Pj.BetaAbs at h h'`. Take `⟨hβ, hs, hn⟩` from `h`. Take `⟨-, hs', hn'⟩` from `h'`. Establish `hP : IsUnit (∏ τ, _root_.Formalism.L2.Pj.idealAt c Λ.La τ ^ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult Dw τ)`. Use `Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one (fun τ _ => ?_)` and prove the remaining obligations.

Establish `h3` using `l.three_le`. Conclude with `(_root_.GlobalTheory.ShortLawsCompare.isUnit_idealAt c hT hU (by omega) τ).pow _`. Establish `heq : (𝓞 c.F ∙ β) = 𝓞 c.F ∙ β'` using `hP.mul_right_cancel (hs.trans hs'.symm)`. Take `⟨u, hu⟩` from `Submodule.span_singleton_eq_span_singleton.mp heq`. Establish `hβ'eq : β' = ((u : 𝓞 c.F) : c.F) * β`.

Rewrite using `[← hu]`. Both sides reduce to the same expression. Use `⟨((u : 𝓞 c.F) : c.F), ?_, hβ'eq⟩` and prove the remaining obligations. Establish `htors : u ∈ NumberField.Units.torsion c.F`. Rewrite using `[NumberField.Units.mem_torsion]`.

Introduce `w`. Rewrite using `[← w.mk_embedding, NumberField.InfinitePlace.apply]`. Establish `h1` using `hn w.embedding`. Establish `h2` using `hn' w.embedding`. Establish `hne : ‖w.embedding β‖ ≠ 0` using `by simpa using hβ`.

Establish `hsq : ‖w.embedding ((u : 𝓞 c.F) : c.F)‖ ^ 2 * ‖w.embedding β‖ ^ 2 = 1 * ‖w.embedding β‖ ^ 2`. Rewrite using `[_root_.one_mul, ← _root_.mul_pow, ← norm_mul, ← map_mul, ← hβ'eq, h2, h1]`. Establish `hsq'` using `mul_right_cancel₀ (pow_ne_zero 2 hne) hsq`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp hsq'`. Take `⟨m, hm, hum⟩` from `isOfFinOrder_iff_pow_eq_one.mp ((CommGroup.mem_torsion _).mp htors)`.

Use `isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, ?_⟩` and prove the remaining obligations. Use `congrArg (fun x : (𝓞 c.F)ˣ => ((x : 𝓞 c.F) : c.F)) hum` as an intermediate fact. Simplify using `using this`.
-/
theorem _root_.GlobalTheory.ShortLawsCompare.isBeta_ratio {n : ℕ} {Λ : _root_.Formalism.L2.Pj.GenLat E n} (hU : Λ.Unimod)
    (hT : Λ.TrivAt l.M) {β β' : c.F}
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility.IsBeta Dw c Λ β) (h' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility.IsBeta Dw c Λ β') :
    ∃ ζ : c.F, IsOfFinOrder ζ ∧ β' = ζ * β := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility.IsBeta _root_.Formalism.L2.Pj.BetaIs _root_.Formalism.L2.Pj.BetaAbs at h h'
  obtain ⟨hβ, hs, hn⟩ := h
  obtain ⟨-, hs', hn'⟩ := h'
  have hP : IsUnit (∏ τ, _root_.Formalism.L2.Pj.idealAt c Λ.La τ ^ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult Dw τ) := by
    refine Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
      (fun τ _ => ?_)
    have h3 := l.three_le
    exact (_root_.GlobalTheory.ShortLawsCompare.isUnit_idealAt c hT hU (by omega) τ).pow _
  have heq : (𝓞 c.F ∙ β) = 𝓞 c.F ∙ β' := hP.mul_right_cancel (hs.trans hs'.symm)
  obtain ⟨u, hu⟩ := Submodule.span_singleton_eq_span_singleton.mp heq
  have hβ'eq : β' = ((u : 𝓞 c.F) : c.F) * β := by
    rw [← hu]
    rfl
  refine ⟨((u : 𝓞 c.F) : c.F), ?_, hβ'eq⟩
  have htors : u ∈ NumberField.Units.torsion c.F := by
    rw [NumberField.Units.mem_torsion]
    intro w
    rw [← w.mk_embedding, NumberField.InfinitePlace.apply]
    have h1 := hn w.embedding
    have h2 := hn' w.embedding
    have hne : ‖w.embedding β‖ ≠ 0 := by simpa using hβ
    have hsq : ‖w.embedding ((u : 𝓞 c.F) : c.F)‖ ^ 2 * ‖w.embedding β‖ ^ 2 =
        1 * ‖w.embedding β‖ ^ 2 := by
      rw [_root_.one_mul, ← _root_.mul_pow, ← norm_mul, ← map_mul, ← hβ'eq, h2, h1]
    have hsq' := mul_right_cancel₀ (pow_ne_zero 2 hne) hsq
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp hsq'
  obtain ⟨m, hm, hum⟩ := isOfFinOrder_iff_pow_eq_one.mp ((CommGroup.mem_torsion _).mp htors)
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, ?_⟩
  have := congrArg (fun x : (𝓞 c.F)ˣ => ((x : 𝓞 c.F) : c.F)) hum
  simpa using this

set_option autoImplicit false in
open NumberField MvPolynomial in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} in
variable (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) in

/- English proof (translation)
Unfold `_root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility.IsBeta _root_.Formalism.L2.Pj.BetaIs _root_.Formalism.L2.Pj.BetaAbs at h ⊢`. Take `⟨hβ, hspan, hnorm⟩` from `h`. Take `⟨k, hk, hζk⟩` from `isOfFinOrder_iff_pow_eq_one.mp hζ`. Establish `hζ0 : ζ ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hζk` using `[zero_pow hk.ne']`. Conclude with `zero_ne_one hζk`. Establish `hint : IsIntegral ℤ ζ` using `IsIntegral.of_pow hk (by rw [hζk]; exact isIntegral_one)`. Establish `hint' : IsIntegral ℤ ζ⁻¹` using `IsIntegral.of_pow hk (by rw [inv_pow, hζk, inv_one]; exact isIntegral_one)`. Establish `hsp : (𝓞 c.F ∙ (ζ * β)) = 𝓞 c.F ∙ β`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]`. Conclude with `⟨⟨ζ, hint⟩, rfl⟩`. Rewrite using `[Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]`. Use `⟨⟨ζ⁻¹, hint'⟩, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `ζ⁻¹ * (ζ * β) = β`. Rewrite using `[← _root_.mul_assoc, inv_mul_cancel₀ hζ0, _root_.one_mul]`. Use `⟨mul_ne_zero hζ0 hβ, by rw [hsp]; exact hspan, fun σ => ?_⟩` and prove the remaining obligations. Establish `hσ : ‖σ ζ‖ = 1` using `Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hζk, map_one]) hk.ne'`. Rewrite using `[map_mul, norm_mul, hσ, _root_.one_mul]`.

Conclude with `hnorm σ`.
-/
theorem _root_.GlobalTheory.ShortLawsCompare.isBeta_mul {n : ℕ} {Λ : _root_.Formalism.L2.Pj.GenLat E n} {β ζ : c.F}
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility.IsBeta Dw c Λ β) (hζ : IsOfFinOrder ζ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility.IsBeta Dw c Λ (ζ * β) := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility.IsBeta _root_.Formalism.L2.Pj.BetaIs _root_.Formalism.L2.Pj.BetaAbs at h ⊢
  obtain ⟨hβ, hspan, hnorm⟩ := h
  obtain ⟨k, hk, hζk⟩ := isOfFinOrder_iff_pow_eq_one.mp hζ
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hk.ne'] at hζk
    exact zero_ne_one hζk
  have hint : IsIntegral ℤ ζ := IsIntegral.of_pow hk (by rw [hζk]; exact isIntegral_one)
  have hint' : IsIntegral ℤ ζ⁻¹ :=
    IsIntegral.of_pow hk (by rw [inv_pow, hζk, inv_one]; exact isIntegral_one)
  have hsp : (𝓞 c.F ∙ (ζ * β)) = 𝓞 c.F ∙ β := by
    apply le_antisymm
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      exact ⟨⟨ζ, hint⟩, rfl⟩
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      refine ⟨⟨ζ⁻¹, hint'⟩, ?_⟩
      change ζ⁻¹ * (ζ * β) = β
      rw [← _root_.mul_assoc, inv_mul_cancel₀ hζ0, _root_.one_mul]
  refine ⟨mul_ne_zero hζ0 hβ, by rw [hsp]; exact hspan, fun σ => ?_⟩
  have hσ : ‖σ ζ‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hζk, map_one]) hk.ne'
  rw [map_mul, norm_mul, hσ, _root_.one_mul]
  exact hnorm σ

/- English proof (translation)
Establish `h` using `GlobalTheory.BetaEx.betaExists E H Dw l c n b hK Λ hU hT`. Unfold `betaH`. Rewrite using `[dif_pos h]`. Conclude with `h.choose_spec`.
-/
theorem isBeta_betaH (hK : KPsiIn (Dw := Dw) c) {n b : ℕ} {Λ : GenLat E n} (hU : Λ.Unimod) (hT : Λ.TrivAt b) :
    BlockLatticeAdmissibility.IsBeta Dw c Λ (betaH (Dw := Dw) c Λ) := by
  have h := GlobalTheory.BetaEx.betaExists E H Dw l c n b hK Λ hU hT
  unfold betaH
  rw [dif_pos h]
  exact h.choose_spec

end Beta

section Level

variable {Xo : Moduli Dw l} {c : Coeff l}

end Level

section Objects

variable (c : Coeff l) {n₁ n₂ : ℕ}

omit [IsCMField E] in

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem blockLat_eq (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) : BlockLatticeAdmissibility.blockLat Λ₁ Λ₂ = BlockProductLattices.blockLat Λ₁ Λ₂ := rfl

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem latAdm_iff {n : ℕ} (bad : ℕ) (Λ : GenLat E n) : BlockLatticeAdmissibility.LatAdm l bad Λ ↔ BlockProductLattices.LatOK bad l.M Λ := Iff.rfl

set_option autoImplicit false in
open NumberField MvPolynomial in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {E : Type} [Field E] [NumberField E] in
variable {n₁ n₂ : ℕ} in
/- English proof (translation)
Unfold `_root_.Formalism.L2.Pj.GenLat.Unimod at *`. Introduce `v`. Simplify using `only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockProductLattices.mem_blockLat, Fin.sum_univ_add]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hv₁, hv₂⟩ w ⟨hw₁, hw₂⟩`.

Conclude with `add_mem ((h₁ _).1 hv₁ _ hw₁) ((h₂ _).1 hv₂ _ hw₂)`. Introduce `h`. Use `⟨(h₁ _).2 fun w₁ hw₁ => ?_, (h₂ _).2 fun w₂ hw₂ => ?_⟩` and prove the remaining obligations. Establish `hz : (fun j => (0 : Fin n₂ → E) j) ∈ Λ₂.La` using `Λ₂.La.zero_mem`. Use `h (Fin.append w₁ 0) ⟨by simpa using hw₁, by simpa using hz⟩` as an intermediate fact.

Simplify using `using this`. Establish `hz : (fun j => (0 : Fin n₁ → E) j) ∈ Λ₁.La` using `Λ₁.La.zero_mem`. Use `h (Fin.append 0 w₂) ⟨by simpa using hz, by simpa using hw₂⟩` as an intermediate fact. Simplify using `using this`.
-/
private theorem blockLat_unimod [IsCMField E] {Λ₁ : _root_.Formalism.L2.Pj.GenLat E n₁}
    {Λ₂ : _root_.Formalism.L2.Pj.GenLat E n₂} (h₁ : Λ₁.Unimod) (h₂ : Λ₂.Unimod) :
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockProductLattices.blockLat Λ₁ Λ₂).Unimod := by
  unfold _root_.Formalism.L2.Pj.GenLat.Unimod at *
  intro v
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockProductLattices.mem_blockLat, Fin.sum_univ_add]
  constructor
  · rintro ⟨hv₁, hv₂⟩ w ⟨hw₁, hw₂⟩
    exact add_mem ((h₁ _).1 hv₁ _ hw₁) ((h₂ _).1 hv₂ _ hw₂)
  · intro h
    refine ⟨(h₁ _).2 fun w₁ hw₁ => ?_, (h₂ _).2 fun w₂ hw₂ => ?_⟩
    · have hz : (fun j => (0 : Fin n₂ → E) j) ∈ Λ₂.La := Λ₂.La.zero_mem
      have := h (Fin.append w₁ 0) ⟨by simpa using hw₁, by simpa using hz⟩
      simpa using this
    · have hz : (fun j => (0 : Fin n₁ → E) j) ∈ Λ₁.La := Λ₁.La.zero_mem
      have := h (Fin.append 0 w₂) ⟨by simpa using hz, by simpa using hw₂⟩
      simpa using this

set_option autoImplicit false in
open NumberField MvPolynomial in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {E : Type} [Field E] [NumberField E] in
variable {n₁ n₂ : ℕ} in
/- English proof (translation)
Unfold `_root_.Formalism.L2.Pj.GenLat.TrivAt at *`. Take `⟨k₁, hk₁, a₁, b₁⟩` from `h₁`. Take `⟨k₂, hk₂, a₂, b₂⟩` from `h₂`. Establish `hle₁ : Ideal.span {((k₁ * k₂ : ℕ) : 𝓞 E)} ≤ Ideal.span {((k₁ : ℕ) : 𝓞 E)}` using `Ideal.span_singleton_le_span_singleton.mpr ⟨(k₂ : 𝓞 E), by push_cast; ring⟩`. Establish `hle₂ : Ideal.span {((k₁ * k₂ : ℕ) : 𝓞 E)} ≤ Ideal.span {((k₂ : ℕ) : 𝓞 E)}` using `Ideal.span_singleton_le_span_singleton.mpr ⟨(k₁ : 𝓞 E), by push_cast; ring⟩`.

Use `⟨k₁ * k₂, Nat.Coprime.mul hk₁ hk₂, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[stdLat_add_eq_inf_comap_funLeft]`. Conclude with `smul_inf_comap_funLeft_le _ _ _ _ _ ((Submodule.smul_mono_left hle₁).trans a₁) ((Submodule.smul_mono_left hle₂).trans a₂)`. Rewrite using `[stdLat_add_eq_inf_comap_funLeft]`. Conclude with `smul_inf_comap_funLeft_le _ _ _ _ _ ((Submodule.smul_mono_left hle₁).trans b₁) ((Submodule.smul_mono_left hle₂).trans b₂)`.
-/
private theorem blockLat_trivAt {Λ₁ : _root_.Formalism.L2.Pj.GenLat E n₁} {Λ₂ : _root_.Formalism.L2.Pj.GenLat E n₂} {b : ℕ}
    (h₁ : Λ₁.TrivAt b) (h₂ : Λ₂.TrivAt b) : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockProductLattices.blockLat Λ₁ Λ₂).TrivAt b := by
  unfold _root_.Formalism.L2.Pj.GenLat.TrivAt at *
  obtain ⟨k₁, hk₁, a₁, b₁⟩ := h₁
  obtain ⟨k₂, hk₂, a₂, b₂⟩ := h₂
  have hle₁ : Ideal.span {((k₁ * k₂ : ℕ) : 𝓞 E)} ≤ Ideal.span {((k₁ : ℕ) : 𝓞 E)} :=
    Ideal.span_singleton_le_span_singleton.mpr ⟨(k₂ : 𝓞 E), by push_cast; ring⟩
  have hle₂ : Ideal.span {((k₁ * k₂ : ℕ) : 𝓞 E)} ≤ Ideal.span {((k₂ : ℕ) : 𝓞 E)} :=
    Ideal.span_singleton_le_span_singleton.mpr ⟨(k₁ : 𝓞 E), by push_cast; ring⟩
  refine ⟨k₁ * k₂, Nat.Coprime.mul hk₁ hk₂, ?_, ?_⟩
  · rw [stdLat_add_eq_inf_comap_funLeft]
    exact smul_inf_comap_funLeft_le _ _ _ _ _ ((Submodule.smul_mono_left hle₁).trans a₁)
      ((Submodule.smul_mono_left hle₂).trans a₂)
  · rw [stdLat_add_eq_inf_comap_funLeft]
    exact smul_inf_comap_funLeft_le _ _ _ _ _ ((Submodule.smul_mono_left hle₁).trans b₁)
      ((Submodule.smul_mono_left hle₂).trans b₂)

set_option autoImplicit false in
open NumberField MvPolynomial in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} in
variable (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) {n₁ n₂ : ℕ} in
/- English proof (translation)
Assemble the required witnesses or components as `⟨blockLat_unimod h₁.1 h₂.1, blockLat_trivAt h₁.2.1 h₂.2.1, blockLat_trivAt h₁.2.2 h₂.2.2⟩`.
-/
theorem _root_.GlobalTheory.ShortLawsCompare.latOK_block {bad : ℕ} {Λ₁ : _root_.Formalism.L2.Pj.GenLat E n₁} {Λ₂ : _root_.Formalism.L2.Pj.GenLat E n₂}
    (h₁ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockProductLattices.LatOK bad l.M Λ₁)
    (h₂ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockProductLattices.LatOK bad l.M Λ₂) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockProductLattices.LatOK bad l.M (_root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockProductLattices.blockLat Λ₁ Λ₂) :=
  ⟨blockLat_unimod h₁.1 h₂.1, blockLat_trivAt h₁.2.1 h₂.2.1,
    blockLat_trivAt h₁.2.2 h₂.2.2⟩

end Objects

variable (Xo : Moduli Dw l) (c : Coeff l)

/- English proof (translation)
Establish `key : ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (φ : S →ₐ[c.F] S') (a b d : c.F) (Z : S'), φ v = algebraMap c.F S' (β⁻¹ * a * b * d) * Z ↔ φ (algebraMap c.F S β * v) = algebraMap c.F S' (1⁻¹ * a * b * d) * Z`. Introduce `S' _ _ φ a b d Z`. Establish `hu : IsUnit (algebraMap c.F S' β)` using `(IsUnit.mk0 β hβ).map _`. Rewrite using `[map_mul φ, φ.commutes, ← hu.mul_right_inj, ← _root_.mul_assoc, ← map_mul]`. Establish `: β * (β⁻¹ * a * b * d) = 1⁻¹ * a * b * d` using `by field_simp`.

Rewrite using `[this]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7⟩`. Conclude with `⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, (key S' φ _ _ _ _).1 h7⟩`. Introduce and unpack `⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7⟩`.

Conclude with `⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, (key S' φ _ _ _ _).2 h7⟩`.
-/
theorem shortValAt_beta (nab : NabV Xo c) {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) {β : c.F}
    (hβ : β ≠ 0) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (v : S) :
    ShortValAt Xo c nab w Λ β N P y v ↔ ShortValAt Xo c nab w Λ 1 N P y (algebraMap c.F S β * v) := by
  have key : ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (φ : S →ₐ[c.F] S') (a b d : c.F) (Z : S'),
      φ v = algebraMap c.F S' (β⁻¹ * a * b * d) * Z ↔
        φ (algebraMap c.F S β * v) = algebraMap c.F S' (1⁻¹ * a * b * d) * Z := by
    intro S' _ _ φ a b d Z
    have hu : IsUnit (algebraMap c.F S' β) := (IsUnit.mk0 β hβ).map _
    rw [map_mul φ, φ.commutes, ← hu.mul_right_inj, ← _root_.mul_assoc, ← map_mul]
    have : β * (β⁻¹ * a * b * d) = 1⁻¹ * a * b * d := by field_simp
    rw [this]
  constructor
  · rintro ⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, (key S' φ _ _ _ _).1 h7⟩
  · rintro ⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, (key S' φ _ _ _ _).2 h7⟩

def CarryN (nab : NabV Xo c) (bad : ℕ) : Prop :=
  ∀ (n : ℕ) (Λ : GenLat E n) (N N' : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (w : (Fin n → LevQ Dw l) → c.F) (β : c.F),
    BlockProductLattices.LatOK bad l.M Λ → Λ.LevOK N l.M → Λ.LevOK N' l.M → P ∈ harmL c Λ a → β ≠ 0 →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S),
      (∃ v, ShortValAt Xo c nab w Λ β N P y v) → ∃ v', ShortValAt Xo c nab w Λ β N' P y v'

def CarryBlock (nab : NabV Xo c) (bad : ℕ) : Prop :=
  ∀ (n₁ n₂ : ℕ) (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) (N : ℕ) (a₁ a₂ : (E →+* ℂ) × ℕ → ℕ)
    (P₁ : MvPolynomial (LtN Dw n₁) c.F) (P₂ : MvPolynomial (LtN Dw n₂) c.F)
    (w₁ : (Fin n₁ → LevQ Dw l) → c.F) (w₂ : (Fin n₂ → LevQ Dw l) → c.F),
    BlockProductLattices.LatOK bad l.M Λ₁ → BlockProductLattices.LatOK bad l.M Λ₂ → Λ₁.LevOK N l.M → Λ₂.LevOK N l.M →
    P₁ ∈ harmL c Λ₁ a₁ → P₂ ∈ harmL c Λ₂ a₂ →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S),
      (∃ v₁, ShortValAt Xo c nab w₁ Λ₁ 1 N P₁ y v₁) → (∃ v₂, ShortValAt Xo c nab w₂ Λ₂ 1 N P₂ y v₂) →
      ∃ v, ShortValAt Xo c nab (BlockProductLattices.blockDat c w₁ w₂) (BlockProductLattices.blockLat Λ₁ Λ₂) 1 N (BlockProductLattices.blockPol c P₁ P₂) y v

def CarryMove (nab : NabV Xo c) (bad : ℕ) : Prop :=
  ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (w : (Fin n → LevQ Dw l) → c.F) (β : c.F) (g gA : Dw.La →ₗ[𝓞 E] Dw.La),
    BlockProductLattices.LatOK bad l.M Λ → Λ.LevOK N l.M → P ∈ harmL c Λ a → β ≠ 0 →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S), levR (g, gA) y y' →
      ((∃ v', ShortValAt Xo c nab (BlockLatticeAdmissibility.moveDat g w) Λ β N P y' v') ↔ ∃ v, ShortValAt Xo c nab w Λ β N P y v)

def ValuesExist (nab : NabV Xo c) (bad : ℕ) : Prop :=
  ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (w : (Fin n → LevQ Dw l) → c.F) (β : c.F),
    BlockProductLattices.LatOK bad l.M Λ → Λ.LevOK N l.M → P ∈ harmL c Λ a → β ≠ 0 →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), ∃ v, ShortValAt Xo c nab w Λ β N P y v

def BlockHarmLev (Dw : Datum H) (c : Coeff l) (bad : ℕ) : Prop :=
  ∀ (n₁ n₂ : ℕ) (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) (N : ℕ) (a₁ a₂ : (E →+* ℂ) × ℕ → ℕ)
    (P₁ : MvPolynomial (LtN Dw n₁) c.F) (P₂ : MvPolynomial (LtN Dw n₂) c.F),
    BlockProductLattices.LatOK bad l.M Λ₁ → BlockProductLattices.LatOK bad l.M Λ₂ → Λ₁.LevOK N l.M → Λ₂.LevOK N l.M →
    P₁ ∈ harmL c Λ₁ a₁ → P₂ ∈ harmL c Λ₂ a₂ →
      BlockProductLattices.blockPol c P₁ P₂ ∈ harmL c (BlockProductLattices.blockLat Λ₁ Λ₂) (a₁ + a₂)

variable [StarRing (𝓞 E)] {Xo c} {nab : NabV Xo c}

def LawsAt (nab : NabV Xo c) (bad : ℕ) : Prop :=
  BlockLatticeAdmissibility.FreeOfLevel Xo c nab bad ∧ BlockLatticeAdmissibility.BlockProduct Xo c nab bad ∧ BlockLatticeAdmissibility.LevelMove Xo c nab bad ∧
    BlockLatticeAdmissibility.BlockBeta Dw c bad

end GlobalTheory.ShortLawsCompare
