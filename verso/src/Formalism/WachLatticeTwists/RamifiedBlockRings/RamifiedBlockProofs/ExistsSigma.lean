import Formalism.WachLatticeTwists.RamifiedBlockRings.LemmaFiveThreeAnyResidueField
import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.AbsIrrOfSpan

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.RepresentationBoundsCohomology.BR

section

variable {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O']
  [IsDiscreteValuationRing O'] [Algebra O O'] {X d G : Type} [Fintype d] [DecidableEq d] [Group G] {t : ℕ}
  {bl : d → Fin (t + 1)} {T : Subalgebra O (X → O)} {r : G →* (X → Matrix d d O)} {π : X}
  {χ₁ ε : G →* Oˣ} {g₀ : G} {eB e₁ s : X → Matrix d d O} {D : RingData O X d G t bl}
  {D' : RingData O' X d G t bl}

/- English proof (translation)
Unfold `blockPoly`. Rewrite using `[← Polynomial.coe_mapRingHom, RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [h, Matrix.one_apply]`.
-/
private theorem blockPoly_map_lemma {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) {d : Type*}
    [Fintype d] [DecidableEq d] (e a : Matrix d d A) :
    blockPoly (e.map f) (a.map f) = (blockPoly e a).map f := by
  unfold blockPoly
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

/- English proof (translation)
Establish `h1 : bcM O' eB x = (eB x).map (algebraMap O O')` using `rfl`. Establish `h3 : bcR O' r g₀ x = (r g₀ x).map (algebraMap O O')` using `rfl`. Establish `hs : bcM O' s x = (s x).map (algebraMap O O')` using `rfl`. Establish `h2 : bcM O' eB x * bcR O' r g₀ x * bcM O' eB x + bcM O' s x = (eB x * r g₀ x * eB x + s x).map (algebraMap O O')`. Rewrite using `[h1, h3, hs]`.

Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Matrix.add_apply, map_sum, map_mul, map_add]`. Rewrite using `[h2, h1, blockPoly_map_lemma, blockPoly_map_lemma]`.
-/
theorem blockPoly_bc (x : X) :
    blockPoly ((bcM O' eB x).map (algebraMap O' (FractionRing O')))
      ((bcM O' eB x * bcR O' r g₀ x * bcM O' eB x + bcM O' s x).map (algebraMap O' (FractionRing O'))) =
    ((blockPoly (eB x) (eB x * r g₀ x * eB x + s x)).map (algebraMap O O')).map
      (algebraMap O' (FractionRing O')) := by
  have h1 : bcM O' eB x = (eB x).map (algebraMap O O') := rfl
  have h3 : bcR O' r g₀ x = (r g₀ x).map (algebraMap O O') := rfl
  have hs : bcM O' s x = (s x).map (algebraMap O O') := rfl
  have h2 : bcM O' eB x * bcR O' r g₀ x * bcM O' eB x + bcM O' s x =
      (eB x * r g₀ x * eB x + s x).map (algebraMap O O') := by
    rw [h1, h3, hs]
    ext i j
    simp [Matrix.mul_apply, Matrix.add_apply, map_sum, map_mul, map_add]
  rw [h2, h1, blockPoly_map_lemma, blockPoly_map_lemma]

/- English proof (translation)
Establish `hι'inj : Function.Injective (algebraMap O' (FractionRing O'))` using `IsFractionRing.injective O' (FractionRing O')`. Establish `hD0` using `hD`. Establish `hD'0` using `hD'`. Simplify using `only [RingDef] at hD0 hD'0`. Take `⟨-, huniq, -, -, hpπ, hrrπ, -⟩` from `hD0`.

Take `⟨hfac', -, -, -, hpπ', hrrπ', -⟩` from `hD'0`. Unfold `DistinctEigenvalueCornerPerturbation at hX`. Take `⟨-, -, -, -, hαX⟩` from `hX`. Establish `key : ∀ y' : D'.X', ∃! x' : D.X', D.p x' = D'.p y' ∧ ∀ i, i < t → algebraMap O O' ((D.rr i : D.X' → O) x') = (D'.rr i : D'.X' → O') y'`. Introduce `y'`.

Establish `h1 : ((blockPoly (eB (D'.p y')) (eB (D'.p y') * r g₀ (D'.p y') * eB (D'.p y') + s (D'.p y'))).map (algebraMap O O')).map (algebraMap O' (FractionRing O')) = ∏ i ∈ Finset.range t, (Polynomial.X - Polynomial.C (algebraMap O' (FractionRing O') ((D'.rr i : D'.X' → O') y')))`. Rewrite using `[← blockPoly_bc]`. Conclude with `hfac' y'`. Take `⟨α, -, hα⟩` from `hαX (D'.p y')`. Rewrite `hα` using `[blockPoly_map_lemma]`.

Take `⟨β, -, hβ⟩` from `rootsInt O _ t α hα`. Establish `hroot : ∀ i, i < t → ∃ b : O, algebraMap O O' b = (D'.rr i : D'.X' → O') y'`. Introduce `i hi`. Establish `h2` using `congrArg (Polynomial.eval (algebraMap O' (FractionRing O') ((D'.rr i : D'.X' → O') y'))) h1`. Rewrite `h2` using `[hβ]`.

Simplify using `only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h2`. Establish `h3 : ∏ k ∈ Finset.range t, (algebraMap O' (FractionRing O') ((D'.rr i : D'.X' → O') y') - algebraMap O' (FractionRing O') ((D'.rr k : D'.X' → O') y')) = 0` using `Finset.prod_eq_zero (Finset.mem_range.2 hi) (sub_self _)`. Rewrite `h2` using `[h3, Finset.prod_eq_zero_iff]`. Take `⟨j, -, hj0⟩` from `h2`. Conclude with `⟨β j, hι'inj (sub_eq_zero.1 hj0).symm⟩`.

Use `choose b hb using hroot`. Set `α' : ℕ → O` to `fun i => if h : i < t then b i h else 0`. Establish `hα' : ∀ i, i < t → algebraMap O O' (α' i) = (D'.rr i : D'.X' → O') y'`. Introduce `i hi`. Simplify using `only [α', dif_pos hi]`.

Conclude with `hb i hi`. Establish `hPinj : Function.Injective (Polynomial.map ((algebraMap O' (FractionRing O')).comp (algebraMap O O')))` using `Polynomial.map_injective _ (hι'inj.comp hj)`. Establish `hP2 : blockPoly (eB (D'.p y')) (eB (D'.p y') * r g₀ (D'.p y') * eB (D'.p y') + s (D'.p y')) = ∏ i ∈ Finset.range t, (Polynomial.X - Polynomial.C (α' i))`. Apply `hPinj` to reduce the goal to its premises. Rewrite using `[← Polynomial.map_map, h1]`.

Simplify using `only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, RingHom.comp_apply]`. Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[hα' i (Finset.mem_range.1 hi)]`. Establish `hfacO : blockPoly ((eB (D'.p y')).map (algebraMap O (FractionRing O))) ((eB (D'.p y') * r g₀ (D'.p y') * eB (D'.p y') + s (D'.p y')).map (algebraMap O (FractionRing O))) = ∏ i ∈ Finset.range t, (Polynomial.X - Polynomial.C (algebraMap O (FractionRing O) (α' i)))`. Rewrite using `[blockPoly_map_lemma, hP2]`.

Simplify using `only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]`. Take `⟨x', ⟨hx'1, hx'2⟩, hx'u⟩` from `huniq (D'.p y') α' hfacO`. Use `⟨x', ⟨hx'1, fun i hi => by rw [hx'2 i hi, hα' i hi]⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `z ⟨hz1, hz2⟩`. Use `hx'u z ⟨hz1, fun i hi => hj ?_⟩` and prove the remaining obligations.

Rewrite using `[hz2 i hi, hα' i hi]`. Use `choose σ hσ using fun y' => (key y').exists`. Use `⟨σ, fun y' => (hσ y').1, fun y' i hi => (hσ y').2 i hi, ?_⟩` and prove the remaining obligations. Use `(key D'.π').unique (hσ D'.π') ⟨by rw [hpπ, hpπ'], fun i hi => ?_⟩` and prove the remaining obligations. Rewrite using `[hrrπ i hi, hrrπ' i hi]`.

Simplify using `[bcChar]`.
-/
theorem exists_sigma (hj : Function.Injective (algebraMap O O')) (hX : DistinctEigenvalueCornerPerturbation O T r π t g₀ eB s)
    (hD : RingDef O T r π χ₁ ε g₀ eB e₁ s D)
    (hD' : RingDef O' (bcT O' T) (bcR O' r) π (bcChar O' χ₁) (bcChar O' ε) g₀ (bcM O' eB) (bcM O' e₁)
      (bcM O' s) D') :
    ∃ σ : D'.X' → D.X', (∀ y', D.p (σ y') = D'.p y') ∧
      (∀ y' i, i < t → algebraMap O O' ((D.rr i : D.X' → O) (σ y')) = (D'.rr i : D'.X' → O') y') ∧
      σ D'.π' = D.π' := by
  classical
  have hι'inj : Function.Injective (algebraMap O' (FractionRing O')) :=
    IsFractionRing.injective O' (FractionRing O')
  have hD0 := hD
  have hD'0 := hD'
  dsimp only [RingDef] at hD0 hD'0
  obtain ⟨-, huniq, -, -, hpπ, hrrπ, -⟩ := hD0
  obtain ⟨hfac', -, -, -, hpπ', hrrπ', -⟩ := hD'0
  unfold DistinctEigenvalueCornerPerturbation at hX
  obtain ⟨-, -, -, -, hαX⟩ := hX
  have key : ∀ y' : D'.X', ∃! x' : D.X', D.p x' = D'.p y' ∧
      ∀ i, i < t → algebraMap O O' ((D.rr i : D.X' → O) x') = (D'.rr i : D'.X' → O') y' := by
    intro y'
    have h1 : ((blockPoly (eB (D'.p y')) (eB (D'.p y') * r g₀ (D'.p y') * eB (D'.p y') + s (D'.p y'))).map
        (algebraMap O O')).map (algebraMap O' (FractionRing O')) =
        ∏ i ∈ Finset.range t, (Polynomial.X - Polynomial.C
          (algebraMap O' (FractionRing O') ((D'.rr i : D'.X' → O') y'))) := by
      rw [← blockPoly_bc]
      exact hfac' y'
    obtain ⟨α, -, hα⟩ := hαX (D'.p y')
    rw [blockPoly_map_lemma] at hα
    obtain ⟨β, -, hβ⟩ := rootsInt O _ t α hα
    have hroot : ∀ i, i < t → ∃ b : O, algebraMap O O' b = (D'.rr i : D'.X' → O') y' := by
      intro i hi
      have h2 := congrArg (Polynomial.eval
        (algebraMap O' (FractionRing O') ((D'.rr i : D'.X' → O') y'))) h1
      rw [hβ] at h2
      simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
        Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h2
      have h3 : ∏ k ∈ Finset.range t, (algebraMap O' (FractionRing O') ((D'.rr i : D'.X' → O') y') -
          algebraMap O' (FractionRing O') ((D'.rr k : D'.X' → O') y')) = 0 :=
        Finset.prod_eq_zero (Finset.mem_range.2 hi) (sub_self _)
      rw [h3, Finset.prod_eq_zero_iff] at h2
      obtain ⟨j, -, hj0⟩ := h2
      exact ⟨β j, hι'inj (sub_eq_zero.1 hj0).symm⟩
    choose b hb using hroot
    let α' : ℕ → O := fun i => if h : i < t then b i h else 0
    have hα' : ∀ i, i < t → algebraMap O O' (α' i) = (D'.rr i : D'.X' → O') y' := by
      intro i hi
      simp only [α', dif_pos hi]
      exact hb i hi
    have hPinj : Function.Injective
        (Polynomial.map ((algebraMap O' (FractionRing O')).comp (algebraMap O O'))) :=
      Polynomial.map_injective _ (hι'inj.comp hj)
    have hP2 : blockPoly (eB (D'.p y')) (eB (D'.p y') * r g₀ (D'.p y') * eB (D'.p y') + s (D'.p y')) =
        ∏ i ∈ Finset.range t, (Polynomial.X - Polynomial.C (α' i)) := by
      apply hPinj
      rw [← Polynomial.map_map, h1]
      simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
        RingHom.comp_apply]
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [hα' i (Finset.mem_range.1 hi)]
    have hfacO : blockPoly ((eB (D'.p y')).map (algebraMap O (FractionRing O)))
        ((eB (D'.p y') * r g₀ (D'.p y') * eB (D'.p y') + s (D'.p y')).map (algebraMap O (FractionRing O))) =
        ∏ i ∈ Finset.range t, (Polynomial.X - Polynomial.C (algebraMap O (FractionRing O) (α' i))) := by
      rw [blockPoly_map_lemma, hP2]
      simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    obtain ⟨x', ⟨hx'1, hx'2⟩, hx'u⟩ := huniq (D'.p y') α' hfacO
    refine ⟨x', ⟨hx'1, fun i hi => by rw [hx'2 i hi, hα' i hi]⟩, ?_⟩
    rintro z ⟨hz1, hz2⟩
    refine hx'u z ⟨hz1, fun i hi => hj ?_⟩
    rw [hz2 i hi, hα' i hi]
  choose σ hσ using fun y' => (key y').exists
  refine ⟨σ, fun y' => (hσ y').1, fun y' i hi => (hσ y').2 i hi, ?_⟩
  refine (key D'.π').unique (hσ D'.π') ⟨by rw [hpπ, hpπ'], fun i hi => ?_⟩
  rw [hrrπ i hi, hrrπ' i hi]
  simp [bcChar]

/- English proof (translation)
Simplify using `only [RingDef] at hD hD'`. Take `⟨-, -, hT, -⟩` from `hD`. Take `⟨-, -, hT', -⟩` from `hD'`. Rewrite `hf` using `[hT]`. Rewrite using `[hT']`.

Proceed by induction on `hf using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Apply `Algebra.subset_adjoin` to reduce the goal to its premises. Break down `hx with ⟨g, hg, rfl⟩ | ⟨i, hi, rfl⟩` into its components or cases. Use `Or.inl ⟨algebraMap O O' ∘ g, Algebra.subset_adjoin ⟨g, hg, rfl⟩, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `y'`. Simplify using `[hσ1 y']`. Conclude with `Or.inr ⟨i, hi, funext fun y' => hσ2 y' i hi⟩`. Consider the case `algebraMap c`. Use `Subalgebra.algebraMap_mem (Algebra.adjoin O' _) (algebraMap O O' c) using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `y'`. Simplify using the standard rewrite rules. Consider the case `add x y _ _ ihx ihy`. Use `Subalgebra.add_mem _ ihx ihy using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `y'`.

Simplify using the standard rewrite rules. Consider the case `mul x y _ _ ihx ihy`. Use `Subalgebra.mul_mem _ ihx ihy using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `y'`. Simplify using the standard rewrite rules.
-/
theorem bcT'_mem (hD : RingDef O T r π χ₁ ε g₀ eB e₁ s D)
    (hD' : RingDef O' (bcT O' T) (bcR O' r) π (bcChar O' χ₁) (bcChar O' ε) g₀ (bcM O' eB) (bcM O' e₁)
      (bcM O' s) D') (σ : D'.X' → D.X') (hσ1 : ∀ y', D.p (σ y') = D'.p y')
    (hσ2 : ∀ y' i, i < t →
      algebraMap O O' ((D.rr i : D.X' → O) (σ y')) = (D'.rr i : D'.X' → O') y')
    {f : D.X' → O} (hf : f ∈ D.T') : (fun y' => algebraMap O O' (f (σ y'))) ∈ D'.T' := by
  dsimp only [RingDef] at hD hD'
  obtain ⟨-, -, hT, -⟩ := hD
  obtain ⟨-, -, hT', -⟩ := hD'
  rw [hT] at hf
  rw [hT']
  induction hf using Algebra.adjoin_induction with
  | mem x hx =>
    apply Algebra.subset_adjoin
    rcases hx with ⟨g, hg, rfl⟩ | ⟨i, hi, rfl⟩
    · refine Or.inl ⟨algebraMap O O' ∘ g, Algebra.subset_adjoin ⟨g, hg, rfl⟩, ?_⟩
      funext y'
      simp [hσ1 y']
    · exact Or.inr ⟨i, hi, funext fun y' => hσ2 y' i hi⟩
  | algebraMap c =>
    convert Subalgebra.algebraMap_mem (Algebra.adjoin O' _) (algebraMap O O' c) using 1
    funext y'
    simp
  | add x y _ _ ihx ihy =>
    convert Subalgebra.add_mem _ ihx ihy using 1
    funext y'
    simp
  | mul x y _ _ ihx ihy =>
    convert Subalgebra.mul_mem _ ihx ihy using 1
    funext y'
    simp

/- English proof (translation)
Establish `hmem : ∀ f ∈ D.T', (fun y' => algebraMap O O' (f (σ y'))) ∈ D'.T'` using `fun f hf => bcT'_mem hD hD' σ hσ1 hσ2 hf`. Simplify using `only [RingDef] at hD hD'`. Take `⟨-, -, -, -, -, -, hr, hR, -⟩` from `hD`. Take `⟨-, -, -, -, -, -, hr', hR', -⟩` from `hD'`. Establish `ha2` using `(hR a).1 ha`.

Use `(hR' _).2 ?_` and prove the remaining obligations. Simplify using `only [tSpan, Set.mem_setOf_eq] at ha2 ⊢`. Take `⟨s0, c, hc, rfl⟩` from `ha2`. Use `⟨s0, fun g y' => algebraMap O O' (c g (σ y')), fun g => hmem _ (hc g), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `y'`.

Use extensionality with `i j`. Simplify using `[Finset.sum_apply, Matrix.sum_apply, map_sum, hr, hr', hσ1, hκ, bcR, bcM]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul, hκ, hκ, ← IsScalarTower.algebraMap_apply O O' (FractionRing O')]`.
-/
theorem bcR'_mem (hD : RingDef O T r π χ₁ ε g₀ eB e₁ s D)
    (hD' : RingDef O' (bcT O' T) (bcR O' r) π (bcChar O' χ₁) (bcChar O' ε) g₀ (bcM O' eB) (bcM O' e₁)
      (bcM O' s) D') (σ : D'.X' → D.X') (hσ1 : ∀ y', D.p (σ y') = D'.p y')
    (hσ2 : ∀ y' i, i < t →
      algebraMap O O' ((D.rr i : D.X' → O) (σ y')) = (D'.rr i : D'.X' → O') y')
    (κ : FractionRing O →+* FractionRing O')
    (hκ : ∀ y, κ (algebraMap O (FractionRing O) y) = algebraMap O' (FractionRing O') (algebraMap O O' y))
    {a : D.X' → Matrix d d (FractionRing O)} (ha : a ∈ D.R') :
    (fun y' => (a (σ y')).map κ) ∈ D'.R' := by
  have hmem : ∀ f ∈ D.T', (fun y' => algebraMap O O' (f (σ y'))) ∈ D'.T' :=
    fun f hf => bcT'_mem hD hD' σ hσ1 hσ2 hf
  dsimp only [RingDef] at hD hD'
  obtain ⟨-, -, -, -, -, -, hr, hR, -⟩ := hD
  obtain ⟨-, -, -, -, -, -, hr', hR', -⟩ := hD'
  have ha2 := (hR a).1 ha
  refine (hR' _).2 ?_
  simp only [tSpan, Set.mem_setOf_eq] at ha2 ⊢
  obtain ⟨s0, c, hc, rfl⟩ := ha2
  refine ⟨s0, fun g y' => algebraMap O O' (c g (σ y')),
    fun g => hmem _ (hc g), ?_⟩
  funext y'
  ext i j
  simp [Finset.sum_apply, Matrix.sum_apply, map_sum, hr, hr', hσ1, hκ, bcR, bcM]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, hκ, hκ, ← IsScalarTower.algebraMap_apply O O' (FractionRing O')]

end

end Formalism.RepresentationBoundsCohomology.ringDataObjects
