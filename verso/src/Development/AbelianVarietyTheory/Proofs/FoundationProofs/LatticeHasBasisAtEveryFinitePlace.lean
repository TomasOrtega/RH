import Mathlib
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas

open Module NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.LatBasisAt

variable {K : Type} [Field K] [NumberField K]

abbrev locRing (w : HeightOneSpectrum (𝓞 K)) : Subalgebra (𝓞 K) K :=
  haveI := w.isPrime
  Localization.subalgebra.ofField K w.asIdeal.primeCompl w.asIdeal.primeCompl_le_nonZeroDivisors

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
lemma mem_locRing (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ locRing w ↔ ∃ (a s : 𝓞 K) (_ : s ∉ w.asIdeal),
      x = algebraMap (𝓞 K) K a * (algebraMap (𝓞 K) K s)⁻¹ :=
  Iff.rfl

/- English proof (translation)
Introduce `h`. Establish `: s = 0` using `(IsFractionRing.injective (𝓞 K) K) (by simpa using h)`. Conclude with `hs (this ▸ w.asIdeal.zero_mem)`.
-/
lemma algebraMap_ne_zero (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K}
    (hs : s ∉ w.asIdeal) : algebraMap (𝓞 K) K s ≠ 0 := by
  intro h
  have : s = 0 := (IsFractionRing.injective (𝓞 K) K) (by simpa using h)
  exact hs (this ▸ w.asIdeal.zero_mem)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
lemma mem_localization_iff (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (M : Submodule (𝓞 K) (Fin d → K))
    (x : Fin d → K) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M ↔ ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ M :=
  Iff.rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨s, hs, hsx⟩` from `(mem_localization_iff w M x).mp h`. Establish `hs0` using `algebraMap_ne_zero w hs`. Establish `h1 : (1 : 𝓞 K) ∉ w.asIdeal` using `(Ideal.ne_top_iff_one _).mp w.isPrime.ne_top`.

Establish `hu : (algebraMap (𝓞 K) K s)⁻¹ ∈ locRing w` using `(mem_locRing w _).mpr ⟨1, s, hs, by simp⟩`. Establish `hx : x = (⟨_, hu⟩ : locRing w) • (s • x)`. Rewrite using `[Subalgebra.smul_def, ← algebraMap_smul K s x, smul_smul]`. Simplify using `[hs0]`. Rewrite using `[hx]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hsx)`. Introduce `hx`. Establish `h1 : (1 : 𝓞 K) ∉ w.asIdeal` using `(Ideal.ne_top_iff_one _).mp w.isPrime.ne_top`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact (mem_localization_iff w M y).mpr ⟨1, h1, by simpa using hy⟩`.

Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `add y z _ _ hy hz => exact Submodule.add_mem _ hy hz`. Consider the case `smul a y _ hy`. Take `⟨s, hs, hsy⟩` from `(mem_localization_iff w M y).mp hy`. Take `⟨r, t, ht, hat⟩` from `(mem_locRing w a).mp a.2`.

Use `(mem_localization_iff w M _).mpr ⟨t * s, fun h => (w.isPrime.mem_or_mem h).elim ht hs, ?_⟩` and prove the remaining obligations. Establish `ht0` using `algebraMap_ne_zero w ht`. Establish `he : (t * s) • (a • y) = r • (s • y)`. Rewrite using `[Subalgebra.smul_def, hat, ← algebraMap_smul K (t * s), ← algebraMap_smul K r, ← algebraMap_smul K s, smul_smul, smul_smul]`. Use `congr 1`.

Rewrite using `[map_mul]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[he]`. Conclude with `M.smul_mem r hsy`.
-/
lemma mem_localization_iff_mem_span (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (M : Submodule (𝓞 K) (Fin d → K))
    (x : Fin d → K) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M ↔ x ∈ Submodule.span (locRing w) (M : Set (Fin d → K)) := by
  constructor
  · intro h
    obtain ⟨s, hs, hsx⟩ := (mem_localization_iff w M x).mp h
    have hs0 := algebraMap_ne_zero w hs
    have h1 : (1 : 𝓞 K) ∉ w.asIdeal := (Ideal.ne_top_iff_one _).mp w.isPrime.ne_top
    have hu : (algebraMap (𝓞 K) K s)⁻¹ ∈ locRing w := (mem_locRing w _).mpr ⟨1, s, hs, by simp⟩
    have hx : x = (⟨_, hu⟩ : locRing w) • (s • x) := by
      rw [Subalgebra.smul_def, ← algebraMap_smul K s x, smul_smul]
      simp [hs0]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hsx)
  · intro hx
    have h1 : (1 : 𝓞 K) ∉ w.asIdeal := (Ideal.ne_top_iff_one _).mp w.isPrime.ne_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact (mem_localization_iff w M y).mpr ⟨1, h1, by simpa using hy⟩
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul a y _ hy =>
      obtain ⟨s, hs, hsy⟩ := (mem_localization_iff w M y).mp hy
      obtain ⟨r, t, ht, hat⟩ := (mem_locRing w a).mp a.2
      refine (mem_localization_iff w M _).mpr ⟨t * s, fun h => (w.isPrime.mem_or_mem h).elim ht hs, ?_⟩
      have ht0 := algebraMap_ne_zero w ht
      have he : (t * s) • (a • y) = r • (s • y) := by
        rw [Subalgebra.smul_def, hat, ← algebraMap_smul K (t * s), ← algebraMap_smul K r,
          ← algebraMap_smul K s, smul_smul, smul_smul]
        congr 1
        rw [map_mul]
        field_simp
      rw [he]
      exact M.smul_mem r hsy

/- English proof (translation)
Introduce `K _ _ d L hL w`. Use `haveI := w.isPrime`. Establish `: IsDiscreteValuationRing (locRing w)` using `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) w.ne_bot (locRing w)`. Use `set N : Submodule (locRing w) (Fin d → K) := Submodule.span (locRing w) (L : Set (Fin d → K)) with hN`. Establish `: Module.Finite (locRing w) N`.

Take `⟨s, hs⟩` from `hL.fg`. Rewrite using `[Module.Finite.iff_fg]`. Use `⟨s, ?_⟩` and prove the remaining obligations. Rewrite using `[hN, ← hs, Submodule.span_span_of_tower]`. Establish `: Module.IsTorsionFree (locRing w) N` using `inferInstance`.

Set `b` to `Module.Free.chooseBasis (locRing w) N`. Set `v : Module.Free.ChooseBasisIndex (locRing w) N → Fin d → K` to `fun i => (b i : Fin d → K)`. Establish `hliA : LinearIndependent (locRing w) v` using `b.linearIndependent.map' N.subtype N.ker_subtype`. Establish `hli : LinearIndependent K v` using `(LinearIndependent.iff_fractionRing (locRing w) K).mp hliA`. Establish `hspanA : Submodule.span (locRing w) (Set.range v) = N`.

Establish `: Set.range v = N.subtype '' Set.range b`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[this, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]`. Establish `hspan : ⊤ ≤ Submodule.span K (Set.range v)`.

Rewrite using `[← hL.span_eq_top, Submodule.span_le]`. Introduce `x hx`. Establish `hxN : x ∈ Submodule.span (locRing w) (Set.range v)`. Rewrite using `[hspanA]`. Conclude with `Submodule.subset_span hx`.

Conclude with `Submodule.span_le_restrictScalars (locRing w) K _ hxN`. Set `bK : Basis _ K (Fin d → K)` to `Basis.mk hli hspan`. Establish `hcard : Fintype.card (Module.Free.ChooseBasisIndex (locRing w) N) = d`. Rewrite using `[← Module.finrank_eq_card_basis bK, Module.finrank_fin_fun]`. Set `e` to `Fintype.equivFinOfCardEq hcard`.

Establish `hli' : LinearIndependent K (v ∘ e.symm)` using `hli.comp _ e.symm.injective`. Set `P : Matrix (Fin d) (Fin d) K` to `Matrix.of fun a j => (v ∘ e.symm) j a`. Establish `hP : IsUnit P` using `Matrix.linearIndependent_cols_iff_isUnit.mp hli'`. Use `⟨hP.unit, ?_⟩` and prove the remaining obligations. Establish `hcol : Formalism.L2.DIV.colLat hP.unit = Submodule.span (𝓞 K) (Set.range (v ∘ e.symm))` using `rfl`.

Unfold `Formalism.L2.DIV.IsBasisAt`. Use extensionality with `x`. Rewrite using `[hcol, mem_localization_iff_mem_span, mem_localization_iff_mem_span, Submodule.span_span_of_tower, EquivLike.range_comp, hspanA]`.
-/
theorem basisAtEx : Formalism.L2.DIV.BasisAtEx := by
  intro K _ _ d L hL w
  haveI := w.isPrime
  have : IsDiscreteValuationRing (locRing w) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) w.ne_bot (locRing w)
  set N : Submodule (locRing w) (Fin d → K) := Submodule.span (locRing w) (L : Set (Fin d → K))
    with hN
  have : Module.Finite (locRing w) N := by
    obtain ⟨s, hs⟩ := hL.fg
    rw [Module.Finite.iff_fg]
    refine ⟨s, ?_⟩
    rw [hN, ← hs, Submodule.span_span_of_tower]
  have : Module.IsTorsionFree (locRing w) N := inferInstance
  let b := Module.Free.chooseBasis (locRing w) N
  let v : Module.Free.ChooseBasisIndex (locRing w) N → Fin d → K := fun i => (b i : Fin d → K)
  have hliA : LinearIndependent (locRing w) v := b.linearIndependent.map' N.subtype N.ker_subtype
  have hli : LinearIndependent K v := (LinearIndependent.iff_fractionRing (locRing w) K).mp hliA
  have hspanA : Submodule.span (locRing w) (Set.range v) = N := by
    have : Set.range v = N.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspan : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← hL.span_eq_top, Submodule.span_le]
    intro x hx
    have hxN : x ∈ Submodule.span (locRing w) (Set.range v) := by
      rw [hspanA]; exact Submodule.subset_span hx
    exact Submodule.span_le_restrictScalars (locRing w) K _ hxN
  let bK : Basis _ K (Fin d → K) := Basis.mk hli hspan
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex (locRing w) N) = d := by
    rw [← Module.finrank_eq_card_basis bK, Module.finrank_fin_fun]
  let e := Fintype.equivFinOfCardEq hcard
  have hli' : LinearIndependent K (v ∘ e.symm) := hli.comp _ e.symm.injective
  let P : Matrix (Fin d) (Fin d) K := Matrix.of fun a j => (v ∘ e.symm) j a
  have hP : IsUnit P := Matrix.linearIndependent_cols_iff_isUnit.mp hli'
  refine ⟨hP.unit, ?_⟩
  have hcol : Formalism.L2.DIV.colLat hP.unit = Submodule.span (𝓞 K) (Set.range (v ∘ e.symm)) := rfl
  unfold Formalism.L2.DIV.IsBasisAt
  ext x
  rw [hcol, mem_localization_iff_mem_span, mem_localization_iff_mem_span, Submodule.span_span_of_tower,
    EquivLike.range_comp, hspanA]

end GlobalTheory.LatBasisAt
