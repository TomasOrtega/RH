import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SplitPlaceTypes
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLetterOfLocalEmbedding
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

namespace GlobalTheory.SplitRowProbe

section Host
variable {R : Ranks} (H : Host R)

/- English proof (translation)
The claim follows from `H.toHostAx.conjE_apply φ x`.
-/
theorem conj_sqrt (φ : H.E →+* ℂ) (x : H.E) : φ (H.conj x) = starRingEnd ℂ (φ x) :=
  H.toHostAx.conjE_apply φ x

/- English proof (translation)
Establish `h : (H.sqd) ^ 2 = -(H.d : H.E)` using `H.sqd_sq`. Rewrite using `[← map_pow, h]`. Simplify using the standard rewrite rules.
-/
theorem sqrt_sq (φ : H.E →+* ℂ) : φ (H.sqd) ^ 2 = -(H.d : ℂ) := by
  have h : (H.sqd) ^ 2 = -(H.d : H.E) := H.sqd_sq
  rw [← map_pow, h]; simp

/- English proof (translation)
Express the relevant statement in the definitionally equal form `φ (H.conj (H.sqd)) = _ ↔ _`. Rewrite using `[conj_sqrt]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `congrArg (starRingEnd ℂ) h` as an intermediate fact.

Simplify using `using this`. Introduce `h`. Rewrite using `[h]`. Simplify using the standard rewrite rules.
-/
theorem mem_halfType_false (φ : H.E →+* ℂ) :
    φ ∈ halfType H false ↔ φ (H.sqd) = -(Complex.I * (Real.sqrt H.d : ℂ)) := by
  change φ (H.conj (H.sqd)) = _ ↔ _
  rw [conj_sqrt]
  constructor
  · intro h
    have := congrArg (starRingEnd ℂ) h
    simpa using this
  · intro h
    rw [h]; simp

/- English proof (translation)
Rewrite using `[mem_halfType_false]`. Express the relevant statement in the definitionally equal form `Xor' (φ (H.sqd) = Complex.I * (Real.sqrt H.d : ℂ)) _`. Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.hyp.2.1.pos`. Establish `hs : (Complex.I * (Real.sqrt H.d : ℂ)) ^ 2 = -(H.d : ℂ)`. Rewrite using `[mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt hd.le]`.

Simplify using the standard rewrite rules. Establish `hne : Complex.I * (Real.sqrt H.d : ℂ) ≠ 0` using `mul_ne_zero Complex.I_ne_zero (by exact_mod_cast (Real.sqrt_pos.2 hd).ne')`. Establish `hne' : Complex.I * (Real.sqrt H.d : ℂ) ≠ -(Complex.I * (Real.sqrt H.d : ℂ))` using `fun e => hne (by linear_combination e / 2)`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 ((sqrt_sq H φ).trans hs.symm) with h | h` into its components or cases. Conclude with `Or.inl ⟨h, fun h' => hne' (h.symm.trans h')⟩`.

Conclude with `Or.inr ⟨h, fun h' => hne' (h'.symm.trans h)⟩`.
-/
theorem halfType_xor (φ : H.E →+* ℂ) : Xor' (φ ∈ halfType H true) (φ ∈ halfType H false) := by
  rw [mem_halfType_false]
  change Xor' (φ (H.sqd) = Complex.I * (Real.sqrt H.d : ℂ)) _
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
  have hs : (Complex.I * (Real.sqrt H.d : ℂ)) ^ 2 = -(H.d : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt hd.le]; simp
  have hne : Complex.I * (Real.sqrt H.d : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (by exact_mod_cast (Real.sqrt_pos.2 hd).ne')
  have hne' : Complex.I * (Real.sqrt H.d : ℂ) ≠ -(Complex.I * (Real.sqrt H.d : ℂ)) := fun e =>
    hne (by linear_combination e / 2)
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 ((sqrt_sq H φ).trans hs.symm) with h | h
  · exact Or.inl ⟨h, fun h' => hne' (h.symm.trans h')⟩
  · exact Or.inr ⟨h, fun h' => hne' (h'.symm.trans h)⟩

end Host

section Loc
variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
  (hw : w ∈ placesOver D.host.E (D.nd.l i))

/- English proof (translation)
Assemble the required witnesses or components as `⟨((D.nbr i w hw).Kw.1.val).codRestrict (D.nbr i w hw).LL.1.toSubalgebra ((D.nbr i w hw).LL_split _)⟩`.
-/
theorem nonempty_emb : Nonempty (Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) :=
  ⟨((D.nbr i w hw).Kw.1.val).codRestrict (D.nbr i w hw).LL.1.toSubalgebra
    ((D.nbr i w hw).LL_split _)⟩

/- English proof (translation)
Take `⟨g, key, -⟩` from `GlobalTheory.HTW.exists_letter_of_local_embedding D i w hw τ`. Establish `hemb : ∀ x, D.what₂.embLL (D.embE (D.host.sigmaOf g x)) = D.host.emb g x` using `fun x => DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf g x)`. Establish `main : ∀ s, EmbIn (N` using `D.nd) D.nbr i s w hw τ ↔ D.host.emb g ∈ halfType D.host s := by`. Introduce `s`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨-, φ, hφ, h⟩`. Establish `: D.host.emb g = φ` using `RingHom.ext fun x => by`. Rewrite using `[← hemb x]`. Conclude with `h x _ (key x).symm`. Conclude with `this ▸ hφ`.

Introduce `hg`. Use `⟨fun x => ⟨_, (key x).symm⟩, D.host.emb g, hg, fun x y hy => ?_⟩` and prove the remaining obligations. Establish `hy' : y = D.embE (D.host.sigmaOf g x)` using `(D.nd.embK i).injective ((Br.toLLK (D.nbr i w hw)).injective (hy.trans (key x)))`. Rewrite using `[hy', hemb]`. Rewrite using `[main, main]`.

Conclude with `halfType_xor D.host _`.
-/
theorem embIn_xor (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) :
    Xor' (EmbIn (N := D.nd) D.nbr i true w hw τ) (EmbIn (N := D.nd) D.nbr i false w hw τ) := by
  obtain ⟨g, key, -⟩ := GlobalTheory.HTW.exists_letter_of_local_embedding D i w hw τ
  have hemb : ∀ x, D.what₂.embLL (D.embE (D.host.sigmaOf g x)) = D.host.emb g x := fun x =>
    DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf g x)
  have main : ∀ s, EmbIn (N := D.nd) D.nbr i s w hw τ ↔ D.host.emb g ∈ halfType D.host s := by
    intro s
    constructor
    · rintro ⟨-, φ, hφ, h⟩
      have : D.host.emb g = φ := RingHom.ext fun x => by
        rw [← hemb x]
        exact h x _ (key x).symm
      exact this ▸ hφ
    · intro hg
      refine ⟨fun x => ⟨_, (key x).symm⟩, D.host.emb g, hg, fun x y hy => ?_⟩
      have hy' : y = D.embE (D.host.sigmaOf g x) :=
        (D.nd.embK i).injective ((Br.toLLK (D.nbr i w hw)).injective (hy.trans (key x)))
      rw [hy', hemb]
  rw [main, main]
  exact halfType_xor D.host _

/- English proof (translation)
Introduce and unpack `⟨⟨⟨τ⟩, h1⟩, -, h2⟩`. Break down `embIn_xor D i w hw τ with h | h` into its components or cases. Conclude with `h.2 (h2 τ)`. Conclude with `h.2 (h1 τ)`.
-/
theorem not_both_columns : ¬ (PlIn (N := D.nd) D.nbr i true w hw ∧ PlIn (N := D.nd) D.nbr i false w hw) := by
  rintro ⟨⟨⟨τ⟩, h1⟩, -, h2⟩
  rcases embIn_xor D i w hw τ with h | h
  · exact h.2 (h2 τ)
  · exact h.2 (h1 τ)

/- English proof (translation)
Rewrite using `[← D.nd.plOm.2 w x]`. Use `set y := algebraMap D.host.E D.nd.Om (x : D.host.E)`. Distinguish the cases in `hy : y = 0`. Simplify using `[hy]`. Establish `hj : 0 < ‖(D.nbr i w hw).j y‖` using `norm_pos_iff.2 ((map_ne_zero _).2 hy)`.

Establish `h` using `D.nbr_ind i w hw y⁻¹`. Rewrite `h` using `[← ValuationSubring.valuation_le_one_iff, map_inv₀, map_inv₀, norm_inv, inv_le_one₀ hj, inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 hy))]`. Rewrite using `[← not_le, ← not_le, h]`.
-/
theorem bridge_place (x : 𝓞 D.host.E) :
    x ∈ w.asIdeal ↔ ‖(D.nbr i w hw).j (algebraMap D.host.E D.nd.Om (x : D.host.E))‖ < 1 := by
  rw [← D.nd.plOm.2 w x]
  set y := algebraMap D.host.E D.nd.Om (x : D.host.E)
  by_cases hy : y = 0
  · simp [hy]
  have hj : 0 < ‖(D.nbr i w hw).j y‖ := norm_pos_iff.2 ((map_ne_zero _).2 hy)
  have h := D.nbr_ind i w hw y⁻¹
  rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, map_inv₀, norm_inv, inv_le_one₀ hj,
    inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 hy))] at h
  rw [← not_le, ← not_le, h]

end Loc

end GlobalTheory.SplitRowProbe
