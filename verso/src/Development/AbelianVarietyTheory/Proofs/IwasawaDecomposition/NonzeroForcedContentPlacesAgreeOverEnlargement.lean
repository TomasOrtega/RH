import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPlacesEqUnionThreeParts
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Top.Bl

/- English proof (translation)
Establish `hm : ((Examples₂.PlacesToy.resCharW w : ℕ) : 𝓞 K) ∈ (Formalism.DivisionValues.conjPl w).asIdeal`. Use `Ideal.mem_map_of_mem (Formalism.DivisionValues.cO K) (Examples₂.PlacesToy.resCharW_mem w)` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Conclude with `Examples₂.PlacesToy.prime_mem_unique _ (Examples₂.PlacesToy.resCharW_prime _) (Examples₂.PlacesToy.resCharW_prime _) (Examples₂.PlacesToy.resCharW_mem _) hm`.
-/
theorem resCharW_conjPl {K : Type} [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)) :
    Examples₂.PlacesToy.resCharW (Formalism.DivisionValues.conjPl w) = Examples₂.PlacesToy.resCharW w := by
  have hm : ((Examples₂.PlacesToy.resCharW w : ℕ) : 𝓞 K) ∈ (Formalism.DivisionValues.conjPl w).asIdeal := by
    have := Ideal.mem_map_of_mem (Formalism.DivisionValues.cO K) (Examples₂.PlacesToy.resCharW_mem w)
    rwa [map_natCast] at this
  exact Examples₂.PlacesToy.prime_mem_unique _ (Examples₂.PlacesToy.resCharW_prime _) (Examples₂.PlacesToy.resCharW_prime _)
    (Examples₂.PlacesToy.resCharW_mem _) hm

/- English proof (translation)
Unfold `FTypeG fockDeg`. Use `congr 2`. Use `push_cast`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Take `⟨hb, hs⟩` from `hk j h1 h2 τ`.

Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← hb i]`. Use `norm_cast`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[show ((DV.aMinusQ D j τ c : ℚ) : ℝ) = -((D.what₂.kaSmall j τ c : ℚ) : ℝ) by rw [hs c]; push_cast; ring, abs_neg]`. Use `norm_cast`.
-/
theorem FTypeG_of_kapDef {D : D7} (hk : DV.KapDef D) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    FTypeG D j = -(∑ τ : D.what₂.Tau, ((∑ i : Fin (D.R.sigW j).1, |((DV.aPlusQ D j τ i : ℚ) : ℝ)|) +
      ∑ c : Fin (D.R.sigW j).2, |((DV.aMinusQ D j τ c : ℚ) : ℝ)|)) / 2 := by
  unfold FTypeG fockDeg
  congr 2
  push_cast
  refine Finset.sum_congr rfl fun τ _ => ?_
  obtain ⟨hb, hs⟩ := hk j h1 h2 τ
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hb i]
    norm_cast
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [show ((DV.aMinusQ D j τ c : ℚ) : ℝ) = -((D.what₂.kaSmall j τ c : ℚ) : ℝ) by rw [hs c]; push_cast; ring, abs_neg]
    norm_cast

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨j, y, hy, h⟩`. Use `⟨j.1, j.2, ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy`. Break down `hy with rfl | rfl` into its components or cases.

Conclude with `h`. Establish `e : F0K s (w.D Z) (Formalism.DivisionValues.conjPl v) j = FK s (w.D Z) (j.1 + 1) (Examples₂.PlacesToy.resCharW v)` using `by show FK s (w.D Z) (j.1 + 1) (Examples₂.PlacesToy.resCharW (Formalism.DivisionValues.conjPl v)) = _`. Rewrite using `[resCharW_conjPl]`. Conclude with `e ▸ h`. Introduce and unpack `⟨j, hj, h⟩`.

Conclude with `⟨⟨j, hj⟩, v, Or.inl rfl, h⟩`.
-/
theorem mem_W1F_forced_iff (s : Scale) {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt)
    (v : HeightOneSpectrum (𝓞 B.LL)) :
    v ∈ R3.placesWithNonzeroContentOrConj (w.D Z) (F0K s (w.D Z)) ↔
      ∃ j : ℕ, j < B.R.m ∧ FK s (w.D Z) (j + 1) (Examples₂.PlacesToy.resCharW v) ≠ 0 := by
  constructor
  · rintro ⟨j, y, hy, h⟩
    refine ⟨j.1, j.2, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact h
    · have e : F0K s (w.D Z) (Formalism.DivisionValues.conjPl v) j = FK s (w.D Z) (j.1 + 1) (Examples₂.PlacesToy.resCharW v) := by
        show FK s (w.D Z) (j.1 + 1) (Examples₂.PlacesToy.resCharW (Formalism.DivisionValues.conjPl v)) = _
        rw [resCharW_conjPl]
      exact e ▸ h
  · rintro ⟨j, hj, h⟩
    exact ⟨⟨j, hj⟩, v, Or.inl rfl, h⟩

/- English proof (translation)
Establish `h2' : j ≤ B'.R.m` using `by rw [h]; exact h2`. Unfold `FK`. Rewrite using `[FTypeG_of_kapDef hk h1 h2, FTypeG_of_kapDef hk' h1 h2']`. Use `clear hk hk'`. Consider the cases of `B'`.

Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem FK_enl (s : Scale) {B B' : Base} {f : Fr B.toPre} {T : TwDat B} {f' : Fr B'.toPre} {T' : TwDat B'}
    (w : ColW B f T) (w' : ColW B' f' T') (Z : w.Lt) (Z' : w'.Lt) (h : B'.toPre = B.toPre)
    (hk : DV.KapDef (w.D Z)) (hk' : DV.KapDef (w'.D Z')) (j p : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ B.R.m) :
    FK s (w.D Z) j p = FK s (w'.D Z') j p := by
  have h2' : j ≤ B'.R.m := by rw [h]; exact h2
  unfold FK
  rw [FTypeG_of_kapDef hk h1 h2, FTypeG_of_kapDef hk' h1 h2']
  clear hk hk'
  cases B'
  subst h
  rfl

/- English proof (translation)
Establish `he : (w.D Z).what₂.embLL (((Examples₂.PlacesToy.resCharW v : ℕ) : 𝓞 (w.D Z).what₂.LL) : (w.D Z).what₂.LL) = (w'.D Z').what₂.embLL (((Examples₂.PlacesToy.resCharW v : ℕ) : 𝓞 (w'.D Z').what₂.LL) : (w'.D Z').what₂.LL)`. Simplify using `only [map_natCast]`. Establish `hm` using `(hB _ _ he).1 (Examples₂.PlacesToy.resCharW_mem v)`. Conclude with `Examples₂.PlacesToy.prime_mem_unique _ (Examples₂.PlacesToy.resCharW_prime _) (Examples₂.PlacesToy.resCharW_prime _) (Examples₂.PlacesToy.resCharW_mem _) hm`.
-/
theorem resCharW_of_below {B B' : Base} {f : Fr B.toPre} {T : TwDat B} {f' : Fr B'.toPre} {T' : TwDat B'}
    (w : ColW B f T) (w' : ColW B' f' T') (Z : w.Lt) (Z' : w'.Lt) (v : HeightOneSpectrum (𝓞 B.LL))
    (v' : HeightOneSpectrum (𝓞 B'.LL)) (hB : Below (w.D Z) (w'.D Z') v v') :
    Examples₂.PlacesToy.resCharW v' = Examples₂.PlacesToy.resCharW v := by
  have he : (w.D Z).what₂.embLL (((Examples₂.PlacesToy.resCharW v : ℕ) : 𝓞 (w.D Z).what₂.LL) : (w.D Z).what₂.LL) =
      (w'.D Z').what₂.embLL (((Examples₂.PlacesToy.resCharW v : ℕ) : 𝓞 (w'.D Z').what₂.LL) : (w'.D Z').what₂.LL) := by
    simp only [map_natCast]
  have hm := (hB _ _ he).1 (Examples₂.PlacesToy.resCharW_mem v)
  exact Examples₂.PlacesToy.prime_mem_unique _ (Examples₂.PlacesToy.resCharW_prime _) (Examples₂.PlacesToy.resCharW_prime _)
    (Examples₂.PlacesToy.resCharW_mem _) hm

/- English proof (translation)
Introduce `K B f T w B' f' T' w' hE Z Z' hk hk' v v' hB`. Establish `hres` using `resCharW_of_below w w' Z Z' v v' hB`. Establish `hm : B'.R.m = B.R.m` using `by rw [hE.1]`. Use `(mem_W1F_forced_iff K.s w Z v).trans (Iff.trans ?_ (mem_W1F_forced_iff K.s w' Z' v').symm)` and prove the remaining obligations. Rewrite using `[hm, hres]`.

Use `exists_congr fun j => and_congr_right fun hj => ?_` and prove the remaining obligations. Rewrite using `[FK_enl K.s w w' Z Z' hE.1 hk hk' (j + 1) _ (Nat.succ_pos j) hj]`.
-/
theorem nonzeroForcedContentPlaces_agree_over_enlargement : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (B' : Base) (f' : Fr B'.toPre) (T' : TwDat B')
    (w' : ColW B' f' T'), Enl B B' → ∀ (Z : w.Lt) (Z' : w'.Lt), DV.KapDef (w.D Z) → DV.KapDef (w'.D Z') →
    ∀ v v', Below (w.D Z) (w'.D Z') v v' →
      (v ∈ R3.placesWithNonzeroContentOrConj (w.D Z) (F0K K.s (w.D Z)) ↔ v' ∈ R3.placesWithNonzeroContentOrConj (w'.D Z') (F0K K.s (w'.D Z'))) := by
  intro K B f T w B' f' T' w' hE Z Z' hk hk' v v' hB
  have hres := resCharW_of_below w w' Z Z' v v' hB
  have hm : B'.R.m = B.R.m := by rw [hE.1]
  refine (mem_W1F_forced_iff K.s w Z v).trans (Iff.trans ?_ (mem_W1F_forced_iff K.s w' Z' v').symm)
  rw [hm, hres]
  refine exists_congr fun j => and_congr_right fun hj => ?_
  rw [FK_enl K.s w w' Z Z' hE.1 hk hk' (j + 1) _ (Nat.succ_pos j) hj]

end GlobalTheory.Mem.Top.Bl
