import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfQuad
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.ThetaG

open IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

/- English proof (translation)
Set `φ : (Fin n → (A.loc p).Ep) →ₗ[(A.L p).O] (Fin n → (A.loc p).Ep)` to `(LinearMap.lsmul (A.loc p).Ep (Fin n → (A.loc p).Ep) ((A.loc p).ιE (a : E))).restrictScalars (A.L p).O`. Establish `hφ : ∀ v, φ v = (A.loc p).ιE (a : E) • v` using `fun v => rfl`. Establish `hbc : ∀ v : Fin n → E, A.bc p (a • v) = φ (A.bc p v)`. Introduce `v`. Use function extensionality and compare the values at `i`.

Use `show (A.loc p).ιE ((a : E) * v i) = (A.loc p).ιE (a : E) * (A.loc p).ιE (v i)`. Conclude with `map_mul _ _ _`. Establish `hset : A.bc p '' ((Ideal.span {a} • Λ : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) = φ '' (A.bc p '' (Λ : Set (Fin n → E)))`. Rewrite using `[Submodule.ideal_span_singleton_smul, Submodule.coe_pointwise_smul, ← Set.image_smul, Set.image_image, Set.image_image]`. Conclude with `Set.image_congr fun v _ => hbc v`.

Establish `heq : A.lat p (Ideal.span {a} • Λ) = (A.lat p Λ).map φ`. Unfold `Places.lat`. Rewrite using `[hset, Submodule.map_span]`. Rewrite using `[heq, Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨z, hz, rfl⟩`. Conclude with `⟨z, hz, rfl⟩`. Introduce and unpack `⟨z, hz, rfl⟩`. Conclude with `⟨z, hz, rfl⟩`.
-/
theorem mem_lat_span_smul_iff (A : Places F E sig) {n : ℕ} (p : HeightOneSpectrum (𝓞 F))
    (Λ : Submodule (𝓞 E) (Fin n → E)) (a : 𝓞 E) (x : Fin n → (A.loc p).Ep) :
    x ∈ A.lat p (Ideal.span {a} • Λ) ↔ ∃ z ∈ A.lat p Λ, x = (A.loc p).ιE (a : E) • z := by
  let φ : (Fin n → (A.loc p).Ep) →ₗ[(A.L p).O] (Fin n → (A.loc p).Ep) :=
    (LinearMap.lsmul (A.loc p).Ep (Fin n → (A.loc p).Ep) ((A.loc p).ιE (a : E))).restrictScalars (A.L p).O
  have hφ : ∀ v, φ v = (A.loc p).ιE (a : E) • v := fun v => rfl
  have hbc : ∀ v : Fin n → E, A.bc p (a • v) = φ (A.bc p v) := by
    intro v
    funext i
    show (A.loc p).ιE ((a : E) * v i) = (A.loc p).ιE (a : E) * (A.loc p).ιE (v i)
    exact map_mul _ _ _
  have hset : A.bc p '' ((Ideal.span {a} • Λ : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) =
      φ '' (A.bc p '' (Λ : Set (Fin n → E))) := by
    rw [Submodule.ideal_span_singleton_smul, Submodule.coe_pointwise_smul, ← Set.image_smul,
      Set.image_image, Set.image_image]
    exact Set.image_congr fun v _ => hbc v
  have heq : A.lat p (Ideal.span {a} • Λ) = (A.lat p Λ).map φ := by
    unfold Places.lat
    rw [hset, Submodule.map_span]
  rw [heq, Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Use `⟨(⟨w, hw⟩ : O) • y, N.smul_mem _ hy, ?_⟩` and prove the remaining obligations. Rewrite using `[Subring.smul_def, smul_smul, hs, mul_assoc, mul_comm b w, hwb, mul_one]`. Introduce and unpack `⟨z, hz, rfl⟩`.

Use `⟨(⟨b, hb⟩ : O) • z, N.smul_mem _ hz, ?_⟩` and prove the remaining obligations. Rewrite using `[Subring.smul_def, smul_smul, hs]`.
-/
theorem smul_mem_iff_of_unit {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (O : Subring R)
    (N : Submodule O M) (θ s w b : R) (hw : w ∈ O) (hb : b ∈ O) (hs : s = θ * b) (hwb : w * b = 1) (x : M) :
    (∃ y ∈ N, x = θ • y) ↔ ∃ z ∈ N, x = s • z := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(⟨w, hw⟩ : O) • y, N.smul_mem _ hy, ?_⟩
    rw [Subring.smul_def, smul_smul, hs, mul_assoc, mul_comm b w, hwb, mul_one]
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(⟨b, hb⟩ : O) • z, N.smul_mem _ hz, ?_⟩
    rw [Subring.smul_def, smul_smul, hs]

/- English proof (translation)
Unfold `Formalism.MainNotions.S.Loc.resChar`. Use `haveI := p.isPrime`. Establish `h0 : ((q : ℕ) : 𝓞 F ⧸ p.asIdeal) = 0`. Rewrite using `[← map_natCast (Ideal.Quotient.mk p.asIdeal)]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 h`.

Break down `hq.eq_one_or_self_of_dvd _ (ringChar.dvd h0) with h1 | h1` into its components or cases. Conclude with `absurd h1 CharP.ringChar_ne_one`. Conclude with `h1`.
-/
theorem resChar_eq_of_mem (p : HeightOneSpectrum (𝓞 F)) {q : ℕ} (hq : q.Prime)
    (h : ((q : ℕ) : 𝓞 F) ∈ p.asIdeal) : Formalism.MainNotions.S.Loc.resChar p = q := by
  unfold Formalism.MainNotions.S.Loc.resChar
  haveI := p.isPrime
  have h0 : ((q : ℕ) : 𝓞 F ⧸ p.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk p.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 h
  rcases hq.eq_one_or_self_of_dvd _ (ringChar.dvd h0) with h1 | h1
  · exact absurd h1 CharP.ringChar_ne_one
  · exact h1

end GlobalTheory.HL.ThetaG

namespace GlobalTheory.HL.ThetaG

open IsDedekindDomain ValuativeRel

/- English proof (translation)
Introduce `D X Y T T' F00 F'0 FP G c P hP Λ x`. Use `haveI := P.isPrime`. Establish `hmem : ∀ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → Formalism.MainNotions.S.Loc.resChar (below D P) = D.host.g i`. Introduce `i hi`. Apply `resChar_eq_of_mem (below D P) (D.host.g_prime i)` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `_ ∈ Ideal.comap _ P.asIdeal`. Rewrite using `[Ideal.mem_comap, map_natCast]`. Conclude with `hi`. Establish `hg : ((gS D : ℕ) : 𝓞 D.host.E) = ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E)`. Unfold `gS`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Choose the witnesses or unpack the hypotheses as in `⟨i, j, hij, hi, hgij⟩ : ∃ i j : Fin 2, D.host.g i ≠ D.host.g j ∧ ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal ∧ ((gS D : ℕ) : 𝓞 D.host.E) = ((D.host.g i : ℕ) : 𝓞 D.host.E) * ((D.host.g j : ℕ) : 𝓞 D.host.E) := by`. Rewrite `hP` using `[hg]`. Break down `P.isPrime.mem_or_mem hP with h | h` into its components or cases.

Conclude with `⟨0, 1, D.host.g_ne, h, hg⟩`. Conclude with `⟨1, 0, D.host.g_ne.symm, h, by rw [hg, mul_comm]⟩`. Establish `hres` using `hmem i hi`. Establish `hj : ((D.host.g j : ℕ) : 𝓞 D.host.F) ∉ (below D P).asIdeal`. Introduce `hj'`.

Conclude with `hij (hres.symm.trans (resChar_eq_of_mem (below D P) (D.host.g_prime j) hj'))`. Apply the tactic sequence `have hsome : ((D.s.atP (below D P)).split).isSome = true := (D.s_split (below D P)).2 (by rw [hres]; fin_cases i <;> simp)`. Take `⟨sg, hsg⟩` from `Option.isSome_iff_exists.1 hsome`. Establish `hA` using `(Y.agree (below D P)).2.2.2.2.2`. Rewrite `hA` using `[hsg]`.

Choose the witnesses or unpack the hypotheses as in `⟨g', hM, hq⟩ : ∃ g', (Y.M (below D P)).split = some g' ∧ g'.q = sg.q := by`. Consider the cases of `hM : (Y.M (below D P)).split with`. Consider the case `none => rw [hM] at hA`. Conclude with `hA.elim`. Consider the case `some g' => rw [hM] at hA`.

Conclude with `⟨g', rfl, hA.2⟩`. Establish `hgg` using `(c.c (below D P)).gg_some g' hM`. Establish `hth : (G.S (below D P)).th = ((D.host.g i : ℕ) : (D.s.atP (below D P)).Fp)`. Unfold `Frames.th`. Rewrite using `[if_pos hgg.1, hgg.2, hq, sg.q_eq, hres]`.

Use `haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).char0`. Establish `hgj0 : ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp) ≠ 0` using `Nat.cast_ne_zero.2 (D.host.g_prime j).ne_zero`. Establish `hval : (below D P).valuation D.host.F ((D.host.g j : ℕ) : D.host.F) = 1`. Rewrite using `[← map_natCast (algebraMap (𝓞 D.host.F) D.host.F)]`. Conclude with `le_antisymm ((below D P).valuation_le_one _) (not_lt.1 fun hlt => hj (((below D P).valuation_lt_one_iff_mem (K := D.host.F) _).1 hlt))`.

Establish `hint : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιF ((D.host.g j : ℕ) : D.host.F)⁻¹ ∈ 𝒪[((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp]` using `(GlobalTheory.HL.PlacesInt.mem_int_iff ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)) _).2 (by rw [map_inv₀, hval, inv_one])`. Establish `hιF : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιF ((D.host.g j : ℕ) : D.host.F)⁻¹ = ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp)⁻¹`. Rewrite using `[map_inv₀, map_natCast]`. Set `w : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep` to `algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp)⁻¹`. Establish `hwO : w ∈ ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).L (below D P)).O`.

Rewrite `hint` using `[hιF]`. Use `(((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).L (below D P)).O_def _).2 ?_` and prove the remaining obligations. Establish `: IsIntegral 𝒪[((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp] (algebraMap 𝒪[((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp] ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep ⟨_, hint⟩)` using `isIntegral_algebraMap`. Conclude with `this`. Establish `hw : w * ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) = 1`.

Simplify using `only [w]`. Rewrite using `[← map_natCast (algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep), ← map_mul, inv_mul_cancel₀ hgj0, map_one]`. Establish `huO : ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) ∈ ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).L (below D P)).O` using `natCast_mem _ _`. Establish `hι : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιE (((((D.host.g i : ℕ) : 𝓞 D.host.E) * ((D.host.g j : ℕ) : 𝓞 D.host.E) : 𝓞 D.host.E)) : D.host.E) = ((D.host.g i : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) * ((D.host.g j : ℕ) : ((pl …`. Use `push_cast`.

Rewrite using `[map_mul, map_natCast, map_natCast]`. Establish `hθE : algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep (G.S (below D P)).th = ((D.host.g i : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep)`. Rewrite using `[hth]`. Conclude with `map_natCast _ _`. Establish `hιS : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιE ((((gS D : ℕ) : 𝓞 D.host.E)) : D.host.E) = ((D.host.g i : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) * ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D …`.

Rewrite using `[hgij]`. Conclude with `hι`. Take `⟨a, ha⟩ : ∃ a : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep, ((D.host.g i : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) = a` from `⟨_, rfl⟩`. Take `⟨b, hb⟩ : ∃ b : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep, ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) = b` from `⟨_, rfl⟩`. Rewrite `hιS` using `[ha, hb]`.

Rewrite `hθE` using `[ha]`. Rewrite `hw`, `huO` using `[hb]`. Use `clear_value w`. Establish `hs : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιE ((((gS D : ℕ) : 𝓞 D.host.E)) : D.host.E) = algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep (G.S (below D P)).th * b`. Rewrite using `[hιS, hθE]`.

Unfold `Frames.InTh`. Rewrite using `[mem_lat_span_smul_iff]`. Conclude with `smul_mem_iff_of_unit _ _ _ _ w b hwO huO hs hw x`.
-/
theorem inTh_lat_iff : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) {T T' : D.host.E} (F00 : LFlag (VS D) D.R.rS T) (F'0 : LFlag (VS D) D.R.rS T') (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS) (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∀ (Λ : G.Lt) (x : (G.S (below D P)).V), (G.S (below D P)).InTh ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat (below D P) Λ) x ↔ x ∈ (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat (below D P) (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
  intro D X Y T T' F00 F'0 FP G c P hP Λ x
  haveI := P.isPrime
  have hmem : ∀ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
      Formalism.MainNotions.S.Loc.resChar (below D P) = D.host.g i := by
    intro i hi
    apply resChar_eq_of_mem (below D P) (D.host.g_prime i)
    change _ ∈ Ideal.comap _ P.asIdeal
    rw [Ideal.mem_comap, map_natCast]
    exact hi
  have hg : ((gS D : ℕ) : 𝓞 D.host.E) =
      ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) := by
    unfold gS
    push_cast
    ring
  obtain ⟨i, j, hij, hi, hgij⟩ : ∃ i j : Fin 2, D.host.g i ≠ D.host.g j ∧
      ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal ∧
      ((gS D : ℕ) : 𝓞 D.host.E) = ((D.host.g i : ℕ) : 𝓞 D.host.E) * ((D.host.g j : ℕ) : 𝓞 D.host.E) := by
    rw [hg] at hP
    rcases P.isPrime.mem_or_mem hP with h | h
    · exact ⟨0, 1, D.host.g_ne, h, hg⟩
    · exact ⟨1, 0, D.host.g_ne.symm, h, by rw [hg, mul_comm]⟩
  have hres := hmem i hi
  have hj : ((D.host.g j : ℕ) : 𝓞 D.host.F) ∉ (below D P).asIdeal := by
    intro hj'
    exact hij (hres.symm.trans (resChar_eq_of_mem (below D P) (D.host.g_prime j) hj'))
  have hsome : ((D.s.atP (below D P)).split).isSome = true :=
    (D.s_split (below D P)).2 (by rw [hres]; fin_cases i <;> simp)
  obtain ⟨sg, hsg⟩ := Option.isSome_iff_exists.1 hsome
  have hA := (Y.agree (below D P)).2.2.2.2.2
  rw [hsg] at hA
  obtain ⟨g', hM, hq⟩ : ∃ g', (Y.M (below D P)).split = some g' ∧ g'.q = sg.q := by
    cases hM : (Y.M (below D P)).split with
    | none => rw [hM] at hA; exact hA.elim
    | some g' => rw [hM] at hA; exact ⟨g', rfl, hA.2⟩
  have hgg := (c.c (below D P)).gg_some g' hM
  have hth : (G.S (below D P)).th = ((D.host.g i : ℕ) : (D.s.atP (below D P)).Fp) := by
    unfold Frames.th
    rw [if_pos hgg.1, hgg.2, hq, sg.q_eq, hres]
  haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).char0
  have hgj0 : ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp) ≠ 0 :=
    Nat.cast_ne_zero.2 (D.host.g_prime j).ne_zero
  have hval : (below D P).valuation D.host.F ((D.host.g j : ℕ) : D.host.F) = 1 := by
    rw [← map_natCast (algebraMap (𝓞 D.host.F) D.host.F)]
    exact le_antisymm ((below D P).valuation_le_one _)
      (not_lt.1 fun hlt => hj (((below D P).valuation_lt_one_iff_mem (K := D.host.F) _).1 hlt))
  have hint : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιF ((D.host.g j : ℕ) : D.host.F)⁻¹ ∈ 𝒪[((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp] :=
    (GlobalTheory.HL.PlacesInt.mem_int_iff ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)) _).2 (by rw [map_inv₀, hval, inv_one])
  have hιF : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιF ((D.host.g j : ℕ) : D.host.F)⁻¹ =
      ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp)⁻¹ := by
    rw [map_inv₀, map_natCast]
  let w : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep :=
    algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp)⁻¹
  have hwO : w ∈ ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).L (below D P)).O := by
    rw [hιF] at hint
    refine (((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).L (below D P)).O_def _).2 ?_
    have : IsIntegral 𝒪[((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp]
        (algebraMap 𝒪[((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp] ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep ⟨_, hint⟩) :=
      isIntegral_algebraMap
    exact this
  have hw : w * ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) = 1 := by
    simp only [w]
    rw [← map_natCast (algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep), ← map_mul,
      inv_mul_cancel₀ hgj0, map_one]
  have huO : ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) ∈
      ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).L (below D P)).O :=
    natCast_mem _ _
  have hι : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιE (((((D.host.g i : ℕ) : 𝓞 D.host.E) * ((D.host.g j : ℕ) : 𝓞 D.host.E) :
      𝓞 D.host.E)) : D.host.E) =
      ((D.host.g i : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) * ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) := by
    push_cast
    rw [map_mul, map_natCast, map_natCast]
  have hθE : algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp
      ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep (G.S (below D P)).th =
      ((D.host.g i : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) := by
    rw [hth]
    exact map_natCast _ _
  have hιS : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιE ((((gS D : ℕ) : 𝓞 D.host.E)) : D.host.E) =
      ((D.host.g i : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) *
        ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) := by
    rw [hgij]
    exact hι
  obtain ⟨a, ha⟩ : ∃ a : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep, ((D.host.g i : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep, ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) = b := ⟨_, rfl⟩
  rw [ha, hb] at hιS
  rw [ha] at hθE
  rw [hb] at hw huO
  clear_value w
  have hs : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιE ((((gS D : ℕ) : 𝓞 D.host.E)) : D.host.E) =
      algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp
        ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep (G.S (below D P)).th * b := by
    rw [hιS, hθE]
  unfold Frames.InTh
  rw [mem_lat_span_smul_iff]
  exact smul_mem_iff_of_unit _ _ _ _ w b hwO huO hs hw x

end GlobalTheory.HL.ThetaG
