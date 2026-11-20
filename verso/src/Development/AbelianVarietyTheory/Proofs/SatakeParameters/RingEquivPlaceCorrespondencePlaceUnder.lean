import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.TendstoUnderCofinite
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousMapGL
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne

noncomputable section

open NumberField IsDedekindDomain Topology Matrix
open GlobalTheory.CuspRep

namespace GlobalTheory.IsoPull

section Coord

variable {E : Type} [Field E]

/- English proof (translation)
Unfold `coord`. Rewrite using `[InfinitePlace.mk_embedding, if_pos rfl]`. Both sides reduce to the same expression.
-/
theorem coord_embedding (w : InfinitePlace E) (x : Cinf E) : coord w.embedding x = x w := by
  unfold coord
  rw [InfinitePlace.mk_embedding, if_pos rfl]
  rfl

/- English proof (translation)
The claim follows from `funext fun w => by rw [← coord_embedding w x, h, coord_embedding]`.
-/
theorem ext_coord {x y : Cinf E} (h : ∀ τ, coord τ x = coord τ y) : x = y :=
  funext fun w => by rw [← coord_embedding w x, h, coord_embedding]

/- English proof (translation)
Unfold `coord`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem coord_star (τ : E →+* ℂ) (x : Cinf E) : coord τ (star x) = star (coord τ x) := by
  unfold coord
  split_ifs <;> simp

/- English proof (translation)
Unfold `coord`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem coord_smul (τ : E →+* ℂ) (t : ℝ) (x : Cinf E) : coord τ (t • x) = t • coord τ x := by
  unfold coord
  split_ifs <;> simp

/- English proof (translation)
Unfold `coord`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem norm_coord (τ : E →+* ℂ) (x : Cinf E) : ‖coord τ x‖ = ‖x (InfinitePlace.mk τ)‖ := by
  unfold coord
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[← norm_eq_zero, norm_coord, norm_eq_zero]`. Unfold `atEmb`. Conclude with `Pi.single_eq_of_ne h _`.
-/
theorem coord_atEmb_of_ne {σ τ : E →+* ℂ} (h : InfinitePlace.mk σ ≠ InfinitePlace.mk τ) (z : ℂ) :
    coord σ (atEmb τ z) = 0 := by
  classical
  rw [← norm_eq_zero, norm_coord, norm_eq_zero]
  unfold atEmb
  exact Pi.single_eq_of_ne h _

variable [NumberField E] [IsTotallyComplex E]

/- English proof (translation)
Establish `hne : ComplexEmbedding.conjugate τ ≠ τ` using `fun h => InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ)) (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 h))`. Unfold `coord`. Rewrite using `[InfinitePlace.mk_conjugate_eq]`. Break down `InfinitePlace.embedding_mk_eq τ with h | h` into its components or cases. Rewrite using `[if_neg (fun h' => hne (h'.symm.trans h)), if_pos h]`.

Both sides reduce to the same expression. Rewrite using `[if_pos h, if_neg (fun h' => hne (h.symm.trans h'))]`. Simplify using the standard rewrite rules.
-/
theorem coord_conj (τ : E →+* ℂ) (x : Cinf E) :
    coord (ComplexEmbedding.conjugate τ) x = starRingEnd ℂ (coord τ x) := by
  have hne : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
    InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 h))
  unfold coord
  rw [InfinitePlace.mk_conjugate_eq]
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · rw [if_neg (fun h' => hne (h'.symm.trans h)), if_pos h]
    rfl
  · rw [if_pos h, if_neg (fun h' => hne (h.symm.trans h'))]
    simp

end Coord

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M]

section Inf

def cInf (e : K ≃+* M) : Cinf K →+* Cinf M :=
  RingHom.pi fun w : InfinitePlace M => coord (w.embedding.comp e.toRingHom)

omit [NumberField K] [NumberField M] in

/- English proof (translation)
The claim follows from `funext fun _ => coord_star _ x`.
-/
theorem cInf_star (e : K ≃+* M) (x : Cinf K) : cInf e (star x) = star (cInf e x) :=
  funext fun _ => coord_star _ x

omit [NumberField K] [NumberField M] in

/- English proof (translation)
The claim follows from `funext fun _ => coord_smul _ t x`.
-/
theorem cInf_smul (e : K ≃+* M) (t : ℝ) (x : Cinf K) : cInf e (t • x) = t • cInf e x :=
  funext fun _ => coord_smul _ t x

omit [NumberField M] in

/- English proof (translation)
The claim follows from `LinearMap.continuous_of_finiteDimensional ({ toFun := cInf e, map_add' := map_add _, map_smul' := cInf_smul e } : Cinf K →ₗ[ℝ] Cinf M)`.
-/
theorem continuous_cInf (e : K ≃+* M) : Continuous (cInf e) :=
  LinearMap.continuous_of_finiteDimensional
    ({ toFun := cInf e, map_add' := map_add _, map_smul' := cInf_smul e } : Cinf K →ₗ[ℝ] Cinf M)

/- English proof (translation)
The claim follows from `(pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun _ => (norm_coord _ x).trans_le (norm_le_pi_norm x _)`.
-/
theorem norm_cInf_le (e : K ≃+* M) (x : Cinf K) : ‖cInf e x‖ ≤ ‖x‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun _ => (norm_coord _ x).trans_le (norm_le_pi_norm x _)

variable [IsTotallyComplex K] [IsTotallyComplex M]

omit [NumberField M] [IsTotallyComplex M] in

/- English proof (translation)
Use `conv_lhs => unfold coord`. Use `split_ifs with h`. Express the relevant statement in the definitionally equal form `coord ((InfinitePlace.mk τ).embedding.comp e.toRingHom) x = _`. Rewrite using `[h]`. Express the relevant statement in the definitionally equal form `starRingEnd ℂ (coord ((InfinitePlace.mk τ).embedding.comp e.toRingHom) x) = _`.

Rewrite using `[(InfinitePlace.embedding_mk_eq τ).resolve_left h]`. Express the relevant statement in the definitionally equal form `starRingEnd ℂ (coord (ComplexEmbedding.conjugate (τ.comp e.toRingHom)) x) = _`. Rewrite using `[coord_conj]`. Simplify using the standard rewrite rules.
-/
theorem coord_cInf (e : K ≃+* M) (τ : M →+* ℂ) (x : Cinf K) :
    coord τ (cInf e x) = coord (τ.comp e.toRingHom) x := by
  conv_lhs => unfold coord
  split_ifs with h
  · change coord ((InfinitePlace.mk τ).embedding.comp e.toRingHom) x = _
    rw [h]
  · change starRingEnd ℂ (coord ((InfinitePlace.mk τ).embedding.comp e.toRingHom) x) = _
    rw [(InfinitePlace.embedding_mk_eq τ).resolve_left h]
    change starRingEnd ℂ (coord (ComplexEmbedding.conjugate (τ.comp e.toRingHom)) x) = _
    rw [coord_conj]
    simp

/- English proof (translation)
The claim follows from `ext_coord fun τ => by rw [coord_cInf, coord_cInf] congr 2 ext y simp`.
-/
theorem cInf_symm (e : K ≃+* M) (x : Cinf K) : cInf e.symm (cInf e x) = x :=
  ext_coord fun τ => by
    rw [coord_cInf, coord_cInf]
    congr 2
    ext y
    simp

/- English proof (translation)
The claim follows from `ext_coord fun σ => by rw [coord_cInf] by_cases h : InfinitePlace.mk σ = InfinitePlace.mk τ · rcases InfinitePlace.mk_eq_iff.1 h.symm with rfl | rfl · rw [coord_atEmb, coord_atEmb] · change coord (ComplexEmbedding.conjugate (τ.comp e.toRingHom)) _ = _ rw [coord_conj, coord_conj, c …`.
-/
theorem cInf_atEmb (e : K ≃+* M) (τ : M →+* ℂ) (z : ℂ) : cInf e (atEmb (τ.comp e.toRingHom) z) = atEmb τ z :=
  ext_coord fun σ => by
    rw [coord_cInf]
    by_cases h : InfinitePlace.mk σ = InfinitePlace.mk τ
    · rcases InfinitePlace.mk_eq_iff.1 h.symm with rfl | rfl
      · rw [coord_atEmb, coord_atEmb]
      · change coord (ComplexEmbedding.conjugate (τ.comp e.toRingHom)) _ = _
        rw [coord_conj, coord_conj, coord_atEmb, coord_atEmb]
    · rw [coord_atEmb_of_ne h, coord_atEmb_of_ne]
      intro h'
      refine h ?_
      have := congrArg (fun w : InfinitePlace K => w.comap e.symm.toRingHom) h'
      simpa [RingHom.comp_assoc] using this

end Inf

section Fin

def Over (e : K ≃+* M) (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 M)) : Prop :=
  ∀ x : 𝓞 K, x ∈ v.asIdeal ↔ RingOfIntegers.mapRingEquiv e x ∈ w.asIdeal

omit [NumberField K] [NumberField M] in

/- English proof (translation)
Introduce `x` and use `by rw [h] exact Iff.of_eq (congrArg (· ∈ w.asIdeal) ((RingOfIntegers.mapRingEquiv e).apply_symm_apply x).symm)`.
-/
theorem Over.symm {e : K ≃+* M} {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)} (h : Over e v w) :
    Over e.symm w v := fun x => by
  rw [h]
  exact Iff.of_eq (congrArg (· ∈ w.asIdeal) ((RingOfIntegers.mapRingEquiv e).apply_symm_apply x).symm)

omit [NumberField K] [NumberField M] in

/- English proof (translation)
The claim follows from `HeightOneSpectrum.ext (Ideal.ext fun x => (h x).trans (h' x).symm)`.
-/
theorem Over.unique {e : K ≃+* M} {v v' : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)} (h : Over e v w)
    (h' : Over e v' w) : v = v' := HeightOneSpectrum.ext (Ideal.ext fun x => (h x).trans (h' x).symm)

def src (e : K ≃+* M) (w : HeightOneSpectrum (𝓞 M)) : HeightOneSpectrum (𝓞 K) :=
  letI := e.toRingHom.toAlgebra
  w.under (𝓞 K)

/- English proof (translation)
Introduce `_` and use `Iff.rfl`.
-/
theorem ringEquivPlaceCorrespondence_placeUnder (e : K ≃+* M) (w : HeightOneSpectrum (𝓞 M)) : Over e (src e w) w := fun _ => Iff.rfl

def cLoc {e : K ≃+* M} {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)} (h : Over e v w) :
    v.adicCompletion K →+* w.adicCompletion M :=
  letI := e.toRingHom.toAlgebra
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨Ideal.ext h⟩
  KStar.Choice.complMap v w

variable {e : K ≃+* M} {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}

/- English proof (translation)
The claim follows from `letI := e.toRingHom.toAlgebra haveI : w.asIdeal.LiesOver v.asIdeal := ⟨Ideal.ext h⟩ KStar.Choice.continuous_complMap v w`.
-/
theorem continuous_cLoc (h : Over e v w) : Continuous (cLoc h) :=
  letI := e.toRingHom.toAlgebra
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨Ideal.ext h⟩
  KStar.Choice.continuous_complMap v w

/- English proof (translation)
The claim follows from `letI := e.toRingHom.toAlgebra haveI : w.asIdeal.LiesOver v.asIdeal := ⟨Ideal.ext h⟩ KStar.Choice.complMap_algebraMap v w x`.
-/
theorem cLoc_algebraMap (h : Over e v w) (x : K) : cLoc h (algebraMap K _ x) = algebraMap M _ (e x) :=
  letI := e.toRingHom.toAlgebra
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨Ideal.ext h⟩
  KStar.Choice.complMap_algebraMap v w x

/- English proof (translation)
Use `(HeightOneSpectrum.denseRange_algebraMap K v).equalizer ((continuous_cLoc h').comp (continuous_cLoc h)) continuous_id (funext fun y => by simp [cLoc_algebraMap])` as an intermediate fact. Conclude with `congrFun this x`.
-/
theorem cLoc_symm (h : Over e v w) (h' : Over e.symm w v) (x : v.adicCompletion K) : cLoc h' (cLoc h x) = x := by
  have := (HeightOneSpectrum.denseRange_algebraMap K v).equalizer ((continuous_cLoc h').comp (continuous_cLoc h))
    continuous_id (funext fun y => by simp [cLoc_algebraMap])
  exact congrFun this x

def locEquiv (h : Over e v w) : v.adicCompletion K ≃+* w.adicCompletion M :=
  { cLoc h with
    invFun := cLoc h.symm
    left_inv := cLoc_symm h h.symm
    right_inv := cLoc_symm h.symm h }

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨n, hn⟩ : ∃ n : ℕ, ∀ x, Valued.v (cLoc h x) = Valued.v x ^ n :=`. Use `letI := e.toRingHom.toAlgebra`. Use `haveI : w.asIdeal.LiesOver v.asIdeal := ⟨Ideal.ext h⟩`. Use the proof step `⟨_, KStar.Choice.valued_complMap K M v w⟩`. Take `⟨ϖ, hϖ⟩` from `GlobalTheory.LFun.exists_isUnifV w`.

Take `⟨y, rfl⟩` from `(locEquiv h).surjective ϖ`. Establish `h1 : Valued.v y ^ n = WithZero.exp (-1 : ℤ)` using `(hn y).symm.trans hϖ`. Establish `h2` using `congrArg WithZero.log h1`. Rewrite `h2` using `[WithZero.log_pow, WithZero.log_exp, nsmul_eq_mul]`. Establish `h3 : (n : ℤ) ∣ 1` using `⟨-WithZero.log (Valued.v y), by linarith⟩`.

Take `rfl : n = 1` from `Nat.dvd_one.1 (by exact_mod_cast h3)`. Rewrite using `[hn, pow_one]`.
-/
theorem valued_cLoc (h : Over e v w) (x : v.adicCompletion K) : Valued.v (cLoc h x) = Valued.v x := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ x, Valued.v (cLoc h x) = Valued.v x ^ n :=
    letI := e.toRingHom.toAlgebra
    haveI : w.asIdeal.LiesOver v.asIdeal := ⟨Ideal.ext h⟩
    ⟨_, KStar.Choice.valued_complMap K M v w⟩
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV w
  obtain ⟨y, rfl⟩ := (locEquiv h).surjective ϖ
  have h1 : Valued.v y ^ n = WithZero.exp (-1 : ℤ) := (hn y).symm.trans hϖ
  have h2 := congrArg WithZero.log h1
  rw [WithZero.log_pow, WithZero.log_exp, nsmul_eq_mul] at h2
  have h3 : (n : ℤ) ∣ 1 := ⟨-WithZero.log (Valued.v y), by linarith⟩
  obtain rfl : n = 1 := Nat.dvd_one.1 (by exact_mod_cast h3)
  rw [hn, pow_one]

/- English proof (translation)
Establish `e1 : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv e : 𝓞 K →+* 𝓞 M)`. Rewrite using `[show v.asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingEquiv e : 𝓞 K →+* 𝓞 M) from Ideal.ext h]`. Conclude with `(Ideal.map_comap_of_surjective _ (RingEquiv.surjective _) _).symm`. Conclude with `(Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv e) e1).toEquiv).symm`.
-/
theorem qV_eq (h : Over e v w) : Formalism.UG.qV M w = Formalism.UG.qV K v := by
  have e1 : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv e : 𝓞 K →+* 𝓞 M) := by
    rw [show v.asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingEquiv e : 𝓞 K →+* 𝓞 M) from Ideal.ext h]
    exact (Ideal.map_comap_of_surjective _ (RingEquiv.surjective _) _).symm
  exact (Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv e) e1).toEquiv).symm

def cFin (e : K ≃+* M) : Af K →+* Af M :=
  letI := e.toRingHom.toAlgebra
  KStar.Choice.finAdeleMap K M

/- English proof (translation)
Take `rfl` from `(ringEquivPlaceCorrespondence_placeUnder e w).unique h`. Both sides reduce to the same expression.
-/
theorem pLoc_cFin (h : Over e v w) (x : Af K) : pLoc M w (cFin e x) = cLoc h (pLoc K v x) := by
  obtain rfl := (ringEquivPlaceCorrespondence_placeUnder e w).unique h
  rfl

/- English proof (translation)
The claim follows from `letI := e.toRingHom.toAlgebra continuous_snd.comp ((KStar.Choice.adeleMap_spec K M).1.comp (continuous_const.prodMk continuous_id : Continuous fun x : Af K => ((0, x) : InfiniteAdeleRing K × Af K)))`.
-/
theorem continuous_cFin (e : K ≃+* M) : Continuous (cFin e) :=
  letI := e.toRingHom.toAlgebra
  continuous_snd.comp ((KStar.Choice.adeleMap_spec K M).1.comp (continuous_const.prodMk continuous_id :
    Continuous fun x : Af K => ((0, x) : InfiniteAdeleRing K × Af K)))

/- English proof (translation)
The claim follows from `FiniteAdeleRing.ext _ fun w => (pLoc_cFin (ringEquivPlaceCorrespondence_placeUnder e w) _).trans (cLoc_algebraMap (ringEquivPlaceCorrespondence_placeUnder e w) x)`.
-/
theorem cFin_algebraMap (e : K ≃+* M) (x : K) : cFin e (algebraMap K _ x) = algebraMap M _ (e x) :=
  FiniteAdeleRing.ext _ fun w => (pLoc_cFin (ringEquivPlaceCorrespondence_placeUnder e w) _).trans (cLoc_algebraMap (ringEquivPlaceCorrespondence_placeUnder e w) x)

/- English proof (translation)
The claim follows from `FiniteAdeleRing.ext _ fun v => by have h := ringEquivPlaceCorrespondence_placeUnder e.symm v exact (pLoc_cFin h _).trans ((congrArg _ (pLoc_cFin (e := e) h.symm x)).trans (cLoc_symm (e := e) h.symm h _))`.
-/
theorem cFin_symm (e : K ≃+* M) (x : Af K) : cFin e.symm (cFin e x) = x :=
  FiniteAdeleRing.ext _ fun v => by
    have h := ringEquivPlaceCorrespondence_placeUnder e.symm v
    exact (pLoc_cFin h _).trans ((congrArg _ (pLoc_cFin (e := e) h.symm x)).trans (cLoc_symm (e := e) h.symm h _))

/- English proof (translation)
Establish `key : ∀ u, GeneralLinearGroup.map (pLoc M u) (GeneralLinearGroup.map (cFin e) (locGL K a v g)) = GeneralLinearGroup.map (pLoc M u) (locGL M a w (GeneralLinearGroup.map (cLoc h) g))` using `fun u => by`. Establish `h1 : ∀ {t} (ht : Over e t u) (k : GL (Fin a) (Af K)), GeneralLinearGroup.map (pLoc M u) (GeneralLinearGroup.map (cFin e) k) = GeneralLinearGroup.map (cLoc ht) (GeneralLinearGroup.map (pLoc K t) k)` using `fun ht k => by`. Use extensionality with `i j : 2`. Conclude with `pLoc_cFin ht _`. Distinguish the cases in `hu : u = w`.

Substitute `hu` using the available equality. Rewrite using `[h1 h, pLoc_locGL, pLoc_locGL]`. Rewrite using `[h1 (ringEquivPlaceCorrespondence_placeUnder e u), pLoc_locGL_of_ne hu, pLoc_locGL_of_ne, map_one]`. Introduce `h2`. Conclude with `hu ((h2 ▸ ringEquivPlaceCorrespondence_placeUnder e u).symm.unique h.symm)`.

Use `Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun u => ?_)` and prove the remaining obligations. Conclude with `congrArg (fun y : GL (Fin a) (u.adicCompletion M) => y.val i j) (key u)`.
-/
theorem cFin_locGL {a : ℕ} (h : Over e v w) (g : GL (Fin a) (v.adicCompletion K)) :
    GeneralLinearGroup.map (cFin e) (locGL K a v g) = locGL M a w (GeneralLinearGroup.map (cLoc h) g) := by
  have key : ∀ u, GeneralLinearGroup.map (pLoc M u) (GeneralLinearGroup.map (cFin e) (locGL K a v g)) =
      GeneralLinearGroup.map (pLoc M u) (locGL M a w (GeneralLinearGroup.map (cLoc h) g)) := fun u => by
    have h1 : ∀ {t} (ht : Over e t u) (k : GL (Fin a) (Af K)),
        GeneralLinearGroup.map (pLoc M u) (GeneralLinearGroup.map (cFin e) k) =
        GeneralLinearGroup.map (cLoc ht) (GeneralLinearGroup.map (pLoc K t) k) := fun ht k => by
      ext i j : 2
      exact pLoc_cFin ht _
    by_cases hu : u = w
    · subst hu
      rw [h1 h, pLoc_locGL, pLoc_locGL]
    · rw [h1 (ringEquivPlaceCorrespondence_placeUnder e u), pLoc_locGL_of_ne hu, pLoc_locGL_of_ne, map_one]
      intro h2
      exact hu ((h2 ▸ ringEquivPlaceCorrespondence_placeUnder e u).symm.unique h.symm)
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun u => ?_)
  exact congrArg (fun y : GL (Fin a) (u.adicCompletion M) => y.val i j) (key u)

end Fin

variable [IsTotallyComplex K] [IsTotallyComplex M]

def cAd (e : K ≃+* M) : Ad K →+* Ad M :=
  RingHom.prod ((infEq M).toRingHom.comp ((cInf e).comp (pInf K))) ((cFin e).comp (pFin K))

/- English proof (translation)
The claim follows from `(infEq M).symm_apply_apply _`.
-/
theorem pInf_cAd (e : K ≃+* M) (x : Ad K) : pInf M (cAd e x) = cInf e (pInf K x) := (infEq M).symm_apply_apply _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pFin_cAd (e : K ≃+* M) (x : Ad K) : pFin M (cAd e x) = cFin e (pFin K x) := rfl

/- English proof (translation)
The claim follows from `ad_ext (by rw [pInf_cAd, pInf_cAd, cInf_symm]) (by rw [pFin_cAd, pFin_cAd, cFin_symm])`.
-/
theorem cAd_symm (e : K ≃+* M) (x : Ad K) : cAd e.symm (cAd e x) = x :=
  ad_ext (by rw [pInf_cAd, pInf_cAd, cInf_symm]) (by rw [pFin_cAd, pFin_cAd, cFin_symm])

/- English proof (translation)
The claim follows from `ad_ext (ext_coord fun τ => by rw [pInf_cAd, coord_cInf, coord_algebraMap, coord_algebraMap]; rfl) (cFin_algebraMap e x)`.
-/
theorem cAd_algebraMap (e : K ≃+* M) (x : K) : cAd e (algebraMap K _ x) = algebraMap M _ (e x) :=
  ad_ext (ext_coord fun τ => by rw [pInf_cAd, coord_cInf, coord_algebraMap, coord_algebraMap]; rfl)
    (cFin_algebraMap e x)

/- English proof (translation)
Establish `h : Continuous (pInf K)` using `continuous_pi fun w => (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp ((continuous_apply w).comp continuous_fst)`. Conclude with `((continuous_infEq M).comp ((continuous_cInf e).comp h)).prodMk ((continuous_cFin e).comp continuous_snd)`.
-/
theorem continuous_cAd (e : K ≃+* M) : Continuous (cAd e) := by
  have h : Continuous (pInf K) := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)
  exact ((continuous_infEq M).comp ((continuous_cInf e).comp h)).prodMk ((continuous_cFin e).comp continuous_snd)

end GlobalTheory.IsoPull

end
