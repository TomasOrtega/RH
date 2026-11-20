import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

noncomputable section

namespace GlobalTheory.SplitPts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

variable (E) in

abbrev conjE : E ≃+* E := (IsCMField.complexConj E).toRingEquiv

/- English proof (translation)
The claim follows from `(eq_conjSrc fun x => by rw [← conjPl_conjSrc (conjE E) v ((conjE E) x)] exact congrArg _ (IsCMField.complexConj_apply_apply E x)).symm`.
-/
theorem conjSrc_conjSrc_cm (v : HeightOneSpectrum (𝓞 E)) : conjSrc (conjE E) (conjSrc (conjE E) v) = v :=
  (eq_conjSrc fun x => by
    rw [← conjPl_conjSrc (conjE E) v ((conjE E) x)]
    exact congrArg _ (IsCMField.complexConj_apply_apply E x)).symm

/- English proof (translation)
Establish `h` using `conjPl_conjSrc (conjE E) (conjSrc (conjE E) w)`. Rewrite `h` using `[conjSrc_conjSrc_cm]`. Then use the resulting hypothesis.
-/
theorem conjPl_self_conjSrc (w : HeightOneSpectrum (𝓞 E)) : GlobalTheory.Mem.Chr.ConjPl (conjE E) w (conjSrc (conjE E) w) := by
  have h := conjPl_conjSrc (conjE E) (conjSrc (conjE E) w)
  rwa [conjSrc_conjSrc_cm] at h

/- English proof (translation)
Establish `key` using `GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E) (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) w`. Establish `h2 : ∀ u, GlobalTheory.Mem.Chr.ConjPl (conjE E) w u → u = conjSrc (conjE E) w` using `fun u h => by`. Rewrite using `[eq_conjSrc h, conjSrc_conjSrc_cm]`. Take `⟨u, hu, hu'⟩` from `hw`. Use `⟨?_, (key _).2 (Or.inr (conjPl_self_conjSrc w)), fun u' h => ((key u').1 h).imp_right (h2 u')⟩` and prove the remaining obligations.

Break down `(key u).1 hu' with h | h` into its components or cases. Conclude with `absurd h hu`. Rewrite using `[← h2 u h]`. Conclude with `hu`.
-/
theorem over_split {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) :
    conjSrc (conjE E) w ≠ w ∧
      (conjSrc (conjE E) w).under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) ∧
      ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) →
        u = w ∨ u = conjSrc (conjE E) w := by
  have key := GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) w
  have h2 : ∀ u, GlobalTheory.Mem.Chr.ConjPl (conjE E) w u → u = conjSrc (conjE E) w := fun u h => by
    rw [eq_conjSrc h, conjSrc_conjSrc_cm]
  obtain ⟨u, hu, hu'⟩ := hw
  refine ⟨?_, (key _).2 (Or.inr (conjPl_self_conjSrc w)), fun u' h => ((key u').1 h).imp_right (h2 u')⟩
  rcases (key u).1 hu' with h | h
  · exact absurd h hu
  · rw [← h2 u h]; exact hu

/- English proof (translation)
Establish `h : cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * x.1.val = 1` using `x.2`. Rewrite `h` using `[Matrix.mul_one]`. Establish `h2` using `congrArg (RingHom.mapMatrix ((pLoc E u).comp (pFin E))) h`. Rewrite `h2` using `[map_one, map_mul]`. Conclude with `h2`.
-/
theorem comp_eq (x : UA E n) (u : HeightOneSpectrum (𝓞 E)) :
    ((cLoc (conjSrc (conjE E) u) x).val.map (conjLoc (conjE E) u))ᵀ * (cLoc u x).val = 1 := by
  have h : cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * x.1.val = 1 := x.2
  rw [Matrix.mul_one] at h
  have h2 := congrArg (RingHom.mapMatrix ((pLoc E u).comp (pFin E))) h
  rw [map_one, map_mul] at h2
  exact h2

/- English proof (translation)
Take `⟨-, -, hover⟩` from `over_split hw`. Establish `hw1 : ∀ v, v = w → cLoc v z.1 = 1`. Introduce and unpack `v rfl`. Conclude with `h1`. Establish `hall : ∀ u, cLoc u z.1 = 1`.

Introduce `u`. Distinguish the cases in `hu : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))`. Break down `hover u hu with rfl | rfl` into its components or cases. Conclude with `h1`. Establish `hce` using `comp_eq z.1 (conjSrc (conjE E) w)`.

Rewrite `hce` using `[hw1 _ (conjSrc_conjSrc_cm w), Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul]`. Conclude with `Units.ext hce`. Establish `hz` using `(Subgroup.mem_inf.1 z.2).2`. Conclude with `MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hz u) hu)`. Establish `hinf : cInf z.1 = 1` using `MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 z.2).1`.

Use `Subtype.ext (Subtype.ext (ga_ext ?_ ?_))` and prove the remaining obligations. Conclude with `hinf.trans (map_one _).symm`. Rewrite using `[Subgroup.coe_one, Subgroup.coe_one, map_one]`. Use `Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun u => ?_)` and prove the remaining obligations. Use `congrArg (fun g : GL (Fin n) (u.adicCompletion E) => g.val i j) (hall u)` as an intermediate fact.

Simplify using `only [Units.val_one, Matrix.one_apply] at this`. Use `this.trans ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs with hij <;> simp [hij]`.
-/
theorem eq_one_of_cLoc {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) (z : locU n w) (h1 : cLoc w z.1 = 1) :
    z = 1 := by
  obtain ⟨-, -, hover⟩ := over_split hw
  have hw1 : ∀ v, v = w → cLoc v z.1 = 1 := by
    rintro v rfl
    exact h1
  have hall : ∀ u, cLoc u z.1 = 1 := by
    intro u
    by_cases hu : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))
    · rcases hover u hu with rfl | rfl
      · exact h1
      · have hce := comp_eq z.1 (conjSrc (conjE E) w)
        rw [hw1 _ (conjSrc_conjSrc_cm w), Units.val_one, Matrix.map_one _ (map_zero _) (map_one _),
          Matrix.transpose_one, Matrix.one_mul] at hce
        exact Units.ext hce
    · have hz := (Subgroup.mem_inf.1 z.2).2
      exact MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hz u) hu)
  have hinf : cInf z.1 = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 z.2).1
  refine Subtype.ext (Subtype.ext (ga_ext ?_ ?_))
  · exact hinf.trans (map_one _).symm
  · rw [Subgroup.coe_one, Subgroup.coe_one, map_one]
    refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun u => ?_)
    have := congrArg (fun g : GL (Fin n) (u.adicCompletion E) => g.val i j) (hall u)
    simp only [Units.val_one, Matrix.one_apply] at this
    refine this.trans ?_
    split_ifs with hij <;> simp [hij]

def psi (w : HeightOneSpectrum (𝓞 E)) : w.adicCompletion E →+* (conjSrc (conjE E) w).adicCompletion E :=
  (GlobalTheory.Mem.Chr.exists_finCompl_map (conjE E) (conjPl_self_conjSrc w)).choose

/- English proof (translation)
Assemble the required witnesses or components as `⟨(GlobalTheory.Mem.Chr.exists_finCompl_map (conjE E) (conjPl_self_conjSrc w)).choose_spec.1, (GlobalTheory.Mem.Chr.exists_finCompl_map (conjE E) (conjPl_self_conjSrc w)).choose_spec.2.1⟩`.
-/
theorem psi_spec (w : HeightOneSpectrum (𝓞 E)) : Continuous (psi w) ∧
    ∀ k : E, psi w (algebraMap E _ k) = algebraMap E _ (conjE E k) :=
  ⟨(GlobalTheory.Mem.Chr.exists_finCompl_map (conjE E) (conjPl_self_conjSrc w)).choose_spec.1,
    (GlobalTheory.Mem.Chr.exists_finCompl_map (conjE E) (conjPl_self_conjSrc w)).choose_spec.2.1⟩

/- English proof (translation)
Use `congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) w).equalizer ((conjLoc_spec (conjE E) w).1.comp (psi_spec w).1) continuous_id (funext fun k => ?_)) y` and prove the remaining obligations. Simplify using `only [Function.comp_apply, id, (psi_spec w).2, (conjLoc_spec (conjE E) w).2.1]`. Conclude with `congrArg _ (IsCMField.complexConj_apply_apply E k)`.
-/
theorem conjLoc_psi (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) : conjLoc (conjE E) w (psi w y) = y := by
  refine congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) w).equalizer
    ((conjLoc_spec (conjE E) w).1.comp (psi_spec w).1) continuous_id (funext fun k => ?_)) y
  simp only [Function.comp_apply, id, (psi_spec w).2, (conjLoc_spec (conjE E) w).2.1]
  exact congrArg _ (IsCMField.complexConj_apply_apply E k)

/- English proof (translation)
Establish `key : ∀ (v : HeightOneSpectrum (𝓞 E)) (_ : v = w) (f : v.adicCompletion E →+* (conjSrc (conjE E) w).adicCompletion E), Continuous f → (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (conjE E k)) → f (pLoc E v a) = psi w (pLoc E w a)`. Introduce and unpack `v rfl f hf h`. Conclude with `congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf (psi_spec v).1 (funext fun k => (h k).trans ((psi_spec v).2 k).symm)) _`. Conclude with `key _ (conjSrc_conjSrc_cm w) _ (conjLoc_spec (conjE E) _).1 (conjLoc_spec (conjE E) _).2.1`.
-/
theorem conjLoc_pLoc (w : HeightOneSpectrum (𝓞 E)) (a : Af E) :
    conjLoc (conjE E) (conjSrc (conjE E) w) (pLoc E (conjSrc (conjE E) (conjSrc (conjE E) w)) a) = psi w (pLoc E w a) := by
  have key : ∀ (v : HeightOneSpectrum (𝓞 E)) (_ : v = w)
      (f : v.adicCompletion E →+* (conjSrc (conjE E) w).adicCompletion E), Continuous f →
      (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (conjE E k)) → f (pLoc E v a) = psi w (pLoc E w a) := by
    rintro v rfl f hf h
    exact congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf (psi_spec v).1
      (funext fun k => (h k).trans ((psi_spec v).2 k).symm)) _
  exact key _ (conjSrc_conjSrc_cm w) _ (conjLoc_spec (conjE E) _).1 (conjLoc_spec (conjE E) _).2.1

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `((g⁻¹ : GL (Fin n) R).val)ᵀ.map f = ((GeneralLinearGroup.map f g)⁻¹).valᵀ`. Rewrite using `[← map_inv]`. Both sides reduce to the same expression.
-/
theorem invT_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (g : GL (Fin n) R) :
    GeneralLinearGroup.map f (invT n R g) = invT n S (GeneralLinearGroup.map f g) := by
  apply Units.ext
  change ((g⁻¹ : GL (Fin n) R).val)ᵀ.map f = ((GeneralLinearGroup.map f g)⁻¹).valᵀ
  rw [← map_inv]
  rfl

def finPt (w : HeightOneSpectrum (𝓞 E)) (h : GL (Fin n) (w.adicCompletion E)) : GL (Fin n) (Af E) :=
  locGL E n w h * locGL E n (conjSrc (conjE E) w) (invT n _ (GeneralLinearGroup.map (psi w) h))

/- English proof (translation)
Rewrite using `[finPt, map_mul, pLoc_locGL, pLoc_locGL_of_ne (Ne.symm hne), mul_one]`.
-/
theorem finPt_w {w : HeightOneSpectrum (𝓞 E)} (hne : conjSrc (conjE E) w ≠ w) (h : GL (Fin n) (w.adicCompletion E)) :
    GeneralLinearGroup.map (pLoc E w) (finPt w h) = h := by
  rw [finPt, map_mul, pLoc_locGL, pLoc_locGL_of_ne (Ne.symm hne), mul_one]

/- English proof (translation)
Rewrite using `[finPt, map_mul, pLoc_locGL, pLoc_locGL_of_ne hne, one_mul]`.
-/
theorem finPt_w' {w : HeightOneSpectrum (𝓞 E)} (hne : conjSrc (conjE E) w ≠ w) (h : GL (Fin n) (w.adicCompletion E)) :
    GeneralLinearGroup.map (pLoc E (conjSrc (conjE E) w)) (finPt w h) =
      invT n _ (GeneralLinearGroup.map (psi w) h) := by
  rw [finPt, map_mul, pLoc_locGL, pLoc_locGL_of_ne hne, one_mul]

/- English proof (translation)
Rewrite using `[finPt, map_mul, pLoc_locGL_of_ne h1, pLoc_locGL_of_ne h2, one_mul]`.
-/
theorem finPt_other {w u : HeightOneSpectrum (𝓞 E)} (h1 : u ≠ w) (h2 : u ≠ conjSrc (conjE E) w)
    (h : GL (Fin n) (w.adicCompletion E)) : GeneralLinearGroup.map (pLoc E u) (finPt w h) = 1 := by
  rw [finPt, map_mul, pLoc_locGL_of_ne h1, pLoc_locGL_of_ne h2, one_mul]

omit [IsCMField E] in
/- English proof (translation)
The claim follows from `Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun u => congrFun (congrFun (h u) i) j`.
-/
theorem matAf_ext {M N : Matrix (Fin n) (Fin n) (Af E)}
    (h : ∀ u, RingHom.mapMatrix (pLoc E u) M = RingHom.mapMatrix (pLoc E u) N) : M = N :=
  Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun u => congrFun (congrFun (h u) i) j

/- English proof (translation)
The claim follows from `Matrix.ext fun i j => ad_ext (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)`.
-/
theorem matAd_ext {M N : Matrix (Fin n) (Fin n) (Ad E)} (h1 : RingHom.mapMatrix (pInf E) M = RingHom.mapMatrix (pInf E) N)
    (h2 : RingHom.mapMatrix (pFin E) M = RingHom.mapMatrix (pFin E) N) : M = N :=
  Matrix.ext fun i j => ad_ext (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)

/- English proof (translation)
Use `show cT (conjAd E) (finGL E n k).val * 1 * (finGL E n k).val = 1`. Rewrite using `[Matrix.mul_one]`. Establish `hinf : (finGL E n k).val.map (pInf E) = 1` using `congrArg Units.val (pInf_finGL k)`. Establish `hfin : (finGL E n k).val.map (pFin E) = k.val` using `congrArg Units.val (pFin_finGL k)`. Use `matAd_ext ?_ ?_` and prove the remaining obligations.

Rewrite using `[map_mul, map_one]`. Establish `e : RingHom.mapMatrix (pInf E) (cT (conjAd E) (finGL E n k).val) = 1`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Establish `hji` using `congrFun (congrFun hinf j) i`. Express the relevant statement in the definitionally equal form `pInf E (conjAd E ((finGL E n k).val j i)) = _`.

Rewrite using `[show pInf E (conjAd E ((finGL E n k).val j i)) = starRingEnd (Cinf E) (pInf E ((finGL E n k).val j i)) from (infEq E).symm_apply_apply _]`. Express the relevant statement in the definitionally equal form `starRingEnd (Cinf E) (((finGL E n k).val.map (pInf E)) j i) = _`. Rewrite using `[hinf]`. Simplify using `[Matrix.one_apply, eq_comm]`. Rewrite using `[e, one_mul]`.

Conclude with `hinf`. Rewrite using `[map_mul, map_one]`. Establish `e : RingHom.mapMatrix (pFin E) (cT (conjAd E) (finGL E n k).val) = cT (conjFin (conjE E)) k.val`. Rewrite using `[← hfin]`. Both sides reduce to the same expression.

Express the relevant statement in the definitionally equal form `RingHom.mapMatrix (pFin E) (cT (conjAd E) (finGL E n k).val) * (finGL E n k).val.map (pFin E) = 1`. Rewrite using `[e, hfin]`. Use `matAf_ext fun u => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_one]`. Conclude with `hk u`.
-/
theorem finGL_mem_UA (k : GL (Fin n) (Af E))
    (hk : ∀ u, ((GeneralLinearGroup.map (pLoc E (conjSrc (conjE E) u)) k).val.map (conjLoc (conjE E) u))ᵀ *
      (GeneralLinearGroup.map (pLoc E u) k).val = 1) : finGL E n k ∈ UA E n := by
  show cT (conjAd E) (finGL E n k).val * 1 * (finGL E n k).val = 1
  rw [Matrix.mul_one]
  have hinf : (finGL E n k).val.map (pInf E) = 1 := congrArg Units.val (pInf_finGL k)
  have hfin : (finGL E n k).val.map (pFin E) = k.val := congrArg Units.val (pFin_finGL k)
  refine matAd_ext ?_ ?_
  · rw [map_mul, map_one]
    have e : RingHom.mapMatrix (pInf E) (cT (conjAd E) (finGL E n k).val) = 1 := by
      refine Matrix.ext fun i j => ?_
      have hji := congrFun (congrFun hinf j) i
      change pInf E (conjAd E ((finGL E n k).val j i)) = _
      rw [show pInf E (conjAd E ((finGL E n k).val j i)) = starRingEnd (Cinf E) (pInf E ((finGL E n k).val j i)) from
        (infEq E).symm_apply_apply _]
      change starRingEnd (Cinf E) (((finGL E n k).val.map (pInf E)) j i) = _
      rw [hinf]
      simp [Matrix.one_apply, eq_comm]
    rw [e, one_mul]
    exact hinf
  · rw [map_mul, map_one]
    have e : RingHom.mapMatrix (pFin E) (cT (conjAd E) (finGL E n k).val) = cT (conjFin (conjE E)) k.val := by
      rw [← hfin]; rfl
    change RingHom.mapMatrix (pFin E) (cT (conjAd E) (finGL E n k).val) * (finGL E n k).val.map (pFin E) = 1
    rw [e, hfin]
    refine matAf_ext fun u => ?_
    rw [map_mul, map_one]
    exact hk u

/- English proof (translation)
Take `⟨hne, -, -⟩` from `over_split hw`. Distinguish the cases in `h1 : u = w`. Rewrite using `[h1, finPt_w' hne, finPt_w hne]`. Express the relevant statement in the definitionally equal form `((GeneralLinearGroup.map (conjLoc (conjE E) w) (invT n _ (GeneralLinearGroup.map (psi w) h))).val)ᵀ * h.val = 1`. Rewrite using `[invT_map, show GeneralLinearGroup.map (conjLoc (conjE E) w) (GeneralLinearGroup.map (psi w) h) = h from Units.ext (Matrix.ext fun i j => conjLoc_psi w _)]`.

Express the relevant statement in the definitionally equal form `(((h⁻¹ : GL (Fin n) _).val)ᵀ)ᵀ * h.val = 1`. Rewrite using `[Matrix.transpose_transpose, Units.inv_mul]`. Distinguish the cases in `h2 : u = conjSrc (conjE E) w`. Rewrite using `[h2, finPt_w' hne]`. Establish `e : (GeneralLinearGroup.map (pLoc E (conjSrc (conjE E) (conjSrc (conjE E) w))) (finPt w h)).val.map (conjLoc (conjE E) (conjSrc (conjE E) w)) = (GeneralLinearGroup.map (psi w) h).val`.

Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Use `(conjLoc_pLoc w _).trans ?_` and prove the remaining obligations. Use `congrArg (fun g : GL (Fin n) (w.adicCompletion E) => g.val i j) (finPt_w hne h)` as an intermediate fact. Conclude with `congrArg (psi w) this`. Rewrite using `[e]`.

Express the relevant statement in the definitionally equal form `(GeneralLinearGroup.map (psi w) h).valᵀ * ((GeneralLinearGroup.map (psi w) h)⁻¹).valᵀ = 1`. Rewrite using `[← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]`. Establish `h3 : conjSrc (conjE E) u ≠ w` using `fun e => h2 (by rw [← e, conjSrc_conjSrc_cm])`. Establish `h4 : conjSrc (conjE E) u ≠ conjSrc (conjE E) w` using `fun e => h1 (conjSrc_injective _ e)`. Rewrite using `[finPt_other h3 h4, finPt_other h1 h2]`.

Simplify using the standard rewrite rules.
-/
theorem finPt_cond {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) (h : GL (Fin n) (w.adicCompletion E))
    (u : HeightOneSpectrum (𝓞 E)) :
    ((GeneralLinearGroup.map (pLoc E (conjSrc (conjE E) u)) (finPt w h)).val.map (conjLoc (conjE E) u))ᵀ *
      (GeneralLinearGroup.map (pLoc E u) (finPt w h)).val = 1 := by
  obtain ⟨hne, -, -⟩ := over_split hw
  by_cases h1 : u = w
  · rw [h1, finPt_w' hne, finPt_w hne]
    change ((GeneralLinearGroup.map (conjLoc (conjE E) w) (invT n _ (GeneralLinearGroup.map (psi w) h))).val)ᵀ * h.val = 1
    rw [invT_map, show GeneralLinearGroup.map (conjLoc (conjE E) w) (GeneralLinearGroup.map (psi w) h) = h from
      Units.ext (Matrix.ext fun i j => conjLoc_psi w _)]
    change (((h⁻¹ : GL (Fin n) _).val)ᵀ)ᵀ * h.val = 1
    rw [Matrix.transpose_transpose, Units.inv_mul]
  · by_cases h2 : u = conjSrc (conjE E) w
    · rw [h2, finPt_w' hne]
      have e : (GeneralLinearGroup.map (pLoc E (conjSrc (conjE E) (conjSrc (conjE E) w))) (finPt w h)).val.map
          (conjLoc (conjE E) (conjSrc (conjE E) w)) = (GeneralLinearGroup.map (psi w) h).val := by
        refine Matrix.ext fun i j => ?_
        refine (conjLoc_pLoc w _).trans ?_
        have := congrArg (fun g : GL (Fin n) (w.adicCompletion E) => g.val i j) (finPt_w hne h)
        exact congrArg (psi w) this
      rw [e]
      change (GeneralLinearGroup.map (psi w) h).valᵀ * ((GeneralLinearGroup.map (psi w) h)⁻¹).valᵀ = 1
      rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
    · have h3 : conjSrc (conjE E) u ≠ w := fun e => h2 (by rw [← e, conjSrc_conjSrc_cm])
      have h4 : conjSrc (conjE E) u ≠ conjSrc (conjE E) w := fun e => h1 (conjSrc_injective _ e)
      rw [finPt_other h3 h4, finPt_other h1 h2]
      simp

/- English proof (translation)
Express the relevant statement in the definitionally equal form `GeneralLinearGroup.map ((pLoc E u).comp (pFin E)) (finGL E n k) = _`. Establish `e : ∀ g : GA E n, GeneralLinearGroup.map ((pLoc E u).comp (pFin E)) g = GeneralLinearGroup.map (pLoc E u) (GeneralLinearGroup.map (pFin E) g)` using `fun g => Units.ext rfl`. Rewrite using `[e, pFin_finGL]`.
-/
theorem cLoc_finGL (u : HeightOneSpectrum (𝓞 E)) (k : GL (Fin n) (Af E)) (hk : finGL E n k ∈ UA E n) :
    cLoc u (⟨finGL E n k, hk⟩ : UA E n) = GeneralLinearGroup.map (pLoc E u) k := by
  change GeneralLinearGroup.map ((pLoc E u).comp (pFin E)) (finGL E n k) = _
  have e : ∀ g : GA E n, GeneralLinearGroup.map ((pLoc E u).comp (pFin E)) g =
      GeneralLinearGroup.map (pLoc E u) (GeneralLinearGroup.map (pFin E) g) := fun g => Units.ext rfl
  rw [e, pFin_finGL]

def locPt {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) (h : GL (Fin n) (w.adicCompletion E)) : locU n w :=
  ⟨⟨finGL E n (finPt w h), finGL_mem_UA _ (finPt_cond hw h)⟩, by
    obtain ⟨-, hw', -⟩ := over_split hw
    refine Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 (pInf_finGL _), Subgroup.mem_iInf.2 fun u =>
      Subgroup.mem_iInf.2 fun hu => MonoidHom.mem_ker.2 ?_⟩
    rw [cLoc_finGL]
    exact finPt_other (fun e => hu (by rw [e])) (fun e => hu (by rw [e, hw'])) h⟩

/- English proof (translation)
The claim follows from `(cLoc_finGL w _ _).trans (finPt_w (over_split hw).1 h)`.
-/
theorem cLoc_locPt {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) (h : GL (Fin n) (w.adicCompletion E)) :
    cLoc w (locPt hw h).1 = h :=
  (cLoc_finGL w _ _).trans (finPt_w (over_split hw).1 h)

/- English proof (translation)
The claim follows from `Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩`.
-/
theorem continuous_invT (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (invT n R) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

end GlobalTheory.SplitPts

open GlobalTheory.SplitPts in

/- English proof (translation)
Introduce `E _ _ _ n w hw`. Establish `inj : ∀ a b : locU n w, cLoc w a.1 = cLoc w b.1 → a = b` using `fun a b hab => by`. Use `eq_one_of_cLoc hw (a * b⁻¹) (by rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hab, mul_inv_cancel])` as an intermediate fact. Conclude with `mul_inv_eq_one.1 this`. Establish `hfin : Continuous (finGL E n)` using `Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))))`.

Use `⟨{ toFun := fun x => cLoc w x.1 invFun := locPt hw left_inv := fun x => inj _ _ (cLoc_locPt hw _) right_inv := fun h => cLoc_locPt hw h map_mul' := fun x y => map_mul (cLoc w) x.1 y.1 continuous_toFun := ?_ continuous_invFun := ?_ }, fun x => rfl⟩` and prove the remaining obligations. Conclude with `(Continuous.units_map _ (continuous_id.matrix_map ((RestrictedProduct.continuous_eval w).comp continuous_snd))).comp (continuous_subtype_val.comp continuous_subtype_val)`. Use `Continuous.subtype_mk (Continuous.subtype_mk (hfin.comp ?_) _) _` and prove the remaining obligations. Conclude with `(CuspSub.continuous_locGL w).mul ((CuspSub.continuous_locGL _).comp ((continuous_invT _).comp (Continuous.units_map _ (continuous_id.matrix_map (psi_spec w).1))))`.
-/
theorem GlobalTheory.locU_equiv_GL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w →
      ∃ e : locU n w ≃ₜ* GL (Fin n) (w.adicCompletion E), ∀ x : locU n w, e x = cLoc w (x : UA E n) := by
  intro E _ _ _ n w hw
  have inj : ∀ a b : locU n w, cLoc w a.1 = cLoc w b.1 → a = b := fun a b hab => by
    have := eq_one_of_cLoc hw (a * b⁻¹)
      (by rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hab, mul_inv_cancel])
    exact mul_inv_eq_one.1 this
  have hfin : Continuous (finGL E n) :=
    Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
      (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))))
  refine ⟨{ toFun := fun x => cLoc w x.1
            invFun := locPt hw
            left_inv := fun x => inj _ _ (cLoc_locPt hw _)
            right_inv := fun h => cLoc_locPt hw h
            map_mul' := fun x y => map_mul (cLoc w) x.1 y.1
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun x => rfl⟩
  · exact (Continuous.units_map _ (continuous_id.matrix_map
      ((RestrictedProduct.continuous_eval w).comp continuous_snd))).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  · refine Continuous.subtype_mk (Continuous.subtype_mk (hfin.comp ?_) _) _
    exact (CuspSub.continuous_locGL w).mul ((CuspSub.continuous_locGL _).comp ((continuous_invT _).comp
      (Continuous.units_map _ (continuous_id.matrix_map (psi_spec w).1))))
