import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.LocalGlobalOfIwahori
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct
open GlobalTheory.WeilDeligne LocalGlobalAboveLAlt

namespace GlobalTheory.CompanionTheory.RelOpsLeaf

section Linear

variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

/- English proof (translation)
Establish `hm` using `LinearMap.charpoly_monic f`. Establish `hd : f.charpoly.natDegree = 1` using `by rw [LinearMap.charpoly_natDegree, hV]`. Establish `h1` using `hm.eq_X_add_C hd`. Establish `h2` using `LinearMap.aeval_self_charpoly f`. Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : ∃ t : ℂ, f = t • (1 : Module.End ℂ V) := by`.

Use `⟨-f.charpoly.coeff 0, ?_⟩` and prove the remaining obligations. Rewrite `h2` using `[h1, map_add, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]`. Rewrite using `[neg_smul, eq_neg_iff_add_eq_zero]`. Conclude with `h2`. Substitute `ht` using the available equality.

Rewrite using `[LinearMap.det_smul, hV, pow_one]`. Simplify using the standard rewrite rules.
-/
theorem eq_det_smul_one (hV : finrank ℂ V = 1) (f : Module.End ℂ V) :
    f = LinearMap.det f • (1 : Module.End ℂ V) := by
  have hm := LinearMap.charpoly_monic f
  have hd : f.charpoly.natDegree = 1 := by rw [LinearMap.charpoly_natDegree, hV]
  have h1 := hm.eq_X_add_C hd
  have h2 := LinearMap.aeval_self_charpoly f
  obtain ⟨t, ht⟩ : ∃ t : ℂ, f = t • (1 : Module.End ℂ V) := by
    refine ⟨-f.charpoly.coeff 0, ?_⟩
    rw [h1, map_add, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at h2
    rw [neg_smul, eq_neg_iff_add_eq_zero]
    exact h2
  subst ht
  rw [LinearMap.det_smul, hV, pow_one]
  simp

/- English proof (translation)
Use `Polynomial.funext fun z => ?_` and prove the remaining obligations. Establish `h0 : t * (z / t) = z` using `by field_simp`. Establish `h1` using `scaleRoots_eval₂_mul (p := f.charpoly) (RingHom.id ℂ) (z / t) t`. Simplify using `only [RingHom.id_apply, h0, eval₂_id] at h1`. Rewrite using `[h1, LinearMap.eval_charpoly, LinearMap.eval_charpoly, LinearMap.charpoly_natDegree, ← LinearMap.det_smul]`.

Use `congr 1`. Rewrite using `[smul_sub, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_smul, h0]`.
-/
theorem charpoly_smul_eq_scaleRoots (f : Module.End ℂ V) {t : ℂ} (ht : t ≠ 0) :
    (t • f).charpoly = f.charpoly.scaleRoots t := by
  refine Polynomial.funext fun z => ?_
  have h0 : t * (z / t) = z := by field_simp
  have h1 := scaleRoots_eval₂_mul (p := f.charpoly) (RingHom.id ℂ) (z / t) t
  simp only [RingHom.id_apply, h0, eval₂_id] at h1
  rw [h1, LinearMap.eval_charpoly, LinearMap.eval_charpoly, LinearMap.charpoly_natDegree,
    ← LinearMap.det_smul]
  congr 1
  rw [smul_sub, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_smul, h0]

/- English proof (translation)
Set `e : V' ≃ₗ[ℂ] ℂ` to `LinearEquiv.ofFinrankEq _ _ (by rw [hV', finrank_self])`. Set `F : (V ⊗[ℂ] V') ≃ₗ[ℂ] V` to `(TensorProduct.congr (LinearEquiv.refl ℂ V) e).trans (TensorProduct.rid ℂ V)`. Establish `key : ∀ u, F (TensorProduct.map f (1 : Module.End ℂ V') u) = f (F u)`. Introduce `u`. Proceed by induction on `u using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a b => simp [F]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Rewrite using `[← LinearEquiv.charpoly_conj F]`. Use `congr 1`.

Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Take `⟨u, rfl⟩` from `F.surjective v`. Simplify using `[LinearEquiv.conj_apply, key]`.
-/
theorem charpoly_map_one (hV' : finrank ℂ V' = 1) (f : Module.End ℂ V) :
    (TensorProduct.map f (1 : Module.End ℂ V')).charpoly = f.charpoly := by
  let e : V' ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq _ _ (by rw [hV', finrank_self])
  let F : (V ⊗[ℂ] V') ≃ₗ[ℂ] V :=
    (TensorProduct.congr (LinearEquiv.refl ℂ V) e).trans (TensorProduct.rid ℂ V)
  have key : ∀ u, F (TensorProduct.map f (1 : Module.End ℂ V') u) = f (F u) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [F]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [← LinearEquiv.charpoly_conj F]
  congr 1
  refine LinearMap.ext fun v => ?_
  obtain ⟨u, rfl⟩ := F.surjective v
  simp [LinearEquiv.conj_apply, key]

end Linear

/- English proof (translation)
Establish `e : (X - 1 : ℂ[X]) = X - C 1` using `by simp`. Rewrite `h`, the goal using `[e]`. Establish `key : ∀ {r : ℂ[X]}, r.Monic → r ∣ (X - C 1) ^ (m + n) → r = (X - C 1) ^ r.natDegree`. Introduce `r hr hd`. Take `⟨i, -, hi⟩` from `(dvd_prime_pow (prime_X_sub_C (1 : ℂ)) _).1 hd`.

Establish `h1` using `eq_of_monic_of_associated hr ((monic_X_sub_C (1 : ℂ)).pow i) hi`. Establish `h2 : r.natDegree = i` using `by rw [h1, natDegree_pow, natDegree_X_sub_C, mul_one]`. Rewrite using `[h2]`. Conclude with `h1`. Substitute `hpd hqd` using the available equality.

Conclude with `⟨key hp (Dvd.intro _ h), key hq (Dvd.intro_left _ h)⟩`.
-/
theorem pow_of_mul_eq_pow {p q : ℂ[X]} {m n : ℕ} (hp : p.Monic) (hq : q.Monic)
    (hpd : p.natDegree = m) (hqd : q.natDegree = n) (h : p * q = (X - 1) ^ (m + n)) :
    p = (X - 1) ^ m ∧ q = (X - 1) ^ n := by
  have e : (X - 1 : ℂ[X]) = X - C 1 := by simp
  rw [e] at h ⊢
  have key : ∀ {r : ℂ[X]}, r.Monic → r ∣ (X - C 1) ^ (m + n) → r = (X - C 1) ^ r.natDegree := by
    intro r hr hd
    obtain ⟨i, -, hi⟩ := (dvd_prime_pow (prime_X_sub_C (1 : ℂ)) _).1 hd
    have h1 := eq_of_monic_of_associated hr ((monic_X_sub_C (1 : ℂ)).pow i) hi
    have h2 : r.natDegree = i := by rw [h1, natDegree_pow, natDegree_X_sub_C, mul_one]
    rw [h2]
    exact h1
  subst hpd hqd
  exact ⟨key hp (Dvd.intro _ h), key hq (Dvd.intro_left _ h)⟩

section Rel

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

/- English proof (translation)
Proceed by induction on `c using WD.ind with`. Consider the case `hP m b`. Rewrite `hc` using `[WD.lpDim_mk]`. Set `f : ↥(Weil h) →* ℂ` to `(LinearMap.det : Module.End ℂ (Fin m → ℂ) →* ℂ).comp b.ρ`. Use `⟨f.toHomUnits, fun x g => ?_⟩` and prove the remaining obligations.

Proceed by induction on `x using WD.ind with`. Consider the case `hP n a`. Establish `hb : b.ρ g = ((f.toHomUnits g : ℂˣ) : ℂ) • (1 : Module.End ℂ (Fin m → ℂ))`. Rewrite using `[MonoidHom.coe_toHomUnits]`. Conclude with `eq_det_smul_one hc (b.ρ g)`.

Rewrite using `[WD.lpChar_mk, WD.charPol_mk, WD.charPol_mk, WDRep.tensor_ρ, hb, TensorProduct.map_smul_right, charpoly_smul_eq_scaleRoots _ (Units.ne_zero _), charpoly_map_one hc]`.
-/
theorem exists_char_of_lpDim_eq_one (c : WD h) (hc : c.lpDim = 1) :
    ∃ χ : ↥(Weil h) →* ℂˣ, ∀ (x : WD h) (g : ↥(Weil h)),
      (x.lpChar c).charPol g = (x.charPol g).scaleRoots (χ g : ℂ) := by
  induction c using WD.ind with
  | hP m b =>
    rw [WD.lpDim_mk] at hc
    let f : ↥(Weil h) →* ℂ := (LinearMap.det : Module.End ℂ (Fin m → ℂ) →* ℂ).comp b.ρ
    refine ⟨f.toHomUnits, fun x g => ?_⟩
    induction x using WD.ind with
    | hP n a =>
      have hb : b.ρ g = ((f.toHomUnits g : ℂˣ) : ℂ) • (1 : Module.End ℂ (Fin m → ℂ)) := by
        rw [MonoidHom.coe_toHomUnits]
        exact eq_det_smul_one hc (b.ρ g)
      rw [WD.lpChar_mk, WD.charPol_mk, WD.charPol_mk, WDRep.tensor_ρ, hb,
        TensorProduct.map_smul_right, charpoly_smul_eq_scaleRoots _ (Units.ne_zero _),
        charpoly_map_one hc]

end Rel

end GlobalTheory.CompanionTheory.RelOpsLeaf
