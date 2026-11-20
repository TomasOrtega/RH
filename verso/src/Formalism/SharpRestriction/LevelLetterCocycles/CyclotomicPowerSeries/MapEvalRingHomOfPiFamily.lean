import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstantCoeffAeval
import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.CycloSimple
import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.CycloDist
import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.PiSeries

noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

def ofPiFamily {LL ι : Type} [CommRing LL] (f : ι → PowerSeries LL) :
    PowerSeries (ι → LL) :=
  PowerSeries.mk fun n i => coeff n (f i)

/- English proof (translation)
Use extensionality with `n`. Simplify using `[ofPiFamily, PowerSeries.coeff_map, PowerSeries.coeff_mk]`.
-/
theorem map_evalRingHom_ofPiFamily {LL ι : Type} [CommRing LL] (f : ι → PowerSeries LL) (i : ι) :
    PowerSeries.map (Pi.evalRingHom (fun _ => LL) i) (ofPiFamily f) = f i := by
  ext n
  simp [ofPiFamily, PowerSeries.coeff_map, PowerSeries.coeff_mk]

/- English proof (translation)
Use extensionality with `n i`. Establish `h' : coeff n (PowerSeries.map (Pi.evalRingHom (fun _ => LL) i) F) = coeff n (PowerSeries.map (Pi.evalRingHom (fun _ => LL) i) G)` using `by rw [h i]`. Simplify `h'` using `[PowerSeries.coeff_map]`.
-/
theorem ext_evalRingHom {LL ι : Type} [CommRing LL] {F G : PowerSeries (ι → LL)}
    (h : ∀ i, PowerSeries.map (Pi.evalRingHom (fun _ => LL) i) F =
      PowerSeries.map (Pi.evalRingHom (fun _ => LL) i) G) : F = G := by
  ext n i
  have h' : coeff n (PowerSeries.map (Pi.evalRingHom (fun _ => LL) i) F) =
      coeff n (PowerSeries.map (Pi.evalRingHom (fun _ => LL) i) G) := by rw [h i]
  simpa [PowerSeries.coeff_map] using h'

def piAlgHom {O LL ι : Type} [CommRing O] [CommRing LL] [Algebra O LL]
    (ρ : ι → (PowerSeries O →ₐ[O] PowerSeries LL)) : PowerSeries O →ₐ[O] PowerSeries (ι → LL) where
  toFun a := ofPiFamily fun i => ρ i a
  map_one' := ext_evalRingHom fun i => by simp [map_evalRingHom_ofPiFamily]
  map_mul' a b := ext_evalRingHom fun i => by simp [map_evalRingHom_ofPiFamily]
  map_zero' := ext_evalRingHom fun i => by simp [map_evalRingHom_ofPiFamily]
  map_add' a b := ext_evalRingHom fun i => by simp [map_evalRingHom_ofPiFamily]
  commutes' c := ext_evalRingHom fun i => by
    rw [map_evalRingHom_ofPiFamily, AlgHom.commutes]
    ext n
    simp [PowerSeries.algebraMap_apply, coeff_C]

/- English proof (translation)
Use `first`. Consider the case `exact map_evalRingHom_ofPiFamily (fun i => ρ i a) i`. Consider the case `(simp only [piAlgHom, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]`. Conclude with `map_evalRingHom_ofPiFamily _ i)`.
-/
theorem map_evalRingHom_piAlgHom {O LL ι : Type} [CommRing O] [CommRing LL] [Algebra O LL]
    (ρ : ι → (PowerSeries O →ₐ[O] PowerSeries LL)) (i : ι) (a : PowerSeries O) :
    PowerSeries.map (Pi.evalRingHom (fun _ => LL) i) (piAlgHom ρ a) = ρ i a := by
  first
    | exact map_evalRingHom_ofPiFamily (fun i => ρ i a) i
    | (simp only [piAlgHom, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
       exact map_evalRingHom_ofPiFamily _ i)

/- English proof (translation)
Rewrite using `[← map_evalRingHom_piAlgHom ρ i a, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]`. Both sides reduce to the same expression.
-/
theorem constantCoeff_piAlgHom {O LL ι : Type} [CommRing O] [CommRing LL] [Algebra O LL]
    (ρ : ι → (PowerSeries O →ₐ[O] PowerSeries LL)) (i : ι) (a : PowerSeries O) :
    constantCoeff (piAlgHom ρ a) i = constantCoeff (ρ i a) := by
  rw [← map_evalRingHom_piAlgHom ρ i a, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
  rfl

/- English proof (translation)
Establish `hdiv : Polynomial.cyclotomic n LL ∣ r.comp (Polynomial.X - 1)`. Rewrite using `[Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ₀]`. Apply `Finset.prod_dvd_of_coprime` to reduce the goal to its premises. Conclude with `(Polynomial.pairwise_coprime_X_sub_C Function.injective_id).set_pairwise _`. Introduce `μ hμ`.

Rewrite using `[Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, Polynomial.eval_comp]`. Simplify using `using hr μ ((mem_primitiveRoots hn).mp hμ)`. Take `⟨c, hc⟩` from `hdiv`. Use `⟨c.comp (Polynomial.X + 1), ?_⟩` and prove the remaining obligations. Establish `hback : (r.comp (Polynomial.X - 1)).comp (Polynomial.X + 1) = r`.

Rewrite using `[Polynomial.comp_assoc]`. Simplify using the standard rewrite rules. Rewrite using `[← hback, hc, Polynomial.mul_comp]`.
-/
theorem cyclotomic_comp_dvd {LL : Type} [Field LL] (n : ℕ) (hn : 0 < n) (ζ₀ : LL)
    (hζ₀ : IsPrimitiveRoot ζ₀ n) (r : Polynomial LL)
    (hr : ∀ ζ, IsPrimitiveRoot ζ n → r.eval (ζ - 1) = 0) :
    (Polynomial.cyclotomic n LL).comp (Polynomial.X + 1) ∣ r := by
  classical
  have hdiv : Polynomial.cyclotomic n LL ∣ r.comp (Polynomial.X - 1) := by
    rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ₀]
    apply Finset.prod_dvd_of_coprime
    · exact (Polynomial.pairwise_coprime_X_sub_C Function.injective_id).set_pairwise _
    · intro μ hμ
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, Polynomial.eval_comp]
      simpa using hr μ ((mem_primitiveRoots hn).mp hμ)
  obtain ⟨c, hc⟩ := hdiv
  refine ⟨c.comp (Polynomial.X + 1), ?_⟩
  have hback : (r.comp (Polynomial.X - 1)).comp (Polynomial.X + 1) = r := by
    rw [Polynomial.comp_assoc]
    simp
  rw [← hback, hc, Polynomial.mul_comp]

/- English proof (translation)
Use extensionality with `n`. Establish `key : (1 / ((n + 1).factorial : ℚ)) * ((n : ℚ) + 1) = 1 / (n.factorial : ℚ)`. Establish `h0 : (n.factorial : ℚ) ≠ 0` using `by exact_mod_cast Nat.factorial_ne_zero n`. Rewrite using `[Nat.factorial_succ, Nat.cast_mul]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[PowerSeries.coeff_derivative, PowerSeries.coeff_exp, PowerSeries.coeff_exp]`. Establish `h` using `congrArg (algebraMap ℚ A) key`. Rewrite `h` using `[map_mul]`. Simplify using `using h`.
-/
private theorem derivative_exp_eq_exp' (A : Type) [Field A] [CharZero A] :
    derivative A (PowerSeries.exp A) = PowerSeries.exp A := by
  ext n
  have key : (1 / ((n + 1).factorial : ℚ)) * ((n : ℚ) + 1) = 1 / (n.factorial : ℚ) := by
    have h0 : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    rw [Nat.factorial_succ, Nat.cast_mul]
    push_cast
    field_simp
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_exp, PowerSeries.coeff_exp]
  have h := congrArg (algebraMap ℚ A) key
  rw [map_mul] at h
  simpa using h

/- English proof (translation)
Use `first`. Consider the case `simp`. Consider the case `(rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_exp]; simp)`.
-/
private theorem constantCoeff_exp_eq_one (A : Type) [Field A] [CharZero A] :
    constantCoeff (PowerSeries.exp A) = 1 := by
  first
    | simp
    | (rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_exp]; simp)

/- English proof (translation)
Establish `hexp0` using `constantCoeff_exp_eq_one LL`. Establish `hcyc : ∀ z : PowerSeries LL, Polynomial.aeval z (Polynomial.cyclotomic n O) = Polynomial.aeval z (Polynomial.cyclotomic n LL)`. Introduce `z`. Use `first`. Consider the case `rw [← Polynomial.map_cyclotomic n (algebraMap O LL), Polynomial.aeval_map_algebraMap]`.

Consider the case `rw [← Polynomial.map_cyclotomic_int n O, ← Polynomial.map_cyclotomic_int n LL, ← algebraMap_int_eq, ← algebraMap_int_eq, Polynomial.aeval_map_algebraMap, Polynomial.aeval_map_algebraMap]`. Establish `hunit : ∀ ζ, IsPrimitiveRoot ζ n → ∃ w : (PowerSeries LL)ˣ, ρ ζ (((Polynomial.cyclotomic n O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) = (w : PowerSeries LL) * X`. Introduce `ζ hζ`. Establish `hroot : Polynomial.aeval ζ (Polynomial.cyclotomic n LL) = 0`. Rewrite using `[Polynomial.coe_aeval_eq_eval]`.

Use `haveI : NeZero (n : LL) := ⟨by exact_mod_cast hn.ne'⟩`. Use `first`. Consider the case `exact Polynomial.isRoot_cyclotomic_iff.mpr hζ`. Consider the case `exact Polynomial.isRoot_cyclotomic hn hζ`. Take `⟨w, hw⟩` from `cycloSimple LL LL n hn ζ (PowerSeries.exp LL) hroot hexp0 (derivative_exp_eq_exp' LL)`.

Use `⟨w, ?_⟩` and prove the remaining obligations. Rewrite using `[algHom_coe_eq_aeval, Polynomial.aeval_comp]`. Establish `h1 : Polynomial.aeval (ρ ζ X) (Polynomial.X + 1 : Polynomial O) = C ζ * PowerSeries.exp LL`. Rewrite using `[map_add, Polynomial.aeval_X, map_one, add_comm]`. Conclude with `hρ ζ hζ`.

Rewrite using `[h1, hcyc]`. Conclude with `hw`. Use `choose! w hw using hunit`. Establish `hWu : IsUnit (ofPiFamily fun i : {ζ : LL // IsPrimitiveRoot ζ n} => (w i.1 : PowerSeries LL))` using `((piSeries LL {ζ : LL // IsPrimitiveRoot ζ n}).2 _).2.mpr fun i => by`. Rewrite using `[map_evalRingHom_ofPiFamily]`.

Conclude with `(w i.1).isUnit`. Establish `hρP : piAlgHom (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) (((Polynomial.cyclotomic n O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) = (hWu.unit : PowerSeries ({ζ : LL // IsPrimitiveRoot ζ n} → LL)) * X`. Rewrite using `[IsUnit.unit_spec]`. Apply `ext_evalRingHom` to reduce the goal to its premises. Introduce `i`.

Rewrite using `[map_evalRingHom_piAlgHom, map_mul, map_evalRingHom_ofPiFamily, PowerSeries.map_X]`. Conclude with `hw i.1 i.2`. Establish `hcc : ∀ i : {ζ : LL // IsPrimitiveRoot ζ n}, constantCoeff (piAlgHom (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) X) i = i.1 - 1`. Introduce `i`. Rewrite using `[constantCoeff_piAlgHom]`.

Establish `h : constantCoeff (1 + ρ i.1 X) = constantCoeff (C i.1 * PowerSeries.exp LL)`. Rewrite using `[hρ i.1 i.2]`. Rewrite `h` using `[map_add, map_one, map_mul, constantCoeff_C, hexp0, mul_one]`. Take the linear combination `h`. Establish `hroots : ∀ r : Polynomial LL, Polynomial.aeval (constantCoeff (piAlgHom (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) X)) r = 0 → ((Polynomial.cyclotomic n O).comp (Polynomial.X + 1)).map (algebraMap O LL) ∣ r`.

Introduce `r hr`. Establish `hmap : ((Polynomial.cyclotomic n O).comp (Polynomial.X + 1)).map (algebraMap O LL) = (Polynomial.cyclotomic n LL).comp (Polynomial.X + 1)`. Rewrite using `[Polynomial.map_comp, Polynomial.map_cyclotomic, Polynomial.map_add, Polynomial.map_X, Polynomial.map_one]`. Rewrite using `[hmap]`. Apply `cyclotomic_comp_dvd n hn ζ₀ hζ₀ r` to reduce the goal to its premises.

Introduce `ζ hζ`. Establish `h : (Polynomial.aeval (constantCoeff (piAlgHom (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) X)) r) ⟨ζ, hζ⟩ = 0`. Rewrite using `[hr]`. Both sides reduce to the same expression. Rewrite `h` using `[show (Polynomial.aeval (constantCoeff (piAlgHom (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) X)) r) ⟨ζ, hζ⟩ = Polynomial.aeval (constantCoeff (piAlgHom (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) X) ⟨ζ, hζ⟩) r from (Polynomial.aeval_algHom_apply (Pi.evalAlgHom LL (f …`.

Conclude with `h`. Establish `hXk : (X : PowerSeries ({ζ : LL // IsPrimitiveRoot ζ n} → LL)) ^ k ∣ piAlgHom (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) a` using `(((piSeries LL {ζ : LL // IsPrimitiveRoot ζ n}).2 _).1 k).mpr fun i => by`. Rewrite using `[map_evalRingHom_piAlgHom]`. Conclude with `hk i.1 i.2`. Conclude with `rhoCompl O LL ({ζ : LL // IsPrimitiveRoot ζ n} → LL) _ hP (piAlgHom fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) ⟨hWu.unit, hρP⟩ hroots k a hXk`.
-/
private theorem cyclotomic_comp_pow_dvd_of_X_pow_dvd {O LL : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Field LL] [CharZero LL]
    [Algebra O LL] [IsFractionRing O LL] (n : ℕ) (hn : 0 < n) (ζ₀ : LL)
    (hζ₀ : IsPrimitiveRoot ζ₀ n)
    (hP : ((Polynomial.cyclotomic n O).comp (Polynomial.X + 1)).IsDistinguishedAt (maximalIdeal O))
    (ρ : LL → (PowerSeries O →ₐ[O] PowerSeries LL))
    (hρ : ∀ ζ, IsPrimitiveRoot ζ n → 1 + ρ ζ X = C ζ * PowerSeries.exp LL)
    (k : ℕ) (a : PowerSeries O)
    (hk : ∀ ζ, IsPrimitiveRoot ζ n → (X : PowerSeries LL) ^ k ∣ ρ ζ a) :
    (((Polynomial.cyclotomic n O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) ^ k ∣ a := by
  classical
  have hexp0 := constantCoeff_exp_eq_one LL
  have hcyc : ∀ z : PowerSeries LL, Polynomial.aeval z (Polynomial.cyclotomic n O) =
      Polynomial.aeval z (Polynomial.cyclotomic n LL) := by
    intro z
    first
      | rw [← Polynomial.map_cyclotomic n (algebraMap O LL), Polynomial.aeval_map_algebraMap]
      | rw [← Polynomial.map_cyclotomic_int n O, ← Polynomial.map_cyclotomic_int n LL,
          ← algebraMap_int_eq, ← algebraMap_int_eq, Polynomial.aeval_map_algebraMap,
          Polynomial.aeval_map_algebraMap]
  have hunit : ∀ ζ, IsPrimitiveRoot ζ n → ∃ w : (PowerSeries LL)ˣ,
      ρ ζ (((Polynomial.cyclotomic n O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) =
        (w : PowerSeries LL) * X := by
    intro ζ hζ
    have hroot : Polynomial.aeval ζ (Polynomial.cyclotomic n LL) = 0 := by
      rw [Polynomial.coe_aeval_eq_eval]
      haveI : NeZero (n : LL) := ⟨by exact_mod_cast hn.ne'⟩
      first
        | exact Polynomial.isRoot_cyclotomic_iff.mpr hζ
        | exact Polynomial.isRoot_cyclotomic hn hζ
    obtain ⟨w, hw⟩ := cycloSimple LL LL n hn ζ (PowerSeries.exp LL) hroot hexp0
      (derivative_exp_eq_exp' LL)
    refine ⟨w, ?_⟩
    rw [algHom_coe_eq_aeval, Polynomial.aeval_comp]
    have h1 : Polynomial.aeval (ρ ζ X) (Polynomial.X + 1 : Polynomial O) =
        C ζ * PowerSeries.exp LL := by
      rw [map_add, Polynomial.aeval_X, map_one, add_comm]
      exact hρ ζ hζ
    rw [h1, hcyc]
    exact hw
  choose! w hw using hunit
  have hWu : IsUnit (ofPiFamily fun i : {ζ : LL // IsPrimitiveRoot ζ n} => (w i.1 : PowerSeries LL)) :=
    ((piSeries LL {ζ : LL // IsPrimitiveRoot ζ n}).2 _).2.mpr fun i => by
      rw [map_evalRingHom_ofPiFamily]
      exact (w i.1).isUnit
  have hρP : piAlgHom (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1)
      (((Polynomial.cyclotomic n O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) =
        (hWu.unit : PowerSeries ({ζ : LL // IsPrimitiveRoot ζ n} → LL)) * X := by
    rw [IsUnit.unit_spec]
    apply ext_evalRingHom
    intro i
    rw [map_evalRingHom_piAlgHom, map_mul, map_evalRingHom_ofPiFamily, PowerSeries.map_X]
    exact hw i.1 i.2
  have hcc : ∀ i : {ζ : LL // IsPrimitiveRoot ζ n},
      constantCoeff (piAlgHom (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) X) i = i.1 - 1 := by
    intro i
    rw [constantCoeff_piAlgHom]
    have h : constantCoeff (1 + ρ i.1 X) = constantCoeff (C i.1 * PowerSeries.exp LL) := by
      rw [hρ i.1 i.2]
    rw [map_add, map_one, map_mul, constantCoeff_C, hexp0, mul_one] at h
    linear_combination h
  have hroots : ∀ r : Polynomial LL,
      Polynomial.aeval (constantCoeff (piAlgHom (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) X)) r = 0 →
        ((Polynomial.cyclotomic n O).comp (Polynomial.X + 1)).map (algebraMap O LL) ∣ r := by
    intro r hr
    have hmap : ((Polynomial.cyclotomic n O).comp (Polynomial.X + 1)).map (algebraMap O LL) =
        (Polynomial.cyclotomic n LL).comp (Polynomial.X + 1) := by
      rw [Polynomial.map_comp, Polynomial.map_cyclotomic, Polynomial.map_add, Polynomial.map_X,
        Polynomial.map_one]
    rw [hmap]
    apply cyclotomic_comp_dvd n hn ζ₀ hζ₀ r
    intro ζ hζ
    have h : (Polynomial.aeval (constantCoeff (piAlgHom
        (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) X)) r) ⟨ζ, hζ⟩ = 0 := by
      rw [hr]
      rfl
    rw [show (Polynomial.aeval (constantCoeff (piAlgHom
        (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) X)) r) ⟨ζ, hζ⟩ =
        Polynomial.aeval (constantCoeff (piAlgHom
          (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) X) ⟨ζ, hζ⟩) r from
        (Polynomial.aeval_algHom_apply (Pi.evalAlgHom LL (fun _ : {ζ : LL // IsPrimitiveRoot ζ n} => LL)
          ⟨ζ, hζ⟩) _ r).symm, hcc, Polynomial.coe_aeval_eq_eval] at h
    exact h
  have hXk : (X : PowerSeries ({ζ : LL // IsPrimitiveRoot ζ n} → LL)) ^ k ∣
      piAlgHom (fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) a :=
    (((piSeries LL {ζ : LL // IsPrimitiveRoot ζ n}).2 _).1 k).mpr fun i => by
      rw [map_evalRingHom_piAlgHom]
      exact hk i.1 i.2
  exact rhoCompl O LL ({ζ : LL // IsPrimitiveRoot ζ n} → LL) _ hP
    (piAlgHom fun i : {ζ : LL // IsPrimitiveRoot ζ n} => ρ i.1) ⟨hWu.unit, hρP⟩ hroots k a hXk

/- English proof (translation)
Unfold `SplitComplStatement`. Introduce `O LL _ _ _ _ _ _ _ _ l s hl hlm hζ0 ρ hρ k a hk`. Take `⟨ζ₀, hζ₀⟩` from `hζ0`. Conclude with `cyclotomic_comp_pow_dvd_of_X_pow_dvd (l ^ (s + 1)) (pow_pos hl.pos _) ζ₀ hζ₀ (cycloDist O l s hl hlm) ρ hρ k a hk`.
-/
theorem splitCompl : SplitComplStatement := by
  unfold SplitComplStatement
  intro O LL _ _ _ _ _ _ _ _ l s hl hlm hζ0 ρ hρ k a hk
  obtain ⟨ζ₀, hζ₀⟩ := hζ0
  exact cyclotomic_comp_pow_dvd_of_X_pow_dvd (l ^ (s + 1)) (pow_pos hl.pos _) ζ₀ hζ₀
    (cycloDist O l s hl hlm) ρ hρ k a hk

end LevelStatements.Lv
