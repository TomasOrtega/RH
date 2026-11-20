import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.FiniteNarrowIdeleClassesAndUnitsModSquares
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.MaximalCompactGL2FiniteAdeleCharacterization

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.StabFin

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Establish `hc : IsCompact ((fun k : G => g * k * g⁻¹) '' (K : Set G))` using `hK.image (by fun_prop)`. Take `⟨C, hC⟩` from `hc.elim_finite_subcover (fun c : G => (fun x => x * c⁻¹) ⁻¹' (U : Set G)) (fun c => hU.preimage (by fun_prop)) (fun x _ => Set.mem_iUnion.2 ⟨x, by simp⟩)`. Use `⟨C, fun k hk => ?_⟩` and prove the remaining obligations. Take `⟨c, hc, h⟩` from `Set.mem_iUnion₂.1 (hC ⟨k, hk, rfl⟩)`. Conclude with `⟨c, hc, h⟩`.
-/
theorem cover_gen {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K U : Subgroup G)
    (hK : IsCompact (K : Set G)) (hU : IsOpen (U : Set G)) (g : G) :
    ∃ C : Finset G, ∀ k ∈ K, ∃ c ∈ C, g * k * g⁻¹ * c⁻¹ ∈ U := by
  have hc : IsCompact ((fun k : G => g * k * g⁻¹) '' (K : Set G)) := hK.image (by fun_prop)
  obtain ⟨C, hC⟩ := hc.elim_finite_subcover (fun c : G => (fun x => x * c⁻¹) ⁻¹' (U : Set G))
    (fun c => hU.preimage (by fun_prop)) (fun x _ => Set.mem_iUnion.2 ⟨x, by simp⟩)
  refine ⟨C, fun k hk => ?_⟩
  obtain ⟨c, hc, h⟩ := Set.mem_iUnion₂.1 (hC ⟨k, hk, rfl⟩)
  exact ⟨c, hc, h⟩

/- English proof (translation)
The claim follows from `cover_gen _ _ (isCompact_KLev le_rfl) (isOpen_KLev hN) g`.
-/
theorem cover (g : GL (Fin 2) (Af F)) {N : ℕ} (hN : 0 < N) :
    ∃ C : Finset (GL (Fin 2) (Af F)), ∀ k ∈ KLev F 2 1, ∃ c ∈ C, g * k * g⁻¹ * c⁻¹ ∈ KLev F 2 N :=
  cover_gen _ _ (isCompact_KLev le_rfl) (isOpen_KLev hN) g

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [toFin, Matrix.GeneralLinearGroup.scalar]`.
-/
theorem toFin_scalar (η : Fˣ) : toFin (Matrix.GeneralLinearGroup.scalar (Fin 2) η) =
    Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap F (Af F)).toMonoidHom η) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toFin, Matrix.GeneralLinearGroup.scalar]

/- English proof (translation)
Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem det_toFin (δ : GL (Fin 2) F) : (toFin δ).val.det = algebraMap F (Af F) δ.val.det := by
  rw [RingHom.map_det]; rfl

/- English proof (translation)
Establish `H` using `(GlobalTheory.T.maximalCompactGL2_finiteAdele_characterization F).2.2.2.2`. Establish `h1 : IsIntegral ℤ x` using `(H x).1 fun w => (h w).le`. Establish `h2 : IsIntegral ℤ x⁻¹` using `(H _).1 fun w => by rw [map_inv₀, h w, inv_one]`. Use `⟨⟨⟨x, h1⟩, ⟨x⁻¹, h2⟩, ?_, ?_⟩, rfl⟩` and prove the remaining obligations. Conclude with `Subtype.ext (mul_inv_cancel₀ hx)`.

Conclude with `Subtype.ext (inv_mul_cancel₀ hx)`.
-/
theorem exists_unit {x : F} (h : ∀ w : HeightOneSpectrum (𝓞 F), w.valuation F x = 1) (hx : x ≠ 0) :
    ∃ ε : (𝓞 F)ˣ, ((ε : 𝓞 F) : F) = x := by
  have H := (GlobalTheory.T.maximalCompactGL2_finiteAdele_characterization F).2.2.2.2
  have h1 : IsIntegral ℤ x := (H x).1 fun w => (h w).le
  have h2 : IsIntegral ℤ x⁻¹ := (H _).1 fun w => by rw [map_inv₀, h w, inv_one]
  refine ⟨⟨⟨x, h1⟩, ⟨x⁻¹, h2⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (mul_inv_cancel₀ hx)
  · exact Subtype.ext (inv_mul_cancel₀ hx)

/- English proof (translation)
Take `⟨H1, -, -, H4, -⟩` from `GlobalTheory.T.maximalCompactGL2_finiteAdele_characterization F`. Use `exists_unit (fun w => ?_) δ.det_ne_zero` and prove the remaining obligations. Establish `e : (toFin δ).val.det = k.val.det`. Rewrite using `[h, Units.val_mul, Units.val_mul, Matrix.det_units_conj]`. Rewrite using `[← H4, ← det_toFin, e]`.

Conclude with `((H1 k).1 hk).2 w`.
-/
theorem det_unit {g k : GL (Fin 2) (Af F)} (hk : k ∈ KLev F 2 1) {δ : GL (Fin 2) F} (h : toFin δ = g * k * g⁻¹) :
    ∃ ε : (𝓞 F)ˣ, ((ε : 𝓞 F) : F) = δ.val.det := by
  obtain ⟨H1, -, -, H4, -⟩ := GlobalTheory.T.maximalCompactGL2_finiteAdele_characterization F
  refine exists_unit (fun w => ?_) δ.det_ne_zero
  have e : (toFin δ).val.det = k.val.det := by
    rw [h, Units.val_mul, Units.val_mul, Matrix.det_units_conj]
  rw [← H4, ← det_toFin, e]
  exact ((H1 k).1 hk).2 w

/- English proof (translation)
Take `⟨-, -, -, H4, H5⟩` from `GlobalTheory.T.maximalCompactGL2_finiteAdele_characterization F`. Use `(H5 x).1 fun w => ?_` and prove the remaining obligations. Rewrite using `[← H4]`. Conclude with `(Subring.mem_iInf.1 h w : pLoc F w (algebraMap F (Af F) x) ∈ w.adicCompletionIntegers F)`.
-/
theorem integral_of_mem {x : F} (h : algebraMap F (Af F) x ∈ Ohat F) : IsIntegral ℤ x := by
  obtain ⟨-, -, -, H4, H5⟩ := GlobalTheory.T.maximalCompactGL2_finiteAdele_characterization F
  refine (H5 x).1 fun w => ?_
  rw [← H4]
  exact (Subring.mem_iInf.1 h w : pLoc F w (algebraMap F (Af F) x) ∈ w.adicCompletionIntegers F)

/- English proof (translation)
Take `⟨h1, -, h3⟩` from `mem_KLev.1 h`. Use `⟨hd, integral_of_mem (h1 0 0), integral_of_mem (h1 0 1), integral_of_mem ?_, integral_of_mem (h1 1 1)⟩` and prove the remaining obligations. Take `⟨y, hy, e⟩` from `h3 1 0`. Establish `hN' : (N : F) ≠ 0` using `Nat.cast_ne_zero.2 hN.ne'`. Establish `e' : algebraMap F (Af F) (γ.val 1 0) = (N : Af F) * y`.

Rewrite using `[← e]`. Simplify using `[toFin]`. Establish `: algebraMap F (Af F) (γ.val 1 0 / N) = y`. Rewrite using `[div_eq_inv_mul, map_mul, e', ← mul_assoc, ← map_natCast (algebraMap F (Af F)), ← map_mul, inv_mul_cancel₀ hN', map_one, one_mul]`. Rewrite using `[this]` and apply the resulting hypothesis.
-/
theorem inGam_of_mem {N : ℕ} (hN : 0 < N) {γ : GL (Fin 2) F} (hd : γ.val.det = 1) (h : toFin γ ∈ KLev F 2 N) :
    InGam N γ := by
  obtain ⟨h1, -, h3⟩ := mem_KLev.1 h
  refine ⟨hd, integral_of_mem (h1 0 0), integral_of_mem (h1 0 1), integral_of_mem ?_, integral_of_mem (h1 1 1)⟩
  obtain ⟨y, hy, e⟩ := h3 1 0
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have e' : algebraMap F (Af F) (γ.val 1 0) = (N : Af F) * y := by
    rw [← e]; simp [toFin]
  have : algebraMap F (Af F) (γ.val 1 0 / N) = y := by
    rw [div_eq_inv_mul, map_mul, e', ← mul_assoc, ← map_natCast (algebraMap F (Af F)), ← map_mul,
      inv_mul_cancel₀ hN', map_one, one_mul]
  rwa [this]

/- English proof (translation)
Take `⟨-, H2, -, H4, -⟩` from `GlobalTheory.T.maximalCompactGL2_finiteAdele_characterization F`. Use `(H2 _ 0 (fun w => ?_) (fun w => by simp)).2` and prove the remaining obligations. Use `(H4 (algebraMap (𝓞 F) F ε) w).trans ?_` and prove the remaining obligations. Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `HeightOneSpectrum.intValuation_eq_one_iff.2 fun h => w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h ε.isUnit)`.
-/
theorem unit_scalar_mem (ε : (𝓞 F)ˣ) : Matrix.GeneralLinearGroup.scalar (Fin 2)
    (Units.map (algebraMap F (Af F)).toMonoidHom (Units.map (algebraMap (𝓞 F) F).toMonoidHom ε)) ∈ KLev F 2 1 := by
  obtain ⟨-, H2, -, H4, -⟩ := GlobalTheory.T.maximalCompactGL2_finiteAdele_characterization F
  refine (H2 _ 0 (fun w => ?_) (fun w => by simp)).2
  refine (H4 (algebraMap (𝓞 F) F ε) w).trans ?_
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_eq_one_iff.2 fun h => w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h ε.isUnit)

/- English proof (translation)
Take `⟨⟨Y, hY⟩, E, hE⟩` from `GlobalTheory.T.finite_narrowIdeleClasses_and_units_mod_squares F`. Take `⟨C, hC⟩` from `cover g hN`. Establish `hb : ∀ y : (Af F)ˣ, ∃ b : GL (Fin 2) F, ∀ δ : GL (Fin 2) F, ∀ k ∈ KLev F 2 1, toFin δ = Matrix.GeneralLinearGroup.scalar (Fin 2) y * (g * k * g⁻¹) → ∃ k' ∈ KLev F 2 1, toFin (δ * b⁻¹) = g * k' * g⁻¹` using `fun y => by`. Distinguish the cases in `h : ∃ b : GL (Fin 2) F, ∃ k ∈ KLev F 2 1, toFin b = Matrix.GeneralLinearGroup.scalar (Fin 2) y * (g * k * g⁻¹)`. Take `⟨b, k₀, hk₀, e⟩` from `h`.

Use `⟨b, fun δ k hk e' => ⟨k * k₀⁻¹, mul_mem hk (inv_mem hk₀), ?_⟩⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_inv, e, e', Matrix.GeneralLinearGroup.scalar_commute y, Matrix.GeneralLinearGroup.scalar_commute y]`. Use `group`. Conclude with `⟨1, fun δ k hk e => absurd ⟨δ, k, hk, e⟩ h⟩`. Use `choose b hb using hb`.

Use `⟨(Y ×ˢ E ×ˢ C).image fun t => (((t.2.1 : 𝓞 F) : F) * (b t.1).val.det, t.2.2 * toFin (b t.1)), ?_⟩` and prove the remaining obligations. Introduce and unpack `γ ⟨-, z, u, hu, e⟩`. Take `⟨y, hy, ξ, v, -, hv, rfl⟩` from `hY z`. Establish `hvK` using `((GlobalTheory.T.maximalCompactGL2_finiteAdele_characterization F).2.1 v 0 hv (fun w => by simp)).2`. Take `⟨k, hk, ek⟩` from `hb y (Matrix.GeneralLinearGroup.scalar (Fin 2) ξ⁻¹ * γ) _ (mul_mem hvK hu) (by`.

Rewrite using `[map_mul, eq_mul_inv_of_mul_eq e, map_inv, map_inv, toFin_scalar, map_mul, map_mul, ← mul_assoc g, ← Matrix.GeneralLinearGroup.scalar_commute v g]`. Use the proof step `group)`. Take `⟨ε, hε⟩` from `det_unit hk ek`. Take `⟨e₀, he₀, η, rfl⟩` from `hE ε`. Take `⟨c, hc, hcK⟩` from `hC _ (mul_mem (unit_scalar_mem η⁻¹) hk)`.

Use `⟨_, Finset.mem_image.2 ⟨(y, e₀, c), by simp [hy, he₀, hc], rfl⟩, Units.map (algebraMap (𝓞 F) F).toMonoidHom η⁻¹ * ξ⁻¹, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : (Matrix.GeneralLinearGroup.scalar (Fin 2) ξ⁻¹ * γ).val.det = ((e₀ * η ^ 2 : (𝓞 F)ˣ) : 𝓞 F) * (b y).val.det`. Rewrite using `[hε, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel_right]`. Rewrite using `[map_mul, mul_assoc, Units.val_mul, Matrix.det_mul, h1, ← Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.det_scalar]`. Establish `hη : ((η : 𝓞 F) : F) ≠ 0` using `by simp`.

Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Use `hcK using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_mul (Matrix.GeneralLinearGroup.scalar (Fin 2)), mul_assoc _ _ γ, map_mul toFin, toFin_scalar, ← mul_assoc g, ← Matrix.GeneralLinearGroup.scalar_commute _ g, mul_assoc _ g k, mul_assoc _ (g * k), ← ek, map_mul toFin _ (b y)⁻¹, map_inv toFin]`. Use `group`.
-/
theorem invariants [IsTotallyReal F] (g : GL (Fin 2) (Af F)) {N : ℕ} (hN : 0 < N) :
    ∃ I : Finset (F × GL (Fin 2) (Af F)), ∀ γ, Stab g γ → ∃ i ∈ I, ∃ η : Fˣ,
      (Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ).val.det = i.1 ∧
        toFin (Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ) * i.2⁻¹ ∈ KLev F 2 N := by
  classical
  obtain ⟨⟨Y, hY⟩, E, hE⟩ := GlobalTheory.T.finite_narrowIdeleClasses_and_units_mod_squares F
  obtain ⟨C, hC⟩ := cover g hN
  have hb : ∀ y : (Af F)ˣ, ∃ b : GL (Fin 2) F, ∀ δ : GL (Fin 2) F, ∀ k ∈ KLev F 2 1,
      toFin δ = Matrix.GeneralLinearGroup.scalar (Fin 2) y * (g * k * g⁻¹) →
        ∃ k' ∈ KLev F 2 1, toFin (δ * b⁻¹) = g * k' * g⁻¹ := fun y => by
    by_cases h : ∃ b : GL (Fin 2) F, ∃ k ∈ KLev F 2 1,
      toFin b = Matrix.GeneralLinearGroup.scalar (Fin 2) y * (g * k * g⁻¹)
    · obtain ⟨b, k₀, hk₀, e⟩ := h
      refine ⟨b, fun δ k hk e' => ⟨k * k₀⁻¹, mul_mem hk (inv_mem hk₀), ?_⟩⟩
      rw [map_mul, map_inv, e, e', Matrix.GeneralLinearGroup.scalar_commute y,
        Matrix.GeneralLinearGroup.scalar_commute y]
      group
    · exact ⟨1, fun δ k hk e => absurd ⟨δ, k, hk, e⟩ h⟩
  choose b hb using hb
  refine ⟨(Y ×ˢ E ×ˢ C).image fun t => (((t.2.1 : 𝓞 F) : F) * (b t.1).val.det, t.2.2 * toFin (b t.1)), ?_⟩
  rintro γ ⟨-, z, u, hu, e⟩
  obtain ⟨y, hy, ξ, v, -, hv, rfl⟩ := hY z
  have hvK := ((GlobalTheory.T.maximalCompactGL2_finiteAdele_characterization F).2.1 v 0 hv (fun w => by simp)).2
  obtain ⟨k, hk, ek⟩ := hb y (Matrix.GeneralLinearGroup.scalar (Fin 2) ξ⁻¹ * γ) _ (mul_mem hvK hu) (by
    rw [map_mul, eq_mul_inv_of_mul_eq e, map_inv, map_inv, toFin_scalar, map_mul, map_mul, ← mul_assoc g,
      ← Matrix.GeneralLinearGroup.scalar_commute v g]
    group)
  obtain ⟨ε, hε⟩ := det_unit hk ek
  obtain ⟨e₀, he₀, η, rfl⟩ := hE ε
  obtain ⟨c, hc, hcK⟩ := hC _ (mul_mem (unit_scalar_mem η⁻¹) hk)
  refine ⟨_, Finset.mem_image.2 ⟨(y, e₀, c), by simp [hy, he₀, hc], rfl⟩,
    Units.map (algebraMap (𝓞 F) F).toMonoidHom η⁻¹ * ξ⁻¹, ?_, ?_⟩
  · have h1 : (Matrix.GeneralLinearGroup.scalar (Fin 2) ξ⁻¹ * γ).val.det =
        ((e₀ * η ^ 2 : (𝓞 F)ˣ) : 𝓞 F) * (b y).val.det := by
      rw [hε, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel_right]
    rw [map_mul, mul_assoc, Units.val_mul, Matrix.det_mul, h1, ← Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.GeneralLinearGroup.det_scalar]
    have hη : ((η : 𝓞 F) : F) ≠ 0 := by simp
    simp
    field_simp
  · convert hcK using 1
    rw [map_mul (Matrix.GeneralLinearGroup.scalar (Fin 2)), mul_assoc _ _ γ, map_mul toFin, toFin_scalar, ← mul_assoc g, ← Matrix.GeneralLinearGroup.scalar_commute _ g,
      mul_assoc _ g k, mul_assoc _ (g * k), ← ek, map_mul toFin _ (b y)⁻¹, map_inv toFin]
    group

/- English proof (translation)
Introduce `F _ _ _ g N hN`. Take `⟨I, hI⟩` from `invariants g hN`. Set `P : GL (Fin 2) F → F × GL (Fin 2) (Af F) → Prop` to `fun γ i => Stab g γ ∧ ∃ η : Fˣ, (Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ).val.det = i.1 ∧ toFin (Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ) * i.2⁻¹ ∈ KLev F 2 N`. Establish `hr : ∀ i, ∃ τ, (∃ γ, P γ i) → P τ i` using `fun i => by`. Distinguish the cases in `h : ∃ γ, P γ i`.

Conclude with `⟨h.choose, fun _ => h.choose_spec⟩`. Conclude with `⟨1, fun h' => absurd h' h⟩`. Use `choose r hr using hr`. Use `⟨(I.filter fun i => ∃ γ, P γ i).image r, fun τ hτ => ?_, fun γ hγ => ?_⟩` and prove the remaining obligations. Take `⟨i, hi, rfl⟩` from `Finset.mem_image.1 hτ`.

Conclude with `(hr i (Finset.mem_filter.1 hi).2).1`. Take `⟨i, hi, η, h1, h2⟩` from `hI γ hγ`. Establish `hP : ∃ γ, P γ i` using `⟨γ, hγ, η, h1, h2⟩`. Take `⟨-, η', h1', h2'⟩` from `hr i hP`. Use `⟨η⁻¹ * η', Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ * (Matrix.GeneralLinearGroup.scalar (Fin 2) η' * r i)⁻¹, r i, Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hi, hP⟩), inGam_of_mem hN ?_ ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Units.val_mul, Matrix.det_mul, h1, ← h1', ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]`. Use `mul_mem h2 (inv_mem h2') using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_mul toFin (_ * γ), map_inv]`. Use `group`. Rewrite using `[mul_comm η⁻¹, map_mul, map_inv, Matrix.GeneralLinearGroup.scalar_commute η' (r i), mul_assoc, mul_assoc, Matrix.GeneralLinearGroup.scalar_commute η']`.

Rewrite using `[← Matrix.GeneralLinearGroup.scalar_commute η' (r i), mul_assoc, mul_assoc, mul_assoc, ← Matrix.GeneralLinearGroup.scalar_commute η' (r i)]`. Use `group`.
-/
theorem finite_index : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (g : GL (Fin 2) (Af F)) (N : ℕ), 0 < N → ∃ T : Finset (GL (Fin 2) F), (∀ τ ∈ T, Stab g τ) ∧ ∀ γ, Stab g γ → ∃ (η : Fˣ) (γ₀ : GL (Fin 2) F), ∃ τ ∈ T, InGam N γ₀ ∧ γ = Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ₀ * τ := by
  classical
  intro F _ _ _ g N hN
  obtain ⟨I, hI⟩ := invariants g hN
  let P : GL (Fin 2) F → F × GL (Fin 2) (Af F) → Prop := fun γ i => Stab g γ ∧ ∃ η : Fˣ,
      (Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ).val.det = i.1 ∧
        toFin (Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ) * i.2⁻¹ ∈ KLev F 2 N
  have hr : ∀ i, ∃ τ, (∃ γ, P γ i) → P τ i := fun i => by
    by_cases h : ∃ γ, P γ i
    · exact ⟨h.choose, fun _ => h.choose_spec⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose r hr using hr
  refine ⟨(I.filter fun i => ∃ γ, P γ i).image r, fun τ hτ => ?_, fun γ hγ => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hτ
    exact (hr i (Finset.mem_filter.1 hi).2).1
  · obtain ⟨i, hi, η, h1, h2⟩ := hI γ hγ
    have hP : ∃ γ, P γ i := ⟨γ, hγ, η, h1, h2⟩
    obtain ⟨-, η', h1', h2'⟩ := hr i hP
    refine ⟨η⁻¹ * η', Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ *
      (Matrix.GeneralLinearGroup.scalar (Fin 2) η' * r i)⁻¹, r i,
      Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hi, hP⟩), inGam_of_mem hN ?_ ?_, ?_⟩
    · rw [Units.val_mul, Matrix.det_mul, h1, ← h1', ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.det_one]
    · convert mul_mem h2 (inv_mem h2') using 1
      rw [map_mul toFin (_ * γ), map_inv]
      group
    · rw [mul_comm η⁻¹, map_mul, map_inv, Matrix.GeneralLinearGroup.scalar_commute η' (r i), mul_assoc, mul_assoc,
        Matrix.GeneralLinearGroup.scalar_commute η']
      rw [← Matrix.GeneralLinearGroup.scalar_commute η' (r i), mul_assoc, mul_assoc, mul_assoc, ← Matrix.GeneralLinearGroup.scalar_commute η' (r i)]
      group

end GlobalTheory.HilbertThetaSeries.StabFin

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.HilbertThetaSeries.StabFin.finite_index | exact GlobalTheory.HilbertThetaSeries.StabFin.finite_index | (intros; apply GlobalTheory.HilbertThetaSeries.StabFin.finite_index <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.stabilizer_eq_scalar_mul_congruence_mul_finset : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (g : GL (Fin 2) (Af F)) (N : ℕ), 0 < N → ∃ T : Finset (GL (Fin 2) F), (∀ τ ∈ T, Stab g τ) ∧ ∀ γ, Stab g γ → ∃ (η : Fˣ) (γ₀ : GL (Fin 2) F), ∃ τ ∈ T, InGam N γ₀ ∧ γ = Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ₀ * τ := by
  first | exact @GlobalTheory.HilbertThetaSeries.StabFin.finite_index | exact GlobalTheory.HilbertThetaSeries.StabFin.finite_index | (intros; apply GlobalTheory.HilbertThetaSeries.StabFin.finite_index <;> assumption)
