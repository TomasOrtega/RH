import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOne
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section
namespace GlobalTheory.TwV.Xc.ClsPow

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Set `a : Neutral.B1.Ideles E` to `⟨((1 : InfiniteAdeleRing E), (y : FiniteAdeleRing (𝓞 E) E)), ((1 : InfiniteAdeleRing E), ((y⁻¹ : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E)), Prod.ext (mul_one _) y.mul_inv, Prod.ext (mul_one _) y.inv_mul⟩`. Establish `hc : ReciprocityTheory.Neutral.Bridge.HCFR.classOf E (a ^ Fintype.card (ClassGroup (𝓞 E))) = 1`. Rewrite using `[map_pow, pow_card_eq_one]`. Take `⟨k, u, hu, he⟩` from `(ReciprocityTheory.Neutral.Bridge.HCFR.classOf_eq_one_iff E _).1 hc`. Use `⟨k, ⟨(u : AdeleRing (𝓞 E) E).2, ((u⁻¹ : Neutral.B1.Ideles E) : AdeleRing (𝓞 E) E).2, ?_, ?_⟩, fun P => (hu.2 P).1, ?_⟩` and prove the remaining obligations.

Conclude with `congrArg Prod.snd u.mul_inv`. Conclude with `congrArg Prod.snd u.inv_mul`. Apply `Units.ext` to reduce the goal to its premises. Establish `h2 : ((a ^ Fintype.card (ClassGroup (𝓞 E)) : Neutral.B1.Ideles E) : AdeleRing (𝓞 E) E).2 = ((Neutral.B1.diagUnits E k * u : Neutral.B1.Ideles E) : AdeleRing (𝓞 E) E).2` using `by rw [he]`. Establish `h3 : ∀ (t : Neutral.B1.Ideles E) (n : ℕ), ((t ^ n : Neutral.B1.Ideles E) : AdeleRing (𝓞 E) E).2 = ((t : AdeleRing (𝓞 E) E).2) ^ n`.

Introduce `t n`. Proceed by induction on `n with`. Consider the case `zero => rfl`. Consider the case `succ n ih => rw [pow_succ, pow_succ, ← ih]`. Both sides reduce to the same expression.

Rewrite `h2` using `[h3]`. Rewrite using `[Units.val_pow_eq_pow_val]`. Conclude with `h2.trans rfl`.
-/
theorem exists_pow_eq_diag_mul (y : (FiniteAdeleRing (𝓞 E) E)ˣ) :
    ∃ (k : Eˣ) (u : (FiniteAdeleRing (𝓞 E) E)ˣ),
      (∀ P : HeightOneSpectrum (𝓞 E), Valued.v ((u : FiniteAdeleRing (𝓞 E) E) P) = 1) ∧
      y ^ Fintype.card (ClassGroup (𝓞 E)) = Units.map (algebraMap E (FiniteAdeleRing (𝓞 E) E)).toMonoidHom k * u := by
  classical
  let a : Neutral.B1.Ideles E := ⟨((1 : InfiniteAdeleRing E), (y : FiniteAdeleRing (𝓞 E) E)),
    ((1 : InfiniteAdeleRing E), ((y⁻¹ : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E)),
    Prod.ext (mul_one _) y.mul_inv, Prod.ext (mul_one _) y.inv_mul⟩
  have hc : ReciprocityTheory.Neutral.Bridge.HCFR.classOf E (a ^ Fintype.card (ClassGroup (𝓞 E))) = 1 := by
    rw [map_pow, pow_card_eq_one]
  obtain ⟨k, u, hu, he⟩ := (ReciprocityTheory.Neutral.Bridge.HCFR.classOf_eq_one_iff E _).1 hc
  refine ⟨k, ⟨(u : AdeleRing (𝓞 E) E).2, ((u⁻¹ : Neutral.B1.Ideles E) : AdeleRing (𝓞 E) E).2, ?_, ?_⟩, fun P => (hu.2 P).1, ?_⟩
  · exact congrArg Prod.snd u.mul_inv
  · exact congrArg Prod.snd u.inv_mul
  · apply Units.ext
    have h2 : ((a ^ Fintype.card (ClassGroup (𝓞 E)) : Neutral.B1.Ideles E) : AdeleRing (𝓞 E) E).2 =
        ((Neutral.B1.diagUnits E k * u : Neutral.B1.Ideles E) : AdeleRing (𝓞 E) E).2 := by rw [he]
    have h3 : ∀ (t : Neutral.B1.Ideles E) (n : ℕ), ((t ^ n : Neutral.B1.Ideles E) : AdeleRing (𝓞 E) E).2 = ((t : AdeleRing (𝓞 E) E).2) ^ n := by
      intro t n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, pow_succ, ← ih]; rfl
    rw [h3] at h2
    rw [Units.val_pow_eq_pow_val]
    exact h2.trans rfl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨ι, h1, h2⟩` from `GlobalTheory.TwU.exists_isAdIso F E`. Take `⟨a, u, hu, he⟩` from `exists_pow_eq_diag_mul (Units.map ι.toRingHom.toMonoidHom x)`. Establish `hinv : ∀ P : HeightOneSpectrum (𝓞 E), Valued.v (((u⁻¹ : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) P) = 1`. Introduce `P`. Establish `e : (((u⁻¹ : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) P) * ((u : FiniteAdeleRing (𝓞 E) E) P) = 1`.

Conclude with `congrArg (fun t : FiniteAdeleRing (𝓞 E) E => t P) (Units.inv_mul u)`. Establish `e2` using `congrArg Valued.v e`. Rewrite `e2` using `[map_mul, hu P, mul_one, map_one]`. Conclude with `e2`. Use `⟨a, Units.map ι.symm.toRingHom.toMonoidHom u, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[intU, Submonoid.mem_units_iff]`. Prove the components needed by the constructor for the conclusion. Use `show ι.symm (u : FiniteAdeleRing (𝓞 E) E) ∈ RInt F E`. Rewrite using `[h2]`. Introduce `P`.

Rewrite using `[RingEquiv.apply_symm_apply, hu P]`. Use `show ι.symm ((u⁻¹ : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) ∈ RInt F E`. Rewrite using `[h2]`. Introduce `P`. Rewrite using `[RingEquiv.apply_symm_apply, hinv P]`.

Apply `Units.ext` to reduce the goal to its premises. Apply `ι.injective` to reduce the goal to its premises. Establish `e` using `congrArg (fun t : (FiniteAdeleRing (𝓞 E) E)ˣ => (t : FiniteAdeleRing (𝓞 E) E)) he`. Simplify using `only [Units.val_pow_eq_pow_val, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at e`. Rewrite using `[Units.val_pow_eq_pow_val, map_pow, e, Units.val_mul, map_mul]`.

Simplify using `only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply]`. Use `congr 1`. Rewrite using `[ratId, Units.coe_map]`. Use `show _ = ι (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) (a : E))`. Rewrite using `[inclE, Algebra.TensorProduct.includeLeftRingHom_apply, h1]`.
-/
theorem exists_pow_eq_ratId_mul (x : (AfE F E)ˣ) :
    ∃ (a : Eˣ) (k : (AfE F E)ˣ), k ∈ intU F E ∧ x ^ Fintype.card (ClassGroup (𝓞 E)) = ratId F E a * k := by
  obtain ⟨ι, h1, h2⟩ := GlobalTheory.TwU.exists_isAdIso F E
  obtain ⟨a, u, hu, he⟩ := exists_pow_eq_diag_mul (Units.map ι.toRingHom.toMonoidHom x)
  have hinv : ∀ P : HeightOneSpectrum (𝓞 E), Valued.v (((u⁻¹ : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) P) = 1 := by
    intro P
    have e : (((u⁻¹ : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) P) * ((u : FiniteAdeleRing (𝓞 E) E) P) = 1 := by
      exact congrArg (fun t : FiniteAdeleRing (𝓞 E) E => t P) (Units.inv_mul u)
    have e2 := congrArg Valued.v e
    rw [map_mul, hu P, mul_one, map_one] at e2
    exact e2
  refine ⟨a, Units.map ι.symm.toRingHom.toMonoidHom u, ?_, ?_⟩
  · rw [intU, Submonoid.mem_units_iff]
    constructor
    · show ι.symm (u : FiniteAdeleRing (𝓞 E) E) ∈ RInt F E
      rw [h2]
      intro P
      rw [RingEquiv.apply_symm_apply, hu P]
    · show ι.symm ((u⁻¹ : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) ∈ RInt F E
      rw [h2]
      intro P
      rw [RingEquiv.apply_symm_apply, hinv P]
  · apply Units.ext
    apply ι.injective
    have e := congrArg (fun t : (FiniteAdeleRing (𝓞 E) E)ˣ => (t : FiniteAdeleRing (𝓞 E) E)) he
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at e
    rw [Units.val_pow_eq_pow_val, map_pow, e, Units.val_mul, map_mul]
    simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.apply_symm_apply]
    congr 1
    rw [ratId, Units.coe_map]
    show _ = ι (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) (a : E))
    rw [inclE, Algebra.TensorProduct.includeLeftRingHom_apply, h1]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Simplify using `[conjId, ratId, sigR, inclE]`.
-/
theorem conjId_ratId (σ : E →ₐ[F] E) (a : Eˣ) :
    conjId σ (ratId F E a) = ratId F E (Units.map (σ : E →+* E).toMonoidHom a) := by
  apply Units.ext
  simp [conjId, ratId, sigR, inclE]

/- English proof (translation)
Establish `hle : RInt F E ≤ (RInt F E).comap (sigR σ (FiniteAdeleRing (𝓞 F) F))`. Use `(Subring.closure_le).2 ?_` and prove the remaining obligations. Introduce and unpack `g (⟨⟨e, ⟨b, rfl⟩⟩, rfl⟩ | ⟨c, rfl⟩)`. Use `Subring.subset_closure (Or.inl ⟨⟨σ (algebraMap (𝓞 E) E b), ⟨RingOfIntegers.mapRingHom (σ : E →+* E) b, ?_⟩⟩, ?_⟩)` and prove the remaining obligations. Both sides reduce to the same expression.

Simplify using `[sigR]`. Use `Subring.subset_closure (Or.inr ⟨c, ?_⟩)` and prove the remaining obligations. Simplify using `[sigR]`. Conclude with `hle hy`.
-/
theorem sigR_mem_RInt (σ : E →ₐ[F] E) {y : AfE F E} (hy : y ∈ RInt F E) :
    sigR σ (FiniteAdeleRing (𝓞 F) F) y ∈ RInt F E := by
  have hle : RInt F E ≤ (RInt F E).comap (sigR σ (FiniteAdeleRing (𝓞 F) F)) := by
    refine (Subring.closure_le).2 ?_
    rintro g (⟨⟨e, ⟨b, rfl⟩⟩, rfl⟩ | ⟨c, rfl⟩)
    · refine Subring.subset_closure (Or.inl ⟨⟨σ (algebraMap (𝓞 E) E b), ⟨RingOfIntegers.mapRingHom (σ : E →+* E) b, ?_⟩⟩, ?_⟩)
      · rfl
      · simp [sigR]
    · refine Subring.subset_closure (Or.inr ⟨c, ?_⟩)
      simp [sigR]
  exact hle hy

/- English proof (translation)
Rewrite `hk`, the goal using `[intU, Submonoid.mem_units_iff]`. Use `⟨sigR_mem_RInt σ hk.1, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_inv]`. Conclude with `sigR_mem_RInt σ hk.2`.
-/
theorem conjId_mem_intU (σ : E →ₐ[F] E) {k : (AfE F E)ˣ} (hk : k ∈ intU F E) : conjId σ k ∈ intU F E := by
  rw [intU, Submonoid.mem_units_iff] at hk ⊢
  refine ⟨sigR_mem_RInt σ hk.1, ?_⟩
  rw [← map_inv]
  exact sigR_mem_RInt σ hk.2

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use `show sigR σ (FiniteAdeleRing (𝓞 F) F) (sigR σ (FiniteAdeleRing (𝓞 F) F) (k : AfE F E)) = k`. Proceed by induction on `(k : AfE F E) using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul e c => simp [sigR, hσ]`.

Consider the case `add s t hs ht => rw [map_add, map_add, hs, ht]`.
-/
theorem conjId_conjId (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (k : (AfE F E)ˣ) : conjId σ (conjId σ k) = k := by
  apply Units.ext
  show sigR σ (FiniteAdeleRing (𝓞 F) F) (sigR σ (FiniteAdeleRing (𝓞 F) F) (k : AfE F E)) = k
  induction (k : AfE F E) using TensorProduct.induction_on with
  | zero => simp
  | tmul e c => simp [sigR, hσ]
  | add s t hs ht => rw [map_add, map_add, hs, ht]

/- English proof (translation)
Take `⟨a, k₀, hk₀, he⟩` from `exists_pow_eq_ratId_mul (F := F) x`. Use `set h := Fintype.card (ClassGroup (𝓞 E))`. Establish `hx' : x * conjId σ x = 1`. Rewrite `hx` using `[U1, MonoidHom.mem_ker]`. Conclude with `hx`.

Establish `hw : x ^ h * conjId σ (x ^ h) = 1` using `by rw [map_pow, ← mul_pow, hx', one_pow]`. Establish `hw' : x ^ h = (conjId σ (x ^ h))⁻¹` using `eq_inv_of_mul_eq_one_left hw`. Set `sa : Eˣ` to `Units.map (σ : E →+* E).toMonoidHom a`. Use `⟨2 * h, a * sa⁻¹, k₀ * (conjId σ k₀)⁻¹, Nat.mul_pos two_pos Fintype.card_pos, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `ha : (a : E) ≠ 0` using `a.ne_zero`.

Establish `hsa : σ (a : E) ≠ 0`. Introduce `h0`. Apply `ha` to reduce the goal to its premises. Rewrite using `[← hσ (a : E), h0, map_zero]`. Simplify using `only [sa, Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, AlgHom.coe_toRingHom, RingHom.coe_coe, map_mul, map_inv₀, hσ]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[U1, MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.id_apply, map_mul, map_inv, conjId_conjId σ hσ]`. Rewrite using `[mul_assoc, inv_mul_cancel_left, mul_inv_cancel]`. Conclude with `mul_mem hk₀ (inv_mem (conjId_mem_intU σ hk₀))`. Establish `hc : conjId σ (x ^ h) = ratId F E sa * conjId σ k₀` using `by rw [he, map_mul, conjId_ratId]`.

Rewrite using `[mul_comm 2 h, pow_mul, sq]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hc, he, map_mul, map_inv, mul_inv]`. The two sides agree by associativity and commutativity.
-/
theorem normOne_idele_pow_eq_normOne_principal_mul_unit (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (x : (AfE F E)ˣ) (hx : x ∈ U1 σ) :
    ∃ (m : ℕ) (z : Eˣ) (k : (AfE F E)ˣ), 0 < m ∧ (z : E) * σ (z : E) = 1 ∧ k ∈ U1 σ ∧ k ∈ intU F E ∧
      x ^ m = ratId F E z * k := by
  classical
  obtain ⟨a, k₀, hk₀, he⟩ := exists_pow_eq_ratId_mul (F := F) x
  set h := Fintype.card (ClassGroup (𝓞 E))
  have hx' : x * conjId σ x = 1 := by
    rw [U1, MonoidHom.mem_ker] at hx
    exact hx
  have hw : x ^ h * conjId σ (x ^ h) = 1 := by rw [map_pow, ← mul_pow, hx', one_pow]
  have hw' : x ^ h = (conjId σ (x ^ h))⁻¹ := eq_inv_of_mul_eq_one_left hw
  let sa : Eˣ := Units.map (σ : E →+* E).toMonoidHom a
  refine ⟨2 * h, a * sa⁻¹, k₀ * (conjId σ k₀)⁻¹, Nat.mul_pos two_pos Fintype.card_pos, ?_, ?_, ?_, ?_⟩
  · have ha : (a : E) ≠ 0 := a.ne_zero
    have hsa : σ (a : E) ≠ 0 := by
      intro h0
      apply ha
      rw [← hσ (a : E), h0, map_zero]
    simp only [sa, Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
      AlgHom.coe_toRingHom, RingHom.coe_coe, map_mul, map_inv₀, hσ]
    field_simp
  · rw [U1, MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.id_apply, map_mul, map_inv, conjId_conjId σ hσ]
    rw [mul_assoc, inv_mul_cancel_left, mul_inv_cancel]
  · exact mul_mem hk₀ (inv_mem (conjId_mem_intU σ hk₀))
  · have hc : conjId σ (x ^ h) = ratId F E sa * conjId σ k₀ := by rw [he, map_mul, conjId_ratId]
    rw [mul_comm 2 h, pow_mul, sq]
    calc x ^ h * x ^ h = x ^ h * (conjId σ (x ^ h))⁻¹ := by rw [← hw']
      _ = ratId F E (a * sa⁻¹) * (k₀ * (conjId σ k₀)⁻¹) := by
        rw [hc, he, map_mul, map_inv, mul_inv]
        ac_rfl

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ σ hσ x hx` and use `normOne_idele_pow_eq_normOne_principal_mul_unit σ hσ x hx`.
-/
theorem _root_.GlobalTheory.TwV.Xc.exists_pow_normOne_idele_eq_principal_mul_integralUnit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ a, σ (σ a) = a) → ∀ x ∈ U1 σ, ∃ (m : ℕ) (z : Eˣ) (k : (AfE F E)ˣ), 0 < m ∧ (z : E) * σ (z : E) = 1 ∧ k ∈ U1 σ ∧ k ∈ intU F E ∧ x ^ m = ratId F E z * k :=
  fun _ _ _ _ _ _ _ σ hσ x hx => normOne_idele_pow_eq_normOne_principal_mul_unit σ hσ x hx

end GlobalTheory.TwV.Xc.ClsPow
