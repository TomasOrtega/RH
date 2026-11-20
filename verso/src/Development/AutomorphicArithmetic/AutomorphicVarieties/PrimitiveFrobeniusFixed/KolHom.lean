import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.GalBasic

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

section
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

/- English proof (translation)
Simplify using `only [opP, map_mul, mul_pow]`. Conclude with `mul_div_mul_comm _ _ _ _`.
-/
private theorem opP_mul' (δ : G ℚ Ω) (a : ℕ) (x y : Ω) : opP δ a (x * y) = opP δ a x * opP δ a y := by
  simp only [opP, map_mul, mul_pow]
  exact mul_div_mul_comm _ _ _ _

/- English proof (translation)
The claim follows from `div_ne_zero ((map_ne_zero δ).2 hx) (pow_ne_zero _ hx)`.
-/
private theorem opP_ne' (δ : G ℚ Ω) (a : ℕ) {x : Ω} (hx : x ≠ 0) : opP δ a x ≠ 0 :=
  div_ne_zero ((map_ne_zero δ).2 hx) (pow_ne_zero _ hx)

/- English proof (translation)
Establish `hy0 : y ≠ 0`. Introduce `h0`. Rewrite `hy` using `[h0, zero_pow hM]`. Conclude with `hy rfl`. Establish `hw : (x / y) ^ M = 1` using `by rw [div_pow, h, div_self hy]`.

Establish `hw0 : x / y ≠ 0`. Introduce `h0`. Rewrite `hw` using `[h0, zero_pow hM]`. Conclude with `zero_ne_one hw`. Establish `hx : x = y * (x / y)` using `(mul_div_cancel₀ x hy0).symm`.

Establish `h1 : opP δ a (x / y) = 1`. Unfold `opP`. Rewrite using `[hδ _ hw, div_self (pow_ne_zero _ hw0)]`. Rewrite using `[hx, opP_mul', h1, mul_one]`.
-/
private theorem opP_eq' {M a : ℕ} (hM : M ≠ 0) {δ : G ℚ Ω} (hδ : Pows M a δ) {x y : Ω} (hy : y ^ M ≠ 0)
    (h : x ^ M = y ^ M) : opP δ a x = opP δ a y := by
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, zero_pow hM] at hy
    exact hy rfl
  have hw : (x / y) ^ M = 1 := by rw [div_pow, h, div_self hy]
  have hw0 : x / y ≠ 0 := by
    intro h0
    rw [h0, zero_pow hM] at hw
    exact zero_ne_one hw
  have hx : x = y * (x / y) := (mul_div_cancel₀ x hy0).symm
  have h1 : opP δ a (x / y) = 1 := by
    unfold opP
    rw [hδ _ hw, div_self (pow_ne_zero _ hw0)]
  rw [hx, opP_mul', h1, mul_one]

/- English proof (translation)
Rewrite `h` using `[← pow_add]`. Establish `h2 : ζ ^ (j.val + k.val) = ζ ^ ((j + k).val)`. Rewrite using `[ZMod.val_add]`. Use `conv_lhs => rw [← Nat.mod_add_div (j.val + k.val) M, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]`. Conclude with `ZMod.val_injective M (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (h.trans h2))`.
-/
private theorem zeta_inj' {M : ℕ} [NeZero M] {ζ : Ω} (hζ : IsPrimitiveRoot ζ M) {i j k : ZMod M}
    (h : ζ ^ i.val = ζ ^ j.val * ζ ^ k.val) : i = j + k := by
  rw [← pow_add] at h
  have h2 : ζ ^ (j.val + k.val) = ζ ^ ((j + k).val) := by
    rw [ZMod.val_add]
    conv_lhs => rw [← Nat.mod_add_div (j.val + k.val) M, pow_add, pow_mul, hζ.pow_eq_one,
      one_pow, mul_one]
  exact ZMod.val_injective M (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (h.trans h2))

end

/- English proof (translation)
Introduce `Ω _ _ _ M F n a _ hFn hMF ζ hζ δ hδ y hy hfix κ hK`. Establish `hM : M ≠ 0` using `NeZero.ne M`. Establish `gb` using `galBasic Ω (F * n) hFn`. Establish `gbF : fixMu ℚ Ω (F * n) ≤ fixMu ℚ Ω F` using `gb.2.2.2.2.2.2.2.2.1 F (dvd_mul_right F n)`. Take `⟨Y₀, hY₀, hK'⟩` from `hK`.

Establish `hgy : ∀ g : G ℚ Ω, g y / y ≠ 0` using `fun g => div_ne_zero ((map_ne_zero g).mpr hy) hy`. Establish `hY0 : Y₀ ≠ 0`. Introduce `h0`. Rewrite `hY₀` using `[h0, zero_pow hM]`. Conclude with `hy hY₀.symm`.

Establish `hA : opP δ a Y₀ ≠ 0` using `opP_ne' δ a hY0`. Establish `key : ∀ Y : Ω, Y ^ M = y → ∀ g ∈ fixMu ℚ Ω F, ∀ z : Ω, z ^ M = g y / y → ζ ^ (κ g).val = g (opP δ a Y) / opP δ a Y / opP δ a z`. Introduce `Y hY g hg z hz`. Take `⟨z₀, -, hz₀, hκ⟩` from `hK' g hg`. Establish `e1 : opP δ a Y = opP δ a Y₀` using `opP_eq' hM hδ (by rw [hY₀]; exact hy) (hY.trans hY₀.symm)`.

Establish `e2 : opP δ a z = opP δ a z₀` using `opP_eq' hM hδ (by rw [hz₀]; exact hgy g) (hz.trans hz₀.symm)`. Rewrite using `[e1, e2]`. Conclude with `hκ`. Establish `hmul : ∀ u ∈ fixMu ℚ Ω F, ∀ v ∈ fixMu ℚ Ω F, κ (u * v) = κ u + κ v`. Introduce `u hu v hv`.

Take `⟨zu, -, hzu, hκu⟩` from `hK' u hu`. Take `⟨zv, hzvfix, hzv, hκv⟩` from `hK' v hv`. Establish `hzu0 : zu ≠ 0`. Introduce `h0`. Rewrite `hzu` using `[h0, zero_pow hM]`.

Conclude with `hgy u hzu.symm`. Establish `hzv0 : zv ≠ 0`. Introduce `h0`. Rewrite `hzv` using `[h0, zero_pow hM]`. Conclude with `hgy v hzv.symm`.

Establish `huy : u y ≠ 0` using `(map_ne_zero u).mpr hy`. Establish `hz : (u zv * zu) ^ M = (u * v) y / y`. Rewrite using `[mul_pow, ← map_pow, hzv, hzu, map_div₀, AlgEquiv.mul_apply]`. Clear the denominators using the available nonvanishing facts. Establish `euv` using `key Y₀ hY₀ (u * v) (mul_mem hu hv) (u zv * zu) hz`.

Establish `hcomm : δ (u zv) = u (δ zv)` using `gb.2.2.2.2.2.1 zv hzvfix δ u`. Establish `hPu : opP δ a (u zv) = u (opP δ a zv)`. Unfold `opP`. Rewrite using `[hcomm, map_div₀, map_pow]`. Rewrite `euv` using `[opP_mul', hPu, AlgEquiv.mul_apply]`.

Establish `hfixζ : u (ζ ^ (κ v).val) = ζ ^ (κ v).val`. Apply `hu` to reduce the goal to its premises. Take `⟨c, hc⟩` from `hMF`. Rewrite using `[hc, pow_mul, ← pow_mul ζ, mul_comm (κ v).val M, pow_mul, hζ.pow_eq_one, one_pow, one_pow]`. Establish `ev' : ζ ^ (κ v).val = u (v (opP δ a Y₀)) / u (opP δ a Y₀) / u (opP δ a zv)`.

Rewrite using `[← hfixζ, hκv, map_div₀, map_div₀]`. Establish `hB : opP δ a zu ≠ 0` using `opP_ne' δ a hzu0`. Establish `huA : u (opP δ a Y₀) ≠ 0` using `(map_ne_zero u).mpr hA`. Establish `huC : u (opP δ a zv) ≠ 0` using `(map_ne_zero u).mpr (opP_ne' δ a hzv0)`. Apply `zeta_inj' hζ` to reduce the goal to its premises.

Rewrite using `[euv, hκu, ev']`. Clear the denominators using the available nonvanishing facts. Use `⟨hmul, ?_, key⟩` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`.

Use `haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic`. Establish `hint : IsIntegral ℚ (opP δ a Y₀)` using `(Algebra.IsAlgebraic.isAlgebraic _).isIntegral`. Use `haveI := IntermediateField.adjoin.finiteDimensional hint`. Set `H : Set (G ℚ Ω)` to `(fixMu ℚ Ω (F * n) : Set (G ℚ Ω)) ∩ ((IntermediateField.adjoin ℚ {opP δ a Y₀}).fixingSubgroup : Set (G ℚ Ω))`. Establish `hHo : IsOpen H` using `gb.2.1.inter (IntermediateField.fixingSubgroup_isOpen _)`.

Establish `hH0 : ∀ h ∈ H, κ h = 0`. Introduce and unpack `h ⟨h1, h2⟩`. Establish `e` using `key Y₀ hY₀ h (gbF h1) 1 (by rw [one_pow, hfix h h1, div_self hy])`. Establish `hP1 : opP δ a (1 : Ω) = 1` using `by simp [opP]`. Establish `hfx : h (opP δ a Y₀) = opP δ a Y₀` using `(IntermediateField.mem_fixingSubgroup_iff _ _).mp h2 _ (IntermediateField.mem_adjoin_simple_self ℚ _)`.

Rewrite `e` using `[hP1, hfx, div_self hA, div_one]`. Establish `e0` using `zeta_inj' hζ (i := κ h) (j := 0) (k := 0) (by rw [e, ZMod.val_zero, pow_zero, one_mul])`. Simplify using `using e0`. Establish `hS : IsOpen {w : fixMu ℚ Ω F | (x : G ℚ Ω)⁻¹ * w ∈ H}` using `hHo.preimage (continuous_const.mul continuous_subtype_val)`. Establish `hx : x ∈ {w : fixMu ℚ Ω F | (x : G ℚ Ω)⁻¹ * w ∈ H}` using `by show (x : G ℚ Ω)⁻¹ * x ∈ H`.

Rewrite using `[inv_mul_cancel]`. Conclude with `⟨one_mem _, one_mem _⟩`. Use `filter_upwards [hS.mem_nhds hx] with w hw`. Establish `hw' : (x : G ℚ Ω)⁻¹ * w ∈ fixMu ℚ Ω F` using `gbF hw.1`. Establish `e` using `hmul x x.2 _ hw'`.

Rewrite `e` using `[mul_inv_cancel_left, hH0 _ hw, add_zero]`. Conclude with `e`.
-/
theorem UpperTheory.V.ML.kolHom :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M F n a : ℕ) [NeZero M], F * n ≠ 0 → M ∣ F → ∀ (ζ : Ω), IsPrimitiveRoot ζ M → ∀ δ : G ℚ Ω, Pows M a δ → ∀ y : Ω, y ≠ 0 → (∀ h ∈ fixMu ℚ Ω (F * n), h y = y) →
    ∀ κ : G ℚ Ω → ZMod M, IsKol M F n ζ δ a y κ →
    (∀ u ∈ fixMu ℚ Ω F, ∀ v ∈ fixMu ℚ Ω F, κ (u * v) = κ u + κ v) ∧ IsLocallyConstant (fun u : fixMu ℚ Ω F => κ u) ∧
    ∀ Y : Ω, Y ^ M = y → ∀ g ∈ fixMu ℚ Ω F, ∀ z : Ω, z ^ M = g y / y → ζ ^ (κ g).val = g (opP δ a Y) / opP δ a Y / opP δ a z := by
  intro Ω _ _ _ M F n a _ hFn hMF ζ hζ δ hδ y hy hfix κ hK
  have hM : M ≠ 0 := NeZero.ne M
  have gb := galBasic Ω (F * n) hFn
  have gbF : fixMu ℚ Ω (F * n) ≤ fixMu ℚ Ω F := gb.2.2.2.2.2.2.2.2.1 F (dvd_mul_right F n)
  obtain ⟨Y₀, hY₀, hK'⟩ := hK
  have hgy : ∀ g : G ℚ Ω, g y / y ≠ 0 := fun g => div_ne_zero ((map_ne_zero g).mpr hy) hy
  have hY0 : Y₀ ≠ 0 := by
    intro h0
    rw [h0, zero_pow hM] at hY₀
    exact hy hY₀.symm
  have hA : opP δ a Y₀ ≠ 0 := opP_ne' δ a hY0
  have key : ∀ Y : Ω, Y ^ M = y → ∀ g ∈ fixMu ℚ Ω F, ∀ z : Ω, z ^ M = g y / y →
      ζ ^ (κ g).val = g (opP δ a Y) / opP δ a Y / opP δ a z := by
    intro Y hY g hg z hz
    obtain ⟨z₀, -, hz₀, hκ⟩ := hK' g hg
    have e1 : opP δ a Y = opP δ a Y₀ :=
      opP_eq' hM hδ (by rw [hY₀]; exact hy) (hY.trans hY₀.symm)
    have e2 : opP δ a z = opP δ a z₀ :=
      opP_eq' hM hδ (by rw [hz₀]; exact hgy g) (hz.trans hz₀.symm)
    rw [e1, e2]
    exact hκ
  have hmul : ∀ u ∈ fixMu ℚ Ω F, ∀ v ∈ fixMu ℚ Ω F, κ (u * v) = κ u + κ v := by
    intro u hu v hv
    obtain ⟨zu, -, hzu, hκu⟩ := hK' u hu
    obtain ⟨zv, hzvfix, hzv, hκv⟩ := hK' v hv
    have hzu0 : zu ≠ 0 := by
      intro h0
      rw [h0, zero_pow hM] at hzu
      exact hgy u hzu.symm
    have hzv0 : zv ≠ 0 := by
      intro h0
      rw [h0, zero_pow hM] at hzv
      exact hgy v hzv.symm
    have huy : u y ≠ 0 := (map_ne_zero u).mpr hy
    have hz : (u zv * zu) ^ M = (u * v) y / y := by
      rw [mul_pow, ← map_pow, hzv, hzu, map_div₀, AlgEquiv.mul_apply]
      field_simp
    have euv := key Y₀ hY₀ (u * v) (mul_mem hu hv) (u zv * zu) hz
    have hcomm : δ (u zv) = u (δ zv) := gb.2.2.2.2.2.1 zv hzvfix δ u
    have hPu : opP δ a (u zv) = u (opP δ a zv) := by
      unfold opP
      rw [hcomm, map_div₀, map_pow]
    rw [opP_mul', hPu, AlgEquiv.mul_apply] at euv
    have hfixζ : u (ζ ^ (κ v).val) = ζ ^ (κ v).val := by
      apply hu
      obtain ⟨c, hc⟩ := hMF
      rw [hc, pow_mul, ← pow_mul ζ, mul_comm (κ v).val M, pow_mul, hζ.pow_eq_one, one_pow,
        one_pow]
    have ev' : ζ ^ (κ v).val = u (v (opP δ a Y₀)) / u (opP δ a Y₀) / u (opP δ a zv) := by
      rw [← hfixζ, hκv, map_div₀, map_div₀]
    have hB : opP δ a zu ≠ 0 := opP_ne' δ a hzu0
    have huA : u (opP δ a Y₀) ≠ 0 := (map_ne_zero u).mpr hA
    have huC : u (opP δ a zv) ≠ 0 := (map_ne_zero u).mpr (opP_ne' δ a hzv0)
    apply zeta_inj' hζ
    rw [euv, hκu, ev']
    field_simp
  refine ⟨hmul, ?_, key⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hint : IsIntegral ℚ (opP δ a Y₀) := (Algebra.IsAlgebraic.isAlgebraic _).isIntegral
  haveI := IntermediateField.adjoin.finiteDimensional hint
  let H : Set (G ℚ Ω) := (fixMu ℚ Ω (F * n) : Set (G ℚ Ω)) ∩
    ((IntermediateField.adjoin ℚ {opP δ a Y₀}).fixingSubgroup : Set (G ℚ Ω))
  have hHo : IsOpen H := gb.2.1.inter (IntermediateField.fixingSubgroup_isOpen _)
  have hH0 : ∀ h ∈ H, κ h = 0 := by
    rintro h ⟨h1, h2⟩
    have e := key Y₀ hY₀ h (gbF h1) 1 (by rw [one_pow, hfix h h1, div_self hy])
    have hP1 : opP δ a (1 : Ω) = 1 := by simp [opP]
    have hfx : h (opP δ a Y₀) = opP δ a Y₀ :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp h2 _
        (IntermediateField.mem_adjoin_simple_self ℚ _)
    rw [hP1, hfx, div_self hA, div_one] at e
    have e0 := zeta_inj' hζ (i := κ h) (j := 0) (k := 0)
      (by rw [e, ZMod.val_zero, pow_zero, one_mul])
    simpa using e0
  have hS : IsOpen {w : fixMu ℚ Ω F | (x : G ℚ Ω)⁻¹ * w ∈ H} :=
    hHo.preimage (continuous_const.mul continuous_subtype_val)
  have hx : x ∈ {w : fixMu ℚ Ω F | (x : G ℚ Ω)⁻¹ * w ∈ H} := by
    show (x : G ℚ Ω)⁻¹ * x ∈ H
    rw [inv_mul_cancel]
    exact ⟨one_mem _, one_mem _⟩
  filter_upwards [hS.mem_nhds hx] with w hw
  have hw' : (x : G ℚ Ω)⁻¹ * w ∈ fixMu ℚ Ω F := gbF hw.1
  have e := hmul x x.2 _ hw'
  rw [mul_inv_cancel_left, hH0 _ hw, add_zero] at e
  exact e
