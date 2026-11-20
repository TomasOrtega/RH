import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntIntCast
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open GlobalTheory GlobalTheory.LKMid GlobalTheory.LKRes GlobalTheory.HeckeApprox
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

/- English proof (translation)
Introduce `hNu p _ D G L g hI`. Use `set A := L.actG g with hA`. Use `set B := L.actG g⁻¹ with hB`. Establish `hBA : ∀ v, B (A v) = v` using `fun v => by`. Rewrite using `[hA, hB, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`.

Establish `hAB : ∀ v, A (B v) = v` using `fun v => by`. Rewrite using `[hA, hB, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`. Establish `hAint : ∀ v ∈ LaHat D, A v ∈ LaHat D` using `hI`. Take `⟨j₁, hj₁, hj₁p, hj₁B⟩` from `GlobalTheory.T.exists_coprime_nsmul_endomorphism_preserves_completion p D B`. Use `set ν : AfP p := UpperTheory.Gal.G3.mul g with hν`.

Use `set ν' : AfP p := ((((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p) with hν'`. Establish `hνν' : ν * ν' = 1` using `Units.mul_inv _`. Establish `hνint : IsIntAf ν` using `hNu p D G L g hI`. Take `⟨j₃, hj₃, hj₃p, hj₃ν⟩` from `GlobalTheory.T.exists_coprime_nat_mul_finiteAdeleAwayP_integral p ν'`. Use `set k := j₁ * j₃ with hk`.

Establish `hkp : k.Coprime p` using `Nat.Coprime.mul_left hj₁p hj₃p`. Establish `hk0 : 0 < k` using `Nat.mul_pos hj₁ hj₃`. Use `set h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) := k • B with hh₀`. Establish `hh₀v : ∀ v, h₀ v = k • B v` using `fun v => rfl`. Establish `hh₀int : ∀ v ∈ LaHat D, h₀ v ∈ LaHat D` using `fun v hv => by`.

Rewrite using `[hh₀v, hk, mul_comm, mul_smul]`. Conclude with `nsmul_mem (hj₁B v hv) _`. Establish `hh₀A : ∀ v, h₀ (A v) = k • v` using `fun v => by`. Rewrite using `[hh₀v, hBA]`. Establish `hAh₀ : ∀ v, A (h₀ v) = k • v` using `fun v => by`.

Rewrite using `[hh₀v, map_nsmul, hAB]`. Establish `hh₀O : ∀ (c : D.O) v, h₀ (actAf D c v) = actAf D c (h₀ v)` using `fun c v => by`. Rewrite using `[hh₀v, hh₀v, hB, actG_actAf, map_nsmul]`. Use `set mu : AfP p := (k : AfP p) ^ 2 * ν' with hmu`. Establish `hh₀sim : ∀ v w, fAf D (h₀ v) (h₀ w) = mu * fAf D v w` using `fun v w => by`.

Simplify using `only [hh₀v, map_nsmul, LinearMap.smul_apply]`. Rewrite using `[hB, GlobalTheory.T.harrisTaylor_action_form_eq_similitude_mul p D G L g⁻¹ v w]`. Simplify using `only [nsmul_eq_mul, hmu, hν']`. Rewrite using `[show (((g⁻¹ : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : AfP p) = ((((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p) from rfl]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hmuint : IsIntAf mu`. Establish `e : mu = ((j₁ : AfP p) ^ 2 * j₃) * ((j₃ : AfP p) * ν')` using `by rw [hmu, hk]; push_cast; ring`. Rewrite using `[e]; exact isInt_mul (isInt_mul (by rw [sq]; exact isInt_mul (isInt_natCast _) (isInt_natCast _)) (isInt_natCast _)) hj₃ν`. Establish `hmuν : mu * ν = ((k ^ 2 : ℕ) : AfP p)`. Rewrite using `[hmu]`.

Use `push_cast`. Take the linear combination `((k : AfP p) ^ 2) * hνν'`. Take `⟨c, ε, ε', hcp, hck, hε, hε', hεε', hmuε⟩` from `GlobalTheory.T.exists_divisor_mul_integralUnit_finiteAdelesAwayP p mu ν (k ^ 2) (pow_pos hk0 2) (Nat.Coprime.pow_left 2 hkp) hmuint hνint hmuν`. Take `⟨u, hut, hu⟩` from `GlobalTheory.T.integral_adele_unit_congruence_sequence p ε ε' hε hε' hεε'`. Take `⟨f, hf⟩` from `GlobalTheory.T.lattice_endomorphism_integral_approximation p D h₀ hh₀int`.

Establish `hfe : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, inAf D (f n x) = h₀ (inAf D x) - n • w` using `fun n hn hnp x => by`. Take `⟨w, hw, e⟩` from `hf n hn hnp x`. Conclude with `⟨w, hw, by rw [e]; abel⟩`. Establish `hmult : IsMult ν (k ^ 2 / c)`. Use `⟨ε', ε, hε', hε, by rw [mul_comm]; exact hεε', ?_⟩` and prove the remaining obligations.

Establish `hc0 : c ≠ 0` using `fun h0 => by`. Rewrite `hck` using `[h0, zero_dvd_iff]`. Conclude with `(pow_pos hk0 2).ne' hck`. Establish `hcu : IsUnit (c : AfP p)`. Establish `: IsUnit (algebraMap ℚ (AfP p) (c : ℚ))` using `(IsUnit.mk0 (c : ℚ) (Nat.cast_ne_zero.mpr hc0)).map _`.

Simplify using `using this`. Establish `e1 : ((k ^ 2 : ℕ) : AfP p) = (c : AfP p) * ((k ^ 2 / c : ℕ) : AfP p)`. Rewrite using `[← Nat.cast_mul, Nat.mul_div_cancel' hck]`. Apply `hcu.mul_left_cancel` to reduce the goal to its premises. Establish `e2 : (c : AfP p) * ε * ν = (c : AfP p) * ((k ^ 2 / c : ℕ) : AfP p)`.

Rewrite using `[← hmuε, hmuν, e1]`. Take the linear combination `ε' * e2 - ((c : AfP p) * ν) * hεε'`. Use `⟨f, u, c, k, ⟨hcp, hkp, hck, ?_, ?_, ?_, ?_⟩, hmult, fun v hv => hh₀int v hv, ?_⟩` and prove the remaining obligations. Introduce `n hn hnp a x`. Take `⟨w₁, hw₁, e₁⟩` from `hfe n hn hnp (a • x)`.

Take `⟨w₂, hw₂, e₂⟩` from `hfe n hn hnp x`. Take `⟨z, hz⟩` from `LatDiv.eq_nsmul_of_inAf_eq_nsmul p D (f n (a • x) - a • f n x) n hn hnp (actAf D a w₂ - w₁) (sub_mem (actAf_mem_laHat D a hw₂) hw₁) (by`. Rewrite using `[inAf_sub, ← actAf_inAf, e₁, e₂, ← actAf_inAf, hh₀O, map_sub, map_nsmul, smul_sub]`. Use the proof step `abel)`. Conclude with `⟨z, by rw [← hz]; abel⟩`.

Introduce `n m hn hm hnm`. Establish `hnp : n.Coprime p` using `Nat.Coprime.coprime_dvd_left (dvd_mul_right n m) hnm`. Use `⟨fun x => ?_, hut n m hn hm hnm⟩` and prove the remaining obligations. Take `⟨w₁, hw₁, e₁⟩` from `hfe (n * m) (Nat.mul_pos hn hm) hnm x`. Take `⟨w₂, hw₂, e₂⟩` from `hfe n hn hnp x`.

Take `⟨z, hz⟩` from `LatDiv.eq_nsmul_of_inAf_eq_nsmul p D (f (n * m) x - f n x) n hn hnp (w₂ - m • w₁) (sub_mem hw₂ (nsmul_mem hw₁ m)) (by`. Rewrite using `[inAf_sub, e₁, e₂, smul_sub, smul_smul]`. Use the proof step `abel)`. Conclude with `⟨z, by rw [← hz]; abel⟩`. Introduce `n hn hnp`.

Take `⟨hco, β, hβ, hεβ⟩` from `hu n hn hnp`. Use `⟨hco, fun x y => ?_⟩` and prove the remaining obligations. Take `⟨w₁, hw₁, e₁⟩` from `hfe n hn hnp x`. Take `⟨w₂, hw₂, e₂⟩` from `hfe n hn hnp y`. Establish `hX` using `hh₀int _ (inAf_mem D x)`.

Establish `hY` using `hh₀int _ (inAf_mem D y)`. Use `IntDvdAdele.dvd_of_eq_mul_int p n hn hnp _ ((c : AfP p) * β * (D.EF x y : AfP p) - fAf D (h₀ (inAf D x)) w₂ - fAf D w₁ (h₀ (inAf D y)) + (n : AfP p) * fAf D w₁ w₂) (isInt_add (isInt_sub (isInt_sub (isInt_mul (isInt_mul (isInt_natCast c) hβ) (isInt_intCast _)) (formInt_laHat p D _ …` and prove the remaining obligations. Establish `e : ((D.EF (f n x) (f n y) : ℤ) : AfP p) = fAf D (inAf D (f n x)) (inAf D (f n y))` using `(form_inAf D _ _).symm`. Use `push_cast`. Rewrite using `[e, e₁, e₂]`.

Simplify using `only [map_sub, map_nsmul, LinearMap.sub_apply, LinearMap.smul_apply, nsmul_eq_mul]`. Rewrite using `[hh₀sim, hmuε, hεβ, form_inAf]`. Expand and normalize the polynomial expressions, which then agree. Introduce `n hn hnp x`. Take `⟨y, w, hw, e⟩` from `exists_inAf_add_nsmul_of_mem_laHat p D n hn hnp (A (inAf D x)) (hAint _ (inAf_mem D x))`.

Take `⟨w', hw', e'⟩` from `hfe n hn hnp y`. Establish `e2 : h₀ (inAf D y) = k • inAf D x - n • h₀ w`. Rewrite using `[← hh₀A, e, map_add, map_nsmul]`. Normalize the expressions using the abelian group laws. Take `⟨z, hz⟩` from `LatDiv.eq_nsmul_of_inAf_eq_nsmul p D (f n y - k • x) n hn hnp (-(w' + h₀ w)) (neg_mem (add_mem hw' (hh₀int w hw))) (by`.

Rewrite using `[inAf_sub, e', e2, inAf_nsmul, smul_neg, smul_add]`. Use the proof step `abel)`. Conclude with `⟨y, z, by rw [← hz]; abel⟩`. Introduce `n hn hnp x`. Take `⟨w, hw, e⟩` from `hfe n hn hnp x`.

Use `⟨-(A w), neg_mem (hAint w hw), ?_⟩` and prove the remaining obligations. Rewrite using `[e, map_sub, map_nsmul, hAh₀, smul_neg]`. Normalize the expressions using the abelian group laws.
-/
theorem UpperTheory.Gal.G3.pSysOf :
    NuInt → SysOf := by
  intro hNu p _ D G L g hI
  classical
  set A := L.actG g with hA
  set B := L.actG g⁻¹ with hB
  have hBA : ∀ v, B (A v) = v := fun v => by
    rw [hA, hB, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hAB : ∀ v, A (B v) = v := fun v => by
    rw [hA, hB, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hAint : ∀ v ∈ LaHat D, A v ∈ LaHat D := hI
  obtain ⟨j₁, hj₁, hj₁p, hj₁B⟩ := GlobalTheory.T.exists_coprime_nsmul_endomorphism_preserves_completion p D B
  set ν : AfP p := UpperTheory.Gal.G3.mul g with hν
  set ν' : AfP p := ((((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p) with hν'
  have hνν' : ν * ν' = 1 := Units.mul_inv _
  have hνint : IsIntAf ν := hNu p D G L g hI
  obtain ⟨j₃, hj₃, hj₃p, hj₃ν⟩ := GlobalTheory.T.exists_coprime_nat_mul_finiteAdeleAwayP_integral p ν'
  set k := j₁ * j₃ with hk
  have hkp : k.Coprime p := Nat.Coprime.mul_left hj₁p hj₃p
  have hk0 : 0 < k := Nat.mul_pos hj₁ hj₃
  set h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) := k • B with hh₀
  have hh₀v : ∀ v, h₀ v = k • B v := fun v => rfl
  have hh₀int : ∀ v ∈ LaHat D, h₀ v ∈ LaHat D := fun v hv => by
    rw [hh₀v, hk, mul_comm, mul_smul]; exact nsmul_mem (hj₁B v hv) _
  have hh₀A : ∀ v, h₀ (A v) = k • v := fun v => by
    rw [hh₀v, hBA]
  have hAh₀ : ∀ v, A (h₀ v) = k • v := fun v => by
    rw [hh₀v, map_nsmul, hAB]
  have hh₀O : ∀ (c : D.O) v, h₀ (actAf D c v) = actAf D c (h₀ v) := fun c v => by
    rw [hh₀v, hh₀v, hB, actG_actAf, map_nsmul]
  set mu : AfP p := (k : AfP p) ^ 2 * ν' with hmu
  have hh₀sim : ∀ v w, fAf D (h₀ v) (h₀ w) = mu * fAf D v w := fun v w => by
    simp only [hh₀v, map_nsmul, LinearMap.smul_apply]
    rw [hB, GlobalTheory.T.harrisTaylor_action_form_eq_similitude_mul p D G L g⁻¹ v w]
    simp only [nsmul_eq_mul, hmu, hν']
    rw [show (((g⁻¹ : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : AfP p) =
      ((((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p) from rfl]
    ring
  have hmuint : IsIntAf mu := by
    have e : mu = ((j₁ : AfP p) ^ 2 * j₃) * ((j₃ : AfP p) * ν') := by rw [hmu, hk]; push_cast; ring
    rw [e]; exact isInt_mul (isInt_mul (by rw [sq]; exact isInt_mul (isInt_natCast _) (isInt_natCast _))
      (isInt_natCast _)) hj₃ν
  have hmuν : mu * ν = ((k ^ 2 : ℕ) : AfP p) := by
    rw [hmu]; push_cast; linear_combination ((k : AfP p) ^ 2) * hνν'
  obtain ⟨c, ε, ε', hcp, hck, hε, hε', hεε', hmuε⟩ :=
    GlobalTheory.T.exists_divisor_mul_integralUnit_finiteAdelesAwayP p mu ν (k ^ 2) (pow_pos hk0 2) (Nat.Coprime.pow_left 2 hkp) hmuint hνint hmuν
  obtain ⟨u, hut, hu⟩ := GlobalTheory.T.integral_adele_unit_congruence_sequence p ε ε' hε hε' hεε'
  obtain ⟨f, hf⟩ := GlobalTheory.T.lattice_endomorphism_integral_approximation p D h₀ hh₀int
  have hfe : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, inAf D (f n x) = h₀ (inAf D x) - n • w :=
    fun n hn hnp x => by
      obtain ⟨w, hw, e⟩ := hf n hn hnp x
      exact ⟨w, hw, by rw [e]; abel⟩
  have hmult : IsMult ν (k ^ 2 / c) := by
    refine ⟨ε', ε, hε', hε, by rw [mul_comm]; exact hεε', ?_⟩
    have hc0 : c ≠ 0 := fun h0 => by
      rw [h0, zero_dvd_iff] at hck
      exact (pow_pos hk0 2).ne' hck
    have hcu : IsUnit (c : AfP p) := by
      have : IsUnit (algebraMap ℚ (AfP p) (c : ℚ)) :=
        (IsUnit.mk0 (c : ℚ) (Nat.cast_ne_zero.mpr hc0)).map _
      simpa using this
    have e1 : ((k ^ 2 : ℕ) : AfP p) = (c : AfP p) * ((k ^ 2 / c : ℕ) : AfP p) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hck]
    apply hcu.mul_left_cancel
    have e2 : (c : AfP p) * ε * ν = (c : AfP p) * ((k ^ 2 / c : ℕ) : AfP p) := by
      rw [← hmuε, hmuν, e1]
    linear_combination ε' * e2 - ((c : AfP p) * ν) * hεε'
  refine ⟨f, u, c, k, ⟨hcp, hkp, hck, ?_, ?_, ?_, ?_⟩, hmult, fun v hv => hh₀int v hv, ?_⟩
  ·
    intro n hn hnp a x
    obtain ⟨w₁, hw₁, e₁⟩ := hfe n hn hnp (a • x)
    obtain ⟨w₂, hw₂, e₂⟩ := hfe n hn hnp x
    obtain ⟨z, hz⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D (f n (a • x) - a • f n x) n hn hnp
      (actAf D a w₂ - w₁) (sub_mem (actAf_mem_laHat D a hw₂) hw₁) (by
        rw [inAf_sub, ← actAf_inAf, e₁, e₂, ← actAf_inAf, hh₀O, map_sub, map_nsmul, smul_sub]; abel)
    exact ⟨z, by rw [← hz]; abel⟩
  ·
    intro n m hn hm hnm
    have hnp : n.Coprime p := Nat.Coprime.coprime_dvd_left (dvd_mul_right n m) hnm
    refine ⟨fun x => ?_, hut n m hn hm hnm⟩
    obtain ⟨w₁, hw₁, e₁⟩ := hfe (n * m) (Nat.mul_pos hn hm) hnm x
    obtain ⟨w₂, hw₂, e₂⟩ := hfe n hn hnp x
    obtain ⟨z, hz⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D (f (n * m) x - f n x) n hn hnp
      (w₂ - m • w₁) (sub_mem hw₂ (nsmul_mem hw₁ m)) (by
        rw [inAf_sub, e₁, e₂, smul_sub, smul_smul]; abel)
    exact ⟨z, by rw [← hz]; abel⟩
  ·
    intro n hn hnp
    obtain ⟨hco, β, hβ, hεβ⟩ := hu n hn hnp
    refine ⟨hco, fun x y => ?_⟩
    obtain ⟨w₁, hw₁, e₁⟩ := hfe n hn hnp x
    obtain ⟨w₂, hw₂, e₂⟩ := hfe n hn hnp y
    have hX := hh₀int _ (inAf_mem D x)
    have hY := hh₀int _ (inAf_mem D y)
    refine IntDvdAdele.dvd_of_eq_mul_int p n hn hnp _
      ((c : AfP p) * β * (D.EF x y : AfP p) - fAf D (h₀ (inAf D x)) w₂ - fAf D w₁ (h₀ (inAf D y)) +
        (n : AfP p) * fAf D w₁ w₂)
      (isInt_add (isInt_sub (isInt_sub (isInt_mul (isInt_mul (isInt_natCast c) hβ) (isInt_intCast _))
        (formInt_laHat p D _ _ hX hw₂)) (formInt_laHat p D _ _ hw₁ hY))
        (isInt_mul (isInt_natCast n) (formInt_laHat p D _ _ hw₁ hw₂))) ?_
    have e : ((D.EF (f n x) (f n y) : ℤ) : AfP p) = fAf D (inAf D (f n x)) (inAf D (f n y)) :=
      (form_inAf D _ _).symm
    push_cast
    rw [e, e₁, e₂]
    simp only [map_sub, map_nsmul, LinearMap.sub_apply, LinearMap.smul_apply, nsmul_eq_mul]
    rw [hh₀sim, hmuε, hεβ, form_inAf]
    ring
  ·
    intro n hn hnp x
    obtain ⟨y, w, hw, e⟩ := exists_inAf_add_nsmul_of_mem_laHat p D n hn hnp (A (inAf D x))
      (hAint _ (inAf_mem D x))
    obtain ⟨w', hw', e'⟩ := hfe n hn hnp y
    have e2 : h₀ (inAf D y) = k • inAf D x - n • h₀ w := by
      rw [← hh₀A, e, map_add, map_nsmul]; abel
    obtain ⟨z, hz⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D (f n y - k • x) n hn hnp
      (-(w' + h₀ w)) (neg_mem (add_mem hw' (hh₀int w hw))) (by
        rw [inAf_sub, e', e2, inAf_nsmul, smul_neg, smul_add]; abel)
    exact ⟨y, z, by rw [← hz]; abel⟩
  ·
    intro n hn hnp x
    obtain ⟨w, hw, e⟩ := hfe n hn hnp x
    refine ⟨-(A w), neg_mem (hAint w hw), ?_⟩
    rw [e, map_sub, map_nsmul, hAh₀, smul_neg]
    abel
