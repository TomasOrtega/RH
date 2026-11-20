import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.MemIntPolIff

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.CountingStatementReduction

section Val

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ}

/- English proof (translation)
Establish `h` using `valuation_algebraMap_eq_alt (O := O) p 1 one_ne_zero`. Rewrite `h` using `[map_one]`. Rewrite using `[h, dvr_order_unit_eq_zero isUnit_one]`. Simplify using the standard rewrite rules.
-/
theorem vK_one (p : ℕ) : vK p (1 : KK O) = 0 := by
  have h := valuation_algebraMap_eq_alt (O := O) p 1 one_ne_zero
  rw [map_one] at h
  rw [h, dvr_order_unit_eq_zero isUnit_one]
  simp

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, vK_one]`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Rewrite using `[pow_succ, valuation_mul_alt, ih, hx, ← WithTop.coe_add]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vK_npow {x : KK O} {q : ℚ} (hx : vK p x = (q : WithTop ℚ)) (n : ℕ) :
    vK p (x ^ n) = (((n : ℚ) * q : ℚ) : WithTop ℚ) := by
  induction n with
  | zero => rw [pow_zero, vK_one]; simp
  | succ n ih =>
    rw [pow_succ, valuation_mul_alt, ih, hx, ← WithTop.coe_add]
    congr 1
    push_cast
    ring

/- English proof (translation)
Establish `h` using `valuation_mul_alt (O := O) p x x⁻¹`. Rewrite `h` using `[mul_inv_cancel₀ hx0, vK_one, hx]`. Consider the cases of `ht : vK p x⁻¹ with`. Consider the case `top => rw [ht] at h`. Simplify using `at h`.

Consider the case `coe t`. Rewrite `h` using `[ht, ← WithTop.coe_add]`. Establish `: q + t = 0` using `by exact_mod_cast h.symm`. Use `congr 1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem vK_inv' {x : KK O} (hx0 : x ≠ 0) {q : ℚ} (hx : vK p x = (q : WithTop ℚ)) :
    vK p x⁻¹ = ((-q : ℚ) : WithTop ℚ) := by
  have h := valuation_mul_alt (O := O) p x x⁻¹
  rw [mul_inv_cancel₀ hx0, vK_one, hx] at h
  cases ht : vK p x⁻¹ with
  | top => rw [ht] at h; simp at h
  | coe t =>
    rw [ht, ← WithTop.coe_add] at h
    have : q + t = 0 := by exact_mod_cast h.symm
    congr 1
    linarith

/- English proof (translation)
Consider the cases of `k with`. Consider the case `ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast, vK_npow hx]`. Use `push_cast`. Both sides reduce to the same expression. Consider the case `negSucc n`.

Rewrite using `[zpow_negSucc, vK_inv' (pow_ne_zero _ hx0) (vK_npow hx (n + 1))]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vK_zpow {x : KK O} (hx0 : x ≠ 0) {q : ℚ} (hx : vK p x = (q : WithTop ℚ)) (k : ℤ) :
    vK p (x ^ k) = (((k : ℚ) * q : ℚ) : WithTop ℚ) := by
  cases k with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast, vK_npow hx]; push_cast; rfl
  | negSucc n =>
    rw [zpow_negSucc, vK_inv' (pow_ne_zero _ hx0) (vK_npow hx (n + 1))]
    congr 1
    push_cast
    ring

end Val

section FockMap

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Unfold `fock Formalism.GM.M.fockK`. Rewrite using `[support_map_of_injective _ ι.injective, map_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_map, coeff_map, map_mul, map_mul]`. Use `congr 1`.

Unfold `expFact`. Simplify using `only [Finsupp.prod, Nat.cast_prod, map_prod, map_natCast]`.
-/
theorem fock_map (ι : ℚ_[p] →+* KK O) {σ : Type} (F G : MvPolynomial σ ℚ_[p]) :
    fock (map ι F) (map ι G) = ι (Formalism.GM.M.fockK F G) := by
  classical
  unfold fock Formalism.GM.M.fockK
  rw [support_map_of_injective _ ι.injective, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_map, coeff_map, map_mul, map_mul]
  congr 1
  unfold expFact
  simp only [Finsupp.prod, Nat.cast_prod, map_prod, map_natCast]

/- English proof (translation)
Rewrite using `[fock_form_smul_right, fock_form_symm, fock_form_smul_right, fock_form_symm B A, smul_eq_mul, smul_eq_mul]`.
-/
theorem fock_smul_both {σ : Type} (a : KK O) (A B : MvPolynomial σ (KK O)) :
    fock (a • A) (a • B) = a * (a * fock A B) := by
  rw [fock_form_smul_right, fock_form_symm, fock_form_smul_right, fock_form_symm B A, smul_eq_mul, smul_eq_mul]

end FockMap

section Assemble

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

/- English proof (translation)
Unfold `specConst`. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `i _`. Use `split_ifs`. Conclude with `mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)`.

Conclude with `one_ne_zero`.
-/
theorem specConst_ne_zero {s r : ℕ} (p : ℕ) (S : SegData s) (b : SegBlock s r) : specConst p S b ≠ 0 := by
  unfold specConst
  rw [Finset.prod_ne_zero_iff]
  intro i _
  split_ifs
  · exact mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
  · exact one_ne_zero

/- English proof (translation)
Establish `h2 : X.setting.w ^ 2 = (X.p : X.O)` using `Formalism.MainNotions.G.dvrOfStd_sq X.std`. Establish `: ramE X.p X.O = dvrOrderNat (X.p : X.O)` using `rfl`. Rewrite using `[this, ← h2, dvr_order_pow X.setting.w_irr.ne_zero, nv_irr' X.setting.w_irr]`.
-/
theorem ramE_eq_two : ramE X.p X.O = 2 := by
  have h2 : X.setting.w ^ 2 = (X.p : X.O) := Formalism.MainNotions.G.dvrOfStd_sq X.std
  have : ramE X.p X.O = dvrOrderNat (X.p : X.O) := rfl
  rw [this, ← h2, dvr_order_pow X.setting.w_irr.ne_zero, nv_irr' X.setting.w_irr]

/- English proof (translation)
Rewrite using `[valuation_algebraMap_eq_alt X.p _ X.setting.w_irr.ne_zero, nv_irr' X.setting.w_irr, ramE_eq_two]`. Simplify using the standard rewrite rules.
-/
theorem vK_w : vK X.p (algebraMap X.O (KK X.O) X.setting.w) = (((1 : ℚ) / 2 : ℚ) : WithTop ℚ) := by
  rw [valuation_algebraMap_eq_alt X.p _ X.setting.w_irr.ne_zero, nv_irr' X.setting.w_irr, ramE_eq_two]
  simp

/- English proof (translation)
Rewrite using `[valuation_natCast_padicVal X.std.1.prime X.setting X.p X.std.1.prime.ne_zero, padicValNat_self]`. Simplify using the standard rewrite rules.
-/
theorem vK_p : vK X.p ((X.p : ℕ) : KK X.O) = ((1 : ℚ) : WithTop ℚ) := by
  rw [valuation_natCast_padicVal X.std.1.prime X.setting X.p X.std.1.prime.ne_zero, padicValNat_self]
  simp

/- English proof (translation)
Take `⟨F0, rfl⟩` from `hF`. Use `⟨F0.coeff v, ?_⟩` and prove the remaining obligations. Simplify using `[MvPolynomial.coeff_map]`.
-/
theorem coeff_of_int {p : ℕ} [Fact p.Prime] {σ : Type} (F : MvPolynomial σ ℚ_[p]) (hF : F ∈ Formalism.GM.M.IntPol p σ)
    (v : σ →₀ ℕ) : ∃ c : ℤ_[p], F.coeff v = (c : ℚ_[p]) := by
  obtain ⟨F0, rfl⟩ := hF
  refine ⟨F0.coeff v, ?_⟩
  simp [MvPolynomial.coeff_map]

/- English proof (translation)
Establish `hint` using `iotaX_int X`. Use `set ι := iotaX X with hι`. Use `set sp := specConst X.p (X.S C0 CE1 CE2) b with hsp`. Use `set F : ℤ := ⌊(D : ℝ) + levelPassageLoss X⌋ with hF`. Use `set k : ℤ := F - e - (padicValNat X.p sp : ℤ) with hk'`.

Use `set wK : KK X.O := algebraMap X.O (KK X.O) X.setting.w with hwK`. Establish `hw0 : wK ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective X.O (KK X.O))).2 X.setting.w_irr.ne_zero`. Use `set lam : KK X.O := wK ^ k with hlam`. Establish `hvlam : vK X.p lam = ((((k : ℚ) * (1 / 2)) : ℚ) : WithTop ℚ)` using `vK_zpow hw0 (vK_w X) k`. Establish `hmemL : ∀ z : MvPolynomial (BVar (2 * X.s + 1) X.r (X.S C0 CE1 CE2).t) ℚ_[X.p], z ∈ (gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r` using `X.r) → lam • map ι z ∈ blockLat X.O X.p X.r (X.S C0 CE1 CE2) aTop aPlus X.m b := by`.

Introduce `z hz`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show lam • map ι z ∈ Submodule.span (KK X.O) _`. Conclude with `Submodule.smul_mem _ _ (map_SSZ hint (blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b) z hz)`. Establish `hzi : z ∈ Formalism.GM.M.IntPol X.p (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t)` using `SSZ_int (gB C0 CE1 CE2 X aTop aPlus b) z hz`.

Rewrite using `[MvPolynomial.as_sum (lam • map ι z)]`. Use `Submodule.sum_mem _ fun v hv => Submodule.subset_span ⟨v, _, ?_, rfl⟩` and prove the remaining obligations. Establish `hcv : (lam • map ι z).coeff v = lam * ι (z.coeff v)`. Rewrite using `[coeff_smul, coeff_map, smul_eq_mul]`. Establish `hzv : z.coeff v ≠ 0`.

Introduce `h0`. Rewrite `hv` using `[MvPolynomial.mem_support_iff, hcv, h0, map_zero, mul_zero]`. Conclude with `hv rfl`. Establish `hvz : v ∈ z.support` using `MvPolynomial.mem_support_iff.2 hzv`. Establish `hm` using `hmon z hz v hvz`.

Take `⟨c0, hc0⟩` from `coeff_of_int z hzi v`. Take `⟨o, ho⟩` from `hint c0`. Establish `hcz : ι (z.coeff v) = algebraMap X.O (KK X.O) o` using `by rw [hc0]; exact ho`. Establish `ho0 : (0 : WithTop ℚ) ≤ vK X.p (algebraMap X.O (KK X.O) o)` using `(valuation_nonneg_iff_integral X.setting _).2 ⟨o, rfl⟩`. Rewrite using `[hcv, valuation_mul_alt, hvlam, hcz]`.

Establish `hint2 : (0 : ℤ) ≤ k + (padicValNat X.p (expFact v) : ℤ) + (padicValNat X.p sp : ℤ)`. Establish `h1 : e - (padicValNat X.p (expFact v) : ℤ) ≤ F`. Rewrite using `[hF]`. Apply `Int.le_floor.2` to reduce the goal to its premises. Simplify using `only [Int.cast_sub, Int.cast_natCast]`.

Establish `: (e : ℝ) ≤ (padicValNat X.p (expFact v) : ℝ) + D + levelPassageLoss X` using `hm`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hk']`. Use linear arithmetic over natural numbers and integers. Consider the cases of `hvo : vK X.p (algebraMap X.O (KK X.O) o) with`.

Consider the case `top => simp`. Consider the case `coe t`. Rewrite `ho0` using `[hvo]`. Establish `ht : (0 : ℚ) ≤ t` using `by exact_mod_cast ho0`. Rewrite using `[← WithTop.coe_add, ← WithTop.coe_add]`.

Establish `hq : (0 : ℚ) ≤ (k : ℚ) + (padicValNat X.p (expFact v) : ℚ) + (padicValNat X.p sp : ℚ)`. Establish `h5` using `(Int.cast_le (R := ℚ)).2 hint2`. Simplify `h5` using `only [Int.cast_add, Int.cast_zero, Int.cast_natCast]`. Conclude with `(show (0 : ℚ) ≤ (k : ℚ) * (1 / 2) + t + ((padicValNat X.p (expFact v) : ℚ) / 2 + (padicValNat X.p sp : ℚ) / 2) by linarith)` after adjusting the coercions. Use `set c : KK X.O := (sp : KK X.O) * (lam * (lam * ι ((X.p : ℚ_[X.p]) ^ e))) with hc`.

Establish `hform : ∀ i j, blockForm X.O X.p X.r (X.S C0 CE1 CE2) b (lam • map ι (x i)) (lam • map ι (y j)) = if i = j then c else 0`. Introduce `i j`. Unfold `blockForm`. Rewrite using `[fock_smul_both, fock_map, hxy]`. Use `split_ifs`.

Both sides reduce to the same expression. Simplify using the standard rewrite rules. Establish `hvc : vLE X.p c ((D : ℝ) + levelPassageLoss X)`. Establish `hsp0 : sp ≠ 0` using `specConst_ne_zero X.p (X.S C0 CE1 CE2) b`. Establish `hpe : ι ((X.p : ℚ_[X.p]) ^ e) = ((X.p : ℕ) : KK X.O) ^ e`.

Rewrite using `[map_zpow₀, map_natCast]`. Establish `hp0 : ((X.p : ℕ) : KK X.O) ≠ 0`. Use `(vK_p X)` as an intermediate fact. Introduce `h0`. Rewrite `this` using `[h0, valuation_zero_alt]`.

Conclude with `WithTop.top_ne_coe this`. Use `⟨(padicValNat X.p sp : ℚ) + ((k : ℚ) * (1 / 2) + ((k : ℚ) * (1 / 2) + (e : ℚ) * 1)), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hc, valuation_mul_alt, valuation_mul_alt, valuation_mul_alt, hpe, vK_zpow hp0 (vK_p X) e, hvlam, valuation_natCast_padicVal X.std.1.prime X.setting sp hsp0]`. Simplify using `only [← WithTop.coe_add]`. Establish `h1 : (padicValNat X.p sp : ℚ) + ((k : ℚ) * (1 / 2) + ((k : ℚ) * (1 / 2) + (e : ℚ) * 1)) = (F : ℚ)`.

Rewrite using `[hk']`. Simplify using `only [Int.cast_sub, Int.cast_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, hF]`. Use `Int.floor_le ((D : ℝ) + levelPassageLoss X)` as an intermediate fact.

Conclude with `this` after adjusting the coercions. Establish `hsm : ∀ (a : KK X.O) (u v : MvPolynomial (BVar (2 * X.s + 1) X.r (X.S C0 CE1 CE2).t) (KK X.O)), blockForm X.O X.p X.r (X.S C0 CE1 CE2) b (a • u) v = a * blockForm X.O X.p X.r (X.S C0 CE1 CE2) b u v`. Introduce `a u v`. Unfold `blockForm`. Rewrite using `[fock_form_symm, fock_form_smul_right, fock_form_symm v u, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hadd : ∀ (u u' v : MvPolynomial (BVar (2 * X.s + 1) X.r (X.S C0 CE1 CE2).t) (KK X.O)), blockForm X.O X.p X.r (X.S C0 CE1 CE2) b (u + u') v = blockForm X.O X.p X.r (X.S C0 CE1 CE2) b u v + blockForm X.O X.p X.r (X.S C0 CE1 CE2) b u' v`. Introduce `u u' v`. Unfold `blockForm`. Rewrite using `[fock_form_symm, fock_form_add_right, fock_form_symm v u, fock_form_symm v u']`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `goodSub_of_dual X.setting (blockForm X.O X.p X.r (X.S C0 CE1 CE2) b) hsm hadd (blockLat X.O X.p X.r (X.S C0 CE1 CE2) aTop aPlus X.m b) (fun i => lam • map ι (x i)) (fun i => lam • map ι (y i)) (fun i => hmemL _ (hx i)) (fun i => hmemL _ (hy i)) c hform _ hvc`.
-/
theorem block_dual_family_bound (aTop : Fin X.s → ℕ) (aPlus : ℕ) (b : SegBlock X.s X.r) (D : ℤ) (n : ℕ)
    (x y : Fin n → MvPolynomial (BVar (2 * X.s + 1) X.r (X.S C0 CE1 CE2).t) ℚ_[X.p]) (e : ℤ)
    (hx : ∀ i, x i ∈ (gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r))
    (hy : ∀ i, y i ∈ (gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r))
    (hxy : ∀ i j, Formalism.GM.M.fockK (x i) (y j) = if i = j then (X.p : ℚ_[X.p]) ^ e else 0)
    (hmon : ∀ z : MvPolynomial (BVar (2 * X.s + 1) X.r (X.S C0 CE1 CE2).t) ℚ_[X.p],
      z ∈ (gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r) → ∀ μ ∈ z.support,
        (e : ℝ) ≤ (padicValNat X.p (μ.prod fun _ k => k.factorial) : ℝ) + D + levelPassageLoss X) :
    ∃ L₂ : Submodule X.O (MvPolynomial (BVar (2 * X.s + 1) X.r (X.S C0 CE1 CE2).t) (KK X.O)),
      GoodSub X.p (blockForm X.O X.p X.r (X.S C0 CE1 CE2) b)
        (blockLat X.O X.p X.r (X.S C0 CE1 CE2) aTop aPlus X.m b) L₂ ((D : ℝ) + levelPassageLoss X) ∧
      n ≤ Module.finrank X.O L₂ := by
  have hint := iotaX_int X
  set ι := iotaX X with hι
  set sp := specConst X.p (X.S C0 CE1 CE2) b with hsp
  set F : ℤ := ⌊(D : ℝ) + levelPassageLoss X⌋ with hF
  set k : ℤ := F - e - (padicValNat X.p sp : ℤ) with hk'
  set wK : KK X.O := algebraMap X.O (KK X.O) X.setting.w with hwK
  have hw0 : wK ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective X.O (KK X.O))).2 X.setting.w_irr.ne_zero
  set lam : KK X.O := wK ^ k with hlam
  have hvlam : vK X.p lam = ((((k : ℚ) * (1 / 2)) : ℚ) : WithTop ℚ) := vK_zpow hw0 (vK_w X) k

  have hmemL : ∀ z : MvPolynomial (BVar (2 * X.s + 1) X.r (X.S C0 CE1 CE2).t) ℚ_[X.p],
      z ∈ (gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r) →
      lam • map ι z ∈ blockLat X.O X.p X.r (X.S C0 CE1 CE2) aTop aPlus X.m b := by
    intro z hz
    refine ⟨?_, ?_⟩
    · show lam • map ι z ∈ Submodule.span (KK X.O) _
      exact Submodule.smul_mem _ _ (map_SSZ hint (blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b) z hz)
    · have hzi : z ∈ Formalism.GM.M.IntPol X.p (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t) :=
        SSZ_int (gB C0 CE1 CE2 X aTop aPlus b) z hz
      rw [MvPolynomial.as_sum (lam • map ι z)]
      refine Submodule.sum_mem _ fun v hv => Submodule.subset_span ⟨v, _, ?_, rfl⟩
      have hcv : (lam • map ι z).coeff v = lam * ι (z.coeff v) := by
        rw [coeff_smul, coeff_map, smul_eq_mul]
      have hzv : z.coeff v ≠ 0 := by
        intro h0
        rw [MvPolynomial.mem_support_iff, hcv, h0, map_zero, mul_zero] at hv
        exact hv rfl
      have hvz : v ∈ z.support := MvPolynomial.mem_support_iff.2 hzv
      have hm := hmon z hz v hvz
      obtain ⟨c0, hc0⟩ := coeff_of_int z hzi v
      obtain ⟨o, ho⟩ := hint c0
      have hcz : ι (z.coeff v) = algebraMap X.O (KK X.O) o := by rw [hc0]; exact ho
      have ho0 : (0 : WithTop ℚ) ≤ vK X.p (algebraMap X.O (KK X.O) o) :=
        (valuation_nonneg_iff_integral X.setting _).2 ⟨o, rfl⟩
      rw [hcv, valuation_mul_alt, hvlam, hcz]
      have hint2 : (0 : ℤ) ≤ k + (padicValNat X.p (expFact v) : ℤ) + (padicValNat X.p sp : ℤ) := by
        have h1 : e - (padicValNat X.p (expFact v) : ℤ) ≤ F := by
          rw [hF]
          apply Int.le_floor.2
          simp only [Int.cast_sub, Int.cast_natCast]
          have : (e : ℝ) ≤ (padicValNat X.p (expFact v) : ℝ) + D + levelPassageLoss X := hm
          linarith
        rw [hk']
        omega
      cases hvo : vK X.p (algebraMap X.O (KK X.O) o) with
      | top => simp
      | coe t =>
        rw [hvo] at ho0
        have ht : (0 : ℚ) ≤ t := by exact_mod_cast ho0
        rw [← WithTop.coe_add, ← WithTop.coe_add]
        have hq : (0 : ℚ) ≤ (k : ℚ) + (padicValNat X.p (expFact v) : ℚ) + (padicValNat X.p sp : ℚ) := by
          have h5 := (Int.cast_le (R := ℚ)).2 hint2
          simpa only [Int.cast_add, Int.cast_zero, Int.cast_natCast] using h5
        exact_mod_cast (show (0 : ℚ) ≤ (k : ℚ) * (1 / 2) + t +
          ((padicValNat X.p (expFact v) : ℚ) / 2 + (padicValNat X.p sp : ℚ) / 2) by linarith)

  set c : KK X.O := (sp : KK X.O) * (lam * (lam * ι ((X.p : ℚ_[X.p]) ^ e))) with hc
  have hform : ∀ i j, blockForm X.O X.p X.r (X.S C0 CE1 CE2) b (lam • map ι (x i)) (lam • map ι (y j)) = if i = j then c else 0 := by
    intro i j
    unfold blockForm
    rw [fock_smul_both, fock_map, hxy]
    split_ifs
    · rfl
    · simp
  have hvc : vLE X.p c ((D : ℝ) + levelPassageLoss X) := by
    have hsp0 : sp ≠ 0 := specConst_ne_zero X.p (X.S C0 CE1 CE2) b
    have hpe : ι ((X.p : ℚ_[X.p]) ^ e) = ((X.p : ℕ) : KK X.O) ^ e := by
      rw [map_zpow₀, map_natCast]
    have hp0 : ((X.p : ℕ) : KK X.O) ≠ 0 := by
      have := (vK_p X)
      intro h0
      rw [h0, valuation_zero_alt] at this
      exact WithTop.top_ne_coe this
    refine ⟨(padicValNat X.p sp : ℚ) + ((k : ℚ) * (1 / 2) + ((k : ℚ) * (1 / 2) + (e : ℚ) * 1)), ?_, ?_⟩
    · rw [hc, valuation_mul_alt, valuation_mul_alt, valuation_mul_alt, hpe, vK_zpow hp0 (vK_p X) e, hvlam,
        valuation_natCast_padicVal X.std.1.prime X.setting sp hsp0]
      simp only [← WithTop.coe_add]
    · have h1 : (padicValNat X.p sp : ℚ) + ((k : ℚ) * (1 / 2) + ((k : ℚ) * (1 / 2) + (e : ℚ) * 1)) = (F : ℚ) := by
        rw [hk']; simp only [Int.cast_sub, Int.cast_natCast]; ring
      rw [h1, hF]
      have := Int.floor_le ((D : ℝ) + levelPassageLoss X)
      exact_mod_cast this
  have hsm : ∀ (a : KK X.O) (u v : MvPolynomial (BVar (2 * X.s + 1) X.r (X.S C0 CE1 CE2).t) (KK X.O)),
      blockForm X.O X.p X.r (X.S C0 CE1 CE2) b (a • u) v = a * blockForm X.O X.p X.r (X.S C0 CE1 CE2) b u v := by
    intro a u v
    unfold blockForm
    rw [fock_form_symm, fock_form_smul_right, fock_form_symm v u, smul_eq_mul]
    ring
  have hadd : ∀ (u u' v : MvPolynomial (BVar (2 * X.s + 1) X.r (X.S C0 CE1 CE2).t) (KK X.O)),
      blockForm X.O X.p X.r (X.S C0 CE1 CE2) b (u + u') v = blockForm X.O X.p X.r (X.S C0 CE1 CE2) b u v + blockForm X.O X.p X.r (X.S C0 CE1 CE2) b u' v := by
    intro u u' v
    unfold blockForm
    rw [fock_form_symm, fock_form_add_right, fock_form_symm v u, fock_form_symm v u']
    ring
  exact goodSub_of_dual X.setting (blockForm X.O X.p X.r (X.S C0 CE1 CE2) b) hsm hadd
    (blockLat X.O X.p X.r (X.S C0 CE1 CE2) aTop aPlus X.m b) (fun i => lam • map ι (x i)) (fun i => lam • map ι (y i))
    (fun i => hmemL _ (hx i)) (fun i => hmemL _ (hy i)) c hform _ hvc

/- English proof (translation)
Introduce `aTop hT aPlus hP b hk D hD`. Take `⟨n, x, y, e, hx, hy, hxy, hmon, hrk⟩` from `hZ aTop hT aPlus hP b hk D hD`. Take `⟨L₂, hg, hn⟩` from `block_dual_family_bound C0 CE1 CE2 X aTop aPlus b D n x y e hx hy hxy hmon`. Conclude with `⟨L₂, hg, (hdim aTop hT aPlus hP b hk).trans (hrk.trans (Nat.add_le_add_right hn _))⟩`.
-/
theorem block_bound_of_dual_families (hZ : BlockBoundIntegers C0 CE1 CE2 X) (hdim : RestBCdim C0 CE1 CE2 X) : BlockBoundUniformiser C0 CE1 CE2 X := by
  intro aTop hT aPlus hP b hk D hD
  obtain ⟨n, x, y, e, hx, hy, hxy, hmon, hrk⟩ := hZ aTop hT aPlus hP b hk D hD
  obtain ⟨L₂, hg, hn⟩ := block_dual_family_bound C0 CE1 CE2 X aTop aPlus b D n x y e hx hy hxy hmon
  exact ⟨L₂, hg, (hdim aTop hT aPlus hP b hk).trans (hrk.trans (Nat.add_le_add_right hn _))⟩

end Assemble

end Formalism.MainNotions.G.SymmetricFormBlocks

end
