import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HeisenbergCocycleFormIntegralSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexEqOfSelfDualAlternatingStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeylHeisenbergOperatorCalculusRationalStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PeriodLatticeHalfLatticeInclusionsSplitPrimeStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PerLatticeFactsStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLiftHalfLatticeRationalStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicNumbersPadicPlacesFactsStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AddSubgroupRepsExistenceCardSumStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaMovedCosetIndicatorVacuumShapeStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.MomT.CosetBar

section Groups

variable {E H : Type} [Field E] [AddCommGroup H] [Module E H]

def scl (r : E) (M : AddSubgroup H) : AddSubgroup H := M.map (DistribSMul.toAddMonoidHom H r)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_scl {r : E} {M : AddSubgroup H} {y : H} : y ∈ scl r M ↔ ∃ m ∈ M, r • m = y := Iff.rfl

/- English proof (translation)
Rewrite `hk`, `hl` using `[Nat.cast_smul_eq_nsmul]`. Take `⟨s, t, hst⟩` from `Nat.isCoprime_iff_coprime.2 h`. Establish `: x = s • (k • x) + t • (l • x)`. Rewrite using `[← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, ← add_smul, hst, one_smul]`. Rewrite using `[this]`.

Conclude with `add_mem (zsmul_mem hk _) (zsmul_mem hl _)`.
-/
theorem mem_of_coprime (M : AddSubgroup H) {k l : ℕ} (h : Nat.Coprime k l) {x : H} (hk : (k : E) • x ∈ M)
    (hl : (l : E) • x ∈ M) : x ∈ M := by
  rw [Nat.cast_smul_eq_nsmul] at hk hl
  obtain ⟨s, t, hst⟩ := Nat.isCoprime_iff_coprime.2 h
  have : x = s • (k • x) + t • (l • x) := by
    rw [← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, ← add_smul, hst, one_smul]
  rw [this]
  exact add_mem (zsmul_mem hk _) (zsmul_mem hl _)

/- English proof (translation)
Rewrite using `[Nat.cast_smul_eq_nsmul]`. Conclude with `nsmul_mem hx _`.
-/
theorem nat_smul_mem (M : AddSubgroup H) (k : ℕ) {x : H} (hx : x ∈ M) : (k : E) • x ∈ M := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hx _

/- English proof (translation)
Rewrite using `[← AddSubgroup.relIndex_map_map_of_injective (f := DistribSMul.toAddMonoidHom H r) M L (smul_right_injective H hr)]`. Introduce `h`. Use `hM (AddSubgroup.relIndex_eq_zero_of_le_right ?_ h)` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `hL y hy`.
-/
theorem relIndex_ne_zero_of_smul {M L : AddSubgroup H} {r : E} (hr : r ≠ 0) (hM : (scl r M).relIndex M ≠ 0)
    (hL : ∀ y ∈ L, r • y ∈ M) : M.relIndex L ≠ 0 := by
  rw [← AddSubgroup.relIndex_map_map_of_injective (f := DistribSMul.toAddMonoidHom H r) M L (smul_right_injective H hr)]
  intro h
  refine hM (AddSubgroup.relIndex_eq_zero_of_le_right ?_ h)
  rintro _ ⟨y, hy, rfl⟩
  exact hL y hy

/- English proof (translation)
Rewrite using `[scl, ← AddSubgroup.relIndex_comap, ← AddSubgroup.inf_relIndex_right, ← AddSubgroup.inf_relIndex_right M]`. Use `congr 1`. Use extensionality with `y`. Simplify using `only [AddSubgroup.mem_inf, AddSubgroup.mem_comap, and_congr_left_iff]`. Conclude with `fun hy => ⟨fun h' => mem_of_coprime (E := E) M h h' (hK y hy), fun h' => nat_smul_mem (E := E) M k h'⟩`.
-/
theorem relIndex_scl_nat (M K : AddSubgroup H) {k p : ℕ} (h : Nat.Coprime k p) (hK : ∀ y ∈ K, (p : E) • y ∈ M) :
    M.relIndex (scl (k : E) K) = M.relIndex K := by
  rw [scl, ← AddSubgroup.relIndex_comap, ← AddSubgroup.inf_relIndex_right, ← AddSubgroup.inf_relIndex_right M]
  congr 1
  ext y
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_comap, and_congr_left_iff]
  exact fun hy => ⟨fun h' => mem_of_coprime (E := E) M h h' (hK y hy), fun h' => nat_smul_mem (E := E) M k h'⟩

/- English proof (translation)
Use extensionality with `y`. Simplify using `only [mem_scl, mul_smul]`. Conclude with `⟨fun ⟨_, ⟨m, hm, rfl⟩, h⟩ => ⟨m, hm, h⟩, fun ⟨m, hm, h⟩ => ⟨_, ⟨m, hm, rfl⟩, h⟩⟩`.
-/
theorem scl_scl (r s : E) (M : AddSubgroup H) : scl r (scl s M) = scl (r * s) M := by
  ext y
  simp only [mem_scl, mul_smul]
  exact ⟨fun ⟨_, ⟨m, hm, rfl⟩, h⟩ => ⟨m, hm, h⟩, fun ⟨m, hm, h⟩ => ⟨_, ⟨m, hm, rfl⟩, h⟩⟩

/- English proof (translation)
Establish `h` using `AddSubgroup.relIndex_inf_mul_relIndex B K M`. Use `⟨B.relIndex (K ⊓ M), ?_, ?_⟩` and prove the remaining obligations. Use `(GlobalTheory.T.addSubgroup_reps_existence_card_sum H).2.2.2.2 B (K ⊓ M) g p hp hg (fun h0 => hfin (by rw [← h, h0, zero_mul])) fun x hx => ?_` and prove the remaining obligations. Rewrite using `[← Nat.cast_smul_eq_nsmul E]`. Conclude with `hK x hx.1`.

Rewrite using `[mul_comm, h]`. Conclude with `AddSubgroup.relIndex_dvd_of_le_left _ inf_le_left`.
-/
theorem relIndex_dvd (M B K : AddSubgroup H) {g p : ℕ} (hp : p.Prime) (hg : Nat.Coprime g p)
    (hK : ∀ y ∈ K, (g : E) • y ∈ B) (hfin : (B ⊓ K).relIndex M ≠ 0) :
    ∃ c : ℕ, ¬ p ∣ c ∧ B.relIndex M ∣ K.relIndex M * c := by
  have h := AddSubgroup.relIndex_inf_mul_relIndex B K M
  refine ⟨B.relIndex (K ⊓ M), ?_, ?_⟩
  · refine (GlobalTheory.T.addSubgroup_reps_existence_card_sum H).2.2.2.2 B (K ⊓ M) g p hp hg (fun h0 => hfin (by rw [← h, h0, zero_mul])) fun x hx => ?_
    rw [← Nat.cast_smul_eq_nsmul E]
    exact hK x hx.1
  · rw [mul_comm, h]
    exact AddSubgroup.relIndex_dvd_of_le_left _ inf_le_left

/- English proof (translation)
Take `⟨k, hk, hx⟩` from `hfull x`. Take `⟨l, hl, hy⟩` from `hfull y`. Rewrite `hx`, `hy` using `[Nat.cast_smul_eq_nsmul]`. Take `⟨n, hn⟩` from `hM _ hx _ hy`. Establish `e1 : ω (k • x) (l • y) = k • ω x (l • y)` using `map_nsmul (AddMonoidHom.mk' (fun s => ω s (l • y)) fun s t => h1 s t _) k x`.

Establish `e2 : ω x (l • y) = l • ω x y` using `map_nsmul (AddMonoidHom.mk' (fun s => ω x s) fun s t => h2 x s t) l y`. Rewrite `hn` using `[e1, e2, nsmul_eq_mul, nsmul_eq_mul]`. Use `⟨n / (k * l), ?_⟩` and prove the remaining obligations. Establish `: (k : ℝ) ≠ 0` using `by positivity`. Establish `: (l : ℝ) ≠ 0` using `by positivity`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rat_of_biadd (ω : H → H → ℝ) (h1 : ∀ x y z, ω (x + y) z = ω x z + ω y z) (h2 : ∀ x y z, ω x (y + z) = ω x y + ω x z)
    (M : AddSubgroup H) (hM : ∀ x ∈ M, ∀ y ∈ M, ∃ n : ℤ, ω x y = n) (hfull : ∀ x : H, ∃ n : ℕ, 0 < n ∧ (n : E) • x ∈ M)
    (x y : H) : ∃ r : ℚ, ω x y = r := by
  obtain ⟨k, hk, hx⟩ := hfull x
  obtain ⟨l, hl, hy⟩ := hfull y
  rw [Nat.cast_smul_eq_nsmul] at hx hy
  obtain ⟨n, hn⟩ := hM _ hx _ hy
  have e1 : ω (k • x) (l • y) = k • ω x (l • y) := map_nsmul (AddMonoidHom.mk' (fun s => ω s (l • y)) fun s t => h1 s t _) k x
  have e2 : ω x (l • y) = l • ω x y := map_nsmul (AddMonoidHom.mk' (fun s => ω x s) fun s t => h2 x s t) l y
  rw [e1, e2, nsmul_eq_mul, nsmul_eq_mul] at hn
  refine ⟨n / (k * l), ?_⟩
  have : (k : ℝ) ≠ 0 := by positivity
  have : (l : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  linarith

end Groups

section Place

variable {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p])

/- English proof (translation)
Simplify using `only [TaylorLogMetric.lamC, dif_pos hx, dif_pos hy, dif_pos (mul_mem hx hy)]`. Conclude with `map_mul lam ⟨x, hx⟩ ⟨y, hy⟩`.
-/
theorem lamC_mul {x y : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (hy : y ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (x * y) = TaylorLogMetric.lamC lam x * TaylorLogMetric.lamC lam y := by
  simp only [TaylorLogMetric.lamC, dif_pos hx, dif_pos hy, dif_pos (mul_mem hx hy)]
  exact map_mul lam ⟨x, hx⟩ ⟨y, hy⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Establish `: TaylorLogMetric.lamC lam 0 = lam 0` using `dif_pos (zero_mem _)`. Simplify using `only [Finset.sum_empty, this, map_zero]`. Consider the case `insert k s hk ih`.

Establish `h1` using `h k (Finset.mem_insert_self _ _)`. Establish `h2 : ∀ j ∈ s, f j ∈ TaylorLogMetric.Qbar` using `fun j hj => h j (Finset.mem_insert_of_mem hj)`. Establish `h3` using `sum_mem h2`. Rewrite using `[Finset.sum_insert hk, Finset.sum_insert hk, ← ih h2]`. Simplify using `only [TaylorLogMetric.lamC, dif_pos h1, dif_pos h3, dif_pos (add_mem h1 h3)]`.

Conclude with `map_add lam ⟨_, h1⟩ ⟨_, h3⟩`.
-/
theorem lamC_sum {κ : Type} (s : Finset κ) (f : κ → ℂ) (h : ∀ k ∈ s, f k ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (∑ k ∈ s, f k) = ∑ k ∈ s, TaylorLogMetric.lamC lam (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : TaylorLogMetric.lamC lam 0 = lam 0 := dif_pos (zero_mem _)
    simp only [Finset.sum_empty, this, map_zero]
  | insert k s hk ih =>
    have h1 := h k (Finset.mem_insert_self _ _)
    have h2 : ∀ j ∈ s, f j ∈ TaylorLogMetric.Qbar := fun j hj => h j (Finset.mem_insert_of_mem hj)
    have h3 := sum_mem h2
    rw [Finset.sum_insert hk, Finset.sum_insert hk, ← ih h2]
    simp only [TaylorLogMetric.lamC, dif_pos h1, dif_pos h3, dif_pos (add_mem h1 h3)]
    exact map_add lam ⟨_, h1⟩ ⟨_, h3⟩

/- English proof (translation)
Simplify using `using lamC_sum lam (∅ : Finset Unit) (fun _ => 0) (by simp)`.
-/
theorem lamC_zero' : TaylorLogMetric.lamC lam 0 = 0 := by simpa using lamC_sum lam (∅ : Finset Unit) (fun _ => 0) (by simp)

/- English proof (translation)
Establish `hm : (n : ℂ)⁻¹ * k ∈ TaylorLogMetric.Qbar` using `mul_mem (inv_mem (natCast_mem _ n)) (natCast_mem _ k)`. Establish `e : TaylorLogMetric.lamC lam ((n : ℂ)⁻¹ * k) = (n : ℂ_[p])⁻¹ * k`. Simplify using `only [TaylorLogMetric.lamC, dif_pos hm]`. Establish `: (⟨_, hm⟩ : TaylorLogMetric.Qbar) = (n : TaylorLogMetric.Qbar)⁻¹ * k` using `Subtype.ext (by simp)`. Rewrite using `[this]`.

Simplify using the standard rewrite rules. Take `⟨d, hd⟩` from `h`. Establish `hc1 : ‖(c : ℂ_[p])‖ = 1`. Use `PadicComplex.norm_extends' p (c : ℚ_[p])` as an intermediate fact. Rewrite `this` using `[Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hc)]`.

Simplify using `using this`. Establish `hn' : (n : ℂ_[p]) ≠ 0` using `by exact_mod_cast hn`. Establish `e2 : (n : ℂ_[p])⁻¹ * k * c = d`. Establish `: (k : ℂ_[p]) * c = n * d` using `by exact_mod_cast hd`. Rewrite using `[mul_assoc, this]`.

Clear the denominators using the available nonvanishing facts. Use `IsUltrametricDist.norm_natCast_le_one ℂ_[p] d` as an intermediate fact. Rewrite `this` using `[← e2, norm_mul, hc1, mul_one, ← e]`. Then use the resulting hypothesis.
-/
theorem norm_lamC_ratio {n k c : ℕ} (hn : n ≠ 0) (hc : ¬ p ∣ c) (h : n ∣ k * c) :
    ‖TaylorLogMetric.lamC lam ((n : ℂ)⁻¹ * k)‖ ≤ 1 := by
  have hm : (n : ℂ)⁻¹ * k ∈ TaylorLogMetric.Qbar := mul_mem (inv_mem (natCast_mem _ n)) (natCast_mem _ k)
  have e : TaylorLogMetric.lamC lam ((n : ℂ)⁻¹ * k) = (n : ℂ_[p])⁻¹ * k := by
    simp only [TaylorLogMetric.lamC, dif_pos hm]
    have : (⟨_, hm⟩ : TaylorLogMetric.Qbar) = (n : TaylorLogMetric.Qbar)⁻¹ * k := Subtype.ext (by simp)
    rw [this]; simp
  obtain ⟨d, hd⟩ := h
  have hc1 : ‖(c : ℂ_[p])‖ = 1 := by
    have := PadicComplex.norm_extends' p (c : ℚ_[p])
    rw [Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hc)] at this
    simpa using this
  have hn' : (n : ℂ_[p]) ≠ 0 := by exact_mod_cast hn
  have e2 : (n : ℂ_[p])⁻¹ * k * c = d := by
    have : (k : ℂ_[p]) * c = n * d := by exact_mod_cast hd
    rw [mul_assoc, this]; field_simp
  have := IsUltrametricDist.norm_natCast_le_one ℂ_[p] d
  rwa [← e2, norm_mul, hc1, mul_one, ← e] at this

end Place

section Ops

variable {X : Fields} (A : Amb X) {a b : ℕ}

/- English proof (translation)
Rewrite using `[← Complex.exp_int_mul_two_pi_mul_I (-n)]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exp_int (n : ℤ) : Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * ((n : ℝ) : ℂ)) = 1 := by
  rw [← Complex.exp_int_mul_two_pi_mul_I (-n)]
  congr 1
  push_cast
  ring

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `only [Wx, opU]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Wx_mul (x : HomE X.E a b) (c : ℂ) (F : VCx X.Tau a b → ℂ) :
    Wx A x (fun z => c * F z) = fun z => c * Wx A x F z := by
  funext z
  simp only [Wx, opU]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `only [Wx, opU, Finset.sum_mul, Finset.mul_sum]`.
-/
theorem Wx_sum {κ : Type} (x : HomE X.E a b) (s : Finset κ) (F : κ → VCx X.Tau a b → ℂ) :
    Wx A x (fun z => ∑ k ∈ s, F k z) = fun z => ∑ k ∈ s, Wx A x (F k) z := by
  funext z
  simp only [Wx, opU, Finset.sum_mul, Finset.mul_sum]

/- English proof (translation)
Take `⟨n, hn⟩` from `h`. Rewrite using `[(GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b).1, hn, exp_int]`. Simplify using the standard rewrite rules.
-/
theorem Wx_Wx_of_int {x y : HomE X.E a b} (h : ∃ n : ℤ, coc A x y = n) (F : VCx X.Tau a b → ℂ) :
    Wx A x (Wx A y F) = Wx A (x + y) F := by
  obtain ⟨n, hn⟩ := h
  rw [(GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b).1, hn, exp_int]
  simp

/- English proof (translation)
Rewrite using `[← Wx_Wx_of_int A h, (GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b).2.1, (GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b).1 (-t), Wx_mul, neg_add_eq_sub]`. Use function extensionality and compare the values at `z`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Wx_neg_add {y₁ y₂ : HomE X.E a b} (t : HomE X.E a b) (h : ∃ n : ℤ, coc A y₁ y₂ = n) (F : VCx X.Tau a b → ℂ) :
    Wx A (-t) (Wx A (y₁ + y₂) F) = fun z =>
      Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (coc A (-t) y₂ : ℂ)) * brkE A y₁ (-t) * Wx A y₁ (Wx A (y₂ - t) F) z := by
  rw [← Wx_Wx_of_int A h, (GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b).2.1, (GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b).1 (-t), Wx_mul, neg_add_eq_sub]
  funext z
  ring

/- English proof (translation)
Take `⟨-, -, -, h4, h5, -⟩` from `GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b`. Rewrite using `[h5, h5, h5, (h4 t y y').2.2.2, ← Complex.exp_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem brkE_add_left (y y' t : HomE X.E a b) : brkE A (y + y') t = brkE A y t * brkE A y' t := by
  obtain ⟨-, -, -, h4, h5, -⟩ := GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b
  rw [h5, h5, h5, (h4 t y y').2.2.2, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/- English proof (translation)
Take `⟨-, -, -, h4, h5, -⟩` from `GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b`. Rewrite using `[h5, h5, h5, (h4 t t' y).2.2.1, ← Complex.exp_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem brkE_add_right (y t t' : HomE X.E a b) : brkE A y (t + t') = brkE A y t * brkE A y t' := by
  obtain ⟨-, -, -, h4, h5, -⟩ := GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b
  rw [h5, h5, h5, (h4 t t' y).2.2.1, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/- English proof (translation)
Establish `h6` using `(GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b).2.2.2.2.2.1`. Establish `h` using `(GlobalTheory.T.addSubgroup_reps_existence_card_sum _).2.2.2.1 ℂ M _ R (fun y => brkE A y s) hR (fun x _ y _ => brkE_add_left A x y s) (by`. Introduce and unpack `_ ⟨m, hm, rfl⟩ hM`. Express the relevant statement in the definitionally equal form `((N₁ : X.E) * u) • m ∈ M at hM`. Express the relevant statement in the definitionally equal form `brkE A (((N₁ : X.E) * u) • m) s = 1`.

Rewrite `hM`, the goal using `[mul_smul]`. Rewrite using `[h6, ← star_natCast, ← hadj]`. Conclude with `(hsd _).1 hs _ (mem_of_coprime M hN hM (hpu m hm)))`. Distinguish the cases in `hc : ∀ y ∈ scl ((N₁ : X.E) * u) M, brkE A y s = 1`. Use `Or.inr ⟨h.1 hc, (star u * N₁) • s, (hsd _).2 fun m hm => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hadj, star_mul, star_star, star_natCast, ← h6]`. Conclude with `hc _ ⟨m, hm, rfl⟩`. Express the relevant statement in the definitionally equal form `u • (star u * N₁) • s = _`. Rewrite using `[smul_smul, ← mul_assoc, hu, one_mul]`. Conclude with `Or.inl (h.2 hc)`.
-/
theorem char_sum (M : AddSubgroup (HomE X.E a b)) (hsd : ∀ x, x ∈ M ↔ ∀ y ∈ M, ∃ n : ℤ, imH A x y = n)
    (hadj : ∀ (r : X.E) (x y : HomE X.E a b), imH A (r • x) y = imH A x (star r • y))
    {u : X.E} (hu : u * star u = 1) {p N₁ : ℕ} (hpu : ∀ y ∈ M, (p : X.E) • u • y ∈ M) (hN : Nat.Coprime N₁ p)
    {R : Finset (HomE X.E a b)} (hR : IsReps M (scl ((N₁ : X.E) * u) M) R) {s : HomE X.E a b} (hs : (N₁ : X.E) • s ∈ M) :
    ∑ y ∈ R, brkE A y s = 0 ∨ (∑ y ∈ R, brkE A y s = R.card ∧ (N₁ : X.E) • s ∈ scl u M) := by
  have h6 := (GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b).2.2.2.2.2.1
  have h := (GlobalTheory.T.addSubgroup_reps_existence_card_sum _).2.2.2.1 ℂ M _ R (fun y => brkE A y s) hR (fun x _ y _ => brkE_add_left A x y s) (by
    rintro _ ⟨m, hm, rfl⟩ hM
    change ((N₁ : X.E) * u) • m ∈ M at hM
    change brkE A (((N₁ : X.E) * u) • m) s = 1
    rw [mul_smul] at hM ⊢
    rw [h6, ← star_natCast, ← hadj]
    exact (hsd _).1 hs _ (mem_of_coprime M hN hM (hpu m hm)))
  by_cases hc : ∀ y ∈ scl ((N₁ : X.E) * u) M, brkE A y s = 1
  · refine Or.inr ⟨h.1 hc, (star u * N₁) • s, (hsd _).2 fun m hm => ?_, ?_⟩
    · rw [hadj, star_mul, star_star, star_natCast, ← h6]
      exact hc _ ⟨m, hm, rfl⟩
    · change u • (star u * N₁) • s = _
      rw [smul_smul, ← mul_assoc, hu, one_mul]
  · exact Or.inl (h.2 hc)

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Establish `hu0 : u ≠ 0` using `left_ne_zero_of_mul_eq_one hu`. Take `⟨k, rfl⟩` from `hd`. Establish `hN0 : (N₀ : X.E) ≠ 0`. Introduce and unpack `h`.

Rewrite `hN` using `[Nat.cast_eq_zero.1 h]`. Conclude with `hp.one_lt.ne' (by simpa using hN)`. Establish `hc : ∀ y : HomE X.E a b, ((N₀ : X.E) * u) • ((N₀ : X.E) * u)⁻¹ • y = y` using `fun y => smul_inv_smul₀ (mul_ne_zero hN0 hu0) y`. Establish `hs : ∀ x ∈ M, ((N₀ * k : ℕ) : X.E) • (x - t) ∈ M` using `fun x hx => by`. Rewrite using `[smul_sub]`.

Conclude with `sub_mem (nat_smul_mem M _ hx) ht`. Use `clo_comb (Sup' := Sup) (tab' := tab) (M' := Set.univ) hJ R (fun y _ => TaylorLogMetric.lamC lam (γ * brkE A y (-t))) (fun y m => (((N₀ : X.E) * u)⁻¹ • y, m)) (by` as an intermediate fact. Introduce `y hy m _`. Take `⟨z, hz, rfl⟩` from `mem_scl.1 (hR.1 y hy)`. Express the relevant statement in the definitionally equal form `((N₀ : X.E) * u)⁻¹ • (((N₀ * k : ℕ) : X.E) * u) • z ∈ M`.

Rewrite using `[smul_smul, show ((N₀ : X.E) * u)⁻¹ * (((N₀ * k : ℕ) : X.E) * u) = k by push_cast; field_simp]`. Conclude with `nat_smul_mem M k hz)`. Use the proof step `(fun x => TaylorLogMetric.lamC lam (γ * ∑ y ∈ R, brkE A y (x - t))) (fun x hx => by`. Break down `char_sum A M hsd hadj hu hpu hN hR (hs x hx) with h | ⟨h, -⟩` into its components or cases. Simplify using `[h, lamC_zero']`.

Rewrite using `[h]) (fun x hx hn => by` and apply the resulting hypothesis. Break down `char_sum A M hsd hadj hu hpu hN hR (hs x hx) with h | ⟨-, h⟩` into its components or cases. Simplify using `[h, lamC_zero']`. Conclude with `absurd (hSup x h) hn) (fun x _ m _ => by`. Rewrite using `[Finset.mul_sum, lamC_sum _ _ _ (fun y _ => mul_mem hγ (hq _ _)), Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Simplify using `only [hc]`. Rewrite using `[← mul_assoc, ← lamC_mul lam (mul_mem hγ (hq _ _)) (hq _ _), mul_assoc γ, ← brkE_add_right, neg_add_eq_sub])`. Simplify `this` using `only [hc]`.
-/
theorem clo_class {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (M : AddSubgroup (HomE X.E a b))
    (hsd : ∀ x, x ∈ M ↔ ∀ y ∈ M, ∃ n : ℤ, imH A x y = n)
    (hadj : ∀ (r : X.E) (x y : HomE X.E a b), imH A (r • x) y = imH A x (star r • y))
    (hq : ∀ y t : HomE X.E a b, brkE A y t ∈ TaylorLogMetric.Qbar)
    {u : X.E} (hu : u * star u = 1) {N₀ N₁ : ℕ} (hpu : ∀ y ∈ M, (p : X.E) • u • y ∈ M) (hN : Nat.Coprime N₁ p) (hd : N₀ ∣ N₁)
    {R : Finset (HomE X.E a b)} (hR : IsReps M (scl ((N₁ : X.E) * u) M) R) {t : HomE X.E a b} (ht : (N₁ : X.E) • t ∈ M)
    {I : Type} (tab : HomE X.E a b → I → ℂ_[p]) (J : HomE X.E a b → I → ℂ_[p])
    (hJ : InIntClosure (M : Set (HomE X.E a b)) (fun x (k : HomE X.E a b × I) =>
      TaylorLogMetric.lamC lam (brkE A (((N₀ : X.E) * u) • k.1) x) * tab x k.2) {k | k.1 ∈ M} fun k => J (((N₀ : X.E) * u) • k.1) k.2)
    {γ : ℂ} (hγ : γ ∈ TaylorLogMetric.Qbar) (hγ1 : ‖TaylorLogMetric.lamC lam (γ * R.card)‖ ≤ 1) (Sup : Set (HomE X.E a b))
    (hSup : ∀ x, (N₁ : X.E) • (x - t) ∈ scl u M → x ∈ Sup) :
    InIntClosure Sup tab Set.univ fun m => ∑ y ∈ R, TaylorLogMetric.lamC lam (γ * brkE A y (-t)) * J y m := by
  have hp : p.Prime := Fact.out
  have hu0 : u ≠ 0 := left_ne_zero_of_mul_eq_one hu
  obtain ⟨k, rfl⟩ := hd
  have hN0 : (N₀ : X.E) ≠ 0 := by
    rintro h
    rw [Nat.cast_eq_zero.1 h] at hN
    exact hp.one_lt.ne' (by simpa using hN)
  have hc : ∀ y : HomE X.E a b, ((N₀ : X.E) * u) • ((N₀ : X.E) * u)⁻¹ • y = y := fun y => smul_inv_smul₀ (mul_ne_zero hN0 hu0) y
  have hs : ∀ x ∈ M, ((N₀ * k : ℕ) : X.E) • (x - t) ∈ M := fun x hx => by
    rw [smul_sub]; exact sub_mem (nat_smul_mem M _ hx) ht
  have := clo_comb (Sup' := Sup) (tab' := tab) (M' := Set.univ) hJ R (fun y _ => TaylorLogMetric.lamC lam (γ * brkE A y (-t)))
    (fun y m => (((N₀ : X.E) * u)⁻¹ • y, m)) (by
      intro y hy m _
      obtain ⟨z, hz, rfl⟩ := mem_scl.1 (hR.1 y hy)
      change ((N₀ : X.E) * u)⁻¹ • (((N₀ * k : ℕ) : X.E) * u) • z ∈ M
      rw [smul_smul, show ((N₀ : X.E) * u)⁻¹ * (((N₀ * k : ℕ) : X.E) * u) = k by push_cast; field_simp]
      exact nat_smul_mem M k hz)
    (fun x => TaylorLogMetric.lamC lam (γ * ∑ y ∈ R, brkE A y (x - t))) (fun x hx => by
      rcases char_sum A M hsd hadj hu hpu hN hR (hs x hx) with h | ⟨h, -⟩
      · simp [h, lamC_zero']
      · rwa [h]) (fun x hx hn => by
      rcases char_sum A M hsd hadj hu hpu hN hR (hs x hx) with h | ⟨-, h⟩
      · simp [h, lamC_zero']
      · exact absurd (hSup x h) hn) (fun x _ m _ => by
      rw [Finset.mul_sum, lamC_sum _ _ _ (fun y _ => mul_mem hγ (hq _ _)), Finset.sum_mul]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [hc]
      rw [← mul_assoc, ← lamC_mul lam (mul_mem hγ (hq _ _)) (hq _ _), mul_assoc γ, ← brkE_add_right, neg_add_eq_sub])
  simpa only [hc] using this

end Ops

/- English proof (translation)
Introduce `X A a b S SG ϖ p g cA N N' _ lam ι un hC hN hN' hP x hx hxϖ`. Take `⟨hA0, b1, b2, b3, -, b5, b6, -⟩` from `GlobalTheory.T.periodLattice_halfLattice_inclusions_splitPrime X A a b S SG ϖ p g cA N N' hC hN hN'`. Take `⟨hX, hL, -, hsm, hp, hϖ, -, hS, -, hg, hcA⟩` from `hC`. Establish `hL'` using `hL`. Take `⟨hδ, -, hconj, hAU, hFG, hfacts⟩` from `hL'`.

Take `⟨hfix, hLa⟩` from `hfacts N N' hN hN'`. Take `⟨-, hfull, hfin0, -⟩` from `GlobalTheory.T.per_relIndex_ne_zero_and_mem_locP_iff X A a b N N' hFG hA0 hN hN'`. Take `⟨hadj', hsd, -⟩` from `GlobalTheory.T.heisenbergCocycleForm_integral_selfDual X A a b N N' hX hδ hLa`. Take `⟨-, -, h3, h4, h5, -, h7, h8⟩` from `GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b`. Take `⟨r1, r2, r3, -, -⟩` from `GlobalTheory.T.addSubgroup_reps_existence_card_sum (HomE X.E a b)`.

Establish `hroot` using `(GlobalTheory.T.algebraicNumbers_padicPlaces_facts X.K p A.σ₀ ι).2.2 lam`. Establish `hadj : ∀ (r : X.E) (x y : HomE X.E a b), imH A (r • x) y = imH A x (star r • y)` using `fun r x y => (hadj' r x y).2`. Establish `pos : ∀ k : ℕ, Nat.Coprime k p → 0 < k` using `fun k hk => Nat.pos_of_ne_zero (by`. Introduce and unpack `rfl`. Conclude with `hp.one_lt.ne' (by simpa using hk))`.

Establish `hg0` using `pos g hg`. Establish `hcA0` using `pos cA hcA`. Establish `hpg0 : 0 < p * g` using `Nat.mul_pos hp.pos hg0`. Take `⟨t, ht, htx⟩` from `GlobalTheory.T.exists_lift_halfLattice_rational X A a b S N N' cA (p * g) hFG hA0 hconj hAU hN hN' hcA0 hpg0 x hx`. Take `⟨n, hn0, hnd, hth⟩` from `GlobalTheory.T.theta_movedCosetIndicator_vacuum_shape X A a b S N N' cA (p * g) hX hL hA0 hN hN' hcA0 hpg0`.

Use `replace hth := hth x hx t ht htx`. Use `replace b3 := b3 x hx hxϖ t ht htx`. Establish `hE : (ϖ : X.E) * star (ϖ : X.E) = p`. Use `congrArg (fun r : 𝓞 X.E => (r : X.E)) hϖ` as an intermediate fact. Simplify using `only [map_mul, map_natCast, RingOfIntegers.coe_eq_algebraMap] at this`.

Conclude with `this`. Establish `hpE : (p : X.E) ≠ 0` using `Nat.cast_ne_zero.2 hp.ne_zero`. Establish `hϖ0 : (ϖ : X.E) ≠ 0` using `left_ne_zero_of_mul (hE ▸ hpE)`. Establish `hϖ1 : star (ϖ : X.E) ≠ 0` using `right_ne_zero_of_mul (hE ▸ hpE)`. Establish `hO : ∀ y ∈ per A N N', (ϖ : X.E) • y ∈ per A N N'` using `fun y hy => (per A N N').smul_mem ϖ hy`.

Establish `hO' : ∀ y ∈ per A N N', star (ϖ : X.E) • y ∈ per A N N'` using `fun y hy => (per A N N').smul_mem (X.conjO ϖ) hy`. Establish `hfin : ∀ k : ℕ, k ≠ 0 → (scl (k : X.E) (per A N N').toAddSubgroup).relIndex (per A N N').toAddSubgroup ≠ 0` using `fun k hk => by`. Use `hfin0 (k : 𝓞 X.E) (Nat.cast_ne_zero.2 hk)` as an intermediate fact. Rewrite `this` using `[show ((k : 𝓞 X.E) : X.E) = k by simp]`. Then use the resulting hypothesis. Establish `hSup : ∀ (k : ℕ), Nat.Coprime k p → ∀ y, (k : X.E) • (y - t) ∈ scl ((ϖ : X.E) / star (ϖ : X.E)) (per A N N').toAddSubgroup → y - x ∈ mulLat p (homAt (divs ϖ) N N')`.

Introduce `k hk y hy`. Rewrite using `[← sub_add_sub_cancel y t x]`. Use `add_mem (b5 _ k hk hy) ?_` and prove the remaining obligations. Take `⟨w, hw, hw'⟩` from `htx`. Use `⟨(g : 𝓞 X.E) • w, Submodule.smul_mem _ _ fun P hP => hw P ((hS P).2 (Or.inl ?_)), ?_⟩` and prove the remaining obligations.

Conclude with `(mem_divs (by rintro rfl; exact hϖ0 (by simp)) P).1 hP`. Rewrite using `[← hw']`. Simplify using `only [LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_mul, mul_smul]`. Establish `hfixW : ∀ l ∈ per A N N', Wx A l (A.e a b N N') = A.e a b N N'` using `fun l hl =>`. Use function extensionality and compare the values at `fun z => hfix _ ⟨l, hl, rfl⟩ z`.

Use `replace hP := hP N N' hN hN'`. Use `replace hsm := hsm N N' hN hN'`. Use `set u : X.E := (ϖ : X.E) / star (ϖ : X.E) with hu`. Use `set e := A.e a b N N'`. Use `set Θ := A.thInd S N N' (p * g) x`.

Use `set M : AddSubgroup (HomE X.E a b) := (per A N N').toAddSubgroup with hM`. Use `set B : AddSubgroup (HomE X.E a b) := (halfBO S (per A N N') (p * g)).toAddSubgroup with hB`. Express the relevant statement in the definitionally equal form `∀ y ∈ M, _ ∈ M at hO hO'`. Express the relevant statement in the definitionally equal form `∀ y ∈ M, _ ∈ B at b1`. Express the relevant statement in the definitionally equal form `∀ y ∈ B, _ ∈ M at b2`.

Express the relevant statement in the definitionally equal form `_ ∈ M at b3`. Express the relevant statement in the definitionally equal form `∀ x ∈ B, ∀ y ∈ B, _ at b6`. Express the relevant statement in the definitionally equal form `∀ x, x ∈ M ↔ ∀ y ∈ M, _ at hsd`. Express the relevant statement in the definitionally equal form `∀ x, ∃ n : ℕ, 0 < n ∧ _ ∈ M at hfull`. Establish `huu : u * star u = 1` using `by rw [hu, star_div₀, star_star]; field_simp`.

Establish `hpu : ∀ y ∈ M, (p : X.E) • u • y ∈ M` using `fun y hy => by`. Use `hO _ (hO y hy)` as an intermediate fact. Rewrite `this` using `[smul_smul, show (ϖ : X.E) * ϖ = p * u by rw [← hE, hu]; field_simp, mul_smul]`. Then use the resulting hypothesis. Establish `hpu' : ∀ y ∈ M, (p : X.E) • y = u • star (ϖ : X.E) • star (ϖ : X.E) • y` using `fun y _ => by`. Rewrite using `[smul_smul, smul_smul, ← hE, hu]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Establish `hBM : ∀ y ∈ B, ((p * g : ℕ) : X.E) • y ∈ M` using `fun y hy => by`. Use `hO _ (hO _ (b2 y hy))` as an intermediate fact. Rewrite `this` using `[smul_smul, smul_smul]`.

Use `this using 2` and compare the differences between its conclusion and the goal. Use `push_cast`. Rewrite using `[← hE]`. Clear the denominators using the available nonvanishing facts. Establish `hMB : ∀ y ∈ M, ((p * g : ℕ) : X.E) • y ∈ B` using `fun y hy => by`.

Use `b1 _ (hO' _ (hO' y hy))` as an intermediate fact. Rewrite `this` using `[mul_smul, ← hpu' y hy, smul_smul, mul_comm, ← Nat.cast_mul]`. Then use the resulting hypothesis. Establish `hq : ∀ y s : HomE X.E a b, brkE A y s ∈ TaylorLogMetric.Qbar` using `fun y s => by`. Take `⟨r, hr⟩` from `rat_of_biadd (E := X.E) (imH A) (fun x y z => (h4 x y z).2.2.1) (fun x y z => (h4 x y z).2.2.2) M (fun x hx => (hsd x).1 hx) hfull s y`. Rewrite using `[h5, hr]`.

Conclude with `(hroot r).1`. Establish `hζ : ∀ y s : HomE X.E a b, Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (coc A s y : ℂ)) ∈ TaylorLogMetric.Qbar ∧ ‖TaylorLogMetric.lamC lam (Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (coc A s y : ℂ)))‖ = 1` using `fun y s => by`. Take `⟨r, hr⟩` from `rat_of_biadd (E := X.E) (coc A) (fun x y z => (h4 x y z).1) (fun x y z => (h4 x y z).2.1) B b6 (fun x => by`. Take `⟨k, hk, hx⟩` from `hfull x`. Conclude with `⟨p * g * k, Nat.mul_pos hpg0 hk, by rw [Nat.cast_mul, mul_smul]; exact hMB _ hx⟩) s y`.

Rewrite using `[hr]`. Conclude with `hroot r`. Establish `hpgE : ((p * g : ℕ) : X.E) ≠ 0` using `Nat.cast_ne_zero.2 hpg0.ne'`. Establish `hfB : M.relIndex B ≠ 0` using `relIndex_ne_zero_of_smul hpgE (hfin _ hpg0.ne') hBM`. Establish `hB₂ : scl (p : X.E) B ≤ B`.

Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `nat_smul_mem (E := X.E) B p hy`. Take `⟨R, hR⟩` from `r1 M B hfB`. Take `⟨R₂, hR₂⟩` from `r1 M (scl (p : X.E) B) fun h => hfB (AddSubgroup.relIndex_eq_zero_of_le_right hB₂ h)`. Establish `hg₂ : ∀ y ∈ scl (p : X.E) B, (g : X.E) • y ∈ M`.

Introduce and unpack `_ ⟨y, hy, rfl⟩`. Use `hBM y hy` as an intermediate fact. Rewrite `this` using `[mul_comm, Nat.cast_mul, mul_smul]`. Then use the resulting hypothesis. Establish `hcg : Nat.Coprime (cA * g) p` using `Nat.Coprime.mul_left hcA hg`. Establish `hP'` using `fun y (hy : y ∈ R₂) => hP (y - t) ⟨cA * g, hcg, by`.

Rewrite using `[smul_sub]`. Use `M.sub_mem ?_ b3` and prove the remaining obligations. Rewrite using `[Nat.cast_mul, mul_smul]`. Conclude with `nat_smul_mem M cA (hg₂ y (hR₂.1 y hy))⟩`. Use `choose! N₀ hN₀ halg hclo using hP'`.

Take `⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, N₁ = cA * g * ∏ y ∈ R₂, N₀ y` from `⟨_, rfl⟩`. Establish `hN₁p : Nat.Coprime N₁ p` using `hN₁ ▸ Nat.Coprime.mul_left hcg (Nat.Coprime.prod_left hN₀)`. Establish `hdv : ∀ y ∈ R₂, N₀ y ∣ N₁` using `fun y hy => hN₁ ▸ Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hy) _`. Establish `hN₁t : (N₁ : X.E) • t ∈ M`. Rewrite using `[hN₁, mul_comm, Nat.cast_mul, mul_smul]`.

Conclude with `nat_smul_mem M _ b3`. Establish `hB₁ : scl ((N₁ : X.E) * u) M ≤ B`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Use `b1 _ (nat_smul_mem (E := X.E) M (cA * ∏ y ∈ R₂, N₀ y) hy)` as an intermediate fact. Rewrite `this` using `[smul_smul]`.

Express the relevant statement in the definitionally equal form `((N₁ : X.E) * u) • y ∈ B`. Use `this using 2` and compare the differences between its conclusion and the goal. Rewrite using `[hN₁]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨R₁, hR₁⟩` from `r1 M (scl ((N₁ : X.E) * u) M) fun h => hfB (AddSubgroup.relIndex_eq_zero_of_le_right hB₁ h)`. Establish `hpK : ∀ y ∈ scl u M, (p : X.E) • y ∈ M`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `hpu y hy`. Establish `hMK : ∀ y ∈ M, (p : X.E) • y ∈ scl u M` using `fun y hy => ⟨_, hO' _ (hO' y hy), (hpu' y hy).symm⟩`.

Establish `hcard : R₁.card = (scl u M).relIndex M`. Rewrite using `[r2 _ _ _ hR₁, ← scl_scl, relIndex_scl_nat M _ hN₁p hpK]`. Use `GlobalTheory.T.relIndex_eq_of_selfDual_alternating _ (imH A) M (scl u M) (fun x y z => (h4 x y z).2.2.1) (fun x y => by rw [h3, h3]; ring) hsd (fun x => ?_) (relIndex_ne_zero_of_smul hpE (hfin _ hp.ne_zero) hpK) (fun h => hfin _ hp.ne_zero (AddSubgroup.relIndex_eq_zero_of_le_left …` and prove the remaining obligations. Establish `e1 : ∀ y, imH A x (u • y) = imH A (star u • x) y` using `fun y => by rw [hadj, star_star]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨m, hm, rfl⟩ _ ⟨y, hy, rfl⟩`. Express the relevant statement in the definitionally equal form `∃ n : ℤ, imH A (u • m) (u • y) = n`. Rewrite using `[hadj, smul_smul, mul_comm, huu, one_smul]`. Conclude with `(hsd m).1 hm y hy`. Introduce `h`.

Use `⟨star u • x, (hsd _).2 fun y hy => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← e1]`. Conclude with `h _ ⟨y, hy, rfl⟩`. Express the relevant statement in the definitionally equal form `u • star u • x = x`. Rewrite using `[smul_smul, huu, one_smul]`.

Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `hMK y hy`. Take `⟨c, hc, hcd⟩` from `relIndex_dvd (E := X.E) M B (scl u M) hp hg (by`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Use `b1 y hy` as an intermediate fact.

Rewrite using `[mul_smul] at this)` and apply the resulting hypothesis. Use the proof step `(fun h => hfin _ hpg0.ne' (AddSubgroup.relIndex_eq_zero_of_le_left (by`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Use `⟨hMB y hy, ?_⟩` and prove the remaining obligations. Use `hMK _ (nat_smul_mem (E := X.E) M g hy)` as an intermediate fact.

Rewrite using `[smul_smul, ← Nat.cast_mul] at this) h))` and apply the resulting hypothesis. Establish `hnorm` using `norm_lamC_ratio lam hn0 hc (hcard ▸ hnd.trans hcd)`. Establish `hnq : (n : ℂ)⁻¹ ∈ TaylorLogMetric.Qbar` using `inv_mem (natCast_mem _ n)`. Establish `hsum` using `r3 _ M B _ _ R R₁ R₂ (fun y => Wx A (-t) (Wx A y e)) hB₁ hB₂ (fun y hy => by`. Take `⟨s, s', hs⟩` from `Nat.isCoprime_iff_coprime.2 (Nat.Coprime.mul_left hN₁p hg)`.

Use `⟨_, ⟨_, zsmul_mem (b2 y hy) s, rfl⟩, _, ⟨_, zsmul_mem hy s', rfl⟩, ?_⟩` and prove the remaining obligations. Establish `hs' : (s : X.E) * (N₁ * g) + s' * p = 1` using `by exact_mod_cast congrArg (Int.cast : ℤ → X.E) hs`. Simplify using `only [DistribSMul.toAddMonoidHom_apply, ← Int.cast_smul_eq_zsmul X.E, smul_smul, ← add_smul]`. Rewrite using `[show (N₁ : X.E) * u * (s * (g * (star (ϖ : X.E) / ϖ))) + p * s' = 1 by rw [← hs', hu]; field_simp, one_smul, sub_self]`. Conclude with `zero_mem _)`.

Use the proof step `(fun y₁ h₁ y₂ h₂ h => by`. Use `mem_of_coprime (E := X.E) M hg ?_ ?_` and prove the remaining obligations. Use `sub_mem (nat_smul_mem (E := X.E) M g h) (hg₂ y₂ h₂)` as an intermediate fact. Rewrite `this` using `[smul_add, add_sub_cancel_right]`. Then use the resulting hypothesis. Take `⟨m, hm, rfl⟩` from `mem_scl.1 h₁`.

Rewrite using `[mul_smul, smul_comm]`. Conclude with `nat_smul_mem M _ (hpu m hm))`. Use `hR hR₁ hR₂ (fun y hy l hl hl' => by`. Rewrite using `[← Wx_Wx_of_int A (b6 y hy l hl'), hfixW l hl])`. Use `set γ : HomE X.E a b → ℂ := fun y => (n : ℂ)⁻¹ * Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (coc A (-t) y : ℂ)) with hγ`.

Establish `hγq : ∀ y, γ y ∈ TaylorLogMetric.Qbar` using `fun y => mul_mem hnq (hζ y _).1`. Establish `hΘ : Θ = fun z => ∑ q ∈ R₂ ×ˢ R₁, (γ q.1 * brkE A q.2 (-t)) * Wx A q.2 (Wx A (q.1 - t) e) z`. Rewrite using `[hth R hR, Wx_sum]`. Use function extensionality and compare the values at `z`. Use `congrFun hsum z` as an intermediate fact.

Simplify using `only [Finset.sum_apply] at this`. Use `beta_reduce`. Rewrite using `[this, Finset.sum_product, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun y₂ h₂ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun y₁ h₁ => ?_` and prove the remaining obligations. Rewrite using `[Wx_neg_add A t (b6 _ (hB₁ (hR₁.1 _ h₁)) _ (hB₂ (hR₂.1 _ h₂))), hγ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hjet : ∀ m, jetC A.cD Θ m = ∑ q ∈ R₂ ×ˢ R₁, (γ q.1 * brkE A q.2 (-t)) * jetC A.cD (Wx A q.2 (Wx A (q.1 - t) e)) m` using `fun m => by`. Rewrite using `[hΘ]`.

Conclude with `h8 _ (R₂ ×ˢ R₁) (fun q => γ q.1 * brkE A q.2 (-t)) (fun q => Wx A q.2 (Wx A (q.1 - t) e)) (fun q _ => h7 q.2 _ (h7 (q.1 - t) e hsm)) m`. Establish `halg' : ∀ q ∈ R₂ ×ˢ R₁, ∀ m, jetC A.cD (Wx A q.2 (Wx A (q.1 - t) e)) m ∈ TaylorLogMetric.Qbar`. Introduce and unpack `⟨y₂, y₁⟩ hq' m`. Take `⟨h₂, h₁⟩` from `Finset.mem_product.1 hq'`. Take `⟨z, hz, rfl⟩` from `mem_scl.1 (hR₁.1 _ h₁)`.

Take `⟨k, hk⟩` from `hdv y₂ h₂`. Use `halg y₂ h₂ _ (nat_smul_mem (E := X.E) M k hz) m` as an intermediate fact. Rewrite `this` using `[smul_smul]`. Rewrite using `[show (N₁ : X.E) * u = N₀ y₂ * u * k by rw [hk]; push_cast; ring]` and apply the resulting hypothesis. Use `⟨fun m => hjet m ▸ sum_mem fun q hq' => mul_mem (mul_mem (hγq _) (hq _ _)) (halg' q hq' m), ?_⟩` and prove the remaining obligations.

Use `clo_congr (clo_sum R₂ _ fun y₂ h₂ => clo_class A lam M hsd hadj hq huu hpu hN₁p (hdv y₂ h₂) hR₁ hN₁t (ptTab ι un) (fun y m => TaylorLogMetric.lamC lam (jetC A.cD (Wx A y (Wx A (y₂ - t) e)) m)) (hclo y₂ h₂) (hγq y₂) ?_ _ (hSup N₁ hN₁p)) subset_rfl subset_rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[hγ, mul_right_comm, lamC_mul lam (mul_mem hnq (natCast_mem _ _)) (hζ _ _).1, norm_mul, (hζ _ _).2, mul_one]`. Conclude with `hnorm`. Rewrite using `[hjet, lamC_sum _ _ _ fun q hq' => mul_mem (mul_mem (hγq _) (hq _ _)) (halg' q hq' m), Finset.sum_product]`. Use `Finset.sum_congr rfl fun y₂ h₂ => Finset.sum_congr rfl fun y₁ h₁ => ?_` and prove the remaining obligations.

Conclude with `lamC_mul lam (mul_mem (hγq _) (hq _ _)) (halg' _ (Finset.mk_mem_product h₂ h₁) m)`.
-/
theorem moments_thInd : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S SG : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (p g cA : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : X.K →+* ℂ_[p]) (un : X.Tau → ℂ_[p]), Ctx A a b S SG ϖ p g cA → IsSdLat N → IsSdLat N' → PtMom A a b lam ι un ((ϖ : X.E) / star (ϖ : X.E)) → ∀ x ∈ divLat cA (homAt S N N'), x ∈ homAt (divs ϖ) N N' → (∀ m, jetC A.cD (A.thInd S N N' (p * g) x) m ∈ TaylorLogMetric.Qbar) ∧ InIntClosure {t | t - x ∈ mulLat p (homAt (divs ϖ) N N')} (ptTab ι un) Set.univ fun m => TaylorLogMetric.lamC lam (jetC A.cD (A.thInd S N N' (p * g) x) m) := by
  classical
  intro X A a b S SG ϖ p g cA N N' _ lam ι un hC hN hN' hP x hx hxϖ
  obtain ⟨hA0, b1, b2, b3, -, b5, b6, -⟩ := GlobalTheory.T.periodLattice_halfLattice_inclusions_splitPrime X A a b S SG ϖ p g cA N N' hC hN hN'
  obtain ⟨hX, hL, -, hsm, hp, hϖ, -, hS, -, hg, hcA⟩ := hC
  have hL' := hL
  obtain ⟨hδ, -, hconj, hAU, hFG, hfacts⟩ := hL'
  obtain ⟨hfix, hLa⟩ := hfacts N N' hN hN'
  obtain ⟨-, hfull, hfin0, -⟩ := GlobalTheory.T.per_relIndex_ne_zero_and_mem_locP_iff X A a b N N' hFG hA0 hN hN'
  obtain ⟨hadj', hsd, -⟩ := GlobalTheory.T.heisenbergCocycleForm_integral_selfDual X A a b N N' hX hδ hLa
  obtain ⟨-, -, h3, h4, h5, -, h7, h8⟩ := GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b
  obtain ⟨r1, r2, r3, -, -⟩ := GlobalTheory.T.addSubgroup_reps_existence_card_sum (HomE X.E a b)
  have hroot := (GlobalTheory.T.algebraicNumbers_padicPlaces_facts X.K p A.σ₀ ι).2.2 lam
  have hadj : ∀ (r : X.E) (x y : HomE X.E a b), imH A (r • x) y = imH A x (star r • y) := fun r x y => (hadj' r x y).2
  have pos : ∀ k : ℕ, Nat.Coprime k p → 0 < k := fun k hk => Nat.pos_of_ne_zero (by
    rintro rfl
    exact hp.one_lt.ne' (by simpa using hk))
  have hg0 := pos g hg
  have hcA0 := pos cA hcA
  have hpg0 : 0 < p * g := Nat.mul_pos hp.pos hg0
  obtain ⟨t, ht, htx⟩ := GlobalTheory.T.exists_lift_halfLattice_rational X A a b S N N' cA (p * g) hFG hA0 hconj hAU hN hN' hcA0 hpg0 x hx
  obtain ⟨n, hn0, hnd, hth⟩ := GlobalTheory.T.theta_movedCosetIndicator_vacuum_shape X A a b S N N' cA (p * g) hX hL hA0 hN hN' hcA0 hpg0
  replace hth := hth x hx t ht htx
  replace b3 := b3 x hx hxϖ t ht htx
  have hE : (ϖ : X.E) * star (ϖ : X.E) = p := by
    have := congrArg (fun r : 𝓞 X.E => (r : X.E)) hϖ
    simp only [map_mul, map_natCast, RingOfIntegers.coe_eq_algebraMap] at this
    exact this
  have hpE : (p : X.E) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hϖ0 : (ϖ : X.E) ≠ 0 := left_ne_zero_of_mul (hE ▸ hpE)
  have hϖ1 : star (ϖ : X.E) ≠ 0 := right_ne_zero_of_mul (hE ▸ hpE)
  have hO : ∀ y ∈ per A N N', (ϖ : X.E) • y ∈ per A N N' := fun y hy => (per A N N').smul_mem ϖ hy
  have hO' : ∀ y ∈ per A N N', star (ϖ : X.E) • y ∈ per A N N' := fun y hy => (per A N N').smul_mem (X.conjO ϖ) hy
  have hfin : ∀ k : ℕ, k ≠ 0 → (scl (k : X.E) (per A N N').toAddSubgroup).relIndex (per A N N').toAddSubgroup ≠ 0 :=
    fun k hk => by
      have := hfin0 (k : 𝓞 X.E) (Nat.cast_ne_zero.2 hk)
      rwa [show ((k : 𝓞 X.E) : X.E) = k by simp] at this
  have hSup : ∀ (k : ℕ), Nat.Coprime k p → ∀ y, (k : X.E) • (y - t) ∈
      scl ((ϖ : X.E) / star (ϖ : X.E)) (per A N N').toAddSubgroup → y - x ∈ mulLat p (homAt (divs ϖ) N N') := by
    intro k hk y hy
    rw [← sub_add_sub_cancel y t x]
    refine add_mem (b5 _ k hk hy) ?_
    obtain ⟨w, hw, hw'⟩ := htx
    refine ⟨(g : 𝓞 X.E) • w, Submodule.smul_mem _ _ fun P hP => hw P ((hS P).2 (Or.inl ?_)), ?_⟩
    · exact (mem_divs (by rintro rfl; exact hϖ0 (by simp)) P).1 hP
    · rw [← hw']
      simp only [LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_mul, mul_smul]
  have hfixW : ∀ l ∈ per A N N', Wx A l (A.e a b N N') = A.e a b N N' := fun l hl =>
    funext fun z => hfix _ ⟨l, hl, rfl⟩ z
  replace hP := hP N N' hN hN'
  replace hsm := hsm N N' hN hN'
  set u : X.E := (ϖ : X.E) / star (ϖ : X.E) with hu
  set e := A.e a b N N'
  set Θ := A.thInd S N N' (p * g) x
  set M : AddSubgroup (HomE X.E a b) := (per A N N').toAddSubgroup with hM
  set B : AddSubgroup (HomE X.E a b) := (halfBO S (per A N N') (p * g)).toAddSubgroup with hB
  change ∀ y ∈ M, _ ∈ M at hO hO'
  change ∀ y ∈ M, _ ∈ B at b1
  change ∀ y ∈ B, _ ∈ M at b2
  change _ ∈ M at b3
  change ∀ x ∈ B, ∀ y ∈ B, _ at b6
  change ∀ x, x ∈ M ↔ ∀ y ∈ M, _ at hsd
  change ∀ x, ∃ n : ℕ, 0 < n ∧ _ ∈ M at hfull
  have huu : u * star u = 1 := by rw [hu, star_div₀, star_star]; field_simp
  have hpu : ∀ y ∈ M, (p : X.E) • u • y ∈ M := fun y hy => by
    have := hO _ (hO y hy)
    rwa [smul_smul, show (ϖ : X.E) * ϖ = p * u by rw [← hE, hu]; field_simp, mul_smul] at this
  have hpu' : ∀ y ∈ M, (p : X.E) • y = u • star (ϖ : X.E) • star (ϖ : X.E) • y := fun y _ => by
    rw [smul_smul, smul_smul, ← hE, hu]; congr 1; field_simp
  have hBM : ∀ y ∈ B, ((p * g : ℕ) : X.E) • y ∈ M := fun y hy => by
    have := hO _ (hO _ (b2 y hy))
    rw [smul_smul, smul_smul] at this
    convert this using 2
    push_cast; rw [← hE]; field_simp
  have hMB : ∀ y ∈ M, ((p * g : ℕ) : X.E) • y ∈ B := fun y hy => by
    have := b1 _ (hO' _ (hO' y hy))
    rwa [mul_smul, ← hpu' y hy, smul_smul, mul_comm, ← Nat.cast_mul] at this
  have hq : ∀ y s : HomE X.E a b, brkE A y s ∈ TaylorLogMetric.Qbar := fun y s => by
    obtain ⟨r, hr⟩ := rat_of_biadd (E := X.E) (imH A) (fun x y z => (h4 x y z).2.2.1) (fun x y z => (h4 x y z).2.2.2) M
      (fun x hx => (hsd x).1 hx) hfull s y
    rw [h5, hr]; exact (hroot r).1
  have hζ : ∀ y s : HomE X.E a b, Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (coc A s y : ℂ)) ∈ TaylorLogMetric.Qbar ∧
      ‖TaylorLogMetric.lamC lam (Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (coc A s y : ℂ)))‖ = 1 := fun y s => by
    obtain ⟨r, hr⟩ := rat_of_biadd (E := X.E) (coc A) (fun x y z => (h4 x y z).1) (fun x y z => (h4 x y z).2.1) B b6
      (fun x => by
        obtain ⟨k, hk, hx⟩ := hfull x
        exact ⟨p * g * k, Nat.mul_pos hpg0 hk, by rw [Nat.cast_mul, mul_smul]; exact hMB _ hx⟩) s y
    rw [hr]; exact hroot r
  have hpgE : ((p * g : ℕ) : X.E) ≠ 0 := Nat.cast_ne_zero.2 hpg0.ne'
  have hfB : M.relIndex B ≠ 0 := relIndex_ne_zero_of_smul hpgE (hfin _ hpg0.ne') hBM
  have hB₂ : scl (p : X.E) B ≤ B := by
    rintro _ ⟨y, hy, rfl⟩
    exact nat_smul_mem (E := X.E) B p hy
  obtain ⟨R, hR⟩ := r1 M B hfB
  obtain ⟨R₂, hR₂⟩ := r1 M (scl (p : X.E) B) fun h => hfB (AddSubgroup.relIndex_eq_zero_of_le_right hB₂ h)
  have hg₂ : ∀ y ∈ scl (p : X.E) B, (g : X.E) • y ∈ M := by
    rintro _ ⟨y, hy, rfl⟩
    have := hBM y hy
    rwa [mul_comm, Nat.cast_mul, mul_smul] at this
  have hcg : Nat.Coprime (cA * g) p := Nat.Coprime.mul_left hcA hg
  have hP' := fun y (hy : y ∈ R₂) => hP (y - t) ⟨cA * g, hcg, by
    rw [smul_sub]
    refine M.sub_mem ?_ b3
    rw [Nat.cast_mul, mul_smul]
    exact nat_smul_mem M cA (hg₂ y (hR₂.1 y hy))⟩
  choose! N₀ hN₀ halg hclo using hP'
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, N₁ = cA * g * ∏ y ∈ R₂, N₀ y := ⟨_, rfl⟩
  have hN₁p : Nat.Coprime N₁ p := hN₁ ▸ Nat.Coprime.mul_left hcg (Nat.Coprime.prod_left hN₀)
  have hdv : ∀ y ∈ R₂, N₀ y ∣ N₁ := fun y hy => hN₁ ▸ Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hy) _
  have hN₁t : (N₁ : X.E) • t ∈ M := by
    rw [hN₁, mul_comm, Nat.cast_mul, mul_smul]
    exact nat_smul_mem M _ b3
  have hB₁ : scl ((N₁ : X.E) * u) M ≤ B := by
    rintro _ ⟨y, hy, rfl⟩
    have := b1 _ (nat_smul_mem (E := X.E) M (cA * ∏ y ∈ R₂, N₀ y) hy)
    rw [smul_smul] at this
    change ((N₁ : X.E) * u) • y ∈ B
    convert this using 2
    rw [hN₁]; push_cast; ring
  obtain ⟨R₁, hR₁⟩ := r1 M (scl ((N₁ : X.E) * u) M) fun h => hfB (AddSubgroup.relIndex_eq_zero_of_le_right hB₁ h)
  have hpK : ∀ y ∈ scl u M, (p : X.E) • y ∈ M := by
    rintro _ ⟨y, hy, rfl⟩
    exact hpu y hy
  have hMK : ∀ y ∈ M, (p : X.E) • y ∈ scl u M := fun y hy => ⟨_, hO' _ (hO' y hy), (hpu' y hy).symm⟩

  have hcard : R₁.card = (scl u M).relIndex M := by
    rw [r2 _ _ _ hR₁, ← scl_scl, relIndex_scl_nat M _ hN₁p hpK]
    refine GlobalTheory.T.relIndex_eq_of_selfDual_alternating _ (imH A) M (scl u M) (fun x y z => (h4 x y z).2.2.1) (fun x y => by rw [h3, h3]; ring) hsd
      (fun x => ?_) (relIndex_ne_zero_of_smul hpE (hfin _ hp.ne_zero) hpK)
      (fun h => hfin _ hp.ne_zero (AddSubgroup.relIndex_eq_zero_of_le_left ?_ h))
    · have e1 : ∀ y, imH A x (u • y) = imH A (star u • x) y := fun y => by rw [hadj, star_star]
      constructor
      · rintro ⟨m, hm, rfl⟩ _ ⟨y, hy, rfl⟩
        change ∃ n : ℤ, imH A (u • m) (u • y) = n
        rw [hadj, smul_smul, mul_comm, huu, one_smul]
        exact (hsd m).1 hm y hy
      · intro h
        refine ⟨star u • x, (hsd _).2 fun y hy => ?_, ?_⟩
        · rw [← e1]; exact h _ ⟨y, hy, rfl⟩
        · change u • star u • x = x
          rw [smul_smul, huu, one_smul]
    · rintro _ ⟨y, hy, rfl⟩
      exact hMK y hy
  obtain ⟨c, hc, hcd⟩ := relIndex_dvd (E := X.E) M B (scl u M) hp hg (by
      rintro _ ⟨y, hy, rfl⟩
      have := b1 y hy
      rwa [mul_smul] at this)
    (fun h => hfin _ hpg0.ne' (AddSubgroup.relIndex_eq_zero_of_le_left (by
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨hMB y hy, ?_⟩
      have := hMK _ (nat_smul_mem (E := X.E) M g hy)
      rwa [smul_smul, ← Nat.cast_mul] at this) h))
  have hnorm := norm_lamC_ratio lam hn0 hc (hcard ▸ hnd.trans hcd)
  have hnq : (n : ℂ)⁻¹ ∈ TaylorLogMetric.Qbar := inv_mem (natCast_mem _ n)

  have hsum := r3 _ M B _ _ R R₁ R₂ (fun y => Wx A (-t) (Wx A y e)) hB₁ hB₂ (fun y hy => by
      obtain ⟨s, s', hs⟩ := Nat.isCoprime_iff_coprime.2 (Nat.Coprime.mul_left hN₁p hg)
      refine ⟨_, ⟨_, zsmul_mem (b2 y hy) s, rfl⟩, _, ⟨_, zsmul_mem hy s', rfl⟩, ?_⟩
      have hs' : (s : X.E) * (N₁ * g) + s' * p = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → X.E) hs
      simp only [DistribSMul.toAddMonoidHom_apply, ← Int.cast_smul_eq_zsmul X.E, smul_smul, ← add_smul]
      rw [show (N₁ : X.E) * u * (s * (g * (star (ϖ : X.E) / ϖ))) + p * s' = 1 by rw [← hs', hu]; field_simp, one_smul, sub_self]
      exact zero_mem _)
    (fun y₁ h₁ y₂ h₂ h => by
      refine mem_of_coprime (E := X.E) M hg ?_ ?_
      · have := sub_mem (nat_smul_mem (E := X.E) M g h) (hg₂ y₂ h₂)
        rwa [smul_add, add_sub_cancel_right] at this
      · obtain ⟨m, hm, rfl⟩ := mem_scl.1 h₁
        rw [mul_smul, smul_comm]
        exact nat_smul_mem M _ (hpu m hm))
    hR hR₁ hR₂ (fun y hy l hl hl' => by
      rw [← Wx_Wx_of_int A (b6 y hy l hl'), hfixW l hl])
  set γ : HomE X.E a b → ℂ := fun y => (n : ℂ)⁻¹ * Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (coc A (-t) y : ℂ)) with hγ
  have hγq : ∀ y, γ y ∈ TaylorLogMetric.Qbar := fun y => mul_mem hnq (hζ y _).1
  have hΘ : Θ = fun z => ∑ q ∈ R₂ ×ˢ R₁, (γ q.1 * brkE A q.2 (-t)) * Wx A q.2 (Wx A (q.1 - t) e) z := by
    rw [hth R hR, Wx_sum]
    funext z
    have := congrFun hsum z
    simp only [Finset.sum_apply] at this
    beta_reduce
    rw [this, Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y₂ h₂ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y₁ h₁ => ?_
    rw [Wx_neg_add A t (b6 _ (hB₁ (hR₁.1 _ h₁)) _ (hB₂ (hR₂.1 _ h₂))), hγ]
    ring
  have hjet : ∀ m, jetC A.cD Θ m =
      ∑ q ∈ R₂ ×ˢ R₁, (γ q.1 * brkE A q.2 (-t)) * jetC A.cD (Wx A q.2 (Wx A (q.1 - t) e)) m := fun m => by
    rw [hΘ]
    exact h8 _ (R₂ ×ˢ R₁) (fun q => γ q.1 * brkE A q.2 (-t)) (fun q => Wx A q.2 (Wx A (q.1 - t) e))
      (fun q _ => h7 q.2 _ (h7 (q.1 - t) e hsm)) m
  have halg' : ∀ q ∈ R₂ ×ˢ R₁, ∀ m, jetC A.cD (Wx A q.2 (Wx A (q.1 - t) e)) m ∈ TaylorLogMetric.Qbar := by
    rintro ⟨y₂, y₁⟩ hq' m
    obtain ⟨h₂, h₁⟩ := Finset.mem_product.1 hq'
    obtain ⟨z, hz, rfl⟩ := mem_scl.1 (hR₁.1 _ h₁)
    obtain ⟨k, hk⟩ := hdv y₂ h₂
    have := halg y₂ h₂ _ (nat_smul_mem (E := X.E) M k hz) m
    rw [smul_smul] at this
    rwa [show (N₁ : X.E) * u = N₀ y₂ * u * k by rw [hk]; push_cast; ring]
  refine ⟨fun m => hjet m ▸ sum_mem fun q hq' => mul_mem (mul_mem (hγq _) (hq _ _)) (halg' q hq' m), ?_⟩
  refine clo_congr (clo_sum R₂ _ fun y₂ h₂ => clo_class A lam M hsd hadj hq huu hpu hN₁p (hdv y₂ h₂) hR₁ hN₁t (ptTab ι un)
    (fun y m => TaylorLogMetric.lamC lam (jetC A.cD (Wx A y (Wx A (y₂ - t) e)) m)) (hclo y₂ h₂) (hγq y₂) ?_ _ (hSup N₁ hN₁p))
    subset_rfl subset_rfl fun m _ => ?_
  · rw [hγ, mul_right_comm, lamC_mul lam (mul_mem hnq (natCast_mem _ _)) (hζ _ _).1, norm_mul, (hζ _ _).2, mul_one]
    exact hnorm
  · rw [hjet, lamC_sum _ _ _ fun q hq' => mul_mem (mul_mem (hγq _) (hq _ _)) (halg' q hq' m), Finset.sum_product]
    refine Finset.sum_congr rfl fun y₂ h₂ => Finset.sum_congr rfl fun y₁ h₁ => ?_
    exact lamC_mul lam (mul_mem (hγq _) (hq _ _)) (halg' _ (Finset.mk_mem_product h₂ h₁) m)

end GlobalTheory.MomT.CosetBar
