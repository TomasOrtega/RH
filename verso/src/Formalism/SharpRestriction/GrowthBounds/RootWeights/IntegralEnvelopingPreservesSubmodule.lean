import Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantDenominatorEllPBound

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

/- English proof (translation)
Take `⟨w, _, p_mem, p_ne, _⟩` from `S`. Use `haveI : CharZero O := by`. Take `⟨q, hq⟩` from `CharP.exists O`. Break down `CharP.char_is_prime_or_zero O q with hqp | hq0` into its components or cases. It suffices to derive a contradiction.

Distinguish the cases in `hdvd : q ∣ p`. Establish `hqp' : q = p` using `(Nat.prime_dvd_prime_iff_eq hqp hp).mp hdvd`. Substitute `hqp'` using the available equality. Conclude with `p_ne (CharP.cast_eq_zero O q)`. Establish `hcop : Nat.Coprime p q` using `(Nat.coprime_primes hp hqp).mpr (fun h => hdvd (by subst h; exact dvd_rfl))`.

Establish `hu : IsUnit (p : ZMod q)`. Rewrite using `[← ZMod.coe_unitOfCoprime p hcop]`. Conclude with `Units.isUnit _`. Establish `hu' : IsUnit (p : O)`. Establish `h5` using `hu.map (ZMod.castHom (dvd_refl q) O)`.

Simplify using `using h5`. Conclude with `(IsLocalRing.mem_maximalIdeal _).mp p_mem hu'`. Substitute `hq0` using the available equality. Conclude with `CharP.charP_to_charZero O`. Unfold `KK`.

Conclude with `charZero_of_injective_algebraMap (IsFractionRing.injective O (FractionRing O))`.
-/
theorem dvr_fraction_field_char_zero_prime {p : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : UniformizedDVR p O) (hp : p.Prime) : CharZero (KK O) := by
  obtain ⟨w, _, p_mem, p_ne, _⟩ := S
  haveI : CharZero O := by
    obtain ⟨q, hq⟩ := CharP.exists O
    rcases CharP.char_is_prime_or_zero O q with hqp | hq0
    · exfalso
      by_cases hdvd : q ∣ p
      · have hqp' : q = p := (Nat.prime_dvd_prime_iff_eq hqp hp).mp hdvd
        subst hqp'
        exact p_ne (CharP.cast_eq_zero O q)
      · have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hqp).mpr (fun h => hdvd (by subst h; exact dvd_rfl))
        have hu : IsUnit (p : ZMod q) := by
          rw [← ZMod.coe_unitOfCoprime p hcop]; exact Units.isUnit _
        have hu' : IsUnit (p : O) := by
          have h5 := hu.map (ZMod.castHom (dvd_refl q) O)
          simpa using h5
        exact (IsLocalRing.mem_maximalIdeal _).mp p_mem hu'
    · subst hq0
      exact CharP.charP_to_charZero O
  unfold KK
  exact charZero_of_injective_algebraMap (IsFractionRing.injective O (FractionRing O))

section field

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/- English proof (translation)
Unfold `weightSp`. Simplify using `[Submodule.mem_iInf, sub_eq_zero]`.
-/
theorem mem_weightSpace_iff_diag_scalar {E : GLOps n K V} {mu : Fin n → ℤ} {x : V} :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  unfold weightSp
  simp [Submodule.mem_iInf, sub_eq_zero]

/- English proof (translation)
Establish `h1` using `Ring.descPochhammer_eq_factorial_smul_choose m k`. Rewrite `h1` using `[← Polynomial.eval_eq_smeval, descPochhammer_eval_eq_prod_range, nsmul_eq_mul]`. Establish `h2` using `congrArg (fun z : ℤ => (z : K)) h1`. Move the coercions through the operations in `at h2`. Rewrite using `[h2, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)), one_mul]`.
-/
theorem inv_factorial_prod_eq_choose [CharZero K] (m : ℤ) (k : ℕ) :
    ((k.factorial : K)⁻¹) * ∏ j ∈ range k, ((m : K) - (j : K)) = ((Ring.choose m k : ℤ) : K) := by
  have h1 := Ring.descPochhammer_eq_factorial_smul_choose m k
  rw [← Polynomial.eval_eq_smeval, descPochhammer_eval_eq_prod_range, nsmul_eq_mul] at h1
  have h2 := congrArg (fun z : ℤ => (z : K)) h1
  push_cast at h2
  rw [h2, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)), one_mul]

/- English proof (translation)
Establish `hx'` using `(mem_weightSpace_iff_diag_scalar.mp hx) a`. Unfold `binomE`. Rewrite using `[LinearMap.smul_apply, ← inv_factorial_prod_eq_choose (mu a) k, mul_smul]`. Use `congr 1`. Proceed by induction on `k with`.

Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[List.range_succ, List.map_append, List.prod_append, Finset.prod_range_succ]`. Simplify using `only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hx']`. Rewrite using `[← sub_smul, map_smul, ih, smul_smul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem binomial_diagonal_on_weight [CharZero K] {E : GLOps n K V} {mu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E mu)
    (a : Fin n) (k : ℕ) : binomE E a k x = ((Ring.choose (mu a) k : ℤ) : K) • x := by
  have hx' := (mem_weightSpace_iff_diag_scalar.mp hx) a
  unfold binomE
  rw [LinearMap.smul_apply, ← inv_factorial_prod_eq_choose (mu a) k, mul_smul]
  congr 1
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.prod_append, Finset.prod_range_succ]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Module.End.mul_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hx']
    rw [← sub_smul, map_smul, ih, smul_smul]
    congr 1
    ring

def shiftedBinomialOperator (E : GLOps n K V) (a : Fin n) (c : ℤ) (d : ℕ) : Module.End K V :=
  ∑ ij ∈ antidiagonal d, ((Ring.choose c ij.2 : ℤ) : K) • binomE E a ij.1

/- English proof (translation)
Unfold `shiftedBinomialOperator`. Rewrite using `[LinearMap.sum_apply]`. Simplify using `only [LinearMap.smul_apply, binomial_diagonal_on_weight hx, smul_smul, ← Finset.sum_smul]`. Use `congr 1`. Rewrite using `[Ring.add_choose_eq d (Commute.all _ _)]`.

Use `push_cast`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `ij _`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem shifted_binomial_on_weight [CharZero K] {E : GLOps n K V} {mu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E mu)
    (a : Fin n) (c : ℤ) (d : ℕ) : shiftedBinomialOperator E a c d x = ((Ring.choose (mu a + c) d : ℤ) : K) • x := by
  unfold shiftedBinomialOperator
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, binomial_diagonal_on_weight hx, smul_smul, ← Finset.sum_smul]
  congr 1
  rw [Ring.add_choose_eq d (Commute.all _ _)]
  push_cast
  apply Finset.sum_congr rfl
  intro ij _
  ring

end field

section lattice

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

/- English proof (translation)
Rewrite using `[Int.cast_smul_eq_zsmul]`. Conclude with `zsmul_mem hx z`.
-/
theorem intCast_smul_mem_submodule (M : Submodule O V) (z : ℤ) {x : V} (hx : x ∈ M) : ((z : ℤ) : KK O) • x ∈ M := by
  rw [Int.cast_smul_eq_zsmul]
  exact zsmul_mem hx z

/- English proof (translation)
Unfold `UZStable at hM`. Unfold `shiftedBinomialOperator`. Rewrite using `[LinearMap.sum_apply]`. Apply `Submodule.sum_mem` to reduce the goal to its premises. Introduce `ij _`.

Rewrite using `[LinearMap.smul_apply]`. Conclude with `intCast_smul_mem_submodule M _ (hM _ (Or.inr ⟨a, ij.1, rfl⟩) x hx)`.
-/
theorem shifted_binomial_preserves_lattice {E : GLOps n (KK O) V} {M : Submodule O V} (hM : UZStable (O := O) E M) (a : Fin n) (c : ℤ)
    (d : ℕ) {x : V} (hx : x ∈ M) : shiftedBinomialOperator E a c d x ∈ M := by
  unfold UZStable at hM
  unfold shiftedBinomialOperator
  rw [LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro ij _
  rw [LinearMap.smul_apply]
  exact intCast_smul_mem_submodule M _ (hM _ (Or.inr ⟨a, ij.1, rfl⟩) x hx)

/- English proof (translation)
Establish `hex : ∃ a, nu a ≠ lam a`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `h (funext hc)`. Take `⟨a, ha⟩` from `hex`.

Break down `lt_or_gt_of_ne ha with hlt | hgt` into its components or cases. Take `⟨δ, hδ⟩ : ∃ δ : ℕ, lam a - nu a = δ` from `⟨(lam a - nu a).toNat, by omega⟩`. Use `⟨shiftedBinomialOperator E a (-nu a) δ, fun mu => Ring.choose (mu a + -nu a) δ, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show Ring.choose (lam a + -nu a) δ = 1`. Rewrite using `[show lam a + -nu a = (δ : ℤ) by omega, Ring.choose_natCast, Nat.choose_self, Nat.cast_one]`.

Use `show Ring.choose (nu a + -nu a) δ = 0`. Rewrite using `[show nu a + -nu a = ((0 : ℕ) : ℤ) by simp, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]`. Introduce `mu x hx`. Conclude with `shifted_binomial_on_weight hx a (-nu a) δ`. Conclude with `fun M hM x hx => shifted_binomial_preserves_lattice hM a (-nu a) δ hx`.

Take `⟨δ, hδ⟩ : ∃ δ : ℕ, nu a - lam a = δ` from `⟨(nu a - lam a).toNat, by omega⟩`. Use `⟨1 - shiftedBinomialOperator E a (-lam a) δ, fun mu => 1 - Ring.choose (mu a + -lam a) δ, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show 1 - Ring.choose (lam a + -lam a) δ = 1`. Rewrite using `[show lam a + -lam a = ((0 : ℕ) : ℤ) by simp, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, sub_zero]`. Use `show 1 - Ring.choose (nu a + -lam a) δ = 0`.

Rewrite using `[show nu a + -lam a = (δ : ℤ) by omega, Ring.choose_natCast, Nat.choose_self, Nat.cast_one, sub_self]`. Introduce `mu x hx`. Rewrite using `[LinearMap.sub_apply, Module.End.one_apply, shifted_binomial_on_weight hx a (-lam a) δ]`. Use `push_cast`. Rewrite using `[sub_smul, one_smul]`.

Introduce `M hM x hx`. Rewrite using `[LinearMap.sub_apply, Module.End.one_apply]`. Conclude with `M.sub_mem hx (shifted_binomial_preserves_lattice hM a (-lam a) δ hx)`.
-/
theorem lattice_stable_weight_separator [CharZero (KK O)] (E : GLOps n (KK O) V) {lam nu : Fin n → ℤ} (h : nu ≠ lam) :
    ∃ (T : Module.End (KK O) V) (g : (Fin n → ℤ) → ℤ), g lam = 1 ∧ g nu = 0 ∧
      (∀ mu, ∀ x ∈ weightSp E mu, T x = ((g mu : ℤ) : KK O) • x) ∧
      ∀ M : Submodule O V, UZStable (O := O) E M → ∀ x ∈ M, T x ∈ M := by
  have hex : ∃ a, nu a ≠ lam a := by
    by_contra hc
    push_neg at hc
    exact h (funext hc)
  obtain ⟨a, ha⟩ := hex
  rcases lt_or_gt_of_ne ha with hlt | hgt
  · obtain ⟨δ, hδ⟩ : ∃ δ : ℕ, lam a - nu a = δ := ⟨(lam a - nu a).toNat, by omega⟩
    refine ⟨shiftedBinomialOperator E a (-nu a) δ, fun mu => Ring.choose (mu a + -nu a) δ, ?_, ?_, ?_, ?_⟩
    · show Ring.choose (lam a + -nu a) δ = 1
      rw [show lam a + -nu a = (δ : ℤ) by omega, Ring.choose_natCast, Nat.choose_self, Nat.cast_one]
    · show Ring.choose (nu a + -nu a) δ = 0
      rw [show nu a + -nu a = ((0 : ℕ) : ℤ) by simp, Ring.choose_natCast,
        Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    · intro mu x hx
      exact shifted_binomial_on_weight hx a (-nu a) δ
    · exact fun M hM x hx => shifted_binomial_preserves_lattice hM a (-nu a) δ hx
  · obtain ⟨δ, hδ⟩ : ∃ δ : ℕ, nu a - lam a = δ := ⟨(nu a - lam a).toNat, by omega⟩
    refine ⟨1 - shiftedBinomialOperator E a (-lam a) δ, fun mu => 1 - Ring.choose (mu a + -lam a) δ, ?_, ?_, ?_, ?_⟩
    · show 1 - Ring.choose (lam a + -lam a) δ = 1
      rw [show lam a + -lam a = ((0 : ℕ) : ℤ) by simp, Ring.choose_natCast,
        Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, sub_zero]
    · show 1 - Ring.choose (nu a + -lam a) δ = 0
      rw [show nu a + -lam a = (δ : ℤ) by omega, Ring.choose_natCast, Nat.choose_self, Nat.cast_one, sub_self]
    · intro mu x hx
      rw [LinearMap.sub_apply, Module.End.one_apply, shifted_binomial_on_weight hx a (-lam a) δ]
      push_cast
      rw [sub_smul, one_smul]
    · intro M hM x hx
      rw [LinearMap.sub_apply, Module.End.one_apply]
      exact M.sub_mem hx (shifted_binomial_preserves_lattice hM a (-lam a) δ hx)

/- English proof (translation)
Proceed by induction on `F using Finset.induction_on with`. Consider the case `empty`. Introduce `_ y0 f _ _ hmem`. Simplify using `using hmem`. Consider the case `@insert a F ha ih`.

Introduce `hl y0 f hy0 hf hmem`. Establish `hal : a ≠ lam` using `fun h => hl (h ▸ Finset.mem_insert_self a F)`. Take `⟨T, g', hg1, hg0, hT, hTM⟩` from `lattice_stable_weight_separator E hal`. Establish `hlF : lam ∉ F` using `fun h => hl (Finset.mem_insert_of_mem h)`. Establish `h2` using `hTM M hM _ hmem`.

Rewrite `h2` using `[map_add, map_sum, Finset.sum_insert ha]`. Rewrite `h2` using `[hT lam y0 hy0, hg1, hT a (f a) (hf a (Finset.mem_insert_self a F)), hg0]`. Establish `h3 : ∀ nu ∈ F, T (f nu) = ((g' nu : ℤ) : KK O) • f nu` using `fun nu hnu => hT nu (f nu) (hf nu (Finset.mem_insert_of_mem hnu))`. Rewrite `h2` using `[Finset.sum_congr rfl h3]`. Simplify using `only [Int.cast_one, one_smul, Int.cast_zero, zero_smul, zero_add] at h2`.

Conclude with `ih hlF y0 (fun nu => ((g' nu : ℤ) : KK O) • f nu) hy0 (fun nu hnu => Submodule.smul_mem _ _ (hf nu (Finset.mem_insert_of_mem hnu))) h2`.
-/
theorem lattice_weight_components_mem [CharZero (KK O)] (E : GLOps n (KK O) V) (M : Submodule O V) (hM : UZStable (O := O) E M)
    (lam : Fin n → ℤ) (F : Finset (Fin n → ℤ)) : lam ∉ F → ∀ (y0 : V) (f : (Fin n → ℤ) → V),
      y0 ∈ weightSp E lam → (∀ nu ∈ F, f nu ∈ weightSp E nu) → y0 + ∑ nu ∈ F, f nu ∈ M → y0 ∈ M := by
  induction F using Finset.induction_on with
  | empty =>
    intro _ y0 f _ _ hmem
    simpa using hmem
  | @insert a F ha ih =>
    intro hl y0 f hy0 hf hmem
    have hal : a ≠ lam := fun h => hl (h ▸ Finset.mem_insert_self a F)
    obtain ⟨T, g', hg1, hg0, hT, hTM⟩ := lattice_stable_weight_separator E hal
    have hlF : lam ∉ F := fun h => hl (Finset.mem_insert_of_mem h)
    have h2 := hTM M hM _ hmem
    rw [map_add, map_sum, Finset.sum_insert ha] at h2
    rw [hT lam y0 hy0, hg1, hT a (f a) (hf a (Finset.mem_insert_self a F)), hg0] at h2
    have h3 : ∀ nu ∈ F, T (f nu) = ((g' nu : ℤ) : KK O) • f nu :=
      fun nu hnu => hT nu (f nu) (hf nu (Finset.mem_insert_of_mem hnu))
    rw [Finset.sum_congr rfl h3] at h2
    simp only [Int.cast_one, one_smul, Int.cast_zero, zero_smul, zero_add] at h2
    exact ih hlF y0 (fun nu => ((g' nu : ℤ) : KK O) • f nu) hy0
      (fun nu hnu => Submodule.smul_mem _ _ (hf nu (Finset.mem_insert_of_mem hnu))) h2

/- English proof (translation)
Establish `hy : y ∈ ⨆ mu : Fin n → ℤ, weightSp E mu`. Rewrite using `[hE]`. Conclude with `Submodule.mem_top`. Take `⟨c, hc, hsum⟩` from `(Submodule.mem_iSup_iff_exists_finsupp _ y).mp hy`. Use `⟨c lam, c.support.erase lam, c, by simp, hc lam, fun nu _ => hc nu, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hsum]`. Simplify using `only [Finsupp.sum]`. Distinguish the cases in `h : lam ∈ c.support`. Conclude with `(Finset.add_sum_erase _ _ h).symm`. Establish `h0 : c lam = 0` using `by simpa using h`.

Rewrite using `[Finset.erase_eq_self.mpr h, h0, zero_add]`.
-/
theorem weight_component_decomposition (E : GLOps n (KK O) V) (hE : (⨆ mu : Fin n → ℤ, weightSp E mu) = ⊤) (lam : Fin n → ℤ) (y : V) :
    ∃ (y0 : V) (F : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → V), lam ∉ F ∧ y0 ∈ weightSp E lam ∧
      (∀ nu ∈ F, f nu ∈ weightSp E nu) ∧ y = y0 + ∑ nu ∈ F, f nu := by
  have hy : y ∈ ⨆ mu : Fin n → ℤ, weightSp E mu := by
    rw [hE]; exact Submodule.mem_top
  obtain ⟨c, hc, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ y).mp hy
  refine ⟨c lam, c.support.erase lam, c, by simp, hc lam, fun nu _ => hc nu, ?_⟩
  rw [← hsum]
  simp only [Finsupp.sum]
  by_cases h : lam ∈ c.support
  · exact (Finset.add_sum_erase _ _ h).symm
  · have h0 : c lam = 0 := by simpa using h
    rw [Finset.erase_eq_self.mpr h, h0, zero_add]

/- English proof (translation)
Unfold `UZmon at hu`. Unfold `UZStable at hM`. Proceed by induction on `hu using Submonoid.closure_induction with`. Consider the case `mem u hu => exact hM u hu`. Consider the case `one => intro x hx`.

Conclude with `hx`. Consider the case `mul u v _ _ hu hv => intro x hx`. Conclude with `hu _ (hv x hx)`.
-/
theorem integral_enveloping_preserves_submodule {E : GLOps n (KK O) V} {M : Submodule O V} (hM : UZStable (O := O) E M)
    {u : Module.End (KK O) V} (hu : u ∈ UZmon E) : ∀ x ∈ M, u x ∈ M := by
  unfold UZmon at hu
  unfold UZStable at hM
  induction hu using Submonoid.closure_induction with
  | mem u hu => exact hM u hu
  | one => intro x hx; exact hx
  | mul u v _ _ hu hv => intro x hx; exact hu _ (hv x hx)

/- English proof (translation)
Unfold `otherWts`. Apply `Submodule.sum_mem` to reduce the goal to its premises. Introduce `nu hnu`. Establish `hne : nu ≠ lam` using `fun h => hl (h ▸ hnu)`. Conclude with `(le_iSup₂ (f := fun mu (_ : mu ∈ {mu | mu ≠ lam}) => weightSp E mu) nu hne) (hf nu hnu)`.
-/
theorem sum_other_weights_mem (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (F : Finset (Fin n → ℤ)) (hl : lam ∉ F)
    (f : (Fin n → ℤ) → V) (hf : ∀ nu ∈ F, f nu ∈ weightSp E nu) : ∑ nu ∈ F, f nu ∈ otherWts E lam := by
  unfold otherWts
  apply Submodule.sum_mem
  intro nu hnu
  have hne : nu ≠ lam := fun h => hl (h ▸ hnu)
  exact (le_iSup₂ (f := fun mu (_ : mu ∈ {mu | mu ≠ lam}) => weightSp E mu) nu hne) (hf nu hnu)

/- English proof (translation)
Unfold `Delta Nabla`. Establish `hv : v ∈ M` using `((hl v).mpr ⟨1, (one_smul O v).symm⟩).1`. Prove the components needed by the constructor for the conclusion. Rewrite using `[Submodule.span_le]`. Introduce and unpack `x ⟨u, hu, rfl⟩`.

Conclude with `integral_enveloping_preserves_submodule hM hu v hv`. Introduce `x hx u hu`. Establish `hux : u x ∈ M` using `integral_enveloping_preserves_submodule hM hu x hx`. Take `⟨y0, F, f, hlF, hy0, hf, hdec⟩` from `weight_component_decomposition E hE lam (u x)`. Establish `hy0M : y0 ∈ M` using `lattice_weight_components_mem E M hM lam F hlF y0 f hy0 hf (by rw [← hdec]; exact hux)`.

Take `⟨c, hc⟩` from `(hl y0).mp ⟨hy0M, hy0⟩`. Use `⟨c, ?_⟩` and prove the remaining obligations. Rewrite using `[algebraMap_smul, hdec, hc, add_sub_cancel_left]`. Conclude with `sum_other_weights_mem E lam F hlF f hf`.
-/
theorem highest_weight_lattice_bounds [CharZero (KK O)] (E : GLOps n (KK O) V) (hE : (⨆ mu : Fin n → ℤ, weightSp E mu) = ⊤)
    (lam : Fin n → ℤ) (v : V) (M : Submodule O V) (hM : UZStable (O := O) E M)
    (hl : ∀ x, (x ∈ M ∧ x ∈ weightSp E lam) ↔ ∃ c : O, x = c • v) :
    Delta (O := O) E v ≤ M ∧ (M : Set V) ⊆ Nabla (O := O) E lam v := by
  unfold Delta Nabla
  have hv : v ∈ M := ((hl v).mpr ⟨1, (one_smul O v).symm⟩).1
  constructor
  · rw [Submodule.span_le]
    rintro x ⟨u, hu, rfl⟩
    exact integral_enveloping_preserves_submodule hM hu v hv
  · intro x hx u hu
    have hux : u x ∈ M := integral_enveloping_preserves_submodule hM hu x hx
    obtain ⟨y0, F, f, hlF, hy0, hf, hdec⟩ := weight_component_decomposition E hE lam (u x)
    have hy0M : y0 ∈ M := lattice_weight_components_mem E M hM lam F hlF y0 f hy0 hf (by rw [← hdec]; exact hux)
    obtain ⟨c, hc⟩ := (hl y0).mp ⟨hy0M, hy0⟩
    refine ⟨c, ?_⟩
    rw [algebraMap_smul, hdec, hc, add_sub_cancel_left]
    exact sum_other_weights_mem E lam F hlF f hf

end lattice

end Formalism.MainNotions.G.GLWeightTheory
