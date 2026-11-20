import Mathlib

open TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.TensorComplete

section Elementary

variable {A : Type} [CommRing A] (π : A)

/- English proof (translation)
Rewrite using `[SModEq.sub_mem, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Simplify using the standard rewrite rules.
-/
theorem smodEq_span_iff {M : Type} [AddCommGroup M] [Module A M] (n : ℕ) (x y : M) :
    x ≡ y [SMOD (Ideal.span {π} ^ n • ⊤ : Submodule A M)] ↔ ∃ z : M, π ^ n • z = x - y := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun x hx => ?_, fun u hu => ?_⟩` and prove the remaining obligations. Use `h.toIsHausdorff.haus x fun n => ?_` and prove the remaining obligations. Rewrite using `[smodEq_span_iff, sub_zero]`.

Conclude with `hx n`. Establish `hc : ∀ {m n : ℕ}, m ≤ n → u m ≡ u n [SMOD (Ideal.span {π} ^ m • ⊤ : Submodule A M)]`. Introduce `m n hmn`. Rewrite using `[smodEq_span_iff]`. Proceed by induction on `n, hmn using Nat.le_induction with`.

Consider the case `base => exact ⟨0, by simp⟩`. Consider the case `succ k hk ih`. Take `⟨z, hz⟩` from `ih`. Take `⟨w, hw⟩` from `hu k`. Use `⟨z + π ^ (k - m) • w, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_add, smul_smul, ← pow_add, Nat.add_sub_cancel' hk, hz, hw]`. Normalize the expressions using the abelian group laws. Take `⟨L, hL⟩` from `h.toIsPrecomplete.prec hc`. Conclude with `⟨L, fun n => (smodEq_span_iff π n _ _).1 (hL n)⟩`. Introduce and unpack `⟨h1, h2⟩ haveI : IsHausdorff (Ideal.span {π}) M := ⟨fun x hx => h1 x fun n => by`.

Simplify using `using (smodEq_span_iff π n _ _).1 (hx n)⟩`. Use `haveI : IsPrecomplete (Ideal.span {π}) M := ⟨fun u hu => by`. Take `⟨L, hL⟩` from `h2 u fun n => (smodEq_span_iff π n _ _).1 (hu (Nat.le_succ n))`. Conclude with `⟨L, fun n => (smodEq_span_iff π n _ _).2 (hL n)⟩⟩`. Conclude with `⟨⟩`.
-/
theorem isAdicComplete_span_iff {M : Type} [AddCommGroup M] [Module A M] :
    IsAdicComplete (Ideal.span {π}) M ↔
      (∀ x : M, (∀ n : ℕ, ∃ z : M, π ^ n • z = x) → x = 0) ∧
      ∀ u : ℕ → M, (∀ n : ℕ, ∃ z : M, π ^ n • z = u n - u (n + 1)) →
        ∃ L : M, ∀ n : ℕ, ∃ z : M, π ^ n • z = u n - L := by
  constructor
  · intro h
    refine ⟨fun x hx => ?_, fun u hu => ?_⟩
    · refine h.toIsHausdorff.haus x fun n => ?_
      rw [smodEq_span_iff, sub_zero]
      exact hx n
    · have hc : ∀ {m n : ℕ}, m ≤ n →
          u m ≡ u n [SMOD (Ideal.span {π} ^ m • ⊤ : Submodule A M)] := by
        intro m n hmn
        rw [smodEq_span_iff]
        induction n, hmn using Nat.le_induction with
        | base => exact ⟨0, by simp⟩
        | succ k hk ih =>
          obtain ⟨z, hz⟩ := ih
          obtain ⟨w, hw⟩ := hu k
          refine ⟨z + π ^ (k - m) • w, ?_⟩
          rw [smul_add, smul_smul, ← pow_add, Nat.add_sub_cancel' hk, hz, hw]
          abel
      obtain ⟨L, hL⟩ := h.toIsPrecomplete.prec hc
      exact ⟨L, fun n => (smodEq_span_iff π n _ _).1 (hL n)⟩
  · rintro ⟨h1, h2⟩
    haveI : IsHausdorff (Ideal.span {π}) M := ⟨fun x hx => h1 x fun n => by
      simpa using (smodEq_span_iff π n _ _).1 (hx n)⟩
    haveI : IsPrecomplete (Ideal.span {π}) M := ⟨fun u hu => by
      obtain ⟨L, hL⟩ := h2 u fun n => (smodEq_span_iff π n _ _).1 (hu (Nat.le_succ n))
      exact ⟨L, fun n => (smodEq_span_iff π n _ _).2 (hL n)⟩⟩
    exact ⟨⟩

variable {π}

/- English proof (translation)
Take `⟨h1, h2⟩` from `(isAdicComplete_span_iff π).1 h`. Use `(isAdicComplete_span_iff π).2 ⟨fun x hx => ?_, fun u hu => ?_⟩` and prove the remaining obligations. Establish `: e.symm x = 0` using `h1 _ fun n => by`. Take `⟨z, hz⟩` from `hx n`. Conclude with `⟨e.symm z, by rw [← map_smul, hz]⟩`.

Simplify using `using this`. Take `⟨L, hL⟩` from `h2 (fun n => e.symm (u n)) fun n => by`. Take `⟨z, hz⟩` from `hu n`. Conclude with `⟨e.symm z, by rw [← map_smul, hz, map_sub]⟩`. Use `⟨e L, fun n => ?_⟩` and prove the remaining obligations.

Take `⟨z, hz⟩` from `hL n`. Conclude with `⟨e z, by rw [← map_smul, hz, map_sub, LinearEquiv.apply_symm_apply]⟩`.
-/
theorem isAdicComplete_of_linearEquiv {M M' : Type} [AddCommGroup M] [Module A M]
    [AddCommGroup M'] [Module A M'] (e : M ≃ₗ[A] M')
    (h : IsAdicComplete (Ideal.span {π}) M) : IsAdicComplete (Ideal.span {π}) M' := by
  obtain ⟨h1, h2⟩ := (isAdicComplete_span_iff π).1 h
  refine (isAdicComplete_span_iff π).2 ⟨fun x hx => ?_, fun u hu => ?_⟩
  · have : e.symm x = 0 := h1 _ fun n => by
      obtain ⟨z, hz⟩ := hx n
      exact ⟨e.symm z, by rw [← map_smul, hz]⟩
    simpa using this
  · obtain ⟨L, hL⟩ := h2 (fun n => e.symm (u n)) fun n => by
      obtain ⟨z, hz⟩ := hu n
      exact ⟨e.symm z, by rw [← map_smul, hz, map_sub]⟩
    refine ⟨e L, fun n => ?_⟩
    obtain ⟨z, hz⟩ := hL n
    exact ⟨e z, by rw [← map_smul, hz, map_sub, LinearEquiv.apply_symm_apply]⟩

/- English proof (translation)
Take `⟨h1, h2⟩` from `(isAdicComplete_span_iff π).1 h`. Take `⟨h1', h2'⟩` from `(isAdicComplete_span_iff π).1 h'`. Use `(isAdicComplete_span_iff π).2 ⟨fun x hx => ?_, fun u hu => ?_⟩` and prove the remaining obligations. Use `Prod.ext (h1 _ fun n => ?_) (h1' _ fun n => ?_)` and prove the remaining obligations. Take `⟨z, hz⟩` from `hx n`.

Conclude with `⟨z.1, by rw [← hz]; rfl⟩`. Take `⟨z, hz⟩` from `hx n`. Conclude with `⟨z.2, by rw [← hz]; rfl⟩`. Take `⟨L, hL⟩` from `h2 (fun n => (u n).1) fun n => by`. Take `⟨z, hz⟩` from `hu n`.

Conclude with `⟨z.1, by simpa using congrArg Prod.fst hz⟩`. Take `⟨L', hL'⟩` from `h2' (fun n => (u n).2) fun n => by`. Take `⟨z, hz⟩` from `hu n`. Conclude with `⟨z.2, by simpa using congrArg Prod.snd hz⟩`. Use `⟨(L, L'), fun n => ?_⟩` and prove the remaining obligations.

Take `⟨z, hz⟩` from `hL n`. Take `⟨z', hz'⟩` from `hL' n`. Conclude with `⟨(z, z'), Prod.ext hz hz'⟩`.
-/
theorem isAdicComplete_prod {M M' : Type} [AddCommGroup M] [Module A M]
    [AddCommGroup M'] [Module A M'] (h : IsAdicComplete (Ideal.span {π}) M)
    (h' : IsAdicComplete (Ideal.span {π}) M') : IsAdicComplete (Ideal.span {π}) (M × M') := by
  obtain ⟨h1, h2⟩ := (isAdicComplete_span_iff π).1 h
  obtain ⟨h1', h2'⟩ := (isAdicComplete_span_iff π).1 h'
  refine (isAdicComplete_span_iff π).2 ⟨fun x hx => ?_, fun u hu => ?_⟩
  · refine Prod.ext (h1 _ fun n => ?_) (h1' _ fun n => ?_)
    · obtain ⟨z, hz⟩ := hx n
      exact ⟨z.1, by rw [← hz]; rfl⟩
    · obtain ⟨z, hz⟩ := hx n
      exact ⟨z.2, by rw [← hz]; rfl⟩
  · obtain ⟨L, hL⟩ := h2 (fun n => (u n).1) fun n => by
      obtain ⟨z, hz⟩ := hu n
      exact ⟨z.1, by simpa using congrArg Prod.fst hz⟩
    obtain ⟨L', hL'⟩ := h2' (fun n => (u n).2) fun n => by
      obtain ⟨z, hz⟩ := hu n
      exact ⟨z.2, by simpa using congrArg Prod.snd hz⟩
    refine ⟨(L, L'), fun n => ?_⟩
    obtain ⟨z, hz⟩ := hL n
    obtain ⟨z', hz'⟩ := hL' n
    exact ⟨(z, z'), Prod.ext hz hz'⟩

/- English proof (translation)
Take `⟨h1, h2⟩` from `(isAdicComplete_span_iff π).1 h`. Use `(isAdicComplete_span_iff π).2 ⟨fun x hx => ?_, fun u hu => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Use `h1 _ fun k => ?_` and prove the remaining obligations. Take `⟨z, hz⟩` from `hx k`.

Conclude with `⟨z i, by rw [← hz]; rfl⟩`. Use `choose z hz using hu`. Establish `key : ∀ i : Fin n, ∃ L : M, ∀ k : ℕ, ∃ w : M, π ^ k • w = u k i - L` using `fun i => h2 (fun k => u k i) fun k => ⟨z k i, by simpa using congrFun (hz k) i⟩`. Use `choose L hL using key`. Use `⟨L, fun k => ?_⟩` and prove the remaining obligations.

Use `choose w hw using fun i => hL i k`. Conclude with `⟨w, funext hw⟩`.
-/
theorem isAdicComplete_fin_pi {M : Type} [AddCommGroup M] [Module A M]
    (h : IsAdicComplete (Ideal.span {π}) M) (n : ℕ) :
    IsAdicComplete (Ideal.span {π}) (Fin n → M) := by
  obtain ⟨h1, h2⟩ := (isAdicComplete_span_iff π).1 h
  refine (isAdicComplete_span_iff π).2 ⟨fun x hx => ?_, fun u hu => ?_⟩
  · funext i
    refine h1 _ fun k => ?_
    obtain ⟨z, hz⟩ := hx k
    exact ⟨z i, by rw [← hz]; rfl⟩
  · choose z hz using hu
    have key : ∀ i : Fin n, ∃ L : M, ∀ k : ℕ, ∃ w : M, π ^ k • w = u k i - L := fun i =>
      h2 (fun k => u k i) fun k => ⟨z k i, by simpa using congrFun (hz k) i⟩
    choose L hL using key
    refine ⟨L, fun k => ?_⟩
    choose w hw using fun i => hL i k
    exact ⟨w, funext hw⟩

/- English proof (translation)
Use `(isAdicComplete_span_iff π).2 ⟨fun x hx => ?_, fun u hu => ?_⟩` and prove the remaining obligations. Take `⟨z, rfl⟩` from `hx E`. Conclude with `h z`. Establish `tel : ∀ n k : ℕ, ∃ z : M, π ^ n • z = u n - u (n + k)`. Introduce `n k`.

Proceed by induction on `k with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `succ k ih`. Take `⟨z, hz⟩` from `ih`. Take `⟨w, hw⟩` from `hu (n + k)`.

Use `⟨z + π ^ k • w, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add, smul_smul, ← pow_add, hz, hw, ← add_assoc]`. Normalize the expressions using the abelian group laws. Use `⟨u E, fun n => ?_⟩` and prove the remaining obligations. Take `⟨z, hz⟩` from `tel n E`.

Take `⟨w, hw⟩` from `tel E n`. Rewrite `hw` using `[h w, add_comm E n]`. Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[hz, ← sub_eq_zero.1 hw.symm]`.
-/
theorem isAdicComplete_of_pow_smul_eq_zero {M : Type} [AddCommGroup M] [Module A M] (E : ℕ)
    (h : ∀ x : M, π ^ E • x = 0) : IsAdicComplete (Ideal.span {π}) M := by
  refine (isAdicComplete_span_iff π).2 ⟨fun x hx => ?_, fun u hu => ?_⟩
  · obtain ⟨z, rfl⟩ := hx E
    exact h z
  · have tel : ∀ n k : ℕ, ∃ z : M, π ^ n • z = u n - u (n + k) := by
      intro n k
      induction k with
      | zero => exact ⟨0, by simp⟩
      | succ k ih =>
        obtain ⟨z, hz⟩ := ih
        obtain ⟨w, hw⟩ := hu (n + k)
        refine ⟨z + π ^ k • w, ?_⟩
        rw [smul_add, smul_smul, ← pow_add, hz, hw, ← add_assoc]
        abel
    refine ⟨u E, fun n => ?_⟩
    obtain ⟨z, hz⟩ := tel n E
    obtain ⟨w, hw⟩ := tel E n
    rw [h w, add_comm E n] at hw
    refine ⟨z, ?_⟩
    rw [hz, ← sub_eq_zero.1 hw.symm]

end Elementary

section Tensor

variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]

/- English proof (translation)
Establish `hmax : (Ideal.span {q}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible hq`. Establish `heq : Ideal.span {q} = IsLocalRing.maximalIdeal R` using `IsLocalRing.eq_maximalIdeal hmax`. Rewrite using `[← Ideal.mem_span_singleton, heq]`. Conclude with `(IsLocalRing.mem_maximalIdeal r).2 hr`.
-/
theorem irreducible_dvd_of_not_isUnit {q r : R} (hq : Irreducible q) (hr : ¬IsUnit r) : q ∣ r := by
  have hmax : (Ideal.span {q}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hq
  have heq : Ideal.span {q} = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hmax
  rw [← Ideal.mem_span_singleton, heq]
  exact (IsLocalRing.mem_maximalIdeal r).2 hr

/- English proof (translation)
Use `⟨∑ i, e i, fun x => ?_⟩` and prove the remaining obligations. Use `DFinsupp.ext fun i => ?_` and prove the remaining obligations. Establish `hmem : r ^ (∑ i, e i) ∈ Submodule.span R {q i ^ e i}`. Rewrite using `[Submodule.mem_span_singleton]`. Establish `h1 : q i ^ e i ∣ r ^ (∑ i, e i)` using `(pow_dvd_pow_of_dvd (irreducible_dvd_of_not_isUnit (hq i) hr) (e i)).trans (pow_dvd_pow r (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)))`.

Take `⟨c, hc⟩` from `h1`. Conclude with `⟨c, by rw [hc, smul_eq_mul, mul_comm]⟩`. Take `⟨y, hy⟩` from `Submodule.Quotient.mk_surjective _ (x i)`. Express the relevant statement in the definitionally equal form `r ^ (∑ i, e i) • x i = 0`. Rewrite using `[← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`.

Simplify `Submodule.smul_mem _ y hmem` using `[smul_eq_mul, mul_comm]`.
-/
theorem exists_pow_smul_directSum_eq_zero {ι : Type} [Fintype ι] (q : ι → R)
    (hq : ∀ i, Irreducible (q i)) (e : ι → ℕ) {r : R} (hr : ¬IsUnit r) :
    ∃ E : ℕ, ∀ x : DirectSum ι (fun i => R ⧸ Submodule.span R {q i ^ e i}), r ^ E • x = 0 := by
  classical
  refine ⟨∑ i, e i, fun x => ?_⟩
  refine DFinsupp.ext fun i => ?_
  have hmem : r ^ (∑ i, e i) ∈ Submodule.span R {q i ^ e i} := by
    rw [Submodule.mem_span_singleton]
    have h1 : q i ^ e i ∣ r ^ (∑ i, e i) :=
      (pow_dvd_pow_of_dvd (irreducible_dvd_of_not_isUnit (hq i) hr) (e i)).trans
        (pow_dvd_pow r (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)))
    obtain ⟨c, hc⟩ := h1
    exact ⟨c, by rw [hc, smul_eq_mul, mul_comm]⟩
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (x i)
  change r ^ (∑ i, e i) • x i = 0
  rw [← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  simpa [smul_eq_mul, mul_comm] using Submodule.smul_mem _ y hmem

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul o x`. Establish `h1 : (p : O) ^ E * o = (p : R) ^ E • o`. Rewrite using `[Algebra.smul_def, map_pow, map_natCast]`.

Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, h1, TensorProduct.smul_tmul, h x, TensorProduct.tmul_zero]`. Consider the case `add a b ha hb => rw [smul_add, ha, hb, add_zero]`.
-/
theorem pow_natCast_smul_tensor_eq_zero {O T : Type} [CommRing O] [Algebra R O] [AddCommGroup T]
    [Module R T] (p E : ℕ) (h : ∀ x : T, (p : R) ^ E • x = 0) (t : O ⊗[R] T) :
    (p : O) ^ E • t = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul o x =>
    have h1 : (p : O) ^ E * o = (p : R) ^ E • o := by
      rw [Algebra.smul_def, map_pow, map_natCast]
    rw [TensorProduct.smul_tmul', smul_eq_mul, h1, TensorProduct.smul_tmul, h x,
      TensorProduct.tmul_zero]
  | add a b ha hb => rw [smul_add, ha, hb, add_zero]

end Tensor

/- English proof (translation)
Introduce `p _ R O _ _ _ _ _ _ _ hp1 hp2 N _ _ _`. Take `⟨n, ι, _, q, hq, e, ⟨f⟩⟩` from `Module.equiv_free_prod_directSum (R := R) (M := N)`. Take `⟨E, hE⟩` from `exists_pow_smul_directSum_eq_zero q hq e hp2`. Establish `hfree : IsAdicComplete (Ideal.span {(p : O)}) (O ⊗[R] (Fin n →₀ R))` using `isAdicComplete_of_linearEquiv ((Finsupp.linearEquivFunOnFinite O O (Fin n)).symm.trans (TensorProduct.finsuppScalarRight R O O (Fin n)).symm) (isAdicComplete_fin_pi inferInstance n)`. Establish `htors : IsAdicComplete (Ideal.span {(p : O)}) (O ⊗[R] DirectSum ι (fun i => R ⧸ Submodule.span R {q i ^ e i}))` using `isAdicComplete_of_pow_smul_eq_zero E (pow_natCast_smul_tensor_eq_zero p E hE)`.

Conclude with `isAdicComplete_of_linearEquiv ((TensorProduct.prodRight R O O _ _).symm.trans (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl O O) f).symm) (isAdicComplete_prod hfree htors)`.
-/
theorem isAdicComplete_tensor : ∀ (p : ℕ) [Fact p.Prime] (R O : Type) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [IsLocalRing R] [CommRing O] [Algebra R O]
    [IsAdicComplete (Ideal.span {(p : O)}) O],
    (p : R) ≠ 0 → ¬IsUnit (p : R) →
    ∀ (N : Type) [AddCommGroup N] [Module R N] [Module.Finite R N],
      IsAdicComplete (Ideal.span {(p : O)}) (O ⊗[R] N) := by
  intro p _ R O _ _ _ _ _ _ _ hp1 hp2 N _ _ _
  obtain ⟨n, ι, _, q, hq, e, ⟨f⟩⟩ := Module.equiv_free_prod_directSum (R := R) (M := N)
  obtain ⟨E, hE⟩ := exists_pow_smul_directSum_eq_zero q hq e hp2
  have hfree : IsAdicComplete (Ideal.span {(p : O)}) (O ⊗[R] (Fin n →₀ R)) :=
    isAdicComplete_of_linearEquiv
      ((Finsupp.linearEquivFunOnFinite O O (Fin n)).symm.trans
        (TensorProduct.finsuppScalarRight R O O (Fin n)).symm)
      (isAdicComplete_fin_pi inferInstance n)
  have htors : IsAdicComplete (Ideal.span {(p : O)})
      (O ⊗[R] DirectSum ι (fun i => R ⧸ Submodule.span R {q i ^ e i})) :=
    isAdicComplete_of_pow_smul_eq_zero E (pow_natCast_smul_tensor_eq_zero p E hE)
  exact isAdicComplete_of_linearEquiv
    ((TensorProduct.prodRight R O O _ _).symm.trans
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl O O) f).symm)
    (isAdicComplete_prod hfree htors)

end GlobalTheory.CompanionTheory.TensorComplete
