import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
open GlobalTheory

namespace GlobalTheory.ShuffleCount

open MvPolynomial

/- English proof (translation)
Establish `key : (aeval (fun Δ : U => φ Δ)).comp (killCompl (R` using `ℚ) (Subtype.val_injective : Function.Injective (Subtype.val : U → S))) = aeval φ := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `Δ`. Distinguish the cases in `hΔ : Δ ∈ U`. Establish `hX : (X Δ : MvPolynomial S ℚ) = rename Subtype.val (X (⟨Δ, hΔ⟩ : U))` using `by rw [rename_X]`.

Rewrite using `[AlgHom.comp_apply]`. Use `conv_lhs => rw [hX]`. Rewrite using `[killCompl_rename_app, aeval_X, aeval_X]`. Rewrite using `[AlgHom.comp_apply, aeval_X, h0 Δ hΔ, X, killCompl_monomial_eq_zero_of_not_subset, map_zero]`. Introduce `h`.

Take `⟨⟨_, hmem⟩, rfl⟩` from `h (by simp : Δ ∈ (↑(Finsupp.single Δ 1).support : Set S))`. Conclude with `hΔ hmem`. Conclude with `AlgHom.congr_fun key P`.
-/
private theorem aeval_killCompl {S B : Type*} [CommRing B] [Algebra ℚ B] (U : Set S)
    (φ : S → B) (h0 : ∀ Δ ∉ U, φ Δ = 0) (P : MvPolynomial S ℚ) :
    aeval (fun Δ : U => φ Δ) (killCompl (R := ℚ) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)) P) = aeval φ P := by
  classical
  have key : (aeval (fun Δ : U => φ Δ)).comp (killCompl (R := ℚ) (Subtype.val_injective : Function.Injective (Subtype.val : U → S))) = aeval φ := by
    apply MvPolynomial.algHom_ext
    intro Δ
    by_cases hΔ : Δ ∈ U
    · have hX : (X Δ : MvPolynomial S ℚ) = rename Subtype.val (X (⟨Δ, hΔ⟩ : U)) := by rw [rename_X]
      rw [AlgHom.comp_apply]
      conv_lhs => rw [hX]
      rw [killCompl_rename_app, aeval_X, aeval_X]
    · rw [AlgHom.comp_apply, aeval_X, h0 Δ hΔ, X, killCompl_monomial_eq_zero_of_not_subset, map_zero]
      intro h
      obtain ⟨⟨_, hmem⟩, rfl⟩ := h (by simp : Δ ∈ (↑(Finsupp.single Δ 1).support : Set S))
      exact hΔ hmem
  exact AlgHom.congr_fun key P

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on' with`. Consider the case `monomial n r`. Distinguish the cases in `hn : ↑n.support ⊆ Set.range (Subtype.val : U → S)`. Rewrite using `[killCompl_monomial_eq_monomial_comapDomain_of_subset _ _ hn, coeff_monomial, coeff_monomial]`. Establish `hiff : n.comapDomain (Subtype.val : U → S) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)).injOn = m.comapDomain (Subtype.val : U → S) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)).injOn ↔ n = m`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[← Finsupp.mapDomain_comapDomain _ Subtype.val_injective n hn, ← Finsupp.mapDomain_comapDomain _ Subtype.val_injective m hm, h]`. Introduce and unpack `rfl`. Both sides reduce to the same expression.

Simplify using `only [hiff]`. Rewrite using `[killCompl_monomial_eq_zero_of_not_subset _ _ hn, coeff_zero, coeff_monomial, if_neg]`. Introduce and unpack `rfl`. Conclude with `hn hm`. Consider the case `add P Q hP hQ => rw [map_add, coeff_add, coeff_add, hP, hQ]`.
-/
private theorem coeff_killCompl_comapDomain {S : Type*} (U : Set S) (P : MvPolynomial S ℚ) (m : S →₀ ℕ)
    (hm : ↑m.support ⊆ Set.range (Subtype.val : U → S)) :
    coeff (m.comapDomain (Subtype.val : U → S) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)).injOn)
      (killCompl (R := ℚ) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)) P) = coeff m P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial n r =>
    by_cases hn : ↑n.support ⊆ Set.range (Subtype.val : U → S)
    · rw [killCompl_monomial_eq_monomial_comapDomain_of_subset _ _ hn, coeff_monomial, coeff_monomial]
      have hiff : n.comapDomain (Subtype.val : U → S) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)).injOn =
          m.comapDomain (Subtype.val : U → S) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)).injOn ↔ n = m := by
        constructor
        · intro h
          rw [← Finsupp.mapDomain_comapDomain _ Subtype.val_injective n hn,
            ← Finsupp.mapDomain_comapDomain _ Subtype.val_injective m hm, h]
        · rintro rfl
          rfl
      simp only [hiff]
    · rw [killCompl_monomial_eq_zero_of_not_subset _ _ hn, coeff_zero, coeff_monomial, if_neg]
      rintro rfl
      exact hn hm
  | add P Q hP hQ => rw [map_add, coeff_add, coeff_add, hP, hQ]

/- English proof (translation)
Establish `hm' : ↑m.support ⊆ Set.range (Subtype.val : U → S)` using `fun Δ hΔ => ⟨⟨Δ, hm Δ (Finset.mem_coe.1 hΔ)⟩, rfl⟩`. Rewrite using `[← coeff_killCompl_comapDomain U P m hm']`. Establish `hQ : killCompl (R` using `ℚ) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)) P = 0 := by`. Apply `algebraicIndependent_iff_injective_aeval.1 hind` to reduce the goal to its premises. Rewrite using `[map_zero, aeval_killCompl U φ h0 P, hP]`.

Rewrite using `[hQ, coeff_zero]`.
-/
theorem coeff_eq_zero_of_aeval_eq_zero {S B : Type*} [CommRing B] [Algebra ℚ B] (U : Set S)
    (φ : S → B) (hind : AlgebraicIndependent ℚ (fun Δ : U => φ Δ)) (h0 : ∀ Δ ∉ U, φ Δ = 0)
    (P : MvPolynomial S ℚ) (hP : aeval φ P = 0) (m : S →₀ ℕ) (hm : ∀ Δ ∈ m.support, Δ ∈ U) :
    coeff m P = 0 := by
  classical
  have hm' : ↑m.support ⊆ Set.range (Subtype.val : U → S) := fun Δ hΔ =>
    ⟨⟨Δ, hm Δ (Finset.mem_coe.1 hΔ)⟩, rfl⟩
  rw [← coeff_killCompl_comapDomain U P m hm']
  have hQ : killCompl (R := ℚ) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)) P = 0 := by
    apply algebraicIndependent_iff_injective_aeval.1 hind
    rw [map_zero, aeval_killCompl U φ h0 P, hP]
  rw [hQ, coeff_zero]

/- English proof (translation)
Introduce `I S A _ _ Ψ M U ℓ φ hinj hU hφ0 hcnt n p c hp hne hc`. Set `Rh : List A → (I →₀ ℤ) →+ ℤ` to `fun w => Finsupp.liftAddHom fun x => AddMonoidHom.mulRight ((M x w).toNat : ℤ)`. Establish `hRs : ∀ w x a, Rh w (Finsupp.single x a) = a * ((M x w).toNat : ℤ)` using `fun w x a => by`. Simplify using `[Rh]`. Establish `hRsum : ∀ w (y : I →₀ ℤ), Rh w y = y.sum fun x a => a * ((M x w).toNat : ℤ)` using `fun w y => by`.

Simplify using `[Rh, Finsupp.liftAddHom_apply]`. Establish `K0 : ∀ (y : I →₀ ℤ) (w : List A) (N : ℕ), 0 ≤ y → (y.sum fun x a => (a.toNat : ℕ∞) * M x w) = (N : ℕ∞) → Rh w y = N`. Introduce `y w N hy hN`. Rewrite `hN` using `[Finsupp.sum]`. Establish `hfin : ∀ x ∈ y.support, ((y x).toNat : ℕ∞) * M x w ≠ ⊤`.

Introduce `x hx htop`. Establish `hle : ((y x).toNat : ℕ∞) * M x w ≤ ∑ x ∈ y.support, ((y x).toNat : ℕ∞) * M x w` using `Finset.single_le_sum (f := fun x => ((y x).toNat : ℕ∞) * M x w) (fun _ _ => zero_le) hx`. Rewrite `hle` using `[hN, htop]`. Conclude with `ENat.natCast_ne_top N (top_le_iff.1 hle)`. Establish `h1` using `congrArg ENat.toNat hN`.

Rewrite `h1` using `[ENat.toNat_sum hfin, ENat.toNat_natCast]`. Simplify using `only [ENat.toNat_mul, ENat.toNat_natCast] at h1`. Rewrite using `[hRsum, Finsupp.sum, ← h1, Nat.cast_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[Nat.cast_mul, Int.toNat_of_nonneg (Finsupp.le_def.1 hy x)]`.

Establish `K1 : ∀ (w : List A) (P : MvPolynomial S ℤ), (ShuffleAlgebra.wordBasis ℚ A).repr (aeval φ (MvPolynomial.map (Int.castRingHom ℚ) P)) w = ((Rh w (Ψ.symm P) : ℤ) : ℚ)`. Introduce `w P`. Proceed by induction on `P using MvPolynomial.induction_on' with`. Consider the case `monomial m r`. Take `⟨hpos, s, hs1, hs2⟩` from `hcnt m`.

Establish `hmr : (MvPolynomial.monomial m r : MvPolynomial S ℤ) = r • MvPolynomial.monomial m 1`. Rewrite using `[MvPolynomial.smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[MvPolynomial.map_monomial, MvPolynomial.aeval_monomial, ← hs2, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, Lyndon.repr_sum_word, hmr, map_zsmul, map_zsmul, K0 _ w _ hpos (hs1 w), smul_eq_mul, smul_eq_mul]`. Simplify using `only [eq_intCast, Int.cast_mul, Int.cast_natCast]`. Reduce the equality to equality of the corresponding arguments.

Consider the case `add P Q hP hQ`. Simplify using `only [map_add, Finsupp.add_apply, hP, hQ, Int.cast_add]`. Establish `K2 : ∀ m : S →₀ ℕ, (∃ Δ ∈ m.support, Δ ∉ U) → ∀ x, Ψ.symm (MvPolynomial.monomial m 1) x ≠ 0 → ∀ w, M x w = 0`. Introduce and unpack `m ⟨Δ, hΔ, hΔU⟩ x hx w`. Take `⟨hpos, s, hs1, hs2⟩` from `hcnt m`.

Establish `hprod : (m.prod fun Δ e => φ Δ ^ e) = 0` using `Finset.prod_eq_zero hΔ (by show φ Δ ^ m Δ = 0; rw [hφ0 Δ hΔU, zero_pow (Finsupp.mem_support_iff.1 hΔ)])`. Establish `hcount : s.count w = 0`. Establish `h` using `Lyndon.repr_sum_word ℚ s w`. Rewrite `h` using `[hs2, hprod, map_zero, Finsupp.zero_apply]`. Establish `h''` using `Nat.cast_eq_zero.1 h.symm`.

Use `h''` and compare the differences between its conclusion and the goal. Establish `h1` using `hs1 w`. Rewrite `h1` using `[hcount, Finsupp.sum, Nat.cast_zero, Finset.sum_eq_zero_iff]`. Establish `h2` using `h1 x (Finsupp.mem_support_iff.2 hx)`. Break down `mul_eq_zero.1 h2 with h | h` into its components or cases.

It suffices to derive a contradiction. Establish `hnn` using `Finsupp.le_def.1 hpos x`. Establish `h0 : (Ψ.symm (MvPolynomial.monomial m 1) x).toNat = 0` using `by exact_mod_cast h`. Simplify using `only [Finsupp.coe_zero, Pi.zero_apply] at hnn`. Use linear arithmetic over natural numbers and integers.

Conclude with `h`. Establish `hind : AlgebraicIndependent ℚ (fun Δ : U => φ Δ)`. Establish `hR` using `Published.radfordShufflePolynomial_holds.algebraicIndependent ℚ A`. Establish `he : Function.Injective (fun Δ : U => (⟨ℓ Δ, (hU Δ Δ.2).1⟩ : {w : List A // IsLyndon w}))`. Introduce `a b hab`.

Conclude with `Subtype.ext (hinj a.2 b.2 (congrArg Subtype.val hab))`. Establish `hcomp` using `hR.comp _ he`. Establish `heq : (fun Δ : U => φ Δ) = (fun l : {w : List A // IsLyndon w} => ShuffleAlgebra.word ℚ l.1) ∘ (fun Δ : U => (⟨ℓ Δ, (hU Δ Δ.2).1⟩ : {w : List A // IsLyndon w}))`. Use function extensionality and compare the values at `Δ`. Conclude with `(hU Δ Δ.2).2`.

Rewrite using `[heq]`. Conclude with `hcomp`. Establish `K3 : ∀ k : Fin n → ℤ, (∀ w, ∑ j, k j * ((M (p j) w).toNat : ℤ) = 0) → ∀ i, k i = 0`. Introduce `k hk i`. Assume the negation of the conclusion as `hki`.

Use `set y : I →₀ ℤ := ∑ j, Finsupp.single (p j) (k j) with hy`. Establish `hRy : ∀ w, Rh w y = 0` using `fun w => by`. Rewrite using `[hy, map_sum]`. Simplify using `only [hRs]`. Conclude with `hk w`.

Use `set P := Ψ y with hPdef`. Establish `hEv : aeval φ (MvPolynomial.map (Int.castRingHom ℚ) P) = 0`. Apply `(ShuffleAlgebra.wordBasis ℚ A).repr.injective` to reduce the goal to its premises. Rewrite using `[map_zero]`. Use extensionality with `w`.

Rewrite using `[K1, hPdef, AddEquiv.symm_apply_apply, hRy, Int.cast_zero, Finsupp.zero_apply]`. Establish `hcoef : ∀ m : S →₀ ℕ, (∀ Δ ∈ m.support, Δ ∈ U) → P.coeff m = 0`. Introduce `m hm`. Establish `h` using `coeff_eq_zero_of_aeval_eq_zero U φ hind hφ0 _ hEv m hm`. Rewrite `h` using `[MvPolynomial.coeff_map, eq_intCast, Int.cast_eq_zero]`.

Conclude with `h`. Establish `hyP : y = ∑ m ∈ P.support, P.coeff m • Ψ.symm (MvPolynomial.monomial m 1)`. Establish `h : y = Ψ.symm P` using `by rw [hPdef, AddEquiv.symm_apply_apply]`. Use `conv_lhs => rw [h, P.as_sum]`. Rewrite using `[map_sum]`.

Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[← map_zsmul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]`. Establish `hyi : y (p i) = k i`. Rewrite using `[hy, Finsupp.finsetSum_apply, Finset.sum_eq_single i]`. Simplify using the standard rewrite rules.

Introduce `j _ hji`. Rewrite using `[Finsupp.single_apply, if_neg]`. Conclude with `fun h => hji (hp h)`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.

Establish `hne0 : (∑ m ∈ P.support, P.coeff m • Ψ.symm (MvPolynomial.monomial m 1)) (p i) ≠ 0`. Rewrite using `[← hyP, hyi]`. Conclude with `hki`. Rewrite `hne0` using `[Finsupp.finsetSum_apply]`. Take `⟨m, _, hm0⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hne0`.

Rewrite `hm0` using `[Finsupp.smul_apply, smul_eq_mul]`. Establish `hc0 : P.coeff m ≠ 0` using `left_ne_zero_of_mul hm0`. Establish `hx0 : Ψ.symm (MvPolynomial.monomial m 1) (p i) ≠ 0` using `right_ne_zero_of_mul hm0`. Establish `hout : ∃ Δ ∈ m.support, Δ ∉ U`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hc0 (hcoef m h)`. Take `⟨w, hw⟩` from `hne i`. Conclude with `hw (K2 m hout (p i) hx0 w)`. Establish `KQ : ∀ q : Fin n → ℚ, (∀ w, ∑ j, q j * ((M (p j) w).toNat : ℚ) = 0) → ∀ i, q i = 0`.

Introduce `q hq i`. Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ) (Finset.univ : Finset (Fin n)) q`. Use `choose k hk using fun j => RingHom.mem_rangeS.1 (hb j (Finset.mem_univ j))`. Establish `hk' : ∀ j, (k j : ℚ) = ((b : ℤ) : ℚ) * q j` using `fun j => by`. Simplify `hk j` using `[Algebra.smul_def]`.

Establish `hkrel : ∀ w, ∑ j, k j * ((M (p j) w).toNat : ℤ) = 0`. Introduce `w`. Establish `h : ((∑ j, k j * ((M (p j) w).toNat : ℤ) : ℤ) : ℚ) = 0`. Use `push_cast`. Simplify using `only [hk', mul_assoc, ← Finset.mul_sum, hq w, mul_zero]`.

Conclude with `h` after adjusting the coercions. Establish `hki` using `K3 k hkrel i`. Establish `hb0 : ((b : ℤ) : ℚ) ≠ 0` using `by exact_mod_cast nonZeroDivisors.coe_ne_zero b`. Establish `h2` using `hk' i`. Rewrite `h2` using `[hki, Int.cast_zero]`.

Conclude with `(mul_eq_zero.1 h2.symm).resolve_left hb0`. Introduce `i`. Establish `hq : ∀ ψ : Module.Dual ℚ ℂ, ∀ j, ψ (c j) = 0`. Introduce `ψ`. Apply `KQ (fun j => ψ (c j))` to reduce the goal to its premises.

Introduce `w`. Establish `h` using `congrArg ψ (hc w)`. Rewrite `h` using `[map_sum, map_zero]`. Rewrite using `[← h]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Use `show ψ (c j) * _ = ψ (c j * _)`. Rewrite using `[mul_comm (c j), ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, mul_comm]`. Conclude with `(Module.forall_dual_apply_eq_zero_iff ℚ (c i)).1 fun ψ => hq ψ i`.
-/
theorem separates_of_shuffle_count : ∀ (I S : Type 1) (A : Type) [DecidableEq A] [LinearOrder A] (Ψ : (I →₀ ℤ) ≃+ MvPolynomial S ℤ) (M : I → List A → ℕ∞) (U : Set S) (ℓ : S → List A) (φ : S → ShuffleAlgebra ℚ A), Set.InjOn ℓ U → (∀ Δ ∈ U, IsLyndon (ℓ Δ) ∧ φ Δ = ShuffleAlgebra.word ℚ (ℓ Δ)) → (∀ Δ ∉ U, φ Δ = 0) → (∀ m : S →₀ ℕ, 0 ≤ Ψ.symm (MvPolynomial.monomial m 1) ∧ ∃ s : Multiset (List A), (∀ w, ((Ψ.symm (MvPolynomial.monomial m 1)).sum fun x a => (a.toNat : ℕ∞) * M x w) = (s.count w : ℕ∞)) ∧ (s.map (ShuffleAlgebra.word ℚ)).sum = m.prod fun Δ e => φ Δ ^ e) → ∀ (n : ℕ) (p : Fin n → I) (c : Fin n → ℂ), Function.Injective p → (∀ i, ∃ w, M (p i) w ≠ 0) → (∀ w, ∑ i, c i * ((M (p i) w).toNat : ℂ) = 0) → ∀ i, c i = 0 := by
  intro I S A _ _ Ψ M U ℓ φ hinj hU hφ0 hcnt n p c hp hne hc
  classical
  let Rh : List A → (I →₀ ℤ) →+ ℤ := fun w =>
    Finsupp.liftAddHom fun x => AddMonoidHom.mulRight ((M x w).toNat : ℤ)
  have hRs : ∀ w x a, Rh w (Finsupp.single x a) = a * ((M x w).toNat : ℤ) := fun w x a => by
    simp [Rh]
  have hRsum : ∀ w (y : I →₀ ℤ), Rh w y = y.sum fun x a => a * ((M x w).toNat : ℤ) := fun w y => by
    simp [Rh, Finsupp.liftAddHom_apply]
  have K0 : ∀ (y : I →₀ ℤ) (w : List A) (N : ℕ), 0 ≤ y →
      (y.sum fun x a => (a.toNat : ℕ∞) * M x w) = (N : ℕ∞) → Rh w y = N := by
    intro y w N hy hN
    rw [Finsupp.sum] at hN
    have hfin : ∀ x ∈ y.support, ((y x).toNat : ℕ∞) * M x w ≠ ⊤ := by
      intro x hx htop
      have hle : ((y x).toNat : ℕ∞) * M x w ≤ ∑ x ∈ y.support, ((y x).toNat : ℕ∞) * M x w :=
        Finset.single_le_sum (f := fun x => ((y x).toNat : ℕ∞) * M x w) (fun _ _ => zero_le) hx
      rw [hN, htop] at hle
      exact ENat.natCast_ne_top N (top_le_iff.1 hle)
    have h1 := congrArg ENat.toNat hN
    rw [ENat.toNat_sum hfin, ENat.toNat_natCast] at h1
    simp only [ENat.toNat_mul, ENat.toNat_natCast] at h1
    rw [hRsum, Finsupp.sum, ← h1, Nat.cast_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Nat.cast_mul, Int.toNat_of_nonneg (Finsupp.le_def.1 hy x)]
  have K1 : ∀ (w : List A) (P : MvPolynomial S ℤ),
      (ShuffleAlgebra.wordBasis ℚ A).repr (aeval φ (MvPolynomial.map (Int.castRingHom ℚ) P)) w =
        ((Rh w (Ψ.symm P) : ℤ) : ℚ) := by
    intro w P
    induction P using MvPolynomial.induction_on' with
    | monomial m r =>
      obtain ⟨hpos, s, hs1, hs2⟩ := hcnt m
      have hmr : (MvPolynomial.monomial m r : MvPolynomial S ℤ) = r • MvPolynomial.monomial m 1 := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [MvPolynomial.map_monomial, MvPolynomial.aeval_monomial, ← hs2, ← Algebra.smul_def, map_smul,
        Finsupp.smul_apply, Lyndon.repr_sum_word, hmr, map_zsmul, map_zsmul, K0 _ w _ hpos (hs1 w),
        smul_eq_mul, smul_eq_mul]
      simp only [eq_intCast, Int.cast_mul, Int.cast_natCast]
      congr
    | add P Q hP hQ =>
      simp only [map_add, Finsupp.add_apply, hP, hQ, Int.cast_add]
  have K2 : ∀ m : S →₀ ℕ, (∃ Δ ∈ m.support, Δ ∉ U) →
      ∀ x, Ψ.symm (MvPolynomial.monomial m 1) x ≠ 0 → ∀ w, M x w = 0 := by
    rintro m ⟨Δ, hΔ, hΔU⟩ x hx w
    obtain ⟨hpos, s, hs1, hs2⟩ := hcnt m
    have hprod : (m.prod fun Δ e => φ Δ ^ e) = 0 :=
      Finset.prod_eq_zero hΔ (by show φ Δ ^ m Δ = 0; rw [hφ0 Δ hΔU, zero_pow (Finsupp.mem_support_iff.1 hΔ)])
    have hcount : s.count w = 0 := by
      have h := Lyndon.repr_sum_word ℚ s w
      rw [hs2, hprod, map_zero, Finsupp.zero_apply] at h
      have h'' := Nat.cast_eq_zero.1 h.symm
      convert h''
    have h1 := hs1 w
    rw [hcount, Finsupp.sum, Nat.cast_zero, Finset.sum_eq_zero_iff] at h1
    have h2 := h1 x (Finsupp.mem_support_iff.2 hx)
    rcases mul_eq_zero.1 h2 with h | h
    · exfalso
      have hnn := Finsupp.le_def.1 hpos x
      have h0 : (Ψ.symm (MvPolynomial.monomial m 1) x).toNat = 0 := by exact_mod_cast h
      simp only [Finsupp.coe_zero, Pi.zero_apply] at hnn
      omega
    · exact h
  have hind : AlgebraicIndependent ℚ (fun Δ : U => φ Δ) := by
    have hR := Published.radfordShufflePolynomial_holds.algebraicIndependent ℚ A
    have he : Function.Injective
        (fun Δ : U => (⟨ℓ Δ, (hU Δ Δ.2).1⟩ : {w : List A // IsLyndon w})) := by
      intro a b hab
      exact Subtype.ext (hinj a.2 b.2 (congrArg Subtype.val hab))
    have hcomp := hR.comp _ he
    have heq : (fun Δ : U => φ Δ) =
        (fun l : {w : List A // IsLyndon w} => ShuffleAlgebra.word ℚ l.1) ∘
          (fun Δ : U => (⟨ℓ Δ, (hU Δ Δ.2).1⟩ : {w : List A // IsLyndon w})) := by
      funext Δ
      exact (hU Δ Δ.2).2
    rw [heq]
    exact hcomp
  have K3 : ∀ k : Fin n → ℤ, (∀ w, ∑ j, k j * ((M (p j) w).toNat : ℤ) = 0) → ∀ i, k i = 0 := by
    intro k hk i
    by_contra hki
    set y : I →₀ ℤ := ∑ j, Finsupp.single (p j) (k j) with hy
    have hRy : ∀ w, Rh w y = 0 := fun w => by
      rw [hy, map_sum]
      simp only [hRs]
      exact hk w
    set P := Ψ y with hPdef
    have hEv : aeval φ (MvPolynomial.map (Int.castRingHom ℚ) P) = 0 := by
      apply (ShuffleAlgebra.wordBasis ℚ A).repr.injective
      rw [map_zero]
      ext w
      rw [K1, hPdef, AddEquiv.symm_apply_apply, hRy, Int.cast_zero, Finsupp.zero_apply]
    have hcoef : ∀ m : S →₀ ℕ, (∀ Δ ∈ m.support, Δ ∈ U) → P.coeff m = 0 := by
      intro m hm
      have h := coeff_eq_zero_of_aeval_eq_zero U φ hind hφ0 _ hEv m hm
      rw [MvPolynomial.coeff_map, eq_intCast, Int.cast_eq_zero] at h
      exact h
    have hyP : y = ∑ m ∈ P.support, P.coeff m • Ψ.symm (MvPolynomial.monomial m 1) := by
      have h : y = Ψ.symm P := by rw [hPdef, AddEquiv.symm_apply_apply]
      conv_lhs => rw [h, P.as_sum]
      rw [map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← map_zsmul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    have hyi : y (p i) = k i := by
      rw [hy, Finsupp.finsetSum_apply, Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        rw [Finsupp.single_apply, if_neg]
        exact fun h => hji (hp h)
      · intro h
        exact absurd (Finset.mem_univ i) h
    have hne0 : (∑ m ∈ P.support, P.coeff m • Ψ.symm (MvPolynomial.monomial m 1)) (p i) ≠ 0 := by
      rw [← hyP, hyi]
      exact hki
    rw [Finsupp.finsetSum_apply] at hne0
    obtain ⟨m, _, hm0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne0
    rw [Finsupp.smul_apply, smul_eq_mul] at hm0
    have hc0 : P.coeff m ≠ 0 := left_ne_zero_of_mul hm0
    have hx0 : Ψ.symm (MvPolynomial.monomial m 1) (p i) ≠ 0 := right_ne_zero_of_mul hm0
    have hout : ∃ Δ ∈ m.support, Δ ∉ U := by
      by_contra h
      push_neg at h
      exact hc0 (hcoef m h)
    obtain ⟨w, hw⟩ := hne i
    exact hw (K2 m hout (p i) hx0 w)
  have KQ : ∀ q : Fin n → ℚ, (∀ w, ∑ j, q j * ((M (p j) w).toNat : ℚ) = 0) → ∀ i, q i = 0 := by
    intro q hq i
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ)
      (Finset.univ : Finset (Fin n)) q
    choose k hk using fun j => RingHom.mem_rangeS.1 (hb j (Finset.mem_univ j))
    have hk' : ∀ j, (k j : ℚ) = ((b : ℤ) : ℚ) * q j := fun j => by
      simpa [Algebra.smul_def] using hk j
    have hkrel : ∀ w, ∑ j, k j * ((M (p j) w).toNat : ℤ) = 0 := by
      intro w
      have h : ((∑ j, k j * ((M (p j) w).toNat : ℤ) : ℤ) : ℚ) = 0 := by
        push_cast
        simp only [hk', mul_assoc, ← Finset.mul_sum, hq w, mul_zero]
      exact_mod_cast h
    have hki := K3 k hkrel i
    have hb0 : ((b : ℤ) : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero b
    have h2 := hk' i
    rw [hki, Int.cast_zero] at h2
    exact (mul_eq_zero.1 h2.symm).resolve_left hb0
  intro i
  have hq : ∀ ψ : Module.Dual ℚ ℂ, ∀ j, ψ (c j) = 0 := by
    intro ψ
    apply KQ (fun j => ψ (c j))
    intro w
    have h := congrArg ψ (hc w)
    rw [map_sum, map_zero] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    show ψ (c j) * _ = ψ (c j * _)
    rw [mul_comm (c j), ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, mul_comm]
  exact (Module.forall_dual_apply_eq_zero_iff ℚ (c i)).1 fun ψ => hq ψ i

end GlobalTheory.ShuffleCount
