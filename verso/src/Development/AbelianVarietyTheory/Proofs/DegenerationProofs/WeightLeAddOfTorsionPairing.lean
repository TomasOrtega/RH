import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisAdaptedLatticeSubspace
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsNilpotentSubOneOfConjPow
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FinrankLeOfWeightsUnipotentSymplecticStatement

namespace GlobalTheory.SS.Weight
open Module
open scoped TensorProduct nonZeroDivisors

/- English proof (translation)
Take `⟨u, snf⟩` from `U.smithNormalForm (Module.Free.chooseBasis ℤ_[l] T)`. Establish `hu : finrank ℤ_[l] U = u` using `by rw [finrank_eq_card_basis snf.bN, Fintype.card_fin]`. Rewrite using `[hu]`. Establish `ha : ∀ i, snf.a i ≠ 0`. Introduce `i h`.

Apply `snf.bN.ne_zero i` to reduce the goal to its premises. Use `ext`. Rewrite using `[snf.snf, h, zero_smul]`. Both sides reduce to the same expression. Choose the witnesses or unpack the hypotheses as in `⟨e, he⟩ : ∃ e : ℕ, ∀ i, snf.a i ∣ (l : ℤ_[l]) ^ e := by`.

Use `⟨∑ i, (snf.a i).valuation, fun i => ?_⟩` and prove the remaining obligations. Establish `h1 : snf.a i ∣ (l : ℤ_[l]) ^ (snf.a i).valuation` using `by conv_lhs => rw [PadicInt.unitCoeff_spec (ha i)]`. Rewrite using `[Units.mul_left_dvd]`. Conclude with `h1.trans (pow_dvd_pow _ (Finset.single_le_sum (f := fun i => (snf.a i).valuation) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)))`. Establish `hl0 : (l : ℤ_[l]) ≠ 0` using `Nat.cast_ne_zero.2 hl.out.ne_zero`.

Establish `key : ∀ n, (l ^ n) ^ u ≤ C * l ^ ((n + e) * k)`. Introduce `n`. Use `le_trans ?_ (hc (n + e))` and prove the remaining obligations. Establish `htor : ∀ x, l ^ (n + e) • π (n + e) x = 0` using `fun x => by`. Rewrite using `[← map_nsmul, hker]`.

Conclude with `⟨x, rfl⟩`. Use `haveI : Finite {x : H // l ^ (n + e) • x = 0} := by haveI := hfin (n + e)`. Use `Finite.of_injective (β := {x : M // l ^ (n + e) • x = 0}) (fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩) ?_` and prove the remaining obligations. Introduce `x y h`. Conclude with `Subtype.ext (Subtype.ext (congrArg (fun z => z.1) h))`.

Set `v : (Fin u → Fin (l ^ n)) → U` to `fun c => snf.bN.equivFun.symm fun i => ((c i : ℕ) : ℤ_[l])`. Set `F : (Fin u → Fin (l ^ n)) → {x : H // l ^ (n + e) • x = 0}` to `fun c => ⟨⟨π (n + e) (v c), hU _ _ (v c).2⟩, Subtype.ext (htor _)⟩`. Establish `hF : Function.Injective F`. Introduce `c c' h`. Establish `h1 : π (n + e) ((v c - v c' : U) : T) = 0`.

Rewrite using `[Submodule.coe_sub, map_sub, sub_eq_zero]`. Conclude with `congrArg (fun z => z.1.1) h`. Take `⟨y, hy⟩` from `(hker _ _).1 h1`. Use function extensionality and compare the values at `i`. Establish `h2` using `snf.repr_apply_embedding_eq_repr_smul (v c - v c') (i := i)`.

Rewrite `h2` using `[hy, map_nsmul, map_smul, map_sub]`. Establish `h3 : ∀ c, snf.bN.repr (v c) i = ((c i : ℕ) : ℤ_[l])` using `fun c => by`. Rewrite using `[← snf.bN.equivFun_apply]`. Simplify using `only [v, LinearEquiv.apply_symm_apply]`. Simplify using `only [Finsupp.smul_apply, Finsupp.sub_apply, h3, nsmul_eq_mul, smul_eq_mul] at h2`.

Establish `h4 : (l : ℤ_[l]) ^ e * (l : ℤ_[l]) ^ n ∣ (l : ℤ_[l]) ^ e * (((c i : ℕ) : ℤ_[l]) - ((c' i : ℕ) : ℤ_[l]))`. Use `Dvd.dvd.trans ?_ (mul_dvd_mul_right (he i) _)` and prove the remaining obligations. Rewrite using `[← h2]`. Use `Dvd.dvd.mul_right ?_ _` and prove the remaining obligations. Rewrite using `[← pow_add, add_comm]`.

Simplify using the standard rewrite rules. Establish `h5` using `(mul_dvd_mul_iff_left (pow_ne_zero e hl0)).1 h4`. Establish `h6 : ((l : ℤ) ^ n) ∣ (((c i : ℕ) : ℤ) - ((c' i : ℕ) : ℤ))`. Rewrite using `[← PadicInt.pow_p_dvd_int_iff]`. Simplify using `using h5`.

Establish `h7` using `(c i).2`. Establish `h8` using `(c' i).2`. Establish `h9 : (((c i : ℕ) : ℤ) - ((c' i : ℕ) : ℤ)) = 0`. Use `Int.eq_zero_of_abs_lt_dvd h6 ?_` and prove the remaining obligations. Use `zify at h7 h8`.

Apply the tactic sequence `rw [abs_lt]; constructor <;> omega`. Use `ext`. Use linear arithmetic over natural numbers and integers. Use `Nat.card_le_card_of_injective F hF` as an intermediate fact. Simplify using `using this`.

Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Use `set n := C * l ^ (e * k) with hn`. Establish `h1` using `key n`. Establish `h2 : l ^ n * l ^ (n * k) ≤ (l ^ n) ^ u`.

Rewrite using `[← pow_add, ← pow_mul]`. Conclude with `Nat.pow_le_pow_right hl.out.pos (by nlinarith)`. Establish `h3 : C * l ^ ((n + e) * k) = n * l ^ (n * k)`. Rewrite using `[add_mul, pow_add]`. Use `conv_rhs => rw [hn]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h4 : n < l ^ n` using `Nat.lt_pow_self hl.out.one_lt`. Establish `h5 : 0 < l ^ (n * k)` using `pow_pos hl.out.pos _`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem finrank_le_of_card (l : ℕ) [hl : Fact l.Prime] {T M : Type} [AddCommGroup T]
    [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] [AddCommGroup M]
    (π : ℕ → T →+ M) (hker : ∀ n x, π n x = 0 ↔ ∃ y, x = l ^ n • y)
    (hfin : ∀ n, Finite {x : M // l ^ n • x = 0})
    (U : Submodule ℤ_[l] T) (H : AddSubgroup M) (hU : ∀ n, ∀ x ∈ U, π n x ∈ H) (C k : ℕ)
    (hc : ∀ n, Nat.card {x : H // l ^ n • x = 0} ≤ C * l ^ (n * k)) :
    finrank ℤ_[l] U ≤ k := by
  classical
  obtain ⟨u, snf⟩ := U.smithNormalForm (Module.Free.chooseBasis ℤ_[l] T)
  have hu : finrank ℤ_[l] U = u := by rw [finrank_eq_card_basis snf.bN, Fintype.card_fin]
  rw [hu]
  have ha : ∀ i, snf.a i ≠ 0 := by
    intro i h
    apply snf.bN.ne_zero i
    ext
    rw [snf.snf, h, zero_smul]; rfl
  obtain ⟨e, he⟩ : ∃ e : ℕ, ∀ i, snf.a i ∣ (l : ℤ_[l]) ^ e := by
    refine ⟨∑ i, (snf.a i).valuation, fun i => ?_⟩
    have h1 : snf.a i ∣ (l : ℤ_[l]) ^ (snf.a i).valuation := by
      conv_lhs => rw [PadicInt.unitCoeff_spec (ha i)]
      rw [Units.mul_left_dvd]
    exact h1.trans (pow_dvd_pow _ (Finset.single_le_sum (f := fun i => (snf.a i).valuation)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)))
  have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  have key : ∀ n, (l ^ n) ^ u ≤ C * l ^ ((n + e) * k) := by
    intro n
    refine le_trans ?_ (hc (n + e))
    have htor : ∀ x, l ^ (n + e) • π (n + e) x = 0 := fun x => by
      rw [← map_nsmul, hker]; exact ⟨x, rfl⟩
    haveI : Finite {x : H // l ^ (n + e) • x = 0} := by
      haveI := hfin (n + e)
      refine Finite.of_injective (β := {x : M // l ^ (n + e) • x = 0})
        (fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩) ?_
      intro x y h
      exact Subtype.ext (Subtype.ext (congrArg (fun z => z.1) h))
    let v : (Fin u → Fin (l ^ n)) → U := fun c => snf.bN.equivFun.symm fun i => ((c i : ℕ) : ℤ_[l])
    let F : (Fin u → Fin (l ^ n)) → {x : H // l ^ (n + e) • x = 0} := fun c =>
      ⟨⟨π (n + e) (v c), hU _ _ (v c).2⟩, Subtype.ext (htor _)⟩
    have hF : Function.Injective F := by
      intro c c' h
      have h1 : π (n + e) ((v c - v c' : U) : T) = 0 := by
        rw [Submodule.coe_sub, map_sub, sub_eq_zero]
        exact congrArg (fun z => z.1.1) h
      obtain ⟨y, hy⟩ := (hker _ _).1 h1
      funext i
      have h2 := snf.repr_apply_embedding_eq_repr_smul (v c - v c') (i := i)
      rw [hy, map_nsmul, map_smul, map_sub] at h2
      have h3 : ∀ c, snf.bN.repr (v c) i = ((c i : ℕ) : ℤ_[l]) := fun c => by
        rw [← snf.bN.equivFun_apply]; simp only [v, LinearEquiv.apply_symm_apply]
      simp only [Finsupp.smul_apply, Finsupp.sub_apply, h3, nsmul_eq_mul, smul_eq_mul] at h2
      have h4 : (l : ℤ_[l]) ^ e * (l : ℤ_[l]) ^ n ∣
          (l : ℤ_[l]) ^ e * (((c i : ℕ) : ℤ_[l]) - ((c' i : ℕ) : ℤ_[l])) := by
        refine Dvd.dvd.trans ?_ (mul_dvd_mul_right (he i) _)
        rw [← h2]
        refine Dvd.dvd.mul_right ?_ _
        rw [← pow_add, add_comm]; simp
      have h5 := (mul_dvd_mul_iff_left (pow_ne_zero e hl0)).1 h4
      have h6 : ((l : ℤ) ^ n) ∣ (((c i : ℕ) : ℤ) - ((c' i : ℕ) : ℤ)) := by
        rw [← PadicInt.pow_p_dvd_int_iff]; simpa using h5
      have h7 := (c i).2
      have h8 := (c' i).2
      have h9 : (((c i : ℕ) : ℤ) - ((c' i : ℕ) : ℤ)) = 0 := by
        refine Int.eq_zero_of_abs_lt_dvd h6 ?_
        zify at h7 h8
        rw [abs_lt]; constructor <;> omega
      ext; omega
    have := Nat.card_le_card_of_injective F hF
    simpa using this
  by_contra hlt
  push_neg at hlt
  set n := C * l ^ (e * k) with hn
  have h1 := key n
  have h2 : l ^ n * l ^ (n * k) ≤ (l ^ n) ^ u := by
    rw [← pow_add, ← pow_mul]
    exact Nat.pow_le_pow_right hl.out.pos (by nlinarith)
  have h3 : C * l ^ ((n + e) * k) = n * l ^ (n * k) := by
    rw [add_mul, pow_add]; conv_rhs => rw [hn]
    ring
  have h4 : n < l ^ n := Nat.lt_pow_self hl.out.one_lt
  have h5 : 0 < l ^ (n * k) := pow_pos hl.out.pos _
  nlinarith

/- English proof (translation)
Set `V` to `ℚ_[l] ⊗[ℤ_[l]] T`. Set `ι : T →ₗ[ℤ_[l]] V` to `TensorProduct.mk ℤ_[l] ℚ_[l] T 1`. Use `haveI hloc : IsLocalizedModule (ℤ_[l])⁰ ι := inferInstanceAs (IsLocalizedModule (ℤ_[l])⁰ (TensorProduct.mk ℤ_[l] ℚ_[l] T 1))`. Establish `hinj : Function.Injective ι` using `(IsLocalizedModule.injective_iff_isRegular (ℤ_[l])⁰ ι).2 fun s => IsSMulRegular.of_ne_zero (nonZeroDivisors.ne_zero s.2)`. Establish `hsurj : ∀ v : V, ∃ (s : ℚ_[l]) (t : T), v = s • ι t`.

Introduce `v`. Take `⟨⟨t, s⟩, h⟩` from `IsLocalizedModule.surj (ℤ_[l])⁰ ι v`. Establish `hs : (algebraMap ℤ_[l] ℚ_[l] s) ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective ℤ_[l] ℚ_[l])).2 (nonZeroDivisors.ne_zero s.2)`. Use `⟨(algebraMap ℤ_[l] ℚ_[l] s)⁻¹, t, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_inv_smul_iff₀ hs, algebraMap_smul]`.

Conclude with `h`. Set `S' : V ≃ₗ[ℚ_[l]] V` to `LinearEquiv.baseChange ℤ_[l] ℚ_[l] T T S`. Set `Φ' : V ≃ₗ[ℚ_[l]] V` to `LinearEquiv.baseChange ℤ_[l] ℚ_[l] T T Φ`. Establish `hS' : ∀ t, S' (ι t) = ι (S t)` using `fun t => LinearEquiv.baseChange_tmul ..`. Establish `hΦ' : ∀ t, Φ' (ι t) = ι (Φ t)` using `fun t => LinearEquiv.baseChange_tmul ..`.

Set `B' : LinearMap.BilinForm ℚ_[l] V` to `B.baseChange ℚ_[l]`. Establish `hB' : ∀ x y, B' (ι x) (ι y) = algebraMap ℤ_[l] ℚ_[l] (B x y)` using `fun x y => by`. Use `LinearMap.BilinForm.baseChange_tmul (A := ℚ_[l]) B 1 x 1 y` as an intermediate fact. Rewrite `this` using `[mul_one, ← Algebra.algebraMap_eq_smul_one]`. Conclude with `this`.

Establish `hsk' : ∀ x y, B' y x = - B' x y`. Introduce `x y`. Take `⟨s, x, rfl⟩` from `hsurj x`. Take `⟨s', y, rfl⟩` from `hsurj y`. Simplify using `only [map_smul, LinearMap.smul_apply, hB', hsk x y, map_neg, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hleft : ∀ x, (∀ y, B' x y = 0) → x = 0`. Introduce `x hx`. Take `⟨s, x, rfl⟩` from `hsurj x`. Distinguish the cases in `hs : s = 0`.

Simplify using `[hs]`. Establish `: x = 0` using `hB x fun y => by`. Use `hx (ι y)` as an intermediate fact. Simplify using `only [map_smul, LinearMap.smul_apply, hB', smul_eq_mul, mul_eq_zero, hs, false_or] at this`. Conclude with `(map_eq_zero_iff _ (IsFractionRing.injective ℤ_[l] ℚ_[l])).1 this`.

Simplify using `[this]`. Establish `hfix : ∀ v, S' v = v → ∃ (s : ℚ_[l]) (t : T), S t = t ∧ v = s • ι t`. Introduce `v hv`. Take `⟨s, t, rfl⟩` from `hsurj v`. Distinguish the cases in `hs : s = 0`.

Conclude with `⟨0, 0, by simp, by simp [hs]⟩`. Use `⟨s, t, hinj ?_, rfl⟩` and prove the remaining obligations. Rewrite `hv` using `[map_smul, hS']`. Conclude with `smul_right_injective V hs hv`. Establish `hmem : ∀ (U : Submodule ℤ_[l] T) (s : ℚ_[l]) (t : T), t ∈ U → s • ι t ∈ U.localized' ℚ_[l] (ℤ_[l])⁰ ι` using `fun U s t ht => Submodule.smul_mem _ _ ⟨t, ht, 1, IsLocalizedModule.mk'_one _ _ _⟩`.

Establish `hrk : ∀ (U : Submodule ℤ_[l] T), finrank ℚ_[l] (U.localized' ℚ_[l] (ℤ_[l])⁰ ι) = finrank ℤ_[l] U` using `fun U => by`. Rewrite using `[IsLocalization.finrank_eq ℚ_[l] (ℤ_[l])⁰ le_rfl, IsLocalizedModule.finrank_eq (ℤ_[l])⁰ (U.toLocalized' ℚ_[l] (ℤ_[l])⁰ ι) le_rfl]`. Establish `hit : ∀ (E : T ≃ₗ[ℤ_[l]] T) (E' : V ≃ₗ[ℚ_[l]] V), (∀ t, E' (ι t) = ι (E t)) → ∀ (j : ℕ) t, E'^[j] (ι t) = ι (E^[j] t)`. Introduce `E E' h j`. Proceed by induction on `j with`.

Consider the case `zero => intro t`. Both sides reduce to the same expression. Consider the case `succ j ih => intro t`. Rewrite using `[Function.iterate_succ_apply, Function.iterate_succ_apply, h, ih]`. Establish `main` using `GlobalTheory.T.finrank_le_of_weights_unipotent_symplectic ℚ_[l] V B' ⟨hleft, fun y hy => hleft y fun x => by`.

Rewrite using `[hsk' x y, hy x, neg_zero]⟩ hsk' S' Φ' q hq ?_ ?_ ?_ ?_`. Use the proof step `(W.localized' ℚ_[l] (ℤ_[l])⁰ ι) P hP ?_ ?_`. Establish `h1 : finrank ℚ_[l] V = finrank ℤ_[l] T` using `Module.finrank_baseChange`. Rewrite `main` using `[h1, hrk]`. Use `main.trans (Nat.add_le_add_right ?_ _)` and prove the remaining obligations.

Rewrite using `[← hrk]`. Use `Submodule.finrank_mono fun v hv => ?_` and prove the remaining obligations. Take `⟨s, t, ht, rfl⟩` from `hfix v (by simpa [sub_eq_zero] using hv)`. Conclude with `hmem _ s t (by simpa [sub_eq_zero] using ht)`. Use `hN.map (Module.End.baseChangeHom ℤ_[l] ℚ_[l] T)` as an intermediate fact.

Rewrite `this` using `[map_sub, map_one]`. Conclude with `this`. Introduce `x y`. Take `⟨s, x, rfl⟩` from `hsurj x`. Take `⟨s', y, rfl⟩` from `hsurj y`.

Simplify using `only [map_smul, LinearMap.smul_apply, hS', hB', hS]`. Introduce `x y`. Take `⟨s, x, rfl⟩` from `hsurj x`. Take `⟨s', y, rfl⟩` from `hsurj y`. Simplify using `only [map_smul, LinearMap.smul_apply, hΦ', hB', hΦ, map_mul, map_natCast, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Use extensionality with `v`. Take `⟨s, t, rfl⟩` from `hsurj v`. Establish `h1 : Φ (S t) = S^[q] (Φ t)`. Use `LinearEquiv.congr_fun hc t` as an intermediate fact.

Rewrite `this` using `[LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.pow_apply]`. Then use the resulting hypothesis. Rewrite using `[map_smul, map_smul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.pow_apply, hS', hΦ', hΦ', hit S S' hS', h1]`. Introduce `v hv`. Rewrite `hv` using `[Submodule.localized'_eq_span]`. Proceed by induction on `hv using Submodule.span_induction with`.

Consider the case `mem v hv`. Take `⟨t, ht, rfl⟩` from `hv`. Rewrite using `[hΦ', hW t ht, map_nsmul, Nat.cast_smul_eq_nsmul]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]`.

Consider the case `smul a x _ hx => rw [map_smul, hx, smul_comm]`. Introduce `v hv`. Take `⟨s, t, ht, rfl⟩` from `hfix v hv`. Establish `hc1 : (c : ℚ_[l]) ≠ 0` using `Nat.cast_ne_zero.2 hc0`. Establish `h1 : s • ι t = (s * (c : ℚ_[l])⁻¹) • ι (c • t)`.

Rewrite using `[map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ_[l], smul_smul, mul_assoc, inv_mul_cancel₀ hc1, mul_one]`. Establish `h2` using `hmem W (s * (c : ℚ_[l])⁻¹) _ (hPW t ht)`. Rewrite using `[h1, map_smul, Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]`. Use `h2 using 2` and compare the differences between its conclusion and the goal. Rewrite using `[map_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, ← hit Φ Φ' hΦ', LinearMap.smul_apply, Module.End.pow_apply]`. Both sides reduce to the same expression.
-/
theorem finrank_le_ker_add (l : ℕ) [Fact l.Prime] {T : Type} [AddCommGroup T]
    [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T]
    (B : LinearMap.BilinForm ℤ_[l] T) (hB : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hsk : ∀ x y, B y x = - B x y) (S Φ : T ≃ₗ[ℤ_[l]] T) (q : ℕ) (hq : 2 ≤ q)
    (hN : IsNilpotent ((S : T →ₗ[ℤ_[l]] T) - 1)) (hS : ∀ x y, B (S x) (S y) = B x y)
    (hΦ : ∀ x y, B (Φ x) (Φ y) = q * B x y) (hc : Φ * S = S ^ q * Φ)
    (W : Submodule ℤ_[l] T) (P : Polynomial ℤ)
    (hP : ∀ β : ℂ, Polynomial.aeval β P = 0 → ‖β‖ < q) (hW : ∀ x ∈ W, Φ x = q • x)
    (c : ℕ) (hc0 : c ≠ 0)
    (hPW : ∀ x, S x = x →
      ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j • (Φ^[j] (c • x)) ∈ W) :
    finrank ℤ_[l] T ≤ finrank ℤ_[l] (LinearMap.ker ((S : T →ₗ[ℤ_[l]] T) - 1)) +
      finrank ℤ_[l] W := by
  let V := ℚ_[l] ⊗[ℤ_[l]] T
  let ι : T →ₗ[ℤ_[l]] V := TensorProduct.mk ℤ_[l] ℚ_[l] T 1
  haveI hloc : IsLocalizedModule (ℤ_[l])⁰ ι := inferInstanceAs
    (IsLocalizedModule (ℤ_[l])⁰ (TensorProduct.mk ℤ_[l] ℚ_[l] T 1))
  have hinj : Function.Injective ι :=
    (IsLocalizedModule.injective_iff_isRegular (ℤ_[l])⁰ ι).2 fun s =>
      IsSMulRegular.of_ne_zero (nonZeroDivisors.ne_zero s.2)
  have hsurj : ∀ v : V, ∃ (s : ℚ_[l]) (t : T), v = s • ι t := by
    intro v
    obtain ⟨⟨t, s⟩, h⟩ := IsLocalizedModule.surj (ℤ_[l])⁰ ι v
    have hs : (algebraMap ℤ_[l] ℚ_[l] s) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective ℤ_[l] ℚ_[l])).2 (nonZeroDivisors.ne_zero s.2)
    refine ⟨(algebraMap ℤ_[l] ℚ_[l] s)⁻¹, t, ?_⟩
    rw [eq_inv_smul_iff₀ hs, algebraMap_smul]
    exact h
  let S' : V ≃ₗ[ℚ_[l]] V := LinearEquiv.baseChange ℤ_[l] ℚ_[l] T T S
  let Φ' : V ≃ₗ[ℚ_[l]] V := LinearEquiv.baseChange ℤ_[l] ℚ_[l] T T Φ
  have hS' : ∀ t, S' (ι t) = ι (S t) := fun t => LinearEquiv.baseChange_tmul ..
  have hΦ' : ∀ t, Φ' (ι t) = ι (Φ t) := fun t => LinearEquiv.baseChange_tmul ..
  let B' : LinearMap.BilinForm ℚ_[l] V := B.baseChange ℚ_[l]
  have hB' : ∀ x y, B' (ι x) (ι y) = algebraMap ℤ_[l] ℚ_[l] (B x y) := fun x y => by
    have := LinearMap.BilinForm.baseChange_tmul (A := ℚ_[l]) B 1 x 1 y
    rw [mul_one, ← Algebra.algebraMap_eq_smul_one] at this
    exact this
  have hsk' : ∀ x y, B' y x = - B' x y := by
    intro x y
    obtain ⟨s, x, rfl⟩ := hsurj x
    obtain ⟨s', y, rfl⟩ := hsurj y
    simp only [map_smul, LinearMap.smul_apply, hB', hsk x y, map_neg, smul_eq_mul]
    ring
  have hleft : ∀ x, (∀ y, B' x y = 0) → x = 0 := by
    intro x hx
    obtain ⟨s, x, rfl⟩ := hsurj x
    by_cases hs : s = 0
    · simp [hs]
    have : x = 0 := hB x fun y => by
      have := hx (ι y)
      simp only [map_smul, LinearMap.smul_apply, hB', smul_eq_mul, mul_eq_zero, hs,
        false_or] at this
      exact (map_eq_zero_iff _ (IsFractionRing.injective ℤ_[l] ℚ_[l])).1 this
    simp [this]
  have hfix : ∀ v, S' v = v → ∃ (s : ℚ_[l]) (t : T), S t = t ∧ v = s • ι t := by
    intro v hv
    obtain ⟨s, t, rfl⟩ := hsurj v
    by_cases hs : s = 0
    · exact ⟨0, 0, by simp, by simp [hs]⟩
    refine ⟨s, t, hinj ?_, rfl⟩
    rw [map_smul, hS'] at hv
    exact smul_right_injective V hs hv
  have hmem : ∀ (U : Submodule ℤ_[l] T) (s : ℚ_[l]) (t : T), t ∈ U →
      s • ι t ∈ U.localized' ℚ_[l] (ℤ_[l])⁰ ι := fun U s t ht =>
    Submodule.smul_mem _ _ ⟨t, ht, 1, IsLocalizedModule.mk'_one _ _ _⟩
  have hrk : ∀ (U : Submodule ℤ_[l] T),
      finrank ℚ_[l] (U.localized' ℚ_[l] (ℤ_[l])⁰ ι) = finrank ℤ_[l] U := fun U => by
    rw [IsLocalization.finrank_eq ℚ_[l] (ℤ_[l])⁰ le_rfl,
      IsLocalizedModule.finrank_eq (ℤ_[l])⁰ (U.toLocalized' ℚ_[l] (ℤ_[l])⁰ ι) le_rfl]
  have hit : ∀ (E : T ≃ₗ[ℤ_[l]] T) (E' : V ≃ₗ[ℚ_[l]] V), (∀ t, E' (ι t) = ι (E t)) →
      ∀ (j : ℕ) t, E'^[j] (ι t) = ι (E^[j] t) := by
    intro E E' h j
    induction j with
    | zero => intro t; rfl
    | succ j ih => intro t; rw [Function.iterate_succ_apply, Function.iterate_succ_apply, h, ih]
  have main := GlobalTheory.T.finrank_le_of_weights_unipotent_symplectic ℚ_[l] V B' ⟨hleft, fun y hy => hleft y fun x => by
      rw [hsk' x y, hy x, neg_zero]⟩ hsk' S' Φ' q hq ?_ ?_ ?_ ?_
    (W.localized' ℚ_[l] (ℤ_[l])⁰ ι) P hP ?_ ?_
  · have h1 : finrank ℚ_[l] V = finrank ℤ_[l] T := Module.finrank_baseChange
    rw [h1, hrk] at main
    refine main.trans (Nat.add_le_add_right ?_ _)
    rw [← hrk]
    refine Submodule.finrank_mono fun v hv => ?_
    obtain ⟨s, t, ht, rfl⟩ := hfix v (by simpa [sub_eq_zero] using hv)
    exact hmem _ s t (by simpa [sub_eq_zero] using ht)
  · have := hN.map (Module.End.baseChangeHom ℤ_[l] ℚ_[l] T)
    rw [map_sub, map_one] at this
    exact this
  · intro x y
    obtain ⟨s, x, rfl⟩ := hsurj x
    obtain ⟨s', y, rfl⟩ := hsurj y
    simp only [map_smul, LinearMap.smul_apply, hS', hB', hS]
  · intro x y
    obtain ⟨s, x, rfl⟩ := hsurj x
    obtain ⟨s', y, rfl⟩ := hsurj y
    simp only [map_smul, LinearMap.smul_apply, hΦ', hB', hΦ, map_mul, map_natCast, smul_eq_mul]
    ring
  · ext v
    obtain ⟨s, t, rfl⟩ := hsurj v
    have h1 : Φ (S t) = S^[q] (Φ t) := by
      have := LinearEquiv.congr_fun hc t
      rwa [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.pow_apply] at this
    rw [map_smul, map_smul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.pow_apply,
      hS', hΦ', hΦ', hit S S' hS', h1]
  · intro v hv
    rw [Submodule.localized'_eq_span] at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨t, ht, rfl⟩ := hv
      rw [hΦ', hW t ht, map_nsmul, Nat.cast_smul_eq_nsmul]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
    | smul a x _ hx => rw [map_smul, hx, smul_comm]
  · intro v hv
    obtain ⟨s, t, ht, rfl⟩ := hfix v hv
    have hc1 : (c : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hc0
    have h1 : s • ι t = (s * (c : ℚ_[l])⁻¹) • ι (c • t) := by
      rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ_[l], smul_smul, mul_assoc, inv_mul_cancel₀ hc1,
        mul_one]
    have h2 := hmem W (s * (c : ℚ_[l])⁻¹) _ (hPW t ht)
    rw [h1, map_smul, Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
    convert h2 using 2
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, ← hit Φ Φ' hΦ', LinearMap.smul_apply, Module.End.pow_apply]
    rfl

/- English proof (translation)
Establish `hext : ∀ x y : T, (∀ n, π n x = π n y) → x = y` using `fun x y h => (hu (fun n => π n y) (h0 y) (fun n => h1 n y)).unique h fun _ => rfl`. Establish `lin : ∀ S : M ≃+ M, ∃ S' : T →ₗ[ℤ_[l]] T, ∀ n x, π n (S' x) = S (π n x)`. Introduce `S`. Use `choose f hf using fun x => (hu (fun n => S (π n x)) (by simp [h0]) (fun n => by rw [← map_nsmul, h1])).exists`. Use `⟨⟨⟨f, fun x y => hext _ _ fun n => ?_⟩, fun a x => hext _ _ fun n => ?_⟩, fun n x => hf x n⟩` and prove the remaining obligations.

Simplify using `[hf]`. Simplify using `[hf, hs]`. Take `⟨f, hf⟩` from `lin S`. Take `⟨g, hg⟩` from `lin S.symm`. Use `⟨LinearEquiv.ofLinear f g ?_ ?_, hf⟩` and prove the remaining obligations.

Use extensionality with `x; exact hext _ _ fun n => by simp [hf, hg]`. Use extensionality with `x; exact hext _ _ fun n => by simp [hf, hg]`.
-/
theorem exists_lift (l : ℕ) [Fact l.Prime] {T M : Type} [AddCommGroup T]
    [Module ℤ_[l] T] [AddCommGroup M] (π : ℕ → T →+ M)
    (h1 : ∀ n x, l • π (n + 1) x = π n x) (h0 : ∀ x, π 0 x = 0)
    (hs : ∀ n (a : ℤ_[l]) x, π n (a • x) = (PadicInt.toZModPow n a).val • π n x)
    (hu : ∀ s : ℕ → M, s 0 = 0 → (∀ n, l • s (n + 1) = s n) → ∃! x, ∀ n, π n x = s n)
    (S : M ≃+ M) : ∃ S' : T ≃ₗ[ℤ_[l]] T, ∀ n x, π n (S' x) = S (π n x) := by
  have hext : ∀ x y : T, (∀ n, π n x = π n y) → x = y := fun x y h =>
    (hu (fun n => π n y) (h0 y) (fun n => h1 n y)).unique h fun _ => rfl
  have lin : ∀ S : M ≃+ M, ∃ S' : T →ₗ[ℤ_[l]] T, ∀ n x, π n (S' x) = S (π n x) := by
    intro S
    choose f hf using fun x => (hu (fun n => S (π n x)) (by simp [h0])
      (fun n => by rw [← map_nsmul, h1])).exists
    refine ⟨⟨⟨f, fun x y => hext _ _ fun n => ?_⟩, fun a x => hext _ _ fun n => ?_⟩,
      fun n x => hf x n⟩
    · simp [hf]
    · simp [hf, hs]
  obtain ⟨f, hf⟩ := lin S
  obtain ⟨g, hg⟩ := lin S.symm
  refine ⟨LinearEquiv.ofLinear f g ?_ ?_, hf⟩
  · ext x; exact hext _ _ fun n => by simp [hf, hg]
  · ext x; exact hext _ _ fun n => by simp [hf, hg]

/- English proof (translation)
Use `haveI : Fact l.Prime := ⟨hl⟩`. Take `⟨T, _, _, π, _, _, hrk, h1, h0, hs, hsurj, hker, hu⟩` from `GlobalTheory.exists_tateModule_of_card M l (2 * g) fun n => by rw [hM, mul_comm]`. Take `⟨T', _, _, π', _, _, hrk', h1', h0', hs', -, -, hu'⟩` from `GlobalTheory.exists_tateModule_of_card A l 1 fun n => by rw [hA, one_mul]`. Establish `hext : ∀ x y : T, (∀ n, π n x = π n y) → x = y` using `fun x y h => (hu (fun n => π n y) (h0 y) (fun n => h1 n y)).unique h fun _ => rfl`. Establish `hext' : ∀ x y : T', (∀ n, π' n x = π' n y) → x = y` using `fun x y h => (hu' (fun n => π' n y) (h0' y) (fun n => h1' n y)).unique h fun _ => rfl`.

Establish `htor : ∀ n x, l ^ n • π n x = 0` using `fun n x => by`. Rewrite using `[← map_nsmul, hker]`. Conclude with `⟨x, rfl⟩`. Establish `hfin : ∀ n, Finite {x : M // l ^ n • x = 0}` using `fun n => Nat.finite_of_card_ne_zero (by rw [hM]; exact pow_ne_zero _ hl.ne_zero)`. Establish `hsm : ∀ n (k : ℕ) x y, l ^ n • x = 0 → l ^ n • y = 0 → e n (k • x) y = k • e n x y`.

Introduce `n k x y hx hy`. Proceed by induction on `k with`. Consider the case `zero`. Use `(he1 n 0 0 y (by simp) (by simp) hy).1` as an intermediate fact. Simplify using `using this`.

Consider the case `succ k ih`. Rewrite using `[succ_nsmul, succ_nsmul, (he1 n _ x y (by rw [smul_comm, hx, smul_zero]) hx hy).1, ih]`. Establish `hsk : ∀ n x y, l ^ n • x = 0 → l ^ n • y = 0 → e n y x = - e n x y` using `fun n x y hx hy => (he1 n x x y hx hx hy).2`. Use `choose b hb using fun x y : T => (hu' (fun n => e n (π n x) (π n y)) (by`. Use `hsm 0 0 (π 0 x) (π 0 y) (htor _ _) (htor _ _)` as an intermediate fact.

Rewrite `this` using `[zero_smul, zero_smul]`. Rewrite using `[← this, h0 x])`. Use the proof step `(fun n => by`. Establish `hy : l ^ (n + 1) • π n y = 0` using `by rw [pow_succ', mul_smul, htor, smul_zero]`. Rewrite using `[hsk (n + 1) _ _ (htor _ y) (htor _ x), smul_neg, ← hsm _ _ _ _ (htor _ y) (htor _ x), h1, ← hsk (n + 1) _ _ hy (htor _ x), he2 _ _ _ (htor _ x) (htor _ y), h1])).exists`.

Establish `bsk : ∀ x y, b y x = - b x y` using `fun x y => hext' _ _ fun n => by`. Rewrite using `[map_neg, hb, hb, hsk n _ _ (htor _ x) (htor _ y)]`. Establish `badd : ∀ x x' y, b (x + x') y = b x y + b x' y` using `fun x x' y => hext' _ _ fun n => by`. Rewrite using `[map_add, hb, hb, hb, map_add, (he1 n _ _ _ (htor _ x) (htor _ x') (htor _ y)).1]`. Establish `bsm : ∀ (r : ℤ_[l]) x y, b (r • x) y = r • b x y` using `fun r x y => hext' _ _ fun n => by`.

Rewrite using `[hs', hb, hb, hs, hsm n _ _ _ (htor _ x) (htor _ y)]`. Set `φ : T' ≃ₗ[ℤ_[l]] ℤ_[l]` to `LinearEquiv.ofFinrankEq T' ℤ_[l] (by rw [hrk', finrank_self])`. Set `B : LinearMap.BilinForm ℤ_[l] T` to `LinearMap.mk₂ ℤ_[l] (fun x y => φ (b x y)) (fun x x' y => by rw [badd, map_add]) (fun r x y => by rw [bsm, map_smul]) (fun x y y' => by rw [bsk (y + y'), badd, bsk y x, bsk y' x, neg_add, map_add]) (fun r x y => by rw [bsk (r • y), bsm, bsk y x, ← smul_neg, map_smul])`. Establish `hBb : ∀ x y, B x y = φ (b x y)` using `fun _ _ => rfl`. Take `⟨S', hS'⟩` from `exists_lift l π h1 h0 hs hu S`.

Take `⟨Φ', hΦ'⟩` from `exists_lift l π h1 h0 hs hu Φ`. Establish `hit : ∀ (E : M ≃+ M) (E' : T ≃ₗ[ℤ_[l]] T), (∀ n x, π n (E' x) = E (π n x)) → ∀ n (j : ℕ) x, π n (E'^[j] x) = E^[j] (π n x)`. Introduce `E E' h n j`. Proceed by induction on `j with`. Consider the case `zero => intro t`.

Both sides reduce to the same expression. Consider the case `succ j ih => intro t`. Rewrite using `[Function.iterate_succ_apply, Function.iterate_succ_apply, ih, h]`. Establish `hcomm' : Φ' * S' = S' ^ q * Φ'`. Use extensionality with `x`.

Use `hext _ _ fun n => ?_` and prove the remaining obligations. Rewrite using `[LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.pow_apply, hit S S' hS', hΦ', hΦ', hS', hcomm n _ (htor n x)]`. Establish `hN` using `GlobalTheory.isNilpotent_sub_one_of_conj_pow l hl3 T S' Φ' q hq hcomm' fun x => by`. Establish `: π 1 (S' x - x) = 0`. Rewrite using `[map_sub, hS', hS1 _ (by simpa using htor 1 x), sub_self]`.

Simplify using `using (hker 1 _).1 this`. Set `W' : Submodule ℤ_[l] T` to `{ carrier := {x | ∀ n, π n x ∈ W} add_mem' := fun hx hy n => by rw [map_add]; exact W.add_mem (hx n) (hy n) zero_mem' := fun n => by rw [map_zero]; exact W.zero_mem smul_mem' := fun r x hx n => by rw [hs]; exact W.nsmul_mem (hx n) _ }`. Establish `hfixH : ∀ x, S' x = x → ∀ n, π n (c • x) ∈ H` using `fun x hx n => by`. Rewrite using `[map_nsmul]`. Conclude with `hH n _ (htor n x) (by rw [← hS', hx])`.

Establish `main` using `finrank_le_ker_add l B ?_ ?_ S' Φ' q hq hN ?_ ?_ hcomm' W' P hP ?_ c (by omega) ?_`. Establish `hW' : finrank ℤ_[l] W' ≤ t` using `finrank_le_of_card l π hker hfin W' W (fun n x hx => hx n) C t fun n => (hcard n).2`. Establish `hinj : Function.Injective (c • LinearMap.id : T →ₗ[ℤ_[l]] T)`. Introduce `x y h`. Establish `hc0 : (c : ℤ_[l]) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`.

Use `smul_right_injective T hc0 ?_` and prove the remaining obligations. Simplify `h` using `[Nat.cast_smul_eq_nsmul]`. Establish `hK` using `finrank_le_of_card l π hker hfin ((LinearMap.ker ((S' : T →ₗ[ℤ_[l]] T) - 1)).map (c • LinearMap.id : T →ₗ[ℤ_[l]] T)) H (by`. Introduce and unpack `n _ ⟨x, hx, rfl⟩`. Conclude with `hfixH x (by simpa [sub_eq_zero] using hx) n) C _ fun n => (hcard n).1`.

Rewrite `hK` using `[← (Submodule.equivMapOfInjective _ hinj _).finrank_eq]`. Use linear arithmetic over natural numbers and integers. Introduce `x hx`. Use `hext _ _ fun n => ?_` and prove the remaining obligations. Rewrite using `[map_zero]`.

Use `he3 n _ (htor n x) fun y hy => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩` from `hsurj n y hy`. Rewrite using `[← hb, (map_eq_zero_iff φ φ.injective).1 (hx y), map_zero]`. Introduce `x y`. Rewrite using `[hBb, hBb, bsk, map_neg]`.

Introduce `x y`. Rewrite using `[hBb, hBb]`. Use `congr 1`. Use `hext' _ _ fun n => ?_` and prove the remaining obligations. Rewrite using `[hb, hb, hS', hS', (hSΦ n _ _ (htor n x) (htor n y)).1]`.

Introduce `x y`. Rewrite using `[hBb, hBb, ← nsmul_eq_mul, ← map_nsmul]`. Use `congr 1`. Use `hext' _ _ fun n => ?_` and prove the remaining obligations. Rewrite using `[map_nsmul, hb, hb, hΦ', hΦ', (hSΦ n _ _ (htor n x) (htor n y)).2]`.

Introduce `x hx`. Use `hext _ _ fun n => ?_` and prove the remaining obligations. Rewrite using `[hΦ', map_nsmul, hW n _ (hx n) (htor n x)]`. Introduce `x hx n`. Rewrite using `[map_sum]`.

Simplify using `only [map_zsmul, hit Φ Φ' hΦ']`. Conclude with `hPW n _ (hfixH x hx n) (htor n _)`.
-/
theorem le_add_of_pairing (M A : Type) [AddCommGroup M] [AddCommGroup A] (l q g t a c C : ℕ)
    (hl : l.Prime) (hl3 : 3 ≤ l) (hq : 2 ≤ q) (hc : 1 ≤ c)
    (hA : ∀ n, Nat.card {x : A // l ^ n • x = 0} = l ^ n)
    (hM : ∀ n, Nat.card {x : M // l ^ n • x = 0} = l ^ (n * (2 * g)))
    (e : ℕ → M → M → A)
    (he1 : ∀ n x x' y, l ^ n • x = 0 → l ^ n • x' = 0 → l ^ n • y = 0 →
      e n (x + x') y = e n x y + e n x' y ∧ e n y x = - e n x y)
    (he2 : ∀ n x y, l ^ (n + 1) • x = 0 → l ^ n • y = 0 → e (n + 1) x y = e n (l • x) y)
    (he3 : ∀ n x, l ^ n • x = 0 → (∀ y, l ^ n • y = 0 → e n x y = 0) → x = 0)
    (S Φ : M ≃+ M)
    (hSΦ : ∀ n x y, l ^ n • x = 0 → l ^ n • y = 0 →
      e n (S x) (S y) = e n x y ∧ e n (Φ x) (Φ y) = q • e n x y)
    (hcomm : ∀ n x, l ^ n • x = 0 → Φ (S x) = S^[q] (Φ x))
    (hS1 : ∀ x, l • x = 0 → S x = x) (H W : AddSubgroup M) (P : Polynomial ℤ)
    (hH : ∀ n x, l ^ n • x = 0 → S x = x → c • x ∈ H)
    (hcard : ∀ n, Nat.card {x : H // l ^ n • x = 0} ≤ C * l ^ (n * (t + 2 * a)) ∧
      Nat.card {x : W // l ^ n • x = 0} ≤ C * l ^ (n * t))
    (hP : ∀ β : ℂ, Polynomial.aeval β P = 0 → ‖β‖ < q)
    (hW : ∀ n, ∀ x ∈ W, l ^ n • x = 0 → Φ x = q • x)
    (hPW : ∀ n, ∀ x ∈ H, l ^ n • x = 0 →
      ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j • (Φ^[j] x) ∈ W) : g ≤ t + a := by
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨T, _, _, π, _, _, hrk, h1, h0, hs, hsurj, hker, hu⟩ :=
    GlobalTheory.exists_tateModule_of_card M l (2 * g) fun n => by rw [hM, mul_comm]
  obtain ⟨T', _, _, π', _, _, hrk', h1', h0', hs', -, -, hu'⟩ :=
    GlobalTheory.exists_tateModule_of_card A l 1 fun n => by rw [hA, one_mul]
  have hext : ∀ x y : T, (∀ n, π n x = π n y) → x = y := fun x y h =>
    (hu (fun n => π n y) (h0 y) (fun n => h1 n y)).unique h fun _ => rfl
  have hext' : ∀ x y : T', (∀ n, π' n x = π' n y) → x = y := fun x y h =>
    (hu' (fun n => π' n y) (h0' y) (fun n => h1' n y)).unique h fun _ => rfl
  have htor : ∀ n x, l ^ n • π n x = 0 := fun n x => by
    rw [← map_nsmul, hker]; exact ⟨x, rfl⟩
  have hfin : ∀ n, Finite {x : M // l ^ n • x = 0} := fun n =>
    Nat.finite_of_card_ne_zero (by rw [hM]; exact pow_ne_zero _ hl.ne_zero)
  have hsm : ∀ n (k : ℕ) x y, l ^ n • x = 0 → l ^ n • y = 0 →
      e n (k • x) y = k • e n x y := by
    intro n k x y hx hy
    induction k with
    | zero =>
      have := (he1 n 0 0 y (by simp) (by simp) hy).1
      simpa using this
    | succ k ih =>
      rw [succ_nsmul, succ_nsmul, (he1 n _ x y (by rw [smul_comm, hx, smul_zero]) hx hy).1, ih]
  have hsk : ∀ n x y, l ^ n • x = 0 → l ^ n • y = 0 → e n y x = - e n x y :=
    fun n x y hx hy => (he1 n x x y hx hx hy).2
  choose b hb using fun x y : T => (hu' (fun n => e n (π n x) (π n y))
    (by
      have := hsm 0 0 (π 0 x) (π 0 y) (htor _ _) (htor _ _)
      rw [zero_smul, zero_smul] at this
      rw [← this, h0 x])
    (fun n => by
      have hy : l ^ (n + 1) • π n y = 0 := by rw [pow_succ', mul_smul, htor, smul_zero]
      rw [hsk (n + 1) _ _ (htor _ y) (htor _ x), smul_neg, ← hsm _ _ _ _ (htor _ y) (htor _ x),
        h1, ← hsk (n + 1) _ _ hy (htor _ x), he2 _ _ _ (htor _ x) (htor _ y), h1])).exists
  have bsk : ∀ x y, b y x = - b x y := fun x y => hext' _ _ fun n => by
    rw [map_neg, hb, hb, hsk n _ _ (htor _ x) (htor _ y)]
  have badd : ∀ x x' y, b (x + x') y = b x y + b x' y := fun x x' y => hext' _ _ fun n => by
    rw [map_add, hb, hb, hb, map_add, (he1 n _ _ _ (htor _ x) (htor _ x') (htor _ y)).1]
  have bsm : ∀ (r : ℤ_[l]) x y, b (r • x) y = r • b x y := fun r x y => hext' _ _ fun n => by
    rw [hs', hb, hb, hs, hsm n _ _ _ (htor _ x) (htor _ y)]
  let φ : T' ≃ₗ[ℤ_[l]] ℤ_[l] := LinearEquiv.ofFinrankEq T' ℤ_[l] (by rw [hrk', finrank_self])
  let B : LinearMap.BilinForm ℤ_[l] T := LinearMap.mk₂ ℤ_[l] (fun x y => φ (b x y))
    (fun x x' y => by rw [badd, map_add]) (fun r x y => by rw [bsm, map_smul])
    (fun x y y' => by rw [bsk (y + y'), badd, bsk y x, bsk y' x, neg_add, map_add])
    (fun r x y => by rw [bsk (r • y), bsm, bsk y x, ← smul_neg, map_smul])
  have hBb : ∀ x y, B x y = φ (b x y) := fun _ _ => rfl
  obtain ⟨S', hS'⟩ := exists_lift l π h1 h0 hs hu S
  obtain ⟨Φ', hΦ'⟩ := exists_lift l π h1 h0 hs hu Φ
  have hit : ∀ (E : M ≃+ M) (E' : T ≃ₗ[ℤ_[l]] T), (∀ n x, π n (E' x) = E (π n x)) →
      ∀ n (j : ℕ) x, π n (E'^[j] x) = E^[j] (π n x) := by
    intro E E' h n j
    induction j with
    | zero => intro t; rfl
    | succ j ih => intro t; rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, h]
  have hcomm' : Φ' * S' = S' ^ q * Φ' := by
    ext x
    refine hext _ _ fun n => ?_
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.pow_apply, hit S S' hS', hΦ',
      hΦ', hS', hcomm n _ (htor n x)]
  have hN := GlobalTheory.isNilpotent_sub_one_of_conj_pow l hl3 T S' Φ' q hq hcomm' fun x => by
    have : π 1 (S' x - x) = 0 := by
      rw [map_sub, hS', hS1 _ (by simpa using htor 1 x), sub_self]
    simpa using (hker 1 _).1 this
  let W' : Submodule ℤ_[l] T :=
    { carrier := {x | ∀ n, π n x ∈ W}
      add_mem' := fun hx hy n => by rw [map_add]; exact W.add_mem (hx n) (hy n)
      zero_mem' := fun n => by rw [map_zero]; exact W.zero_mem
      smul_mem' := fun r x hx n => by rw [hs]; exact W.nsmul_mem (hx n) _ }
  have hfixH : ∀ x, S' x = x → ∀ n, π n (c • x) ∈ H := fun x hx n => by
    rw [map_nsmul]
    exact hH n _ (htor n x) (by rw [← hS', hx])
  have main := finrank_le_ker_add l B ?_ ?_ S' Φ' q hq hN ?_ ?_ hcomm' W' P hP ?_ c (by omega) ?_
  · have hW' : finrank ℤ_[l] W' ≤ t :=
      finrank_le_of_card l π hker hfin W' W (fun n x hx => hx n) C t fun n => (hcard n).2
    have hinj : Function.Injective (c • LinearMap.id : T →ₗ[ℤ_[l]] T) := by
      intro x y h
      have hc0 : (c : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      refine smul_right_injective T hc0 ?_
      simpa [Nat.cast_smul_eq_nsmul] using h
    have hK := finrank_le_of_card l π hker hfin
      ((LinearMap.ker ((S' : T →ₗ[ℤ_[l]] T) - 1)).map (c • LinearMap.id : T →ₗ[ℤ_[l]] T)) H
      (by
        rintro n _ ⟨x, hx, rfl⟩
        exact hfixH x (by simpa [sub_eq_zero] using hx) n) C _ fun n => (hcard n).1
    rw [← (Submodule.equivMapOfInjective _ hinj _).finrank_eq] at hK
    omega
  · intro x hx
    refine hext _ _ fun n => ?_
    rw [map_zero]
    refine he3 n _ (htor n x) fun y hy => ?_
    obtain ⟨y, rfl⟩ := hsurj n y hy
    rw [← hb, (map_eq_zero_iff φ φ.injective).1 (hx y), map_zero]
  · intro x y
    rw [hBb, hBb, bsk, map_neg]
  · intro x y
    rw [hBb, hBb]
    congr 1
    refine hext' _ _ fun n => ?_
    rw [hb, hb, hS', hS', (hSΦ n _ _ (htor n x) (htor n y)).1]
  · intro x y
    rw [hBb, hBb, ← nsmul_eq_mul, ← map_nsmul]
    congr 1
    refine hext' _ _ fun n => ?_
    rw [map_nsmul, hb, hb, hΦ', hΦ', (hSΦ n _ _ (htor n x) (htor n y)).2]
  · intro x hx
    refine hext _ _ fun n => ?_
    rw [hΦ', map_nsmul, hW n _ (hx n) (htor n x)]
  · intro x hx n
    rw [map_sum]
    simp only [map_zsmul, hit Φ Φ' hΦ']
    exact hPW n _ (hfixH x hx n) (htor n _)

/- English proof (translation)
Use `haveI : NeZero ((l ^ n : ℕ) : K) := ⟨by rw [Nat.cast_pow]; exact pow_ne_zero _ hl⟩`. Use `haveI : NeZero (l ^ n) := NeZero.of_neZero_natCast K`. Conclude with `HasEnoughRootsOfUnity.natCard_rootsOfUnity K (l ^ n)`.
-/
theorem card_torsion_units (K : Type) [Field K] [IsAlgClosed K] (l : ℕ) (hl : (l : K) ≠ 0)
    (n : ℕ) : Nat.card {x : Additive Kˣ // l ^ n • x = 0} = l ^ n := by
  haveI : NeZero ((l ^ n : ℕ) : K) := ⟨by rw [Nat.cast_pow]; exact pow_ne_zero _ hl⟩
  haveI : NeZero (l ^ n) := NeZero.of_neZero_natCast K
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity K (l ^ n)

end GlobalTheory.SS.Weight

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

/- English proof (translation)
Introduce `M _ Ω _ l q g t a c C hl hl3 hlΩ hq hc hM e he S Φ hSΦ hcomm hS1 H W P hH hcard hP hW hPW`. Take `⟨he1, he2, he3⟩` from `he`. Set `K` to `AlgebraicClosure Ω`. Set `u : Ωˣ →* Kˣ` to `Units.map (algebraMap Ω K : Ω →* K)`. Establish `hu : Function.Injective u` using `Units.map_injective (algebraMap Ω K).injective`.

Establish `hlK : (l : K) ≠ 0`. Rewrite using `[← map_natCast (algebraMap Ω K)]`. Conclude with `(map_ne_zero_iff _ (algebraMap Ω K).injective).2 hlΩ`. Use `GlobalTheory.SS.Weight.le_add_of_pairing (Additive M) (Additive Kˣ) l q g t a c C hl hl3 hq hc (GlobalTheory.SS.Weight.card_torsion_units K l hlK) hM (fun n x y => Additive.ofMul (u (e n x.toMul y.toMul))) ?_ ?_ ?_ (MulEquiv.toAdditive S) (MulEquiv.toAdditive Φ) ?_ hcomm hS1 (Sub …` and prove the remaining obligations. Introduce `n x x' y hx hx' hy`.

Take `⟨h1, h2⟩` from `he1 n x.toMul x'.toMul y.toMul hx hx' hy`. Conclude with `⟨by rw [toMul_add, h1, map_mul, ofMul_mul], by rw [h2, map_inv, ofMul_inv]⟩`. Introduce `n x y hx hy`. Rewrite using `[he2 n x.toMul y.toMul hx hy, toMul_nsmul]`. Introduce `n x hx h`.

Conclude with `he3 n x.toMul hx fun y hy => hu ((h (Additive.ofMul y) hy).trans (map_one u).symm)`. Introduce `n x y hx hy`. Take `⟨h1, h2⟩` from `hSΦ n x.toMul y.toMul hx hy`. Conclude with `⟨congrArg (fun z => Additive.ofMul (u z)) h1, (congrArg (fun z => Additive.ofMul (u z)) h2).trans (by rw [map_pow, ofMul_pow])⟩`. Introduce `n x hx hx'`.

Conclude with `hPW n x.toMul hx hx'`.
-/
theorem GlobalTheory.SS.Weight.le_add_of_torsion : ∀ (M : Type) [CommGroup M] (Ω : Type) [Field Ω] (l q g t a c C : ℕ), l.Prime → 3 ≤ l → (l : Ω) ≠ 0 → 2 ≤ q → 1 ≤ c → (∀ n, Nat.card {x : M // x ^ l ^ n = 1} = l ^ (n * (2 * g))) → ∀ e : ℕ → M → M → Ωˣ, ((∀ n x x' y, x ^ l ^ n = 1 → x' ^ l ^ n = 1 → y ^ l ^ n = 1 → e n (x * x') y = e n x y * e n x' y ∧ e n y x = (e n x y)⁻¹) ∧ (∀ n x y, x ^ l ^ (n + 1) = 1 → y ^ l ^ n = 1 → e (n + 1) x y = e n (x ^ l) y) ∧ (∀ n x, x ^ l ^ n = 1 → (∀ y, y ^ l ^ n = 1 → e n x y = 1) → x = 1)) → ∀ S Φ : M ≃* M, (∀ n x y, x ^ l ^ n = 1 → y ^ l ^ n = 1 → e n (S x) (S y) = e n x y ∧ e n (Φ x) (Φ y) = e n x y ^ q) → (∀ n x, x ^ l ^ n = 1 → Φ (S x) = S^[q] (Φ x)) → (∀ x, x ^ l = 1 → S x = x) → ∀ (H W : Subgroup M) (P : Polynomial ℤ), (∀ n x, x ^ l ^ n = 1 → S x = x → x ^ c ∈ H) → (∀ n, Nat.card {x : H // x ^ l ^ n = 1} ≤ C * l ^ (n * (t + 2 * a)) ∧ Nat.card {x : W // x ^ l ^ n = 1} ≤ C * l ^ (n * t)) → (∀ β : ℂ, Polynomial.aeval β P = 0 → ‖β‖ < q) → (∀ n, ∀ x ∈ W, x ^ l ^ n = 1 → Φ x = x ^ q) → (∀ n, ∀ x ∈ H, x ^ l ^ n = 1 → ∏ j ∈ Finset.range (P.natDegree + 1), (Φ^[j] x) ^ P.coeff j ∈ W) → g ≤ t + a := by
  intro M _ Ω _ l q g t a c C hl hl3 hlΩ hq hc hM e he S Φ hSΦ hcomm hS1 H W P hH hcard hP hW hPW
  obtain ⟨he1, he2, he3⟩ := he
  let K := AlgebraicClosure Ω
  let u : Ωˣ →* Kˣ := Units.map (algebraMap Ω K : Ω →* K)
  have hu : Function.Injective u := Units.map_injective (algebraMap Ω K).injective
  have hlK : (l : K) ≠ 0 := by
    rw [← map_natCast (algebraMap Ω K)]
    exact (map_ne_zero_iff _ (algebraMap Ω K).injective).2 hlΩ
  refine GlobalTheory.SS.Weight.le_add_of_pairing (Additive M) (Additive Kˣ) l q g t a c C hl hl3 hq hc
    (GlobalTheory.SS.Weight.card_torsion_units K l hlK) hM
    (fun n x y => Additive.ofMul (u (e n x.toMul y.toMul))) ?_ ?_ ?_
    (MulEquiv.toAdditive S) (MulEquiv.toAdditive Φ) ?_ hcomm hS1 (Subgroup.toAddSubgroup H)
    (Subgroup.toAddSubgroup W) P hH hcard hP hW ?_
  · intro n x x' y hx hx' hy
    obtain ⟨h1, h2⟩ := he1 n x.toMul x'.toMul y.toMul hx hx' hy
    exact ⟨by rw [toMul_add, h1, map_mul, ofMul_mul], by rw [h2, map_inv, ofMul_inv]⟩
  · intro n x y hx hy
    rw [he2 n x.toMul y.toMul hx hy, toMul_nsmul]
  · intro n x hx h
    exact he3 n x.toMul hx fun y hy => hu ((h (Additive.ofMul y) hy).trans (map_one u).symm)
  · intro n x y hx hy
    obtain ⟨h1, h2⟩ := hSΦ n x.toMul y.toMul hx hy
    exact ⟨congrArg (fun z => Additive.ofMul (u z)) h1,
      (congrArg (fun z => Additive.ofMul (u z)) h2).trans (by rw [map_pow, ofMul_pow])⟩
  · intro n x hx hx'
    exact hPW n x.toMul hx hx'
