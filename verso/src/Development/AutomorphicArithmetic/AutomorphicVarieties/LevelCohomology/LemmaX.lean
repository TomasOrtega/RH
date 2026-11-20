import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.UnramifiedCocycleIsCoboundaryOfBernoulliUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Counts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsPrimitiveRootPow
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.LxCore
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.LxPartial
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.ExistsResidueMapPadicAlgClIntegers
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.PrimitiveTwoPowCharacterOneAddHalfEqNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BOneSum

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.ML UpperTheory.V.X

/- English proof (translation)
Simplify using `only [prodX, MulChar.coeToFun_mul, Pi.mul_apply]`. Distinguish the cases in `h : IsCoprime a ((f * 2 ^ n : ℕ) : ℤ)`. Rewrite using `[DirichletCharacter.changeLevel_eq_cast_of_dvd' φ _ h, DirichletCharacter.changeLevel_eq_cast_of_dvd' ξ _ h]`. Establish `hnu : ¬IsUnit (a : ZMod (f * 2 ^ n))` using `fun hu => h (isCoprime_comm.1 ((ZMod.coe_int_isUnit_iff_isCoprime _ _).1 hu))`. Rewrite using `[MulChar.map_nonunit _ hnu, zero_mul]`.

Establish `hc : ¬IsCoprime a (f : ℤ) ∨ ¬IsCoprime a ((2 ^ n : ℕ) : ℤ)`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Apply `h` to reduce the goal to its premises. Move the coercions through the operations in `at hc ⊢`.

Conclude with `hc.1.mul_right hc.2`. Break down `hc with hc | hc` into its components or cases. Rewrite using `[MulChar.map_nonunit φ (fun hu => hc (isCoprime_comm.1 ((ZMod.coe_int_isUnit_iff_isCoprime _ _).1 hu))), zero_mul]`. Rewrite using `[MulChar.map_nonunit ξ (fun hu => hc (isCoprime_comm.1 ((ZMod.coe_int_isUnit_iff_isCoprime _ _).1 hu))), mul_zero]`.
-/
private theorem UpperTheory.V.X.prodX_nat {R : Type} [CommRing R] {f n : ℕ} (φ : DirichletCharacter R f) (ξ : DirichletCharacter R (2 ^ n))
    (a : ℤ) : prodX φ ξ (a : ZMod (f * 2 ^ n)) = φ (a : ZMod f) * ξ (a : ZMod (2 ^ n)) := by
  simp only [prodX, MulChar.coeToFun_mul, Pi.mul_apply]
  by_cases h : IsCoprime a ((f * 2 ^ n : ℕ) : ℤ)
  · rw [DirichletCharacter.changeLevel_eq_cast_of_dvd' φ _ h, DirichletCharacter.changeLevel_eq_cast_of_dvd' ξ _ h]
  · have hnu : ¬IsUnit (a : ZMod (f * 2 ^ n)) := fun hu =>
      h (isCoprime_comm.1 ((ZMod.coe_int_isUnit_iff_isCoprime _ _).1 hu))
    rw [MulChar.map_nonunit _ hnu, zero_mul]
    have hc : ¬IsCoprime a (f : ℤ) ∨ ¬IsCoprime a ((2 ^ n : ℕ) : ℤ) := by
      by_contra hc
      push_neg at hc
      apply h
      push_cast at hc ⊢
      exact hc.1.mul_right hc.2
    rcases hc with hc | hc
    · rw [MulChar.map_nonunit φ (fun hu => hc (isCoprime_comm.1 ((ZMod.coe_int_isUnit_iff_isCoprime _ _).1 hu))), zero_mul]
    · rw [MulChar.map_nonunit ξ (fun hu => hc (isCoprime_comm.1 ((ZMod.coe_int_isUnit_iff_isCoprime _ _).1 hu))), mul_zero]

/- English proof (translation)
Establish `hneg : prodX φ ξ (-1 : ZMod (f * 2 ^ n)) = -1`. Establish `h` using `UpperTheory.V.X.prodX_nat φ ξ (-1)`. Simplify using `only [Int.cast_neg, Int.cast_one] at h`. Rewrite using `[h, hodd]`. Establish `hN1 : f * 2 ^ n ≠ 1`.

Introduce `h1`. Use `haveI : Subsingleton (ZMod (f * 2 ^ n)) := by`. Rewrite using `[h1]`. Use `infer_instance`. Establish `e : (-1 : ZMod (f * 2 ^ n)) = 1` using `Subsingleton.elim _ _`.

Rewrite `hneg` using `[e, MulChar.map_one]`. Evaluate the numerical expressions using `at hneg`. Use `haveI : NeZero (f * 2 ^ n) := ⟨(Nat.mul_pos hf (by positivity)).ne'⟩`. Use `haveI : Nontrivial (ZMod (f * 2 ^ n)) := ZMod.nontrivial_iff.2 hN1`. Establish `hsum : ∑ a, (prodX φ ξ) a = 0`.

Use `MulChar.sum_eq_zero_of_ne_one (fun h1 => ?_)` and prove the remaining obligations. Rewrite `hneg` using `[h1, MulChar.one_apply isUnit_one.neg]`. Evaluate the numerical expressions using `at hneg`. Rewrite using `[Bern.b_one _ hsum]`. Establish `gen : ∀ (g : ℕ → K) (M : ℕ), g 0 = 0 → g (M + 1) = 0 → ∑ a ∈ Finset.Icc 1 (M + 1), g a = ∑ a ∈ Finset.range (M + 1), g a`.

Introduce `g M h0 hM`. Establish `key : ∀ M' : ℕ, ∑ a ∈ Finset.Icc 1 M', g a = ∑ k ∈ Finset.range M', g (k + 1)`. Introduce `M'`. Proceed by induction on `M' with`. Consider the case `zero => simp`.

Consider the case `succ M' ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]`. Rewrite using `[Finset.sum_range_succ', h0, add_zero, key, Finset.sum_range_succ, hM, add_zero]`. Take `⟨M, hM⟩ : ∃ M, f * 2 ^ n = M + 1` from `⟨f * 2 ^ n - 1, by have := NeZero.ne (f * 2 ^ n); omega⟩`. Establish `hterm : ∀ a : ℕ, prodX φ ξ (a : ZMod (f * 2 ^ n)) * (a : K) = φ (a : ZMod f) * ξ (a : ZMod (2 ^ n)) * a`. Introduce `a`.

Establish `h` using `UpperTheory.V.X.prodX_nat φ ξ (a : ℤ)`. Simplify using `only [Int.cast_natCast] at h`. Rewrite using `[h]`. Establish `htop : prodX φ ξ ((M + 1 : ℕ) : ZMod (f * 2 ^ n)) * ((M + 1 : ℕ) : K) = 0`. Rewrite using `[← hM, ZMod.natCast_self, MulChar.map_zero, zero_mul]`.

Establish `hg` using `gen (fun a => prodX φ ξ (a : ZMod (f * 2 ^ n)) * (a : K)) M (by simp) htop`. Rewrite using `[Finset.sum_congr rfl (fun a _ => (hterm a).symm)]`. Rewrite using `[show Finset.Icc 1 (f * 2 ^ n) = Finset.Icc 1 (M + 1) by rw [hM], show Finset.range (f * 2 ^ n) = Finset.range (M + 1) by rw [hM]]`. Conclude with `hg`.
-/
private theorem UpperTheory.V.X.genB_prodX {K : Type} [Field K] [CharZero K] {f n : ℕ} (hf : 0 < f) (φ : DirichletCharacter K f)
    (ξ : DirichletCharacter K (2 ^ n)) (hodd : φ (-1) * ξ (-1) = -1) :
    ((f * 2 ^ n : ℕ) : K) * Bern.genB 1 (prodX φ ξ : ZMod (f * 2 ^ n) → K) =
      ∑ a ∈ Finset.range (f * 2 ^ n), φ (a : ZMod f) * ξ (a : ZMod (2 ^ n)) * a := by
  have hneg : prodX φ ξ (-1 : ZMod (f * 2 ^ n)) = -1 := by
    have h := UpperTheory.V.X.prodX_nat φ ξ (-1)
    simp only [Int.cast_neg, Int.cast_one] at h
    rw [h, hodd]
  have hN1 : f * 2 ^ n ≠ 1 := by
    intro h1
    haveI : Subsingleton (ZMod (f * 2 ^ n)) := by
      rw [h1]
      infer_instance
    have e : (-1 : ZMod (f * 2 ^ n)) = 1 := Subsingleton.elim _ _
    rw [e, MulChar.map_one] at hneg
    norm_num at hneg
  haveI : NeZero (f * 2 ^ n) := ⟨(Nat.mul_pos hf (by positivity)).ne'⟩
  haveI : Nontrivial (ZMod (f * 2 ^ n)) := ZMod.nontrivial_iff.2 hN1
  have hsum : ∑ a, (prodX φ ξ) a = 0 := by
    refine MulChar.sum_eq_zero_of_ne_one (fun h1 => ?_)
    rw [h1, MulChar.one_apply isUnit_one.neg] at hneg
    norm_num at hneg
  rw [Bern.b_one _ hsum]
  have gen : ∀ (g : ℕ → K) (M : ℕ), g 0 = 0 → g (M + 1) = 0 →
      ∑ a ∈ Finset.Icc 1 (M + 1), g a = ∑ a ∈ Finset.range (M + 1), g a := by
    intro g M h0 hM
    have key : ∀ M' : ℕ, ∑ a ∈ Finset.Icc 1 M', g a = ∑ k ∈ Finset.range M', g (k + 1) := by
      intro M'
      induction M' with
      | zero => simp
      | succ M' ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
    rw [Finset.sum_range_succ', h0, add_zero, key, Finset.sum_range_succ, hM, add_zero]
  obtain ⟨M, hM⟩ : ∃ M, f * 2 ^ n = M + 1 := ⟨f * 2 ^ n - 1, by have := NeZero.ne (f * 2 ^ n); omega⟩
  have hterm : ∀ a : ℕ, prodX φ ξ (a : ZMod (f * 2 ^ n)) * (a : K) = φ (a : ZMod f) * ξ (a : ZMod (2 ^ n)) * a := by
    intro a
    have h := UpperTheory.V.X.prodX_nat φ ξ (a : ℤ)
    simp only [Int.cast_natCast] at h
    rw [h]
  have htop : prodX φ ξ ((M + 1 : ℕ) : ZMod (f * 2 ^ n)) * ((M + 1 : ℕ) : K) = 0 := by
    rw [← hM, ZMod.natCast_self, MulChar.map_zero, zero_mul]
  have hg := gen (fun a => prodX φ ξ (a : ZMod (f * 2 ^ n)) * (a : K)) M (by simp) htop
  rw [Finset.sum_congr rfl (fun a _ => (hterm a).symm)]
  rw [show Finset.Icc 1 (f * 2 ^ n) = Finset.Icc 1 (M + 1) by rw [hM],
    show Finset.range (f * 2 ^ n) = Finset.range (M + 1) by rw [hM]]
  exact hg

/- English proof (translation)
Introduce `l _ d f n φ ξ hX`. Take `⟨k, _, _, A, red, hA, hred⟩` from `UpperTheory.exists_residue_map_padicAlgCl_integers l`. Establish `hlp : l.Prime` using `Fact.out`. Use `haveI : ExpChar k l := ExpChar.prime hlp`. Establish `hq1 : 1 < l ^ d` using `Nat.one_lt_pow hX.d_pos.ne' hlp.one_lt`.

Establish `hl2 : l ≠ 2`. Introduce `h`. Substitute `h` using the available equality. Establish `h4` using `hX.four`. Establish `h2a : 2 ∣ 2 ^ d - 1` using `dvd_trans (by norm_num) h4`.

Establish `h2d : 2 ∣ 2 ^ d` using `dvd_pow_self 2 hX.d_pos.ne'`. Use linear arithmetic over natural numbers and integers. Take `⟨e, he⟩ : ∃ e, e = (l ^ d - 1).factorization 2` from `⟨_, rfl⟩`. Establish `hne : l ^ d - 1 ≠ 0` using `by omega`. Establish `he2 : 2 ≤ e`.

Rewrite using `[he]`. Conclude with `(Nat.prime_two.pow_dvd_iff_le_factorization hne).1 (by rw [show (2:ℕ) ^ 2 = 4 by norm_num]; exact hX.four)`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha, hao⟩ : ∃ a, l ^ d - 1 = 2 ^ e * a ∧ Odd a := by`. Use `⟨(l ^ d - 1) / 2 ^ e, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[he]`.

Conclude with `(Nat.ordProj_mul_ordCompl_eq_self _ 2).symm`. Rewrite using `[he]`. Conclude with `Nat.coprime_two_left.1 (Nat.coprime_ordCompl Nat.prime_two hne)`. Establish `hbig : f * 4 ^ e ≤ 2 ^ n` using `by rw [he]; exact hX.big`. Establish `hf1 : 1 ≤ f` using `hX.f_odd.pos`.

Establish `h4e : (4 : ℕ) ^ e = 2 ^ e * 2 ^ e`. Rewrite using `[← mul_pow]`. Evaluate the numerical expressions. Establish `hen : e + e ≤ n`. Establish `h' : 2 ^ (e + e) ≤ 2 ^ n`.

Rewrite using `[pow_add, ← h4e]`. Conclude with `le_trans (Nat.le_mul_of_pos_left _ hf1) hbig`. Conclude with `(Nat.pow_le_pow_iff_right (by norm_num)).1 h'`. Take `⟨m, rfl⟩ : ∃ m, n = m + e` from `⟨n - e, by omega⟩`. Establish `hs : f * 2 ^ e ≤ 2 ^ m`.

Establish `h' : f * 2 ^ e * 2 ^ e ≤ 2 ^ m * 2 ^ e`. Rewrite using `[← pow_add, mul_assoc, ← h4e]`. Conclude with `hbig`. Conclude with `Nat.le_of_mul_le_mul_right h' (by positivity)`. Establish `h4le : 4 ≤ 2 ^ e`.

Combine the equalities or inequalities in the displayed calculation. Establish `hs1 : 1 < f * 2 ^ e`. Combine the equalities or inequalities in the displayed calculation. Establish `hft : f * 2 ^ e ≤ 2 ^ (m + e)` using `le_trans hs (Nat.pow_le_pow_right (by norm_num) (by omega))`. Establish `normA : ∀ x : PadicAlgCl l, ‖x‖ ≤ 1 → x ∈ A` using `fun x hx => (hA x).2 hx`.

Establish `pow_one_norm : ∀ (x : PadicAlgCl l) (j : ℕ), 0 < j → x ^ j = 1 → ‖x‖ = 1`. Introduce `x j hj hx`. Establish `h' : ‖x‖ ^ j = 1` using `by rw [← norm_pow, hx, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg x) hj.ne').1 h'`. Establish `hξn : ∀ u, ‖ξ u‖ ≤ 1`.

Introduce `u`. Distinguish the cases in `hu : IsUnit u`. Establish `h' : ξ u ^ Nat.totient (2 ^ (m + e)) = 1`. Take `⟨v, rfl⟩` from `hu`. Rewrite using `[← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one, map_one]`.

Conclude with `(pow_one_norm _ _ (Nat.totient_pos.2 (by positivity)) h').le`. Rewrite using `[MulChar.map_nonunit _ hu, norm_zero]`. Conclude with `zero_le_one`. Establish `hφq : ∀ u : ZMod f, φ u ^ (l ^ d) = φ u`. Introduce `u`.

Distinguish the cases in `hu : IsUnit u`. Establish `h1' : φ ^ (l ^ d - 1) = 1` using `orderOf_dvd_iff_pow_eq_one.1 hX.ord`. Establish `h' : φ u ^ (l ^ d - 1) = 1`. Rewrite using `[← MulChar.pow_apply' φ hne u, h1', MulChar.one_apply hu]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[MulChar.map_nonunit _ hu, zero_pow (by positivity)]`. Set `B : Subring (PadicAlgCl l)` to `(RingHom.eqLocus ((iterateFrobenius k l d).comp red) red).map A.subtype`. Establish `memB : ∀ (x : PadicAlgCl l) (hx : x ∈ A), red ⟨x, hx⟩ ^ (l ^ d) = red ⟨x, hx⟩ → x ∈ B`. Introduce `x hx h`. Use `⟨⟨x, hx⟩, ?_, rfl⟩` and prove the remaining obligations.

Use `show (iterateFrobenius k l d) (red ⟨x, hx⟩) = red ⟨x, hx⟩`. Rewrite using `[iterateFrobenius_def]` and apply the resulting hypothesis. Establish `ofB : ∀ x ∈ B, ∃ hx : x ∈ A, red ⟨x, hx⟩ ^ (l ^ d) = red ⟨x, hx⟩`. Introduce and unpack `x ⟨y, hy, rfl⟩`. Use `⟨y.2, ?_⟩` and prove the remaining obligations.

Establish `h' : (iterateFrobenius k l d) (red y) = red y` using `hy`. Rewrite `h'` using `[iterateFrobenius_def]`. Then use the resulting hypothesis. Establish `fixB : ∀ x : PadicAlgCl l, x ^ (l ^ d) = x → x ∈ B`. Introduce `x hx`. Establish `hn : ‖x‖ ≤ 1`.

Distinguish the cases in `h0 : x = 0`. Simplify using `[h0]`. Establish `h' : x ^ (l ^ d - 1) = 1`. Establish `h'' : x ^ (l ^ d - 1) * x = 1 * x`. Rewrite using `[← pow_succ, Nat.sub_add_cancel hq1.le, one_mul, hx]`.

Conclude with `mul_right_cancel₀ h0 h''`. Conclude with `(pow_one_norm x _ (by omega) h').le`. Use `memB x (normA x hn) ?_` and prove the remaining obligations. Rewrite using `[← map_pow]`. Use `congr 1`.

Conclude with `Subtype.ext (by simp [hx])`. Establish `h2k : ((2 : ℕ) : k) ≠ 0`. Introduce `h`. Establish `h'` using `(CharP.cast_eq_zero_iff k l 2).1 h`. Conclude with `hl2 ((Nat.prime_dvd_prime_iff_eq hlp Nat.prime_two).1 h')`.

Establish `h2A : ((2 : ℕ) : PadicAlgCl l) ∈ A` using `natCast_mem A 2`. Establish `hnorm2 : ‖((2 : ℕ) : PadicAlgCl l)‖ = 1`. Apply `le_antisymm ((hA _).1 h2A)` to reduce the goal to its premises. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`.

Apply `h2k` to reduce the goal to its premises. Establish `h'` using `(hred ⟨_, h2A⟩).2 hlt`. Establish `e2 : (⟨((2 : ℕ) : PadicAlgCl l), h2A⟩ : A) = ((2 : ℕ) : A)` using `Subtype.ext (map_natCast A.subtype 2).symm`. Rewrite `h'` using `[e2, map_natCast]`. Conclude with `h'`.

Establish `hinvN : ((2 ^ (m + e) : ℕ) : PadicAlgCl l)⁻¹ ∈ B`. Establish `hyn : ‖((2 ^ (m + e) : ℕ) : PadicAlgCl l)⁻¹‖ = 1`. Rewrite using `[norm_inv, Nat.cast_pow, norm_pow, hnorm2, one_pow, inv_one]`. Establish `hyA` using `normA _ hyn.le`. Use `memB _ hyA ?_` and prove the remaining obligations.

Establish `h2nA : ((2 ^ (m + e) : ℕ) : PadicAlgCl l) ∈ A` using `natCast_mem A _`. Establish `hN0 : ((2 ^ (m + e) : ℕ) : PadicAlgCl l) ≠ 0` using `Nat.cast_ne_zero.2 (by positivity)`. Establish `hprod : red ⟨_, hyA⟩ * red ⟨_, h2nA⟩ = 1`. Rewrite using `[← map_mul, ← map_one red]`. Use `congr 1`.

Conclude with `Subtype.ext (by simp [hN0])`. Establish `e2 : (⟨((2 ^ (m + e) : ℕ) : PadicAlgCl l), h2nA⟩ : A) = ((2 ^ (m + e) : ℕ) : A)` using `Subtype.ext (map_natCast A.subtype _).symm`. Rewrite `hprod` using `[e2, map_natCast]`. Establish `hfrob : ((2 ^ (m + e) : ℕ) : k) ^ (l ^ d) = ((2 ^ (m + e) : ℕ) : k)`. Rewrite using `[← iterateFrobenius_def, map_natCast]`.

Establish `hne0 : ((2 ^ (m + e) : ℕ) : k) ≠ 0`. Introduce `h0`. Rewrite `hprod` using `[h0, mul_zero]`. Conclude with `zero_ne_one hprod`. Establish `h' : red ⟨_, hyA⟩ ^ (l ^ d) * ((2 ^ (m + e) : ℕ) : k) = red ⟨_, hyA⟩ * ((2 ^ (m + e) : ℕ) : k)`.

Rewrite using `[hprod, ← hfrob, ← mul_pow, hprod, one_pow]`. Conclude with `mul_right_cancel₀ hne0 h'`. Establish `hφB : ∀ a : ℕ, φ (a : ZMod f) ∈ B` using `fun a => fixB _ (hφq _)`. Use `haveI : NeZero (2 ^ (m + e)) := ⟨by positivity⟩`. Establish `hcop : f.Coprime (2 ^ (m + e))` using `Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hX.f_odd)`.

Take `⟨g, c, hgB, hcB, hshift, hsumid⟩` from `lx_partial (K := PadicAlgCl l) f (2 ^ (m + e)) hX.f_odd.pos hcop (fun a => φ (a : ZMod f)) (fun a => by simp [Nat.cast_add, ZMod.natCast_self]) B hφB hinvN`. Establish `hxi1` using `UpperTheory.primitive_two_pow_character_one_add_half_eq_neg_one (PadicAlgCl l) (m + e) (by omega) ξ hX.prim2`. Establish `hξsum : ∑ u, ξ u = 0`. Use `MulChar.sum_eq_zero_of_ne_one (fun h1 => ?_)` and prove the remaining obligations. Rewrite `hxi1` using `[h1]`.

Distinguish the cases in `hu : IsUnit (1 + 2 ^ (m + e - 1) : ZMod (2 ^ (m + e)))`. Rewrite `hxi1` using `[MulChar.one_apply hu]`. Evaluate the numerical expressions using `at hxi1`. Rewrite `hxi1` using `[MulChar.map_nonunit _ hu]`. Evaluate the numerical expressions using `at hxi1`.

Establish `hH2` using `UpperTheory.V.X.genB_prodX hX.f_odd.pos φ ξ hX.odd`. Establish `hid` using `hsumid ξ hξsum`. Establish `hG : Bern.genB 1 (prodX φ ξ : ZMod (f * 2 ^ (m + e)) → PadicAlgCl l) = ∑ u, ξ u * g u`. Establish `hne' : ((f * 2 ^ (m + e) : ℕ) : PadicAlgCl l) ≠ 0` using `Nat.cast_ne_zero.2 (by positivity)`. Apply `mul_left_cancel₀ hne'` to reduce the goal to its premises.

Rewrite using `[hH2]`. Conclude with `hid`. Establish `hξA : ∀ u, ξ u ∈ A` using `fun u => normA _ (hξn u)`. Establish `hgA : ∀ u, g u ∈ A` using `fun u => (ofB _ (hgB u)).1`. Establish `hgq : ∀ u, red ⟨g u, hgA u⟩ ^ (l ^ d) = red ⟨g u, hgA u⟩` using `fun u => (ofB _ (hgB u)).2`.

Establish `hφA : ∀ a : ℕ, φ (a : ZMod f) ∈ A` using `fun a => (ofB _ (hφB a)).1`. Establish `hcA : ((2 ^ e : ℕ) : PadicAlgCl l) * c ∈ A` using `(ofB _ (B.mul_mem (natCast_mem B _) hcB)).1`. Set `ξk : ZMod (2 ^ (m + e)) →* k` to `{ toFun := fun u => red ⟨ξ u, hξA u⟩ map_one' := by`. Rewrite using `[← map_one red]`. Use `congr 1`.

Conclude with `Subtype.ext (by simp)`. Use the proof step `map_mul' := fun u v => by`. Rewrite using `[← map_mul]`. Use `congr 1`. Conclude with `Subtype.ext (by simp) }`.

Establish `hξk0 : ∀ u : ZMod (2 ^ (m + e)), ¬IsUnit u → ξk u = 0`. Introduce `u hu`. Use `show red ⟨ξ u, hξA u⟩ = 0`. Establish `e0 : (⟨ξ u, hξA u⟩ : A) = 0` using `Subtype.ext (by simp [MulChar.map_nonunit _ hu])`. Rewrite using `[e0, map_zero]`.

Establish `hξkv : ξk (1 + 2 ^ (m + e - 1)) = -1` using `by show red ⟨ξ _, hξA _⟩ = -1`. Establish `e0 : (⟨ξ (1 + 2 ^ (m + e - 1)), hξA _⟩ : A) = -1` using `Subtype.ext (by simp [hxi1])`. Rewrite using `[e0, map_neg, map_one]`. Establish `hshiftk : ∀ u : ZMod (2 ^ (m + e)), red ⟨g u, hgA u⟩ - red ⟨g (u - ((f * 2 ^ e : ℕ) : ZMod (2 ^ (m + e)))), hgA _⟩ = red ⟨_, hcA⟩ - if u.val < f * 2 ^ e then red ⟨φ (u.val : ZMod f), hφA u.val⟩ else 0`. Introduce `u`.

Establish `h` using `hshift (2 ^ e) hft u`. Rewrite using `[← map_sub]`. Use `split_ifs with hlt`. Rewrite using `[← map_sub]`. Use `congr 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show g u - g (u - _) = ((2 ^ e : ℕ) : PadicAlgCl l) * c - φ _`. Rewrite using `[h, if_pos hlt]`. Rewrite using `[sub_zero]`. Use `congr 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show g u - g (u - _) = ((2 ^ e : ℕ) : PadicAlgCl l) * c`. Rewrite using `[h, if_neg hlt, sub_zero]`. Establish `hφk1 : red ⟨φ ((1 : ℕ) : ZMod f), hφA 1⟩ = 1`. Establish `e0 : (⟨φ ((1 : ℕ) : ZMod f), hφA 1⟩ : A) = 1` using `Subtype.ext (by simp)`.

Rewrite using `[e0, map_one]`. Establish `hφks : red ⟨φ ((f * 2 ^ e - 1 : ℕ) : ZMod f), hφA _⟩ * ξk (-1) = -1` using `by show red _ * red ⟨ξ (-1), hξA _⟩ = -1`. Rewrite using `[← map_mul]`. Establish `hc : ((f * 2 ^ e - 1 : ℕ) : ZMod f) = -1`. Rewrite using `[Nat.cast_sub (by omega : 1 ≤ f * 2 ^ e)]`.

Simplify using the standard rewrite rules. Establish `e0 : (⟨φ ((f * 2 ^ e - 1 : ℕ) : ZMod f), hφA _⟩ * ⟨ξ (-1), hξA _⟩ : A) = -1`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show φ _ * ξ (-1) = -1`. Rewrite using `[hc, hX.odd]`.

Rewrite using `[e0, map_neg, map_one]`. Establish `hlint : ((l ^ d : ℕ) : ℤ) = 1 + 2 ^ e * (a : ℤ)`. Establish `hnat : l ^ d = 1 + 2 ^ e * a` using `by rw [← ha]; omega`. Conclude with `hnat` after adjusting the coercions. Establish `hcore` using `lx_core (k := k) l hl2 d e m (f * 2 ^ e) (a : ℤ) he2 hao.natCast hlint (by omega) hs hs1 (dvd_mul_left _ _) ξk hξk0 hξkv (fun u => red ⟨g u, hgA u⟩) hgq (fun a => red ⟨φ (a : ZMod f), hφA a⟩) (red ⟨_, hcA⟩) hshiftk hφk1 hφks`.

Rewrite using `[hG]`. Establish `hSA : (∑ u, ξ u * g u) ∈ A` using `A.sum_mem (fun u _ => A.mul_mem (hξA u) (hgA u))`. Establish `hred_sum : red ⟨∑ u, ξ u * g u, hSA⟩ = ∑ u, ξk u * red ⟨g u, hgA u⟩`. Establish `e0 : (⟨∑ u, ξ u * g u, hSA⟩ : A) = ∑ u, (⟨ξ u, hξA u⟩ * ⟨g u, hgA u⟩ : A)` using `Subtype.ext (by simp)`. Rewrite using `[e0, map_sum]`.

Simplify using `only [map_mul]`. Both sides reduce to the same expression. Apply `le_antisymm ((hA _).1 hSA)` to reduce the goal to its premises. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`.

Conclude with `hcore (hred_sum ▸ (hred ⟨_, hSA⟩).2 hlt)`.
-/
theorem UpperTheory.V.X.lemmaX :
    LemmaX := by
  intro l _ d f n φ ξ hX
  obtain ⟨k, _, _, A, red, hA, hred⟩ := UpperTheory.exists_residue_map_padicAlgCl_integers l
  have hlp : l.Prime := Fact.out
  haveI : ExpChar k l := ExpChar.prime hlp
  have hq1 : 1 < l ^ d := Nat.one_lt_pow hX.d_pos.ne' hlp.one_lt
  have hl2 : l ≠ 2 := by
    intro h
    subst h
    have h4 := hX.four
    have h2a : 2 ∣ 2 ^ d - 1 := dvd_trans (by norm_num) h4
    have h2d : 2 ∣ 2 ^ d := dvd_pow_self 2 hX.d_pos.ne'
    omega
  obtain ⟨e, he⟩ : ∃ e, e = (l ^ d - 1).factorization 2 := ⟨_, rfl⟩
  have hne : l ^ d - 1 ≠ 0 := by omega
  have he2 : 2 ≤ e := by
    rw [he]
    exact (Nat.prime_two.pow_dvd_iff_le_factorization hne).1 (by rw [show (2:ℕ) ^ 2 = 4 by norm_num]; exact hX.four)
  obtain ⟨a, ha, hao⟩ : ∃ a, l ^ d - 1 = 2 ^ e * a ∧ Odd a := by
    refine ⟨(l ^ d - 1) / 2 ^ e, ?_, ?_⟩
    · rw [he]
      exact (Nat.ordProj_mul_ordCompl_eq_self _ 2).symm
    · rw [he]
      exact Nat.coprime_two_left.1 (Nat.coprime_ordCompl Nat.prime_two hne)
  have hbig : f * 4 ^ e ≤ 2 ^ n := by rw [he]; exact hX.big
  have hf1 : 1 ≤ f := hX.f_odd.pos
  have h4e : (4 : ℕ) ^ e = 2 ^ e * 2 ^ e := by
    rw [← mul_pow]
    norm_num
  have hen : e + e ≤ n := by
    have h' : 2 ^ (e + e) ≤ 2 ^ n := by
      rw [pow_add, ← h4e]
      exact le_trans (Nat.le_mul_of_pos_left _ hf1) hbig
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h'
  obtain ⟨m, rfl⟩ : ∃ m, n = m + e := ⟨n - e, by omega⟩
  have hs : f * 2 ^ e ≤ 2 ^ m := by
    have h' : f * 2 ^ e * 2 ^ e ≤ 2 ^ m * 2 ^ e := by
      rw [← pow_add, mul_assoc, ← h4e]
      exact hbig
    exact Nat.le_of_mul_le_mul_right h' (by positivity)
  have h4le : 4 ≤ 2 ^ e := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he2
  have hs1 : 1 < f * 2 ^ e := by
    calc 1 < 2 ^ e := by omega
      _ ≤ f * 2 ^ e := Nat.le_mul_of_pos_left _ hf1
  have hft : f * 2 ^ e ≤ 2 ^ (m + e) := le_trans hs (Nat.pow_le_pow_right (by norm_num) (by omega))
  have normA : ∀ x : PadicAlgCl l, ‖x‖ ≤ 1 → x ∈ A := fun x hx => (hA x).2 hx
  have pow_one_norm : ∀ (x : PadicAlgCl l) (j : ℕ), 0 < j → x ^ j = 1 → ‖x‖ = 1 := by
    intro x j hj hx
    have h' : ‖x‖ ^ j = 1 := by rw [← norm_pow, hx, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg x) hj.ne').1 h'
  have hξn : ∀ u, ‖ξ u‖ ≤ 1 := by
    intro u
    by_cases hu : IsUnit u
    · have h' : ξ u ^ Nat.totient (2 ^ (m + e)) = 1 := by
        obtain ⟨v, rfl⟩ := hu
        rw [← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one, map_one]
      exact (pow_one_norm _ _ (Nat.totient_pos.2 (by positivity)) h').le
    · rw [MulChar.map_nonunit _ hu, norm_zero]
      exact zero_le_one
  have hφq : ∀ u : ZMod f, φ u ^ (l ^ d) = φ u := by
    intro u
    by_cases hu : IsUnit u
    · have h1' : φ ^ (l ^ d - 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 hX.ord
      have h' : φ u ^ (l ^ d - 1) = 1 := by
        rw [← MulChar.pow_apply' φ hne u, h1', MulChar.one_apply hu]
      calc φ u ^ (l ^ d) = φ u ^ (l ^ d - 1 + 1) := by rw [Nat.sub_add_cancel hq1.le]
        _ = φ u := by rw [pow_succ, h', one_mul]
    · rw [MulChar.map_nonunit _ hu, zero_pow (by positivity)]
  let B : Subring (PadicAlgCl l) := (RingHom.eqLocus ((iterateFrobenius k l d).comp red) red).map A.subtype
  have memB : ∀ (x : PadicAlgCl l) (hx : x ∈ A), red ⟨x, hx⟩ ^ (l ^ d) = red ⟨x, hx⟩ → x ∈ B := by
    intro x hx h
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    show (iterateFrobenius k l d) (red ⟨x, hx⟩) = red ⟨x, hx⟩
    rwa [iterateFrobenius_def]
  have ofB : ∀ x ∈ B, ∃ hx : x ∈ A, red ⟨x, hx⟩ ^ (l ^ d) = red ⟨x, hx⟩ := by
    rintro x ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    have h' : (iterateFrobenius k l d) (red y) = red y := hy
    rwa [iterateFrobenius_def] at h'
  have fixB : ∀ x : PadicAlgCl l, x ^ (l ^ d) = x → x ∈ B := by
    intro x hx
    have hn : ‖x‖ ≤ 1 := by
      by_cases h0 : x = 0
      · simp [h0]
      · have h' : x ^ (l ^ d - 1) = 1 := by
          have h'' : x ^ (l ^ d - 1) * x = 1 * x := by
            rw [← pow_succ, Nat.sub_add_cancel hq1.le, one_mul, hx]
          exact mul_right_cancel₀ h0 h''
        exact (pow_one_norm x _ (by omega) h').le
    refine memB x (normA x hn) ?_
    rw [← map_pow]
    congr 1
    exact Subtype.ext (by simp [hx])
  have h2k : ((2 : ℕ) : k) ≠ 0 := by
    intro h
    have h' := (CharP.cast_eq_zero_iff k l 2).1 h
    exact hl2 ((Nat.prime_dvd_prime_iff_eq hlp Nat.prime_two).1 h')
  have h2A : ((2 : ℕ) : PadicAlgCl l) ∈ A := natCast_mem A 2
  have hnorm2 : ‖((2 : ℕ) : PadicAlgCl l)‖ = 1 := by
    apply le_antisymm ((hA _).1 h2A)
    by_contra hlt
    push_neg at hlt
    apply h2k
    have h' := (hred ⟨_, h2A⟩).2 hlt
    have e2 : (⟨((2 : ℕ) : PadicAlgCl l), h2A⟩ : A) = ((2 : ℕ) : A) := Subtype.ext (map_natCast A.subtype 2).symm
    rw [e2, map_natCast] at h'
    exact h'
  have hinvN : ((2 ^ (m + e) : ℕ) : PadicAlgCl l)⁻¹ ∈ B := by
    have hyn : ‖((2 ^ (m + e) : ℕ) : PadicAlgCl l)⁻¹‖ = 1 := by
      rw [norm_inv, Nat.cast_pow, norm_pow, hnorm2, one_pow, inv_one]
    have hyA := normA _ hyn.le
    refine memB _ hyA ?_
    have h2nA : ((2 ^ (m + e) : ℕ) : PadicAlgCl l) ∈ A := natCast_mem A _
    have hN0 : ((2 ^ (m + e) : ℕ) : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
    have hprod : red ⟨_, hyA⟩ * red ⟨_, h2nA⟩ = 1 := by
      rw [← map_mul, ← map_one red]
      congr 1
      exact Subtype.ext (by simp [hN0])
    have e2 : (⟨((2 ^ (m + e) : ℕ) : PadicAlgCl l), h2nA⟩ : A) = ((2 ^ (m + e) : ℕ) : A) :=
      Subtype.ext (map_natCast A.subtype _).symm
    rw [e2, map_natCast] at hprod
    have hfrob : ((2 ^ (m + e) : ℕ) : k) ^ (l ^ d) = ((2 ^ (m + e) : ℕ) : k) := by
      rw [← iterateFrobenius_def, map_natCast]
    have hne0 : ((2 ^ (m + e) : ℕ) : k) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hprod
      exact zero_ne_one hprod
    have h' : red ⟨_, hyA⟩ ^ (l ^ d) * ((2 ^ (m + e) : ℕ) : k) = red ⟨_, hyA⟩ * ((2 ^ (m + e) : ℕ) : k) := by
      rw [hprod, ← hfrob, ← mul_pow, hprod, one_pow]
    exact mul_right_cancel₀ hne0 h'
  have hφB : ∀ a : ℕ, φ (a : ZMod f) ∈ B := fun a => fixB _ (hφq _)
  haveI : NeZero (2 ^ (m + e)) := ⟨by positivity⟩
  have hcop : f.Coprime (2 ^ (m + e)) := Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hX.f_odd)
  obtain ⟨g, c, hgB, hcB, hshift, hsumid⟩ := lx_partial (K := PadicAlgCl l) f (2 ^ (m + e)) hX.f_odd.pos hcop
    (fun a => φ (a : ZMod f)) (fun a => by simp [Nat.cast_add, ZMod.natCast_self]) B hφB hinvN
  have hxi1 := UpperTheory.primitive_two_pow_character_one_add_half_eq_neg_one (PadicAlgCl l) (m + e) (by omega) ξ hX.prim2
  have hξsum : ∑ u, ξ u = 0 := by
    refine MulChar.sum_eq_zero_of_ne_one (fun h1 => ?_)
    rw [h1] at hxi1
    by_cases hu : IsUnit (1 + 2 ^ (m + e - 1) : ZMod (2 ^ (m + e)))
    · rw [MulChar.one_apply hu] at hxi1
      norm_num at hxi1
    · rw [MulChar.map_nonunit _ hu] at hxi1
      norm_num at hxi1
  have hH2 := UpperTheory.V.X.genB_prodX hX.f_odd.pos φ ξ hX.odd
  have hid := hsumid ξ hξsum
  have hG : Bern.genB 1 (prodX φ ξ : ZMod (f * 2 ^ (m + e)) → PadicAlgCl l) = ∑ u, ξ u * g u := by
    have hne' : ((f * 2 ^ (m + e) : ℕ) : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
    apply mul_left_cancel₀ hne'
    rw [hH2]
    exact hid
  have hξA : ∀ u, ξ u ∈ A := fun u => normA _ (hξn u)
  have hgA : ∀ u, g u ∈ A := fun u => (ofB _ (hgB u)).1
  have hgq : ∀ u, red ⟨g u, hgA u⟩ ^ (l ^ d) = red ⟨g u, hgA u⟩ := fun u => (ofB _ (hgB u)).2
  have hφA : ∀ a : ℕ, φ (a : ZMod f) ∈ A := fun a => (ofB _ (hφB a)).1
  have hcA : ((2 ^ e : ℕ) : PadicAlgCl l) * c ∈ A := (ofB _ (B.mul_mem (natCast_mem B _) hcB)).1
  let ξk : ZMod (2 ^ (m + e)) →* k :=
    { toFun := fun u => red ⟨ξ u, hξA u⟩
      map_one' := by
        rw [← map_one red]
        congr 1
        exact Subtype.ext (by simp)
      map_mul' := fun u v => by
        rw [← map_mul]
        congr 1
        exact Subtype.ext (by simp) }
  have hξk0 : ∀ u : ZMod (2 ^ (m + e)), ¬IsUnit u → ξk u = 0 := by
    intro u hu
    show red ⟨ξ u, hξA u⟩ = 0
    have e0 : (⟨ξ u, hξA u⟩ : A) = 0 := Subtype.ext (by simp [MulChar.map_nonunit _ hu])
    rw [e0, map_zero]
  have hξkv : ξk (1 + 2 ^ (m + e - 1)) = -1 := by
    show red ⟨ξ _, hξA _⟩ = -1
    have e0 : (⟨ξ (1 + 2 ^ (m + e - 1)), hξA _⟩ : A) = -1 := Subtype.ext (by simp [hxi1])
    rw [e0, map_neg, map_one]
  have hshiftk : ∀ u : ZMod (2 ^ (m + e)),
      red ⟨g u, hgA u⟩ - red ⟨g (u - ((f * 2 ^ e : ℕ) : ZMod (2 ^ (m + e)))), hgA _⟩ =
        red ⟨_, hcA⟩ - if u.val < f * 2 ^ e then red ⟨φ (u.val : ZMod f), hφA u.val⟩ else 0 := by
    intro u
    have h := hshift (2 ^ e) hft u
    rw [← map_sub]
    split_ifs with hlt
    · rw [← map_sub]
      congr 1
      apply Subtype.ext
      show g u - g (u - _) = ((2 ^ e : ℕ) : PadicAlgCl l) * c - φ _
      rw [h, if_pos hlt]
    · rw [sub_zero]
      congr 1
      apply Subtype.ext
      show g u - g (u - _) = ((2 ^ e : ℕ) : PadicAlgCl l) * c
      rw [h, if_neg hlt, sub_zero]
  have hφk1 : red ⟨φ ((1 : ℕ) : ZMod f), hφA 1⟩ = 1 := by
    have e0 : (⟨φ ((1 : ℕ) : ZMod f), hφA 1⟩ : A) = 1 := Subtype.ext (by simp)
    rw [e0, map_one]
  have hφks : red ⟨φ ((f * 2 ^ e - 1 : ℕ) : ZMod f), hφA _⟩ * ξk (-1) = -1 := by
    show red _ * red ⟨ξ (-1), hξA _⟩ = -1
    rw [← map_mul]
    have hc : ((f * 2 ^ e - 1 : ℕ) : ZMod f) = -1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ f * 2 ^ e)]
      simp
    have e0 : (⟨φ ((f * 2 ^ e - 1 : ℕ) : ZMod f), hφA _⟩ * ⟨ξ (-1), hξA _⟩ : A) = -1 := by
      apply Subtype.ext
      show φ _ * ξ (-1) = -1
      rw [hc, hX.odd]
    rw [e0, map_neg, map_one]
  have hlint : ((l ^ d : ℕ) : ℤ) = 1 + 2 ^ e * (a : ℤ) := by
    have hnat : l ^ d = 1 + 2 ^ e * a := by rw [← ha]; omega
    exact_mod_cast hnat
  have hcore := lx_core (k := k) l hl2 d e m (f * 2 ^ e) (a : ℤ) he2 hao.natCast hlint (by omega) hs hs1
    (dvd_mul_left _ _) ξk hξk0 hξkv (fun u => red ⟨g u, hgA u⟩) hgq
    (fun a => red ⟨φ (a : ZMod f), hφA a⟩) (red ⟨_, hcA⟩) hshiftk hφk1 hφks
  rw [hG]
  have hSA : (∑ u, ξ u * g u) ∈ A := A.sum_mem (fun u _ => A.mul_mem (hξA u) (hgA u))
  have hred_sum : red ⟨∑ u, ξ u * g u, hSA⟩ = ∑ u, ξk u * red ⟨g u, hgA u⟩ := by
    have e0 : (⟨∑ u, ξ u * g u, hSA⟩ : A) = ∑ u, (⟨ξ u, hξA u⟩ * ⟨g u, hgA u⟩ : A) := Subtype.ext (by simp)
    rw [e0, map_sum]
    simp only [map_mul]
    rfl
  apply le_antisymm ((hA _).1 hSA)
  by_contra hlt
  push_neg at hlt
  exact hcore (hred_sum ▸ (hred ⟨_, hSA⟩).2 hlt)
