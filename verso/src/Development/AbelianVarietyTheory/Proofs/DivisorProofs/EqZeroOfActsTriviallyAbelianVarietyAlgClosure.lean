import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAbelianVarietyTorsionSepClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAbelianVarietyTorsionSepClosed
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ActTrivialInj

/- English proof (translation)
Use `set y := algebraMap O F x with hydef`. Establish `hy : y ≠ 0`. Introduce `h`. Apply `hx` to reduce the goal to its premises. Apply `IsFractionRing.injective O F` to reduce the goal to its premises.

Rewrite using `[map_zero]`. Conclude with `h`. Establish `hint : IsIntegral ℚ y` using `Algebra.IsIntegral.isIntegral y`. Establish `hp0 : (minpoly ℚ y).coeff 0 ≠ 0` using `minpoly.coeff_zero_ne_zero hint hy`. Use `set q := IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ y) with hqdef`.

Establish `hq : Polynomial.aeval y q = 0` using `IsLocalization.integerNormalization_aeval_eq_zero (nonZeroDivisors ℤ) (minpoly ℚ y) (minpoly.aeval ℚ y)`. Take `⟨b, hb⟩` from `IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) (minpoly ℚ y)`. Use `set c := q.coeff 0 with hcdef`. Establish `hc : c ≠ 0`. Introduce `h`.

Establish `h'` using `congrArg (fun P => P.coeff 0) hb`. Simplify using `only [Polynomial.coeff_map, Polynomial.coeff_smul] at h'`. Rewrite `h'` using `[← hcdef, h, map_zero, eq_comm, smul_eq_zero]`. Break down `h' with h' | h'` into its components or cases. Conclude with `nonZeroDivisors.ne_zero b.2 h'`.

Conclude with `hp0 h'`. Establish `hO : Polynomial.aeval x q = 0`. Apply `IsFractionRing.injective O F` to reduce the goal to its premises. Rewrite using `[← Polynomial.aeval_algebraMap_apply, map_zero]`. Conclude with `hq`.

Establish `key` using `congrArg (Polynomial.aeval x) (Polynomial.X_mul_divX_add q)`. Rewrite `key` using `[hO, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, ← hcdef, algebraMap_int_eq, eq_intCast]`. Establish `hc' : (c : O) = x * -(Polynomial.aeval x q.divX)` using `by linear_combination key`. Use `⟨c.natAbs, Int.natAbs_ne_zero.2 hc, ?_⟩` and prove the remaining obligations. Establish `hn : ((c.natAbs : ℕ) : O) = ((|c| : ℤ) : O)` using `by rw [← Int.natCast_natAbs, Int.cast_natCast]`.

Break down `abs_choice c with h | h` into its components or cases. Conclude with `⟨-(Polynomial.aeval x q.divX), by rw [hn, h, hc']⟩`. Conclude with `⟨Polynomial.aeval x q.divX, by rw [hn, h, Int.cast_neg, hc']; ring⟩`.
-/
theorem exists_nat_eq_mul {F : Type} [Field F] [NumberField F] {O : Type} [CommRing O] [Algebra O F]
    [IsFractionRing O F] {x : O} (hx : x ≠ 0) : ∃ n : ℕ, n ≠ 0 ∧ ∃ r : O, (n : O) = x * r := by
  set y := algebraMap O F x with hydef
  have hy : y ≠ 0 := by
    intro h
    apply hx
    apply IsFractionRing.injective O F
    rw [map_zero]
    exact h
  have hint : IsIntegral ℚ y := Algebra.IsIntegral.isIntegral y
  have hp0 : (minpoly ℚ y).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hy
  set q := IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ y) with hqdef
  have hq : Polynomial.aeval y q = 0 :=
    IsLocalization.integerNormalization_aeval_eq_zero (nonZeroDivisors ℤ) (minpoly ℚ y) (minpoly.aeval ℚ y)
  obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) (minpoly ℚ y)
  set c := q.coeff 0 with hcdef
  have hc : c ≠ 0 := by
    intro h
    have h' := congrArg (fun P => P.coeff 0) hb
    simp only [Polynomial.coeff_map, Polynomial.coeff_smul] at h'
    rw [← hcdef, h, map_zero, eq_comm, smul_eq_zero] at h'
    rcases h' with h' | h'
    · exact nonZeroDivisors.ne_zero b.2 h'
    · exact hp0 h'
  have hO : Polynomial.aeval x q = 0 := by
    apply IsFractionRing.injective O F
    rw [← Polynomial.aeval_algebraMap_apply, map_zero]
    exact hq
  have key := congrArg (Polynomial.aeval x) (Polynomial.X_mul_divX_add q)
  rw [hO, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, ← hcdef, algebraMap_int_eq, eq_intCast] at key
  have hc' : (c : O) = x * -(Polynomial.aeval x q.divX) := by linear_combination key
  refine ⟨c.natAbs, Int.natAbs_ne_zero.2 hc, ?_⟩
  have hn : ((c.natAbs : ℕ) : O) = ((|c| : ℤ) : O) := by rw [← Int.natCast_natAbs, Int.cast_natCast]
  rcases abs_choice c with h | h
  · exact ⟨-(Polynomial.aeval x q.divX), by rw [hn, h, hc']⟩
  · exact ⟨Polynomial.aeval x q.divX, by rw [hn, h, Int.cast_neg, hc']; ring⟩

/- English proof (translation)
Introduce and unpack `K Ω _ _ _ _ A _ _ hA ⟨d, hd, hsm⟩ l _ hl F _ _ O _ _ _ α x hx`. Assume the negation of the conclusion as `hx0`. Establish `hl' : l.Prime` using `Fact.out`. Use `set L := AlgebraicClosure Ω`. Use `set t : Sp L ⟶ Sp K := spMap (algebraMap K L) with htdef`.

Establish `hgp` using `isGrpPullback_pullback A t`. Take `⟨e, he⟩` from `GlobalTheory.exists_mulEquiv_of_isGrpPullback hgp (𝟙 (Sp L)) t (Category.id_comp t).symm`. Establish `h1 : ∀ y : ptOver K L ⟶ A, y ≫ α.act x = 1`. Introduce `y`. Take `⟨v, rfl⟩` from `e.surjective y`.

Establish `hv : e (v ≫ (OAct.pullback t A α).act x) = e v ≫ α.act x`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[he, Over.comp_left, Over.comp_left, he, Category.assoc, Category.assoc]`. Use `congr 1`. Conclude with `pullback.lift_fst _ _ _`.

Rewrite using `[← hv, hx, comp_one, map_one]`. Take `⟨n, hn0, r, hr⟩` from `exists_nat_eq_mul (F := F) hx0`. Establish `h0 : α.act 0 = 1`. Establish `h00` using `α.add 0 0`. Rewrite `h00` using `[add_zero]`.

Conclude with `mul_left_cancel (h00.symm.trans (_root_.mul_one _).symm)`. Establish `hnat : ∀ m : ℕ, ∀ y : ptOver K L ⟶ A, y ≫ α.act (m : O) = y ^ m`. Introduce `m y`. Proceed by induction on `m with`. Consider the case `zero => rw [Nat.cast_zero, h0, comp_one, pow_zero]`.

Consider the case `succ m ih => rw [Nat.cast_succ, α.add, comp_mul, ih, α.one, Category.comp_id, pow_succ]`. Establish `hall : ∀ y : ptOver K L ⟶ A, y ^ n = 1`. Introduce `y`. Use `haveI := α.hom r`. Rewrite using `[← hnat, hr, α.mul, ← Category.assoc, h1, one_comp]`.

Take `⟨v, m, hlm, hnm⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hn0 l hl'.ne_one`. Establish `hsub : ∀ y : ptOver K L ⟶ A, y ^ (l ^ (v + 1)) = 1 → y ^ (l ^ v) = 1`. Introduce `y hy`. Establish `e1 : (y ^ l ^ v) ^ l = 1` using `by rw [← pow_mul, ← pow_succ]; exact hy`. Establish `e2 : (y ^ l ^ v) ^ m = 1` using `by rw [← pow_mul, ← hnm]; exact hall y`.

Establish `hcop : Nat.Coprime l m` using `(Nat.Prime.coprime_iff_not_dvd hl').2 hlm`. Establish `e3` using `pow_gcd_eq_one.2 ⟨e1, e2⟩`. Rewrite `e3` using `[hcop.gcd_eq_one, pow_one]`. Then use the resulting hypothesis. Establish `hlK : ∀ k : ℕ, ((l ^ k : ℕ) : K) ≠ 0` using `fun k => by rw [Nat.cast_pow]; exact pow_ne_zero _ hl`. Establish `cN` using `GlobalTheory.SepClosedTorsion.card_torsion_sepClosed K L A hA d hsm (l ^ (v + 1)) (hlK _)`.

Establish `cv` using `GlobalTheory.SepClosedTorsion.card_torsion_sepClosed K L A hA d hsm (l ^ v) (hlK _)`. Establish `hfin : Finite {y : ptOver K L ⟶ A // y ^ (l ^ v) = 1}` using `Nat.finite_of_card_ne_zero (by rw [cv]; exact pow_ne_zero _ (pow_ne_zero _ hl'.ne_zero))`. Establish `hle` using `Nat.card_le_card_of_injective (fun y : {y : ptOver K L ⟶ A // y ^ (l ^ (v + 1)) = 1} => (⟨y.1, hsub y.1 y.2⟩ : {y : ptOver K L ⟶ A // y ^ (l ^ v) = 1})) (fun a b h => Subtype.ext (congrArg (fun z : {y : ptOver K L ⟶ A // y ^ (l ^ v) = 1} => z.1) h))`. Rewrite `hle` using `[cN, cv]`. Establish `hlt : (l ^ v) ^ (2 * d) < (l ^ (v + 1)) ^ (2 * d)` using `Nat.pow_lt_pow_left (Nat.pow_lt_pow_right hl'.one_lt (Nat.lt_succ_self v)) (by omega)`.

Use linear arithmetic over natural numbers and integers.
-/
theorem eq_zero_of_act_pullback_eq_one : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → (∃ d : ℕ, 0 < d ∧ SmoothOfRelativeDimension d A.hom) → ∀ (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (F : Type) [Field F] [NumberField F] (O : Type) [CommRing O] [Algebra O F] [IsFractionRing O F] (α : OAct O A) (x : O), (OAct.pullback (spMap (algebraMap K (AlgebraicClosure Ω))) A α).act x = 1 → x = 0 := by
  rintro K Ω _ _ _ _ A _ _ hA ⟨d, hd, hsm⟩ l _ hl F _ _ O _ _ _ α x hx
  by_contra hx0
  have hl' : l.Prime := Fact.out
  set L := AlgebraicClosure Ω
  set t : Sp L ⟶ Sp K := spMap (algebraMap K L) with htdef
  have hgp := isGrpPullback_pullback A t
  obtain ⟨e, he⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hgp (𝟙 (Sp L)) t (Category.id_comp t).symm
  have h1 : ∀ y : ptOver K L ⟶ A, y ≫ α.act x = 1 := by
    intro y
    obtain ⟨v, rfl⟩ := e.surjective y
    have hv : e (v ≫ (OAct.pullback t A α).act x) = e v ≫ α.act x := by
      apply Over.OverMorphism.ext
      rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, Category.assoc]
      congr 1
      exact pullback.lift_fst _ _ _
    rw [← hv, hx, comp_one, map_one]
  obtain ⟨n, hn0, r, hr⟩ := exists_nat_eq_mul (F := F) hx0
  have h0 : α.act 0 = 1 := by
    have h00 := α.add 0 0
    rw [add_zero] at h00
    exact mul_left_cancel (h00.symm.trans (_root_.mul_one _).symm)
  have hnat : ∀ m : ℕ, ∀ y : ptOver K L ⟶ A, y ≫ α.act (m : O) = y ^ m := by
    intro m y
    induction m with
    | zero => rw [Nat.cast_zero, h0, comp_one, pow_zero]
    | succ m ih => rw [Nat.cast_succ, α.add, comp_mul, ih, α.one, Category.comp_id, pow_succ]
  have hall : ∀ y : ptOver K L ⟶ A, y ^ n = 1 := by
    intro y
    haveI := α.hom r
    rw [← hnat, hr, α.mul, ← Category.assoc, h1, one_comp]
  obtain ⟨v, m, hlm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 l hl'.ne_one
  have hsub : ∀ y : ptOver K L ⟶ A, y ^ (l ^ (v + 1)) = 1 → y ^ (l ^ v) = 1 := by
    intro y hy
    have e1 : (y ^ l ^ v) ^ l = 1 := by rw [← pow_mul, ← pow_succ]; exact hy
    have e2 : (y ^ l ^ v) ^ m = 1 := by rw [← pow_mul, ← hnm]; exact hall y
    have hcop : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hl').2 hlm
    have e3 := pow_gcd_eq_one.2 ⟨e1, e2⟩
    rwa [hcop.gcd_eq_one, pow_one] at e3
  have hlK : ∀ k : ℕ, ((l ^ k : ℕ) : K) ≠ 0 := fun k => by rw [Nat.cast_pow]; exact pow_ne_zero _ hl
  have cN := GlobalTheory.SepClosedTorsion.card_torsion_sepClosed K L A hA d hsm (l ^ (v + 1)) (hlK _)
  have cv := GlobalTheory.SepClosedTorsion.card_torsion_sepClosed K L A hA d hsm (l ^ v) (hlK _)
  have hfin : Finite {y : ptOver K L ⟶ A // y ^ (l ^ v) = 1} :=
    Nat.finite_of_card_ne_zero (by rw [cv]; exact pow_ne_zero _ (pow_ne_zero _ hl'.ne_zero))
  have hle := Nat.card_le_card_of_injective
    (fun y : {y : ptOver K L ⟶ A // y ^ (l ^ (v + 1)) = 1} =>
      (⟨y.1, hsub y.1 y.2⟩ : {y : ptOver K L ⟶ A // y ^ (l ^ v) = 1}))
    (fun a b h => Subtype.ext (congrArg (fun z : {y : ptOver K L ⟶ A // y ^ (l ^ v) = 1} => z.1) h))
  rw [cN, cv] at hle
  have hlt : (l ^ v) ^ (2 * d) < (l ^ (v + 1)) ^ (2 * d) :=
    Nat.pow_lt_pow_left (Nat.pow_lt_pow_right hl'.one_lt (Nat.lt_succ_self v)) (by omega)
  omega

end GlobalTheory.ActTrivialInj

end
