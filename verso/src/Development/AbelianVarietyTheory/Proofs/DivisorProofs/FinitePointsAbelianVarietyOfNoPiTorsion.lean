import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePointsOfIsOpenImmersion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinitePointsAbelianVarietyOfNoTorsion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardKerIntegralCombinationEndoLePowStatement
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.NoPiTorsion

/- English proof (translation)
Use `letI := Fintype.ofFinite (R ⧸ I)`. Set `f : (Fin d → Fin (K + 1)) → R ⧸ I` to `fun v => Ideal.Quotient.mk I (∑ i, ((v i : ℕ) : ℤ) • a i)`. Take `⟨v, w, hvw, hf⟩` from `Fintype.exists_ne_map_eq_of_card_lt f (by`. Rewrite using `[← Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]`. Conclude with `hK)`.

Use `⟨fun i => ((v i : ℕ) : ℤ) - ((w i : ℕ) : ℤ), fun i => ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show (((v i : ℕ) : ℤ) - ((w i : ℕ) : ℤ)).natAbs ≤ K`. Use `(v i).isLt` as an intermediate fact. Use `(w i).isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Introduce `h0`. Apply `hvw` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Use `(Fintype.linearIndependent_iff.1 ha) _ h0 i` as an intermediate fact. Conclude with `Fin.ext (by omega)`.

Establish `: ∑ i, (((v i : ℕ) : ℤ) - ((w i : ℕ) : ℤ)) • a i = ∑ i, ((v i : ℕ) : ℤ) • a i - ∑ i, ((w i : ℕ) : ℤ) • a i`. Simplify using `only [sub_smul, Finset.sum_sub_distrib]`. Rewrite using `[this]`. Conclude with `Ideal.Quotient.eq.1 hf`.
-/
theorem exists_small_mem {R : Type} [CommRing R] (I : Ideal R) [Finite (R ⧸ I)] {d : ℕ} (a : Fin d → R)
    (ha : LinearIndependent ℤ a) (K : ℕ) (hK : Nat.card (R ⧸ I) < (K + 1) ^ d) :
    ∃ n : Fin d → ℤ, (∀ i, (n i).natAbs ≤ K) ∧ ∑ i, n i • a i ≠ 0 ∧ ∑ i, n i • a i ∈ I := by
  classical
  letI := Fintype.ofFinite (R ⧸ I)
  let f : (Fin d → Fin (K + 1)) → R ⧸ I := fun v => Ideal.Quotient.mk I (∑ i, ((v i : ℕ) : ℤ) • a i)
  obtain ⟨v, w, hvw, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by
    rw [← Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]; exact hK)
  refine ⟨fun i => ((v i : ℕ) : ℤ) - ((w i : ℕ) : ℤ), fun i => ?_, ?_, ?_⟩
  · show (((v i : ℕ) : ℤ) - ((w i : ℕ) : ℤ)).natAbs ≤ K
    have := (v i).isLt; have := (w i).isLt; omega
  · intro h0
    apply hvw
    funext i
    have := (Fintype.linearIndependent_iff.1 ha) _ h0 i
    exact Fin.ext (by omega)
  · have : ∑ i, (((v i : ℕ) : ℤ) - ((w i : ℕ) : ℤ)) • a i =
        ∑ i, ((v i : ℕ) : ℤ) • a i - ∑ i, ((w i : ℕ) : ℤ) • a i := by
      simp only [sub_smul, Finset.sum_sub_distrib]
    rw [this]
    exact Ideal.Quotient.eq.1 hf

variable {E : Type} [Field E] [NumberField E] {k : Type} [Field k] {A : Over (Sp k)} [GrpObj A]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Establish `h` using `act.add 0 0`. Rewrite `h` using `[add_zero]`. Rewrite using `[Nat.cast_zero, pow_zero]`.

Apply the tactic sequence `first | exact left_eq_mul.1 h | exact self_eq_mul_right.1 h`. Consider the case `succ n ih => rw [Nat.cast_succ, act.add, ih, act.one, pow_succ]`.
-/
theorem act_natCast (act : OAct (𝓞 E) A) (n : ℕ) : act.act (n : 𝓞 E) = 𝟙 A ^ n := by
  induction n with
  | zero =>
    have h := act.add 0 0
    rw [add_zero] at h
    rw [Nat.cast_zero, pow_zero]
    first | exact left_eq_mul.1 h | exact self_eq_mul_right.1 h
  | succ n ih => rw [Nat.cast_succ, act.add, ih, act.one, pow_succ]

/- English proof (translation)
Rewrite using `[act_natCast, MonObj.comp_pow, Category.comp_id]`.
-/
theorem comp_act_natCast (act : OAct (𝓞 E) A) (x : 𝟙_ (Over (Sp k)) ⟶ A) (n : ℕ) :
    x ≫ act.act (n : 𝓞 E) = x ^ n := by
  rw [act_natCast, MonObj.comp_pow, Category.comp_id]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => intro y hy`. Rewrite `hy` using `[pow_zero, act.one, Category.comp_id]`. Then use the resulting hypothesis. Consider the case `succ m ih`. Introduce `y hy`.

Rewrite `hy` using `[pow_succ, act.mul, ← Category.assoc]`. Conclude with `ih y (htor _ hy)`.
-/
theorem eq_one_of_comp_act_pow (act : OAct (𝓞 E) A) (π : 𝓞 E)
    (htor : ∀ x : 𝟙_ (Over (Sp k)) ⟶ A, x ≫ act.act π = 1 → x = 1) (m : ℕ) :
    ∀ y : 𝟙_ (Over (Sp k)) ⟶ A, y ≫ act.act (π ^ m) = 1 → y = 1 := by
  induction m with
  | zero => intro y hy; rwa [pow_zero, act.one, Category.comp_id] at hy
  | succ m ih =>
    intro y hy
    rw [pow_succ, act.mul, ← Category.assoc] at hy
    exact ih y (htor _ hy)

/- English proof (translation)
Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hb`. Establish `hy : x ≫ act.act (π' ^ m) = 1`. Use `eq_one_of_comp_act_pow act π htor m _ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, ← act.mul, ← mul_pow, mul_comm π', ← hN, ← Nat.cast_pow, comp_act_natCast, hx]`. Use `act.hom c` as an intermediate fact.

Rewrite using `[mul_comm, act.mul, ← Category.assoc, hy, MonObj.one_comp]`.
-/
theorem comp_act_eq_one_of_pow_eq_one (act : OAct (𝓞 E) A) (π π' : 𝓞 E) (N m : ℕ)
    (hN : (N : 𝓞 E) = π * π') (htor : ∀ x : 𝟙_ (Over (Sp k)) ⟶ A, x ≫ act.act π = 1 → x = 1)
    (x : 𝟙_ (Over (Sp k)) ⟶ A) (hx : x ^ (N ^ m) = 1) (b : 𝓞 E) (hb : b ∈ Ideal.span {π' ^ m}) :
    x ≫ act.act b = 1 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
  have hy : x ≫ act.act (π' ^ m) = 1 := by
    refine eq_one_of_comp_act_pow act π htor m _ ?_
    rw [Category.assoc, ← act.mul, ← mul_pow, mul_comm π', ← hN, ← Nat.cast_pow, comp_act_natCast, hx]
  have := act.hom c
  rw [mul_comm, act.mul, ← Category.assoc, hy, MonObj.one_comp]

end GlobalTheory.NoPiTorsion

namespace GlobalTheory.NoPiTorsion

/- English proof (translation)
Introduce `E _ _ k _ _ _ A _ act π g hA hg hπ0 hπu htor`. Use `set N := (Algebra.norm ℤ π).natAbs with hNdef`. Establish `hN0 : N ≠ 0`. Rewrite using `[hNdef, ← Ideal.absNorm_span_singleton]`. Introduce `h`.

Conclude with `hπ0 (Ideal.span_singleton_eq_bot.1 (Ideal.absNorm_eq_zero_iff.1 h))`. Establish `hN1 : N ≠ 1`. Rewrite using `[hNdef, ← Ideal.absNorm_span_singleton]`. Introduce `h`. Conclude with `hπu (Ideal.span_singleton_eq_top.1 (Ideal.absNorm_eq_one_iff.1 h))`.

Choose the witnesses or unpack the hypotheses as in `⟨π', hπ'⟩ : π ∣ (N : 𝓞 E) := by`. Use `Ideal.absNorm_mem (Ideal.span {π})` as an intermediate fact. Rewrite `this` using `[Ideal.absNorm_span_singleton, ← hNdef, Ideal.mem_span_singleton]`. Then use the resulting hypothesis. Set `ιB` to `Module.Free.ChooseBasisIndex ℤ (𝓞 E)`. Set `d` to `Fintype.card ιB`.

Set `a : Fin d → 𝓞 E` to `fun i => RingOfIntegers.basis E ((Fintype.equivFin ιB).symm i)`. Establish `ha : LinearIndependent ℤ a` using `(RingOfIntegers.basis E).linearIndependent.comp _ (Fintype.equivFin ιB).symm.injective`. Establish `hd : Module.finrank ℤ (𝓞 E) = d` using `Module.finrank_eq_card_chooseBasisIndex ℤ (𝓞 E)`. Establish `hd0 : 0 < d` using `hd ▸ Module.finrank_pos`. Use `set N' := (Algebra.norm ℤ π').natAbs with hN'def`.

Establish `hNN : N * N' = N ^ d`. Establish `h` using `congrArg (fun z => (Algebra.norm ℤ z).natAbs) hπ'`. Simplify using `only [map_mul, Int.natAbs_mul] at h`. Rewrite using `[← h]`. Establish `: ((N : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (N : ℤ)` using `by simp`.

Rewrite using `[this, Algebra.norm_algebraMap, hd, Int.natAbs_pow, Int.natAbs_natCast]`. Establish `hN'0 : N' ≠ 0`. Introduce `h`. Rewrite `hNN` using `[h, mul_zero]`. Conclude with `hN0 (pow_eq_zero_iff hd0.ne' |>.1 hNN.symm)`.

Take `⟨C, hC⟩` from `GlobalTheory.T.card_ker_integralCombination_endo_le_pow E k A act g hA hg d a`. Establish `key : ∀ t : ℕ, (N ^ t) ^ (2 * g) ≤ C`. Introduce `t`. Establish `hI : Nat.card (𝓞 E ⧸ Ideal.span {π' ^ (d * t)}) = N' ^ (d * t)`. Rewrite using `[← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton, map_pow, Int.natAbs_pow]`.

Use `haveI : Finite (𝓞 E ⧸ Ideal.span {π' ^ (d * t)}) := Nat.finite_of_card_ne_zero (by rw [hI]; exact pow_ne_zero _ hN'0)`. Take `⟨n, hnK, hn0, hnI⟩` from `exists_small_mem (Ideal.span {π' ^ (d * t)}) a ha (N' ^ t) (by`. Rewrite using `[hI, mul_comm d t, pow_mul]`. Conclude with `Nat.pow_lt_pow_left (Nat.lt_succ_self _) hd0.ne')`. Take `⟨hfin, hcard⟩` from `hC n (N' ^ t) hnK hn0`.

Establish `hMk : ((N ^ (d * t) : ℕ) : k) ≠ 0` using `Nat.cast_ne_zero.2 (pow_ne_zero _ hN0)`. Establish `htors` using `GlobalTheory.abMulN_holds k A g (N ^ (d * t)) hA hg hMk`. Establish `hle : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ A // x ^ (N ^ (d * t)) = 1} ≤ Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ A // x ≫ act.act (∑ i, n i • a i) = 1}` using `Nat.card_le_card_of_injective (fun x => ⟨x.1, comp_act_eq_one_of_pow_eq_one act π π' N (d * t) hπ' htor x.1 x.2 _ hnI⟩) (by intro x y h; simp only [Subtype.mk.injEq] at h; exact Subtype.ext h)`. Rewrite `hle` using `[htors]`. Establish `h1` using `hle.trans hcard`.

Establish `hsplit : N ^ (d * t) = N ^ t * N' ^ t` using `by rw [pow_mul, ← hNN, mul_pow]`. Rewrite `h1` using `[hsplit, mul_pow]`. Establish `hpos : 0 < (N' ^ t) ^ (2 * g)` using `by positivity`. Conclude with `Nat.le_of_mul_le_mul_right h1 hpos`. Establish `hg0 : g = 0`.

Assume the negation of the conclusion as `hg0`. Establish `h` using `key C`. Establish `h2 : 2 ≤ N` using `by omega`. Establish `h3 : C < 2 ^ C` using `Nat.lt_two_pow_self`. Establish `h4 : 2 ^ C ≤ N ^ C` using `Nat.pow_le_pow_left h2 C`.

Establish `h5 : N ^ C ≤ (N ^ C) ^ (2 * g)` using `Nat.le_self_pow (by omega) _`. Use linear arithmetic over natural numbers and integers. Substitute `hg0` using the available equality. Establish `h2k : ((2 : ℕ) : k) ≠ 0` using `Nat.cast_ne_zero.2 two_ne_zero`. Use `GlobalTheory.AbelianNoTorsion.finite_points_of_no_torsion k A hA 2 le_rfl h2k fun x hx => ?_` and prove the remaining obligations.

Establish `h2` using `GlobalTheory.abMulN_holds k A 0 2 hA hg h2k`. Rewrite `h2` using `[mul_zero, pow_zero]`. Establish `: Subsingleton {x : 𝟙_ (Over (Sp k)) ⟶ A // x ^ 2 = 1}` using `(Nat.card_eq_one_iff_unique.1 h2).1`. Conclude with `congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : {x : 𝟙_ (Over (Sp k)) ⟶ A // x ^ 2 = 1}) ⟨1, one_pow 2⟩)`.
-/
theorem finite_points : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : Over (Sp k)) [GrpObj A] (act : OAct (𝓞 E) A) (π : 𝓞 E) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → π ≠ 0 → ¬ IsUnit π → (∀ x : 𝟙_ (Over (Sp k)) ⟶ A, x ≫ act.act π = 1 → x = 1) → Finite (𝟙_ (Over (Sp k)) ⟶ A) := by
  intro E _ _ k _ _ _ A _ act π g hA hg hπ0 hπu htor
  classical
  set N := (Algebra.norm ℤ π).natAbs with hNdef
  have hN0 : N ≠ 0 := by
    rw [hNdef, ← Ideal.absNorm_span_singleton]; intro h
    exact hπ0 (Ideal.span_singleton_eq_bot.1 (Ideal.absNorm_eq_zero_iff.1 h))
  have hN1 : N ≠ 1 := by
    rw [hNdef, ← Ideal.absNorm_span_singleton]; intro h
    exact hπu (Ideal.span_singleton_eq_top.1 (Ideal.absNorm_eq_one_iff.1 h))
  obtain ⟨π', hπ'⟩ : π ∣ (N : 𝓞 E) := by
    have := Ideal.absNorm_mem (Ideal.span {π})
    rwa [Ideal.absNorm_span_singleton, ← hNdef, Ideal.mem_span_singleton] at this
  let ιB := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let d := Fintype.card ιB
  let a : Fin d → 𝓞 E := fun i => RingOfIntegers.basis E ((Fintype.equivFin ιB).symm i)
  have ha : LinearIndependent ℤ a :=
    (RingOfIntegers.basis E).linearIndependent.comp _ (Fintype.equivFin ιB).symm.injective
  have hd : Module.finrank ℤ (𝓞 E) = d := Module.finrank_eq_card_chooseBasisIndex ℤ (𝓞 E)
  have hd0 : 0 < d := hd ▸ Module.finrank_pos
  set N' := (Algebra.norm ℤ π').natAbs with hN'def
  have hNN : N * N' = N ^ d := by
    have h := congrArg (fun z => (Algebra.norm ℤ z).natAbs) hπ'
    simp only [map_mul, Int.natAbs_mul] at h
    rw [← h]
    have : ((N : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (N : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, hd, Int.natAbs_pow, Int.natAbs_natCast]
  have hN'0 : N' ≠ 0 := by
    intro h; rw [h, mul_zero] at hNN; exact hN0 (pow_eq_zero_iff hd0.ne' |>.1 hNN.symm)
  obtain ⟨C, hC⟩ := GlobalTheory.T.card_ker_integralCombination_endo_le_pow E k A act g hA hg d a
  have key : ∀ t : ℕ, (N ^ t) ^ (2 * g) ≤ C := by
    intro t
    have hI : Nat.card (𝓞 E ⧸ Ideal.span {π' ^ (d * t)}) = N' ^ (d * t) := by
      rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton, map_pow,
        Int.natAbs_pow]
    haveI : Finite (𝓞 E ⧸ Ideal.span {π' ^ (d * t)}) :=
      Nat.finite_of_card_ne_zero (by rw [hI]; exact pow_ne_zero _ hN'0)
    obtain ⟨n, hnK, hn0, hnI⟩ := exists_small_mem (Ideal.span {π' ^ (d * t)}) a ha (N' ^ t) (by
      rw [hI, mul_comm d t, pow_mul]; exact Nat.pow_lt_pow_left (Nat.lt_succ_self _) hd0.ne')
    obtain ⟨hfin, hcard⟩ := hC n (N' ^ t) hnK hn0
    have hMk : ((N ^ (d * t) : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ hN0)
    have htors := GlobalTheory.abMulN_holds k A g (N ^ (d * t)) hA hg hMk
    have hle : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ A // x ^ (N ^ (d * t)) = 1} ≤
        Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ A // x ≫ act.act (∑ i, n i • a i) = 1} :=
      Nat.card_le_card_of_injective
        (fun x => ⟨x.1, comp_act_eq_one_of_pow_eq_one act π π' N (d * t) hπ' htor x.1 x.2 _ hnI⟩)
        (by intro x y h; simp only [Subtype.mk.injEq] at h; exact Subtype.ext h)
    rw [htors] at hle
    have h1 := hle.trans hcard
    have hsplit : N ^ (d * t) = N ^ t * N' ^ t := by rw [pow_mul, ← hNN, mul_pow]
    rw [hsplit, mul_pow] at h1
    have hpos : 0 < (N' ^ t) ^ (2 * g) := by positivity
    exact Nat.le_of_mul_le_mul_right h1 hpos
  have hg0 : g = 0 := by
    by_contra hg0
    have h := key C
    have h2 : 2 ≤ N := by omega
    have h3 : C < 2 ^ C := Nat.lt_two_pow_self
    have h4 : 2 ^ C ≤ N ^ C := Nat.pow_le_pow_left h2 C
    have h5 : N ^ C ≤ (N ^ C) ^ (2 * g) := Nat.le_self_pow (by omega) _
    omega
  subst hg0
  have h2k : ((2 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.2 two_ne_zero
  refine GlobalTheory.AbelianNoTorsion.finite_points_of_no_torsion k A hA 2 le_rfl h2k fun x hx => ?_
  have h2 := GlobalTheory.abMulN_holds k A 0 2 hA hg h2k
  rw [mul_zero, pow_zero] at h2
  have : Subsingleton {x : 𝟙_ (Over (Sp k)) ⟶ A // x ^ 2 = 1} := (Nat.card_eq_one_iff_unique.1 h2).1
  exact congrArg Subtype.val
    (Subsingleton.elim (⟨x, hx⟩ : {x : 𝟙_ (Over (Sp k)) ⟶ A // x ^ 2 = 1}) ⟨1, one_pow 2⟩)

end GlobalTheory.NoPiTorsion
