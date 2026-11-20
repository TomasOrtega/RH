import Development.EtaleCohomology.EtaleSheaves.SHEqvPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Polynomial IsLocalRing

namespace LateralTheory.E.TwFBijPf

/- English proof (translation)
Rewrite using `[aeval_def, aeval_def, Polynomial.hom_eval₂]`. Use `congr 1`.
-/
theorem aeval_res {C : Type} [CommRing C] [IsLocalRing C] (q : ℕ) (x : C) :
    aeval (residue C x) (cyclotomic q ℤ) = residue C (aeval x (cyclotomic q ℤ)) :=
  by
  rw [aeval_def, aeval_def, Polynomial.hom_eval₂]; congr 1

/- English proof (translation)
Rewrite using `[← map_cyclotomic_int, IsRoot, Polynomial.eval_map, aeval_def, algebraMap_int_eq]`.
-/
theorem isRoot_iff {K : Type} [CommRing K] (q : ℕ) (x : K) :
    IsRoot (cyclotomic q K) x ↔ aeval x (cyclotomic q ℤ) = 0 := by
  rw [← map_cyclotomic_int, IsRoot, Polynomial.eval_map, aeval_def, algebraMap_int_eq]

/- English proof (translation)
Use `haveI : NeZero ((q : ℕ) : ResidueField C) := ⟨by`. Use `hq.map (residue C)` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Conclude with `this.ne_zero⟩`. Rewrite using `[← isRoot_cyclotomic_iff, isRoot_iff]`.

Conclude with `(aeval_res q ζ).trans (by rw [h, map_zero])`.
-/
theorem res_prim {C : Type} [CommRing C] [IsLocalRing C] {q : ℕ} [NeZero q] (hq : IsUnit (q : C)) {ζ : C}
    (h : aeval ζ (cyclotomic q ℤ) = 0) : IsPrimitiveRoot (residue C ζ) q := by
  haveI : NeZero ((q : ℕ) : ResidueField C) := ⟨by
    have := hq.map (residue C); rw [map_natCast] at this; exact this.ne_zero⟩
  rw [← isRoot_cyclotomic_iff, isRoot_iff]
  exact (aeval_res q ζ).trans (by rw [h, map_zero])

/- English proof (translation)
Take `⟨g, hg⟩` from `cyclotomic.dvd_X_pow_sub_one q ℤ`. Use `congrArg (aeval ζ) hg` as an intermediate fact. Simplify using `[h] at this`. Conclude with `sub_eq_zero.1 this`.
-/
theorem pow_q {C : Type} [CommRing C] {q : ℕ} {ζ : C} (h : aeval ζ (cyclotomic q ℤ) = 0) : ζ ^ q = 1 := by
  obtain ⟨g, hg⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have := congrArg (aeval ζ) hg
  simp [h] at this
  exact sub_eq_zero.1 this

/- English proof (translation)
Use `⟨pow_q h, fun l hl => (res_prim hq h).dvd_of_pow_eq_one l ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow, hl, map_one]`.
-/
theorem prim {C : Type} [CommRing C] [IsLocalRing C] {q : ℕ} [NeZero q] (hq : IsUnit (q : C)) {ζ : C}
    (h : aeval ζ (cyclotomic q ℤ) = 0) : IsPrimitiveRoot ζ q := by
  refine ⟨pow_q h, fun l hl => (res_prim hq h).dvd_of_pow_eq_one l ?_⟩
  rw [← map_pow, hl, map_one]

/- English proof (translation)
Establish `hn0 : n ≠ 0` using `by rintro rfl; simp at hn`. Establish `key` using `(Commute.all x y).geom_sum₂_mul n`. Rewrite `key` using `[hx, hy, sub_self]`. Establish `hS : IsUnit (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i))`. Rewrite using `[← residue_ne_zero_iff_isUnit, map_sum]`.

Establish `: ∀ i ∈ Finset.range n, residue C (x ^ i * y ^ (n - 1 - i)) = residue C x ^ (n - 1)`. Introduce `i hi`. Rewrite using `[map_mul, map_pow, map_pow, ← hr, ← pow_add]`. Use `congr 1`. Use `Finset.mem_range.1 hi` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite using `[Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]`. Establish `h1 : IsUnit (residue C (n : C))` using `hn.map _`. Establish `h2 : IsUnit (residue C x)` using `(show IsUnit x from ⟨⟨x, x ^ (n - 1), by rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0), hx], by rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0), hx]⟩, rfl⟩).map _`. Rewrite `h1` using `[map_natCast]`.

Conclude with `(h1.mul (h2.pow _)).ne_zero`. Use `hS.mul_right_eq_zero.1 key` as an intermediate fact. Conclude with `sub_eq_zero.1 this`.
-/
theorem uniq {C : Type} [CommRing C] [IsLocalRing C] {n : ℕ} (hn : IsUnit (n : C)) {x y : C} (hx : x ^ n = 1)
    (hy : y ^ n = 1) (hr : residue C x = residue C y) : x = y := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have key := (Commute.all x y).geom_sum₂_mul n
  rw [hx, hy, sub_self] at key
  have hS : IsUnit (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) := by
    rw [← residue_ne_zero_iff_isUnit, map_sum]
    have : ∀ i ∈ Finset.range n, residue C (x ^ i * y ^ (n - 1 - i)) = residue C x ^ (n - 1) := by
      intro i hi
      rw [map_mul, map_pow, map_pow, ← hr, ← pow_add]
      congr 1
      have := Finset.mem_range.1 hi
      omega
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h1 : IsUnit (residue C (n : C)) := hn.map _
    have h2 : IsUnit (residue C x) := (show IsUnit x from ⟨⟨x, x ^ (n - 1), by rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0), hx],
      by rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0), hx]⟩, rfl⟩).map _
    rw [map_natCast] at h1
    exact (h1.mul (h2.pow _)).ne_zero
  have := hS.mul_right_eq_zero.1 key
  exact sub_eq_zero.1 this

/- English proof (translation)
Take `⟨i, hi, he⟩` from `(res_prim hq hη).eq_pow_of_pow_eq_one (ξ := residue C ξ) (by rw [← map_pow, pow_q hξ, map_one])`. Establish `hηi : η ^ i = ξ` using `uniq hq (by rw [← pow_mul, mul_comm, pow_mul, pow_q hη, one_pow]) (pow_q hξ) (by rw [map_pow, he])`. Establish `hc : i.Coprime q` using `((prim hq hη).pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) i).1 (hηi ▸ prim hq hξ)`. Use `⟨ZMod.unitOfCoprime i hc, ?_⟩` and prove the remaining obligations. Rewrite using `[ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi, hηi]`.
-/
theorem pow_rep {C : Type} [CommRing C] [IsLocalRing C] {q : ℕ} [NeZero q] (hq : IsUnit (q : C)) {η ξ : C}
    (hη : aeval η (cyclotomic q ℤ) = 0) (hξ : aeval ξ (cyclotomic q ℤ) = 0) :
    ∃ a : (ZMod q)ˣ, ξ = η ^ (a : ZMod q).val := by
  obtain ⟨i, hi, he⟩ := (res_prim hq hη).eq_pow_of_pow_eq_one (ξ := residue C ξ) (by rw [← map_pow, pow_q hξ, map_one])
  have hηi : η ^ i = ξ := uniq hq (by rw [← pow_mul, mul_comm, pow_mul, pow_q hη, one_pow]) (pow_q hξ) (by rw [map_pow, he])
  have hc : i.Coprime q := ((prim hq hη).pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) i).1 (hηi ▸ prim hq hξ)
  refine ⟨ZMod.unitOfCoprime i hc, ?_⟩
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi, hηi]

/- English proof (translation)
The claim follows from `Units.ext (ZMod.val_injective q (hη.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h))`.
-/
theorem pow_inj {C : Type} [CommRing C] {q : ℕ} [NeZero q] {η : C} (hη : IsPrimitiveRoot η q) {a b : (ZMod q)ˣ}
    (h : η ^ (a : ZMod q).val = η ^ (b : ZMod q).val) : a = b :=
  Units.ext (ZMod.val_injective q (hη.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h))

/- English proof (translation)
Take `⟨hH, hS⟩` from `hA`. Use `haveI : NeZero ((q : ℕ) : ResidueField A) := ⟨by`. Use `hq.map (residue A)` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Conclude with `this.ne_zero⟩`.

Take `⟨x, hx⟩` from `IsSepClosed.exists_root (cyclotomic q (ResidueField A)) (ne_of_gt (degree_cyclotomic_pos q _ (Nat.pos_of_ne_zero (NeZero.ne q)))) (separable_cyclotomic q _)`. Take `⟨a0, rfl⟩` from `residue_surjective x`. Establish `hd : IsUnit ((cyclotomic q A).derivative.eval a0)`. Rewrite using `[← residue_ne_zero_iff_isUnit]`. Use `(separable_cyclotomic q (ResidueField A)).aeval_derivative_ne_zero (x := residue A a0) (by` as an intermediate fact.

Rewrite using `[aeval_def, Algebra.algebraMap_self, eval₂_id]`. Conclude with `hx)`. Rewrite `this` using `[aeval_def, Algebra.algebraMap_self, eval₂_id, ← map_cyclotomic q (residue A), derivative_map, Polynomial.eval_map, Polynomial.eval₂_hom]`. Conclude with `this`. Take `⟨a, ha, -⟩` from `HenselianLocalRing.is_henselian (cyclotomic q A) (cyclotomic.monic q A) a0 (by`.

Rewrite using `[← residue_eq_zero_iff, ← Polynomial.eval₂_hom, ← Polynomial.eval_map, map_cyclotomic]`. Conclude with `hx) hd`. Conclude with `⟨a, (isRoot_iff q a).1 ha⟩`.
-/
theorem exists_root {A : Type} [CommRing A] {q : ℕ} [NeZero q] (hq : IsUnit (q : A)) (hA : SH A) :
    ∃ ζ : A, aeval ζ (cyclotomic q ℤ) = 0 := by
  obtain ⟨hH, hS⟩ := hA
  haveI : NeZero ((q : ℕ) : ResidueField A) := ⟨by
    have := hq.map (residue A); rw [map_natCast] at this; exact this.ne_zero⟩
  obtain ⟨x, hx⟩ := IsSepClosed.exists_root (cyclotomic q (ResidueField A))
    (ne_of_gt (degree_cyclotomic_pos q _ (Nat.pos_of_ne_zero (NeZero.ne q)))) (separable_cyclotomic q _)
  obtain ⟨a0, rfl⟩ := residue_surjective x
  have hd : IsUnit ((cyclotomic q A).derivative.eval a0) := by
    rw [← residue_ne_zero_iff_isUnit]
    have := (separable_cyclotomic q (ResidueField A)).aeval_derivative_ne_zero (x := residue A a0) (by
      rw [aeval_def, Algebra.algebraMap_self, eval₂_id]; exact hx)
    rw [aeval_def, Algebra.algebraMap_self, eval₂_id, ← map_cyclotomic q (residue A), derivative_map,
      Polynomial.eval_map, Polynomial.eval₂_hom] at this
    exact this
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (cyclotomic q A) (cyclotomic.monic q A) a0 (by
    rw [← residue_eq_zero_iff, ← Polynomial.eval₂_hom, ← Polynomial.eval_map, map_cyclotomic]; exact hx) hd
  exact ⟨a, (isRoot_iff q a).1 ha⟩

section Gen
variable {q : ℕ} [NeZero q] (i : ℤ) {C : Type} [CommRing C] [IsLocalRing C]

/- English proof (translation)
Use `conv_rhs => rw [← Nat.mod_add_div n q, pow_add, pow_mul, hη.pow_eq_one, one_pow, mul_one]`.
-/
theorem pmod {η : C} (hη : IsPrimitiveRoot η q) (n : ℕ) : η ^ (n % q) = η ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n q, pow_add, pow_mul, hη.pow_eq_one, one_pow, mul_one]

def ex (η ξ : Prim q C) : (ZMod q)ˣ := Classical.choose (pow_rep η.2.1 η.2.2 ξ.2.2)

/- English proof (translation)
The claim follows from `Classical.choose_spec (pow_rep η.2.1 η.2.2 ξ.2.2)`.
-/
theorem ex_spec (η ξ : Prim q C) : ξ.1 = η.1 ^ (ex η ξ : ZMod q).val := Classical.choose_spec (pow_rep η.2.1 η.2.2 ξ.2.2)

/- English proof (translation)
Establish `hη` using `prim η.2.1 η.2.2`. Apply `pow_inj hη` to reduce the goal to its premises. Rewrite using `[← ex_spec, h, ex_spec η ζ, ← pow_mul, Units.val_mul, ZMod.val_mul, pmod hη]`.
-/
theorem ex_pow (η ξ ζ : Prim q C) (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) : ex η ξ = ex η ζ * a := by
  have hη := prim η.2.1 η.2.2
  apply pow_inj hη
  rw [← ex_spec, h, ex_spec η ζ, ← pow_mul, Units.val_mul, ZMod.val_mul, pmod hη]

/- English proof (translation)
Establish `hη` using `prim η.2.1 η.2.2`. Apply `pow_inj hη` to reduce the goal to its premises. Rewrite using `[← ex_spec, Units.val_one, ZMod.val_one_eq_one_mod, pmod hη, pow_one]`.
-/
theorem ex_self (η : Prim q C) : ex η η = 1 := by
  have hη := prim η.2.1 η.2.2
  apply pow_inj hη
  rw [← ex_spec, Units.val_one, ZMod.val_one_eq_one_mod, pmod hη, pow_one]

def psi (η : Prim q C) : (Prim q C →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  Finsupp.linearCombination _ (fun ξ => ULift.up (((ex η ξ ^ i : (ZMod q)ˣ) : ZMod q)))

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `x ⟨ζ, ξ, a, h, rfl⟩`. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, psi, Finsupp.linearCombination_single, ex_pow η ξ ζ a h, mul_zpow, Units.val_mul]`. Apply `ULift.ext` to reduce the goal to its premises. Simplify using `[mul_comm]`.
-/
theorem rel_le (η : Prim q C) : twRel q i C ≤ LinearMap.ker (psi i η) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ, ξ, a, h, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, psi, Finsupp.linearCombination_single, ex_pow η ξ ζ a h,
    mul_zpow, Units.val_mul]
  apply ULift.ext
  simp [mul_comm]

def Psi (η : Prim q C) : ((Prim q C →₀ ULift.{1} (ZMod q)) ⧸ twRel q i C) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  (twRel q i C).liftQ (psi i η) (rel_le i η)

def gen (η : Prim q C) : (Prim q C →₀ ULift.{1} (ZMod q)) ⧸ twRel q i C := Submodule.Quotient.mk (Finsupp.single η 1)

/- English proof (translation)
Simplify using `[Psi, gen, psi, Finsupp.linearCombination_single, ex_self]`. Both sides reduce to the same expression.
-/
theorem Psi_gen (η : Prim q C) : Psi i η (gen i η) = 1 := by
  simp [Psi, gen, psi, Finsupp.linearCombination_single, ex_self]
  rfl

/- English proof (translation)
Proceed by induction on `z using Submodule.Quotient.induction_on with`. Consider the case `H x`. Proceed by induction on `x using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add x y hx hy`.

Rewrite using `[Submodule.Quotient.mk_add, map_add, add_smul, ← hx, ← hy]`. Consider the case `single ξ c`. Establish `hrel : Finsupp.single ξ (1 : ULift.{1} (ZMod q)) - Finsupp.single η (ULift.up (((ex η η * ex η ξ) ^ i : (ZMod q)ˣ) : ZMod q)) ∈ twRel q i C`. Use `Submodule.subset_span ⟨η, ξ, ex η ξ, ex_spec η ξ, ?_⟩` and prove the remaining obligations. Rewrite using `[ex_self, one_mul]`.

Rewrite `hrel` using `[ex_self, one_mul]`. Establish `h1 : (Submodule.Quotient.mk (Finsupp.single ξ 1) : (Prim q C →₀ ULift.{1} (ZMod q)) ⧸ twRel q i C) = ULift.up (((ex η ξ ^ i : (ZMod q)ˣ) : ZMod q)) • gen i η`. Rewrite using `[gen, ← Submodule.Quotient.mk_smul, Finsupp.smul_single, smul_eq_mul, mul_one]`. Conclude with `(Submodule.Quotient.eq _).2 hrel`. Establish `h2 : (Finsupp.single ξ c : Prim q C →₀ ULift.{1} (ZMod q)) = c • Finsupp.single ξ 1`.

Rewrite using `[Finsupp.smul_single, smul_eq_mul, mul_one]`. Rewrite using `[h2, Submodule.Quotient.mk_smul, h1, smul_smul]`. Use `congr 1`. Rewrite using `[map_smul, Psi_gen, smul_eq_mul, mul_one]`.
-/
theorem decomp (η : Prim q C) (z : (Prim q C →₀ ULift.{1} (ZMod q)) ⧸ twRel q i C) : z = Psi i η z • gen i η := by
  induction z using Submodule.Quotient.induction_on with
  | H x =>
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [Submodule.Quotient.mk_add, map_add, add_smul, ← hx, ← hy]
  | single ξ c =>
    have hrel : Finsupp.single ξ (1 : ULift.{1} (ZMod q)) - Finsupp.single η (ULift.up (((ex η η * ex η ξ) ^ i : (ZMod q)ˣ) : ZMod q))
        ∈ twRel q i C := by
      refine Submodule.subset_span ⟨η, ξ, ex η ξ, ex_spec η ξ, ?_⟩
      rw [ex_self, one_mul]
    rw [ex_self, one_mul] at hrel
    have h1 : (Submodule.Quotient.mk (Finsupp.single ξ 1) : (Prim q C →₀ ULift.{1} (ZMod q)) ⧸ twRel q i C) =
        ULift.up (((ex η ξ ^ i : (ZMod q)ˣ) : ZMod q)) • gen i η := by
      rw [gen, ← Submodule.Quotient.mk_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
      exact (Submodule.Quotient.eq _).2 hrel
    have h2 : (Finsupp.single ξ c : Prim q C →₀ ULift.{1} (ZMod q)) = c • Finsupp.single ξ 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [h2, Submodule.Quotient.mk_smul, h1, smul_smul]
    congr 1
    rw [map_smul, Psi_gen, smul_eq_mul, mul_one]

end Gen

/- English proof (translation)
Use `set F := Submodule.mapQ (twRel q i X) (twRel q i Y) (Finsupp.lmapDomain (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q)) (Prim.map g)) (twRel_le q i g)`. Establish `hF : ∀ z, F z = Psi i ζ z • gen i (Prim.map g ζ)`. Introduce `z`. Use `conv_lhs => rw [decomp i ζ z]`. Rewrite using `[map_smul]`.

Use `congr 1`. Simplify using `only [F, gen, Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]`. Establish `hP : ∀ z, Psi i (Prim.map g ζ) (F z) = Psi i ζ z`. Introduce `z`. Rewrite using `[hF, map_smul, Psi_gen, smul_eq_mul, mul_one]`.

Use `⟨fun z1 z2 h => ?_, fun w => ⟨Psi i (Prim.map g ζ) w • gen i ζ, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[decomp i ζ z1, decomp i ζ z2, ← hP z1, ← hP z2, h]`. Rewrite using `[hF, map_smul, Psi_gen, smul_eq_mul, mul_one]`. Conclude with `(decomp i _ w).symm`.
-/
theorem bij_ty {q : ℕ} [NeZero q] (i : ℤ) {X Y : Type} [CommRing X] [CommRing Y] [IsLocalRing X] [IsLocalRing Y]
    (g : X →+* Y) (ζ : Prim q X) :
    Function.Bijective (Submodule.mapQ (twRel q i X) (twRel q i Y) (Finsupp.lmapDomain (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q))
      (Prim.map g)) (twRel_le q i g)) := by
  set F := Submodule.mapQ (twRel q i X) (twRel q i Y) (Finsupp.lmapDomain (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q))
      (Prim.map g)) (twRel_le q i g)
  have hF : ∀ z, F z = Psi i ζ z • gen i (Prim.map g ζ) := by
    intro z
    conv_lhs => rw [decomp i ζ z]
    rw [map_smul]
    congr 1
    simp only [F, gen, Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  have hP : ∀ z, Psi i (Prim.map g ζ) (F z) = Psi i ζ z := by
    intro z
    rw [hF, map_smul, Psi_gen, smul_eq_mul, mul_one]
  refine ⟨fun z1 z2 h => ?_, fun w => ⟨Psi i (Prim.map g ζ) w • gen i ζ, ?_⟩⟩
  · rw [decomp i ζ z1, decomp i ζ z2, ← hP z1, ← hP z2, h]
  · rw [hF, map_smul, Psi_gen, smul_eq_mul, mul_one]
    exact (decomp i _ w).symm

/- English proof (translation)
The claim follows from `bij_ty i g.hom ζ`.
-/
theorem bij_gen {q : ℕ} [NeZero q] (i : ℤ) {X Y : CommRingCat.{0}} [IsLocalRing X] [IsLocalRing Y] (g : X ⟶ Y)
    (ζ : Prim q X) : Function.Bijective ((twF q i).map g).hom :=
  bij_ty i g.hom ζ

/- English proof (translation)
Introduce `q _ i A B f hq hA hB`. Take `⟨hHA, hSA⟩` from `hA`. Take `⟨hHB, -⟩` from `hB`. Establish `hloc : ∀ (R : CommRingCat.{0}), IsLocalRing R → IsLocalRing Γ(Spec R, ⊤)`. Introduce `R _`.

Set `e` to `(Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv`. Use `haveI : Nontrivial Γ(Spec R, ⊤) := e.toEquiv.nontrivial`. Conclude with `IsLocalRing.of_surjective' e.symm.toRingHom e.symm.surjective`. Use `haveI := hloc A inferInstance`. Use `haveI := hloc B inferInstance`.

Take `⟨ζ, hζ⟩` from `exists_root hq ⟨hHA, hSA⟩`. Conclude with `bij_gen i _ (Prim.map (Scheme.ΓSpecIso A).inv.hom ⟨ζ, hq, hζ⟩)`.
-/
theorem TwFBij_of : LateralTheory.E.SHEqvPf.TwFBij := by
  intro q _ i A B f hq hA hB
  obtain ⟨hHA, hSA⟩ := hA
  obtain ⟨hHB, -⟩ := hB
  have hloc : ∀ (R : CommRingCat.{0}), IsLocalRing R → IsLocalRing Γ(Spec R, ⊤) := by
    intro R _
    let e := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
    haveI : Nontrivial Γ(Spec R, ⊤) := e.toEquiv.nontrivial
    exact IsLocalRing.of_surjective' e.symm.toRingHom e.symm.surjective
  haveI := hloc A inferInstance
  haveI := hloc B inferInstance
  obtain ⟨ζ, hζ⟩ := exists_root hq ⟨hHA, hSA⟩
  exact bij_gen i _ (Prim.map (Scheme.ΓSpecIso A).inv.hom ⟨ζ, hq, hζ⟩)

end LateralTheory.E.TwFBijPf
