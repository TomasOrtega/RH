import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import ReciprocityTheory.DualLattices.CharTableIsUnit
import ReciprocityTheory.DualLattices.SqIdeal
import ReciprocityTheory.DualLattices.PowMemCarrier
import Development.WeilBound.CoreStatements.HodgeTatePoints.RiEasy

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

noncomputable section

namespace PositivityTheory.HtPt.Ri

section
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, fun _ => c, ⟨(φ.quotKerEquivOfSurjective hφ).symm.trans ((Submodule.quotEquivOfEq _ _ hk).trans (LinearEquiv.funUnique (Fin 1) R _).symm)⟩, by simp⟩`.
-/
lemma hasLen_of_surj {M : Type} [AddCommGroup M] [Module R M] (φ : R →ₗ[R] M)
    (hφ : Function.Surjective φ) (c : R) (hk : LinearMap.ker φ = Ideal.span {c}) :
    HasLen v R M (v (algebraMap R C c)) :=
  ⟨1, fun _ => c, ⟨(φ.quotKerEquivOfSurjective hφ).symm.trans
    ((Submodule.quotEquivOfEq _ _ hk).trans (LinearEquiv.funUnique (Fin 1) R _).symm)⟩, by simp⟩

/- English proof (translation)
Take `⟨s, hs⟩` from `Submodule.mem_span_singleton.1 h`. Use `Ideal.mem_span_singleton'.2 ⟨s, hv.hom_inj ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, ← hs, Algebra.smul_def]`.
-/
lemma mem_span_alg (hv : v.Integers R) {r c : R}
    (h : algebraMap R C r ∈ Submodule.span R {algebraMap R C c}) : r ∈ Ideal.span {c} := by
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 h
  refine Ideal.mem_span_singleton'.2 ⟨s, hv.hom_inj ?_⟩
  rw [map_mul, ← hs, Algebra.smul_def]

/- English proof (translation)
Take `⟨μ, hμ⟩` from `hv.exists_of_le_one h.le`. Establish `ht' : (μ + n) ^ p = μ + n` using `hv.hom_inj (by`. Rewrite using `[map_pow, map_add, hμ, map_natCast, sub_add_cancel, ht])`. Take `⟨r, hr⟩` from `exists_add_pow_prime_eq hp.out μ (n : R)`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : (p : ℤ) ∣ (n : ℤ) ^ p - n := by`.

Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `push_cast`. Rewrite using `[ZMod.pow_card, sub_self]`. Establish `hk' : (n : R) ^ p - n = p * (k : R)` using `by exact_mod_cast congrArg (Int.cast : ℤ → R) hk`. Establish `hu : IsUnit (1 - μ ^ (p - 1))`.

Rewrite using `[hv.isUnit_iff_valuation_eq_one, map_sub, map_one]`. Apply `v.map_one_sub_of_lt` to reduce the goal to its premises. Rewrite using `[map_pow, map_pow, hμ]`. Conclude with `pow_lt_one₀ (by positivity) h (by have := hp.out.two_le; omega)`. Establish `e : μ ^ p = μ * μ ^ (p - 1)`.

Rewrite using `[← pow_succ']`. Use `congr 1`. Use `hp.out.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[← hμ]`.

Apply `alg_mem_pInt` to reduce the goal to its premises. Rewrite using `[← Ideal.mul_unit_mem_iff_mem _ hu]`. Use `Ideal.mem_span_singleton'.2 ⟨k + μ * n * r, ?_⟩` and prove the remaining obligations. Take the linear combination `ht' - hr - hk' - e`.
-/
lemma teich_mod_p (p : ℕ) [hp : Fact p.Prime] (hv : v.Integers R) {t : C} (ht : t ^ p = t) (n : ℕ)
    (h : v (t - n) < 1) : t - n ∈ pInt (C := C) R p := by
  obtain ⟨μ, hμ⟩ := hv.exists_of_le_one h.le
  have ht' : (μ + n) ^ p = μ + n := hv.hom_inj (by
    rw [map_pow, map_add, hμ, map_natCast, sub_add_cancel, ht])
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out μ (n : R)
  obtain ⟨k, hk⟩ : (p : ℤ) ∣ (n : ℤ) ^ p - n := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [ZMod.pow_card, sub_self]
  have hk' : (n : R) ^ p - n = p * (k : R) := by exact_mod_cast congrArg (Int.cast : ℤ → R) hk
  have hu : IsUnit (1 - μ ^ (p - 1)) := by
    rw [hv.isUnit_iff_valuation_eq_one, map_sub, map_one]
    apply v.map_one_sub_of_lt
    rw [map_pow, map_pow, hμ]
    exact pow_lt_one₀ (by positivity) h (by have := hp.out.two_le; omega)
  have e : μ ^ p = μ * μ ^ (p - 1) := by
    rw [← pow_succ']; congr 1; have := hp.out.two_le; omega
  rw [← hμ]
  apply alg_mem_pInt
  rw [← Ideal.mul_unit_mem_iff_mem _ hu]
  refine Ideal.mem_span_singleton'.2 ⟨k + μ * n * r, ?_⟩
  linear_combination ht' - hr - hk' - e

end

/- English proof (translation)
Take `⟨x, ω, δ, hx, hx0, hωp, hωc, hxω, -, hδ, hA, hI, hI2, hcol⟩` from `u3 p C v R hv hpv AA`. Establish `hp2` using `hp.out.two_le`. Establish `: Fact (1 < p)` using `⟨hp.out.one_lt⟩`. Take `⟨r1, hr1⟩` from `AA.le_int hx 1`. Establish `hxI : x ∈ augIdeal AA.carrier` using `(mem_aug _ _).2 ⟨hx, hx0⟩`.

Establish `hxl : ∀ a : ZMod p, x a - algebraMap R C r1 * (a.val : C) ∈ pInt (C` using `C) R p := by`. Introduce `a`. Use `Submodule.smul_mem _ r1 (teich_mod_p p hv (hωp a) a.val (hωc a))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[hxω a, Algebra.smul_def, hr1]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hl : (fun a : ZMod p => (a.val : C)) ∈ linFun (C` using `C) R p (ZMod p) := by`. Use `⟨fun a => ⟨a.val, map_natCast _ _⟩, fun a b => ?_⟩` and prove the remaining obligations. Use `alg_mem_pInt (C := C) p (val_add_mem (R := R) p a b)` as an intermediate fact. Simplify `this` using `only [map_sub, map_natCast]`.

Establish `hxadd : x ∈ addFun (C` using `C) R p (ZMod p) := by`. Introduce `a b`. Use `Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _ (hxl (a + b)) (hxl a)) (hxl b)) (Submodule.smul_mem _ r1 (hl.2 a b))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[Algebra.smul_def]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hev : ∀ f ∈ augIdeal AA.carrier, f 1 ∈ Submodule.span R {algebraMap R C r1}`. Establish `: augIdeal AA.carrier ≤ (Submodule.span R {algebraMap R C r1}).comap (LinearMap.proj (R` using `R) (φ := fun _ : ZMod p => C) 1) := by`. Rewrite using `[hI, Submodule.span_le]`. Introduce and unpack `_ ⟨j, hj, -, rfl⟩`.

Use `Submodule.mem_span_singleton.2 ⟨r1 ^ (j - 1), ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.proj_apply, Pi.pow_apply, Algebra.smul_def, map_pow, hr1]`. Rewrite using `[← pow_succ]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Conclude with `fun f hf => this hf`. Establish `hpr : pInt (C` using `C) R p ≤ Submodule.span R {algebraMap R C r1} := by`. Take `⟨g, hg, hg0, hg1⟩` from `hg`. Rewrite using `[pInt, Submodule.span_le, Set.singleton_subset_iff, ← hg1]`. Conclude with `hev g ((mem_aug _ _).2 ⟨hg, hg0⟩)`.

Prove the components needed by the constructor for the conclusion. Use `⟨v (algebraMap R C r1), _, v (algebraMap R C δ), ?_, hcol, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `hasLen_of_surj ((Submodule.mkQ _) ∘ₗ LinearMap.toSpanSingleton R _ ⟨_, hl⟩) ?_ r1 ?_` and prove the remaining obligations. Introduce `y`. Take `⟨⟨f, hf⟩, rfl⟩` from `Submodule.mkQ_surjective _ y`.

Take `⟨r, hr⟩` from `hf.1 1`. Use `⟨r, Eq.symm ((Submodule.Quotient.eq _).2 ?_)⟩` and prove the remaining obligations. Use `Submodule.mem_sup_right (T := pFun R p (ZMod p)) fun a _ => ?_` and prove the remaining obligations. Use `add_nsmul_mem hf.2 1 a.val` as an intermediate fact. Rewrite `this` using `[nsmul_one, ZMod.natCast_zmod_val, ← hr, mul_comm]`.

Simplify `this` using `[Algebra.smul_def]`. Use extensionality with `r`. Simplify using `only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Take `⟨g, hg, k, hk, e⟩` from `Submodule.mem_sup.1 h`. Establish `e1 : g 1 + k 1 = algebraMap R C r`. Use `congrFun e 1` as an intermediate fact. Simplify `this` using `only [Pi.add_apply, Pi.smul_apply, Algebra.smul_def, ZMod.val_one, Nat.cast_one, mul_one]`. Apply `mem_span_alg hv` to reduce the goal to its premises.

Take `⟨r0, hr0⟩` from `AA.le_int hg.1 0`. Establish `h1` using `hev (g - r0 • 1) ((mem_aug _ _).2 ⟨Submodule.sub_mem _ hg.1 (Submodule.smul_mem _ _ AA.one_mem), by`. Simplify using `[Algebra.smul_def, hr0]⟩)`. Establish `h2` using `Submodule.add_mem _ (Submodule.add_mem _ h1 (hpr (add_zero_mem hg.2))) (hpr (hk 1 trivial))`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Simplify using `[← e1, Algebra.smul_def, hr0]`. Introduce `h`. Take `⟨s, rfl⟩` from `Ideal.mem_span_singleton'.1 h`. Rewrite using `[mul_smul]`. Use `Submodule.smul_mem _ _ (Submodule.mem_sup.2 ⟨x, ⟨hx, hxadd⟩, (r1 • fun a : ZMod p => (a.val : C)) - x, fun a _ => ?_, by abel⟩)` and prove the remaining obligations.

Use `Submodule.neg_mem _ (hxl a)` as an intermediate fact. Simplify `this` using `[Algebra.smul_def]`. Establish `htop : ⊤ ≤ Submodule.span C (Set.range fun j : Fin p => x ^ (j : ℕ))`. Take `⟨B, hB, hAB⟩` from `AA.lat`. Introduce `u _`.

Establish `: u = ∑ j, (B⁻¹ *ᵥ u) j • fun i => B i j` using `by conv_lhs => rw [← Matrix.one_mulVec u, ← Matrix.mul_nonsing_inv B hB, ← Matrix.mulVec_mulVec]`. Use function extensionality and compare the values at `i`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Use `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Apply `Submodule.span_subset_span R C` to reduce the goal to its premises. Rewrite using `[← hA, hAB]`. Conclude with `Submodule.subset_span ⟨j, rfl⟩`. Set `b` to `basisOfTopLeSpanOfCardEqFinrank _ htop (by simp)`.

Establish `hb : ∀ j : Fin p, b j = x ^ (j : ℕ)` using `fun j => by simp [b]`. Set `φ : (ZMod p → C) →ₗ[R] C` to `(b.coord ⟨1, by omega⟩).restrictScalars R`. Establish `hφ1 : φ x = 1`. Use `hb ⟨1, by omega⟩` as an intermediate fact. Rewrite `this` using `[pow_one]`.

Simplify using `[φ, ← this]`. Establish `hφ2 : ∀ j, 2 ≤ j → j < p → φ (x ^ j) = 0`. Introduce `j h1 h2`. Use `hb ⟨j, h2⟩` as an intermediate fact. Simplify using `only [φ, LinearMap.restrictScalars_apply]`.

Rewrite using `[← this, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne]`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers.

Establish `hδx : (fun a => algebraMap R C δ * x a) = δ • x`. Use function extensionality and compare the values at `a`. Simplify using `[Algebra.smul_def]`. Use `hasLen_of_surj ((Submodule.mkQ _) ∘ₗ LinearMap.toSpanSingleton R _ ⟨_, hxI⟩) ?_ δ ?_` and prove the remaining obligations. Introduce `y`.

Take `⟨⟨f, hf⟩, rfl⟩` from `Submodule.mkQ_surjective _ y`. Establish `hle : augIdeal AA.carrier ≤ Submodule.span R {x} ⊔ sqIdeal (augIdeal AA.carrier)`. Rewrite using `[hI2, hI, Submodule.span_le]`. Introduce and unpack `_ ⟨j, hj, hj', rfl⟩`. Distinguish the cases in `h1 : j = 1`.

Rewrite using `[h1, pow_one]`. Conclude with `Submodule.mem_sup_left (Submodule.mem_span_singleton_self x)`. Conclude with `Submodule.mem_sup_right (Submodule.subset_span (Or.inr ⟨j, by omega, hj', rfl⟩))`. Take `⟨y, hy, z, hz, e⟩` from `Submodule.mem_sup.1 (hle hf)`. Take `⟨r, rfl⟩` from `Submodule.mem_span_singleton.1 hy`.

Use `⟨r, Eq.symm ((Submodule.Quotient.eq _).2 ?_)⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `f - r • x ∈ sqIdeal (augIdeal AA.carrier)`. Rewrite using `[← e, add_sub_cancel_left]`. Conclude with `hz`. Use extensionality with `r`.

Simplify using `only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hle : sqIdeal (augIdeal AA.carrier) ≤ (Submodule.span R {algebraMap R C δ}).comap φ`. Rewrite using `[hI2, Submodule.span_le]`.

Introduce and unpack `_ (rfl | ⟨j, h1, h2, rfl⟩)`. Rewrite using `[hδx]`. Express the relevant statement in the definitionally equal form `φ (δ • x) ∈ Submodule.span R {algebraMap R C δ}`. Rewrite using `[map_smul, hφ1, Algebra.smul_def, mul_one]`. Conclude with `Submodule.mem_span_singleton_self _`.

Express the relevant statement in the definitionally equal form `φ (x ^ j) ∈ Submodule.span R {algebraMap R C δ}`. Rewrite using `[hφ2 j h1 h2]`. Conclude with `Submodule.zero_mem _`. Use `hle h` as an intermediate fact. Rewrite `this` using `[Submodule.mem_comap, map_smul, hφ1, Algebra.smul_def, mul_one]`.

Conclude with `mem_span_alg hv this`. Introduce `h`. Take `⟨s, rfl⟩` from `Ideal.mem_span_singleton'.1 h`. Rewrite using `[mul_smul, hI2, ← hδx]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl rfl))`.

Rewrite using `[hr1, ← pow_mul, ZMod.card, Nat.div_mul_cancel (Nat.even_mul_pred_self p).two_dvd]`. Rewrite using `[hδ, ← pow_mul, ← pow_mul, ZMod.card, Nat.div_mul_cancel (Nat.even_mul_pred_self p).two_dvd, mul_comm]`. Introduce `K g hg`. Distinguish the cases in `hK : ∀ k ∈ K, k = 0`. Establish `hxK : x ∈ afFun p (invFun AA.carrier K)` using `⟨⟨hx, fun a k hk => by rw [hK k hk, add_zero]⟩, hxadd⟩`.

Establish `hg1` using `hg.1`. Rewrite `hg1` using `[hA]`. Use `(Submodule.span_le.2 ?_) hg1` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `Subalgebra.pow_mem _ (Algebra.subset_adjoin hxK) _`.

Use `push Not at hK`. Take `⟨k, hk, hk0⟩` from `hK`. Take `⟨r, hr⟩` from `AA.le_int hg.1 0`. Establish `: g = algebraMap R (ZMod p → C) r`. Use function extensionality and compare the values at `a`.

Establish `ha : a ∈ K`. Use `K.nsmul_mem hk (a * k⁻¹).val` as an intermediate fact. Rewrite `this` using `[nsmul_eq_mul, ZMod.natCast_zmod_val, inv_mul_cancel_right₀ hk0]`. Then use the resulting hypothesis. Use `hg.2 0 a ha` as an intermediate fact. Rewrite `this` using `[zero_add]`.

Rewrite using `[this, ← hr]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `Subalgebra.algebraMap_mem _ r`.
-/
theorem tight_of (p : ℕ) [hp : Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] (hv : v.Integers R)
    (hpv : v (p : C) < 1) (AA : HopfOrder (C := C) R (ZMod p))
    (hg : ∃ g ∈ AA.carrier, g 0 = 0 ∧ g 1 = p) :
    IsTight v p AA.carrier ∧ ∀ K, GenAF p AA.carrier K := by
  obtain ⟨x, ω, δ, hx, hx0, hωp, hωc, hxω, -, hδ, hA, hI, hI2, hcol⟩ := u3 p C v R hv hpv AA
  have hp2 := hp.out.two_le
  have : Fact (1 < p) := ⟨hp.out.one_lt⟩
  obtain ⟨r1, hr1⟩ := AA.le_int hx 1
  have hxI : x ∈ augIdeal AA.carrier := (mem_aug _ _).2 ⟨hx, hx0⟩
  have hxl : ∀ a : ZMod p, x a - algebraMap R C r1 * (a.val : C) ∈ pInt (C := C) R p := by
    intro a
    have := Submodule.smul_mem _ r1 (teich_mod_p p hv (hωp a) a.val (hωc a))
    convert this using 1
    rw [hxω a, Algebra.smul_def, hr1]; ring
  have hl : (fun a : ZMod p => (a.val : C)) ∈ linFun (C := C) R p (ZMod p) := by
    refine ⟨fun a => ⟨a.val, map_natCast _ _⟩, fun a b => ?_⟩
    have := alg_mem_pInt (C := C) p (val_add_mem (R := R) p a b)
    simpa only [map_sub, map_natCast] using this
  have hxadd : x ∈ addFun (C := C) R p (ZMod p) := by
    intro a b
    have := Submodule.add_mem _
      (Submodule.sub_mem _ (Submodule.sub_mem _ (hxl (a + b)) (hxl a)) (hxl b))
      (Submodule.smul_mem _ r1 (hl.2 a b))
    convert this using 1
    rw [Algebra.smul_def]; ring
  have hev : ∀ f ∈ augIdeal AA.carrier, f 1 ∈ Submodule.span R {algebraMap R C r1} := by
    have : augIdeal AA.carrier ≤ (Submodule.span R {algebraMap R C r1}).comap
        (LinearMap.proj (R := R) (φ := fun _ : ZMod p => C) 1) := by
      rw [hI, Submodule.span_le]
      rintro _ ⟨j, hj, -, rfl⟩
      refine Submodule.mem_span_singleton.2 ⟨r1 ^ (j - 1), ?_⟩
      simp only [LinearMap.proj_apply, Pi.pow_apply, Algebra.smul_def, map_pow, hr1]
      rw [← pow_succ]; congr 1; omega
    exact fun f hf => this hf
  have hpr : pInt (C := C) R p ≤ Submodule.span R {algebraMap R C r1} := by
    obtain ⟨g, hg, hg0, hg1⟩ := hg
    rw [pInt, Submodule.span_le, Set.singleton_subset_iff, ← hg1]
    exact hev g ((mem_aug _ _).2 ⟨hg, hg0⟩)
  constructor
  · refine ⟨v (algebraMap R C r1), _, v (algebraMap R C δ), ?_, hcol, ?_, ?_, ?_⟩
    · refine hasLen_of_surj ((Submodule.mkQ _) ∘ₗ LinearMap.toSpanSingleton R _ ⟨_, hl⟩) ?_ r1 ?_
      · intro y
        obtain ⟨⟨f, hf⟩, rfl⟩ := Submodule.mkQ_surjective _ y
        obtain ⟨r, hr⟩ := hf.1 1
        refine ⟨r, Eq.symm ((Submodule.Quotient.eq _).2 ?_)⟩
        refine Submodule.mem_sup_right (T := pFun R p (ZMod p)) fun a _ => ?_
        have := add_nsmul_mem hf.2 1 a.val
        rw [nsmul_one, ZMod.natCast_zmod_val, ← hr, mul_comm] at this
        simpa [Algebra.smul_def] using this
      · ext r
        simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
          Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
          Submodule.subtype_apply, Submodule.coe_smul]
        constructor
        · intro h
          obtain ⟨g, hg, k, hk, e⟩ := Submodule.mem_sup.1 h
          have e1 : g 1 + k 1 = algebraMap R C r := by
            have := congrFun e 1
            simpa only [Pi.add_apply, Pi.smul_apply, Algebra.smul_def, ZMod.val_one, Nat.cast_one,
              mul_one] using this
          apply mem_span_alg hv
          obtain ⟨r0, hr0⟩ := AA.le_int hg.1 0
          have h1 := hev (g - r0 • 1) ((mem_aug _ _).2
            ⟨Submodule.sub_mem _ hg.1 (Submodule.smul_mem _ _ AA.one_mem), by
              simp [Algebra.smul_def, hr0]⟩)
          have h2 := Submodule.add_mem _ (Submodule.add_mem _ h1 (hpr (add_zero_mem hg.2)))
            (hpr (hk 1 trivial))
          convert h2 using 1
          simp [← e1, Algebra.smul_def, hr0]
        · intro h
          obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 h
          rw [mul_smul]
          refine Submodule.smul_mem _ _ (Submodule.mem_sup.2 ⟨x, ⟨hx, hxadd⟩,
            (r1 • fun a : ZMod p => (a.val : C)) - x, fun a _ => ?_, by abel⟩)
          have := Submodule.neg_mem _ (hxl a)
          simpa [Algebra.smul_def] using this
    · have htop : ⊤ ≤ Submodule.span C (Set.range fun j : Fin p => x ^ (j : ℕ)) := by
        obtain ⟨B, hB, hAB⟩ := AA.lat
        intro u _
        have : u = ∑ j, (B⁻¹ *ᵥ u) j • fun i => B i j := by
          conv_lhs => rw [← Matrix.one_mulVec u, ← Matrix.mul_nonsing_inv B hB,
            ← Matrix.mulVec_mulVec]
          funext i
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
          rfl
        rw [this]
        refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
        apply Submodule.span_subset_span R C
        rw [← hA, hAB]
        exact Submodule.subset_span ⟨j, rfl⟩
      let b := basisOfTopLeSpanOfCardEqFinrank _ htop (by simp)
      have hb : ∀ j : Fin p, b j = x ^ (j : ℕ) := fun j => by simp [b]
      let φ : (ZMod p → C) →ₗ[R] C := (b.coord ⟨1, by omega⟩).restrictScalars R
      have hφ1 : φ x = 1 := by
        have := hb ⟨1, by omega⟩
        rw [pow_one] at this
        simp [φ, ← this]
      have hφ2 : ∀ j, 2 ≤ j → j < p → φ (x ^ j) = 0 := by
        intro j h1 h2
        have := hb ⟨j, h2⟩
        simp only [φ, LinearMap.restrictScalars_apply]
        rw [← this, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne]
        intro h
        have := congrArg Fin.val h
        simp at this; omega
      have hδx : (fun a => algebraMap R C δ * x a) = δ • x := by
        funext a; simp [Algebra.smul_def]
      refine hasLen_of_surj ((Submodule.mkQ _) ∘ₗ LinearMap.toSpanSingleton R _ ⟨_, hxI⟩) ?_ δ ?_
      · intro y
        obtain ⟨⟨f, hf⟩, rfl⟩ := Submodule.mkQ_surjective _ y
        have hle : augIdeal AA.carrier ≤
            Submodule.span R {x} ⊔ sqIdeal (augIdeal AA.carrier) := by
          rw [hI2, hI, Submodule.span_le]
          rintro _ ⟨j, hj, hj', rfl⟩
          by_cases h1 : j = 1
          · rw [h1, pow_one]
            exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self x)
          · exact Submodule.mem_sup_right
              (Submodule.subset_span (Or.inr ⟨j, by omega, hj', rfl⟩))
        obtain ⟨y, hy, z, hz, e⟩ := Submodule.mem_sup.1 (hle hf)
        obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hy
        refine ⟨r, Eq.symm ((Submodule.Quotient.eq _).2 ?_)⟩
        change f - r • x ∈ sqIdeal (augIdeal AA.carrier)
        rw [← e, add_sub_cancel_left]; exact hz
      · ext r
        simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
          Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
          Submodule.subtype_apply, Submodule.coe_smul]
        constructor
        · intro h
          have hle : sqIdeal (augIdeal AA.carrier) ≤
              (Submodule.span R {algebraMap R C δ}).comap φ := by
            rw [hI2, Submodule.span_le]
            rintro _ (rfl | ⟨j, h1, h2, rfl⟩)
            · rw [hδx]
              change φ (δ • x) ∈ Submodule.span R {algebraMap R C δ}
              rw [map_smul, hφ1, Algebra.smul_def, mul_one]
              exact Submodule.mem_span_singleton_self _
            · change φ (x ^ j) ∈ Submodule.span R {algebraMap R C δ}
              rw [hφ2 j h1 h2]; exact Submodule.zero_mem _
          have := hle h
          rw [Submodule.mem_comap, map_smul, hφ1, Algebra.smul_def, mul_one] at this
          exact mem_span_alg hv this
        · intro h
          obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 h
          rw [mul_smul, hI2, ← hδx]
          exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl rfl))
    · rw [hr1, ← pow_mul, ZMod.card, Nat.div_mul_cancel (Nat.even_mul_pred_self p).two_dvd]
    · rw [hδ, ← pow_mul, ← pow_mul, ZMod.card,
        Nat.div_mul_cancel (Nat.even_mul_pred_self p).two_dvd, mul_comm]
  · intro K g hg
    by_cases hK : ∀ k ∈ K, k = 0
    · have hxK : x ∈ afFun p (invFun AA.carrier K) :=
        ⟨⟨hx, fun a k hk => by rw [hK k hk, add_zero]⟩, hxadd⟩
      have hg1 := hg.1
      rw [hA] at hg1
      refine (Submodule.span_le.2 ?_) hg1
      rintro _ ⟨j, rfl⟩
      exact Subalgebra.pow_mem _ (Algebra.subset_adjoin hxK) _
    · push Not at hK
      obtain ⟨k, hk, hk0⟩ := hK
      obtain ⟨r, hr⟩ := AA.le_int hg.1 0
      have : g = algebraMap R (ZMod p → C) r := by
        funext a
        have ha : a ∈ K := by
          have := K.nsmul_mem hk (a * k⁻¹).val
          rwa [nsmul_eq_mul, ZMod.natCast_zmod_val, inv_mul_cancel_right₀ hk0] at this
        have := hg.2 0 a ha
        rw [zero_add] at this
        rw [this, ← hr]; rfl
      rw [this]
      exact Subalgebra.algebraMap_mem _ r

/- English proof (translation)
Introduce `p hp C _ _ _ v R _ _ hv hpv`. Establish `: Fact (1 < p)` using `⟨hp.out.one_lt⟩`. Prove the components needed by the constructor for the conclusion. Establish `hc : (constOrder (C` using `C) (R := R) (N := ZMod p)).carrier = intFun R (ZMod p) := by`. Use `le_antisymm constOrder.le_int fun f hf => ?_` and prove the remaining obligations.

Use `choose r hr using hf`. Establish `: f = ∑ a, r a • (Pi.single a (1 : C) : ZMod p → C)`. Use function extensionality and compare the values at `y`. Simplify using `[Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hr]`. Rewrite using `[this]`.

Conclude with `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)`. Use `⟨constOrder, hc, ?_, tight_of p C v R hv hpv _ ⟨Pi.single 1 (p : C), ?_, by simp, by simp⟩⟩` and prove the remaining obligations. Rewrite using `[hc]`. Conclude with `fun a g hg y => hg _`. Rewrite using `[hc]`.

Introduce `y`. Distinguish the cases in `hy : y = 1`. Conclude with `⟨p, by simp [hy]⟩`. Conclude with `⟨0, by simp [hy]⟩`. Establish `hcard` using `card_addChar C (ZMod p)`.

Establish `: Finite (AddChar (ZMod p) C)` using `Nat.finite_of_card_ne_zero (by rw [hcard]; exact Fintype.card_ne_zero)`. Set `e : ZMod p ≃ AddChar (ZMod p) C` to `(Finite.card_eq.1 (hcard.trans Nat.card_eq_fintype_card.symm)).some.symm`. Establish `hc : (multOrder' v hv e).carrier = Submodule.span R (Set.range fun (ψ : AddChar (ZMod p) C) (x : ZMod p) => ψ x)`. Express the relevant statement in the definitionally equal form `Submodule.span R _ = _`. Rewrite using `[← e.surjective.range_comp fun (ψ : AddChar (ZMod p) C) (x : ZMod p) => ψ x]`.

Both sides reduce to the same expression. Establish `hmem : ∀ ψ : AddChar (ZMod p) C, (fun x => ψ x) ∈ (multOrder' v hv e).carrier` using `fun ψ => hc ▸ Submodule.subset_span ⟨ψ, rfl⟩`. Establish `hpow : ∀ ψ : AddChar (ZMod p) C, ψ 1 ^ p = 1` using `fun ψ => by`. Rewrite using `[← AddChar.map_nsmul_eq_pow, nsmul_one, ZMod.natCast_self, AddChar.map_zero_eq_one]`. Use `⟨multOrder' v hv e, hc, ?_, ?_, tight_of p C v R hv hpv _ ?_⟩` and prove the remaining obligations.

Introduce `h`. Establish `key : ∀ g ∈ (multOrder' v hv e).carrier, v (g 1 - g 0) < 1`. Introduce `g hg`. Rewrite `hg` using `[hc]`. Proceed by induction on `hg using Submodule.span_induction with`.

Consider the case `mem g hg`. Take `⟨ψ, rfl⟩` from `hg`. Simplify using `only [AddChar.map_zero_eq_one]`. Distinguish the cases in `h1 : ψ 1 = 1`. Simplify using `[h1]`.

Establish `hz : IsPrimitiveRoot (ψ 1) p`. Establish `h2` using `IsPrimitiveRoot.orderOf (ψ 1)`. Rewrite `h2` using `[orderOf_eq_prime (hpow ψ) h1]`. Then use the resulting hypothesis. Use `U3.val_prim_root (v := v) hz` as an intermediate fact. Rewrite `hpv` using `[← this]`.

Conclude with `lt_of_not_ge fun hh => absurd hpv (not_lt.2 (one_le_pow₀ hh))`. Consider the case `zero => simp`. Consider the case `add f g _ _ hf hg`. Establish `: (f + g) 1 - (f + g) 0 = (f 1 - f 0) + (g 1 - g 0)`. Simplify using `only [Pi.add_apply]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `v.map_add_lt hf hg`. Consider the case `smul r f _ hf`. Establish `: (r • f) 1 - (r • f) 0 = algebraMap R C r * (f 1 - f 0)`.

Simplify using `only [Pi.smul_apply, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (hv.map_le_one r)) hf`. Use `key (Pi.single 1 1) (by` as an intermediate fact.

Rewrite using `[h]`. Introduce `y`. Distinguish the cases in `hy : y = 1`. Conclude with `⟨1, by simp [hy]⟩`. Conclude with `⟨0, by simp [hy]⟩)`.

Simplify using `at this`. Introduce `a g hg`. Rewrite `hg`, the goal using `[hc]`. Establish `: Submodule.span R (Set.range fun (ψ : AddChar (ZMod p) C) (x : ZMod p) => ψ x) ≤ (Submodule.span R (Set.range fun (ψ : AddChar (ZMod p) C) (x : ZMod p) => ψ x)).comap (LinearMap.funLeft R C fun x : ZMod p => a • x)`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨ψ, rfl⟩`. Conclude with `Submodule.subset_span ⟨ψ.mulShift a, rfl⟩`. Conclude with `this hg`. Establish `: Nontrivial (AddChar (ZMod p) C)` using `e.symm.nontrivial`. Take `⟨ψ, hψ⟩` from `exists_ne (1 : AddChar (ZMod p) C)`.

Establish `h1 : ψ 1 ≠ 1`. Introduce `h`. Apply `hψ` to reduce the goal to its premises. Use extensionality with `y`. Rewrite using `[← ZMod.natCast_zmod_val y, ← nsmul_one, AddChar.map_nsmul_eq_pow, h]`.

Simplify using the standard rewrite rules. Use `⟨∑ i ∈ Finset.range p, (1 - fun x => (ψ ^ i) x), Submodule.sum_mem _ fun i _ => Submodule.sub_mem _ (multOrder' v hv e).one_mem (hmem _), by simp [Finset.sum_apply], ?_⟩` and prove the remaining obligations. Establish `e3` using `geom_sum_mul (ψ 1) p`. Rewrite `e3` using `[hpow, sub_self, mul_eq_zero]`. Simplify using `[Finset.sum_apply, Finset.sum_sub_distrib, AddChar.pow_apply, e3.resolve_right (sub_ne_zero.2 h1)]`.
-/
theorem inh_af : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → (∃ AA : HopfOrder (C := C) R (ZMod p), AA.carrier = intFun R (ZMod p) ∧ FStable (ZMod p) AA.carrier ∧ IsTight v p AA.carrier ∧ ∀ K, GenAF p AA.carrier K) ∧ (∃ AA : HopfOrder (C := C) R (ZMod p), AA.carrier = Submodule.span R (Set.range fun (ψ : AddChar (ZMod p) C) (x : ZMod p) => ψ x) ∧ AA.carrier ≠ intFun R (ZMod p) ∧ FStable (ZMod p) AA.carrier ∧ IsTight v p AA.carrier ∧ ∀ K, GenAF p AA.carrier K) := by
  intro p hp C _ _ _ v R _ _ hv hpv
  have : Fact (1 < p) := ⟨hp.out.one_lt⟩
  constructor
  · have hc : (constOrder (C := C) (R := R) (N := ZMod p)).carrier = intFun R (ZMod p) := by
      refine le_antisymm constOrder.le_int fun f hf => ?_
      choose r hr using hf
      have : f = ∑ a, r a • (Pi.single a (1 : C) : ZMod p → C) := by
        funext y; simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hr]
      rw [this]
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    refine ⟨constOrder, hc, ?_, tight_of p C v R hv hpv _ ⟨Pi.single 1 (p : C), ?_, by simp, by simp⟩⟩
    · rw [hc]; exact fun a g hg y => hg _
    · rw [hc]
      intro y
      by_cases hy : y = 1
      · exact ⟨p, by simp [hy]⟩
      · exact ⟨0, by simp [hy]⟩
  · have hcard := card_addChar C (ZMod p)
    have : Finite (AddChar (ZMod p) C) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact Fintype.card_ne_zero)
    let e : ZMod p ≃ AddChar (ZMod p) C :=
      (Finite.card_eq.1 (hcard.trans Nat.card_eq_fintype_card.symm)).some.symm
    have hc : (multOrder' v hv e).carrier =
        Submodule.span R (Set.range fun (ψ : AddChar (ZMod p) C) (x : ZMod p) => ψ x) := by
      change Submodule.span R _ = _
      rw [← e.surjective.range_comp fun (ψ : AddChar (ZMod p) C) (x : ZMod p) => ψ x]
      rfl
    have hmem : ∀ ψ : AddChar (ZMod p) C, (fun x => ψ x) ∈ (multOrder' v hv e).carrier :=
      fun ψ => hc ▸ Submodule.subset_span ⟨ψ, rfl⟩
    have hpow : ∀ ψ : AddChar (ZMod p) C, ψ 1 ^ p = 1 := fun ψ => by
      rw [← AddChar.map_nsmul_eq_pow, nsmul_one, ZMod.natCast_self, AddChar.map_zero_eq_one]
    refine ⟨multOrder' v hv e, hc, ?_, ?_, tight_of p C v R hv hpv _ ?_⟩
    · intro h
      have key : ∀ g ∈ (multOrder' v hv e).carrier, v (g 1 - g 0) < 1 := by
        intro g hg
        rw [hc] at hg
        induction hg using Submodule.span_induction with
        | mem g hg =>
          obtain ⟨ψ, rfl⟩ := hg
          simp only [AddChar.map_zero_eq_one]
          by_cases h1 : ψ 1 = 1
          · simp [h1]
          · have hz : IsPrimitiveRoot (ψ 1) p := by
              have h2 := IsPrimitiveRoot.orderOf (ψ 1)
              rwa [orderOf_eq_prime (hpow ψ) h1] at h2
            have := U3.val_prim_root (v := v) hz
            rw [← this] at hpv
            exact lt_of_not_ge fun hh => absurd hpv (not_lt.2 (one_le_pow₀ hh))
        | zero => simp
        | add f g _ _ hf hg =>
          have : (f + g) 1 - (f + g) 0 = (f 1 - f 0) + (g 1 - g 0) := by
            simp only [Pi.add_apply]; ring
          rw [this]; exact v.map_add_lt hf hg
        | smul r f _ hf =>
          have : (r • f) 1 - (r • f) 0 = algebraMap R C r * (f 1 - f 0) := by
            simp only [Pi.smul_apply, Algebra.smul_def]; ring
          rw [this, map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_left' (hv.map_le_one r)) hf
      have := key (Pi.single 1 1) (by
        rw [h]
        intro y
        by_cases hy : y = 1
        · exact ⟨1, by simp [hy]⟩
        · exact ⟨0, by simp [hy]⟩)
      simp at this
    · intro a g hg
      rw [hc] at hg ⊢
      have : Submodule.span R (Set.range fun (ψ : AddChar (ZMod p) C) (x : ZMod p) => ψ x) ≤
          (Submodule.span R (Set.range fun (ψ : AddChar (ZMod p) C) (x : ZMod p) => ψ x)).comap
            (LinearMap.funLeft R C fun x : ZMod p => a • x) := by
        rw [Submodule.span_le]
        rintro _ ⟨ψ, rfl⟩
        exact Submodule.subset_span ⟨ψ.mulShift a, rfl⟩
      exact this hg
    · have : Nontrivial (AddChar (ZMod p) C) := e.symm.nontrivial
      obtain ⟨ψ, hψ⟩ := exists_ne (1 : AddChar (ZMod p) C)
      have h1 : ψ 1 ≠ 1 := by
        intro h
        apply hψ
        ext y
        rw [← ZMod.natCast_zmod_val y, ← nsmul_one, AddChar.map_nsmul_eq_pow, h]
        simp
      refine ⟨∑ i ∈ Finset.range p, (1 - fun x => (ψ ^ i) x), Submodule.sum_mem _ fun i _ =>
        Submodule.sub_mem _ (multOrder' v hv e).one_mem (hmem _), by simp [Finset.sum_apply], ?_⟩
      have e3 := geom_sum_mul (ψ 1) p
      rw [hpow, sub_self, mul_eq_zero] at e3
      simp [Finset.sum_apply, Finset.sum_sub_distrib, AddChar.pow_apply,
        e3.resolve_right (sub_ne_zero.2 h1)]

end PositivityTheory.HtPt.Ri
