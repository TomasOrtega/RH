import Mathlib
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMemWpNormSubLtOne
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct Topology

namespace GlobalTheory.UnramifiedCrys

section Abstract

variable {p : ℕ} [hp : Fact p.Prime] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] {R : Type} [CommRing R] [IsDomain R] [CharP R p]
  (ρ : G →* (R ≃+* R))

def fixedPow (p : ℕ) (R : Type) [CommRing R] (m : ℕ) : Submonoid R where
  carrier := {y | y ^ p ^ m = y}
  one_mem' := one_pow _
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [mul_pow, ha, hb]

def fixer (p : ℕ) (m : ℕ) : Subgroup G where
  carrier := {g | ∀ y : R, y ^ p ^ m = y → ρ g y = y}
  one_mem' := fun y _ => by simp
  mul_mem' := fun {a b} ha hb y hy => by
    rw [map_mul, RingAut.mul_apply, hb y hy, ha y hy]
  inv_mem' := fun {a} ha y hy => by
    conv_lhs => rw [← ha y hy]
    rw [← RingAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, RingAut.one_apply]

omit [IsDomain R] [CharP R p] hp in
/- English proof (translation)
Proceed by induction on `b with`. Consider the case `zero => simp`. Consider the case `succ b ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]`.
-/
theorem pow_pow_mul {y : R} {a : ℕ} (h : y ^ p ^ a = y) (b : ℕ) : y ^ p ^ (a * b) = y := by
  induction b with
  | zero => simp
  | succ b ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

omit [CharP R p] in
/- English proof (translation)
Establish `h1 : 1 < p ^ m` using `Nat.one_lt_pow hm.ne' hp.out.one_lt`. Establish `hne : (Polynomial.X ^ p ^ m - Polynomial.X : Polynomial R) ≠ 0` using `(Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast h1)).ne_zero`. Use `(Polynomial.roots (Polynomial.X ^ p ^ m - Polynomial.X : Polynomial R)).toFinset.finite_toSet.subset ?_` and prove the remaining obligations. Introduce `y hy`. Simplify using `only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]`.

Conclude with `sub_eq_zero.2 hy`.
-/
theorem finite_fixedPow {m : ℕ} (hm : 0 < m) : {y : R | y ^ p ^ m = y}.Finite := by
  classical
  have h1 : 1 < p ^ m := Nat.one_lt_pow hm.ne' hp.out.one_lt
  have hne : (Polynomial.X ^ p ^ m - Polynomial.X : Polynomial R) ≠ 0 :=
    (Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast h1)).ne_zero
  refine (Polynomial.roots (Polynomial.X ^ p ^ m - Polynomial.X : Polynomial R)).toFinset.finite_toSet.subset ?_
  intro y hy
  simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot,
    Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
  exact sub_eq_zero.2 hy

omit [CharP R p] [CompactSpace G] in
/- English proof (translation)
Apply `Subgroup.isOpen_of_mem_nhds (g := 1)` to reduce the goal to its premises. Conclude with `((finite_fixedPow (p := p) (R := R) hm).eventually_all.2 (fun y hy => hopen y m hm hy)).mono fun g hg y hy => hg y hy`.
-/
theorem isOpen_fixer (hopen : ∀ (y : R) (m : ℕ), 0 < m → y ^ p ^ m = y → ∀ᶠ g in 𝓝 (1 : G), ρ g y = y)
    {m : ℕ} (hm : 0 < m) : IsOpen (fixer ρ p m : Set G) := by
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  exact ((finite_fixedPow (p := p) (R := R) hm).eventually_all.2
    (fun y hy => hopen y m hm hy)).mono fun g hg y hy => hg y hy

/- English proof (translation)
Take `⟨U, hU, hJU, hUe⟩` from `mem_nhdsSet_iff_exists.1 h0`. Take `⟨⟨m, hm⟩, hmU⟩` from `hU.isClosed_compl.isCompact.elim_directed_family_closed (fun m : {m : ℕ // 0 < m} => (fixer ρ p m.1 : Set G)) (fun m => Subgroup.isClosed_of_isOpen _ (isOpen_fixer ρ hopen m.2)) (by`. Rewrite using `[← Set.disjoint_iff_inter_eq_empty, Set.disjoint_left]`. Introduce `g hg hg'`. Conclude with `hg (hJU fun m hm => Set.mem_iInter.1 hg' ⟨m, hm⟩))`.

Use the proof step `(by`. Introduce `a b`. Use `⟨⟨a.1 * b.1, Nat.mul_pos a.2 b.2⟩, fun g hg y hy => hg y (pow_pow_mul hy _), fun g hg y hy => hg y ?_⟩` and prove the remaining obligations. Use `pow_pow_mul hy a.1` as an intermediate fact. Rewrite using `[mul_comm] at this)` and apply the resulting hypothesis.

Use `set N := fixer ρ p m with hN`. Establish `heN : ∀ g ∈ N, e g = 0` using `fun g hg => hUe (by`. Assume the negation of the conclusion as `hc`. Conclude with `Set.disjoint_left.1 (Set.disjoint_iff_inter_eq_empty.2 hmU) hc hg)`. Use `haveI : Finite (G ⧸ N) := Subgroup.quotient_finite_of_isOpen N (isOpen_fixer ρ hopen hm)`.

Use `letI : Fintype (G ⧸ N) := Fintype.ofFinite _`. Set `χ : G ⧸ N → (fixedPow p R m →* R)` to `fun x => (ρ x.out).toMonoidHom.comp (fixedPow p R m).subtype`. Establish `hχ : Function.Injective χ`. Introduce `x x' h`. Rewrite using `[← x.out_eq, ← x'.out_eq]`.

Apply `Quotient.sound` to reduce the goal to its premises. Apply `QuotientGroup.leftRel_apply.2` to reduce the goal to its premises. Introduce `y hy`. Establish `h1 : ρ x.out y = ρ x'.out y` using `DFunLike.congr_fun h ⟨y, hy⟩`. Rewrite using `[map_mul, RingAut.mul_apply, ← h1, ← RingAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, RingAut.one_apply]`.

Establish `hli` using `(linearIndependent_monoidHom (fixedPow p R m) R).comp χ hχ`. Choose the witnesses or unpack the hypotheses as in `⟨θ, hθ⟩ : ∃ θ : fixedPow p R m, ∑ x : G ⧸ N, ρ x.out θ ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Use `Fintype.linearIndependent_iff.1 hli (fun _ => 1) (by` as an intermediate fact.

Use function extensionality and compare the values at `θ`. Simplify using `only [one_smul, Finset.sum_apply, Function.comp, Pi.zero_apply]`. Conclude with `hc θ) (QuotientGroup.mk 1)`. Conclude with `one_ne_zero this`. Establish `hθm : (θ : R) ^ p ^ m = θ` using `θ.2`.

Establish `hsum : ∀ (f : G → R), (∀ g, ∀ n ∈ N, f (g * n) = f g) → ∀ g, ∑ x : G ⧸ N, f (g * x.out) = ∑ x : G ⧸ N, f x.out`. Introduce `f hf g`. Use `Fintype.sum_equiv (MulAction.toPerm g) _ _ fun x => ?_` and prove the remaining obligations. Take `⟨n, hn⟩` from `QuotientGroup.mk_out_eq_mul N (g * x.out)`. Establish `: MulAction.toPerm g x = QuotientGroup.mk (g * x.out)`.

Rewrite using `[MulAction.toPerm_apply]`. Use `conv_lhs => rw [← x.out_eq]`. Both sides reduce to the same expression. Rewrite using `[this, hn, hf _ _ n.2]`. Use `set t := ∑ x : G ⧸ N, ρ x.out θ with ht`.

Establish `hθN : ∀ g, ∀ n ∈ N, ρ (g * n) θ = ρ g θ` using `fun g n hn => by`. Rewrite using `[map_mul, RingAut.mul_apply, hn θ hθm]`. Establish `htg : ∀ g, ρ g t = t` using `fun g => by`. Rewrite using `[ht, map_sum, ← hsum (fun g => ρ g θ) hθN g]`. Simplify using `only [map_mul, RingAut.mul_apply]`.

Establish `htq : t ^ p ^ m = t`. Rewrite using `[ht, sum_pow_char_pow]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[← map_pow, hθm]`. Establish `h1 : 1 < p ^ m` using `Nat.one_lt_pow hm.ne' hp.out.one_lt`.

Establish `hu : t ^ (p ^ m - 2) * t = 1`. Apply `mul_right_cancel₀ hθ` to reduce the goal to its premises. Rewrite using `[← pow_succ, ← pow_succ, one_mul, show p ^ m - 2 + 1 + 1 = p ^ m by omega, htq]`. Use `⟨-(t ^ (p ^ m - 2) * ∑ x : G ⧸ N, e x.out * ρ x.out θ), fun g => ?_⟩` and prove the remaining obligations. Establish `h2` using `hsum (fun g => e g * ρ g θ) (fun g n hn => by`.

Simplify using `only [he, heN n hn, map_zero, add_zero, hθN g n hn]) g`. Establish `h3 : ρ g (∑ x : G ⧸ N, e x.out * ρ x.out θ) = ∑ x : G ⧸ N, e x.out * ρ x.out θ - e g * t` using `by conv_rhs => rw [← h2, ← htg g, ht]`. Rewrite using `[map_sum, map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Simplify using `only [he, map_mul, RingAut.mul_apply]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_neg, map_mul, map_pow, htg, h3]`. Take the linear combination `(-e g) * hu`.
-/
theorem exists_coboundary
    (hopen : ∀ (y : R) (m : ℕ), 0 < m → y ^ p ^ m = y → ∀ᶠ g in 𝓝 (1 : G), ρ g y = y)
    (e : G → R) (he : ∀ g h, e (g * h) = e g + ρ g (e h))
    (h0 : ∀ᶠ g in 𝓝ˢ {g : G | ∀ m, 0 < m → g ∈ fixer ρ p m}, e g = 0) :
    ∃ β : R, ∀ g, e g = ρ g β - β := by
  classical
  obtain ⟨U, hU, hJU, hUe⟩ := mem_nhdsSet_iff_exists.1 h0
  obtain ⟨⟨m, hm⟩, hmU⟩ := hU.isClosed_compl.isCompact.elim_directed_family_closed
    (fun m : {m : ℕ // 0 < m} => (fixer ρ p m.1 : Set G))
    (fun m => Subgroup.isClosed_of_isOpen _ (isOpen_fixer ρ hopen m.2))
    (by
      rw [← Set.disjoint_iff_inter_eq_empty, Set.disjoint_left]
      intro g hg hg'
      exact hg (hJU fun m hm => Set.mem_iInter.1 hg' ⟨m, hm⟩))
    (by
      intro a b
      refine ⟨⟨a.1 * b.1, Nat.mul_pos a.2 b.2⟩, fun g hg y hy => hg y (pow_pow_mul hy _),
        fun g hg y hy => hg y ?_⟩
      have := pow_pow_mul hy a.1
      rwa [mul_comm] at this)
  set N := fixer ρ p m with hN
  have heN : ∀ g ∈ N, e g = 0 := fun g hg => hUe (by
    by_contra hc
    exact Set.disjoint_left.1 (Set.disjoint_iff_inter_eq_empty.2 hmU) hc hg)
  haveI : Finite (G ⧸ N) := Subgroup.quotient_finite_of_isOpen N (isOpen_fixer ρ hopen hm)
  letI : Fintype (G ⧸ N) := Fintype.ofFinite _
  let χ : G ⧸ N → (fixedPow p R m →* R) := fun x =>
    (ρ x.out).toMonoidHom.comp (fixedPow p R m).subtype
  have hχ : Function.Injective χ := by
    intro x x' h
    rw [← x.out_eq, ← x'.out_eq]
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.2
    intro y hy
    have h1 : ρ x.out y = ρ x'.out y := DFunLike.congr_fun h ⟨y, hy⟩
    rw [map_mul, RingAut.mul_apply, ← h1, ← RingAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      RingAut.one_apply]
  have hli := (linearIndependent_monoidHom (fixedPow p R m) R).comp χ hχ
  obtain ⟨θ, hθ⟩ : ∃ θ : fixedPow p R m, ∑ x : G ⧸ N, ρ x.out θ ≠ 0 := by
    by_contra hc
    push Not at hc
    have := Fintype.linearIndependent_iff.1 hli (fun _ => 1) (by
      funext θ
      simp only [one_smul, Finset.sum_apply, Function.comp, Pi.zero_apply]
      exact hc θ) (QuotientGroup.mk 1)
    exact one_ne_zero this
  have hθm : (θ : R) ^ p ^ m = θ := θ.2

  have hsum : ∀ (f : G → R), (∀ g, ∀ n ∈ N, f (g * n) = f g) → ∀ g,
      ∑ x : G ⧸ N, f (g * x.out) = ∑ x : G ⧸ N, f x.out := by
    intro f hf g
    refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun x => ?_
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N (g * x.out)
    have : MulAction.toPerm g x = QuotientGroup.mk (g * x.out) := by
      rw [MulAction.toPerm_apply]
      conv_lhs => rw [← x.out_eq]
      rfl
    rw [this, hn, hf _ _ n.2]
  set t := ∑ x : G ⧸ N, ρ x.out θ with ht
  have hθN : ∀ g, ∀ n ∈ N, ρ (g * n) θ = ρ g θ := fun g n hn => by
    rw [map_mul, RingAut.mul_apply, hn θ hθm]
  have htg : ∀ g, ρ g t = t := fun g => by
    rw [ht, map_sum, ← hsum (fun g => ρ g θ) hθN g]
    simp only [map_mul, RingAut.mul_apply]
  have htq : t ^ p ^ m = t := by
    rw [ht, sum_pow_char_pow]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← map_pow, hθm]
  have h1 : 1 < p ^ m := Nat.one_lt_pow hm.ne' hp.out.one_lt
  have hu : t ^ (p ^ m - 2) * t = 1 := by
    apply mul_right_cancel₀ hθ
    rw [← pow_succ, ← pow_succ, one_mul, show p ^ m - 2 + 1 + 1 = p ^ m by omega, htq]
  refine ⟨-(t ^ (p ^ m - 2) * ∑ x : G ⧸ N, e x.out * ρ x.out θ), fun g => ?_⟩
  have h2 := hsum (fun g => e g * ρ g θ) (fun g n hn => by
    simp only [he, heN n hn, map_zero, add_zero, hθN g n hn]) g
  have h3 : ρ g (∑ x : G ⧸ N, e x.out * ρ x.out θ) =
      ∑ x : G ⧸ N, e x.out * ρ x.out θ - e g * t := by
    conv_rhs => rw [← h2, ← htg g, ht]
    rw [map_sum, map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [he, map_mul, RingAut.mul_apply]
    ring
  rw [map_neg, map_mul, map_pow, htg, h3]
  linear_combination (-e g) * hu

end Abstract

section Witt

variable {p : ℕ} [hp : Fact p.Prime] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] {R : Type} [CommRing R] [IsDomain R] [CharP R p]
  [PerfectRing R p] (ρ : G →* (R ≃+* R))

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [IsDomain R] [CharP R p]
  [PerfectRing R p] in
/- English proof (translation)
Use extensionality with `n`. Simplify using `[WittVector.map_coeff]`.
-/
theorem wittMap_mul (g h : G) (x : WittVector p R) :
    WittVector.map (ρ (g * h)).toRingHom x =
      WittVector.map (ρ g).toRingHom (WittVector.map (ρ h).toRingHom x) := by
  ext n
  simp [WittVector.map_coeff]

/- English proof (translation)
Use `choose d hd using hd`. Establish `hp0 : (p : WittVector p R) ^ n ≠ 0` using `pow_ne_zero _ (WittVector.p_nonzero p R)`. Establish `hdc : ∀ g h, d (g * h) = d g + WittVector.map (ρ g).toRingHom (d h)`. Introduce `g h`. Apply `mul_left_cancel₀ hp0` to reduce the goal to its premises.

Establish `h1` using `congrArg (WittVector.map (ρ g).toRingHom) (hd h)`. Rewrite `h1` using `[map_mul, map_pow, map_natCast, map_sub, map_sub, map_zlW, ← wittMap_mul]`. Rewrite using `[mul_add, ← hd, ← hd, ← h1, hadd, map_add]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsmall : ∀ᶠ g in 𝓝ˢ {g : G | ∀ m, 0 < m → g ∈ fixer ρ p m}, (p : ℤ_[p]) ^ (n + 1) ∣ c g`.

Rewrite using `[eventually_nhdsSet_iff_forall]`. Introduce `x hx`. Establish `h1 : ∀ᶠ g in 𝓝 x, ‖c g‖ < (p : ℝ) ^ (-((n + 1 : ℕ) : ℤ))`. Apply `hc.norm.continuousAt.eventually_lt continuousAt_const` to reduce the goal to its premises. Rewrite using `[hJ x hx, norm_zero]`.

Use `hp.out.pos` as an intermediate fact. Check the signs of the components of the expression. Use `h1.mono fun g hg => ?_` and prove the remaining obligations. Conclude with `Ideal.mem_span_singleton.1 ((PadicInt.norm_le_pow_iff_mem_span_pow _ _).1 hg.le)`. Establish `he0 : ∀ᶠ g in 𝓝ˢ {g : G | ∀ m, 0 < m → g ∈ fixer ρ p m}, (d g).coeff 0 = 0` using `by filter_upwards [hb, hsmall] with g h1 h2`.

Take `⟨z, hz⟩` from `h2`. Establish `h3` using `hd g`. Rewrite `h3` using `[h1, hz, map_mul, map_pow, map_natCast]`. Establish `h4 : d g = (p : WittVector p R) * -(zlW p R z)`. Apply `mul_left_cancel₀ hp0` to reduce the goal to its premises.

Rewrite using `[← h3]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← WittVector.mem_span_p_iff_coeff_zero_eq_zero, Ideal.mem_span_singleton]`. Conclude with `⟨_, h4⟩`. Take `⟨β, hβ⟩` from `exists_coboundary ρ hopen (fun g => (d g).coeff 0) (fun g h => by`.

Use `congrArg WittVector.constantCoeff (hdc g h)` as an intermediate fact. Rewrite `this` using `[map_add]`. Simplify `this) he0` using `[WittVector.map_coeff]`. Use `⟨b - (p : WittVector p R) ^ n * WittVector.teichmuller p β, ⟨_, sub_sub_cancel _ _⟩, ?_, fun g => ?_⟩` and prove the remaining obligations. Use `filter_upwards [hb, he0] with g h1 h2`.

Establish `h3 : (ρ g).toRingHom β = β`. Use `hβ g` as an intermediate fact. Rewrite `this` using `[h2]`. Conclude with `sub_eq_zero.1 this.symm`. Rewrite using `[map_sub, map_mul, map_pow, map_natCast, h1, WittVector.map_teichmuller, h3]`.

Establish `h1 : (p : WittVector p R) ∣ d g - (WittVector.teichmuller p ((ρ g).toRingHom β) - WittVector.teichmuller p β)`. Rewrite using `[← Ideal.mem_span_singleton, WittVector.mem_span_p_iff_coeff_zero_eq_zero]`. Rewrite using `[← WittVector.constantCoeff_apply, map_sub, map_sub]`. Simplify using `only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]`. Conclude with `sub_eq_zero.2 (hβ g)`.

Take `⟨w, hw⟩` from `h1`. Use `⟨w, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, map_mul, map_pow, map_natCast, WittVector.map_teichmuller, pow_succ, mul_assoc, ← hw, mul_sub, ← hd]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem approx_step
    (hopen : ∀ (y : R) (m : ℕ), 0 < m → y ^ p ^ m = y → ∀ᶠ g in 𝓝 (1 : G), ρ g y = y)
    (c : G → ℤ_[p]) (hc : Continuous c) (hadd : ∀ g h, c (g * h) = c g + c h)
    (hJ : ∀ g, (∀ m, 0 < m → g ∈ fixer ρ p m) → c g = 0) (n : ℕ) (b : WittVector p R)
    (hb : ∀ᶠ g in 𝓝ˢ {g : G | ∀ m, 0 < m → g ∈ fixer ρ p m}, WittVector.map (ρ g).toRingHom b = b)
    (hd : ∀ g, (p : WittVector p R) ^ n ∣ WittVector.map (ρ g).toRingHom b - b - zlW p R (c g)) :
    ∃ b' : WittVector p R, (p : WittVector p R) ^ n ∣ b - b' ∧
      (∀ᶠ g in 𝓝ˢ {g : G | ∀ m, 0 < m → g ∈ fixer ρ p m},
        WittVector.map (ρ g).toRingHom b' = b') ∧
      ∀ g, (p : WittVector p R) ^ (n + 1) ∣
        WittVector.map (ρ g).toRingHom b' - b' - zlW p R (c g) := by
  choose d hd using hd
  have hp0 : (p : WittVector p R) ^ n ≠ 0 := pow_ne_zero _ (WittVector.p_nonzero p R)
  have hdc : ∀ g h, d (g * h) = d g + WittVector.map (ρ g).toRingHom (d h) := by
    intro g h
    apply mul_left_cancel₀ hp0
    have h1 := congrArg (WittVector.map (ρ g).toRingHom) (hd h)
    rw [map_mul, map_pow, map_natCast, map_sub, map_sub, map_zlW, ← wittMap_mul] at h1
    rw [mul_add, ← hd, ← hd, ← h1, hadd, map_add]
    ring
  have hsmall : ∀ᶠ g in 𝓝ˢ {g : G | ∀ m, 0 < m → g ∈ fixer ρ p m},
      (p : ℤ_[p]) ^ (n + 1) ∣ c g := by
    rw [eventually_nhdsSet_iff_forall]
    intro x hx
    have h1 : ∀ᶠ g in 𝓝 x, ‖c g‖ < (p : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by
      apply hc.norm.continuousAt.eventually_lt continuousAt_const
      rw [hJ x hx, norm_zero]
      have := hp.out.pos
      positivity
    refine h1.mono fun g hg => ?_
    exact Ideal.mem_span_singleton.1 ((PadicInt.norm_le_pow_iff_mem_span_pow _ _).1 hg.le)
  have he0 : ∀ᶠ g in 𝓝ˢ {g : G | ∀ m, 0 < m → g ∈ fixer ρ p m}, (d g).coeff 0 = 0 := by
    filter_upwards [hb, hsmall] with g h1 h2
    obtain ⟨z, hz⟩ := h2
    have h3 := hd g
    rw [h1, hz, map_mul, map_pow, map_natCast] at h3
    have h4 : d g = (p : WittVector p R) * -(zlW p R z) := by
      apply mul_left_cancel₀ hp0
      rw [← h3]; ring
    rw [← WittVector.mem_span_p_iff_coeff_zero_eq_zero, Ideal.mem_span_singleton]
    exact ⟨_, h4⟩
  obtain ⟨β, hβ⟩ := exists_coboundary ρ hopen (fun g => (d g).coeff 0) (fun g h => by
    have := congrArg WittVector.constantCoeff (hdc g h)
    rw [map_add] at this
    simpa [WittVector.map_coeff] using this) he0
  refine ⟨b - (p : WittVector p R) ^ n * WittVector.teichmuller p β, ⟨_, sub_sub_cancel _ _⟩, ?_,
    fun g => ?_⟩
  · filter_upwards [hb, he0] with g h1 h2
    have h3 : (ρ g).toRingHom β = β := by
      have := hβ g
      rw [h2] at this
      exact sub_eq_zero.1 this.symm
    rw [map_sub, map_mul, map_pow, map_natCast, h1, WittVector.map_teichmuller, h3]
  · have h1 : (p : WittVector p R) ∣ d g - (WittVector.teichmuller p ((ρ g).toRingHom β) -
        WittVector.teichmuller p β) := by
      rw [← Ideal.mem_span_singleton, WittVector.mem_span_p_iff_coeff_zero_eq_zero]
      rw [← WittVector.constantCoeff_apply, map_sub, map_sub]
      simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
      exact sub_eq_zero.2 (hβ g)
    obtain ⟨w, hw⟩ := h1
    refine ⟨w, ?_⟩
    rw [map_sub, map_mul, map_pow, map_natCast, WittVector.map_teichmuller, pow_succ, mul_assoc,
      ← hw, mul_sub, ← hd]
    ring

/- English proof (translation)
Set `P : ℕ → WittVector p R → Prop` to `fun n b => (∀ᶠ g in 𝓝ˢ {g : G | ∀ m, 0 < m → g ∈ fixer ρ p m}, WittVector.map (ρ g).toRingHom b = b) ∧ ∀ g, (p : WittVector p R) ^ n ∣ WittVector.map (ρ g).toRingHom b - b - zlW p R (c g)`. Establish `hstep : ∀ n (b : {b // P n b}), ∃ b' : {b // P (n + 1) b}, (p : WittVector p R) ^ n ∣ b.1 - b'.1` using `fun n b => by`. Take `⟨b', h1, h2, h3⟩` from `approx_step ρ hopen c hc hadd hJ n b.1 b.2.1 b.2.2`. Conclude with `⟨⟨b', h2, h3⟩, h1⟩`. Use `choose F hF using hstep`.

Set `s : ∀ n, {b // P n b}` to `fun n => Nat.rec (motive := fun n => {b // P n b}) ⟨0, Filter.Eventually.of_forall fun g => map_zero _, fun g => by simp⟩ F n`. Establish `hs : ∀ n, (p : WittVector p R) ^ n ∣ (s n).1 - (s (n + 1)).1` using `fun n => hF n (s n)`. Establish `hsm : ∀ (n : ℕ) (x y : WittVector p R), x ≡ y [SMOD (Ideal.span {(p : WittVector p R)} ^ n • ⊤ : Submodule (WittVector p R) _)] ↔ (p : WittVector p R) ^ n ∣ x - y` using `fun n x y => by`. Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Establish `hcomp` using `WittVector.isAdicCompleteIdealSpanP (p := p) (k := R)`.

Take `⟨L, hL⟩` from `hcomp.toIsPrecomplete.prec (f := fun n => (s n).1) (by`. Introduce `m n hmn`. Rewrite using `[hsm]`. Proceed by induction on `n, hmn using Nat.le_induction with`. Consider the case `base => simp`.

Consider the case `succ n hmn ih`. Use `dvd_add ih ((pow_dvd_pow _ hmn).trans (hs n))` as an intermediate fact. Rewrite using `[sub_add_sub_cancel] at this)` and apply the resulting hypothesis. Use `⟨L, fun g => sub_eq_zero.1 (hcomp.toIsHausdorff.haus _ fun n => ?_)⟩` and prove the remaining obligations. Rewrite using `[hsm, sub_zero]`.

Establish `h1` using `(hsm _ _ _).1 (hL n)`. Establish `h2` using `map_dvd (WittVector.map (ρ g).toRingHom) h1`. Rewrite `h2` using `[map_pow, map_natCast, map_sub]`. Establish `h3` using `dvd_add (dvd_sub ((s n).2.2 g) h2) h1`. Use `h3 using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_witt_coboundary
    (hopen : ∀ (y : R) (m : ℕ), 0 < m → y ^ p ^ m = y → ∀ᶠ g in 𝓝 (1 : G), ρ g y = y)
    (c : G → ℤ_[p]) (hc : Continuous c) (hadd : ∀ g h, c (g * h) = c g + c h)
    (hJ : ∀ g, (∀ m, 0 < m → g ∈ fixer ρ p m) → c g = 0) :
    ∃ b : WittVector p R, ∀ g, WittVector.map (ρ g).toRingHom b - b = zlW p R (c g) := by
  let P : ℕ → WittVector p R → Prop := fun n b =>
    (∀ᶠ g in 𝓝ˢ {g : G | ∀ m, 0 < m → g ∈ fixer ρ p m}, WittVector.map (ρ g).toRingHom b = b) ∧
      ∀ g, (p : WittVector p R) ^ n ∣ WittVector.map (ρ g).toRingHom b - b - zlW p R (c g)
  have hstep : ∀ n (b : {b // P n b}), ∃ b' : {b // P (n + 1) b},
      (p : WittVector p R) ^ n ∣ b.1 - b'.1 := fun n b => by
    obtain ⟨b', h1, h2, h3⟩ := approx_step ρ hopen c hc hadd hJ n b.1 b.2.1 b.2.2
    exact ⟨⟨b', h2, h3⟩, h1⟩
  choose F hF using hstep
  let s : ∀ n, {b // P n b} := fun n => Nat.rec (motive := fun n => {b // P n b})
    ⟨0, Filter.Eventually.of_forall fun g => map_zero _, fun g => by simp⟩ F n
  have hs : ∀ n, (p : WittVector p R) ^ n ∣ (s n).1 - (s (n + 1)).1 := fun n => hF n (s n)
  have hsm : ∀ (n : ℕ) (x y : WittVector p R),
      x ≡ y [SMOD (Ideal.span {(p : WittVector p R)} ^ n • ⊤ : Submodule (WittVector p R) _)] ↔
        (p : WittVector p R) ^ n ∣ x - y := fun n x y => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  have hcomp := WittVector.isAdicCompleteIdealSpanP (p := p) (k := R)
  obtain ⟨L, hL⟩ := hcomp.toIsPrecomplete.prec (f := fun n => (s n).1) (by
    intro m n hmn
    rw [hsm]
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := dvd_add ih ((pow_dvd_pow _ hmn).trans (hs n))
      rwa [sub_add_sub_cancel] at this)
  refine ⟨L, fun g => sub_eq_zero.1 (hcomp.toIsHausdorff.haus _ fun n => ?_)⟩
  rw [hsm, sub_zero]
  have h1 := (hsm _ _ _).1 (hL n)
  have h2 := map_dvd (WittVector.map (ρ g).toRingHom) h1
  rw [map_pow, map_natCast, map_sub] at h2
  have h3 := dvd_add (dvd_sub ((s n).2.2 g) h2) h1
  convert h3 using 1
  ring

end Witt

section Tilt

variable {l : ℕ} [hl : Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

/- English proof (translation)
The claim follows from `GlobalTheory.RingBasics.mem_OC x`.
-/
theorem mem_OC {x : ℂ_[l]} : x ∈ PadicComplexInt l ↔ ‖x‖ ≤ 1 := GlobalTheory.RingBasics.mem_OC x

/- English proof (translation)
Establish `key : ∀ (z : OCb l) (n : ℕ), PreTilt.coeff n z ^ l ^ n = PreTilt.coeff 0 z`. Introduce `z n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`.

Rewrite using `[pow_succ', pow_mul, ← ih]`. Use `congr 1`. Conclude with `Perfection.coeff_pow_p' (R := ModP (OC l) l) z n`. Establish `key2 : ∀ (z : OCb l), z ^ l ^ m = z → ∀ n : ℕ, PreTilt.coeff n z = PreTilt.coeff 0 z ^ l ^ ((m - 1) * n)`. Introduce `z hz n`.

Rewrite using `[← key z n, ← pow_mul, ← pow_add, ← map_pow, show n + (m - 1) * n = m * n by`. Take `⟨k, rfl⟩ : ∃ k, m = k + 1` from `⟨m - 1, by omega⟩`. Simplify using `only [Nat.add_sub_cancel]`. Use the proof step `ring, pow_pow_mul hz]`. Use `Perfection.ext (R := ModP (OC l) l) fun n => ?_` and prove the remaining obligations.

Rewrite using `[← PreTilt.coeff_def, ← PreTilt.coeff_def, key2 y hy, key2 y' hy', h]`.
-/
theorem eq_of_coeff_zero {m : ℕ} (hm : 0 < m) {y y' : OCb l} (hy : y ^ l ^ m = y)
    (hy' : y' ^ l ^ m = y') (h : PreTilt.coeff 0 y = PreTilt.coeff 0 y') : y = y' := by
  have key : ∀ (z : OCb l) (n : ℕ), PreTilt.coeff n z ^ l ^ n = PreTilt.coeff 0 z := by
    intro z n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', pow_mul, ← ih]
      congr 1
      exact Perfection.coeff_pow_p' (R := ModP (OC l) l) z n
  have key2 : ∀ (z : OCb l), z ^ l ^ m = z → ∀ n : ℕ,
      PreTilt.coeff n z = PreTilt.coeff 0 z ^ l ^ ((m - 1) * n) := by
    intro z hz n
    rw [← key z n, ← pow_mul, ← pow_add, ← map_pow,
      show n + (m - 1) * n = m * n by
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        simp only [Nat.add_sub_cancel]; ring, pow_pow_mul hz]
  refine Perfection.ext (R := ModP (OC l) l) fun n => ?_
  rw [← PreTilt.coeff_def, ← PreTilt.coeff_def, key2 y hy, key2 y' hy', h]

/- English proof (translation)
Take `⟨w, hw⟩` from `Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h)`. Establish `h1` using `congrArg (fun t : OC l => (t : ℂ_[l])) hw`. Move the coercions through the operations in `at h1`. Rewrite using `[h1, norm_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) GlobalTheory.ResidueRoot.norm_p_lt_one (mem_OC.1 w.2)`.
-/
theorem norm_lt_one_of_mk_eq {a b : OC l}
    (h : Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) a =
      Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) b) : ‖(a : ℂ_[l]) - b‖ < 1 := by
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h)
  have h1 := congrArg (fun t : OC l => (t : ℂ_[l])) hw
  push_cast at h1
  rw [h1, norm_mul]
  exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) GlobalTheory.ResidueRoot.norm_p_lt_one
    (mem_OC.1 w.2)

/- English proof (translation)
Take `⟨z, hz⟩` from `Ideal.Quotient.mk_surjective (I := Ideal.span {((l : ℕ) : OC l)}) (PreTilt.coeff 0 y)`. Establish `hl0 : (l : ℂ_[l]) ≠ 0` using `Nat.cast_ne_zero.2 hl.out.ne_zero`. Take `⟨x, hx⟩` from `Metric.denseRange_iff.1 (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl l)) (z : ℂ_[l]) _ (norm_pos_iff.2 hl0)`. Rewrite `hx` using `[dist_eq_norm]`. Establish `hw : ‖((z : ℂ_[l]) - x) / l‖ ≤ 1`.

Rewrite using `[norm_div]`. Conclude with `(div_le_one (norm_pos_iff.2 hl0)).2 hx.le`. Set `w : OC l` to `⟨_, mem_OC.2 hw⟩`. Establish `hx' : ((z - (l : OC l) * w : OC l) : ℂ_[l]) = (x : ℂ_[l])`. Use `push_cast`.

Simplify using `only [w]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hy0 : PreTilt.coeff 0 y = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (z - (l : OC l) * w)`. Rewrite using `[← hz]`.

Conclude with `Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 ⟨w, by ring⟩)`. Use `filter_upwards [(stabilizer_isOpen_of_isIntegral (K := ℚ_[l]) x).mem_nhds (one_mem _)] with g hg`. Take `⟨y', h1, h2⟩` from `AI.actT_coeff g y 0 _ hy0`. Establish `hg' : g x = x` using `hg`. Rewrite `h1` using `[hx', AI.actC_ext, hg', ← hx']`.

Use `eq_of_coeff_zero hm (by rw [← map_pow, hy]) hy ?_` and prove the remaining obligations. Rewrite using `[h2, hy0, Subtype.ext h1]`.
-/
theorem eventually_actT_eq (y : OCb l) (m : ℕ) (hm : 0 < m) (hy : y ^ l ^ m = y) :
    ∀ᶠ g in 𝓝 (1 : GQ l), AI.actT g y = y := by
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {((l : ℕ) : OC l)})
    (PreTilt.coeff 0 y)
  have hl0 : (l : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  obtain ⟨x, hx⟩ := Metric.denseRange_iff.1
    (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl l)) (z : ℂ_[l]) _ (norm_pos_iff.2 hl0)
  rw [dist_eq_norm] at hx
  have hw : ‖((z : ℂ_[l]) - x) / l‖ ≤ 1 := by
    rw [norm_div]; exact (div_le_one (norm_pos_iff.2 hl0)).2 hx.le
  let w : OC l := ⟨_, mem_OC.2 hw⟩
  have hx' : ((z - (l : OC l) * w : OC l) : ℂ_[l]) = (x : ℂ_[l]) := by
    push_cast
    simp only [w]
    field_simp
    ring
  have hy0 : PreTilt.coeff 0 y =
      Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (z - (l : OC l) * w) := by
    rw [← hz]
    exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 ⟨w, by ring⟩)
  filter_upwards [(stabilizer_isOpen_of_isIntegral (K := ℚ_[l]) x).mem_nhds (one_mem _)] with g hg
  obtain ⟨y', h1, h2⟩ := AI.actT_coeff g y 0 _ hy0
  have hg' : g x = x := hg
  rw [hx', AI.actC_ext, hg', ← hx'] at h1
  refine eq_of_coeff_zero hm (by rw [← map_pow, hy]) hy ?_
  rw [h2, hy0, Subtype.ext h1]

/- English proof (translation)
Establish `hgx : ‖g x‖ = ‖x‖`. Rewrite using `[← PadicComplex.norm_extends, ← AI.actC_ext, AI.actC_norm, PadicComplex.norm_extends]`. Break down `hx.lt_or_eq with h | h` into its components or cases. Rewrite using `[sub_eq_add_neg]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hgx ▸ h) (by rwa [norm_neg]))`.

Take `⟨n, hn, hyn⟩` from `GlobalTheory.ResidueRoot.exists_pow_alg x h`. Take `⟨k, m, hm, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hn.ne' l hl.out.ne_one`. Establish `hm0 : 0 < m` using `Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero l))`. Establish `h3 : ‖((x : ℂ_[l]) ^ m) ^ l ^ k - 1‖ < 1`. Rewrite `hyn` using `[← PadicComplex.norm_extends, PadicComplex.coe_eq, map_sub, map_pow, map_one, ← PadicComplex.coe_eq]`.

Rewrite using `[← pow_mul, mul_comm]` and apply the resulting hypothesis. Establish `h4` using `GlobalTheory.ResidueRoot.sub_one_lt_of_pow_p_pow k (by rw [norm_pow, PadicComplex.norm_extends, h, one_pow]) h3`. Take `⟨ζ, hζ, h5⟩` from `GlobalTheory.ResidueRoot.exists_root hm0 h4`. Establish `hζ1 : ‖ζ‖ ≤ 1`. Use `congrArg norm hζ` as an intermediate fact.

Rewrite `this` using `[norm_pow, norm_one]`. Conclude with `((pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0.ne').1 this).le`. Set `Z : OC l` to `⟨ζ, mem_OC.2 hζ1⟩`. Establish `hZm : Z ^ m = 1` using `Subtype.ext hζ`. Establish `hZ : Z ^ l ^ m.totient = Z`.

Establish `h6` using `Nat.ModEq.pow_totient ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hm)`. Rewrite using `[pow_eq_pow_mod _ hZm, h6, ← pow_eq_pow_mod _ hZm, pow_one]`. Take `⟨r, hr⟩ : ∃ r, m.totient = r + 1` from `⟨m.totient - 1, by`. Use `Nat.totient_pos.2 hm0` as an intermediate fact. Use the proof step `omega⟩`.

Rewrite `hZ` using `[hr]`. Set `y : OCb l` to `⟨fun j => Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (Z ^ l ^ (r * j)), fun j => by show (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (Z ^ l ^ (r * (j + 1)))) ^ l = _`. Rewrite using `[← map_pow, ← pow_mul, ← pow_succ, show r * (j + 1) + 1 = (r + 1) + r * j by ring, pow_add, pow_mul, hZ]⟩`. Establish `hyc : ∀ j, PreTilt.coeff j y = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (Z ^ l ^ (r * j))` using `fun j => rfl`. Establish `hy : y ^ l ^ (r + 1) = y`.

Use `Perfection.ext (R := ModP (OC l) l) fun j => ?_` and prove the remaining obligations. Rewrite using `[← PreTilt.coeff_def, ← PreTilt.coeff_def, map_pow, hyc]`. Use `show (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (Z ^ l ^ (r * j))) ^ l ^ (r + 1) = _`. Rewrite using `[← map_pow, ← pow_mul, mul_comm, pow_mul, hZ]`. Establish `hy0 : PreTilt.coeff 0 y = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) Z`.

Rewrite using `[hyc]`. Simplify using the standard rewrite rules. Take `⟨y', h1, h2⟩` from `AI.actT_coeff g y 0 _ hy0`. Rewrite `h2` using `[hg _ (Nat.succ_pos r) y hy, hy0]`. Establish `h7` using `norm_lt_one_of_mk_eq h2`.

Rewrite `h7` using `[h1]`. Establish `h8 : ‖AI.actC g ((x : ℂ_[l]) - ζ)‖ < 1` using `by rwa [AI.actC_norm]`. Rewrite using `[← PadicComplex.norm_extends, PadicComplex.coe_eq, map_sub, ← PadicComplex.coe_eq, ← PadicComplex.coe_eq, ← AI.actC_ext]`. Establish `h9` using `GlobalTheory.ResidueRoot.norm_add_lt_one h8 (GlobalTheory.ResidueRoot.norm_add_lt_one (by rw [norm_neg]; exact h7 : ‖-(ζ - AI.actC g ζ)‖ < 1) (by rw [norm_neg]; exact h5 : ‖-((x : ℂ_[l]) - ζ)‖ < 1))`. Use `h9 using 2` and compare the differences between its conclusion and the goal.

Rewrite using `[map_sub]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_sub_lt_one_of_fix (g : GQ l)
    (hg : ∀ m, 0 < m → ∀ y : OCb l, y ^ l ^ m = y → AI.actT g y = y) (x : Om l) (hx : ‖x‖ ≤ 1) :
    ‖g x - x‖ < 1 := by
  have hgx : ‖g x‖ = ‖x‖ := by
    rw [← PadicComplex.norm_extends, ← AI.actC_ext, AI.actC_norm, PadicComplex.norm_extends]
  rcases hx.lt_or_eq with h | h
  · rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hgx ▸ h) (by rwa [norm_neg]))
  obtain ⟨n, hn, hyn⟩ := GlobalTheory.ResidueRoot.exists_pow_alg x h
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' l hl.out.ne_one
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero l))
  have h3 : ‖((x : ℂ_[l]) ^ m) ^ l ^ k - 1‖ < 1 := by
    rw [← PadicComplex.norm_extends, PadicComplex.coe_eq, map_sub, map_pow, map_one,
      ← PadicComplex.coe_eq] at hyn
    rwa [← pow_mul, mul_comm]
  have h4 := GlobalTheory.ResidueRoot.sub_one_lt_of_pow_p_pow k
    (by rw [norm_pow, PadicComplex.norm_extends, h, one_pow]) h3
  obtain ⟨ζ, hζ, h5⟩ := GlobalTheory.ResidueRoot.exists_root hm0 h4
  have hζ1 : ‖ζ‖ ≤ 1 := by
    have := congrArg norm hζ
    rw [norm_pow, norm_one] at this
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0.ne').1 this).le
  let Z : OC l := ⟨ζ, mem_OC.2 hζ1⟩
  have hZm : Z ^ m = 1 := Subtype.ext hζ
  have hZ : Z ^ l ^ m.totient = Z := by
    have h6 := Nat.ModEq.pow_totient ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hm)
    rw [pow_eq_pow_mod _ hZm, h6, ← pow_eq_pow_mod _ hZm, pow_one]
  obtain ⟨r, hr⟩ : ∃ r, m.totient = r + 1 := ⟨m.totient - 1, by
    have := Nat.totient_pos.2 hm0
    omega⟩
  rw [hr] at hZ
  let y : OCb l := ⟨fun j => Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (Z ^ l ^ (r * j)),
    fun j => by
      show (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (Z ^ l ^ (r * (j + 1)))) ^ l = _
      rw [← map_pow, ← pow_mul, ← pow_succ, show r * (j + 1) + 1 = (r + 1) + r * j by ring,
        pow_add, pow_mul, hZ]⟩
  have hyc : ∀ j, PreTilt.coeff j y =
      Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (Z ^ l ^ (r * j)) := fun j => rfl
  have hy : y ^ l ^ (r + 1) = y := by
    refine Perfection.ext (R := ModP (OC l) l) fun j => ?_
    rw [← PreTilt.coeff_def, ← PreTilt.coeff_def, map_pow, hyc]
    show (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (Z ^ l ^ (r * j))) ^ l ^ (r + 1) = _
    rw [← map_pow, ← pow_mul, mul_comm, pow_mul, hZ]
  have hy0 : PreTilt.coeff 0 y = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) Z := by
    rw [hyc]; simp
  obtain ⟨y', h1, h2⟩ := AI.actT_coeff g y 0 _ hy0
  rw [hg _ (Nat.succ_pos r) y hy, hy0] at h2
  have h7 := norm_lt_one_of_mk_eq h2
  rw [h1] at h7
  have h8 : ‖AI.actC g ((x : ℂ_[l]) - ζ)‖ < 1 := by rwa [AI.actC_norm]
  rw [← PadicComplex.norm_extends, PadicComplex.coe_eq, map_sub, ← PadicComplex.coe_eq,
    ← PadicComplex.coe_eq, ← AI.actC_ext]
  have h9 := GlobalTheory.ResidueRoot.norm_add_lt_one h8
    (GlobalTheory.ResidueRoot.norm_add_lt_one (by rw [norm_neg]; exact h7 : ‖-(ζ - AI.actC g ζ)‖ < 1)
      (by rw [norm_neg]; exact h5 : ‖-((x : ℂ_[l]) - ζ)‖ < 1))
  convert h9 using 2
  rw [map_sub]
  ring

end Tilt

section Main

variable {l : ℕ} [hl : Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

open scoped Formalism.Per in

/- English proof (translation)
Apply `T.eB.injective` to reduce the goal to its premises. Rewrite using `[T.ιA, T.zB]`. Conclude with `GlobalTheory.RingIface.aB_algebraMap_padicInt l z`.
-/
theorem ιA_zlW (T : LocTied l P AI) (z : ℤ_[l]) :
    AI.ιA (zlW l (OCb l) z) = algebraMap ℚ_[l] P.R.B (z : ℚ_[l]) := by
  apply T.eB.injective
  rw [T.ιA, T.zB]
  exact GlobalTheory.RingIface.aB_algebraMap_padicInt l z

/- English proof (translation)
Use `haveI := K.2`. Conclude with `isCompact_iff_compactSpace.1 (IntermediateField.fixingSubgroup_isClosed K.1).isCompact`.
-/
theorem compactSpace_GK (K : FinExt l) : CompactSpace ↥(GK K) := by
  haveI := K.2
  exact isCompact_iff_compactSpace.1 (IntermediateField.fixingSubgroup_isClosed K.1).isCompact

/- English proof (translation)
Use `haveI := compactSpace_GK K`. Take `⟨b, hb⟩` from `exists_witt_coboundary (p := l) (AI.actT.comp (GK K).subtype) (fun y m hm hy => (continuous_subtype_val.tendsto (1 : ↥(GK K))).eventually (eventually_actT_eq AI y m hm hy)) c hc hadd (fun g hg => hI g (Subgroup.subset_closure fun x hx => norm_sub_lt_one_of_fix AI g (fun m hm y hy …`. Use `⟨AI.ιA b, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[← AI.ιA_act, ← map_sub, ← ιA_zlW AI T, ← hb g]`. Both sides reduce to the same expression.
-/
theorem exists_int (T : LocTied l P AI) (K : FinExt l) (c : ↥(GK K) → ℤ_[l]) (hc : Continuous c)
    (hadd : ∀ g h, c (g * h) = c g + c h) (hI : ∀ g ∈ IK K, c g = 0) :
    ∃ b : P.R.B, ∀ g : ↥(GK K), P.actQ g b - b = algebraMap ℚ_[l] P.R.B (c g : ℚ_[l]) := by
  haveI := compactSpace_GK K
  obtain ⟨b, hb⟩ := exists_witt_coboundary (p := l) (AI.actT.comp (GK K).subtype)
    (fun y m hm hy => (continuous_subtype_val.tendsto (1 : ↥(GK K))).eventually
      (eventually_actT_eq AI y m hm hy)) c hc hadd
    (fun g hg => hI g (Subgroup.subset_closure fun x hx =>
      norm_sub_lt_one_of_fix AI g (fun m hm y hy => hg m hm y hy) x hx))
  refine ⟨AI.ιA b, fun g => ?_⟩
  rw [← AI.ιA_act, ← map_sub, ← ιA_zlW AI T, ← hb g]
  rfl

/- English proof (translation)
Use `haveI := compactSpace_GK K`. Take `⟨C, hC⟩` from `(isCompact_range hc).isBounded.exists_norm_le`. Take `⟨a, ha0, ha⟩` from `NormedField.exists_norm_lt ℚ_[l] (r := (max C 1)⁻¹) (by positivity)`. Establish `ha1 : ∀ g, ‖a * c g‖ ≤ 1` using `fun g => by`. Rewrite using `[norm_mul]`.

Establish `h1 : ‖c g‖ ≤ max C 1` using `(hC _ ⟨g, rfl⟩).trans (le_max_left _ _)`. Combine the equalities or inequalities in the displayed calculation. Establish `ha' : a ≠ 0` using `norm_pos_iff.1 ha0`. Take `⟨b, hb⟩` from `exists_int AI T K (fun g => ⟨a * c g, ha1 g⟩) ((continuous_const.mul hc).subtype_mk _) (fun g h => Subtype.ext (by`. Express the relevant statement in the definitionally equal form `a * c (g * h) = a * c g + a * c h`.

Rewrite using `[hadd, mul_add]))`. Use the proof step `(fun g hg => Subtype.ext (by`. Express the relevant statement in the definitionally equal form `a * c g = 0`. Rewrite using `[hI g hg, mul_zero]))`. Use `⟨a⁻¹ • b, fun g => ?_⟩` and prove the remaining obligations.

Rewrite using `[map_smul, ← smul_sub, hb g, Algebra.smul_def, ← map_mul]`. Use `congr 1`. Conclude with `inv_mul_cancel_left₀ ha' _`.
-/
theorem exists_rat (T : LocTied l P AI) (K : FinExt l) (c : ↥(GK K) → ℚ_[l]) (hc : Continuous c)
    (hadd : ∀ g h, c (g * h) = c g + c h) (hI : ∀ g ∈ IK K, c g = 0) :
    ∃ b : P.R.B, ∀ g : ↥(GK K), P.actQ g b - b = algebraMap ℚ_[l] P.R.B (c g) := by
  haveI := compactSpace_GK K
  obtain ⟨C, hC⟩ := (isCompact_range hc).isBounded.exists_norm_le
  obtain ⟨a, ha0, ha⟩ := NormedField.exists_norm_lt ℚ_[l] (r := (max C 1)⁻¹) (by positivity)
  have ha1 : ∀ g, ‖a * c g‖ ≤ 1 := fun g => by
    rw [norm_mul]
    have h1 : ‖c g‖ ≤ max C 1 := (hC _ ⟨g, rfl⟩).trans (le_max_left _ _)
    calc ‖a‖ * ‖c g‖ ≤ (max C 1)⁻¹ * max C 1 := by gcongr
      _ = 1 := inv_mul_cancel₀ (by positivity)
  have ha' : a ≠ 0 := norm_pos_iff.1 ha0
  obtain ⟨b, hb⟩ := exists_int AI T K (fun g => ⟨a * c g, ha1 g⟩)
    ((continuous_const.mul hc).subtype_mk _)
    (fun g h => Subtype.ext (by
      change a * c (g * h) = a * c g + a * c h
      rw [hadd, mul_add]))
    (fun g hg => Subtype.ext (by
      change a * c g = 0
      rw [hI g hg, mul_zero]))
  refine ⟨a⁻¹ • b, fun g => ?_⟩
  rw [map_smul, ← smul_sub, hb g, Algebra.smul_def, ← map_mul]
  congr 1
  exact inv_mul_cancel_left₀ ha' _

end Main

/- English proof (translation)
Introduce `D l _ K LL c hc`. Take `⟨hZ, x, hx⟩` from `hc`. Use `⟨hZ, ?_⟩` and prove the remaining obligations. Take `⟨hcont, hadd⟩` from `hZ`. Use `haveI := LL.2`.

Set `v` to `Module.finBasis ℚ_[l] ↥LL.1`. Establish `hI : ∀ g ∈ IK K, c g = 0` using `fun g hg => by simpa using hx g hg`. Establish `hex : ∀ i, ∃ b : (D.loc l).R.B, ∀ g : ↥(GK K), (D.loc l).actQ g b - b = algebraMap ℚ_[l] _ (v.coord i (c g))` using `fun i => exists_rat (D.locA l) (D.locT l) K (fun g => v.coord i (c g)) ((v.coord i).continuous_of_finiteDimensional.comp hcont) (fun g h => by rw [hadd, map_add]; rfl) (fun g hg => by rw [hI g hg, map_zero])`. Use `choose b hb using hex`. Use `⟨∑ i, v i ⊗ₜ[ℚ_[l]] b i, fun g => ?_⟩` and prove the remaining obligations.

Rewrite using `[map_sum, ← Finset.sum_sub_distrib]`. Use `conv_lhs => rw [← v.sum_repr (c g), TensorProduct.sum_tmul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h1 : actVB ((D.loc l).PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) g (v i ⊗ₜ[ℚ_[l]] b i) = v i ⊗ₜ[ℚ_[l]] (D.loc l).actQ g (b i)`. Rewrite using `[← (D.loc l).PD_actB]`.

Both sides reduce to the same expression. Rewrite using `[h1, ← TensorProduct.tmul_sub, hb, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]`. Both sides reduce to the same expression.
-/
theorem unramified_mem_Z1f : ∀ (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime] (K LL : FinExt l),
    ∀ c ∈ Z1ur (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) (IK K),
      c ∈ finiteCocycles ((D.loc l).PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) := by
  intro D l _ K LL c hc
  obtain ⟨hZ, x, hx⟩ := hc
  refine ⟨hZ, ?_⟩
  obtain ⟨hcont, hadd⟩ := hZ
  haveI := LL.2
  let v := Module.finBasis ℚ_[l] ↥LL.1
  have hI : ∀ g ∈ IK K, c g = 0 := fun g hg => by simpa using hx g hg
  have hex : ∀ i, ∃ b : (D.loc l).R.B, ∀ g : ↥(GK K),
      (D.loc l).actQ g b - b = algebraMap ℚ_[l] _ (v.coord i (c g)) := fun i =>
    exists_rat (D.locA l) (D.locT l) K (fun g => v.coord i (c g))
      ((v.coord i).continuous_of_finiteDimensional.comp hcont)
      (fun g h => by rw [hadd, map_add]; rfl) (fun g hg => by rw [hI g hg, map_zero])
  choose b hb using hex
  refine ⟨∑ i, v i ⊗ₜ[ℚ_[l]] b i, fun g => ?_⟩
  rw [map_sum, ← Finset.sum_sub_distrib]
  conv_lhs => rw [← v.sum_repr (c g), TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : actVB ((D.loc l).PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) g (v i ⊗ₜ[ℚ_[l]] b i) =
      v i ⊗ₜ[ℚ_[l]] (D.loc l).actQ g (b i) := by
    rw [← (D.loc l).PD_actB]
    rfl
  rw [h1, ← TensorProduct.tmul_sub, hb, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  rfl

end GlobalTheory.UnramifiedCrys
