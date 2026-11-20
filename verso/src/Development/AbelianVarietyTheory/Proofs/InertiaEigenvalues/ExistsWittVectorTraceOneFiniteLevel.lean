import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix

namespace GlobalTheory.UnramifiedCrys

/- English proof (translation)
Introduce `p hp G _ R _ _ _ _ ρ m hm hfin`. Use `set N := fixer ρ p m with hN`. Use `letI : Fintype (G ⧸ N) := Fintype.ofFinite _`. Set `χ : G ⧸ N → (fixedPow p R m →* R)` to `fun x => (ρ x.out).toMonoidHom.comp (fixedPow p R m).subtype`. Establish `hχ : Function.Injective χ`.

Introduce `x x' h`. Rewrite using `[← x.out_eq, ← x'.out_eq]`. Apply `Quotient.sound` to reduce the goal to its premises. Apply `QuotientGroup.leftRel_apply.2` to reduce the goal to its premises. Introduce `y hy`.

Establish `h1 : ρ x.out y = ρ x'.out y` using `DFunLike.congr_fun h ⟨y, hy⟩`. Rewrite using `[map_mul, RingAut.mul_apply, ← h1, ← RingAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, RingAut.one_apply]`. Establish `hli` using `(linearIndependent_monoidHom (fixedPow p R m) R).comp χ hχ`. Choose the witnesses or unpack the hypotheses as in `⟨θ, hθ⟩ : ∃ θ : fixedPow p R m, ∑ x : G ⧸ N, ρ x.out θ ≠ 0 := by`. Assume the negation of the conclusion as `hc`.

Use `push Not at hc`. Use `Fintype.linearIndependent_iff.1 hli (fun _ => 1) (by` as an intermediate fact. Use function extensionality and compare the values at `θ`. Simplify using `only [one_smul, Finset.sum_apply, Function.comp, Pi.zero_apply]`. Conclude with `hc θ) (QuotientGroup.mk 1)`.

Conclude with `one_ne_zero this`. Establish `hθm : (θ : R) ^ p ^ m = θ` using `θ.2`. Establish `hsum : ∀ (f : G → WittVector p R), (∀ g, ∀ n ∈ N, f (g * n) = f g) → ∀ g, ∑ x : G ⧸ N, f (g * x.out) = ∑ x : G ⧸ N, f x.out`. Introduce `f hf g`. Use `Fintype.sum_equiv (MulAction.toPerm g) _ _ fun x => ?_` and prove the remaining obligations.

Take `⟨n, hn⟩` from `QuotientGroup.mk_out_eq_mul N (g * x.out)`. Establish `: MulAction.toPerm g x = QuotientGroup.mk (g * x.out)`. Rewrite using `[MulAction.toPerm_apply]`. Use `conv_lhs => rw [← x.out_eq]`. Both sides reduce to the same expression.

Rewrite using `[this, hn, hf _ _ n.2]`. Use `set t := ∑ x : G ⧸ N, ρ x.out θ with ht`. Establish `htq : t ^ p ^ m = t`. Rewrite using `[ht, sum_pow_char_pow]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations.

Rewrite using `[← map_pow, hθm]`. Establish `h1 : 1 < p ^ m` using `Nat.one_lt_pow hm.ne' hp.out.one_lt`. Establish `hu : t ^ (p ^ m - 2) * t = 1`. Apply `mul_right_cancel₀ hθ` to reduce the goal to its premises. Rewrite using `[← pow_succ, ← pow_succ, one_mul, show p ^ m - 2 + 1 + 1 = p ^ m by omega, htq]`.

Establish `hθN : ∀ n ∈ N, WittVector.map (ρ n).toRingHom (WittVector.teichmuller p (θ : R)) = WittVector.teichmuller p (θ : R)` using `fun n hn => by`. Rewrite using `[WittVector.map_teichmuller]`. Use `congr 1`. Conclude with `hn θ hθm`. Use `set T := ∑ x : G ⧸ N, WittVector.map (ρ x.out).toRingHom (WittVector.teichmuller p (θ : R)) with hT`.

Establish `hTg : ∀ g, WittVector.map (ρ g).toRingHom T = T` using `fun g => by`. Rewrite using `[hT, map_sum, ← hsum (fun g => WittVector.map (ρ g).toRingHom (WittVector.teichmuller p (θ : R))) (fun g n hn => by`. Simplify using `only [wittMap_mul, hθN n hn]) g]`. Simplify using `only [wittMap_mul]`. Establish `hT0 : WittVector.constantCoeff T = t`.

Rewrite using `[hT, map_sum, ht]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[WittVector.map_teichmuller, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]`. Both sides reduce to the same expression. Establish `hcomp` using `WittVector.isAdicCompleteIdealSpanP (p := p) (k := R)`.

Establish `hmem : T * WittVector.teichmuller p (t ^ (p ^ m - 2)) - 1 ∈ Ideal.span {(p : WittVector p R)}`. Rewrite using `[WittVector.mem_span_p_iff_coeff_zero_eq_zero, ← WittVector.constantCoeff_apply, map_sub, map_mul, map_one, hT0, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, mul_comm, hu, sub_self]`. Establish `hunit : IsUnit T`. Use `Ideal.mem_jacobson_bot.1 (IsAdicComplete.le_jacobson_bot _ hmem) 1` as an intermediate fact. Rewrite `this` using `[mul_one, sub_add_cancel]`.

Conclude with `isUnit_of_mul_isUnit_left this`. Take `⟨S, hS⟩` from `hunit.exists_left_inv`. Establish `hSg : ∀ g, WittVector.map (ρ g).toRingHom S = S` using `fun g => by`. Establish `h2` using `congrArg (WittVector.map (ρ g).toRingHom) hS`. Rewrite `h2` using `[map_mul, hTg, map_one]`.

Conclude with `hunit.mul_right_cancel (h2.trans hS.symm)`. Use `⟨S * WittVector.teichmuller p (θ : R), fun g hg => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hSg, hθN g hg]`. Rewrite using `[finsum_eq_sum_of_fintype]`. Simplify using `only [map_mul, hSg]`.

Rewrite using `[← Finset.mul_sum, ← hT, hS]`.
-/
theorem exists_witt_trace_one : ∀ (p : ℕ) [Fact p.Prime] (G : Type) [Group G] (R : Type) [CommRing R] [IsDomain R] [CharP R p] [PerfectRing R p] (ρ : G →* (R ≃+* R)) (m : ℕ), 0 < m → Finite (G ⧸ GlobalTheory.UnramifiedCrys.fixer ρ p m) → ∃ τ : WittVector p R, (∀ g ∈ GlobalTheory.UnramifiedCrys.fixer ρ p m, WittVector.map (ρ g).toRingHom τ = τ) ∧ ∑ᶠ x : G ⧸ GlobalTheory.UnramifiedCrys.fixer ρ p m, WittVector.map (ρ x.out).toRingHom τ = 1 := by
  intro p hp G _ R _ _ _ _ ρ m hm hfin
  classical
  set N := fixer ρ p m with hN
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
  have hsum : ∀ (f : G → WittVector p R), (∀ g, ∀ n ∈ N, f (g * n) = f g) → ∀ g,
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
  have htq : t ^ p ^ m = t := by
    rw [ht, sum_pow_char_pow]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← map_pow, hθm]
  have h1 : 1 < p ^ m := Nat.one_lt_pow hm.ne' hp.out.one_lt
  have hu : t ^ (p ^ m - 2) * t = 1 := by
    apply mul_right_cancel₀ hθ
    rw [← pow_succ, ← pow_succ, one_mul, show p ^ m - 2 + 1 + 1 = p ^ m by omega, htq]
  have hθN : ∀ n ∈ N, WittVector.map (ρ n).toRingHom (WittVector.teichmuller p (θ : R)) =
      WittVector.teichmuller p (θ : R) := fun n hn => by
    rw [WittVector.map_teichmuller]
    congr 1
    exact hn θ hθm
  set T := ∑ x : G ⧸ N, WittVector.map (ρ x.out).toRingHom (WittVector.teichmuller p (θ : R))
    with hT
  have hTg : ∀ g, WittVector.map (ρ g).toRingHom T = T := fun g => by
    rw [hT, map_sum, ← hsum (fun g => WittVector.map (ρ g).toRingHom
      (WittVector.teichmuller p (θ : R))) (fun g n hn => by
        simp only [wittMap_mul, hθN n hn]) g]
    simp only [wittMap_mul]
  have hT0 : WittVector.constantCoeff T = t := by
    rw [hT, map_sum, ht]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [WittVector.map_teichmuller, WittVector.constantCoeff_apply,
      WittVector.teichmuller_coeff_zero]
    rfl
  have hcomp := WittVector.isAdicCompleteIdealSpanP (p := p) (k := R)
  have hmem : T * WittVector.teichmuller p (t ^ (p ^ m - 2)) - 1 ∈
      Ideal.span {(p : WittVector p R)} := by
    rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero, ← WittVector.constantCoeff_apply, map_sub,
      map_mul, map_one, hT0, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero,
      mul_comm, hu, sub_self]
  have hunit : IsUnit T := by
    have := Ideal.mem_jacobson_bot.1 (IsAdicComplete.le_jacobson_bot _ hmem) 1
    rw [mul_one, sub_add_cancel] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨S, hS⟩ := hunit.exists_left_inv
  have hSg : ∀ g, WittVector.map (ρ g).toRingHom S = S := fun g => by
    have h2 := congrArg (WittVector.map (ρ g).toRingHom) hS
    rw [map_mul, hTg, map_one] at h2
    exact hunit.mul_right_cancel (h2.trans hS.symm)
  refine ⟨S * WittVector.teichmuller p (θ : R), fun g hg => ?_, ?_⟩
  · rw [map_mul, hSg, hθN g hg]
  · rw [finsum_eq_sum_of_fintype]
    simp only [map_mul, hSg]
    rw [← Finset.mul_sum, ← hT, hS]

end GlobalTheory.UnramifiedCrys
