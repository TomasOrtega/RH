import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SphereMeanSubArchimedean

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

/- English proof (translation)
Take `⟨hpr, hh⟩` from `hp`. Use `haveI := hpr`. Take `⟨g, hg, hpg⟩` from `ValUFD.heightOne_principal p hh`. Establish `hPr : p.IsPrincipal` using `⟨⟨g, hpg⟩⟩`. Unfold `gen`.

Rewrite using `[dif_pos hPr]`. Introduce `h0`. Establish `hbot : p = ⊥` using `(Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero p).2 h0`. Rewrite `hpg` using `[hbot]`. Conclude with `hg.ne_zero (Ideal.span_singleton_eq_bot.1 hpg.symm)`.
-/
theorem gen_ne_zero_of_mem_htOne {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) : d.gen p ≠ 0 := by
  obtain ⟨hpr, hh⟩ := hp
  haveI := hpr
  obtain ⟨g, hg, hpg⟩ := ValUFD.heightOne_principal p hh
  have hPr : p.IsPrincipal := ⟨⟨g, hpg⟩⟩
  unfold gen
  rw [dif_pos hPr]
  intro h0
  have hbot : p = ⊥ := (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero p).2 h0
  rw [hbot] at hpg
  exact hg.ne_zero (Ideal.span_singleton_eq_bot.1 hpg.symm)

/- English proof (translation)
Establish `hspec : ∀ c, hd.a4.choose c ∈ 𝒜 c d.wF ∧ hd.a4.choose c ≠ 0` using `hd.a4.choose_spec.1`. Establish `hfin : ∀ c, {p | p ∈ d.HtOne ∧ d.nP h c d.wF (hd.a4.choose c) p ≠ 0}.Finite` using `fun c => (d.good_primes_properties hd h c).2.2.1 d.wF (hd.a4.choose c) (hspec c).1 (hspec c).2`. Take `⟨T, hmemT⟩ : ∃ T : ι → Finset (Ideal (KTp K d.D d.N)), ∀ c p, p ∈ T c ↔ p ∈ d.HtOne ∧ d.nP h c d.wF (hd.a4.choose c) p ≠ 0` from `⟨fun c => (hfin c).toFinset, fun c p => by simp⟩`. Establish `hmemS : ∀ x ∈ Finset.univ.sigma T, x.2 ∈ d.HtOne ∧ d.nP h x.1 d.wF (hd.a4.choose x.1) x.2 ≠ 0`. Introduce `x hx`.

Rewrite `hx` using `[Finset.mem_sigma]`. Conclude with `(hmemT _ _).1 hx.2`. Establish `hne : ∀ x ∈ Finset.univ.sigma T, d.gen x.2 ≠ 0` using `fun x hx => d.gen_ne_zero_of_mem_htOne (hmemS x hx).1`. Establish `hmh : ∀ x ∈ Finset.univ.sigma T, IsMultiHomogeneous (fun b : Fin (d.D + 1) => if b = 0 then 0 else d.dg (d.gen x.2)) (d.gen x.2)`. Introduce `x hx`.

Take `⟨hp, hn⟩` from `hmemS x hx`. Use `(d.good_primes_properties hd h x.1).2.1 x.2 hp ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hw`. Use `push_neg at hw`. Apply `hn` to reduce the goal to its premises.

Simplify using `[nP, hw]`. Establish `halg : ∀ x ∈ Finset.univ.sigma T, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen x.2) ≠ 0` using `fun x hx => (map_ne_zero_iff _ (IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N))).2 (hne x hx)`. Establish `key : ∀ (a : KTf K d.D d.N), a ≠ 0 → ∀ m : ℤ, a ^ m * a ^ (-m).toNat = a ^ m.toNat`. Introduce `a ha m`. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_add₀ ha]`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers. Use `⟨∏ x ∈ Finset.univ.sigma T, d.gen x.2 ^ (d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat, ∏ x ∈ Finset.univ.sigma T, d.gen x.2 ^ (-d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat, Finset.prod_ne_zero_iff.2 fun x hx => pow_ne_zero _ (hne x hx), Finset.prod_ne_zero_iff.2 fun x hx => po …` and prove the remaining obligations. Establish `hfac : ∀ c, (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nP h c d.wF (hd.a4.choose c) p) = ∏ p ∈ T c, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nP h c d.wF (hd.a4.choose c) p`. Introduce `c`.

Apply `finprod_mem_eq_prod_of_subset` to reduce the goal to its premises. Introduce and unpack `p ⟨hp, hp1⟩`. Rewrite `hp1` using `[Function.mem_mulSupport]`. Rewrite using `[Finset.mem_coe, hmemT]`. Conclude with `⟨hp, fun h0' => hp1 (by rw [h0', zpow_zero])⟩`.

Introduce `p hp`. Conclude with `((hmemT c p).1 hp).1`. Establish `hf : d.fDivE hd h = ∏ x ∈ Finset.univ.sigma T, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen x.2) ^ d.nP h x.1 d.wF (hd.a4.choose x.1) x.2`. Rewrite using `[Finset.prod_sigma]`. Unfold `fDivE`.

Conclude with `Finset.prod_congr rfl fun c _ => hfac c`. Rewrite using `[hf, map_prod, map_prod, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun x hx => ?_` and prove the remaining obligations. Rewrite using `[map_pow, map_pow]`. Conclude with `key _ (halg x hx) _`.

Establish `hsum : ∀ c, (∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), (d.nP h c d.wF (hd.a4.choose c) p : ℝ) * h0 (d.gen p)) = ∑ p ∈ T c, (d.nP h c d.wF (hd.a4.choose c) p : ℝ) * h0 (d.gen p)`. Introduce `c`. Apply `finsum_mem_eq_sum_of_subset` to reduce the goal to its premises. Introduce and unpack `p ⟨hp, hp1⟩`. Rewrite `hp1` using `[Function.mem_support]`.

Rewrite using `[Finset.mem_coe, hmemT]`. Conclude with `⟨hp, fun h0' => hp1 (by rw [h0', Int.cast_zero, zero_mul])⟩`. Introduce `p hp`. Conclude with `((hmemT c p).1 hp).1`. Establish `hn0 : 0 < d.N + 1` using `Nat.succ_pos _`.

Establish `hU : h0 (∏ x ∈ Finset.univ.sigma T, d.gen x.2 ^ (d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat) = ∑ x ∈ Finset.univ.sigma T, ((d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat : ℝ) * h0 (d.gen x.2)` using `HeightMultiplicativity.logHeight_prod_pow (B := d.D + 1) (n := d.N + 1) hn0 (Finset.univ.sigma T) (fun x b => if b = 0 then 0 else d.dg (d.gen x.2)) (fun x => d.gen x.2) _ hne hmh`. Establish `hV : h0 (∏ x ∈ Finset.univ.sigma T, d.gen x.2 ^ (-d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat) = ∑ x ∈ Finset.univ.sigma T, ((-d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat : ℝ) * h0 (d.gen x.2)` using `HeightMultiplicativity.logHeight_prod_pow (B := d.D + 1) (n := d.N + 1) hn0 (Finset.univ.sigma T) (fun x b => if b = 0 then 0 else d.dg (d.gen x.2)) (fun x => d.gen x.2) _ hne hmh`. Rewrite using `[hU, hV, ← Finset.sum_sub_distrib, Finset.sum_sigma]`. Unfold `h0f`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[hsum c]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[← sub_mul]`. Use `congr 1`. Conclude with `(Int.toNat_sub_toNat_neg _).symm` after adjusting the coercions.
-/
theorem finite_height_fraction_repr (hd : d.AxH 𝒜) (h : d.S1) :
    ∃ U V : KTp K d.D d.N, U ≠ 0 ∧ V ≠ 0 ∧ (∃ eU, IsMultiHomogeneous eU U) ∧
      (∃ eV, IsMultiHomogeneous eV V) ∧
      d.fDivE hd h * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) V =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) U ∧
      d.h0f h d.wF hd.a4.choose = h0 U - h0 V := by
  classical
  have hspec : ∀ c, hd.a4.choose c ∈ 𝒜 c d.wF ∧ hd.a4.choose c ≠ 0 := hd.a4.choose_spec.1
  have hfin : ∀ c, {p | p ∈ d.HtOne ∧ d.nP h c d.wF (hd.a4.choose c) p ≠ 0}.Finite := fun c =>
    (d.good_primes_properties hd h c).2.2.1 d.wF (hd.a4.choose c) (hspec c).1 (hspec c).2
  obtain ⟨T, hmemT⟩ : ∃ T : ι → Finset (Ideal (KTp K d.D d.N)),
      ∀ c p, p ∈ T c ↔ p ∈ d.HtOne ∧ d.nP h c d.wF (hd.a4.choose c) p ≠ 0 :=
    ⟨fun c => (hfin c).toFinset, fun c p => by simp⟩
  have hmemS : ∀ x ∈ Finset.univ.sigma T,
      x.2 ∈ d.HtOne ∧ d.nP h x.1 d.wF (hd.a4.choose x.1) x.2 ≠ 0 := by
    intro x hx
    rw [Finset.mem_sigma] at hx
    exact (hmemT _ _).1 hx.2
  have hne : ∀ x ∈ Finset.univ.sigma T, d.gen x.2 ≠ 0 := fun x hx => d.gen_ne_zero_of_mem_htOne (hmemS x hx).1
  have hmh : ∀ x ∈ Finset.univ.sigma T,
      IsMultiHomogeneous (fun b : Fin (d.D + 1) => if b = 0 then 0 else d.dg (d.gen x.2)) (d.gen x.2) := by
    intro x hx
    obtain ⟨hp, hn⟩ := hmemS x hx
    refine (d.good_primes_properties hd h x.1).2.1 x.2 hp ?_
    by_contra hw
    push_neg at hw
    apply hn
    simp [nP, hw]
  have halg : ∀ x ∈ Finset.univ.sigma T,
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen x.2) ≠ 0 := fun x hx =>
    (map_ne_zero_iff _ (IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N))).2 (hne x hx)
  have key : ∀ (a : KTf K d.D d.N), a ≠ 0 → ∀ m : ℤ, a ^ m * a ^ (-m).toNat = a ^ m.toNat := by
    intro a ha m
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ ha]
    congr 1
    omega
  refine ⟨∏ x ∈ Finset.univ.sigma T, d.gen x.2 ^ (d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat,
    ∏ x ∈ Finset.univ.sigma T, d.gen x.2 ^ (-d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat,
    Finset.prod_ne_zero_iff.2 fun x hx => pow_ne_zero _ (hne x hx),
    Finset.prod_ne_zero_iff.2 fun x hx => pow_ne_zero _ (hne x hx),
    ⟨_, HeightMultiplicativity.multi_prod _ _ _ fun x hx => HeightMultiplicativity.multi_pow (hmh x hx) _⟩,
    ⟨_, HeightMultiplicativity.multi_prod _ _ _ fun x hx => HeightMultiplicativity.multi_pow (hmh x hx) _⟩, ?_, ?_⟩
  · have hfac : ∀ c, (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nP h c d.wF (hd.a4.choose c) p) =
        ∏ p ∈ T c, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^
          d.nP h c d.wF (hd.a4.choose c) p := by
      intro c
      apply finprod_mem_eq_prod_of_subset
      · rintro p ⟨hp, hp1⟩
        rw [Function.mem_mulSupport] at hp1
        rw [Finset.mem_coe, hmemT]
        exact ⟨hp, fun h0' => hp1 (by rw [h0', zpow_zero])⟩
      · intro p hp
        exact ((hmemT c p).1 hp).1
    have hf : d.fDivE hd h = ∏ x ∈ Finset.univ.sigma T,
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen x.2) ^ d.nP h x.1 d.wF (hd.a4.choose x.1) x.2 := by
      rw [Finset.prod_sigma]
      unfold fDivE
      exact Finset.prod_congr rfl fun c _ => hfac c
    rw [hf, map_prod, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [map_pow, map_pow]
    exact key _ (halg x hx) _
  · have hsum : ∀ c, (∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        (d.nP h c d.wF (hd.a4.choose c) p : ℝ) * h0 (d.gen p)) =
        ∑ p ∈ T c, (d.nP h c d.wF (hd.a4.choose c) p : ℝ) * h0 (d.gen p) := by
      intro c
      apply finsum_mem_eq_sum_of_subset
      · rintro p ⟨hp, hp1⟩
        rw [Function.mem_support] at hp1
        rw [Finset.mem_coe, hmemT]
        exact ⟨hp, fun h0' => hp1 (by rw [h0', Int.cast_zero, zero_mul])⟩
      · intro p hp
        exact ((hmemT c p).1 hp).1
    have hn0 : 0 < d.N + 1 := Nat.succ_pos _
    have hU : h0 (∏ x ∈ Finset.univ.sigma T,
        d.gen x.2 ^ (d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat) =
        ∑ x ∈ Finset.univ.sigma T,
          ((d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat : ℝ) * h0 (d.gen x.2) :=
      HeightMultiplicativity.logHeight_prod_pow (B := d.D + 1) (n := d.N + 1) hn0 (Finset.univ.sigma T)
        (fun x b => if b = 0 then 0 else d.dg (d.gen x.2)) (fun x => d.gen x.2) _ hne hmh
    have hV : h0 (∏ x ∈ Finset.univ.sigma T,
        d.gen x.2 ^ (-d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat) =
        ∑ x ∈ Finset.univ.sigma T,
          ((-d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat : ℝ) * h0 (d.gen x.2) :=
      HeightMultiplicativity.logHeight_prod_pow (B := d.D + 1) (n := d.N + 1) hn0 (Finset.univ.sigma T)
        (fun x b => if b = 0 then 0 else d.dg (d.gen x.2)) (fun x => d.gen x.2) _ hne hmh
    rw [hU, hV, ← Finset.sum_sub_distrib, Finset.sum_sigma]
    unfold h0f
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hsum c]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← sub_mul]
    congr 1
    exact_mod_cast (Int.toNat_sub_toNat_neg _).symm

end Data

end ReciprocityTheory.ChartRestriction.G.T0
