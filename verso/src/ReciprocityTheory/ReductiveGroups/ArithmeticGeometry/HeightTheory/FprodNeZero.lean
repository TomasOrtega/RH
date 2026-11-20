import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscBDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.UnitAtIntAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.DePres
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AGFrameNonneg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GoodPrimesProperties
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.BlockDegOfScale
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ProdZpowEqZpowSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Hartogs

set_option linter.style.haveILetI false

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

/- English proof (translation)
Take `⟨hpr, hht⟩` from `hp`. Establish `hne : p ≠ ⊥`. Introduce and unpack `rfl`. Use `first`. Consider the case `(simp at hht; done)`.

Consider the case `(rw [Ideal.height_bot] at hht; exact zero_ne_one hht)`. Take `⟨q, hqp, hq⟩` from `hpr.exists_mem_prime_of_ne_bot hne`. Establish `hqi : (Ideal.span {q}).IsPrime` using `(Ideal.span_singleton_prime hq.ne_zero).mpr hq`. Establish `hle : Ideal.span {q} ≤ p` using `(Ideal.span_singleton_le_iff_mem p).mpr hqp`. Establish `hbot : (⊥ : Ideal (KTp K d.D d.N)) < Ideal.span {q}` using `bot_lt_iff_ne_bot.mpr (by simpa using hq.ne_zero)`.

Use `haveI := hpr`. Use `haveI := hqi`. Establish `hspan : Ideal.span {q} = p`. Assume the negation of the conclusion as `hne'`. Establish `hlt : Ideal.span {q} < p` using `lt_of_le_of_ne hle hne'`.

Establish `h3 : (Ideal.span {q}).height < 1`. Establish `hp1 : p.height ≤ (1 : ℕ)` using `by rw [hht]; rfl`. Conclude with `(Ideal.height_le_iff.mp hp1) _ hqi hlt`. Establish `h0 : (Ideal.span {q}).height ≤ (0 : ℕ)`. Rewrite `h3` using `[ENat.lt_one_iff_eq_zero]`.

Rewrite using `[h3]`. Both sides reduce to the same expression. Establish `h2` using `(Ideal.height_le_iff.mp h0) ⊥ Ideal.bot_prime hbot`. Use `first`. Consider the case `(simp at h2; done)`.

Consider the case `exact absurd h2 (not_lt_of_ge bot_le)`. Consider the case `exact ENat.not_lt_zero _ h2`. Establish `hprin : p.IsPrincipal` using `⟨⟨q, hspan.symm⟩⟩`. Use `haveI := hprin`. Simplify using `only [Data.gen, dif_pos hprin]`.

Introduce `h0`. Conclude with `hne ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero p).mpr h0)`.
-/
private theorem gen_ne_zero_of_mem_htOne_heightData {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) : d.gen p ≠ 0 := by
  obtain ⟨hpr, hht⟩ := hp
  have hne : p ≠ ⊥ := by
    rintro rfl
    first
      | (simp at hht; done)
      | (rw [Ideal.height_bot] at hht; exact zero_ne_one hht)
  obtain ⟨q, hqp, hq⟩ := hpr.exists_mem_prime_of_ne_bot hne
  have hqi : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
  have hle : Ideal.span {q} ≤ p := (Ideal.span_singleton_le_iff_mem p).mpr hqp
  have hbot : (⊥ : Ideal (KTp K d.D d.N)) < Ideal.span {q} :=
    bot_lt_iff_ne_bot.mpr (by simpa using hq.ne_zero)
  haveI := hpr
  haveI := hqi
  have hspan : Ideal.span {q} = p := by
    by_contra hne'
    have hlt : Ideal.span {q} < p := lt_of_le_of_ne hle hne'
    have h3 : (Ideal.span {q}).height < 1 := by
      have hp1 : p.height ≤ (1 : ℕ) := by rw [hht]; rfl
      exact (Ideal.height_le_iff.mp hp1) _ hqi hlt
    have h0 : (Ideal.span {q}).height ≤ (0 : ℕ) := by
      rw [ENat.lt_one_iff_eq_zero] at h3
      rw [h3]; rfl
    have h2 := (Ideal.height_le_iff.mp h0) ⊥ Ideal.bot_prime hbot
    first
      | (simp at h2; done)
      | exact absurd h2 (not_lt_of_ge bot_le)
      | exact ENat.not_lt_zero _ h2
  have hprin : p.IsPrincipal := ⟨⟨q, hspan.symm⟩⟩
  haveI := hprin
  simp only [Data.gen, dif_pos hprin]
  intro h0
  exact hne ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero p).mpr h0)

/- English proof (translation)
Use `finprod_mem_induction (fun x => x ≠ 0) one_ne_zero (fun x y hx hy => mul_ne_zero hx hy) ?_` and prove the remaining obligations. Introduce `q hq`. Apply `zpow_ne_zero` to reduce the goal to its premises. Establish `hg` using `gen_ne_zero_of_mem_htOne_heightData d hq`. Use `first`.

Consider the case `exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hg`. Consider the case `exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hg`. Consider the case `exact (map_ne_zero_iff _ (NoZeroSMulDivisors.algebraMap_injective _ _)).mpr hg`. Consider the case `(simpa using hg)`.
-/
theorem fprod_ne_zero (E : Ideal (KTp K d.D d.N) → ℤ) (hE : {q | q ∈ d.HtOne ∧ E q ≠ 0}.Finite) :
    (∏ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne),
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q) ≠ 0 := by
  refine finprod_mem_induction (fun x => x ≠ 0) one_ne_zero (fun x y hx hy => mul_ne_zero hx hy) ?_
  intro q hq
  apply zpow_ne_zero
  have hg := gen_ne_zero_of_mem_htOne_heightData d hq
  first
    | exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hg
    | exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hg
    | exact (map_ne_zero_iff _ (NoZeroSMulDivisors.algebraMap_injective _ _)).mpr hg
    | (simpa using hg)

/- English proof (translation)
Establish `h1 : d.HtOne ∩ Function.mulSupport (fun q => algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q) ⊆ hE.toFinset`. Introduce and unpack `q ⟨hq, hs⟩`. Rewrite using `[Set.Finite.coe_toFinset]`. Conclude with `⟨hq, fun h0 => hs (by simp only [h0, zpow_zero])⟩`. Establish `h1' : d.HtOne ∩ Function.support (fun q => E q * ((if bb = 0 then 0 else d.dg (d.gen q) : ℕ) : ℤ)) ⊆ hE.toFinset`.

Introduce and unpack `q ⟨hq, hs⟩`. Rewrite using `[Set.Finite.coe_toFinset]`. Conclude with `⟨hq, fun h0 => hs (by simp only [h0, zero_mul])⟩`. Establish `h2 : (hE.toFinset : Set (Ideal (KTp K d.D d.N))) ⊆ d.HtOne`. Introduce `q hq`.

Rewrite `hq` using `[Set.Finite.coe_toFinset]`. Conclude with `hq.1`. Rewrite using `[finprod_mem_eq_prod_of_subset _ h1 h2, finsum_mem_eq_sum_of_subset _ h1' h2, map_prod]`. Establish `hκ : algebraMap K (KTf K d.D d.N) (u : K) ≠ 0` using `(map_ne_zero _).mpr u.ne_zero`. Rewrite using `[← HDiscOmL.prod_zpow hκ, ← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun q hq => ?_` and prove the remaining obligations. Establish `hq' : q ∈ d.HtOne ∧ E q ≠ 0`. Rewrite `hq` using `[Set.Finite.mem_toFinset]`. Conclude with `hq`. Establish `hs : sigP (N` using `d.N) bb u (d.gen q) = MvPolynomial.C ((u : K) ^ (if bb = 0 then 0 else d.dg (d.gen q))) * d.gen q := scale_multiHomogeneous bb u (fun b : Fin (d.D + 1) => if b = 0 then 0 else d.dg (d.gen q)) (d.gen q) (hg q hq'.1 hq'.2)`.

Establish `hs' : sigF (K` using `K) (D := d.D) (N := d.N) bb u (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q)) = algebraMap K (KTf K d.D d.N) (u : K) ^ ((if bb = 0 then 0 else d.dg (d.gen q) : ℕ) : ℤ) * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) := by`. Rewrite using `[d.sigF_algebraMap, hs, map_mul, ← d.algebraMap_K_KTf, map_pow, zpow_natCast]`. Rewrite using `[map_zpow₀, hs', mul_zpow, ← zpow_mul, mul_comm (E q)]`.
-/
theorem sig_fprod (E : Ideal (KTp K d.D d.N) → ℤ) (hE : {q | q ∈ d.HtOne ∧ E q ≠ 0}.Finite)
    (hg : ∀ q ∈ d.HtOne, E q ≠ 0 → ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous
      (fun b : Fin (d.D + 1) => if b = 0 then 0 else d.dg (d.gen q)) (d.gen q))
    (bb : Fin (d.D + 1)) (u : Kˣ) :
    sigF (K := K) (D := d.D) (N := d.N) bb u (∏ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne),
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q) =
      algebraMap K (KTf K d.D d.N) (u : K) ^ (∑ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne),
        E q * ((if bb = 0 then 0 else d.dg (d.gen q) : ℕ) : ℤ)) *
      ∏ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne),
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q := by
  classical
  have h1 : d.HtOne ∩ Function.mulSupport (fun q =>
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q) ⊆ hE.toFinset := by
    rintro q ⟨hq, hs⟩
    rw [Set.Finite.coe_toFinset]
    exact ⟨hq, fun h0 => hs (by simp only [h0, zpow_zero])⟩
  have h1' : d.HtOne ∩ Function.support (fun q =>
      E q * ((if bb = 0 then 0 else d.dg (d.gen q) : ℕ) : ℤ)) ⊆ hE.toFinset := by
    rintro q ⟨hq, hs⟩
    rw [Set.Finite.coe_toFinset]
    exact ⟨hq, fun h0 => hs (by simp only [h0, zero_mul])⟩
  have h2 : (hE.toFinset : Set (Ideal (KTp K d.D d.N))) ⊆ d.HtOne := by
    intro q hq
    rw [Set.Finite.coe_toFinset] at hq
    exact hq.1
  rw [finprod_mem_eq_prod_of_subset _ h1 h2, finsum_mem_eq_sum_of_subset _ h1' h2, map_prod]
  have hκ : algebraMap K (KTf K d.D d.N) (u : K) ≠ 0 :=
    (map_ne_zero _).mpr u.ne_zero
  rw [← HDiscOmL.prod_zpow hκ, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun q hq => ?_
  have hq' : q ∈ d.HtOne ∧ E q ≠ 0 := by
    rw [Set.Finite.mem_toFinset] at hq
    exact hq
  have hs : sigP (N := d.N) bb u (d.gen q) =
      MvPolynomial.C ((u : K) ^ (if bb = 0 then 0 else d.dg (d.gen q))) * d.gen q :=
    scale_multiHomogeneous bb u (fun b : Fin (d.D + 1) => if b = 0 then 0 else d.dg (d.gen q))
      (d.gen q) (hg q hq'.1 hq'.2)
  have hs' : sigF (K := K) (D := d.D) (N := d.N) bb u
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q)) =
      algebraMap K (KTf K d.D d.N) (u : K) ^ ((if bb = 0 then 0 else d.dg (d.gen q) : ℕ) : ℤ) *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) := by
    rw [d.sigF_algebraMap, hs, map_mul, ← d.algebraMap_K_KTf, map_pow, zpow_natCast]
  rw [map_zpow₀, hs', mul_zpow, ← zpow_mul, mul_comm (E q)]

/- English proof (translation)
Take `⟨he, -, -⟩` from `hd.a4.choose_spec`. Establish `hfin : ∀ c, {q | q ∈ d.HtOne ∧ d.nP h c d.wF (hd.a4.choose c) q ≠ 0}.Finite` using `fun c => (d.good_primes_properties hd h c).2.2.1 d.wF (hd.a4.choose c) (he c).1 (he c).2`. Establish `hint : ∀ p ∈ d.HtOne, LocAt.IntAt p (d.omE hd h)`. Introduce `p hp`. Use `haveI := hp.1`.

Establish `hs : ∀ c, ∃ V : KTf K d.D d.N, LocAt.UnitAt p V ∧ (∏ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne), algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ d.nP h c d.wF (hd.a4.choose c) q) = algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nP h c d.wF (hd.a4.choose c) p …` using `fun c => d.split_at _ (hfin c) hp`. Use `choose V hV hVe using hs`. Establish `hX0 : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (d.gen_prime' hp).ne_zero`. Establish `hf : d.fDivE hd h = algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ (∑ c, d.nP h c d.wF (hd.a4.choose c) p) * ∏ c, V c`. Simplify using `only [fDivE]`.

Rewrite using `[Finset.prod_congr rfl fun c _ => hVe c, Finset.prod_mul_distrib, HDiscOmL.prod_zpow hX0]`. Establish `h2 : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ (2 * ∑ c, d.nP h c d.wF (hd.a4.choose c) p) = (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ (∑ c, d.nP h c d.wF (hd.a4.choose c) p)) ^ 2`. Rewrite using `[mul_comm, zpow_mul]`. Use `norm_cast`. Establish `hom : d.omE hd h = (d.De hd h * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ (2 * ∑ c, d.nP h c d.wF (hd.a4.choose c) p)) * (∏ c, V c) ^ 2`.

Rewrite using `[omE, hf, h2]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hom]`. Conclude with `LocAt.intAt_mul (d.de_local hd h hp) (LocAt.unitAt_intAt (LocAt.unitAt_pow (LocAt.unitAt_prod _ _ fun c _ => hV c) 2))`. Take `⟨Om, hOm⟩` from `ufd_mem_of_forall_prime (R := KTp K d.D d.N) (d.omE hd h) (fun q hq => by`.

Establish `hp : Ideal.span {q} ∈ d.HtOne` using `⟨(Ideal.span_singleton_prime hq.ne_zero).mpr hq, ValUFD.height_span_prime hq⟩`. Take `⟨a, s, hs, e⟩` from `hint _ hp`. Conclude with `⟨a, s, fun hdv => hs (Ideal.mem_span_singleton.mpr hdv), e⟩)`. Establish `hf0 : d.fDivE hd h ≠ 0`. Simplify using `only [fDivE]`.

Rewrite using `[Finset.prod_ne_zero_iff]`. Conclude with `fun c _ => d.fprod_ne_zero _ (hfin c)`. Establish `hom0 : d.omE hd h ≠ 0` using `mul_ne_zero (d.disc_lattice hd h).1 (pow_ne_zero 2 hf0)`. Establish `hOm0 : Om ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hOm` using `[map_zero]`. Conclude with `hom0 hOm`. Use `⟨Om, hOm.symm, hOm0, ?_⟩` and prove the remaining obligations. Take `⟨a, b, hb0, hab, m, -, ha, hbm⟩` from `d.de_pres hd h`. Establish `hsigDe : ∀ (bb : Fin (d.D + 1)) (u : Kˣ), sigF (K` using `K) (D := d.D) (N := d.N) bb u (d.De hd h) = d.De hd h := by`.

Introduce `bb u`. Establish `e1` using `congrArg (sigF (K := K) (D := d.D) (N := d.N) bb u) hab`. Establish `sa : sigP (N` using `d.N) bb u a = MvPolynomial.C ((u : K) ^ m bb) * a := scale_multiHomogeneous bb u m a ha`. Establish `sb : sigP (N` using `d.N) bb u b = MvPolynomial.C ((u : K) ^ m bb) * b := scale_multiHomogeneous bb u m b hbm`. Rewrite `e1` using `[d.sigF_algebraMap, map_mul, d.sigF_algebraMap, sa, sb, map_mul, map_mul, hab, ← d.algebraMap_K_KTf]`.

Establish `hC : algebraMap K (KTf K d.D d.N) ((u : K) ^ m bb) ≠ 0` using `(map_ne_zero _).mpr (pow_ne_zero _ u.ne_zero)`. Establish `hB : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hb0`. Apply `mul_right_cancel₀ (mul_ne_zero hC hB)` to reduce the goal to its premises. Take the linear combination `-e1`. Use `set Eb : Fin (d.D + 1) → ℤ := fun bb => ∑ c, ∑ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne), d.nP h c d.wF (hd.a4.choose c) q * ((if bb = 0 then 0 else d.dg (d.gen q) : ℕ) : ℤ) with hEb`.

Establish `hsigf : ∀ (bb : Fin (d.D + 1)) (u : Kˣ), sigF (K` using `K) (D := d.D) (N := d.N) bb u (d.fDivE hd h) = algebraMap K (KTf K d.D d.N) (u : K) ^ Eb bb * d.fDivE hd h := by`. Introduce `bb u`. Establish `hκ : algebraMap K (KTf K d.D d.N) (u : K) ≠ 0` using `(map_ne_zero _).mpr u.ne_zero`. Simplify using `only [fDivE, hEb]`. Rewrite using `[map_prod, Finset.prod_congr rfl fun c _ => d.sig_fprod _ (hfin c) (fun q hq hn => (d.good_primes_properties hd h c).2.1 q hq (by`.

Assume the negation of the conclusion as `hno`. Apply `hn` to reduce the goal to its premises. Simplify using `only [nP]`. Rewrite using `[finsum_mem_def]`. Use `finsum_eq_zero_of_forall_eq_zero fun w => ?_` and prove the remaining obligations.

Rewrite using `[Set.indicator_apply, if_neg (fun hw => hno ⟨w, hw⟩)])) bb u,`. Use the proof step `Finset.prod_mul_distrib, HDiscOmL.prod_zpow hκ]`. Establish `hEb : ∀ bb : Fin (d.D + 1), 2 * Eb bb = ((if bb = 0 then 0 else 2 * (d.aG h d.wF hd.a4.choose).toNat : ℕ) : ℤ)`. Introduce `bb`. Distinguish the cases in `hbb : bb = 0`.

Simplify using `[hEb, hbb]`. Simplify using `only [hEb, hbb, if_false]`. Rewrite using `[Nat.cast_mul, Int.toNat_of_nonneg (d.aG_frame_nonneg hd h)]`. Both sides reduce to the same expression. Introduce `s hs bb`.

Use `block_deg_of_scale bb _ Om (fun u => ?_) s hs` and prove the remaining obligations. Apply `IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (sigP (N := d.N) bb u Om) = algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (MvPolynomial.C ((u : K) ^ (if bb = 0 then 0 else 2 * (d.aG h d.wF hd.a4.choose).toNat)) * Om)`. Rewrite using `[← d.sigF_algebraMap, map_mul, ← hOm, ← d.algebraMap_K_KTf, map_pow, ← zpow_natCast, ← hEb bb]`. Establish `hk : algebraMap K (KTf K d.D d.N) (u : K) ^ (2 * Eb bb) = (algebraMap K (KTf K d.D d.N) (u : K) ^ Eb bb) ^ 2`.

Rewrite using `[mul_comm, zpow_mul]`. Use `norm_cast`. Simplify using `only [omE]`. Rewrite using `[map_mul, map_pow, hsigDe, hsigf, hk]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem om_is_poly (hd : d.AxH 𝒜) (h : d.S1) :
    ∃ Om : KTp K d.D d.N, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Om = d.omE hd h ∧ Om ≠ 0 ∧
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous
        (fun b : Fin (d.D + 1) => if b = 0 then 0 else 2 * (d.aG h d.wF hd.a4.choose).toNat) Om := by
  classical
  obtain ⟨he, -, -⟩ := hd.a4.choose_spec
  have hfin : ∀ c, {q | q ∈ d.HtOne ∧ d.nP h c d.wF (hd.a4.choose c) q ≠ 0}.Finite := fun c =>
    (d.good_primes_properties hd h c).2.2.1 d.wF (hd.a4.choose c) (he c).1 (he c).2

  have hint : ∀ p ∈ d.HtOne, LocAt.IntAt p (d.omE hd h) := by
    intro p hp
    haveI := hp.1
    have hs : ∀ c, ∃ V : KTf K d.D d.N, LocAt.UnitAt p V ∧
        (∏ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne),
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ d.nP h c d.wF (hd.a4.choose c) q) =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nP h c d.wF (hd.a4.choose c) p * V :=
      fun c => d.split_at _ (hfin c) hp
    choose V hV hVe using hs
    have hX0 : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (d.gen_prime' hp).ne_zero
    have hf : d.fDivE hd h = algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^
        (∑ c, d.nP h c d.wF (hd.a4.choose c) p) * ∏ c, V c := by
      simp only [fDivE]
      rw [Finset.prod_congr rfl fun c _ => hVe c, Finset.prod_mul_distrib, HDiscOmL.prod_zpow hX0]
    have h2 : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^
        (2 * ∑ c, d.nP h c d.wF (hd.a4.choose c) p) =
        (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^
          (∑ c, d.nP h c d.wF (hd.a4.choose c) p)) ^ 2 := by
      rw [mul_comm, zpow_mul]
      norm_cast
    have hom : d.omE hd h = (d.De hd h * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^
        (2 * ∑ c, d.nP h c d.wF (hd.a4.choose c) p)) * (∏ c, V c) ^ 2 := by
      rw [omE, hf, h2]
      ring
    rw [hom]
    exact LocAt.intAt_mul (d.de_local hd h hp)
      (LocAt.unitAt_intAt (LocAt.unitAt_pow (LocAt.unitAt_prod _ _ fun c _ => hV c) 2))
  obtain ⟨Om, hOm⟩ := ufd_mem_of_forall_prime (R := KTp K d.D d.N) (d.omE hd h) (fun q hq => by
    have hp : Ideal.span {q} ∈ d.HtOne :=
      ⟨(Ideal.span_singleton_prime hq.ne_zero).mpr hq, ValUFD.height_span_prime hq⟩
    obtain ⟨a, s, hs, e⟩ := hint _ hp
    exact ⟨a, s, fun hdv => hs (Ideal.mem_span_singleton.mpr hdv), e⟩)

  have hf0 : d.fDivE hd h ≠ 0 := by
    simp only [fDivE]
    rw [Finset.prod_ne_zero_iff]
    exact fun c _ => d.fprod_ne_zero _ (hfin c)
  have hom0 : d.omE hd h ≠ 0 :=
    mul_ne_zero (d.disc_lattice hd h).1 (pow_ne_zero 2 hf0)
  have hOm0 : Om ≠ 0 := by
    rintro rfl
    rw [map_zero] at hOm
    exact hom0 hOm
  refine ⟨Om, hOm.symm, hOm0, ?_⟩

  obtain ⟨a, b, hb0, hab, m, -, ha, hbm⟩ := d.de_pres hd h
  have hsigDe : ∀ (bb : Fin (d.D + 1)) (u : Kˣ),
      sigF (K := K) (D := d.D) (N := d.N) bb u (d.De hd h) = d.De hd h := by
    intro bb u
    have e1 := congrArg (sigF (K := K) (D := d.D) (N := d.N) bb u) hab
    have sa : sigP (N := d.N) bb u a = MvPolynomial.C ((u : K) ^ m bb) * a :=
      scale_multiHomogeneous bb u m a ha
    have sb : sigP (N := d.N) bb u b = MvPolynomial.C ((u : K) ^ m bb) * b :=
      scale_multiHomogeneous bb u m b hbm
    rw [d.sigF_algebraMap, map_mul, d.sigF_algebraMap, sa, sb, map_mul, map_mul, hab,
      ← d.algebraMap_K_KTf] at e1
    have hC : algebraMap K (KTf K d.D d.N) ((u : K) ^ m bb) ≠ 0 :=
      (map_ne_zero _).mpr (pow_ne_zero _ u.ne_zero)
    have hB : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hb0
    apply mul_right_cancel₀ (mul_ne_zero hC hB)
    linear_combination -e1
  set Eb : Fin (d.D + 1) → ℤ := fun bb => ∑ c, ∑ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne),
    d.nP h c d.wF (hd.a4.choose c) q * ((if bb = 0 then 0 else d.dg (d.gen q) : ℕ) : ℤ) with hEb
  have hsigf : ∀ (bb : Fin (d.D + 1)) (u : Kˣ),
      sigF (K := K) (D := d.D) (N := d.N) bb u (d.fDivE hd h) =
        algebraMap K (KTf K d.D d.N) (u : K) ^ Eb bb * d.fDivE hd h := by
    intro bb u
    have hκ : algebraMap K (KTf K d.D d.N) (u : K) ≠ 0 := (map_ne_zero _).mpr u.ne_zero
    simp only [fDivE, hEb]
    rw [map_prod, Finset.prod_congr rfl fun c _ => d.sig_fprod _ (hfin c) (fun q hq hn =>
      (d.good_primes_properties hd h c).2.1 q hq (by
        by_contra hno
        apply hn
        simp only [nP]
        rw [finsum_mem_def]
        refine finsum_eq_zero_of_forall_eq_zero fun w => ?_
        rw [Set.indicator_apply, if_neg (fun hw => hno ⟨w, hw⟩)])) bb u,
      Finset.prod_mul_distrib, HDiscOmL.prod_zpow hκ]
  have hEb : ∀ bb : Fin (d.D + 1), 2 * Eb bb =
      ((if bb = 0 then 0 else 2 * (d.aG h d.wF hd.a4.choose).toNat : ℕ) : ℤ) := by
    intro bb
    by_cases hbb : bb = 0
    · simp [hEb, hbb]
    · simp only [hEb, hbb, if_false]
      rw [Nat.cast_mul, Int.toNat_of_nonneg (d.aG_frame_nonneg hd h)]
      rfl
  intro s hs bb
  refine block_deg_of_scale bb _ Om (fun u => ?_) s hs
  apply IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
  change algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (sigP (N := d.N) bb u Om) =
    algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (MvPolynomial.C ((u : K) ^
      (if bb = 0 then 0 else 2 * (d.aG h d.wF hd.a4.choose).toNat)) * Om)
  rw [← d.sigF_algebraMap, map_mul, ← hOm, ← d.algebraMap_K_KTf, map_pow, ← zpow_natCast, ← hEb bb]
  have hk : algebraMap K (KTf K d.D d.N) (u : K) ^ (2 * Eb bb) =
      (algebraMap K (KTf K d.D d.N) (u : K) ^ Eb bb) ^ 2 := by
    rw [mul_comm, zpow_mul]
    norm_cast
  simp only [omE]
  rw [map_mul, map_pow, hsigDe, hsigf, hk]
  ring

end Data

end ReciprocityTheory.ChartRestriction.G.T0
