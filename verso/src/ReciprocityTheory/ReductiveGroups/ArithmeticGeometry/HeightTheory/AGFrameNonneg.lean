import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormFactorizationClause
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GeneratorNeZeroOfHeight
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FsumEqSum

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

/- English proof (translation)
Establish `hespec` using `hd.a4.choose_spec`. Unfold `aG`. Use `Finset.sum_nonneg fun c _ => ?_` and prove the remaining obligations. Establish `hec : hd.a4.choose c ∈ 𝒜 c d.wF ∧ hd.a4.choose c ≠ 0` using `hespec.1 c`. Establish `hk : ∃ k, d.thp (hd.sel k) c ≠ 0`.

Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Take `⟨q, hq, p, hp⟩` from `hespec.2.2 (fun _ => 1)`. Establish `e1` using `hp c`. Simplify using `only [mul_one] at e1`.

Apply `hq c` to reduce the goal to its premises. Rewrite using `[e1]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hno k, ratio_eq_of_eq_smul hec.2 (zero_smul (Ω c) (hd.a4.choose c)).symm, map_zero, mul_zero]`. Take `⟨k, hk⟩` from `hk`.

Establish `htm : d.thp (hd.sel k) c ∈ 𝒜 c d.wF` using `hd.thp_mem _ c`. Establish `hr` using `eq_ratio_smul_on_line d (hd := hd) htm hec.1 hec.2`. Establish `hr0 : ratio (Ω` using `Ω c) (d.thp (hd.sel k) c) (hd.a4.choose c) ≠ 0 := by`. Introduce `h0`. Apply `hk` to reduce the goal to its premises.

Rewrite using `[hr, h0, zero_smul]`. Establish `hthpmem : d.thp (hd.sel k) ∈ d.Thp`. Rewrite using `[hd.Thp_span]`. Conclude with `Submodule.subset_span ⟨_, rfl⟩`. Establish `hord : ∀ v, d.admitted c v → 0 ≤ d.ord c v d.wF (d.thp (hd.sel k) c)` using `fun v hv => hd.ord_nonneg_Thp c v hv _ hthpmem hk`.

Establish `x2` using `d.good_primes_properties hd h c`. Establish `hsplit : ∀ p ∈ d.HtOne, d.nP h c d.wF (d.thp (hd.sel k) c) p = d.nP h c d.wF (hd.a4.choose c) p + ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p), (d.fze h c w : ℤ) * WithTop.untopD 0 (d.Wres c w (ratio (Ω` using `Ω c) (d.thp (hd.sel k) c) (hd.a4.choose c))) := by`. Introduce `p hp`. Establish `e2` using `d.nP_smul hd h c hec.1 hec.2 hr0 hp`. Rewrite `e2` using `[← hr]`.

Conclude with `e2`. Establish `hkey` using `d.key_degree hd h c _ hr0`. Establish `hfe` using `x2.2.2.1 _ _ hec.1 hec.2`. Establish `hfm` using `d.use₈ hd h c _ hr0`. Establish `eq1 : (∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), d.nP h c d.wF (d.thp (hd.sel k) c) p * (d.dg (d.gen p) : ℤ)) = (∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), d.nP h c d.wF (hd.a4.choose c) p * (d.dg (d.gen p) : ℤ)) + ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), …` using `Ω c) (d.thp (hd.sel k) c) (hd.a4.choose c)))) * (d.dg (d.gen p) : ℤ) := by`.

Rewrite using `[← finsum_mem_add_distrib' ?_ ?_]`. Conclude with `finsum_mem_congr rfl fun p hp => by rw [hsplit p hp, add_mul]`. Use `hfe.subset ?_` and prove the remaining obligations. Introduce and unpack `p ⟨hp, hne⟩`. Conclude with `⟨hp, fun h0 => hne (by simp [h0])⟩`.

Use `hfm.subset ?_` and prove the remaining obligations. Introduce and unpack `p ⟨hp, hne⟩`. Conclude with `⟨hp, fun h0 => hne (by simp [h0])⟩`. Establish `hnn : 0 ≤ ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), d.nP h c d.wF (d.thp (hd.sel k) c) p * (d.dg (d.gen p) : ℤ)` using `finsum_nonneg fun p => finsum_nonneg fun hp => mul_nonneg (d.nP_nonneg hd h c hp _ _ hord) (Nat.cast_nonneg _)`. Rewrite `hnn` using `[eq1, hkey, add_zero]`.

Conclude with `hnn`.
-/
theorem aG_frame_nonneg (hd : d.AxH 𝒜) (h : d.S1) : 0 ≤ d.aG h d.wF hd.a4.choose := by
  classical
  have hespec := hd.a4.choose_spec
  unfold aG
  refine Finset.sum_nonneg fun c _ => ?_
  have hec : hd.a4.choose c ∈ 𝒜 c d.wF ∧ hd.a4.choose c ≠ 0 := hespec.1 c
  have hk : ∃ k, d.thp (hd.sel k) c ≠ 0 := by
    by_contra hno
    push_neg at hno
    obtain ⟨q, hq, p, hp⟩ := hespec.2.2 (fun _ => 1)
    have e1 := hp c
    simp only [mul_one] at e1
    apply hq c
    rw [e1]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hno k, ratio_eq_of_eq_smul hec.2 (zero_smul (Ω c) (hd.a4.choose c)).symm, map_zero, mul_zero]
  obtain ⟨k, hk⟩ := hk
  have htm : d.thp (hd.sel k) c ∈ 𝒜 c d.wF := hd.thp_mem _ c
  have hr := eq_ratio_smul_on_line d (hd := hd) htm hec.1 hec.2
  have hr0 : ratio (Ω := Ω c) (d.thp (hd.sel k) c) (hd.a4.choose c) ≠ 0 := by
    intro h0
    apply hk
    rw [hr, h0, zero_smul]
  have hthpmem : d.thp (hd.sel k) ∈ d.Thp := by
    rw [hd.Thp_span]; exact Submodule.subset_span ⟨_, rfl⟩
  have hord : ∀ v, d.admitted c v → 0 ≤ d.ord c v d.wF (d.thp (hd.sel k) c) :=
    fun v hv => hd.ord_nonneg_Thp c v hv _ hthpmem hk
  have x2 := d.good_primes_properties hd h c
  have hsplit : ∀ p ∈ d.HtOne, d.nP h c d.wF (d.thp (hd.sel k) c) p =
      d.nP h c d.wF (hd.a4.choose c) p +
      ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
        (d.fze h c w : ℤ) *
          WithTop.untopD 0 (d.Wres c w (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (hd.a4.choose c))) := by
    intro p hp
    have e2 := d.nP_smul hd h c hec.1 hec.2 hr0 hp
    rw [← hr] at e2
    exact e2
  have hkey := d.key_degree hd h c _ hr0
  have hfe := x2.2.2.1 _ _ hec.1 hec.2
  have hfm := d.use₈ hd h c _ hr0
  have eq1 : (∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        d.nP h c d.wF (d.thp (hd.sel k) c) p * (d.dg (d.gen p) : ℤ)) =
      (∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        d.nP h c d.wF (hd.a4.choose c) p * (d.dg (d.gen p) : ℤ)) +
      ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
          (d.fze h c w : ℤ) *
            WithTop.untopD 0 (d.Wres c w (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (hd.a4.choose c)))) *
          (d.dg (d.gen p) : ℤ) := by
    rw [← finsum_mem_add_distrib' ?_ ?_]
    · exact finsum_mem_congr rfl fun p hp => by rw [hsplit p hp, add_mul]
    · refine hfe.subset ?_
      rintro p ⟨hp, hne⟩
      exact ⟨hp, fun h0 => hne (by simp [h0])⟩
    · refine hfm.subset ?_
      rintro p ⟨hp, hne⟩
      exact ⟨hp, fun h0 => hne (by simp [h0])⟩
  have hnn : 0 ≤ ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      d.nP h c d.wF (d.thp (hd.sel k) c) p * (d.dg (d.gen p) : ℤ) :=
    finsum_nonneg fun p => finsum_nonneg fun hp =>
      mul_nonneg (d.nP_nonneg hd h c hp _ _ hord) (Nat.cast_nonneg _)
  rw [eq1, hkey, add_zero] at hnn
  exact hnn

end Data

end ReciprocityTheory.ChartRestriction.G.T0
