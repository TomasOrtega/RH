import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.SecInjG
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.IdealSplit

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

/- English proof (translation)
Introduce `hTj hRead hKer hLev hDesc hFet hOnto hPul p _ D G L sc E _ _ gb w q _ r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hu hb hi h hint htj M₁ M₂ c₁ c₂ a₁ a₂ n₁ n₂ _ C₁ C₂ W`. Establish `hq : q.Prime` using `Fact.out`. Take `⟨f, ⟨hf, ⟨mf⟩⟩, -⟩` from `X₂.M.rep _ _ X₁.Y.univ`. Establish `hqw : (q : 𝓞 D.F) ∈ 𝔴'` using `hu (Ideal.subset_span (Set.mem_insert _ _))`. Establish `hd : Ideal.absNorm 𝔴' ∣ q ^ Module.finrank ℤ (𝓞 D.F)`.

Use `Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem 𝔴').2 hqw)` as an intermediate fact. Rewrite `this` using `[Ideal.absNorm_span_natCast]`. Then use the resulting hypothesis. Take `⟨f', -, hf'⟩` from `(Nat.dvd_prime_pow hq).1 hd`. Establish `hpos : 0 < f'` using `Nat.pos_of_ne_zero fun h0 => hmax.ne_top (Ideal.absNorm_eq_one_iff.1 (by simpa [h0] using hf'))`. Establish `he : Ideal.absNorm 𝔴' ^ i = q ^ (f' * i)` using `by rw [hf', pow_mul]`.

Establish `he' : 0 < i → 0 < f' * i` using `fun h => Nat.mul_pos hpos h`. Take `⟨Tj⟩` from `hTj q (datAt S.atq S.sp) (Ow w) S.b N₀ X₂.lev.1 X₂.lev.2.1 S.std.pmem S.std.m1 r 𝔴' i (f' * i) hmax hu hi he' X₂.M`. Take `⟨B⟩` from `hRead p D G L sc E gb w q r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hu hb hi h hint htj M₁ M₂ c₁ c₂ a₁ a₂ n₁ n₂ C₁ C₂ W f mf hf _ he he' Tj`. Establish `k1` using `hKer p D G L sc E gb w q r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hu hb hi h hint htj M₁ M₂ c₁ c₂ a₁ a₂ n₁ n₂ C₁ C₂ W f mf hf _ he he' Tj B`. Establish `k2` using `hLev p D G L sc E gb w q r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hu hb hi h hint htj M₁ M₂ c₁ c₂ a₁ a₂ n₁ n₂ C₁ C₂ W f mf hf _ he he' Tj B`.

Take `⟨hfin, het⟩` from `hFet p D G L sc E gb w q r 𝔴 _ X₁.site k T M₁ c₁ a₁ n₁ C₁`. Establish `honto` using `hOnto p D G L sc E gb w q r 𝔴 _ X₁.site k T M₁ c₁ a₁ n₁ C₁`. Establish `hsm : Smooth X₁.Y.s` using `by haveI := X₁.M.smooth haveI : Smooth X₁.M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) X₁.M.s haveI := X₁.et`. Rewrite using `[← X₁.ov]`. Use `infer_instance`.

Take `⟨y', hy, hys⟩` from `hDesc (Ow w) E _ _ _ _ X₁.Y.s _ C₁.j C₁.ov hsm hfin het honto f Tj.s B.y Tj.fin B.ys k1`. Take `⟨P⟩` from `hPul q (datAt S.atq S.sp) (Ow w) S.b N₀ X₂.lev.1 X₂.lev.2.1 X₂.M r 𝔴' i _ Tj _ f _ hf X₁.Y.univ mf y' hys`. Take `⟨t, ht, htπ⟩` from `hDesc (Ow w) E _ _ _ _ X₁.Y.s _ C₁.j C₁.ov hsm hfin het honto (y' ≫ Tj.t) X₂.π (W.π ≫ C₂.j) X₂.fin (by rw [← Category.assoc C₁.j, hy, B.yt, Category.assoc]) fun Ω _ _ x x' e => k2 Ω x x' e (k1 Ω x x' e)`. Establish `hw : (P.ψ.left ≫ P.m'.φ ≫ Tj.mt.φ) ≫ X₂.M.univ.A.hom = (X₁.Y.univ.A.hom ≫ t) ≫ X₂.π`. Rewrite using `[Category.assoc, Category.assoc, Tj.mt.cart.1.w, ← Category.assoc P.m'.φ, P.m'.cart.1.w, Category.assoc, ← Category.assoc, Over.w P.ψ, Category.assoc, htπ]`.

Establish `hfa : C₁.m.φ ≫ P.m₀.φ = B.fa` using `Tj.ms.cart.1.hom_ext (by rw [Category.assoc, P.tri, B.ms]) (by rw [Category.assoc, P.m₀.cart.1.w, ← Category.assoc, C₁.m.cart.1.w, Category.assoc, hy, B.ca.1.w])`. Use `⟨⟨t, ?_, X₂.mπ.cart.1.lift _ _ hw, X₂.mπ.cart.1.lift_snd _ _ _⟩, ht, X₂.mπ.cart.1.hom_ext ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[← X₂.ov, ← Category.assoc, htπ, Category.assoc, ← Tj.st, ← Category.assoc, hys, hf]`. Rewrite using `[Category.assoc, IsPullback.lift_fst, ← Category.assoc P.ψ.left, ← P.sq, Category.assoc, ← Category.assoc, hfa, ← Category.assoc, B.sq, Category.assoc, B.mt]`. Simplify using `only [Category.assoc]`.

Rewrite using `[Category.assoc, IsPullback.lift_snd, ← Category.assoc, C₁.m.cart.1.w, Category.assoc, ht]`. Simplify using `only [Category.assoc]`. Rewrite using `[C₂.m.cart.1.w, ← Category.assoc W.φ.φ, W.φ.cart.1.w, Category.assoc, ← Category.assoc W.ψ.left, Over.w W.ψ]`.
-/
theorem UpperTheory.Gal.FiniteEtaleModels.stepB_of :
    TjExG → BRead → BKer → BLev → DescExt → BaseFet → BaseOnto → UpperTheory.Gal.crystallineComparison.Mod.PulledEx → StepB := by
  intro hTj hRead hKer hLev hDesc hFet hOnto hPul p _ D G L sc E _ _ gb w q _ r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hu hb hi h hint htj
    M₁ M₂ c₁ c₂ a₁ a₂ n₁ n₂ _ C₁ C₂ W
  have hq : q.Prime := Fact.out
  obtain ⟨f, ⟨hf, ⟨mf⟩⟩, -⟩ := X₂.M.rep _ _ X₁.Y.univ
  have hqw : (q : 𝓞 D.F) ∈ 𝔴' := hu (Ideal.subset_span (Set.mem_insert _ _))
  have hd : Ideal.absNorm 𝔴' ∣ q ^ Module.finrank ℤ (𝓞 D.F) := by
    have := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem 𝔴').2 hqw)
    rwa [Ideal.absNorm_span_natCast] at this
  obtain ⟨f', -, hf'⟩ := (Nat.dvd_prime_pow hq).1 hd
  have hpos : 0 < f' := Nat.pos_of_ne_zero fun h0 => hmax.ne_top (Ideal.absNorm_eq_one_iff.1 (by simpa [h0] using hf'))
  have he : Ideal.absNorm 𝔴' ^ i = q ^ (f' * i) := by rw [hf', pow_mul]
  have he' : 0 < i → 0 < f' * i := fun h => Nat.mul_pos hpos h
  obtain ⟨Tj⟩ := hTj q (datAt S.atq S.sp) (Ow w) S.b N₀ X₂.lev.1 X₂.lev.2.1 S.std.pmem S.std.m1 r 𝔴' i (f' * i) hmax hu hi he' X₂.M
  obtain ⟨B⟩ := hRead p D G L sc E gb w q r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hu hb hi h hint htj M₁ M₂ c₁ c₂ a₁ a₂ n₁ n₂ C₁ C₂ W f mf hf
    _ he he' Tj
  have k1 := hKer p D G L sc E gb w q r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hu hb hi h hint htj M₁ M₂ c₁ c₂ a₁ a₂ n₁ n₂ C₁ C₂ W f mf hf
    _ he he' Tj B
  have k2 := hLev p D G L sc E gb w q r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hu hb hi h hint htj M₁ M₂ c₁ c₂ a₁ a₂ n₁ n₂ C₁ C₂ W f mf hf
    _ he he' Tj B
  obtain ⟨hfin, het⟩ := hFet p D G L sc E gb w q r 𝔴 _ X₁.site k T M₁ c₁ a₁ n₁ C₁
  have honto := hOnto p D G L sc E gb w q r 𝔴 _ X₁.site k T M₁ c₁ a₁ n₁ C₁
  have hsm : Smooth X₁.Y.s := by
    haveI := X₁.M.smooth
    haveI : Smooth X₁.M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) X₁.M.s
    haveI := X₁.et
    rw [← X₁.ov]
    infer_instance
  obtain ⟨y', hy, hys⟩ := hDesc (Ow w) E _ _ _ _ X₁.Y.s _ C₁.j C₁.ov hsm hfin het honto f Tj.s B.y Tj.fin B.ys k1
  obtain ⟨P⟩ := hPul q (datAt S.atq S.sp) (Ow w) S.b N₀ X₂.lev.1 X₂.lev.2.1 X₂.M r 𝔴' i _ Tj _ f _ hf X₁.Y.univ mf y' hys
  obtain ⟨t, ht, htπ⟩ := hDesc (Ow w) E _ _ _ _ X₁.Y.s _ C₁.j C₁.ov hsm hfin het honto (y' ≫ Tj.t) X₂.π (W.π ≫ C₂.j) X₂.fin
    (by rw [← Category.assoc C₁.j, hy, B.yt, Category.assoc]) fun Ω _ _ x x' e => k2 Ω x x' e (k1 Ω x x' e)
  have hw : (P.ψ.left ≫ P.m'.φ ≫ Tj.mt.φ) ≫ X₂.M.univ.A.hom = (X₁.Y.univ.A.hom ≫ t) ≫ X₂.π := by
    rw [Category.assoc, Category.assoc, Tj.mt.cart.1.w, ← Category.assoc P.m'.φ, P.m'.cart.1.w, Category.assoc, ← Category.assoc,
      Over.w P.ψ, Category.assoc, htπ]
  have hfa : C₁.m.φ ≫ P.m₀.φ = B.fa := Tj.ms.cart.1.hom_ext
    (by rw [Category.assoc, P.tri, B.ms])
    (by rw [Category.assoc, P.m₀.cart.1.w, ← Category.assoc, C₁.m.cart.1.w, Category.assoc, hy, B.ca.1.w])
  refine ⟨⟨t, ?_, X₂.mπ.cart.1.lift _ _ hw, X₂.mπ.cart.1.lift_snd _ _ _⟩, ht, X₂.mπ.cart.1.hom_ext ?_ ?_⟩
  · rw [← X₂.ov, ← Category.assoc, htπ, Category.assoc, ← Tj.st, ← Category.assoc, hys, hf]
  · rw [Category.assoc, IsPullback.lift_fst, ← Category.assoc P.ψ.left, ← P.sq, Category.assoc, ← Category.assoc, hfa,
      ← Category.assoc, B.sq, Category.assoc, B.mt]
    simp only [Category.assoc]
  · rw [Category.assoc, IsPullback.lift_snd, ← Category.assoc, C₁.m.cart.1.w, Category.assoc, ht]
    simp only [Category.assoc]
    rw [C₂.m.cart.1.w, ← Category.assoc W.φ.φ, W.φ.cart.1.w, Category.assoc, ← Category.assoc W.ψ.left, Over.w W.ψ]
