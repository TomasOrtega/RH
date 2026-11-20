import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.GaugeRatio
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.TB

namespace GaugeR

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

@[reducible] def barStar (H : Host E) : StarRing (𝓞 E) where
  star := H.bar
  star_involutive a := by
    apply RingOfIntegers.ext
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
  star_mul a b := by
    show H.bar (a * b) = H.bar b * H.bar a
    rw [map_mul, mul_comm]
  star_add a b := map_add H.bar a b

variable {H : Host E} {Dw : Datum H} {l : Level H}

def chi (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (σ : E →+* ℂ) : 𝓞 E →+* S :=
  (algebraMap c.F S).comp (embK c σ)

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use `show (ComplexEmbedding.conjugate σ) (a : E) = σ ((H.bar a : 𝓞 E) : E)`. Rewrite using `[H.bar_eq, ComplexEmbedding.conjugate_coe_eq, NumberField.IsCMField.complexEmbedding_complexConj]`.
-/
theorem embK_conj (c : Coeff l) (σ : E →+* ℂ) (a : 𝓞 E) :
    embK c (ComplexEmbedding.conjugate σ) a = embK c σ (H.bar a) := by
  apply Subtype.ext
  show (ComplexEmbedding.conjugate σ) (a : E) = σ ((H.bar a : 𝓞 E) : E)
  rw [H.bar_eq, ComplexEmbedding.conjugate_coe_eq, NumberField.IsCMField.complexEmbedding_complexConj]

/- English proof (translation)
Establish `hex : ∃ a : 𝓞 E, σ (a : E) ≠ τ (a : E)`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Apply `h` to reduce the goal to its premises. Use extensionality with `x`.

Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 E) x`. Rewrite using `[map_div₀, map_div₀]`. Conclude with `congrArg₂ (· / ·) (hc a) (hc b)`. Take `⟨a, ha⟩` from `hex`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Establish `hne : embK c σ a - embK c τ a ≠ 0`. Introduce `h0`. Apply `ha` to reduce the goal to its premises. Conclude with `congrArg (fun z : c.F => (z : ℂ)) (sub_eq_zero.mp h0)`. Establish `hu` using `(hne.isUnit).map (algebraMap c.F S)`.

Simplify `hu` using `[chi, map_sub]`.
-/
theorem hunit_chi (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (σ τ : E →+* ℂ) (h : σ ≠ τ) :
    ∃ a, IsUnit (chi c S σ a - chi c S τ a) := by
  classical
  have hex : ∃ a : 𝓞 E, σ (a : E) ≠ τ (a : E) := by
    by_contra hc
    push_neg at hc
    apply h
    ext x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
    rw [map_div₀, map_div₀]
    exact congrArg₂ (· / ·) (hc a) (hc b)
  obtain ⟨a, ha⟩ := hex
  refine ⟨a, ?_⟩
  have hne : embK c σ a - embK c τ a ≠ 0 := by
    intro h0
    apply ha
    exact congrArg (fun z : c.F => (z : ℂ)) (sub_eq_zero.mp h0)
  have hu := (hne.isUnit).map (algebraMap c.F S)
  simpa [chi, map_sub] using hu

def nu (Dw : Datum H) : Lt1 Dw ≃ Fin 1 × Fin (dL Dw) where
  toFun ℓ := ((0 : Fin 1), ltIdx Dw ℓ)
  invFun p := (ltIdx Dw).symm p.2
  left_inv ℓ := by simp
  right_inv p := Prod.ext (Subsingleton.elim _ _) (by simp)

/- English proof (translation)
Use `⟨Finsupp.equivMapDomain (nu Dw).symm x, ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.embDomain_eq_mapDomain, Equiv.coe_toEmbedding, ← Finsupp.equivMapDomain_eq_mapDomain]`. Use extensionality with `p`. Simplify using `[Finsupp.equivMapDomain_apply]`.
-/
theorem exists_embDomain (x : Fin 1 × Fin (dL Dw) →₀ ℕ) : ∃ y, Finsupp.embDomain (nu Dw).toEmbedding y = x := by
  refine ⟨Finsupp.equivMapDomain (nu Dw).symm x, ?_⟩
  rw [Finsupp.embDomain_eq_mapDomain, Equiv.coe_toEmbedding, ← Finsupp.equivMapDomain_eq_mapDomain]
  ext p
  simp [Finsupp.equivMapDomain_apply]

/- English proof (translation)
Use `show ∑ i ∈ (Finsupp.embDomain f y).support, (Finsupp.embDomain f y) i = ∑ i ∈ y.support, y i`. Rewrite using `[Finsupp.support_embDomain, Finset.sum_map]`. Simplify using the standard rewrite rules.
-/
theorem degree_embDomain {α β : Type} (f : α ↪ β) (y : α →₀ ℕ) : (Finsupp.embDomain f y).degree = y.degree := by
  classical
  show ∑ i ∈ (Finsupp.embDomain f y).support, (Finsupp.embDomain f y) i = ∑ i ∈ y.support, y i
  rw [Finsupp.support_embDomain, Finset.sum_map]
  simp

/- English proof (translation)
The claim follows from `MvPowerSeries.coeff_embDomain_rename _ _ _`.
-/
private theorem coeff_rename_emb_lemma {S : Type} [CommRing S] (p : MvPowerSeries (Lt1 Dw) S)
    (y : Lt1 Dw →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.embDomain (nu Dw).toEmbedding y) (MvPowerSeries.rename (nu Dw).toEmbedding p) =
      MvPowerSeries.coeff y p :=
  MvPowerSeries.coeff_embDomain_rename _ _ _

/- English proof (translation)
Use extensionality with `x`. Take `⟨y, rfl⟩` from `exists_embDomain (Dw := Dw) x`. Apply the tactic sequence `simp only [coeff_rename_emb_lemma, MvPowerSeries.coeff_rescale, Finsupp.prod_embDomain] <;> rfl`.
-/
theorem rename_rescale {S : Type} [CommRing S] (s : Fin 1 × Fin (dL Dw) → S) (p : MvPowerSeries (Lt1 Dw) S) :
    MvPowerSeries.rename (nu Dw).toEmbedding (MvPowerSeries.rescale (fun ℓ => s (nu Dw ℓ)) p) =
      MvPowerSeries.rescale s (MvPowerSeries.rename (nu Dw).toEmbedding p) := by
  ext x
  obtain ⟨y, rfl⟩ := exists_embDomain (Dw := Dw) x
  simp only [coeff_rename_emb_lemma, MvPowerSeries.coeff_rescale, Finsupp.prod_embDomain] <;> rfl

def sc (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (a : 𝓞 E) : Fin 1 × Fin (dL Dw) → S :=
  fun p => algebraMap c.F S (embK c ((ltIdx Dw).symm p.2).1 a)

/- English proof (translation)
Use `letI : StarRing (𝓞 E) := barStar H`. Set `r' : MvPowerSeries (Lt1 Dw) S` to `fun y => MvPowerSeries.coeff (Finsupp.embDomain (nu Dw).toEmbedding y) r`. Establish `hcr' : ∀ y, MvPowerSeries.coeff y r' = MvPowerSeries.coeff (Finsupp.embDomain (nu Dw).toEmbedding y) r` using `fun y => rfl`. Establish `hrr : MvPowerSeries.rename (nu Dw).toEmbedding r' = r`. Use extensionality with `x`.

Take `⟨y, rfl⟩` from `exists_embDomain (Dw := Dw) x`. Rewrite using `[coeff_rename_emb_lemma, hcr']`. Establish `hinj : ∀ p p' : MvPowerSeries (Lt1 Dw) S, MvPowerSeries.rename (nu Dw).toEmbedding p = MvPowerSeries.rename (nu Dw).toEmbedding p' → p = p'`. Introduce `p p' hpp`. Use extensionality with `y`.

Establish `hc` using `congrArg (MvPowerSeries.coeff (Finsupp.embDomain (nu Dw).toEmbedding y)) hpp`. Simplify `hc` using `only [coeff_rename_emb_lemma]`. Establish `hsc : ∀ b : 𝓞 E, (fun ℓ : Lt1 Dw => sc (Dw` using `Dw) c S b (nu Dw ℓ)) = fun ℓ => chi c S ℓ.1 b := by`. Introduce `b`. Use function extensionality and compare the values at `ℓ`.

Simplify using `[sc, chi, nu]`. Establish `hscale : ∀ (b : 𝓞 E) (p : MvPowerSeries (Lt1 Dw) S), MvPowerSeries.rename (nu Dw).toEmbedding (scaleBy (rk` using `Dw.mult) (chi c S) b p) = MvPowerSeries.rescale (sc (Dw := Dw) c S b) (MvPowerSeries.rename (nu Dw).toEmbedding p) := by`. Introduce `b p`. Apply the tactic sequence `(rw [← rename_rescale, hsc b]) <;> rfl`. Establish `hr0' : MvPowerSeries.constantCoeff r' = 1`.

Rewrite using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hcr', Finsupp.embDomain_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h1]`. Establish `hr' : ∀ a : 𝓞 E, scaleBy (rk` using `Dw.mult) (chi c S) (1 + a * star a) r' = scaleBy (rk := Dw.mult) (chi c S) a r' ^ 2 * r' * scaleBy (rk := Dw.mult) (chi c S) (a * star a) r' := by`. Introduce `a`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, map_pow, hscale, hscale, hscale, hrr]`.

Conclude with `hr a`. Establish `hcc : ∀ (σ : E →+* ℂ) (a : 𝓞 E), chi c S (ComplexEmbedding.conjugate σ) a = chi c S σ (star a)`. Introduce `σ a`. Simplify using `only [chi, RingHom.comp_apply]`. Apply the tactic sequence `(rw [embK_conj]) <;> rfl`.

Take `⟨q', hq0, hqdeg, hqpair, hqexp⟩` from `hR (𝓞 E) S (E →+* ℂ) Dw.mult (chi c S) ComplexEmbedding.conjugate hcc (fun σ τ hστ => hunit_chi c S σ τ hστ) r' hr0' hr'`. Establish `hq0r : MvPowerSeries.constantCoeff (MvPowerSeries.rename (nu Dw).toEmbedding q') = 0`. Rewrite using `[MvPowerSeries.constantCoeff_rename, hq0]`. Use `⟨MvPowerSeries.rename (nu Dw).toEmbedding q', hq0r, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `m hm`.

Take `⟨y, rfl⟩` from `exists_embDomain (Dw := Dw) m`. Rewrite `hm` using `[coeff_rename_emb_lemma]`. Rewrite using `[degree_embDomain]`. Conclude with `hqdeg y hm`. Introduce `ℓ ℓ' hm`.

Apply the tactic sequence `have hsum : Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ) 1 + Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ') 1 = Finsupp.embDomain (nu Dw).toEmbedding (Finsupp.single ℓ 1 + Finsupp.single ℓ' 1) := by (rw [Finsupp.embDomain_add, Finsupp.embDomain_single, Finsupp.embDomain_single]) <;> rfl`. Rewrite `hm` using `[hsum, coeff_rename_emb_lemma]`. Conclude with `hqpair ℓ ℓ' hm`. Use extensionality with `m`. Take `⟨y, rfl⟩` from `exists_embDomain (Dw := Dw) m`.

Rewrite using `[← hrr, coeff_rename_emb_lemma, hqexp, PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hq0), PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hq0r)]`. Use `congr 1`. Use function extensionality and compare the values at `d`. Rewrite using `[← map_pow, coeff_rename_emb_lemma]`.
-/
theorem ratio_exp (hR : GaugeRatioSt) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    (r : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (h1 : MvPowerSeries.constantCoeff r = 1)
    (hr : ∀ a : 𝓞 E, MvPowerSeries.rescale (sc (Dw := Dw) c S (1 + a * H.bar a)) r =
      MvPowerSeries.rescale (sc (Dw := Dw) c S a) r ^ 2 * r * MvPowerSeries.rescale (sc (Dw := Dw) c S (a * H.bar a)) r) :
    ∃ q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S, MvPowerSeries.constantCoeff q = 0 ∧
      (∀ m, MvPowerSeries.coeff m q ≠ 0 → m.degree = 2) ∧
      (∀ ℓ ℓ' : Lt1 Dw, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ) 1 +
          Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ') 1) q ≠ 0 → ℓ'.1 = ComplexEmbedding.conjugate ℓ.1) ∧
      r = PowerSeries.subst q (PowerSeries.exp S) := by
  letI : StarRing (𝓞 E) := barStar H
  let r' : MvPowerSeries (Lt1 Dw) S := fun y => MvPowerSeries.coeff (Finsupp.embDomain (nu Dw).toEmbedding y) r
  have hcr' : ∀ y, MvPowerSeries.coeff y r' = MvPowerSeries.coeff (Finsupp.embDomain (nu Dw).toEmbedding y) r :=
    fun y => rfl
  have hrr : MvPowerSeries.rename (nu Dw).toEmbedding r' = r := by
    ext x
    obtain ⟨y, rfl⟩ := exists_embDomain (Dw := Dw) x
    rw [coeff_rename_emb_lemma, hcr']
  have hinj : ∀ p p' : MvPowerSeries (Lt1 Dw) S,
      MvPowerSeries.rename (nu Dw).toEmbedding p = MvPowerSeries.rename (nu Dw).toEmbedding p' → p = p' := by
    intro p p' hpp
    ext y
    have hc := congrArg (MvPowerSeries.coeff (Finsupp.embDomain (nu Dw).toEmbedding y)) hpp
    simpa only [coeff_rename_emb_lemma] using hc
  have hsc : ∀ b : 𝓞 E, (fun ℓ : Lt1 Dw => sc (Dw := Dw) c S b (nu Dw ℓ)) = fun ℓ => chi c S ℓ.1 b := by
    intro b
    funext ℓ
    simp [sc, chi, nu]
  have hscale : ∀ (b : 𝓞 E) (p : MvPowerSeries (Lt1 Dw) S),
      MvPowerSeries.rename (nu Dw).toEmbedding (scaleBy (rk := Dw.mult) (chi c S) b p) =
        MvPowerSeries.rescale (sc (Dw := Dw) c S b) (MvPowerSeries.rename (nu Dw).toEmbedding p) := by
    intro b p
    (rw [← rename_rescale, hsc b]) <;> rfl
  have hr0' : MvPowerSeries.constantCoeff r' = 1 := by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hcr', Finsupp.embDomain_zero,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h1]
  have hr' : ∀ a : 𝓞 E, scaleBy (rk := Dw.mult) (chi c S) (1 + a * star a) r' =
      scaleBy (rk := Dw.mult) (chi c S) a r' ^ 2 * r' * scaleBy (rk := Dw.mult) (chi c S) (a * star a) r' := by
    intro a
    apply hinj
    rw [map_mul, map_mul, map_pow, hscale, hscale, hscale, hrr]
    exact hr a
  have hcc : ∀ (σ : E →+* ℂ) (a : 𝓞 E), chi c S (ComplexEmbedding.conjugate σ) a = chi c S σ (star a) := by
    intro σ a
    simp only [chi, RingHom.comp_apply]
    (rw [embK_conj]) <;> rfl
  obtain ⟨q', hq0, hqdeg, hqpair, hqexp⟩ :=
    hR (𝓞 E) S (E →+* ℂ) Dw.mult (chi c S) ComplexEmbedding.conjugate hcc
      (fun σ τ hστ => hunit_chi c S σ τ hστ) r' hr0' hr'
  have hq0r : MvPowerSeries.constantCoeff (MvPowerSeries.rename (nu Dw).toEmbedding q') = 0 := by
    rw [MvPowerSeries.constantCoeff_rename, hq0]
  refine ⟨MvPowerSeries.rename (nu Dw).toEmbedding q', hq0r, ?_, ?_, ?_⟩
  · intro m hm
    obtain ⟨y, rfl⟩ := exists_embDomain (Dw := Dw) m
    rw [coeff_rename_emb_lemma] at hm
    rw [degree_embDomain]
    exact hqdeg y hm
  · intro ℓ ℓ' hm
    have hsum : Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ) 1 + Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ') 1 =
        Finsupp.embDomain (nu Dw).toEmbedding (Finsupp.single ℓ 1 + Finsupp.single ℓ' 1) := by
      (rw [Finsupp.embDomain_add, Finsupp.embDomain_single, Finsupp.embDomain_single]) <;> rfl
    rw [hsum, coeff_rename_emb_lemma] at hm
    exact hqpair ℓ ℓ' hm
  · ext m
    obtain ⟨y, rfl⟩ := exists_embDomain (Dw := Dw) m
    rw [← hrr, coeff_rename_emb_lemma, hqexp,
      PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hq0),
      PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hq0r)]
    congr 1
    funext d
    rw [← map_pow, coeff_rename_emb_lemma]

end GaugeR

end Formalism.MainNotions.ModuliIntegralCharts.H1
