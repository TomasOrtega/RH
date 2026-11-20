import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceQuot
import GroundTheory.AutomorphicForms.SmoothRep

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

section Mean

open GroundTheory.Automorphic (stabilizerOf mem_stabilizerOf)

variable {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

private noncomputable def mean (T : Subgroup H) [T.FiniteIndex] (v : V) : V :=
  (Nat.card (H ⧸ T) : ℂ)⁻¹ • ∑ q : H ⧸ T, ρ q.out v

/- English proof (translation)
Rewrite using `[Nat.cast_ne_zero]`. Conclude with `Subgroup.FiniteIndex.index_ne_zero`.
-/
private theorem card_ne (T : Subgroup H) [T.FiniteIndex] : (Nat.card (H ⧸ T) : ℂ) ≠ 0 := by
  rw [Nat.cast_ne_zero]
  exact Subgroup.FiniteIndex.index_ne_zero

/- English proof (translation)
Take `⟨t, ht⟩` from `QuotientGroup.mk_out_eq_mul T x`. Rewrite using `[ht, map_mul, Module.End.mul_apply, hv t t.2]`.
-/
private theorem out_apply {T : Subgroup H} {v : V} (hv : ∀ t ∈ T, ρ t v = v) (x : H) :
    ρ (x : H ⧸ T).out v = ρ x v := by
  obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul T x
  rw [ht, map_mul, Module.End.mul_apply, hv t t.2]

/- English proof (translation)
Unfold `mean`. Establish `hcard : Nat.card (H ⧸ T') = Nat.card (H ⧸ T) * Nat.card (T ⧸ T'.subgroupOf T)`. Rewrite using `[Nat.card_congr (Subgroup.quotientEquivProdOfLE hle), Nat.card_prod]`. Establish `hsum : ∑ q : H ⧸ T', ρ q.out v = ∑ x : (H ⧸ T) × (T ⧸ T'.subgroupOf T), ρ x.1.out v`. Use `Fintype.sum_equiv (Subgroup.quotientEquivProdOfLE hle) _ _ ?_` and prove the remaining obligations.

Introduce `q`. Take `⟨x, rfl⟩` from `QuotientGroup.mk_surjective q`. Rewrite using `[Subgroup.quotientEquivProdOfLE_apply]`. Use `show ρ (x : H ⧸ T').out v = ρ (x : H ⧸ T).out v`. Rewrite using `[out_apply ρ (fun t ht => hv t (hle ht)), out_apply ρ hv]`.

Establish `hm : (Nat.card (T ⧸ T'.subgroupOf T) : ℂ) ≠ 0`. Rewrite using `[Nat.cast_ne_zero]`. Conclude with `Subgroup.FiniteIndex.index_ne_zero`. Rewrite using `[hsum, Fintype.sum_prod_type, hcard]`. Simplify using `only [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ]`.

Rewrite using `[← Finset.smul_sum, smul_smul]`. Use `congr 1`. Rewrite using `[Nat.cast_mul, mul_inv, mul_assoc, inv_mul_cancel₀ hm, mul_one]`.
-/
private theorem mean_eq {T' T : Subgroup H} [T'.FiniteIndex] [T.FiniteIndex] (hle : T' ≤ T) {v : V}
    (hv : ∀ t ∈ T, ρ t v = v) : mean ρ T' v = mean ρ T v := by
  unfold mean
  have hcard : Nat.card (H ⧸ T') = Nat.card (H ⧸ T) * Nat.card (T ⧸ T'.subgroupOf T) := by
    rw [Nat.card_congr (Subgroup.quotientEquivProdOfLE hle), Nat.card_prod]
  have hsum : ∑ q : H ⧸ T', ρ q.out v =
      ∑ x : (H ⧸ T) × (T ⧸ T'.subgroupOf T), ρ x.1.out v := by
    refine Fintype.sum_equiv (Subgroup.quotientEquivProdOfLE hle) _ _ ?_
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [Subgroup.quotientEquivProdOfLE_apply]
    show ρ (x : H ⧸ T').out v = ρ (x : H ⧸ T).out v
    rw [out_apply ρ (fun t ht => hv t (hle ht)), out_apply ρ hv]
  have hm : (Nat.card (T ⧸ T'.subgroupOf T) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Subgroup.FiniteIndex.index_ne_zero
  rw [hsum, Fintype.sum_prod_type, hcard]
  simp only [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ]
  rw [← Finset.smul_sum, smul_smul]
  congr 1
  rw [Nat.cast_mul, mul_inv, mul_assoc, inv_mul_cancel₀ hm, mul_one]

/- English proof (translation)
Unfold `mean`. Rewrite using `[map_smul, map_sum]`. Use `congr 1`. Use `Fintype.sum_equiv (MulAction.toPerm h) _ _ ?_` and prove the remaining obligations. Introduce `q`.

Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Establish `hq : ((h * q.out : H) : H ⧸ T) = h • q`. Rewrite using `[← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']`. Rewrite using `[← out_apply ρ hv (h * q.out), hq]`. Both sides reduce to the same expression.
-/
private theorem mean_mem {T : Subgroup H} [T.FiniteIndex] {v : V} (hv : ∀ t ∈ T, ρ t v = v) (h : H) :
    ρ h (mean ρ T v) = mean ρ T v := by
  unfold mean
  rw [map_smul, map_sum]
  congr 1
  refine Fintype.sum_equiv (MulAction.toPerm h) _ _ ?_
  intro q
  rw [← Module.End.mul_apply, ← map_mul]
  have hq : ((h * q.out : H) : H ⧸ T) = h • q := by
    rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
  rw [← out_apply ρ hv (h * q.out), hq]
  rfl

/- English proof (translation)
Simplify using `only [mean, map_smul, map_sum, hp, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ (card_ne T), one_smul]`.
-/
private theorem mean_lin {W : Type} [AddCommGroup W] [Module ℂ W] (T : Subgroup H) [T.FiniteIndex]
    (p : V →ₗ[ℂ] W) {v : V} (hp : ∀ h, p (ρ h v) = p v) : p (mean ρ T v) = p v := by
  simp only [mean, map_smul, map_sum, hp, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ (card_ne T), one_smul]

/- English proof (translation)
Simplify using `only [mean, map_add, Finset.sum_add_distrib, smul_add]`.
-/
private theorem mean_add (T : Subgroup H) [T.FiniteIndex] (x y : V) :
    mean ρ T (x + y) = mean ρ T x + mean ρ T y := by
  simp only [mean, map_add, Finset.sum_add_distrib, smul_add]

/- English proof (translation)
Simplify using `only [mean, map_smul, ← Finset.smul_sum]`. Conclude with `smul_comm _ _ _`.
-/
private theorem mean_smul (T : Subgroup H) [T.FiniteIndex] (c : ℂ) (x : V) :
    mean ρ T (c • x) = c • mean ρ T x := by
  simp only [mean, map_smul, ← Finset.smul_sum]
  exact smul_comm _ _ _

/- English proof (translation)
Unfold `mean`. Use `congr 1`. Use `Fintype.sum_equiv (Equiv.mulRight (h : H ⧸ T)) _ _ ?_` and prove the remaining obligations. Introduce `q`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`.

Establish `hq : ((q.out * h : H) : H ⧸ T) = q * (h : H ⧸ T)`. Rewrite using `[QuotientGroup.mk_mul, QuotientGroup.out_eq']`. Rewrite using `[← out_apply ρ hv (q.out * h), hq]`. Both sides reduce to the same expression.
-/
private theorem mean_act {T : Subgroup H} [T.FiniteIndex] [T.Normal] {v : V} (hv : ∀ t ∈ T, ρ t v = v)
    (h : H) : mean ρ T (ρ h v) = mean ρ T v := by
  unfold mean
  congr 1
  refine Fintype.sum_equiv (Equiv.mulRight (h : H ⧸ T)) _ _ ?_
  intro q
  rw [← Module.End.mul_apply, ← map_mul]
  have hq : ((q.out * h : H) : H ⧸ T) = q * (h : H ⧸ T) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
  rw [← out_apply ρ hv (q.out * h), hq]
  rfl

/- English proof (translation)
Set `E : V → V` to `fun v => @mean H V _ _ _ ρ (stabilizerOf ρ v) (hfin v) v`. Establish `hE : ∀ (v : V) (T : Subgroup H) [T.FiniteIndex], T ≤ stabilizerOf ρ v → E v = mean ρ T v`. Introduce `v T _ hle`. Use `haveI := hfin v`. Conclude with `(mean_eq ρ hle (fun t ht => mem_stabilizerOf.1 ht)).symm`.

Establish `hfx : ∀ v, ∀ t ∈ stabilizerOf ρ v, ρ t v = v` using `fun v t ht => mem_stabilizerOf.1 ht`. Use `⟨{ toFun := E, map_add' := ?_, map_smul' := ?_ }, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y haveI := hfin x haveI := hfin y haveI := hfin (x + y) show E (x + y) = E x + E y`. Rewrite using `[hE (x + y) (stabilizerOf ρ x ⊓ stabilizerOf ρ y ⊓ stabilizerOf ρ (x + y)) inf_le_right, hE x (stabilizerOf ρ x ⊓ stabilizerOf ρ y ⊓ stabilizerOf ρ (x + y)) (inf_le_left.trans inf_le_left), hE y (stabilizerOf ρ x ⊓ stabilizerOf ρ y ⊓ stabilizerOf ρ (x + y)) (inf_le_left.trans inf …`. Introduce `c x haveI := hfin x haveI := hfin (c • x) show E (c • x) = c • E x`.

Rewrite using `[hE (c • x) (stabilizerOf ρ x ⊓ stabilizerOf ρ (c • x)) inf_le_right, hE x (stabilizerOf ρ x ⊓ stabilizerOf ρ (c • x)) inf_le_left, mean_smul]`. Introduce `h v haveI := hfin v`. Conclude with `mean_mem ρ (hfx v) h`. Introduce `h v haveI := hfin v haveI := hfin (ρ h v)`. Establish `hle : (stabilizerOf ρ v).normalCore ≤ stabilizerOf ρ (ρ h v)`.

Introduce `t ht`. Rewrite using `[mem_stabilizerOf]`. Establish `h1 : h⁻¹ * t * h ∈ (stabilizerOf ρ v).normalCore`. Use `(Subgroup.normalCore_normal (stabilizerOf ρ v)).conj_mem t ht h⁻¹` as an intermediate fact. Simplify using `using this`.

Establish `h2` using `hfx v _ (Subgroup.normalCore_le _ h1)`. Combine the equalities or inequalities in the displayed calculation. Use `show E (ρ h v) = E v`. Rewrite using `[hE (ρ h v) _ hle, hE v _ (Subgroup.normalCore_le _), mean_act ρ (fun t ht => hfx v t (Subgroup.normalCore_le _ ht)) h]`. Introduce `W _ _ p v hp haveI := hfin v`.

Conclude with `mean_lin ρ _ p hp`.
-/
private theorem exists_avg (hfin : ∀ v, (stabilizerOf ρ v).FiniteIndex) : ∃ e : V →ₗ[ℂ] V,
    (∀ h v, ρ h (e v) = e v) ∧ (∀ h v, e (ρ h v) = e v) ∧
      ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (p : V →ₗ[ℂ] W) (v : V),
        (∀ h, p (ρ h v) = p v) → p (e v) = p v := by
  let E : V → V := fun v => @mean H V _ _ _ ρ (stabilizerOf ρ v) (hfin v) v
  have hE : ∀ (v : V) (T : Subgroup H) [T.FiniteIndex], T ≤ stabilizerOf ρ v → E v = mean ρ T v := by
    intro v T _ hle
    haveI := hfin v
    exact (mean_eq ρ hle (fun t ht => mem_stabilizerOf.1 ht)).symm
  have hfx : ∀ v, ∀ t ∈ stabilizerOf ρ v, ρ t v = v := fun v t ht => mem_stabilizerOf.1 ht
  refine ⟨{ toFun := E, map_add' := ?_, map_smul' := ?_ }, ?_, ?_, ?_⟩
  · intro x y
    haveI := hfin x
    haveI := hfin y
    haveI := hfin (x + y)
    show E (x + y) = E x + E y
    rw [hE (x + y) (stabilizerOf ρ x ⊓ stabilizerOf ρ y ⊓ stabilizerOf ρ (x + y)) inf_le_right,
      hE x (stabilizerOf ρ x ⊓ stabilizerOf ρ y ⊓ stabilizerOf ρ (x + y)) (inf_le_left.trans inf_le_left),
      hE y (stabilizerOf ρ x ⊓ stabilizerOf ρ y ⊓ stabilizerOf ρ (x + y)) (inf_le_left.trans inf_le_right),
      mean_add]
  · intro c x
    haveI := hfin x
    haveI := hfin (c • x)
    show E (c • x) = c • E x
    rw [hE (c • x) (stabilizerOf ρ x ⊓ stabilizerOf ρ (c • x)) inf_le_right,
      hE x (stabilizerOf ρ x ⊓ stabilizerOf ρ (c • x)) inf_le_left, mean_smul]
  · intro h v
    haveI := hfin v
    exact mean_mem ρ (hfx v) h
  · intro h v
    haveI := hfin v
    haveI := hfin (ρ h v)
    have hle : (stabilizerOf ρ v).normalCore ≤ stabilizerOf ρ (ρ h v) := by
      intro t ht
      rw [mem_stabilizerOf]
      have h1 : h⁻¹ * t * h ∈ (stabilizerOf ρ v).normalCore := by
        have := (Subgroup.normalCore_normal (stabilizerOf ρ v)).conj_mem t ht h⁻¹
        simpa using this
      have h2 := hfx v _ (Subgroup.normalCore_le _ h1)
      calc ρ t (ρ h v) = ρ (t * h) v := by rw [map_mul, Module.End.mul_apply]
        _ = ρ (h * (h⁻¹ * t * h)) v := by rw [show h * (h⁻¹ * t * h) = t * h by group]
        _ = ρ h (ρ (h⁻¹ * t * h) v) := by rw [map_mul, Module.End.mul_apply]
        _ = ρ h v := by rw [h2]
    show E (ρ h v) = E v
    rw [hE (ρ h v) _ hle, hE v _ (Subgroup.normalCore_le _),
      mean_act ρ (fun t ht => hfx v t (Subgroup.normalCore_le _ ht)) h]
  · intro W _ _ p v hp
    haveI := hfin v
    exact mean_lin ρ _ p hp

end Mean

/- English proof (translation)
Introduce `G V _ _ _ _ _ π hsm K hK`. Unfold `IsSmooth at hsm`. Unfold `CO at hK`. Use `haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK.1`. Set `ρ : Representation ℂ K V` to `π.comp K.subtype`.

Establish `hfin : ∀ v, (GroundTheory.Automorphic.stabilizerOf ρ v).FiniteIndex`. Introduce `v`. Use `haveI := Subgroup.quotient_finite_of_isOpen (GroundTheory.Automorphic.stabilizerOf ρ v) ((hsm v).preimage continuous_subtype_val)`. Conclude with `Subgroup.finiteIndex_of_finite_quotient`. Take `⟨e, he1, he2, he3⟩` from `exists_avg ρ hfin`.

Establish `hfix : ∀ w, (∀ g ∈ K, π g w = w) → e w = w`. Introduce `w hw`. Use `he3 V LinearMap.id w (fun h => hw h h.2)` as an intermediate fact. Simplify using `using this`. Use `⟨e, ⟨?_, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Introduce `v`. Rewrite using `[GlobalTheory.Parabolic.mem_fixed]`. Introduce `g hg`. Conclude with `he1 ⟨g, hg⟩ v`. Introduce `v hv`.

Rewrite `hv` using `[GlobalTheory.Parabolic.mem_fixed]`. Conclude with `hfix v hv`. Introduce `g hg v`. Conclude with `he2 ⟨g, hg⟩ v`. Introduce `W _ _ p v hp`.

Conclude with `he3 W p v (fun h => hp h h.2)`. Introduce `s A hA hs hsurj v`. Establish `h1 : e (A (e v)) = A (e v)`. Apply `hfix` to reduce the goal to its premises. Introduce `g hg`.

Take `⟨h, hh, rfl⟩` from `hsurj g hg`. Rewrite using `[← hA]`. Use `congr 1`. Conclude with `he1 ⟨h, hh⟩ v`. Establish `h2 : e (A (e v)) = e (A v)`.

Use `he3 V (e ∘ₗ A) v (fun h => ?_)` and prove the remaining obligations. Use `show e (A (π h v)) = e (A v)`. Rewrite using `[hA]`. Conclude with `he2 ⟨s h, hs h h.2⟩ (A v)`. Rewrite using `[← h1, h2]`.
-/
theorem UpperTheory.Gal.Join.avgEx :
    UpperTheory.Gal.Join.AvgEx := by
  intro G V _ _ _ _ _ π hsm K hK
  unfold IsSmooth at hsm
  unfold CO at hK
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK.1
  let ρ : Representation ℂ K V := π.comp K.subtype
  have hfin : ∀ v, (GroundTheory.Automorphic.stabilizerOf ρ v).FiniteIndex := by
    intro v
    haveI := Subgroup.quotient_finite_of_isOpen (GroundTheory.Automorphic.stabilizerOf ρ v) ((hsm v).preimage continuous_subtype_val)
    exact Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨e, he1, he2, he3⟩ := exists_avg ρ hfin
  have hfix : ∀ w, (∀ g ∈ K, π g w = w) → e w = w := by
    intro w hw
    have := he3 V LinearMap.id w (fun h => hw h h.2)
    simpa using this
  refine ⟨e, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro v
    rw [GlobalTheory.Parabolic.mem_fixed]
    intro g hg
    exact he1 ⟨g, hg⟩ v
  · intro v hv
    rw [GlobalTheory.Parabolic.mem_fixed] at hv
    exact hfix v hv
  · intro g hg v
    exact he2 ⟨g, hg⟩ v
  · intro W _ _ p v hp
    exact he3 W p v (fun h => hp h h.2)
  · intro s A hA hs hsurj v
    have h1 : e (A (e v)) = A (e v) := by
      apply hfix
      intro g hg
      obtain ⟨h, hh, rfl⟩ := hsurj g hg
      rw [← hA]
      congr 1
      exact he1 ⟨h, hh⟩ v
    have h2 : e (A (e v)) = e (A v) := by
      refine he3 V (e ∘ₗ A) v (fun h => ?_)
      show e (A (π h v)) = e (A v)
      rw [hA]
      exact he2 ⟨s h, hs h h.2⟩ (A v)
    rw [← h1, h2]
