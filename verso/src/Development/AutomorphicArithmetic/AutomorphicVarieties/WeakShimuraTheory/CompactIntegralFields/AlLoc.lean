import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CoefSup
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsValuationExtensionIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIntegralClosurePreimageOfIsIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ResidueIsIntegralOfAlgebraicOverDvr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Establish `hl : (l : c.O) ≠ 0` using `Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero`. Establish `hk : RingHom.ker g ≠ ⊥` using `fun h => hl (by`. Establish `: (l : c.O) ∈ RingHom.ker g` using `by rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]`. Rewrite using `[h, Ideal.mem_bot] at this)` and apply the resulting hypothesis. Establish `hm : RingHom.ker g = maximalIdeal c.O` using `eq_maximalIdeal ((RingHom.ker_isPrime g).isMaximal hk)`.

Use `⟨fun x hx => by_contra fun h => hx.ne_zero ?_⟩` and prove the remaining obligations. Establish `: x ∈ RingHom.ker g` using `hm ▸ (mem_maximalIdeal x).2 h`. Conclude with `this`.
-/
private theorem al_loc {l : ℕ} [Fact l.Prime] (c : Coef l) {B : Type} [CommRing B] [IsDomain B] [CharP B l] (g : c.O →+* B) :
    IsLocalHom g := by
  have hl : (l : c.O) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hk : RingHom.ker g ≠ ⊥ := fun h => hl (by
    have : (l : c.O) ∈ RingHom.ker g := by rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
    rwa [h, Ideal.mem_bot] at this)
  have hm : RingHom.ker g = maximalIdeal c.O := eq_maximalIdeal ((RingHom.ker_isPrime g).isMaximal hk)
  refine ⟨fun x hx => by_contra fun h => hx.ne_zero ?_⟩
  have : x ∈ RingHom.ker g := hm ▸ (mem_maximalIdeal x).2 h
  exact this

/- English proof (translation)
Introduce `x hx` and use `(Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val`.
-/
private theorem al_le {l : ℕ} [Fact l.Prime] (c : Coef l) : c.O ≤ integralClosure ℤ_[l] (PadicAlgCl l) := fun x hx =>
  (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val

/- English proof (translation)
Introduce `l _ c A _ _ _ _ _ _ a`. Use `haveI := c.dvr`. Use `haveI := c.fin`. Set `K` to `AlgebraicClosure (FractionRing A)`. Set `g0 : A →+* K` to `(algebraMap (FractionRing A) K).comp (algebraMap A (FractionRing A))`.

Establish `hg0 : Function.Injective g0` using `(algebraMap (FractionRing A) K).injective.comp (IsFractionRing.injective A (FractionRing A))`. Take `⟨V, hV, hloc⟩` from `IsLocalRing.exists_factor_valuationRing g0`. Set `f : A →+* V` to `g0.codRestrict V hV`. Establish `hfinj : Function.Injective f` using `fun x y h => hg0 (congrArg Subtype.val h)`. Establish `hfloc : IsLocalHom f` using `hloc`.

Use `haveI hK : CharP K l := charP_of_injective_ringHom hg0 l`. Use `haveI : CharP V l := charP_of_injective_ringHom hfinj l`. Establish `heq : V.subtype.comp f = g0` using `RingHom.ext fun _ => rfl`. Establish `halg : ∀ z : K, ∃ p : A[X], p ≠ 0 ∧ eval₂ (V.subtype.comp f) z p = 0`. Introduce `z`.

Take `⟨q, hq0, hq⟩` from `Algebra.IsAlgebraic.isAlgebraic (R := FractionRing A) z`. Use `⟨IsLocalization.integerNormalization (nonZeroDivisors A) q, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ne, IsFractionRing.integerNormalization_eq_zero_iff]` and apply the resulting hypothesis. Rewrite `hq` using `[Polynomial.aeval_def]`. Rewrite using `[heq]`.

Conclude with `IsLocalization.integerNormalization_eval₂_eq_zero (nonZeroDivisors A) (algebraMap (FractionRing A) K) q hq`. Set `S` to `integralClosure c.O (PadicAlgCl l)`. Establish `hinj : Function.Injective (algebraMap c.O S)`. Introduce `x y h`. Apply `Subtype.ext` to reduce the goal to its premises.

Establish `h2` using `congrArg Subtype.val h`. Conclude with `h2`. Take `⟨Φ, hΦ⟩` from `UpperTheory.exists_valuation_extension_integral c.O S K V hinj (f.comp a)`. Establish `hS : ∀ c' : Coef l, ∀ x : c'.O, (x : PadicAlgCl l) ∈ S` using `fun c' x => IsIntegral.tower_top (A := c.O) (al_le c' x.2)`. Set `ι : ∀ c' : Coef l, c'.O →+* S` to `fun c' => c'.O.val.toRingHom.codRestrict S (hS c')`.

Use `⟨Amb.mk K V (fun c' => Φ.comp (ι c')) ?_ ?_ ?_, f, hK, ⟨hfinj, hfloc, inferInstance, inferInstance, halg⟩, ?_⟩` and prove the remaining obligations. Introduce `c1 c2 h x`. Conclude with `congrArg Φ (Subtype.ext rfl)`. Introduce `c'`. Conclude with `al_loc c' _`.

Introduce `x`. Take `⟨p, hp0, hp⟩` from `halg x`. Establish `hint` using `UpperTheory.residue_isIntegral_of_algebraic_over_dvr A K V f hfinj hfloc x ⟨p, hp0, hp⟩`. Take `⟨y, hy⟩` from `UpperTheory.exists_integralClosure_preimage_of_isIntegral c.O (PadicAlgCl l) (ResidueField V) ((IsLocalRing.residue V).comp Φ) (IsLocalRing.residue V x) hint`. Establish `hyl : IsIntegral ℤ_[l] (y : PadicAlgCl l)` using `isIntegral_trans (A := c.O) _ y.2`.

Take `⟨c', -, hc'⟩` from `(coefSup l).2.2.1 c y.1 hyl`. Use `⟨c', ⟨y.1, hc'⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← hy]`. Both sides reduce to the same expression. Conclude with `hΦ.symm.trans (congrArg Φ.comp (RingHom.ext fun x => Subtype.ext rfl))`.
-/
theorem UpperTheory.V.Ws.ambL :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
      [Finite (ResidueField A)] [CharP A l] (a : c.O →+* A), ∃ (𝔞 : Amb l) (f : A →+* 𝔞.V), CharP 𝔞.K l ∧ 𝔞.IsDvr f ∧ f.comp a = 𝔞.a c := by
  intro l _ c A _ _ _ _ _ _ a
  haveI := c.dvr
  haveI := c.fin
  let K := AlgebraicClosure (FractionRing A)
  let g0 : A →+* K := (algebraMap (FractionRing A) K).comp (algebraMap A (FractionRing A))
  have hg0 : Function.Injective g0 :=
    (algebraMap (FractionRing A) K).injective.comp (IsFractionRing.injective A (FractionRing A))
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing g0
  let f : A →+* V := g0.codRestrict V hV
  have hfinj : Function.Injective f := fun x y h => hg0 (congrArg Subtype.val h)
  have hfloc : IsLocalHom f := hloc
  haveI hK : CharP K l := charP_of_injective_ringHom hg0 l
  haveI : CharP V l := charP_of_injective_ringHom hfinj l
  have heq : V.subtype.comp f = g0 := RingHom.ext fun _ => rfl
  have halg : ∀ z : K, ∃ p : A[X], p ≠ 0 ∧ eval₂ (V.subtype.comp f) z p = 0 := by
    intro z
    obtain ⟨q, hq0, hq⟩ := Algebra.IsAlgebraic.isAlgebraic (R := FractionRing A) z
    refine ⟨IsLocalization.integerNormalization (nonZeroDivisors A) q, ?_, ?_⟩
    · rwa [Ne, IsFractionRing.integerNormalization_eq_zero_iff]
    · rw [Polynomial.aeval_def] at hq
      rw [heq]
      exact IsLocalization.integerNormalization_eval₂_eq_zero (nonZeroDivisors A)
        (algebraMap (FractionRing A) K) q hq
  let S := integralClosure c.O (PadicAlgCl l)
  have hinj : Function.Injective (algebraMap c.O S) := by
    intro x y h
    apply Subtype.ext
    have h2 := congrArg Subtype.val h
    exact h2
  obtain ⟨Φ, hΦ⟩ := UpperTheory.exists_valuation_extension_integral c.O S K V hinj (f.comp a)
  have hS : ∀ c' : Coef l, ∀ x : c'.O, (x : PadicAlgCl l) ∈ S := fun c' x =>
    IsIntegral.tower_top (A := c.O) (al_le c' x.2)
  let ι : ∀ c' : Coef l, c'.O →+* S := fun c' => c'.O.val.toRingHom.codRestrict S (hS c')
  refine ⟨Amb.mk K V (fun c' => Φ.comp (ι c')) ?_ ?_ ?_, f, hK, ⟨hfinj, hfloc, inferInstance, inferInstance, halg⟩, ?_⟩
  · intro c1 c2 h x
    exact congrArg Φ (Subtype.ext rfl)
  · intro c'
    exact al_loc c' _
  · intro x
    obtain ⟨p, hp0, hp⟩ := halg x
    have hint := UpperTheory.residue_isIntegral_of_algebraic_over_dvr A K V f hfinj hfloc x ⟨p, hp0, hp⟩
    obtain ⟨y, hy⟩ := UpperTheory.exists_integralClosure_preimage_of_isIntegral c.O (PadicAlgCl l) (ResidueField V)
      ((IsLocalRing.residue V).comp Φ) (IsLocalRing.residue V x) hint
    have hyl : IsIntegral ℤ_[l] (y : PadicAlgCl l) := isIntegral_trans (A := c.O) _ y.2
    obtain ⟨c', -, hc'⟩ := (coefSup l).2.2.1 c y.1 hyl
    refine ⟨c', ⟨y.1, hc'⟩, ?_⟩
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← hy]
    rfl
  · exact hΦ.symm.trans (congrArg Φ.comp (RingHom.ext fun x => Subtype.ext rfl))
