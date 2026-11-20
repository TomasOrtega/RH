import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalRingCardinality.SpanPowerMembership.Places

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain HeightOneSpectrum WithZero ValuativeRel Formalism.MainNotions.S.Loc
open scoped TensorProduct

def intSub (K A : Type) [Field K] [ValuativeRel K] [CommRing A] [Algebra K A] : Subring A :=
  (integralClosure 𝒪[K] A).toSubring

def psiTr (l : ℕ) [Fact l.Prime] (K A : Type) [Field K] [CommRing A] [Algebra K A] [Algebra ℚ_[l] K] :
    AddChar A ℂ :=
  letI := ((algebraMap K A).comp (algebraMap ℚ_[l] K)).toAlgebra
  (LocF.psi0 l).compAddMonoidHom (Algebra.trace ℚ_[l] A).toAddMonoidHom

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (sig : E →ₐ[F] E) (hsig : ∀ x, sig (sig x) = x) (h2 : Module.finrank F E = 2)
  (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Use `show (ringChar (𝓞 F ⧸ v.asIdeal)).Prime`. Use `haveI : v.asIdeal.IsPrime := v.isPrime`. Use `haveI : Finite (𝓞 F ⧸ v.asIdeal) := by first`. Consider the case `exact Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot`. Consider the case `exact Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot`.

Consider the case `infer_instance`. Conclude with `(CharP.char_is_prime_or_zero (𝓞 F ⧸ v.asIdeal) (ringChar (𝓞 F ⧸ v.asIdeal))).resolve_right (CharP.char_ne_zero_of_finite (𝓞 F ⧸ v.asIdeal) _)`.
-/
theorem resChar_prime : (resChar v).Prime := by
  show (ringChar (𝓞 F ⧸ v.asIdeal)).Prime
  haveI : v.asIdeal.IsPrime := v.isPrime
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := by
    first
    | exact Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
    | exact Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
    | infer_instance
  exact (CharP.char_is_prime_or_zero (𝓞 F ⧸ v.asIdeal) (ringChar (𝓞 F ⧸ v.asIdeal))).resolve_right
    (CharP.char_ne_zero_of_finite (𝓞 F ⧸ v.asIdeal) _)

/- English proof (translation)
Use `show ((ringChar (𝓞 F ⧸ v.asIdeal) : ℕ) : 𝓞 F) ∈ v.asIdeal`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`. Use `first`. Consider the case `exact ringChar.Nat.cast_ringChar`. Consider the case `exact CharP.cast_eq_zero _ _`.
-/
theorem resChar_mem : ((resChar v : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  show ((ringChar (𝓞 F ⧸ v.asIdeal) : ℕ) : 𝓞 F) ∈ v.asIdeal
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  first
  | exact ringChar.Nat.cast_ringChar
  | exact CharP.cast_eq_zero _ _

def cjT : (v.adicCompletion F ⊗[F] E) ≃ₐ[v.adicCompletion F] (v.adicCompletion F ⊗[F] E) :=
  AlgEquiv.ofAlgHom (Algebra.TensorProduct.map (AlgHom.id _ _) sig)
    (Algebra.TensorProduct.map (AlgHom.id _ _) sig)
    (by ext x; simp [hsig]) (by ext x; simp [hsig])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cjT_tmul (a : v.adicCompletion F) (x : E) : cjT sig hsig v (a ⊗ₜ x) = a ⊗ₜ sig x := rfl

def locAtC : LocAt F E sig v :=
  haveI : Fact (resChar v).Prime := ⟨resChar_prime v⟩
  letI := LocF.vrel v
  letI := (LocF.emb v (resChar v) (resChar_mem v)).toAlgebra
  letI : TopologicalSpace (v.adicCompletion F ⊗[F] E) := moduleTopology (v.adicCompletion F) _
  letI : MeasurableSpace (v.adicCompletion F ⊗[F] E) := borel _
  { Fp := v.adicCompletion F
    Ep := v.adicCompletion F ⊗[F] E
    lf := LocF.isLocalField v
    char0 := inferInstance
    ιF := algebraMap F _
    ιE := (Algebra.TensorProduct.includeRight : E →ₐ[F] v.adicCompletion F ⊗[F] E).toRingHom
    compat := fun a => by
      show (1 : v.adicCompletion F) ⊗ₜ[F] algebraMap F E a = (algebraMap F (v.adicCompletion F) a) ⊗ₜ[F] (1 : E)
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one a, TensorProduct.smul_tmul]
    dense := v.denseRange_algebraMap F
    val := fun x y => by
      show Valued.v (algebraMap F (v.adicCompletion F) x) ≤ Valued.v (algebraMap F (v.adicCompletion F) y) ↔ _
      rw [adicCompl_val_algebraMap, adicCompl_val_algebraMap]
    free := inferInstance
    rank := by rw [Module.finrank_baseChange, h2]
    span := by
      rw [eq_top_iff]
      rintro x -
      induction x using TensorProduct.induction_on with
      | zero => exact zero_mem _
      | add a b ha hb => exact add_mem ha hb
      | tmul a x =>
        have : a ⊗ₜ[F] x = a • ((1 : v.adicCompletion F) ⊗ₜ[F] x) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
    top := ⟨rfl⟩
    borel := ⟨rfl⟩
    cj := cjT sig hsig v
    cj_ιE := fun _ => rfl
    O := intSub _ _
    O_def := fun _ => Iff.rfl
    ellPrime := ⟨resChar_prime v⟩
    qlCont := LocF.emb_cont v _ _
    qlFin := LocF.emb_finite v _ _
    psiE := psiTr (resChar v) (v.adicCompletion F) _
    psiE_def := fun _ => LocF.padicCharacter_spec _ _
    split := none }

/- English proof (translation)
Set `K` to `v.adicCompletion F`. Set `_` to `LocF.vrel v`. Establish `hc` using `LocF.vcompat v`. Set `e : K ⊗[F] E →ₐ[K] K × K` to `Algebra.TensorProduct.lift (Algebra.ofId K (K × K)) (φ.prod (φ.comp sig)) (fun _ _ => Commute.all _ _)`. Establish `he : ∀ (a : K) (x : E), e (a ⊗ₜ x) = (a * φ x, a * φ (sig x))` using `fun a x => Algebra.TensorProduct.lift_tmul _ _ (fun _ _ => Commute.all _ _) a x`.

Establish `hr : φ b ≠ 0` using `(map_ne_zero φ).mpr hb0`. Establish `hsurj : Function.Surjective e`. Introduce and unpack `⟨x, y⟩`. Use `⟨((x + y) / 2) ⊗ₜ 1 + ((x - y) / (2 * φ b)) ⊗ₜ b, ?_⟩` and prove the remaining obligations. Establish `h2K : (2 : K) ≠ 0` using `two_ne_zero`.

Rewrite using `[map_add, he, he, hb, map_one sig, map_one φ, map_neg]`. Establish `aux : ∀ r : K, r ≠ 0 → ((x + y) / 2 * 1 + (x - y) / (2 * r) * r = x ∧ (x + y) / 2 * 1 + (x - y) / (2 * r) * -r = y)` using `fun r hr => by`. Establish `h1 : (x - y) / (2 * r) * r = (x - y) / 2`. Rewrite using `[div_mul_eq_mul_div, mul_div_mul_right _ _ hr]`. Establish `h3 : (2 : K)⁻¹ * 2 = 1` using `inv_mul_cancel₀ h2K`.

Rewrite using `[mul_neg, h1, div_eq_mul_inv, div_eq_mul_inv]`. Prove the components needed by the constructor for the conclusion. Take the linear combination `x * h3`. Take the linear combination `y * h3`. Conclude with `Prod.ext (aux _ hr).1 (aux _ hr).2`.

Establish `hdim : Module.finrank K (K ⊗[F] E) = Module.finrank K (K × K)`. Rewrite using `[Module.finrank_baseChange, h2]`. Simplify using the standard rewrite rules. Establish `hinj : Function.Injective e` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := e.toLinearMap)).mpr hsurj`. Establish `hval : Valued.v ((resChar v : ℕ) : K) = exp (-1 : ℤ)`.

Rewrite using `[← map_natCast (algebraMap F K), adicCompl_val_algebraMap, hv]`. Establish `hmem : ∀ x : K, x ∈ 𝒪[K] ↔ x ∈ v.adicCompletionIntegers F` using `fun x => by`. Rewrite using `[Valuation.mem_integer_iff, mem_adicCompletionIntegers]`. Conclude with `(ValuativeRel.isEquiv (valuation K) (Valued.v : Valuation K ℤᵐ⁰)).le_one_iff_le_one`. Set `ι : 𝒪[K] ≃+* v.adicCompletionIntegers F` to `{ toFun := fun x => ⟨x.1, (hmem _).1 x.2⟩ invFun := fun x => ⟨x.1, (hmem _).2 x.2⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl map_mul' := fun _ _ => rfl map_add' := fun _ _ => rfl }`.

Establish `hirr : Irreducible ((resChar v : ℕ) : v.adicCompletionIntegers F)` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr (adicInt_max_eq_span v _ (by simpa using hval))`. Use `⟨⟨AlgEquiv.ofBijective e ⟨hinj, hsurj⟩, fun x => ?_, ((resChar v : ℕ) : 𝒪[K]), ?_, ?_⟩⟩` and prove the remaining obligations. Use `show e (cjT sig hsig v x) = (e x).swap`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `add a b ha hb => rw [map_add, map_add, map_add, ha, hb, Prod.swap_add]`. Consider the case `tmul a x => rw [cjT_tmul, he, he, hsig]`. Both sides reduce to the same expression. Use `show Irreducible ((resChar v : ℕ) : 𝒪[K])`. Rewrite using `[← MulEquiv.irreducible_iff ι.toMulEquiv]`.

Establish `: ι.toMulEquiv ((resChar v : ℕ) : 𝒪[K]) = ((resChar v : ℕ) : v.adicCompletionIntegers F)` using `map_natCast ι _`. Rewrite using `[this]`. Conclude with `hirr`. Conclude with `SubringClass.coe_natCast _ _`.
-/
theorem splitAt_nonempty (φ : E →ₐ[F] v.adicCompletion F) (b : E) (hb0 : b ≠ 0) (hb : sig b = -b)
    (hv : v.valuation F ((resChar v : ℕ) : F) = exp (-1 : ℤ)) :
    Nonempty (SplitAt (locAtC sig hsig h2 v).Fp (locAtC sig hsig h2 v).Ep (locAtC sig hsig h2 v).cj
      (resChar v)) := by
  let K := v.adicCompletion F
  let _ := LocF.vrel v
  have hc := LocF.vcompat v
  let e : K ⊗[F] E →ₐ[K] K × K :=
    Algebra.TensorProduct.lift (Algebra.ofId K (K × K)) (φ.prod (φ.comp sig)) (fun _ _ => Commute.all _ _)
  have he : ∀ (a : K) (x : E), e (a ⊗ₜ x) = (a * φ x, a * φ (sig x)) := fun a x =>
    Algebra.TensorProduct.lift_tmul _ _ (fun _ _ => Commute.all _ _) a x
  have hr : φ b ≠ 0 := (map_ne_zero φ).mpr hb0
  have hsurj : Function.Surjective e := by
    rintro ⟨x, y⟩
    refine ⟨((x + y) / 2) ⊗ₜ 1 + ((x - y) / (2 * φ b)) ⊗ₜ b, ?_⟩
    have h2K : (2 : K) ≠ 0 := two_ne_zero
    rw [map_add, he, he, hb, map_one sig, map_one φ, map_neg]
    have aux : ∀ r : K, r ≠ 0 → ((x + y) / 2 * 1 + (x - y) / (2 * r) * r = x ∧
        (x + y) / 2 * 1 + (x - y) / (2 * r) * -r = y) := fun r hr => by
      have h1 : (x - y) / (2 * r) * r = (x - y) / 2 := by
        rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hr]
      have h3 : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2K
      rw [mul_neg, h1, div_eq_mul_inv, div_eq_mul_inv]
      constructor
      · linear_combination x * h3
      · linear_combination y * h3
    exact Prod.ext (aux _ hr).1 (aux _ hr).2
  have hdim : Module.finrank K (K ⊗[F] E) = Module.finrank K (K × K) := by
    rw [Module.finrank_baseChange, h2]; simp
  have hinj : Function.Injective e :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := e.toLinearMap)).mpr hsurj
  have hval : Valued.v ((resChar v : ℕ) : K) = exp (-1 : ℤ) := by
    rw [← map_natCast (algebraMap F K), adicCompl_val_algebraMap, hv]
  have hmem : ∀ x : K, x ∈ 𝒪[K] ↔ x ∈ v.adicCompletionIntegers F := fun x => by
    rw [Valuation.mem_integer_iff, mem_adicCompletionIntegers]
    exact (ValuativeRel.isEquiv (valuation K) (Valued.v : Valuation K ℤᵐ⁰)).le_one_iff_le_one
  let ι : 𝒪[K] ≃+* v.adicCompletionIntegers F :=
    { toFun := fun x => ⟨x.1, (hmem _).1 x.2⟩
      invFun := fun x => ⟨x.1, (hmem _).2 x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  have hirr : Irreducible ((resChar v : ℕ) : v.adicCompletionIntegers F) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
      (adicInt_max_eq_span v _ (by simpa using hval))
  refine ⟨⟨AlgEquiv.ofBijective e ⟨hinj, hsurj⟩, fun x => ?_, ((resChar v : ℕ) : 𝒪[K]), ?_, ?_⟩⟩
  · show e (cjT sig hsig v x) = (e x).swap
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, map_add, ha, hb, Prod.swap_add]
    | tmul a x => rw [cjT_tmul, he, he, hsig]; rfl
  · show Irreducible ((resChar v : ℕ) : 𝒪[K])
    rw [← MulEquiv.irreducible_iff ι.toMulEquiv]
    have : ι.toMulEquiv ((resChar v : ℕ) : 𝒪[K]) = ((resChar v : ℕ) : v.adicCompletionIntegers F) :=
      map_natCast ι _
    rw [this]; exact hirr
  · exact SubringClass.coe_natCast _ _

include hsig in
/- English proof (translation)
Establish `hbF : b ∉ Set.range (algebraMap F E)`. Introduce and unpack `⟨a, ha⟩`. Apply `hb0` to reduce the goal to its premises. Establish `h1 : sig b = b` using `by rw [← ha]; exact sig.commutes a`. Establish `h2 : (2 : E) * b = 0` using `by linear_combination hb - h1`.

Conclude with `(mul_eq_zero.mp h2).resolve_left two_ne_zero`. Establish `hmonic : (Polynomial.X ^ 2 + Polynomial.C (d : F) : Polynomial F).Monic` using `by first`. Consider the case `exact Polynomial.monic_X_pow_add_C _ two_ne_zero`. Consider the case `exact Polynomial.monic_X_pow_add_C _ (by norm_num)`. Consider the case `monicity!`.

Establish `haeval : Polynomial.aeval b (Polynomial.X ^ 2 + Polynomial.C (d : F) : Polynomial F) = 0`. Simplify using `[hb2]`. Establish `hirr : Irreducible (Polynomial.X ^ 2 + Polynomial.C (d : F) : Polynomial F)`. Apply `Polynomial.irreducible_of_degree_le_three_of_not_isRoot` to reduce the goal to its premises. Rewrite using `[Polynomial.natDegree_X_pow_add_C]`.

Evaluate the decidable proposition. Introduce `a ha`. Apply `hbF` to reduce the goal to its premises. Establish `ha' : a ^ 2 + (d : F) = 0` using `by simpa using ha`. Establish `hx : (algebraMap F E a) ^ 2 + (d : E) = 0`.

Rewrite using `[← map_pow, ← map_natCast (algebraMap F E) d, ← map_add, ha', map_zero]`. Establish `hsq : (b - algebraMap F E a) * (b + algebraMap F E a) = 0`. Take the linear combination `hb2 - hx`. Break down `mul_eq_zero.mp hsq with h | h` into its components or cases. Conclude with `⟨a, (sub_eq_zero.mp h).symm⟩`.

Conclude with `⟨-a, by rw [map_neg]; linear_combination -h⟩`. Establish `hmin : (Polynomial.X ^ 2 + Polynomial.C (d : F) : Polynomial F) = minpoly F b` using `minpoly.eq_of_irreducible_of_monic hirr haeval hmonic`. Establish `hint : IsIntegral F b` using `⟨_, hmonic, haeval⟩`. Establish `htop : IntermediateField.adjoin F {b} = ⊤`. Rewrite using `[eq_top_iff]`.

Introduce `x _`. Establish `hA : sig ((x + sig x) / 2) = (x + sig x) / 2`. Rewrite using `[map_div₀, map_add, hsig, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Establish `hB : sig ((x - sig x) / (2 * b)) = (x - sig x) / (2 * b)`.

Rewrite using `[map_div₀, map_sub, map_mul, hsig, map_ofNat, hb]`. Use `first`. Consider the case `(field_simp; ring)`. Consider the case `field_simp`. Consider the case `ring`.

Take `⟨a1, ha1⟩` from `hfix _ hA`. Take `⟨a2, ha2⟩` from `hfix _ hB`. Establish `hx : x = algebraMap F E a1 + algebraMap F E a2 * b`. Rewrite using `[ha1, ha2]`. Use `first`.

Consider the case `(field_simp; ring)`. Consider the case `field_simp`. Consider the case `ring`. Rewrite using `[hx]`. Conclude with `add_mem (IntermediateField.algebraMap_mem _ a1) (mul_mem (IntermediateField.algebraMap_mem _ a2) (IntermediateField.mem_adjoin_simple_self F b))`.

Establish `hr' : Polynomial.aeval r (minpoly F (IntermediateField.adjoin.powerBasis hint).gen) = 0`. Rewrite using `[IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen, ← hmin]`. Simplify using `[hr]`. Conclude with `⟨((IntermediateField.adjoin.powerBasis hint).lift r hr').comp ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv).symm.toAlgHom⟩`.
-/
theorem exists_emb {K : Type} [Field K] [Algebra F K]
    (hfix : ∀ x, sig x = x → ∃ a, algebraMap F E a = x) (b : E) (hb0 : b ≠ 0) (hb : sig b = -b)
    (d : ℕ) (hb2 : b ^ 2 = -(d : E)) (r : K) (hr : r ^ 2 = -(d : K)) : Nonempty (E →ₐ[F] K) := by
  classical
  have hbF : b ∉ Set.range (algebraMap F E) := by
    rintro ⟨a, ha⟩
    apply hb0
    have h1 : sig b = b := by rw [← ha]; exact sig.commutes a
    have h2 : (2 : E) * b = 0 := by linear_combination hb - h1
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  have hmonic : (Polynomial.X ^ 2 + Polynomial.C (d : F) : Polynomial F).Monic := by
    first
    | exact Polynomial.monic_X_pow_add_C _ two_ne_zero
    | exact Polynomial.monic_X_pow_add_C _ (by norm_num)
    | monicity!
  have haeval : Polynomial.aeval b (Polynomial.X ^ 2 + Polynomial.C (d : F) : Polynomial F) = 0 := by
    simp [hb2]
  have hirr : Irreducible (Polynomial.X ^ 2 + Polynomial.C (d : F) : Polynomial F) := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [Polynomial.natDegree_X_pow_add_C]
      decide
    · intro a ha
      apply hbF
      have ha' : a ^ 2 + (d : F) = 0 := by simpa using ha
      have hx : (algebraMap F E a) ^ 2 + (d : E) = 0 := by
        rw [← map_pow, ← map_natCast (algebraMap F E) d, ← map_add, ha', map_zero]
      have hsq : (b - algebraMap F E a) * (b + algebraMap F E a) = 0 := by
        linear_combination hb2 - hx
      rcases mul_eq_zero.mp hsq with h | h
      · exact ⟨a, (sub_eq_zero.mp h).symm⟩
      · exact ⟨-a, by rw [map_neg]; linear_combination -h⟩
  have hmin : (Polynomial.X ^ 2 + Polynomial.C (d : F) : Polynomial F) = minpoly F b :=
    minpoly.eq_of_irreducible_of_monic hirr haeval hmonic
  have hint : IsIntegral F b := ⟨_, hmonic, haeval⟩
  have htop : IntermediateField.adjoin F {b} = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hA : sig ((x + sig x) / 2) = (x + sig x) / 2 := by
      rw [map_div₀, map_add, hsig, map_ofNat]
      ring
    have hB : sig ((x - sig x) / (2 * b)) = (x - sig x) / (2 * b) := by
      rw [map_div₀, map_sub, map_mul, hsig, map_ofNat, hb]
      first
      | (field_simp; ring)
      | field_simp
      | ring
    obtain ⟨a1, ha1⟩ := hfix _ hA
    obtain ⟨a2, ha2⟩ := hfix _ hB
    have hx : x = algebraMap F E a1 + algebraMap F E a2 * b := by
      rw [ha1, ha2]
      first
      | (field_simp; ring)
      | field_simp
      | ring
    rw [hx]
    exact add_mem (IntermediateField.algebraMap_mem _ a1)
      (mul_mem (IntermediateField.algebraMap_mem _ a2) (IntermediateField.mem_adjoin_simple_self F b))
  have hr' : Polynomial.aeval r (minpoly F (IntermediateField.adjoin.powerBasis hint).gen) = 0 := by
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen, ← hmin]
    simp [hr]
  exact ⟨((IntermediateField.adjoin.powerBasis hint).lift r hr').comp
    ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv).symm.toAlgHom⟩

/- English proof (translation)
Use `haveI : Fact g.Prime := ⟨hg⟩`. Establish `hne : (d : ZMod g) ≠ 0`. Introduce `h0`. Establish `h1 : (((-(d : ℤ)) : ℤ) : ZMod g) = 0` using `by push_cast; rw [h0, neg_zero]`. Establish `h2` using `(legendreSym.eq_zero_iff g (-(d : ℤ))).mpr h1`.

Use `first`. Consider the case `(rw [jacobiSym.legendreSym.to_jacobiSym, hj] at h2; exact one_ne_zero h2)`. Consider the case `(rw [← jacobiSym.legendreSym.to_jacobiSym] at hj; rw [hj] at h2; exact one_ne_zero h2)`. Consider the case `(simp only [jacobiSym.legendreSym.to_jacobiSym, hj] at h2; exact one_ne_zero h2)`. Establish `hsqr : IsSquare (((-(d : ℤ)) : ℤ) : ZMod g)` using `by first`.

Consider the case `exact ZMod.isSquare_of_jacobiSym_eq_one hj`. Consider the case `exact (legendreSym.eq_one_iff g (by push_cast; exact neg_ne_zero.mpr hne)).1 (by rw [jacobiSym.legendreSym.to_jacobiSym]; exact hj)`. Take `⟨c, hc⟩` from `hsqr`. Move the coercions through the operations in `at hc`. Take `⟨a0, ha0⟩` from `ZMod.intCast_surjective c`.

Establish `hdvd : (g : ℤ) ∣ a0 ^ 2 + d`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `push_cast`. Rewrite using `[ha0]`. Take the linear combination `-hc`.

Establish `h2ne : (2 : ZMod g) ≠ 0` using `by first`. Consider the case `exact Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hg2)`. Consider the case `(intro h`. Establish `h' : ((2 : ℕ) : ZMod g) = 0` using `by exact_mod_cast h`. Rewrite `h'` using `[ZMod.natCast_zmod_eq_zero_iff_dvd]`.

Conclude with `hg2 ((Nat.prime_dvd_prime_iff_eq hg Nat.prime_two).1 h'))`. Establish `hnd : ¬ (g : ℤ) ∣ 2 * a0`. Introduce `h`. Establish `h2 : (((2 * a0 : ℤ)) : ZMod g) = 0` using `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h`. Move the coercions through the operations in `at h2`.

Rewrite `h2` using `[ha0]`. Establish `hc0 : c = 0` using `(mul_eq_zero.mp h2).resolve_left h2ne`. Apply `hne` to reduce the goal to its premises. Rewrite `hc` using `[hc0, mul_zero]`. Conclude with `neg_eq_zero.mp hc`.

Use `set P : Polynomial ℤ_[g] := Polynomial.X ^ 2 + Polynomial.C (d : ℤ_[g]) with hP`. Establish `hev : P.eval (a0 : ℤ_[g]) = ((a0 ^ 2 + d : ℤ) : ℤ_[g])` using `by first`. Consider the case `(simp [hP]; done)`. Consider the case `(simp [hP]; norm_num; done)`. Consider the case `(simp [hP]; ring)`.

Establish `hder : P.derivative.eval (a0 : ℤ_[g]) = ((2 * a0 : ℤ) : ℤ_[g])` using `by first`. Consider the case `(simp [hP]; done)`. Consider the case `(simp [hP]; norm_num; done)`. Consider the case `(simp [hP]; ring)`. Establish `hn1 : ‖((a0 ^ 2 + d : ℤ) : ℤ_[g])‖ < 1` using `by first`.

Consider the case `exact (PadicInt.norm_int_lt_one_iff_dvd _).2 hdvd`. Consider the case `(rw [PadicInt.norm_lt_one_iff_dvd]; simpa using map_dvd (Int.castRingHom ℤ_[g]) hdvd)`. Establish `hn2 : ‖((2 * a0 : ℤ) : ℤ_[g])‖ = 1`. Establish `hle` using `PadicInt.norm_le_one ((2 * a0 : ℤ) : ℤ_[g])`. Establish `hnlt : ¬ ‖((2 * a0 : ℤ) : ℤ_[g])‖ < 1`.

Rewrite using `[PadicInt.norm_int_lt_one_iff_dvd]`. Conclude with `hnd`. Conclude with `le_antisymm hle (not_lt.mp hnlt)`. Take `⟨z, hz, -⟩` from `hensels_lemma (F := P) (a := (a0 : ℤ_[g])) (by simp only [Polynomial.coe_aeval_eq_eval]; rw [hev, hder, hn2]; simpa using hn1)`. Establish `hz' : z ^ 2 + (d : ℤ_[g]) = 0` using `by simpa [hP] using hz`.

Establish `hs : z ^ 2 = -(d : ℤ_[g])` using `by linear_combination hz'`. Establish `hq : ((z : ℚ_[g])) ^ 2 = -(d : ℚ_[g])`. Use `congrArg (fun t : ℤ_[g] => (t : ℚ_[g])) hs` as an intermediate fact. Simplify using `using this`. Use `⟨LocF.emb v g hgv (z : ℚ_[g]), ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_pow, hq, map_neg, map_natCast]`.
-/
theorem exists_sqrt (g d : ℕ) (hg : g.Prime) (hg2 : g ≠ 2) (hgv : (g : 𝓞 F) ∈ v.asIdeal)
    (hj : jacobiSym (-(d : ℤ)) g = 1) : ∃ r : v.adicCompletion F, r ^ 2 = -(d : v.adicCompletion F) := by
  haveI : Fact g.Prime := ⟨hg⟩
  have hne : (d : ZMod g) ≠ 0 := by
    intro h0
    have h1 : (((-(d : ℤ)) : ℤ) : ZMod g) = 0 := by push_cast; rw [h0, neg_zero]
    have h2 := (legendreSym.eq_zero_iff g (-(d : ℤ))).mpr h1
    first
    | (rw [jacobiSym.legendreSym.to_jacobiSym, hj] at h2; exact one_ne_zero h2)
    | (rw [← jacobiSym.legendreSym.to_jacobiSym] at hj; rw [hj] at h2; exact one_ne_zero h2)
    | (simp only [jacobiSym.legendreSym.to_jacobiSym, hj] at h2; exact one_ne_zero h2)
  have hsqr : IsSquare (((-(d : ℤ)) : ℤ) : ZMod g) := by
    first
    | exact ZMod.isSquare_of_jacobiSym_eq_one hj
    | exact (legendreSym.eq_one_iff g (by push_cast; exact neg_ne_zero.mpr hne)).1
        (by rw [jacobiSym.legendreSym.to_jacobiSym]; exact hj)
  obtain ⟨c, hc⟩ := hsqr
  push_cast at hc
  obtain ⟨a0, ha0⟩ := ZMod.intCast_surjective c
  have hdvd : (g : ℤ) ∣ a0 ^ 2 + d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ha0]
    linear_combination -hc
  have h2ne : (2 : ZMod g) ≠ 0 := by
    first
    | exact Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hg2)
    | (intro h
       have h' : ((2 : ℕ) : ZMod g) = 0 := by exact_mod_cast h
       rw [ZMod.natCast_zmod_eq_zero_iff_dvd] at h'
       exact hg2 ((Nat.prime_dvd_prime_iff_eq hg Nat.prime_two).1 h'))
  have hnd : ¬ (g : ℤ) ∣ 2 * a0 := by
    intro h
    have h2 : (((2 * a0 : ℤ)) : ZMod g) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h
    push_cast at h2
    rw [ha0] at h2
    have hc0 : c = 0 := (mul_eq_zero.mp h2).resolve_left h2ne
    apply hne
    rw [hc0, mul_zero] at hc
    exact neg_eq_zero.mp hc
  set P : Polynomial ℤ_[g] := Polynomial.X ^ 2 + Polynomial.C (d : ℤ_[g]) with hP
  have hev : P.eval (a0 : ℤ_[g]) = ((a0 ^ 2 + d : ℤ) : ℤ_[g]) := by
    first
    | (simp [hP]; done)
    | (simp [hP]; norm_num; done)
    | (simp [hP]; ring)
  have hder : P.derivative.eval (a0 : ℤ_[g]) = ((2 * a0 : ℤ) : ℤ_[g]) := by
    first
    | (simp [hP]; done)
    | (simp [hP]; norm_num; done)
    | (simp [hP]; ring)
  have hn1 : ‖((a0 ^ 2 + d : ℤ) : ℤ_[g])‖ < 1 := by
    first
    | exact (PadicInt.norm_int_lt_one_iff_dvd _).2 hdvd
    | (rw [PadicInt.norm_lt_one_iff_dvd]; simpa using map_dvd (Int.castRingHom ℤ_[g]) hdvd)
  have hn2 : ‖((2 * a0 : ℤ) : ℤ_[g])‖ = 1 := by
    have hle := PadicInt.norm_le_one ((2 * a0 : ℤ) : ℤ_[g])
    have hnlt : ¬ ‖((2 * a0 : ℤ) : ℤ_[g])‖ < 1 := by
      rw [PadicInt.norm_int_lt_one_iff_dvd]
      exact hnd
    exact le_antisymm hle (not_lt.mp hnlt)
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := P) (a := (a0 : ℤ_[g])) (by simp only [Polynomial.coe_aeval_eq_eval]; rw [hev, hder, hn2]; simpa using hn1)
  have hz' : z ^ 2 + (d : ℤ_[g]) = 0 := by simpa [hP] using hz
  have hs : z ^ 2 = -(d : ℤ_[g]) := by linear_combination hz'
  have hq : ((z : ℚ_[g])) ^ 2 = -(d : ℚ_[g]) := by
    have := congrArg (fun t : ℤ_[g] => (t : ℚ_[g])) hs
    simpa using this
  refine ⟨LocF.emb v g hgv (z : ℚ_[g]), ?_⟩
  rw [← map_pow, hq, map_neg, map_natCast]

end Gen

section HostLoc

variable {R : Ranks} (H : Host R)

/- English proof (translation)
Use `show H.conj (H.conj x) = x`. Establish `hcc : R.toFrame.cc * R.toFrame.cc = 1`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `first`. Consider the case `decide`.

Consider the case `rfl`. Consider the case `simp [Formalism.HC.Frame.cc]`. Use `first`. Consider the case `exact mul_one _`. Consider the case `simp [Formalism.HC.Frame.cc]`.

Establish `hc2 : H.conj * H.conj = 1` using `by show H.gal.symm R.toFrame.cc * H.gal.symm R.toFrame.cc = 1`. Rewrite using `[← map_mul, hcc, map_one]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem conjF_conjF (x : H.E) : conjF H (conjF H x) = x := by
  show H.conj (H.conj x) = x
  have hcc : R.toFrame.cc * R.toFrame.cc = 1 := by
    refine Prod.ext ?_ ?_
    · first
      | decide
      | rfl
      | simp [Formalism.HC.Frame.cc]
    · first
      | exact mul_one _
      | simp [Formalism.HC.Frame.cc]
  have hc2 : H.conj * H.conj = 1 := by
    show H.gal.symm R.toFrame.cc * H.gal.symm R.toFrame.cc = 1
    rw [← map_mul, hcc, map_one]
  calc H.conj (H.conj x) = (H.conj * H.conj) x := rfl
    _ = x := by rw [hc2]; rfl

/- English proof (translation)
Establish `hcc : ∀ y, conjF H (conjF H y) = y` using `conjF_conjF H`. Establish `hdpos : 0 < H.d` using `lt_of_le_of_lt (Nat.zero_le _) H.qd_big.2`. Establish `hb0 : H.sqd ≠ 0`. Introduce `h0`. Establish `h1` using `H.sqd_sq`.

Rewrite `h1` using `[h0]`. Establish `h3 : (H.d : H.E) = 0` using `by linear_combination h1`. Conclude with `hdpos.ne' (by exact_mod_cast h3)`. Establish `hb : conjF H H.sqd = -H.sqd` using `by show H.conj H.sqd = -H.sqd`. Establish `h1` using `H.gal_sqd H.conj`.

Establish `hg1 : H.gal H.conj = R.toFrame.cc` using `H.gal.apply_symm_apply _`. Rewrite `h1` using `[hg1]`. Establish `hc : (((R.toFrame.cc.1.2 : ℤˣ) : ℤ)) = -1` using `by first`. Consider the case `rfl`. Consider the case `decide`.

Consider the case `simp [Formalism.HC.Frame.cc]`. Rewrite using `[h1, hc]`. Simplify using the standard rewrite rules. Establish `hfix : ∀ x, conjF H x = x → ∃ a, algebraMap H.F H.E a = x` using `fun x hx => ⟨⟨x, (conj_eq_self_iff H x).1 hx⟩, rfl⟩`. Establish `hbF : H.sqd ∉ Set.range (algebraMap H.F H.E)`.

Introduce and unpack `⟨a, ha⟩`. Apply `hb0` to reduce the goal to its premises. Establish `h1 : conjF H H.sqd = H.sqd` using `by rw [← ha]; exact (conjF H).commutes a`. Establish `h2 : (2 : H.E) * H.sqd = 0` using `by linear_combination hb - h1`. Conclude with `(mul_eq_zero.mp h2).resolve_left two_ne_zero`.

Establish `hmonic : (Polynomial.X ^ 2 + Polynomial.C (H.d : H.F) : Polynomial H.F).Monic` using `by first`. Consider the case `exact Polynomial.monic_X_pow_add_C _ two_ne_zero`. Consider the case `exact Polynomial.monic_X_pow_add_C _ (by norm_num)`. Consider the case `monicity!`. Establish `haeval : Polynomial.aeval H.sqd (Polynomial.X ^ 2 + Polynomial.C (H.d : H.F) : Polynomial H.F) = 0`.

Simplify using `[H.sqd_sq]`. Establish `hirr : Irreducible (Polynomial.X ^ 2 + Polynomial.C (H.d : H.F) : Polynomial H.F)`. Apply `Polynomial.irreducible_of_degree_le_three_of_not_isRoot` to reduce the goal to its premises. Rewrite using `[Polynomial.natDegree_X_pow_add_C]`. Evaluate the decidable proposition.

Introduce `a ha`. Apply `hbF` to reduce the goal to its premises. Establish `ha' : a ^ 2 + (H.d : H.F) = 0` using `by simpa using ha`. Establish `hx : (algebraMap H.F H.E a) ^ 2 + (H.d : H.E) = 0`. Rewrite using `[← map_pow, ← map_natCast (algebraMap H.F H.E) H.d, ← map_add, ha', map_zero]`.

Establish `hsq : (H.sqd - algebraMap H.F H.E a) * (H.sqd + algebraMap H.F H.E a) = 0`. Take the linear combination `H.sqd_sq - hx`. Break down `mul_eq_zero.mp hsq with h | h` into its components or cases. Conclude with `⟨a, (sub_eq_zero.mp h).symm⟩`. Conclude with `⟨-a, by rw [map_neg]; linear_combination -h⟩`.

Establish `hmin : (Polynomial.X ^ 2 + Polynomial.C (H.d : H.F) : Polynomial H.F) = minpoly H.F H.sqd` using `minpoly.eq_of_irreducible_of_monic hirr haeval hmonic`. Establish `hint : IsIntegral H.F H.sqd` using `⟨_, hmonic, haeval⟩`. Establish `htop : IntermediateField.adjoin H.F {H.sqd} = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `x _`.

Establish `hA : conjF H ((x + conjF H x) / 2) = (x + conjF H x) / 2`. Rewrite using `[map_div₀, map_add, hcc, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Establish `hB : conjF H ((x - conjF H x) / (2 * H.sqd)) = (x - conjF H x) / (2 * H.sqd)`. Rewrite using `[map_div₀, map_sub, map_mul, hcc, map_ofNat, hb]`.

Use `first`. Consider the case `(field_simp; ring)`. Consider the case `field_simp`. Consider the case `ring`. Take `⟨a1, ha1⟩` from `hfix _ hA`.

Take `⟨a2, ha2⟩` from `hfix _ hB`. Establish `hx : x = algebraMap H.F H.E a1 + algebraMap H.F H.E a2 * H.sqd`. Rewrite using `[ha1, ha2]`. Use `first`. Consider the case `(field_simp; ring)`.

Consider the case `field_simp`. Consider the case `ring`. Rewrite using `[hx]`. Conclude with `add_mem (IntermediateField.algebraMap_mem _ a1) (mul_mem (IntermediateField.algebraMap_mem _ a2) (IntermediateField.mem_adjoin_simple_self H.F H.sqd))`. Establish `hfin : Module.finrank H.F (IntermediateField.adjoin H.F {H.sqd}) = (minpoly H.F H.sqd).natDegree` using `IntermediateField.adjoin.finrank hint`.

Rewrite `hfin` using `[← hmin, Polynomial.natDegree_X_pow_add_C]`. Rewrite using `[← hfin]`. Conclude with `((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv).toLinearEquiv.finrank_eq.symm`.
-/
theorem finrank_FE : Module.finrank H.F H.E = 2 := by
  classical
  have hcc : ∀ y, conjF H (conjF H y) = y := conjF_conjF H
  have hdpos : 0 < H.d := lt_of_le_of_lt (Nat.zero_le _) H.qd_big.2
  have hb0 : H.sqd ≠ 0 := by
    intro h0
    have h1 := H.sqd_sq
    rw [h0] at h1
    have h3 : (H.d : H.E) = 0 := by linear_combination h1
    exact hdpos.ne' (by exact_mod_cast h3)
  have hb : conjF H H.sqd = -H.sqd := by
    show H.conj H.sqd = -H.sqd
    have h1 := H.gal_sqd H.conj
    have hg1 : H.gal H.conj = R.toFrame.cc := H.gal.apply_symm_apply _
    rw [hg1] at h1
    have hc : (((R.toFrame.cc.1.2 : ℤˣ) : ℤ)) = -1 := by
      first
      | rfl
      | decide
      | simp [Formalism.HC.Frame.cc]
    rw [h1, hc]
    simp
  have hfix : ∀ x, conjF H x = x → ∃ a, algebraMap H.F H.E a = x :=
    fun x hx => ⟨⟨x, (conj_eq_self_iff H x).1 hx⟩, rfl⟩
  have hbF : H.sqd ∉ Set.range (algebraMap H.F H.E) := by
    rintro ⟨a, ha⟩
    apply hb0
    have h1 : conjF H H.sqd = H.sqd := by rw [← ha]; exact (conjF H).commutes a
    have h2 : (2 : H.E) * H.sqd = 0 := by linear_combination hb - h1
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  have hmonic : (Polynomial.X ^ 2 + Polynomial.C (H.d : H.F) : Polynomial H.F).Monic := by
    first
    | exact Polynomial.monic_X_pow_add_C _ two_ne_zero
    | exact Polynomial.monic_X_pow_add_C _ (by norm_num)
    | monicity!
  have haeval : Polynomial.aeval H.sqd (Polynomial.X ^ 2 + Polynomial.C (H.d : H.F) : Polynomial H.F) = 0 := by
    simp [H.sqd_sq]
  have hirr : Irreducible (Polynomial.X ^ 2 + Polynomial.C (H.d : H.F) : Polynomial H.F) := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [Polynomial.natDegree_X_pow_add_C]
      decide
    · intro a ha
      apply hbF
      have ha' : a ^ 2 + (H.d : H.F) = 0 := by simpa using ha
      have hx : (algebraMap H.F H.E a) ^ 2 + (H.d : H.E) = 0 := by
        rw [← map_pow, ← map_natCast (algebraMap H.F H.E) H.d, ← map_add, ha', map_zero]
      have hsq : (H.sqd - algebraMap H.F H.E a) * (H.sqd + algebraMap H.F H.E a) = 0 := by
        linear_combination H.sqd_sq - hx
      rcases mul_eq_zero.mp hsq with h | h
      · exact ⟨a, (sub_eq_zero.mp h).symm⟩
      · exact ⟨-a, by rw [map_neg]; linear_combination -h⟩
  have hmin : (Polynomial.X ^ 2 + Polynomial.C (H.d : H.F) : Polynomial H.F) = minpoly H.F H.sqd :=
    minpoly.eq_of_irreducible_of_monic hirr haeval hmonic
  have hint : IsIntegral H.F H.sqd := ⟨_, hmonic, haeval⟩
  have htop : IntermediateField.adjoin H.F {H.sqd} = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hA : conjF H ((x + conjF H x) / 2) = (x + conjF H x) / 2 := by
      rw [map_div₀, map_add, hcc, map_ofNat]
      ring
    have hB : conjF H ((x - conjF H x) / (2 * H.sqd)) = (x - conjF H x) / (2 * H.sqd) := by
      rw [map_div₀, map_sub, map_mul, hcc, map_ofNat, hb]
      first
      | (field_simp; ring)
      | field_simp
      | ring
    obtain ⟨a1, ha1⟩ := hfix _ hA
    obtain ⟨a2, ha2⟩ := hfix _ hB
    have hx : x = algebraMap H.F H.E a1 + algebraMap H.F H.E a2 * H.sqd := by
      rw [ha1, ha2]
      first
      | (field_simp; ring)
      | field_simp
      | ring
    rw [hx]
    exact add_mem (IntermediateField.algebraMap_mem _ a1)
      (mul_mem (IntermediateField.algebraMap_mem _ a2) (IntermediateField.mem_adjoin_simple_self H.F H.sqd))
  have hfin : Module.finrank H.F (IntermediateField.adjoin H.F {H.sqd}) = (minpoly H.F H.sqd).natDegree :=
    IntermediateField.adjoin.finrank hint
  rw [← hmin, Polynomial.natDegree_X_pow_add_C] at hfin
  rw [← hfin]
  exact ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv).toLinearEquiv.finrank_eq.symm

def slocH (v : HeightOneSpectrum (𝓞 H.F)) : LocAt H.F H.E (conjF H) v :=
  locAtC (conjF H) (conjF_conjF H) (finrank_FE H) v

open Ideal in

/- English proof (translation)
Establish `: IsGaloisGroup Gal(H.E/ℚ) ℤ (𝓞 H.E)` using `IsGaloisGroup.of_isFractionRing _ _ _ ℚ H.E`. Establish `hpZ : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.1 hp`. Establish `hpI : (span {(p : ℤ)}).IsPrime` using `(span_singleton_prime hpZ.ne_zero).2 hpZ`. Establish `hpM : (span {(p : ℤ)}).IsMaximal` using `hpI.isMaximal (by rw [Ne, span_singleton_eq_bot]; exact hpZ.ne_zero)`. Establish `hne0 : ∀ I : Ideal (𝓞 H.E), I.LiesOver (span {(p : ℤ)}) → I ≠ ⊥`.

Introduce and unpack `I hI rfl`. Establish `h0 : span {(p : ℤ)} = ⊥`. Rewrite using `[hI.over]`. Conclude with `Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 H.E))`. Conclude with `hpZ.ne_zero (span_singleton_eq_bot.1 h0)`.

Establish `himg : (fun w : HeightOneSpectrum (𝓞 H.E) => w.asIdeal) '' placesOver H.E p = (span {(p : ℤ)}).primesOver (𝓞 H.E)`. Use extensionality with `I`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Use `⟨w.isPrime, ⟨?_⟩⟩` and prove the remaining obligations.

Establish `hle : span {(p : ℤ)} ≤ w.asIdeal.under ℤ`. Rewrite using `[span_le, Set.singleton_subset_iff]`. Express the relevant statement in the definitionally equal form `algebraMap ℤ (𝓞 H.E) p ∈ w.asIdeal`. Establish `hw' : ((p : ℕ) : 𝓞 H.E) ∈ w.asIdeal` using `hw`. Simplify using `using hw'`.

Use `w.isPrime` as an intermediate fact. Conclude with `hpM.eq_of_le (Ideal.IsPrime.under ℤ w.asIdeal).ne_top hle`. Introduce and unpack `⟨hI, hIl⟩`. Use `⟨⟨I, hI, hne0 I hIl⟩, ?_, rfl⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((p : ℕ) : 𝓞 H.E) ∈ I`.

Establish `: (p : ℤ) ∈ I.under ℤ` using `by rw [← hIl.over]; exact mem_span_singleton_self _`. Simplify using `using this`. Establish `key` using `ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (span {(p : ℤ)}) (𝓞 H.E) Gal(H.E/ℚ)`. Rewrite `key` using `[← himg, Set.ncard_image_of_injective _ (fun v w h => HeightOneSpectrum.ext h), h, IsGalois.card_aut_eq_finrank]`. Establish `hpos : 0 < Module.finrank ℚ H.E` using `Module.finrank_pos`.

Establish `he : ramificationIdxIn (span {(p : ℤ)}) (𝓞 H.E) = 1` using `Nat.eq_one_of_mul_eq_one_right ((Nat.mul_eq_left hpos.ne').mp key)`. Establish `hvp` using `v.isPrime`. Establish `hvl : v.asIdeal.LiesOver (span {(p : ℤ)})` using `⟨by`. Use `hpM.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top ?_` and prove the remaining obligations. Rewrite using `[span_le, Set.singleton_subset_iff]`.

Express the relevant statement in the definitionally equal form `algebraMap ℤ (𝓞 H.F) p ∈ v.asIdeal`. Simplify using `using hv⟩`. Take `⟨⟨P, hPp, hPl⟩⟩ : Nonempty (v.asIdeal.primesOver (𝓞 H.E))` from `inferInstance`. Establish `hPZ : P.LiesOver (span {(p : ℤ)})` using `Ideal.LiesOver.trans P v.asIdeal _`. Rewrite `he` using `[ramificationIdxIn_eq_ramificationIdx (span {(p : ℤ)}) P Gal(H.E/ℚ), Ideal.ramificationIdx_tower (R := ℤ) v.asIdeal P]`.

Establish `h1 : eWL H.F v = 1` using `Nat.eq_one_of_mul_eq_one_right he`. Establish `h2` using `bridge_unit_rule_holds H.F p v hp hv`. Rewrite `h2` using `[h1, vAdd]`. Establish `hne : v.valuation H.F (p : H.F) ≠ 0` using `(Valuation.ne_zero_iff _).mpr (Nat.cast_ne_zero.mpr hp.ne_zero)`. Rewrite using `[← exp_log hne]`.

Use `congr 1`. Move the coercions through the operations in `at h2`. Use linear arithmetic over natural numbers and integers.
-/
theorem val_eq_of_split (p : ℕ) (hp : p.Prime)
    (h : (placesOver H.E p).ncard = Module.finrank ℚ H.E) (v : HeightOneSpectrum (𝓞 H.F))
    (hv : (p : 𝓞 H.F) ∈ v.asIdeal) : v.valuation H.F (p : H.F) = exp (-1 : ℤ) := by
  have : IsGaloisGroup Gal(H.E/ℚ) ℤ (𝓞 H.E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ H.E
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (span {(p : ℤ)}).IsPrime := (span_singleton_prime hpZ.ne_zero).2 hpZ
  have hpM : (span {(p : ℤ)}).IsMaximal :=
    hpI.isMaximal (by rw [Ne, span_singleton_eq_bot]; exact hpZ.ne_zero)
  have hne0 : ∀ I : Ideal (𝓞 H.E), I.LiesOver (span {(p : ℤ)}) → I ≠ ⊥ := by
    rintro I hI rfl
    have h0 : span {(p : ℤ)} = ⊥ := by
      rw [hI.over]; exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 H.E))
    exact hpZ.ne_zero (span_singleton_eq_bot.1 h0)
  have himg : (fun w : HeightOneSpectrum (𝓞 H.E) => w.asIdeal) '' placesOver H.E p =
      (span {(p : ℤ)}).primesOver (𝓞 H.E) := by
    ext I
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w.isPrime, ⟨?_⟩⟩
      have hle : span {(p : ℤ)} ≤ w.asIdeal.under ℤ := by
        rw [span_le, Set.singleton_subset_iff]
        change algebraMap ℤ (𝓞 H.E) p ∈ w.asIdeal
        have hw' : ((p : ℕ) : 𝓞 H.E) ∈ w.asIdeal := hw
        simpa using hw'
      have := w.isPrime
      exact hpM.eq_of_le (Ideal.IsPrime.under ℤ w.asIdeal).ne_top hle
    · rintro ⟨hI, hIl⟩
      refine ⟨⟨I, hI, hne0 I hIl⟩, ?_, rfl⟩
      change ((p : ℕ) : 𝓞 H.E) ∈ I
      have : (p : ℤ) ∈ I.under ℤ := by rw [← hIl.over]; exact mem_span_singleton_self _
      simpa using this
  have key := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (span {(p : ℤ)}) (𝓞 H.E) Gal(H.E/ℚ)
  rw [← himg, Set.ncard_image_of_injective _ (fun v w h => HeightOneSpectrum.ext h), h,
    IsGalois.card_aut_eq_finrank] at key
  have hpos : 0 < Module.finrank ℚ H.E := Module.finrank_pos
  have he : ramificationIdxIn (span {(p : ℤ)}) (𝓞 H.E) = 1 :=
    Nat.eq_one_of_mul_eq_one_right ((Nat.mul_eq_left hpos.ne').mp key)
  have hvp := v.isPrime
  have hvl : v.asIdeal.LiesOver (span {(p : ℤ)}) := ⟨by
    refine hpM.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top ?_
    rw [span_le, Set.singleton_subset_iff]
    change algebraMap ℤ (𝓞 H.F) p ∈ v.asIdeal
    simpa using hv⟩
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty (v.asIdeal.primesOver (𝓞 H.E)) := inferInstance
  have hPZ : P.LiesOver (span {(p : ℤ)}) := Ideal.LiesOver.trans P v.asIdeal _
  rw [ramificationIdxIn_eq_ramificationIdx (span {(p : ℤ)}) P Gal(H.E/ℚ),
    Ideal.ramificationIdx_tower (R := ℤ) v.asIdeal P] at he
  have h1 : eWL H.F v = 1 := Nat.eq_one_of_mul_eq_one_right he
  have h2 := bridge_unit_rule_holds H.F p v hp hv
  rw [h1, vAdd] at h2
  have hne : v.valuation H.F (p : H.F) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  rw [← exp_log hne]
  congr 1
  push_cast at h2
  omega

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, resChar v = H.g k := by`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hv`. Break down `hv with h | h` into its components or cases. Conclude with `⟨0, h⟩`. Conclude with `⟨1, h⟩`.

Establish `hp : (resChar v).Prime` using `resChar_prime v`. Establish `hmem : ((resChar v : ℕ) : 𝓞 H.F) ∈ v.asIdeal` using `resChar_mem v`. Establish `hspl : (placesOver H.E (resChar v)).ncard = Module.finrank ℚ H.E`. Rewrite using `[hk]`. Conclude with `hg k`.

Establish `hval : v.valuation H.F ((resChar v : ℕ) : H.F) = exp (-1 : ℤ)` using `val_eq_of_split H (resChar v) hp hspl v hmem`. Establish `hj2 : resChar v ≠ 2` using `by rw [hk]; exact (hj k).1`. Establish `hjac : jacobiSym (-(H.d : ℤ)) (resChar v) = 1` using `by rw [hk]; exact (hj k).2`. Take `⟨r, hr⟩` from `exists_sqrt v (resChar v) H.d hp hj2 hmem hjac`. Establish `hdpos : 0 < H.d` using `lt_of_le_of_lt (Nat.zero_le _) H.qd_big.2`.

Establish `hb0 : H.sqd ≠ 0`. Introduce `h0`. Establish `h1` using `H.sqd_sq`. Rewrite `h1` using `[h0]`. Establish `h3 : (H.d : H.E) = 0` using `by linear_combination h1`.

Conclude with `hdpos.ne' (by exact_mod_cast h3)`. Establish `hb : conjF H H.sqd = -H.sqd` using `by show H.conj H.sqd = -H.sqd`. Establish `h1` using `H.gal_sqd H.conj`. Establish `hg1 : H.gal H.conj = R.toFrame.cc` using `H.gal.apply_symm_apply _`. Rewrite `h1` using `[hg1]`.

Establish `hc : (((R.toFrame.cc.1.2 : ℤˣ) : ℤ)) = -1` using `by first`. Consider the case `rfl`. Consider the case `decide`. Consider the case `simp [Formalism.HC.Frame.cc]`. Rewrite using `[h1, hc]`.

Simplify using the standard rewrite rules. Establish `hfix : ∀ x, conjF H x = x → ∃ a, algebraMap H.F H.E a = x` using `fun x hx => ⟨⟨x, (conj_eq_self_iff H x).1 hx⟩, rfl⟩`. Take `⟨φ⟩` from `exists_emb (conjF H) (conjF_conjF H) hfix H.sqd hb0 hb H.d H.sqd_sq r hr`. Conclude with `splitAt_nonempty (conjF H) (conjF_conjF H) (finrank_FE H) v φ H.sqd hb0 hb hval`.
-/
theorem splH (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E)
    (hj : ∀ k, H.g k ≠ 2 ∧ jacobiSym (-(H.d : ℤ)) (H.g k) = 1) (v : HeightOneSpectrum (𝓞 H.F))
    (hv : resChar v ∈ ({H.g 0, H.g 1} : Finset ℕ)) :
    Nonempty (SplitAt (slocH H v).Fp (slocH H v).Ep (slocH H v).cj (resChar v)) := by
  obtain ⟨k, hk⟩ : ∃ k, resChar v = H.g k := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  have hp : (resChar v).Prime := resChar_prime v
  have hmem : ((resChar v : ℕ) : 𝓞 H.F) ∈ v.asIdeal := resChar_mem v
  have hspl : (placesOver H.E (resChar v)).ncard = Module.finrank ℚ H.E := by
    rw [hk]; exact hg k
  have hval : v.valuation H.F ((resChar v : ℕ) : H.F) = exp (-1 : ℤ) :=
    val_eq_of_split H (resChar v) hp hspl v hmem
  have hj2 : resChar v ≠ 2 := by rw [hk]; exact (hj k).1
  have hjac : jacobiSym (-(H.d : ℤ)) (resChar v) = 1 := by rw [hk]; exact (hj k).2
  obtain ⟨r, hr⟩ := exists_sqrt v (resChar v) H.d hp hj2 hmem hjac
  have hdpos : 0 < H.d := lt_of_le_of_lt (Nat.zero_le _) H.qd_big.2
  have hb0 : H.sqd ≠ 0 := by
    intro h0
    have h1 := H.sqd_sq
    rw [h0] at h1
    have h3 : (H.d : H.E) = 0 := by linear_combination h1
    exact hdpos.ne' (by exact_mod_cast h3)
  have hb : conjF H H.sqd = -H.sqd := by
    show H.conj H.sqd = -H.sqd
    have h1 := H.gal_sqd H.conj
    have hg1 : H.gal H.conj = R.toFrame.cc := H.gal.apply_symm_apply _
    rw [hg1] at h1
    have hc : (((R.toFrame.cc.1.2 : ℤˣ) : ℤ)) = -1 := by
      first
      | rfl
      | decide
      | simp [Formalism.HC.Frame.cc]
    rw [h1, hc]
    simp
  have hfix : ∀ x, conjF H x = x → ∃ a, algebraMap H.F H.E a = x :=
    fun x hx => ⟨⟨x, (conj_eq_self_iff H x).1 hx⟩, rfl⟩
  obtain ⟨φ⟩ := exists_emb (conjF H) (conjF_conjF H) hfix H.sqd hb0 hb H.d H.sqd_sq r hr
  exact splitAt_nonempty (conjF H) (conjF_conjF H) (finrank_FE H) v φ H.sqd hb0 hb hval

end HostLoc

end Formalism.BasicNotions.Examples₂
