import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermPrimitiveForm
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteFibreGermIntegral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StZariskiAnalyticNormality
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDiscrAdjoin
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Polynomial

noncomputable section

/- English proof (translation)
Establish `: FaithfulSMul R S` using `(faithfulSMul_iff_algebraMap_injective R S).2 hinj`. Set `_ : Algebra (FractionRing R) (FractionRing S)` to `FractionRing.liftAlgebra R (FractionRing S)`. Set `ι : S →ₐ[R] FractionRing S` to `IsScalarTower.toAlgHom R S (FractionRing S)`. Establish `hι : Function.Injective ι` using `IsFractionRing.injective S (FractionRing S)`. Establish `hint : ∀ s : S, IsIntegral R (ι s)` using `fun s => (Algebra.IsIntegral.isIntegral s).map ι`.

Set `zb : Fin n → FractionRing S` to `fun j => ι (z j)`. Set `L'` to `IntermediateField.adjoin (FractionRing R) (Set.range zb)`. Establish `: FiniteDimensional (FractionRing R) L'` using `IntermediateField.finiteDimensional_adjoin (by`. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `(hint (z j)).tower_top)`.

Set `_ : Algebra ℂ (FractionRing R)` to `((algebraMap R (FractionRing R)).comp c).toAlgebra`. Set `_ : Algebra ℂ L'` to `((algebraMap (FractionRing R) L').comp (algebraMap ℂ (FractionRing R))).toAlgebra`. Establish `: IsScalarTower ℂ (FractionRing R) L'` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `: CharZero (FractionRing R)` using `charZero_of_injective_algebraMap (algebraMap ℂ (FractionRing R)).injective`. Establish `: Algebra.IsSeparable (FractionRing R) L'` using `inferInstance`.

Set `V : L' →ₐ[R] FractionRing S` to `(IntermediateField.val L').restrictScalars R`. Establish `hV : Function.Injective V` using `Subtype.val_injective`. Set `x : Fin n → L'` to `fun j => ⟨zb j, IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩⟩`. Establish `hVx : ∀ j, V (x j) = ι (z j)` using `fun j => rfl`. Establish `hx : IntermediateField.adjoin (FractionRing R) (Set.range x) = ⊤`.

Apply `IntermediateField.map_injective L'.val` to reduce the goal to its premises. Rewrite using `[IntermediateField.adjoin_map, ← Set.range_comp, ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val]`. Both sides reduce to the same expression. Take `⟨Dp, hDp0, hDp⟩` from `hG ℂ (FractionRing R) L' n x hx`. Take `⟨cc, hcc⟩ : ∃ cc : Fin n → ℂ, MvPolynomial.eval cc Dp ≠ 0` from `by by_contra! h`.

Conclude with `hDp0 (MvPolynomial.funext fun v => by simpa using h v)`. Establish `hprim` using `hDp cc hcc`. Use `set ℓs : S := ∑ j, algebraMap R S (c (cc j)) * z j with hℓs`. Use `set ℓ' : L' := ∑ j, cc j • x j with hℓ'`. Establish `hVℓ : V ℓ' = ι ℓs`.

Simplify using `only [hℓ', hℓs, map_sum, map_mul, Algebra.smul_def, hVx]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[AlgHom.commutes, IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing S)]`. Both sides reduce to the same expression.

Establish `hintL : ∀ w : L', IsIntegral R (V w) → IsIntegral R w` using `fun w h => (isIntegral_algHom_iff V hV).1 h`. Establish `hℓint : IsIntegral R ℓ'` using `hintL _ (by rw [hVℓ]; exact hint _)`. Take `⟨-, hdisc, hmem⟩` from `hD R (FractionRing R) L' ℓ' hℓint hprim`. Use `set p := minpoly R ℓ' with hp`. Establish `hpm : p.Monic` using `minpoly.monic hℓint`.

Establish `hpos : 0 < p.natDegree` using `minpoly.natDegree_pos hℓint`. Establish `htransfer : ∀ (f : R[X]) (s : S) (w : L'), V w = ι s → ι (aeval s f) = V (aeval w f)` using `fun f s w h => by rw [← aeval_algHom_apply, ← aeval_algHom_apply, h]`. Establish `hres : p.resultant (derivative p) p.natDegree (p.natDegree - 1) = (-1) ^ (p.natDegree * (p.natDegree - 1) / 2) * p.discr`. Rewrite using `[resultant_deriv (natDegree_pos_iff_degree_pos.1 hpos), hpm.leadingCoeff, mul_one]`. Use `⟨cc, p, hpm, hpos, ?_, ?_, fun i => ?_⟩` and prove the remaining obligations.

Apply `hι` to reduce the goal to its premises. Rewrite using `[htransfer p ℓs ℓ' hVℓ, minpoly.aeval, map_zero, map_zero]`. Rewrite using `[hres]`. Conclude with `mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hdisc`. Establish `hxi : IsIntegral R (x i)` using `hintL _ (by rw [hVx]; exact hint _)`.

Establish `hm : p.resultant (derivative p) p.natDegree (p.natDegree - 1) • x i ∈ Algebra.adjoin R {ℓ'}`. Rewrite using `[hres, mul_smul]`. Conclude with `Subalgebra.smul_mem _ (hmem _ hxi) _`. Rewrite `hm` using `[Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨f, hf⟩` from `hm`.

Use `⟨f %ₘ p, natDegree_modByMonic_lt f hpm (minpoly.ne_one R ℓ'), ?_⟩` and prove the remaining obligations. Apply `hι` to reduce the goal to its premises. Rewrite using `[htransfer _ ℓs ℓ' hVℓ, aeval_modByMonic_eq_self_of_root (minpoly.aeval R ℓ')]`. Establish `hf' : aeval ℓ' f = _` using `hf`. Rewrite using `[hf', map_smul, hVx, ← map_smul, Algebra.smul_def]`.
-/
theorem primitive_with_resultant_denominator (hG : GroundTheory.Heights₂.Heights.ComplexSets.GenericPrimitive.Statement)
    (hD : GroundTheory.Heights₂.Heights.ComplexSets.DiscrAdjoin.Statement)
    {R S : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing S] [IsDomain S] [Algebra R S]
    (hinj : Function.Injective (algebraMap R S)) [Algebra.IsIntegral R S] (c : ℂ →+* R)
    {n : ℕ} (z : Fin n → S) :
    ∃ (cc : Fin n → ℂ) (p : R[X]), p.Monic ∧ 0 < p.natDegree ∧
      aeval (∑ j, algebraMap R S (c (cc j)) * z j) p = 0 ∧
      p.resultant (derivative p) p.natDegree (p.natDegree - 1) ≠ 0 ∧
      ∀ i, ∃ f : R[X], f.natDegree < p.natDegree ∧
        aeval (∑ j, algebraMap R S (c (cc j)) * z j) f =
          algebraMap R S (p.resultant (derivative p) p.natDegree (p.natDegree - 1)) * z i := by
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).2 hinj
  let _ : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra R (FractionRing S)
  let ι : S →ₐ[R] FractionRing S := IsScalarTower.toAlgHom R S (FractionRing S)
  have hι : Function.Injective ι := IsFractionRing.injective S (FractionRing S)
  have hint : ∀ s : S, IsIntegral R (ι s) := fun s => (Algebra.IsIntegral.isIntegral s).map ι
  let zb : Fin n → FractionRing S := fun j => ι (z j)
  let L' := IntermediateField.adjoin (FractionRing R) (Set.range zb)
  have : FiniteDimensional (FractionRing R) L' := IntermediateField.finiteDimensional_adjoin (by
    rintro _ ⟨j, rfl⟩
    exact (hint (z j)).tower_top)
  let _ : Algebra ℂ (FractionRing R) := ((algebraMap R (FractionRing R)).comp c).toAlgebra
  let _ : Algebra ℂ L' := ((algebraMap (FractionRing R) L').comp (algebraMap ℂ (FractionRing R))).toAlgebra
  have : IsScalarTower ℂ (FractionRing R) L' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (algebraMap ℂ (FractionRing R)).injective
  have : Algebra.IsSeparable (FractionRing R) L' := inferInstance
  let V : L' →ₐ[R] FractionRing S := (IntermediateField.val L').restrictScalars R
  have hV : Function.Injective V := Subtype.val_injective
  let x : Fin n → L' := fun j => ⟨zb j, IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩⟩
  have hVx : ∀ j, V (x j) = ι (z j) := fun j => rfl
  have hx : IntermediateField.adjoin (FractionRing R) (Set.range x) = ⊤ := by
    apply IntermediateField.map_injective L'.val
    rw [IntermediateField.adjoin_map, ← Set.range_comp, ← AlgHom.fieldRange_eq_map,
      IntermediateField.fieldRange_val]
    rfl
  obtain ⟨Dp, hDp0, hDp⟩ := hG ℂ (FractionRing R) L' n x hx
  obtain ⟨cc, hcc⟩ : ∃ cc : Fin n → ℂ, MvPolynomial.eval cc Dp ≠ 0 := by
    by_contra! h
    exact hDp0 (MvPolynomial.funext fun v => by simpa using h v)
  have hprim := hDp cc hcc
  set ℓs : S := ∑ j, algebraMap R S (c (cc j)) * z j with hℓs
  set ℓ' : L' := ∑ j, cc j • x j with hℓ'
  have hVℓ : V ℓ' = ι ℓs := by
    simp only [hℓ', hℓs, map_sum, map_mul, Algebra.smul_def, hVx]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing S)]
    rfl
  have hintL : ∀ w : L', IsIntegral R (V w) → IsIntegral R w := fun w h =>
    (isIntegral_algHom_iff V hV).1 h
  have hℓint : IsIntegral R ℓ' := hintL _ (by rw [hVℓ]; exact hint _)
  obtain ⟨-, hdisc, hmem⟩ := hD R (FractionRing R) L' ℓ' hℓint hprim
  set p := minpoly R ℓ' with hp
  have hpm : p.Monic := minpoly.monic hℓint
  have hpos : 0 < p.natDegree := minpoly.natDegree_pos hℓint
  have htransfer : ∀ (f : R[X]) (s : S) (w : L'), V w = ι s → ι (aeval s f) = V (aeval w f) :=
    fun f s w h => by rw [← aeval_algHom_apply, ← aeval_algHom_apply, h]
  have hres : p.resultant (derivative p) p.natDegree (p.natDegree - 1) =
      (-1) ^ (p.natDegree * (p.natDegree - 1) / 2) * p.discr := by
    rw [resultant_deriv (natDegree_pos_iff_degree_pos.1 hpos), hpm.leadingCoeff, mul_one]
  refine ⟨cc, p, hpm, hpos, ?_, ?_, fun i => ?_⟩
  · apply hι
    rw [htransfer p ℓs ℓ' hVℓ, minpoly.aeval, map_zero, map_zero]
  · rw [hres]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hdisc
  · have hxi : IsIntegral R (x i) := hintL _ (by rw [hVx]; exact hint _)
    have hm : p.resultant (derivative p) p.natDegree (p.natDegree - 1) • x i ∈ Algebra.adjoin R {ℓ'} := by
      rw [hres, mul_smul]
      exact Subalgebra.smul_mem _ (hmem _ hxi) _
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hm
    obtain ⟨f, hf⟩ := hm
    refine ⟨f %ₘ p, natDegree_modByMonic_lt f hpm (minpoly.ne_one R ℓ'), ?_⟩
    apply hι
    rw [htransfer _ ℓs ℓ' hVℓ, aeval_modByMonic_eq_self_of_root (minpoly.aeval R ℓ')]
    have hf' : aeval ℓ' f = _ := hf
    rw [hf', map_smul, hVx, ← map_smul, Algebra.smul_def]

def germsAlong {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) : Subring (Germ (𝓝[X] x) ℂ) where
  carrier := {φ | ∃ f : (σ → ℂ) → ℂ, AnalyticAt ℂ f x ∧ (f : Germ (𝓝[X] x) ℂ) = φ}
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, rfl⟩
  one_mem' := ⟨fun _ => 1, analyticAt_const, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, rfl⟩
  zero_mem' := ⟨fun _ => 0, analyticAt_const, rfl⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, rfl⟩

def analyticAtRing {ι : Type} [Fintype ι] (w : ι → ℂ) : Subring ((ι → ℂ) → ℂ) where
  carrier := {f | AnalyticAt ℂ f w}
  mul_mem' := fun hf hg => hf.mul hg
  one_mem' := (analyticAt_const : AnalyticAt ℂ (fun _ : ι → ℂ => (1 : ℂ)) w)
  add_mem' := fun hf hg => hf.add hg
  zero_mem' := (analyticAt_const : AnalyticAt ℂ (fun _ : ι → ℂ => (0 : ℂ)) w)
  neg_mem' := fun hf => hf.neg

def germOf {ι : Type} [Fintype ι] (w : ι → ℂ) : analyticAtRing w →+* holGerms w :=
  ((Germ.coeRingHom (𝓝 w)).comp (analyticAtRing w).subtype).codRestrict (holGerms w)
    fun f => ⟨f.1, f.2, rfl⟩

/- English proof (translation)
Introduce `φ`. Take `⟨f, hf, hφ⟩` from `φ.2`. Conclude with `⟨⟨f, hf⟩, Subtype.ext hφ⟩`.
-/
theorem germOf_surjective {ι : Type} [Fintype ι] (w : ι → ℂ) : Function.Surjective (germOf w) := by
  intro φ
  obtain ⟨f, hf, hφ⟩ := φ.2
  exact ⟨⟨f, hf⟩, Subtype.ext hφ⟩

def germRep {ι : Type} [Fintype ι] (w : ι → ℂ) : holGerms w → analyticAtRing w :=
  Function.surjInv (germOf_surjective w)

/- English proof (translation)
The claim follows from `Function.surjInv_eq (germOf_surjective w) φ`.
-/
theorem germOf_germRep {ι : Type} [Fintype ι] (w : ι → ℂ) (φ : holGerms w) : germOf w (germRep w φ) = φ :=
  Function.surjInv_eq (germOf_surjective w) φ

/- English proof (translation)
Rewrite using `[← Subtype.coe_inj]`. Conclude with `Germ.coe_eq`.
-/
theorem germOf_eq_zero {ι : Type} [Fintype ι] (w : ι → ℂ) (f : analyticAtRing w) :
    germOf w f = 0 ↔ ∀ᶠ y in 𝓝 w, f.1 y = 0 := by
  rw [← Subtype.coe_inj]
  exact Germ.coe_eq

def alongOf {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) : analyticAtRing x →+* germsAlong X x :=
  ((Germ.coeRingHom (𝓝[X] x)).comp (analyticAtRing x).subtype).codRestrict (germsAlong X x)
    fun f => ⟨f.1, f.2, rfl⟩

def germCompHom {α β : Type} {l : Filter β} {l' : Filter α} (g : α → β) (hg : Tendsto g l' l) :
    Germ l ℂ →+* Germ l' ℂ where
  toFun φ := φ.compTendsto g hg
  map_one' := rfl
  map_mul' φ ψ := Germ.inductionOn₂ φ ψ fun _ _ => rfl
  map_zero' := rfl
  map_add' φ ψ := Germ.inductionOn₂ φ ψ fun _ _ => rfl

/- English proof (translation)
The claim follows from `(A.continuous.tendsto x).mono_left nhdsWithin_le_nhds`.
-/
theorem tendsto_nhdsWithin_linear {σ : Type} [Fintype σ] {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (X : Set (σ → ℂ)) (x : σ → ℂ) : Tendsto A (𝓝[X] x) (𝓝 (A x)) :=
  (A.continuous.tendsto x).mono_left nhdsWithin_le_nhds

def alongPull {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) :
    holGerms (A x) →+* germsAlong X x :=
  ((germCompHom A (tendsto_nhdsWithin_linear A X x)).comp (holGerms (A x)).subtype).codRestrict _ fun φ => by
    obtain ⟨f, hf, hφ⟩ := φ.2
    refine ⟨f ∘ A, hf.comp (A.analyticAt x), ?_⟩
    change _ = (φ.1 : Germ (𝓝 (A x)) ℂ).compTendsto A (tendsto_nhdsWithin_linear A X x)
    rw [← hφ]
    rfl

def preLinear {σ : Type} [Fintype σ] (x : σ → ℂ) {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) :
    analyticAtRing (A x) →+* ((σ → ℂ) → ℂ) :=
  (RingHom.pi fun z => Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) (A z)).comp (analyticAtRing (A x)).subtype

/- English proof (translation)
The claim follows from `eventually_nhdsWithin_iff.1 (Germ.coe_eq.1 h)`.
-/
theorem eventually_of_germ_eq {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {x : σ → ℂ} {f g : (σ → ℂ) → ℂ}
    (h : (f : Germ (𝓝[X] x) ℂ) = g) : ∀ᶠ z in 𝓝 x, z ∈ X → f z = g z :=
  eventually_nhdsWithin_iff.1 (Germ.coe_eq.1 h)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(germsAlong X x).subtype _ = Germ.coeRingHom _ _`. Rewrite using `[eval₂_map, hom_eval₂, hom_eval₂]`. Both sides reduce to the same expression.
-/
theorem coe_eval₂_map {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (P : (analyticAtRing (A x))[X]) (v : analyticAtRing x) :
    ((eval₂ (alongPull X x A) (alongOf X x v) (P.map (germOf (A x))) : germsAlong X x) : Germ (𝓝[X] x) ℂ) =
      ((eval₂ (preLinear x A) v.1 P : (σ → ℂ) → ℂ) : Germ (𝓝[X] x) ℂ) := by
  change (germsAlong X x).subtype _ = Germ.coeRingHom _ _
  rw [eval₂_map, hom_eval₂, hom_eval₂]
  rfl

def constAn {ι : Type} [Fintype ι] (w : ι → ℂ) : ℂ →+* analyticAtRing w :=
  (Pi.constRingHom (ι → ℂ) ℂ).codRestrict _ fun c => (analyticAt_const : AnalyticAt ℂ (fun _ : ι → ℂ => c) w)

/- English proof (translation)
Simplify using `[eval₂_finsetSum, Finset.sum_apply, preLinear]`.
-/
theorem eval₂_monic_apply {σ : Type} [Fintype σ] (x : σ → ℂ) {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (g : (σ → ℂ) → ℂ) {M : ℕ} (b : Fin M → analyticAtRing (A x)) (z : σ → ℂ) :
    eval₂ (preLinear x A) g (X ^ M + ∑ j, C (b j) * X ^ (j : ℕ)) z =
      g z ^ M + ∑ j, (b j).1 (A z) * g z ^ (j : ℕ) := by
  simp [eval₂_finsetSum, Finset.sum_apply, preLinear]

/- English proof (translation)
Simplify using `[eval₂_finsetSum, Finset.sum_apply, preLinear]`.
-/
theorem eval₂_sum_apply {σ : Type} [Fintype σ] (x : σ → ℂ) {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (g : (σ → ℂ) → ℂ) {M : ℕ} (b : Fin M → analyticAtRing (A x)) (z : σ → ℂ) :
    eval₂ (preLinear x A) g (∑ j, C (b j) * X ^ (j : ℕ)) z = ∑ j, (b j).1 (A z) * g z ^ (j : ℕ) := by
  simp [eval₂_finsetSum, Finset.sum_apply, preLinear]

/- English proof (translation)
Introduce `σ _ X x d A hXan hirr hiso hinj`. Establish `hZ0` using `hZ (Fin d) ⊥ (A x) Ideal.isPrime_bot (IsIntegrallyClosed.of_equiv (RingEquiv.quotientBot (MvPolynomial (Fin d) ℂ)).symm) (fun q hq => by rw [(Ideal.mem_bot).1 hq, map_zero])`. Rewrite `hZ0` using `[Ideal.map_bot]`. Take `⟨hprime, hnormal⟩` from `hZ0`. Establish `: IsDomain (holGerms (A x) ⧸ (⊥ : Ideal (holGerms (A x))))` using `Ideal.Quotient.isDomain _`.

Establish `: IsDomain (holGerms (A x))` using `Function.Injective.isDomain (RingEquiv.quotientBot (holGerms (A x))).symm (RingEquiv.injective _)`. Establish `: IsIntegrallyClosed (holGerms (A x))` using `IsIntegrallyClosed.of_equiv (RingEquiv.quotientBot _)`. Establish `: (𝓝[X] x).NeBot` using `mem_closure_iff_nhdsWithin_neBot.1 (subset_closure hirr.1)`. Establish `germ_zero : ∀ f : (σ → ℂ) → ℂ, (∀ᶠ z in 𝓝 x, z ∈ X → f z = 0) → (f : Germ (𝓝[X] x) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝[X] x) ℂ)` using `fun f h => Germ.coe_eq.2 (eventually_nhdsWithin_iff.2 h)`. Establish `: NoZeroDivisors (germsAlong X x)`.

Use `⟨fun {a b} hab => ?_⟩` and prove the remaining obligations. Take `⟨f, hf, hfa⟩` from `a.2`. Take `⟨g, hg, hgb⟩` from `b.2`. Establish `h0 : ((f * g : (σ → ℂ) → ℂ) : Germ (𝓝[X] x) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝[X] x) ℂ)`. Rewrite using `[Germ.coe_mul, hfa, hgb]`.

Conclude with `congrArg Subtype.val hab`. Break down `hirr.2 f g hf hg ((eventually_of_germ_eq h0).mono fun z hz hzX => by simpa using hz hzX) with h | h` into its components or cases. Use `left`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hfa]`.

Conclude with `germ_zero f h`. Use `right`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hgb]`. Conclude with `germ_zero g h`.

Establish `: IsDomain (germsAlong X x)` using `NoZeroDivisors.to_isDomain _`. Set `_ : Algebra (holGerms (A x)) (germsAlong X x)` to `(alongPull X x A).toAlgebra`. Establish `hα : Function.Injective (algebraMap (holGerms (A x)) (germsAlong X x))`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `φ hφ`.

Take `⟨h, hh, hφh⟩` from `φ.2`. Establish `h1 : ((h ∘ A : (σ → ℂ) → ℂ) : Germ (𝓝[X] x) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝[X] x) ℂ)`. Establish `h2` using `congrArg Subtype.val hφ`. Express the relevant statement in the definitionally equal form `(φ.1 : Germ (𝓝 (A x)) ℂ).compTendsto A (tendsto_nhdsWithin_linear A X x) = (0 : Germ (𝓝[X] x) ℂ) at h2`. Rewrite `h2` using `[← hφh]`.

Conclude with `h2`. Establish `h3` using `hinj h hh ((eventually_of_germ_eq h1).mono fun z hz hzX => hz hzX)`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hφh]`. Conclude with `Germ.coe_eq.2 h3`.

Establish `: Algebra.IsIntegral (holGerms (A x)) (germsAlong X x)`. Use `⟨fun s => ?_⟩` and prove the remaining obligations. Take `⟨g, hg, hgs⟩` from `s.2`. Establish `hs : s = alongOf X x ⟨g, hg⟩` using `Subtype.ext hgs.symm`. Take `⟨M, b, hb, hev⟩` from `hF σ X x d A hXan hiso g hg`.

Set `bt : Fin M → analyticAtRing (A x)` to `fun j => ⟨b j, hb j⟩`. Use `⟨(Polynomial.X ^ M + ∑ j, C (bt j) * Polynomial.X ^ (j : ℕ)).map (germOf (A x)), (monic_X_pow_add (degree_sum_fin_lt _)).map _, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hs]`. Express the relevant statement in the definitionally equal form `((eval₂ (alongPull X x A) (alongOf X x ⟨g, hg⟩) ((Polynomial.X ^ M + ∑ j, C (bt j) * Polynomial.X ^ (j : ℕ)).map (germOf (A x))) : germsAlong X x) : Germ (𝓝[X] x) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝[X] x) ℂ)`.

Rewrite using `[coe_eval₂_map]`. Use `germ_zero _ (hev.mono fun z hz hzX => ?_)` and prove the remaining obligations. Rewrite using `[eval₂_monic_apply]`. Conclude with `hz hzX`. Set `c : ℂ →+* holGerms (A x)` to `(germOf (A x)).comp (constAn (A x))`.

Set `e` to `Fintype.equivFin σ`. Set `coord : σ → analyticAtRing x` to `fun i => ⟨fun w => w i, (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt x⟩`. Take `⟨cc, p, hpm, hpos, hroot, hres0, hq⟩` from `primitive_with_resultant_denominator hG hD hα c (fun j => alongOf X x (coord (e.symm j)))`. Set `ℓ : (σ → ℂ) →L[ℂ] ℂ` to `∑ j, cc j • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) (e.symm j)`. Establish `hℓs : ∑ j, algebraMap (holGerms (A x)) (germsAlong X x) (c (cc j)) * alongOf X x (coord (e.symm j)) = alongOf X x ⟨ℓ, ℓ.analyticAt x⟩`.

Establish `h1 : ∀ j, algebraMap (holGerms (A x)) (germsAlong X x) (c (cc j)) = alongOf X x (constAn x (cc j))` using `fun j => rfl`. Simplify using `only [h1, ← map_mul, ← map_sum]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `w`.

Simplify using `[ℓ, coord, constAn]`. Rewrite `hroot`, `hq` using `[hℓs]`. Use `set N := p.natDegree with hN`. Set `a : Fin N → analyticAtRing (A x)` to `fun j => germRep (A x) (p.coeff j)`. Establish `hPt : (Polynomial.X ^ N + ∑ j, C (a j) * Polynomial.X ^ (j : ℕ)).map (germOf (A x)) = p` using `by conv_rhs => rw [hpm.as_sum]`.

Simplify using `only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, a, germOf_germRep]`. Rewrite using `[← hN, Fin.sum_univ_eq_sum_range (fun i => C (p.coeff i) * Polynomial.X ^ i) N]`. Use `set Pt : (analyticAtRing (A x))[X] := Polynomial.X ^ N + ∑ j, C (a j) * Polynomial.X ^ (j : ℕ) with hPtdef`. Set `res : analyticAtRing (A x)` to `Pt.resultant (derivative Pt) N (N - 1)`. Establish `hγres : germOf (A x) res = p.resultant (derivative p) N (N - 1)`.

Rewrite using `[← resultant_map_map, ← derivative_map, hPt]`. Use `choose f hfdeg hfeq using hq`. Set `q : σ → Fin N → analyticAtRing (A x)` to `fun i j => germRep (A x) ((f (e i)).coeff j)`. Establish `hQt : ∀ i, (∑ j, C (q i j) * Polynomial.X ^ (j : ℕ)).map (germOf (A x)) = f (e i)`. Introduce `i`.

Use `conv_rhs => rw [as_sum_range' (f (e i)) N (hfdeg (e i))]`. Simplify using `only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, q, germOf_germRep]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun k => C ((f (e i)).coeff k) * Polynomial.X ^ k) N]`. Simplify using `only [C_mul_X_pow_eq_monomial]`. Establish `hPtdeg : Pt.natDegree ≤ N`.

Rewrite using `[hPtdef, natDegree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact degree_sum_fin_lt _), natDegree_X_pow]`. Use `⟨ℓ, N, fun j => (a j).1, res.1, fun i j => (q i j).1, fun j => (a j).2, res.2, fun i j => (q i j).2, ?_, ?_, ?_, fun i => ?_⟩` and prove the remaining obligations. Introduce `h`. Apply `hres0` to reduce the goal to its premises. Rewrite using `[← hγres]`.

Conclude with `(germOf_eq_zero _ _).2 h`. Rewrite `hroot` using `[← hPt]`. Establish `h1` using `congrArg Subtype.val hroot`. Express the relevant statement in the definitionally equal form `((eval₂ (alongPull X x A) (alongOf X x ⟨ℓ, ℓ.analyticAt x⟩) (Pt.map (germOf (A x))) : germsAlong X x) : Germ (𝓝[X] x) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝[X] x) ℂ) at h1`. Rewrite `h1` using `[coe_eval₂_map]`.

Use `(eventually_of_germ_eq h1).mono fun z hz hzX => ?_` and prove the remaining obligations. Establish `h2` using `hz hzX`. Rewrite `h2` using `[hPtdef, eval₂_monic_apply]`. Conclude with `h2`. Use `Eventually.of_forall fun y hy => ?_` and prove the remaining obligations.

Take `⟨u, v, -, -, huv⟩` from `exists_mul_add_mul_eq_C_resultant Pt (derivative Pt) hPtdeg ((natDegree_derivative_le Pt).trans (Nat.sub_le_sub_right hPtdeg 1)) (Or.inl hpos.ne')`. Set `ev : analyticAtRing (A x) →+* ℂ` to `(Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y).comp (analyticAtRing (A x)).subtype`. Establish `hmap : Pt.map ev = Polynomial.X ^ N + ∑ j, C ((a j).1 y) * Polynomial.X ^ (j : ℕ)`. Simplify using `[hPtdef, Polynomial.map_sum, ev]`. Establish `h2` using `congrArg (Polynomial.map ev) huv`.

Rewrite `h2` using `[Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, ← derivative_map, hmap]`. Establish `hy' : ev res ≠ 0` using `hy`. Use `⟨C (ev res)⁻¹ * u.map ev, C (ev res)⁻¹ * v.map ev, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `h` using `hfeq (e i)`.

Rewrite `h` using `[← hQt i, ← hγres, e.symm_apply_apply]`. Establish `h1` using `congrArg Subtype.val h`. Express the relevant statement in the definitionally equal form `((eval₂ (alongPull X x A) (alongOf X x ⟨ℓ, ℓ.analyticAt x⟩) ((∑ j, C (q i j) * Polynomial.X ^ (j : ℕ)).map (germOf (A x))) : germsAlong X x) : Germ (𝓝[X] x) ℂ) = ((res.1 ∘ A * fun w => w i : (σ → ℂ) → ℂ) : Germ (𝓝[X] x) ℂ) at h1`. Rewrite `h1` using `[coe_eval₂_map]`. Use `(eventually_of_germ_eq h1).mono fun z hz hzX => ?_` and prove the remaining obligations.

Establish `h2` using `hz hzX`. Rewrite `h2` using `[eval₂_sum_apply]`. Conclude with `h2.symm`.
-/
theorem IrreducibleGermPrimitiveForm.proof (hF : FiniteFibreGermIntegral.Statement)
    (hZ : ZariskiAnalyticNormality.Statement)
    (hG : GroundTheory.Heights₂.Heights.ComplexSets.GenericPrimitive.Statement)
    (hD : GroundTheory.Heights₂.Heights.ComplexSets.DiscrAdjoin.Statement) :
    IrreducibleGermPrimitiveForm.Statement := by
  intro σ _ X x d A hXan hirr hiso hinj

  have hZ0 := hZ (Fin d) ⊥ (A x) Ideal.isPrime_bot
    (IsIntegrallyClosed.of_equiv (RingEquiv.quotientBot (MvPolynomial (Fin d) ℂ)).symm)
    (fun q hq => by rw [(Ideal.mem_bot).1 hq, map_zero])
  rw [Ideal.map_bot] at hZ0
  obtain ⟨hprime, hnormal⟩ := hZ0
  have : IsDomain (holGerms (A x) ⧸ (⊥ : Ideal (holGerms (A x)))) := Ideal.Quotient.isDomain _
  have : IsDomain (holGerms (A x)) :=
    Function.Injective.isDomain (RingEquiv.quotientBot (holGerms (A x))).symm (RingEquiv.injective _)
  have : IsIntegrallyClosed (holGerms (A x)) := IsIntegrallyClosed.of_equiv (RingEquiv.quotientBot _)

  have : (𝓝[X] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (subset_closure hirr.1)
  have germ_zero : ∀ f : (σ → ℂ) → ℂ, (∀ᶠ z in 𝓝 x, z ∈ X → f z = 0) →
      (f : Germ (𝓝[X] x) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝[X] x) ℂ) :=
    fun f h => Germ.coe_eq.2 (eventually_nhdsWithin_iff.2 h)
  have : NoZeroDivisors (germsAlong X x) := by
    refine ⟨fun {a b} hab => ?_⟩
    obtain ⟨f, hf, hfa⟩ := a.2
    obtain ⟨g, hg, hgb⟩ := b.2
    have h0 : ((f * g : (σ → ℂ) → ℂ) : Germ (𝓝[X] x) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝[X] x) ℂ) := by
      rw [Germ.coe_mul, hfa, hgb]
      exact congrArg Subtype.val hab
    rcases hirr.2 f g hf hg ((eventually_of_germ_eq h0).mono fun z hz hzX => by simpa using hz hzX) with h | h
    · left
      apply Subtype.ext
      rw [← hfa]
      exact germ_zero f h
    · right
      apply Subtype.ext
      rw [← hgb]
      exact germ_zero g h
  have : IsDomain (germsAlong X x) := NoZeroDivisors.to_isDomain _

  let _ : Algebra (holGerms (A x)) (germsAlong X x) := (alongPull X x A).toAlgebra
  have hα : Function.Injective (algebraMap (holGerms (A x)) (germsAlong X x)) := by
    rw [injective_iff_map_eq_zero]
    intro φ hφ
    obtain ⟨h, hh, hφh⟩ := φ.2
    have h1 : ((h ∘ A : (σ → ℂ) → ℂ) : Germ (𝓝[X] x) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝[X] x) ℂ) := by
      have h2 := congrArg Subtype.val hφ
      change (φ.1 : Germ (𝓝 (A x)) ℂ).compTendsto A (tendsto_nhdsWithin_linear A X x) =
        (0 : Germ (𝓝[X] x) ℂ) at h2
      rw [← hφh] at h2
      exact h2
    have h3 := hinj h hh ((eventually_of_germ_eq h1).mono fun z hz hzX => hz hzX)
    apply Subtype.ext
    rw [← hφh]
    exact Germ.coe_eq.2 h3
  have : Algebra.IsIntegral (holGerms (A x)) (germsAlong X x) := by
    refine ⟨fun s => ?_⟩
    obtain ⟨g, hg, hgs⟩ := s.2
    have hs : s = alongOf X x ⟨g, hg⟩ := Subtype.ext hgs.symm
    obtain ⟨M, b, hb, hev⟩ := hF σ X x d A hXan hiso g hg
    let bt : Fin M → analyticAtRing (A x) := fun j => ⟨b j, hb j⟩
    refine ⟨(Polynomial.X ^ M + ∑ j, C (bt j) * Polynomial.X ^ (j : ℕ)).map (germOf (A x)),
      (monic_X_pow_add (degree_sum_fin_lt _)).map _, ?_⟩
    apply Subtype.ext
    rw [hs]
    change ((eval₂ (alongPull X x A) (alongOf X x ⟨g, hg⟩)
      ((Polynomial.X ^ M + ∑ j, C (bt j) * Polynomial.X ^ (j : ℕ)).map (germOf (A x))) : germsAlong X x) : Germ (𝓝[X] x) ℂ) =
        ((0 : (σ → ℂ) → ℂ) : Germ (𝓝[X] x) ℂ)
    rw [coe_eval₂_map]
    refine germ_zero _ (hev.mono fun z hz hzX => ?_)
    rw [eval₂_monic_apply]
    exact hz hzX

  let c : ℂ →+* holGerms (A x) := (germOf (A x)).comp (constAn (A x))
  let e := Fintype.equivFin σ
  let coord : σ → analyticAtRing x := fun i =>
    ⟨fun w => w i, (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt x⟩
  obtain ⟨cc, p, hpm, hpos, hroot, hres0, hq⟩ :=
    primitive_with_resultant_denominator hG hD hα c (fun j => alongOf X x (coord (e.symm j)))
  let ℓ : (σ → ℂ) →L[ℂ] ℂ := ∑ j, cc j • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) (e.symm j)
  have hℓs : ∑ j, algebraMap (holGerms (A x)) (germsAlong X x) (c (cc j)) * alongOf X x (coord (e.symm j)) =
      alongOf X x ⟨ℓ, ℓ.analyticAt x⟩ := by
    have h1 : ∀ j, algebraMap (holGerms (A x)) (germsAlong X x) (c (cc j)) = alongOf X x (constAn x (cc j)) :=
      fun j => rfl
    simp only [h1, ← map_mul, ← map_sum]
    congr 1
    apply Subtype.ext
    funext w
    simp [ℓ, coord, constAn]
  rw [hℓs] at hroot hq
  set N := p.natDegree with hN
  let a : Fin N → analyticAtRing (A x) := fun j => germRep (A x) (p.coeff j)
  have hPt : (Polynomial.X ^ N + ∑ j, C (a j) * Polynomial.X ^ (j : ℕ)).map (germOf (A x)) = p := by
    conv_rhs => rw [hpm.as_sum]
    simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
      Polynomial.map_mul, Polynomial.map_C, a, germOf_germRep]
    rw [← hN, Fin.sum_univ_eq_sum_range (fun i => C (p.coeff i) * Polynomial.X ^ i) N]
  set Pt : (analyticAtRing (A x))[X] := Polynomial.X ^ N + ∑ j, C (a j) * Polynomial.X ^ (j : ℕ) with hPtdef
  let res : analyticAtRing (A x) := Pt.resultant (derivative Pt) N (N - 1)
  have hγres : germOf (A x) res = p.resultant (derivative p) N (N - 1) := by
    rw [← resultant_map_map, ← derivative_map, hPt]
  choose f hfdeg hfeq using hq
  let q : σ → Fin N → analyticAtRing (A x) := fun i j => germRep (A x) ((f (e i)).coeff j)
  have hQt : ∀ i, (∑ j, C (q i j) * Polynomial.X ^ (j : ℕ)).map (germOf (A x)) = f (e i) := by
    intro i
    conv_rhs => rw [as_sum_range' (f (e i)) N (hfdeg (e i))]
    simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_X, q, germOf_germRep]
    rw [Fin.sum_univ_eq_sum_range (fun k => C ((f (e i)).coeff k) * Polynomial.X ^ k) N]
    simp only [C_mul_X_pow_eq_monomial]
  have hPtdeg : Pt.natDegree ≤ N := by
    rw [hPtdef, natDegree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact degree_sum_fin_lt _),
      natDegree_X_pow]
  refine ⟨ℓ, N, fun j => (a j).1, res.1, fun i j => (q i j).1, fun j => (a j).2, res.2, fun i j => (q i j).2,
    ?_, ?_, ?_, fun i => ?_⟩
  · intro h
    apply hres0
    rw [← hγres]
    exact (germOf_eq_zero _ _).2 h
  · rw [← hPt] at hroot
    have h1 := congrArg Subtype.val hroot
    change ((eval₂ (alongPull X x A) (alongOf X x ⟨ℓ, ℓ.analyticAt x⟩) (Pt.map (germOf (A x))) :
      germsAlong X x) : Germ (𝓝[X] x) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝[X] x) ℂ) at h1
    rw [coe_eval₂_map] at h1
    refine (eventually_of_germ_eq h1).mono fun z hz hzX => ?_
    have h2 := hz hzX
    rw [hPtdef, eval₂_monic_apply] at h2
    exact h2
  · refine Eventually.of_forall fun y hy => ?_
    obtain ⟨u, v, -, -, huv⟩ := exists_mul_add_mul_eq_C_resultant Pt (derivative Pt) hPtdeg
      ((natDegree_derivative_le Pt).trans (Nat.sub_le_sub_right hPtdeg 1)) (Or.inl hpos.ne')
    let ev : analyticAtRing (A x) →+* ℂ :=
      (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y).comp (analyticAtRing (A x)).subtype
    have hmap : Pt.map ev = Polynomial.X ^ N + ∑ j, C ((a j).1 y) * Polynomial.X ^ (j : ℕ) := by
      simp [hPtdef, Polynomial.map_sum, ev]
    have h2 := congrArg (Polynomial.map ev) huv
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, ← derivative_map,
      hmap] at h2
    have hy' : ev res ≠ 0 := hy
    refine ⟨C (ev res)⁻¹ * u.map ev, C (ev res)⁻¹ * v.map ev, ?_⟩
    calc C (ev res)⁻¹ * u.map ev * (Polynomial.X ^ N + ∑ j, C ((a j).1 y) * Polynomial.X ^ (j : ℕ)) +
          C (ev res)⁻¹ * v.map ev * derivative (Polynomial.X ^ N + ∑ j, C ((a j).1 y) * Polynomial.X ^ (j : ℕ)) =
        C (ev res)⁻¹ * ((Polynomial.X ^ N + ∑ j, C ((a j).1 y) * Polynomial.X ^ (j : ℕ)) * u.map ev +
          derivative (Polynomial.X ^ N + ∑ j, C ((a j).1 y) * Polynomial.X ^ (j : ℕ)) * v.map ev) := by ring
      _ = 1 := by rw [h2, ← C_mul, inv_mul_cancel₀ hy', C_1]
  · have h := hfeq (e i)
    rw [← hQt i, ← hγres, e.symm_apply_apply] at h
    have h1 := congrArg Subtype.val h
    change ((eval₂ (alongPull X x A) (alongOf X x ⟨ℓ, ℓ.analyticAt x⟩)
      ((∑ j, C (q i j) * Polynomial.X ^ (j : ℕ)).map (germOf (A x))) : germsAlong X x) : Germ (𝓝[X] x) ℂ) =
        ((res.1 ∘ A * fun w => w i : (σ → ℂ) → ℂ) : Germ (𝓝[X] x) ℂ) at h1
    rw [coe_eval₂_map] at h1
    refine (eventually_of_germ_eq h1).mono fun z hz hzX => ?_
    have h2 := hz hzX
    rw [eval₂_sum_apply] at h2
    exact h2.symm

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
