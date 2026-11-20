import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwaStmt

noncomputable section

namespace PI.IwaMeasEx.Wau

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Topology

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Rewrite using `[algebraMap_adicCompletion]`. Simplify using `[valuedAdicCompletion_eq_valuation']`.
-/
theorem val_algebraMap_F (v : HeightOneSpectrum (𝓞 F)) (t : F) :
    Valued.v (algebraMap F (v.adicCompletion F) t) = v.valuation F t := by
  rw [algebraMap_adicCompletion]
  simp [valuedAdicCompletion_eq_valuation']

/- English proof (translation)
Establish `hnhds : {y : v.adicCompletion F | Valued.v (y - x) < 1} ∈ 𝓝 x`. Rewrite using `[Valued.mem_nhds]`. Conclude with `⟨1, fun y hy => by simpa [Valuation.restrict_lt_one_iff] using hy⟩`. Take `⟨_, hy, ⟨k, rfl⟩⟩` from `mem_closure_iff_nhds.mp ((denseRange_algebraMap (K := F) (v := v)) x) _ hnhds`. Simplify using `only [Set.mem_ofPred_eq] at hy`.

Establish `hk : v.valuation F k ≤ 1`. Rewrite using `[← val_algebraMap_F]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨a, ha⟩` from `exists_valuation_sub_lt_of_integer v hk 1`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Establish `h2 : Valued.v (algebraMap F (v.adicCompletion F) k - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < 1`. Rewrite using `[← map_sub, val_algebraMap_F, ← Valuation.map_neg, neg_sub]`. Simplify using `using ha`. Combine the equalities or inequalities in the displayed calculation. Use `max_lt ?_ h2` and prove the remaining obligations.

Rewrite using `[← Valuation.map_neg, neg_sub]`. Conclude with `hy`.
-/
theorem exists_int_near (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F)
    (hx : Valued.v x ≤ 1) :
    ∃ a : 𝓞 F, Valued.v (x - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < 1 := by
  have hnhds : {y : v.adicCompletion F | Valued.v (y - x) < 1} ∈ 𝓝 x := by
    rw [Valued.mem_nhds]
    exact ⟨1, fun y hy => by simpa [Valuation.restrict_lt_one_iff] using hy⟩
  obtain ⟨_, hy, ⟨k, rfl⟩⟩ :=
    mem_closure_iff_nhds.mp ((denseRange_algebraMap (K := F) (v := v)) x) _ hnhds
  simp only [Set.mem_ofPred_eq] at hy
  have hk : v.valuation F k ≤ 1 := by
    rw [← val_algebraMap_F]
    calc Valued.v (algebraMap F (v.adicCompletion F) k)
        = Valued.v ((algebraMap F (v.adicCompletion F) k - x) + x) := by rw [sub_add_cancel]
      _ ≤ max (Valued.v (algebraMap F (v.adicCompletion F) k - x)) (Valued.v x) :=
          Valuation.map_add _ _ _
      _ ≤ 1 := max_le hy.le hx
  obtain ⟨a, ha⟩ := exists_valuation_sub_lt_of_integer v hk 1
  refine ⟨a, ?_⟩
  have h2 : Valued.v (algebraMap F (v.adicCompletion F) k -
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < 1 := by
    rw [← map_sub, val_algebraMap_F, ← Valuation.map_neg, neg_sub]
    simpa using ha
  calc Valued.v (x - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a))
      = Valued.v ((x - algebraMap F (v.adicCompletion F) k) + (algebraMap F (v.adicCompletion F) k -
          algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a))) := by ring_nf
    _ ≤ max _ _ := Valuation.map_add _ _ _
    _ < 1 := by
      refine max_lt ?_ h2
      rw [← Valuation.map_neg, neg_sub]; exact hy

def toOv (v : HeightOneSpectrum (𝓞 F)) : 𝓞 F →+* Valued.integer (v.adicCompletion F) :=
  ((algebraMap F (v.adicCompletion F)).comp (algebraMap (𝓞 F) F)).codRestrict _ (fun a => by
    show Valued.v (_ : v.adicCompletion F) ≤ 1
    simp only [RingHom.comp_apply]
    rw [val_algebraMap_F, valuation_of_algebraMap]
    exact intValuation_le_one v a)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toOv_coe (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) :
    ((toOv v a : Valued.integer (v.adicCompletion F)) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) := rfl

/- English proof (translation)
The claim follows from `(Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) _)).isUnit_iff_valuation_eq_one`.
-/
theorem isUnit_integer_iff (v : HeightOneSpectrum (𝓞 F)) (x : Valued.integer (v.adicCompletion F)) :
    IsUnit x ↔ Valued.v (x : v.adicCompletion F) = 1 :=
  (Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) _)).isUnit_iff_valuation_eq_one

/- English proof (translation)
Establish `hfin : Finite (𝓞 F ⧸ v.asIdeal)` using `Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot`. Set `φ : 𝓞 F →+* IsLocalRing.ResidueField (Valued.integer (v.adicCompletion F))` to `(IsLocalRing.residue _).comp (toOv v)`. Establish `hker : ∀ a ∈ v.asIdeal, φ a = 0`. Introduce `a ha`. Simplify using `only [φ, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_integer_iff, toOv_coe, val_algebraMap_F, valuation_of_algebraMap]`.

Conclude with `((intValuation_lt_one_iff_mem v a).mpr ha).ne`. Set `ψ` to `Ideal.Quotient.lift v.asIdeal φ hker`. Use `Finite.of_surjective ψ ?_` and prove the remaining obligations. Introduce `z`. Take `⟨x, rfl⟩` from `IsLocalRing.residue_surjective z`.

Take `⟨a, ha⟩` from `exists_int_near v (x : v.adicCompletion F) x.2`. Use `⟨Ideal.Quotient.mk _ a, ?_⟩` and prove the remaining obligations. Simplify using `only [ψ, Ideal.Quotient.lift_mk, φ, RingHom.comp_apply]`. Rewrite using `[eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_integer_iff]`. Move the coercions through the operations in `[toOv_coe]`.

Conclude with `ha.ne`.
-/
theorem finite_residue (v : HeightOneSpectrum (𝓞 F)) :
    Finite (IsLocalRing.ResidueField (Valued.integer (v.adicCompletion F))) := by
  have hfin : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  let φ : 𝓞 F →+* IsLocalRing.ResidueField (Valued.integer (v.adicCompletion F)) :=
    (IsLocalRing.residue _).comp (toOv v)
  have hker : ∀ a ∈ v.asIdeal, φ a = 0 := by
    intro a ha
    simp only [φ, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, isUnit_integer_iff, toOv_coe, val_algebraMap_F, valuation_of_algebraMap]
    exact ((intValuation_lt_one_iff_mem v a).mpr ha).ne
  let ψ := Ideal.Quotient.lift v.asIdeal φ hker
  refine Finite.of_surjective ψ ?_
  intro z
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨a, ha⟩ := exists_int_near v (x : v.adicCompletion F) x.2
  refine ⟨Ideal.Quotient.mk _ a, ?_⟩
  simp only [ψ, Ideal.Quotient.lift_mk, φ, RingHom.comp_apply]
  rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, isUnit_integer_iff]
  push_cast [toOv_coe]
  exact ha.ne

/- English proof (translation)
Rewrite using `[Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField]`. Use `⟨?_, ?_, finite_residue v⟩` and prove the remaining obligations. Conclude with `(Valued.isClosed_integer (R := v.adicCompletion F)).completeSpace_coe`. Conclude with `inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F))`.
-/
theorem compactSpace_integer (v : HeightOneSpectrum (𝓞 F)) :
    CompactSpace (Valued.integer (v.adicCompletion F)) := by
  rw [Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField]
  refine ⟨?_, ?_, finite_residue v⟩
  · exact (Valued.isClosed_integer (R := v.adicCompletion F)).completeSpace_coe
  · exact inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F))

/- English proof (translation)
Use `compactSpace_integer v` as an intermediate fact. Conclude with `isCompact_iff_compactSpace.mpr this`.
-/
theorem isCompact_Ov (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  have := compactSpace_integer v
  exact isCompact_iff_compactSpace.mpr this

instance compactSpace_Ov (v : HeightOneSpectrum (𝓞 F)) : CompactSpace (v.adicCompletionIntegers F) :=
  isCompact_iff_compactSpace.mp (isCompact_Ov v)

def Ohat (F : Type) [Field F] [NumberField F] : Set (FiniteAdeleRing (𝓞 F) F) :=
  {a | ∀ v, a v ∈ v.adicCompletionIntegers F}

/- English proof (translation)
The claim follows from `RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (fun _ ↦ Valued.isOpen_valuationSubring _)`.
-/
theorem isOpen_Ohat : IsOpen (Ohat F) :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun _ ↦ Valued.isOpen_valuationSubring _)

instance compactSpace_Ov' (v : HeightOneSpectrum (𝓞 F)) :
    CompactSpace ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
  isCompact_iff_compactSpace.mp (isCompact_Ov v)

/- English proof (translation)
Establish `hc : Continuous (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite)` using `RestrictedProduct.isEmbedding_structureMap.continuous`. Establish `: Ohat F = Set.range (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite)`. Use extensionality with `a`. Prove the components needed by the constructor for the conclusion. Introduce `ha`.

Conclude with `⟨fun v => ⟨a v, ha v⟩, rfl⟩`. Introduce and unpack `⟨x, rfl⟩ v`. Conclude with `(x v).2`. Rewrite using `[this]`. Conclude with `isCompact_range hc`.
-/
theorem isCompact_Ohat : IsCompact (Ohat F) := by
  have hc : Continuous (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite) :=
    RestrictedProduct.isEmbedding_structureMap.continuous
  have : Ohat F = Set.range (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite) := by
    ext a
    constructor
    · intro ha
      exact ⟨fun v => ⟨a v, ha v⟩, rfl⟩
    · rintro ⟨x, rfl⟩ v
      exact (x v).2
  rw [this]
  exact isCompact_range hc

instance t2Space_finiteAdeleRing_alt : T2Space (FiniteAdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))

end PI.IwaMeasEx.Wau

end

noncomputable section

namespace PI.IwaMeasEx.Wau

open scoped TensorProduct

variable {F E B : Type} [Field F] [Field E] [Algebra F E] [CommRing B] [Algebra F B]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)

def coord : E ⊗[F] B →ₗ[F] (ι → B) :=
  TensorProduct.lift (LinearMap.mk₂ F (fun (e : E) (a : B) => fun k => b.repr e k • a)
    (fun e₁ e₂ a => by funext k; simp [add_smul])
    (fun c e a => by funext k; simp [smul_smul])
    (fun e a₁ a₂ => by funext k; simp [smul_add])
    (fun c e a => by funext k; simp [smul_comm c]))

/- English proof (translation)
Simplify using `[coord]`.
-/
theorem coord_tmul (e : E) (a : B) : coord b (e ⊗ₜ[F] a) = fun k => b.repr e k • a := by
  simp [coord]

def emb (c : ι → B) : E ⊗[F] B := ∑ i, b i ⊗ₜ[F] c i

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `only [emb, map_sum, coord_tmul, Finset.sum_apply, Module.Basis.repr_self]`. Simplify using `[Finsupp.single_apply]`.
-/
theorem coord_emb (c : ι → B) : coord b (emb b c) = c := by
  funext k
  simp only [emb, map_sum, coord_tmul, Finset.sum_apply, Module.Basis.repr_self]
  simp [Finsupp.single_apply]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp [emb]`. Consider the case `tmul e a`. Simplify using `only [emb, coord_tmul]`. Use `conv_rhs => rw [← b.sum_repr e]`.

Rewrite using `[TensorProduct.sum_tmul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[TensorProduct.smul_tmul]`. Consider the case `add x y hx hy`. Establish `: emb b (coord b (x + y)) = emb b (coord b x) + emb b (coord b y)`.

Simplify using `[emb, map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]`. Rewrite using `[this, hx, hy]`.
-/
theorem emb_coord (x : E ⊗[F] B) : emb b (coord b x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp [emb]
  | tmul e a =>
    simp only [emb, coord_tmul]
    conv_rhs => rw [← b.sum_repr e]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.smul_tmul]
  | add x y hx hy =>
    have : emb b (coord b (x + y)) = emb b (coord b x) + emb b (coord b y) := by
      simp [emb, map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
    rw [this, hx, hy]

/- English proof (translation)
The claim follows from `Function.LeftInverse.injective (emb_coord b)`.
-/
theorem coord_injective : Function.Injective (coord b : E ⊗[F] B → ι → B) :=
  Function.LeftInverse.injective (emb_coord b)

/- English proof (translation)
Use `conv_lhs => rw [← emb_coord b x, ← emb_coord b y]`. Simplify using `only [emb, Finset.sum_mul_sum, Algebra.TensorProduct.tmul_mul_tmul, map_sum, coord_tmul]`. Use function extensionality and compare the values at `k`. Simplify using `[Finset.sum_apply]`.
-/
theorem coord_mul (x y : E ⊗[F] B) :
    coord b (x * y) = fun k => ∑ i, ∑ j, b.repr (b i * b j) k • (coord b x i * coord b y j) := by
  conv_lhs => rw [← emb_coord b x, ← emb_coord b y]
  simp only [emb, Finset.sum_mul_sum, Algebra.TensorProduct.tmul_mul_tmul, map_sum, coord_tmul]
  funext k
  simp [Finset.sum_apply]

/- English proof (translation)
The claim follows from `map_smul _ _ _`.
-/
theorem coord_smul (c : F) (x : E ⊗[F] B) : coord b (c • x) = c • coord b x := map_smul _ _ _

/- English proof (translation)
Use `conv_lhs => rw [← emb_coord b x]`. Simplify using `only [emb, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_sum, coord_tmul]`. Use function extensionality and compare the values at `k`. Simplify using `[Finset.sum_apply, Module.Basis.repr_self, Finsupp.single_apply]`.
-/
theorem coord_tmul_one_mul (a : B) (x : E ⊗[F] B) :
    coord b ((1 ⊗ₜ[F] a) * x) = fun k => a * coord b x k := by
  conv_lhs => rw [← emb_coord b x]
  simp only [emb, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_sum, coord_tmul]
  funext k
  simp [Finset.sum_apply, Module.Basis.repr_self, Finsupp.single_apply]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `[Algebra.TensorProduct.includeLeftRingHom_apply, coord_tmul, Algebra.algebraMap_eq_smul_one]`.
-/
theorem coord_incl (e : E) :
    coord b (Algebra.TensorProduct.includeLeftRingHom (R := F) (B := B) e) = fun k => algebraMap F B (b.repr e k) := by
  funext k
  simp [Algebra.TensorProduct.includeLeftRingHom_apply, coord_tmul, Algebra.algebraMap_eq_smul_one]

/- English proof (translation)
Use `conv_lhs => rw [← emb_coord b x]`. Simplify using `only [emb, map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, coord_tmul]`. Use function extensionality and compare the values at `k`. Simplify using `[Finset.sum_apply]`.
-/
theorem coord_map (σ : E →ₐ[F] E) (x : E ⊗[F] B) :
    coord b (Algebra.TensorProduct.map σ (AlgHom.id F B) x) =
      fun k => ∑ i, b.repr (σ (b i)) k • coord b x i := by
  conv_lhs => rw [← emb_coord b x]
  simp only [emb, map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, coord_tmul]
  funext k
  simp [Finset.sum_apply]

section Topology

variable [TopologicalSpace B] [IsTopologicalRing B]

/- English proof (translation)
Repeatedly rewrite using `[Algebra.smul_def]`. Conclude with `continuous_const.mul hh`.
-/
theorem cont_smul {X : Type*} [TopologicalSpace X] (c : F) {h : X → B} (hh : Continuous h) :
    Continuous (fun x => c • h x) := by
  simp_rw [Algebra.smul_def]
  exact continuous_const.mul hh

def CtsA {X : Type*} [TopologicalSpace X] (f : X → E ⊗[F] B) : Prop :=
  Continuous (fun x => coord b (f x))

variable {b}
variable {X : Type*} [TopologicalSpace X]

/- English proof (translation)
The claim follows from `continuous_const`.
-/
theorem ctsA_const (y : E ⊗[F] B) : CtsA b (fun _ : X => y) := continuous_const

/- English proof (translation)
Simplify `hg` using `[CtsA, coord_emb]`.
-/
theorem ctsA_emb {g : X → ι → B} (hg : Continuous g) : CtsA b (fun x => emb b (g x)) := by
  simpa [CtsA, coord_emb] using hg

/- English proof (translation)
Unfold `CtsA at *`. Simplify using `only [map_add]`. Conclude with `hf.add hg`.
-/
theorem ctsA_add {f g : X → E ⊗[F] B} (hf : CtsA b f) (hg : CtsA b g) : CtsA b (fun x => f x + g x) := by
  unfold CtsA at *
  simp only [map_add]
  exact hf.add hg

/- English proof (translation)
Unfold `CtsA at *`. Simplify using `only [map_sub]`. Conclude with `hf.sub hg`.
-/
theorem ctsA_sub {f g : X → E ⊗[F] B} (hf : CtsA b f) (hg : CtsA b g) : CtsA b (fun x => f x - g x) := by
  unfold CtsA at *
  simp only [map_sub]
  exact hf.sub hg

/- English proof (translation)
Unfold `CtsA`. Simplify using `only [map_sum]`. Conclude with `continuous_finset_sum _ hf`.
-/
theorem ctsA_sum {κ : Type*} (s : Finset κ) {f : κ → X → E ⊗[F] B} (hf : ∀ i ∈ s, CtsA b (f i)) :
    CtsA b (fun x => ∑ i ∈ s, f i x) := by
  unfold CtsA
  simp only [map_sum]
  exact continuous_finset_sum _ hf

/- English proof (translation)
Unfold `CtsA`. Simplify using `only [coord_mul]`. Use `continuous_pi fun k => continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_` and prove the remaining obligations. Conclude with `cont_smul _ (((continuous_apply i).comp hf).mul ((continuous_apply j).comp hg))`.
-/
theorem ctsA_mul {f g : X → E ⊗[F] B} (hf : CtsA b f) (hg : CtsA b g) : CtsA b (fun x => f x * g x) := by
  unfold CtsA
  simp only [coord_mul]
  refine continuous_pi fun k => continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact cont_smul _ (((continuous_apply i).comp hf).mul ((continuous_apply j).comp hg))

/- English proof (translation)
Unfold `CtsA`. Simplify using `only [coord_map]`. Conclude with `continuous_pi fun k => continuous_finset_sum _ fun i _ => cont_smul _ ((continuous_apply i).comp hf)`.
-/
theorem ctsA_map (σ : E →ₐ[F] E) {f : X → E ⊗[F] B} (hf : CtsA b f) :
    CtsA b (fun x => Algebra.TensorProduct.map σ (AlgHom.id F B) (f x)) := by
  unfold CtsA
  simp only [coord_map]
  exact continuous_pi fun k => continuous_finset_sum _ fun i _ => cont_smul _ ((continuous_apply i).comp hf)

end Topology

end PI.IwaMeasEx.Wau

end

noncomputable section

namespace PI.IwaMeasEx.Wau

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped TensorProduct

/- English proof (translation)
Take `⟨a, s, hs, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 K) x`. Establish `hs0 : s ≠ 0` using `nonZeroDivisors.ne_zero hs`. Establish `hN0 : Ideal.absNorm (Ideal.span {s}) ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`. Conclude with `hs0`.

Take `⟨t, ht⟩` from `Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {s}))`. Use `⟨Ideal.absNorm (Ideal.span {s}), Nat.pos_of_ne_zero hN0, t * a, ?_⟩` and prove the remaining obligations. Establish `hsK : algebraMap (𝓞 K) K s ≠ 0`. Rewrite using `[Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)]` and apply the resulting hypothesis. Establish `: ((Ideal.absNorm (Ideal.span {s}) : ℕ) : K) = algebraMap (𝓞 K) K t * algebraMap (𝓞 K) K s`.

Rewrite using `[← map_mul, ht, map_natCast]`. Rewrite using `[this, map_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_den {K : Type} [Field K] [NumberField K] (x : K) :
    ∃ m : ℕ, 0 < m ∧ ∃ a : 𝓞 K, (m : K) * x = algebraMap (𝓞 K) K a := by
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hN0 : Ideal.absNorm (Ideal.span {s}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hs0
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {s}))
  refine ⟨Ideal.absNorm (Ideal.span {s}), Nat.pos_of_ne_zero hN0, t * a, ?_⟩
  have hsK : algebraMap (𝓞 K) K s ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)]
  have : ((Ideal.absNorm (Ideal.span {s}) : ℕ) : K) = algebraMap (𝓞 K) K t * algebraMap (𝓞 K) K s := by
    rw [← map_mul, ht, map_natCast]
  rw [this, map_mul]
  field_simp

variable {F : Type} [Field F] [NumberField F]

def IntF (f : F) : Prop := algebraMap F (FiniteAdeleRing (𝓞 F) F) f ∈ Ohat F

/- English proof (translation)
Introduce `v` and use `by show a v * c v ∈ _ exact mul_mem (ha v) (hc v)`.
-/
theorem ohat_mul {a c : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Ohat F) (hc : c ∈ Ohat F) : a * c ∈ Ohat F :=
  fun v => by
    show a v * c v ∈ _
    exact mul_mem (ha v) (hc v)

/- English proof (translation)
Introduce `v` and use `by show a v + c v ∈ _ exact add_mem (ha v) (hc v)`.
-/
theorem ohat_add {a c : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Ohat F) (hc : c ∈ Ohat F) : a + c ∈ Ohat F :=
  fun v => by
    show a v + c v ∈ _
    exact add_mem (ha v) (hc v)

/- English proof (translation)
Introduce `v` and use `by show -(a v) ∈ _ exact neg_mem (ha v)`.
-/
theorem ohat_neg {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Ohat F) : -a ∈ Ohat F :=
  fun v => by
    show -(a v) ∈ _
    exact neg_mem (ha v)

/- English proof (translation)
Introduce `v` and use `by show (0 : v.adicCompletion F) ∈ _ exact zero_mem _`.
-/
theorem ohat_zero : (0 : FiniteAdeleRing (𝓞 F) F) ∈ Ohat F :=
  fun v => by
    show (0 : v.adicCompletion F) ∈ _
    exact zero_mem _

/- English proof (translation)
Introduce `v` and use `by show (1 : v.adicCompletion F) ∈ _ exact one_mem _`.
-/
theorem ohat_one : (1 : FiniteAdeleRing (𝓞 F) F) ∈ Ohat F :=
  fun v => by
    show (1 : v.adicCompletion F) ∈ _
    exact one_mem _

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using ohat_zero`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.sum_insert hi]`. Conclude with `ohat_add (hf i (Finset.mem_insert_self i s)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))`.
-/
theorem ohat_sum {κ : Type*} (s : Finset κ) {f : κ → FiniteAdeleRing (𝓞 F) F} (hf : ∀ i ∈ s, f i ∈ Ohat F) :
    ∑ i ∈ s, f i ∈ Ohat F := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ohat_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact ohat_add (hf i (Finset.mem_insert_self i s)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using ohat_zero`. Consider the case `succ m ih => rw [succ_nsmul]`. Conclude with `ohat_add ih ha`.
-/
theorem ohat_nsmul {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Ohat F) (m : ℕ) : m • a ∈ Ohat F := by
  induction m with
  | zero => simpa using ohat_zero
  | succ m ih => rw [succ_nsmul]; exact ohat_add ih ha

/- English proof (translation)
Break down `Int.eq_nat_or_neg m with ⟨k, rfl | rfl⟩` into its components or cases. Simplify using `using ohat_nsmul ha k`. Rewrite using `[neg_smul]; exact ohat_neg (by simpa using ohat_nsmul ha k)`.
-/
theorem ohat_zsmul {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Ohat F) (m : ℤ) : m • a ∈ Ohat F := by
  rcases Int.eq_nat_or_neg m with ⟨k, rfl | rfl⟩
  · simpa using ohat_nsmul ha k
  · rw [neg_smul]; exact ohat_neg (by simpa using ohat_nsmul ha k)

/- English proof (translation)
Introduce `v` and use `by show ((algebraMap (𝓞 F) F a : F) : v.adicCompletion F) ∈ _ exact coe_algebraMap_mem (𝓞 F) F v a`.
-/
theorem intF_of_int (a : 𝓞 F) : IntF (algebraMap (𝓞 F) F a) := fun v => by
  show ((algebraMap (𝓞 F) F a : F) : v.adicCompletion F) ∈ _
  exact coe_algebraMap_mem (𝓞 F) F v a

/- English proof (translation)
Use `choose m hm a ha using fun i => exists_den (f i)`. Use `⟨∏ i, m i, Finset.prod_pos fun i _ => hm i, fun i => ?_⟩` and prove the remaining obligations. Take `⟨q, hq⟩ : m i ∣ ∏ j, m j` from `Finset.dvd_prod_of_mem m (Finset.mem_univ i)`. Establish `: ((∏ j, m j : ℕ) : F) * f i = algebraMap (𝓞 F) F ((q : 𝓞 F) * a i)`. Rewrite using `[hq, map_mul, ← ha i]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `intF_of_int _`.
-/
theorem exists_den_fin {κ : Type} [Fintype κ] (f : κ → F) :
    ∃ m : ℕ, 0 < m ∧ ∀ i, IntF ((m : F) * f i) := by
  classical
  choose m hm a ha using fun i => exists_den (f i)
  refine ⟨∏ i, m i, Finset.prod_pos fun i _ => hm i, fun i => ?_⟩
  obtain ⟨q, hq⟩ : m i ∣ ∏ j, m j := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  have : ((∏ j, m j : ℕ) : F) * f i = algebraMap (𝓞 F) F ((q : 𝓞 F) * a i) := by
    rw [hq, map_mul, ← ha i]; push_cast; ring
  rw [this]; exact intF_of_int _

section Coord

variable {E : Type} [Field E] [NumberField E] [Algebra F E]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)

local notation "Af" => FiniteAdeleRing (𝓞 F) F

def IntC (x : E ⊗[F] Af) : Prop := ∀ k, coord b x k ∈ Ohat F

variable {b}

/- English proof (translation)
Introduce `k` and use `by rw [map_add]; exact ohat_add (hx k) (hy k)`.
-/
theorem intC_add {x y : E ⊗[F] Af} (hx : IntC b x) (hy : IntC b y) : IntC b (x + y) := fun k => by
  rw [map_add]; exact ohat_add (hx k) (hy k)

/- English proof (translation)
Introduce `k` and use `by rw [map_nsmul]; exact ohat_nsmul (hx k) m`.
-/
theorem intC_nsmul {x : E ⊗[F] Af} (hx : IntC b x) (m : ℕ) : IntC b (m • x) := fun k => by
  rw [map_nsmul]; exact ohat_nsmul (hx k) m

/- English proof (translation)
Introduce `k` and use `by rw [map_sum, Finset.sum_apply] exact ohat_sum s fun i hi => hf i hi k`.
-/
theorem intC_sum {κ : Type*} (s : Finset κ) {f : κ → E ⊗[F] Af} (hf : ∀ i ∈ s, IntC b (f i)) :
    IntC b (∑ i ∈ s, f i) := fun k => by
  rw [map_sum, Finset.sum_apply]
  exact ohat_sum s fun i hi => hf i hi k

/- English proof (translation)
The claim follows from `Algebra.smul_def c a`.
-/
theorem smul_eq_algebraMap_mul (c : F) (a : Af) : c • a = algebraMap F Af c * a := Algebra.smul_def c a

/- English proof (translation)
Take `⟨m, hm, h⟩` from `exists_den_fin (fun p : ι × ι × ι => b.repr (b p.1 * b p.2.1) p.2.2)`. Use `⟨m, hm, fun x y hx hy k => ?_⟩` and prove the remaining obligations. Rewrite using `[map_nsmul, coord_mul]`. Simplify using `only [Pi.smul_apply, Finset.smul_sum]`. Use `ohat_sum _ fun i _ => ohat_sum _ fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_eq_algebraMap_mul, nsmul_eq_mul, ← mul_assoc]`. Establish `h1 : (m : Af) * algebraMap F Af (b.repr (b i * b j) k) = algebraMap F Af ((m : F) * b.repr (b i * b j) k)`. Simplify using the standard rewrite rules. Rewrite using `[h1]`. Conclude with `ohat_mul (h (i, j, k)) (ohat_mul (hx i) (hy j))`.
-/
theorem exists_den_mul (b : Module.Basis ι F E) :
    ∃ m : ℕ, 0 < m ∧ ∀ x y : E ⊗[F] Af, IntC b x → IntC b y → IntC b (m • (x * y)) := by
  obtain ⟨m, hm, h⟩ := exists_den_fin (fun p : ι × ι × ι => b.repr (b p.1 * b p.2.1) p.2.2)
  refine ⟨m, hm, fun x y hx hy k => ?_⟩
  rw [map_nsmul, coord_mul]
  simp only [Pi.smul_apply, Finset.smul_sum]
  refine ohat_sum _ fun i _ => ohat_sum _ fun j _ => ?_
  rw [smul_eq_algebraMap_mul, nsmul_eq_mul, ← mul_assoc]
  have h1 : (m : Af) * algebraMap F Af (b.repr (b i * b j) k) = algebraMap F Af ((m : F) * b.repr (b i * b j) k) := by
    simp
  rw [h1]
  exact ohat_mul (h (i, j, k)) (ohat_mul (hx i) (hy j))

/- English proof (translation)
Introduce `k` and use `by rw [coord_incl]; exact he k`.
-/
theorem intC_incl {e : E} (he : ∀ k, IntF (b.repr e k)) :
    IntC b (Algebra.TensorProduct.includeLeftRingHom (R := F) (B := Af) e) := fun k => by
  rw [coord_incl]; exact he k

end Coord

end PI.IwaMeasEx.Wau

end
