import Mathlib
import Formalism.LocalRingCardinality.DataLevel
import Formalism.LocalRingCardinality.DataLevelD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHeckeOpFullDualLab
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactLevelOffFinEmpty
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexMulMeasure
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct
open MeasureTheory

namespace GlobalTheory.StabConjIndex

/- English proof (translation)
Use `set K' := K.map (MulAut.conj g).toMonoidHom with hK'`. Set `μ : Measure H` to `Measure.haar`. Use `haveI : μ.IsMulRightInvariant := ⟨fun g => by`. Rewrite using `[GlobalTheory.AdelicUnimod.map_mul_right_eq, hmod, one_smul]⟩`. Establish `e : (K' : Set H) = (fun x => g⁻¹ * x) ⁻¹' ((fun x => x * g) ⁻¹' (K : Set H))`.

Use extensionality with `x`. Simplify using `only [hK', SetLike.mem_coe, Set.mem_preimage, Subgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, rfl⟩`. Simplify `hk` using `[mul_assoc]`.

Introduce `h`. Conclude with `⟨_, h, by simp [mul_assoc]⟩`. Establish `ho' : IsOpen (K' : Set H)`. Rewrite using `[e]`. Conclude with `(ho.preimage (continuous_mul_const g)).preimage (continuous_const_mul g⁻¹)`.

Establish `hc' : IsCompact (K' : Set H)`. Rewrite using `[hK', Subgroup.coe_map]`. Conclude with `hc.image (f := fun x => g * x * g⁻¹) (by fun_prop)`. Establish `hμ : μ K' = μ K` using `by rw [e, measure_preimage_mul, measure_preimage_mul_right]`. Establish `hoi : IsOpen ((K ⊓ K' : Subgroup H) : Set H)` using `ho.inter ho'`.

Establish `key : ∀ L : Subgroup H, IsCompact (L : Set H) → K ⊓ K' ≤ L → ((K ⊓ K').relIndex L : ENNReal) * μ (K ⊓ K' : Subgroup H) = μ L` using `fun L hL hle => by haveI : CompactSpace L := isCompact_iff_compactSpace.1 hL haveI : Finite (L ⧸ (K ⊓ K').subgroupOf L) := Subgroup.quotient_finite_of_isOpen _ (hoi.preimage continuous_subtype_val) haveI : ((K ⊓ K').subgroupOf L).FiniteIndex := Subgroup.finiteIndex_of_finite_quot …`. Conclude with `GlobalTheory.BaseModule.relIndex_mul_measure' _ _ hle hoi.measurableSet μ`. Establish `h1` using `key K hc inf_le_left`. Establish `h2` using `key K' hc' inf_le_right`. Rewrite `h1` using `[Subgroup.inf_relIndex_left]`.

Rewrite `h2` using `[Subgroup.inf_relIndex_right, hμ, ← h1]`. Establish `h0 : μ (K ⊓ K' : Subgroup H) ≠ 0` using `(hoi.measure_pos μ ⟨1, one_mem _⟩).ne'`. Establish `ht : μ (K ⊓ K' : Subgroup H) ≠ ⊤` using `((measure_mono (show ((K ⊓ K' : Subgroup H) : Set H) ⊆ K from inf_le_left (a := K))).trans_lt hc.measure_lt_top).ne`. Conclude with `((ENNReal.mul_left_inj h0 ht).1 h2).symm` after adjusting the coercions.
-/
theorem relIndex_conj_comm {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (hmod : ∀ h : H, Measure.modularCharacter h = 1) (K : Subgroup H) (ho : IsOpen (K : Set H))
    (hc : IsCompact (K : Set H)) (g : H) :
    (K.map (MulAut.conj g).toMonoidHom).relIndex K = K.relIndex (K.map (MulAut.conj g).toMonoidHom) := by
  set K' := K.map (MulAut.conj g).toMonoidHom with hK'
  let μ : Measure H := Measure.haar
  haveI : μ.IsMulRightInvariant := ⟨fun g => by
    rw [GlobalTheory.AdelicUnimod.map_mul_right_eq, hmod, one_smul]⟩
  have e : (K' : Set H) = (fun x => g⁻¹ * x) ⁻¹' ((fun x => x * g) ⁻¹' (K : Set H)) := by
    ext x
    simp only [hK', SetLike.mem_coe, Set.mem_preimage, Subgroup.mem_map]
    constructor
    · rintro ⟨k, hk, rfl⟩
      simpa [mul_assoc] using hk
    · intro h
      exact ⟨_, h, by simp [mul_assoc]⟩
  have ho' : IsOpen (K' : Set H) := by
    rw [e]
    exact (ho.preimage (continuous_mul_const g)).preimage (continuous_const_mul g⁻¹)
  have hc' : IsCompact (K' : Set H) := by
    rw [hK', Subgroup.coe_map]
    exact hc.image (f := fun x => g * x * g⁻¹) (by fun_prop)
  have hμ : μ K' = μ K := by rw [e, measure_preimage_mul, measure_preimage_mul_right]
  have hoi : IsOpen ((K ⊓ K' : Subgroup H) : Set H) := ho.inter ho'
  have key : ∀ L : Subgroup H, IsCompact (L : Set H) → K ⊓ K' ≤ L →
      ((K ⊓ K').relIndex L : ENNReal) * μ (K ⊓ K' : Subgroup H) = μ L := fun L hL hle => by
    haveI : CompactSpace L := isCompact_iff_compactSpace.1 hL
    haveI : Finite (L ⧸ (K ⊓ K').subgroupOf L) :=
      Subgroup.quotient_finite_of_isOpen _ (hoi.preimage continuous_subtype_val)
    haveI : ((K ⊓ K').subgroupOf L).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    exact GlobalTheory.BaseModule.relIndex_mul_measure' _ _ hle hoi.measurableSet μ
  have h1 := key K hc inf_le_left
  have h2 := key K' hc' inf_le_right
  rw [Subgroup.inf_relIndex_left] at h1
  rw [Subgroup.inf_relIndex_right, hμ, ← h1] at h2
  have h0 : μ (K ⊓ K' : Subgroup H) ≠ 0 := (hoi.measure_pos μ ⟨1, one_mem _⟩).ne'
  have ht : μ (K ⊓ K' : Subgroup H) ≠ ⊤ :=
    ((measure_mono (show ((K ⊓ K' : Subgroup H) : Set H) ⊆ K from inf_le_left (a := K))).trans_lt
      hc.measure_lt_top).ne
  exact_mod_cast ((ENNReal.mul_left_inj h0 ht).1 h2).symm

section Transport

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))

noncomputable def swap : (v.adicCompletion F ⊗[F] E) ≃+* (E ⊗[F] v.adicCompletion F) :=
  (Algebra.TensorProduct.comm F _ _).toRingEquiv

omit [NumberField E] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem swap_tmul (a : v.adicCompletion F) (x : E) : swap v (a ⊗ₜ[F] x) = x ⊗ₜ[F] a := rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use `GlobalTheory.AdelicU.intLoc_induction (p := fun y => swap v y ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) (fun a ha x => ?_) (by simp) (fun y z hy hz => by rw [map_add]; exact add_mem hy hz) (fun y hy => by rw [map_neg]; exact neg_mem …` and prove the remaining obligations. Establish `: swap v (a ⊗ₜ[F] (x : E)) = ((x : E) ⊗ₜ[F] (1 : v.adicCompletion F)) * ((1 : E) ⊗ₜ[F] a)`. Rewrite using `[swap_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Rewrite using `[this]`.

Conclude with `mul_mem (Subring.subset_closure (Or.inl ⟨⟨x, x, rfl⟩, rfl⟩)) (Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩))`. Introduce `h`. Establish `: tensInt (F` using `F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring ≤ (GlobalTheory.AdelicU.intLoc F E v).comap (swap (E := E) v).symm.toRingHom := by`. Use `Subring.closure_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ (⟨⟨_, x, rfl⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩)`.

Conclude with `GlobalTheory.AdelicU.tmul_mem_intLoc (one_mem _) x`. Conclude with `GlobalTheory.AdelicU.tmul_mem_intLoc ha 1`. Simplify using `using this h`.
-/
theorem swap_mem_int (y : v.adicCompletion F ⊗[F] E) : y ∈ GlobalTheory.AdelicU.intLoc F E v ↔
    swap v y ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring := by
  constructor
  · refine GlobalTheory.AdelicU.intLoc_induction (p := fun y => swap v y ∈
      tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) (fun a ha x => ?_)
      (by simp) (fun y z hy hz => by rw [map_add]; exact add_mem hy hz)
      (fun y hy => by rw [map_neg]; exact neg_mem hy)
    have : swap v (a ⊗ₜ[F] (x : E)) = ((x : E) ⊗ₜ[F] (1 : v.adicCompletion F)) * ((1 : E) ⊗ₜ[F] a) := by
      rw [swap_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [this]
    exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨x, x, rfl⟩, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩))
  · intro h
    have : tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring ≤
        (GlobalTheory.AdelicU.intLoc F E v).comap (swap (E := E) v).symm.toRingHom := by
      refine Subring.closure_le.2 ?_
      rintro _ (⟨⟨_, x, rfl⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩)
      · exact GlobalTheory.AdelicU.tmul_mem_intLoc (one_mem _) x
      · exact GlobalTheory.AdelicU.tmul_mem_intLoc ha 1
    simpa using this h

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use `GlobalTheory.AdelicU.latLoc_induction (p := fun y => (fun i => swap v (y i)) ∈ latS (F := F) (v.adicCompletion F) (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) N) (fun a ha x hx => ?_) ?_ (fun y z hy hz => ?_) (fun y hy => ?_)` and prove the remaining obligations. Establish `h` using `Submodule.smul_mem (latS (F := F) (v.adicCompletion F) (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) N) ⟨(1 : E) ⊗ₜ[F] a, Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)⟩ (Submodule.subset_span ⟨x, hx, rfl⟩)`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`.

Express the relevant statement in the definitionally equal form `x i ⊗ₜ[F] a = ((1 : E) ⊗ₜ[F] a) * (x i ⊗ₜ[F] (1 : v.adicCompletion F))`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Use `Submodule.zero_mem _ using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Conclude with `map_zero _`.

Use `add_mem hy hz using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Conclude with `map_add _ _ _`. Use `neg_mem hy using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`.

Conclude with `map_neg _ _`. Introduce `h`. Establish `: ∀ z ∈ latS (F` using `F) (v.adicCompletion F) (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) N, (fun i => (swap v).symm (z i)) ∈ GlobalTheory.AdelicU.latLoc F N v := fun z hz => by`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`.

Take `⟨x, hx, rfl⟩` from `hz`. Conclude with `GlobalTheory.AdelicU.tmul_mem_latLoc (one_mem _) hx`. Consider the case `zero`. Use `Submodule.zero_mem _ using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`.

Conclude with `map_zero _`. Consider the case `add y z _ _ hy hz`. Use `add_mem hy hz using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Conclude with `map_add _ _ _`.

Consider the case `smul c y _ hy`. Use `(GlobalTheory.AdelicU.latLoc F N v).smul_mem ⟨(swap v).symm c.1, (swap_mem_int v _).2 (by simpa using c.2)⟩ hy` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Conclude with `map_mul (swap v).symm c.1 (y i)`.

Simplify using `using this _ h`.
-/
theorem swap_mem_lat (N : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → v.adicCompletion F ⊗[F] E) :
    y ∈ GlobalTheory.AdelicU.latLoc F N v ↔ (fun i => swap v (y i)) ∈ latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) N := by
  constructor
  · refine GlobalTheory.AdelicU.latLoc_induction (p := fun y => (fun i => swap v (y i)) ∈ latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) N)
      (fun a ha x hx => ?_) ?_ (fun y z hy hz => ?_) (fun y hy => ?_)
    · have h := Submodule.smul_mem (latS (F := F) (v.adicCompletion F)
        (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) N)
        ⟨(1 : E) ⊗ₜ[F] a, Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)⟩ (Submodule.subset_span ⟨x, hx, rfl⟩)
      convert h using 1
      funext i
      change x i ⊗ₜ[F] a = ((1 : E) ⊗ₜ[F] a) * (x i ⊗ₜ[F] (1 : v.adicCompletion F))
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    · convert Submodule.zero_mem _ using 1
      funext i
      exact map_zero _
    · convert add_mem hy hz using 1
      funext i
      exact map_add _ _ _
    · convert neg_mem hy using 1
      funext i
      exact map_neg _ _
  · intro h
    have : ∀ z ∈ latS (F := F) (v.adicCompletion F)
        (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) N,
        (fun i => (swap v).symm (z i)) ∈ GlobalTheory.AdelicU.latLoc F N v := fun z hz => by
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨x, hx, rfl⟩ := hz
        exact GlobalTheory.AdelicU.tmul_mem_latLoc (one_mem _) hx
      | zero =>
        convert Submodule.zero_mem _ using 1
        funext i
        exact map_zero _
      | add y z _ _ hy hz =>
        convert add_mem hy hz using 1
        funext i
        exact map_add _ _ _
      | smul c y _ hy =>
        have := (GlobalTheory.AdelicU.latLoc F N v).smul_mem
          ⟨(swap v).symm c.1, (swap_mem_int v _).2 (by simpa using c.2)⟩ hy
        convert this using 1
        funext i
        exact map_mul (swap v).symm c.1 (y i)
    simpa using this _ h

omit [NumberField E] in
/- English proof (translation)
Establish `hs : ∀ x, sigR σ (v.adicCompletion F) (swap v x) = swap v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ x)` using `fun x => by`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => rfl`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.

Establish `h1 : cT (sigR σ (v.adicCompletion F)) (g.1.map (swap (E` using `E) v).toRingHom) = (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) g.1).map (swap (E := E) v).toRingHom := by`. Use extensionality with `i j`. Conclude with `hs _`. Establish `h2 : J.map (inclE (F` using `F) (v.adicCompletion F)) = (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (v.adicCompletion F) J).map (swap (E := E) v).toRingHom := rfl`. Express the relevant statement in the definitionally equal form `cT (sigR σ (v.adicCompletion F)) (g.1.map (swap (E := E) v).toRingHom) * _ * g.1.map (swap (E := E) v).toRingHom = _ ↔ cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) g.1 * _ * g.1 = _`.

Rewrite using `[h1, h2, ← Matrix.map_mul, ← Matrix.map_mul]`. Conclude with `(Matrix.map_injective (swap v).injective).eq_iff`.
-/
theorem mem_UPts_swap (g : GL (Fin n) (v.adicCompletion F ⊗[F] E)) :
    bc (swap (E := E) v).toRingHom g ∈ UPts σ J (v.adicCompletion F) ↔ g ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (v.adicCompletion F) σ J := by
  have hs : ∀ x, sigR σ (v.adicCompletion F) (swap v x) = swap v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ x) := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have h1 : cT (sigR σ (v.adicCompletion F)) (g.1.map (swap (E := E) v).toRingHom) =
      (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) g.1).map (swap (E := E) v).toRingHom := by
    ext i j
    exact hs _
  have h2 : J.map (inclE (F := F) (v.adicCompletion F)) =
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (v.adicCompletion F) J).map (swap (E := E) v).toRingHom := rfl
  change cT (sigR σ (v.adicCompletion F)) (g.1.map (swap (E := E) v).toRingHom) * _ * g.1.map (swap (E := E) v).toRingHom = _ ↔
    cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) g.1 * _ * g.1 = _
  rw [h1, h2, ← Matrix.map_mul, ← Matrix.map_mul]
  exact (Matrix.map_injective (swap v).injective).eq_iff

noncomputable def toGL : GlobalTheory.AdelicU.GLoc σ J v →* GL (Fin n) (E ⊗[F] v.adicCompletion F) :=
  (bc (swap (E := E) v).toRingHom).comp (GlobalTheory.AdelicU.matHom _ σ J)

omit [NumberField E] in
/- English proof (translation)
Introduce `_ _ h` and use `GlobalTheory.AdelicU.matHom_injective _ σ J (Units.ext (Matrix.map_injective (swap v).injective (congrArg Units.val h)))`.
-/
theorem toGL_injective : Function.Injective (toGL σ J v) := fun _ _ h =>
  GlobalTheory.AdelicU.matHom_injective _ σ J
    (Units.ext (Matrix.map_injective (swap v).injective (congrArg Units.val h)))

omit [NumberField E] in
/- English proof (translation)
Establish `e : bc (swap (E` using `E) v).toRingHom (bc (swap (E := E) v).symm.toRingHom γ) = γ := by`. Use extensionality with `i j`. Conclude with `(swap v).apply_symm_apply _`. Conclude with `⟨⟨bc (swap (E := E) v).symm.toRingHom γ, (mem_UPts_swap σ J v _).1 (e.symm ▸ h)⟩, e⟩`.
-/
theorem exists_toGL {γ : GL (Fin n) (E ⊗[F] v.adicCompletion F)} (h : γ ∈ UPts σ J (v.adicCompletion F)) :
    ∃ g, toGL σ J v g = γ := by
  have e : bc (swap (E := E) v).toRingHom (bc (swap (E := E) v).symm.toRingHom γ) = γ := by
    ext i j
    exact (swap v).apply_symm_apply _
  exact ⟨⟨bc (swap (E := E) v).symm.toRingHom γ, (mem_UPts_swap σ J v _).1 (e.symm ▸ h)⟩, e⟩

/- English proof (translation)
Establish `key : ∀ g, g ∈ GlobalTheory.AdelicU.stabLoc σ J N v ↔ toGL σ J v g ∈ stabGL (latS (F` using `F) (v.adicCompletion F) (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) N) := fun g => by`. Establish `hm : ∀ y : Fin n → v.adicCompletion F ⊗[F] E, (fun i => swap v (((GlobalTheory.AdelicU.matHom _ σ J g).1 *ᵥ y) i)) = (toGL σ J v g).1 *ᵥ fun i => swap v (y i)` using `fun y =>`. Use function extensionality and compare the values at `fun i => RingHom.map_mulVec (swap (E := E) v).toRingHom _ y i`. Rewrite using `[GlobalTheory.AdelicU.mem_stabLoc]`. Simplify using `only [swap_mem_lat, hm]`.

Use `⟨fun h x => ?_, fun h y => h _⟩` and prove the remaining obligations. Simplify using `using h fun i => (swap v).symm (x i)`. Use extensionality with `γ`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg, rfl⟩`.

Conclude with `⟨(mem_UPts_swap σ J v _).2 g.2, (key g).1 hg⟩`. Introduce and unpack `⟨h1, h2⟩`. Take `⟨g, rfl⟩` from `exists_toGL σ J v h1`. Conclude with `⟨g, (key g).2 h2, rfl⟩`.
-/
theorem map_stabLoc (N : Submodule (𝓞 E) (Fin n → E)) :
    (GlobalTheory.AdelicU.stabLoc σ J N v).map (toGL σ J v) = levelVL σ J v N := by
  have key : ∀ g, g ∈ GlobalTheory.AdelicU.stabLoc σ J N v ↔ toGL σ J v g ∈ stabGL (latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) N) := fun g => by
    have hm : ∀ y : Fin n → v.adicCompletion F ⊗[F] E,
        (fun i => swap v (((GlobalTheory.AdelicU.matHom _ σ J g).1 *ᵥ y) i)) =
          (toGL σ J v g).1 *ᵥ fun i => swap v (y i) := fun y =>
      funext fun i => RingHom.map_mulVec (swap (E := E) v).toRingHom _ y i
    rw [GlobalTheory.AdelicU.mem_stabLoc]
    simp only [swap_mem_lat, hm]
    refine ⟨fun h x => ?_, fun h y => h _⟩
    simpa using h fun i => (swap v).symm (x i)
  ext γ
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨(mem_UPts_swap σ J v _).2 g.2, (key g).1 hg⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨g, rfl⟩ := exists_toGL σ J v h1
    exact ⟨g, (key g).2 h2, rfl⟩

end Transport

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ hc n J hJ hd N hN hspan v γ hγ`. Take `⟨δ, hδ, hσδ⟩ : ∃ δ : E, δ ≠ 0 ∧ hc.sig δ = -δ` from `by by_contra! h`. Establish `hs : Function.Surjective (algebraMap F E)` using `fun a => (hc.fixed a).1 (by`. Assume the negation of the conclusion as `hne`. Conclude with `h (star a - a) (sub_ne_zero.2 hne) (by show star _ = _; simp))`.

Use `(LinearEquiv.ofBijective (Algebra.linearMap F E) ⟨(algebraMap F E).injective, hs⟩).finrank_eq` as an intermediate fact. Rewrite `this` using `[hc.deg2, Module.finrank_self]`. Use linear arithmetic over natural numbers and integers. Use `haveI : Submodule.IsLattice E N := ⟨Module.Finite.iff_fg.1 hN, hspan⟩`. Take `⟨g, rfl⟩` from `exists_toGL hc.sig J v hγ`.

Establish `h` using `relIndex_conj_comm (GlobalTheory.HeckeDual.modular_eq_one hc.sig J (fun x => star_star x) hδ hσδ ⟨fun i j => congrFun (congrFun hJ i) j, hd.ne_zero⟩ v) _ (GlobalTheory.AdelicU.isOpen_stabLoc hc.sig J N v) (GlobalTheory.AdelicU.isCompact_stabLoc hc.sig J N v) g`. Establish `e : ((GlobalTheory.AdelicU.stabLoc hc.sig J N v).map (toGL hc.sig J v)).map (MulAut.conj (toGL hc.sig J v g)).toMonoidHom = ((GlobalTheory.AdelicU.stabLoc hc.sig J N v).map (MulAut.conj g).toMonoidHom).map (toGL hc.sig J v)`. Rewrite using `[Subgroup.map_map, Subgroup.map_map]`. Use `congr 1`. Use `ext1 x`.

Simplify using the standard rewrite rules. Rewrite using `[← map_stabLoc, e, Subgroup.relIndex_map_map_of_injective _ _ (toGL_injective _ _ _), Subgroup.relIndex_map_map_of_injective _ _ (toGL_injective _ _ _), h]`.
-/
theorem relIndex_conj_levelVL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (hc.sig : E →+* E) J → IsUnit J.det → ∀ (N : Submodule (𝓞 E) (Fin n → E)), Module.Finite (𝓞 E) N → Submodule.span E (N : Set (Fin n → E)) = ⊤ → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ γ ∈ UPts hc.sig J (v.adicCompletion F), ((levelVL hc.sig J v N).map (MulAut.conj γ).toMonoidHom).relIndex (levelVL hc.sig J v N) = (levelVL hc.sig J v N).relIndex ((levelVL hc.sig J v N).map (MulAut.conj γ).toMonoidHom) := by
  intro F E _ _ _ _ _ _ hc n J hJ hd N hN hspan v γ hγ
  obtain ⟨δ, hδ, hσδ⟩ : ∃ δ : E, δ ≠ 0 ∧ hc.sig δ = -δ := by
    by_contra! h
    have hs : Function.Surjective (algebraMap F E) := fun a => (hc.fixed a).1 (by
      by_contra hne
      exact h (star a - a) (sub_ne_zero.2 hne) (by show star _ = _; simp))
    have := (LinearEquiv.ofBijective (Algebra.linearMap F E) ⟨(algebraMap F E).injective, hs⟩).finrank_eq
    rw [hc.deg2, Module.finrank_self] at this
    omega
  haveI : Submodule.IsLattice E N := ⟨Module.Finite.iff_fg.1 hN, hspan⟩
  obtain ⟨g, rfl⟩ := exists_toGL hc.sig J v hγ
  have h := relIndex_conj_comm (GlobalTheory.HeckeDual.modular_eq_one hc.sig J (fun x => star_star x) hδ hσδ
    ⟨fun i j => congrFun (congrFun hJ i) j, hd.ne_zero⟩ v) _ (GlobalTheory.AdelicU.isOpen_stabLoc hc.sig J N v)
    (GlobalTheory.AdelicU.isCompact_stabLoc hc.sig J N v) g
  have e : ((GlobalTheory.AdelicU.stabLoc hc.sig J N v).map (toGL hc.sig J v)).map
      (MulAut.conj (toGL hc.sig J v g)).toMonoidHom =
      ((GlobalTheory.AdelicU.stabLoc hc.sig J N v).map (MulAut.conj g).toMonoidHom).map (toGL hc.sig J v) := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext1 x
    simp
  rw [← map_stabLoc, e, Subgroup.relIndex_map_map_of_injective _ _ (toGL_injective _ _ _),
    Subgroup.relIndex_map_map_of_injective _ _ (toGL_injective _ _ _), h]

end GlobalTheory.StabConjIndex
