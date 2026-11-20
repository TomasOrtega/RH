import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualUnramifiedPlaces
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntSmulEqInteger
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.LatticeIndicator

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Establish `: Module.Finite (𝓞 E) L` using `Module.Finite.iff_fg.2 hL`. Establish `: Module.Finite ℤ L` using `Module.Finite.trans (𝓞 E) L`. Take `⟨k, s, hs⟩` from `Module.Finite.exists_fin (R := ℤ) (M := L)`. Use `⟨k, fun j => s j, fun j => (s j).2, fun w hw => ?_⟩` and prove the remaining obligations. Establish `: (⟨w, hw⟩ : L) ∈ Submodule.span ℤ (Set.range s)` using `hs ▸ Submodule.mem_top`.

Take `⟨m, hm⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).1 this`. Conclude with `⟨m, by simpa using (congrArg Subtype.val hm).symm⟩`.
-/
theorem exists_int_generators (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    ∃ (k : ℕ) (x : Fin k → Fin n → E), (∀ j, x j ∈ L) ∧
      ∀ w ∈ L, ∃ m : Fin k → ℤ, w = ∑ j, m j • x j := by
  have : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL
  have : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := L)
  refine ⟨k, fun j => s j, fun j => (s j).2, fun w hw => ?_⟩
  have : (⟨w, hw⟩ : L) ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 this
  exact ⟨m, by simpa using (congrArg Subtype.val hm).symm⟩

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.IntSmulIntegerEq.exists_int_smul_mem`. Consider the case `exact _root_.GlobalTheory.IntSmulIntegerEq.exists_int_smul_mem`. Consider the case `(apply _root_.GlobalTheory.IntSmulIntegerEq.exists_int_smul_mem <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.IntSmulIntegerEq.exists_int_smul_mem <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.IntSmulIntegerEq.exists_int_smul_mem <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.IntSmulIntegerEq.exists_int_smul_mem ..)`.
-/
theorem exists_int_smul_mem (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (w : Fin n → E) : ∃ N : ℤ, N ≠ 0 ∧ N • w ∈ L := by
  first
  | exact @_root_.GlobalTheory.IntSmulIntegerEq.exists_int_smul_mem
  | exact _root_.GlobalTheory.IntSmulIntegerEq.exists_int_smul_mem
  | (apply _root_.GlobalTheory.IntSmulIntegerEq.exists_int_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntSmulIntegerEq.exists_int_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntSmulIntegerEq.exists_int_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntSmulIntegerEq.exists_int_smul_mem ..)

/- English proof (translation)
Use `haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _`. Use `haveI : CharZero (Fv F v) := charZero_of_injective_ringHom (algebraMap F (Fv F v)).injective`. Take `⟨k, x, hxL, hx⟩` from `exists_int_generators L hL.fg`. Set `f : (Fin k → Fv F v) →ₗ[Fv F v] (Fin n → Fv F v ⊗[F] E)` to `Fintype.linearCombination _ fun j i => (1 : Fv F v) ⊗ₜ[F] x j i`.

Establish `hfa : ∀ a i, f a i = ∑ j, a j ⊗ₜ[F] x j i` using `fun a i => by`. Simplify using `[f, Fintype.linearCombination_apply, TensorProduct.smul_tmul']`. Establish `hm : ∀ (a : Fv F v) (m : Fin k → ℤ), f (fun j => m j • a) = fun i => a ⊗ₜ[F] (∑ j, m j • x j) i` using `fun a m => by`. Use function extensionality and compare the values at `i`. Rewrite using `[hfa]`.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, TensorProduct.tmul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => TensorProduct.smul_tmul _ _ _`. Establish `hf : Function.Surjective f`. Establish `h1 : ∀ (a : Fv F v) (w : Fin n → E), (fun i => a ⊗ₜ[F] w i) ∈ LinearMap.range f`. Introduce `a w`.

Take `⟨N, hN, h⟩` from `exists_int_smul_mem L hL w`. Take `⟨m, e⟩` from `hx _ h`. Use `⟨fun j => m j • ((N : Fv F v)⁻¹ * a), ?_⟩` and prove the remaining obligations. Rewrite using `[hm, ← e]`. Use function extensionality and compare the values at `i`.

Rewrite using `[Pi.smul_apply, ← TensorProduct.smul_tmul, zsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (Int.cast_ne_zero.2 hN), one_mul]`. Introduce `y`. Rewrite using `[← LinearMap.mem_range, ← Finset.univ_sum_single y]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Generalize the expression as in `y i = z`.

Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add p q hp hq => rw [Pi.single_add]`. Conclude with `add_mem hp hq`. Consider the case `tmul a e`.

Use `h1 a (Pi.single i e) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h]`. Establish `hfo : IsOpenMap f` using `IsModuleTopology.isOpenMap_of_surjective (φ := f) hf`. Establish `hfc : Continuous f` using `IsModuleTopology.continuous_of_linearMap f`. Establish `himg : (GlobalTheory.AdelicU.latLoc F L v : Set (Fin n → Fv F v ⊗[F] E)) = f '' Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v))`. Use extensionality with `y`.

Prove the components needed by the constructor for the conclusion. Use `GlobalTheory.AdelicU.latLoc_induction (p := fun y => y ∈ f '' Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) ?_ ⟨0, fun _ _ => zero_mem _, map_zero _⟩ ?_ ?_` and prove the remaining obligations. Introduce `a ha w hw`. Take `⟨m, rfl⟩` from `hx w hw`. Conclude with `⟨fun j => m j • a, fun j _ => zsmul_mem ha _, hm a m⟩`.

Introduce and unpack `_ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩`. Conclude with `⟨a + b, fun j _ => add_mem (s := v.adicCompletionIntegers F) (ha j trivial) (hb j trivial), map_add _ _ _⟩`. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Conclude with `⟨-a, fun j _ => neg_mem (s := v.adicCompletionIntegers F) (ha j trivial), map_neg _ _⟩`. Introduce and unpack `⟨a, ha, rfl⟩`.

Establish `: f a = ∑ j, fun i => a j ⊗ₜ[F] x j i` using `funext fun i => by rw [hfa, Finset.sum_apply]`. Rewrite using `[this]`. Conclude with `sum_mem (S := GlobalTheory.AdelicU.latLoc F L v) fun j _ => GlobalTheory.AdelicU.tmul_mem_latLoc (ha j trivial) (hxL j)`. Establish `hc : IsCompact (v.adicCompletionIntegers F : Set (Fv F v))` using `isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)`. Establish `ho : IsOpen (v.adicCompletionIntegers F : Set (Fv F v))` using `Valued.isOpen_valuationSubring _`.

Rewrite using `[himg]`. Conclude with `⟨(isCompact_univ_pi fun _ => hc).image hfc, hfo _ (isOpen_set_pi Set.finite_univ fun _ _ => ho)⟩`.
-/
theorem latLoc_compact_open (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (GlobalTheory.AdelicU.latLoc F L v : Set (Fin n → Fv F v ⊗[F] E)) ∧
      IsOpen (GlobalTheory.AdelicU.latLoc F L v : Set (Fin n → Fv F v ⊗[F] E)) := by
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  haveI : CharZero (Fv F v) := charZero_of_injective_ringHom (algebraMap F (Fv F v)).injective
  obtain ⟨k, x, hxL, hx⟩ := exists_int_generators L hL.fg
  let f : (Fin k → Fv F v) →ₗ[Fv F v] (Fin n → Fv F v ⊗[F] E) :=
    Fintype.linearCombination _ fun j i => (1 : Fv F v) ⊗ₜ[F] x j i
  have hfa : ∀ a i, f a i = ∑ j, a j ⊗ₜ[F] x j i := fun a i => by
    simp [f, Fintype.linearCombination_apply, TensorProduct.smul_tmul']
  have hm : ∀ (a : Fv F v) (m : Fin k → ℤ),
      f (fun j => m j • a) = fun i => a ⊗ₜ[F] (∑ j, m j • x j) i := fun a m => by
    funext i
    rw [hfa]
    simp only [Finset.sum_apply, Pi.smul_apply, TensorProduct.tmul_sum]
    exact Finset.sum_congr rfl fun j _ => TensorProduct.smul_tmul _ _ _
  have hf : Function.Surjective f := by
    have h1 : ∀ (a : Fv F v) (w : Fin n → E), (fun i => a ⊗ₜ[F] w i) ∈ LinearMap.range f := by
      intro a w
      obtain ⟨N, hN, h⟩ := exists_int_smul_mem L hL w
      obtain ⟨m, e⟩ := hx _ h
      refine ⟨fun j => m j • ((N : Fv F v)⁻¹ * a), ?_⟩
      rw [hm, ← e]
      funext i
      rw [Pi.smul_apply, ← TensorProduct.smul_tmul, zsmul_eq_mul, ← mul_assoc,
        mul_inv_cancel₀ (Int.cast_ne_zero.2 hN), one_mul]
    intro y
    rw [← LinearMap.mem_range, ← Finset.univ_sum_single y]
    refine sum_mem fun i _ => ?_
    generalize y i = z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add p q hp hq => rw [Pi.single_add]; exact add_mem hp hq
    | tmul a e =>
      convert h1 a (Pi.single i e) using 1
      funext j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
  have hfo : IsOpenMap f := IsModuleTopology.isOpenMap_of_surjective (φ := f) hf
  have hfc : Continuous f := IsModuleTopology.continuous_of_linearMap f
  have himg : (GlobalTheory.AdelicU.latLoc F L v : Set (Fin n → Fv F v ⊗[F] E)) =
      f '' Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext y
    constructor
    · refine GlobalTheory.AdelicU.latLoc_induction (p := fun y => y ∈ f '' Set.pi Set.univ fun _ =>
        (v.adicCompletionIntegers F : Set (Fv F v))) ?_ ⟨0, fun _ _ => zero_mem _, map_zero _⟩ ?_ ?_
      · intro a ha w hw
        obtain ⟨m, rfl⟩ := hx w hw
        exact ⟨fun j => m j • a, fun j _ => zsmul_mem ha _, hm a m⟩
      · rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, fun j _ => add_mem (s := v.adicCompletionIntegers F) (ha j trivial) (hb j trivial),
          map_add _ _ _⟩
      · rintro _ ⟨a, ha, rfl⟩
        exact ⟨-a, fun j _ => neg_mem (s := v.adicCompletionIntegers F) (ha j trivial), map_neg _ _⟩
    · rintro ⟨a, ha, rfl⟩
      have : f a = ∑ j, fun i => a j ⊗ₜ[F] x j i := funext fun i => by rw [hfa, Finset.sum_apply]
      rw [this]
      exact sum_mem (S := GlobalTheory.AdelicU.latLoc F L v) fun j _ =>
        GlobalTheory.AdelicU.tmul_mem_latLoc (ha j trivial) (hxL j)
  have hc : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
    isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
  have ho : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  rw [himg]
  exact ⟨(isCompact_univ_pi fun _ => hc).image hfc,
    hfo _ (isOpen_set_pi Set.finite_univ fun _ _ => ho)⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ n L hL v`. Use `haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _`. Take `⟨hc, ho⟩` from `latLoc_compact_open L hL v`. Establish `hcl : IsClosed (GlobalTheory.AdelicU.latLoc F L v : Set (Fin n → Fv F v ⊗[F] E))` using `(GlobalTheory.AdelicU.latLoc F L v).toAddSubgroup.isClosed_of_isOpen ho`.

Establish `e : {X : Fin 1 → Fin n → Fv F v ⊗[F] E | X 0 ∈ GlobalTheory.AdelicU.latLoc F L v} = Set.pi Set.univ fun _ : Fin 1 => (GlobalTheory.AdelicU.latLoc F L v : Set (Fin n → Fv F v ⊗[F] E))`. Use extensionality with `X`. Simplify using `[Fin.forall_fin_one]`. Rewrite using `[e]`. Establish `h1` using `isCompact_univ_pi fun _ : Fin 1 => hc`.

Establish `h2` using `isOpen_set_pi Set.finite_univ fun (_ : Fin 1) _ => ho`. Establish `h3` using `isClosed_set_pi (i := Set.univ) fun (_ : Fin 1) _ => hcl`. Use `⟨(IsLocallyConstant.iff_exists_open _).2 fun X => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hX : X ∈ Set.pi Set.univ fun _ : Fin 1 => (GlobalTheory.AdelicU.latLoc F L v : Set (Fin n → Fv F v ⊗[F] E))`. Conclude with `⟨_, h2, hX, fun Y hY => by rw [Set.indicator_of_mem hY, Set.indicator_of_mem hX]; rfl⟩`.

Conclude with `⟨_, h3.isOpen_compl, hX, fun Y hY => by`. Rewrite using `[Set.indicator_of_notMem hY, Set.indicator_of_notMem hX]⟩`. Conclude with `HasCompactSupport.intro' h1 h3 fun X hX => Set.indicator_of_notMem hX _`.
-/
theorem isSB_indicator_latLoc : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → ∀ v : HeightOneSpectrum (𝓞 F), IsSB ({X : Fin 1 → Fin n → Fv F v ⊗[F] E | X 0 ∈ GlobalTheory.AdelicU.latLoc F L v}.indicator (1 : (Fin 1 → Fin n → Fv F v ⊗[F] E) → ℂ)) := by
  intro F E _ _ _ _ _ n L hL v
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  obtain ⟨hc, ho⟩ := latLoc_compact_open L hL v
  have hcl : IsClosed (GlobalTheory.AdelicU.latLoc F L v : Set (Fin n → Fv F v ⊗[F] E)) :=
    (GlobalTheory.AdelicU.latLoc F L v).toAddSubgroup.isClosed_of_isOpen ho
  have e : {X : Fin 1 → Fin n → Fv F v ⊗[F] E | X 0 ∈ GlobalTheory.AdelicU.latLoc F L v} =
      Set.pi Set.univ fun _ : Fin 1 => (GlobalTheory.AdelicU.latLoc F L v : Set (Fin n → Fv F v ⊗[F] E)) := by
    ext X
    simp [Fin.forall_fin_one]
  rw [e]
  have h1 := isCompact_univ_pi fun _ : Fin 1 => hc
  have h2 := isOpen_set_pi Set.finite_univ fun (_ : Fin 1) _ => ho
  have h3 := isClosed_set_pi (i := Set.univ) fun (_ : Fin 1) _ => hcl
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun X => ?_, ?_⟩
  · by_cases hX : X ∈ Set.pi Set.univ fun _ : Fin 1 =>
        (GlobalTheory.AdelicU.latLoc F L v : Set (Fin n → Fv F v ⊗[F] E))
    · exact ⟨_, h2, hX, fun Y hY => by rw [Set.indicator_of_mem hY, Set.indicator_of_mem hX]; rfl⟩
    · exact ⟨_, h3.isOpen_compl, hX, fun Y hY => by
        rw [Set.indicator_of_notMem hY, Set.indicator_of_notMem hX]⟩
  · exact HasCompactSupport.intro' h1 h3 fun X hX => Set.indicator_of_notMem hX _

end GlobalTheory.LatticeIndicator
