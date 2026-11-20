import Formalism.LocalToGlobal.GlobalTheory.BlockActions.LatSOfMem
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG

namespace Formalism.L2.GlobalTheoryTheory.Br

section Proof

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

omit [Field E] [NumberField E] [Algebra F E] in
/- English proof (translation)
Take `⟨M, hM⟩` from `Ideal.exists_maximal (𝓞 F)`. Set `v : HeightOneSpectrum (𝓞 F)` to `⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField F)⟩`. Use `⟨⟨0, 1, fun h => ?_⟩⟩` and prove the remaining obligations. Establish `h'` using `congrArg (evalV F v) h`. Rewrite `h'` using `[map_zero, map_one]`.

Conclude with `zero_ne_one h'`.
-/
theorem finiteAdeleRing_nontrivial : Nontrivial (FiniteAdeleRing (𝓞 F) F) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  let v : HeightOneSpectrum (𝓞 F) :=
    ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField F)⟩
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have h' := congrArg (evalV F v) h
  rw [map_zero, map_one] at h'
  exact zero_ne_one h'

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_mono h)`.
-/
theorem latS_mono_fin {Λ Λ' : Submodule (𝓞 E) (Fin n → E)} (h : Λ ≤ Λ') :
    latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ ≤ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ' :=
  Submodule.span_mono (Set.image_mono h)

/- English proof (translation)
Use `set c : Fin n → E := fun i => f (Pi.single i 1)`. Establish `hfc : ∀ y : Fin n → E, f y = ∑ i, c i * y i`. Introduce `y`. Establish `hy : y = ∑ i, y i • (Pi.single i 1 : Fin n → E)`. Use extensionality with `j`.

Simplify using `[Finset.sum_apply, Pi.single_apply]`. Use `conv_lhs => rw [hy]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul, mul_comm]`.

Establish `key : ∀ u ∈ latS (F` using `F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ, ∑ i, ι (c i) * u i = 0 := by`. Introduce `u hu`. Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem u hu`. Take `⟨y, hy, rfl⟩` from `hu`.

Simplify using `only [← map_mul, ← map_sum]`. Rewrite using `[← hfc, hf y hy, map_zero]`. Consider the case `zero => simp`. Consider the case `add u w _ _ hu hw`. Simplify using `only [Pi.add_apply, mul_add, Finset.sum_add_distrib]`.

Rewrite using `[hu, hw, add_zero]`. Consider the case `smul a u _ hu`. Establish `h : ∑ i, ι (c i) * (a • u) i = (a : 𝒜) * ∑ i, ι (c i) * u i`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Pi.smul_apply]`. Use `show _ * ((a : 𝒜) * u i) = _`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h, hu, mul_zero]`. Establish `h1` using `key _ hx`.

Simplify using `only [← map_mul, ← map_sum] at h1`. Rewrite `h1` using `[← hfc]`. Conclude with `inclE_injective_fin h1`. Use `where inclE_injective_fin {a : E} (h : ι a = 0) : a = 0 :=`. Use `finiteAdeleRing_nontrivial (F := F)` as an intermediate fact.

Use the proof step `Formalism.UG.P.inclE_injective F E (FiniteAdeleRing (𝓞 F) F) (by rw [h, map_zero])`.
-/
theorem latS_functional (Λ : Submodule (𝓞 E) (Fin n → E)) (f : Module.Dual E (Fin n → E))
    (hf : ∀ y ∈ Λ, f y = 0) (x : Fin n → E)
    (hx : (fun i => ι (x i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ) : f x = 0 := by
  set c : Fin n → E := fun i => f (Pi.single i 1)
  have hfc : ∀ y : Fin n → E, f y = ∑ i, c i * y i := by
    intro y
    have hy : y = ∑ i, y i • (Pi.single i 1 : Fin n → E) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hy]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  have key : ∀ u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ, ∑ i, ι (c i) * u i = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨y, hy, rfl⟩ := hu
      simp only [← map_mul, ← map_sum]
      rw [← hfc, hf y hy, map_zero]
    | zero => simp
    | add u w _ _ hu hw =>
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      rw [hu, hw, add_zero]
    | smul a u _ hu =>
      have h : ∑ i, ι (c i) * (a • u) i = (a : 𝒜) * ∑ i, ι (c i) * u i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Pi.smul_apply]
        show _ * ((a : 𝒜) * u i) = _
        ring
      rw [h, hu, mul_zero]
  have h1 := key _ hx
  simp only [← map_mul, ← map_sum] at h1
  rw [← hfc] at h1
  exact inclE_injective_fin h1
where
  inclE_injective_fin {a : E} (h : ι a = 0) : a = 0 :=
    have := finiteAdeleRing_nontrivial (F := F)
    Formalism.UG.P.inclE_injective F E (FiniteAdeleRing (𝓞 F) F) (by rw [h, map_zero])

/- English proof (translation)
Assume the negation of the conclusion as `hxV`. Take `⟨f, hfx, hf⟩` from `Submodule.exists_dual_map_eq_bot_of_notMem hxV inferInstance`. Use `hfx (latS_functional (F := F) Λ f (fun y hy => ?_) x hx)` and prove the remaining obligations. Establish `h2 : f y ∈ (Submodule.span E (Λ : Set (Fin n → E))).map f` using `Submodule.mem_map_of_mem (Submodule.subset_span hy)`. Rewrite `h2` using `[hf]`.

Conclude with `(Submodule.mem_bot E).1 h2`.
-/
theorem latS_mem_span (Λ : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E)
    (hx : (fun i => ι (x i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ) :
    x ∈ Submodule.span E (Λ : Set (Fin n → E)) := by
  by_contra hxV
  obtain ⟨f, hfx, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hxV inferInstance
  refine hfx (latS_functional (F := F) Λ f (fun y hy => ?_) x hx)
  have h2 : f y ∈ (Submodule.span E (Λ : Set (Fin n → E))).map f :=
    Submodule.mem_map_of_mem (Submodule.subset_span hy)
  rw [hf] at h2
  exact (Submodule.mem_bot E).1 h2

/- English proof (translation)
Establish `hxV` using `latS_mem_span (F := F) Λ x hx`. Take `⟨C, hC⟩` from `Submodule.exists_isCompl (Submodule.span E (Λ : Set (Fin n → E)))`. Set `b` to `Module.finBasis E C`. Set `W : Submodule (𝓞 E) (Fin n → E)` to `Submodule.span (𝓞 E) (Set.range fun i => (b i : Fin n → E))`. Set `Λ' : Submodule (𝓞 E) (Fin n → E)` to `Λ ⊔ W`.

Establish `hfin' : Module.Finite (𝓞 E) Λ'` using `Module.Finite.iff_fg.mpr ((Module.Finite.iff_fg.mp hfin).sup (Submodule.fg_span (Set.finite_range _)))`. Establish `hV' : Submodule.span E (Λ : Set (Fin n → E)) ≤ Submodule.span E (Λ' : Set (Fin n → E))` using `Submodule.span_mono (fun y hy => Submodule.mem_sup_left hy)`. Establish `hC' : C ≤ Submodule.span E (Λ' : Set (Fin n → E))`. Introduce `c hc`. Establish `h` using `congrArg Subtype.val (b.sum_repr ⟨c, hc⟩)`.

Simplify using `only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h`. Rewrite using `[← h]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)` and prove the remaining obligations. Conclude with `Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)`. Establish `hspan' : Submodule.span E (Λ' : Set (Fin n → E)) = ⊤`.

Rewrite using `[eq_top_iff, ← hC.sup_eq_top]`. Conclude with `sup_le hV' hC'`. Establish `hx' : x ∈ Λ'`. Establish `h` using `Formalism.UG.P.csGlob_one (F := F) Formalism.UG.P.csGlob_intAdApprox Λ' hfin' hspan'`. Rewrite using `[← h]`.

Use `show ((1⁻¹ : GL (Fin n) 𝒜) : Matrix (Fin n) (Fin n) 𝒜) *ᵥ (fun i => ι (x i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ'`. Rewrite using `[inv_one, Units.val_one, one_mulVec]`. Conclude with `latS_mono_fin le_sup_left hx`. Take `⟨y, hy, w, hw, rfl⟩` from `Submodule.mem_sup.1 hx'`. Establish `hwC : w ∈ C` using `(Submodule.span_le (p := C.restrictScalars (𝓞 E))).2 (by rintro _ ⟨i, rfl⟩; exact (b i).2) hw`.

Establish `hwV : w ∈ Submodule.span E (Λ : Set (Fin n → E))`. Establish `e : w = (y + w) - y` using `by abel`. Rewrite using `[e]`. Conclude with `sub_mem hxV (Submodule.subset_span hy)`. Establish `hw0 : w = 0` using `Submodule.disjoint_def.1 hC.disjoint w hwV hwC`.

Rewrite using `[hw0, add_zero]`. Conclude with `hy`.
-/
theorem latLocGlob_main (Λ : Submodule (𝓞 E) (Fin n → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (x : Fin n → E)
    (hx : (fun i => ι (x i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ) : x ∈ Λ := by
  have hxV := latS_mem_span (F := F) Λ x hx
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (Submodule.span E (Λ : Set (Fin n → E)))
  let b := Module.finBasis E C
  let W : Submodule (𝓞 E) (Fin n → E) :=
    Submodule.span (𝓞 E) (Set.range fun i => (b i : Fin n → E))
  let Λ' : Submodule (𝓞 E) (Fin n → E) := Λ ⊔ W
  have hfin' : Module.Finite (𝓞 E) Λ' :=
    Module.Finite.iff_fg.mpr ((Module.Finite.iff_fg.mp hfin).sup (Submodule.fg_span (Set.finite_range _)))
  have hV' : Submodule.span E (Λ : Set (Fin n → E)) ≤ Submodule.span E (Λ' : Set (Fin n → E)) :=
    Submodule.span_mono (fun y hy => Submodule.mem_sup_left hy)
  have hC' : C ≤ Submodule.span E (Λ' : Set (Fin n → E)) := by
    intro c hc
    have h := congrArg Subtype.val (b.sum_repr ⟨c, hc⟩)
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h
    rw [← h]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)
  have hspan' : Submodule.span E (Λ' : Set (Fin n → E)) = ⊤ := by
    rw [eq_top_iff, ← hC.sup_eq_top]
    exact sup_le hV' hC'
  have hx' : x ∈ Λ' := by
    have h := Formalism.UG.P.csGlob_one (F := F) Formalism.UG.P.csGlob_intAdApprox Λ' hfin' hspan'
    rw [← h]
    show ((1⁻¹ : GL (Fin n) 𝒜) : Matrix (Fin n) (Fin n) 𝒜) *ᵥ (fun i => ι (x i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ'
    rw [inv_one, Units.val_one, one_mulVec]
    exact latS_mono_fin le_sup_left hx
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hx'
  have hwC : w ∈ C :=
    (Submodule.span_le (p := C.restrictScalars (𝓞 E))).2 (by rintro _ ⟨i, rfl⟩; exact (b i).2) hw
  have hwV : w ∈ Submodule.span E (Λ : Set (Fin n → E)) := by
    have e : w = (y + w) - y := by abel
    rw [e]
    exact sub_mem hxV (Submodule.subset_span hy)
  have hw0 : w = 0 := Submodule.disjoint_def.1 hC.disjoint w hwV hwC
  rw [hw0, add_zero]
  exact hy

end Proof

/- English proof (translation)
Introduce `F E _ _ _ _ _ n Λ hfin x hx`. Conclude with `latLocGlob_main Λ hfin x hx`.
-/
theorem latLocGlob : LatLocGlob := by
  intro F E _ _ _ _ _ n Λ hfin x hx
  exact latLocGlob_main Λ hfin x hx

end Formalism.L2.GlobalTheoryTheory.Br
