import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.CardStepOf

open NumberField PI.UJClassFin PI.UJClassMass

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

/- English proof (translation)
Rewrite using `[show (((y : 𝓞 F) : F)) = (y : F) by rfl, Int.cast_smul_eq_zsmul]`.
-/
theorem intF_smul (y : ℤ) (e : E) : (((y : 𝓞 F) : F)) • e = y • e := by
  rw [show (((y : 𝓞 F) : F)) = (y : F) by rfl, Int.cast_smul_eq_zsmul]

/- English proof (translation)
Take `⟨s, hs⟩` from `hfg`. Take `⟨y, hy, hint⟩` from `exists_integral_multiples ℤ ℚ ((s ×ˢ (Finset.univ : Finset (Fin M))).image (fun p => b.equivFun p.1 p.2))`. Use `⟨y, hy, fun x hx i => ?_⟩` and prove the remaining obligations. Establish `hw : (∑ j, x j • b j) ∈ Submodule.span (𝓞 E) (s : Set V)` using `by rw [hs]; exact hx`. Establish `key : ∀ w ∈ Submodule.span (𝓞 E) (s : Set V), ∀ i, IsIntegral ℤ (y • b.equivFun w i)`.

Introduce `w hw'`. Proceed by induction on `hw' using Submodule.span_induction with`. Consider the case `mem v hv`. Introduce `i`. Conclude with `hint _ (Finset.mem_image.mpr ⟨(v, i), Finset.mem_product.mpr ⟨hv, Finset.mem_univ _⟩, rfl⟩)`.

Consider the case `zero => intro i`. Simplify using `[isIntegral_zero]`. Consider the case `add v w _ _ hv hw => intro i`. Rewrite using `[map_add, Pi.add_apply, smul_add]`. Conclude with `(hv i).add (hw i)`.

Consider the case `smul a v _ hv`. Introduce `i`. Rewrite using `[← algebraMap_smul E a v, map_smul, Pi.smul_apply, smul_eq_mul, ← mul_smul_comm]`. Conclude with `(RingOfIntegers.isIntegral_coe a).mul (hv i)`. Use `key _ hw i` as an intermediate fact.

Rewrite using `[show b.equivFun (∑ j, x j • b j) = x by` and apply the resulting hypothesis. Rewrite `this` using `[← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]]`.
-/
theorem crd_upper {M : ℕ} (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) (hfg : L0.FG) :
    ∃ y : ℤ, y ≠ 0 ∧ ∀ x ∈ crdOf b L0, ∀ i, IsIntegral ℤ (y • x i) := by
  classical
  obtain ⟨s, hs⟩ := hfg
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ
    ((s ×ˢ (Finset.univ : Finset (Fin M))).image (fun p => b.equivFun p.1 p.2))
  refine ⟨y, hy, fun x hx i => ?_⟩
  have hw : (∑ j, x j • b j) ∈ Submodule.span (𝓞 E) (s : Set V) := by rw [hs]; exact hx
  have key : ∀ w ∈ Submodule.span (𝓞 E) (s : Set V), ∀ i, IsIntegral ℤ (y • b.equivFun w i) := by
    intro w hw'
    induction hw' using Submodule.span_induction with
    | mem v hv =>
      intro i
      exact hint _ (Finset.mem_image.mpr ⟨(v, i), Finset.mem_product.mpr ⟨hv, Finset.mem_univ _⟩, rfl⟩)
    | zero => intro i; simp [isIntegral_zero]
    | add v w _ _ hv hw => intro i; rw [map_add, Pi.add_apply, smul_add]; exact (hv i).add (hw i)
    | smul a v _ hv =>
      intro i
      rw [← algebraMap_smul E a v, map_smul, Pi.smul_apply, smul_eq_mul, ← mul_smul_comm]
      exact (RingOfIntegers.isIntegral_coe a).mul (hv i)
  have := key _ hw i
  rwa [show b.equivFun (∑ j, x j • b j) = x by
    rw [← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]] at this

/- English proof (translation)
Set `a : 𝓞 E` to `⟨e, he⟩`. Establish `ha : algebraMap (𝓞 E) E a = e` using `rfl`. Rewrite using `[← ha, algebraMap_smul]`. Conclude with `L0.smul_mem a hv`.
-/
theorem int_smul_mem (L0 : Submodule (𝓞 E) V) {e : E} (he : IsIntegral ℤ e) {v : V} (hv : v ∈ L0) :
    e • v ∈ L0 := by
  let a : 𝓞 E := ⟨e, he⟩
  have ha : algebraMap (𝓞 E) E a = e := rfl
  rw [← ha, algebraMap_smul]
  exact L0.smul_mem a hv

/- English proof (translation)
Establish `hmem : ∀ i, b i ∈ Submodule.span E (L0 : Set V)` using `fun i => by rw [hspan]; exact Submodule.mem_top`. Use `choose n f g hfg using fun i => (Submodule.mem_span_set' (R := E)).mp (hmem i)`. Take `⟨y, hy, hint⟩` from `exists_integral_multiples ℤ ℚ (Finset.univ.biUnion (fun i => Finset.univ.image (f i)))`. Use `⟨y, hy, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[← hfg i, Finset.smul_sum]`.

Use `Submodule.sum_mem _ (fun k _ => ?_)` and prove the remaining obligations. Establish `hk : IsIntegral ℤ (y • f i k)` using `hint _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩)`. Rewrite using `[← smul_assoc]`. Conclude with `int_smul_mem L0 hk (g i k).2`.
-/
theorem crd_lower {M : ℕ} (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V)
    (hspan : Submodule.span E (L0 : Set V) = ⊤) :
    ∃ y : ℤ, y ≠ 0 ∧ ∀ i, y • b i ∈ L0 := by
  classical
  have hmem : ∀ i, b i ∈ Submodule.span E (L0 : Set V) := fun i => by rw [hspan]; exact Submodule.mem_top
  choose n f g hfg using fun i => (Submodule.mem_span_set' (R := E)).mp (hmem i)
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.biUnion (fun i => Finset.univ.image (f i)))
  refine ⟨y, hy, fun i => ?_⟩
  rw [← hfg i, Finset.smul_sum]
  refine Submodule.sum_mem _ (fun k _ => ?_)
  have hk : IsIntegral ℤ (y • f i k) := hint _ (Finset.mem_biUnion.mpr
    ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩)
  rw [← smul_assoc]
  exact int_smul_mem L0 hk (g i k).2

/- English proof (translation)
Conclude with `hy` after adjusting the coercions.
-/
theorem intCast_ne_zero_OF (y : ℤ) (hy : y ≠ 0) : (y : 𝓞 F) ≠ 0 := by
  exact_mod_cast hy

end

/- English proof (translation)
Introduce `F E _ _ _ _ _ V _ _ _ _ _ M b L0 hL`. Take `⟨y1, hy1, h1⟩` from `crd_upper b L0 hL.fg`. Take `⟨y2, hy2, h2⟩` from `crd_lower b L0 hL.span_eq_top`. Use `⟨⟨(y1 : 𝓞 F), intCast_ne_zero_OF y1 hy1, fun x hx i => ?_⟩, ⟨(y2 : 𝓞 F), intCast_ne_zero_OF y2 hy2, fun i e he => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[intF_smul]`.

Conclude with `h1 x hx i`. Use `show ∑ j, (Pi.single i ((((y2 : 𝓞 F) : F)) • e) : Fin M → E) j • b j ∈ L0`. Rewrite using `[Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp), Pi.single_eq_same, intF_smul, smul_assoc, smul_comm]`. Conclude with `int_smul_mem L0 he (h2 i)`.
-/
theorem crdBounds : CrdBounds := by
  intro F E _ _ _ _ _ V _ _ _ _ _ M b L0 hL
  obtain ⟨y1, hy1, h1⟩ := crd_upper b L0 hL.fg
  obtain ⟨y2, hy2, h2⟩ := crd_lower b L0 hL.span_eq_top
  refine ⟨⟨(y1 : 𝓞 F), intCast_ne_zero_OF y1 hy1, fun x hx i => ?_⟩,
    ⟨(y2 : 𝓞 F), intCast_ne_zero_OF y2 hy2, fun i e he => ?_⟩⟩
  · rw [intF_smul]
    exact h1 x hx i
  · show ∑ j, (Pi.single i ((((y2 : 𝓞 F) : F)) • e) : Fin M → E) j • b j ∈ L0
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp),
      Pi.single_eq_same, intF_smul, smul_assoc, smul_comm]
    exact int_smul_mem L0 he (h2 i)

/- English proof (translation)
The claim follows from `uJClassMass_of_deep hR crdBounds s1 s4`.
-/
theorem uJClassMass_of_deep' (hR : PI.UnitaryGroupMassFormula.UJClassFin.RatDense) (s1 : LatStep) (s4 : SurjStep) :
    PI.UJClassMass2.UJClassMass :=
  uJClassMass_of_deep hR crdBounds s1 s4

end PI.UnitaryGroupMassFormula.UJClassMass

end
