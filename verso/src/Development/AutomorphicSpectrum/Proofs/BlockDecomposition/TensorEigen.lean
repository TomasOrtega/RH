import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount

open TensorProduct

namespace GlobalTheory.CompanionTheory.TensContr

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

noncomputable def contr (v : V ⊗[ℂ] W) : Module.Dual ℂ W →ₗ[ℂ] V where
  toFun l := TensorProduct.rid ℂ V (LinearMap.lTensor V l v)
  map_add' l m := by
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [add_smul]
    | add s t hs ht =>
      simp only [map_add] at hs ht ⊢
      rw [hs, ht]; abel
  map_smul' c l := by
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [mul_smul]
    | add s t hs ht =>
      simp only [map_add, RingHom.id_apply, smul_add] at hs ht ⊢
      rw [hs, ht]

/- English proof (translation)
Use `show TensorProduct.rid ℂ V (LinearMap.lTensor V l (a ⊗ₜ[ℂ] b)) = l b • a`. Rewrite using `[LinearMap.lTensor_tmul, TensorProduct.rid_tmul]`.
-/
@[simp] theorem contr_tmul (a : V) (b : W) (l : Module.Dual ℂ W) :
    contr (a ⊗ₜ[ℂ] b) l = l b • a := by
  show TensorProduct.rid ℂ V (LinearMap.lTensor V l (a ⊗ₜ[ℂ] b)) = l b • a
  rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem contr_apply (v : V ⊗[ℂ] W) (l : Module.Dual ℂ W) :
    contr v l = TensorProduct.rid ℂ V (LinearMap.lTensor V l v) := rfl

/- English proof (translation)
Simplify using `only [GlobalTheory.CompanionTheory.TensContr.contr_apply, map_add]`.
-/
theorem contr_add (s t : V ⊗[ℂ] W) (l : Module.Dual ℂ W) :
    contr (s + t) l = contr s l + contr t l := by
  simp only [GlobalTheory.CompanionTheory.TensContr.contr_apply, map_add]

/- English proof (translation)
Simplify using `only [GlobalTheory.CompanionTheory.TensContr.contr_apply, map_smul]`.
-/
theorem contr_smul (c : ℂ) (t : V ⊗[ℂ] W) (l : Module.Dual ℂ W) :
    contr (c • t) l = c • contr t l := by
  simp only [GlobalTheory.CompanionTheory.TensContr.contr_apply, map_smul]

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero, GlobalTheory.CompanionTheory.TensContr.contr_apply]`. Consider the case `tmul a b`. Rewrite using `[TensorProduct.map_tmul, GlobalTheory.CompanionTheory.TensContr.contr_tmul, GlobalTheory.CompanionTheory.TensContr.contr_tmul, LinearMap.comp_apply, map_smul]`. Consider the case `add s t hs ht`.

Rewrite using `[map_add, GlobalTheory.CompanionTheory.TensContr.contr_add, GlobalTheory.CompanionTheory.TensContr.contr_add, hs, ht, map_add]`.
-/
theorem contr_map (f : V →ₗ[ℂ] V) (g : W →ₗ[ℂ] W) (t : V ⊗[ℂ] W) (l : Module.Dual ℂ W) :
    contr (TensorProduct.map f g t) l = f (contr t (l ∘ₗ g)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, GlobalTheory.CompanionTheory.TensContr.contr_apply]
  | tmul a b =>
    rw [TensorProduct.map_tmul, GlobalTheory.CompanionTheory.TensContr.contr_tmul, GlobalTheory.CompanionTheory.TensContr.contr_tmul,
      LinearMap.comp_apply, map_smul]
  | add s t hs ht =>
    rw [map_add, GlobalTheory.CompanionTheory.TensContr.contr_add, GlobalTheory.CompanionTheory.TensContr.contr_add, hs, ht, map_add]

/- English proof (translation)
Proceed by induction on `v using TensorProduct.induction_on with`. Consider the case `zero`. Use `⟨∅, fun l => ?_⟩` and prove the remaining obligations. Simplify using `only [GlobalTheory.CompanionTheory.TensContr.contr_apply, map_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `tmul a b`. Use `⟨{a}, fun l => ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.CompanionTheory.TensContr.contr_tmul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (by simp))`. Consider the case `add s t hs ht`.

Take `⟨S, hS⟩` from `hs`. Take `⟨T, hT⟩` from `ht`. Use `⟨S ∪ T, fun l => ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.CompanionTheory.TensContr.contr_add]`. Use `Submodule.add_mem _ (Submodule.span_mono ?_ (hS l)) (Submodule.span_mono ?_ (hT l))` and prove the remaining obligations.

Conclude with `Finset.subset_union_left` after adjusting the coercions. Conclude with `Finset.subset_union_right` after adjusting the coercions.
-/
theorem exists_finset_contr (v : V ⊗[ℂ] W) :
    ∃ s : Finset V, ∀ l, contr v l ∈ Submodule.span ℂ (s : Set V) := by
  classical
  induction v using TensorProduct.induction_on with
  | zero =>
    refine ⟨∅, fun l => ?_⟩
    simp only [GlobalTheory.CompanionTheory.TensContr.contr_apply, map_zero]
    exact Submodule.zero_mem _
  | tmul a b =>
    refine ⟨{a}, fun l => ?_⟩
    rw [GlobalTheory.CompanionTheory.TensContr.contr_tmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  | add s t hs ht =>
    obtain ⟨S, hS⟩ := hs
    obtain ⟨T, hT⟩ := ht
    refine ⟨S ∪ T, fun l => ?_⟩
    rw [GlobalTheory.CompanionTheory.TensContr.contr_add]
    refine Submodule.add_mem _ (Submodule.span_mono ?_ (hS l)) (Submodule.span_mono ?_ (hT l))
    · exact_mod_cast Finset.subset_union_left
    · exact_mod_cast Finset.subset_union_right

/- English proof (translation)
Take `⟨s, hs⟩` from `GlobalTheory.CompanionTheory.TensContr.exists_finset_contr v`. Use `haveI := FiniteDimensional.span_finset ℂ s`. Establish `hle : LinearMap.range (GlobalTheory.CompanionTheory.TensContr.contr v) ≤ Submodule.span ℂ (s : Set V)`. Introduce and unpack `_ ⟨l, rfl⟩`. Conclude with `hs l`.

Conclude with `Submodule.finiteDimensional_of_le hle`.
-/
theorem finiteDimensional_range_contr (v : V ⊗[ℂ] W) :
    FiniteDimensional ℂ (LinearMap.range (contr v)) := by
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.TensContr.exists_finset_contr v
  haveI := FiniteDimensional.span_finset ℂ s
  have hle : LinearMap.range (GlobalTheory.CompanionTheory.TensContr.contr v) ≤ Submodule.span ℂ (s : Set V) := by
    rintro _ ⟨l, rfl⟩
    exact hs l
  exact Submodule.finiteDimensional_of_le hle

/- English proof (translation)
Set `b` to `Module.Basis.ofVectorSpace ℂ W`. Set `e` to `TensorProduct.equivFinsuppOfBasisRight (M := V) b`. Establish `key : ∀ (t : V ⊗[ℂ] W) i, e t i = GlobalTheory.CompanionTheory.TensContr.contr t (b.coord i)`. Introduce `t i`. Proceed by induction on `t using TensorProduct.induction_on with`.

Consider the case `zero`. Simplify using `only [map_zero, Finsupp.coe_zero, Pi.zero_apply, GlobalTheory.CompanionTheory.TensContr.contr_apply]`. Consider the case `tmul a w`. Rewrite using `[TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, GlobalTheory.CompanionTheory.TensContr.contr_tmul, Module.Basis.coord_apply]`. Consider the case `add s t hs ht`.

Rewrite using `[map_add, Finsupp.add_apply, hs, ht, GlobalTheory.CompanionTheory.TensContr.contr_add]`. Establish `he : e v = 0`. Use extensionality with `i`. Rewrite using `[key, h, Finsupp.coe_zero, Pi.zero_apply]`. Conclude with `(LinearEquiv.map_eq_zero_iff e).mp he`.
-/
theorem eq_zero_of_contr (v : V ⊗[ℂ] W) (h : ∀ l, contr v l = 0) : v = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace ℂ W
  let e := TensorProduct.equivFinsuppOfBasisRight (M := V) b
  have key : ∀ (t : V ⊗[ℂ] W) i, e t i = GlobalTheory.CompanionTheory.TensContr.contr t (b.coord i) := by
    intro t i
    induction t using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply, GlobalTheory.CompanionTheory.TensContr.contr_apply]
    | tmul a w =>
      rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, GlobalTheory.CompanionTheory.TensContr.contr_tmul,
        Module.Basis.coord_apply]
    | add s t hs ht =>
      rw [map_add, Finsupp.add_apply, hs, ht, GlobalTheory.CompanionTheory.TensContr.contr_add]
  have he : e v = 0 := by
    ext i
    rw [key, h, Finsupp.coe_zero, Pi.zero_apply]
  exact (LinearEquiv.map_eq_zero_iff e).mp he

end GlobalTheory.CompanionTheory.TensContr

namespace GlobalTheory.CompanionTheory.TensContr

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable {X Y : Type*}

/- English proof (translation)
Simplify using `only [← GlobalTheory.CompanionTheory.TensContr.contr_apply]`. Use `set φ := GlobalTheory.CompanionTheory.TensContr.contr v with hφ`. Establish `hne : ∃ l, φ l ≠ 0`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Conclude with `hv (GlobalTheory.CompanionTheory.TensContr.eq_zero_of_contr v hcon)`. Take `⟨l₀, hl₀⟩` from `hne`. Distinguish the cases in `hX : IsEmpty X`. Conclude with `⟨l₀, 1, one_ne_zero, hl₀, fun x => (hX.false x).elim⟩`. Take `⟨x₀⟩` from `not_isEmpty_iff.mp hX`.

Take `⟨y₀⟩` from `‹Nonempty Y›`. Establish `rel : ∀ x l, A x (φ (l ∘ₗ B y₀)) = (lam x * mu y₀) • φ l`. Introduce `x l`. Rewrite using `[hφ, ← GlobalTheory.CompanionTheory.TensContr.contr_map, heig, GlobalTheory.CompanionTheory.TensContr.contr_smul]`. Set `U` to `LinearMap.range φ`.

Use `haveI : FiniteDimensional ℂ U := GlobalTheory.CompanionTheory.TensContr.finiteDimensional_range_contr v`. Set `U'` to `LinearMap.range (φ ∘ₗ (B y₀).dualMap)`. Establish `hU'U : U' ≤ U` using `LinearMap.range_comp_le_range _ _`. Establish `hmapU' : U ≤ Submodule.map (A x₀) U'`. Introduce and unpack `_ ⟨l, rfl⟩`.

Establish `hk : lam x₀ * mu y₀ ≠ 0` using `mul_ne_zero (hlam x₀) (hmu y₀)`. Use `⟨φ (((lam x₀ * mu y₀)⁻¹ • l) ∘ₗ B y₀), ⟨(lam x₀ * mu y₀)⁻¹ • l, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, LinearMap.dualMap_apply']`. Rewrite using `[rel, map_smul, smul_smul, mul_inv_cancel₀ hk, one_smul]`. Use `haveI : FiniteDimensional ℂ U' := Submodule.finiteDimensional_of_le hU'U`.

Establish `hUU' : U' = U`. Use `Submodule.eq_of_le_of_finrank_le hU'U ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `hrepr : ∀ u ∈ U, ∃ l, u = φ (l ∘ₗ B y₀)`. Introduce `u hu`.

Rewrite `hu` using `[← hUU']`. Take `⟨l, rfl⟩` from `hu`. Conclude with `⟨l, by rw [LinearMap.comp_apply, LinearMap.dualMap_apply']⟩`. Establish `hmaps : ∀ x, ∀ u ∈ U, A x u ∈ U`. Introduce `x u hu`.

Take `⟨l, rfl⟩` from `hrepr u hu`. Rewrite using `[rel]`. Conclude with `Submodule.smul_mem _ _ ⟨l, rfl⟩`. Establish `hprop : ∀ x, ∀ u ∈ U, A x u = (lam x * (lam x₀)⁻¹) • A x₀ u`. Introduce `x u hu`.

Take `⟨l, rfl⟩` from `hrepr u hu`. Rewrite using `[rel, rel, smul_smul]`. Use `congr 1`. Clear denominators, using `[hlam x₀, hmu y₀]` for the nonvanishing conditions. Set `T : Module.End ℂ U` to `(A x₀).restrict (hmaps x₀)`.

Establish `hsurj : Function.Surjective T`. Introduce and unpack `⟨u, hu⟩`. Take `⟨w, hw, hwu⟩` from `hmapU' hu`. Conclude with `⟨⟨w, hU'U hw⟩, Subtype.ext (by simpa [T, LinearMap.restrict_apply] using hwu)⟩`. Establish `hinj : Function.Injective T` using `LinearMap.injective_iff_surjective.mpr hsurj`.

Use `haveI : Nontrivial U := nontrivial_of_ne (⟨φ l₀, ⟨l₀, rfl⟩⟩ : U) 0 (fun h => hl₀ (congrArg Subtype.val h))`. Take `⟨t, ht⟩` from `Module.End.exists_eigenvalue T`. Take `⟨u, hu⟩` from `ht.exists_hasEigenvector`. Establish `hTu` using `hu.apply_eq_smul`. Establish `hu0 : u ≠ 0` using `hu.2`.

Establish `ht0 : t ≠ 0`. Introduce and unpack `rfl`. Rewrite `hTu` using `[zero_smul]`. Conclude with `hu0 (hinj (by rw [hTu, map_zero]))`. Establish `hAu : A x₀ u = t • (u : V)`.

Use `congrArg Subtype.val hTu` as an intermediate fact. Simplify `this` using `[T, LinearMap.restrict_apply]`. Take `⟨l, hl⟩` from `u.2`. Use `⟨l, t * (lam x₀)⁻¹, mul_ne_zero ht0 (inv_ne_zero (hlam x₀)), ?_, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[hl]`.

Conclude with `fun h => hu0 (Subtype.ext h)`. Rewrite using `[hl, hprop x _ u.2, hAu, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_contr_eigen [Nonempty Y]
    (A : X → V →ₗ[ℂ] V) (B : Y → W →ₗ[ℂ] W) (lam : X → ℂ) (mu : Y → ℂ)
    (hlam : ∀ x, lam x ≠ 0) (hmu : ∀ y, mu y ≠ 0)
    (v : V ⊗[ℂ] W) (hv : v ≠ 0)
    (heig : ∀ x y, TensorProduct.map (A x) (B y) v = (lam x * mu y) • v) :
    ∃ (l : Module.Dual ℂ W) (c : ℂ), c ≠ 0 ∧
      TensorProduct.rid ℂ V (LinearMap.lTensor V l v) ≠ 0 ∧
      ∀ x, A x (TensorProduct.rid ℂ V (LinearMap.lTensor V l v)) =
        (c * lam x) • TensorProduct.rid ℂ V (LinearMap.lTensor V l v) := by
  simp only [← GlobalTheory.CompanionTheory.TensContr.contr_apply]
  set φ := GlobalTheory.CompanionTheory.TensContr.contr v with hφ
  have hne : ∃ l, φ l ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hv (GlobalTheory.CompanionTheory.TensContr.eq_zero_of_contr v hcon)
  obtain ⟨l₀, hl₀⟩ := hne
  by_cases hX : IsEmpty X
  · exact ⟨l₀, 1, one_ne_zero, hl₀, fun x => (hX.false x).elim⟩
  obtain ⟨x₀⟩ := not_isEmpty_iff.mp hX
  obtain ⟨y₀⟩ := ‹Nonempty Y›
  have rel : ∀ x l, A x (φ (l ∘ₗ B y₀)) = (lam x * mu y₀) • φ l := by
    intro x l
    rw [hφ, ← GlobalTheory.CompanionTheory.TensContr.contr_map, heig, GlobalTheory.CompanionTheory.TensContr.contr_smul]
  let U := LinearMap.range φ
  haveI : FiniteDimensional ℂ U := GlobalTheory.CompanionTheory.TensContr.finiteDimensional_range_contr v
  let U' := LinearMap.range (φ ∘ₗ (B y₀).dualMap)
  have hU'U : U' ≤ U := LinearMap.range_comp_le_range _ _
  have hmapU' : U ≤ Submodule.map (A x₀) U' := by
    rintro _ ⟨l, rfl⟩
    have hk : lam x₀ * mu y₀ ≠ 0 := mul_ne_zero (hlam x₀) (hmu y₀)
    refine ⟨φ (((lam x₀ * mu y₀)⁻¹ • l) ∘ₗ B y₀), ⟨(lam x₀ * mu y₀)⁻¹ • l, ?_⟩, ?_⟩
    · rw [LinearMap.comp_apply, LinearMap.dualMap_apply']
    · rw [rel, map_smul, smul_smul, mul_inv_cancel₀ hk, one_smul]
  haveI : FiniteDimensional ℂ U' := Submodule.finiteDimensional_of_le hU'U
  have hUU' : U' = U := by
    refine Submodule.eq_of_le_of_finrank_le hU'U ?_
    calc Module.finrank ℂ U ≤ Module.finrank ℂ (Submodule.map (A x₀) U') :=
          Submodule.finrank_mono hmapU'
      _ ≤ Module.finrank ℂ U' := Submodule.finrank_map_le _ _
  have hrepr : ∀ u ∈ U, ∃ l, u = φ (l ∘ₗ B y₀) := by
    intro u hu
    rw [← hUU'] at hu
    obtain ⟨l, rfl⟩ := hu
    exact ⟨l, by rw [LinearMap.comp_apply, LinearMap.dualMap_apply']⟩
  have hmaps : ∀ x, ∀ u ∈ U, A x u ∈ U := by
    intro x u hu
    obtain ⟨l, rfl⟩ := hrepr u hu
    rw [rel]
    exact Submodule.smul_mem _ _ ⟨l, rfl⟩
  have hprop : ∀ x, ∀ u ∈ U, A x u = (lam x * (lam x₀)⁻¹) • A x₀ u := by
    intro x u hu
    obtain ⟨l, rfl⟩ := hrepr u hu
    rw [rel, rel, smul_smul]
    congr 1
    field_simp [hlam x₀, hmu y₀]
  let T : Module.End ℂ U := (A x₀).restrict (hmaps x₀)
  have hsurj : Function.Surjective T := by
    rintro ⟨u, hu⟩
    obtain ⟨w, hw, hwu⟩ := hmapU' hu
    exact ⟨⟨w, hU'U hw⟩, Subtype.ext (by simpa [T, LinearMap.restrict_apply] using hwu)⟩
  have hinj : Function.Injective T := LinearMap.injective_iff_surjective.mpr hsurj
  haveI : Nontrivial U := nontrivial_of_ne (⟨φ l₀, ⟨l₀, rfl⟩⟩ : U) 0
    (fun h => hl₀ (congrArg Subtype.val h))
  obtain ⟨t, ht⟩ := Module.End.exists_eigenvalue T
  obtain ⟨u, hu⟩ := ht.exists_hasEigenvector
  have hTu := hu.apply_eq_smul
  have hu0 : u ≠ 0 := hu.2
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hTu
    exact hu0 (hinj (by rw [hTu, map_zero]))
  have hAu : A x₀ u = t • (u : V) := by
    have := congrArg Subtype.val hTu
    simpa [T, LinearMap.restrict_apply] using this
  obtain ⟨l, hl⟩ := u.2
  refine ⟨l, t * (lam x₀)⁻¹, mul_ne_zero ht0 (inv_ne_zero (hlam x₀)), ?_, fun x => ?_⟩
  · rw [hl]
    exact fun h => hu0 (Subtype.ext h)
  · rw [hl, hprop x _ u.2, hAu, smul_smul]
    congr 1
    ring

end GlobalTheory.CompanionTheory.TensContr

namespace GlobalTheory.CompanionTheory.TensContr

/- English proof (translation)
Introduce `V W X Y _ _ _ _ A B lam mu v hv hY hlam hmu heig`. Conclude with `GlobalTheory.CompanionTheory.TensContr.exists_contr_eigen A B lam mu hlam hmu v hv heig`.
-/
theorem tensEig : PositivityTheory.Rg.BcB.F.Tail.PExp.TensEig := by
  intro V W X Y _ _ _ _ A B lam mu v hv hY hlam hmu heig
  exact GlobalTheory.CompanionTheory.TensContr.exists_contr_eigen A B lam mu hlam hmu v hv heig

end GlobalTheory.CompanionTheory.TensContr
