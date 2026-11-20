import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingMapEqSmulMultiplier

namespace GlobalTheory

/- English proof (translation)
Establish `expand : ∀ (U : Submodule K A) [FiniteDimensional K U] (f : U), rd (f : A) = ∑ j, σ ((Module.finBasis K U).repr f j) • rd ((Module.finBasis K U j : U) : A)`. Introduce `U _ f`. Use `conv_lhs => rw [← (Module.finBasis K U).sum_repr f]`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, map_sum, hsemi]`. Use `set bV := Module.finBasis K V with hbV`.

Use `set bV' := Module.finBasis K V' with hbV'`. Set `gV : Fin (Module.finrank K V) → R` to `fun j => ⟨rd (bV j : A), hV _ (bV j).2⟩`. Set `gV' : Fin (Module.finrank K V') → R` to `fun j => ⟨rd (bV' j : A), hV' _ (bV' j).2⟩`. Establish `liV : LinearIndependent ℂ gV`. Apply `LinearIndependent.of_comp R.val.toLinearMap` to reduce the goal to its premises.

Conclude with `hind _ (fun j => (bV j : A)) (fun j => (bV j).2) (bV.linearIndependent.map' V.subtype V.ker_subtype)`. Establish `liV' : LinearIndependent ℂ gV'`. Apply `LinearIndependent.of_comp R.val.toLinearMap` to reduce the goal to its premises. Conclude with `hind' _ (fun j => (bV' j : A)) (fun j => (bV' j).2) (bV'.linearIndependent.map' V'.subtype V'.ker_subtype)`. Set `W` to `Submodule.span ℂ (Set.range gV)`.

Set `W'` to `Submodule.span ℂ (Set.range gV')`. Establish `eqV : ∀ f : V, (⟨rd f, hV _ f.2⟩ : R) = ∑ j, σ (bV.repr f j) • gV j`. Introduce `f`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, gV]`.

Conclude with `expand V f`. Establish `eqV' : ∀ f : V', (⟨rd f, hV' _ f.2⟩ : R) = ∑ j, σ (bV'.repr f j) • gV' j`. Introduce `f`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, gV']`.

Conclude with `expand V' f`. Establish `memW : ∀ f : V, (⟨rd f, hV _ f.2⟩ : R) ∈ W`. Introduce `f`. Rewrite using `[eqV f]`. Conclude with `Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))`.

Establish `memW' : ∀ f : V', (⟨rd f, hV' _ f.2⟩ : R) ∈ W'`. Introduce `f`. Rewrite using `[eqV' f]`. Conclude with `Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))`. Set `bW : Module.Basis (Fin (Module.finrank K V)) ℂ W` to `Module.Basis.span liV`.

Establish `bW_apply : ∀ j, (bW j : R) = gV j` using `fun j => congrArg Subtype.val (Module.Basis.span_apply liV j)`. Set `img : Fin (Module.finrank K V) → W'` to `fun j => ⟨⟨rd (T (bV j) : A), hV' _ (T (bV j)).2⟩, memW' (T (bV j))⟩`. Set `Tc : W →ₗ[ℂ] W'` to `bW.constr ℂ img`. Establish `Tc_rd : ∀ f : V, Tc ⟨⟨rd f, hV _ f.2⟩, memW f⟩ = ⟨⟨rd (T f : A), hV' _ (T f).2⟩, memW' (T f)⟩`. Introduce `f`.

Establish `e1 : (⟨⟨rd f, hV _ f.2⟩, memW f⟩ : W) = ∑ j, σ (bV.repr f j) • bW j`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, bW_apply]`. Conclude with `eqV f`. Rewrite using `[e1, map_sum]`.

Simplify using `only [map_smul, Tc, Module.Basis.constr_basis]`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, img]`. Use `conv_rhs => rw [← bV.sum_repr f]`.

Simplify using `only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, hsemi]`. Establish `Tc_basis : ∀ i, Tc (bW i) = img i` using `fun i => by`. Simplify using `only [Tc, Module.Basis.constr_basis]`. Use `haveI : FiniteDimensional ℂ W := Module.Finite.of_basis bW`. Establish `Tc_ne : Tc ≠ 0`.

Choose the witnesses or unpack the hypotheses as in `⟨f, hf⟩ : ∃ f, T f ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hT (LinearMap.ext hc)`. Establish `hfA : (T f : A) ≠ 0` using `fun hz => hf (Subtype.ext hz)`.

Establish `li1 : LinearIndependent ℂ (fun _ : Fin 1 => rd (T f : A))` using `hind' 1 (fun _ => (T f : A)) (fun _ => (T f).2) (linearIndependent_unique_iff.mpr hfA)`. Establish `hne : rd (T f : A) ≠ 0` using `li1.ne_zero 0`. Introduce `h0`. Apply `hne` to reduce the goal to its premises. Use `congrArg (fun x : W' => ((x : R) : B)) (Tc_rd f)` as an intermediate fact.

Simplify using `only [h0, LinearMap.zero_apply] at this`. Simplify using `using this.symm`. Establish `spanLe : Submodule.span ℂ (rd '' (V : Set A)) ≤ W.map R.val.toLinearMap`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨f, hf, rfl⟩`.

Conclude with `⟨⟨rd f, hV _ hf⟩, memW ⟨f, hf⟩, rfl⟩`. Establish `hW'W : ∀ w ∈ W', (⟨h', hh'⟩ : R) * w ∈ W`. Introduce `w hw`. Establish `hle : W' ≤ W.comap (LinearMap.mulLeft ℂ (⟨h', hh'⟩ : R))`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Use `show (⟨h', hh'⟩ : R) * gV' i ∈ W`. Take `⟨z, hz, hzeq⟩` from `spanLe (hsub _ (bV' i).2)`. Establish `: z = (⟨h', hh'⟩ : R) * gV' i` using `Subtype.ext hzeq`. Rewrite using `[← this]`.

Conclude with `hz`. Conclude with `hle hw`. Establish `hcommTc : ∀ x y : W, ((Tc x : R)) * (y : R) = (x : R) * (Tc y : R)`. Set `B1 : W →ₗ[ℂ] W →ₗ[ℂ] R` to `(LinearMap.mul ℂ R).compl₁₂ (W'.subtype ∘ₗ Tc) W.subtype`. Set `B2 : W →ₗ[ℂ] W →ₗ[ℂ] R` to `(LinearMap.mul ℂ R).compl₁₂ W.subtype (W'.subtype ∘ₗ Tc)`.

Establish `hB : B1 = B2`. Use `bW.ext fun i => bW.ext fun j => ?_` and prove the remaining obligations. Simplify using `only [B1, B2, LinearMap.compl₁₂_apply, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.mul_apply', Tc_basis, bW_apply]`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [img, gV, Subalgebra.coe_mul, ← map_mul]`.

Rewrite using `[hcomm]`. Introduce `x y`. Use `LinearMap.congr_fun₂ hB x y` as an intermediate fact. Simplify `this` using `[B1, B2]`. Establish `hhhR : (⟨h, hh⟩ : R) * ⟨h', hh'⟩ = 1` using `Subtype.ext (by simpa using hhh)`.

Take `⟨a, ha, hkey⟩` from `commuting_map_eq_smul_multiplier R W W' ⟨h, hh⟩ ⟨h', hh'⟩ hhhR hW'W Tc Tc_ne hcommTc`. Use `⟨a, ha, fun f => ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val (hkey ⟨⟨rd f, hV _ f.2⟩, memW f⟩)` as an intermediate fact. Rewrite `this` using `[Tc_rd]`. Simplify using `using this`.
-/
theorem commuting_multiplier_eq_const_smul_generator
    (K A B : Type) [Field K] [CommRing A] [Algebra K A] [CommRing B] [Algebra ℂ B]
    (σ : K →+* ℂ) (rd : A →+* B)
    (hsemi : ∀ (a : K) (f : A), rd (a • f) = σ a • rd f)
    (R : Subalgebra ℂ B) [IsDomain R] (V V' : Submodule K A)
    [FiniteDimensional K V] [FiniteDimensional K V']
    (hV : ∀ f ∈ V, rd f ∈ R) (hV' : ∀ f ∈ V', rd f ∈ R)
    (hind : ∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V) → LinearIndependent K b →
      LinearIndependent ℂ (fun i => rd (b i)))
    (hind' : ∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V') → LinearIndependent K b →
      LinearIndependent ℂ (fun i => rd (b i)))
    (h h' : B) (hh : h ∈ R) (hh' : h' ∈ R) (hhh : h * h' = 1)
    (hsub : ∀ f ∈ V', h' * rd f ∈ Submodule.span ℂ (rd '' (V : Set A)))
    (T : V →ₗ[K] V') (hT : T ≠ 0)
    (hcomm : ∀ f g : V, (T f : A) * (g : A) = (f : A) * (T g : A)) :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ f : V, rd (T f) = a • (h * rd f) := by
  classical
  have expand : ∀ (U : Submodule K A) [FiniteDimensional K U] (f : U),
      rd (f : A) = ∑ j, σ ((Module.finBasis K U).repr f j) •
        rd ((Module.finBasis K U j : U) : A) := by
    intro U _ f
    conv_lhs => rw [← (Module.finBasis K U).sum_repr f]
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, hsemi]
  set bV := Module.finBasis K V with hbV
  set bV' := Module.finBasis K V' with hbV'
  let gV : Fin (Module.finrank K V) → R := fun j => ⟨rd (bV j : A), hV _ (bV j).2⟩
  let gV' : Fin (Module.finrank K V') → R := fun j => ⟨rd (bV' j : A), hV' _ (bV' j).2⟩
  have liV : LinearIndependent ℂ gV := by
    apply LinearIndependent.of_comp R.val.toLinearMap
    exact hind _ (fun j => (bV j : A)) (fun j => (bV j).2)
      (bV.linearIndependent.map' V.subtype V.ker_subtype)
  have liV' : LinearIndependent ℂ gV' := by
    apply LinearIndependent.of_comp R.val.toLinearMap
    exact hind' _ (fun j => (bV' j : A)) (fun j => (bV' j).2)
      (bV'.linearIndependent.map' V'.subtype V'.ker_subtype)
  let W := Submodule.span ℂ (Set.range gV)
  let W' := Submodule.span ℂ (Set.range gV')
  have eqV : ∀ f : V, (⟨rd f, hV _ f.2⟩ : R) = ∑ j, σ (bV.repr f j) • gV j := by
    intro f
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, gV]
    exact expand V f
  have eqV' : ∀ f : V', (⟨rd f, hV' _ f.2⟩ : R) = ∑ j, σ (bV'.repr f j) • gV' j := by
    intro f
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, gV']
    exact expand V' f
  have memW : ∀ f : V, (⟨rd f, hV _ f.2⟩ : R) ∈ W := by
    intro f
    rw [eqV f]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  have memW' : ∀ f : V', (⟨rd f, hV' _ f.2⟩ : R) ∈ W' := by
    intro f
    rw [eqV' f]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  let bW : Module.Basis (Fin (Module.finrank K V)) ℂ W := Module.Basis.span liV
  have bW_apply : ∀ j, (bW j : R) = gV j := fun j => congrArg Subtype.val (Module.Basis.span_apply liV j)
  let img : Fin (Module.finrank K V) → W' := fun j => ⟨⟨rd (T (bV j) : A), hV' _ (T (bV j)).2⟩, memW' (T (bV j))⟩
  let Tc : W →ₗ[ℂ] W' := bW.constr ℂ img
  have Tc_rd : ∀ f : V, Tc ⟨⟨rd f, hV _ f.2⟩, memW f⟩ = ⟨⟨rd (T f : A), hV' _ (T f).2⟩, memW' (T f)⟩ := by
    intro f
    have e1 : (⟨⟨rd f, hV _ f.2⟩, memW f⟩ : W) = ∑ j, σ (bV.repr f j) • bW j := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, bW_apply]
      exact eqV f
    rw [e1, map_sum]
    simp only [map_smul, Tc, Module.Basis.constr_basis]
    apply Subtype.ext; apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, AddSubmonoidClass.coe_finset_sum,
      SetLike.val_smul, img]
    conv_rhs => rw [← bV.sum_repr f]
    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, hsemi]
  have Tc_basis : ∀ i, Tc (bW i) = img i := fun i => by
    simp only [Tc, Module.Basis.constr_basis]
  haveI : FiniteDimensional ℂ W := Module.Finite.of_basis bW
  have Tc_ne : Tc ≠ 0 := by
    obtain ⟨f, hf⟩ : ∃ f, T f ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hT (LinearMap.ext hc)
    have hfA : (T f : A) ≠ 0 := fun hz => hf (Subtype.ext hz)
    have li1 : LinearIndependent ℂ (fun _ : Fin 1 => rd (T f : A)) :=
      hind' 1 (fun _ => (T f : A)) (fun _ => (T f).2)
        (linearIndependent_unique_iff.mpr hfA)
    have hne : rd (T f : A) ≠ 0 := li1.ne_zero 0
    intro h0
    apply hne
    have := congrArg (fun x : W' => ((x : R) : B)) (Tc_rd f)
    simp only [h0, LinearMap.zero_apply] at this
    simpa using this.symm
  have spanLe : Submodule.span ℂ (rd '' (V : Set A)) ≤ W.map R.val.toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨⟨rd f, hV _ hf⟩, memW ⟨f, hf⟩, rfl⟩
  have hW'W : ∀ w ∈ W', (⟨h', hh'⟩ : R) * w ∈ W := by
    intro w hw
    have hle : W' ≤ W.comap (LinearMap.mulLeft ℂ (⟨h', hh'⟩ : R)) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      show (⟨h', hh'⟩ : R) * gV' i ∈ W
      obtain ⟨z, hz, hzeq⟩ := spanLe (hsub _ (bV' i).2)
      have : z = (⟨h', hh'⟩ : R) * gV' i := Subtype.ext hzeq
      rw [← this]; exact hz
    exact hle hw
  have hcommTc : ∀ x y : W, ((Tc x : R)) * (y : R) = (x : R) * (Tc y : R) := by
    let B1 : W →ₗ[ℂ] W →ₗ[ℂ] R := (LinearMap.mul ℂ R).compl₁₂ (W'.subtype ∘ₗ Tc) W.subtype
    let B2 : W →ₗ[ℂ] W →ₗ[ℂ] R := (LinearMap.mul ℂ R).compl₁₂ W.subtype (W'.subtype ∘ₗ Tc)
    have hB : B1 = B2 := by
      refine bW.ext fun i => bW.ext fun j => ?_
      simp only [B1, B2, LinearMap.compl₁₂_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        LinearMap.mul_apply', Tc_basis, bW_apply]
      apply Subtype.ext
      simp only [img, gV, Subalgebra.coe_mul, ← map_mul]
      rw [hcomm]
    intro x y
    have := LinearMap.congr_fun₂ hB x y
    simpa [B1, B2] using this
  have hhhR : (⟨h, hh⟩ : R) * ⟨h', hh'⟩ = 1 := Subtype.ext (by simpa using hhh)
  obtain ⟨a, ha, hkey⟩ := commuting_map_eq_smul_multiplier R W W' ⟨h, hh⟩ ⟨h', hh'⟩ hhhR hW'W Tc Tc_ne hcommTc
  refine ⟨a, ha, fun f => ?_⟩
  have := congrArg Subtype.val (hkey ⟨⟨rd f, hV _ f.2⟩, memW f⟩)
  rw [Tc_rd] at this
  simpa using this

end GlobalTheory
