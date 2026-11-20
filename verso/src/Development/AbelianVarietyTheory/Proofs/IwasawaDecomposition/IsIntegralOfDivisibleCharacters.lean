import Mathlib
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart

open Formalism.MainNotions.DIV.Cons (intO)
open Polynomial

namespace GlobalTheory.IntegralOfPointValues

/- English proof (translation)
Set `V : ValuationSubring C` to `{ intO C with mem_or_inv_mem' := fun x => by`. Express the relevant statement in the definitionally equal form `‖x‖ ≤ 1 ∨ ‖x⁻¹‖ ≤ 1`. Break down `le_total ‖x‖ 1 with h | h` into its components or cases. Conclude with `Or.inl h`. Conclude with `Or.inr (by rw [norm_inv]; exact inv_le_one_of_one_le₀ h) }`.

Establish `hz' : IsIntegral V z` using `hz`. Take `⟨v, rfl⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := V) (K := C)).1 hz'`. Conclude with `v.2`.
-/
theorem mem_intO_of_isIntegral {C : Type} [NormedField C] [IsUltrametricDist C] {z : C}
    (hz : IsIntegral ↥(intO C) z) : z ∈ intO C := by
  let V : ValuationSubring C :=
    { intO C with
      mem_or_inv_mem' := fun x => by
        change ‖x‖ ≤ 1 ∨ ‖x⁻¹‖ ≤ 1
        rcases le_total ‖x‖ 1 with h | h
        · exact Or.inl h
        · exact Or.inr (by rw [norm_inv]; exact inv_le_one_of_one_le₀ h) }
  have hz' : IsIntegral V z := hz
  obtain ⟨v, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := C)).1 hz'
  exact v.2

open Polynomial in

/- English proof (translation)
Use `set y := j x with hy`. Use `set a := (algebraMap O C q)⁻¹ with ha`. Establish `hjint : ∀ b, IsIntegral C (j b)` using `fun b => ((Algebra.IsIntegral.isIntegral (R := O) b).map j).tower_top`. Establish `hyint : IsIntegral C y` using `hjint x`. Establish `hroot : ∀ α ∈ (minpoly C y).roots, ∃ k : O, algebraMap O C k = a * α`.

Introduce `α hα`. Use `set D := Algebra.adjoin C (Set.range j) with hD`. Use `haveI : Algebra.IsIntegral C D := Algebra.IsIntegral.adjoin (by rintro _ ⟨b, rfl⟩; exact hjint b)`. Establish `hmem : ∀ b, j b ∈ D` using `fun b => Algebra.subset_adjoin ⟨b, rfl⟩`. Set `yD : D` to `⟨y, hmem x⟩`.

Establish `hnu : yD - algebraMap C D α ∈ nonunits D`. Introduce `hu`. Establish `hu' : IsUnit (y - algebraMap C B₁ α)`. Simplify using `using hu.map D.val`. Establish `hαr : IsRoot (minpoly C y) α` using `(mem_roots (minpoly.ne_zero hyint)).1 hα`.

Establish `hfac` using `mul_divByMonic_eq_iff_isRoot.2 hαr`. Establish `hmon : ((minpoly C y) /ₘ (X - Polynomial.C α)).Monic` using `(monic_X_sub_C α).of_mul_monic_left (by rw [hfac]; exact minpoly.monic hyint)`. Apply `minpoly.aeval_ne_zero_of_dvdNotUnit_minpoly (A := C) (x := y) hyint hmon` to reduce the goal to its premises. Use `⟨hmon.ne_zero, X - Polynomial.C α, ?_, by rw [mul_comm, hfac]⟩` and prove the remaining obligations. Conclude with `not_isUnit_X_sub_C α`.

Establish `h0` using `minpoly.aeval C y`. Rewrite `h0` using `[← hfac, map_mul]`. Simplify `h0)` using `using (hu'.mul_right_eq_zero).1 (by simpa`. Take `⟨M, hMmax, hMmem⟩` from `exists_max_ideal_of_mem_nonunits hnu`. Use `letI : Field (D ⧸ M) := Ideal.Quotient.field M`.

Establish `hbij : Function.Bijective (algebraMap C (D ⧸ M))` using `IsAlgClosed.algebraMap_bijective_of_isIntegral`. Set `e : C ≃ₐ[C] D ⧸ M` to `AlgEquiv.ofBijective (Algebra.ofId C (D ⧸ M)) hbij`. Set `ψ : D →ₐ[C] C` to `e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ C M)`. Establish `hψy : ψ yD = α`. Establish `h1 : Ideal.Quotient.mkₐ C M yD = e α`.

Rewrite using `[Ideal.Quotient.mkₐ_eq_mk]`. Express the relevant statement in the definitionally equal form `_ = Ideal.Quotient.mk M (algebraMap C D α)`. Rewrite using `[Ideal.Quotient.eq]`. Conclude with `hMmem`. Simplify using `only [ψ, AlgHom.comp_apply, h1]`.

Conclude with `e.symm_apply_apply α`. Establish `hcomm : ∀ o : O, (⟨j (algebraMap O B₀ o), hmem _⟩ : D) = algebraMap C D (algebraMap O C o)` using `fun o => by ext; simp [IsScalarTower.algebraMap_apply O C B₁]`. Set `jres : B₀ →+* D` to `(j : B₀ →+* B₁).codRestrict D hmem`. Set `χ₀ : B₀ →ₐ[O] C` to `{ ψ.toRingHom.comp jres with commutes' := fun o => by show ψ ⟨j (algebraMap O B₀ o), hmem _⟩ = _`. Rewrite using `[hcomm]`.

Conclude with `ψ.commutes _ }`. Establish `hχ₀x : χ₀ x = α` using `hψy`. Establish `hval : ∀ b, χ₀ b ∈ (⊥ : Subalgebra O C)` using `fun b => by`. Rewrite using `[Algebra.mem_bot]`. Take `⟨t, ht⟩` from `hcl _ ((Algebra.IsIntegral.isIntegral (R := O) b).map χ₀)`.

Conclude with `⟨t, ht⟩`. Set `eb` to `Algebra.botEquivOfInjective hinj`. Set `χ : B₀ →ₐ[O] O` to `eb.toAlgHom.comp (χ₀.codRestrict ⊥ hval)`. Establish `hback : ∀ s : (⊥ : Subalgebra O C), algebraMap O C (eb s) = s` using `fun s => by`. Establish `h2 : eb.symm (eb s) = s` using `eb.symm_apply_apply s`.

Rewrite `h2` using `[← Algebra.algebraMap_self_apply (eb s), eb.symm.commutes]`. Conclude with `congrArg Subtype.val h2`. Establish `hχx : algebraMap O C (χ x) = α`. Rewrite using `[← hχ₀x]`. Conclude with `hback _`.

Take `⟨k, hk⟩` from `h χ`. Use `⟨k, ?_⟩` and prove the remaining obligations. Establish `hq' : algebraMap O C q ≠ 0` using `(map_ne_zero_iff _ hinj).2 hq`. Rewrite using `[← hχx, hk, map_mul, ha, ← mul_assoc, inv_mul_cancel₀ hq', one_mul]`. Use `set s := (minpoly C y).roots with hs`.

Set `f : C → O` to `fun α => if hh : ∃ k : O, algebraMap O C k = a * α then hh.choose else 0`. Establish `hf : ∀ α ∈ s, algebraMap O C (f α) = a * α` using `fun α hα => by`. Establish `hh` using `hroot α hα`. Simplify using `only [f, dif_pos hh]`. Conclude with `hh.choose_spec`.

Establish `hsplit : minpoly C y = (s.map fun α => X - Polynomial.C α).prod` using `(IsAlgClosed.splits (minpoly C y)).eq_prod_roots_of_monic (minpoly.monic hyint)`. Establish `hzero : (s.map fun α => y - algebraMap C B₁ α).prod = 0`. Establish `h0` using `minpoly.aeval C y`. Rewrite `h0` using `[hsplit, map_multiset_prod, Multiset.map_map]`. Simplify `h0` using `[Function.comp_def]`.

Use `⟨(s.map fun α => X - Polynomial.C (f α)).prod, monic_multiset_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _), ?_⟩` and prove the remaining obligations. Rewrite using `[eval₂_multiset_prod, Multiset.map_map]`. Establish `hfac : ∀ α ∈ s, (eval₂ (algebraMap O B₁) (a • y) ∘ fun α => X - Polynomial.C (f α)) α = algebraMap C B₁ a * (y - algebraMap C B₁ α)` using `fun α hα => by`. Simplify using `only [Function.comp_apply, eval₂_sub, eval₂_X, eval₂_C]`. Rewrite using `[IsScalarTower.algebraMap_apply O C B₁, hf α hα, Algebra.smul_def, map_mul, mul_sub]`.

Rewrite using `[Multiset.map_congr rfl hfac, Multiset.prod_map_mul, hzero, mul_zero]`.
-/
theorem _root_.GlobalTheory.IntegralOfPointValues.isIntegral_inv_smul_of_closed {O C B₀ B₁ : Type*} [CommRing O] [Field C] [IsAlgClosed C]
    [Algebra O C] (hinj : Function.Injective (algebraMap O C))
    (hcl : ∀ z : C, IsIntegral O z → z ∈ (algebraMap O C).range)
    [CommRing B₀] [Algebra O B₀] [Algebra.IsIntegral O B₀] [CommRing B₁] [Algebra C B₁]
    [Algebra O B₁] [IsScalarTower O C B₁] (j : B₀ →ₐ[O] B₁) (x : B₀) (q : O) (hq : q ≠ 0)
    (h : ∀ χ : B₀ →ₐ[O] O, q ∣ χ x) : IsIntegral O ((algebraMap O C q)⁻¹ • j x) := by
  classical
  set y := j x with hy
  set a := (algebraMap O C q)⁻¹ with ha
  have hjint : ∀ b, IsIntegral C (j b) := fun b =>
    ((Algebra.IsIntegral.isIntegral (R := O) b).map j).tower_top
  have hyint : IsIntegral C y := hjint x
  have hroot : ∀ α ∈ (minpoly C y).roots, ∃ k : O, algebraMap O C k = a * α := by
    intro α hα
    set D := Algebra.adjoin C (Set.range j) with hD
    haveI : Algebra.IsIntegral C D :=
      Algebra.IsIntegral.adjoin (by rintro _ ⟨b, rfl⟩; exact hjint b)
    have hmem : ∀ b, j b ∈ D := fun b => Algebra.subset_adjoin ⟨b, rfl⟩
    let yD : D := ⟨y, hmem x⟩
    have hnu : yD - algebraMap C D α ∈ nonunits D := by
      intro hu
      have hu' : IsUnit (y - algebraMap C B₁ α) := by
        simpa using hu.map D.val
      have hαr : IsRoot (minpoly C y) α := (mem_roots (minpoly.ne_zero hyint)).1 hα
      have hfac := mul_divByMonic_eq_iff_isRoot.2 hαr
      have hmon : ((minpoly C y) /ₘ (X - Polynomial.C α)).Monic :=
        (monic_X_sub_C α).of_mul_monic_left (by rw [hfac]; exact minpoly.monic hyint)
      apply minpoly.aeval_ne_zero_of_dvdNotUnit_minpoly (A := C) (x := y) hyint hmon
      · refine ⟨hmon.ne_zero, X - Polynomial.C α, ?_, by rw [mul_comm, hfac]⟩
        exact not_isUnit_X_sub_C α
      · have h0 := minpoly.aeval C y
        rw [← hfac, map_mul] at h0
        simpa using (hu'.mul_right_eq_zero).1 (by simpa using h0)
    obtain ⟨M, hMmax, hMmem⟩ := exists_max_ideal_of_mem_nonunits hnu
    letI : Field (D ⧸ M) := Ideal.Quotient.field M
    have hbij : Function.Bijective (algebraMap C (D ⧸ M)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    let e : C ≃ₐ[C] D ⧸ M := AlgEquiv.ofBijective (Algebra.ofId C (D ⧸ M)) hbij
    let ψ : D →ₐ[C] C := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ C M)
    have hψy : ψ yD = α := by
      have h1 : Ideal.Quotient.mkₐ C M yD = e α := by
        rw [Ideal.Quotient.mkₐ_eq_mk]
        change _ = Ideal.Quotient.mk M (algebraMap C D α)
        rw [Ideal.Quotient.eq]
        exact hMmem
      simp only [ψ, AlgHom.comp_apply, h1]
      exact e.symm_apply_apply α
    have hcomm : ∀ o : O,
        (⟨j (algebraMap O B₀ o), hmem _⟩ : D) = algebraMap C D (algebraMap O C o) :=
      fun o => by ext; simp [IsScalarTower.algebraMap_apply O C B₁]
    let jres : B₀ →+* D := (j : B₀ →+* B₁).codRestrict D hmem
    let χ₀ : B₀ →ₐ[O] C :=
      { ψ.toRingHom.comp jres with
        commutes' := fun o => by
          show ψ ⟨j (algebraMap O B₀ o), hmem _⟩ = _
          rw [hcomm]; exact ψ.commutes _ }
    have hχ₀x : χ₀ x = α := hψy
    have hval : ∀ b, χ₀ b ∈ (⊥ : Subalgebra O C) := fun b => by
      rw [Algebra.mem_bot]
      obtain ⟨t, ht⟩ := hcl _ ((Algebra.IsIntegral.isIntegral (R := O) b).map χ₀)
      exact ⟨t, ht⟩
    let eb := Algebra.botEquivOfInjective hinj
    let χ : B₀ →ₐ[O] O := eb.toAlgHom.comp (χ₀.codRestrict ⊥ hval)
    have hback : ∀ s : (⊥ : Subalgebra O C), algebraMap O C (eb s) = s := fun s => by
      have h2 : eb.symm (eb s) = s := eb.symm_apply_apply s
      rw [← Algebra.algebraMap_self_apply (eb s), eb.symm.commutes] at h2
      exact congrArg Subtype.val h2
    have hχx : algebraMap O C (χ x) = α := by
      rw [← hχ₀x]; exact hback _
    obtain ⟨k, hk⟩ := h χ
    refine ⟨k, ?_⟩
    have hq' : algebraMap O C q ≠ 0 := (map_ne_zero_iff _ hinj).2 hq
    rw [← hχx, hk, map_mul, ha, ← mul_assoc, inv_mul_cancel₀ hq', one_mul]
  set s := (minpoly C y).roots with hs
  let f : C → O := fun α => if hh : ∃ k : O, algebraMap O C k = a * α then hh.choose else 0
  have hf : ∀ α ∈ s, algebraMap O C (f α) = a * α := fun α hα => by
    have hh := hroot α hα
    simp only [f, dif_pos hh]
    exact hh.choose_spec
  have hsplit : minpoly C y = (s.map fun α => X - Polynomial.C α).prod :=
    (IsAlgClosed.splits (minpoly C y)).eq_prod_roots_of_monic (minpoly.monic hyint)
  have hzero : (s.map fun α => y - algebraMap C B₁ α).prod = 0 := by
    have h0 := minpoly.aeval C y
    rw [hsplit, map_multiset_prod, Multiset.map_map] at h0
    simpa [Function.comp_def] using h0
  refine ⟨(s.map fun α => X - Polynomial.C (f α)).prod,
    monic_multiset_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _), ?_⟩
  rw [eval₂_multiset_prod, Multiset.map_map]
  have hfac : ∀ α ∈ s, (eval₂ (algebraMap O B₁) (a • y) ∘ fun α => X - Polynomial.C (f α)) α =
      algebraMap C B₁ a * (y - algebraMap C B₁ α) := fun α hα => by
    simp only [Function.comp_apply, eval₂_sub, eval₂_X, eval₂_C]
    rw [IsScalarTower.algebraMap_apply O C B₁, hf α hα, Algebra.smul_def, map_mul, mul_sub]
  rw [Multiset.map_congr rfl hfac, Multiset.prod_map_mul, hzero, mul_zero]

/- English proof (translation)
Introduce `C _ _ _ B₀ B₁ _ _ _ _ _ _ _ j x q hq h`. Conclude with `isIntegral_inv_smul_of_closed (O := ↥(intO C)) (C := C) Subtype.val_injective (fun z hz => ⟨⟨z, mem_intO_of_isIntegral hz⟩, rfl⟩) j x q hq h`.
-/
theorem isIntegral_inv_smul : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] (B₀ B₁ : Type) [CommRing B₀] [Algebra ↥(intO C) B₀] [Module.Finite ↥(intO C) B₀] [CommRing B₁] [Algebra C B₁] [Algebra ↥(intO C) B₁] [IsScalarTower ↥(intO C) C B₁] (j : B₀ →ₐ[↥(intO C)] B₁) (x : B₀) (q : ↥(intO C)), q ≠ 0 → (∀ χ : B₀ →ₐ[↥(intO C)] ↥(intO C), q ∣ χ x) → IsIntegral ↥(intO C) (((q : C)⁻¹) • j x) := by
  intro C _ _ _ B₀ B₁ _ _ _ _ _ _ _ j x q hq h
  exact isIntegral_inv_smul_of_closed (O := ↥(intO C)) (C := C) Subtype.val_injective
    (fun z hz => ⟨⟨z, mem_intO_of_isIntegral hz⟩, rfl⟩) j x q hq h

end GlobalTheory.IntegralOfPointValues
