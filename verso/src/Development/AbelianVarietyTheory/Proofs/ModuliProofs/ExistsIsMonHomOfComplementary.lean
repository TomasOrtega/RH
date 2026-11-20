import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemicharacterSqEqOneOfSymmetric
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.SectionsPowThetaFunctions
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsUniquePointOfRingHom
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.EqZeroOfForallAlgHomComplex
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsUniqueHomOfLocallyRegular
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsReducedTensorObjComplex
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsTopLePreimageOfISupEqTop
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.AppLESurjective

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LatticeHom

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

/- English proof (translation)
Take `⟨i, hi⟩` from `SymmetricSemicharacter.exists_chart u SymmetricSemicharacter.valueRules hL z`. Use `⟨fun _ => i, ?_⟩` and prove the remaining obligations. Rewrite using `[Cartier.lbPow_U]` and apply the resulting hypothesis.
-/
theorem exists_chart_lbPow (u : HolUnif A L g) (hL : L.IsLB) (n : ℕ) (z : Fin g → ℂ) :
    ∃ k : (lbPow L n).ι, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U k := by
  obtain ⟨i, hi⟩ := SymmetricSemicharacter.exists_chart u SymmetricSemicharacter.valueRules hL z
  refine ⟨fun _ => i, ?_⟩
  rwa [Cartier.lbPow_U]

/- English proof (translation)
The claim follows from `pow_ne_zero n (u.fr_ne _ z (Cartier.lbPow_U L n k ▸ hk))`.
-/
theorem fr_pow_ne_zero (u : HolUnif A L g) (n : ℕ) {z : Fin g → ℂ} {k : (lbPow L n).ι}
    (hk : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U k) : u.fr (k PUnit.unit) z ^ n ≠ 0 :=
  pow_ne_zero n (u.fr_ne _ z (Cartier.lbPow_U L n k ▸ hk))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨k, hk⟩` from `TopologicalSpace.Opens.mem_iSup.1 ((top_le_preimage_iff_mem _ _).1 h)`. Establish `h1` using `(top_le_preimage_basicOpen_iff _ _ _).1 ((top_le_preimage_iff_mem _ _).2 hk)`. Rewrite `h1` using `[hs k z (top_le_preimage_of_valAt'_ne_zero _ h1)]`.

Conclude with `left_ne_zero_of_mul h1`. Introduce `h`. Take `⟨k, hk⟩` from `exists_chart_lbPow u hL n z`. Use `top_le_preimage_mono _ (le_iSup (fun k => A.left.basicOpen (s.f k)) k) ?_` and prove the remaining obligations. Rewrite using `[top_le_preimage_basicOpen_iff, hs k z hk]`.

Conclude with `mul_ne_zero h (fr_pow_ne_zero u n hk)`.
-/
theorem le_preimage_nonzeroLocus_iff (u : HolUnif A L g) (hL : L.IsLB) {n : ℕ} {s : (lbPow L n).Sec}
    {θ : (Fin g → ℂ) → ℂ} (hs : u.IsFnPow n s θ) (z : Fin g → ℂ) :
    ⊤ ≤ (u.ex z).left ⁻¹ᵁ Out.nonzeroLocus s ↔ θ z ≠ 0 := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 ((top_le_preimage_iff_mem _ _).1 h)
    have h1 := (top_le_preimage_basicOpen_iff _ _ _).1 ((top_le_preimage_iff_mem _ _).2 hk)
    rw [hs k z (top_le_preimage_of_valAt'_ne_zero _ h1)] at h1
    exact left_ne_zero_of_mul h1
  · intro h
    obtain ⟨k, hk⟩ := exists_chart_lbPow u hL n z
    refine top_le_preimage_mono _ (le_iSup (fun k => A.left.basicOpen (s.f k)) k) ?_
    rw [top_le_preimage_basicOpen_iff, hs k z hk]
    exact mul_ne_zero h (fr_pow_ne_zero u n hk)

/- English proof (translation)
Take `⟨k, hk⟩` from `exists_chart_lbPow u hL n z`. Establish `hW` using `(top_le_preimage_inf _ _ _).2 ⟨(le_preimage_nonzeroLocus_iff u hL hs z).2 hz, hk⟩`. Establish `h` using `congrArg (valAt' (u.ex z).left _) (hr k)`. Rewrite `h` using `[valAt'_mul, valAt'_res _ _ _ hW, valAt'_res _ _ _ hW, valAt'_res _ _ _ hW, hs k z hk, hs' k z hk, ← _root_.mul_assoc]`. Rewrite using `[mul_right_cancel₀ (fr_pow_ne_zero u n hk) h, mul_div_cancel_right₀ _ hz]`.
-/
theorem valAt'_eq_div_of_mul (u : HolUnif A L g) (hL : L.IsLB) {n : ℕ} {s s' : (lbPow L n).Sec}
    {θ θ' : (Fin g → ℂ) → ℂ} (hs : u.IsFnPow n s θ) (hs' : u.IsFnPow n s' θ') (r : Γ(A.left, Out.nonzeroLocus s))
    (hr : ∀ k, resG _ (inf_le_right : Out.nonzeroLocus s ⊓ (lbPow L n).U k ≤ _) (s'.f k) =
      resG _ inf_le_left r * resG _ inf_le_right (s.f k)) {z : Fin g → ℂ} (hz : θ z ≠ 0) :
    valAt' (u.ex z).left _ r = θ' z / θ z := by
  obtain ⟨k, hk⟩ := exists_chart_lbPow u hL n z
  have hW := (top_le_preimage_inf _ _ _).2 ⟨(le_preimage_nonzeroLocus_iff u hL hs z).2 hz, hk⟩
  have h := congrArg (valAt' (u.ex z).left _) (hr k)
  rw [valAt'_mul, valAt'_res _ _ _ hW, valAt'_res _ _ _ hW, valAt'_res _ _ _ hW, hs k z hk, hs' k z hk,
    ← _root_.mul_assoc] at h
  rw [mul_right_cancel₀ (fr_pow_ne_zero u n hk) h, mul_div_cancel_right₀ _ hz]

/- English proof (translation)
Take `⟨k, hk⟩` from `exists_chart_lbPow u hL n z₀`. Establish `hle` using `A.left.basicOpen_le ((s i).f k)`. Take `⟨v, hv⟩ : IsUnit (resG A.left hle ((s i).f k))` from `RingedSpace.isUnit_res_basicOpen _ _`. Use `⟨A.left.basicOpen ((s i).f k), fun j => resG A.left hle ((s j).f k) * (v⁻¹).val, ?_, fun z hz => ?_⟩` and prove the remaining obligations. Rewrite using `[top_le_preimage_basicOpen_iff, hs i k z₀ hk]`.

Conclude with `mul_ne_zero h0 (fr_pow_ne_zero u n hk)`. Establish `hk'` using `top_le_preimage_mono _ hle hz`. Establish `h1` using `(top_le_preimage_basicOpen_iff _ _ _).1 hz`. Rewrite `h1` using `[hs i k z hk']`. Use `⟨left_ne_zero_of_mul h1, fun j => ?_⟩` and prove the remaining obligations.

Rewrite using `[valAt'_mul, valAt'_units_inv _ hz, hv, valAt'_res _ _ _ hz, valAt'_res _ _ _ hz, hs i k z hk', hs j k z hk', ← div_eq_mul_inv, mul_div_mul_right _ _ (right_ne_zero_of_mul h1)]`.
-/
theorem exists_regular_quotients (u : HolUnif A L g) (hL : L.IsLB) {n : ℕ} {κ : Type*} {s : κ → (lbPow L n).Sec}
    {θ : κ → (Fin g → ℂ) → ℂ} (hs : ∀ j, u.IsFnPow n (s j) (θ j)) (i : κ) {z₀ : Fin g → ℂ} (h0 : θ i z₀ ≠ 0) :
    ∃ (U : A.left.Opens) (ρ : κ → Γ(A.left, U)), ⊤ ≤ (u.ex z₀).left ⁻¹ᵁ U ∧
      ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ U → θ i z ≠ 0 ∧ ∀ j, valAt' (u.ex z).left U (ρ j) = θ j z / θ i z := by
  obtain ⟨k, hk⟩ := exists_chart_lbPow u hL n z₀
  have hle := A.left.basicOpen_le ((s i).f k)
  obtain ⟨v, hv⟩ : IsUnit (resG A.left hle ((s i).f k)) := RingedSpace.isUnit_res_basicOpen _ _
  refine ⟨A.left.basicOpen ((s i).f k), fun j => resG A.left hle ((s j).f k) * (v⁻¹).val, ?_, fun z hz => ?_⟩
  · rw [top_le_preimage_basicOpen_iff, hs i k z₀ hk]
    exact mul_ne_zero h0 (fr_pow_ne_zero u n hk)
  · have hk' := top_le_preimage_mono _ hle hz
    have h1 := (top_le_preimage_basicOpen_iff _ _ _).1 hz
    rw [hs i k z hk'] at h1
    refine ⟨left_ne_zero_of_mul h1, fun j => ?_⟩
    rw [valAt'_mul, valAt'_units_inv _ hz, hv, valAt'_res _ _ _ hz, valAt'_res _ _ _ hz, hs i k z hk', hs j k z hk',
      ← div_eq_mul_inv, mul_div_mul_right _ _ (right_ne_zero_of_mul h1)]

/- English proof (translation)
Establish `hr : IsReduced A.left` using `isReduced_of_smooth_complex _ A.hom inferInstance`. Establish `h0 : u.ex 0 = η[A]`. Rewrite using `[(u.ker 0).2 u.Λ.zero_mem, Hom.one_def, toUnit_unit, Category.id_comp]`. Establish `h0' : u'.ex 0 = η[A']`. Rewrite using `[(u'.ker 0).2 u'.Λ.zero_mem, Hom.one_def, toUnit_unit, Category.id_comp]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← h0, ← hf, map_zero, h0']`. Establish `hft : LocallyOfFiniteType (A ⊗ A).hom`. Express the relevant statement in the definitionally equal form `LocallyOfFiniteType (pullback.fst A.hom A.hom ≫ A.hom)`. Use `infer_instance`.

Use `TorusEnd.hom_ext_of_points (existsUnique_hom_of_locally_regular existsUnique_point_of_ringHom (eq_of_valAt'_eq valAt'_rules existsUnique_point_of_ringHom) A' (A ⊗ A) (isReduced_tensorObj_complex A A hr hr inferInstance inferInstance) hft) fun y => ?_` and prove the remaining obligations. Take `⟨z, hz⟩` from `u.ex_onto (y ≫ fst A A)`. Take `⟨w, hw⟩` from `u.ex_onto (y ≫ snd A A)`. Apply the tactic sequence `have hy : y = lift (u.ex z) (u.ex w) := by ext1 <;> simp [hz, hw]`. Rewrite using `[hy, ← Category.assoc, ← Hom.mul_def, ← u.ex_add, ← hf, map_add, u'.ex_add, Hom.mul_def, ← Category.assoc, lift_map, ← hf, ← hf]`.
-/
theorem isMonHom_of_lift {A' : Over (Sp ℂ)} [GrpObj A'] {L' : LB A'.left} {g' : ℕ} (u : HolUnif A L g)
    (u' : HolUnif A' L' g') [Smooth A.hom] (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (f : A ⟶ A')
    (hf : ∀ z, u'.ex (F z) = u.ex z ≫ f) : IsMonHom f := by
  have hr : IsReduced A.left := isReduced_of_smooth_complex _ A.hom inferInstance
  have h0 : u.ex 0 = η[A] := by
    rw [(u.ker 0).2 u.Λ.zero_mem, Hom.one_def, toUnit_unit, Category.id_comp]
  have h0' : u'.ex 0 = η[A'] := by
    rw [(u'.ker 0).2 u'.Λ.zero_mem, Hom.one_def, toUnit_unit, Category.id_comp]
  refine ⟨?_, ?_⟩
  · rw [← h0, ← hf, map_zero, h0']
  · have hft : LocallyOfFiniteType (A ⊗ A).hom := by
      change LocallyOfFiniteType (pullback.fst A.hom A.hom ≫ A.hom)
      infer_instance
    refine TorusEnd.hom_ext_of_points (existsUnique_hom_of_locally_regular existsUnique_point_of_ringHom
      (eq_of_valAt'_eq valAt'_rules existsUnique_point_of_ringHom) A' (A ⊗ A)
      (isReduced_tensorObj_complex A A hr hr inferInstance inferInstance) hft) fun y => ?_
    obtain ⟨z, hz⟩ := u.ex_onto (y ≫ fst A A)
    obtain ⟨w, hw⟩ := u.ex_onto (y ≫ snd A A)
    have hy : y = lift (u.ex z) (u.ex w) := by
      ext1 <;> simp [hz, hw]
    rw [hy, ← Category.assoc, ← Hom.mul_def, ← u.ex_add, ← hf, map_add, u'.ex_add, Hom.mul_def, ← Category.assoc,
      lift_map, ← hf, ← hf]

/- English proof (translation)
Establish `hsm` using `P.isAb.smooth`. Establish `hr : IsReduced P.A.left` using `isReduced_of_smooth_complex _ P.A.hom hsm`. Set `Φ : (𝟙_ (Over (Sp ℂ)) ⟶ P.A) → (𝟙_ (Over (Sp ℂ)) ⟶ P'.A)` to `fun y => u'.ex (F (Function.surjInv u.ex_onto y))`. Establish `hΦ : ∀ z, Φ (u.ex z) = u'.ex (F z)` using `fun z => by`. Establish `h1 : Function.surjInv u.ex_onto (u.ex z) - z ∈ u.Λ`.

Rewrite using `[← u.ker]`. Use `u.ex_add (Function.surjInv u.ex_onto (u.ex z) - z) z` as an intermediate fact. Rewrite `this` using `[sub_add_cancel, Function.surjInv_eq u.ex_onto]`. Conclude with `mul_eq_right.1 this.symm`. Use `SectionTheta.ex_add_lattice u' (F z) ⟨_, hF _ h1⟩` as an intermediate fact.

Rewrite `this` using `[← map_add, add_sub_cancel]`. Then use the resulting hypothesis. Take `⟨m, s, hcov, hD⟩` from `veryAmple_lbPow hamp ℂ P' 4 le_rfl`. Use `choose θ hθ hθs using fun j => hfn 4 (s j)`. Take `⟨f, hf, -⟩` from `existsUnique_hom_of_locally_regular existsUnique_point_of_ringHom (eq_of_valAt'_eq valAt'_rules existsUnique_point_of_ringHom) P'.A P.A hr inferInstance Φ fun y => by`. Take `⟨z₀, rfl⟩` from `u.ex_onto y`.

Take `⟨i, hi⟩` from `TorusEnd.exists_top_le_preimage_of_iSup_eq_top (u'.ex (F z₀)).left _ hcov`. Take `⟨haff, r, hr, hgen⟩` from `hD i`. Establish `hmem` using `le_preimage_nonzeroLocus_iff u' P'.isLB (hθs i)`. Take `⟨G, hG0, hG⟩` from `hd z₀`. Use `choose t ht using fun j => hsec d _ (hG _ (hθ j))`.

Take `⟨U, ρ, hU0, hU⟩` from `exists_regular_quotients u P.isLB ht i (mul_ne_zero ((hmem _).1 hi) hG0)`. Use `⟨U, _, hU0, haff, fun y' hy' => ?_, fun ψ => ?_⟩` and prove the remaining obligations. Take `⟨z, rfl⟩` from `u.ex_onto y'`. Rewrite using `[hΦ]`. Conclude with `(hmem _).2 (left_ne_zero_of_mul (hU z hy').1)`.

Take `⟨Q, rfl⟩` from `hgen ψ`. Use `⟨MvPolynomial.eval₂ (RingHom.comp (P.A.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) ρ Q, fun y' hy' => ?_⟩` and prove the remaining obligations. Take `⟨z, rfl⟩` from `u.ex_onto y'`. Establish `h1` using `left_ne_zero_of_mul (hU z hy').1`. Establish `h2` using `right_ne_zero_of_mul (hU z hy').1`.

Rewrite using `[hΦ, TorusEnd.valAt'_eval₂ _ _ hy', TorusEnd.valAt'_eval₂ _ _ ((hmem _).2 h1)]`. Use `congr 2`. Use function extensionality and compare the values at `j`. Rewrite using `[(hU z hy').2 j, valAt'_eq_div_of_mul u' P'.isLB (hθs i) (hθs j) (r j) (hr j) h1, mul_div_mul_right _ _ h2]`. Establish `hfe : ∀ z, u'.ex (F z) = u.ex z ≫ f` using `fun z => by rw [hf, hΦ]`.

Conclude with `⟨f, isMonHom_of_lift u u' F f hfe, hfe⟩`.
-/
theorem exists_isMonHom_of_complementary (hamp : Out.AmpleSt) (P P' : Out.PolAV (Sp ℂ)) {g g' : ℕ}
    (u : HolUnif P.A P.L g) (u' : HolUnif P'.A P'.L g') {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    {Hm' : Matrix (Fin g') (Fin g') ℂ} {χ' : u'.Λ → ℂ}
    (hsec : ∀ (k : ℕ) θ, u.IsThetaFn Hm χ k θ → ∃ s, u.IsFnPow k s θ)
    (hfn : ∀ (k : ℕ) s, ∃ θ, u'.IsThetaFn Hm' χ' k θ ∧ u'.IsFnPow k s θ)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hF : ∀ l ∈ u.Λ, F l ∈ u'.Λ) (d : ℕ)
    (hd : ∀ z₀, ∃ G : (Fin g → ℂ) → ℂ, G z₀ ≠ 0 ∧
      ∀ θ, u'.IsThetaFn Hm' χ' 4 θ → u.IsThetaFn Hm χ d (fun z => θ (F z) * G z)) :
    ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u'.ex (F z) = u.ex z ≫ f := by
  have hsm := P.isAb.smooth
  have hr : IsReduced P.A.left := isReduced_of_smooth_complex _ P.A.hom hsm
  let Φ : (𝟙_ (Over (Sp ℂ)) ⟶ P.A) → (𝟙_ (Over (Sp ℂ)) ⟶ P'.A) := fun y => u'.ex (F (Function.surjInv u.ex_onto y))
  have hΦ : ∀ z, Φ (u.ex z) = u'.ex (F z) := fun z => by
    have h1 : Function.surjInv u.ex_onto (u.ex z) - z ∈ u.Λ := by
      rw [← u.ker]
      have := u.ex_add (Function.surjInv u.ex_onto (u.ex z) - z) z
      rw [sub_add_cancel, Function.surjInv_eq u.ex_onto] at this
      exact mul_eq_right.1 this.symm
    have := SectionTheta.ex_add_lattice u' (F z) ⟨_, hF _ h1⟩
    rwa [← map_add, add_sub_cancel] at this
  obtain ⟨m, s, hcov, hD⟩ := veryAmple_lbPow hamp ℂ P' 4 le_rfl
  choose θ hθ hθs using fun j => hfn 4 (s j)
  obtain ⟨f, hf, -⟩ := existsUnique_hom_of_locally_regular existsUnique_point_of_ringHom
      (eq_of_valAt'_eq valAt'_rules existsUnique_point_of_ringHom) P'.A P.A hr inferInstance Φ fun y => by
    obtain ⟨z₀, rfl⟩ := u.ex_onto y
    obtain ⟨i, hi⟩ := TorusEnd.exists_top_le_preimage_of_iSup_eq_top (u'.ex (F z₀)).left _ hcov
    obtain ⟨haff, r, hr, hgen⟩ := hD i
    have hmem := le_preimage_nonzeroLocus_iff u' P'.isLB (hθs i)
    obtain ⟨G, hG0, hG⟩ := hd z₀
    choose t ht using fun j => hsec d _ (hG _ (hθ j))
    obtain ⟨U, ρ, hU0, hU⟩ := exists_regular_quotients u P.isLB ht i (mul_ne_zero ((hmem _).1 hi) hG0)
    refine ⟨U, _, hU0, haff, fun y' hy' => ?_, fun ψ => ?_⟩
    · obtain ⟨z, rfl⟩ := u.ex_onto y'
      rw [hΦ]
      exact (hmem _).2 (left_ne_zero_of_mul (hU z hy').1)
    · obtain ⟨Q, rfl⟩ := hgen ψ
      refine ⟨MvPolynomial.eval₂ (RingHom.comp (P.A.hom.appLE ⊤ _ le_top).hom
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) ρ Q, fun y' hy' => ?_⟩
      obtain ⟨z, rfl⟩ := u.ex_onto y'
      have h1 := left_ne_zero_of_mul (hU z hy').1
      have h2 := right_ne_zero_of_mul (hU z hy').1
      rw [hΦ, TorusEnd.valAt'_eval₂ _ _ hy', TorusEnd.valAt'_eval₂ _ _ ((hmem _).2 h1)]
      congr 2
      funext j
      rw [(hU z hy').2 j, valAt'_eq_div_of_mul u' P'.isLB (hθs i) (hθs j) (r j) (hr j) h1, mul_div_mul_right _ _ h2]
  have hfe : ∀ z, u'.ex (F z) = u.ex z ≫ f := fun z => by rw [hf, hΦ]
  exact ⟨f, isMonHom_of_lift u u' F f hfe, hfe⟩

end GlobalTheory.LatticeHom
