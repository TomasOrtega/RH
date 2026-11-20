import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.CrossGlobal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.ValuationAtUnit

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

def ValAtUnit {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {H : Geo.Tor.Host E} {t : Geo.Tor.SAB H (Spec (CommRingCat.of V))}
    (P : Geo.Tor.PELUnif (maximalIdeal V) t) (k : ℕ) (s : P.U.SecK k) (x : FractionRing V) : Prop :=
  ∃ τ : LB.Gen (LB.LinComb P.U.LG.L (K := Fin 1) (fun _ => unitK ≫ gK) (fun _ => (k : ℤ))), τ.IsGen ∧
    LB.Gen.Corr P.U.LG.L _ _ _ _ τ
      (LB.pullGen P.U.LG.L _ _ (GeneratorPullback.powGen P.U.LG.L _ _ P.U.LG.rig k) (jK V)) ∧
    ∀ j, rs (wchart_comp_le (L := P.U.LG.L) (fun _ : Fin 1 => gK) unitK j) ((unitK.app _).hom (s.f j)) =
      ((Spec (CommRingCat.of (FractionRing V))).presheaf.map (homOfLE le_top).op).hom
          ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom x) * (τ.s j).val

/- English proof (translation)
Establish `hz : (𝟙 (Spec (CommRingCat.of F)) : _) z ∈ (⊤ : (Spec (CommRingCat.of F)).Opens)` using `trivial`. Unfold `gs at h`. Rewrite `h` using `[dif_pos hz, dif_pos hz]`. Establish `h2 : (Scheme.Hom.app (𝟙 (Spec (CommRingCat.of F))) ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) = (Scheme.Hom.app (𝟙 (Spec (CommRingCat.of F))) ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c')` using `by first`. Consider the case `exact AlgebraicGeometry.germ_injective_of_isIntegral _ _ hz h`.

Consider the case `exact AlgebraicGeometry.germ_injective_of_isIntegral _ _ _ hz h`. Consider the case `exact AlgebraicGeometry.germ_injective_of_isIntegral _ hz h`. Consider the case `exact AlgebraicGeometry.germ_injective_of_isIntegral (Spec (CommRingCat.of F)) h`. Establish `h2' : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c = (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c'` using `by first`. Consider the case `exact h2`.

Consider the case `simpa only [RingHom.id_apply] using h2`. Consider the case `(simp only [Scheme.Hom.id_app, CommRingCat.hom_id, RingHom.id_apply] at h2; exact h2)`. Establish `h3` using `congrArg (fun y => (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom y) h2'`. Simplify using `using h3`.
-/
theorem eq_of_gs_eq {F : Type} [Field F] (z : Spec (CommRingCat.of F)) (c c' : F)
    (h : gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) =
      gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c')) : c = c' := by
  have hz : (𝟙 (Spec (CommRingCat.of F)) : _) z ∈ (⊤ : (Spec (CommRingCat.of F)).Opens) := trivial
  unfold gs at h
  rw [dif_pos hz, dif_pos hz] at h
  have h2 : (Scheme.Hom.app (𝟙 (Spec (CommRingCat.of F))) ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) =
      (Scheme.Hom.app (𝟙 (Spec (CommRingCat.of F))) ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c') := by
    first
    | exact AlgebraicGeometry.germ_injective_of_isIntegral _ _ hz h
    | exact AlgebraicGeometry.germ_injective_of_isIntegral _ _ _ hz h
    | exact AlgebraicGeometry.germ_injective_of_isIntegral _ hz h
    | exact AlgebraicGeometry.germ_injective_of_isIntegral (Spec (CommRingCat.of F)) h
  have h2' : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c = (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c' := by
    first
    | exact h2
    | simpa only [RingHom.id_apply] using h2
    | (simp only [Scheme.Hom.id_app, CommRingCat.hom_id, RingHom.id_apply] at h2; exact h2)
  have h3 := congrArg (fun y => (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom y) h2'
  simpa using h3

/- English proof (translation)
Take `⟨τ, -, cτ, eτ⟩` from `h`. Take `⟨τ', -, cτ', eτ'⟩` from `h'`. Take `⟨z⟩ : Nonempty (Spec (CommRingCat.of F))` from `inferInstanceAs (Nonempty (PrimeSpectrum F))`. Use `choose J hJ using fun χ : Spec (CommRingCat.of F) ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (χ z)`. Establish `hm` using `Good.mem hJ (fun i => (DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i) (𝟙 _)`.

Establish `e` using `congrArg (gs (𝟙 _) z _) ((eτ (fun i => J (𝟙 _ ≫ (DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i))).symm.trans (eτ' (fun i => J (𝟙 _ ≫ (DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i))))`. Establish `A` using `(gs_mul (𝟙 _) z _ hm _ _).symm.trans (e.trans (gs_mul (𝟙 _) z _ hm _ _))`. Set `r0 : Spec (CommRingCat.of F) ⟶ (TF (R` to `V) F).left := 𝟙 _`. Establish `B : gs (𝟙 (Spec (CommRingCat.of F))) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * (val τ r0 z J).val = gs (𝟙 (Spec (CommRingCat.of F))) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c') * (val τ' r0 z J).val`. Apply the tactic sequence `convert A using 2 <;> first`.

Consider the case `exact (gs_res (𝟙 _) z le_top hm _).symm`. Consider the case `exact (gs_unit (𝟙 _) z _ hm _).symm`. Rewrite `B` using `[val_corr hJ cτ, val_corr hJ cτ']`. Conclude with `eq_of_gs_eq z c c' (mul_right_cancel₀ (Units.ne_zero _) B)`.
-/
theorem valueAtZero_unique_of_stalk_reading {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F] {k : ℕ}
    {α : D.toPre.X} {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))} {c c' : F}
    (h : Val0 D F k α s c) (h' : Val0 D F k α s c') : c = c' := by
  obtain ⟨τ, -, cτ, eτ⟩ := h
  obtain ⟨τ', -, cτ', eτ'⟩ := h'
  obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of F)) := inferInstanceAs (Nonempty (PrimeSpectrum F))
  choose J hJ using fun χ : Spec (CommRingCat.of F) ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (χ z)
  have hm := Good.mem hJ (fun i => (DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i) (𝟙 _)
  have e := congrArg (gs (𝟙 _) z _)
    ((eτ (fun i => J (𝟙 _ ≫ (DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i))).symm.trans
      (eτ' (fun i => J (𝟙 _ ≫ (DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i))))
  have A := (gs_mul (𝟙 _) z _ hm _ _).symm.trans (e.trans (gs_mul (𝟙 _) z _ hm _ _))
  let r0 : Spec (CommRingCat.of F) ⟶ (TF (R := V) F).left := 𝟙 _
  have B : gs (𝟙 (Spec (CommRingCat.of F))) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) *
        (val τ r0 z J).val =
      gs (𝟙 (Spec (CommRingCat.of F))) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c') *
        (val τ' r0 z J).val := by
    convert A using 2 <;> first
      | exact (gs_res (𝟙 _) z le_top hm _).symm
      | exact (gs_unit (𝟙 _) z _ hm _).symm
  rw [val_corr hJ cτ, val_corr hJ cτ'] at B
  exact eq_of_gs_eq z c c' (mul_right_cancel₀ (Units.ne_zero _) B)

/- English proof (translation)
Take `⟨x₁, h₁, s₁⟩` from `hx`. Take `⟨x₂, h₂, s₂⟩` from `hx'`. Take `rfl : x₁ = x₂` from `funext fun α => valueAtZero_unique_of_stalk_reading (h₁ α) (h₂ α)`. Assume the negation of the conclusion as `hne`. Establish `hd : x - x' ≠ 0` using `sub_ne_zero.2 hne`.

Take `⟨r, hr⟩` from `WithTop.ne_top_iff_exists.1 (fun h => hd ((AddValuation.top_iff v).1 h))`. Take `⟨S₁, hS₁⟩` from `s₁ (r + 1)`. Take `⟨S₂, hS₂⟩` from `s₂ (r + 1)`. Establish `a₁` using `hS₁ (S₁ ∪ S₂) Finset.subset_union_left`. Establish `a₂` using `hS₂ (S₁ ∪ S₂) Finset.subset_union_right`.

Establish `key : x - x' = (x - ∑ α ∈ S₁ ∪ S₂, x₁ α) - (x' - ∑ α ∈ S₁ ∪ S₂, x₁ α)` using `by ring`. Establish `hle` using `AddValuation.map_sub v (x - ∑ α ∈ S₁ ∪ S₂, x₁ α) (x' - ∑ α ∈ S₁ ∪ S₂, x₁ α)`. Rewrite `hle` using `[← key, ← hr]`. Use `le_trans (le_min a₁ a₂) hle` as an intermediate fact. Rewrite `this` using `[WithTop.coe_le_coe]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem valAt0_unique {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {H : Geo.Tor.Host E} {t : Geo.Tor.SAB H (Spec (CommRingCat.of V))}
    (P : Geo.Tor.PELUnif (maximalIdeal V) t) (ϖ : V) (hϖ : Irreducible ϖ)
    (v : AddValuation (FractionRing V) (WithTop ℚ)) (hv : ValOver ϖ (FractionRing V) v) {k : ℕ}
    (F : Fam P.D.toPre (FractionRing V) k) (x x' : FractionRing V)
    (hx : ValAt0 P.D (FractionRing V) v k F x) (hx' : ValAt0 P.D (FractionRing V) v k F x') : x = x' := by
  classical
  obtain ⟨x₁, h₁, s₁⟩ := hx
  obtain ⟨x₂, h₂, s₂⟩ := hx'
  obtain rfl : x₁ = x₂ := funext fun α => valueAtZero_unique_of_stalk_reading (h₁ α) (h₂ α)
  by_contra hne
  have hd : x - x' ≠ 0 := sub_ne_zero.2 hne
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (fun h => hd ((AddValuation.top_iff v).1 h))
  obtain ⟨S₁, hS₁⟩ := s₁ (r + 1)
  obtain ⟨S₂, hS₂⟩ := s₂ (r + 1)
  have a₁ := hS₁ (S₁ ∪ S₂) Finset.subset_union_left
  have a₂ := hS₂ (S₁ ∪ S₂) Finset.subset_union_right
  have key : x - x' = (x - ∑ α ∈ S₁ ∪ S₂, x₁ α) - (x' - ∑ α ∈ S₁ ∪ S₂, x₁ α) := by ring
  have hle := AddValuation.map_sub v (x - ∑ α ∈ S₁ ∪ S₂, x₁ α) (x' - ∑ α ∈ S₁ ∪ S₂, x₁ α)
  rw [← key, ← hr] at hle
  have := le_trans (le_min a₁ a₂) hle
  rw [WithTop.coe_le_coe] at this
  linarith

/- English proof (translation)
Set `r : ∀ j, Γ(Y, M.U j)` to `fun j => s.f j * ((τ.s j)⁻¹ : Γ(Y, M.U j)ˣ).val`. Establish `compat : ∀ i j, (Y.presheaf.map (homOfLE (inf_le_left : M.U i ⊓ M.U j ≤ M.U i)).op).hom (r i) = (Y.presheaf.map (homOfLE (inf_le_right : M.U i ⊓ M.U j ≤ M.U j)).op).hom (r j)`. Introduce `i j`. Establish `hs` using `s.compat i j`. Establish `hti : (Y.presheaf.map (homOfLE (inf_le_left : M.U i ⊓ M.U j ≤ M.U i)).op).hom ((τ.s i)⁻¹ : Γ(Y, M.U i)ˣ).val = (Y.presheaf.map (homOfLE (inf_le_right : M.U i ⊓ M.U j ≤ M.U j)).op).hom ((τ.s j)⁻¹ : Γ(Y, M.U j)ˣ).val * ((M.g i j)⁻¹ : Γ(Y, M.U i ⊓ M.U j)ˣ).val`.

Use `congrArg (fun u => (u⁻¹ : Γ(Y, M.U i ⊓ M.U j)ˣ).val) (hτ i j)` as an intermediate fact. Simplify using `only [mul_inv_rev, Units.val_mul] at this`. Conclude with `this`. Establish `hg : (M.g i j : Γ(Y, M.U i ⊓ M.U j)ˣ).val * ((M.g i j)⁻¹ : Γ(Y, M.U i ⊓ M.U j)ˣ).val = 1`. Rewrite using `[← Units.val_mul, _root_.mul_inv_cancel, Units.val_one]`.

Simplify using `only [r, map_mul]`. Rewrite using `[hs, hti]`. Take the linear combination `((Y.presheaf.map (homOfLE (inf_le_right : M.U i ⊓ M.U j ≤ M.U j)).op).hom (s.f j) * (Y.presheaf.map (homOfLE (inf_le_right : M.U i ⊓ M.U j ≤ M.U j)).op).hom ((τ.s j)⁻¹ : Γ(Y, M.U j)ˣ).val) * hg`. Take `⟨a, ha, -⟩` from `Y.sheaf.existsUnique_gluing' M.U ⊤ (fun j => homOfLE le_top) hc.ge r compat`. Establish `ha' : ∀ j, (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom a = r j` using `ha`.

Use `⟨a, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[ha' j]`. Simplify using `only [r]`. Rewrite using `[_root_.mul_assoc, ← Units.val_mul, _root_.inv_mul_cancel, Units.val_one, _root_.mul_one]`.
-/
theorem exists_glue_ratio {Y : Scheme.{0}} {M : LB Y} (hc : ⨆ j, M.U j = ⊤) (s : LB.Sec M) (τ : LB.Gen M)
    (hτ : τ.IsGen) : ∃ a : Γ(Y, ⊤), ∀ j, s.f j = (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom a * (τ.s j).val := by
  let r : ∀ j, Γ(Y, M.U j) := fun j => s.f j * ((τ.s j)⁻¹ : Γ(Y, M.U j)ˣ).val
  have compat : ∀ i j, (Y.presheaf.map (homOfLE (inf_le_left : M.U i ⊓ M.U j ≤ M.U i)).op).hom (r i) =
      (Y.presheaf.map (homOfLE (inf_le_right : M.U i ⊓ M.U j ≤ M.U j)).op).hom (r j) := by
    intro i j
    have hs := s.compat i j
    have hti : (Y.presheaf.map (homOfLE (inf_le_left : M.U i ⊓ M.U j ≤ M.U i)).op).hom ((τ.s i)⁻¹ : Γ(Y, M.U i)ˣ).val =
        (Y.presheaf.map (homOfLE (inf_le_right : M.U i ⊓ M.U j ≤ M.U j)).op).hom ((τ.s j)⁻¹ : Γ(Y, M.U j)ˣ).val *
          ((M.g i j)⁻¹ : Γ(Y, M.U i ⊓ M.U j)ˣ).val := by
      have := congrArg (fun u => (u⁻¹ : Γ(Y, M.U i ⊓ M.U j)ˣ).val) (hτ i j)
      simp only [mul_inv_rev, Units.val_mul] at this
      exact this
    have hg : (M.g i j : Γ(Y, M.U i ⊓ M.U j)ˣ).val * ((M.g i j)⁻¹ : Γ(Y, M.U i ⊓ M.U j)ˣ).val = 1 := by
      rw [← Units.val_mul, _root_.mul_inv_cancel, Units.val_one]
    simp only [r, map_mul]
    rw [hs, hti]
    linear_combination ((Y.presheaf.map (homOfLE (inf_le_right : M.U i ⊓ M.U j ≤ M.U j)).op).hom (s.f j) *
      (Y.presheaf.map (homOfLE (inf_le_right : M.U i ⊓ M.U j ≤ M.U j)).op).hom ((τ.s j)⁻¹ : Γ(Y, M.U j)ˣ).val) * hg
  obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' M.U ⊤ (fun j => homOfLE le_top) hc.ge r compat
  have ha' : ∀ j, (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom a = r j := ha
  refine ⟨a, fun j => ?_⟩
  rw [ha' j]
  simp only [r]
  rw [_root_.mul_assoc, ← Units.val_mul, _root_.inv_mul_cancel, Units.val_one, _root_.mul_one]

/- English proof (translation)
Establish `hL : P.U.LG.L.IsLB` using `P.U.LG.isLB`. Take `⟨τ, gτ, vτ⟩` from `exists_gen hL (φ' := fun _ : Fin 1 => unitK ≫ gK) (ε' := fun _ => (k : ℤ)) (fun U _ h => by`. Establish `hu : (unitK : _ ⟶ pullback t.G.hom (jK V)) ≫ gK = jK V ≫ eSec t.G` using `pullback.lift_fst _ _ _`. Rewrite using `[Fintype.prod_unique, Fin.prod_univ_one, hu, _root_.mul_one])`. Use the proof step `(LB.pullGen P.U.LG.L _ _ (GeneratorPullback.powGen P.U.LG.L _ _ P.U.LG.rig k) (jK V))`.

Use the proof step `(pullGen_isGen _ _ _ _ (powGen_isGen _ _ _ _ P.U.LG.rigGen k) _)`. Establish `cτ` using `corr_of_val hL fun y J hJ => vτ _ (𝟙 _) y J hJ`. Take `⟨a, ha⟩` from `exists_glue_ratio (linComb_cover _ hL _ _) (pullSec P.U.LG.L (fun _ : Fin 1 => gK) (fun _ => (k : ℤ)) s unitK) τ gτ`. Take `⟨x, hx⟩` from `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv).2 a`. Use `⟨x, τ, gτ, cτ, fun j => ?_⟩` and prove the remaining obligations.

Establish `e` using `ha j`. Rewrite `e` using `[← hx]`. Conclude with `e`.
-/
theorem exists_valAtUnit {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {H : Geo.Tor.Host E} {t : Geo.Tor.SAB H (Spec (CommRingCat.of V))}
    (P : Geo.Tor.PELUnif (maximalIdeal V) t) (k : ℕ) (s : P.U.SecK k) :
    ∃ x, ValAtUnit P k s x := by
  have hL : P.U.LG.L.IsLB := P.U.LG.isLB
  obtain ⟨τ, gτ, vτ⟩ := exists_gen hL (φ' := fun _ : Fin 1 => unitK ≫ gK) (ε' := fun _ => (k : ℤ))
    (fun U _ h => by
      have hu : (unitK : _ ⟶ pullback t.G.hom (jK V)) ≫ gK = jK V ≫ eSec t.G := pullback.lift_fst _ _ _
      rw [Fintype.prod_unique, Fin.prod_univ_one, hu, _root_.mul_one])
    (LB.pullGen P.U.LG.L _ _ (GeneratorPullback.powGen P.U.LG.L _ _ P.U.LG.rig k) (jK V))
    (pullGen_isGen _ _ _ _ (powGen_isGen _ _ _ _ P.U.LG.rigGen k) _)
  have cτ := corr_of_val hL fun y J hJ => vτ _ (𝟙 _) y J hJ
  obtain ⟨a, ha⟩ := exists_glue_ratio (linComb_cover _ hL _ _)
    (pullSec P.U.LG.L (fun _ : Fin 1 => gK) (fun _ => (k : ℤ)) s unitK) τ gτ
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv).2 a
  refine ⟨x, τ, gτ, cτ, fun j => ?_⟩
  have e := ha j
  rw [← hx] at e
  exact e

end ReciprocityTheory.ChartRestriction.G.DVR.ValuationAtUnit
