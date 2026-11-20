import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.TriCanon
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.MapDiagonalRepMatrixEq

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

namespace UpperTheory.V.UnitaryThreeInertia

/- English proof (translation)
Use `ext1 g`. Simplify using `[conjBy]`.
-/
private theorem conjBy_one_inv_eq_self {R D : Type} [CommRing R] [Group D] (r : D →* GG 3 R) :
    conjBy (1 : GL (Fin 3) R)⁻¹ r = r := by
  ext1 g
  simp [conjBy]

/- English proof (translation)
Simplify using `[GG.mat, hg]`.
-/
private theorem rep_mul_matrix_of_trivial_sign {R D : Type} [CommRing R] [Group D] (r : D →* GG 3 R) (g h : D) (hg : (r g).right = 1) :
    (r (g * h)).mat = (r g).mat * (r h).mat := by
  simp [GG.mat, hg]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single a (fun c _ hc => by rw [hX hc.symm, zero_mul]) (fun hn => absurd (Finset.mem_univ a) hn)]`.
-/
private theorem diagonal_mul_diag_entry {R : Type} [CommRing R] {X : Matrix (Fin 3) (Fin 3) R} (hX : X.IsDiag)
    (Y : Matrix (Fin 3) (Fin 3) R) (a : Fin 3) : (X * Y) a a = X a a * Y a a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a (fun c _ hc => by rw [hX hc.symm, zero_mul])
    (fun hn => absurd (Finset.mem_univ a) hn)]

private def kap {R D : Type} [CommRing R] [Group D] (η : D →* ℤˣ) (r : D →* GG 3 R) (hm : HasMult η r)
    (hd : ∀ g, η g = 1 → (r g).mat.IsDiag) (a : Fin 3) : η.ker →* R where
  toFun g := (r g).mat a a
  map_one' := by simp [GG.mat]
  map_mul' g h := by
    rw [Subgroup.coe_mul, rep_mul_matrix_of_trivial_sign r _ _ ((hm g).trans g.2), diagonal_mul_diag_entry (hd g g.2)]

/- English proof (translation)
Establish `e` using `mul_geom_sum (u : R) N`. Rewrite `e` using `[← Units.val_pow_eq_pow_val, h2, Units.val_one, sub_self]`. Establish `hu : residue R (u : R) = 1`. Use `(residue_eq_zero_iff _).2 h1` as an intermediate fact. Rewrite `this` using `[map_sub, map_one, sub_eq_zero]`. Then use the resulting hypothesis.

Establish `hs : IsUnit (∑ i ∈ Finset.range N, (u : R) ^ i)`. Rewrite `hN`, the goal using `[← residue_ne_zero_iff_isUnit]`. Simplify `hN` using `[map_sum, hu]`. Conclude with `Units.ext (sub_eq_zero.1 (hs.mul_left_eq_zero.1 e))`.
-/
private theorem unit_eq_one_of_pow_eq_one_of_residue_one {R : Type} [CommRing R] [IsLocalRing R] (u : Rˣ) (N : ℕ) (hN : IsUnit (N : R))
    (h1 : (u : R) - 1 ∈ maximalIdeal R) (h2 : u ^ N = 1) : u = 1 := by
  have e := mul_geom_sum (u : R) N
  rw [← Units.val_pow_eq_pow_val, h2, Units.val_one, sub_self] at e
  have hu : residue R (u : R) = 1 := by
    have := (residue_eq_zero_iff _).2 h1
    rwa [map_sub, map_one, sub_eq_zero] at this
  have hs : IsUnit (∑ i ∈ Finset.range N, (u : R) ^ i) := by
    rw [← residue_ne_zero_iff_isUnit] at hN ⊢
    simpa [map_sum, hu] using hN
  exact Units.ext (sub_eq_zero.1 (hs.mul_left_eq_zero.1 e))

/- English proof (translation)
The claim follows from `SemidirectProduct.ext (Units.ext h) ((hm g).trans (hm' g).symm)`.
-/
private theorem apply_eq_of_hasMult_of_mat_eq {R D : Type} [CommRing R] [Group D] {η : D →* ℤˣ} {r ρ : D →* GG 3 R} (hm : HasMult η r)
    (hm' : HasMult η ρ) (g : D) (h : (r g).mat = (ρ g).mat) : r g = ρ g :=
  SemidirectProduct.ext (Units.ext h) ((hm g).trans (hm' g).symm)

/- English proof (translation)
Take `⟨x, hx, hx'⟩` from `hx`. Establish `hc : Canon (r x).mat 1` using `⟨fun a b => by simp, fun a => by simp, by simpa using hd x hx⟩`. Use `((cond_iff_canon η Ψ I r x 1 hr hx hx' hc).1.1 hT).ine s hs hη a` as an intermediate fact. Rewrite `this` using `[conjBy_one_inv_eq_self]`. Then use the resulting hypothesis.
-/
private theorem diag_entry_eq_character_on_inertia {O R D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [Group D]
    {η : D →* ℤˣ} {Ψ : D →* Oˣ} {I : Subgroup D} {r : D →* GG 3 R} (hr : Red η Ψ r)
    (hd : ∀ g, η g = 1 → (r g).mat.IsDiag) (hx : ∃ x, η x = 1 ∧ IsUnit ((Ψ x : O) ^ 2 - 1)) (hT : CondT η Ψ I r)
    (s : D) (hs : s ∈ I) (hη : η s = 1) (a : Fin 3) : (r s).mat a a = algebraMap O R (psi Ψ a s) := by
  obtain ⟨x, hx, hx'⟩ := hx
  have hc : Canon (r x).mat 1 := ⟨fun a b => by simp, fun a => by simp, by simpa using hd x hx⟩
  have := ((cond_iff_canon η Ψ I r x 1 hr hx hx' hc).1.1 hT).ine s hs hη a
  rwa [conjBy_one_inv_eq_self] at this

/- English proof (translation)
Set `u : Fin 3 → (F.η.ker →* Rˣ)` to `fun a => (kap F.η r hr.mult hd a).toHomUnits / (kap F.η ρ hρ.mult hd' a).toHomUnits`. Establish `hu : ∀ a (g : F.η.ker), (u a g : R) * (ρ g).mat a a = (r g).mat a a` using `fun a g => by show (((kap F.η r hr.mult hd a).toHomUnits g / (kap F.η ρ hρ.mult hd' a).toHomUnits g : Rˣ) : R) * (((kap F.η ρ hρ.mult hd' a).toHomUnits g : Rˣ) : R) = ((kap F.η r hr.mult hd a).toHomUnits g : Rˣ)`. Rewrite using `[← Units.val_mul, div_mul_cancel]`. Establish `hun : ∀ a (g : F.η.ker), IsUnit ((ρ g).mat a a)` using `fun a g => ((kap F.η ρ hρ.mult hd' a).toHomUnits g).isUnit`. Establish `h1 : ∀ (g : F.η.ker), r g = ρ g → ∀ a, u a g = 1` using `fun g e a => by`.

Apply `Units.ext` to reduce the goal to its premises. Apply `(hun a g).mul_right_cancel` to reduce the goal to its premises. Rewrite using `[hu, e, Units.val_one, one_mul]`. Establish `h2 : ∀ (g : F.η.ker), (∀ a, (r g).mat a a = (ρ g).mat a a) → r g = ρ g` using `fun g e => by`. Use `apply_eq_of_hasMult_of_mat_eq hr.mult hρ.mult _ ?_` and prove the remaining obligations.

Use extensionality with `a b`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Conclude with `e a`. Rewrite using `[hd g g.2 hab, hd' g g.2 hab]`.

Establish `h2' : ∀ (g : F.η.ker), (∀ a, u a g = 1) → r g = ρ g` using `fun g e => h2 g fun a => by rw [← hu, e, Units.val_one, one_mul]`. Establish `hc : r F.c = ρ F.c` using `apply_eq_of_hasMult_of_mat_eq hr.mult hρ.mult _ (hr.norm.atc.trans hρ.norm.atc.symm)`. Establish `hI : ∀ v (s : F.D v), s ∈ F.Iv v → F.η (F.loc v s) = 1 → r (F.loc v s) = ρ (F.loc v s)`. Introduce `v s hs hη`. Distinguish the cases in `hv : v ∈ F.Tb`.

Establish `key : ∀ r : Γ →* GG 3 R, F.IsPt g₁ r → (∀ g, F.η g = 1 → (r g).mat.IsDiag) → ∀ a, (r (F.loc v s)).mat a a = algebraMap O R (psi (F.Ψv v) a s)`. Introduce `r hr hd a`. Use `diag_entry_eq_character_on_inertia (η := F.ηv v) (Ψ := F.Ψv v) (I := F.Iv v) (r := r.comp (F.loc v)) ⟨fun g => hr.mult (F.loc v g), fun g => hr.red (F.loc v g)⟩ (fun g hg => hd (F.loc v g) hg) (hF.x v hv) ?_ s hs hη a` and prove the remaining obligations. Break down `hv with hv | hv` into its components or cases. Conclude with `(hr.loc v).1 hv`.

Take `⟨h, hh, hD⟩` from `(hr.loc v).2.1 hv`. Conclude with `⟨h, hh, hD.toTriIn⟩`. Conclude with `h2 ⟨_, hη⟩ fun a => (key r hr hd a).trans (key ρ hρ hd' a).symm`. Use `haveI := Fintype.ofFinite (ResidueField O)`. Establish `hmem : s ^ Fintype.card (ResidueField O)ˣ ∈ F.Nv v`.

Use `⟨⟨pow_mem hs _, pow_mem (show s ∈ (F.ηv v).ker from hη) _⟩, ?_⟩` and prove the remaining obligations. Use `show ((Units.map (residue O).toMonoidHom).comp (F.Ψv v)) _ = 1`. Rewrite using `[map_pow, pow_card_eq_one]`. Establish `hN : IsUnit ((Fintype.card (ResidueField O)ˣ : ℕ) : O)`. Rewrite using `[← residue_ne_zero_iff_isUnit, map_natCast, Fintype.card_units, Nat.cast_sub Fintype.card_pos, FiniteField.cast_card_eq_zero]`.

Simplify using the standard rewrite rules. Use `h2' ⟨_, hη⟩ fun a => unit_eq_one_of_pow_eq_one_of_residue_one _ (Fintype.card (ResidueField O)ˣ) (by simpa using hN.map (algebraMap O R)) ?_ ?_` and prove the remaining obligations. Establish `e1` using `hr.red (F.loc v s) a a`. Establish `e2` using `hρ.red (F.loc v s) a a`. Establish `e3` using `sub_mem e1 e2`.

Rewrite `e3` using `[Matrix.sub_apply, Matrix.sub_apply, sub_sub_sub_cancel_right]`. Establish `e4` using `hu a ⟨_, hη⟩`. Rewrite using `[← Ideal.mul_unit_mem_iff_mem _ (hun a ⟨_, hη⟩), sub_mul, e4, one_mul]`. Conclude with `e3`. Rewrite using `[← map_pow]`.

Use `h1 _ ?_ a` and prove the remaining obligations. Establish `e1` using `(hr.loc v).2.2 hv _ hmem`. Establish `e2` using `(hρ.loc v).2.2 hv _ hmem`. Rewrite `e1`, `e2` using `[MonoidHom.comp_apply, map_pow (F.loc v)]`. Conclude with `e1.trans e2.symm`.

Establish `hsplit : ∀ g, F.η g = 1 ∨ ∃ g', F.η g' = 1 ∧ g = g' * F.c` using `fun g => by`. Break down `Int.units_eq_one_or (F.η g) with h | h` into its components or cases. Conclude with `Or.inl h`. Conclude with `Or.inr ⟨g * F.c, by simp [h, hF.ηc], by rw [mul_assoc, hF.csq, mul_one]⟩`. Establish `hconj : ∀ a (g x : Γ) (hg : F.η g = 1) (hx : F.η x = 1) (h : g * x * g⁻¹ ∈ F.η.ker), r x = ρ x → u a ⟨_, h⟩ = 1`.

Introduce `a g x hg hx h e`. Establish `: (⟨_, h⟩ : F.η.ker) = ⟨g, hg⟩ * ⟨x, hx⟩ * ⟨g, hg⟩⁻¹` using `rfl`. Rewrite using `[this, map_mul, map_mul, h1 ⟨x, hx⟩ e a, map_inv, mul_one, mul_inv_cancel]`. Establish `hker : ∀ g : F.η.ker, r g = ρ g`. Introduce `g`.

Use `h2' g fun a => Units.ext ?_` and prove the remaining obligations. Rewrite using `[← sub_eq_zero, ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R) Ideal.IsPrime.ne_top', Submodule.mem_iInf]`. Introduce `n`. Set `q : R →* R ⧸ maximalIdeal R ^ n` to `(Ideal.Quotient.mk (maximalIdeal R ^ n)).toMonoidHom`. Establish `lc : ∀ (r : Γ →* GG 3 R) (hr : F.IsPt g₁ r) (hd : ∀ g, F.η g = 1 → (r g).mat.IsDiag), IsLocallyConstant fun g => Units.map q ((kap F.η r hr.mult hd a).toHomUnits g)` using `fun r hr hd => IsLocallyConstant.desc _ Units.val (((hr.cont n).comp fun X => X a a).comp_continuous continuous_subtype_val) Units.val_injective`.

Establish `hχ` using `hC _ ((Units.map q).comp (u a)) (by`. Use `(lc r hr hd).div (lc ρ hρ hd')` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`. Conclude with `map_div (Units.map q) _ _) (by`.

Introduce `v s g h hs`. Establish `hη : F.η (F.loc v s) = 1`. Establish `: F.η (g * F.loc v s * g⁻¹) = 1` using `h`. Rewrite `this` using `[map_mul, map_mul, map_inv, mul_inv_cancel_comm]`. Then use the resulting hypothesis. Establish `e` using `hI v s hs hη`.

Rewrite using `[MonoidHom.comp_apply]`. Break down `hsplit g with hg | ⟨g', hg, rfl⟩` into its components or cases. Rewrite using `[hconj a g _ hg hη h e, map_one]`. Establish `e0 : g' * F.c * F.loc v s * (g' * F.c)⁻¹ = g' * (F.c * F.loc v s * F.c⁻¹) * g'⁻¹` using `by group`. Use `hconj a g' (F.c * F.loc v s * F.c⁻¹) hg (by simp [hη]) (e0 ▸ h) (by simp only [map_mul, map_inv, hc, e])` as an intermediate fact.

Rewrite using `[show (⟨_, h⟩ : F.η.ker) = ⟨_, e0 ▸ h⟩ from Subtype.ext e0, this, map_one])`. Use `congrArg Units.val (DFunLike.congr_fun hχ g)` as an intermediate fact. Rewrite using `[← Ideal.Quotient.eq]`. Conclude with `this`. Use `ext1 g`.

Break down `hsplit g with hg | ⟨g', hg, rfl⟩` into its components or cases. Conclude with `hker ⟨g, hg⟩`. Rewrite using `[map_mul, map_mul, hc, hker ⟨g', hg⟩]`.
-/
private theorem diagonal_reps_eq_of_same_frame_point {O R G Γ ι : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra O R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group Γ] [TopologicalSpace Γ] (F : Frame O G Γ ι) (hF : F.Ok) (hC : F.Cl1) (g₁ : Γ)
    (r ρ : Γ →* GG 3 R) (hr : F.IsPt g₁ r) (hρ : F.IsPt g₁ ρ) (hd : ∀ g, F.η g = 1 → (r g).mat.IsDiag)
    (hd' : ∀ g, F.η g = 1 → (ρ g).mat.IsDiag) : r = ρ := by
  classical
  let u : Fin 3 → (F.η.ker →* Rˣ) := fun a =>
    (kap F.η r hr.mult hd a).toHomUnits / (kap F.η ρ hρ.mult hd' a).toHomUnits
  have hu : ∀ a (g : F.η.ker), (u a g : R) * (ρ g).mat a a = (r g).mat a a := fun a g => by
    show (((kap F.η r hr.mult hd a).toHomUnits g / (kap F.η ρ hρ.mult hd' a).toHomUnits g : Rˣ) : R) *
      (((kap F.η ρ hρ.mult hd' a).toHomUnits g : Rˣ) : R) = ((kap F.η r hr.mult hd a).toHomUnits g : Rˣ)
    rw [← Units.val_mul, div_mul_cancel]
  have hun : ∀ a (g : F.η.ker), IsUnit ((ρ g).mat a a) := fun a g =>
    ((kap F.η ρ hρ.mult hd' a).toHomUnits g).isUnit
  have h1 : ∀ (g : F.η.ker), r g = ρ g → ∀ a, u a g = 1 := fun g e a => by
    apply Units.ext
    apply (hun a g).mul_right_cancel
    rw [hu, e, Units.val_one, one_mul]
  have h2 : ∀ (g : F.η.ker), (∀ a, (r g).mat a a = (ρ g).mat a a) → r g = ρ g := fun g e => by
    refine apply_eq_of_hasMult_of_mat_eq hr.mult hρ.mult _ ?_
    ext a b
    by_cases hab : a = b
    · subst hab; exact e a
    · rw [hd g g.2 hab, hd' g g.2 hab]
  have h2' : ∀ (g : F.η.ker), (∀ a, u a g = 1) → r g = ρ g := fun g e =>
    h2 g fun a => by rw [← hu, e, Units.val_one, one_mul]
  have hc : r F.c = ρ F.c := apply_eq_of_hasMult_of_mat_eq hr.mult hρ.mult _ (hr.norm.atc.trans hρ.norm.atc.symm)
  have hI : ∀ v (s : F.D v), s ∈ F.Iv v → F.η (F.loc v s) = 1 → r (F.loc v s) = ρ (F.loc v s) := by
    intro v s hs hη
    by_cases hv : v ∈ F.Tb
    · have key : ∀ r : Γ →* GG 3 R, F.IsPt g₁ r → (∀ g, F.η g = 1 → (r g).mat.IsDiag) → ∀ a,
          (r (F.loc v s)).mat a a = algebraMap O R (psi (F.Ψv v) a s) := by
        intro r hr hd a
        refine diag_entry_eq_character_on_inertia (η := F.ηv v) (Ψ := F.Ψv v) (I := F.Iv v) (r := r.comp (F.loc v)) ⟨fun g => hr.mult (F.loc v g), fun g => hr.red (F.loc v g)⟩
          (fun g hg => hd (F.loc v g) hg) (hF.x v hv) ?_ s hs hη a
        rcases hv with hv | hv
        · exact (hr.loc v).1 hv
        · obtain ⟨h, hh, hD⟩ := (hr.loc v).2.1 hv
          exact ⟨h, hh, hD.toTriIn⟩
      exact h2 ⟨_, hη⟩ fun a => (key r hr hd a).trans (key ρ hρ hd' a).symm
    · haveI := Fintype.ofFinite (ResidueField O)
      have hmem : s ^ Fintype.card (ResidueField O)ˣ ∈ F.Nv v := by
        refine ⟨⟨pow_mem hs _, pow_mem (show s ∈ (F.ηv v).ker from hη) _⟩, ?_⟩
        show ((Units.map (residue O).toMonoidHom).comp (F.Ψv v)) _ = 1
        rw [map_pow, pow_card_eq_one]
      have hN : IsUnit ((Fintype.card (ResidueField O)ˣ : ℕ) : O) := by
        rw [← residue_ne_zero_iff_isUnit, map_natCast, Fintype.card_units,
          Nat.cast_sub Fintype.card_pos, FiniteField.cast_card_eq_zero]
        simp
      refine h2' ⟨_, hη⟩ fun a => unit_eq_one_of_pow_eq_one_of_residue_one _ (Fintype.card (ResidueField O)ˣ)
        (by simpa using hN.map (algebraMap O R)) ?_ ?_
      · have e1 := hr.red (F.loc v s) a a
        have e2 := hρ.red (F.loc v s) a a
        have e3 := sub_mem e1 e2
        rw [Matrix.sub_apply, Matrix.sub_apply, sub_sub_sub_cancel_right] at e3
        have e4 := hu a ⟨_, hη⟩
        rw [← Ideal.mul_unit_mem_iff_mem _ (hun a ⟨_, hη⟩), sub_mul, e4, one_mul]
        exact e3
      · rw [← map_pow]
        refine h1 _ ?_ a
        have e1 := (hr.loc v).2.2 hv _ hmem
        have e2 := (hρ.loc v).2.2 hv _ hmem
        rw [MonoidHom.comp_apply, map_pow (F.loc v)] at e1 e2
        exact e1.trans e2.symm
  have hsplit : ∀ g, F.η g = 1 ∨ ∃ g', F.η g' = 1 ∧ g = g' * F.c := fun g => by
    rcases Int.units_eq_one_or (F.η g) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨g * F.c, by simp [h, hF.ηc], by rw [mul_assoc, hF.csq, mul_one]⟩
  have hconj : ∀ a (g x : Γ) (hg : F.η g = 1) (hx : F.η x = 1) (h : g * x * g⁻¹ ∈ F.η.ker), r x = ρ x →
      u a ⟨_, h⟩ = 1 := by
    intro a g x hg hx h e
    have : (⟨_, h⟩ : F.η.ker) = ⟨g, hg⟩ * ⟨x, hx⟩ * ⟨g, hg⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, h1 ⟨x, hx⟩ e a, map_inv, mul_one, mul_inv_cancel]
  have hker : ∀ g : F.η.ker, r g = ρ g := by
    intro g
    refine h2' g fun a => Units.ext ?_
    rw [← sub_eq_zero, ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R) Ideal.IsPrime.ne_top',
      Submodule.mem_iInf]
    intro n
    let q : R →* R ⧸ maximalIdeal R ^ n := (Ideal.Quotient.mk (maximalIdeal R ^ n)).toMonoidHom
    have lc : ∀ (r : Γ →* GG 3 R) (hr : F.IsPt g₁ r) (hd : ∀ g, F.η g = 1 → (r g).mat.IsDiag),
        IsLocallyConstant fun g => Units.map q ((kap F.η r hr.mult hd a).toHomUnits g) := fun r hr hd =>
      IsLocallyConstant.desc _ Units.val
        (((hr.cont n).comp fun X => X a a).comp_continuous continuous_subtype_val) Units.val_injective
    have hχ := hC _ ((Units.map q).comp (u a)) (by
      have := (lc r hr hd).div (lc ρ hρ hd')
      convert this using 1
      funext g
      exact map_div (Units.map q) _ _) (by
      intro v s g h hs
      have hη : F.η (F.loc v s) = 1 := by
        have : F.η (g * F.loc v s * g⁻¹) = 1 := h
        rwa [map_mul, map_mul, map_inv, mul_inv_cancel_comm] at this
      have e := hI v s hs hη
      rw [MonoidHom.comp_apply]
      rcases hsplit g with hg | ⟨g', hg, rfl⟩
      · rw [hconj a g _ hg hη h e, map_one]
      · have e0 : g' * F.c * F.loc v s * (g' * F.c)⁻¹ = g' * (F.c * F.loc v s * F.c⁻¹) * g'⁻¹ := by group
        have := hconj a g' (F.c * F.loc v s * F.c⁻¹) hg (by simp [hη]) (e0 ▸ h) (by simp only [map_mul, map_inv, hc, e])
        rw [show (⟨_, h⟩ : F.η.ker) = ⟨_, e0 ▸ h⟩ from Subtype.ext e0, this, map_one])
    have := congrArg Units.val (DFunLike.congr_fun hχ g)
    rw [← Ideal.Quotient.eq]
    exact this
  ext1 g
  rcases hsplit g with hg | ⟨g', hg, rfl⟩
  · exact hker ⟨g, hg⟩
  · rw [map_mul, map_mul, hc, hker ⟨g', hg⟩]

end UpperTheory.V.UnitaryThreeInertia

/- English proof (translation)
Introduce `l _ O _ _ _ _ _ _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF hC g₁ _ r ⟨A, _, _, t, r', hp, he⟩ hU hL`. Use `haveI : FaithfulSMul O A := (faithfulSMul_iff_algebraMap_injective O A).2 fun x y h => FaithfulSMul.algebraMap_injective O (PadicAlgCl l) (congrArg Subtype.val h)`. Establish `hz : ∀ (B : Type) [CommRing B] [Algebra O B] g, (F.rz B g).mat.IsDiag`. Introduce `B _ _ g a b hab`. Use `show algebraMap O B (((tor O (F.Ψ g) : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) a b) = 0`.

Rewrite using `[tor_val, Matrix.diagonal_apply_ne _ hab, map_zero]`. Establish `hent : ∀ g a b, ((r' g).mat a b : PadicAlgCl l) = ((t ^ wt a b : (PadicAlgCl l)ˣ) : PadicAlgCl l) * (r g).mat a b` using `fun g a b => by`. Rewrite using `[← (conjBy_tor r t).1, ← he]`. Both sides reduce to the same expression. Establish `hd : ∀ g, F.η g = 1 → (r' g).mat.IsDiag`.

Introduce `g hg a b hab`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hent]`. Establish `: wt a b ≠ 0` using `fun h => hab (by`. Establish `h' : wt1 a = wt1 b` using `sub_eq_zero.1 h`.

Simplify using `only [wt1] at h'`. Apply `Fin.ext` to reduce the goal to its premises. Use the proof step `omega)`. Break down `lt_or_gt_of_ne this with h | h` into its components or cases. Rewrite using `[hU g hg a b h, mul_zero]`.

Both sides reduce to the same expression. Rewrite using `[hL g hg a b h, mul_zero]`. Both sides reduce to the same expression. Use `haveI : IsNoetherianRing A := PrincipalIdealRing.isNoetherianRing`. Use `haveI : IsLocalHom (algebraMap O A) := Algebra.IsIntegral.isLocalHom O A`.

Establish `e` using `diagonal_reps_eq_of_same_frame_point F hF hC g₁ r' (F.rz A) hp (isPt_rz F hF g₁) hd fun g _ => hz A g`. Substitute `e` using the available equality. Use `ext1 g`. Use `SemidirectProduct.ext (Units.ext ?_) ?_` and prove the remaining obligations. Use `show (r g).mat = (F.rz (PadicAlgCl l) g).mat`.

Use extensionality with `a b`. Establish `h` using `hent g a b`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite `h` using `[wt, sub_self, zpow_zero, Units.val_one, one_mul]`.

Rewrite using `[← h]`. Both sides reduce to the same expression. Rewrite `h` using `[hz A g hab]`. Rewrite using `[hz _ g hab]`. Conclude with `(Units.mul_right_eq_zero _).1 h.symm`.

Rewrite using `[← (conjBy_tor r t).2.1, ← he]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.UnitaryThreeInertia.eq_rz_of_diag :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [FaithfulSMul O (PadicAlgCl l)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    F.Cl1 → ∀ g₁, F.Marked g₁ → ∀ (r : Γ →* GG 3 (PadicAlgCl l)), F.IsCharZeroPt g₁ r → Upper F.η r → Lower F.η r → r = F.rz (PadicAlgCl l) := by
  intro l _ O _ _ _ _ _ _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF hC g₁ _ r ⟨A, _, _, t, r', hp, he⟩ hU hL
  haveI : FaithfulSMul O A := (faithfulSMul_iff_algebraMap_injective O A).2 fun x y h =>
    FaithfulSMul.algebraMap_injective O (PadicAlgCl l) (congrArg Subtype.val h)
  have hz : ∀ (B : Type) [CommRing B] [Algebra O B] g, (F.rz B g).mat.IsDiag := by
    intro B _ _ g a b hab
    show algebraMap O B (((tor O (F.Ψ g) : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) a b) = 0
    rw [tor_val, Matrix.diagonal_apply_ne _ hab, map_zero]
  have hent : ∀ g a b, ((r' g).mat a b : PadicAlgCl l) =
      ((t ^ wt a b : (PadicAlgCl l)ˣ) : PadicAlgCl l) * (r g).mat a b := fun g a b => by
    rw [← (conjBy_tor r t).1, ← he]; rfl
  have hd : ∀ g, F.η g = 1 → (r' g).mat.IsDiag := by
    intro g hg a b hab
    apply Subtype.ext
    rw [hent]
    have : wt a b ≠ 0 := fun h => hab (by
      have h' : wt1 a = wt1 b := sub_eq_zero.1 h
      simp only [wt1] at h'
      apply Fin.ext; omega)
    rcases lt_or_gt_of_ne this with h | h
    · rw [hU g hg a b h, mul_zero]; rfl
    · rw [hL g hg a b h, mul_zero]; rfl
  haveI : IsNoetherianRing A := PrincipalIdealRing.isNoetherianRing
  haveI : IsLocalHom (algebraMap O A) := Algebra.IsIntegral.isLocalHom O A
  have e := diagonal_reps_eq_of_same_frame_point F hF hC g₁ r' (F.rz A) hp (isPt_rz F hF g₁) hd fun g _ => hz A g
  subst e
  ext1 g
  refine SemidirectProduct.ext (Units.ext ?_) ?_
  · show (r g).mat = (F.rz (PadicAlgCl l) g).mat
    ext a b
    have h := hent g a b
    by_cases hab : a = b
    · subst hab
      rw [wt, sub_self, zpow_zero, Units.val_one, one_mul] at h
      rw [← h]; rfl
    · rw [hz A g hab] at h
      rw [hz _ g hab]
      exact (Units.mul_right_eq_zero _).1 h.symm
  · rw [← (conjBy_tor r t).2.1, ← he]; rfl
