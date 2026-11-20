import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ClosedHeckeCosets.HeckeIdealEnd
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Adelise
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.RealExistenceFromPublished
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PrimRam
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HilbertClassFieldOfGlobalArtinReciprocity

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published

namespace UpperTheory.V.Sd.EG

section Norm

variable {l : ℕ} [hl : Fact l.Prime]

/- English proof (translation)
Use `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := x - 1) (y := 1) (by rw [norm_one]; exact h.ne)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel, norm_one, max_eq_right h.le]`. Then use the resulting hypothesis.
-/
theorem norm_eq_one_of {x : Qbar l} (h : ‖x - 1‖ < 1) : ‖x‖ = 1 := by
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := x - 1) (y := 1) (by rw [norm_one]; exact h.ne)
  rwa [sub_add_cancel, norm_one, max_eq_right h.le] at this

/- English proof (translation)
The claim follows from `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx hy)`.
-/
theorem small_add {x y : Qbar l} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x + y‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx hy)

/- English proof (translation)
Establish `h2 : ‖x‖ ^ n = 1` using `by rw [← norm_pow, h, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 h2`.
-/
theorem norm_root {x : Qbar l} {n : ℕ} (hn : n ≠ 0) (h : x ^ n = 1) : ‖x‖ = 1 := by
  have h2 : ‖x‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 h2

/- English proof (translation)
Establish `h : (l : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l])` using `by simp`. Rewrite using `[h, norm_algebraMap']`. Conclude with `Padic.norm_p_lt_one`.
-/
theorem norm_l : ‖(l : Qbar l)‖ < 1 := by
  have h : (l : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']
  exact Padic.norm_p_lt_one

/- English proof (translation)
Use `(IsUltrametricDist.isClosed_ball (0 : Qbar l) 1).preimage hf` as an intermediate fact. Simplify `this` using `[Set.preimage]`.
-/
theorem isClosed_small {Γ : Type} [TopologicalSpace Γ] {f : Γ → Qbar l} (hf : Continuous f) :
    IsClosed {s | ‖f s‖ < 1} := by
  have := (IsUltrametricDist.isClosed_ball (0 : Qbar l) 1).preimage hf
  simpa [Set.preimage] using this

/- English proof (translation)
Rewrite `h` using `[Matrix.charpoly_fin_two]`. Establish `h0` using `congrArg (coeff · 0) h`. Establish `h1` using `congrArg (coeff · 1) h`. Simplify using `[coeff_X, coeff_C, coeff_X_pow] at h0 h1`. Conclude with `⟨by rw [← h1]; simp, by rw [← h0]; simp⟩`.
-/
theorem tr_det (ι : Qbar l ≃+* ℂ) (B : Matrix (Fin 2) (Fin 2) (Qbar l)) {a d : ℂ}
    (h : B.charpoly.map ι.toRingHom = X ^ 2 - C a * X + C d) : B.trace = ι.symm a ∧ B.det = ι.symm d := by
  rw [Matrix.charpoly_fin_two] at h
  have h0 := congrArg (coeff · 0) h
  have h1 := congrArg (coeff · 1) h
  simp [coeff_X, coeff_C, coeff_X_pow] at h0 h1
  exact ⟨by rw [← h1]; simp, by rw [← h0]; simp⟩

end Norm

/- English proof (translation)
Establish `: Fact r.Prime` using `⟨hr⟩`. Establish `: IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed ℚ`. Establish `: NeZero (ordCompl[r] N)` using `⟨(Nat.ordCompl_pos r (NeZero.ne N)).ne'⟩`. Establish `hcop : (ordCompl[r] N).Coprime r` using `(Nat.coprime_ordCompl hr (NeZero.ne N)).symm`. Establish `hone : ∀ ζ : Ω, ζ ^ ordCompl[r] N = 1 → ζ ^ ((1 : (ZMod (ordCompl[r] N))ˣ) : ZMod (ordCompl[r] N)).val = ζ` using `fun ζ hζ => by`.

Rewrite using `[Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ, pow_one]`. Take `⟨w, hw⟩` from `KStar.TotallyRealRoots.redPow_surjective (l := r) (N.factorization r) (ZMod.unitsMap (Nat.ordProj_dvd N r) u)`. Take `⟨σ, hσ, hσw⟩` from `GlobalTheory.CycInertia.cycZ_Ine_surjective Ω r A hA w`. Use `⟨σ, hσ, (Chr.clsFacts ℚ Ω N).2.2.1 σ u ?_⟩` and prove the remaining obligations. Use `(LDataCardLeFinrank.classIff Ω r N σ.toRingEquiv u).2 ⟨fun ζ hζ => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[MonoidHom.mem_ker.1 hu, hone ζ hζ]`. Conclude with `(LDataCardLeFinrank.ineFixRoots ℚ Ω r A hA _ hcop ζ hζ).2 σ hσ`. Establish `hc : cyclotomicCharacter Ω r σ.toRingEquiv = w` using `hσw`. Rewrite using `[hc, hw]`.
-/
private theorem primRam_lift (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (r : ℕ) (hr : r.Prime)
    (A : ValuationSubring Ω) (hA : A.valuation (r : Ω) < 1) (u : (ZMod N)ˣ)
    (hu : u ∈ (ZMod.unitsMap (Nat.ordCompl_dvd N r)).ker) :
    ∃ σ ∈ Ine (F := ℚ) A, Chr.cls ℚ Ω N σ = u := by
  have : Fact r.Prime := ⟨hr⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero (ordCompl[r] N) := ⟨(Nat.ordCompl_pos r (NeZero.ne N)).ne'⟩
  have hcop : (ordCompl[r] N).Coprime r := (Nat.coprime_ordCompl hr (NeZero.ne N)).symm
  have hone : ∀ ζ : Ω, ζ ^ ordCompl[r] N = 1 →
      ζ ^ ((1 : (ZMod (ordCompl[r] N))ˣ) : ZMod (ordCompl[r] N)).val = ζ := fun ζ hζ => by
    rw [Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ, pow_one]
  obtain ⟨w, hw⟩ := KStar.TotallyRealRoots.redPow_surjective (l := r) (N.factorization r) (ZMod.unitsMap (Nat.ordProj_dvd N r) u)
  obtain ⟨σ, hσ, hσw⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω r A hA w
  refine ⟨σ, hσ, (Chr.clsFacts ℚ Ω N).2.2.1 σ u ?_⟩
  refine (LDataCardLeFinrank.classIff Ω r N σ.toRingEquiv u).2 ⟨fun ζ hζ => ?_, ?_⟩
  · rw [MonoidHom.mem_ker.1 hu, hone ζ hζ]
    exact (LDataCardLeFinrank.ineFixRoots ℚ Ω r A hA _ hcop ζ hζ).2 σ hσ
  · have hc : cyclotomicCharacter Ω r σ.toRingEquiv = w := hσw
    rw [hc, hw]

section Gal

variable {l : ℕ} [hl : Fact l.Prime] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

/- English proof (translation)
The claim follows from `(ML.placeBasic Ω).2.2.2.1 A v M ((Nat.Prime.coprime_iff_not_dvd hv).2 hM) hA`.
-/
theorem not_over {A : ValuationSubring Ω} {v M : ℕ} (hv : v.Prime) (hA : A.valuation (v : Ω) < 1) (hM : ¬ v ∣ M) :
    ¬ A.valuation (M : Ω) < 1 :=
  (ML.placeBasic Ω).2.2.2.1 A v M ((Nat.Prime.coprime_iff_not_dvd hv).2 hM) hA

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dirG_val {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) (s : G ℚ Ω) :
    (Chr.dirG ℚ Ω χ s : O) = χ (Chr.cls ℚ Ω N s : ZMod N) := rfl

/- English proof (translation)
Establish `h : IsLocallyConstant (Chr.cls ℚ Ω N)`. Rewrite using `[IsLocallyConstant.iff_exists_open]`. Use `fun x => ⟨_, (Chr.clsFacts ℚ Ω N).1.preimage (continuous_const_mul x⁻¹), by simp, fun y hy => ?_⟩` and prove the remaining obligations. Establish `h1 : Chr.cls ℚ Ω N (x⁻¹ * y) = 1` using `hy`. Rewrite `h1` using `[map_mul, map_inv, inv_mul_eq_one]`.

Conclude with `h1.symm`. Conclude with `(h.comp fun u : (ZMod N)ˣ => χ (u : ZMod N)).continuous`.
-/
theorem dirG_cont {N : ℕ} [NeZero N] (χ : DirichletCharacter (Qbar l) N) :
    Continuous fun s : G ℚ Ω => (Chr.dirG ℚ Ω χ s : Qbar l) := by
  have h : IsLocallyConstant (Chr.cls ℚ Ω N) := by
    rw [IsLocallyConstant.iff_exists_open]
    refine fun x => ⟨_, (Chr.clsFacts ℚ Ω N).1.preimage (continuous_const_mul x⁻¹), by simp, fun y hy => ?_⟩
    have h1 : Chr.cls ℚ Ω N (x⁻¹ * y) = 1 := hy
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  exact (h.comp fun u : (ZMod N)ˣ => χ (u : ZMod N)).continuous

/- English proof (translation)
Use `norm_root (n := Fintype.card (ZMod N)ˣ) Fintype.card_ne_zero ?_` and prove the remaining obligations. Rewrite using `[dirG_val, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]`.
-/
theorem dirG_norm {N : ℕ} [NeZero N] (χ : DirichletCharacter (Qbar l) N) (s : G ℚ Ω) :
    ‖(Chr.dirG ℚ Ω χ s : Qbar l)‖ = 1 := by
  refine norm_root (n := Fintype.card (ZMod N)ˣ) Fintype.card_ne_zero ?_
  rw [dirG_val, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]

/- English proof (translation)
Rewrite using `[Chr.dirG, MonoidHom.comp_apply, MonoidHom.mem_ker.1 ((Chr.clsFacts ℚ Ω N).2.2.2.2 A hA hg), map_one]`.
-/
theorem dirG_unr {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) {A : ValuationSubring Ω}
    (hA : ¬ A.valuation (N : Ω) < 1) {g : G ℚ Ω} (hg : g ∈ Ine (F := ℚ) A) : Chr.dirG ℚ Ω χ g = 1 := by
  rw [Chr.dirG, MonoidHom.comp_apply, MonoidHom.mem_ker.1 ((Chr.clsFacts ℚ Ω N).2.2.2.2 A hA hg), map_one]

/- English proof (translation)
Establish `h2` using `(Chr.clsFacts ℚ Ω N).2.2.1 σ (ZMod.unitOfCoprime v hc) fun ζ hζ => by`. Rewrite using `[h1 ζ hζ, ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_eq_pow_mod v hζ]`. Rewrite using `[h2, ZMod.coe_unitOfCoprime]`.
-/
theorem cls_pow {N v : ℕ} [NeZero N] (hc : v.Coprime N) {σ : G ℚ Ω} (h1 : ∀ ζ : Ω, ζ ^ N = 1 → σ ζ = ζ ^ v) :
    ((Chr.cls ℚ Ω N σ : (ZMod N)ˣ) : ZMod N) = v := by
  have h2 := (Chr.clsFacts ℚ Ω N).2.2.1 σ (ZMod.unitOfCoprime v hc) fun ζ hζ => by
    rw [h1 ζ hζ, ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_eq_pow_mod v hζ]
  rw [h2, ZMod.coe_unitOfCoprime]

/- English proof (translation)
Rewrite using `[dirG_val, cls_pow ((Nat.Prime.coprime_iff_not_dvd hv).2 hN) ((ML.placeBasic Ω).2.2.2.2.2.2.1 A v N σ h (not_over hv hA hN))]`.
-/
theorem dirG_frob {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) {A : ValuationSubring Ω} {v : ℕ}
    (hv : v.Prime) (hA : A.valuation (v : Ω) < 1) (hN : ¬ v ∣ N) {σ : G ℚ Ω} (h : IsFrob (F := ℚ) A v σ) :
    (Chr.dirG ℚ Ω χ σ : O) = χ v := by
  rw [dirG_val, cls_pow ((Nat.Prime.coprime_iff_not_dvd hv).2 hN)
    ((ML.placeBasic Ω).2.2.2.2.2.2.1 A v N σ h (not_over hv hA hN))]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cyc_val (s : G ℚ Ω) : (cycBar ℚ Ω l s : Qbar l) = algebraMap ℚ_[l] (Qbar l) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) := rfl

/- English proof (translation)
The claim follows from `(continuous_algebraMap ℚ_[l] (Qbar l)).comp (continuous_subtype_val.comp ((Units.continuous_val (M := ℤ_[l])).comp (continuous_cycZ ℚ Ω l)))`.
-/
theorem cyc_cont : Continuous fun s : G ℚ Ω => (cycBar ℚ Ω l s : Qbar l) :=
  (continuous_algebraMap ℚ_[l] (Qbar l)).comp
    (continuous_subtype_val.comp ((Units.continuous_val (M := ℤ_[l])).comp (continuous_cycZ ℚ Ω l)))

/- English proof (translation)
Rewrite using `[cyc_val, norm_algebraMap']`. Conclude with `PadicInt.norm_units _`.
-/
theorem cyc_norm (s : G ℚ Ω) : ‖(cycBar ℚ Ω l s : Qbar l)‖ = 1 := by
  rw [cyc_val, norm_algebraMap']
  exact PadicInt.norm_units _

/- English proof (translation)
Take `⟨w, hw, rfl, -⟩` from `(ML.placeBasic Ω).2.2.2.2.2.2.2.2.1 A v hv hA`. Establish `h1 : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal` using `fun h' => not_over hv hA hN (by simpa using (hw _).2 h')`. Rewrite using `[cyc_val, cycZ_of_isFrob h1 hw h]`. Simplify using the standard rewrite rules.
-/
theorem cyc_frob {A : ValuationSubring Ω} {v : ℕ} (hv : v.Prime) (hA : A.valuation (v : Ω) < 1) (hN : ¬ v ∣ l)
    {σ : G ℚ Ω} (h : IsFrob (F := ℚ) A v σ) : (cycBar ℚ Ω l σ : Qbar l) = v := by
  obtain ⟨w, hw, rfl, -⟩ := (ML.placeBasic Ω).2.2.2.2.2.2.2.2.1 A v hv hA
  have h1 : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h' => not_over hv hA hN (by simpa using (hw _).2 h')
  rw [cyc_val, cycZ_of_isFrob h1 hw h]
  simp

omit [IsAlgClosure ℚ Ω] in
/- English proof (translation)
Rewrite using `[← mem_iff, ← h]`. Simplify using the standard rewrite rules.
-/
theorem over_iff {A : ValuationSubring Ω} {w : Pl ℚ} (h : IsPlaceOver A w) (n : ℕ) : A.valuation (n : Ω) < 1 ↔ normV w ∣ n := by
  rw [← mem_iff, ← h]
  simp

/- English proof (translation)
The claim follows from `Subgroup.isOpen_mono (H₁ := (Chr.cls ℚ Ω N).ker) (fun s hs => by rw [MonoidHom.mem_ker, Chr.dirG, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hs, map_one]) (Chr.clsFacts ℚ Ω N).1`.
-/
theorem dirG_open {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) :
    IsOpen ((Chr.dirG ℚ Ω χ).ker : Set (G ℚ Ω)) :=
  Subgroup.isOpen_mono (H₁ := (Chr.cls ℚ Ω N).ker) (fun s hs => by
    rw [MonoidHom.mem_ker, Chr.dirG, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hs, map_one]) (Chr.clsFacts ℚ Ω N).1

/- English proof (translation)
Introduce `hall` and use `by have hft : χ.FactorsThrough (ordCompl[p] N) := by refine (DirichletCharacter.factorsThrough_iff_ker_unitsMap (Nat.ordCompl_dvd N p)).2 fun u hu => ?_ obtain ⟨σ, hσ, rfl⟩ := primRam_lift Ω N p hp A hA u hu have h1 := congrArg Units.val (MonoidHom.mem_ker.1 (hall hσ)) refine Mon …`.
-/
private theorem ram {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (f : ℂ →+* Qbar l) {p : ℕ} (hp : p.Prime)
    (hpN : p ∣ N) {A : ValuationSubring Ω} (hA : A.valuation (p : Ω) < 1) :
    ¬ Ine (F := ℚ) A ≤ (Chr.dirG ℚ Ω (χ.ringHomComp f)).ker := fun hall => by
  have hft : χ.FactorsThrough (ordCompl[p] N) := by
    refine (DirichletCharacter.factorsThrough_iff_ker_unitsMap (Nat.ordCompl_dvd N p)).2 fun u hu => ?_
    obtain ⟨σ, hσ, rfl⟩ := primRam_lift Ω N p hp A hA u hu
    have h1 := congrArg Units.val (MonoidHom.mem_ker.1 (hall hσ))
    refine MonoidHom.mem_ker.2 (Units.ext (f.injective ?_))
    rw [Units.val_one, map_one]
    exact h1
  have hd : χ.conductor ≤ ordCompl[p] N := Nat.sInf_le hft
  rw [hχ] at hd
  have := Nat.div_lt_self (NeZero.pos N) (Nat.one_lt_pow (hp.factorization_pos_of_dvd (NeZero.ne N) hpN).ne' hp.one_lt)
  omega

/- English proof (translation)
Take `⟨ω, φ, hω, hval, hφ, hcu⟩` from `adelise k N (by omega) χ g`. Take `⟨π, hreg, ⟨χ', hpol⟩, hinf, hU, hsat⟩` from `holRep P ℚ k (by omega) _ ω hω φ _ hφ hcu`. Take `⟨r, wt, HT, hG, hatt, -⟩` from `exR P ℚ Ω l ι 2 one_le_two π χ' hreg hpol`. Establish `hlN : l * N ≠ 0` using `mul_ne_zero hl.out.ne_zero (NeZero.ne N)`. Use `set c : Pl ℚ → ℕ := fun w => N.factorization (normV w) with hc`.

Establish `hc0 : ∀ w, c w = 0 ↔ ¬ normV w ∣ N` using `fun w => by`. Simplify using `[hc, Nat.factorization_eq_zero_iff, normV_prime w, NeZero.ne N]`. Use `set D : G ℚ Ω →* (Qbar l)ˣ := cycBar ℚ Ω l ^ (k - 1) * ψ with hD`. Establish `hDv : ∀ s, (D s : Qbar l) = (cycBar ℚ Ω l s : Qbar l) ^ (k - 1) * Chr.dirG ℚ Ω (χ.ringHomComp ι.symm.toRingHom) s` using `fun s => by`. Rewrite using `[hD, ← hm]`.

Simplify using the standard rewrite rules. Establish `hDc : Continuous fun s => (D s : Qbar l)`. Simplify using `only [hDv]`. Conclude with `(cyc_cont.pow _).mul (dirG_cont _)`. Establish `c1 : Continuous fun s : G ℚ Ω => (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l))` using `Units.continuous_val.comp (hG.cont.comp continuous_inv)`.

Establish `hdense` using `GlobalTheory.Published.ChebotarevDegreeOne.dense (F := ℚ) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' ((Filter.eventually_cofinite.1 hatt.2).union (fin_dvd hlN))`. Establish `hall : ∀ s, ‖(r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + D s)‖ < 1 ∧ (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det = D s` using `fun s => by`. Use `((isClosed_small (c1.matrix_trace.sub (continuous_const.add hDc))).inter (isClosed_eq c1.matrix_det hDc)).closure_subset_iff.2 ?_ (hdense s)` and prove the remaining obligations. Introduce and unpack `σ ⟨w, hw, -, A, hA, hσ⟩`. Simplify using `only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hw`.

Take `⟨⟨B₁, hB₁, hF⟩, hq⟩` from `hw`. Establish `hqN : ¬ normV w ∣ N` using `fun h => hq (h.mul_left _)`. Take `⟨B₂, hB₂, e⟩` from `hsat w ((hc0 w).2 hqN)`. Take `rfl` from `hB₁.unique hB₂`. Take `⟨h2, h3⟩` from `tr_det ι _ (((hF A hA).2 σ hσ).trans e)`.

Establish `hAq` using `(over_iff hA _).2 dvd_rfl`. Establish `h1 : (D σ : Qbar l) = ι.symm (χ (normV w : ZMod N) * (normV w : ℂ) ^ (k - 1))`. Rewrite using `[hDv, cyc_frob (normV_prime w) hAq (fun h => hq (h.mul_right _)) hσ, dirG_frob _ (normV_prime w) hAq hqN hσ]`. Simplify using `[mul_comm]`. Establish `h4` using `hg _ (normV_prime w)`.

Rewrite `h4` using `[map_sub, map_add, map_one, ← h1, ← h2]`. Conclude with `⟨h4, by rw [Set.mem_setOf_eq, h3, h1, (hval w hqN).2]⟩`. Establish `hlev : ∀ w : Pl ℚ, ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal → levL l c w = c w` using `fun w hw => if_neg hw`. Establish `hlev1 : ∀ w : Pl ℚ, ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal → levL l c w = 1` using `fun w hw => if_pos hw`. Establish `hker : ψ⁻¹.ker = ψ.ker` using `by ext s; simp`.

Use `⟨levL l c, π, r, ⟨hreg, ⟨χ', hpol⟩, hG.cont, hatt, MonoidHom.ext fun s => ?_, ?_, ?_, fun w A hA => ?_, fun w hw => ?_, fun w hw hwl => ?_, fun w hw => ?_⟩, fun s => (hall s).1⟩` and prove the remaining obligations. Establish `h1` using `(hall s⁻¹).2`. Rewrite `h1` using `[inv_inv]`. Use `(Units.ext h1 : Matrix.GeneralLinearGroup.det (r s) = D s⁻¹).trans ?_` and prove the remaining obligations. Rewrite using `[show 1 - (k : ℤ) = -((k - 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, ← mul_inv, map_inv]`.

Both sides reduce to the same expression. Rewrite using `[hker, ← hm]`. Conclude with `dirG_open _`. Use `(fin_dvd hlN).subset fun w hw => ?_` and prove the remaining obligations. Distinguish the cases in `h : ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal`.

Conclude with `((mem_iff w l).1 h).mul_right _`. Rewrite `hw` using `[Set.mem_setOf_eq, hlev w h, Ne, hc0, not_not]`. Conclude with `hw.mul_left _`. Rewrite using `[hker, ← hm]`. Distinguish the cases in `h : normV w ∣ N`.

Establish `h1 : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal` using `fun h' => hN ((mem_iff_eq w hl.out).1 h' ▸ h)`. Rewrite using `[hlev w h1, hc0]`. Conclude with `iff_of_false (ram hχ _ (normV_prime w) h ((over_iff hA _).2 dvd_rfl)) (by simp [h, h1])`. Use `iff_of_true (fun s hs => dirG_unr _ (fun h' => h ((over_iff hA _).1 h')) hs) ?_` and prove the remaining obligations. Distinguish the cases in `h1 : ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal`.

Conclude with `Or.inr h1`. Conclude with `Or.inl ((hlev w h1).trans ((hc0 w).2 h))`. Establish `h1 : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal` using `fun h' => by rw [hlev1 w h'] at hw; exact one_ne_zero hw`. Take `⟨v, h2, h3, -⟩` from `hU w`. Rewrite `h3` using `[show N.factorization (normV w) = 0 from (hlev w h1).symm.trans hw]`.

Conclude with `⟨v, h2, h3⟩`. Rewrite `hw`, the goal using `[hlev w hwl]`. Use `⟨_, hU w, norm_eq_one_of ?_⟩` and prove the remaining obligations. Establish `h4` using `hg _ (normV_prime w)`. Rewrite `hw` using `[Ne, hc0, not_not]`.

Rewrite `h4` using `[χ.map_nonunit (fun h' => (Nat.Prime.coprime_iff_not_dvd (normV_prime w)).1 ((ZMod.isUnit_iff_coprime _ _).1 h') hw), zero_mul, add_zero, map_sub, map_one]`. Then use the resulting hypothesis. Establish `hq` using `(mem_iff_eq w hl.out).1 hw`. Establish `hqN : ¬ normV w ∣ N` using `hq ▸ hN`. Take `⟨B, hB, e⟩` from `hsat w ((hc0 w).2 hqN)`. Rewrite `e` using `[(hval w hqN).2]`.

Establish `h2 : ‖ι.symm (χ (normV w : ZMod N))‖ = 1`. Use `norm_root (n := Fintype.card (ZMod N)ˣ) Fintype.card_ne_zero ?_` and prove the remaining obligations. Rewrite using `[← ZMod.coe_unitOfCoprime _ ((Nat.Prime.coprime_iff_not_dvd (normV_prime w)).2 hqN), ← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one, map_one]`. Establish `h3 : ‖(normV w : Qbar l)‖ < 1` using `by rw [hq]; exact norm_l`. Establish `hs : ‖ι.symm (χ (normV w : ZMod N) * (normV w : ℂ) ^ (k - 1))‖ < ‖(normV w : Qbar l)‖`.

Rewrite using `[map_mul, norm_mul, h2, one_mul, map_pow, map_natCast, norm_pow]`. Conclude with `pow_lt_self_of_lt_one₀ (norm_pos_iff.2 (Nat.cast_ne_zero.2 (normV_prime w).ne_zero)) h3 (by omega)`. Establish `ha : ‖ι.symm (g.a (normV w)) - 1‖ < 1`. Use `small_add (hg _ (normV_prime w)) (hs.trans h3)` as an intermediate fact. Rewrite `this` using `[← map_add]`.

Rewrite using `[← map_one ι.symm, ← map_sub]`. Use `this using 3` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Take `⟨lam, h5, h6⟩` from `stab w ι π hB e ha hs`. Use `⟨hlev1 w hw, ?_, ?_, norm_one, ⟨lam, h5, ?_⟩, fun τ _ => hinf _⟩` and prove the remaining obligations.

Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. Simplify using `using h6`.
-/
theorem ordEx (P : HypothesesH) (ι : Qbar l ≃+* ℂ) {k N : ℕ} [NeZero N] (hk : 3 ≤ k) (hN : ¬ l ∣ N) {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (g : Eigenform k N χ)
    (hg : ∀ p : ℕ, p.Prime → ‖ι.symm (g.a p - (1 + χ (p : ZMod N) * (p : ℂ) ^ (k - 1)))‖ < 1)
    {ψ : G ℚ Ω →* (Qbar l)ˣ} (hm : Chr.dirG ℚ Ω (χ.ringHomComp ι.symm.toRingHom) = ψ) :
    ∃ c π r, OrdForm ι ψ⁻¹ (1 - (k : ℤ)) c (fun _ => ![0, 1 - (k : ℤ)]) (fun _ => 1) π r ∧
      ∀ s, ‖(r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + (cycBar ℚ Ω l ^ (k - 1) * ψ) s)‖ < 1 := by
  classical
  obtain ⟨ω, φ, hω, hval, hφ, hcu⟩ := adelise k N (by omega) χ g
  obtain ⟨π, hreg, ⟨χ', hpol⟩, hinf, hU, hsat⟩ := holRep P ℚ k (by omega) _ ω hω φ _ hφ hcu
  obtain ⟨r, wt, HT, hG, hatt, -⟩ := exR P ℚ Ω l ι 2 one_le_two π χ' hreg hpol
  have hlN : l * N ≠ 0 := mul_ne_zero hl.out.ne_zero (NeZero.ne N)
  set c : Pl ℚ → ℕ := fun w => N.factorization (normV w) with hc
  have hc0 : ∀ w, c w = 0 ↔ ¬ normV w ∣ N := fun w => by
    simp [hc, Nat.factorization_eq_zero_iff, normV_prime w, NeZero.ne N]
  set D : G ℚ Ω →* (Qbar l)ˣ := cycBar ℚ Ω l ^ (k - 1) * ψ with hD
  have hDv : ∀ s, (D s : Qbar l) = (cycBar ℚ Ω l s : Qbar l) ^ (k - 1) * Chr.dirG ℚ Ω (χ.ringHomComp ι.symm.toRingHom) s := fun s => by
    rw [hD, ← hm]; simp
  have hDc : Continuous fun s => (D s : Qbar l) := by
    simp only [hDv]
    exact (cyc_cont.pow _).mul (dirG_cont _)
  have c1 : Continuous fun s : G ℚ Ω => (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)) :=
    Units.continuous_val.comp (hG.cont.comp continuous_inv)
  have hdense := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := ℚ) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    ((Filter.eventually_cofinite.1 hatt.2).union (fin_dvd hlN))
  have hall : ∀ s, ‖(r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + D s)‖ < 1 ∧
      (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det = D s := fun s => by
    refine ((isClosed_small (c1.matrix_trace.sub (continuous_const.add hDc))).inter
      (isClosed_eq c1.matrix_det hDc)).closure_subset_iff.2 ?_ (hdense s)
    rintro σ ⟨w, hw, -, A, hA, hσ⟩
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hw
    obtain ⟨⟨B₁, hB₁, hF⟩, hq⟩ := hw
    have hqN : ¬ normV w ∣ N := fun h => hq (h.mul_left _)
    obtain ⟨B₂, hB₂, e⟩ := hsat w ((hc0 w).2 hqN)
    obtain rfl := hB₁.unique hB₂
    obtain ⟨h2, h3⟩ := tr_det ι _ (((hF A hA).2 σ hσ).trans e)
    have hAq := (over_iff hA _).2 dvd_rfl
    have h1 : (D σ : Qbar l) = ι.symm (χ (normV w : ZMod N) * (normV w : ℂ) ^ (k - 1)) := by
      rw [hDv, cyc_frob (normV_prime w) hAq (fun h => hq (h.mul_right _)) hσ, dirG_frob _ (normV_prime w) hAq hqN hσ]
      simp [mul_comm]
    have h4 := hg _ (normV_prime w)
    rw [map_sub, map_add, map_one, ← h1, ← h2] at h4
    exact ⟨h4, by rw [Set.mem_setOf_eq, h3, h1, (hval w hqN).2]⟩
  have hlev : ∀ w : Pl ℚ, ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal → levL l c w = c w := fun w hw => if_neg hw
  have hlev1 : ∀ w : Pl ℚ, ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal → levL l c w = 1 := fun w hw => if_pos hw
  have hker : ψ⁻¹.ker = ψ.ker := by ext s; simp
  refine ⟨levL l c, π, r, ⟨hreg, ⟨χ', hpol⟩, hG.cont, hatt, MonoidHom.ext fun s => ?_, ?_, ?_, fun w A hA => ?_, fun w hw => ?_,
    fun w hw hwl => ?_, fun w hw => ?_⟩, fun s => (hall s).1⟩
  · have h1 := (hall s⁻¹).2
    rw [inv_inv] at h1
    refine (Units.ext h1 : Matrix.GeneralLinearGroup.det (r s) = D s⁻¹).trans ?_
    rw [show 1 - (k : ℤ) = -((k - 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, ← mul_inv, map_inv]
    rfl
  · rw [hker, ← hm]
    exact dirG_open _
  · refine (fin_dvd hlN).subset fun w hw => ?_
    by_cases h : ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
    · exact ((mem_iff w l).1 h).mul_right _
    · rw [Set.mem_setOf_eq, hlev w h, Ne, hc0, not_not] at hw
      exact hw.mul_left _
  · rw [hker, ← hm]
    by_cases h : normV w ∣ N
    · have h1 : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h' => hN ((mem_iff_eq w hl.out).1 h' ▸ h)
      rw [hlev w h1, hc0]
      exact iff_of_false (ram hχ _ (normV_prime w) h ((over_iff hA _).2 dvd_rfl)) (by simp [h, h1])
    · refine iff_of_true (fun s hs => dirG_unr _ (fun h' => h ((over_iff hA _).1 h')) hs) ?_
      by_cases h1 : ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
      · exact Or.inr h1
      · exact Or.inl ((hlev w h1).trans ((hc0 w).2 h))
  · have h1 : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h' => by rw [hlev1 w h'] at hw; exact one_ne_zero hw
    obtain ⟨v, h2, h3, -⟩ := hU w
    rw [show N.factorization (normV w) = 0 from (hlev w h1).symm.trans hw] at h3
    exact ⟨v, h2, h3⟩
  · rw [hlev w hwl] at hw ⊢
    refine ⟨_, hU w, norm_eq_one_of ?_⟩
    have h4 := hg _ (normV_prime w)
    rw [Ne, hc0, not_not] at hw
    rwa [χ.map_nonunit (fun h' => (Nat.Prime.coprime_iff_not_dvd (normV_prime w)).1 ((ZMod.isUnit_iff_coprime _ _).1 h') hw),
      zero_mul, add_zero, map_sub, map_one] at h4
  · have hq := (mem_iff_eq w hl.out).1 hw
    have hqN : ¬ normV w ∣ N := hq ▸ hN
    obtain ⟨B, hB, e⟩ := hsat w ((hc0 w).2 hqN)
    rw [(hval w hqN).2] at e
    have h2 : ‖ι.symm (χ (normV w : ZMod N))‖ = 1 := by
      refine norm_root (n := Fintype.card (ZMod N)ˣ) Fintype.card_ne_zero ?_
      rw [← ZMod.coe_unitOfCoprime _ ((Nat.Prime.coprime_iff_not_dvd (normV_prime w)).2 hqN), ← map_pow, ← map_pow,
        ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one, map_one]
    have h3 : ‖(normV w : Qbar l)‖ < 1 := by rw [hq]; exact norm_l
    have hs : ‖ι.symm (χ (normV w : ZMod N) * (normV w : ℂ) ^ (k - 1))‖ < ‖(normV w : Qbar l)‖ := by
      rw [map_mul, norm_mul, h2, one_mul, map_pow, map_natCast, norm_pow]
      exact pow_lt_self_of_lt_one₀ (norm_pos_iff.2 (Nat.cast_ne_zero.2 (normV_prime w).ne_zero)) h3 (by omega)
    have ha : ‖ι.symm (g.a (normV w)) - 1‖ < 1 := by
      have := small_add (hg _ (normV_prime w)) (hs.trans h3)
      rw [← map_add] at this
      rw [← map_one ι.symm, ← map_sub]
      convert this using 3
      ring
    obtain ⟨lam, h5, h6⟩ := stab w ι π hB e ha hs
    refine ⟨hlev1 w hw, ?_, ?_, norm_one, ⟨lam, h5, ?_⟩, fun τ _ => hinf _⟩
    · simp; omega
    · simp
    · simpa using h6

end Gal

end UpperTheory.V.Sd.EG
