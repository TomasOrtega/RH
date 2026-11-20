import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.RepNewform
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RankTwoAutomorphyDescendsFromAbelianCMToRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.DenseRangeUnitsR
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AutBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.AutomorphicNewformOfHyp

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.TwNewform

instance (priority := high + 1) torsionFree (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] : Module.IsTorsionFree L Ω :=
  DivisionSemiring.to_moduleIsTorsionFree

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨h, ?_⟩` and prove the remaining obligations. Simplify using `only [← map_inv]`. Conclude with `h.comp continuous_inv`.
-/
theorem cont_units {Γ R : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Monoid R]
    [TopologicalSpace R] (f : Γ →* Rˣ) (h : Continuous fun s => (f s : R)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv

/- English proof (translation)
Use `ext1 s`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [tw_val, smul_smul, MonoidHom.mul_apply, Units.val_mul]`.
-/
theorem tw_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (a b : Γ →* kˣ) :
    tw (tw r a) b = tw r (b * a) := by
  ext1 s
  apply Units.ext
  simp only [tw_val, smul_smul, MonoidHom.mul_apply, Units.val_mul]

/- English proof (translation)
Introduce `s hs` and use `h s fun ζ hζ => hs ζ (by obtain ⟨c, rfl⟩ := hMN rw [pow_mul, hζ, one_pow])`.
-/
theorem kills_dvd {Ω : Type} [Field Ω] [Algebra ℚ Ω] {C : Type} [Monoid C] {M N : ℕ} {χ : G ℚ Ω →* C}
    (h : KillsMu M χ) (hMN : M ∣ N) : KillsMu N χ := fun s hs => h s fun ζ hζ => hs ζ (by
  obtain ⟨c, rfl⟩ := hMN
  rw [pow_mul, hζ, one_pow])

/- English proof (translation)
Introduce `s hs` and use `by rw [MonoidHom.mul_apply, h s hs, h' s hs, one_mul]`.
-/
theorem kills_mul {Ω : Type} [Field Ω] [Algebra ℚ Ω] {C : Type} [CommMonoid C] {M : ℕ} {χ ψ : G ℚ Ω →* C}
    (h : KillsMu M χ) (h' : KillsMu M ψ) : KillsMu M (χ * ψ) := fun s hs => by
  rw [MonoidHom.mul_apply, h s hs, h' s hs, one_mul]

/- English proof (translation)
Introduce `s hs` and use `by rw [MonoidHom.inv_apply, h s hs, inv_one]`.
-/
theorem kills_inv {Ω : Type} [Field Ω] [Algebra ℚ Ω] {C : Type} [CommGroup C] {M : ℕ} {χ : G ℚ Ω →* C}
    (h : KillsMu M χ) : KillsMu M χ⁻¹ := fun s hs => by
  rw [MonoidHom.inv_apply, h s hs, inv_one]

/- English proof (translation)
Establish `hfin : {ζ : Ω | ζ ^ M = 1}.Finite` using `by classical`. Use `(Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_` and prove the remaining obligations. Simplify `hζ` using `[Polynomial.mem_nthRoots hM]`. Use `Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset ((hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral (K := ℚ) ζ).mem_nhds ?_) fun s hs => ?_)` and prove the remaining obligations. Simplify using `only [Set.mem_iInter]`.

Conclude with `fun ζ _ => Subgroup.one_mem _`. Simplify using `only [Set.mem_iInter] at hs`. Conclude with `hφ s fun ζ hζ => hs ζ hζ`.
-/
theorem kills_open {Ω C : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [Group C] {M : ℕ} (hM : 1 ≤ M)
    {φ : G ℚ Ω →* C} (hφ : KillsMu M φ) : IsOpen (φ.ker : Set (G ℚ Ω)) := by
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    classical
    refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots hM] using hζ
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
    ((hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral (K := ℚ) ζ).mem_nhds ?_) fun s hs => ?_)
  · simp only [Set.mem_iInter]
    exact fun ζ _ => Subgroup.one_mem _
  · simp only [Set.mem_iInter] at hs
    exact hφ s fun ζ hζ => hs ζ hζ

/- English proof (translation)
Use `continuous_of_continuousAt_one φ ?_` and prove the remaining obligations. Use `(continuousAt_const (y := (1 : C))).congr ?_` and prove the remaining obligations. Use `filter_upwards [(kills_open hM hφ).mem_nhds φ.ker.one_mem] with s hs`. Conclude with `hs.symm`.
-/
theorem cont_kills {Ω C : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [Group C] [TopologicalSpace C]
    [IsTopologicalGroup C] {M : ℕ} (hM : 1 ≤ M) {φ : G ℚ Ω →* C} (hφ : KillsMu M φ) : Continuous φ := by
  refine continuous_of_continuousAt_one φ ?_
  refine (continuousAt_const (y := (1 : C))).congr ?_
  filter_upwards [(kills_open hM hφ).mem_nhds φ.ker.one_mem] with s hs
  exact hs.symm

/- English proof (translation)
Use `haveI : NeZero M := ⟨by omega⟩`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Take `⟨μ, hμ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω M`. Use `⟨Fintype.card (ZMod M)ˣ, Fintype.card_pos, fun s => ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow]`.

Use `hχ _ fun ζ h => ?_` and prove the remaining obligations. Establish `h1` using `hμ.autToPow_spec ℚ (s ^ Fintype.card (ZMod M)ˣ)`. Rewrite `h1` using `[map_pow, pow_card_eq_one, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ hμ.pow_eq_one, pow_one]`. Take `⟨i, -, rfl⟩` from `hμ.eq_pow_of_pow_eq_one h`. Rewrite using `[map_pow, ← h1]`.
-/
theorem kills_pow {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {C : Type} [CommGroup C] {M : ℕ} (hM : 1 ≤ M)
    {χ : G ℚ Ω →* C} (hχ : KillsMu M χ) : ∃ k : ℕ, 0 < k ∧ ∀ s, χ s ^ k = 1 := by
  haveI : NeZero M := ⟨by omega⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  refine ⟨Fintype.card (ZMod M)ˣ, Fintype.card_pos, fun s => ?_⟩
  rw [← map_pow]
  refine hχ _ fun ζ h => ?_
  have h1 := hμ.autToPow_spec ℚ (s ^ Fintype.card (ZMod M)ˣ)
  rw [map_pow, pow_card_eq_one, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ hμ.pow_eq_one, pow_one] at h1
  obtain ⟨i, -, rfl⟩ := hμ.eq_pow_of_pow_eq_one h
  rw [map_pow, ← h1]

/- English proof (translation)
Take `⟨hne, -, hmin⟩` from `h`. Use `⟨hne, fun _ _ _ => Submodule.mem_top, fun W' _ hW' => hmin W' le_top fun s v hv => ?_⟩` and prove the remaining obligations. Establish `e : ((r.comp H.subtype) s : Matrix (Fin n) (Fin n) k).mulVec v = ((φ s)⁻¹ : kˣ).val • (tw r φ (s : Γ) : Matrix (Fin n) (Fin n) k).mulVec v`. Rewrite using `[tw_val, Matrix.smul_mulVec, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `W'.smul_mem _ (hW' _ v hv)`.
-/
theorem irr_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (H : Subgroup Γ) (φ : Γ →* kˣ)
    (h : IsIrr (r.comp H.subtype)) : IsIrr (tw r φ) := by
  obtain ⟨hne, -, hmin⟩ := h
  refine ⟨hne, fun _ _ _ => Submodule.mem_top, fun W' _ hW' => hmin W' le_top fun s v hv => ?_⟩
  have e : ((r.comp H.subtype) s : Matrix (Fin n) (Fin n) k).mulVec v =
      ((φ s)⁻¹ : kˣ).val • (tw r φ (s : Γ) : Matrix (Fin n) (Fin n) k).mulVec v := by
    rw [tw_val, Matrix.smul_mulVec, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    rfl
  rw [e]
  exact W'.smul_mem _ (hW' _ v hv)

end GlobalTheory.Ord2.TwNewform

namespace GlobalTheory.Ord2

open GlobalTheory.Ord2.TwNewform in

/- English proof (translation)
Take `⟨f, M', φ', hM', hφ', hf⟩` from `hA.modular`. Establish `h1 : IsAutR ι (tw W φ')` using `newformAutR P.toClassicalTheorems (2 * e + 1) (by omega) f l Ω ι (tw W φ') (-(e : ℤ)) (by rwa [tw_tw])`. Use `set κ : G ℚ Ω →* (Qbar l)ˣ := φ * φ'⁻¹ with hκ`. Establish `hMM : 1 ≤ M * M'` using `Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))`. Establish `hκM : KillsMu (M * M') κ` using `kills_mul (kills_dvd hφ (dvd_mul_right M M')) (kills_inv (kills_dvd hφ' (dvd_mul_left M' M)))`.

Take `⟨k, hk, hpow⟩` from `kills_pow hMM hκM`. Establish `halg : IsAlgChar ι κ`. Use `(algOfCyc P ℚ Ω l ι).1 κ (cont_kills hMM hκM) fun w _ => ?_` and prove the remaining obligations. Take `⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w` from `exists_isPlaceOver Ω w`. Conclude with `⟨A, hA, 0, k, hk, fun s _ => by rw [neg_zero, zpow_zero, mul_one, hpow]⟩`.

Establish `h2 : IsAut ι (tw (tw W φ') κ)` using `twi P ℚ Ω l ι 2 (tw W φ') κ ((autBridge P ℚ Ω l ι 2 (tw W φ')).1.2 h1) halg`. Establish `e1 : tw (tw W φ') κ = tw W φ`. Rewrite using `[tw_tw, hκ, inv_mul_cancel_right]`. Rewrite `h2` using `[e1]`. Establish `h3 : IsAutR ι (tw W φ)` using `(autBridge P ℚ Ω l ι 2 (tw W φ)).1.1 h2`.

Establish `hc : Continuous (tw W φ)`. Establish `hφc : Continuous φ` using `cont_kills hM hφ`. Use `cont_units _ ?_` and prove the remaining obligations. Simplify using `only [tw_val]`. Conclude with `(Units.continuous_val.comp hφc).smul (Units.continuous_val.comp hA.cont)`.

Establish `hirr : IsIrr (tw W φ)` using `irr_tw W (H0g W) φ hA.irr`. Take `⟨A, χ, κ', hAl, hχ, ⟨g, hg⟩, -, hin⟩` from `hA.flag`. Take `⟨v, hAv, hlv⟩` from `hAl`. Establish `hval : A.valuation (l : Ω) < 1`. Use `(hAv ((l : ℕ) : 𝓞 ℚ)).2 hlv` as an intermediate fact.

Simplify using `using this`. Establish `hχφ : KillsMu (l * M) (χ * φ)` using `kills_mul (kills_dvd hχ (dvd_mul_right l M)) (kills_dvd hφ (dvd_mul_left M l))`. Establish `hlM : 1 ≤ l * M` using `Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Fact.out : l.Prime).ne_zero (by omega))`. Use `autNewformOfKnownTheorems P hR Ω l ι e he (tw W φ) hc hirr h3 A hval (χ * φ).ker (kills_open hlM hχφ) ⟨g, fun s => ?_⟩` and prove the remaining obligations. Establish `hsD : (s : G ℚ Ω) ∈ Dec (F` using `ℚ) A := Ine_le_Dec A s.2.2`.

Establish `hsk : χ s * φ s = 1` using `s.2.1`. Establish `hmat : (g * tw W φ (s : G ℚ Ω) * g⁻¹).val = (φ (s : G ℚ Ω) : Qbar l) • (g * W (s : G ℚ Ω) * g⁻¹).val`. Simplify using `only [Units.val_mul, tw_val, Matrix.mul_smul, Matrix.smul_mul]`. Establish `hlow : ∀ i j : Fin 2, j < i → (g * W (s : G ℚ Ω) * g⁻¹).val i j = 0` using `(hg ⟨s, hsD⟩).1`. Establish `hdiag : ∀ i : Fin 2, (g * W (s : G ℚ Ω) * g⁻¹).val i i = (κ' i ⟨s, hsD⟩ : Qbar l)` using `(hg ⟨s, hsD⟩).2`.

Take `⟨h0, h1'⟩` from `hin ⟨s, hsD⟩ s.2.2`. Establish `hsk' : (χ s : Qbar l) * (φ s : Qbar l) = 1` using `by rw [← Units.val_mul, hsk, Units.val_one]`. Use `⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[hmat, Matrix.smul_apply, smul_eq_mul, hlow i j hij, mul_zero]`. Rewrite using `[hmat, Matrix.smul_apply, smul_eq_mul, hdiag i] fin_cases i`.

Use `show (φ s : Qbar l) * (κ' 0 ⟨s, hsD⟩ : Qbar l) = ((cycBar ℚ Ω l (s : G ℚ Ω) ^ (e : ℤ) : (Qbar l)ˣ) : Qbar l)`. Rewrite using `[h0, Units.val_mul]`. Take the linear combination `((cycBar ℚ Ω l (s : G ℚ Ω) ^ (e : ℤ) : (Qbar l)ˣ) : Qbar l) * hsk'`. Use `show (φ s : Qbar l) * (κ' 1 ⟨s, hsD⟩ : Qbar l) = ((cycBar ℚ Ω l (s : G ℚ Ω) ^ (-(e : ℤ)) : (Qbar l)ˣ) : Qbar l)`. Rewrite using `[h1', Units.val_mul]`.

Take the linear combination `((cycBar ℚ Ω l (s : G ℚ Ω) ^ (-(e : ℤ)) : (Qbar l)ˣ) : Qbar l) * hsk'`.
-/
theorem newform_twist_of_admissible (P : Af.HypothesesH) (hR : Published.RepNewform) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω]
    [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (W : R2 Ω l) (he : 1 ≤ e) (hA : admitted ι e W) (M : ℕ)
    (φ : G ℚ Ω →* (Qbar l)ˣ) (hM : 1 ≤ M) (hφ : KillsMu M φ) :
    ∃ g : Newform (2 * e + 1), g.Att ι (tw (tw W φ) (cycBar ℚ Ω l ^ (-(e : ℤ)))) := by
  obtain ⟨f, M', φ', hM', hφ', hf⟩ := hA.modular

  have h1 : IsAutR ι (tw W φ') :=
    newformAutR P.toClassicalTheorems (2 * e + 1) (by omega) f l Ω ι (tw W φ') (-(e : ℤ)) (by rwa [tw_tw])

  set κ : G ℚ Ω →* (Qbar l)ˣ := φ * φ'⁻¹ with hκ
  have hMM : 1 ≤ M * M' := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hκM : KillsMu (M * M') κ :=
    kills_mul (kills_dvd hφ (dvd_mul_right M M')) (kills_inv (kills_dvd hφ' (dvd_mul_left M' M)))
  obtain ⟨k, hk, hpow⟩ := kills_pow hMM hκM
  have halg : IsAlgChar ι κ := by
    refine (algOfCyc P ℚ Ω l ι).1 κ (cont_kills hMM hκM) fun w _ => ?_
    obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
    exact ⟨A, hA, 0, k, hk, fun s _ => by rw [neg_zero, zpow_zero, mul_one, hpow]⟩
  have h2 : IsAut ι (tw (tw W φ') κ) :=
    twi P ℚ Ω l ι 2 (tw W φ') κ ((autBridge P ℚ Ω l ι 2 (tw W φ')).1.2 h1) halg
  have e1 : tw (tw W φ') κ = tw W φ := by
    rw [tw_tw, hκ, inv_mul_cancel_right]
  rw [e1] at h2
  have h3 : IsAutR ι (tw W φ) := (autBridge P ℚ Ω l ι 2 (tw W φ)).1.1 h2

  have hc : Continuous (tw W φ) := by
    have hφc : Continuous φ := cont_kills hM hφ
    refine cont_units _ ?_
    simp only [tw_val]
    exact (Units.continuous_val.comp hφc).smul (Units.continuous_val.comp hA.cont)
  have hirr : IsIrr (tw W φ) := irr_tw W (H0g W) φ hA.irr

  obtain ⟨A, χ, κ', hAl, hχ, ⟨g, hg⟩, -, hin⟩ := hA.flag
  obtain ⟨v, hAv, hlv⟩ := hAl
  have hval : A.valuation (l : Ω) < 1 := by
    have := (hAv ((l : ℕ) : 𝓞 ℚ)).2 hlv
    simpa using this
  have hχφ : KillsMu (l * M) (χ * φ) :=
    kills_mul (kills_dvd hχ (dvd_mul_right l M)) (kills_dvd hφ (dvd_mul_left M l))
  have hlM : 1 ≤ l * M := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Fact.out : l.Prime).ne_zero (by omega))
  refine autNewformOfKnownTheorems P hR Ω l ι e he (tw W φ) hc hirr h3 A hval (χ * φ).ker (kills_open hlM hχφ) ⟨g, fun s => ?_⟩
  have hsD : (s : G ℚ Ω) ∈ Dec (F := ℚ) A := Ine_le_Dec A s.2.2
  have hsk : χ s * φ s = 1 := s.2.1
  have hmat : (g * tw W φ (s : G ℚ Ω) * g⁻¹).val = (φ (s : G ℚ Ω) : Qbar l) • (g * W (s : G ℚ Ω) * g⁻¹).val := by
    simp only [Units.val_mul, tw_val, Matrix.mul_smul, Matrix.smul_mul]
  have hlow : ∀ i j : Fin 2, j < i → (g * W (s : G ℚ Ω) * g⁻¹).val i j = 0 := (hg ⟨s, hsD⟩).1
  have hdiag : ∀ i : Fin 2, (g * W (s : G ℚ Ω) * g⁻¹).val i i = (κ' i ⟨s, hsD⟩ : Qbar l) := (hg ⟨s, hsD⟩).2
  obtain ⟨h0, h1'⟩ := hin ⟨s, hsD⟩ s.2.2
  have hsk' : (χ s : Qbar l) * (φ s : Qbar l) = 1 := by rw [← Units.val_mul, hsk, Units.val_one]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [hmat, Matrix.smul_apply, smul_eq_mul, hlow i j hij, mul_zero]
  · rw [hmat, Matrix.smul_apply, smul_eq_mul, hdiag i]
    fin_cases i
    · show (φ s : Qbar l) * (κ' 0 ⟨s, hsD⟩ : Qbar l) = ((cycBar ℚ Ω l (s : G ℚ Ω) ^ (e : ℤ) : (Qbar l)ˣ) : Qbar l)
      rw [h0, Units.val_mul]
      linear_combination ((cycBar ℚ Ω l (s : G ℚ Ω) ^ (e : ℤ) : (Qbar l)ˣ) : Qbar l) * hsk'
    · show (φ s : Qbar l) * (κ' 1 ⟨s, hsD⟩ : Qbar l) = ((cycBar ℚ Ω l (s : G ℚ Ω) ^ (-(e : ℤ)) : (Qbar l)ˣ) : Qbar l)
      rw [h1', Units.val_mul]
      linear_combination ((cycBar ℚ Ω l (s : G ℚ Ω) ^ (-(e : ℤ)) : (Qbar l)ˣ) : Qbar l) * hsk'

/- English proof (translation)
Introduce `P hR l _ Ω _ inst _ ι e W _ he hA M φ hM hφ`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Take `rfl : inst = DivisionRing.toRatAlgebra` from `Subsingleton.elim _ _`. Conclude with `newform_twist_of_admissible P hR l Ω ι e W he hA M φ hM hφ`.
-/
theorem twNewform : Af.HypothesesH → Published.RepNewform → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (W : R2 Ω l), l ≠ 2 → 1 ≤ e → admitted ι e W → ∀ (M : ℕ)
    (φ : G ℚ Ω →* (Qbar l)ˣ), 1 ≤ M → KillsMu M φ →
    ∃ g : Newform (2 * e + 1), g.Att ι (tw (tw W φ) (cycBar ℚ Ω l ^ (-(e : ℤ)))) := by
  intro P hR l _ Ω _ inst _ ι e W _ he hA M φ hM hφ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  exact newform_twist_of_admissible P hR l Ω ι e W he hA M φ hM hφ

end GlobalTheory.Ord2

end

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.Ord2.twNewform | exact GlobalTheory.Ord2.twNewform | (intros; apply GlobalTheory.Ord2.twNewform <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.newform_of_admissible_twist : Af.HypothesesH → Published.RepNewform → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (W : R2 Ω l), l ≠ 2 → 1 ≤ e → admitted ι e W → ∀ (M : ℕ) (φ : G ℚ Ω →* (Qbar l)ˣ), 1 ≤ M → KillsMu M φ → ∃ g : Newform (2 * e + 1), g.Att ι (tw (tw W φ) (cycBar ℚ Ω l ^ (-(e : ℤ)))) := by
  first | exact @GlobalTheory.Ord2.twNewform | exact GlobalTheory.Ord2.twNewform | (intros; apply GlobalTheory.Ord2.twNewform <;> assumption)

end
