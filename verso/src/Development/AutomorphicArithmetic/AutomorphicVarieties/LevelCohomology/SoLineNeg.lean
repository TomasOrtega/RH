import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoCocL
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoCobIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PlacesQ

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

/- English proof (translation)
Establish `hp : Prime ((l : ℕ) : 𝓞 ℚ)`. Establish `h : Prime ((l : ℕ) : ℤ)` using `Nat.prime_iff_prime_int.mp hl`. Establish `e : ((l : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((l : ℕ) : ℤ)` using `by simp`. Rewrite using `[e]`. Conclude with `(MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr h`.

Establish `hm : (Ideal.span {((l : ℕ) : 𝓞 ℚ)}).IsMaximal` using `((Ideal.span_singleton_prime hp.ne_zero).mpr hp).isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hp.ne_zero)`. Conclude with `HeightOneSpectrum.ext ((hm.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hv)).symm.trans (hm.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hw)))`.
-/
private theorem pl_uniq {l : ℕ} (hl : l.Prime) {v w : HeightOneSpectrum (𝓞 ℚ)} (hv : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (hw : ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) : v = w := by
  have hp : Prime ((l : ℕ) : 𝓞 ℚ) := by
    have h : Prime ((l : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hl
    have e : ((l : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((l : ℕ) : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr h
  have hm : (Ideal.span {((l : ℕ) : 𝓞 ℚ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp).isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hp.ne_zero)
  exact HeightOneSpectrum.ext
    ((hm.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hv)).symm.trans
      (hm.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hw)))

/- English proof (translation)
Introduce `CK hK pt fK tK lf lt le Ω _ _ _ l hl c N _ e ψ S A F he hF j hj s z hz hc _ _ hD`. Take `⟨n, rfl⟩ : ∃ n : ℕ, j = -(n : ℤ)` from `⟨(-j).toNat, by omega⟩`. Establish `hn : 1 ≤ n` using `by omega`. Set `η₀ : G ℚ Ω →* c.Oˣ` to `(Units.map (Int.castRingHom c.O).toMonoidHom).comp (UnitaryThreeInertia.eta4 Ω)`. Set `ψ' : G ℚ Ω →* c.Oˣ` to `Chr.dirG ℚ Ω ψ ^ n * (η₀ ^ s)⁻¹`.

Establish `hη : ∀ g, F.η (F.π g) = UnitaryThreeInertia.eta4 Ω g` using `fun g => DFunLike.congr_fun hF.η g`. Establish `hΨ : ∀ g, F.Ψ (F.π g) = Chr.Psi l e (Chr.dirG ℚ Ω ψ) g` using `fun g => DFunLike.congr_fun hF.Ψ g`. Establish `hθ : ∀ g, (Chr.Psi l (e * n) ψ')⁻¹ g = lineChar F (-(n : ℤ)) s (F.π g)`. Introduce `g`. Establish `h1 : etaO F (F.π g) = η₀ g`.

Simplify using `only [etaO, η₀, MonoidHom.comp_apply, hη]`. Simplify using `only [lineChar, MonoidHom.mul_apply, MonoidHom.zpow_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, hΨ, h1, Chr.Psi, ψ', zpow_neg, zpow_natCast, mul_pow, pow_mul, mul_inv, inv_inv, mul_assoc]`. Establish `ho : IsOpen (ψ'.ker : Set (G ℚ Ω))`. Use `Subgroup.isOpen_mono (H₁ := (Chr.cls ℚ Ω N).ker ⊓ (Chr.cls ℚ Ω 4).ker) (fun g hg => ?_) ((Chr.clsFacts ℚ Ω N).1.inter (Chr.clsFacts ℚ Ω 4).1)` and prove the remaining obligations. Establish `h1 : Chr.cls ℚ Ω N g = 1` using `hg.1`.

Establish `h2 : Chr.cls ℚ Ω 4 g = 1` using `hg.2`. Simplify using `only [MonoidHom.mem_ker, ψ', η₀, UnitaryThreeInertia.eta4, Chr.dirG, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, h1, h2, map_one, one_pow, inv_one, mul_one]`. Establish `hπc : Continuous F.π` using `by rw [hF.π]; exact continuous_toGS Ω _`. Establish `hπs : Function.Surjective F.π` using `by rw [hF.π]; exact QuotientGroup.mk_surjective`. Establish `hz' : Coc (Chr.Psi l (e * n) ψ')⁻¹ (fun g => z (F.π g))` using `fun g h => by`.

Rewrite using `[hθ]`. Use `show z (F.π (g * h)) = _`. Rewrite using `[map_mul, hz]`. Take `⟨a, ha, m, hm⟩` from `So.soCocL CK hK pt fK tK lf lt le ℚ Ω l c ψ' ho (e * n) (Nat.mul_pos he hn) (fun g => z (F.π g)) hz' (fun k => (hc k).comp_continuous hπc) (fun v hv => by`. Take `rfl : v = F.vl.1` from `pl_uniq hl.out hv hF.vl`.

Use `⟨A F.vl, hF.isOver _, So.cobIndex c.O _ _ _ hz' (UnitaryThreeInertia.eta4 Ω).ker _ ?_ ?_⟩` and prove the remaining obligations. Use `haveI : (UnitaryThreeInertia.eta4 Ω).ker.FiniteIndex := ⟨by rw [Subgroup.index_ker]; exact Nat.card_pos.ne'⟩`. Conclude with `Subgroup.FiniteIndex.index_ne_zero`. Take `⟨y, hy⟩` from `hD hj`. Use `⟨1, one_ne_zero, y, fun g hg => ?_⟩` and prove the remaining obligations.

Rewrite using `[one_mul, hθ]`. Conclude with `hy ⟨g, by rw [hF.D]; exact hg.2⟩ ((hη g).trans hg.1))`. Use `⟨a, ha, m, fun g _ => ?_⟩` and prove the remaining obligations. Take `⟨g, rfl⟩` from `hπs g`. Rewrite using `[← hθ]`.

Conclude with `hm g trivial`.
-/
theorem UpperTheory.V.X.So.lineNeg :
    ∀ CK : ℝ, LemmaK CK → GlobalTheory.Published.PoitouTateDuality → LocalFinitenessK → LocalTateDualityK → LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : HV.Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (S : Finset UnitaryThreeInertia.Pl) (A : S → ValuationSubring Ω) (F : UnitaryThreeInertia.Frame c.O (G ℚ Ω) (UnitaryThreeInertia.Gam Ω S) S), 1 ≤ e → UnitaryThreeInertia.IsHostFrame Ω c e ψ S A F → ∀ j : ℤ, j < 0 → ∀ s : ℕ, LineVan F j (lineChar F j s) := by
  intro CK hK pt fK tK lf lt le Ω _ _ _ l hl c N _ e ψ S A F he hF j hj s z hz hc _ _ hD
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = -(n : ℤ) := ⟨(-j).toNat, by omega⟩
  have hn : 1 ≤ n := by omega
  let η₀ : G ℚ Ω →* c.Oˣ := (Units.map (Int.castRingHom c.O).toMonoidHom).comp (UnitaryThreeInertia.eta4 Ω)
  let ψ' : G ℚ Ω →* c.Oˣ := Chr.dirG ℚ Ω ψ ^ n * (η₀ ^ s)⁻¹
  have hη : ∀ g, F.η (F.π g) = UnitaryThreeInertia.eta4 Ω g := fun g => DFunLike.congr_fun hF.η g
  have hΨ : ∀ g, F.Ψ (F.π g) = Chr.Psi l e (Chr.dirG ℚ Ω ψ) g := fun g => DFunLike.congr_fun hF.Ψ g
  have hθ : ∀ g, (Chr.Psi l (e * n) ψ')⁻¹ g = lineChar F (-(n : ℤ)) s (F.π g) := by
    intro g
    have h1 : etaO F (F.π g) = η₀ g := by
      simp only [etaO, η₀, MonoidHom.comp_apply, hη]
    simp only [lineChar, MonoidHom.mul_apply, MonoidHom.zpow_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, hΨ, h1,
      Chr.Psi, ψ', zpow_neg, zpow_natCast, mul_pow, pow_mul, mul_inv, inv_inv, mul_assoc]
  have ho : IsOpen (ψ'.ker : Set (G ℚ Ω)) := by
    refine Subgroup.isOpen_mono (H₁ := (Chr.cls ℚ Ω N).ker ⊓ (Chr.cls ℚ Ω 4).ker) (fun g hg => ?_)
      ((Chr.clsFacts ℚ Ω N).1.inter (Chr.clsFacts ℚ Ω 4).1)
    have h1 : Chr.cls ℚ Ω N g = 1 := hg.1
    have h2 : Chr.cls ℚ Ω 4 g = 1 := hg.2
    simp only [MonoidHom.mem_ker, ψ', η₀, UnitaryThreeInertia.eta4, Chr.dirG, MonoidHom.mul_apply, MonoidHom.pow_apply,
      MonoidHom.inv_apply, MonoidHom.comp_apply, h1, h2, map_one, one_pow, inv_one, mul_one]
  have hπc : Continuous F.π := by rw [hF.π]; exact continuous_toGS Ω _
  have hπs : Function.Surjective F.π := by rw [hF.π]; exact QuotientGroup.mk_surjective
  have hz' : Coc (Chr.Psi l (e * n) ψ')⁻¹ (fun g => z (F.π g)) := fun g h => by
    rw [hθ]
    show z (F.π (g * h)) = _
    rw [map_mul, hz]
  obtain ⟨a, ha, m, hm⟩ := So.soCocL CK hK pt fK tK lf lt le ℚ Ω l c ψ' ho (e * n) (Nat.mul_pos he hn)
    (fun g => z (F.π g)) hz' (fun k => (hc k).comp_continuous hπc) (fun v hv => by
      obtain rfl : v = F.vl.1 := pl_uniq hl.out hv hF.vl
      refine ⟨A F.vl, hF.isOver _, So.cobIndex c.O _ _ _ hz' (UnitaryThreeInertia.eta4 Ω).ker _ ?_ ?_⟩
      · haveI : (UnitaryThreeInertia.eta4 Ω).ker.FiniteIndex := ⟨by rw [Subgroup.index_ker]; exact Nat.card_pos.ne'⟩
        exact Subgroup.FiniteIndex.index_ne_zero
      · obtain ⟨y, hy⟩ := hD hj
        refine ⟨1, one_ne_zero, y, fun g hg => ?_⟩
        rw [one_mul, hθ]
        exact hy ⟨g, by rw [hF.D]; exact hg.2⟩ ((hη g).trans hg.1))
  refine ⟨a, ha, m, fun g _ => ?_⟩
  obtain ⟨g, rfl⟩ := hπs g
  rw [← hθ]
  exact hm g trivial
